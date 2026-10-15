-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5017
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:28:20.135782+00:00
-- url     : https://prove2.me/submissions/a7eed83d-733b-4d4a-b102-2d3c7df754a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 902158273 ≤ n < 902338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 902159523 1250 902158273 902158331
    0x80f100308070803040c0b030a060f080106050109180204050303120f0603060907290a090f0b04050303040b0304020409060608010b010f02031905091c03180e040c05120f1501050301 79
    0x281c00703850303903c054480d00f006100b51811403105400207410011070000f540308107102c03400054603074108800d584884580fa04070707810503894110300b4051a6003010740d00c0b058410f03001c996402e901c0300c20071041c060b00c03681d00100c4d0540004552000071003084d0000303038011400796128501d00d82d038010900d41e541d0703021600820280d0280004010550000305c02c41180b444105c107104181e000115508a281d00c88245030001400c44c803020041402d0404109018100d1840340f140360038900340c0083c2e564010350003034641410000001c10304555903613201420155000384140002d640d20502c41d4003c0c82e401a400340804c012610b1005030f40d2001c01107605040248103618401e10303150300100c071560031580f800c0c2c2d00300800240c024008003495400702e500d40d1003552031400c07800d403c00070382104a02d194045940070200c80288400100c030844220280c45040c1c2e0809404d00c4c000c980c003443e042c0b05010000050040c42d01c100020020f0f9029181030341e00c180c00034450318058403031014030802104c0854003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 902160773 1250 902159523 902159527
    0x906050a200a0315171c0e060d020403201c03020303011211420702010f140403080318160e0403140d020d0f0501060e06030a020403080703080f100308 66
    0x481d11411001414415400d80340008020318501c50204540481e608000d020148014030f8068042c0f0402118412000580324890800c122890250804005512240c850300c0082440c05020019a06481c0119001175113101010008003458510441c040089030060908082e000b0b000c10720f55a11050f055403650086180d84c0c070b07100d0300d9040200c540b04101c80000d03c54a2040450b583c07400c941140062495910024190001700103452815206012914410240c0c003420b10302c400505a80d08290282420070320904500000c5944404400e14100205400700340401405052030166216100822541d00340d00c0c960180c81c2c2d07880281581c42c401040103c40140000110307003800940042c440d0508000c9989804000c0d0110342180c0d880d41600d50780030070040d1310004c0034000c201065107880410089541060801402c00c9071200c81e540c003980c00080458035200c0c0b141d0480c0c0c02190000a01c646541d42450000c1440206442003001048090007280e13000000800840849510404142c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 902162023 1250 902160773 902160821
    0x10b040c140c1014160c0807030315081b0406050604030f031103090a0905062e0c1104020703050424080a0b0d0506010e0105010f020115050d051f0906050a 68
    0x1181c15800201c56291600030070005001c00b10180c02a5012600034a424801920b0229620004059041c040d0020050340d69240c0300032070303c68800c80b5491a0545000b0850810306002c40c4180c061030350101a4500c2000120418411140300e2141c40c0c01c01150240842d95403882003194500580c00090441c04881204000181c010411250803070f00d040e060b20300b40070042001030444030a07036000e14102516042041002e20309083c001500d1103084c000400c420f41c0005000000c1c880062403401405800000c0c1d4041c00481c0e5030f99880320400810540d6914800c0c600209150002e200301098074854280302d820010600c56100e030304030b52a42e1010160380c0c500f501e01c8040e18900138a142c2228602a018022403801d00c0304501800d5441d0340c681c100e5250000042804100152078803c40e494142e04004049a114241007110003c540c0c1d01202e00040c240981410b50303c1c3c00350319070107200c0358880c80e02e000d143e04103468980c090340e41000195a1503401c032080d65000c140c461a410010350b411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 902163273 1250 902162023 902162057
    0x80d0908071517040b01090c030e0a170c0a15110f09130608031209240f06010207080607020105101a0307110132090d090e09011b11010b040c 62
    0x460b2400c606190095004110024034007003094283c40640f5042032a400501c802c00480c000c080150603d441c0c208148084046166150095220700800101c00c3c03081e001c0011004505989059100500396034200c1c0d418549103950840c49e04000f81841d003040c0d0303149000020715064450b220490702c3c807185010a190100142101d1071514802c02c15034644002c0781940e4200081d01154801e218001c20034104400242c2c604880240405115904220f5110050310101800d6030482040409402281c480d500142c0c28100300360040d04c2288640420000312681c15080346009030341103407008071703801d07103c000d1051103242c88024450380880410102e83c01d80d2042c0031040300d8000352000001c1941e00211001c60728107004c200107207140c580110507240034504026558200014074000c0c100f44400f0880601000214070826858202d5080041c540503002c0d0814003c01820a030180991a040c89004d090355a500000035032941c84e200450340c0da403e051080d515030780e0080e2a0202000011815 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 902164523 1250 902163273 902163299
    0x6070e210a061d1018030806040f051609080106030b18150c0405090a0b180702010e01060f0905090c1c0507030c0e0402030f01060b0304020603060d0506040804080d090807 75
    0x900305607885040c40580c04120244100320103150358030019043d0100400c50300b46086500b41035020030328548036070b6045182c80b00f41070105d00d42d41b50404c00328503520b0300b000070300900d8061035002c00366048c10200211801001d4280c44210400c0d125100482d13250b0a407a803c880c95400014802c004200c00308500d038240c0c26000403580c01950440f2a0200007620524114078190350b18285200c0c00f003001c0c40245080203040398884c1c801d41c0104030009004e800074881a01d241400940d481005010950310380c1700b0740141510351030003c000c3c0a403680d1500c619041c0546481816566454640410007140d03010500c044056001040425140d90b0f50031055038004414904940c2d03481220000000100102012801080b903821900501d180600502d03051103444429281c560b40b5010302413140341c1000c02a40e0300a501610b049440340d45110101b402c0541741d60026009202d50010003040099a00040c016541c411050301c21740c20711003806441d903003003a0186024607048420240500600e1100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 902165773 1250 902164523 902164579
    0x10f08060607021201063003050714031204030e010216062010020403031b121407020d05010b01110a02090c030903040f06030e010b09040b16270806070e 67
    0x201e5103441010b41c0040c290401d4100b20441c665111881081100c160006103820250341044103044240d01a140e219120030a000080511101003904418081d290708044264085442225a074510183e50b04c200c440c0121422000244030390002c54407544042010300c24074008400740c41e0300b0782c1080c1051361603105020300c220151000361140c4880c031000f00410020505500401a6514214140201004100704d03008071001c03800345070580003a0b0004011644880c9078a022884100c20604d014140c0c452180040c0d408026618a002400419400940c3c0c540d007d884a050f10044400003940f2080207101c00b0394001000700001e201400d007000190350100c41d90040c0c3c0e24181c1c0794580440f010300315400250001e9666004526152001d01c0380d442142422100c96556190650781d00703112040040a68018400c180c1041d01c0807400783c080c500c180c0705006d60303010740d825a02c018608688018480c0308443c4c4030399004a100b0500a19800b990790901400008049030784404150260a6050f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 902167023 1250 902165773 902165779
    0x2041d1506150403030306032604150201060902040e100911070318033509100c020102121b01060512060402210a0303020a020f07051c0206120c04150806010f0806 71
    0xb41c4a6030b12052904010009140303e80c400044c0d650560503c80003902144400c1d880404250998a5104101c0d00580703045910100031440c0c450080c400c12401f4010702ea12095100740082004107118907121046441100003140341084540c0d204080d0090342c070215140c1e2001da07020085017000c030b03110391100c0c9000e0501400212140d540ca42c0c88000c1c0d09410f1210348003c5200c080700240200b008a5211041d82541ca0340c0707818490743d00000f88000c403100704000c0501000350720280459000780b050a00e45428803403050b0b1118400d41500e1110410f98800a140f940303800408500e034070746541e490b00c0c103482010040c01e15035140d40c00d120000c0003e0508a036a041044030400300030301c1c100445030740c0e940700c1da03000b5032128244040a45080a070113401c410300e40103030000740142d4a4110310076888521104410008510303600218166100b600d1118421a01c500c040001e99070310f4100520444161680d016400004a0b40c04c5596000c2940d82500080c071910300c800c8041d01c21900c041d0003450007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 902168273 1250 902167023 902167039
    0x130c15050c12040614030106091205011b03021905041d130503040605070c17100f290913030e0f060918180a081c0612060902041d1506 59
    0xc00502e242c002012403001001100040902509038401043d00104485d03884941c11941405000780c80d09840380038403c0c100d03c100c401c0800340102500001011448030004000714088450020302940c00b4403812402003006850003501544980102d6003100c08165a83e00342154541e00c018111740c01429600f07441c88032006100c046038040c0001d01c003e00b00c9441d110341e03540e400e250a61030070031300381c1c8001d4100711f8040c500b417509c50300070419004a900c1544c1c00607035008800714a800070031050005c5000116540d0310b00015103c0c2001c1d078850210300f25600740050340c8003184a90320105014000380050304180c0c1200079410200d1940801d080002c00b11818481100301003076960030321401000c0500c030014203010354600856081c145000720500135200c45106034803101458810032070741c59401c9000d000d40c5010714100f039016002608194521038903032869400c1c8007028041d010016440799203030200b00f045415152017404180782500b00038204841d0f00004011410500800c400d801200c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 902169523 1250 902168273 902168287
    0xf01081501050d11130906060b0f220f030f05010f0203130305070606090906090b0106050405222d060e040f12230c060604050709030215070c090212130c1505 69
    0x4400741784c6031440c2030b250001500c0c2007c0c182181034400c1c0da0310803007032404c08011101c3d2524260040352042203013075406200a000842481104000755489a9060b0340340000100070000c2191044001e540590020b000f0001004013510891000f0f0b200703151090150003205002170700410140820502440d8005000c41da102c81980507541e03404011100d541c1d442ca01c030010040190f40c204d0141800786132450600d400d020128140554021030301e08012804481c2034030303c0782c0c01d8015481c111592040751101c191035044590784031403420140256107091410224002c061080c04922603174002c6083c180070707031403034803480703001503a031003040e402c00c80041c541c3c1402d24007110364ad001401c0740c0d124a542d079081c54020603082040251000b4400d03406c180600c261980d20503680320940b501103c5400d0b80d519007a000c06164407848400803c01020002e00084c201c01c107a0241050307201e051007001c800d0352001c104e903000086080e4010803005827441c0501c051445d402da85e12510701241800c07460120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 902170773 1250 902169523 902169529
    0x2100903150b040e1506061c112701171806010602030406031107150e07121b0501020c100e0d0c180b01050f181302030703050f01081501050d11 63
    0x7007030303901d510300d0325224150212036080500c03c2400803509a0b0103800c04900a0401810500300680414407510010a030ba0f003e00e440c0c4001554a8450108100600c035071147c0030050035084074801001d41c02881000c102c500c90210506006034034147e480451100184e4008513100501402201d58504090710422041400f048480e02800d81034004648852030500000d09a4151070007081d1214018084080080d0202c0703001c0304500040e5070089000c1810000c2c9d40d103000788a62081d0520505c4408940a22074001000002c0c8841c1500c2842100d440700300590343d90a03181e58031508210340900d049005440340443c0000103c008000742c1c2c09114030f44442070300003443d401401202e16007041d030303c0301184603201d8400b9920086c200320307082c030482d059848454020001d01901240380c03401d801c1c140340d881c03801581c1c20320784009003151a0704041030002c00a0800b240d0140c18410710800114040300d00081d408000c09070542070660580c204024440c1020f8422421100004051420900f0796 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 902172023 1250 902170773 902170793
    0x30703110405131a090706050f190c02130f1d030a0320040303020609010f0c0f0503070207030b011d1803042601060608090607090e0a0903090504050109020a11060f0402100903 77
    0x10002072501d490031300b4070070742480c2041425841f01d400d001c41041045881d0a100090725a02c03500d1170350480310344c8040701050b200446802c0d002035018803202d10b0070141e100250b20519440d001c021040103c0c5002e918450f2401d5401c003101c05850340300f40000040c1d10701c82e401294902c05079400085030b4100e850355480700ca810540044000d1f0708560100105d55500b48181d00c40d14000c021b0900001818a1000e0610414480c0700010031a0003c00100614000c01c55000150b5000010300140d40c4d4a130700410401c40420400108d45c4004070114990824000c07070710100c0d481c0207012303502e0240b0f045015400d0b03904480b1070301c610f07800000c002070502400303106580c0241680e448401186ca051078000c6c1c02c0040050101c028846100020b125490341014442e0b442000c5800005214516040644d00904181e100076441030404001003440c4405401500480c02c1c0c40c0c44c2c9446510800c1030300d0b038136070004a0340100100502c2d00060050325002c0c01003c40d500503401e02520702500d1303031500002c1c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 902173273 1250 902172023 902172053
    0x120c19080322060c020f0f15010b0304110618040b0a0f09091a0405060414030307170a020903010f1a0f030c041d010c0e01140a0f0e010210090c060e03070311040513 72
    0x960842c81e1100c22006e8107100390804641d8602c0600646c4194082c44101000107029000c404540400010204a140502400ca094000303240984400d8105200e0120000c02078005000c3c81c01e1a5003104a1304140411409949411680c91504c2e070501c04640000d040c94002502c00308900310f90485100003600640380924010b801420080ca071606241c0c800513030103000000c1c030707610400402490303560043c6a015080c1105415001c0c035161940c215010b0f00419110583c503500e480c080c04091000c80c0d0144202a40c1c0c0c003038012485502c10104498002d811340000d4240e0041c04c00120546050382c48190055104140740e5005c049050001d8215002400041e000c60b48080c2c4010040d03030801c070808941b000d0a45424588000458002c20600350f82d40e851050001d460060001caa00910080e19051002d000421034200311b0f0806c02d00c401c5c03c0b88688800b00c0c2031213036120420b040c00f0030814207980d040180b40171541054020b00004040040400260541c03000031040001c084407289070710 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 902174523 1250 902173273 902173277
    0x120906050c0903060c031e060114160c150c110d0f06020901030f05070e0d0c05190509091c0804030513270b30120c19080322060c 57
    0x302c864400c249440d20070045c1294410400c1030041007241c00342d010800e041c51101d40800656521610016142e000b8185010640a00007045485440c00000c01e80030350305000340007a9810316a180c46080d044030114a9000014480550110114803113104980094002a2440502d50030a480d00407a1140c43c48080b90000c4e0002184551507a00d805160518010f40100304002d090886d00507003120042412980164480700c01c020034441c04041c1d800007041e02800c5445680703a01100560a621540207542c4100032400200d840004001a82e0074851000040012181082882a25580c000910881c1040760412170003c006070880340820013024500c5260810142c14054000004c000100c281011450a032000f4640e980e1040201c1e09000050700c20f0320100c900c00060401c050410a81e03281901c2102c01c14201c4c803020038010310591000301d054034120490124056040055804c010f41000000d002158841141403280b4070006265404030440240f1980c0d8075058900720612100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 902175773 1250 902174523 902174527
    0x5091b03011e09060501081315020f0c070b07170c07150302040311040e1b151201051203130e070c050601092c101d0a050606130c08040201120906050c 66
    0x810880301074009015001c3c0d4103003030001e542002c000034440c0307400800d595504072424240000b40302592086c01400300c08181e0039580c4891005011500c0d80c042c5100345003a00c135006002944c0e0300604183c0e18026072207044202c4100d15032038034980c10b8105424520301c0d03006076000021107645610300c240d502c50b40e5480142e200e61940c1050041076200c1d21f9054010390504a0304601104085070040c00003001180c0c081701200c1660105110800c0c40d2041010400009000701b40d0303882502c00c19040700c000700c0c1c50f5160034508141c030b2a142c2c000d0b005100c42c2e1001508040c488080580b6030294005090700d05000c40781e29545550785000002c1e48149601680ca0940058441696160000059074240070340040c0c0c0092000e20345c0c0b140c0b05100c1600d45551040c0c2201c118503640d8444455165080440d080184141010fa48070101a03645a00c00e2041c42c2c00065031340c80314003905010941d1030301c541415548980065800010707a400c5002c403182c1e658038610002c0c5007031007060b0040550030070081d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 902177023 1250 902175773 902175809
    0x1809020a0e100f0504020a27120602071118010e1e040c06080703020c03071e0203030a11010b01080403020604030f030f0f02030412051615060f14090601090f05091b0301 74
    0x18070030f0380d5034001c18010ba004000f103e42d910340040e10300100000c820003400d000d01c40c16401c2850207600f5086511b8040c80c4a80200c18400640c003d00541c1c0c0c01907040d0440e480024041260a11828103000d410020680c010466101024034090b800311920200c0301d4400e00407020b0343e0b03001c40304503411141c0d412a40b0091054560141c0c200790322a115050840c5080d080407844c0b07a4074041c11070020300d40c841c0b9008601c10340302503010341c1c034240750301504481d01c0d50007040020340388aa810914981c950701c1e044140c603066201d0b107081400f458043d0090110381c0c8032620b084492030144100001416110f181040300745503503210b0402550b004c95001a204c1c1030a2900d445002043d401c08010000c0078403010103840c5141c8141c0320341d030342d000518040c1003554283c00400b5100a9200d001a41d4280c01c1c00a5008101203040702e1140049550882075600d9400640e40f003034040c00382552444241c0f00500a0341418802c2c5a00071741340c0d140d080c00010301064410010307802600102502100c4d904070f2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 902178273 1250 902177023 902177039
    0x415181e110109080703110d080418050a1401170109051e0c03060405250b030708041b1a1305100e090106140f09120111041e1809020a0e10 61
    0x25480728031007403800541d41440d0014090765940d19000140001d0300c54242c10380103550b960a040d8000c2e500844054440d6078491107900030642c0c00303c0b5040220305007070001d4a09249032040c011f50074030400505050b03034200a4040c40c003280118a03c1810f40d40c5d0a219408600c00700b10b02c8013200d000280048811400c0c03441142404521040d00e4005c0e4044802e02c000a100030800404206005409240498481d02d50440300c4070301e6440b580041e400081400101d5a1044401d03118600503503402e080741e6844281001400e5442c8101d085c2010201c04100d107003041d80380200124040051a960a40c2e2908000703900000c010141202040f9000300c00340d030a00301605450700625150602e13604d01142d12040140314890042401d8a4140000350000196224580f0710322000d520350081260540b9802c6503103c55116000381560200c8000140050314035141d81c110951f10481010b14180c5e1001e034161007c0c00d00781c141260f21010310400031400c0001006081d106000318030990900500d40066 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 902179523 1250 902178273 902178293
    0x309041e0e032d2205040614011d130f090302010b0315010e040804030b091b060405130b031c03090309051c02130609020706060f06080415181e 63
    0xc207a0076a0828400d4082d00b00f078858848a800750b00305203001c0d4000002e22120840c1c070600e50442c10842c000c0342d00006514502c54880b054071800d0b01c08018031501e514100a6000100701000d000540030348003000b8608403980c00c3c05400d0b6001d440400458559110541650381d1200303200411542c9420300070506909002c0d80380b0000056028116501c0b6007501800000700c14009d00c0c0c01c400c400c101050810101c0c20171a4011b6820690a2505081c00c030240d40c0c54008118260107080ca40300d081040901d17001c0c080318201c8100074803691505041004840c09050f004003007991502505456402c0d1064950b0702d8501c10415580c000b4081480e0714015240b01d41c035802003409080b081f9880c0084640d923110009043da01114000101910302405c1c40150641e41c01c094400d900206805041180d02c0d0008026500804609440e260300d03a9021190b4990440b40900216149417400b8000556684078a04150084000e9100140c09481c3c000c04054250302940e207600313981204406102803454 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 902180773 1250 902179523 902179541
    0x1b061911010f021206040615050f070213053c0a0b030607120e0304050a030b090a1b0e010b0a230f0403030806210d1b0209010b0a18050612090309041e 66
    0x6401c01815080c005480c008c0c0100e070501006200000400c180399031600c03026904880e42c0101000414a008406180a0182070f902e8412581c042c1800d04085c00014200030085240315440c041c141c00300e6080114140c0025005803d2a50348064020158906010b0b0714442d01c0151070710084051180500422581c1d1201030750030750b400900081c81140d41b00c0010b1802c40382c02c80008441ca46408220031b082c442c2c4201d00a100342c03200400c3e11504400b606400707044074000442e900143ea82c8007440c0c41c0d103200b18002200041c0e41c0c0c0350b0381d42043e8507440c0c00803000700d400d5030a1810070340b03022002116a4403076003007940400c440700e08102c0649402d0b00c1040c01d000010a0b82c0c51011340e40700301d10781d91b00020541c1c482031004130442452064815003c814809400030150351995175146141709103940a00c000f0310001e102080304a4002c028100e90748222500546403c0c42c024950702030100c0c4540140800d5030034001000042c1c210f6442d8000e0502d0040c510b540d50034040800c040c520110f4000329 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 902182023 1250 902180773 902180779
    0x4090b0901080f0c1302120103060b0f01230307121e0e01152904030f060606081513290103060909020f0d03020f030c0309031b061911010f021206 64
    0x80e024410f0540d0101d02c0400748030068410b50040340c0c0650030300b40039000310074081005119940000052108940065040020a4a01d5481201240011039a000412591075412401d4001000610890b20002d540c8403400f441e0a00c000e4a068010318203650107a46000e401181880134244202080e00c0707042d07901c9155100801240ac0d12101c800314801491281d090107c0a400c000039116001803035002e60a028240d40954580d01c07450042031504c07000e502a030f1441c0c5000b20100b169800390001600071005160b4466902d5407840c10032141071200c1544464080e02c606521980c000260000c0e01044040564a11130101140004084865950045000ca0b00303140861002d43c85008a11071511000d581c03403d480f2190b0304003685420a210b50000741880002040e0035264008009400000011419200e0722001e40e80c0380224001840d0b41540d020000b0003c3d192003280c44141200d10070058200610702800d111403081c2140c0500ca28881125000144004407034808020590f10242c11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 902183273 1250 902182023 902182033
    0x10303020d03051906090911030d080a0b1f08090609061009150305191203020a05160c150207061808030a080c130f060807031109150f04090b090108 65
    0x1510029910700d65042248141a40c850109070b0701c800e03140b81d60030f400000380c00171701c0015914500140204000300c410b903040305036100300f05510329002c9910b00c0e034480582e0b5100c00540342c80d84103400900f60840360540c4802d56560401c0401a0b40e040c907081e800d06526011701c0c42c6404100d4a050805c01441030314680c0080d020080a00f542240c424144c0d1a1400001211050060405410030086e003000d46248a4407142003007080e403014035100da0300d204401d01c1100c3c0c081c2d0340d82a0160b00441d90004003194003844098040c00002d019010514011600010b080380e0b9401c1041d41904101d042da40183c02940c3c0610400740c110103c400e0301400c42c042c0c4150640b0300440c4e40c0c3c4a000b07092020080000d01c9000c140c00844800c1690b07450700e041c01640c0106560340101c82d003882041d108031804201008002902d15009218040c1e0500c446050035241c54480c2c0b04001c2c10140741c0d40303180715565003446004c41441a2802520240030038440c005038150405003000024401680412196441 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 902184523 1250 902183273 902183279
    0x20c01030b1e1518100206370e06070f17070c03050c1009020111011a060a03060b13060e10120506010309080c010506010909110715020903070f05150301 67
    0x2507191140c4140e42410790314480c0c40c040c840091034a90309a02c01c03c44140c0082010040d4510141c48011408021245a508042c4244050380c803088100d40d0011002e003000c01c00e0400030501011507803007500d6181e0307203d603860328041c04070229005004800c030940d0205080040003a0005000d600c4140541400c1080401c41d00b00001ca00e40001c20140411043e5982601094040c07415104903c028200fa42c075400200d1014000601c20220309900007000e045519808030818483c11001d41c0c0610000400c0c252644140900c1e035200103810020560740c0c103000036041280002a000a28012aa0035081840e00c9401840380c544860300d1032242c10484152084030381c0200c005100920850004a0103039030307080050700100802880a130450708006984003400e14198031082c0300321001d03202c100016445160700c3c000c4075000d80c06003003404010030500700840e2504426000b51001210094603108a90010900b042c030745922941340031034066401c0c8005d1501c0d40c0b211627036201d034542841c2590b01d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 902185773 1250 902184523 902184529
    0x30f0f0902031b060c0a030e1f0203160804050d140d03020903031c06030c060203031b041d0405010906061d090307150b3106050609090c0d02090406060f020c01030b 72
    0xe0340c0030b08041c0003403030f0121110503031282415521040c0301c6006071000d6811358203000e044d2646203150f0034425130300d00300040386031804045400944402e0707600441c24440c0b10051221401e40408064402c40400e02c8001440e50b41c1250001e6039078442d4600d80c1d522403480782e02a2030820f25070450302c1410700521900359503403000400d9924122007041d40d070ba00f0000081005008054580025000f4800c5050205005030004010350182c1f6001c004810301481161a054250003035010792552662402819810750402c0017800350000d0040000003800c0545a99203c1202c1c43e607400041c5028220384032014481c40708082980c4900c0b00c08c007451030a5243d60711420728901d00b12891003031685d03c41403041c1985601e0101003054a00070303070706071180b0301d0700f9003071a580c3c60419105151203003000750204084c20460280d90362040040d150603010389501994101c0ea821075140442200e42c01d224148080d070311800303600001d00503511003400b11411684000e08003100448c2160605090200803a0b40392 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 902187023 1250 902185773 902185783
    0x310140414160311160213090506130b0f0115030f140108010603051b0109180f090804090b0f150a022b0306172d011401170d090e0604020f0a030f0f090203 68
    0x10381c125801a14010420001c1000700140355010701302b446544100b00c0002c00c0225040d0301140684100426030341d0321907002d84465400d025001240c58030085880b207440c000d0704038070714080e110701011464003503440b6102d9800000340d0003459503a4445004100b80070003400a51400381c00503e150f401d1000420010340544464401c44038862210440000010f034268004824041080000c2c8811030850801803103e4100c0e000300241285080030b489200d15018041c50300e141c20260a0301c2280482401201441d0807905280e000d500600703211465901c0d811403820303152802030303280d0940300034421802801c5400070b03080034900005828551910309000105a0001c10f110f002010a044d14018a80410b505d0b025403200150301b086064500d040501840d01d041e18109031140e00b554036042034056454101c0c0c0759010100d96000f405110705130903a507100d548040701502c0945020f20002180010341e010246100020b40d8410030401481400e000303045600031500030a01c60051036800007500e507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 902188273 1250 902187023 902187067
    0x240627110316120b0319110102191209030506130b06040612060b0114040e0a050f0402060a030b011b080306010305070323040f02030a081b01020310140414160311 71
    0x103c43c0540e403103203400708550440d001040b00503065a0207407030510b43c0750750341d0344540720115202901c0d105d120f0700f194030004224100e6042e00307030001d0380c0c201d19481c0c800c4034050f91100740c410015825404004550b08206a5004444802c008000200b860600c0d030090b00c005005684585e0810000b008801c04906051210136044a00015130b5500f500060364403400d410300001420b0b4002c600002d00b4541034120511074202c4002c180900c1d035400b04030304290081180e0080d1f0110007031004564240c460340c001101280107042075000703246040e45421040c801e90000300d55112001041016659041c01016081038460600744903c0000d1204426680380c0182c4180010040070002070901c801c40000055042d0040d0655164410900b0700030200d07030114840180d001014101426100414400c0324800d6412a105080031820b000744180c10248402e0800e0740103855076010b00f000b0346034541d594020494812614201840c8100c0038050b41c500c04501d008568040c09903503211069440302cbc60036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 902189523 1250 902188273 902188277
    0x1d03161e09060801060504060801092a03051501050319080315031207050a0203060c0c0c0f030a2001021005010f0b0a021e1f09240627110316 62
    0x10010300841030000c00c050641c4481003103030504000050002040d44214250750041d03406000e240c0e00c441656003a10300142c0010901e103000000b2101d561002441445690402d0005030055603813522040d03e00a00c0b010b0035400c182c2c110004000c0c5150412120f022500b10f0001d99000368040c0e107403216240002841d241c0c0e561091502c01000350b5050007207507021002041800e807940319a042103a900c040a040480c080c2c4100d01c00302c0d003c0300e41c1000f031303803807400e50a00101950b00320a41441165030300d81c00302c19050322540e5404400a000000000780c0740c00d07903003041121043c00034002131901c008511603d100381c1c6800014014900c082c451502558100c0c1151641c89042e91001c1340760484c001c6c03d0321461400b240030801000c8001c200307070146140e149840309604602e01e90001c119109250010840d041c075543e0260b03500401d030700c41c0030504404c140000d02c03a83e84400c4026010001c0304040c2c10b041110005054541e1140701d2500f00d00c04c0680642e046150541105801003d024a0801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 902190773 1250 902189523 902189549
    0x1225080702070503031b120f07021e130e1c020a0605091911010228020409020f0301020406050418180f02040204091103150418080c0c101d0316 63
    0x445680200b04840c024030024003240d82c1e418000c11040c2d1001d011024601e0107000c2d100110b480005040207490042440e8111207280c49407660811411040c6040c681d49025041d11451100e81e4030640c6500e0758203c14180031854210b0040c0c014188011303800340d5450072800701740800005a00045d1582c699601403000203480d210500b0f61850038002102107256032024000740401c00c8800400150045001c0e021070700351040d50400200400340014810240f01ea00c15800700141c0307490b400c1181c005e400500f80140451049001c0b030b0036039020f40c0100000c50f100040070001642448250f00114003001004c011a0307840c0c00c526a201c01100101402c6030410740021800d42d80c403681190000c001c4104c0402440080c6421803401d608111a81c01810300d0649241120b400d083c0511408007115100400301c04c0055640d42c01ca507048900001e1591182404181080d1240c1b20400440b00c015107800c6103c03a41106440710503c2540b40c820b009810907100900d2504101f40260140c40c220003003a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 902192023 1250 902190773 902190781
    0x307210204210c0e0702030a0e060702060d201306020c0d02031203071202040e0601110703031e1707030510090612030327111002060105030c04021309050705122508 72
    0x3000c00600780c20440c13812035440144840c480d00000108240141612041c6000c0030032420406203018041c0042c0d0013a01c104120909200b05600494103106c4000e0540351140301d02d8002029500a9000c045c51a4400f40c0e0034066140c040118084804041f12240010a810f9011079203800c1c0c50320b01c800a0340400f001082805020320f02c194406414000115103036a17a80100705200e00d4241c03445808500d20460409802d2800b0411a0a494054445600c141c07031404480c0c1d05407281841d42c0080140b001041c6600f400300c150128000d0002d80d07004901400e200304114a4403400f076118000c0e8514044080104440c1c00710034800310b6405080010b201444c110f04185040c0303501510403042c0c0152101d100400c001c0000c000640203007a6071880c410710b000c0c1020b80e0b85d24030030b018055040d808400403490928281e00242088a000b1518150a966400d150426a0410b90304580443d002089002c0302202d9282d0072a44aa03202c400300198160007203120314600b0b0b0100d40c03002000701200000e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 902193273 1250 902192023 902192033
    0x3020d03170a0605090c27060d020d0218060a0f080c04090e010e0c030703030c0209040812010f03120804150e1e010b0414090d080a0b06030721020421 66
    0x215032900c440c8051200518210b0a1a00104207a02a5600c2151004086151a45903109854180038074440400229000301101441c81014412065010304100080f41c29030f4a140040c003510b0601c0d44026840d0400c40300360381144c40c003940e2014003440c1e048c03000020555010013410705458040c02c04100c6904c0d00c1c1900301f0746100e55041220b41c20700b041d014103103280c0154054018902d40400350703100080c00e2420903880702e20901c005800100303015002c10251038906a059007141c440e4110502d881503101c440d040305613090748280005514607808000340000404100340464a03483c0c08249890305996411901c00b0031061046519510361011605030010800c00401c0c501005510082c1d00702444845d018165104050b07000b00e0130164140c4c40080c980c001c1d01d010300400405071012449034081101c000b00300034a071800d42a101e0301440d0300303911980d009500071007035542c071185112481d0360000c0b0b89043c2450250891441000704101001701c2020400000030740c5458014141007600700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 902194523 1250 902193273 902193287
    0x30e030106120302031306142a07030f050c0301020f0d180629061e0d021213031d0907110f012d0203010605162306180a080403020d03 59
    0x40b024a06501e8400280364001015181110080100b420b42c9910303240100c03440c80d12045132140c0040d0900c00340f696080299036000e0380045003c0842c0300110105041d602c0e00301c9607032055404079640b0401c007084c000180036903000d05006070000d40c904000c1c00200034491003803180b400171030350b40e61801e41d910b82c41c80d0250780d05aa0304a001801150203004d06002001c00c03c0071608140000084c1d14551401c29000380d03194240036246581c0000602801004542e00005240c401c050f820040c040030310b091a1405401039450b00780b80020702d200d40c580900078100c48a000c5509200d85c0440760080d5840c809040e42c811081c0c07602e1241000003052035403600c03240c819010f81d42c0d405d02d0403e28800c0f20b1202d83d1a070b60304203911230802c58600307105908128882802130b0302c000341c01003001440c10641d5215a101c1c40d8420302407509860a06071188810441d1540249080d402c5141840030306440a00306100d40040d10f805811081b005540b40c40c1e0300e03c55403000038000c4100f0f80710981818002c42d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 902195773 1250 902194523 902194529
    0x141302120d020c01030b010c020609061c020f0d0b040203040521040803120402150a350405010911030c0102061603060b0a1e05030f0f090f0a05031801020c0904030e030106 75
    0xc03100c1070868030034080d4645050010f0f0310700103850407070300300c030750350720502d4080b44880e006062646040f1000e0b0600c08960302000c22000c801c0c1042e00c07680020003c1c1c2c8024504101c0b0b01d180380e91184d60f481d00e5001503c40194400e881a4010300500c400309001061066140d40301624801d9541c1800e15400d00e54026544403002c5400046440b0710032a620f9a91a880782d03108036044501010416060286400b411305000c3c0050101260740304010004502d8610743c860b05580300840c240b0800c000d10700b80b602240c0440b85a5102c9070607404000c4418855520b0b1341080f40504000515000000c0d035441c07005060b0120110792405261210340254031500240402010040d5103020203140908014480001c0c81da068004c00c00986001d88030350f0989003c0c0c4140345030742c03d0703589035005521140f83c006002c028140c002e450340400358050401400100d58815805962103003500614908000304034066203045d500700c00207000b250340d10200466070040d0b00d400c041c1010340320400400d0041c45160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 902197023 1250 902195773 902195809
    0x3020c0406080a050c221a040f0b01110106122405040309030b100605092107091d0105010b0a0f03090c032a150c1b090c1101141302 58
    0x10702142680700440da82c54444c0c001c808803a04000c010013440b00459243c140040c002d900c0343c030601003001c500e0300261001e04100a03000342d650000c8001404444a1981c10305400d551074000c6019940c106c03512030900d03103045000f08140380c0b500d03100c45080401e003640100300c2d900060b400c0028100c0212100020100c05604000328a071a29020780300541d80c0c001030f02c3c000446400940f01741040d03804102522880c2da550385c1800c0c480c10034807a068ac2c824004140d8552100d00000700400c0410035000144500040490b05045070020507039550004014600c03c2d904090052040303d4480045800304010340c504072140402c640400c40c01400500d10080c950300700d10600005000302510035040d81e03085002600700d01101240c481c104201980b09220070900c0c1d0700d8907006140d0045040300c0c140d60042103400411542d05000d26190340064200d0131a2650351f0100701140e59001c281c407500480884001c0014880da01b03001c04640c640100716807030b019201c404c06000c640fa1211950122603200c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 902198273 1250 902197023 902197031
    0x90b1609030b09031e0301030c0b0a030e1b010f09080a0807080415030b0f03061e070216031a09060106141c020c0d030b0d170d090c030f03030f05010302061603020c04 73
    0xb943e400e0b8403039001c2c1d500045000c001302e113001c8082111101300c034102c0390310002c001c0c900d9282507003a0003250070500041c1305047c2d4844620728088424040c0c0c0382100c010401d406040740301d0400140c062810b00354120300b0011000c03c203000300e100001b0290286504889256220001864141c64511982d004200c4c210100e80890380f5058160704074039000d000844900c4d00c02c042083c00c0c19501d140440765103002c1103480d085991400d0304400419040695441580c0b060103140860209001c000e50040b01c0d8205441c866504090320340410325080a4500054011549001c10080126414640d03805444500061030048104140581c42e46d1640c0124155180c01c0041c08041c3c45a10311400d260200e03040c134151600d1850112044240e0740c0d0f20000b50500340140c00c1070352110b034015214034411240d0755880040400d8183c4200d5009501c160007940640c0c1003464000c09a0381009003020f0035900b803000500040e0341d03410503501100c0040303000d1140d415050804a02d48400d50105c00d810900d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 902199523 1250 902198273 902198281
    0x160516080304182d06050a03030e0a060206010b04031e06050f0a0b0a06050a050313020901120507050604030f020f03010b040f0b041b05040302191d09060604090b1609030b 75
    0x22001e40221880d148940d50300c0301c128820300f016900030404208080ca8406a030070820041c05901c3ea08051036500009900d41c2c0f039501041c209030b0103400036804180a140d00d440d8604e00401584050301c820303c0038050b42d514084120025000342c5c00f00a08120208550709016101781d00059640e5420003030a11413414a07040135336181005880d40040c0c00d00704407a0f55240c1c03e003400c440702210340c00c2c2d40d40c0e0f2030405840c02c1124142c001500c0a0280703141c00c003075500540d03695100386019152298035600040001e01e0924902080d0307a00c0103006035801d0100f04003068070b900e899011107405807030541e8644410b800080c010001c1d20b40f0300c0d0f072143c60f20a00c0f018041896001d000c0041007035400308000a0000c1d03418900c9809104100002202040705200506110b8400d0300031001844044410f1a04c41511540000781001080b0340200c50740b04101c5080020000707650004802d680400040002e03403035038512044018038503688000502024001d0521030792109004507001a5104c1180c14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 902200773 1250 902199523 902199539
    0x60f0901050d030c2f0f060306040f110705010b03210909150a14100314011715040503071205070f1403040b0409060e100b030103111f030b0306100b160516 68
    0x2403500540f03a00307412030740001160a00c0c807512440e1b51401801d25056030341c0c2104002c00742c0740542207010241c0d100c9000041c5404540081c086641c8148000b042c0ca1355803006040c5805516101081070709040008200078070034101c215111500300741c41041030b41d0340f0b910400c004112030f100801c1c0c01a100c942d00054804449050b440807c1048480421700f519038802201030b1103818016a0380c68030300074010429141c0054803d4a1103410809850780c400c2800040480e00700f00315025901500001011010802035204146200d0020f044c010705024682e2214070306204000001495415240d000d02c018400810030b540041c8a96140c2682c0c55480d80d2802d400381009116440b09181c42c1000b08810310403071100307141623480f140100c0e07045a103551540e02e0706040c044510307a0001012845a440d842034803000d40d240b501e0075103022848001400525140060041900c8403054120606201b002c807402c04548805005404141071b0501c9030901c0c0c2d0034442080c0540300801ca6056000801c52 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 902202023 1250 902200773 902200823
    0x509031f0501081501052e051305060c0d080615040801090507050a060f0c03030b060c0c03070605030c040522061d10060e0603070909050108030d05060f0901050d030c 73
    0x610035003030910590b40d85401155503101c00f51080e40c00e002c0c200005000d41e00b8991a00300d4004043c00c0c40008550888550102d02d00c5e2020718074000410010304021031401441c1e1910003004156400c034a803414020869850f299407500c042c08000075900854103550b580c0340460707451081803110320359403940d0301042802043d407003504507070501401ca000101460040110411190552a00201c00c581e40d40c04894180c91810101c0c14142d560000498a032506005401e0101e4a080107003490b580080400d864101954484410490b0801c00c000c1105046016142102d41c04e598445c0114034101101074042d820b850f142c444246002c0b8009000d54802100200703144000001002c2030300c8aa90a11030041d590240c4004a010b03640d043c00b6504020000715405800791030490f0845884102590a94000703038000d1000d43d001242d0002c0c243c40c180b1070135810240c12603000d10189205c102141d4400e105205491140703501c0742c01c0905050289443d040182d5024044d04031022041c2103c41a50b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 902203273 1250 902202023 902202073
    0xa0501110705150402030a2a03060b03102007050a080a020a0b16050f09240315060913090312051014220209032112101a0a050903 57
    0x684a030290081807902607a60f0640600e40180140c08900e2035511114409600b001c3d18003405141c12080060300c3d007244021201840c0302c1e41020440c2c03250a0300f01880c14190300c0c69004014548818503090080902c02903505000303c224150b00c42e041c4c2d04086040c064450405040c20304001002c0f90a2540454101d02c2c0503c03440440c500f6071030791280c0b4428040512039240200c0ea00f00b0600704900f5130f8001500d4035200c014500e900b445100036001c0c0c60b09000d02070071002e004011050105410911002554902e4113468860030281040002142603050b15120030503140e44e40241000d140c070a015104001183e802c051203141802c1200c0030991f00107200703a8429419842c1104201d00c0e140d44044600007000e0344040b50080c01311103050080d801562425030500c42d8801c25400201c0c041e0750b09030030fa4814940c903034072440103401002d80c400005003e16003003024200d00340407401c0322104100e10410b03501c9030152580304904040e122480b42684d40c5030705100e400309000c050703c0114452042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 902204523 1250 902203273 902203283
    0x15170c090c0c070e090606010c0f0f03030e07080102090123070c080309090c03190c02071d01090c0302070803011211060309060402010e010219110d080a0f0908070b040e090a05011107 80
    0xf40c680d4600003070504101c1a02c2c43d0516400203400b0484a601c00c58001d101103006001d5108000100e540b80403a180039401c0440100b91660f60440325204240000c0f0000c0070044025803900c515400002c4c0500c0301c140d210202c0b041045032104082480a050302c01495101c00c1d0740c903455849a9600d81d494000c0d1442612680324000060392200d034000980b80a0150743c1c0e6403804101c08103405101600d084160101144a51000020080c000740401e40450b00304900100740c55040a0365a800c0c2c46000300307058281401000340400081c60402100c0c11900402e03040302c061216850304000020000303e026501c0500407046c0f0040740004951540141d100362608c00074504010f0040e030322403e0826540c00403c1c0c80b40500300105143c081c00c0d545000c0700814490b80d030b908554540105030003d059860000380c0e6110303901d1102d9007210300c0308068404100200006c502d4001e061519200340e018004085000c0e00100e1a201420811121460303070200c002e11492210250041311504202c00c1515 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 902205773 1250 902204523 902204533
    0x1d280504061d060f131a130207060515010207182a08070c0209060f010314131202030f04150e131e150608180d0c0b070315170c090c0c 59
    0xf54910305a107000b0740b40d6038042c0014040622000c500d000500e4040c4003252503150707001c6454500d507070300c001c0300c203402c20003040c010785500e0641888011103400500c80205280154012000e60f17800190b8103040301c0c00d035100104903c64400e80c000183c1040c0e22089002080301c0e240300c0e101c0ed4142d80700d87c09003105aa0703140395036a039014103c410000c0c0c2c01c1c020750403030028000b140039820003551418081c9030605000c0307044200d01c4008424454103ca504d840310940c1d10621040003680f1081d1000301d0b003175100440c14407586030b00c01c0c1414411417248880c61062446e00d60040d0340910460210081c1c0101002101403000d02c424029000c2c6040080340b60080082c2401c1c00e80380fa01c5421000450313210941c03001800c0140682d00c404000d040d40500c0700c0368103e01840b0380c41c10401c52070640801d940c0c1d0b0000004034135200442e00310103407241c0c05160500694110f0b5070741c1b104501c03048500b0741640010750707138100b082141403d00003e5040d8120000c0c204020401103c10000c184c01c659142c00c4030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 902207023 1250 902205773 902205781
    0x60e1e0604150b13180209010b0310061d0405100306020c01060f09060b090f04110a0509040507050a0e15040b040e10121e0c091b1d280504061d 63
    0x5084410b078100083d48400c0343c0342200c0c904003096201c4403240562031700c1481003021540002d0068030003680441441140007040005407005844000b005101c18240100c08030f0009070001d05625003202072070300030781d40c44000a1886580010f0032004540000c0110756418403488414045c2c00c944c00ba0107403a84c00d0060018544003248180e0048620054044d81845008002c02034100f51071350300f0035817054607081d444001c00d880710020803202d41c098442d2940c0e9000f600902c030039244004d00c00024808e0131301114501c16000032004280074412900c80441480c501c014610354001c1ea04201e10701040810042004200e06040c1da01038006d9041000316140c0d10000c0c0c0b241d0003903410700104070002c4003501c410020a02c800340183c580c0708014801c0035075101c40c030b008210348040322031520b000813250301c8100040c4c000600c145050060000010ba050004002c80c144484202402199400064450782e425120310f4020014281c02403091085558a015614040303800301ea00810882d0004041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 902208273 1250 902207023 902207063
    0x20a080c04150e062101140901050d06020318061311040218011b0812012612090a1d091c09050d1506030b1819060e1e0604 54
    0xc0d800321041c0c10765000210424501c211441c14840480c1c0b604a402030080490b05c0c0350070607692040070100c03481000c666240041541414a00091103806206544018840c40c0c54107075256903032680019003da40d81d1111a00c2c034003440c40100907104540507040610094070f40b4034441d42e400e0303030240c139244069001100c100022482010768404603c050032603058030b55402880c800d201c00710820351042e0a0134940c0c07a601c3d41544021641050010213000601240c82100640040030443c40041003619092017040e603a10103030302c4040c2e04c100b03001003418001d0380d0360741c0f0510000d0a510800403449002048298400c0e41c419503400c1907600844101000c0b910401d004100700608641d102d0864524060911101c401d4102c1d0603030740000c243c800c10416451030700502c0e001b1446220078544600d0049540000680c9000202ca05034000d490b95895602c01518040e60198000400181c1c5240f4018094035125a02c98080203000d40e00707101e08001070020500c0c5100c0d41c007680e071541680001c20705c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 902209523 1250 902208273 902208277
    0x6030b04021204020409170705060106030e0109050c01030209060d14220c061206170a0201030b0103090b060625030c050c04050112060908041e05120118150605040f020a080c 76
    0x2400080882200010f000f500e0160402c1360800d01400c0c454032013440404110700140d10442d42a42c56a1024004000169041c40380b50000f004500003000a40865a42c1544a41031800c62034101a000709414865507a035200302c400001d1420010400c6079034445520320009070449140320f224180365500040034021644035822740354025450300e42141030990589000c007114184d008026607a100c041b4150340e0280c0283c0c01c3c0d5804900402544c18144001000d40710701c403022034100342c20500800700203107e05c0707002034000400f19400d0b9142d05200242504c101c100c1410303c070740b5048c441070300c00600d80c01c101500039140c01201a00c41e42d000e203805010a9407820b2051003a40402d504038607009c103400e6401420841d02c2800c046251640d00c07841c981c80e4102848070380c8500c0560715403c0005240072582290780e540500024400124211054140a0b4200c1c801420040060384c0487c40700c5082e5014202414008000f00191a1442c0c5800005d40081d03128402050124002c0386031b00d00401e007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 902210773 1250 902209523 902209537
    0x61303140d0e0a0317160b06121b0409380604020a0c060f06170f10050f1321050d0e07051507030903050a0f030f11121809040c06030b0402 61
    0x604603946555200642601e107074005c1e900c5c038002448003a180da1800302c1c0043c07455000e00e07002c071182e040072810004e2180c5a192254101e0b4881c280c03801c09195440c80100e006da03812900080c0c01e4038907040403c00208240102079814200380d5245c0c0c6001d91840c420b49615010350400d42480d0755100a02c022441002000d101084099140f80001307a04e58000340444001d4001c00300d2442e9840c01510483d070034007801c0704102c0d00003401e803000c10f1508112080e0020840c04003030100c1d0a0114605402c0c5401521122101411640c81743c10301c84280711506d0f4031812240002d0559400c484000c155402002c0085001400c00c0d404002c0040000b03604130541d00c0040920000003401080035003103070b220010032000d00500000000205100344542c00542e0700601803440e02020394070b03006181d049000580e100303002c1c2519002100e0700c80010300130f111203801000c0325503036581046001c0e0142c00643c00e465119100004200c20000c40c0140681254003a41b000e00c1a155200d013008140c2c01446 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 902212023 1250 902210773 902210779
    0xf130609060201180f030e0d0b19092619020d110a120305060f06031305070503120919150230120606071a060315190b061303140d0e 58
    0xa00c0c0400829404110005e03c07520078140030074407450030804102c03255030717015060321510003103c1002210001c1040c101d80d41d10703084008002c5903503185c4e01e60501e4110240356030300b800c4407444400b0442074144100c03858540007050045002d216210003c0d0740e070207842d124038002800c6050005003640005075140c80c0c640c0c05000d0080103400840101e005182c001c1281d980125500c804c105503440d903c0040d40143e00102c505021002c050620502c0c100707d503845140a030b40020107a01d514102d42c001e56003c14011144414415080079500103540020b812040c1c07400680c160f103100c42500001d00b5442c4a0484089000b503d89405a140b1a600f20440010340150204019544002d50410003607010600070401810f2150390b440300c881c5420701510b80b0b40000070307075418403008c0d00c1c04205c010300344205401c2da80360360b07e48040e000421100011060501e162a00c0c114941950351005403000440404002e52a04c6d9032420510360f059020601004c1c1c0f4003492a04d0300300c00b845110104040f410103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 902213273 1250 902212023 902212061
    0x1902070b07080a180503030a18030c0b04030215190c0504060905041d190c0e1302010c050a172512120908030103060605090603060609070309080f130609060201 70
    0x30000c152002280104000c502d982d6855868132424480001080ba00f40220015a102d151802d540d40855845054000d03040705102158000250300812142d1b10f144e02806000c804d84640c0340c140e141412031001650219103180030822050f90981841100c44000c0805000700d261a00003503407140303d40d0244c4000510513000c103000e075007481e8124000140641200003c2c18511140041c205040c6141d400d01d48019180c030081070000341108407015241a085640e06402e01c601043c420b20904800241030040c069040d60034400288038103500980c0045141e542c81084a416440c260b204544091010804504904803904584080b501c800d9004030a60703204190307004107855620f0082c58004110f62146058800075542c070300034500a500c00c0d440403841d14100000c00c070b21400001c3c0160700030b502a2040004641e01e07161600c3d0481c07450304000603103d0640c10032013841d100b903100c1c04005110014800710070b0300c801c400302d02c105c0d050b594420b0f10307450b2070396022401e8078003c1d00304265a0b401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 902214523 1250 902213273 902213281
    0x3050918011424130302031b03030403020f04020d05011410020f03040905090f0a060204050f0405060a0b030a06050d0b06010f020604210c0f0303150b0c120a180e1902070b 75
    0x398600046a1074180c88452100c040d1a40c00d003202d074004a884180381380740407020011070408201e12040000700100710340c110781c00071000c207980780128031001c1e104006c0440d00c1c07100d40e15a07a044601d20030710808103112640c5c648100107140240031080360301440203841a110703180d1021410048982e402006503141624081e441c42c050702c00501051520b00031044030143d0f8a0081120384405403217000c0150301c4924103000c1207803100702c40b40d400303001d113042c482084090b9903203403406000d9480340c0d042300740c42c1d88400324040c00400c82a0003480d00011038244000034003d083e1000c503c901d00c01d07078981e814101f15400482c2c80c2e034015900248924840702c01e074070050060203801402c50f0041c3c40c02c1d20f20742e2040e4840043c61094a0340541c08290b03244011020001102c5011016013600c03602c40f450306140c0d614159540b0808000792542040c041018000584035515104c110300c00d01040c080e03100e0300c5c0c01180154000945c0e551207035440c50381600322004202e00a84000c1c0303801003d8401e6a0399 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 902215773 1250 902214523 902214529
    0x2090901030f0203011506020d1205060f011d13020909100b2d0a080411010e0102070302041116150b04110d0905070302060f131e030825030509180114 66
    0x81c0690308070313455501d41c82d8000e4440ca1a03d10003004104c1603004001c01c2001000c06442018144280c0000c1030a0500300500c1c3c0e00c1d00781c5044039901c3c0c01e20740682c4005004860313454003080b9400b032a61028400d6040e030707c2903d0742d13000f51090745800c40d100403891300c0c3c40d00007490816203449030149a1a0500c9940c80342c2c2d01011020a12045107c0c42c00c00541d0000642c1c01309a100e050400f0204001c4424072083c0141c0c120203144070740081c00e0100d6901d4028001039512a06880020710594455099205880421040e2000500c0d80c2c4408580c141203885d000100c1000651307960300b090b15054210406103840c1c040d03069541000c2c8545c074a040083c0c030704d641c054184400140d0b62841100d200100503150903004000d00c850a5207500d0b1201165080e217042d40885900401003030401075142812101c501d0f40d00000c8a40c007105140c2d641c0082c000d112004080450080c89132300c8030104030824550004003d04a90100b2130320400d089240c02c0301c0e401c1240e020702550070082003010010807a81 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 902217023 1250 902215773 902215793
    0xc020f0f150c0d111909051c0311010518100b0f09070509090405030a090509010807141504061d30030c0a0f0311060c0f0a0324050a05040209090103 65
    0x10101c00e0b10585802c9006080b001601d1400c400d0361030300c030340002d01c00241298904040001004510f8111802845c04000841400004903000e00300c0c003c180f848800c05004408580b0f152201d20028001c92420091158240c3c540c0e11407c0b04a0182c030140400d00043c078403030410034410040506028036911400d02408483c0102406c0902008112500c109e0340c1d0048182d104906c6840115902c942c2140c00500c00780079a4002c0b0b001b040f2000060014090101c0e8040030380c2c0458004402c3c24030b0301c00c00500d4184402021144455001030041441588018540e0b00018181c80c07030010601c1031030a000e4403951a40d154943c2041e8900040202503560030345403032003a6104200e0307080c4601c4200d582c0c2041440b04c0120743c00c01c00c001c04401099084800078410b000090050081031030701502c141498400d001e420720100500003040c070800340c02a80079030381c40e4042d00114486224800d001540e01d050034051140700d0000c02e800000c80d45000e00032103007592409400740da426442d60790385100b12 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 902218273 1250 902217023 902217031
    0x1c021e09072307030c1e0203100603020303161b0f080c0a060e090702010204180e0f060402030706030b01140f120c1c0f0e01150e1f141f02010c020f0f15 67
    0x16a241215002c5401e000070300040340b80a00140006d5101481054901407041914400b00741c2420010400741e60b002c0240e540c1000140d080071102c11003460240301c40c4000900e5640741200840012910304544082e500035a0261801c0701d400102d44400c00110b11600d202c2e42c40020b40d00500b8080741c2c1040407000d600700704103000143c1056217813100302d00440045406000701075a02c60b00d0f001c0b01d24041100a250321032030009440300d400c00360082038507909140101800d158850100820302d900c118180b42110200b407000d2070f120b120f10403c4808907880785d90768150100d83c8202007411128920100c45041030711400000521150341580000791000d4203010110300d64441c86001201c0082c01600e00d0034a46007490351919050503402c54006d10b000d4044044111b001011a00743d28100c00c1507802c3d203480c9070401030480880400909100c500d1548040009000c2a200103e190150004140e20100b5020b6076032194848c02082e0382c60200c0451104076910a225854000d40c43c0c201c46070300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 902219523 1250 902218273 902218277
    0xa020d02041a04050a0903030f152606070c02041b020d110708070f0305060c04050303040314011517070608041a04031106010e10051e1c021e0907230703 67
    0xc041c84110000e01151401c0742c8568245e51140100803c1583c184240380c0000c260840070000c40219007c0e0f60100405070041d013002424081f030601021010503410110007054104895152801c50401000d0b000d410404034005c9d42081c6e0750001d07110a4507040150703108070340d00501820821510803103101341941d20307079a85400f800402059142c41440003102178441d19100300e40c2c25103180f8220385820320040001d9000c0c1010f20041c0304580d004411141102d400040c00c0c68640444004240100514802c91501818480c0002100d0384064460003407000440d041c1d41c0744c55603c02041d13030911400c44004001c01d440118044151140e81ca40c15045030080c50072036540583e941c80701c1c2c5007000a0700080c07041e00c110001c020480d02e8241214018007025540808441c010031340c0c6d1410300c802e0f101228800c491444c80100455003400c0c42010040e0000c000604d40c0035400c0d0303941405100c490541780291420400299507c0c083d03034500c0f41d00c803022818410009480c00480c800c6402614040342 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 902220773 1250 902219523 902219561
    0xa0e0c060912060a0516080c07081c090b0105120f0705041d06011e0f080a030e01030e0709090209061207030f1b08030309010b010806100809011407050a08090a020d0204 74
    0x440d810401c00344a4130780c1a4000403079040c11072040702844c103450f40e000100100b00f000c103c8880442d00c1a2119a90310074685a00c13250540e41d00130a00c0600c080c00d0801c030745488075100521640703501840c100c600948110b030707401d444840d400d521410a00f850340019444281c040106040c20344c444520050b116840d0305583c00c000d103806040150a9101000200c0340d4580c6a29501080007450000c0c40c02140e10842c440c03619000710f03100c091404003d800d1080020000301315901a401a401c0c0c2c084120039514801d0321140c104c4010664817034142c0c01005140000760031070500c441308013980a040001803080a103142d681c0300f902e14000c403080310111f52040225946404604110010303201c1d5402079600c901d05074a1007402c66059254040c100041c9030107200b4640c40c0d008840085021324070f4904401c7e541c01c6003050162082e04810844a902c0c00200b03c0b0041c0c1c0301d000b0745100d8015a48032142c0e9120f0481003555942d0a10011394400c020310350210041c030f001c1e80240c0400c2c5090304612 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 902222023 1250 902220773 902220799
    0x9060a0506070312150609060f1e050d050a05060306012310090311041419150801090b250c020d0c0f0911191b06020715050a0e0c0609 59
    0x551a50006801200803482c2900305000d440f4803802501703031200d4810781c0112402c0c601440100200d0441c8244e0046c071644502d4000202e00ca09803512813404840c0d8012904903219000601c560b200008100c410781c980800304002e403556019450052000400814140e42412020303140c4c407100440b08001100c1010220040b519a554820944e5115445410380c132461400c0c0015444080100e00c0d00c01c1d07140c550008035240b400042c01d60411076003543e00c40842c1046650038000c040b40b424082d0b18180340c1c0400619480150403e1440c54401d00c62044c0c0f5417603100340e0311481c081800e080e149a0307580000003040b0034480c0c461a1940f41c0010f040030390303414154880c180c000d10300d6001282042d9016005000980c51070003a49010369004021501e000d252051460181c0d00500c02282041480501c188401c00c0c9014010104ca030802070443d40c0e01c84c03d02e89159803081c2d0382d00d4122031504080000d100d61a85100764113050f4403800c0600f0031300940c2c80800c002c0c1e6100c10040c603404100346408c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 902223273 1250 902222023 902222029
    0xf031103120907181503120509030a0c05011e08220b040b0a0b10020604020d03031103070305060f04020a050d0902120d02030903010b2b0510111c021809060a05 70
    0x8280100850b8000e440c43d075050002c18010300c542401e0308030250781400b07034205009100300011030841c2c0d041800e8059468854034211501d03c6442e180c80c0d810300c82c000120050140844210741169003d803910006d80040c040c0c220108006c1c41800c401081103100001d02540c5107513401585070219a4070040d014115603188000d070407007030310151541c441080800003510f031184070340d400355170044801c0f002032a0000002075480400500080c0146207030350a02040600903041204a202030110342a243e240c10100103004080c222000c901c00e03143c0c960800d55506243c402c440c00d80c075440da10189001d4040085201a29822404a0b0045a07101601d010204e0600c1074903e400d881d603010315900ca070381c4410503080d1060b80350741912490302c0c030013885003a03490307807040c0170300b64000e0201c1c44054540c41c00c2440c00c142200c15043c05c000d00b004054030701c0a22a2006144c008040705501c1482c4690312103102c100e010f448200400c0703182c0f9140703130106450a500c80716400800100310130100c50b20340d408 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 902224523 1250 902223273 902223307
    0x7030506060d02041e0e240f120f07120b15120709020714070b03130f050d05090102012d0b040b04060b1207110c06071118010915030f031103 62
    0x21182c6948005d000d07840c00780050130307100802402d001400d80d40c00d0408451407121040942030720701900070300c458454081d80f10b200b103091041340010312072590500c0c50b01410340c031030454025036800741c010701c500440c0380300c0700d0101122041d800c014a59003c0d0707241c0c0c00c003a503d4040300c452164400d01d11280103010703550810050b000761401d45405a2154920b00e80304070000800042d80d1440d810106003031200e003400b20142c1e07500c81c0038000c035401880c00314102059140c01c040f00190143c094100380e500300343e800000504225030281d0080003965a20b5116484441034005041c2400d461000107076120503180e00050700400004000003001300420740020202c6016501c104c14400010039450500711540c088154841100c0c100301e10310307100c1c64084c01c0c2c80740799003100c0f18070030b13440841c0ba8818455580c0150440365005012204482e0841d549600d01d207809100b1000c0035410f10b1081e00240070740c01c40074411268481c4500d8101016550140d401c0e07210300c40305440358030082c0811000d915003408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 902225773 1250 902224523 902224529
    0x6150203074d0a0803120a090c080703080403140a030e01051b1606030c080907060819050405010f060906050f060a0219060c09050a180c121d0c0a0e07030506060d0204 73
    0x20b903642c1c080381d40180301c2164031651014089800c207124888103000103100c0e40354040f10411000401061519100740b612101d42c0210700c4a200761030000c002c0090303c60041003942d006031003c1140e640d000102ca941d403c179a51004001611203048108194003940103400c444070180f041415440d04849282d241003503102c010014001003c8080185541501c15250748200c41d1810f0340345403600b034244681d5080c1c40d200f9241000510400500d49a0070703104003c4450b11040c0040c041d609160070194080d0003d00c0c68044428982540042c000809106007401c07140007510001c1d0040c205c2e000c020403a000100f20744194092050f1541e440703d45421901850b80c4035000005450300c0700d036002020203035181c104a0168004040034080c19086441c0290980d80490b00460346204610040300c998403a441044413040c2003e000301c803001c0c1d0b0300c2d180c0c1032500c4400d411552451110020480c92003154443c0d0360f403400002d000300d403016109401843d88580058406407402520611010403070348268 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 902227023 1250 902225773 902225903
    0x509090d21020a0c0b0c03010b030f0403050403060c020a110919180212070305011109152113060b0f01051207020f0303010308040e0f0603030d020d110d0615020307 72
    0x25074180d040140017410160403003503c2d803a01e42150706018110741588405000c2d1300310715034000001400c242c4a80c017124059940302c07030140070720b40c0f0101e0045d45d168002c401c100c800003201c0701c40c1f2449041818006100d01d89011030345000344d210341020030080c01d4512280d02c6840100080c0d501580300c1c540e110070704000400040200d5451030918500f15a106407102e05d006108100b040c215580f0f15800301c0148110126459541000d07110900c80380e08601541d00800030010f04121054180084c00600345d80903c42c00c4c000009001d0401081401c41286203012980c02c4c000d07041d403108001c2540e030740074480d40100d0b801c1c1200400303403e165800c264002c8030084400503042c0700e003c80540d02d82d44c01c1147d0215170a05404c1410000f03032039000301e070440d510503a40070490320a8100c0c681c020b41b505a03000e0642660307440010302c984c0041c000364047c101010100416090741c451001041303031003158200010f03011b0100c000d02410050109804071582081c03a88400d02d0308041d40040c210342492040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 902228273 1250 902227023 902227037
    0x14010c02030c1e0a1101020f070609290703230f07110904020a0b0f0909090703050c012d050d021c0612080715020403080d05010f0509090d21020a 64
    0x2045024500f000480400c0b24a0f2540040291840c100159002c100c941c004583c088900c90320740100d107080c000318002c2c0841d200312000002e820350000c0d031140a4502a40410005100e50041d40d00484043d824503600c00c042000f110021034410100d00c1c51011007a298941c1d1540e0030016220076410070104903107000030001e40d0204002440c0803412020206807100c2c4072a1425800059041c030301c0388a40c031240b0800050504240c0c01080849000038130081c0903a0310350402c1c4203a5682c0f0519400b0846652042000c56085580210340c02d074121030902c000078404400e0911039034941c500d00360066040c00400d0010000c2a9024005031501219020400a0031405e43d8001c1c02515900d51001c100240f0441c001000b00300b0320030446070079541103008040380750128041a80284901d80c0090076150b03000c5048503d01c405a00000d0494008504852541d0f460304108440c940080c0c40c003629644c881002004d0300380c010810a1103002c811900003030300450001e904002c3e039104400001c001408 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 902229523 1250 902228273 902228287
    0x181a040b1c06050a030f020d021f050304020a082802040f09030c0507150e09060a0f260c0a06080a09060509150124081003050706030c0e040c05040b0714010c0203 71
    0x2480b0b2031008010440d41c24080c0e03807541c0c854440b08001e094019000e00c400140d04419074035035113a550103040303455848070032101030241d004085800a0310224030520700008001020040092441c000c9420b03000b0602c0c0401113580701140c2400316001c120f82080e19400c03410202500d6105100d003882c003c0c0c5800000c010356180c4503003410100c0d04601040801c0507210001f242d40700c45521001042660701514036102d07180015007554050340b160412070706540001c41c902100c0e0420789201e40f0781256440c05006c0c0544069110740f01b5511041e00244108410440d0f00d20407901d454114411070300c0010b040d4080c0d180c003019203008860601d100d42c00003c0081d800d444d00803002e0f005108000b1004c126111072a00c0c0c07010403003288068010003125001190111000c0000c0038001d581c1300c41155100c0d07940d002d01030050540707580d056021401400e50101b4900b898000c88500d901141d94562510b4100700060005403c0b454080d075412a40c3c2c8a640c42c0b0744400d22421614050a800440d01c0d180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 902230773 1250 902229523 902229577
    0xf01110a0f1103041202060c0102220609060516060f051602300306120307030e10020f070306020c0c18010f120f0b0a0b060315010f181a040b 62
    0x1d4003440354800c0101c202c20300c00c00b6400c080140d90a540c010880e0103440c0b2030078000140d141c004c0b100c2080b4a5440002c80c010350f42030701c03240c0c6100003400b40b01c52005140e5500084d604030503a0310500c07008c61020401c074416900c08150b0b094034148240c0e80000c540c422280c004040f034004840e0007800e510b509000420168041000c80c0c06620300720000a48405d00e0101c84c40d0f800080c1154147c0071001001041d1140d60300030b090f28514011200301c0b40c0708d1f1941d0600508001198114901800080081c01d6400d440440c111526001c0b00000b80304d0345181d03a4803880250710110410303070b4034081c2c0700003103041d0341e90a035914100c05002152a011541810000c0411000b1640101811000220b001000414005440689541140110040d036035003410040240c076040d03224550002c0c00108108154036403040913490a0020b984941c0b4111810700c090f00d06a6460300d8030300b520440c60070200400c002c0b510b03621814940010b4601c1c181903036005240714640103100f00c0d00c2c1d080600c800401c101c107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 902232023 1250 902230773 902230787
    0x4230607141f060f050607050118110405010902070b18010b0a17010e0106080a0b07030b27010b03090703170405060c030d15050f091f15080903070210050c0f01110a 72
    0x142c003059080081070300d8010404440a60783c82050f00036000442e0207820b0000c01e41c0651031819a4052150f40115030b482e019400280c082c800600c00e0707180400110f00b6040074425600c640313a0150116106441d401e901d1520300d90051441400c44d9240c5808002c25100ca039101c1e002004100320059a214080c80d1180c2034543c0c450b20886a0fa140c14410020705500042918000350400303112a0b080d00c94078011000741c0804500c141c0c00441200c10008410a03c1403410484a1030100c414204e988901140000d844160350101c45e50348020000c1c800320b20307a05419203540000c110041e2809540b1404505560020b0482c0031060300089580140000c0c0f5000e00e004450581000301e00880c01c15000070b00032511036441c0c601641245001950004510007030318031000da500c010302c1c002941c4520803100d400d40c100b00700c0005503842d0049403026030000250f80c03a990f801041d84a68103404601100c141d00b25410920451285803898440d50b0003c0c4980940c001082511696421308240054416 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 902233273 1250 902232023 902232073
    0x2042a0318050a0b040c08030f0918250201020d050c12010b19031802041b030c090b0d02090d0606060f0e091b0f090a14150423060714 59
    0x1c0401400c100d000a8004100f00c9111903015a02d0222500c4034203290f8a45c01c01354104200601c00064050762098100010b0940075604071240c16030035054550310018980b0a5030165002888541d20440c0030b0400005140f03420201d100050418840400240a40e001a5000490500d00094048100c610128458050080c600e600ba103040805105441254500d46004081640d90101220904001c11503013580325002007081c031600d0100514020020501d000101c042450003607a0b4117410b0061507400210ba100507046800d00d003480144a010b90f11400030f0030707403111a443c90000015202e2040c1c0019010355540c0940140380240044d00d182c10184451b07214003402420003c28608548045010b54031100b106501d4555140c440200e902407a00850380c44100c80700013040d01081c40082115001003107484001100d40001b484080e0700c15401115082040002c2c903080c822140104040b2030b600103800c2d40e2074103210352603020b022807220001504c1c1c0d07004618000c4008a5188500101c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 902234523 1250 902233273 902233301
    0x6110f06271203070507020406241e05161703011502121206122a0a060509150a1806030b010305180a030e031509280b04020d02042a03 59
    0x2030702c80c00d0040c03190f020040480d410003200080f40c0d402c40d10340e03410540062041881c0144002110a8000b00b041013007014180000d500e2200e4005542c09800c0c0220700402036194a8039042c4200d41c2c01c09840c00d034882c1501c0070b14056000243c05000b000003140281000490810074a0101000a042c1003c80700d08612024040c000a000480c07502c86194120701d003200d084140362004e038091803c0c00801d02c0c0c03008171014030041036480046000385003414040111607100040307484900c1900c00d409504030346500103120124951010300240d0050802c1c1c1428140f40c0c50000303202c0f1a80c021046103421040029444440c0c445403560140a4640c01182c0d0840740e107042d5001c410b40c13540c0c1d5421568003408209820b542002c00351810301c1110080040038841001915115010613034a100c00c0100d1002c24070301c42e0700d071210f1520840c448005140d100200c10000d03281c6808000020b0900310040c0e174425034411450002942100c00504060704010380c0310081d4190440c06000c0f0b6240d1440610 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 902235773 1250 902234523 902234533
    0xc09070c030e15091309081605152e0306020a0e03210f0702010311070302070f09020a02070e1f06031e05040213111b0601092406110f0627 61
    0x41c611484405407130f02c4540c103803008003200046004482c080e050b1303060050030124000408000c1d400149014004040c0907604460700088400e0b0410444e034411200990a0300b100c0c540c280c40046d1103c645010745406400c3c50b80070302d84a4481f64100c0c3e019040300b44c0403d41602c4020141d0a040c0a04070103001d074036254001c044042c0c8034090092161482044051000003840011607010313902c413107000702030407a8050b100c1c0c00c2c502d0080e60310f03c1a805452640200c00e4800280070301540211741200c049603018110441c60895641100d081c090140f030300003002580e0100300031061080c10002420150f030081003a072003040c046007504140d80790f20082c103030509007001f016032112444212843c030000c2c030008040b0724030803490044e40154401d05120b0544d21f108854100000900207050742c0d00c42c03c0420904088003490a20030201c541034256401c0308460410000307002d04240780003102ca00c8213884003001d680031118100103049444440206102d00d4000880c0c1002100d044a070400500400c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 902237023 1250 902235773 902235799
    0x70c050c01030203060415030b090c1009090b010e030109060c08060a030215030a0207080301090c1409010c11190b070c0510120506061e070204050709060f0305090c09070c030e 77
    0x56280c1500c02040e074103040e00000401e6a40d22254080104849012035420000c1e07203d1802c20b01504081d926881284a01e00090009107030603440d1001e40c814913256440303518503011450307016000401c002410300107000c201800903107007809440d12140c820a00003d1081c0c1414001c0d240e240080c0c003983c01403104080610058032011f800030791400044001c02d88981d641d80c104c8029200e0008000c004c54008000003070b64514503003150034060040e0b100e02c030202c074101a55120340d000d4000001d0008410320600d001280d95818103111060b004ec200010821141e00030408145403a40304600c01d5100242203002d02840120f8079025100485001000308522403004000c3d2071115480d844041d17580c000305071944c3e11070b821204080d841c00707032010103c0d40c0000700035016088100c1c140c0c045d509003000600498496100b10b426911107450300400b10400003030403002040010f210b8540ca200c0c400b0f1010042c2ea6803507100d4031660882da201602d805052800030681c103e520b03d514000e0343c8003810030b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 902238273 1250 902237023 902237033
    0x11d01050406080a0e030c070f06030203280e030c16080d140a090302150a080a06061d0a092d020c0d050702030309040c05210c030f0711160e070c 64
    0x641c00c0381c40300c0ca8041c040b5150055040b0040201d540952041d10000404001c01e60f00462520119000e02508200c082c3e51032409809a101c101c45404c0c2070b0200110034500d003101d8100c0c075031152031041d400103101c1d14001040e9285600505080c00035a002c281e01d0040702004145d00340c054a0b260018111065207908050000124541c00e941e4403940820758801c501d01c02e602540045800901d441c590f003801c42a030501ca0f034000d00301203000520000004000d00d815018010445000e607880c900590035404003201500c20f4490140d0384031031009400522402180508140b03031200b80c07c82806086040440c040e006c0281c0c0504239040c0c010310000d810000c2c049010b10350015a41442542c0d4400d610000b8118810b004019502500c1d0665540c0c001da841000b0304441c5800846000030000341c4d006010706008100e50101091108000081d003003030031210326541100c1c0a08081d120070b11136103141c904003152500740c081d580c515048100580c911842d01ca580014260a20100e109200d40b0341c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 902239523 1250 902238273 902238277
    0x7150c0c180f09020f0108060607060903081009020c150c0d151d0106020c090a02040b0c0616030204270605030a151404031b030e100c02130b060304120c020603040b06011d0105 77
    0x1117141800301e4078000495075141c0c1c0b002c5170385980e4030800401943c5c0c858078015001c1c80040c0c609100304401c5034000b044803511413084404440e1a0303002059010031000d0300e070405242c003d080c0000c1e4801030141c1d001c0c2e0322031806031742502c08042850402883c14810765180c00641000c800303400e030900600400c0025004038031410002011754003503680b5a03d088445000e03100d40e903c15024107400003950b40f0190f40102c0d040c0d000300919550400417078a80d020031000d90207580140340503181492500951303441941500f444a03031100001003019075543c80042e0800c00110b5081e1103240c0e400041c00d40b01d281500c24003540d640c179007120b0100b90410751001000030400c00030340030000b01c51118810174180542445500064000c01d01854000c00c900d0013019400300281c201d003c1d0025000f59000144c0c0c502448030340d120060a110305694890300c501e0028040043c2d41800d01c03003801555400f40c0c036003d009610550155841c003403030781080800101403000d00407a20000c2d8500e00203600b0640e81c440c0c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 902240773 1250 902239523 902239549
    0xb0603010e040609150b090a15090e0106030f0c0f05040510030312060519061d090615120c0403110301050f131707050d120501030507150c0c180f0902 66
    0x980040241d03520b2428000402c80f514001e840b00100708000d00940c20207801044110700706442c7c0306d60f1a00c4070b0807110140c03240d00500356205492118244481109a03114000f603818032400440c81380da5075181c1d8030012004150135510700c81d190b141405020382402d0f80500038141550200b005141c0050702350906401408000c00f0000a852030381a8031820740c11110140c04000c2516405540022603590403401520404c1e0100f00d180c40e9107100452908010550b402c0050701600c2c656560b041008010a940300941010381c00522040c030f2a1820039035054400c526030010950358a086041044e00d15080a007a03921a07818982000000c00c042c0c200307240c125900b00312040d1740c451507150800c00007c5801d640c43c00c2c4500440c500081c0400000e284010004d00e0b15541ca55600140d150800d07240c090002401582c4802c0c8100041441e04400703440500d22460480e80000e56a034400900b1a1258005080c2c1c440f0360720b200ba000403080c480d00d0300180c1c466008112842459021800c0c10100c64 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 902242023 1250 902240773 902240789
    0x10804120e100509010e060705060c030702070b040b071406160806030708010221180319030e06070908070501021501051e1002070e010e19150803070c0302040f0b060301 74
    0x200c0c0032041030703000e03103100c03124510300030159a00004940360007000b0f9008140b205000400c0c4202d02101c074100075007110001c0e074001001d013a42e66500480340b103d50b440a402d80b411480740ba4000101c0c45050405003000d0489481c206560702c80741c1c1001600090303540c403145241d80006050210465000146082c0b100300350900f000241c6d40e01c40064100ba80c01d5201c11069400060803180f1040000001c2c1c031a5000c00c1490310709a00c03540c0c2164580707211500d10104941c41000340c02c6c07494a02c003030340d11030f500a28580454041e400da00120308101081d146e0710b01182c0300650038050749070f050002c0f10142500f8401130040011294101c1424503040c0301e42801801541c49403040c2420842210380009405032881e8420016284000e50702c084901c180d42501c88510004030f0008162909103024403060041210a4202200c030000141000e103a0781d080750740c0250001030364100600117031482e01c1c02051200c880740c1c9540148000e607107120307100700720303651920740c030780400b07031380e5003090324113440d40340b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 902243273 1250 902242023 902242043
    0xb010609080c12031905031f0302130218040c020d120c1d0d0b01030807050c030c0d0605070e0a090e150903070b0a2c0d0c2310021b0706020309010804 66
    0x9103c45040d1704c9105a03079001d45003410070301203805800c00f004600503402041160841428400c01c3c6044100c107000c001d41c01018401c2021140a607500900000c0010310503900006080800003400c45a00d03178800400360300031120121130305030403a041011701e0007640011701218000010080c4040d500d84200314070400821105421a291020520422035202110322020750b10f0f41000b207103a0b040150100e5091244a40e0740106050110700040c40c80d001901c020b061601c9503445601420000305000e0401040d42d0051303102c7c1d62034481640083c002c0c1d050015114030010b4800b410720040311850018614254140203900e903002084428160304410b1034a416110060250041c149500140c60032642c0702490b030300e0300f0004507254540c04035030104450100301003c0013550380001322100603089440c910075115902480600640010000c001500c00340010519550101d810655038448071651084c0e05003c1c3d04030030080ca0000d00703101e00003542002c0244000070400301004100804030300381 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 902244523 1250 902243273 902243299
    0x9040305161a0f1b0a03020f220f18020708070b04150c031a04200a030b13051005060a0516060906140f0a02090609100806012318010c0c0905040b010609080c 69
    0x481d505231525641c4a2010a0b6a08008810310015020b856040382000d90114400650022500401011a40c038000b01200300b460308031080340207410416051b51403040800c07071403000400081c00341d441980301d03941116a0b001e104000200300d802c2075081c00d06040c50301c040314804100300b0911080441c4112004034805081c4841c0000d046000301c4800c1c4d55100100700c4081c069016080034121020950b10810300d403401e00e59034015a24180c03100c1e4a80964a80140320074200040101549821800d01074170b040854030000c1d466186040d0705035820303a42c5103000010082140665800009841d04091260500c46c20340550b602d005450311603140d5000500106548540c419140c04080081c442c0030110f81c10385015003004800c540c0e150000e500106c540210b140300c0109602c0208107a5800382c1812040808040342c103102845a50510400d070b0700000c00680240c0109014000655000c075031424640303042105442c3c107800000c00d004582c00f05010860000680d83c4515000b1110001c449103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 902245773 1250 902244523 902244527
    0x705090601020727112811031201051207262404030201110a0507020904020d080f1c14040204090f05060901141006020c09040305161a0f1b0a 62
    0x2441d070b0b00801280c01030718a404d202144000c00064002c008410520040e10360b4100100d5501c13540c5c0702c101942d00908180c101d420741c5008513020860545c200b051103103900385401071964100708111807544d0b0304100144a0350800c2440c4408219002005001c07050a02c103071425203035038071013070b450002d8251007041c660200d04018a4003202400350700180350aa04d80c44030300800200712010f60240d800c4c584080a0b02c0d801808580102009550350b41c01e2110990070468410b5000d0010380e40072402d40101d2010501c0c5200070a02050f06000180c0d544082c010b0000c03050650f407500d80c000515200399080e504040c19100780d0300507412500022099943c0ca0400c0440c22140070240c0319100b00d108100170240c0541c45000c8a40d1455840f0600d559200c4283d40002564003c0dc00141c0020b00382c22a40d041400c2d44540080c860b003000c6003000f500000039240b00192640660701861441ca448005c0760440c645150030214807039124540d4946005807000082c458024500c5039840015800001c40c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 902247023 1250 902245773 902245783
    0x20f07020915100e03010e0a0c0611160602030c16050105030606030903160b0a0b030f07030b06271012021e01050d05040b0105091003170f0c0f01050f1008070509060102 74
    0x10041040c25071840b40a030040c07041101c046064046e62030032044900911380010f1088040d81c2c031010340441c042c10864100d504810f032155030300e003610588078445d203204203040f500f8000e00791aa0095441c1d600b00c0e2000b070324103201800300c092821115541031101e0b90307000048941c009002e80b00541d581d142d2081542c60351042c0342c40c095100c40780040c0d030030802c94440c0c070040c02020145424840c100d11001099150720030a0010074807544182c1c000c000080d00c080c2d4095001400900000c2c44c00180d07198590500008031741c07900143c1e0820200207004009640c0c901c007034525258401d0b445419a4045201812403c489001c03490061094003034580c401c004035121203e60031001d10243c205460207826000d000c3c0a61403117169441d001841c551111702007403044a0300203184400b03007800155a0130443d442508801d00c1c02000b08042034180404105005030020160000603031413401440050b8900c0d800341185900070719950040054610024140d0180c038012540c180c815220304005038544 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 902248273 1250 902247023 902247061
    0x170303061e040f06080c0109080c040e0c090901091208160c0816050a02030c0d0c06080601050d1409060a180602090f0907050a02160e130f060609060503010f020f070209 74
    0x11a080507190307210f42d100c0b50040021a103180041340c0290f070b1004015662030003240941e107156448a0150b29040c07405420a8201c81c0000c820303275400d502c0c80f00c042080d42000b202c02032000e80d100c40703180040040c0341c2d45850b0310017011701c0c200718142454000d0003180c800140004041002d140c181c0340070b21104004070f0701007203651340a54014800a280568172050343c25410381c820b0050303074581c00180c02c180c4075588071150700481d000f032a0f90920206640f121000761845040100030310030100000e216100309007501a0004070040303146004034040e4540f0000504040d9002e051140c1c910846000d80403a0000c1d660080c1c0141c1c89100510200d90513555000c90700c0c1d0b1110526003800002c82d00f2600030100d00c0c01e607900380d400c05089032100142412861150700c1c00059004002840308041c02c50980002d84101d0008044400c3c40e00d40c80306030361040e0050701c41c5079661a001c11191078240310700802000b40c12400c0d418214a16407001090042c0302000c0e0107540c1032000160b00c604e00c2010450b01c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 902249523 1250 902248273 902248279
    0x406050a0b18030304170f03030408030415061a0304260f1602041401061704020a050405041a15240a030c020f010908091509090a231807170303061e 65
    0x40311b5540c0e0003103420074886940040c05005880d09200740b51800307c1102c0c0300710342007214140f031502c1e541d44145c000110203000420969032018003081c811a40f50683c82000a50003510b070b1a400d081c107021170203e640d440607500042c0300b404201e105890480035151180c0c54000c0030340e111102c202044c0c0c0742d001d6200009500500c0c182c100c0807694054030390f081c1a0b0700a907880d000c646801002c5000040001c1c0c3c1c010758400101c080400980c40c2c1600101e034424450800742d00e41411a046000d1908015610301c0c5a076445e4800401e0301e401e18903004031a0610f000c02050302440c4c00c1c00310b00014442d44a0305820191940c503800120f44c001c000c40300b51144024002c0104c00d80a0038404030f80e4001303441580c803500c13001c10f00d0800000305006484000d180280380e8001611440c440500030002c01c0205284000009a40d00300d030380141c10741505c0354414040441b510994102e1301410305980360010a4004100540d4140100e000402e03240d0010096821800b600314503810395141e501501070f050f0f8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 902250773 1250 902249523 902249527
    0x150301030b01060305060a0b070803060a030f0b2e0909051e03030901050a02090603060d02190b0301052107141f052205030c041121150406050a0b180303 67
    0x810018801d84050488441e5a4108130390b0701c5020820104032128421003803da02d00780803890104034000c00650304600020300910754103649a1320391200d007040a6050315078004840800050070190804481c1c11090003400210391008242c0c20504090f643c01086090b43c1e44041240800000300b18015038000c41c1704240c011950580280b40c0d4a0303004a40e1148030303500703001c0032a480000da8005c0c3c941c24240208000e0a5541e07010070300c04d0562024405030703804100c44422601d03500c45002000090aa039a40d1260b50758100010f0010000401c0d600c0c1e1554201807094503000d00c80801c1d07007000d071220b81c1c1801c6d401640b050001649603020002c0f0816890340d0304114a60690030100902e444c5032150010340c080840c14002c00c09071682c0c0d2041603055049070607020b04034a016413204500705007402116040104c02150503002c04162040026000012000d00000070b6411400305d1200c40101c1e001d00c003490608021504401c1c9a21501240703400c04502111040054051542c6025010301125 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 902252023 1250 902250773 902250779
    0x120403062f0301091103071733010e060403080313060e07060e030f06090303070c02220b0a09110712020f0615130e0a1202030f0a03091707030e0609150301 68
    0x38840782c0c420310405003164a041c2c4040190000e000603244554213549030024150804120131015010040040c950b242d1074904000e00300c80a0024182801404150209000f0400002508500b08142c50a110f454144001c0000401000440354061140e40602d000d802240c986171010b003000b001c1d2007001e4001e001001c6070240e805401d0510008084003291990524044681d460780f0301515840340702d0300204001070849020300307920400c55102408a50303508640b00d08801400d0901c01618032100c1d102c50802c0c14601c1e00c0000304014001c8402c08000c00328052a20042c1c034420b00500900005595075200c2c40c550092241244000403502552003d20f0b00100f500c0d05607481050b4280b0400c0c443c2c8404c90488003038481e4802280c10300e03000344076904860302d801891001078450081148020445803022400c0f61001d010301c07a503140c030081170015251074455141c43c900107608230150024030000c1e000c41c0d809009019000c1054a003a940d038031101c40441c0051141081144007824000000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 902253273 1250 902252023 902252111
    0x2070f0806040c090207030914130207080309120c15040f02030f0d110c1804080714010506011e0e01081801180b010e010602210d110d06060212040306 66
    0x9544564442c0b10700310f10f5540c0f542515070480c020a0006000624004824004d04207892120544800020700c0c1080a001d000092b000b42da200c0c0d501115900404018490341100c10402c401c1042d1186607581c1c14441000007040e51743c0074400300c5611a0072050082824852a1443c200c2c40c146c024007075680b40c42c0c3c842c41a80c0e48140f00c0c65a00f0000b51038900c1094260b20102d00701c0e404030320060001d11510102807010842c00d501400603113041c40c04003c0480000d1882807400290103500d030000c42c89140c402c0015004200c10022103c40c1d881c0b0960b04c1c8101680840c01150104003420402d00c640c4800310f01401000100c00203c18035840c0200d02c000030031720480c40c11900c51140c00580e070181c1e200e99903004400d000b0712843c40540d00241e1007042091011100b091540d4080b15864201480d15003000d087d90f411150074500d004001540030108551401440c0140080c0e0008003410007030800b08208900c5140f0003d001c059403400b111880101c03140130240141c43d00201b103c04001c0703002035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 902254523 1250 902253273 902253283
    0x302010c181202010e040b0316030302060606031b0c07090e03120c1206061605070f08010f0c21020d0f02090909070503060a0b0315070f09050d0c03110102070f08 71
    0x1406010401c0100724a503800041414101550104221404100c4456005503002010b0a030540c1c1e10549690000e5056101003007a04c3d258102002c4040f481842e5041c0a810410003400c000d0040c40100304020024211083c44a001060905415031382d034440340440f42822565042850700ca8200140c04840c860000003500c1018140a0410455120b01d000c5010b240304a0b05144098074071840040d810380b402c0c0e4080c1004607058503c0e400141c10580e606d6050169a81000031048401c10091041d03c50903c2428003116035180308100d80c04001401038810070301b80a0714421900b900300601b8100102d60151440d03600c4d40041881120402d00e00d100283d0003400710907010308801704c00109401d90014501c81200e102401030310300c0751588082d00010380414002c0310342602c2401c14041e400034034004c03003c1c41040e07a5500c21011110304c1c203006113405c41c25407040e0311031400200f0100200d41058000001c4a52103460340c42d0101403400141e040c0f6170a0340c40300302d16032030800c1d00003202c1102180c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 902255773 1250 902254523 902254541
    0x30307030b0402090a05240307020304030b06040506030c0f01020109300912020108040c1809061a130e07080d0f1b0308060409020a0504230c0406120c09050d030201 72
    0x1001c0c0080c101c010207100c12405021002588840d6850082140d82000c074405805202c040e8140320082282100000f5030350700c00d481c1d540c0143d000040400500002c40e400f01c0d04000e0443c1c1c180858100b41c80040e5659042d10b084920441c2518001c0c1075982c000d50000c40320f594440c05112001040640d5146280240b04640c229096402050500140304403900c50946050000c0211800c0d09278004444840000304220350b4500c1c0d6500114460911900860141202d4070f00840c55101c0d91070200c095400341080f400f00d2483c80845072103550780301d210528041001c3e620024000480c40800d503d407552540c0290100e000301b070a140e81041c0c0c8101680c012100a444013402d1044901c0d8111000c101885c024001501a030040340c038a1629070854000e150008011380c18884d142c20000b42241d0524814506c0701c2d00b6900c903d1100410030035504d9000401c803039400d00385490520003500d001480425844a55620703125004400d00030a140e0000d85405421500c00c801e6a24020b4020700c003000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 902257023 1250 902255773 902255777
    0x714220e1b040e060301140c030a060f08030a0503100e0c0d0516080601050d090b0a230601050913090503030c0705010b040b0a120f080309030a0f0309120c0f020909030307 75
    0x10300000c07050405035251807401580c0c451114901440c2c1441828540c1002d07110344c1e40355488440c1d681c80581b450041c18090440100e040d80e0b00d0402c0c090040403181c2c15400602110f015510070040c124000c8280d5946a00504260340e40350385900300580600c540e41c00c182c05c031003000d400340b260520400010f0003400381c080c90100410344420b41e1504004003002070840001e80000006003541d482140508500391808401140c41881555851080b5000700d845c000c403542d85903030240300146146018198005120310700310170781c2401000200075126101c0c640e030284001d040c10040d210001d511455005030000190ba03146d062a6240e280d0582c00003206031225030070700c0b14450b414036251103403002001004011690b134511713120084100d42030080c01038075080090070b400400300f50908020340c824800d00c00616682ca4007100d01420886041c102441014a000c60388000503c14850780d1020505500b0711010a04091400d5101e00c0e004920003500300c01110144840b01000201843c0148856 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 902258273 1250 902257023 902257049
    0xe13090312020c0703150e0106062a02030a060e120a050d0e0d0c021210020412030305130b04060216050a0b06010e180a1122090c03020909071422 64
    0x75066150980c020360404801c1a0004081080040c1e202c004850030f010140c040880d00e19545074425085641d15480940411018441c00d52844404060900ca031804031703c0301603c50803560007281d500c03114490000e1a080d65060420000c2008100c001030703024024850315074852640d0001807140d0030008111032000e00341003160a20200200d01054084110b645003043c0748440e808201209507200b8034004103000c2c1c0019804a20200d0000b0005809940c1103219104540e01e0000c04540005000e000345d160a07000c1c10b0700040c4013952094004d81c006001580328104400b51110b001c1034100e0050840c0301d40f260030300c10000c203105114070410b400d03221041e520007660b0602c01214545840340301030030442d000040d5000110f42c01120380310034944000d41400310150507070030640b2440f02c28040d01240f030101005644c0304ca020784440d15a00d032509508141d00d08004c100a090050301c03140601c4211890f9200040c0c1010a40380140030b03010420700d0019500741c0804842200d4041c4140d01c400f6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 902259523 1250 902258273 902258297
    0x40f09081318050105031504081303050a02090c030708011a0409020406080a0f060602100f320a090f0204021806190201110a08013c140411040b0a0e130903 68
    0x1592083e0303412543d024000e0440c007201c208698280d030b840100b08940c044000d0000d0711600100141c0c520285108500410030a80c140c01004900c2d000240b49002d0394070104108940164455901411030f10060b0f18211181a031803000c52050240703401c16179131648003041c0080c03e1a071044100b40900c4015800700820907a580c011000c0e00c181e40142c0300980e1003009079a00c0580c49602c0312401c0038000e04009440d00e8690003007902c507940001442d089a180c400b0000c90010800983d40d00420015810450818107a540c995600c80c1c40d07002034403071503001c40d400e01103220540740100d000e140100381e07a984499502500011070790501160006600e460308504c00e40d011002110305811a91310342d522247c0c0f90800d0303090030140e20100141c2144c12015842c024295400308003564880c0381240c0c099050800300c0901441c004190901d214a003806003d00314805018129030070b1703030000d44140f0359030310740b20000f5185040000d102d20f8120403032a90394070f214030907544400f821b20300ca55140e031101d8079 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 902260773 1250 902259523 902259569
    0x150d020d09021f050f0c010608070e040516030f14011503030203190305060904080702150705070e07020c090103110d05100911061809130203060a0b010e01020a0b06040f090813 77
    0x3c403460640110300c0400410140c1d901d00d4026001c41c01808001107080c548034041e05040880d660310520740d001503038042c081004801c0c0103401c01c03007016460203c4840d14607103524048940303000010301928040f450a118200b800e4101069841d1021800c1c00303600d03501d1500035600d5000101110f21303448072a45030704850340302c2e01031503000c1d42e0010000791141d00d641e114102075610402c0100c3e80000c20214080f03015040b007010b41955030280c40a0700099150203c0f0b81aa07000080124003190803050310400240d0b150602c040c1500e4110010089002415022810b440c09040c0080e0440c45020350500145150344c200c0c0110ba4810700f01e44070381c0c0c0310038030a0005a000303e88030060740048014035004141802210554003403650307180c84191209680119090032419140b4003405030729006500c0c01940c01a580380704080080c4010480b81c24191100214444003402d44c3d44110340311802d21071190100e8010b00d19013500141440e95070042d220030b99091508030f01c584401440441c8070241000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 902262023 1250 902260773 902260819
    0x6020f0723010c0e0f0418120e030d03090203190204060506130f06020309210a08040306051803031909050c060f04060207060c030c020d0212070623040f05150d020d0902 74
    0x240d0701904a8544c07101d84410007014222100100701e007d18044003d90200d10b500303000c0e0792650f8075034658500c00d16442051508042c59080807406050624207900c00507200000c04501c03950b0b074030700540940302d842e100090144c101907020940c884008a5400700004000000344200c8209050b10400305c3d603a00300983e00e038002e0800302540266020144071440d030510f03003807181d2083c02078203550802d1190b41d503807009600141c009813011030b0341d0380c00c015200041100480c0f492014000960440c80c1001900080c2c000b4a070469030307032a840d5004202007082c100420f003a549030041001c1c1e2200e40f481404074690300710780f140000501c034405e40081d6190040907148a601c0e010740d140c1e1802440760f005d020903400c00041c00c90700004040c410909441c01071101e0000360000d540c4558049040041c540300458009043c01800c0314100030400c410511801d6804c1181c006440c1800f1122605c000b03080c0e280203071480d82d03200354000201030660039080c3c0d00010205108503840d0700400a99030315000c1032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 902263273 1250 902262023 902262047
    0x1623070e01080705010f0212030106271802160b04050d23040306110c071e0f0f090e120d09020a0803270f0d06060609050907050706020f0723010c 64
    0x164215110602440d44241d107184140c1b030b041c0c0115560804011424221a03200341d02c15030010b4228141e4501c0814411002c945004652555041042c00c0020361094030700d0b40300051250342ea000451800d0028200342500803941c200031240007a01d840d052440e2200c0c06002c0074800919503150010341440e80482c140810f1854114039030415055946207801403001c100d102e90307620760910075603401c801e0130810301e000b611b4080d00c0c401c1100400c0e040d004410340c0c16007006012241105041c45800302c03070a401c0080325008140030030412031104486042001c1801152100703400095400800032458115034100c5100740c0d081200700b03664042c66034a07401b440c902420824110b4100311000d5003140d03001200c0003c01080c0740119510303040020400f00a00380221344c003030f46030300782040b1064010120340300a2005540102403440c0180c002401d6110b0580020421603020070499a5104101c00384c80680d58846100d82603100030952405138803140c0005c00c89190b00344128102824131641c40110b203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 902264523 1250 902263273 902263289
    0x615030411010e04090b04030f110309030c06030c040f0902040509060f06030f07111f0501050f0a121a07120e0304080a0f05120f0304050c040b0105030c1623070e01 72
    0xc1e0140c0c5a004550810f2401411035025858070720120100f1610010715000b0303482500c03407114241c4001d03030250803c10b00b07404074a00ca400500220f0340d1501d01064041c0713035100440700c0c55501e03620481c1008241c01544c20020203502014130128031048154001c005448045500003010f85d21801000480c1181c0451190085404d1011500181c0d0407040035420041c60f080c142c024010044ca081c0c603181060444441c0555201c940e060400c00134860715001d032106442400b8510115000700e50b180c402407040940700921180c0c6030080c0038001c44448141540d10501100b1814052801040c800404070400d80e020b2620800d950303010800003c95085541110103482c2c40d807415140c0100161507040c090f41d003405031404d0b40c502e046003d0001d11460b00e0310164562281040c0c00e045142003141d00301207000d54580b4400d10710b1030b0b800c0001d4a03406004071840903a80c1ca8038440b055411541000001c14074103007200701245800c07007810513034030100d00d01080383e086542d035a44c0c0c4441d040d02071081c551 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 902265773 1250 902264523 902264543
    0x605040501060912061b0f030e0a0c0b0c0c1c20311d0628050406021215041103060a050108060307030f2117152706150304 54
    0x142d036000e20b041c0c090351340c000c40d80010458640030f050302075040080244000194144c80e1076905e00c0d010311868045540c1a0020a0f19001540e50a0003200351806621a070440104014601d0041003014584a00c0054050070381c5c6c0c0340c14062240000d0a207030080340d0300710351052841190203850210f20100b0302c00038080c1d20b6456801d40400c0c0c021882800d02c202e0052440c00035900b60703403503014120700c540c0075184004142405016440c141340c00a00540c0c4001680714484407041d5110320120120038003400006200d07116031511400074400c0445d464100403014040020010304024880c04440701600d0a01c06001c00501400f40e5103c1200d169905c030100d22803d02c001e500c0b441409070b100102400703d644203a2642c07211000c805c54007008807510400340600200c103c01511105c80c841002c0d0801c0780c260343c0000f400030702c00b0400030240c60302e440e58584424869076902965558644981050210051120580d25140c503c1295064061207554224961f80711468003264441d5030001d1040c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 902267023 1250 902265773 902265779
    0x140a0f0b13111509041a03010c1107061d040c020715091d06011808010903030c0e010e010c0203120a02030408010b100c11040f452a0b0d06050405010609 67
    0xc03440304628021a10210020300400503030f0384a5100e1911144580c0c1b2540721484c12500400d07080d00d030b082d0590300c10040140c600a120b071800281400c10364a050600d0720a00481703446103250741d000359940b07070760241c1040142c0304042d4000c10348906a0301210f841d14a80391041400341c8440d080c41c0b241c61500e00d13003200320405100038403400d00d4010071305252011350594029044a00103096401030070302030b59643d001c0010107800d131003840b0391700045040416007022400c00190030084500c20746814423203410012400c6580130300c4490030402880d040c864444207005802992600305019140203986081d030307a110380b0325084240d2003a0340650b0b981c410250109688a1001200c40c3c20000d40042d11210902402c0c40d5a02404814600c2007018508800145081101c692400c03038409407601000030b15001c1e80100d181c01c818000e41c000105d090700b961024542080d20307980c456007407100d00e01000702040010040d401001d050983c04070a1040350703100d40800003240c000f0311440c0c0100c0d9040c8030070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 902268273 1250 902267023 902267029
    0x920180c0a270303051909050a0513110307090e010b040b030601050a1407031d0d0c060e030f240a06051e0103021c0605040e0f19140a0f0b1311 63
    0x406019000c0c509000c60004505000c969502c1960000c4002c00c5003c6140000010840540151950300e4030f042081103180202180b814652401020b00500031480f450311a41c403140c000d0003040c80540c09060307407842d0030103004001c0c401c940120a01225007000001d400d0900406035001e55180b9408a8074544036000103407882e921a22429081c010070048004e07440321104082c1c200b15010b46c6a02403064541c05080d884108a0a0728a00c03910780f402000d00841c80400080080d510181020101da44401002034a000000d44d00f0420f50710500d0462001d0460702d510b81101c00c40d01410200341600c8100504068a1040c02456081800808224200c0d40aa503031380701000d41c103044c014603001c14007100c45140c0040500c90310304a511142c0c108454140f40c401d0f088800ca4003405014145000300400d6260100751000c00c00180c0c0f014148400d2004842c8821140d0007203108948103c012494082880b400160007070b1116080180040c410307880c25800b204406138801100c0d05540081820 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 902269523 1250 902268273 902268287
    0x604020319030912050304060e220213051c020301050705310305060a0606120b030304120203010b0306010e100f140103052206090203010509012c010920180c0a 70
    0x10a070b0801124034030000e07014101c080c41004450040f0003540c1c1c1c40d401c080014000c00302c40b40302c050059461202d16050034040c0e954003000c03441450340269981c11400351704120b01c60580c0145174031a0641d0700340981c8d8040345203020400d6100390001d101c0b6a0f903102c0c01750394a00501c031b6059841301f072079110107403001212a1602200390003901c4101e81c85403281ca540d8903004c3c045035000005036803000248002038001404181415030700c00140412415071001c80d0712402030f441000d4548080322035038002c540e400c0d0002c140d000800381c1160f515695a0791210f565907010b8424840d20b0010a40101d40503001c1901401030310700c541da02c2c00100301c04000460040c0701c0100f0110308061081081c00c8245000c10f242070b40300c2d008040c086080e108900400d4216a80a003482049038500001c9964111141c80f8100103142c0c8554616954246030323440310301401d01c070b8800030440c4480c602a40d1041809000c242c41e041e0041d141000c031101345074503800f442d17141541c204888000520140c03410b50300c1101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 902270773 1250 902269523 902269573
    0xb131107030f1403090a030206062b080f030405071d1006050d0e01050c04031704060804030c06060905010b031501031e020d060b0408011d010501140d080702090f060a0806040203 78
    0x1d0f2202e0903220582840c0f240d60401d4404040d6a00a001c0f01c10915078100400c60300020100c0311041503807240c07a010362860281480d18200c05154030314913024442030b00c080d20204140d021f5441e035280780914044d51503c61500502000d90301c880d48514040c01c0c5101d8603840f40081e45c440d401c0582c100407083d40c460b00b00508400c078898a82d400d60140399000e00800c1c0c01003046208241d140c505524001e02000580c1000071841401880108030b4030341d200060540294141c2010b0000c0f08460030801c0280800303401c0700651900742000060301d90b80c90700c0154410390030741c0d07010030038104140d00440c1914007507080501032040c8104290a60700860740200010f0030310840014106279949010005600503600c01c0403240d64904280e00d180b404103074114216403588000b0401981002518646807559080c03682c080c40348460030204200740c89040b600302940050260342686060f680b402d4905038101d6046026001c600030000e10b58034000381c0e06001c1c1e6801006031040510f42400c029003510501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 902272023 1250 902270773 902270777
    0x2107061d0f1f1d07090b040e06041106160c14040f1814030409050a020a030b0d150203070504120c0f05040c08011401091206230702150612010c030b131107030f 70
    0x6041820f444002c01105000b000403400c0800d08075880740801046034491280c44401c3d07007000e82000005481c100c1e40410000040b641c05454414000c0caa13071841e424120020400c82c8100d9001c145002c005490900c00102282c0c10310205010858100640d201081000005901c1da1342500000d850091b50b0412a0600801ca070709180d42d44c0c140c01c0c1520029a291070a0320f0740061050303d159410f001d00038691400341e40769514140140c0c1d0300d0f4450001c00102c82203156022000c1a90b007445601200c00401e20070310320300c042108070b0030720050b20349443c4288900e11900c00000996410a4041d21119290070307203a010446c1e2030022034001c1050070500090400c4200980420018943c4107905c00303240c0a540005a078031000b000300c07101a1050301401c0d00401d035a608100741c07240d00140101d280f070310000c414074242c2c6034000410311500d0708401c0444154200303c4a071004c00d5069100c1da55440044071420411054802c0040880d6440051103c103000200540c402103806032500d005850118 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 902273273 1250 902272023 902272061
    0x1413050c040c08041403130b0702060904091401050a0b03190204060b0423030a0803060f1f030e011a01050712090906240807022107061d0f1f 62
    0x100c00942118088508007010030920020b120602540e5015035000c0101179009504e00701c00200801070707e40e028499990800000500701046454600030340305003100140040c800d001e110301d00019140050940140c49620300170001c0c1c0d104105000c1c0b4640403101030007a0030a210504088452844400402d9800940b152400554800c400e40240014440300140d86804074201050a03031120306108410320941c000200d0001169041048a42000d400c50b1942c5140b52028080740705d4580710500929681c040f0740b800140d035600340d000341384a000854001c2140c09a040c003a0007481c1490682c0900140b41440780d1b600007181c0c0140b201701074209041c15445140e4454015050b034201b0b0304510031084c0d403000101d91900d03041200c16070305900703400c100c10340e0314107a60000d40d100c26942030105480107010030001c0d6504071008946040d80c00c0102402001008001611000700607402d03c10188105101c0840303403100892180304c04140051503400e1590104028000f0700458071040041044c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 902274523 1250 902273273 902273293
    0x60109051903080c0304180b0306011403100e031804060f121e0f02010905041e020a0903060207200a18050c09030a06050a0510032d02090106170109141305 68
    0xb218091321152021500a5a41d18142803090544880d104034000165003440785100c02039a01041050640703820505000d035083c20384000a04e05004620741951107444d00700c241c908044084014550713042c2e880300115900540c81c0c10f0008807145803149900e8510f916005000d80e00d910340845004d140070702e50124280061900c0d241c80d427940304504480c0350803414031881c02c5580000c01c00c4014882100c0401038040b0301806901d60300120404425043d03400a4000741840c00303114068040e40d04a44115220072540c9051908400c2450040409501c90301e40711000c1d14021681009440e60020340f140f489400503011005040043c04503078030040240049034060300c0410aa465840c012803001c41c41d4103150000340200d5801034649601c0c8031a000c42440410742ea041c5101c5526050081e00d00c002c1d0003800c1c00d03000514120002503008412000000d0602c3c1c0c0044075298081c08660070b1901640d079010350104a41610174070800b0340c4880c0c030001e03070380c6900c002d09048228051000d644005e40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 902275773 1250 902274523 902274533
    0x30a1205040f200108012312010e07090203010302090609090a030305090705090703020d05160518210f010609290a08030c1e19021c06021b06060108060109051903 71
    0x1202c43c407280712080c0c1020004140d903a00003803c50050001072142c050340c05501109444d000c0c09580514012494003110325a003c0095009040c41c42c801001c0e6401640c840300003001950083c40240d100e81c10341c82c08510700303140c100c804c0c034010918480201400745e16990b090b009000020f242c28018080c580c800103640d1940000303248030340308568005980d109031480c4141205c4025064508403100c6c0c400b0103400640000468240605da0031080d0700014032100050701035100d2200c448218040c442ca540131200d0000381c9034126840036802441810703100d0f807208003211992140203501780030034021078481040c4000b9008080c500070305a0b100c900d80341c2101e039140d0351008039081501e500030036103034402d00c089040741c80762101000080c04c000824801d041c42840342844020b403081c045070300f00071f40110030b10380da1090065004a00b50740713850800109811068840e80d6410076802a00001610f41d80b00317408203803040405858140381d0034201824000c0c000d941e400b00c461a8401d80b02c010011403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 902277023 1250 902275773 902275793
    0xf0e0d0c06020705100e0f0f0c011805030313060f0201150506030c190f020708060c1207091e030b071b080f0d02160309080f0309010c0213050901050406050108030a1205040f 76
    0x940400d4080380201041c40b40c03d03e803004000358407095411a010f000580754004c107010885009c00d2070f03c031060640200c2411040d03d4103030300603079042c8400150812856403202c00301088840700d46a40034182c003815400d83c2030303e907112000c4010300207800e424000c5140900c059508000401401e90410095002400c02d2190f00b238445130118031005e03500e80c002070303041001034040d00060300130303180508041000c1071180c0110521500c02c0f410001c0014811442805484000d08042050800c01c0c0210080c0d14000c80c00c0d40001d4440e091150001130b0f849018008204031080c1ca104c81c4003030051507443e5000507400140c00310644940c10024038034101c480d80042e1161058203c8002000305c0d83d4600501040c03000d5011141940100d0710100c1c1c00080441960308440e000e007040120f1055602c001001c0300c08081c116040c940c070302418440036080550005200c2c500c035000400c04e036600c480c1d007580c2d64021070b214000002c0100000100300c046540142e42c00c035116100c005000616999104041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 902278273 1250 902277023 902277043
    0x2503030501030c09020c100e0f0d050a09060516020f210c0a09050919030c12050c120c0d0c0f12170f0601141b0615040f0e0d0c06020705 60
    0x392540d006000b070010440c4640001e00305054114039182285c403040e91590108a608600700d940c07041c01124008060082c00d8050b0003950565040000740700000c2d0140e0056144c450000d040c090300070800798010821111046010144e014616409a0800c229403241810780c3c1e0304069001c003602d000e1083c401c01c20900c641407101a021211540e010310100f00b1716503000307041c2d0303d00301414440e4810010400755039000c201400c00005003428103081c0e4000c12a500001c103080c1d46003600080c07496004002e8100d24107080203a8070403401ca24000d60301401081001c5456400c010507291a8030301420527880e4035482107941c492103c2617a2103200172004c03c4051400481c0100140c40584402c20400f203078001411071108880f4203012000034480c001d945800070107450b00044030280d0310380316000f0401001c514000c4468520b481e1391030649404101c642280210708019680440c3d00380d9000b4855447c460346c0091281c5c00c00031004541c8419010340079100c0380e42c00c21014000c41e500303224103889 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 902279523 1250 902278273 902278277
    0x303040b04052b0b070201020f0a05040602060603070608070e041d0601050306070503011d0601050d09052d061308070c030303020414120a08031e041101020708120304020103022503 79
    0x1a580707410203000340d071a20348043d200c014084001045000419403d0700c903180d50054038800c107175903030310506a00a20812480c141400e201040c04541140c1c054010400c2e91496800d448191b100d40082c1030b0b80d46e85e01c1c00740c3d6001c0351100000510551007034030440420b002c0280046440c250b9a41001452a00c4649404054001070300601c01800c0401000e60407084502d440b0b480c1d50324001d154054100f00592908070800c0b500b01044041e0b209009480c400e030368492041003140e5191400a64800c142ea8400740d0800c07e506102c0401440907115400f8800000c0c068400366940b005540d0713420307c0c0e80c4003c55440b5004d000d81000f0811084003113016610036203005980d1401c040d0306403586070be00e031140351081d44240c400100245000c2149280c0385d0380300b40200d482c0d403a1102c600f82070f152810480800255001c00300070a004078404564958a0213809450240da01d40d041a17403070306001580009100c01c10008600154847da0003003540385d408400d401442e001c6441001c0800d2030449003580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 902280773 1250 902279523 902279527
    0xa0f0305060d0b0c0316020a05030a0f0306050909011a0f010c060c020708030f12060402040311090a0b03010e0c090a180b060402070b07031a09070903020114040e0c0703020c04091a04050c0303040b 86
    0x2400c0500c0346d001100c000c01500042001c0e981c0c960b41c1c583c2c0c0c4c0c490540d41c0300c20460f0601d00b0b24040350081c2c114101502005010403d18540118581c5c000c00404044040b90221480d03090b07800d0400f4030304040141410b035980f00092015807201c8018009816101085129105002529401c00d02c00f4043c41c3c3c0b080503480b96150704116402c44103500c0a0304c2148103600c10041000006d2070795403089000780c0b0a03644101241d03140b038002001884107010064140d42046001d200180c0049036400c124071046889030500e88448000604440c0010141e4004c224038100c0d003008240a82c10450344520020009841c0a4865850600468054074803c011a481c2d04021214020000107400803000c20f980ca60003d203433640000740786810074400039040c441148000c019010741344d012100504214000c0c102c003030800804424565001c58000e03001030154800300300c410300e814000c840c0700d0360f0002d000043d007604040b600a60000060001c9609115058100503503840500242c0001e01e4035848403a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 902282023 1250 902280773 902280781
    0xc010c0f0215010e0f0711070f050406090204050f060c0f0706110d020f060c071401110a12092609030f031c050f0c1b070f050a0b0a0f0305060d0b0c03 66
    0xa440e010404210701c189044990040c4200c0b0513520685030710000c034044c000c526071214281134420340200d08440c0c0303090003a0040440d5400700381c040c5504403002624100010b5540c0e0b04440f0403401903005103a4000c81c414243c841903e0b0060240403441c0c0080d06507500301814907550b5103090b10359441880407075440700310340584140038007034041144410300190201400d5580c1c5a521181d004250a108900214840007404180919603000c160801c4c0204002022100d0168958100302c60f03038000501c10000f00d20038007055000301c1e4521380d849503925044d928903048180701410322007604655403c0034001803020b03940c208040c0c0c094021200c0550f0352110081b1a0100c400200b1121024050a06090004c215822883d031070b03200c0708082c10301d6180d02d001d0342074042640616448500e244151240814603e110f06045403c031038080f81c0c000f904990360707098652240a104800c001041e0009420340e405402500540c0e400100207000c0400100ea07641c50a00416050701c104038846408002c01c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 902283273 1250 902282023 902282027
    0x20102070902190f030c020a0b07020708060a051f1424030a05010303020111070f0809010302072a060c05030307110705030a0308090c0a080a030513051c03030c050405240c010c0f 78
    0x140240d0113501c0c040c4038488480c14040e5440b0702d10803006040c03210ba54006103000c2e05c2401210046d00d02e5000b80c98180c10940d2041000d01001e036102c0039641e61091007007180c5841e80380e00300101c0300506248070b1400402d400b000840041420b40348048640024803c070000300e0355009520844405a000900e541142030083c21100d0200c1d00465243d410010040416089100c50701020341c8500071565038426400100d01a005842008108407140031111007004951700b074002500d6200c407586c0350038a94640045a4900b54490080d100f50070820104141600c664050613034200b8180c11035098503610000b10b464203e20f4074040d4002503250052119044090000200c40c400c00c80d2815901c50a20301d04e00e48460100000800344400001e01610205003180100001d010003805030a180c040c2040103841008101c0c1c00700d001900d801200c0458500803c20340e4141d07903000d041d0641c0c03403082c03000c00700c10384070041000f012542042c818041d01038005d0040780b100205640c0d501100005034180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 902284523 1250 902283273 902283287
    0x905091603030512061e0607050c060c1e0703120e030a170409051803120411030d12051b1c1e061e120f110901090c093002010207090219 60
    0x8414401c170700d0340000c004c540c405031b800340443c0c0c4d00440d80207030754107124a02145004804203040f030300000c01003640503001202084101d42c1c00500c0c0580c41d5081350070207105851300c1c0980001042140004044004c6a115042200c60f07000040c08680001c0601d46903c49125140c1c0166003407800002014410070ba502e000c1c030754010354440e900302e2103000c044c84076940324041c0c840580b0407800e2100c00201030200040c440700b4042d0001d03003030340c0a507821540002d2075640c28030692041300b4204808603414002480c4104000310129602c1400e260000e06030500c0010040040c0e100309440380c40e00c0303515070440c03000304884000588000400c207250586070314000380d01040042c00340400400401c220201d10b1000c070a11944201c002c44403507403a03e0550200c600d4490034a422995040003c02c00e41181e50009003d50b009031159108141c0e40c204030004400500d402d05054480c00340c0e4552100c00054502c0760306807050065580041d10b40c86000202c0e044810f00c88902d40e000d0354180b04917508041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 902285773 1250 902284523 902284531
    0xb0c070c1e090b0d2406030c0e060f03060115270515040b0405041d0f0d08090d02030f0a0320120c041d10120803010906060c0308010905091603030512 66
    0x50700b0f00804441c2030000711001407400c0050b0001c2e00820840380c2e0300840b282c08101c03100520008104081d02d83c100311000714294018020302c0441c000200b45c40d071400701541d43c00c0c258000c00400c4503a00b0031580000c0412004d54110911644203081c0303030000c06a08001004500c86403495a005150a04000c051090503828003034000041100340072800b00641298191041560045010022941d0700c00306400c500c041d24109002e81484111844d501068400c100c0b0107a684200203622294100d075202c00310001d0620143c1c1c400c00100c0c40a000c1c0c0d50140404202078100000c112886c0e6a071f404100b19801d440d400305400004002943d078810040d07258114a201090030300781420141c040c410344c02c00c2400700f000011940b001800380c40f4215808000791000600c0450280c62510700150b00c1d410a0060283c001c1c1001c2c00400c00c01d1064400034040354065880e03010360b910b021007a80080a0281c106070190048250201c5a05100c0d00b11400452082d592203a03120f5000342641680c3c00090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 902287023 1250 902285773 902285789
    0x703081e131b1e0e04050d05090303300a0203060f0d020303120f0714180d050a050714040605270403020c0d0c140a03150213030b040807050f011103040b0c070c1e 71
    0xc4c2488081a40050303061560a540e08149503035040610000b4a075004d074590546032002151244000742c0b8160582003a01600c0340c0c1c500300d0b02c1d01e03220440400c2e80000c88031160402d0154400c034580349486103855000500203003e9030f00e42088081e4004031f0200c201e604500c01c0c444103050140890b0b2044101803070306988000350b41885400c1d0345640020340c10742d40c200c0c800c110f0018000c0500109202d00f12145d6845422101c0107580c40100d885040c0540d01b44a104924050b400212801d080c002020001148c0c19103880801c0c604014082d04a00604158110302c5810084510f948944004014550080e40c80d0f00c3c0852516040c000703000010b030001406442c6034a810000a502c40620b0300b2503030200c100140c1c46101840d4805003260f41640003405d9041e8040a010600c0f084200500b0142e0140782a0750112415481a0742618030000100c046000200b0000e80411290300c0740c2500081e030074203250300c0c0400c80d4079810300703000007904102034008450409024950090200e040200240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 902288273 1250 902287023 902287049
    0x2070203100603170c1608100606030501030f02221103192a1107120b0906130209040204020706020d0c2a0602030c040512030703081e131b1e 62
    0x165180138080d0029180109030000c0032620f202d202d10107108041e5081c90460b24641480d030b039021005d503140340b0b80010110310b518010011580c07074403d00801381a29003080540300e620072a0707801e202c81c1e0921400c980101c5007102c00480b62001d6a4068040c0c1000341710000d6440e8107001201c0c003e24540b0402c80705409140500d4800f040211b44003c80342d02d400390304060072511a01ca8280c5800400004a800b507004040c004240800d090b1040000c486c010b201c42405540c070891903036964441a501d10301444c102165120062816940195002d4400307030025042c00da00d507230f039035082c2c0e003155410078440d6444084074454150300c03502c1d48945440461000841822103541c13a400103414002c09450f880c3c0000000e807076207003039604840090101403c501784200e00d00440b541c40f500300700000c03400541508040340d203000583c1d00074080103003844a08040b5885015103550032212040048900310390400b06070401310240c80101c00103200541401d0501c8900c81d0221202480542280c0b5403100c103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 902289523 1250 902288273 902288279
    0x10b0f070512041a0a17041e0b011701061802090414070302180108150f190807030515040804050105071703090c03071706010509040c090516020d030c1202090402130306020702031006 80
    0x31140d50f0b02c0c420802d500b81c1010580300c900304070030303234a00c0c072a100d24580c5c00100e402e008201d032505050b8100c03a044a81344441e000c082030410309881c11440f51611680e041018212000b400b940140b5010000600008042034840000c540d4410b0407211500820385c0030a45050307c6105c00e046e000c800c00240390a01032031904582032081d080c86085410b01608130716108009a48a00c0c410480c03c8403d9000b00f24030325520841c8503603031400360004682c9402400b44030f040804c0321400f418003035540100c485007040d09003c01140c0b40d4201901c241c620300ac004000a103400c000d60000c3d401440c0400150424a01d140241440c0480d141c3c0a00d84103010203150005010000c91000d0549a0458803c40302e600c65003044c0310416280e4001c058050310705001d05c203180d60f4482c0300c0c070318803440c903002d440c0039080250041c1c0480c1c941c4035000012440d0710000140e443c10790742c005c0c42c0012000740010300b8107800000759680c40003a600211070843d0f001552001f90320381088a840c0d0161055800c0c860141 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 902290773 1250 902289523 902289527
    0x61d03030a0c020d050316030f080601020a02100314150a210204020726030f0708061302030a0e031605070e1b0f0d0c030b10030212010b0f070512041a0a 67
    0x4520498076040101040d86507045503609000031000c55000012640c0b94400200c1a888050a50204402051056041c400000d0080d084148030b44e8050700034240d5980740d5000d00000700c040421040400da03849014001c0c0b4524103c01e20701a5182d6140781c000034801c041404000d0b00d140c0c0080724011803950341d2444100380082c048440342d9040e140981c4a103c10f00d01004841c0056403000ca003000742d86a500030154010014511a504002104415031111001034038078542c180c1e0015005140b99001c6400c0701e10907002103810114038080000c0c0040000e0002d802c540000445200c801b084c40d1020003485000c201e805d0141540d80001203641c03d05981d000c480900c10112446d0814002c40d414060307182820a4035844501c2c0002400344c0040060010001c08601c0ba0040c42900a441000707403141c441c9c0b0079124180804200402140d0078043d92034503c0d0040004013039030600170801030000034010303c5990401c400998001d0380315070070400300b40061284007914030140001400600341241d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 902292023 1250 902290773 902290777
    0x90a0302040b0105120408180625030e0604031b0503030309031207171f0905070e120a1b06090614180a05060a020a060510030c05012016061d0303 64
    0xc0c0d04440c00102a840e0600680b840d000700d03100c1038081c4550381c0802c01132140603001030400b20400c84d01280203c0c80b54042080c0d9004900300c12855661040d15810111443d180301168540a401c10102842c84240000c4040e4001d40045800d041240c80c009681c1001907041e2005c0c04045000d1821440e100150560707a0141480320b40c400b039078590121b0045401142040140d0f00f190984a802c0c0c0b420306907109041d03030507207004081c9054180703000484020500c07595001e02042d41e650b44510082c2c4040020502c40200114401e0107444514400911541008003003071080d00c1d001c200c02d41c41c1c0f5101a10f0303900194070030000d0001c011045e030b9440d042d02d03080300c582e01c11400301501e0b0343d24400c000c549110300e0798103c10b410400014800c0005030b000940c4458452041d0700c184696a54185c417014030804130b11000f044400c0c03402091104c0e6008040149032070078101e428181401425078542c3c60311101c01020524624009003e01c41030b544135061012a252440c130800b00b9055030008603583e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 902293273 1250 902292023 902292029
    0x9140402010f050909040f112215090906151d010b0a0309142a090721050106180e040c050609010207031a0106080f0f04030509130504031e0203090a 65
    0x1110001200081d40618140c44032074a029219021700d240a16012070015039940c0160303000307080035005031050718040c00c0036000c400c05a20852050521b06e185040a030003105004918424032302d0000c14810170710321640401d030340260000300d850919110320f00302024040c4c10401e1a440701c4d00c1161018441140c40c18111160007a03c15942e03600b07100200c004203400d0100912070455031002c41c0c0d5042002802e2040c6604105801a14990b911400c0594a82001015400011180028840600500b2079003621142c00700480d120320304402e0201c1c100c600076044000855068500b8044041c104020400074245407842e40c01c03d030800b6140c4c075005140600c11603100d09000522a289a4400e12040e401103501003110030840e006000c4490303c0c0d580074043c05002907002c3e130010302210305483c40c0764069010244002c0903030300d0f203881c203c0c0c0641c4010000c503000a407507903030040802580c3c8a1244594000e90701e0a44a83d40c00c01e400240d940c103101c190003154001e1002114a9032000d134541c00f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 902294523 1250 902293273 902293277
    0x408090907030e10090c140325030218010306060504020f1b031909080105090309061e041203050306210d1b0b0f180105160c230109020306010914040201 67
    0x3a6910110210043c100b4401d1181282c001c106021003405981d41088002074842d44070351403a251121401040c2410203054185c0c5175101c6c88207212100b02410b90a01d000c840c0141143e041501c1c1e03008180c6c441c201404401c1c8078500c800c01007091001340c5c442c6001030181203500358542000e035014071415005011922188900c0003001e004101c6003002102d030b2801f0300c40d81d50300551440900180054145116906555007001c00142c40244044101c070030501009001e5420607c10701c0080700560001e845c81c10081c2003c00020030703180c21050700780000303d109545581d620300d0008180000752000f8041903610086001012a4440740441c03154414030407440c05a160b070700c0311540306900d40c820420280c114101481032110390228034891512484035000643c8102940501d000e08981d8119050940300550000d00180701d4415a1110780950041085c03525144080e80001210306616000381c64a030b6546000b07404601b410300120303005112200b0104129100c1540350701c9841c81c01040241 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 902295773 1250 902294523 902294539
    0x18060717090106030218131502070c0b04030b0f0c0408010f0c021516110111030f060a2c07050702120106090605060304020a0b0a050d0c0906121b1416080301031a040809 74
    0x1d03020780075082007d0260031070701c0e001c407c0c200d00d9880300c029440300340c043d0f070703990071101c0003003075011040d0101c40441c0d43c07040b03040409580b40c1c0d01c103100e01000500700841201d010000010242401d004800c6041a100400520034035123503070203842c1c803d000302e6518491801d4000c00c103031290180c5d10302c2a40305030f1b8103060540d04c0c1d0001581d4010120000a120a10750103c140b0052940c000d114030300c80d5800b90340031002c464660049a50603030250300c4040c4400d8490004284400001586070f0b0000c09505140c0c0c2032059076030000b4036909280c0140300399a0754680382002803c4150040b0300040209a45692850605801080b840364041c010341030501000502200524440c070200d445d8021121010400440c103517000818205040c421100011000343d0604c007294250701c101c220121140e1940340c40c000e0010070503203a142c074550082c5a121030030302c0040c01038a051140811881d10a5074131680d0303581075207400188400e8804a0480303400b440e400f0400002d8207941294001441126010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 902297023 1250 902295773 902295781
    0xd0b09041502161506060809372001030b0d020105030a0203060a0e0702030d0b01320c0d021e07050307090207050a140a020306060f0a06030518060717090106030218 72
    0x1c0c5503011071010040500b580007500400c81303007155001e1800d0390041d82e0f8070071441d126101c00c550340b81c0d141c4900c280c00660100100803a01c5500c40e200841c5280c9486111140255844020f1840d800c6801070082020110b1903c190350307418866804200000c070f4101c01d860466400003052030000401c9011240d038000042025907603800191300007404441c2d00202c0520f80140d0007500e035041001c0c0a80e01c0c50800f040c404096008d0450040e0074400c0b0030302280da00410901c0740d0201d020a40c5c242c0e100d80000c201c1c000a00d4030601100084070001d400429080d44130441c1232454880914150346a50441c0d202801030356000b1400e031049492a10000d622080c26040c40783c10f240a420380100720b8041c0700e42e2000c10a00114620000d03500171400e540f00e0703584840501031082801d010103a0b01401c000c1b020302101d400b0740d0119401c0000440812184000c84441c0c52601c08250b44c100c01103003810703034440c10300f0408007540b5500122050003481605c0c510703404241d4180344d030705510040c402d410b4009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 902298273 1250 902297023 902297047
    0x1909081b1203070f0605070e06070602030703110a020c090901051b0f090d06050609090f071505040915030b220f14150618040f0201030209011404030501020d0b09041502 74
    0x30565910032003040d41c0c3d0b1201586404504c84840c0e610071140c117070a00000035840c900940003180711050140c207240c40d0a14594a9000a5200518032428181d4070482c12101d07201c1840a0204500305400034240300c120751003003140d00d900c02402e0200a80c100340400803c130007154020301200d0350b511006621484404604207007401201240e54001e40000d038900700f44413031600100e00074241503807214407544582c0c060726228400d0b640c2d42540d650000c1030412896924112500780080725140040c1015121000c1009680d18450204c1c0c441609044c00c0c8203002c0c0700d40441c0d400000d003202240c0c4d540c8051580d079180703504208014001c0300c50790b0050070500c0061503407548404080e0040c0c42060819101c0120414010390391f050190b801c03c01c10b1504900b46a00c290700442d0003400f010700500c1140d0044010394401d400c980d04124100310f46a114bc482c031009000550710650000d82c85541a0404200701c032035403203a56110316081800c1c800403a2001210a515076130400004d646c0b0440380000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 902299523 1250 902298273 902298289
    0x260c120c0c0d081b010b1c0335041208070804030219060608030c010e010b0301110417010b0a06081e0415151a0d060509011a0904201909081b 62
    0x2e411000b20115030304e00d4060011760050618581c2241c680303841e20301416045441100c51f00004001c103120000c0c401e5900c0710f0516000380820342407040381c0c0b0344080048070703080003170143d070100c03201040001c0380003205412030031103584001c0519003d10103141c1500c0003035403061b135903c000200c1300440c603c400901490f42c11001c0a80056000c0340d03039900550345180e0003050ba092140ca419441d02400d4541443e06005441300803070454a801d0034181407400000000480c5400700341c4a40d47c480c8c00b0740550301e410342040014182600c588056280c03844c9002d52040d0f03110b408460f140c1d511010000050b51020141000728031a41c4005031003861a0114240c195484d0010000c402909540802c0b45014500820b90358800f00400d200c403550701c10070701c9402e00e02070040c20b5540d09404603811013820f1031300107018070400042010446101034a0003420040c002c800807142c140e400524498901c0282110640c2c2588500d0058002071a20a1103525220400181501618101c0c00e001207030382d0b0780071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 902300773 1250 902299523 902299537
    0x130807050316050a05060108030a09061809110315061c05090709060f030201021c021e0c090106050c0c010212090f151918081504260c120c0c0d08 64
    0x420b018000c0702d4100103960341d2414500300c5072031145800200300340304040306039103420741d413520360280e0b00d420000191400c00c425904140f15180e0504002380201e8640100140110a2802c5c01d03640e040222801e04010500031503d07014800400c01256900024a036120030750a414900003080e440741d80c46281003010350b610900400f0704140313001c40e41c1d0805510784030840b8030036021100303482e003c802803020030703002c400880c005a04024000521098265071244041080030140d526141c07103440024010312080c0c01200020740082a008041d1004010740c0408040074001003030602c5611103540c40c184510304141c1d0051240c0b9204d0b25450700c0707a0008403961149481841e403646005640313a0803000007248140e000600d0010848030180120302e60000742d85821000d8081c000209a102c541c190004d40101d0b251504060b44502c035201e501c040000005604190790380e11340e50800b025280103081d6446030f80c0d5003c01c1042910f8a100000c070210180c2c000d90340b2000e0782c00c90741444146070103006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 902302023 1250 902300773 902300797
    0x4150e06070801062006060d1401110d1a030a0311120318060117060106050f091207080c040c0912170313020a1202030a03081f0b0c010c081308070503 66
    0x603060001558110310680c0c107849945da1141c805506045d404261902011100c0b50141c100f00c020401a0070719940c0c1c0d0036503c1c05120010b2001080150f95421110700424256001c20b0218070380b02c0c0e800042c0941c20360f000c0440300c510986115640000c0d16031100000040610100e000140c2c1440005c0c081030599000b5685140c1d0cc0b0314000072402641da050049018443c02a0f400201d48251440028124003e0726001484140c2c204107045d40c0a52082c40b429404900a0040305403d54074413080c42441c00c0c0502c00703000003900d8543e00354a015462400d662245051405082d1603a50040c8018100e46a010303c11a1071001d03814081041d03081000d0660903885d000003040680316115002e4543e0034400d98aa00d4030315600d0b4010451400b40c0c00009516170001040440400e100d001265000745506204038082c50402c010720800b500c00c0c1d4884114241c011919114080e828071581001010505020010780b4221040380e450f00310403980100846000700e010800c0c00340c20015203d07400030322 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 902303273 1250 902302023 902302033
    0xc07140d0828051518010302041b0512060f0a06170a020a0c1b052124061003060b040909140307170a02010b0415090c0e09070c0f020306390304150e 65
    0x3100f4070509007007d000580c0034900708145801d2505414030380741c9400c134440c0d07900f6091914440071002003200260041d03600101041c5a84660341e00c1406100051074651a0040210b0200e420703010f84040c01042c0da07080510500100700c0030fa40100709400660f500c0b4820865003000d601400c0303061170041c2c200c150081084042d4090114401100c1c09428100404440c440e90b511b1150322401e0384118036101c1d10502500c04500e0380c0c1441030203940605120304010680e551200d81034256500142c5c07180e4140380c2c4511251007171194003030840ca100131a20f03026500e010036580f658450306911083d8500c204200060280b50076200f94000306070202c00034818804080360745900706501c8500e000d5030b40c80130310701240700304290b0180c001038141c1d070703c05481c3c00015503440c2c0c01980d200404c00c0040e08c10000303900035900103990601017507110700d078241e003c2c8004004040113562184124a180d80d5030020805041c0d40c040b0703035801507d62060b40f00300701155078801040b8103006040d019440e9549885a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 902304523 1250 902303273 902303299
    0x210093506150307120f02120a0f05061f120219080703060b0901050105071a07110105040b0a0c080405070e3102010e0612040602030c07140d08280515 66
    0x70300100010b030000480450381002e85403d80355851500640700100004490f203007000040c00e200d0f0001c581549030030299421010140c0700d881c22a40b442608469540148040100320b55511100d80c62060030364241d00716543c200410b0400748030441c040a032090204a65411000011b002800301420960090710300203a070703a107058000380c007a0202051044900c1c0300042955403180050300e04294100c01d0801d00010401e81d00c00704401c01070240c00411a000c40021382c0001e0074024180280e110b94008a050700d480c0b03a21804480c2038205500030420500103001c0401d4000800206940c0b4040ca03500e1a5120700d849803d00c0000750250f0001c8144c000c42882e4181000154811658001c1e02c0d80040380c0340b03e4081040307034403487c03103e417446440c400007150100c1c10650246600640050800e0300d0801345459148203400f605611800c25405507406680301c59100f12280d41000c0e4121411006000159400c140d1081c3c60380400c0c40c0c80e5580380000c407200d000b954003818007a009001c1c4038540d14 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 902305773 1250 902304523 902304541
    0x6041704030507080d17090a03030b0102010209031f06120b18280c05090606040303034206021c08060a051009090e0d020307030c08040b040b070210093506 68
    0xe250aa88006c02e103d15601c146c0c41c582d25901601c101c07011405450070b0b0400e0341d1700341c00070321303112100300d04541d030a0081d5251600c0401c00705411840181440750001e1302142d114050b24156007048030610032107a003100015a0040041c2d80100510100520403081c2c071081a18021015092001c0f80e0355400c0b6209800b44062102c032850760064007030030105070300c4409110030700703c1c00c2d2a0a5000401040100702080c425400455030509070804010740062800204129040030b41030411100d150a92006900011140d00e10080c89103001610015038222406010b900020f460117041c85811300000b0344507681c00207488040e000c0200180c1d0b00c00e030f44000c000c0c40350441740250408245080e103045a1504006000500142187d004510f406015603045601600010b82120000e4050102103007070700e00f0102070000b90206c28006502c41406004000d0170340d05801c0c3c00c0b014072540d070a080c001c101314006841718050b014903030341d090088130703000101c10b4241b8068004242d01a00090104180c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 902307023 1250 902305773 902305783
    0x615140d021c0e100510051003060b0301030507051003060e0609090a0f140f0f030327150a0606030e0c060a1205040c05030c061804091a04050705150c0604170403050708 74
    0x50b03d072104071024a001c150b444401c0320030988249500f50b030070480c20072180c42d10000f6010112028070700441c1180d560718090b103558200f81c100304c4054228030400d01c464201000c0b02841000c4619041c44494500114007921038409824540607003605d8cc001070000f01d0800190070040d80c441c0300040240b1040c01d1444291820064200040c055400030b00068800003070015208071032540554615101c4124000030141c0c15601802c192403100301c901c2e55614280141030004402c081c2d45129031600f01d590030100c482c0c0e5040081414600524101030080024460000c13181c10780f1280e640e00c0c0149010313a06050f4085e040c00c0f101e42031504000400015040480440d10260116101038544800300000e0380542118181c0c4664105412a624035054018185880c0210604410320302860b460344400b15003250b00380d80651180340308100d68180040d07a1507262801d0349429042c40b00d00c0c89901d450302030262015121841a03001083c20000030021200250b9022040750103481c0c3d640350b031503129 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 902308273 1250 902307023 902307041
    0x91e01411c1a04021e03040507050a0f030606050a03150c030f0e1e03070f03030c0c20030708010e031e04090c0903060b0409020f0105130314100615140d021c 69
    0x50300145952150f401c0c603009880651034054101440c0d80c109010110f82d6400062040c7c03041d00c180c41c40095a0340340c0b1170326880038111550943e07412905604207403007510202d41c4003600540c1c0c00b080070804107000005041d0010b0181c03c0209c0c1440700c00c001100034102d480048589186441c200d0154000700040c0419800c62070403814551510075100c69072a406810300181c040400c142c0c03841e001a210790700c01503000105040603403003800356495a030b2041c800c01700600d0071000c02100d10f291034035081100c400209400c400922100c61162059a12070164000311030010710b940c40c1000102ca00c40007a240501803080041000e4810880b00811181942c4029122a0b25141c2d00344080d003003500482c54a141c018006129000320040115042c1e80460381010303480e510002c020000642030300c4c82042d640030fa01d004110110481d0241030440381a0740c05040611507182c0c0354070096400c800306070401003040e0391464560361341c0e000039000383c8a18120541140240708201c0c01000c40b40d480300c544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 902309523 1250 902308273 902308301
    0x807050a0e0a1e1508041b080a080301090528110903010f050103120c020a060c03030b030d030507111605010507050a0b010b040e060303130e090102091e01411c 70
    0x399603584d1402c08003421914000400040d4103c001a0208452840c00114200e04400300c845095a4404043c141280c02404031421a4000010000142d00e80256034000300802040c001442c564940c0c240102c200e4948801079988401800744000c071041c2c2900c4510a0190007800307118401d200d8000144024002110310000501c0a041c900d4440e00e0348904040c3d02130080c0d1042410000b09a902c0c10501000702d08054603020f03ca070304da0310103000c6910081403a4a0105040c1480c1d003000d07004401040070049554030844140740d0340d4020030040c004a620a00b000c50307441180c0e05101e401c0c0820b0303400c041d003106d020900020f5800c0215006000f281c0fa05501344030b00391038031010544c0764801c08000414103034a580040c000341d6105014260051105800145440c142002003140c400380c5040c004200d115829582c4c1c255600700703601400321030307819800d650310344074440466840f24080310076507401511080150100c6201d40b03044a940107015a401000c150312000c2c0d12001d04052100307003038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 902310773 1250 902309523 902309579
    0x11070b04060c051e251a1815061801030321020a020303040201030b120109050c030111030115050a02100e0f0706020303010605090d06090f051b09070807050a0e0a 71
    0x9a4074032403c20358854a10305a8003100f8460005072500035034000c0002074907080f84882801500c2211500c18035005446070042e0490391040461302041d000c1c00800210f548541203030a00c000d8040442d01006202e900303214902d6684a42000c61030071030203400c0e03d00e0000c2080002006250700002101c10b606a440010f410500800c050301c000d13400f80800c1c01015a205001090066000c0d402c10301e04001d000c0c240c0d0041205000c40f081c01c1d500180819651604101c42c0805141420b0180784900340742c0380d940c0d500c0c551421110b00014284113141c5c0041241c0071031284401c0e8424401402c40403020a42070108501d040c46594940d1315400350305e880e91144440000c0c4480c00801500e040f6102c44e00c43c0c0d410720f02c58105100b60b1800340c0c0003c58080380e071441058005014260003d00c001e0146008004103c086207503c801012006074243c807480740c41d010488070f07641c4400c0184e4410400d250650b114590034106a4080110030200c65000380c40d8603002c00c940128004a001034417160100381 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 902312023 1250 902310773 902310791
    0xe0313081c050403061d030f2703031204032105013204020a18060f1101110d0b030a0c0602030c071e0501050c03120106050324030a110411070b0406 65
    0x10001c01c8900541011401c00c1c4410804650781e44e01c00707607410303480f00c0c400082864412070942c1582c1c030039180c03941080c50104245100f41c040300718980c440070398409440003004902000980e40e01a500c0d0403400800c1a20005040500c503002a0381c2c60101c07120f820807031151040400016050134024041a0310344e103175184411541d5048041104503d6403080040c4490b00c80a002c040e611903d16041804203003500501c3c0d500c00c24540e035004004540e181c0d00c211549000040030b00c20b000215000c0340e810701c9040c424005146c41110444080c82c0800100c0607801d4020070309111200704c4c0a0031a80d00400d0000b00703582c02100030502d2440c010103440d1610340350038140420003820080b11001d005aa142400654000d0006040d115002c0c01100c0c104a403030324454401d01c40903081400000c0010040c084215503000b1600c0349180391190101d000c1c49800b0120f560364002000203401508080d20040e00d40e1076550010301c0021345102100d5031503002d41890300032400c080c0c40440d0030b589895120 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 902313273 1250 902312023 902312053
    0x9020403200d020f12070e0405060702010507021507050a0e0612160309111926011104030506070305061f0518010c020603160210020412021009061b05010e031308 71
    0x75080d0aa0700622420842003030704c081c00102c1040f0172640b02d20b44120a80441c403c1352440440d442940b2078401001c45140464009003510400b0b031000055602038030400c0c800c2c6800c2c1110342c1e0f111090f0314001d5260f5403403100840303401d40340e40769003a040480007504071900343c0c0c0f82907900c0c0301d8858107007058014100241e04508170740c4d040c580030301520055221007000f442c01110780f850900c020710904034501e480e020b01c44423000030307000c482e46000304090000e16030440c2800780c221801410700145041c5480d613154140c64000007080501055a50400245956502200001110007651090045038090540607000b5031001ca140900704143c200c80c046a58499009002c007e540940558296120700792511504c4d0a101c0d0104198020341100710102c03001032000d0001051145001d00302ca161300d00602c010b940f00080302d00304014810505000e41d58100c6d11050401031044d8000b03a9a0b01181026030040007010041c8126000024409501c46403c10242c025100450300f658a292003003550 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 902314523 1250 902313273 902313289
    0x702011406030a0b041506150f02030f030106050306011e030209181612020d110304021905091503070b0a080105100e18040303140703020c0708070f0b130902040320 72
    0x103010b40c903500c81003d4600240c0501c44040e045841610b988103461207003003031081940c80c0c41e08038280340c008020514240c1d41e806100d25910300000c1c00034500e81040d0051081c0c0a1005000c1c510900c51f0000204506900c144001c00780030002455409041200460090180d440310318010b11407615811180400c100c14179000380100c0304000d450003110b00c1383c0c0301520012040303000b0b031001c00c0e400c5c00302c0195102c0c14042c402e40b400071a03024590700e00d0284100310722407400c00141c2000b200d4542050005896044900340c02901d0200d40c6000620003d0000e8a000481d401a1340701801c0800c801100a400c026401d06840044413070302c4110a140350120383d4615484907050b4000c4040c9044403500c80c0c80001d050300715000e860085121140d0a42940741004142d0b000000039500180001011b17509024803400b41c60700d90007508001c0e01e030051409001ca0640200314411000144107070840380300100e588000e0622001c1551910740e60304000d003403003030b8454207081e80d014042580072491800145d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 902315773 1250 902314523 902314531
    0x6060611030f0a20060103050705010f030207050c12010e010213140102061b090609060a0c02010206060102070f181d0708120f070b101805040614090d0e130c0807020114 74
    0xb095080115461040b07480443c070340031041c064807142018031051181488650b01a500172070060881514010004082c161702c08001020907105000c0e013800104040b403a00c8105004440300c240b9101d11a210500404045801402c02d40c030004640d142e510310010610129240742c00c2c43c40144508000680e29200c040303849009941020004038000d1350842c01800200401500041c108030103000801c500b540040507180204507041c01200c115070341040f005030f02076002e1002c0d00c1442d242c1000c2110f028290700074a0880c0103e0a018a80000d5a82c03110018104000100c0b80e45560002c94540301c6c49180200c0e40607004111503c0310110b2480200c03803003d051020540c1c90310181d5100c007002c45501074039150002421400004d44091490b8100c00c0307007003084400007039600305071030700c00f0403186010040185c40e5202d2080006040c00890b11810b010180d0600544004109001071240d0340f002c00500d00b02480c003103d140141e64000910b40c4500d440d0f4008010480c80001c4990320240112 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 902317023 1250 902315773 902315797
    0x105150d1802060d090c0801020a0906031a0414011e060e0111150a15050a050d081e030c030f0702010e0c0f041121180604140a020d0606061103 63
    0xc140c0000d9881e441030220284407450040040d03001e500041241e07002c0550186443e4035510320313030300340211080094003c007443c1c00210301d0040c42c100b0141c0058440d205100038595601e0300480079480a04100350b0801c0c1c010810080c0000e8010000090302c4280120181c00c2041c1101028101040c820401545c84648822191500100c0111842c90b407001440078175010310050304044000d00690980900701e01140892103140d0780c854082c0741580c9a1186114064034803081145868070703000e0b00c003240c2d00a20b0b0183c2d2281e400c140511103540202e0581440c0346c00004210690354010701840c01204141c400c100f81c0e45036044101d084e0342550301c40000c550001502d1007018548107501d002e0225020704007060303507581c0710100342c041e80042c80751000c01e40c244008216415000460113901c8000c0d000e00030101031011081e25500d0200130001010844400c0038021034100c1008100c404a60007050a4055078139464017001030111072050300d01141002ca402d2024207804000e941c40641c0503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 902318273 1250 902317023 902317027
    0xc030c060f021e1903021c0918020405090105090606131d070c020a0504050a06090219080f010f03120507020303031509010f0806041b030c09052205031606110c010b09010515 76
    0x440d401300c0d034807044141c00300c0c2988190501c60f0240b0200104914074180c80d51122241c15280904001c0f900008441450f0490302c1004248a43d0ba074040045066850555904d1590b6a444011035601c2c0b0030401c7c10410341c3c081140000d070742980241c60701c1d101110000b544589890b440d1040d1030345102104005d40c4107040c841e0502042c02c01d507104551025003040e001c5401035841c01c11b40102c0e072140d20307249003d034540515201c82c0c50b04410481d81100c21510340d080386624100007a6481603140c000106041c0c51403040f01c00d03252181c0265410190010140e0b603490410a404001203842c99500f81d006031129000014100d0050484a00321402c2c0f4001e0f100540e900d0381d1794100940845030181980d90984004000302e5501c0420502500c2c10034800221420310020009408140009440411001d01031103400242c000c01954803115a4011402000c0a42d00d000340c080e040a02c00c0804425020884c4180c0e020150800e031a00d403800d496810072641c0b00c10074004204a050545017200c002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 902319523 1250 902318273 902318293
    0x50a03030b0406150903020315011212031407030509070e1501080a060f030b040605012405130506191b0201020c010c0f020a150206060d120c0c030c060f021e 69
    0x2a42107505840e000034000150315031151400850407444c00014800211104014400c60604000c0d1100800210303242008a6240400003100d5203410080201030744403100d62001d01e0381c02900004564010101d00c94100e1074210801401808101d0b854546446100c60005100f0f801c0c0640320300030540d481d4034040c811030000054031071107000f07071840200c5139607088001060078810304110091403065106078983c0c141402c12800781c44040e001036000380c200b100038007612417401c101c1c0f40780a142c0e42004e580f030300b204003000f0a208000c0e52101da01b021000922402091200c100881586199142c445002c540380d5603041107902003c4000b8003507032000004c64101d6024900b080449841042c084040c0c0d91a580840d9540a55501031803103200340315034141c0c00b20340510003154800310560740030022601341d440b21b51020100c0d001010038004041c40303580c11f00002d080c1000c09944c11003180b005540c0c6c1c40c0b00080010403200c1502006004084a407904010b480d0001c0d10805903038070081c171200031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 902320773 1250 902319523 902319527
    0x60905060913140610450803130b030408030f041401180201080c0c0d0e060d11130b04080a031b021914010212041806030803280603050a03 61
    0x110081c580c6521a60642c00d41c0407070080390141c3c0008030041144a2030b1030800760240140caa56210b60321041c004070701c4840030255446030411a4030624402c3c3c80c0c4800920110071002e080066000148001080d134010820314000030040003000c420400450740740340c0e21042c820141c00706483c000c00081080004c5011610440d1403075400c58024540b448860244402007421185c84154081981803800b226809560300700d090194031440389041c2c9031904090314142a140c1c007071181c40c60180702500860720700640350002551802402640c003002603032401c8120580c250011601d0207004000e00310f0110ba403941c3d0400761000c4855042c002e00c1d42050503078082d500212442c1800c46078158588001c80035903964001d1503540000b2440081c809420038045144c55403410000d07a06540c8100f02c040f04540510b02154100e503580c210601c8460000104080a03020356440070b0f105040100034040301004904403c6400d118903050f1030b03140c42180310707910f0699140784406402600502c0e110000f1074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 902322023 1250 902320773 902320777
    0x180605130e030f0406090f0b0f0316021603080309010c09050a0b090609130c081b070b060310020a08070e040b0904082a0f1203060307061809020f19030606090506 71
    0x140103203050720705003443c1228002c002c1d0400e510034400904644800c01010b80c43c220341c0c0d0090541c1141c4d0624050002c1c05400f060b1101404e440e2401455501d000d51480c402d000703503902d40321340210398101d070350b038034104045150001d0340c82501c06d500c0e203012208658020150141220009400135800d076240412120464101c42005074000204001010160b40e9520541d808440003e00014803200d030074074000e00c140c00041c00c1900241c60318007594207410002060340c4a803903222005280c1503a52002181c02c24036602000c0c80d1302070011540380d0030a0742111585200d5084d030303600d8200f512142030800082e00d51141074907800a03060b00106000ca021600108404119403171055480c0240c000d8612000c2c82d038034400405030f0407501010044110a1100300c0490108840060031400c00300002512001c051191600340060303040310f00c02942c414106800104200c5c44115142c1003402407500d0103501244030400d5162032a48042e900501a10940064074170303564a01c481d035030802c8180000380e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 902323273 1250 902322023 902322041
    0x606020d08071e0f021014060d0519030e19150f0c1a09120705061614210601110c04051b04140a080312040201030f0914060118060513 59
    0x20341140d0396078214041003403010f08a0740ca812a9404c0c5110090904010810307a541c007034145507002d5140003006101c1d0342c000f1000c41c1c0600c10340382c062800c54074001d800c807641c40c0c0c960ba400c0d0404c024190441038240c00c0380ca09541100090712950700c0460a01e40d1f600030f01c1c0d00e42880107000c0007509d01c00c03048034080014a0521002280d8a601c801c204c1c8400c13103c159001c0c1c0a1001003080b240301c01d20040101e56100c0308841e081c01c40c03c0d80c52030f44644006003000400480030030f0303611003140305a64104265207081142c9030340b0416140c1d90700c0300c1c03080e44925005544900e0007254040d44900311000b6440e0306031014000b07109000b004c0101402c03020740400c3c0102c0c1d00307000381d115240302940100018507500002c14081103081d400d000c1e855015501115841e00288610025038803020200d80d4025170901e40020203003841641d0800800c2e1181c00035042e00c10b88180e52101c0d10000403150306031250105034200d8100c0d00c03030b01038060f02c05074000c49401108003400c69422a881e0f4200c0140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 902324523 1250 902323273 902323277
    0x18060509120421020109080a120909020405010c0227090303040201020c091e0402130c02010b040b0a05010207180212040f02010809071d04080c1f0f0605100c0c05060301150207090606020d0807 84
    0x240c80d0b031040202e01e4060000020327950403503400e002d00b0409810454150090440c21030a600b0a0700d0000083c12500c02c2d000003030b004020f980b0082425450300b03100880d2030401041d400a560404a02d07866481c0c000701d5080b4050702c282d0500c1082840d2141513244214100c0d200da0800b080040c100b943e0b0060040d0040b6042614000d600c4511003440c05400c1c10144942e0001400c01b00c41c2d0700f00016219a13056090107001181024045079034081000010f03180350004090b600f00c8407400b00d1000340324490300740070019000c105000070449140303030141a0364000d03607800c141074440502d03182c0c4811040c450719416203208000103103454250783c08164010b020302013807070030b00180204050420117800d43c8001883c03072071540d00209807414400e101005c004000d04120450500c8082030035a07413072811500500010501c1c0b241001000c61a810140c000609100d44070350f528089488501d1041c2c21175005400b031807501050903240d91148004842c0d030799008014403280042c0c141e5106001400d2042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 902325773 1250 902324523 902324537
    0x6021e070305191b060f0b1005090103110307140f090301090f060c1418010e0409050c090f010e07110c100e1e1503130b0103030e0a061b0312180605091204210201 71
    0x2d07942e503692640b90907c0302527102d1946d030340e40503c001030840701c00040c590481c0b24140306100b81035510000703c96800380803544030741d42d400e881401d5080c030303001e411031070750b40340d0300b41900c0d04208440b0308924011288200d40074070828109000c141c41040301b102d20300040034000e005010124074400d1090007002e4ac107042c50040322041c88003160a65000c09010707501ca038458000c60b0340078202214019404240c22981c3d402550500881074881d0101800394030401c092a200072000920038840b00b520200e0090010310040c8600202400d0320300081601032007500f803d005800456052007440d51b031424010408503074802141c5040000b42c2003d00318a8514031880e0282000462081046020b14007a0301c9400010701440104950281503406c62820801507404000341c1441041148079100d600d4246004449200c082d800002d10000b05040101008207661805101c41680100e004810200640300c00b41101e2225040a105620803503840c0c2021024130550001144c240610041c41454182 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 902327023 1250 902325773 902325791
    0xf0e0f0406090f021e0f09010f0e030d0807020f0c13020d3e091f0513320303030103061505060a030b040b09100306021e070305191b060f 60
    0x9003220b07440c803e1402030300d6001641465240f90034294a00710340c404484545046e100498a812038098060090b05211000d080485030502400f00c05072a90000360448000c0001d00500a00c074520036244000940110340c55803641c9180810b80c04400c1c603000d400500c5100544c0300580c025400111180d1403a951070a03404070b0300eaa03222031900280c020b4840c0c60f100402800c4208124080c46801c181500001c012034892a10342880b049403262104801c06140c0307201074010307070b81803082041d81070b121000e02c040483c01c0a035070007540c40750091100170300d1a141c0805c000010780c0180740741e00c036901d0350080c00100002880b640100505030001400c10425079030b0b442c04100190007460284000c6510ba00320096241000e1084e5100c101c422140301c0785074104402c4039024103419000117040c81e0380005600c001144070b0304800682101c40c5505668445003800c009015800031800c1c07580d0140300c0d2104084551140001850782d148100c9502c41912090740c1e420300a08a010010700241e07240c006074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 902328273 1250 902327023 902327039
    0x9031002072117041e02031c08010b03010323100203010e0f1506040b21150a060201111c0b03010c11010b0904080f090319060f050105010f0e0f0406 65
    0x150641510601d0110081e0b4000c490128180e040007a002c2c08011110260b11004207500c2200b83e081500640d241001a16110841000040802d4040c0d05417185406a20102c00403000203640c2c501c5503910f28820341d803a4900b0f05160f201c203100c01340004203501c0003c00d1030148499400f041480106c121640703118040288011380c0c000364884d0781030500301403c01003101030742c10781181d10500712020a0301500803000051031038003903130003404801c034408103100291121140b084060508081040c40d0036280050082e81000100103425000e0468828001011340c0140240406030710802d0080f0b003010362082d10404500c903201408100c603504d4950a0000e501c082c071030400850f050790380b5403e41c03401d0000300c90300351086010320741d008100000c01c000c04504248180d86451484400c00c0d81d844261200180c40c0100000b103045500c044c0c0980903003040543d600210361401c550a06200c075a0b60341c1e0066035110b030b01c0f900c0341c4080390b2411481e08a07442e0058030070036421001407000451544604e14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 902329523 1250 902328273 902328277
    0x1706030a03033914070c090c0c06020f0301030201140a080c0d0615020106152111091002030705010c030e06070309051609060e0a090818060d09080a18050d0809031002 73
    0x9615903c00034600c20034032030b482802504803100e4840b140c0e00e0204075035075581c80200c0611602c554140e88484402040f4456140d030502036800400a5499000b08080b200240d8030071b02c070407400b1075101e10004895078851401d80c0c03c43e0450781c481071100d070b442c1d0320301c00f2490f4800d80c40131080a03075490010460b441c0903c0407503100703503a0340d000160940c282110300c1f248040502c8070605214150f0fa140d41c50005800707107902800c5215001140300441c60020030100e011351b006441d4440040041c241066030f0010141c45000d014100900c000900c171102981201c41003080c031411a0490400246035900036007266203242d00c507200b124104002080640950107040d04612081604c13403108005180c61400b40540043c0888070401405150b47d4404656118001444010168100c0e0905290352441c054607a0301c2c4020f001401100540e18042045a1224600a01281ca07182500051060404514098580140c4002050f410039220550345030811181e41e60325218100d00d141e108416400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 902330773 1250 902329523 902329601
    0xe100e061b0a0210020303010b040b0f0d240506030f161101051915120f0609060207300f12060f0807030c060819020306040213151706030a0303 63
    0x750210034581d03c1000754800e003141c2c00700210340c01840184001c0880100700d034115442c2c8200150398114008811603a80a1600c140648602d40401d0010015982a009480d1000758008180e031540320400c0107020f000a0300c411103015001c41c00903c0d8203d008503030001854841c1408801e1640340c1d0342d032500b9030b03070f041790000d01c1c3d480322000002c103020072401703081c080c82c0682c401400d4540c10850754252420003503d0180041c100c078103004041c0612035100f041e0b6540c021000755522405070401d4540e21400d10f030721000860903210130701010403829110711114129a5103d0485084c4240c04903024013140d83e0040700750703540b074500080c1c1c0594007283d6401032045030080c044991441c10445030411950b4011010322107a10100810303442e4031406120100d8a0000040c0c40e91100300204000b4080c0c0500c4d603409a881ca140840e4500c91400720043e85d80c020741e18540700350b49040c25045207110655060750141e006031420300010340241c0100191026021129080c1c44aa456100701b400c0c06c02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 902332023 1250 902330773 902330827
    0x3050a05030a2918011d070c1a151801031403040e090d0906081005100909050a0b03010507020118021017040b060f091608070306051e030d0e100e06 65
    0x10041c20b516082005132805001c03118050388030b856240400940214014a44c07a4202070b908400284c04a030140180301c00fa039030081d62080b1386102011001102017400d40395084107001003d40e48440340f8018402c2104442c0145120090341d20350358585074021a61041c045041c001404041036003440d07041450311800c0074030010132245126410182c80140c2540000e03003080012008c004010281d44070210444805488603607501c00d440c032080b0760720445034000c2e14001c2e0925003402059842c68105c6c8941070411002000240c40780c0600781c0c220350701c0221500402a070014082c01500d080040144201035034100051005205c00011940c05012a02150502066814400390b814000e8120000745800e549000003424107003582001a04a04840d804000c422800610407a03ca5000b480c01080e015250406440d200300c4258015000c004080b03009206a0120084403842000e0540b032000024001450001c03600c0000c0b10041190030070341c3d0708042c1c10003002c0e004070700300c0b000740101903500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 902333273 1250 902332023 902332091
    0x2101a030a0f06150f060e010909060b0903070b0c07030206090607020907050301031b0614030405010b1302070303051006050415170a0504020f09040209280e030a0206090a03050a05030a 81
    0x1a207000303012a00156800303085131910004c2440b070040c8010005080c0d48040c1014840403600d140101e90344501a00900d031020b00700320001400306d003000b0181601e144100e00b50341f07569894900d40e28050081e0a6110304503401a00c0410250a0140080041c4030018016511b1f10740c654010428082065035a800010000070042051107a091980c00824060324448102c40c0c1c980310005210309089100952012000004102005025405a0100e5034058503401c0f40e0f81010b1580710007504100410b40c0444e0400c0d00040700a4548407489042d41d250382c60303031400c05003000c850310281050f00f00c00340705210744074103010750361000c00880307034070508610a011a80c0e141a1040c08002000048a04d0140d0300c0d4000b8800140d5a08a0407a800a0304844807000307840c40c00d54060008104161136000c91b40740c91131055411401100900c0e0740b0340690211440c544501c40c015a54040303005015001980c00c4c0070205066206038001c60300320817032420120b110994030400c01124150102886070440c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 902334523 1250 902333273 902333303
    0x60a0501210e0304031b0506030a0b0d02121e061909050708060c13060309021e01171306060f0b030c031008030a030c0e180a0f0213030b010609050d0302101a030a 71
    0xc6d890050b24075058010024044d034940000304605000207000114206e0701c074041c40307a0580701c3e0541e110712250001c2c0043c0901c19080780c2180ca9900071110708800750000407004c18000000181c90340203403801b0b94810314020900742041e0003803c00f100211158000c07c0c00000c1c13941c0d002c0049078040c050f2969000e0ba030f00300038500110603c4440d4050b00038181401c42c1c0300050703a00d26107900c2a0205065007171001c0b0401d000100c0d502d0000550707250300c050001080c052003101200c64068413600c10b800c10450aa1a0038042200f403000744140e601c107610400c00901358070101405942c02070104241443c0580e22189843d00f150000110303200080c0c0e03500c44142005502c2008030020300829217090070380c0441c40d41c03d824011001491080600e8035000d03400300084d4940d044030861501c1e000c0700c106070f6440c0c1c5809050724200380709140c00180710301c0c0c000c621b9160661084c4800c0d43e00d80c00074036089124421001c0581a4a0072162070a10030022030102074805120310a80144500261000b5100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 902335773 1250 902334523 902334533
    0x3080a05090a0f213e03040e0108070801050105031c020a022e030b010c020d020d0803011502010524010e030f010c2a020d02150c01060608041406060a0501210e030403 73
    0x1110303643c20802408001c9014000c5c0c0021095040c000b00300013040c10108a503202c04603e4241202c41da00d03a210005000a040b81c00b0741843e4182c950300015a501241d8a0044c0707400c1c0c030001e00640b54113401c0003000c290072103200300c0440d407500030b6401581c0d042c01854000901419601034140b07002400c49015800044621204013000099800c04001070340c1c0301c80009045400d0102d00074003408590b2120001d641e90b0000c07038486e10b81c0c03003039440b50f603507850340c4090518416024048001d0b60130034010030b50601003045822500c00484c49040c00391400a0011200c4980e40c500d01501400f0351681219003d07000c1c0140c1407102c0c1e094542102c036821441c2030040700c2810114043c880f000b0121042d0050752540035203c4065011902d13016184030003c01c1d405503215400104c40303150710308100003900580201c4a00d100c1c42c016446a80c01c101c1c2000140c0d113402c41191815030180e0170309c00074090b075809480c44a03201c9009001e09805208540c030910201e5100c2da203c007840c0e600201d41002045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 902337023 1250 902335773 902335823
    0xf0136060c062004090f0204050603040c06081b0909191a01110a05060a110d0c020a03030623010305070e04060807031421071110090e0a060303080a05090a0f 69
    0xa4007000900350721910800c01c0300154002c0c5c0c011301c0d138042d455054411200309203405983c0a004001d0a4596038101860441c80515051003040081000340000888100000380794483c083d0394080c0303403480c00040704108030280784000c4c070b8103070b0081040c1c08080d4882002c0c803910101c0e141100c0f07a44a00c01050300003400182e00c1410b40085580700c00441e0700040d002280c040d03003115900d00045251103281324070b403c090041860b00c108840c60704144e883c0302d13603000650605a5009440402445445003208010404002c2006840340c030f0820800c0c605500c2540b240d40d11130424584480801301000000701500d0890b4818202d65000342000d00501001d800106ca140c02d069000f0900150180004454102c3c003402c1c41090600219801040c4080601d103401008001000d0100c0039400c0b9402614100c1b0360f0041d0034220b40343c007000a50b4410726205034025607415441c0c4805a9840700540b4000d80360092814549001d180c2071000010056803a4215540c8103a44800c00e03240d10340d0b8944860 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 902338129 1106 902337023 902337041
    0xb0a0513051b0705030a080a0b1c06062114010c0207090b0112060608090c040c21060909030804060b18070807020703170702010e0f0136060c06 63
    0x80040000d003041b4450f901d1790010ba4440c07032001c2003114541c0961b240c21509900104001c81da5140c00102003520130203000c0b8030591101900007218000f41640d070001121031550004000301c440c92801c41030b0f00d00008201e1845c844e5002540c2d40d070544100d4040954601030303160310b030740703d5590340000010a460030b001150b980c00380101507070303000c4441c10641d024010011010345802e0068800380c079a01d984500020000820019120000742d10f4040083c1d95003200044101c2e55009014096002e5100c120342c03454981003c0080d0741111f15854800d0003040110500005041006a0003d40c03d1502513480d41d07600ca42685030208a8001500b0b080b1070042d02410454220000c040c060320130b0341c0b040360124008042c00380601c02d00410601161f041c06104c1004100b070071081d07901c40d0003c40c1e040032414203880030382c4040c100c2d900031000141c5106600d80c03d000050040e00e0007 = true := by decide +kernel

theorem cover : BRFrame.Cov 902158273 902338129 := by
  have h0 := BRFrame.cov_init 902158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 902158273 ≤ n) (h2 : n < 902338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
