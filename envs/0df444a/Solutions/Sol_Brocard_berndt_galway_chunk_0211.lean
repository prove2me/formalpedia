-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0211
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:29:20.528984+00:00
-- url     : https://prove2.me/submissions/946278e6-75b2-47e9-93a3-1a1ef8d304e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 37769789 ≤ n < 37949645 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 37771039 1250 37769789 37769819
    0x40303021c09020906011101020f0d0b0109091802090a020706050103080306190b0304060507090f06020312090105150f0102070b030a0209030c01111005070e1201090c05040221090c0a 80
    0x1035050381038112056110a00b80708807200550302070300c404401c0c0e50f0f1000640b005440b07a0190300b2155000c00079007154580c4e0f04014032484140d030500044010b1843c000400100316a00120105450110b8108015030041700c10001a17030304542c006255a240b6030301801900440d0320050503541010004000c0243c1e00000d135120f0201610000880b03500008592020079581c803441110351000c1001c207000c2001030704541d6000c0254102003500c646d07034849000240720941c0c00180140c1010407842110720801c402c0ca5089000b0000038491802c00304059203003040980f00e1580720344103000000d0581c1e40240110710040c4101c03081c3c2074407031a0400102c0c01a6001c160842e101e40a89000c0780d040d98080c044821020000c50024144a610104044024130300038219805003e005e01914103c2e5a030070201402c510a03601c004208500c00c0c0c54060300048181d040035228a0043c003410841c540e00e406050b0035501c040301c0e120300a407100c460341410700a000070172940000420001081c0000125580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 37772289 1250 37771039 37771057
    0x120309030209060607150b0f0901060503010602070b0301081c030b0d03110c090702061303030b10050c06092a04060f080303010810021201060f09050a14011b020108040803040c0306020304030302 85
    0x1904964600f02042114820307120000c1015401e100f51401c10360080d80800740003400a841580758250800c0017550204090f442180050000001072184a038140301c214010072541600b54119410040780382c0e118269101241c403400c40c1d4008403005903210303410811349004064a404081882410003c15025082000d06441e100f0704031500340e0f500781112550f09c15903959000c0c104d1a00c6506044440e800b552009800309038035260f00c1d805550710301e50103000100040c0c030b401c1d5845040031401410210014840d068a4004280000d103009544071015000300c00110304010402915000400820407070704401100c0107928170101c3d02c408008000c50503038220300200c440c62074500c0e003004241d210b001803030841c400e681c1c001045950b003e4208040300002038241400403d40380d00108490380a954480482102154000c40955800c588680c081341c501010001a440041e00080c00307001019000801c195000000a401e0003c4644514040c580c040019544c81c00e0a00b0010080d40000c108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 37773539 1250 37772289 37772299
    0x1090c030b150a0c0804030602030c03040308090d050a030c12060807030c140d080a170a060f0605040308030403080c04170303040b0606090904060b030c03070f0f0f0f1e1203090302 79
    0x114900d82e20b40509103540c445030b003000b01894043d000a04a544110101045903696000d020100000f04540081c6100340306004030680c9a2034035042c01003036804003400f0820160005085104129031117012640402003034100420001c0d407450b800c40d9020401480d00b1003191400c140070038031034404610001140d0090904150607034440c10343c41c260144680119a110941ea0529000905090060107000308581802100c02d481c030032543e0f08800f42180c440008aa585000380414440d01380c1c00e10160003a0f1401e14241411652003d29074800a0006001c2c07020050000d00c290041c001298041d001c210503886895072000000783d542d40041c0d40807540111640005440c41c141902a2140410b00034000b00719030b120740e1900700c010710040049540601a64405042ca900c0400ca0f034001003070440d821900c03981c03410034040f20350340d159040480ea05813103040c1003205403c1011500103071400402c80522004610240c05d1050303905901003c1d00c400c00250351424075030040703107140440c0e0007651 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 37774789 1250 37773539 37773551
    0x7090501030807210801050d08070b0f01050a15021e07080f0105010608071b02010305040501060911040e150102060714090901060f02010509120a080604060b030414010b0409020f091e01090c03 84
    0x11031400313002550a019800a00c00400410184c90a0650185094098005285001e480f07494800462a0445801002d2068040108000c0c140080000001d00481541d41c0155282c0301d8000e4485400e03103601c0c00440080d5807a1074034110180800c500605a0208455500314855a810302030071b0240f0641d03000c1810807000a00e001d000741301c0a00d40f1510002c0074542050140d0040d002000b000d4401d83e9036660b103450104240ca118400c2007001c865030076110f43c0395450000d40f14880c04000380700f204080029245040c3e1640c0010b121a00014503041c07004180e85503e4160b0558020501c0440d0b220010300000a81d05801a060b82c2180006038000e004070b40d650354446507200c035118940131006504002c0744940e140f05001c01d6401c03000040c0040744642d520302d584605038005031816242c00102007031350a4091000d00c0380d00040401540c1c14406400c0c641c0000c2c5410000c5147d1034010381100c4c0010f0032001d1401d002c3c462034904030303212200550b158400c03040208a490364500111345045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 37776039 1250 37774789 37774823
    0x30c0c012306040c0c030f140315030606030a020108161b030309120e01091502030d020f040501020d230a0203071a060a0e0f0109020f040305030d0203040c0504090b01051207090501030807 82
    0x40a4000901c2282e26030350220051a6000c8030a18441021841001664803420b00b420440700000c0d8018403640812b01454021041014206000038014501c00ea1040813000010f0740c000030900e074000f52800100e094074200c002c0a503050426146c0504801101c00e101c401090f805601c41c080300f5000c0c0c036000c401c03441030a03020f07149003240000d41703030104030f88000800c41200071507401d0150b00002d04c184c2c1c0c02c0510162048059030080381e4030103c041800704090205580c10080c20180c1001894001030f0003c52a01001074104040518480d00d900007560b40b10b007070300801c229950301d0391050001c3c00c02c03030701c60100c00f0b0100e00a03030300b0702e12a420310300c8001610310f20701e480c2d280541083c400b00603169281c410300f00d00075400100d200d0ba07079a1007400000040382040c030103840681031031180980e0340c3c40c142c40c00c4441917059800c568411441c200c80707540404c15284040341926826140c1a0300c00d000380e15101d2504200c1c2d0f0060306050308040002c010005098090110184a04040176082d040340e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 37777289 1250 37776039 37776041
    0x50108060306160c0f050102030108010c0206390304050a05010507050a020303181608060601301109130f05090601081b0112020f0306010906050f040902030c0c01230604 74
    0x544400341d056004030003003104089008189040e4245905154030803024650320304c85900c150750400d440507540031004000c021400e0065101040aa1002d4080ca2401c0d0046008940700210501d41c03803050144040700c1407941c5d001d0b0854a004c202c02e00b903100e10305441d06a40c0ca080f4410211615403c00c0c02044c0f000e070182c5c0a85411140e80c2d0041d505540d94000c914010300303c03c0d400c400c1184601d00000a5982c0030340d00705406880b28070090a4223283c0740d4005408000f0403d4415060808061528013840305845091001a40e8060205a005200242e507030603004101e403256101a2104032000000006ea00c101e00000007a10300784641c1c0e0300c46107059141c25091107490903581244143d9070b0010604895804a0030050415007000031104c13903017404a8104210007400044000140841581c04c980124000d020900e0f140b86042801050010580280c1c49801c802075008400325040448440c00c0c1d80041104000800204000e00c4640059103010320020405095000100d5414201 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 37778539 1250 37777289 37777291
    0x10503010605092b080316090b030c03092e0b1503060603090a0f03030903021908041203090510020a0c0f0f26010c120f0203130807020307030b04081201050108 70
    0x31601c0b07550030200b4020501908412512400c5102200c502c0c11000b8011410208640075025400c6140c80346003601c0b440d140b030720741c090a5a0070300c86500702c10442424a4400c5030303800401e000910fa100d49500d00b031a80350070013840319040f28184074040c1d44100b600302d00c4400c107180b032562014000c020080061114000303011036203034040d60b0100005242030030304400031900680b4200464080d9003a6484e10810907a00000803030019803101c01840c180340c0d0401401c00c00c10000c00240b0f10b5500d4070340e9868550312a512840d03613440e50350b01e00c0302c0905002d082440010000a022005580b0f04144025101c1c100e11108603540b480c0424003103000c082c0d0a0403002611034541004107035904281041d52411008152000b042c0041080410f04000078040d000015551381c58900741d01d2755081941d402c0d5071034001e440c0c009600c14010811040c1c1100c44903056181c100301d03016550061400864180811600050802c00420b0309020401c4440c00007004910381c01c4a0b0011945d1301d410044a503104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 37779789 1250 37778539 37778549
    0x110c040209060702091b0418050a050f01030b0912030f0105031c080a021305030a060b100e0a0509070216060e1807080708090c10021e06060d03080405010b04090501150501050301 78
    0x61003d003005003030001005410109401c1c94800e2400c280303514030780c55130158000c10055101b0514010414401d030045d140c2050b5003000912032441d1541c214611003005101c05813401c4246030101d80340c48402d0242c00111811610550359914028492014203142842018040d1203060384000000031210310300d010440007540c5008652301e60781c601601035040b8010a105443c400080004c140c0e07010031490580038810540441e54140e98410800e0412402c41c521090240b520310385007540c3d0b00c032025142030f5181222100100d0300c810408074540715040700300b0004506c110001040803504071600031100a01294070b81e40800c40a003428903407800907218100400c81384808217003103900807d48194451010f01c120784c2c00404040000c4c0360805000150405600400305000e003281c00c2568101c40d1125250051001e810684040340203100056405010061000d0105041040c04c0d00403440340d03040100180492034007070820740d00030011440c21600545c800e45000409501560580b81210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 37781039 1250 37779789 37779799
    0x20601060815041107050a030909020c030405270f15010c11040207060905010606050904050105030106080c060f0d05150907030510090c020705030105012601060305100c031b110c040209 81
    0x103221006010340c103654011200d988182ca0306000d400800c9058081e0843e40d0040c0001d1001c0087c904001d4810b02154110914040c010400380c0005503000044034111801920b82c0e032140c00c00a0740d943c8200394180710a040402c014000d00c070119205140c0107008905000608541101031130055904000e140c0c0c0040010b59403044040c404c0c03134294060301c02c481c00307000d0100e118142c46e9038031421a9100d80149010076000700e20041c80e81420f10506001d0401074008000950038407540c40ea031604950580d922480d0001214904007034454290356980807440e40500c0b05007040a05500c641000d00c0216010f0480d00b0005008580300e4000c0714095440d00003415005424440c0c0c0740054600022800d00354828040f00184a07103003441558000c00d407258584040c500d550702c0f40c11859410345175855403a0f052900510200c1c07004604640310300342c001000140000351103802d8018242c00c03420a00030030107213108081c2d0680c105e034503d88120542001d42e0b00216040007008201c0c010082d51035045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 37782289 1250 37781039 37781041
    0x4141c0209011203020a020312190c080d05040201090e0a0507170721090c17010b010f05040902030a06030b0411010f0207080a0f05010b0d05030c0714010e040507030605060a1e0206010608 82
    0x100501083d240102c0f8024410b0301ca002c245500841d2074121782040c8881081c20014140c849036080d0403c2c00725080003880c1103d0406110745401c0c80c03074090340c400161034503034903000301d811a0b01620ba1040205030900408103e4039081c1c031201e0040900701c0790440400d07004c0410f04c400c1516104101d20440315500c58101f9451642246000901e0894107039581c42d80d42d001da0340104044840d800002d040a0034040c0000806504c05130079941d8804910381072100a0101c5103440d600582600d042d00c80600c0010380380d655403444040500100d5001900706403025052106018a001c00090f10703000030388640b1074a01410310200c0c0d40c2da41c0c912444038260000440c00c000103001c0c400450740180604004260703c0c00001c00540342c00055801203500303500014840c000003d0510401c1d0060a0710f8808043c3c00b8201c90010304007611013034031144600d0b5034100081003640654401d10240030b001d000c507034440f204c254019041030446220f020213640588000c5a0300c910000705a41a10503903a034940c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 37783539 1250 37782289 37782299
    0x2120109061d04030e03030c0714150406030905030909071214070c031407050601060804030807050306010903021918091403030105030a0b0702011103040605040b070c120f1404141c020901 82
    0x100b84002e0030403001c2082d82d525248807a58200050072608070118040c005140c81c00d4280103048040b07012407401000c2c41c07030201c4480e02c0c0c22010361b01144c68078140030621a80a01e4001e045104103020a0781c000c9419041c0140240c2c00b60020f826032490680c01c014030401034110440c04401150030307900140c5040741c1500007074401c0c40002a4000380c140c00504102031a903409040c00d81c00d0b0050000a2003800421043c1356009684603004803050905510313504007200001d085805a000203800b0700e0011003c06501c1060400340001000c10100300c484070003080c04840c025190007031055400300f04424610014001c00b00c21241280c83c000c0042000800b265034108580200030f00a6003995a6001c4440c01c06007404000c601c03070b6105920000d05450280380494030a0000b40c071080c100700d4400f8510000408001e0120b59240d05130500b020001c20110049803120414400540001c07404500065a40510041c448000700b044482c0c0900d164803d1917004d0094099901030740c800340d54001081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 37784789 1250 37783539 37783589
    0x30115030c0504231617040b0c16050106170106060801080703111801180c020a020102060c0f0c0a0c050301060b0322020609030f06040308060303130308090105040305100212010906 79
    0x900c0c60403610703010b00fa11011134a40d4100c03080880b000303801d1940c4000100003817036201ca800c25020b81d446800e680e00b410f082c1c03100c41c14090000e203040611903001035000748010018604c04c5241e130b03210009004568032038032001e204000c0003034220102c2d030070490041900d03070050380182d042c1c0d5510001020101d01d9900c4045520b040b9206c040c1e003105980c41b44001d0441c1c044103140c0a458002070340016059066280811245c1d440100411074020b41c46d4800181c0c0c0c08109940c200300201c1d92251110760010b1841c0c901d120307081608003035201e5840c40c00c04000c1100604000c44104030006c204190382d5020b018603910040310654400b806192034200c08103003031000f82540d03d0010700054106407101e070109162004c04c07030241c40309501c0081044101648182038541c400810743c09182040f01c09201d4040b03c3d140f40c0001000600302003921a440e902c91402d40d4001c0d070b0807004403111014560805802036119000a03014080c40304004204840d250141d1022240c1507100a503140c194487d80c89 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 37786039 1250 37784789 37784801
    0xd020706020c040c030b0a060201050114040219120b030a050a0c060f27050a03030e0f030304060e040209030a0b010e01061e0903110a0902030c0a110606030303180708010c030605030115030c0504 85
    0x1030a240e60f075100d01001f0344400060324094142d0fa000010f4650500c2d070310070450002d00c00b400d80308600400c0400b501005000307407a0b42018840c10200b071301e0300c480b0f01400007601c02100001e070140309040980c1c0501000250380c0d200107005a00c2c0000c1c507500c8035421035545070391a902d1008180318020040725030080700c002c08401c010000000e101c10740ca40c000107680f011243c0c8280d0016000d102c1001e220b24005409042400342140118506032505034003030910200080350511550f40800c40800541f4240b150030081da9010000003442c0d0b07155012190100c0f400e018920010303000000f46864a1039004c034581c0340400359140c6001d880c0c6156031703640800710155402030300010b480d1000585c05095001560090202d400d0b0309031100c11086004209074a44a50094584c2c0078205001d9991000b200700c98200c815001e203a900000d81403000c81c42c000c540e81c4000301ea07618200d01c5449142c0c0c9039004070242c0d10224001d0000040c001c0e0f8034840503000740000381080403000303810045072a06038042c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 37787289 1250 37786039 37786061
    0xb0915010512240412020d120b030304050306090102070c0911090402180301050c0c0c010203120114010c0b07030507080c0901170a060302060f13050603160e060d0f06080d020706020c04 81
    0x126142e42202d203001c4490004101980d100030b000b01c00340010041785400020940ca080c0c0b004084101680c0c500402840804e0100c00009980d400016180c1d01c05004441c080d11000d02116128105440d41398001d52000c002a10740710441c10010481056600401d24007000440040c0d041105600030400254400d440c124642c0c5941040500075840a029040c850340307044644c40d464407000c5106038140010403500604640080203500c00501009550030b042d107141c1034600c0101c90855006071604e181040019040c0d46040c1c1c2042641503154010900c911030959030340d4030503202c62010607103a000b440c54450204540ca0206001420803030281b6500407094000070070200d60304d8000c550241c0c090028240040301c000f41003c2504807081c5010300401098803002d00c0e42c0b400c51030400c80302e01122024020454680c403000d49646c0d4680589400350850301e010004450407100c0c00e0010403d52258008038001c0c10701492000b030010039071804446254000c0c01c00000e803130b42000028102c1502c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 37788539 1250 37787289 37787293
    0xf0a050714150106030204050d0627140120120603070f0306050901140702250e01090207020a05010f09050120010c020601061103040b121b160b0915010512 68
    0x340082811010721800d404500c0018000b00010b0301c00c0250030140581041e0141801000704204030b44604910b0f9203107a40107070001501c440190b490001282c150b0140000d0110a6040201405996400c01004880c2038000704400e1107186020100191117880c80015a803050144041d2036182c0183c5961225008041c1d680460700e40200d1107445505403c2030711420303a40d008001000609202d1942c035480b440192a40c01d2130840802503489030413400c4854155100c8603008140c4400c0e80c0d540e0068001410b0501a40da140c01000d8002d4000b000140d10420400c1d10016042d4000c1e2042c55000300981d0302c1845135402e200055441d480c0c0b0032090b255600030180c0303c181c1e00e882071094600c0181d00d6406460385502d03007280204480310341121194650010001040a428640202c0f81c000d90310040054507640c50522442c0c0103603c0f2403840801640014450445100511458400703901c610200700d45900c52038186640d60808010300e20003051040c0040c0800d142820745400140900d0781 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 37789789 1250 37788539 37788547
    0x3020915030303190b12120a022a01080a050c190c020d03020a03090b040b0d050603100c120f02030603030403020d051009050601060e01170106030c020106090204030b0f06030f030f0a05 81
    0x30201e4070b55442103811308842c0c1410951216584000d0092044c03500c41107840e90f140c1805c0d001c1440e00d5401c5416400e58000340002e1120810b07000f84402120040c0c101d0112555841c00b20140d080c200100c0a46800240e00318001a244221846a180590604000c4a091801c40c80030a400202c101c900c0c4c40c14090244101d800681d50000036141282c401da02508040c4902e14000c0c0c050445600708082c0000140f00501c0071294403801d884090301140400b059903215070010a0610303980200d400c0a4600700500d10f254981c012240c41c08580c4074402c01c03c04085c041e14070604078081952142d81c0b40d00304000c10405864100d900a020768091000c1d200c0901110764640221005c0600488107a007065004001d0030360000e118061404007801c0004100209440e0398003401014090304040c550303948500c803c510b100750700100c0602540c41d411503550b0344a06104a048400722106560200c5005c00223070303182800320307075202d1050046008600348900603610462a421903000c08003001400d00c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 37791039 1250 37789789 37789831
    0x9180318050303040b09150a020c010c060605091608010803070201090e04060b060706090c0b1c0905070503030a0302040503010501080111030c0a03090c06110105060f0d0803130b070503010602010b09070504030209 93
    0x210013007000f403038510035450303a503032000e0140021010400f03400c000628003070000707070390780c0e41c0101e038480c001c3c0c5c001d10b00701b00da1418038940f5000800d60741c1c2280750400c54010400c00c0368100b025031b4018001a0340c44115890f070380c0d104459540d12403554028000b40c2c2c1d20108012800b00d000c01c064000f841110302103040d08075480840c200350081603058886589859801007804145003038a409080d881c400245003180310120301d042519041c5003800420b96480e0903a083c0300081c410540078001c01025644d5800002d040200a504980a181d00c0395181c08000114004144034662403c0c0440c40c6c4982980e82c4c3c00042c0100381c020a680006164071840a84000780e03440e0151340281032a5202c0f40a03120003540d0007800c4407001080715018100d1a035045807183e5071139240d1180303943d0003030042c2d540e965800800d58442d809800001c080304452002d00c10380d02e4001c0061816a0020350080046151020030090291000c3d544480410020041440941040022254400300751032402908010751 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 37792289 1250 37791039 37791043
    0x9010e010213030308010501020d05040b2d04030615030308072a03030203010815040b0115030b0405010e07020f010603030e0d11150a09092304140106030f0c091803180503 75
    0x1a4004503102c200e40c030050013010703040004036003d41002e00c001c0040700390081001c1c0691245000d10514240c0104581c00210316403854841c80740035034200840565000382d144180c42c0c01c00d00007120303441d04080310354400c0039840c030071002242e800d40c5d102038142d2110401580c10784c20420743c1a0082d40c0f016000040c12401403440d848041c86541c00607035030f40c900510309061481184070780e003c0300801810702c00490040e60060b0705580c002c0400c241c402d0100311007580109003100107140c0190404000003000b400140400344514015000e0303078082e0300035100d85400c907003040c0030040103d40144c06e0002d20382011020315000307511441c213640c4051400d400007000c1416401e00d0001281000420103002a0b00c030070303142d009003802442409848000e00e01303807011085aa19401100195000084c10300510003070b114403440b004802042155141d00740b10800030503080d400d031a0404290400a603c003410f116409030000910040c0542800a64040301c0c8002c0035140701c0d211981c4007001140c0b0b6a02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 37793539 1250 37792289 37792297
    0x10c05060709060f030c09150513031214031003030309020607060509010e0f070608010b070201030615030b011b030804020f03070f060908100b0102060c0708070c0303080603280b09010e0102 83
    0x10315112840b1040c609400200601d4803800a0340030035051002205c1c04c0c5421540c000191404e1041d0150117000c0d100d4200d845004111901c4c1400c8140c5000100744041800e408440e00c10342d80c5c4010310f2040341c49025126102c1500c036844c20f11a00d2100b00003003807080d805604114401062180740c1869510b440040e200c01740c800007880d0b595014100c44e040803c000ca842d00000f8078000d042000e14202e40a000244144115004481e0000300b4404683c401d9010780044c00c03100d019446610080030004000703100042e09640811061550204204540c10400940762392643e1420003d95440c3d017030100307181c00b0500c9582c0620500c4d0340031a510b150320f1803280c0a4401c03650b4401003145480342203403a120f0b0078212800270b246032070b0302c3d806a81da006c618035174400b02000325181e80d41810b00e8441480c4c132a0300d0b0084c080c5100c86902208055021455501528049003104d00c84800040d135201e00e4080d00e9218603c00c00c0d0b151280780001e5001c0c180c40c5d400b000c144000103c3c40140001701e0b00b0390b84 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 37794789 1250 37793539 37793551
    0x309030c070609060221090307030503130501031506030216140d080c0708121009140103141b0411070605070f120608031602120d080901180809040209010c0506 70
    0x8200346003103920400403000240754920745480124500342c0061b440c0c615002c40804014901412000320111400841d6481da90180480358816a00e0506a490350840042000031001007100051150300c00c0c01403400d001032000e0140096407401c2e200780c0c000e501041d11402c1c5e65a12643d80b001103070f03601001c0714000440700042d00c00708040b400e00500080d8001c04d003504c0e0320720a1150101003a4082c090f140c0c1080a00b10580042e190254410002c4a0b640c1c002c1c0101420180c0c10200c1031007908501f4100c0e4468400e9011920000b661540c45ea0a000d0460307803801d01e0a441c6400d03510302504100d029441443c01289402c2030380d00d441c0b042e684103c82c114041551401203001302d96102c00050b994000c400000c00115080805a584034841e96603c25090762a140e006800d40d0396200240d03541032074420403101040507040014201150494409945501c0c0600c480030024165200a09050344910200d180020003403c100080d0440c00e1701c2410011501b0780440041ea040020354000c030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 37796039 1250 37794789 37794793
    0x1c0f1401060f0504020c0c0f0a080a05013c11090303030a060519030309060c0305040e0f070315050102060606031503070801090203010c0906050306100e042f03060a0b0705120309 78
    0x14100018842c00c00035030b41c8468015881000741684800011038020160b180803504070303a940c04420000f5032503243d0358101701c0c90f1740210520341e8200401548000020031250310f40264403000d07414403240a004035824940700e0019814588041c121652000c0820700269054a040c120072001081c44c682044400300c5620765950014807442c0b4043c1200740c1a45a0000d10407a40b5045540c01080c001c00b900c20f180610400e03501a40416005105075409400d1f14507111302c0624284c01c9000802c0001c0d141ca070042481c16103610070003d44200c4d10400d403030043e0006c101507141d910901000d580001c0c40c0e080d440521540d200069641407204000030110500041020300c8180101401c544880c4c44203410f0284440c0f0070040302d90050252544444d044446400b0010504e000782e030140c41c1da814956100e0315109100c0900f0000e810151034130715048041140071801a100741c1518801074a10691100d031070708080108178680001000000d200380140c900c08501d01820300d00642054a90341e0301a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 37797289 1250 37796039 37796051
    0x20f07031a0f04050316020301020904020a030c0f030e07051201180503130b03060112020a020f06090f10050f190e030a0905030c092401020c0a030305040303120501051c0f1401 77
    0x1820755a0710a50051000c0c225079460703092560310140d83c0d00c9400f40d00211444061100350a540c0d007076060390200ca27170140003550b5612036800c0040041151030034103808100070140c090103a0341300b4400c120340b88480000502100f4240010000c042d1480841c60302c4543d292500090105850900280c40305d100300001c41c5c8032481d01400d07080ca00d603e500f109011000030b10800003c0d0780d00c101031000c12810b2160059541d446803004034140143c1028030782c000d10515003445182000000c8040c0c1a010007000d4440c60030503180300c28107481080e68030326005000440860400c003200125581600e030720020024500c10409200c0381940c020b542800701240030700d9010400d5040030300001540030f0040312180400d160a840303000d00a240120340050501c080c04c2240e506900801c4507502d401c000500c00d404465503450010610b6205010440016a880c03c00b2600c80b403081c002c3d2350580b00020032450141c440c041443d04120380c2003500769074001c5941c00100105060350807518685003003000200749 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 37798539 1250 37797289 37797323
    0xc0a02103c0e0d090b07020609010f0302070c03120e01020304120206031810050411040504030c080c1002031801060e040f0209070905090403091a040b071704080f010603030f0f0206040b0601020f0703 87
    0x14004541c01405c0350082001801c0c010b9032528126403d408003420407810004095508800900940b40020b00c41c000ca501d01000303010903200301c1240d40e907a56440c815a12000001244c590103944204588080300e20038000042c41c205015550080c03503918090903152000f0350540c80c00c0201800c000d060b40d41c50044c80f0038840003044400d03035440c096809000c0c0d81042c0d60000c006440c2d0714000b810704800405c60340e406810a01140119240300c00d419901d078105103400140d260b5072407610070199860100c00151b60341c0c04110480c40345070081c0234058423001a400f40403003040010410f00402424840104859072004a842c0c002c0b40240da920b101e4906200c80540d41022000c1115007584041c007080050310f1100c0122108658400c0010b1240c01c0350b40c07075034001c0d8045d1790000307409806044071520060b0030540c0802c08032406076030307071a02c10300c40b02005807a0190f00000c0e207070050b00b060b00044e001c1955684110b40100062046943c1000900416820304c03665070000c4420300e60880702006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 37799789 1250 37798539 37798547
    0x130608150607080901080408040504020a05130f030807030323010305030307090f0f06050c100504080310061e030b0a030b0702030c07080f0c010c06060e0c0a02103c0e0d 74
    0x803600e00903960355250040da502d84a585000d010034050403ca0548005410419910181d07001890060810b6460f6081d0a1001d043c58220113a211035814203107200003030310100c260001080b0381e000b8900c1841c5c80d1464404401424107507506401d0b403807245488400404601405600071070160020319102d0805a0004050310043c0d80001b62000d12040244010803c4010b040d00b01c64081c10046d68039680c050307009003001c0c00381c420074000d00d15140c00c110502042c100114070495a210913102c0e2640c4803203064610060310107901446004201c8901c1c1d2050003580200c01c0b100c401880350190036134030307914000c0a04046503c84016000410b1412485800b001000c020380183c40240400b40304655400350b5440a1010460422106500110920400341d0280b4060300c00024040d02c0741c984038031180e00315440b0f0380250300144034600d528002c130300c3c40f40f0900140462401d540f504140b01c0341c03002000183e06600c188a404a00d07540e500c1144401d1143c03c488802c800040c00d143e880b030700b030050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 37801039 1250 37799789 37799821
    0xc030c0b1503010e151801060e1302010909020c060a020702041506050913060b0904020a05040801020c01062d171002030f040326040b0c041502070503011d06040204020f130608 77
    0x10913190f00c03000c40303403c407466195080c41c0c2c80120800002d01c1d401c4028034050140034680e0051001c03852000a100180c42c10b44140d04109000303880340c559484d941c5c000d1004905c144405100107400090100d100010b4a1f0014084a40024004241010344444103511100740f03520260114034001941d04041c140240c080d501e010344102c040007058941303151820b40d403080d032980300d2103158005500c952281c050025980a0300440c1c0007151a40f000240b1903000701014000c0044003148600817000c6083c4920400ca106a082070500050300d02c5c0072244a648624040a0314060080305003600040840344040c5100d040c00b211803612908050030b0207400aa8000c86586003036080160103032905008c3c509880c4c2099100030044840d54902c1c0750005a03002d6500000004411802d040d0a81a40061520180c0d81c044000700506145051109075004040f02d94441d10f8002200240247c41c140d0702a0100c104c510002603d010418032007881f00554503085000881c41074000e0118000204040c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 37802289 1250 37801039 37801061
    0x10305100e040602090a0305070e01090609050c0901030c03020405041a150307050a0e01032d050a020a0c02060f0708120a0b0303030408030f04050c09100e060f09070c030c0b150301 79
    0x200c8002400c14072800581e00004001404142e000a099612a10f40f030940c940250703044016180165100c200405006d03800380b040c00560b42c01c015000c40c18900520039a40103c008010082c5820800d000640160103140c12500900d5401c1c031000070380c1e888a004840c00302811300d0304514200d008004124040d41042100c51525801780100800150403004841c02c910684c205401c00c0211480100e0240909207000603020702c1c001b8611203001e8a060354000000e20040c400c3c8090781e984c8990001301c0c020061888005004038880b44058108800207084642074660068900183e40c0c44094440c4d0010700081e40075500542000b40d0f03108140b01d0076854610460145245041c1603c9079001c0307020143c001c2c500907000c8408074003040010080b0841c159009020084141f82a407484c0c6108911449001c01049100c400a040c0340f60040389064a400000d190b16165101c0b04001c41e030301c0e507000ca011803d0040070060500400c54500641b0302c25125003d0405072190b4920915094402030710304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 37803539 1250 37802289 37802311
    0xd140c03010e060403020703020915040f02090f0d02030706050c1903020a2f04020904091b050f01090b0301030308180a0602070611181020060f0c0301060e01050d110c0c010305 77
    0x504c00081e60105480049a4045911070101e03140c5881100315075400441c5107a001c0d1600c00035104101c5940c0181c108107004540d2103122030b4616080c8105e01e144848001d43c0754011542c14400680180003512001c807840080304c1001550102004100805041c280c01581c072044004040001100c1106481c0420344000b190720307160120081001414a04124801c40c1c0105034070351580c645501060075281c01ca80050001e6100c03000011082c60b890041038001c2c000083d40c940c1035405010158111100c1c290034625580c82c644046800e035601a05c0c448642c00304490074030b800a820020010610300600c0300507031700d115500d003072421154142d0000d01c00c84c01c18081001c03c4a500c0b035542c004418217490b240a02c1281900032189070302a43c5d20300040169003490b480d05c203a0f00083c000e00c504244103035104680c40d403070721085050109208000000b80441b00c254030b654800d4024206d01c00417400049426210444c48a465410060920480d03500602c4055a070b50381c0750144540104030108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 37804789 1250 37803539 37803541
    0xe0f04060c0c0219083d0e06101503020a0c060903020703080a030f0c030506030c040507091d04050c030303160e0612010305010e060606042313020f07050c0612150d140c03010e06 78
    0x41c120541130b04030445d001d0412070007030700409441301b9800c0005014031030001e84400d45001e4481c0f00740c00119010f54201090500c8102c04194001e1088488035440e9480e00d0300244e9440d500c01007d8400440102c1c01c5010768900040000c5000001d4a08044143c4010608048400314041280d45a01c12141010304041c18480355403004600c41e11a9101030341c0100759540d17510320640d542031070f540c088061809081c914248400e070741c00707400d80a107104170140c0b0b141d48140700405a40b40070541c1c1142c14031104a440c0c0300720b0750042c10f000009032800381003a400c002056040401084090b0300a5601d07075107900030104804428020594440c00488030301e81002d003081700c200c00c070700010340300d4680c0e001221030300500664030089000c498144840c4290340e10300c1005030882e61608203020484192003540305034040e41ca41202500c040c803603423020030f00c0f00d03640700614a910490f0344c801058110241c13088080200e4070354103038541e02c0c0d0050402000760040c01d0b800d1500311030f2013032500103051b080740c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 37806039 1250 37804789 37804843
    0x30307020d080606160c050a060201020d0b0405010f0506071e0b04060c090312030e0f07060e010f080c0a1b02090109061d10050f0102030f03100303090e0f04060c0c021908 75
    0x5001d480c100b070b0080174406659441d5217400d1519012036000190320045403e40010391913070540003440b2200340a5401d103c0200402e092009940d03007070040d617610002d0010700b80135600717000c00500a0280202809246204010010304030380c00041c0e000d0b1000d0000c2c42c1044103000050061001c180440c0c50448a200e195448507001c138844441b0103c2010785074018126044400c03c03101034020036200980c2c0d402d96071840050040244001d255000c1035802089078900341c090115284107110410f80301e8070f00341204d8022952011000d50314100a80c000d05070901603241ea4032107602a00070003034000703503843c1041c81d46490078414074030b08095113403c034040001c402494800e03041194415500c40000381c1c0c81c0720050f4110300448100310116a801710410034180f22304c10707005049900a0300c5107101d09442d08002c42000300c00300e50041959102501050000785030f503000a80c0e840c05468075988d06c8030541e0000310b600228003e81450362106c010280a01c103c00e0000421a40000c014000fa1003851 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 37807289 1250 37806039 37806049
    0x9090a03080f06032b1103071104020307120905010603051009050304030b040f290c0406050307140d06080304031401060f0b070302070b03010b0d0605010302040b1206120d02030307020d0806 83
    0x611107031140c0c0e0303050007180c2161405c006001c20390100c2101d454450350690034041900c44110030f0100003070301011000b40416008011502c1203a0007100310003107a030707611003404065407020f4400420461012614100c410a5110b20402c0758440d07400443c40301c0c91420f002d860519051348035003607507241a06610006030000125801c580d8400415030083d0348608100800d02e1102502800c020b2078a188005002e031000030400c00d00010700407441c05030700d403102ca41e48103015500031280071800030400b1803400d0303020700403e204455920440700d260000a04951003510a5544404113a07072010806004000f030280800c03128655050081141d01c0ca0404094075440440c030905030303e1400000c07030000389403080c450f00020340942c003500ca50701d5a40b040c500f0013a51194811072005803901c0400304166100e0300841e030031100841e50582c10001d1040808241400141801354840a101c1018660003002d00500220425603005503480380340ca01e07006424240000113240c2001f20307800070040c2c15594 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 37808539 1250 37807289 37807291
    0x30609180b0606070f051507020309100503090106080d03091a060306040b13051b13090302030a1103120c121503030d0b0103021e0307020f070f030809010c06090c0509090a0308 77
    0x404581d00a8589101180e1907104c0c030540503201d041d1074a42c8400f84000064502550700300002415150768584a0882e01c80c0100001c19a12604400396100d281d80700700050340e00a40c0702c0000240752036a50a046144c5000b01c1818000320b42c540d5225030a003c486907114080428103030103c1400c1c905080082d44924000380000e02111042c03000c1141890303a4050404825444012900401291120a510109915031482c42446000c20031452a80729002d00e10301c06506800842c280820803006496001802d10013042600c01802800e4881040e2000306018250030101d0580c1e8180080790700c50044e0f00145210001111030903080c1c526200041200c0c4941c0b1403420000300e0303019100049004e0310420203214a45500c40c3c0641c0505411200110702408085e02140d600aa1612040d0b4a23003010340700b042d460b0311320b40070108045070010b001000d00500500d000b59404903940d498030304640300070505036002c04d6107003010700c140d051041009400003c80740c000c160510855070b000703041c860 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 37809789 1250 37808539 37808543
    0x41104061103070f050c09071e0f3c020d090e0606040503030705013329030705030103020f01110d121d06060a09050f010b07031e050a03060918 63
    0x55103003000300311240d0a000f0354000c103a011030301440703100c058104290b442c00d2030181184541500d6020a105900504015010840c0700c142d9401c4012215400e640701c0c00740201031000d11100c0118141c0c030030304c511421a0741c95455084000040b8050300a000c01d95284c41e00c2c40e05552040820141c100e0b0000d88070000c403111804460403503950395003c541c1e14021175016541601c0f02052103003c016064100341c0c854150f2882041d41d50250068044080d1003880c081d501c8420b8440051008030341001c1401e24074449448060000020451452015401240c9060000e80c0100c014002c40c903040d18202c2c90040c00740ba0614a80f03c0f801590382c1c4400c00c0915020a02c140348000307041130f40950f000100701c40d00400448078403100c00b03d042d030b865000845000e881500c0f4003401164020642c45481e010340340c1449800c2041e820100c9039800d660052405600b88005c0e21204078410f0403415941510240329500c080d140c6c9101c03c40603041c2c0e0501c0c3c012000090609a001d280b20f660302c119494815 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 37811039 1250 37809789 37809797
    0x1203081503120a080708151e04150303020f06100308160f05060705040306050a05010e0103021201020405090412200d0f0c17070203070602010c050306040b01031401030308010f0504110406 82
    0xd480c00002a140007a816510a80360402050381540e0b203410945892203421151900809a650b6035001000c2d10f14052030258058003e50114007c0324803400540504140680001880100040d110b190000c10740c0c002c40042e0b000c039a120084104c14001c440d007201c80100074946c1981541d131242c205008070a600c44600303c2c214607003001d0000080701e0103d03094000301900d559040890004040d0ba020b80000d80703000c0d042c075022980c884c3d03151146604a619510111180d42d096030b0800071110100307040038042d90740922010481c1d90304e84601c5c0b0700039131181c00c4505011079140005000350010b4101001d02416080c074a010782c0d030000c10002e504010900c0d081403d4450605c00307848120400701c0240402181500381c01a00721300c100200403190080342110915941c4400c101c1c01e07a04121500c40015006001041d45418160015003080d98141004242151000644540e0318403da00640008461031300400520385601c0c401c901601c3e040d201802070070b075041d101c2d1190384900e00c1000204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 37812289 1250 37811039 37811071
    0x90504090503120109020a02160806010603110409140103030e0306060d02011413080102040306240605090d020d03020a02090a090503070206030c040b030c04030b0c0403031205040311010c080a0501120308 89
    0x1018011503042000c07100080105503112541d41d00250001f5800394058801d0300042040d600c402d06054003100c0c0a0001010b090707091003400c0300944442042102480c0f001c1c030001ca21980d0303074001c2d42d0300f45401d249140c481d0743c55414001c0c140c40315083e03014000d8201d00e05100d4642c440c641c40b094219028200b1040820b4100704405441c8104002c1450705448aa408a0803140c10740003442140d005007410b0012000d803c03c4681c0c2d09150742803007940401046810020a801f50000d05256480200003110402c0705802040017041d16000460060300300c1800c81302188bc1c130206c05a00400300301c9080109201a5980036aa8400d0000c043d103d800040001034200c1e50482c11603002e003003034008858480c201070706118401e80141c0011241c007042c00000514203030f024025541201e03050350310510961071100d1400000e160190098040088101c2d051420000134011240309003096070301d900d10303031500600c100304492045c1c01448198000c108c481c0c1c04250720031041600310001c000b40c4a21 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 37813539 1250 37812289 37812293
    0x60914010806060d0c0201050912040b03150d06050408030a1d0d050c0f0715030e030a08060f040902041109030705060a08070807020715121805190f080d050106090905060109050409 79
    0xf41c0a04144201c0950505036140407013941034010b04d02030b01510080b948a260707001c0f2a54035500807400386c0900309030207000203422450741d81e2808540040141c18172014200e2512200280c1d03104480698490b0400411b110700e0344102d08c60140100041808681d40c00b031412240d54840d090b5071003503020400b01040511401030280400c001d161104402c07a98400d40d01c582354102404503d4040700800d10745411800060350102c125103a40c2840d035101460ba6540504100c0c50328654550260415a038901110041c1c489100300d07072603020301c00d40b180d403500701c2d08040500d80a01d0781c0005000c1c000c180300c0c40c0e0003240c01004d65500001c650500c060f00d0350301c01c10100d20300707e10b07980218035003244245494449034101440718200490404280020380d4a00c1c3e401011403d02140102507602001d10192036240452909003070302d100d00c40309107240c1a40c2e101c8803010b030800b5a50540c2240e940004021454000948030010001e05000f88018030f0310000182c042581ca10906010396240c200c0c1100f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 37814789 1250 37813539 37813549
    0xb090402090604150908120705070303110a120306140a030804060804240f0c030e0a0605100f0803210f0411060405130b0405070c080f0a02030403050a06050907060914010806 76
    0x203482c2a4200c2020810441c4c40108915014803952199010340300f0f0f00040b496030007044034102ca410500030b01d40c03c1d155550860308401034070407030034142c01145144c0000031110035692044070346982c2d001c6070003428004070401c0c107031503822818401e0706440400c100144440301620100e40403820442074035038a9040120b40ca0000111040041d0300041003407250707042c541c1c03102551140d800c401b000706400c070040c01e4040b550564202021540230840400000310140c000e41e13030203420501d009481ca641c0e50b51500b8003514942002d046034002084000c0d0600141d05031004412000380c5080c180d08080308d140502032000342020708401078084007010140c60300021200104005480401011002901040140f0345441264859401c6c1004284114030a0010714400390304441c100340703002d122030810095a48450201c9080d8001408000040b40041c03004290850003203201160b45d2400500d80c9040c00c0040d0841c8040c0149444280b100c10079a0001002c4041300f03007000801e82c2c8580e4001303a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 37816039 1250 37814789 37814797
    0xe060a0e15060909010308040f090204060507020d060209031603140309011d1507030302090a060e060a0305060307030c17060a1116050a0c12060b090705030417070204060306060e0a060b0904020906 86
    0xa600111072030000010002464003c0044651842027420000d480d000700c031059124906c52000010418003100001d032a000d8607071f0105600c40c1d02c0040c9802c02140103e402d04000c1c00c503d11540c2c0c1c0c0ea003410400d120145c881441c001210b0405540f0704100c5400103008010b0703a5400c0da0903400c07080700302e03105070711034992103c0c10300c2d044503001c0d480d61190f180081c0a5408811894000c00100c400010760300e0158111030031203840100806d0901c80b60380802c070001e1100500e60381e45032248070f4000001c038400d40c4015010b04103111402c00c600b00e04004070b5191040141081c0000352420084150004980c000c0d20340340e40310840760036030080b104c1c00c001d07151012014029098401c04a030000319080b00320941e1001d2032040c1d07828024035040c0c5080202003d411140c000c0842c40810004000400e042c0d58004035000c01c20303409060901d02c6d004542202c005400440c0e0b9240c0d514024401c0c00d080000845c3e1003104210701740300321420011140e0003401110324190050380c01013240d900f15030b140b805035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 37817289 1250 37816039 37816057
    0xd050307020111121806040308010b0702041b030e16080606011d09100f0e04110d030903060219030e240703020912030901091205060c070314030403090e060a0e1506 72
    0x12540718074120f6103100e0700400544106201e03111003401442d0f400400b06800d485a501500c5510492f0300e405541d100700d41c000034089900c16030b256086694001101900010881c040d6400074030090b0301007400740b500321064101c400c40d5030b0b0080304008404e00020800d0713002c0c2d4203180481c18005400c030551864603882112982c841d01100401002c00c0103007141800b1074035400c8014100c240d640d28044814941950f0107043c01720b0005c01c034003e0b402c01d0403041184520910340740d1402942c030b41718a0101e8208011515040d40f990b450302038481d0b40f500581d0303076a4100780d000d040038a04210300f441800e0f1480b942d14801d95940307000500224000d5050321160400030f81403110752051150b0707480d240d40c85041401c3c0030941524021030040710340c00c50b40503803c0d4004c0003880c40d611800710f15101a08008021000c0080d0382d00003002c03410060300a10b001d24460b0300c890b40c0650900d50040b9a40100070407590003030049080c2008000c031361138012508080e2042d260080c594950f40421454400c007108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 37818539 1250 37817289 37817321
    0x12070f0807021e010306150212070302030f03101a0301050306072f060108010510030213020705010209060f03041202011b0e0a050a031a06030703080405041806050a090519050d0503070201 82
    0x7a0507100d0070341c3c19100590400742e030100001d54446e0b284160300003101d40341c5401a0301c0300c85500c070621140b80041850f04d0090041320700b81784400103004100e0740116030041101c20403003070800c1004504010b0705d10040b00c4048190440d030420300030907541d000082110041040180042c501094145116021800b40ca03a03207208666090f80056038400d800c2c030440e602036190800090804070a40301c84c4050301d9005040e40c034140c443c1307582240a500214400e42c0c45540c20000c0c0c1e480c3e56607400c001d00f001c0c89940e0601e40c803850181010070303200c6403a45200b0b0035a410006a1041c0001e19030450b201e200c502d040c40c165455080000c0350001009402c000d03044080c1003c04030a000003008000b41c4030b90010a60102540c4003030a06032100f0b05032100600958044c001404649030503005200c40081302d00884214000c0d0b40c403444180c42080e1114070082d903655a545d0203014080c4014160a06000900003013050a076840700e03566000d0b01c59200400c6804404a40246d01c06c0d0894500b03000380d284 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 37819789 1250 37818539 37818559
    0x20706060801021603091d071809091101031404030e060d0b040203180f030910030f0b1806030705190b09060d05090c0109051f05030c0c030d0b010e0312070f080702 72
    0x20704a865801c04003680840d00589000030006225281f442c075030f21301e2030072212942d00d4000060700d200c007006c00d042040b01011300000c40c80c0340e503078030601091341d028084072503ea086800000d42114441d20725480b0710409101000003007904160200035241064a030301e55115140c001c020018200b24101c82d82c07050000080c40202c10110a01022000b07000f000d4810a00c0e0409106559101d400c0020317400c2074048111440e42e6002c1d500c4050414202d100c040380c205e86000000b000c0c904104411500708828200340006070608000072405410140c451070f42d11103011040c60303041d210902c1040c40202d130005100c0b40540302c0b502642d40c040045d100c240520300307109801c16210020104550300041011900140300d1928a05085481d01902200b4481082070942100c003503200401000508004018284102604000911103940c518100007003030406800018001d01c908803003184a80d00c1400c40034682d240c210101c840c459402680e03051618120b02c6c00360a00e000e000406584064501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 37821039 1250 37819789 37819807
    0xd020d060f090b060a080406180b090105040308180a0209070203071b03020f010503040f02040b0a080d02010213080a0b0c0913050403080a0509010c1b0c03050d02030a03140c0d02070606080102 84
    0x210700720180d4052440c18801c0640201c00d1201c40d014144c815070010749420302250103d50709078480030342c5400303600f0000102c00c141d03201c0d07201a48060315480c2c2c540e0b40d640100b0092641c0a00c0203070700a584880306d01c40300d1402200c41d660b07802200401a2003284c02a01091480f4000c00480300555070103000c04060842144600100c0e40c0180320a81c01441403201c21051580300d42c089910460f030040701d070003007008a9000d101c010300c030240307556802104122000c61185400c1140d806c482c080c95001682c0d070517000785483d0841071103a12850041d4055070740d0000044d4054141580403140a00d19a26111400c0025200c0204001d05002b05403418060109150303000306074a00c00c200c001014003071038a03402006400c03108042006400a00180c07101c105407924005101c110500410385541080d480ea12001d04101d600c07240300d40503a10014400c4522500b501a00118600c210708101051502e0310f9403060724854003015200090b0700066000800200c1d9101b07201807ca060000c544901c810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 37822289 1250 37821039 37821059
    0x8190b01060216031202010f05271c0f02030d020708030916240314090109021503010f0e07030f0e01050a0f050112020103020307110a03020a12020303100501050d020d06 74
    0x1400096960200080010540d580009500280008414a0118040d02e16107031a820541001c540c8400c554a405882d00c16020034014280103400c01c0c1c0204606490b00401000c3c401444229140c4a401c60310b0034144140c00d01440a4a131001d0741080c0001d245082d100701c0c1144641d00c012a041c0d031000c0307600000c0c066030300c001c0c5101c0c0c41d25400b1200000707040c00c8581480c22461250b0808594541004600105541011010b00c0e555040104000c0f0f40748400c0c0c880c030f07071045038810026035698060038203510b00380301004a41000c5c040c0107459541000c6500e01c6640041c084d00c080c1400c003a0204101520950103000d0080c103400d42001500101110503028242c04c2d00e00052083c1441a048141e07a140c2c81002e040301c0192411503203c01503580150042d400040c44002846822521000074140600a0150052003a8040c03c09240e442c5410100408861031380c108640c414020403003c0300180c400d00c4155182420704513107a80ca4801641d0282c401d84446001143c02d1100c000b6040410f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 37823539 1250 37822289 37822333
    0x60313050303071e0e0a0506160804081b150306040b010e040504061505011d0d0201110304060c12030504020927030a0207080c0306040812060415060c02010f02060105030d1808 77
    0x3014010001c4130302c1c103c008a0300001744124541d40150041010001813038448000d2040c50308a011540400f5015103500182c0e03001a807000402781c00c5108503a42d240c803524081054039100304e8a1100707003050f420700d60f907240c080100b501e03000315510b500803940c030380c015400c000c6103100081c014422440e1900d8454090a0307140358100040f030381c13908041015802002d1400e11654002c2214410014013810080b140e400c1e00b5040e03050001060f200290048180010000f50400e500e60010010141ca082601d54403020b00704000c152a201c00c2c44016513641f03211a8001042441400c034085144a1000e900206118079210621000a0141c0819008541308040354480c0b4107613038410481409064450070200c8005081003c2013089008107418446c0c61a000400540700084c40c004000d9140c400c120035070410800704920314000d804540c0d11003410807000d41e640c8042c00265140401080c0e66000d10f000000a005001000c0c81d0041c40b5024041c00030420541141c20004c9403d0a160300441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 37824789 1250 37823539 37823567
    0x9080901080f0106050d150306180506010504060302060d0e010f0609060e06030d08060111070306050a0b041505010207060507110d08030708090705030a12021525020a05060606031305030307 83
    0x4096000502c40700c8003401c1c0e45040302c540d503d60500c0c0c03075a22881d0400400c110181c070810260741e80c001001254031032168090181c441d8098096100d40341c2041454914160301051095003044400c0c80140ca03080c050f1626400d0b803240201310528490f49250250205403d01100c2a29040700064400c01d6034010000320707204206100c8058840c4e000b4161220b000b81803240200c1c60326401318a003544a0402e6490881044080c0e9034039540f01d42d542020741d0016640001e0b000d45a0941c2e1311a868944540d2120034103413aa000c20301c620300310010351526031b41e101c1c61050100209201c8107001c02d200d84001d4000c001040c0e0442c90150340f419a0103500192912000200c1040c005909144000b4880060360f0b030040041c0340050695a4041303180700c4c0702d2420740440c05003510349004c5500c420961400b580da600c540003045a07414240720000f419000c0c0d55811548059036100100e400070500310380145050720410760340e650b48880d1580034440000000c2061200108201c509640003117a000740c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 37826039 1250 37824789 37824797
    0x1b0f07060f03021b010209180603030a0f05070f05060a0b0103090302060714070c090603050c03060405070b03060a09020307091401020a020904020418050a050105090c0906010813060b040204030f142a03070909080901 94
    0x282c910301040004230381120a140c065004200c00140c0501502c0215100002d0740b61980c60306107150340300d11000c4161907007280e440c0d0004043c021f1180d00743c020881e80040178a810031a04402d0349000b5036405000e4076210a028602c0707044140414124100c8400e0341e000500c14800d296590788c50b80c010000d903c0260b401d070041103081c420b01d10b80450600e000c0d580107401440e111307040ca100c0c0111984003404280c3e0110301c4240011354140240042c511580060712441851441d10300d42000315036911209034115000714010400603541c83c51344c40c1c0c1280d019140007803289100903074007c1900007003d018000c0d100340c0d20860200b00054028911070340780072007038901c034101c03801c18032103203500642c3c4050104135607c0020791143e0002c81190300050043c3c40c0491084604008142241d00a8005682140003056601e00b40006130400e059a00405001041c40010b021200c1c880c00d01a4180150341e070080e1070700c824007560104407107000b4010446007000b0f240f44e1460601c11030b03804001d42501007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 37827289 1250 37826039 37826059
    0x30c0a0b01050a030510050601030b0a0e04050f01200c010e010509030406090902041503050405280308090721050c04111209060c1c090b07051b0f07060f03021b010209 73
    0x3070f003010303040c1c3d1007120303448402803c08140581310800a130600600d400c1c10955a0300500b00907580308106180104005000c00d0b48900f41414440c0c00c20080c00c00c0303041030340e0401004410a0106881c8050040100200240c8800c03261f10100d0162504000858142d03003064144581c00c0030110003130080701c0c1d85880d0005503998600107642a405144a81e04489900c0140901d10301c0c066084164840e1041e016140b0022100c609822400c0741d4100c41c0c007040008004400c101500110415008104036004040c2981307003004000741d4007180021015600b003208081001c02608000d0400d500344010818410040311610b103100b190800010f001700e0500314070114900b000c020030214020002c0024440ca081e201d007041e0b86c03211400d5401240031a98408a11002c9004801d540d80600c4181c6d0b55141d0740c804c40302c1001d02d4402620300465079500030540d810441000040c010084420509051704d10080d2408190000c1c05450203000303441c184940304000c0c200c412350080014440460f00034400d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 37828539 1250 37827289 37827299
    0x213080f070303020a0611090307030303020a1209020a120c0306020307031b03140c0c19050d09150e0112110c070e0a020906162105040504062123030c0a0b01 69
    0x580d00c0c0c54403020f000750300300708103010206005405c42e803c5a10f002d0740507481c214a80011902c1c00c002070b4010750001e5808200c0407901540b100504842c0019184140b11508007a00050034044d044e1180d01903035600f0b0b000f0142004960800030008541050085440740780001303000d00034040c6048005001801c0458519066009200e900e500c441d0582403405039645880c4d45a445a00410134501148200ca02203020f00212a01d505100361060002c0c01c0f9200c0c0ca01c401418489003504019072500b400a201e00c20b8640c400a00c00351200c0928141c90403030001340c440002416500b12031034a2003c002038200c2015800501c04d021124100142140c035070391081182c0032030150a000e141d00090802801c000040b00c2c50107120554010146094901105500050106440c4000303002007180414208024600307071003610028094904680544100143d41500c0012400401041804d000e46c280303007065000034688403945582802c4030b42d40c4580c610690350301c0340405012909202490300106d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 37829789 1250 37828539 37828543
    0x1303090e010806070e040e0708160b09031506010c1e02030609010b030d05090a0e040b0f06060702010f0c031106070203040f0506130e04050c04050408030103030201050a05040c1511010213080f 84
    0x4102d030342040c00b40c0010307180c1c00300850b03030301e000f80300007590081d110250800d2000c030511a500040c00700400800c01b551005000c4501c1d08490307800260759400600c07500c07890340c5000c1440c90013400900700d295502c1d92583c005807003501c03c544001d0209036040d00e84030701150201602c40c8007907008400306c0f106940c80000316800d0b074405000ba9074141d08282c0680340c20030b0185001d400c1d45900103098111264540310541c50842c4100c40640e10362200b41c082c0103003a00c2a080c1507400420a131015450311300c0b181c0019151424082d16281001803c103640010316205080c00307001004607000303649181c00d044000a40d250020f00451682c3d40000304001414503001d821100c0419980318044485482d00d06100b01c4030400410584246c0100703a40700301681d49520915108610900a59441e5411400c2c0203007111001000865a40d2030007043c0808a128a84070304126511240c00b80c0040ca101c00084034030031203e030382c151015800030030308481902034801164140e403842011948490382c40700410b5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 37831039 1250 37829789 37829791
    0x90f0c0a0605090a03140a1401060501080402090414010603060e010b040b0906040c050c06040f03030501050603060d0602030c0405030303090105060f010206010f090209040e19030201050714090d0201020c06031303090e 95
    0x103500009215081040502072000342603003c80c001c000104099a940321a040c6c0c00c0c24510001085d00000d03680c2c2c0400441e91840500540c0b00d400802446c0d0034400040c2c440384010f40080c0c490f6400c9000a400c000d10700389180b400300710010090240582d6441d20b0005007000040090181d420038040c1d101d107003440d10445c0310158004102c1d0030991688424040200140c041d01c80c1000340821151140c13503c1040494015441145010000080d0f410010101c401c1a00090b00c41c1d4030030400e04c6000d954000f60600400d4020b100140d5980701e039020070005115962040f6094000882049123403001988400c6c0f1a00080e101100e000107401c0c01280c45400c24056080c07151060f20040c80040700c10303405880d54900c050000030794080882002807034030f002c40401c540c02c2d007403088113a81010303421b005040d0040454281010b01c00280c1e00904840c0c050f240d0018041e1010810a03415a07100700301007611034002405d480d40e03d0920a00c004012141503600303038049030b111000040c1e040007502d052 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 37832289 1250 37831039 37831063
    0x607021e04110a08040f03020f0714040609020406020604140c040914010f0209090705070c050607050a1101021209011202070609080703020712020d020405100504110909100602030406050a0306081203090f 89
    0x40d13144c03079403159102e0b548010184002e07400c601c28081d941032a0b041c2044000040e00e004041c54581007401302c10442540c1b11508160302207070041c802080f480343c00003031180d0002d0b8060403080f400d035016401c4615081c400d444490f407003410722090388140006001d0f403100180c0568002d10800540c51401c000380d10600c100c0030b4000f4a40000280110f110f0006003045502ca01c0310254041e5580c40040c0d0700344c116000c00e580315001340d02c8250400c03070a40101001c0c1c150a00140249114032f0f0204101800780310042e50501011120070000c00010354110b03499281e010340708104207010350521030350540181c40102c015108250021606c040200719801d40f255004094801055040d409e01c009440702411140c1c069400c0c0d071002c40d10b07503501c0c06400001600300f007946031281d0860041025116016107240c01400c8041824442964048222000e546043c18603541e01c0d265480d04038014406940070301290700a0181100070091124002c0d809840064112000ca1030004811901c80c0f866041f2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 37833539 1250 37832289 37832297
    0x30e0316050f01090c06180302030a060e0607020a05060703020714030c0102040e0f0f0c090f09090105070e060c060a2f0d2403110103150807030201080108030a02060c090607021e04110a 81
    0x10410200303208501601c7c0800e84100406882d654903400300f45007400c03000086542c0c64403012060700c4144200803080c1e01c00c90703502c01000c009000342c0b941911188040c00b00c1080540005500080c04a03074802140d44016040403290383d0001d402940f8000e40160207001c60601090000c6440c591a4862a600400d200101d5801513145d0a258151a03400000d03456000300a030b00301c0d00001d40c1c842c10542e1140b41e46100200d09407401c003074000c00c05000d1324007040c41030b13074144800501da1200140c0303503a12114515000562503180c002c024031007580c981101083c10b41c40c802e0400c018103880c014100d40c1b41441020310010003d500c240014242c24041d00049091401042010845001a04101da0018100003c1041c1c0310b41c01d0200403041500801401d42c400d203010400c650303105512600402480740514141214080c0003522141c01800c0c118480b440891070280c103580c1d6404070b54150343d000380544000041c1403085500c510000300c0080c0300d54a00709000d1140d800c2c10040340c90700041a99 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 37834789 1250 37833539 37833563
    0x607050406022802030102071b090207050303190b0607061a221104050a080703050c01050f0a0809151609240309170313060c020304030c05010c0201030e0316050f0109 73
    0x1070f508140d01506481d074080d81c414283d40c0b8056202880107140c0d1600944c0c1024043c1c108018030040c0008a03881084160301c10480c0301c000c61004130549070401c5101400d02403078070410a02601030701100001c10741c0101d001503407408120081d400310540c445c1420094040c90f03441401c000012000c2e030075040605640c1c00d20310382800d2240e03200c6610303e82061070070341c1842c0c0c552002c5903511055401501c45603100540910178003001700403510540000f4a0060300d883c950009040742d500482c2c021a050040d1100451002c04c005c0c491403400c00282e60300b900e072a2800396031002c62080c1c46441e18001c22482c5e1070118407401280d2b504034241c0d000b807214240c08480319404134010000960152041e00c070000c40c90300f60f071442500560082d0491500340282c40a28140034007200c04100d141340641d0300420013003001800752000c800c1200d509080084c129051400180c2c06401242c40d108080e0200044200c81074030759420741c6454a01500c210b6070f42c00b40308031185080390320b600001b40041071104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 37836039 1250 37834789 37834813
    0x120106060507110102061306020c0f0319080109050c07150e0d0518030a0b0133020703030f03140105010309080d050a060602070602070f15020f07140f0d02090103030305090102070506010f08060705040602 89
    0x10300208ac0b02400181242c00c1a49007203001800c580000c0f00059840a030003400f110201c2d4005049409000d00c0a01000103041151724013210b031284140041c8500d04004c05141800303015485401098a218182c84803940e045800a15071f0b44000d00c200041c40305003400c8041070800250703601c181e650009543d0304503401d084030704405a5049151011412900341d50f04d0b441c0100b84000400c0d21225001018800c2c10761402230b2296209800140030145081900b4600c2c040f40703011039045030b400303090028aa03038090402d10301522410035102c46890910050001425442e8482e60407545582d0036113500c00e03100c060480e164180c1d880760740c2c42c9010319070042c00780c2d0803150300301521106c29004a03084082021251400c008541e403158200c81c43c0b151b01902c050504801e00100faa600300c800d101c200307107250b000619040045c0006410140e40c0d50003c0c401c01025812a41e455810804449443da074400c25100700c61180d0148601030300178032000c601c8450185003a2419140550091301c03c2402071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 37837289 1250 37836039 37836041
    0x80402011b0c08010507020613080a030c050409090c17030c030301030204051e0a0b0102010c090b03040605061c110315101202010504031502030601030b030c0d030806120106060507110102061306 85
    0x800341d41a5207031080700288003090381e034000b8000400003040d00c0c500308034040e0030010700030584103d010114031464000303205034003114540c01c0079080005801201000c1161180103540011111524140120f400d1100440119085805c0c44804404032807180950a81b00e00820018041a600500040c0010328058101e90361001c0303401c0990170400e1240554040d8450103807881d0300b60f07503500c2a2001031035038213026007044041c080c00c20f108454034004412046110040000d803196581f81e011a0960f40c134000762070712820843d81600b0814100f4180100742d01c24054038148240315a4550f4907911882a40e001d00c5174080ca041c90b014180350903404410481e080300c0072030400508104c0400003032100c0454405960300d4000c0140c032881c2000024003100d0314001d02910a52001090764407130740d02d1070161405a9490300c0c0600d207588035100030402f24407000004904c19424603001068165004000d801c3e0f084c0940010460341d524200166140c013030550f02c030607100c180030000401050745 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 37838539 1250 37837289 37837307
    0x102070f0306090f051501031b0b030a051506040602070e01090501050a06050c012901110105040512070602090901060309020a0f080c12030909070503061801080c04110d060e0105100305040308040201 87
    0x40f1001c02d0050042e61780c150030100201242150000604018410700c00041004c0301c03140ba0a607808140203081001c503103a140001050b0043c507170384078000110300e00c42d10b0484001c1e4402c050305ca070f84c8035034031808065103500c100d01941002403111400018404d1050113454122207026008001550400c013003121280d11440c6c081c81c040d0340380e07003001d0013032007050400c90b03805180c26030119041d1958600052507455562109141c507030500c02404007150f07000c81d94030301000c1c0d002840369407003016250010280c010030911aa006011000004180b90560003c10070107201321001c03458151503040e070300c151006600814003039034005000d81105040c22809140c81031903d00403070f82803030403940c005083e1010850b08803001039070101c06d014050500444009100180080090044d03040c090002c1d1f6403003010700114402c9466840d03c110162400c02240c10844111105101c402e4881e00c108a80d610700384121801801c0000300006094030901c10745025980c103903101c11041d00c0b079400460300154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 37839789 1250 37838539 37838543
    0x402070206040b040803040603050c0309060105220203010308030703060b041503090c050d11030c06040602061303050415020105070f0504051c080d09030e10020111030a0e07090509030702030601050102070f030609 93
    0x1d0401011401c15a140c01410061049030000e5580c1d5041034030080c1503800250452001c1c60061050000701c1c54040b40c45410346100b034400409099540c00000392801c0c0003084800c1080c800400801404441001944500c1c819242400002c0d600e01c3e55030030ba0301c5144241302c100e290300e42186001d50701c01e811031003019004000c80903590f91140001100c80b04002000c4600c07404c031010030203280c00c09006201c1d00304011a0054145071901d08040d4491000900c03244254490020040806001e441640c000d88004088044610700360790003e8002d00080d1383c0c1002250810603800c5056100d00122070590740301030070b4106403103600440309890307440444013154451000d0042408110092144d0042a4080d84d10141a80d8031f11042c809580000d980c0d00d400c590400318405545c801e840100e0350040f0201c0000a88000c48207c01c50414880381c015107040750070541800803913840000a096824021001e50b1203c0c0d80c0d400041e40c3c2d40c0342500c68501008240d41d41040444c07991360090000c18 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 37841039 1250 37839789 37839799
    0x6010309080415090b0f0f1b030a09061206180b15030c18040b09010e10050316050102060f0601080109091e06050f070201050403080c0304020f0a0f0602010f060b04030204020702 78
    0x2055450584541050300f20504441001e45840580d80d4001c21810041010400d4103241c0807000d10b03551540e00c1510b407000315102000842100b800c0e02c000100340c0402e4142d00b620f40325036420000414403605031207038030001a00743d07140c907854030b98920880741214000e5400801201c2150062009083c0040b03c85a1010b019003110600309144801544035810746000e51740c2e10030345100750f072086404022840e400b684c60411074048035216a804541134488028130800c0540e283c03c014000505250003441e0140a030b40c200c240b0f4100b45100c2d4400b5030300c09030255541c66503060041d8010038821203040b8002400b1b400100913040d0103602030f480c0640100b042e00030071002806080403400390400d003295125594000c201845e10280032440d0801500d100902c69401c0c00c0e02c005116120150101c100c042d070000124085681303000300c00741c0400018000309819685c540e00704000540b02d1190310059402c0000211405001d0300c2498251480c000d034a0382814195000c0c0070082d044414126080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 37842289 1250 37841039 37841051
    0xe0901150501080903120405161205060a020306120f0303061008070c0219031b08070f030302120d0b0d05010902100f090b0d060506030103050c100302091305070302041a03010f050d0201050a0305060103 88
    0x100841b00220391180f8000e000501c50411020300c0030030090703919845450302e0201055094002540801c00c242c00c01c03c000c00c090b8407a10f6a200148103480501210142d5104800b9000504103011010318441d0400b03da00342d600170281042980e21000450b101c40010391503070001c00051500603140b04112001030301c40c11459071030750b50764080385e001140c805150454100c0d0802806104004e0800070f4140324011208241c0746640181d6588840c45001581802c0442c80c01401d409a038000154810020304650b072250b0141443c50007405c03c0300040e80a0300c1078079003054081d4000e403581c510320b020b80c1d518002d110340380242c055840d030840541d640c0001e8032502c000a8654400c1c020f58061406040070f01148082a41001040303c0c901c02c404040c5030051100804079501c0982d00d07408090590400304042e83d4100c0220000d22864200ea9100000c44110102410403000a107040c3c42840c0d00319881d00d85c8407810080303e2000c03c00c1c0240024810461102460300c80d8104a070492010304010442e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 37843539 1250 37842289 37842307
    0xf09050732090d0f0b0705070812190207060207020405100609120204020d051806011409060120160302030601090504050a02060c0708060a0903021b01051b0c04020309070e0901150501080903 83
    0xf0441240c142c482002242d440003d00042c0c00c2004d81281c102e05245180ca0304a540d541203500540790070b040508aa000010329190040030380021100901e101117550354401c1c500380c00203405c4030000ba07000d50702d0040000c99104108150300e09450f802e444080c0413502e011001290210b0044040381c01a40130321283c12180b01768028103000c1d0200080308060300000d616010302d0004140d000c0181030000ca20280303810b848134200960044420301c0d10f40b03550342c00039580d104078044041001c0fa003485a4004544031040c0a10f940c6d0682c0c0c803c400350b40044c2d0313a8040300c0c815a40203031005003d50b0030880341c0317000610f03101d40140f17030a9000e02e0035113a025584040d001d0601008480103001c0c20344076030918080541c1401070301102d824056400700022051000209203000340b510031900200703c407081001e80b000c10000c0c002c40e0080100255a00c3c509003004544410f8288101642c851407500461203940060050881c2c0c41002d004d8426502e1070300004490b1202c0180030540c0302d000401ca1006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 37844789 1250 37843539 37843549
    0x10b0108060d0f1e0b150d150e06010e070306090603021e121005100510090314010b0d06020403021203040e0f0c040510030605010207050f030303010b0a0e06040f0905073209 76
    0x58004c40401e6071280c901c8141404165130000030030302000002e400781d400149a54007491410b41c15042020803c1c0052215642c1d03005251000700e0f0a154810100002000300d4040c49442c031400095a040c021070703540b40b00203070680391301d80402076000c201c2e280c500340481002034140b1041d0200030103407102d842101200c03508105401360030602c042c0c3c9440401000d0303044045000d00414007616800d0882013043d400401d07224080c00700600034282010f4400c0100001d40250181d1700b0020801a84180c0605c0d040c4022741c0705100c228021801c2c100e10030781050f008019601111510f0608a12a90781d0b643c0ea581a8400140350030600b034400d00012506407280d0441200e04203064070005809070500c000a8034050107540000d21400314420188403545000c019681103985100d41103440300700041d825201c03501e080c003e1a0b003200c800710700050050300008030a811124940d004120035150407508582d00c40801c0e0209190500070504c0d26108040020007554202d45200d100b403c140021002031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 37846039 1250 37844789 37844813
    0x605030f0102180f060909070215100b0910021c09050a0611060c0d060905040803060406150f1803240c0c120503040606091b09080f0a0b040f050703150e010b0108060d0f 74
    0x81c006a010303080c00b4a076192b8125210ba0865810400c4691641c0b0b0401440c060b03109881100e40600460702001d000d00c0d0080007880d0910100620401d080b8192050041c070080312407181078810485480c0000d03034036009608071040007242d81c000d400076036503440700035046a0200c048076040c50b994034000211a14503109035809079103d8010710f03550703050030307030811041d10100c1d00030f1156100980d10400c0381c2c1d60030040d404100c8080d400d01c0c0200200300204400441d80c4ca0380090a1400310160068034108117030240a006500c112003000740c00c40703c0c80210392031644400020701065030a1660b8203014091070266511910440c000300301c0340c0d02c0c0d07100c030300640761100944013481c14400d0394400000d030020365200140820400901c90030b400032103025910b005425004d030858408401182c1401b826148459145800a00700c5042c6940ca14040d5010164480044100c40c5841015001c040043c01461850310701652000e400381c840804000c203011848108841c032003240300300031000941001c080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 37847289 1250 37846039 37846051
    0x5070816021f0509040908070204060e091506010c02120309030a080901090e041a04051207111c0c060e03190506060109060c0b16050c0a060605030f0102180f060909 72
    0xd0a0010244188052014100361110742c5020a071080064141e014042e540040400c4902150b004e0040c14030352a58401c9100183d0040d04207000400d07075010402806001d90070f60030848080c00c20340b02d0004908081520032034006824982158050310302030f60041210f000000c10b4914080b210383c0040d240c2401c0c04030031150301c0030110b084003e543e0840702400040c000c10001ea5a545019683c204415150b02c00c2603540116402c08203062200c20850440e000610140c081d035100f070a8140035140c00e0403500030714440c0713031070480b690a4058030028941d081a4403041101c1c116090881c2521a2a466040685c00d80700c0e805d029401c009000ca42c40380464020303c00741555003004000100441307126080340c401e200607028180d000a152340e007241d90062000209002d510704d0711008442074401d0907010501c0d031080b80b0030b040500071a45d000108a81044007100c641141030a1100c3c03e03401a03222030540e828a86682201da42880107405aa00b10700420301894180d0304070009150711415140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 37848539 1250 37847289 37847317
    0xf180103080906160507080d03060b0913150308040503010f1b0807021204180b0d030507080c0a02040e0105071d06090f0a0e07080106030c2109030c0206030910050c03070c0b07050708 80
    0xc000c0c7c8542440080f442064510b4180a45401e1900c000c1c2c3e00c0c4501c01420303000303458210b90324460b041c060f840080c0e0b02d00041c0c031250056542c2c1c01d00710443e400a01804c2c2c440d502c3c1040381ea6400781c0c503100d13400c01d450702d04400e202500313100581500c0c40c00c801482c103070a502542c0c0700c070304602403950020300260540c04240c00000c00458849000c4901e00c09070b00340078811507001440880d4011094904050b80400100c0e030742e03109820118201052080029000703402e0000c811040c52041d04020712503141695205041e85000b005d1304c0204e06080c5c01c454221f0803c001104071400c100380d14122003d0003404200120b581d40150410080c012113030700c000584008010b1100f0343d4180942600640c1c1880c0003824030651070190013286c5014004584041e40e15045602094003807150101d066400800c03039030f00c030b2510900f09525050022a10400a881c01c1c0000e00c066100100f9071740940c40a45d5040c24608482d90741410060005e071091044c440e0900c240c00018032150008e10b0b080c282c0f126 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 37849789 1250 37848539 37848553
    0x80a1208060f10120506190308030a0209060403031d0103060b040510030912020a020907020a0c06030b12010603050709060b0711060c100203010303210e1b010c05010207060b0f1801030809061605 85
    0x602c4e002141c4001d4445840368440454502805045d0400c843c29a03410800307596032510350041d01d4000384240348070150032100101c0e0000a064110003092084c4030b500352407034000307011503004504640c1070b0301441c2a011401e020030f02050600229074050048076003000508182a82c031012a007803070f1040d91400580c01080c0c0d540031814a000076a4000b0b02500003040d83c08074940d20301000040a00401c8100342c2d881170079012542c0d801c0d080f41901c0c0d80d448000c0100c1e54807420301c692101a64084e545403641444000114000907030129204d5981082200061204c1c007030400100c0c2c1d1003140d21100c0351144098141d0010880c0c8001c5000314440d032100b59802880032501d40c40b4040204100002d10310b087e000f908849004902c80e031081410240f2282401107510050310790304902c0e200503145610115408040140950091074003800440d602e504050706801040003200102c4c8600c00c03030560400c01000050744500c007900207000001d01060505c0030780c2c214440031203541e48080d40c0c3c50348900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 37851039 1250 37849789 37849817
    0x60315061103120118060608010b030c03130f0c080607050c0a0b0a0b0603150f0609010f08040201120f0203010f15020a0f060b10030203150303030112170d0c0f09080a1208060f10 78
    0x440703a2402047c9904260341c041d03152a64081d820702005000c43c159490001c006540603036407460041d400e41c0c0c440000d007074000a505103520f800340d05009064543c8603220124031550b002d80f042d21544100d100040c5583e1b150346c0e0b66600c400a0142c019102c4ca51501d0300803c4a5903820080c52040141c0d40001034074003401c0042143c0b0070928a0502e010300c0081120032407a1b43e2001d03000c04119942e050900280d00c0394801210f117440321400120310103181c40c071200040452500114101e800f106d0f20245a0f5032940d181c0c03a0b0184013520b224015a0001e250742e00019403407141000d1040c001e042c0061001c0c0a400402d0041d08c81d0001007001a500000f0083e00402c0c80107440c002910a400a500310340c10884282c1c0e003440003120107400445015641503490340d0000c21540d54901c042030600142140b2000604501c5c00b80040c0000b14034401004a030a8800003024002c5c990042800c0e6490062804241e450a0700904a20b40000880c1d929042644406650103d94a11680c2e40041003640d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 37852289 1250 37851039 37851041
    0x801021b060c030712090311010c050c07050906100807020703050102040b0919030809060c011119080702120f07020414280203010b040608070504080609030a09060315061103120118 79
    0x2072052442d24800d105124001d54016140340100d40e943d1800a103086032414140e41d03110300c032215918150300313000864403c5944900034000c407002440c111014940c84070b00300850250112480c035084006a038208228038840c2da151600902e041c010380e15140e441e0b0303e81c0d500760303405034201400f100000104440315040100303540e0280d00c05030a4840e4000c1c119520048544200403000d48540004503480128441c02e40c44004614210441c166440301c2d000011822944241609004601c03000005003505c0d00104212006140a446d040d00d0484801a43c550381e400064059801c19500c0040102132048540c0c00c0d40509440d02900340196060740000c000410381c2d06003100f080c3d0040c030041110b008010141c030183c5140c0e0901a00e10750364039404541c01d02440c0c0c4036480c1e03441a101400712000001c0003c00b0402404e0b0f50704003050341c8452050381a85c00101c3d21001c0311103284000c11150744200a03000c4a801d100042d640390010300b00f1440e112200c01c0e0085c0300042480010050240c00c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 37853539 1250 37852289 37852291
    0x3061a03030304050a030f09050a0e010603050606180103051015020f010501050102030702090c030c0c0601060905031c0806010c020103110c010506030c0d020603010905060604030b011e080c0604030206070c0801021b06 95
    0x82240203510358505592204c0e2540d0801c03500a0030f1040d011040c100381070040450310040c1c4405042c500b6199030320a072411102e0400c0c0b0411340441c0c9400d01180440c00c2103411248958015504000c4165184004500400f0010040040140c182c0710100343d4208502c00600d540c4040e500510844006c01c00385421185e040c1e010a065602c20420b2400681300c1071410b9504c12100341415032a80c1c0cac5d00e14506100d200b615082106409104008540540c000c01e00c8002e484040d0110b41088110843c2d400d1200400030101000c2104280007c1041d881307542085080391041c90040b0303030f1008102000d9980c0e0401c0d1001800c69445204002c07660404210044044008440b0300c034807d182c58000c41d100c0c0c07006001e012801038603040059195142d0b0001c6800441e8010b0502d10340390707075070000c841021540f0349000404403034285000601280018030040b00080060901e45064990b900700030ba2070703010360340803590101802d80000f102103003031021f451055440007071074880404105096040ca50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 37854789 1250 37853539 37853591
    0x9010b03161206020c0a0203010612060f150e150907020c1201050f010b13050307060f030506040509030405010507050c030d0c0b010815062209030306090e011b0507031103040306 78
    0x8a81c0300c003000191202c5003090441504510300503035030903502c41864188500150069019800c028000a0a85c0c41d05501031005000713480070403c2c40500c0e001d0f01c2c00d071220ba440d02d00403560000d0741400404039030b856290704684002001d04044a215001c1903480c2c80895851015800201c010300e01400c00240560b08503004000810540c5042c81a81c46910b8040c029590950008100d074140000b20026003800340400500725102250707501401801400f140308090006420400401c0d0a424140945805002c003600a9400c050600004544c7d81c0c0180c2c405071500d22a1041d003120760746050104095041d02c0e9a15104002c1c20b50400500c2c948060f4004075030340e4442000e1008801d203520145421440c00c6440130403070301051280c5c4c03882424001912551a00d0304080f01b0070142c043e03002c0f00881da1804024080e5001d0b00c800e513402c0380c4d0240f00040388402054000c001072271003031000301019442420000d19800c00c04134114a1504940c02c00c4440b81e558651848408100d40d070340303e403054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 37856039 1250 37854789 37854823
    0x40912030c0503060d1202070f03060b01090b13030215040509130303180c0519080f0f010f02120a020d1104080622050d0c082b060e0106200102070b09010b03 69
    0xb00306513000c00e600600c1010040e0000c02d00807a2041011f1003845540c0041501c150402ea07540c3c2c603402c0c240020130032416003034040303616040000f8202d41044d042d07a180c3d40c00c502c1d05810702495030b02070000345002d1034008120b6510810000c102542ea2540e207a0003540c0d801c050000d000410728000d42103504441d540c1d407900c024400d403200019112242d0005455007990034030300710b010380a14020f40c040f0030b0b00614400e008140b0050140c082c0010403001c2c140e040c3d8005d01c0035220080750300049106c0d0f9082c01030300182400c009000c0002e260010001040301ca50001006100035443e0052500550020034175900000305100c0c030f044402e54084042c4803c29203443c2c4a28583d515a41d44820b60f103124400e0188105089041c84228826250314640101410b01640399603200ea10520f8034003564010702600d044800f148004200701d22a05132a55603d80c0130300c00749200300d0400d402041010110321076400300000380014208102d03450003210500004600b010f5060101424114004d00d040240303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 37857289 1250 37856039 37856041
    0x806060901120f02030307080a030e07050a230303130305030304031e0903020919110a020715052d072301050403020303240d03020f1c0f0e0f040912030c0503 69
    0xd103046030070360b0201e02d0380500c540d000c00e907462002ca801d50150140280c000c01000c100141c1c3c5d290560814205101520182d0b541903845400b04401009940100c550a08081200c0464100d58442c070304800d0364014201c1381004201d04034041640407a030803c9030240c2020060208041c0c00054510510490000c0130401c01c0c190b19004040000c18880079100d13910040c0411032000c041c400000c52041800c0050101d40809526015681d0101d801003005102d004800104030070150040005c1072400d64640307140c0b142c20004540311180740c00d402c2505420006210103c80480d83c003c10707450740300702d0003500d03401c410242500c45502c900900c0700059041c40704101c0003c1d40407040740c2d40580d9181030700703039408944003041d1102510000016000094424820203140d00004c0e02001e0b0fa401c40b00b1181d05180414160011040260b02d410104101e82000c2d9078041c0143c08110400002602c03c1d4220184c440003d000d54031b04190556802d440c20020400d819850f02812901a100f402d0040c59 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 37858539 1250 37857289 37857299
    0x5120a180b04080d050405060718030f020118170a03030b010302120703020c0304051e0405060d1e110d030e0103060501020d0903080304020102070e0f0a060f0305100b03010e0d090806060901 83
    0xc00985000070121103994000804100c080300598105901d144800c00440c501454425502c840c10f4400801158042c0c0144004a880151420540750b00c0401d60080140541c0190342d02c010844186900545085001c6050503100d035800c4804c42c20080189040300d503e0401404440303810085038101401040200e0168481004543d00058145001a40e400f6231000b00b50450140c0e0f001942c0c40511031440300c10320b0701d08099943c0c0040c000c8508000e02d442c1c00080100e010114207000b800042e5a0030800c0103001104071040c0c00600808908110103160740c00200f00804600086010810b200801c10181d6490710460016080030700080109600e07030400a0700902c00d03888010540e00300040020b0440e44203000001c01420351902d007004c0703410822428070f1400b6044981c030b61500d00d84100006c0702409001d0900482c0d030003c000d40900302030051441d000d468400e0510b5010b64032400340640130701e800c0010a1200c50650f84e00104c1e6400d0841c51414150060800342c030840307485c001444 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 37859789 1250 37858539 37858571
    0x91615050316090503030708040e0c03100303120b09041a01150c080d0e06011211010201091104150302090106020a030305060607021c050106030c03080315090405030a110a020a0605120a 81
    0x10b04845150700c91107000403074200854400340707a50421074143c000411400100200003001c0c0003075441e61900003440b43d591038620540381c00211403e000780c203140c040800119000d5071000c0755840d9442804103c880b416030205031012003d44080300c03555580801c41107045e8640030301501600380c0301001c45000143e01001006d020000360050710150000070090038140b0b0719170000311042401401d4403815a9200c11007035405e00c260340705980c7c054050790f03009103030f40c4184680074200c0e48c000541c029070b10320001070000600b103801ca0104104030101c000700c0540e513201121030080c4030581c0108160400d134540102074420140c01640114000d101e140016962034101401072008600310607000542800e00d280580840d44c009048000340c9139002c02402001c03c000d40c425514502c0fa81100740241080c00030405c011a030103040341e0418400c1e5045144600e915403100428101140c2034400a43c00242242705254000f0b00030640c00541c0003108155034a5003a440780d078a0030104440da0b81060400c0f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 37861039 1250 37859789 37859791
    0xa02030c100302220314010c0507080d1805101401030507030b1009050106020a0b070206060a0b09030109020612011406070302100203100305030a0305010f050a0807090905030c060916150503 83
    0x152207a00d00060a40c1010322950542e9410a010307400001d03d4440302e039404042c0c103900e01007650a0704000000217180501409485140685035540d41c0c64404242c07107515058010b298584011a1a00501d900e04a45a01c3d500e4400d0701407000740460700809490201220440027030002540c0c80c04004201041c3c0200e25807040b06e402c03140052041e80c807a01c1c0c0b018407210310741040802610f0030001091140d03001a400c81c2d00d0b071190440e40940d072580720003a0b84ea100220340071540003014404c03e000100000d00500001c0c3c401134000320b00f0b0407a1350b001031a0b035004040b540c180140350740010401c43e090000c005510312020ba859515000650314000d40310190010303032081c0c0c5900000403800b01201458014011500401565101c5001d220018064502031003103661840803400040ba15242840e0b0146c12140140001d0840d44c2ca44920140540000c02003500d0074001031002d1541108144486446014100007500a143c615002c40c203001030709422801140c0100004052015002000c507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 37862289 1250 37861039 37861063
    0xb01030e0d0917070305070f030303061d061203040b0a0e0907080603030703030c140a03090b070203040b12040204182301020a1d03101505010206130305072006030c030a0506030a0203 80
    0x50300e607640f0303034820091070800643c0c802801071080b0200096085c82d943c00c003805881c840c1d5814019296101103c0c0806050081c5070591014400040382081ca040b403680c401e580103c038217890a2a40e60481d40c207054000444003004030740300c181a803140746803c072241c0c0d502050604045402e4103207900425501c2c05030040041c02c3c19901e002014090740904000035251401110082c0e0700c83c0b103814001e014102c00c2c1403c0f204100048041514140080240d50949a0000c50346080c400380c0400d10013540d8000d001030382c100780c1d10080b0089400e0301c0d08441d9081400345002c0c0300c0f0064600118803c00074103071391407600e40c3d10503c03844000035030000b034040721484000c10030071803081c140d4002070a00d1040181000d00618101c80211752644503101e00007220402d07002d6451301e586411100c0315940102000070300068080084100090304250200c1c02001d514000703040c2c07803212001140c03643d40140e890141104003c41049940c0f030160003807c0d0301a4090b13000d031030000c031075602203a510701120f04c113 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 37863539 1250 37862289 37862309
    0x13051203040302011407021005210610051b01021306080702070e0117100e0c03010c050301030b01090c090801060306091509050d0302030c090415050f09040506160302070203010f0b01030e0d09 84
    0x10300704a900171020f58903203d030002c00c6882c032403201a1015081e82d1248801401e0310501402c911880c1c00e040c0c1d5268883e51000e094034020119120f4102c880398080004150a404600a161201361092000e00185148261558811805d110000d0410030b4028200b00c210350000e00248204210340c11300c54110703a90040220701600056100c1420605442d0141c0603940c500850f440c000310f000141078600100075402085180011802113510707100900002c1c1500242c08010807035034200c0e500101d50141281f40c8401e0072511604070500790b42c2d8603482030314aa034a0f000040d00307000810340c590f0b50b00e542681c4200b00702c00f0255074454a5800c04c84018050542c0440000c000400b03a40c11100503401c0144100400c42c24010071015000e040d006040c0200081d4842c0401410300e00600c41c0615007042c001d20b41c51b81c2c0c1892001c1d2814110408408140e000d101500040c1c03000d0290010a03000b585010030700e2190000010f00b1600c40318500911684410382c401040d40e0802c001c0002d42c1c06000e1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 37864789 1250 37863539 37863557
    0x30301150c03030b090f040b010f1212030e0a080307030f09020d0210020c13060f060206040309090c0e0414060f060a050a03020702210a03030515010f11120409021305120304030201 79
    0x40a500504441884d680c00021201c20000c050300d40714a818425846040e00e000c41c0d036292000014200101c0c002c940c402a040342000c0b000c6051309682d084622450b190101e200e0302c0a040c3d140c103013810500200c13040c0401205001409405000b40d110000180744100101d244540016a0100b42c0d004064083d48003c113450a6191007401030a401c290050440c0b0642c80940307050030000c1c14248a607802c01c01001201092061000c10032900458160369010740c2642480213002c01480164940c10900c400c00080444c00d8540b0700641c0701102c000c0c1d007800c2641c0b50090a00c400d00c0d00c2540f07058800d1108120720701c4029007090659664414626006859111500c04103443e05400d007103442603024580000082e42200107459070f00d492180d03900b40a02e886141212500046070514540403600040c400080785204800310000310140344110b83c00c2d00b40c0d1203c455400d512940000440c560001412034020060300701030002841300b44c40c400c64400c004200103840e40940d000c0241006810f0b1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 37866039 1250 37864789 37864793
    0x705010305160c14121b1207080c0106151d01020a2d0f0f15050405070902210406061409010b0a030b0118061d030606091801090b040f05010608030301150c 68
    0x64030b042004d100150403035180e01d0010000440f640c0151031540310320500326906650b5900003207108580119010003e07030030406941e8600c03140d50003000c01031009642e2880c000603407800c20302d0700e22541c0c0c1541c0c4407402c09d4010a10001901e99041f011a07040d98410007101c0d0006070881000c0032607940e10025092410a10000c4145c0c40c443d4020203410022008004418030140c4421144190301c2060300c440103002c107100503c151501120050450f410a010800c0510070b9038004001e001c040e20800f400c0104010610310080c40182c1e800d41c1d01c0d9507039020600800e030801c903001c02440700450b840100d643c54503507107002a2050b103442404060302c2c0c40107110a0b0340148200d081c5501c410001e14101502d414000740004902840c0c9070300d050821700006440c1c00d010540030700804d0302401d144401e43e12014072459512401020031201d650711303c164004601c85d184d04030f0180b4400ca001c1d407a005e41c2410078500b034031901c2d0480c41c82c2c1d801c100010004100c2d4408080f000107210b04010305001c51034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 37867289 1250 37866039 37866053
    0xf04020a12200d05070b1305030d0e06031009091b06030b0901120201090803040e1b0a0c0b04020f0a0b0903010c08060108131b0b0304022409060706151203020705010305160c 76
    0xf600080282c450500082082640e00d07020741494041421680402c0348d9030f408040e6104102d04a203808684400e414542c43e04162008650000d8403410554000d80e44040b101c003110113544050b81c0810040108542c01d0f514111514000c0c0a40d150600404c903c3c04001000e200041c0310b0406c18801c02000b410459005585107401482100c069a44907940d0310440c2a16110448180030184002d2001b8140d406440e401d8580200980d5941030800380b855407802503548000d4020782e8411400030311001184c2d85d0130300309805041c200317007480e071990520b40034542900e440f4500402404950010850a640d12100195202038841551604c0c0c1d241400c20035100e140d40c03815450340c0602040c0201e1036500320b40c01540280d1090710480100041d03502d140d20580007072680100c0c14403040001345050320b000406454540d019031400140781010480300d14036942503520148011207006609402e25806110a80041c0400c0c20144101d103000940c0d0030050607a01001c1088c070003002c003000c2c180015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 37868539 1250 37867289 37867309
    0x909020d0608030a11010605060427060906090b0411040302090403050706020d0203010608011805010e0703150b0705010b090c0a0f0f110607050306130b06030604230f04020a1220 78
    0x4010b05496495a03c100002c0040180304558085ea609000e0002003508014007220b0899020300820011a8103924800000c010955038090307030941c80390404507a00050748640401000300c1400007a24500820a12081c2c640300d100c43c2c3d0308208240010000350701c503401c40c1a405a4075103000383e43c501c0f041ca0524000d010b000d5100000301c1c4040004106c19412001d86416564105d8188034408200e4520106a076024020300d0070070b0701000c1c0400c031840d0082d0001800c9046c11040c5507006030300d5486101d125000000140d9540e91142072403000e0342090303030002d5041110350740c04a00d4403140980280c0600000e10030041003003840e23841c1100b428401e1204180742c246041c2912028245040700411517001510503c3c455025152045003443c810321a65000b000c000c0c1003c0c2c00c50340c40004010042045440107031204042c5104012020785841e40d8910806d04094115030909040c010300910118541040345503450002112012500e82d080c0c40b56201640c600a42c803590314800840c40e40c0c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 37869789 1250 37868539 37868549
    0x103020309100501080303060f0303072109091a041803090302061b031603020d0521090a050f030d0c090e240409030201020c010e06010f03030f03290a090506010909020d06 75
    0x1c509400400c1c880170100085004001c1102c420380c041c0c1c1201c2c00c050700c903c00c03244002e2040c0300615038004034401c10094a4014500c41c14411039090b41c9940200a403000d0001400055040c10200c5c001441e191040c0b600c180000d2110b18402406580d01805c90070300d6000182c81000085451900250740c5000030102000100a890b01c60750f04158101554012200843c050300440010b045050b1013403081c0e0303d1002e000d1001c05502c0f484000110312546018105e50058000d4440c52008100d040101d07882d0031380070000440e40d0b0701c50701e640c60049030403e40d104010410f15020800045402c10351454000710301c445134a10700644c10341d03812a44000002a6908182468502010b241d0190301810721410607400070301c0000b080c2e042840d102d620074022182c05207207801c0d0500c0424450003001583c12828140040c01104141c1c260754020155100810388010004860030300d0309004a20308010b0203410801d10440c200310b80060181c01150103540f17203e80d4046824903841c0560340110300181 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 37871039 1250 37869789 37869791
    0x30c0d0c08060102100b060405040509190b01030312060e010501050903100e0102040306060e060102060f040312060e06040c030507020601170a080d02030f0c03090a1509021008071d030309010302030910 88
    0xc0016580581011800c48915000d405004104031000104d03001c0c1d84402c0c10300400d107600d098248000c010040c0300141c2400ea240c490003080c00103040005005181182c00f8012415040d0b1452a00501d100070250350725030702d24205002002451414070400d4190b03039090808035121012800400d00d03002428401107105410100044502e50042d4000c006a038001e0034103004007901c0c0c0e409100180d0081d5440780c01a4090000640100e15402565070403e1182c900700d9002911440b8040c25144c0c290003600c081120b00091003a5881c0a00c81d40e48400c4141c142841a490580e0b0080e40368141442210100030082d009824070117000c0c008984030381d500000c11a101c40c000070741000290011203d41c0113609109001c51b085043c2342c401e980c271907120340d4010030fa001303042d60300c2d01d80d03041c03450091107042510303134034400c005940c0e42d4040c1d001d841d06039a030524685005000103000b40b051201449142003c00c070a40030300e84000c0100c4004140a0074056541d440d00b4030300300d02e400b10041d004d403015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 37872289 1250 37871039 37871051
    0x90c080a0e1f0608010c0201020903100b0d05070b040e0601020a12050f0c060a05010305070b07120e040b0d03020619110304060903140a030c08010b28021f0f1a100302030c0d 76
    0x4155800303e402d13904010000c010b0502800801d9080784510288030b43d05603c84e10054410200b19080300712690005007046440640980e01c99243c0201500041205040498240326000b0441c4c100c55015409200408062034141c0f508040040c0354400d00040200003e00b42550041681c11110f100788001c003220130740e1401c4402c1200405087c00300316030902590720300041c25401c640a9801c070a0700071940c5030450140c2c100513241e62068180c0b80390865105c036031441065a03498804111580241c02502444c50305802c04e555104036600c80360f507404e00d4491100850440102900d034865031200c000148510030741070561309213112580322640e02100007603100e10650326070844c11004081b42c895008590304d81030704441900503403003004031450b009107001400c03008051a00d0001c5195006827680003141e4150801c004110152801480d6101d8010100080c214403c0d81030010704c50181140c8440000006074800d6021401d80c1c04058020011490340503001c021690b424030441010401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 37873539 1250 37872289 37872343
    0x90807021509060a0801051002030309100c020a02100807110105090a02060903010204090504050d0915050a0f09081e0f010506010c0f03110303040f0506060a03050d050703090b04031b090c080a0e 85
    0x85c0f400240240c60140550b034110a4075240000196070223506002d000c0c2540d410304810302c0000740155451601140303d085a0440540c4401c0840d41c030000056403003501610f021000504400c0307480c070503c4110ba00d420100480d03404089014100d45034111807203662100f0100c00640a405a9000010514540700078402041400612080c7c4036015444910f019651403125542c1c00d140a0742800200d1420040000180d11800201c1a15045070500b40c80450300d446003180b801160030a241e090040e0914055515030003088004060001900207003c140b400c400020800c0c429120001c01942c18440d0304c03010140191419145a5074420803a0b841e440c090800440852401c1c805032511301a40020480c81c0c2001004002502e8000008005100200e042164142c4c4400016800c03c440ca01002c14034107800b400400040d40140c2007007580f07840104101d07441090300d91010b00e1261910035180b1006811480c502d60100c50f08000040000c0c840d0708290414260404007400f2824620322051 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 37874789 1250 37873539 37873547
    0x15113a170108030c0f010506150306041b02030417010b030a02040b060d020a030b1e01091a13030c0f061b150902030102030708010603050112031706010c02060406030b010e04090807021509060a 84
    0x1004040c160112030040050845c214200d503000d98006400581030303074a82ea1903000c0c110045070000d4020b800060300f444011500711452682c202440010b8000140801915035802542039a42001c170000704404c06082001030758030800d00000034015501c130b5144025550f03800050f0341c919002d100d000d555640c1004001401010903004c0c807031040c0c90103020605102e00c0381103122000d62040e11603074522400d00768884060014034104811102c400c11074000001820402d080c0190f01c00d031100c404a0b0b00f0b1908128144082d0380040081100356802e0340381c3c500d600c0051124507500178590188070808820b120b40545484040a90958000401d001c101544906a1030496015903410440399880c1d502ea00c0c0f20020007c4040d0000e01c0d10504000603020f440071090700804141813401e201c0301142c0c0492210717005a4031150100341c2d81c28608516503000309403410385250440701000040015a21a48240143d0301d020340a040d10611820240418100b2501e1022005200a40740d802e00c0100034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 37876039 1250 37874789 37874797
    0x10306030f030309022b030305180d020a050f15040305070602040b0318010501060e060a0e1f0f080c03070c0f02040b0405090106061b020901150915113a17010803 71
    0xc0c00340f20920038103106c040119a509060580740d803021000413665031401c6000d00b20207805040c05d00045200514810000c1003400001f8084d40c0291038401d14070304100342082549100340c007542e0081801c1d07038a80c40384a040b02e540f05a150600c1034075021a410300300001d000c0d58000c82d03c5554000f00740800e09404082a4502214640080c44542e0b01c03480202e030f11900c5111256040300c03080c418403903080d014060390031544002500005102814000001e410410a4140e00215100211041e615076000e4401d5a01c90a80a0254690b0800581c0100b9603803801c08040d201344103c0880760119541d641140d008180c000700305000c2800c0003110903000b045240b0030100821406c90a2b1000005a1100c100031150001d0004840303a190100c1e08008035014040e0804202c141600414107115404036501c801c03602d540c1d0564003450349003000e8900710300411052601162020305da058681c0002c001c005040e25400300d03074251198004165600e40c012000c0c1d950028907034002050b0254008054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 37877289 1250 37876039 37876043
    0x30a1b090806100f061115012301020d140d020f0403060504030f020606061204080d05090714010e13050402120f060403080c070b0114030304090e030a09060801080606040c140a020610090623010306030f030309 91
    0x82780000440c00590703070f840d840c4041602085250542c8903540e000603014104440f200c80d005803070a0003140619100f540250812076010342c0c1c420603c4245a841120100200d070305000030300d00d500f42040001e040d030140750f40c60f429901c134000000d410400c4100c140c9041045064091000e41441400d15441c1c03100d50003640341c5120401620426503200d1200c40c0c4214a020301000d210101028040700580002402aa00401d000361400b001110801c0180e4a400c0000094a03050500e490001c1220601801c03e400312501800480041440100c0c050304448980c001c1440380050301000ca8214003d0740c1c00142c43c42e140036210207034640c02000070315517180680c0e142c0350402d4645c4000d40e500ca00038090980642d001d4800504242416882000419054180f03803094507100c01801c031565001c1c04449006800900030f1110386d81c92410004058000f01c603050010900f480e00600e08030780d4803d42c6d00c0b5540d0941e03036031407816402980402d000d507401040101c1d0b04100307418050b010b00015002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 37878539 1250 37877289 37877339
    0xf06130216050a06050a15170c1305010e13020303030a050901150b0715090f06020f070b0901020a1d01020a0f110a081501060311030408030a1b090806100f06111501 72
    0x15035440c1c910b00c82c0003c41007000314a10071f4141040c4010705c0b12000d4521025141c410a420550b2540e114100190480c00f68a0b01007299810a150300204a0340a032145968980100c0c040c07006907408010303654848040600060166180c0710540c2c05014040786081044528490100390b45c1040e03401001404d0140c44161241e00e07040d4420011204210405484a802504040005030044c2c0086c504191500c00e220b081000c2c0e0344038a07a02c1942910040c816a40c001501c62082d60444501403d203514031210034a045000310010b51640c001c1c080007007a40a104002d82c08001c0030084940c90541d001d001050300503100c0d41c0443e9523880085078983c0740c511200c00024000d100c0d02812080c1d55a21792540d00395140d0340d5a100c3e294001505915265131520344541a51200c50800e03102c11500c2da403032040f01854038504a00b40400540300038840210700780c2c18848500800c0904040707c3c52403510ba0a45085a8440c40c1061001d0480401c510240000003900756036641a0041c81e4403c0c0d69 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 37879789 1250 37878539 37878541
    0x2060a110f07030203060106120204090c090509150a09020708040308070b0103030809060601050d0b0d150204090605040b030c0d03020f010903080402010e1e011b0602031014090f06130216050a0605 86
    0x1640e41d490b042c074400294954000d10060250f184681800c02e007040d480d40c0c0240c00c0c280c0750308006051300d468041d04030004a49200800c000e03d0000101600003005442602c03210310604085903140e48540901c108254000800c0c0d810090000d048030010b50f005a4a40d46900c000d03e801c910366442031100341e000070303050004249040d0010490314000c580584903203192142e11003440c0c010348403000586501c11681c12b80000881c1d03502c22801040389088000680c2d69080001d00740442d006500003d0260380b8040490b45961070000349041500f0007140d00c40160700c2e05141c100d18140d041c00c0c254110b075003000c1ca090b04142c1c0261140380100d200340c82c0d060840c0f462109000d42c502401070020340c51150250448a954007034003590942d1017580000607403041c0c1035140d00041e6481a2804c07103010501040400c060103600505582c41c000072a01b494060a00c1907481c400b00d0b2001d0200f0344251140b0a01002c0282558112041401a500c4070401003200d4207140c0e8031388000c00d0041e1803c07424a8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 37881039 1250 37879789 37879813
    0x90c0f1201050414011b0c030f110a0308070f0203040f050f0f0d05010902010e060c0c09100b0a0207180c02063c0601030e0601080d05160501140a0605010503060105030a150302060a11 80
    0x15507800741844076030359100c1258203520708503600103c2140c20401d0ac006807100341049079041c043c41b28450f000b91129541810319010080200084d0100002103410a20061010b0050705000e00d0071a5000c96545d04110038050000d6158800100303280c1c0d12a440254000400c0419044080954002d880d22040d07880440280845440b400c0341c01c251540110501d501540f5055101ca40c0100d51465005a240c1d00c84042c4440b03030f40314820500250340f1a02e03041020200b00701c184910040305120910085a18007030196a91101a19804c20315607142c00c00460352403d100307140c030720100c1007100313540b4071100185107042420240c41e01c030f0009041100c001c2440300002030240c100c85040d00106a03030000040c0441c3c090704001e142270b011442005c46480071802c01d00401d10040c224458040c030500313010540f4400c5410711b0780401d0502c2000e108100c00750b1380000503617500a40c130b8800800d00c0001010b40c1c101c3d1228ad41c20081d40204082550003020303602443c500202031003e401c40c0c108000f48 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 37882289 1250 37881039 37881071
    0x301020301180509070b0a09030209181509031e03010302030105070c110f04020919060206130c060e0112050c04140f0a06050f07061406040f05090c0f120105041401 72
    0x3405410790b2424001c2640c54002c0d219482141c0c440904401d444103c0d0b00c1e59070800b104c0d401000d5100c0040e40c070007824015441c02c80344c0244c10005503d80e000f181e54640400300c3c2c0311010f03200c90310540440c810000b00c03001018030480c2d441c4040d00144000c110a0707420030030070795003080c0000d900a600c0d20707000900c002d01400e4850601a0044c41403040040c4a80800180d040c545132216000380d02400000f02d03035103812800386901c1e04101034120030181030150007882c10000030142c003d03030100640a000031650b5400050191462454520080c10311080161102e602e00059500070924080400041e008460040c01c10303103140c4c031900000310a0b81c40800807402045c1d66096840b068640c1c003000224002e00003001c503c1481d1003190704081c0c0035140c9208070750003100f00e03039240041d041c10024a45003900c12100700d941c150400f04002d0070b10059035a40d40b405a02c240d4091a08030030ba1031196a11294420308901640009200518040c541405032041041c1481ca4942c03d00181c541c5091071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 37883539 1250 37882289 37882291
    0x30a0302030a0e010c0e0f0409080c010209090912030a09030905030a060606030b1207120c12060c0206160f0804032a120201020a1409041103070c0b0916062001060807030b0603010203 80
    0x70581c4c4d1581b1106400c07041000d521015581107600c290303117040400009200102500b42d00e01c03030a000585907141902804140c1b50001d00c0d81d00250000311001060300b00302000c1da6003000d0002400508480b041c40c1c244c074009156013180380d062080c07451941c02c010b2140c101a0594080d07940c00e0081c82d58000500034801081045c10245402041050050b0300e02d002640400c0c9001e80704a00b0401d40c0c0790240c04c8092180601541c03144e0b203446110004503010024160003050781c40300703100c01e4120481c008104480443d401402c200c04400490103051140d03640300c0079028000c0c5004481200c906480700c02c135615138401c5621a07404890200041e0041c42920201c85187d102c0784030101d1811031200b0940d00c05032a0070350169450850005241c2403c0203507200d120140c80304210441c850405d800e4445000300b1040340d9a0003261440440c000050a01d8102c881c40d00f041010010740415000203003e070203070044000d40c82d0901c00074510b032000501c1070840f030162044540d586c48403c10b043c00e0303101c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 37884789 1250 37883539 37883561
    0x10503030a050c0109020d1203060608040807031209080a0e1306140d03050d062c0403140c010f09030c030801060201140c090d0b010e100504050402100c02010908030a0302030a0e01 79
    0x10a000d1141c8441c0200010b00740c8010090001031404a540d0005035540c95902c4c00703039440200c405514500c3c41d010311545c00508078030304120051f454250703aa5860384c03144000003810044038101110020100303805c000307552030b4000446c0d915980581d100400d0b00390f407514064842d14880761b04c20100c1034103200324815130310070111400c1503143c0003050243e002c40c000c20440030407004014000d1400e80e10300c1040044c0002000120b010740c041013051488812440c426140d080c50359080c000000d400080c0c151001090300da4443d01c5858440d5014010065130540c5042c0c04e0134504c0030010103600088400d4030318401d8580c1c40840e62507040c12804c0b5810302445112401c0e010010541c1030030f81b1405003d040100501d41c100075136290340c4508500201707a009a11243d0302c0020701001c01c02c01300118001e003005640420481c607040c0c00003500500d240e00060305003d8030340000015640301e03410401c09004088120396641005c000c000f4002d45c0110f410000b542d03d000180c019401045c01a42c1c6560 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 37886039 1250 37884789 37884793
    0x803100605180108040503070501020c061008190b0a1503080702100203040815040c0305010f050105031b01050409050a0603120c11040e100c050c0106080708060601020c13020d0b060729010503 84
    0x20000300044d2070f00c2c1c2e8094003d030388a220a000a000251007400186001001e08020f884241400d0445410034030f0707260008071a5800104407c441c10640b120620300c00c40d0000310b006200d450b004040402058100f452941400000101005010488004002c010300c01d44441030303c00c0e10300b001241c81780914019454180c1010405030b95503c402c0610b1030704070340544880b003c050fa0785c2c0d85650846020003070b040c0311147c07980b004200a1406001031842162101c1e41e1204860100380001c0543c4128050040c0341940c0307034003003080d5040c0395000ca400707507a2003800c0d40180b0386030030f001404000f6401030454586c0e5207000d0207103003803d260295496000c0e500008103150007489081c0d00142130b607040b0000410006004507040c01c10240255001400400040d20b205410503540780c2c20b180780100074505541c41000042199292403e059504202d001d20041e1100d2010750042c0160040120007039000c000481c501e0140005c82210741100d81d0311160518268040179200403120009204490f450307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 37887289 1250 37886039 37886077
    0x403080409111b060712020a050d0e0102070614181605060a030b030d09051305011208070501020f0a030e01050601020607020616030b19030311010203060a030602070318030803100605 80
    0x1041c9821030105248003101003070900420881c44103911a800b02c0300402a4810b10500c01c40755003140e94100c1d41400c4500952030203907640005486442071007580c0040320b80d9030350015a0000217506589015504c88410b0000301d461074003402400d00700b0b0f82c09010f103041c0071350702002880740002c80a00000c141e00d40c0c0c2c040b041c0b81c070b410002a60040540001858bc9030f2400c1c0c0a1380d90180090710000d02d0940340c4210b454281014404405079100003602810314010040c0050620340e400c6080156002480550320301d0340b482c202d8068000c1110140301c2210120340b4900325605508007900e00385824000f0440c3d0b584802c012a50b40c82c0c20344110001d44c004101007407041e2140340015480b09035904000c00c400d08160007280d0812070350110a035102460705418010590b1006014240718008030003541941880b000203401c0ca607840c0b00007000142c0c0005c03580f04140c0241c1d01c824400f05000b1802c052540c0d42c1c20054000d51044a18403d02800c00f01d01145041c024402d44440108211924500e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 37888539 1250 37887289 37887299
    0x50a09060f0b0901050c0a051b010c0b0c0703020a06020a02030406110c0a0611070e010e04020405010806010b040e1e1f0f030803063304080c0603040f0303050a1e05060a0b04030804 79
    0x5641c00f50080301d040040c204291300c03040c00c0410921021a22030030042028048500150b00400082c501d83d50400c101144640e0208034442d0950760082503034000569505e1040c68103924026841400a000c03a00100e6441449600400980100c03011500c4a803c14000500010b8031846440122a80203440b503405002852181442045408090045a103151b40324408201281c074240e001c042448981801c020460801d4082c0c140100503000040c802c55051141d03030620750045000c4c645100c1c014800181ca2034509c5101c51141c440c050031510715a0804a802c01060240083c2214078460024070005400030343d010b400c402c032600044032a0440d1500e0082080307010740d50081c41001201c0100031a008036951036a07030a46018803029550721032811030351790704084140051610030703070082c420480400d6981207101c0f5066071605d80040c85075261100700004000140c800071400311804140c41600815070721050040c8421560858521340c1c07648940c025104a02004041a101f8441040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 37889789 1250 37888539 37888559
    0x30d0504030311040909061b14030903070b010608040c0b16021c08040f171902011b0b090304060e1504030b04061e020901200d230703050301050a09060f 67
    0x34000e8440e24012440c2d400140910f10581c220743c21094500d5594045081040741c1481941103442e03c0c051601c0c070910460300048e01c808010066202000030000c00115480010b1089883c1a40c0c460342214040d6198500140144802c850444600c1010030700851034200c03078000d44042c5e0810414035942400e0a500740108034912948418100d4109000e407800944d000010700003034aa03040c0070325419858541c118006488600b00b000941c0c014900540550030b0f81300132803032140d4082c28840d031602d44580d44818649481d1402800451152007804070700c0781b000c0000c008451680ea06d9140702803401d0100300001002c6c3d2201c2c1c0c0340b088100400c0000500202c4120762040c000e4800040046d02444000301d2000400304d050601c039400a845821981c0000c01c00d20b05039a0391082c4c410f03010341c800c2d420b581c4180c50811310050100c2180c52110810350601c080c4044026042040d407550407904e0043c0c00c54100b0b0246521544401c0390108030811a03200d03542c21125030f110742c61060b0b407401100c81 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 37891039 1250 37889789 37889791
    0x60a140d03090801110712080402010507020f030c030708031b0c2419090905130b15030309061306030605090f1b0705030a0207030303110711040509010b10080601020c040509030d05 79
    0x7002d02c9151a00040c00150030321031170490b070b80400c4000d9a1041c040c81c121450030b104001c16805e00807901c081c440541d03404816160740b2941650f60101c2090310400280c9844840080341d82d25224994001c038184402201a049100458502c0100c41140294298039561a24072194015047c58100004e10100c2c4d0000001402112401454500450080000e8180741c3c44220b0120b8402c0304208200e10081c41407a81c03200300983c02c49003540b0b29a0703681c050ba20f405882e83c039104a882c904d03003e55a0b0300380304854004030010000c0c0da403103c8007920402c504c4040d20581c03000c01c2c44d0010004080c00c0c500f040c2c0d07118000c010383d1501a0303580c00c1603d128006108484e00c02c032120030300c0007400040c410001081081e42580040c4a00ca01d1490b000381524610300d440c188001c010f0103400001142c8401c80304952204940100305ca54402c103c40d8010043c10343d0042e0b22516400c01c030500940c01c9083c2c64010082070b400d842c107074101e03d8244400d84505444c403881e198804c000381000f902c1582e02031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 37892289 1250 37891039 37891043
    0x20d0204030c0312120506101211040603090203060606090303030c1305060408060a06090c0504050d02181303020c0108060603150a0816091508030a05070c0e040b040605060a140d 78
    0x604054407915102c125032002e8004550216070000e021401c9500020740710300c0d20048a6080c8907614101012480c4024000035036020b0080301d0020300c0810b00c03582c10250181e07061a0380380707458030b80d01c010040c083c0c440da020a0f4080d01520300498030700e00f001021920700300f034054001c51550321041d503171503102c0d48203400300390b4000a1100c0200d46503540000500051540400078401e50500301c1c420001c0f505194010f01c82c0c980f400301c0c0c818044d078101041e0b8013101c200729024034040207180042041500b40007102c0e90b000203040100301409030300b41e80003450300d400b035421100780140d240c0042d21801c40968409500c4482800010b000000041000807855805442c064580d560b80281e00c1c50852001c44518040781d003100107100605091251821028145c8140d0011502c1d1010194692251303480b030740200040003400c1d009000802a800009202641c441103403860709040c0650304d0071054804848403030600022400d186408440641601c0c4c5c010a81060005c1d01e01c20420088030800007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 37893539 1250 37892289 37892291
    0x90304030206030c09040501030f0605070201060305121305030d02071e0e0109020a020c04050403230304080301030b091f0b040c08190e0f0f07150801150804060204030b13060f020f030406020d 84
    0x1082d445c0e900c1e40d005d002d000354400c1c4519000b0414500d0440159a40185903200310380c035001040000c120001941155a026062255602c41d0840682c0705021850b800440e010f101e4010055034080e400110902280c941004080d009030850401c542c94524a01c108180841e000006010520300ca80c000d00d038018860040799010b0036200042801c3ea40d0071541500410b03d000d003491810859104a03281003000a65440e2441c60309aa038001207000c103000241c01c268032440042e035545401c1001400701446a0f0704000e240c505a01040c0140215501050240c1d04210540030b05a0080007d9805600340c14095107500300e0750242140281074481d00f01c14148a28100224180d0b000d10511110020b454003804045042010200e140300d483c0940741301300603801c0010002c552191880315881056403401100c03603202c50074000068060340d000584142450000d026036030101d141c5800c1864400d50003800744a0506020300205c4c09502c8004a01540400004001800035802010701d110701a00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 37894789 1250 37893539 37893547
    0x2011707091a250b1308030f060a03050a0507061d0607030e0411040e04060b01080709060c030e06030f16050c03040918080406021b03071a070215270405090304030206030c 75
    0x520794034031500300c000d011580300d58041001445004940d0301c1d8010780004100b0305170190b81d40d070000c861000034185000485800041191555034500c0d4000958003c0100c6060705101d0401369290707a00c602c1090080382d0f03416050f01b105a881c12500c503200034000c00340d5003084000d4406407550b00011807000c0d0700c41e0b070398440548a010202c0c00380005d016282044040f91900b0301e041807c0f540311312025070511030000100200c4070303805516841501d66510744012034240078035003610611001c01c02e0540c01240270003005400da1007100120302c540300510f01110040f418100c15034152084c00007512140d0000c0100b030101d05e00d46d8005000422444200d0f40308040d4548640311603030080c5d040314006030030080708800709144034002401c800800314003a002d264504000c00c103810b083c100d090000748a01040c20001e43d642c1216044e20104030070b002e1075a941d0010f161a03c0c820400c90600101069004084c200b403d0620038580b0454a10004516003810358080002c036070001031811404034802c00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 37896039 1250 37894789 37894807
    0x302031009051302150405150a0c0b0406090308060904020102071a1b0c10030b0f040504020f100207170109110906030708010603050102130506070209010e0705040306060e0402011707091a 82
    0x12190601c5254100c803c0f082e0303041944104022184000301d0b01452440030320042c0441d6a505000380881c000303401180e581e480062906941d00d48030075074080c15811020040006201da5070b041080058031941d101c496603581c200070401c080c035080e100039005911001062012840030080400241c102c4884d13907081060110410000e8603400505500d20b410800800c0c2440c104510a070361405e18508091002079690310200b02c2260184003003c0c45152180c011074103540b40c070440102012806400c1c0d4020408294000e507640e0320384d10480e9440c0f1103440c06400c9846042c810700c041c81d94091050401c61100504108172840c010742002d9260060000004010009100705001075210304c0000d030722004040314040c04030f1495072206006013010080ca00040c0c2d25050071a06507952b402e281ca03042c0d228510122000d00903900014015480c0040100320000800e865a00c245d100b6030b01c1d072450410f911121070425405952130740c040703814844148442120544100b80e036148034608181030501741 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 37897289 1250 37896039 37896041
    0x604020c1b0301090b09070306051303050706050402011710150c020109030204051b0406081f06020a02011d040207060204030203100605090c0a02030d1407020d03020309030708071407060f0201050a060608070302031009 95
    0x46e609140c0607440340b4030420070840e45018055100c003201c007000c8030b0b441031a140175008c0d109803100140000c2c0e07a400000c085a0192001242c0094030032001603040c9400f2040010b41411801641b0240ca81c00408c102514419420f00030441c3e81030b5900003003a450365007400050038001e4440c209406403034207401002d20a4801503c000c20159079010b0031070400c2c81503a8003410840c0c0504141140040d0144003160b00020055101942071900300e00400c1c01c95240da120160f00540d03130b640b060002401b07005011440e0094815a4021415169028801c0c121802103030580d1180035004903041e400921280d45120252101c82e07503e0043d2440c042c2c4241610b0110b9000e03c07200840e1035810800d016590b0741c10402400e005070903050841c170b1414200744482e0f076401001c3c0d000300035440000780401042026542011041451400c5404850311100c0140c640c00742c00ca5002c005628110010f00612206d0140ea811900c0c2a281e012a9440c0c0d000d044000e54070051400e1040e000f0f0400000c3c82c0021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 37898539 1250 37897289 37897291
    0x6090d0b0c07020d080403060c05070c0e15150a03050c2506090f0624030b0c0a020718140f0402060904090302030717030a0c0201060812090315040312050604020c1b0301090b 76
    0x10510501b83e036141103250100071100800020005c01c1801c2c03000c1d0002944d19460380094030101034007460300d603070740e170612541007030010328003640105060500c00590b00448014010b016004d440602042d600d0b108505106e008440e000c4803181d2206110303410346040b0060113403000e4040c403c003060300116500c4035084816440d501b04c820a55a8035100f14a450f0388a82407551424060341c0420545540c5801c091300002400c6200701340d00018845445038000c10908004150380250071005501d011800300c01403c0c1610400c0c1403208400001d059004034161541c401d903401000036040c003049909100041c0f0940c2c40c01c400351312080107180c020483d10032820391624854006a562480c0050704d49046c2d554100c00e01d41175a0600105000051000c28621800c9540c541c5150300e03010700d44002071a00c2c0350340300c10803034101d000c105000034141d02c10a0600d0010b01c5290610164543c031040c40b00300d1150b0601000190414180d120400d45110b000f407000400c014004201140d55484030900810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 37899789 1250 37898539 37898543
    0x605010807030204050a0c1d21100b01020a030507060b060705030d0902130b0d0803060103091403040906050607081209010f0f0e01060603050c030f09070e16090506090d0b0c07020d 79
    0x888550304100f1868180142644034507802e409001c800741c1620050b00b01c840000c804005000c0c6501d40c4081070322080c91170030030100901106143c02d02500c0c2180e881c0d041511030034024600b80310500300154000121408503030380c5aa205850070a0035281c0100134a440030455074400000c0100e4404030701c0400240c1600c5407c0c8030002503500992041004898211030489445410301c00c0755161650707000d0200703911542100c074143d529035031600100d00500314000b0082055140b500c200034107080020191040e2840d5520801c0701a0310b07842001540d010303241380100784007002c100d5a080140351954154014107aa4008125132039404200c1c41950b11152128041a03902c1c0b128100c410f00074020940100810b090801450a0400f0403100a1000400d08078a414402e8040340320034108009200081030303c0c52000e0400d0820f0f8104194402c6200f000310001024030001003140e18240c42111f00c0190020400d00101c0e8055a5848000070010a0138989180a00190001d611941c1d41e4004442c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 37901039 1250 37899789 37899793
    0xc0201021b0f0105100510080604020c06090f070602060c0306040b010905031b0a050a0b0406210c0c0302010c0e130b0319060501180615080604090215030709090504051b03030706050108 81
    0x40d1016802c01e0840c1c00080a400000408603020042c0d034841985010b260003103881c1a4806035544400f0501074400e4200420760b510070300f030030442100c5001c0f880c40320341c02010003503d1340155500c000b04c0e40c610040c1c5406d4405041040801c1c15132030a135100075144201030401d08802c558920000b800d0100c03500307403082d44c000545c1c174181c00752a00c10b104501802d8103ca0307003040c00d410020201064020b40c01000d06100d01008604a808100c1551500301d8121200070b00c80201d15245c002d050760740c081e0044002d9824207110208040c0100c2c1c003404000005008070865032034100d4100060b200000d003107601809041d030030703410108140b500011041d01805010409500d4480f0f59912035607048000c2c0300c02480d125040c0076800c0342d01d40c040d0300001c0710f280003819a01c036040010020400c804009601100d461282030440c00c145000c0d5100b5005621000000da580750941c00990309d00700c500805070381200300e44070034401d004500c5811040001d001caa0429000303540f054111002a04040303000d0f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 37902289 1250 37901039 37901053
    0x20a03050615030102040810110408030703090312081b030703020409050c07110d08070602030a06090216060507090308070210110313090612030507060b032802090c0708030a0c0201021b 81
    0x1802100b95042c0300c000081d00214a4a0b15200d00c040e11000860030b4501b0a07910380f42e8000b40003a0503000d4602900408044e20382e5000c0502d005040100b00d44821103201050362440240e41e401b030045148a00d00072071940300281d4040300c08902d03070b030710040420b0b041c13503400e00c000f00310440180300d03091280f02003c0d03900390350320b0340c42c1000c0e90342d120b44008452040c0b841562a0000035004000c0c1d88070181e024002503280d8072500d6164001e440b45400c122841440400c444170051a862f4100b4081070003118104429100e2490496482010b8080508982400c0103440c0c011706141c0c1080c0403442a0340f07480b00310607940340442415a40b0991b40c0041400600006000e00301c00751190600600c0301c0e01400680d2181d580e00a8401e0141d09005040d4070340d40c00349410940c80600c2840a141d1321203845c0140c998030003800303186607140b0300401e070300aa914000080202c0003038400c651525030041c0c101800e40d0354404400003c0c000ba2042441195006e0080b46200710610180042180d001409000d0b070f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 37903539 1250 37902289 37902301
    0x60c02030c011401031103030307090603020f0910020303040312062102130501081e0106051003020a110607031a030106050d080310181e0b01090b070204021b0102090102120a0206070e010c020a030506 87
    0xb55100c0d41b9000344c441d400c200188440c2940110510088580c0342c100503856030644020100c0c0703401000502d40d0030214020a94102581c040002c0d8401d42c8241c6900300140307000c04aa004480e0380b40204e07014007803034140e4441070700000000e40c00c030280700030040103441340840b052100740d45007a4000450b59200300400445022001c0142910403210300003003103180e240c9000200d06800041300c0701c0601d50700003110030b50a071160401d0700422803100c0445015003010741d001001800c040c030b8540a51321701000c55103414074060040d00102d810082c0506102681038407080010f034000303084031000f841841d000146031031900d040c40c165105101c10008051200100c0f103064008409849500145006e0414210741e8202c244072064905150742c1c2526000b03a80301160082c4030b10081180801d031000412035000d03005400400341ca8200b81c1c02e0b609a04490401c16402d401184660800360700050005115240300710340300051490145807800ca40807440d0082019032106070800e4415404c10010411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 37904789 1250 37903539 37903553
    0x305040311010e0d1b060c050d0b01030e0706050f0705150402180402090406020a030204240e030a030c0213020906070605040b060109030203070306020318030f0706140c0304060c02030c01140103 85
    0xc40e842824024010291940081c03134950010315161401d01c00243c2c0c0d00348200486241502269600500410141c00e54180180845d000015142441070629101c4510340d4481d004289003102800003d0100d0b80c206042500c0c6c54102040a81688038248181030109908004210703040e24881110605802c141c01440b08801021780c3c80e01088604905002c0142c5030240200d6201d034110000503103482c55403004038082d1003558070180e1306488080c4d075004621840ea00304d01800920f916043e18044a030801d05860b4200c1d2400980454041543c980240c1802c07261f4103030720789103600010702d0050700300300180d6980c100d0355069801d1962071040000300013040b0900758005034242842c500f01895640005e580700010b010091a081d000b0011406c0d01060540310070802c00c1c61815282c0718060080c6400351500301c00000e60f081800d280e460a02c41e41d142e82202c1c01340c0c002851613491075899484030409040003407082d00031884108000d001c80a400e216100c10151401c2501c2659451410004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 37906039 1250 37904789 37904807
    0x1030f0203040203061305011b051c060803070f1110050c0c010306140d0f170d0501151403090a08030a0f0e0c01080103030c0804050907110d0e0303030105040902040603050a0303050403 81
    0x40205031040040c000544d07000510f40d540400710000062072041030307140140c00352100c0c1005001d0442540054580b254000c400ba107514081c4810504c0c900c1502011241610f24500c21802650000c2107814041102119140c00c0c9902a130030344c28210039003002241d000e02482006200103000800ca065020105004803a4030071824030342400450309015408038040c0109520701c0c0301d80041d0403008108410010346452654000c180b4000c0490f40781c184200e55030056442c0d41134103152200100c0c2d44141d0560009008019030b0f2810800c0910101604203503101400d460100c1c492885c01000068450006520465540d480130600c4507507004a01300b580c105ca0140c01c400e8004600d24481a42c4c405e0b459811240c16181c401d0b07c041d098103001c0428450b41d040719402485802c01c01c40c1003034010f030f4506103100c52007044800844400d503049841524032000c0c154941c1007000100060b2425800000c0c0707a60000388005206270752503403007500c3c01c62014821000310351a242000700340b6420984103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 37907289 1250 37906039 37906061
    0x7050303072007030201081315020403051609140601111009050f010b09060d1e080c01020304030905030c090a1e0e07030203070f080712080706050406090c050d0302030316020a0507140103 82
    0x4080c004e09560001c0e00740c800062405825909004280081c8060019000d5003064105030840d0350b20707103030b0403c40e4580f0050001030200c581c5e03483d00006c2d007090601c00c22824078450391f03909040b40c54900044480c90030300114400148645044006405224896214241d00c180e000349400100d00740d60758203440450090520030300c2c04500b00132035919500400300074942d00100d2601c216401d0b1901000280740014007034289100440d209440e410150300540c01a402521104016607490081564170400d040c0a950081d1800c400b1030500340c01600898551440c2064000c411011440310034212212020130f040180d204280800542c00c0c00d01c10a0041c2c0f020803c4080348904016580d03030f81c1d14a43c071030030711841c000c4001e0009204d010b030199101c3d80c0e030002090005042604080c005000d1460050b105001680790010b89482c007501424210756264003d036003160380e4070600e5004042007100100a40c01018074580006801388101c1010302040c0035040c644044035000102210005495 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 37908539 1250 37907289 37907293
    0x1003050709020a021e030f0a0c0204050c042102041d100506010509100809010b0604090c0e0102010b03100b03030d06030c06141c15050415031109040309030b0408070503030720 77
    0x6060f068541c0451440d070300501ca03040c002803040000d01030f40d103103100301d0189042d644404610310703400726400011407007030038000c56061259440b115102d100c188198402d00c807007610b0000740a618180b28548096461b80007c000184181c06540042ea054601c01a000c140d50403031061090105824852503421070003c0c6080c60030b084040740410020300000301c902e428080502c0001d00c4190094000030601e0f80c000d0030b015115540c442051000d03240d203110141c08103001c0f60030300d0201d51051180030380700c0038020001c1040c0d41412414500600103519442c1d018041008040d1520004d4024400214400c0800300e00a502d844001090311b010016240da102d038040040368011210702900c814109a03020001841140216950701c03080b149510054000b820030480d01c19001c180e508e0513007100d0003050500d807241e160000b0410a02c1c81101c004000c59203d001c14800b08e900100071641c490700c0b50341c00300e15040c04c94603118516001200c0c0500054003d42025410420184600c113850401c0300c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 37909789 1250 37908539 37908547
    0xe090a1212061706040b040c0f0306020c010e060c03061002010e010c020a120e011403060f040609050114040603020312070813030b040c0e04230106090e0a0303060e090d05090a030b100305070902 85
    0x48160b110712005d040540307551482004102446903a0720710500502c00803140c418055940d1a0075030294000507442d015039481e020b40c6444031940419550302c0b8107843e900d1300e89150344a0f810801400e10100864003150760715421101e884a003480344ec1c660082c1a001820201440d203884040803138425441010000700e03003120f40c9146d80080c040c0302d030b41c0c485040d45610390703031844003081c02000840400ca03809030034818000b4082100303620043c140c2d17035084030160182d4007420510090350320782e110007500342d41302448003050440c016000d0003815125100703c2e4a40940c0da03005810240c7c5170340080c2c40c901c4410040c8010050200c841000a0103140e0020029203490348039009202003c80b410881200d60b03040b10890300c9000c2d44418003402d03244a080005204400c150b66440416843c00c8000c203280c2140032030a051098000703803098885500400d4400d00040e4103d4503500b1040c0700c550804200103000c00080c0094480e00e05c1204c0007800107550501d03604080345030a515520100c40144100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 37911039 1250 37909789 37909829
    0x5011505070b0f060f0d03080a05010b07080403020d110a090b03060703050c07030c08090a090e0d05040b03010303031e0c030c08150a031704030506010608010303020c041103010e090a121206 83
    0x200380c2c2a880b1241042c3c1d040c00790383c0e075000300305182c29a00003603920007201e89100d400c00d608500264007071040900208400da1721510081c510b841001c50184c11404240001c200511b8003064900c3c2c02440b0b0440052100011004a02154030607084420306c1c645910703507a0000d0408020850f03100103540340c14402d5040108080315544641c81000c3e042000041c008010303ca40c060468003d81d40c0070748907000440c0e851041500900391541c500e102070242c4160306841c00c3c0314100380c07015a010341540c5803640e46190750a4004081d041442102102086100b01140800d4400c008070745c9290389001c940100412001030034013400420041d1703441c3d40084c0310700c150303101c41c04e10405907a840000030171000c3e000160910b85025a9100400343c3c0300c1c000c0081180b60f0701c0f0f280141260f10a808440c1c1a161704001c00c010342c6d40c2c9005003500310005000420000010380804e540101c202d0b42940c2c3c956180e40c40e40e200301c010350071949012034000f540300016000148510f90060a003180d126400322410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 37912289 1250 37911039 37911053
    0x3010609150201060312090e010b0702090f070311070606080d03060b030a0e0a0c030501150905091009021f02061b07050303150118030b060405071107051219060501150507 75
    0xa030045104025500807009000e5000b540305901960308004000c20741c405100c1d000b801c0100c04d002d42032415403010000605c00303001e001521001d650080c01c075005541c40c8000f1a07100c03c402407062003016290940c60000b400000001c000c428002d070004030700d56040c10702807440c2109040c0e41d58109464801d08120140d04c4c0c0c3d0a59401c1a044403012a8030000f01c800180303400800c5202800802004038004104101503010302080d8084444121656960380c403070300708403941110a07608980007110140d07441882c41e8400b0340c03102e1004042840510080d44c030680c0c0020740781c51100c09680000180100c2c8511400c2555070740500c02d6002d0b28116040c0d6a950302c2c0d000107400d10081a11030901401a603006620920302080c0010107244d00e180d481c2084a014002030b01c610340510b280c900440c149500c00d04015403076000e80b80041000314a05814021100c043c2030512641d8001c072000a0807492070243c45083d41801030b00042002d50402032491245101104101d080c000704110403c0040c2c03007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 37913539 1250 37912289 37912307
    0x5010813021c06050a0905070618150c0503030f0f09070302061c0b1002030717030906061003150b18010509090106211d160503100f0204080307081806030106 69
    0x70654041c1c022580c1c80024030051a01c91100520740c500380f0b020040041211343c04120300d81e004108483e022076803540c0680d0110102c0c01c0118900390700744010321104c0c404902c1100a4000341c905040302d054581c880a0440d042580c5010b0b01d900518103100c4040e4084040c0c1e41c0240c0400040e11045145600107403030751161a00e05201c081051a201300322a41a903c60300c920500a0654920414120802500c980c000c030000c4031110041011262030b0001d000c2500e2041c0b0303012008180340d8031258100309501495803150400c05844040040a108000d032805c030043c4000c0f41e045885103031401100f181080d9411110307041100910404010303aa43d10f0b5454110b507000e08140c001c050510403480c0030507405120900b252030404024030303d000300101040c0102c0c0308140940301c0250313110340681400c07440d0748600c43d8558000c1500900081c0c0782c1d4001401e07035400820052038240d882a0386c50858106203829031780d0640201d1003455072070000031f010402e000d04a072410714640c1041005400d00e55 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 37914789 1250 37913539 37913543
    0x121302030616210b040204030516060e0a0302010e030a051b010909020310120602070615030201081308030c0f07170307020d090503030417150c030114031504020603060d0f0309030b0105010813 84
    0xd03c0800110a00d1684540030584002c0c1c020341d0340741d80301d0820541c2c841030201c20064801e40b2078000248544601003040040100818214841c4c2c9542c00450341c0f0341590706501d44c03600903040101c0008000b00018102c1110380040c41e10408810800501010000d50103909450b0040041200b000403010801d0f0640d078090300034007883c04042c20204001d0043c032600a280f2440c28a03000120f664103507140084230b03c00d80c3c8180704e545d500030b42070a807840420801090008103001250394284640040d0070883d80010080e81000c00716203441c8401c0700d104840c415240800000e2101d441c0d410f00ca5540c2c0c080d040c0c00c141d28000d2504000c680e803480b03244141201c00740405a85108010284103083ca150740007031110400e8102300c07900c42980c0d482886145c2140c521031144005a040118161480940d80e00404480ba6140d800b4403505900050001d41e002601d60300702c5000a2181c0542105180603607036402c440c80c02c5150400820106802c02814002040100460070780a0941c2404141e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 37916039 1250 37914789 37914827
    0x1a0a03110f01032f0c03040902031504021606020a141903050c0406020a0f020a0902030f060f010309051b0d0203030c0309090f010b0a0f050c0a053d050408121302030616 74
    0xca8104044d4039030280c0200d01c0d185020002c0c0024281040da0040c41c0500e10007000405000c0310781c81003108038801e0700700e0b52440b985038624400c0801c50a81c0074046003030650a101c144061981d0a640640d0300070f180343c41d509000001c524000035458419a648201c500c0701d0744d0302d040e04018010f90785181c2000b0081048948820202c11522a641217200030b0003034030030640d268109150b008002d05c40440b6460702030004148109250b6100303001e0107412a40142c098511144404c402a060500c00080700ba000301803110404e0060700c00300700501d41342c1414000b654564013500200940d001016201c410340c00c06910043c045240008211220300c5010b090850303400c4c003009002d540d140208223041c041801180d405005201000c83c119400da001820007058801c110030b107180080d03103000242968510182e4030401d0b00c90190f400340383c00c03e01480381d06d410116281c040744102d000c100c4d1480200b40100d4022021404e0030007006801c4049400705880c1d4495600004015010320080101c3c0f030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 37917289 1250 37916039 37916111
    0x602030a140412170c1c0b090403080a06050603010b040b0a03090204050108031c02040e0412020c220506010801180b0a17030c0706030902030c041a0a03110f0103 71
    0x58816980070451034100c140408a5614050800c2c01100002520722804100042e20050100e00c801041c0b900c00c05070600c54034248940c041005a05500c2c110301c98203001c0d0356941c0f0441c240c2d11058a64402c0744a50382e00e00e014504901010141c070300c29840140a820144014805203901c00c1c00e0703c00f07503000b010282e51a40400c0c00c0c203c010308048500030303400505d00000411050b50100c002c00384400d102104440c1d41c1c91005609040344503501c201840303201d080002c90000b40c0281008a810841481180d10070150140010360a2a2580c006070415060700c83d4104561107901480341c1c403170b07400d0030204035562400405803a0f810f07840401c40c822076921070314074400d60b40b016030080203080c500828141c01c010b9403144a5603603000800c040b05500c81e0250019815110307000b510b0550b980039000c3c0002050020501001c4c1c0106c0205490301c4501d005000860f40301e24400800540c083c5141d00c00e07500c1180288004206400c0d5024105800c0c0203400840e83c840305c421020a403000800e0701d010b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 37918539 1250 37917289 37917301
    0x15050a050d021e0405030c01020303041a090312010e01060e030a230a2003010501080a0f08030403090503011505090105030a08090613050d0303060303021204080a150f020406050c01060b09030703060203 88
    0x24400d0001d00c40c0c10f550742d000709840d01503299025200b9603200b5400c54a5494051006981da07000403a40180340841d04501c554604800e540700320f800081200840c0e040004084030070721150400d8020b064182404401003003102d50203140c541e1689410b0380501183c0205131180c0d0000d01c0d00414420324018980c44a1201c04000c000c001d2040d908a5500c200804803000307034614040c42000341a12030341c02c0100200702e1500110799108559403101c1e0072411515aa61152155003000700168107000316080000f41c0741d1000e000d03000000000302854010310303043c0420040381c854180c1245029500420340d100018804404171445414212240d50726000314500d80550100c558004503040640307680b1301c1c0205901904408240c034400d80994800c001c003040c411105001e10320815031950301c0b404000d8007140e16440380600941d140070012075800180129507040c3c0e4041d034000c07800203100103000600100c003031107107030040c122800703045180c084101d000913511120b90101070882c81c0d000002ca19 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 37919789 1250 37918539 37918541
    0xd2105090409030503010e010b0901080403030b011701030f0c0e0c0904020702060705120316020102070210030f1d0714030109080f0a0219080702010f020105070f1817070f15050a050d 80
    0x108100c0d0040c001c0c031a001c81490002e0045e0400e105a8440b540f1382000840c122040b00281c8582c0d40040e9600c0406503940d03103080f0041c1c409810240d041c01850003114600e40700c07908000e4040d500480384210030f0a0039182c4a001000300380c0c0311760a070044403420310008088c0001100c51003581100c0250305c1751810300001c1c14074400c51800030058829103c170041516107040195120b030780c9030082d003500c1d400c850900340d00f41d21518100941c05400101c0503104240a64054004170b4410b981c0010b11203200c04081c0c540084149003c0c4060340505400c11640c0103040310307030120100c1500288460186692030000c140070354020b6103102c45000c15030800c030743d208000c1e4060074035656100b0300400f0054203000305d442e44011802c2e80013818504030609000c1c01401124020031141e600d18003011000385c000c40f0b4201c43d0f85c04401012005410000f201e01004040c03c0c101e02d07880c40603000440c6801c900649509190303100800d09c02d82244aa400c7c0c03a0000c040c3d68456082c2d080c419a5088480502e40c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 37921039 1250 37919789 37919797
    0x102703030e060c15010807080f070305070902030c0d1a0a09140103030f0210050a09120305061f020f0f0708071a03010e060a05030d080a110403050705130902030304091a0d2105 77
    0x4488544000000800d0440047c0c0007040303403030450541e101d4070380d40c00708651142d141d4080030380240d100b100d04001c0e0000395402181d03c420390710b0f00b0034200480908443c06a070000540056100310f99408040140781100c146002005207010401c08010004400d004042c0b0510000d001e02120b07240509502d4002d1002e0340c0181002c0c3c10400c00c910f03054584900900f1030020640300c041c0460001d518560092142c2030003550003d01e072060802041030055803820f031507101903045008401c0000300c01001003090000201c40c000c0036240c6a03007403901052500e200c55002000c0c03c103004120080001580e400c807030554480004003000c0d580e610012455091041d44190f825101c1c00403015051548111094000c881310001031118420002110b010b9000300d000c060070540180d80c0800c1203262002e114903240758008000b00d4072003580e400290950304154049424283c840766043c3c44441c0e03c2e42e6450b88906c0403100e0300b42401d03d94580040340b58054002c4038400b0003880c0101c034518010400d039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 37922289 1250 37921039 37921063
    0x50402030f0d02070608011d040f03051e0301050f0303090616030311030f09010b090114010309060f05040c060e030d050702010c020a05030106080102040f08010e0d080c09102703030e060c 82
    0x9600102d01c40b40001e42d01c0206110311030005040c3c07030020901003640300b008a004c16261001d0f10003901c0f2901e400c110900400e200301e0600c141007150704100794024880e030b081009598540d9450798904802c4c4140001e407071614510a420800ca03040b21542c4031030669103d03500c0e0143e00c2000d0307900361800390001d010803007684000d20341c040104003948020804803481587c021000b4031925140100b4000f40070780038001c20700702d00a1100c150324154420382c082c9000f40c1c02520046040620704100d04c045031000c0d40c0695541000b25414090a60001c1d85421441d10940040201010204d40240300c1c0c010fa843c000c2c1040311440b000420b668414605401816009000b0003806698880180c000c0d80b20b4842c0342c00c1401000f07400200d031041841249403055011010b06860010040c01311010140100250302c010028816450180c0319154071114904840e04e03848060111000e580b00400310840e000f9601a03900141400001d52109450386a034900307440c6da40c1c403903036101c0c00542040a000c00c0c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 37923539 1250 37922289 37922293
    0xf040204083d0f14090601120c05060f070309060e010c06050405010e010e010b0111120a05090d060c020a0b0a0515100309050f010c11071505070204060308030405011508010c02060a050402030f 84
    0x100e026808030b0303640b1008051442d04003c000020f061116030810180849402d10340307070071600c0104400c1110003485288603200e0107890346510380f540b0015040d07130001c0d0b1258000707039030200b644410541c00c850f494019200608041403000c01d40e4000810b807508202008108646980100e020450250400030300300c48140b000780030f0840b11041943c02042044004ca0015807440441c826205012940c2d905070a911840c3c02d28190046400351030350f510004010303420100c01905680071030403a1080303100581d1250b020700000825418a00d02c42c0202410300d464080c91300701480705090803207040900c580800d841600c3c2452000c80150001c1482d0309021748240100301d03c2441100f410351240d503601280d030725030703c01e001c00c10000e131a81d500142c003800c070b8840c01c00080e58040b14081c0010740b4811344014404500281c8950b21a103298005450844260307455800000d00449054005000b8006120017040204401c2d0740c001d59519015007030403840e65985d80803806545050060200003080503003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 37924789 1250 37923539 37923643
    0x10908101a0105040515090a0b070302010501080d0318030e041d03090a0909020a17030906042306190305040206041203050c1b0a03030f110607020c0f04020408 70
    0x200d944040c054000315080d481114460010280d8002d006481c20340343c01428402c0083e0004149018a034040b822031030340b003644000001140c0c40700c0001840401c1c881da002140c1c1d540b41900c3c0a20703200c4d80c00519010b160800c180395020001c6c504500389903035018900000c0300041c50010500800b580040c0c3c04280c3c586150820030340b070001000f0100c0032001c0d940f10318002d42d2035101c04220b606081009501160802c81000282400a8098260220316058034504500180000c00c80c0e8000c3c2e1001801c085c02000c80d10a001001c60502550b10007074800c1440c7c0750081c0ea410441d212107098140c14140c1e6040845c0a40d260304069030080e10a40914050806682c200078115401c0341a40c400103100d19036460b1103040c0350004a6844001c0540406a064107680e4103032002c035030403d818010071203003540000b040c031020401740c1e000703580c15000342a03055882020f01c51410420b40c0c40c6401180104410001101e0004042d030720340b840c201c01441d03c0d04c0350142c407508004e008651044503c802c18 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 37926039 1250 37924789 37924813
    0x91902070f0c09050408070623101805010506160501020c1f14040203031c060b0409050402030d03060311010f050c0a060e0d020609070603050c0d020c0114090615090702070504090c0905070203030c0306040902010908 94
    0x4ad0481c0c2a40d0a2030000007154040e0303550042541c00c00d00230a0340081d002c0c40644148001843c0505965100d05c00160511044699440c50520081e42c07241c00d01e410031080d105100d0980c03251f40c00048078a0400c1810703162540100349c1d82d1103801c00c44c0380c490b601c80380d950f680302d81607610075805440e81861495030b542d0744100d080007404064805034400e00900c8100d8521500921442c4100c82c2c2c40004030b203040b0700c8500192481050140118180003081203401071030300c804e100f4000205e10a0800254800300745002c14684000f12118000f994001000c2c45004000001c0580407581e0a25012540703944800c12461030b409943c551402550010071000391010040d007055000d408050030703001d400c6d0340700c5400c135603a4078055410307004203400048441034034200401c410b94000303900d0045401c0d665a81001c00d013200c0303154905440c8500d400b401800100085d01030f86070020040e04c004d500b10b0030320940d2138403148800380403c2d210315541c3c1100340071a4060200701000344100310595281d05404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 37927289 1250 37926039 37926061
    0x402100306030b190e0f0a0f060603020d05060709060f1b030512150906010c030804020d0309120803040209060303090102190609060507020d03060605040b0405091902070f0c09050408070623 83
    0x403042d50011300c0e0400000e00540040001d400040b84000001031800c1e003015201c0c2003c04a50b0704054070519101c80e008800760f200c100020744c10520401c0104660b10700028001c180c6049a00b02074100007621070780c030740e046500004540301a01904d042c3d84140d4005c1c501640e982c0304402d8400f40005108041100201000311944103a10066800420503580c150045601150041c0002c000c40c07121408500075040607810502514820304100404c0d030b4581340c03040c1c40d07084036020444919000008200031402d01003a15a0007081c2903000b03504203405d0900203925410b50034500c0c900803440310a0301040c002550011701c800c1d07030003640400c00350800040003500e072101d015040010034281880040c0040c401c038200c40840c1c080ea402c99042c00d0410782000010b060203413129020000b2600d01c0325844050b88001c18055201e5020790610b02860319080328030a91a900c842d40d064500020000422100402c98011661001e4005103d0a0440c24080f5030f01040c680744602100140c104071480c544 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 37928539 1250 37927289 37927321
    0xa0504090b09061b03010b09010c1e1703060603180309100e0306060102070630050106050a170106020d0e130501170115080a330f050702010b03060402100306030b 71
    0x106505640e0140e4841074251405800d00d904c1826074903003080100800725040024000150f0145002501c0d03d29503140e5801c503a03c0000e401503d80039100d40d00c0c003001000e240941c441d0282d411050300718581500091944d0000a255a104404208400848000030b10454400c11802040f0213031002510800401c9078200500c443c0c020300c1001c0c0400d140e58000120a400c81d40c0540d512400d155900704140c0b48410322260781094180c031400160740213451801590702800c410f9540648070b258510004101079001441440303843d6142c401401210b0340411041503c15507420100aa0035414010811000f071120035030200602e0032340003054600542c0807040164007030380000d00241c0710000240000300c2061042548942c800c10300d0000040e0035221462400c80050100c2c040804411507007514503105c0300012484075034881c002c442da12070a20075103030490724510081106002c4040401d54425002e40003902c1454001c041800aa01c6908078a018691001501c040d030304220840c4698140d0f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 37929789 1250 37928539 37928551
    0x3060506030f0d030c02030f0316020d0512010b030c04030b1314010e07051504030c090603030210020705030a110c0406060c060509160b0a050904020a020f01060503010204060e0402090a0504090b 85
    0x20414000c62001e150005041024920120140088400503c003d500510640203d48254042032140c54038007207a00c00070794030501d017503400e14070305150144000b0700700740994204405001081c862002006a9200b6241c151200049000d03580d403a5a100c640b450300481d071000f44090f0383e51041001ea4075103c0c3c1c2c084101d500c03c40351520140880c541c11426a4801d07c001d070302c2c40e401084108000e18201b03401c90521180000158902034076502e541080d042d154202c201100c0d242e1008008150341001007410061042c00d0031420030003540c3da0117403640710b0341c8500d10030000301e0030f5101c80b640c0c009e01505401d802c0007002000441c0e52007102414400341c2c0c00098451510300350000e410302001045200b60b100915501c90052420261070503595001011b09404004060011120030f442d02c2c4024a8510743c603070000e0081d20503030440282500c400e50080c0740243d0041c0410488160080111101500101d40140c0c940c505100030800a0b03440d03a20842d401401c00400390f0501400500a80c0a50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 37931039 1250 37929789 37929791
    0x30206040b09041515080402041401150206070504140d060e0601061d031203010501080a0f06120b070e0609040b01050d05100f0609140112090c06030e070603060302130b0604031a010306 81
    0x4040c581e4090b8074520070344244c0803403805e1000c1d0070700e4242c45589620b034403520080c000a190100d04880240c030a000f45c0240207400c401c80000e122940d0100526a44609145031007071900d4100102020080f9212101a0050b104c4211407010403645030040301da5000701500301c81c041e6a40d128010b00c5420302c180201c110f460144d0320044203040100303034005600ca81d64030440c076503481c00c4011100008010030000c49680d5680da11041c0707076290700416000f4206403000c0d079006903450034104595079000d80440188140b0310b28a00207601c2d841c0a50b03071400e1045400242031001d020060b0b642e481b5815200d8038580c500741c204480140958007440a80c1c2403c1c1910081945644090b91001d0350f81c005c8818140d04000c2c1c0280c650703c03460b10b000c40075450071008a0380b130140c1da0f2101d0049846801c61000700340c0300c440d124094401041403a0040005180c144003041c80d54020960390b0380440ea07807000094842c900c2000396142c01c401c980046a0000d52003525501e80b45c45000401000e0004842003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 37932289 1250 37931039 37931051
    0x60403020601090f14010b03060d050109050607080a0504050604081c0609020a0e0603090712080d05070f0e0a0506040b0d020f0c0307031205040206090f0f03030d020d110301061d010504030206040b0904 88
    0x18a101d200700f003000700c1c0d1170200c442d1a900304225044180c00050156905c94003550486000800030b0056071110f920a000500c0d07030b81000305020348000c900510511001c1e01d000304020104400041007900300b50002025550303460200d50140d03901030130303640c16803586080c40400291b10340d42e54014664a5500d0f610803800342c1e031000410400b44003d0755028000d070711182e4144814030900405084851042d042a450b0842c207140b42019034000f01c94000114040e10384803400f00d40c02401004090500300d07120401c5d58205000500640a41e002d41c5d0203031040401c190b5048900f0b0f6045541c0b04501a0986444110380f60f100e65480d4000001200042c2443c0030107044000a80585c1d03006950084c482c0781031226034010300405070030100c80c007070b40250176102035840c43c1c030305000400701c41111140141c3e480c030701141c0c0f64041d9002c43c481860303a504208010080203038071000710040b6000740782c1d511034600b6a80703004a9486c081c540000e5030202c0001000a0482c41c40d0000300640c2c90161428000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 37933539 1250 37932289 37932311
    0x50f1302041a102007230d0b040506040c0503010509150c040302190801110406050301060c0606030b01062316080705011407050d0b0108011503020a09120f1e030905150c06040302060109 81
    0x1170354424401e0194240c02c0b090002001c003803800512603050f0300508003442041c0591901001c86100350303001d54180d000003041c4014840e0380c19022014250a038002d2007141000e480c000da80b00e0140c0341c1c1102c0c1035800008580e4451043c070880d0002d6400400c00c061216510310451014180741c4034a00083d843c0644004258050209907400c030743c050b80340e450440c0e1074268207650514055008403420f41e510b40b0040300141500004a010b011641d41d5405208021070100c2c4c6081c0c0884040000d404c3c1c244410409401803980e500a5540c0c80070007251104190b1500602418218105c0d05820400e0401c01c9212680301020303101211130b07190306005100061005403442d0742c0a001d885915015901e482e50344d14080d4004044508440c50030f0000360f030b565500440c0d805500c1c002181c0e070001120362070043c044801140680e011001c0382c55408185266400781403041d00d8403846009000100d00c403541c400c5911309079aa0f242189054440324541403400a407503007002d0003140384162401842e201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 37934789 1250 37933539 37933543
    0x50a0c02100e03060a0902010806010c0501020c01050903030702070f0317071704060309020418050703061d06010f0501090f0605090907050f07050a030f02120304060b04021308030d050f1302041a1020 87
    0x46687c041c0c41e00700b5241c41d0880112002e00c201d020035501590200108003019009201d140e1184448101640e102c1c03c003e0700080c181082d55200b50110030200e0010f1021651240c1d00c41040000800440e540c2d2055140c182c0882810107c0300311901000705e400500d40b50543c00c074902ea548216020030003400c2e50b12004405c0080140701500316031200300c2c10f00004d401030b8464000d02642c00d00c6c01250103210301c10945003004c240c0000e11001d8113a00c08009a51f048400c00e005404d643c442c1c0082d00b820304200404070f0080048040c803a84800c0041460309018208a6502c1d10800300910b6551007075041680d40d45030200c60807000528640319840c0654030202d0504100b224200810703155403580d0f21030401070b010218445c2d03807048d400c01403002134540080d42e10000f0300d00c1c03001654440542c210b11a08684004103a03c40101a600c104214203541d444a0380c03440760f044400180c098015040e110302c440428403080d401107190305101d03903801e4100440b403c9c0141c00402484076030300c1000c4615 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 37936039 1250 37934789 37934801
    0x31505061c05060f0301060303050403050609120d0207020a030c0308130e13081b06070206190b0a0b0310050a140901080102070308010302100212030f06030c030c03060601050a0c02100e03060a 84
    0x1030200441281c84034054041e40e0080c0f034000c3c60051040c21450780c10700c0001c0c01c65042c0c2e4022408258000340800800070180300d4154807141c0100070389100440c00d003007c841449815444032120b80d0006492086554040400c00655008000015443e40701d140800c0d035580708004001c2001c00f11080021545c944c28001482403401e0b86410401105543d207031040d80c0c020282a01c90501003507890f80c41664100302c0c0e0740c85807001c0e60082000781040c041c0d102218030400740d95003403141802e801d0785090300d80d44480c0088503403400b046070340c0e503452422a5071400215000b095000242c907100081d0980494079400703407004c0444401d0b140b80d9840c00303120300300e00c10703d80010045000c000040025240c040c04012440d2254015a88020040050201c2c00e91003215800d560f03441c424140061414100109081e030a025402001450748030b50001c0e656940080440d410041e00141c48003500c0e1044061000d080c4c1e019007401c180e00c1c541c00700030380503140801015010784079841c0001c0b00708040340500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 37937289 1250 37936039 37936057
    0xb090c0a03020c0102040305010216120201090507120515040c1505070b1f0e0702010204030614070c0602090a050315040203061e0c030c071e020a0b07051c0908070603150506 76
    0x549021100c820a4010f9003120303c0c20380482d5824440000032034000e0000300046003101d00390071094620f1703113404035100702210441c004584c900041a8001030300050240e05589000e100c80c04811a203103816890103103180c5102490b55441810300c0b04100490f10303900c0545404428215101e2481c2c10216514010f50602405801401c00410706090041a028180c1c00e13111881e00d202d00d0310b42d010503c0740386040e1042d800507940060204240b001c94480c140440c084102152400c0c1490000240b5a16403507a01030803041c0d0001d10582c0703a07590301c00e00a00805c000346c2035500340301c3c0f4590b0307480701003400f214142d02901511000a0f1403090561400c01d4403a81e4503403403101038407210300c2860309801c010712440019504000c00c07008920b6505620381d0b603c415480d080d40c403030014814004520b0300b5501c0f894100c03a081c41500300042d00810202801d6160900f164424001c000040f501c5910960008806000d101c6010444541c544c100c4c003046a82228801c21050703590040c40344501c03450200c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 37938539 1250 37937289 37937311
    0x6080115150f1d030109050a1a06100f0f1b081306020601060507140703020604030809040b0f0604050d020a0f06020f0d0905090c03040f060e07080f0a05060c030c12010e01090b09 78
    0x10701448030075281280c0f58110021300000f4a01d2003541d501403600541c440c081d1844218510054844203480005a9100d0380903900b00c0384441c840f06c801b238401046007041c003052200d40c0161800300c602c5150000382050603c8000c50040020703007030100c555802070710300c800c00004e10700b0042096030002031514100c81c02e690b0b800b840c1003e5621001c070210680c0c8800c000718060b010000001d65918409003000e14010003074959103000718001c1000f2182c0c00308070640190054454890345590f002d09580849105840c2030203803808034400110703d606c0f260000c039561030f0150300c040740da160700054002c0c12072049800c88101e4038030b000c1d040d103814101303100d104c1e801081c00000840b004604c0e0080c682082c410001020b040e00140e0f1500d065502e002064a1254000d42e010000b0f910200060803c22040c140600601c0319641c9502c0c0c0c54001c0100300002030b100000c040341150308014100c400c896030701d816040031540c40300b425092186007881000c0300706003000d0148009150a14049001c0e070b02846d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 37939789 1250 37938539 37938557
    0x12c060109030b183a0e0d110603040506070914150d091502030702010f1104050603130b0a1b02030c0615030102130803070b010803130e0a06080115150f 67
    0x510503082c808010042610405044002100540208242103d403000808444086420701150845030705c60b0400c3c2c019285407072040135014580090042c1800c0006a403c00f600a5050820038003058032158102c5c1c02c030000000b04014000e0114080e070282201e990b440ea1074954500c86000d1110207010340070381c0300c4c813411601c43d410380c41c001c0148401942064042404001902e460031704142c0c41d29148416034000041113000c55080c821122801c0347e00c14100900b101c1b68095400b10302542c00b0b041d004050000200750ba007810700c00e07a18000390380802e001c011450040c507608084c22071001011350b0f907280002d145000c9070021003900c281d117014000502040c1d440702c1c4008040c2200c1c510190f007556013000070544000ba80c46240c00900b50f0100203540c0e9064501e0b0400700f00505070300841c1282c0050141191b04081c0c150300e407007100d41d8510b070320380f80381c94407500c500040c26594000703090781d80b074132401c0c00b0000c058040d40c800712003c420000d84248482d079415144400c1800c45080002c002d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 37941039 1250 37939789 37939793
    0x305060604020a0e030613030e150409360c0501030b01051615020d0515010e06070b0c16120e010201050601170429181504060902040e010203012c06010903 68
    0x54003030600800103103400554803003d130000c6410710b24145c4100411154540d4100c003456046100301110010940c1d5460005000d4182118280568010351039a103850381d05841492074880c40c403a4412110105200540e019080c5d13040c040084003800701d421400d04000000c4643c000c0c8a44400164181c40b80c5140c0000495071940001030210215040b4006c9000e107022802c1902c045d1030103034401c500008060811080d8050000354070301d400ca041054030748002c0190745600c1c040e10540f680c0242da5245a031543c48100685000b00b42e002e1200780c200072840f400b403001141c03810600340060340301c00c105030b41070b0f100482c00d0b01c8040303e0f020302041510091a020000c500c0354903a1280c02216002c8405030004204038420027006c0780200d8135081c0c0c809012140030104010110303c0b068400400160a914994040c1440010b03c0501205c3da24560a01951610f410120b10340503440c0c0210f5680d03031034003803004007a401c0003802c1d00c5001020607041694004c81c0070040c00b0b800c05071a003840c542d20310b0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 37942289 1250 37941039 37941041
    0x507020907020a050124080606010c12090315050105040b09010e07050702030a0605070f08092a04090b0405010c0e061303020609210c040e1c050a0203071a04060b0102070305060604 79
    0x90301c014110b1007000070481c04601c1c20b00c02c081a030404009502c031a00743d600402c280000154000c954941c2010084c000c4503a00130f04458901c681c0b0031a615541e6003c81c41c140c0c5c003d10b541d4005491510360740350990112001e903004505840049604100710580c0e5418010740748001d0080c195000c2c0100c01080490340550302902c20207200070b0465641402561311107081c0d40c01070b2028000f081d0740c08034180d03401d508005015400150f28008105c90900d86e00c503201c0c042214180f8800042d5403c1a5103015220383d00400182078020b9031121a908061034010700812030162a080000c450380101c103441c0c50b01000701c1d9001c01002c1a0520828107503001c1110a9000381000f42c1d2107031b601c06e1b00e02c0002d2601800030203c510200090f04940074070301c0500064a004007840041904040b22002800d4040684501c646145162250326001d80c04c40691961140e22405003d60110343c04880e00d03100101c505505c01c9100c0c1006110742030500d401683c0da0300e01400000c045402010028a2604007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 37943539 1250 37942289 37942291
    0x90614030d03020d0612060905010c050a0c02090408040503010e060106030608030c0615010e0d080705060c040608070f022a12030a08010b03090c10020c010206060109062c30010b0105070209 83
    0x20342c150025155a8908451002c0903c01400700d0303d0603102c12304102407100070300c91841c0400d0b031424980e00c0d0100d2548002c1108080190080c860f1510601180500ca140403d0300c01500c1d01034000c1014642c405400344d80d4000034403800c00000d080280100300d542c40441a5a0485040d01c0105036945611409860780c0d070420700c1090400110640b404158ad6035280c00c10106030040c114540d84201c0c0d424401e04100004148440e004010081000440d51083d00190701c101d461428400704bc00040c0d04a09185079810041400c4c68050030502034141034190341070360000120b030042400c0321050b0150b0345070700501c602280441c001c00010008000ca803070041d0740c04414801603132090048400054814500040001c005901c072014107416940c0400000f034003e41d00b400c0c00302200f850150000c0098080980d44480200c208140c00307410b240d01110000340d00c2005140c05005400e0010280804003001c0d21560440d0740c0210b96108504180b1a864008806070f55483c5482a150240404060 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 37944789 1250 37943539 37943557
    0xc0f140c0a02060a090602070b0909130609020301020c150615030105060a03090b0c0301060e2e0306151806030204150c03021507050c07050103050610030504050a05060405010501090614030d0302 85
    0x5141e24820040e070760800113007410741007a160041c6070350602d0f200034501015a0861100c280d01002510b18954801c5000c2c1ea000384001034a885585051404501034002454000d4245d03001040541c0c402c4000b040e2202d220a6120b5441115520b0b81c003005014250345e842841503650400c010b11042c28280f0007000a910705040200d101589035031a00c2140c0000c90b8130003103c24021006010003603105280c2d0801d554212000e41081e0300020004000303103403070302218000590b20955641041e0007a003140d002400400344000e00c13541912070150030301c8030003d61030800390b040c0c22021900320302130f10030746056507a4401400942200001d05640014180341c080d010f40c810840020700c515060b240175441074031300e03070ba4054580c0d209640c41c9240040760b81081d81418248420040142c46500c14510710301e003107250118441c1c8403400c001e0306000031510060043e0281c40104130a01005400c07c1e4100c40e41c0840030040690f98401089030422441c0300d55905400184030400c10a22075009010022 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 37946039 1250 37944789 37944793
    0x12010b0a050d17040e060f0402070c06030f0e030d05010e060108070f0e04020712030915090512210103030201050618010305032a0d020a02030c0f06030a09031b0305030a0c0f140c 78
    0x1184040f0354250342141d482050455060300c1040124203081785c1810101c10169802d6062201c10b40c2c0d062112541809540b040503920204502c460321560010071881d03900c1c0c8192661004c0004900000c0c0000340200c2300c0000c031840200303805503c140d03800c1e8411003031a900c0084070305c06080e00b21072078032030b026200d9841902402100f01240c3c030010500703103c841c1d07610300151811070703458480228001e460041c02002c2c6030141d980003107803010900160101980300d01d02d07983c507080c00e8109909201114203100718813070140007208054055000f140242412507118002d0b20400c40580104003090200902c243c00512441c48080c81c801e00c2441d1904036103000302c070000004450380b89020030510070000146d00c0341d550542542028440e00da05098140d51040c000205000030a05600c40580681e6010381d80700613100a062151b80320070310950028034542d01490345800c00524070b41040c1d8590f82510b1400c03035413a5065004454110590481d61100105d01d82070038a00c1005400409032040c180c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 37947289 1250 37946039 37946063
    0x1061107030b0411130c02071e0e0a0e010204030804090b03010204050f0103020c01140705090909031e0706110a0e03060f190e1f060e010e090c04090f0b041112010b0a050d 75
    0xa80d10300e00703175140311034060100041ca04d603404d000903d4448550300c500c0100410b150b12049402c91104104156a0f00003900348158032102c2c4080010640b14602c61402d500c081070100c10064440c3c002c004540d40b200c1b050101c607075504209800c1348030382c0c130546d176004c1510a84900d01d03500075000f902030001c2810002030081c448851085400c202144c81c0300000b24001540105850159801c0340c0040802000350705000c1c20b11690010790900008002079100042010703000c0009941121440c0500900031948075440d203000034003007240ea80c010512a010701c0303001070f8400da07048400030b03c944809401c100c245441c4003911001020b850075885258020911004c7d200345d8402411480745030301c0140042c41618008159400050680088184d00c40e00780a10504000015031010b103800c040382c0010300d40d034440c5444d20700c200f1410001010ba0380028104424070995807459010004186d0340301c2d51043c00c0800d401d00b00c0b1003d00980d82d0040d44c4d0f43d03003402142072401c0701071440340c0700340e02425207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 37948539 1250 37947289 37947323
    0xf0e010903030e15060a0509040c030512031005060a02060606030c13030506071701030c09023a0c0e06030109090201020a08030a0b03011416120b0604090b040501061107030b04 77
    0x25101549001d9002c2a140d4a1000408104104841107444a043d2420a80c204400010300c030888500c2454401d0170143d0101d81480107100c401b80080d54400102c5200750f40364020303056150012580321b503524200040000e40303801e200c400c03036404d400a540500f51903a41c6200300a02508090184800d540d024042c0801140d0000720b2080a50701810051000d440c003d0401407a8000301e09110805071594401000001e40028040c1d003910714100b405131301e40b00c408202211400882e200c214a421000024801d000640c1400041ea40c8403030703806100c201c01d114000e403070000301c1441140d082002003004012603c840d600c1904050301c148191100c00000c1e4407405442c2e001030b245c511080342c0d120200e40c554a000d203d21b1810b04004100d62034a40341108401d00d00f4881032034250140984034a8000c00c03923402c1d034002640000c1c005c20607600e860b151945540104504016203018610304400800c1c16030180100125003503454000b803181c54116950003400c034201070801c4404509402031010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 37949645 1106 37948539 37948541
    0x1805100602030a051c0603080304050d030e250b0a0801080606010201050103030c030807020109050708010f0b0904080406140702060f032502030412110414180f100f0e01 74
    0xa1501c01c00041c4200e42c5808041207180c1524041b008000c03c50360304040c60055000d02c04556a500003060190115070301620b24120302e6000380c620000c1f815030f100256002c0780702410910442540d80317002c0c203081c0d0810045000480c450341c0040c4200e00c41000b005034016424030091140b07525540300a4001442c0142c081c0421090030000b800c034034002d40015940702d920004542c0513940c4c40e00180c1c028401c4001d042d444501b4100362040c107107090140740d03000e190404141d0745131510b449001d461036044044802801c070402e00c1490003691743d4101421074150046034241e66403030804a0218140e81c607080d005242512100e0304015680e000003541c0c1503480d040e08642c200459824503c5c0140c1048034019845800c1048451071102c40d010258002c401130140941c0488240301138545404800102d110158490791004000d0100754114a070b4003c0d55030400900c3d00107940e5018 = true := by decide +kernel

theorem cover : BRFrame.Cov 37769789 37949645 := by
  have h0 := BRFrame.cov_init 37769789
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37769789 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 37769789 ≤ n) (h2 : n < 37949645) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
