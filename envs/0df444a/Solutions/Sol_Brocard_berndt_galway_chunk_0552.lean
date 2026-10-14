-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0552
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:24:40.341932+00:00
-- url     : https://prove2.me/submissions/6c62dbdd-2b10-421f-8855-5d400c7da300

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 99100719 ≤ n < 99280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 99101969 1250 99100719 99100733
    0x402032811030106021f1e09060b12010f1107020a17010605150d0c03060501140a02030412060506150a020a0308130c0b04181505090c0d0e03120114030a03030c110604 73
    0x1000709510b907107581c960051584c40600a4030146c84000441030b41961810080307e01600c070344481a2242600d80a507002d10341c8604102e0040b0002d030500010700c5c10f08220100017505ca0296607a80740907418455100981d589030a1340045401103654184040740d05060540035260790362105500008200c00244070501540052000c030341c01110030000380341842006d40403680b06015150002e40086040000000088014802c060140c01141c1c01c1960314036001c8512521207000300d41443d241c10a0103218240145801403521503c081c160030170320003e000030b61310b4031042c0020342006804d6001c81d0800020b4803007185801d4000d85060803250301e030010a03060f640144564103d44080c5255450149410311410740012002e0b418000058540005c10201d144081c00f1140320241c02c210203080803a280c0304d46108a00c2a802860f00c4040e06000c0d01c001c000c0581c4040c600c0d041307180754044a50790200d40c01034a250700d03040c005042c1040e140c08076040340040684104030b2240300140701c01d0101c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 99103219 1250 99101969 99101983
    0x5190314060105040b040e0c1309060608070f0f14060d06090c020f0706020d080a020a2109030f0311030f0702030415020c15040b0a05090310020d090b0105040203281103010602 77
    0x3a14140100510a010f06c000c0b030700006058181c42d00140410142031400b4010702e203000040040200c0c195030507032100030881c1c1080d88284200c0d131024004010740155040c400c001403200681511509180ca00755134150b4000052042c4103810001c0c58402c804102e038000d601802c1e00010400c0044115600607540ea500e0107805c00e258400c0f90400500540b0010301420503100d01c0c0e4901c5195203a04100f00c0203500710303030703200303014068030004c0c10309880040c0151020030514620045021121340c10007030989110b44407184e0406003043ca601c07903e04004c004481e08060500c600c140c2c0340c0d9900c00120f007140030301d801c28944075181c04036260605030700050b004e11080d0112048001d24101452400b00c0d80b2a80c8241000e480301400080707d081d020350b0140002c04805000d45080c8018071036110101c3c1e00159000d5a81581c2e00321000030721030140e02c9180585000e40e011813650420355981e0740c402c040180e281107202c0e00706841c00c80b9418160003413008010400d07501c07900c1c0c0d611a0070283d02d0703004c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 99104469 1250 99103219 99103229
    0x1c0f0c03050708010e0601020a0b0901021207090303180e070f0309020301180c0f031101180f030b0405060906100b07110603040b07020d02190209070c051006050a0906080601051903140601 82
    0x9010020400d005c24500075409014160001c0c2409440750741c40c401c0800300146000c070070f55070a00c2090b11400460451920400103555120022403c501d00a40740c00d050b025071903004071450400b405480c0054201c9500690b50341002e241228001408601800003100029015400c1500040c1848490030041600c0d61045290101280d00e9110000c1058013500c0007401400314080c2c111055402400c46003030707041013801c003030041d1900c4403101403007001a980119000d0b1503810810081c04000d001e0107411825800c0a0261403c100aa801103d40345d4011500d45050001c3c1100c1041128a4952404000038203119104d14150628a00700e41c412075940016001e1030004c1289203101040b40504071403000055031208038242c0a001101c200208100240b20400d181c07031001c140f08100c40648550303000000301e482402c000c144810103100b94022040242006c03021b0100540c04101c4d5410340b4825a50312612100e642000c0244905940c405800c00c101410104004080800c490341654 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 99105719 1250 99104469 99104477
    0x20715021c02120109020708120c07030305011e0302040f0b0405090d020c0a1805180109050a03030b0a050306040b13020a030b0105010305060108040b071422030b01090504081c0f0c030507 82
    0x90181c0c10710203901c101c2208521000380640140010a4141e001d40009801000c0c41d13420500060990009030b0810340300c2e83d0103240e004c1390300c00400d5494000c203405095030b211002c4200307e43c003908285420003408028032079502d0f16a041d14041c4640c0c0011004900104248028207003081c91301d8039079020001502c014040e03001b034402e09013410701203001110120310030510055100740040c0c0060601910528482d540e10581c025814024022850628010740240c005400c0307520f0003030100d0b000013600300c2c06242c0600c41001316640202d40c15500c95001601044655100b4254411000b032141d00203500840201022007408103407824541605d0083e03d0810442c0c5401c0300568172040100c400500391400b44002401c118441c0b812507102d0401c182425080403800c600c90265542540f14500051074040030030818001e15807c601c3c010b01c4984420055030819031116400c522820003464007a034500b4940b14a81816030703000c8503045000310020000e00d0f2010f06c0c01009000241d504500103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 99106969 1250 99105719 99105757
    0x1020102220806070e060403170f04030303050618011a0702030a08070b010905070806060403120c02211506031c0e0303030408092403060d03030f0e070302120a030f0c020402071502 79
    0x400e01900070717419001c50040c81d02e82172610310340c1c0f01130001a0f80f80c0c5000780b200007400800601d0030504040c0000e50702c20b8402140c985440300510400b916600b4501d05024180303c0100103081c9000d20028a0b4204011510342d150620700200e4503183d2844030080107034400050850900113141c0c800c5051740e182d44010302c05a00c1c0c0d10300c211140c04060700ca2641c0b214040100b080028640184107008002c2c508000b890044070340c00041c021441a00000b44040c00c418441d80c8040701842079105c2c1c0d40000d000d00084c1d09080c0d000c241c5d9404500e09040040b0940c124803401c544c0924240500c0e060020102c1c1d59901e01464074403c2908524840341c001e401101e503e0001131152103202e5030003102151890305581d226410841d0b28402200154203042d954541007070107204600944900c0003504008042e9646184188101c51030b140b22031008a8000c0701055001a0380040842088070750348c41c0c40c081ca803003076000090007442a81340050403400503419081c07020410f84c0107400f00700d001114200034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 99108219 1250 99106969 99106981
    0x80703080109050c0f07032f010e1902150706050a0603020906100c0605101e0608010f0b040e04030e0904030801051002030406020304170a140109110f01020c040b01020102220806 78
    0x640784180e82d0425084410701101d618021300b04003034060700707020f8035104e1038240300a034843c4c089018440d05d03810b400626204411207234909001d1948042002002001414500004000848441d000c024400c2c40a0610302d43c85140340c406580d00306401c450204003900b0a002c0350303c002e02c400c3c030080b4000c490340000200c0700e00d40b65060b007013141202d40700d0908213511603850f000288402003c0e41820f07690b0311000b09104c12414803218032185c000b00e56982150a003900a01031850503405a44c22400c142070030310800da06007040d07600b200c01400e5414216151442d051799090800c424003a0803210840030841403681c001415030407141c3c103503491520745029500880e100c1c881c074010349003d68030800040001448140202020528002c1601d0040600d9550400e600170220a070040c0703607440d03022130400d0145003403070728540708421908001c54070510b60002c0c0d1642580070344075115a86d03c24243c40035900030b404032070000700741c105526080d030074100003003952400740c1c055801244510400614 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 99109469 1250 99108219 99108221
    0x12003160306030b0403110115030501143102040902120109060b01110312090c0409052104030c05040207061b02010e12040522060b040e01090c0e0f06090604030206030103080703080109 81
    0x3043e00d4002e9000b03449960780f5141030b5a42c2803104901c400369982c030054a50300f40158201d0b50040d6110b0380010801c076105803424002400050802000c24140301d422785006610107004060701d00041085440303200b030b6800094000e243c1d074500650004800b51000b00f0b179400c107605c08841a40b0454082041b181d0701c800444580d2002010600c3c143d10401030380d9178031200d240a02d98440c000031300315408a40920081800c2d6080840110740a0b4045004041900030503001164103443c59a082d0307040500e140c0b03d03015400701611505004540c00900c54050220f07c0c3c2040c0d526561086c62034080540021000f1300800d0004d0400805019108400c00740702c0702c5800700d42c100c03400148803048a01c5018080c0c5503408580010009071583e881c0b00145031001d10303001d8001030a42c013051342030942c0340100c030b1400d0303840c10a40748003004005002407009a84240c400700c003880041d00c0187d02c8170500300c0802c0080c440e50f04080d5005401000000070861030310003e094261003039882c9032190b681c81e19100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 99110719 1250 99109469 99109481
    0xa060519090303090902161a040b070806010804060506061905090f0d0b04030509031005090c1002060906070f200d11070803070b0c040e0412020f1b0d03020120031603 73
    0x140002c60300c0c4d404000300c10040d000381809081c0c2d1660080d28504540e1007400309500d180d20005000d640c5410402804103c150300c0d94441d0b018240842d151901c038000810020009000418898ae5400450f029030be030402940c412004401240b20031b441000005001a000125068441c0310f00b40310340345180c10400c2c40b40c1c515540c090144641c688490350180c8054100116264051090201000c098410380c01554041c2032040041e2880e0a4072005001d64a19110100401d550009090000040000940f40d5200805252051155420380030407942d4011054240550502d44a40303031403201004100841d050301c05855a00c540d0800e041980c0e1100138502c124516030b0028810f15000c500d4821005d035200002d02c08551409454060400020f60150f83c107030703004626640c000d80e10540401161000260745001098040e08031250501e6850100d0b2005008844452111040600075045082c284030303010171004140c124600965011b0700100c3d00c0150300c48001c059001d00c20b010307116031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 99111969 1250 99110719 99110723
    0x90615060708090906060702090f0105030d0e10080603030f040e0a060f0e0a110904050c0702031204050f010c020a0801110d060914012112020f28140304050a0605190903 74
    0x907030401083d0410445800300051000d44c105e401007200da401a034841244e988900d6100150f40d40c0c950402c0300b89407628070341f41c4500051040e038486000f84c2e5034607003d4140c550201450301c542503691341f00c040380c01c40c0a007a0001080c1140800c000c62a0340c40341c16032500c82c002c00e40041042540d1070b07034010300c0d501d52440b5103055140c0d10030104402410715008007403c16240c02c072031842c00d808403002c40c0072524100c455034211040815410210b1070305001d400001d03d4288009801d00c1e090600190140108020050500c010004190211749901400d0f40c000c051800c002c005c16128120040400d83c01100000186403604c0300c00700f8019103900c22202c074056180301c106940e81c24090000e1010354424401624200b11013100e07800244881040e080165495002e40110362003da0124503000303000e001414007510480f0103541000004c01010b80b0b007608440001c09540600c4c03001c40c2184180d804c8560800d4030540c0101c0c0c0b60381c2002c020401020b2049600345021500003040f580d0000781d002c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 99113219 1250 99111969 99111983
    0x31603180521010b190905060405090c0f0d020d0b06120721080702030d12060b04050f151e04150e030d11030906040f03021002030c06070c0c0b030906150607 69
    0x2c9464495164492100440502c00060004803200010f2851210142c99400000b5001418422210f40d0700600d504064195014042400c158a601361600000c44e00030b80584d000d44240e01180da41e01700010841034003e040e2000100507414465040202164564014031000e204424204000140d280495081a000400145120180c0c18034240e4200040d2200c101c1440090007580e001e001c0f80303036580800c0c1c607180300c0060a1501481075403590b82c003030408100c007071000300709a0b04c592010400c540401c4607612001210804a04414042d0300a0340700b4510000c070b070804030040b040c4002c205485028802e10381115443d04102d134041c0e0240740064040c1c0010081c0304005029840c0090191410300699091080000c00304042b40c100781e02c44041e10b2669802042035040ca410a80070342e11951015502d4000000f080d02d5440001901ca10708101e210810002400036884601000d40072488007540d89040031045141c2d907042c03e40b0241012045038031000300074949501100c0d203996016903 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 99114469 1250 99113219 99113239
    0x6060907090608060a030602030703050109050603010b01270e040b01061d030d2001021315030501030302120d0f0608030d050a0605030d0810081207031b02010c060213080316031805 79
    0x6403c6846180c0984035070380142c0542e0012000400e02d0020f5841515582c1d000609580f4045000c0300f03030b500142486000f07915059400e50941d0748075840c000c210640041840220110300b880c440545843d0344070968017060360007440100700072042071504071002c07617903010304969911002c9001c00842007000303941070380031070302c83c0700d855008801454002c040303e10566000289102d0301405d99000711421005142580340501c0b00320f0403c1702d100007000c0c0d80d241c208420340c115030b800f940e50040d1441e504d450100100f500010a41c41d0741002100c0e01c0710300024449240d0742c014080d1390341c1001034200703a021308201c0040e01c007e44921070300c0211031000b401000b40c1464100180d0320003070040c04103951440384460100b1080e00400800c1c110b09103841d0b01c1941d40c0403d0500030054500301014000c0c01d410202c1d00005130303a11070180c1003800d40001e030041e500d0002c41c0404c5003614083d1b000300990702001c1400121062903895245c4214000d44560b04002c007400c144c000040c40710f000740f03580301200700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 99115719 1250 99114469 99114479
    0x240103030c0201111006240215040501020c030a0806011e09060c0507090908130605130605220308041a09130905070b0d0228020706080606090d060b01020606090709 72
    0x700030700e41d41a00605000030404051039100d070501d036094090396415500c0d60300400208102443d141c07012a07802c00030304180729174031030001e44480d06450a0a421204040414203005013035040b944801c59500450b40d40e103d0708240580b03070000860360310340842c514144441d4240b050642d08490110140d84001c8042d04084040d100004400c0301620188030f07040c008240381516115100c02940540b02c1c0079160311241039a03414a90301074101408000703040c000c030200b110000d1a14010340d540e41c2070142d103d24481d0b00c2d40c4448a0f801480c4110000e418000000340281480100259004441d4411f0009910301d9106c2d80b40c85441d04041d000504072041c000100c05540c0b1101c0424402e509076000780b6a0b0341c2180240f6007003500800c030a1a40061620302c1041700560f0046c03100040141c030404107902c090003940320741300c03403050b242440380c8a0002000781d5903840031610a000d006000c10688070032800c0034001040035034581800741c0f003081c000c504039240c02004036100304440c0c0da44296030f038244 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 99116969 1250 99115719 99115727
    0x215031609142d040f1a0324130b240109081b0d0203071401080114010f030c030219020307050105060a0b070f06020403080d0e12040b07031d031e24010303 68
    0x10210800c04070106400100c1d00d84d03510f00a11400214850000c82d01d000c1480740c94840c0c035401d2844c24440e5001701096034030b003003554080c50110f01240501d403409550321540742c12a0f80d0a111f006090219500802000b901601c44140680051071044042c0321507a03401552020101c0c06102101c0d440718a15035510b550000203200700c1380707001e040300016080035030100303140c441b13617401c02c444000c0492074600080d640710900c68018030256104801400020001038a0811a074000d8810145c40d024644180c80c00303901100d00341801100002c60440750031000035141d0b044888200c0321075003050085406850008240000d443c002c4440c2403070902c141e920307401c4140121a007164210380a0000101180b81c2101418415114200103d420302e26034500500344182e4082c0d032039090780c0c1400f0a0284c4d4064005030f490040c1d050501398440c0d6000c3c0c0081d04000c1c00c9a01207680f511072050700840c4840113107001d0358000082c2c0c5c00c84028000702010b01d10009035064500a0850040b00100042882 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 99118219 1250 99116969 99117019
    0xd0e06070c080a0803070e06070b0f0604090c0b07050735070305010603210309030f110712030507050d0905130b24041503090506070804021503160914 66
    0x400c1000020960351480914100030f00488140e454080100070009180d400c410400600502220702501e012842c0e40d13044810040a0f101c1d4024030880d000049190311940d102200060300107404006882d5104c0c0440c40c80e5000c1c1d04102ca09004103100041d80e6145a20b40111803029014409500f0782d030342038a003a000c40f610000d080c540c42001070004c0416030a200c0d5501650040c500321148a0491119480390600e0541131010103241c810141c02080d809503801d1300d1004140b40c06048820304942592801043d608014100e1880240080c10180c21a0003004860710034425585102e806d100700745c0d10016144103003500520a200c0500412101e079110344c0d800c1c0e000a02856040c000100c417591602081c030565030710844006070500074410441803118100115250a0084801d81c0d55066101d0801406a4080c407400d44c0116045545030030007044010183c1e03440c02e0712440c06201500e0000f50390320010000c40c43d8041c0114180d0132250080f602c00c000640390f00c80740ca403840c4454185401d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 99119469 1250 99118219 99118223
    0x106050f0409020c030711090f24090a05061c03080a0c03022203020306010b04060c0602030703020f0a0210180b16030e01090606030b011202101103070606150e030d0e0607 75
    0xe00300008540b1001c0c5201034401c1d2440e02c070041d600d81419141901c0c4005480301b8013440346803688200180c8020002000da409207c9440c09403e11400c0c01c4d00c4640a03182d010352541c00401d000800070081196440140f044c0812a25a2003104000b541074290600c1980043c0008030800006524801d90b0341180da00010a0302e40140380c056084000c2c02e080c002e40c0d017000c1885501482c1001585010803032180905200302c0840c1ca001e142000103400382c0e8400d00000c00c2140c000c40003a403920b0081c0d041c1c881c001640081c00c1d07650301806600a44a0171300c01c8002c0c103100d2904841c407207041c04080c89401c0042d800050040642c9440690741e01c01ca6042c1504000c160b11441940c1400c4003e002d80032100380b0940c4003094090a515040d02e580c2d00503080142003040e9003940102503035510490f07036120007103070078500c0c0c000407a40c03c020701394403c1000c09004a4200400019088100300f008508100c4030303a10200c1410302c08040649840d5840c5d880d00024241c00350b100242e11b401402809400c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 99120719 1250 99119469 99119497
    0x3020a0b071704140d05040f030204240e0412080106050d021e0a02070e0901020c030708031b03151002010e0304140f1f08160c11120f24010e010605 65
    0x8541d004440700d0b01c0b008840032984038406000290085030100200f41411420b424214102410142032020350303038051001912550310303404c1409420600710765240390302904180f840c00650301c840d1441e1001d0025141281c818a06400c08640144203901e940c2c161506a544c0b41c0c035241c0c0040451000e5000034001c05040f14090604808952203140100303146e8403a5006014003626206a1100c4041c0c01004c8074000d9004001d015050b02c404400c03986032603881120540c907600c4202902c0d009040f41d1501c1c066144000003802407010440007900c480040845422038240c854403070890a8405907072038420701343c1c41803100303000c54000c603504d5215205019002125007480200064501460982527404000d0000520b480c6103510810481d032201c08919101d95800b900d1703400410060700450060326803c0951040d030025503400d030721000e91079101400c81c2c0e00404102d03074007038807542120008141c0d038030141810310b880702207100c09038101d03104c144400c51240c0c03802c0c0d400c2e40c1507842142160090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 99121969 1250 99120719 99120737
    0x6030f0f0606030b040f050906040b09030c0a0809040b04090b011a2709070c0305030c03060d120f020c010c020901050607060b06030103050c150f160501021b030306190303020a0b07 79
    0x210350610510300140419540890348108540034001207030210103418074014104010404541c0c0e00085c1a600140c3c01040740036540e6541c00700f24158000e40000400781c1c02000044414131400b040501310070401103408001040301d80040004950b1800e000030505040d01c00100081c0d00c0200c8000f05030f08246050f10301d85030900800000503d07034075045e10152004201d01c042d00382810300702103034488114209240c0c103500312f03100a071280c00b0043c4103911011000000540b584c680c3c822081440c1d03403020130881c14048641c0068a07018465207000018400e51402d000d4640c410f00101c02101d4016184025503402c01003401203e6105e0314003a180c0d40d4540502510948449008500a6000d040070300640801c110421040c242441d41240c1d00200510004440e110b44c80e045880c00554104000300041480c03420340c1c060b0184516901c0d242602c03981c03030303400000e01000442c41410101c0e0080d0300c2d000b5540d510006a1103c0c000940180c4c40820100c00207544048140c0e0000620304200f844 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 99123219 1250 99121969 99121991
    0xc0301090c03060605091b070f0807051506030303130b100b270d030f0804020321040e061009030305030414070308180d02090c07081c06050310050403080106030f 71
    0x2503440c160340c00c8030903440030341d01001444602c0c03050350080c00044644031864141760118501540400d07221101100002030352504200b0b102072000c1d00d2744d6200d083c403a02c8031424242a500c13005201c401001003103155002614501e404401c85e0700c0b6881480004214400585174a0840f881c010b1172078080340345d40c000220300c2000c048041e0400d0f40c1c917140701a40c4801c0201402d24801c40d61000d4074080c14035000c10400082d000919840446594648a0170641e11400000e2070042101e02081d0b21091044000701543c40c1200100180d8034400140984d60f1208800e20121150304800c100004550a005000207481400116002405052041400c004801d105401e11845d0751080b14900740003d418604007881c080e5010a00200311080360741d10040b07030040b42501c900105400d490940020b581000c1104590075030b0360000c1d840220340000101c64a04800800d5a40074603442481512000d080300851402114030441e403540d51510541d1038460250043d0003803580f480f940c141c4895400700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 99124469 1250 99123219 99123221
    0x30405060f0a180b120405010b090901050703060e09071412030d150608060a0635010303020f0604051902040b0414180304030c051e0a1e091a120c0301 66
    0x79225164554540d5035040192004101007020400e180d158038003000051134000680d584513031006120741059a85240c4180104030b0102c1d5640d0141c21141442446401503115901c103c500740c4041201d992199009800c241c030441e1000566403084100340604410b46040389800300e0080d041d1100800c003800d03500e080d80c0080302000d080c7c0780d6038101d10381d16003403008403100200701504120249091050126866160743d001c1d950600001800d0740311071241d12082105040070004603107902c44280c805154030b9010a00c415001482034840f480210400402d640b805658018001c10781c42c249080c640c2e8484d08610030030380e0f0143d600c04a011441d11140070380c80740c0a00d00040c0d00031515000280c0c82228070207a03449805540144801e0000418150b504003e503401101e00c440d50300071009080c10b1418002c855070380c1040640c1800909000c6042c00480000f18401c000d42c0140d8840c4880411140c60095001c171101c400760429031a401c00c014100c01c58808202070340e06200074200403074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 99125719 1250 99124469 99124477
    0x902010e060d0c0912080a03110d0608010906050705030f0114010512090c011e0e0d060b060c0a1415040308070c0b0705040f050901050604051201090f03050c0c0f130e03040506 77
    0x110200741c540080c100d070160700210040190058413120714030685c041e140c04545003da40114424107603074001c4594420721840588000c1d48403440180501d5841d03005680c040d10307505a089800c00e0608011556240c090804e80c4e100b031081e2500076031181e1070000401c06954103000c100c0e060105c104007111032151700007031aa12445002006203050445200018021191540602451156003000d00a600d0b80504070440c05841210785003200c0d880b40c241704005082c260031381a48444001103130040f5040c0843d0b015807842c05066908465013070840c00c144c0b18411520480030f2048050001400640510f1400390025018500000c51522642d11051800c000761a4000840c030086401c0051008940c605005442c00b41e886101c4c5501d00710200e0441c0c0114010301d4424a01003c00b810034000035800040842d800482c0c080480c0080c3c00c000e440c030b50010740d40780030340e020780c0724624414108050b03409044280a0903032484600000d154000500602c6296402c0c0e010800000800781ea41074050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 99126969 1250 99125719 99125737
    0xe040210030212070503040308090a051b01021c09150504030506010e07020316030e10020111030c090d0b01030606060818100c020c22050f150607021f0801030203011805100902010e06 80
    0x3c1e1b589013864100504840c200801d062800d0780103c0a40000580104030341c002800900d00c1d4400c00303460900140c1c103003a44880440000d108445000b90040c1d404400c440446800c41310803498a480c03940c0440d0307984200c0c00003500d546d00078001084000114400160301c8000c0d0b10640b414003503100c0660102280e0040c0980001e002200e1203201890310300c0300907003510b0503030001300481e401ca501c2c1350849000007050301107203c034040388901c041d0b241e8000c941d00c241c0c0d100d424401301c0e6071a840d0650040566000e10f1002808440c00210100d0b41158050070b030395031400c014802c201450034407074054824110041d04501680d20101c445440e0607000d100d034846484030a01442c04407459107400c0f0340d0b004082e40880d0210f030041c007151348007003081c1150b0003500340e07000c079030300d140364008250240c2c035404404415030b08030590424219840340343c87d8140c9108400030301c81b0341e41c80490607035015090f00025116812540d101981422a039102640c01d038410705044100d480942c000504940101e004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 99128219 1250 99126969 99126977
    0x90512120915031e0a0903090e1302060d020c011b0507020907030e0d0c050d03200702010c0b07080a14010b09091905011211010206010b0708072d06050c03010e04021003021207 77
    0x80313040741c2d0780500c6610b903204490700320030000707062244c9006000c20840e02c107007101c8983c01008900c001c00400d03400007156801402e40d036a900141540507000394002041c0c5102035107024201e01000d40c00c03940c01c2c0e0780216142e40703035800d000b09902040030a40303014001d0000d00d0394403100d09001d8a02031000d23805403c61784d120302c01a809141815401c00c9044620342d4205894210b19405a442400d240710768601202d046540f00e038100c0c4010307201d007085540040c005540b104104282a5840200c0d688150415002844a184c482c0c00e0149641000c2c0940c06042c43c00f0f10001e011350610824140d0300008000000340d491440c162101c0488034282c104a400d0303400800c1082c05d00901c42c0400c4904c040c02e2004044075031404000410601030f07a803000f4a940c90002d611030a10054100e4202600395a549400b030a03400300c1001408480481412102c4504180c006800744c031044c0142c07412141504408103640e41d465081060019440d1408420b040e400e0181602e82001180914030403030058407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 99129469 1250 99128219 99128251
    0x3071502030a03060e10060507030c0b240306040b06010c060219051e040602030306090601020c03010e0705100504050603060d3924050309010e060a090309051212091503 74
    0xc0101514202c3d0171000741700c50804140020302402581c0c0c0004c41c3c546280007919004603203001c5500725118413000d4202c00c1c110701481403040400388060340c1304013400d02d241d6a616a86007030507120320040301c002d400030088400246455015600c02c1a05c948503402c01860401c1300328552084019942e07150000410204500d8652180c02041000680024015504082c40e00c1d800a503a03200003000306015061800101c0c2d1705134000c016021507105c005009024003450620041d42d900c0b411302c2910301c11414518511071903401360302183c00b41d50028003401d14680d202c10500035400900401100e103001840469503082c01c010180390b4013079402054410740e00491031540e6010304501d4000704c460400024080002e84c0201c0850081103a0a003001900c075034a50700107600420400c4450103580c010001084441c1c4800c1d03200594480c425261450348035120300502c603229515034061855948402803105154a0785000b030005038030700408130f0390641c60b00c941c060159082954440301d0815500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 99130719 1250 99129469 99129487
    0x1b011b05010c0818060103031206081005070806040207020d170f0f03040615270e07030302030909010911040e041b0815010603180206030901020f1c110f12060307150203 74
    0x4100180c02130b010000d00e03014401c44009042d220803062100a0910050a080301001e8810790800d07401010610141c501c1c1e40d65088441026203030843e103010008407070000051807480d151081e81c61054002d02101d02d190b50319030720144003160f0a10003440800c81400000c6807603501303000030017a10709038400c1c0c540c0303e0416150500030f075250951260401030107144184a000207450034090041d100c1c0f08c140080d07604c0c86200e4001000001c030a1070050080441c08402d00d90004000c1040e10404e540350501c0e40ea0b242c01d01811a100c0c2c5001181d03800d0200f00030404c50420ba0003140c4c100e40a5018100918503012206103000520341c014916034025181001c0f00700300c000a850b0050400c0d083c00d100180d10401c81610140040b44020b21424010000c01c2311045c007507040e5095080740c000542d54480320050b072040900c038210700582c0503504100801d01045141d41c103544002d40a20401410020b245100411070f048c014080d54061181d01000141c00c0c0200018811740792058028641d01d007944 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 99131969 1250 99130719 99130727
    0x3100e070306031205090103113105010906141306091e050609011107090539030a09060b030a140106060302040302030c01030c020a0c0308030109050f040201021b011b05010c 76
    0x20045024980b60030700c10408901c00e0648000082120300d01507a5a542d03035401603005044120010030010070204075400340860042d1180d15400e04880e01c181034090180e42d000c040005030140900045034080304000c014091020280c3c401c0b9142e8282c1d0038210303404008881892140d2201c0c00007440403804100b0320b100824000d11840c0e8501081c0043c9003081c02241651052030841c50404c41101d0700401d0440d402d10081001d002c119070309006500701a40d10080c2c0b900c00401382044411701403801b03510024021803040b00d1074040d90403107084d551100c1e0514000c08a52000351030884c1c55041500c641d950a0151800c51803244007003c010a000d04030590840d15150000800c0c948100b20138000759400088000213540246000b0030b5960a1200c124144030700d010780204814085000071081050010245044e288403040400880e5901070f10060148025907010f8050b8002980081009005c184054000071041c1014490451407483c84c800c00ca09494060b01c0e00c0c1d40d03c184000585501c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 99133219 1250 99131969 99131971
    0x9020f091902120f0606031e0606040f0902070501060602030a021009060902030303040b040b0a0b01050f030c0405060a030902010e0402030411090603031e12090706020d05090307090608010516140405060c1203100e 93
    0x5c291003503801c1d40b81101c221401859201551a10707020b00800060325a034401040320b0280071519041c02403e5a070ba5007240280d040b03c40205c416500705503010458910000a6800006451780141700444e0100c86034001000500c0d410784805481d580381a01503281040198000c40c1706028444035440c00d8208940300c0308000c0c1603039019070f00b004041c1c58a60f910905558510802400c0b4681e25240d18140100500c9144c1c08180c0003280400c1504216801d640404071150003030301d0f840020318601c030070031049200858000300f0002d43c0c50801c1c1a1400c000c40e0140c0d1140014040368070342000003800c04400184941d00d01040d080020344203091040c0314402c290403180b0795004003180c6041a2000e034440c080c003083d8404011011546c084983c5e01004048010f10b030b8000c00f0080c01c0c0c0c83c0d07450580a85003c5a0285101840003075210314541b02c0e202c00030180105c02c10050030729042c01c00700400c0d5480004803141034440c07451909068110791000314000c0003103410800d00c0318a031507103018440c84 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 99134469 1250 99133219 99133231
    0x507050904080904050a0509150c28110d1209020414010906090b030a0f020112060312054906030206031e0703020a05190c0b070e03070909020f091902120f 68
    0x407c200602143c00f82c00101403005282c0301600a165a40b6162490502c4c0540804140110300240303c145042580044032252040b0321b54544805040c00500303641da074000e007148000050035019040c142088194040c80d600e0703100520214651170650ba242005078030a0b0480e0100f180d480078104a40304985c07107031a0301c40074250040c000e02c010b1901d548104014402020b410301000e440051044070302940404084c5601100b08d800c95000b083d4010955000705d060b09202c01550741da0390743c4140c1003554005880c140c142201007050b80180c188191a01074207410034007142c507000301100607580d090280d8030400441a10744040c1400f810340803002e80010703020009051042148281660f804011920712004010400b69142200f001c22255a200c8103005003200740054280841140c3c46840da02841004900700c46270f0715151030034141182c400da54000d500841e140d003000b0b1136040c18004c040d03000f2400000d2500310000f004902041c0c1c0d00548180c00d61404000c02c000e501c0c01c1200d8290f07007201e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 99135719 1250 99134469 99134471
    0x1e0e0c041b0810030609050604030801080a0c0303050c0f030408010b0301150e01031112010f0b0a0b0a02060f060103060b04240503092d01021b0d03020705070e040507050904080904050a 81
    0x11112101203100790895042060402050000090003900c4480000c802158408800c0045c4440c0c0e0800c1500c41c807060394101e0016100000001d60000009245070656401012403102da5166503026101c07640300340032160203070051b064030407450b10050010b8001048030700c001040000c000c40400d42119400000403401b04504203080c0682412488010305403039016544040b012034150000342622451001c8140f190700b85601c2401018098100d0700e80d0030f00c20358038210959221522091640110404c1c8001a8000000600b0468203400c403250010010704000464a03242c015008a44c0c1c8140c001c086800c0d6031070208000380180a0313040350120920700d030090030f5003000100d55454525112441c2c0000240343d0b41070b5000108142c5005200c0d101034021503845071108880d00d0300340c451901ca84424043e0361520403e150190080303542c010741c0a8080d01e40b01e4181100c0605540300a8000c2c0e800b803080d0307180480e4544690807160301590240c0e02c1c140d242c403158020881502c01c005c0813880a2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 99136969 1250 99135719 99135731
    0x60f030f120f020d0c020105070206030a1a010207060c060f06080a030206040507060504050d0f030e090a0b03010501080c0f010f02070306060608090c0102011a010e130504060207020312040f060509041e0e0c04 91
    0x46502055069400640d45000a2140c0880c00120348c94082c00c80003a42c401c0c800802d1044213100c90380410000315107480d0310f0000c083c0200042e038480710f0500c2488d0211b81c0b00e95109000a9082d40203109260804000007102c0f40c480c20041d20b40300030030030100c0160740f1840511050207000c0080e000148642d10b4200d103400c1c00c00c004160040f003581002441050010080c60406010301440b000f9004041c1120f0301c1494008091805000c0580095000e546840700100e080000440c0e801c8080748040d0980520303c6c050f10045841d02c0c0740e001c0240441c0034900c0c0101c0064840d0140e0001000540d540078468240220054108100ca2a22030f065a1612280300c24840088030446111502401c002c0042002a008150568101280b90940038a050100000c016082e4080c04d000d40c02501103c080108d00501c10700c8503c11400b56502100344800d0402c550ba1180300182032003600070b4004a030b0440c0342c0c0c2203d4000c40034a02844002c5441d41c520b0f125494040020144c020800c81e414809 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 99138219 1250 99136969 99136997
    0x150902010e010302070302101e291507050a050102032205060c0c03040b0409050403091710050a020c1005060f0102031309020706060807060c02010e060a080a0b04060f030f12 76
    0x18800d2201d464034181500899110305060081c004424040480d040074030030060b401e001f42c0c0b0b8500140e01c1d4820303030780e240c070b0b5055080036480e80c00c843c0c0031514624103040011104013003094404540a1420804108210100004030705014070340310385128000158582c1406030301d031041d817200c5203000c5c00349040204404000c60800100c0030703000012032100580c1d0b25489601c207401e6125940180350380740d10020703000a00c00615404a4460760003a9180c4040c1603c448081c003c1c001e01d5550316485074044600481c4414965100c0e9800c01c041c6540145000368001da624100980c0c030000925503966002002654102034521480d010000d1000e0b525181c2d242c201c25140c02071501840c0070041d40031510303e04001107640f114010307100e808111101c4c0c03036444d10000c20040415200b240050800e44000030b050410780d0a480c000c034a2034540c1c03200c96680302e0180009181d031401d5103a10680b1000d00145100700c44c407005020794050884a80852142d041c003841601c0c00c07101000c10002d21b800e40d942 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 99139469 1250 99138219 99138227
    0x7050d030305010801200d050a060f12060e0705030a06050a09140109020f0f0d0f0507080304030c08010f020702010804120c150b01081003030219050a08040b2208070b0f0f0301080a15090201 83
    0x41d01fa004030000034140e181d4542400c01006150007001d4008081d41c40030030384042070134044010a110700000e00200b101c41d0303800d40d00c80c8114401d2075050362200d0040b50000d4020340109500c000210400909210700d40c0352020200c150100781a8241d41d00d00a4205600b08565030110343e00381554010044840400461051640550b0140c0702c0a60b010320703203041003018050103000f0185901100c0c0c13155120f09041e001d00540e845454040e41c43c241c0b860146030307124001d4800b0960161100c0c0c80582e80d03030700e0f0900f600b414040c20323804224a000c03440000807490a2084940b014888000400c0c0040700000362038404098105443c948580d82c040002903400103072002007a0140c03a01100102103403500928110f00c0034001444200082804144500c0003406000c05240d0100b6060944684081c81c40d444100c0d4001c0c000c0b10b4119000512032210f01c4002000c14002d4204200d02e4000360410003c020b420a8100f4003540d0400c0c091003090004a043e01e80344607045e01401c00081a03980e00180c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 99140719 1250 99139469 99139477
    0x81b03010b18030d030506030706020c0303030106080c0d1406031e030a030c050f0c1501060f09051e0603040507031b060905090604020c0a03080106120608120c07050d03030501080120 80
    0x7401507480041c0b8002003400c02403071000c1c20007010f0115030401c50504409000b9180c202c41d200d0007449804400540b041c4000f501219114001c2d002d145141d0a1540494145030000c0850340164002c129030082148188242c0785e00940ba150610030740d051000805081000f4901110700c060075101526426000102c04c0311220500ca003000103543c44a010161518064043c1614180c02d000c10304151080c804541a400d142c03400c02141607980e210744069031712208c07100a03080001c032503843c20700160030030414400a054944141c0c0c00410500000110f040d4005c40f0111080c1d000382d8401c00411110400702110307035450f1a030184000d410804014010503c52040500ca100307544c02148654843e9411100c5c856a0380c0d06840c00c0040600b400740c00c284081c80b4680c000317802c2c10318507c03000700e041c8910015180c418010f0882f24401d01c4480100c1d030808181c0b005203016040001400b540d43d40b04a0150350b00c251030200715585003205c06403c6440e00c01e003019103142882e0780381a501c7c00060840b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 99141969 1250 99140719 99140729
    0x80f070909020118030c031514070c0c0b0f0c0f0f060a050604060e011203080f1308091305090a0c06170105010c0f020301050a0f060504060302030a0f140601060e01081b0301 76
    0x71032031041d000403103440c500030000402d500e942c540040148041d801600042d80d0260045910290030215200b044440c0c024041c00701c400c04401240406210b07400300c1c83d086000754414102d070380c0c41d0740e000c450301d5001e1507559007109400540b552400c13006001d81411701080402602d101144a10f2080d00d441c801070103a44501d66a000068103580c450740301d00d0240c454070750028655a100c81808500d1091120260045001c3e0780019a14120b1140700601ca40c00706c12403007110540d0b40e07031002c005070031440400754013500340c0b0031201103007070b10f8030802e4410b5000c1c06c010504114141000201e120b075076002141000800112400c40d8002482540e0440b14217203002d00000842c1d01300200310b440c014100035419405e041c140210052a500700c5440b500c03032110100301c0d26030794130208011180b40b44070081d015000706402101007040d40c0f0f9002c3d1a0790280750502e544000c945105400c20300240c200101095803040d0642d49540e01c0003a040d84040280303403d0007424800d50a2040c40d001c14428 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 99143219 1250 99141969 99141971
    0x109240810080a0f05010506040b064e010603060b12060613030813120b06040b01050408060f041502090109031b080102070b0105151801050a200105040507080f0709 72
    0x1165a1a6200701c040c40144505001d407043d402a13413420281c402410101512950300384070100d0010b01e098030850240d820300030402841e0150550b615040340c2300052000500801208181ca90018180c20703403200e640003e210f0050049074040044048181a00480101480c0c500700f4010002d0001c01c030ac01e02d405a0310a240c180e540c01000401a20900d02c4002142d035031a0300000400c1881006008a82011030131410b1140d100c0340004003604180c0c4010b400641c03e000400c1d03280c2816402096000e0041c0352092420b030300c5d0a00c1300c7c600601981c01c0400c070000a020030003401a81010704602e030300e0a00055103030808140009054510b0390001420320040c40e5035005407000011900720040040c40001e54445041d801c200035010300034440d2502424288512542c055056011524003001c0c00e54010007001038100112001d0b0071882440c001d004484040342c4440d11100030080c2da10348004008681803038140351460401d4015481010641d00035122042c0440003c90003609542403114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 99144469 1250 99143219 99143221
    0xd14030112080409020a110607020c01050d0209010309020a030f0524040b061912021005030106050706020c07090f0905010c081009020c01110304030c03030e1f0e07030203030c070501092408 83
    0x802c20042d1203603500a40546200080d00781604d50070800361000700f2040000e0b29403030f6540110503602c80007454141c90000c0ca0410040b0109002c40c2c2c003404012206142c001038940c8030354040b940722030b405d810a85860320840928030400c035040242680a520083c41c90145502e02a41000240d102500042c030f410341500c0055480d8980e0801444a60034005640320031a6865090b00940c2e0300325801607010b04002002000002e000c0c1c004c481c125542030f80d03903518002541c0c880c0d500039084140c401403917028a450001d06d130f1059006a04880220240000c2d002c000c038a01142140c180102d21402d00c07480e030341080104803451540da000c0350704a031350140e960b0012244c2c80340100050105541606400b000b070005266003c0080d800c0e070b921039101045082c0344681e020b40d07102c034107884248881007060952070828441c1e03003144000b61355000803a603c280e101c0c0d000a0550f04a100385140550180c00c0c108450b41e40030f8010401043c028500c8480e80028000d080150320b8254002010320011074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 99145719 1250 99144469 99144473
    0x50711011d041a120a11060307050403020301090803070e0906061b01020d0c0e031e03070204020d150902090a0609030b0402010c02031c0804030e0603091507020a0b1302030d14030112 80
    0x1c0d2050048500600030041076802e084103419a605803411079000d1400c0d909100c681040008001e540f25800400c45c4d03101222030003c110480c0d100030200c13000c0010600000006850074011840c0803842004210707200c1c9852040281b010304040f280a03c14102c5206020054030b0b40c100712a50741101c070810030306c0000c8400146001e0312aa42807085d019150000481040b607100140744d100c104100c3c155a0306030003626000154a9400c4444000740d0400c00c00c81c1c006151641c010450b101c40c1d485e0209010106101c0c50b0903107205903000307040c0960001a501c2041ca002c0425402030625403d246803110300f542c44102c50080010802410701c08103440c1e40c0c040d940d04214074001741c0704c0d201c580c085c440c6c1d09130320080668106039002c07070200c0c91420f481041890000103a9200f034a21100030b002c00040b0031896086c2d0f40700070300100b0540c02411348800100300300d030004038810412044009011459841450300c0c16441030300c69400c000342c502740341091880f1402224111420000d4908481101c0c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 99146969 1250 99145719 99145757
    0x30204020a050f071a07051e070c2402010c02030703080406200a0e0112060602030a081906030302070e010e0402210106090509010509070b0c100510120309090c05071101 74
    0x11642e01e8144540106000341000305c102c6222041c0071116039081d2445d00c544009507280c1c060301c0c400c00d10040100d88090700080704a0007900078640140ca0008031165070b03404004030f2580c6143d00c52180f00c0c1d44000700c085960240280c1030032259607c021407400165880081c0003002c00ba0009000070b0720350302c16a0720400d20226403c200a0b003102510b94901041c00c002e2300c1b000c00380000d180031410241070b0070342481a034424a001c9402c1c940285140400c1c1d0780307040703c11207030081100b2031080811008824007281880f850340034511980040100340c1c10300c1e5402002c02c2050b408840042036181c00c220050312001010b5000556580d07a01e240390204148036805085281c110f581464508820844082015007140b409505c012082c0c0d07044548604c1c1d510101e110702e945000b031070781c0f20920302d83e10310400b82c4c0310342c1d440000d9222105031f6a032a0b0000032650703540140140c000a261714024800d038400c5106000341c3c82502c0c101b56190001030754034040084042c519030350601c103e01c203403035600c0c480b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 99148219 1250 99146969 99146977
    0x1141b070308121b030c040312030e06150406080d021e0f03130e0601030e0309011d03121b070302010e010503040302030d0f20030907050909150a020409050a15030204020a05 76
    0x202c5840907440740f0320302c49800740c2a081159018841103a03100c5400c0f848102078112030046201002491500703003591150850b042e4480840c03003c160795081c0c00d442d005018480b050081d841010680004401d83c410442034500c980c00540c8582c10140d05841120b40000741002100c00c2c40060201941e9201c0030141060651107017914103002c0000d000da030910b05090188140d40d07004541d6461611210011000c803000c0015201c4a503100f041151100d42c000c0b8031400c20382c03146c2c51a008201100b040400c2c104440794404069400e030115081038211070845111201d544100c1c001c2c4401813564000030720041100030614180b050002c0810181807084c01242d5440c1c410384170030b02554400d2030f081c200900e141410000140001640b20800e0f0000034111380c0030707aa07000e00030103a06003010100b04890b4005880c1c102d8a1240b1500201c908108510042c420b86002c040180c42e589420118000da403170040880740420702c0c00305a045000011803032501070300e40580340141c452014a4007646c40303100b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 99149469 1250 99148219 99148223
    0x10c0309030515060109120b070530090d0807020303040b0a02090402070c03050d0201060f05150c061317030f04060c020705060c0102091c05060a09060f020c01150501141b0703 77
    0xb40c0790002e0512040c2400c032900950b002e071b0b1071440031a138070200260010b0354004020a4810a280400c4035503200710007900b034583c80104254640e50220746000c00b00c1c0f1b000d1020204400c090010081c1108003448101c000d6411401c080c403180c5070000009490317110081c002442000f1000200703940e030b5040d074181c8044900240085548030703100c0c18000705051280c03004403907900c1120300400e241803042c010742084409a42080591600300000c01a48d1100c01070f94110018086c0010820304204228a5004058104c00180c0f2880c0c00d0510200c1c3c0b21151f102c0c80e28078102001405000d100c014815a805600001d00003001c0c48071a80483c145056940400d03402000410700ca01604d506500912103054200e84110590a00d0900c402c0c1c420010318000c0e000d50030120016441c500d0a400440400d0b22840300041d08009503400c0c4002c903041601c40400d00e80d510300c5189605005c081c2c0000152009081c419800f604601002c42e2600c00d012080e42c40401d011580030303000c4400c21003000516 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 99150719 1250 99149469 99149473
    0x8180109170d06080304290f040f0306180305180a0302090109020c061003030507080f0906040b0d0f14011a1b011b03090c210203010504050c040c1d010c03090305 71
    0x2040c8641d10305041d0410742d406100946441000580003000108a030103d07001d010f07080c1081c0d10709550444003401c0c102250130a120082040110700110240240044c0000c840301030390007800c40c10802c2c00c42d50383c09141030030304401c9040c180100c1c1d000700c1035a0100410f40b110181c0400b41402103014aa001c3d4002504040004004034450780c0c0c0f41c014041900700c4500701c0e241942c6070340c440c203c101c41d00e10000d400300c3c00810085011824040061007105100000d061600c09200c0120701203030300c07035440940c18860102d0302c1414001e990007038100380c40b282c50040c090102e0080003d07107070500611445072100c40e40c020004003804101d0036910452444903040c0a04001100024080c0c00303c040054030b42c0c03a40e103c440f25558028440c0035541074014070b050007007a00301a4030b200d13202c1c4607010018880c03245841c0180141d4003406a02d100b24030510241c0000090704c02032000303035513039506200d06000c4200c90442a4030040a442180c1450074a001d071b0002c592402c0c00d0340e00e131003170350400f400c24 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 99151969 1250 99150719 99150743
    0x10c0305090d020601050d0b0903160521030609010915080604080c0d080708011802070210030c020c012a021807080105010806120316080409020a08040219050108180109 74
    0x554055011510841072102691600300707294404903100c4400340541684181000e43d44d07008102d03c0e940c0d182c1d002c8150750440c3e282184822211507010b8610604651030b92280c036222499150354192213040440039500b5609600b0000c000900b91041406a04103003603850001550700340f0341d0030800d0020540c0809032483d5007068200300c0c405a100e01004229485100032640300e5500c0703a520940b08402ca43e40d041c034641d08141c000c0c80103154124840d1000c540a001076000b5a4946003044d00e0800c075030320001100d001084c00a8142485c508a8030b042c801d5485205601d24a00c0c03040c031560061560340b03c182002d0a2002031010078102003030707090720b041308010080800d0700601c000f410303a20262510f19803561828204a02c9140314400c2c2d91003600207200f52002c50502008110709a48190445414a42c850000714200e80040b554900022207050034003003135051040c40030340014a283c600c50f424604180000c1d06505020340007403040380c8881d210740c40b4402c083d400a05850381c170004030165 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 99153219 1250 99151969 99151991
    0xf060b04120b01050105040513091b09200901020c010c230d120c09090515030d0f030e010608060c0a030b030607050307030c030903020c0f040f0f060f0b040b030c0d0e01 74
    0x107861110700741242c44102c8440042065030144003601e0407200010000c0700c00c2c0d204c2c0c1d204040640045c0300e00b01d030080710b002070703400008501401d2a005008071030700000342c0d409541c0c0180380c0a81c25501c02c1500020800031540241d0307011620300c84c180801e003000b0600301c2c440e160042d060a29008541d0500001d2030503211003240100d50802d0408166813501e40755400d480c200b0b0100d540c28410000031841113142044007088640101c4d6102486040300100a80b1180100c1e041c200390001d5000041c901666114101d60944100c02c01c03818100001c014450500400300d0703807514040c101130303045034012480c0c0215502c2034000c5d5040e91806000d480300b5007448140a07020b90002d6800c00d003c03c0c14600704144040c860322600e0390007501680209082c40e9444288007441e40c0c80040a600300b40c950019918032040d500580000c000c5040c000200c0c0e0b0720703000c14142030840c00e4000f441580c1080204004107038450040daa040001104101c0d626074188500c40b00400a6803041509542020702c0c00355 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 99154469 1250 99153219 99153239
    0x506030c0c160e010e0405030c0604060b04060e010b0a0e0307120507050a0509040b07200106030f14030f04061b0209040605010303140c030d020c0a142407050703030f060b04 76
    0x256007201c050484100c009042c400d030382404028001c6110300003983c001080307a41d40c0f240c3c103560801e001d002076030328107803412100c2c6040050486040d603045407183c9030000c1c0c50929100c4d8000421403505000c66950410703604489a01c00c480b410380400c80020400c0f11715940c00d11003032004140581ca22030040c985441c080b912442203204d180e2207108018800220307810540c400341d1003540e1005000d2001c2e52181c03810360302100d0a010032031078442806210303950030301c091140300042d501501d0702580943d418544204090281c81c400704598009000d41050702c450b840c05d44080e0382142c00c0220400b40709000050b01030a2951010f50b201c8000404d10082c8813031903004606a900a0741e4064424401c1f9140b181c0ba4851420780c1003065004000080d0702d030000303602800c10110b400707094403c0e17a101510340045000c4104029500c0c2d80000903140c90138160300141800d451840002c020041c50440c1000d0101c0c000d0a1003d024551907811040610840b54824806440c0c1c1c282c4032502c03039480b000251 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 99155719 1250 99154469 99154477
    0xe030c010c1407020102100e01020918010801050108030c06040303090f02040207030e0118270609021902060708070c12031410030c05031227180f06010f0e010f090506030c 75
    0x2501181d8030103454030b068a5004103d8500c90f40680003011590000d0f0081c00c024407c1d020b403004036541c01d21510040d80c2d03e1900d05211400c0f030040f121915414080c1c1c25007101c00680c042d00840c0d1042000020340c00005c9449035010b07406d818005a100c600d420888071140e4001002580948005034040406400030000d10312040c2c01c1c4da0301900c151950035154840c4d201c9029668103c040b00e101c40b05030044034402d52403a843c03034481c0441e0380303651080010144e13004244420003190801044120031541001242ea21196500d01240300c1d0510420203404080c041c0800f03011071400c00d115042c118001e41018603c460588401d40c4d4a01c0e09042d141d940ca03186000489540001d42070000c1d40e85400286850a800582c1c01145040c2201034090b4219480c4c003080c244a9000512000341c0340d6942c0592519001001d803010b02c2880c140181c3c000e108002800241440011040c0819069000b043d000d110942800c10070000e072078456041d180891749500040d4081030000c01c02c030019413410050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 99156969 1250 99155719 99155741
    0x7080304062901051911070f18060f050409050c0a03140d0504031208060109091103070306090c02060f072304150906080c0708090316030c05010e1e03010e030c01 71
    0x7608240d841c000300e20100580392403042d030016005100d800321103000c0c060310031845641401d10460051300303071004e14103250f080d034001c444a845038401005145c141101e03c05622070700c4c80c803c00500b4104246080c0e4200c050290900440c0d8444a020030448104000701e11010000c00300c00c01d8a42c0c03403500c05034601c401848003403240035031080e4117201406801950152540303c0c04100151300b80700b50888030580002d00c96810060361100c001145007541c0725503107681003155102030b03a038a0402e402809540d09640505c00c0c0c5031610b000d0000c0c440d40030540a400c91141c03903070024551900d00086441040c4103450048803045c00005500c1c2000c964020000c8440b42031080112030600741050b02c2c15521842440041511080040c0209040c4c90041000510031952682441440804a443c1103c200d44080c200c0d00031420900600803100540401001c00b480c09250040400c0f0109000d00351403404400400ba242c500782c0290341c0d00b908120106071003201100c2d160480c0304803040c0030304445090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 99158219 1250 99156969 99157001
    0x70c050406050d150c0504050a090b0405060609030a11062109011109090106120f0e010e010e030406020d030506030307121e0906050406050c150901092d02150708030406 74
    0x56a081c100e503c0619240c10054164580c3c6180d4041c1024181061848040000420000c01c1e1590f4802140016125844000075074034286014841266405046140f16003800d10515481e0342d000078040a106502c03180c0d100401da8407001003081800b808021060704601050b41b08000c420015059100340e40c600020f000862500c10780a00f07600c6264185030304482c0c00801845418080c05c110182240c0292000640d9030404200e6000c481d100a0f1444107a515401d450740040d0090280d82c01514101024515180ca4103401030741d9000301001070001d041d291000645160303001d0050310b040c582c0110b0401f0ac0f003031070703200001e003c15802c06400c04060041c45403101042d1040d5014403d9840c9034913880e00d858104601601c0f290000308600c0303402e00c224040b40340754241e0141560f000e600504004260940c01c0d18003000083e03601c80000500f1400c85078203040964041100000654042d0350502d0a983c1502621449200b0004041d280d40710000074882003002c0c50b80500c8a031011035003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 99159469 1250 99158219 99158231
    0xf110a051201051c02090405100204090c110138060a02011e02040308070605250f0908030903030403110a0306061805151e030a051c02010507020303090a0f020114070c0504 75
    0x20401413040d440c1c400319580010903140707200050900150003504540104c0840d10030303546205d00c004c00d0703a01a0700440c400640310b9a80790300701900214814003503074600f002440012403510060303800b000244008141d065000841244c003015091040d0043c0b4006002d0035620304d20f10b03001070b02030315459141640030544814210102915403094400352548121024903042c100d4a549016000c0034085203403451100c440c810000003150000d05201079103848200030315018683c090010303d220780c8482c0d52500200105503e5a5002c4200e8050340c1d070020001c0c100b20311800110b5892502508000c00f42403401c04046150301061000c842c0c0c600741d0801c2401140c0d01c0c0d07004c0c2d84120400c58035007500918400541c4e50000758205150320750b110064101d8150351103584070b20f03103060b0466030141010178042c0b46030301b140e541c2800342d42d40c0060380d80000d62460a100441d03036540c0e0f541c240058001d03400c61480034116032080f900c01c619040e100700c589444040500384000c80118900c40c01e071107189005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 99160719 1250 99159469 99159479
    0x110f0414070906050a050a230a09060e03010b090c0706060803030901020702040f0e03030604050901150303080618040f080703032009030f06010501050403060510120c080f0703080d0f110a051201 85
    0x13804a880718a0f07141d44560511908a50035680395001d641e43c01c000c101580c09000f02140c0050161000254035510780c44401d103400c002400e0354401c1d01041c2d0180e410700316580d0740358aa950b10740341c00080c103141c0c09548e1121410310100820154100614500000041c00654041500071b001ea040c02242d0030421400c0040c00e840403990342402964003038009000080c840d10342688240d5014507141d002044020403844a507003689404e401c220080344806090004504040801c0207100c9494800600a4141038507084c0c9041c10b4080c006211a00000d40d01c0d04051107904902402c0c0a9075101e0341c280f003900e060348a055005003107220b000f4851802400d04941000642034101c2d181a151030341f9050440c2c642401900004115584e060007212000904080c00250716a0490142d00615482401e042055051020714040f20b01c2c550701040c010303c00309005400310344454221040020f12100350314001e00281403011a800c0300c580c40841c10b0407a0941280080601c0c01a001180381260380711 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 99161969 1250 99160719 99160727
    0x702060603030a080705130312090e010b0a020712111503010302010f18210f0b06032b0e01030912050301060909050c09040b061b010b0405060d03020a110f0414070906 73
    0x518603510004e413903803010031400c0740520000c0c545140b818950603c4130744c99807a00f11402040c200c2500019103000d0041109e80440d07120b0300c1c050f00c500b410a51a083c42d20340000d603248054050590600c03640c409002c10407082103d0f4800c5414094031806441481c0301800d84950024441a400700d50406130718040180f0a00c003407503d007000508012005070030407605101aa1a001007080703108010a04100440c2400e04003034001441a0140c035002d14000c024503050005215a0220183d880d02e09003400180c800c4c0017148152070b43c501309914024240040b07020304691680500b4444602601040255014000314180c90382038a401920640e24021001151401c91724110b1042d0144440721461405401c034205654000b0801c0b42403034002c540c92032017510030404030f8095a560700e800307003420309190080b135606c000121103174110881e054402035240c400c01103004010074404003400100390f441c01e00090385c51401400810403821803058000001c1815101d600201c1c62042c030004809100d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 99163219 1250 99161969 99161977
    0x507081803281101050c0d140f0402151b1e0c0102061801020418060e0c07020d0b041509030c060b03060402030a030516170702180603030f0708120f070206060303 71
    0x7008511404404500c6160b0845040301c60907a08110740030450720340e0030b102402032070f0144041c0c903031040e603894801074440c04466041200c170310f81c4004901000140840009001c0c1d01039015901c006000e103280008a1040c40703980d45100300c64000e580142d12410002440c0b0700311180d020036119025805078421556001100309250041c0c0c86240010f00c440c1d148036210b000110041e00240c10a07454170000324003045a8042140c3c455602c110400100312020041604880c040c41031624240154020034805001d040307010b800114060081402c02900029000c1c155062940070010201e0a140041c0050542c03134041e40c0d0316040440c0304110303207000700c1c2c2540074a9004004203901c02c4140d400344c0d41c0b500501030740303d1204411a900008601460300844245440705100d41c0d5640d01841007003081e0000f846c40c1080f45640c48100702e1280c50000481c0c0740b41444001d90f43c3c071603103189840c088a1151584100d45000c02c0750a2101c1035480301d0801d03000704402e40070364085507582c0c400c0c140d590007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 99164469 1250 99163219 99163237
    0x20706050a050909090c1206130201050d14250314060103020c07181d120a0f03180606080d090510050d0228080703090b010621050f0a11040503060606130305010507081803 75
    0xc0c03c27204c40c4c010b6020381d0080110320350003c80070800c010305c411040b1b40c8900031201c41d5240300503000c400040052000c0c007030303c503a41c240c11300b0071090f811506540781402e40200b14506150303000415560290080005100500341603151125030b45045d060800a009882c0d0864215089200760305285100410382c0300c00c6030845d04040741045001c0e0011102d01030800304600134140d80c0c5004410300000f070741942c43c0090184001145407890300395864904064100030780100210201d0a00140d0748000ca802c036402e155140084c0c032031242c004510000c0c0709282000c003130140511450720040010b08100f070301d40c0e10240c68122056403100300a9007519607991008112441040050100c203000e4420015113054030305032654080c0000030f100003190400e44461121200150800010030710900895103544591443d040c02d06207048003013a174548026042c60321542c008200c03004106251a0144001c6030094000c0c011410304a5002c0c1210009403081740c8444c414141401c03081c00c0000484990174 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 99165719 1250 99164469 99164491
    0x30d080c0a0e0a0305030c0c0909010c2708060a0b010e060708090409080903010c0201060e1503060118021e041a04030b04021e03010609050f090607020706050a050909090c1206 77
    0x8071280e41c212400c0d0907189076181d0042e003015021020400403c09403040ca007004006000c42c1d1300100c20032442190040082c040c0380e051041c0c0c14045907005004094424034468101d12000e800641e01c00010002d8200508070f1081c0c030100712008280f50080c150340c05080c3c81c1c00d2000107500051014a00c61000c002d0b12036401040489543d0609501034900980540721060901a4050011f429140318034050b50041c0c2d1586014803442885565080e081485511442c0807400890f000c00c0d00c80f981407142e40403001445030f95110126541d012901d400c10495030203c1c070501e0600000c0d1254100707000c0c1c081e0071300c0c0a002041c45100500221801e4940206240d00d05a6907a4200b2054070501c803248185005c01040b4046243c809019410203400c01590202d203600c0e095480b40200c0a0090040d51154481c0c400d02140640200e03030340095030b40740c1ca052595404209804d503044c1c4103202c2180c0e003100c61501000718192012890040040040700d01c1e118007101400000d5031000199044070b020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 99166969 1250 99165719 99165727
    0x204110307080c09010302070c06110f0c130905010b0303070b0f2d04020d0c0b0d0f02070f12090b03010f14030106030827100203070213020711010f030e1b030d080c 72
    0x3c01102030a0f240c1d0051401510f0700520f999007125401d01c0e944030354041400701e5503070a0700b14820300c00200710958000081c0000c0301c00d407000907107411880c001198465607500149080c09420b42108603c110040c040300d941d4405032802c02e905403800c40340725110000c64804102030790301200400441c103070784640307000b1701e00301020f8041840140038200303c2e84041e8136030340d150029200d6805d1200070600c0208503906e0326401007814098508050740b003c0c8a500c100151030004100c1c06400d07070103036005185400b00d8000c111080d640c400039030300903c00b07002c6d01000010b088096900c08505545402e01c900c40d050700b4601c01c0c1401d076405800001c1c00b5840501468041d40f01a44100301e02281d030902d0103003004d6070300c800700d43c0c810542c010040041c1c00c001080020340c01d0803100300d01020000c020862a0085648490946845070354505042025407101451300301c1c4290000400c07400300100343c2c1d060010054410000c081e030354400030b0007070203a0200c0c1000c4030700444000e03110704040e841c07151070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 99168219 1250 99166969 99166981
    0x10c020a0b0c130609050f04023c030f100602030a0210021c020d060302011710060309110612010e130515060301020f04090f1a030309010f09080d020a020411030708 72
    0x1d460042c100e0001c0d000038030088190000c0c52088400a02e100c0e01c80c1d40805007031005001c08981d540803014002c50040184d40307a14201e014103004195035207000444242d1406042019402a441c0c080c9010000401488503810508801c240121503020005107043c1d5624002c4c0d0b107a000b0504240c0c05604074030440e500320b04054004203482450580e60001c0d0100103007108080341c200013404428143e80d01414021940c121644042070300ca0503d041a0600c0c0883c044c080741c0c00240500e408047e02c0da0002c104001002c8a016208400104402d4490540c0b07400280e8180e801d109100252000c0004604401160001002c0e074a03005000362106030501001c048441e10050412138056608000260f03041000c00054005031100200110790f000c6049007410640e044091030b0610f50741c0b100502019540c0002c1100d030780c42401e08043d05000d03043c030020340304a1040d60150721607000d071024038032029901007850074100c6d01c02c8400308403006a070740b80c00302e590204441c6280810a00408219 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 99169469 1250 99168219 99168233
    0x4051323010e0f0a120915050f090a030b0402010206070503100504110d0c090603061a0403030e0114030702030405150c15181009060b04110f0c0304080d051209010c020a 74
    0x40d08001000001c03a081401030101403428032601ca11211541116010408210184100c07002810301c5217050081d40d4100010203161844070015107051020010b4025a071041031710540761140e40060409208ca5503d0178102020b4500301c070224014050710000a050340d02410a4900800e0030542800d02c0500744424000100510380d0031002c00ca2080c0411240516640158030804500f5518980300038a07009002e0181e030016041a013001030090304910349041558241c40413a0380614150601c1210f8600603180b590204c2d044c80f80041d000000c01184c190000000d208403502900c0c00c00b0070500300b0052011900524205070302d15040000070701c5104c0c00000c03140307402c026564030b5242c0200500c41da85d860141c501c0c1c00c140c0456291100c220500c4014170610325220010380d01401b0b032056001901503036104030b04001c00c1000020910030170030b201c100103580140652008407004034400c610050442d401c1030304901c4d001e12844c0000b5440d0300060281643c4803c040e00142541e4040f966824 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 99170719 1250 99169469 99169523
    0x905010834021906020a02240f06040207020d0804050307090608100207140a03080403090506030f1b0405091003020a0512030901141225020c030c100207030b040809040513 75
    0x7008610948803011481e80440460019183c8203520040c0da903103140d0340190030300d0083e01c52030780c1c201450040099250003507803203140d10203800501c0c4025641c0c1da0001030700174042c4140c040d4101c01c11254000811028200500603180d048003111030342c07980c03900d50800396000c2d809100796a4000c00502450184280c01074034220b44141c144400090b50308580f82d280c103904110580004281d9001d1200341900000c1c030802609043c0c410514601d812540c031103201c900609540d00500e00e4807040314140d0000010b03030307018240040200405081110074080d203403c1c240800ea2049140038000607080c90101c6e003400c18011903101850410550000540b000314648030f010182c0b6004120212040729100d4455200d0103010401d80d0340c3c142e01107042c20f01c040e607140c4080706550040004040c0740c2da00180718002080102c030041400c1401d070104906100301540000e00340d00c20f55082c4400c024852018005180d801c1d58200944d6a42d030120340390103004200068010040b1100b6040c4100d004c6800c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 99171969 1250 99170719 99170821
    0x130f02061608070605040c15021b01051603031d010c020706080c0d020408030304120912080c0114090d020c041e0e07080f01020d0b271b04030309050108 67
    0x1074002550380d80b1001c15551191100300d49640e43c40381004108000300e9212405040141d4010416448081c8080d580700d5854a541a40001c8401900f90b01d0384114221800e10301141d884059012152901501624000c03510160808008010010204051003034107115001e40e4000c00c1c4007460400d098541c050090104d1420346420412403281840d5400100010b20f2010000c0d980c910b0a03040090081401110b04410055805802c0010360070200b0081c140325041030806558000124460b0f0060004111080d00c13100a10308110035540d0100d41c0e4009e0382c141c0d80a894500f01804100400c50f110015010f0b01151441c102d1030741c0700039a0784075803110f11901084501c0281c8854205240105a05480c0182e030740018525020304006d01410015040c06d64100c84101003914102c4003183c5801e450074003151100c1c0008240303e00103100303602d41c0c0100040466845032681070040550b0b4550244a000c10040c0d00030a11111400f0300d4000104844c2c449084006888014640054800104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 99173219 1250 99171969 99171997
    0x30106110118030c03021e03030c16140c03070603060602070603050618091e12070303050c120408070b1f050112020c0601090207020901080715050a03090f05060906130f0206 76
    0xa00d81420300400c02d0703090039406a191401d40418038500203184c1081c01030f0810701074480d5000406043c5000003540c0d00301411403035140e21a16440705800742450100030281404460030307004540044041580760b01a071003681580d003010745403802541135810500c0707014016070000d43c00b00710541c82603106607046203005280481100242008503070360303d800d840d00c0c3c0690b00648070300d00040c5040000140c0070307010724001d440f031403007405080042d5000d058009002d058440001417815907640084440c00e100704a84c1512038101410b2019079900520003c0700c4241850011912500c9809908000c605c2d80089400001742000700440341d001700c8000155485800780910011600140030b060f018012680c070043e100c1c80c841c0100111f8030b030180e00003441500718003024070001c550320b5081b4a000d070290800c1c0e030792480c0a910450080483c813101070011080320b800401003200120722980140c50500c104c1d01c1c6da443d480350080c00110320300f0005100e80d2403a010304005050ac0c0340079101c410101c0c11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 99174469 1250 99173219 99173231
    0xb120f130303180f11120f12130302091501030506040905190204061502011a040203090706031509050c070201030c03050112020d06020d0e0a0303051e01090905070312030e1209060301061101 83
    0x910789004c0a85842c0c1104c3e0148101d00131000f50400d18903036442110000010000202e03061820758803580741c004481c0b121040041c603130b1304203002060480001c5501404407c11450001120381007164950385440c0002c2c20240444e0480c80c0901548440d0f940000161010f04505084c0d80c00e44081070004a8001d030704c40d2000151308804518410508000da000442c1c020900b038075041e03286019031086880b0307520600c2808041d040001d0754100740c07031060800090350074031102c142c018005a64091200f0f54100010041452142070103070014510030f80f401d00c00301030643c10540680e00240285848084c0520a10340946403a50844240c1c60185400500d024002d58400054407144400009030360321000802040650500c0380325070142072244203049961050783c1403020701ea018803e014006480b0725000741403100501000e0020341d03200b9080700e401c010401000d03001d032080f0403100100e4000d80004050034100719084808424004100b0340c5142e003401026111882821a06951503580d10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 99175719 1250 99174469 99174473
    0x5071a090a02061b0c04140c07050a0f06060303030e070303050307051602090f1911030a022b150512060601050307020a05030304030903140d09030204050702010b0a0b120f13030318 79
    0x40000c02010440400207004c0d0b084066025180101ca2070105000300d2801c0d00203001180c1c4e506050f50000f80d040405035a030800c6040551401c81d848001810310540e140000081221561040301224405c1e1024084024515407194807007105101c050040b4008200203100c46100f800203149460f07040400004205c200d170041100750030101c90883c6100441024040d03410501070811603280c600200c140b01034200aa82c0506d00e000240400d01300c0c0380c010580309000305c003150700710804121441410141c02501c203600d0026100c4101ca4128110031081c01007460300704400392030303c0d030b507808401002141c80d00c40045800f94001801d090460041c030a0001c0054000d000440c003c90107940c4032117006d4210700b4401c00e07203030704601c3c00c030000d521424a81c0d80041c1c0090210b002c070b03501285d00041c03550fa0f0a20a9015000a55010781d115448110104008003214007400d240480a0052160756844810050156000380c584c3d85240d803069581d60b002034840d40060422541119180030b0484041d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 99176969 1250 99175719 99175729
    0x60403080f0a0e0a031a07030e01020a0801090f02090306040b0a0204050904120207060809100504140727140f040503040302040f020307080619030b0a02040b0c060a05060105071a090a02 81
    0x410521070250000d411404070b5885140920b81000444062240310b1079999901c5c603002c01e8100c040003000340c4000280400d406031307111046e02c6120000965903004d1202d0000c1500c90b00740606840d03107107081001c2c61854094800c2e07454910000d0000d0030540c46030b0325101404c080c02015017031400e40800004c500d5483d150200b030700591080c404178100d130785141c001900301070f0320307400400400c400d200401140e40340004842e80c608010302c0d400119a104c5041c001000e047c089802501480340580018031019580c0b09101c201c5580c2007800c1d5910030381110071007940c6d81c0d00881380c0911525400f007402c4414503c0d2464205100300100c0b40703441e5499000c00e081c0c480f403401030184280c0c0802007040c941d4200200546c068001c44900c80302803180320501603080840d020141a0030200b4000481e49140d580c11134000d000360b1003c3c1910f50b1001d41a6035030f01c4130125107059800703081c203000c940194001c40680d00002e600c014204081410a2a002d5080754000c00503080c9104925808001d6160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 99178219 1250 99176969 99176977
    0x30d09140a05150109020f07030c050708010e0709050c03060307180902130506030f01050702060a0906060302060c031306090302130c020a0b01080313060c0f02040504020109080f0c0901060c0201120b06040308 91
    0x10070000303024840c91002807495505416440b2685e02401007100310f04d4001900c0480d840d00f50f241c10080e02005c000d0400b680f0305000c81e04140e4a540c030300005071286400015841c400c03039081007024001a078440001d003181e400180ea4607505580100f1041c8002d0482452307a114035610500000346a000c1c540008919810384074070301c00d1082e80e41013030040c5803c05002c02e22500a5030b900900035030401420007569050002d2021031a80c2d03480c01010100b01742500080011500241040d495145d0002c4040d03c0f580034100040c0600341140000900d01d01035034503e0304a139001491554448047c0c441c0002600003026680214080c46184000191400f140e09001e4001e0700e0095840c0d01026031800540a801d40203030302489001c99440000403e070170b21101d9466070541e00420f0719100c03840107840340c07880ca403c113840c9130090007441110780c2c000081c10124080d0403601c20460740d0307031040251103c00c1c43c800080d0000781352003c00f05804001c1d0700b10030b00042000c2e00c41460180d40307803200401500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 99179469 1250 99178219 99178223
    0x1305010f090606080615030a090501061517130210090506070c0801110f0702040902060c060405030c0d08070512100f081f020c15070201180308040b0a0608030d09140a 73
    0x615418820303403806102c1d4102406813802e0085907410305074000340c0c200c3d0042c0c0e401281c54034000005003442440c0d801c400d411a9100e8006d11200317031034900d008606040812100c000681c0c0000c80c108500c601388000703008840d20901036049403015020320081007046004441404051200051280c03110002040d400780500c03d05044242400345807820f4440c440b0900c507503100305006680424804004513580d55a04a03000174a021403440851924011050f0080090040307000b044244140440208a0242c0400980300c0c0e0b4980d00c441030b6184d10082d248500041c5090041d0501d0f00e00d050f4455070410802140b5a860659501c688144c184090b000701242c0c0c0c11400345034a802c80c8810365001d03540c00f80402503040244000c215952000d1700c80d00c00b000303600c1100105d01100e0003035001200c035500c403000550b0040c0b55070a02400c2800e080c1c031704803081c2a1120018034544002d1084105555a90000e10720344048900c0002c06498824001e491421b45801e5030b507650748040100e001c2581c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 99180719 1250 99179469 99179489
    0xd05060609010602010e030d0e0c09190c0512040204090c08100f0f0b03150c0403021512090115120201050c060405011407050a0918020702031e01110403051209130501 73
    0x200d021424881c0d0900c0680c40401560b0410409111800002c01518890840098000f4001c1032a050312890442e994800c00d4001203000d061110701054440401c1d0801042072052120b80581c444c00c9800307120f404803c101b040c02c104082001031506030170051115004030880078001351104c2e09075041c12421040350030130381e9403058400d9520005002c1e1600342d02c50100c0401007d5602c0002c6a1100100c00e05180c510380700100043c0410404400c0e1409160050211b40701000402c42444844e40811110f198009003400068550401402802c150007207024400410f207103020f00b04500d144054004178180142800030207900e540401140d03208502410003c01c080c54022100d020a241c0a4a0a001c11030204050014036030002540402c9410b5000c054014070300c50300c0000001c0c040c22200a40c14050000000042c00c0c03400c100354a804800002000a8020f00f06942410721540c0b100034510303000600b40032071000c0000060004402d019215440d5828018401e408841007600114951 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 99181969 1250 99180719 99180721
    0x30507020c011107030204050c0d020a052713021303062307020d080106050a0e2d190909031e020f07060908030306090a1d07090509010506060a0c03030b0d0506 70
    0x8a941041140349020081c2031640d2902000c0c9103403600d8190500003e0f01585e115008503000c06000c0c81150b18620f9800000c5445040c01080108968440c0c5485020088d16403807480003c8040c6640c8802040014048000c914441800c0c03401f94001c000250803038401c0781d40001c04143e0314003c01d0300f08000c1c84070903588046265400c0900d0200034249004560141920ac400c03141c00414140c150b6402c0e00b4403a0b01c602c0081c00c00c403254045009565005500340c600207403480440b004017042c500303d862000d548440d100d824010080c4183d80f41303440f504180c010030040c049095100500c0e0741d0203417402c480601005002640030541d4078040e240164400c3c6c0c01c4901c41d40c4180003007030140045103042d1400714500003ca60782c074000546858032844401c404651510b049500158141c0c199a904c0d903080300f01c00ca0647d488050303c0c40b0303407a4558108030000361103207018072550b482044000c28050600c03034900c45c125681c40030060210181541ea40301c3c92004d90f1540100b40352644284020003003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 99183219 1250 99181969 99181981
    0x70306020d1a13050a060b1207080f16030506040914070f05040b130518010e010218030a03080121051911030106030c120203030d0203070207170c0d03200d0305 70
    0x444026001040b10848150410141c954030b900742030701240003040c0042400e440e81080703070b00140029403140e03828441c00200007500760388005110384110010744840c0c031503564007400145408021580c1c911041c0300d410f02c0940c0d80c0d011f9400395030404405040040c03081120b98800d49101c800c03010340c64195019030010005411041c8000d009841c0c141ca0510580d2505000314040c02c020010040f122500c03840020303992404440d0121007241c901000303014030003010582500070750002c500c080c804c040900c1d01070000d040025840c0c0c680c0d03506a075201c4a5030710f040c080100503242d07084402814564006103a021620400400b03407043d0203000d10031001e82c002c2c07900c1500d141c00d40040300d0299040c49801c1000ca1030070661707802281c000081c1844100e00a00c0001d0840c820244681c0c48030348003100f4082e40c158001030000c01e581d200c0c10307041e10782155580030944c0c400c4007121031944500c5031880200003a220343c00c0d00800080701c16031151b144641446c0c140c01c166495800308002580d550070444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 99184469 1250 99183219 99183221
    0x6071116060903151e0509101e0c020705090c0a02120c010f060501080f04031101020f12040c12110f041118040f060b070f0201020f16060201061d1314070306020d 71
    0x5420549001700586146032034a801e4400e2858040303c58207039100000344a45000303000034900260aa50702308010607414240c0c1a5810120030100420b6103000c0d020300c1d41900000d00b407801d40c0c1c001091700b6103664a10029090341d43c40902101c0460045203071000180d04544080c08046900070700110300740c04140c9a1908507521540f065040119040030303c0800b00d0440c000300d030095050314001c4c5041c02c0300e6107100d001e0301c541c01c0b03110740340a0b0000c5e640803121a4052014000c40c400d581c150030700395580e804006085032560010b0226a1101241101c61402c4003191010740c9000c0c1001c5108000c0e031030740a0598204480d401442d10700e80c00c40e51950b1030544111000758041030030130001b0505140504280b8001c00e10700510500304a41400107681c02000b0006115038040116654501c0041401460b88160710030b48025608091000c14000d448400c440d4140d0520340540f05140d81ea040c41c4200301c2c00c0b681d029900f1110320516000000f10500400300610b00544c0b0160303071020400e010384 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 99185719 1250 99184469 99184493
    0x5101a070510020403020609010e0105040f120b1302030304090c0e090702030c06010605161e0b10180902011b0f08040603230403050313170415030c02010501060206071116060903 78
    0x80400b0344100030a100580d01c210030b907650403c007032816004c2c030070031900103a41a12582c1c026074420310402c0030008a84140310443e04800d4810702100300310782c031080b82504006203c2d100095064109000c203008007036180d80010801081c6140c1803d86d58071100220720200d000b80c804c100140c2001070700b0755144204000700d500600c02440c00c549400b4641d0070030514406048001852a02d176600744000ea0703012240041c0e94250050b03803542c00c50504902c42070100001b8450f800c14031513001c1c1c0d600040d00b41c40c82a910340d00e8040c0c44e9040500980182410544000c0c48120350800b0000c0102c00800d5148011380040c02c0305440000d08800302c41040700d06c0e5200c195590340e001818000b0031000036400010340750400c4640d16404d072141854505904013840340b42c1c0001c01a4000b16002882c02e55100400070118070359282048580046d90089090340e0090140c0c5000d6400a008038003254422014072079400d14107403d5810703d0844020b00680c004166001c0400229a1740062090000040c03807a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 99186969 1250 99185719 99185743
    0x12090e0f07020c09190f0603172706040302210a030f110318120f0109030c020109050f0907050c0c030a050304030201140c251e0e090c090a05101a0705 66
    0x2402c0c080ca44465440c8850403140fa400703d0309a00c1d04010320406d40c0780d4102c94050342d8000e16049070b01e040300e2294081900501204007413000c0d80c0e45a200020f030b4030810024901c1026100303628041c1540c09001403a08003200103520703085e8480c240c010890040c084044c4003813103070f81c90400040e0104402042c10410302da04040f66041001480c2d803a100031081e09850000641d040341110121130803072420701c4101301c0070003195428104404101036002c0c000b050000d200362076950040c4c0c0c0724418029080c0364a1803c642003501f5002040d4098012400f4000400e600d100f1203440f80e4030540828200f40c82403400b04c50a500c045000d02c00c40d07070404400200300d41292001030030145504c406568400e1070490300501503124034100283e414030308480070040c10021508140341e108008a10700f0004442c0b09844c003681c1c03030b40c0c089050b01002140d88100c0b481c00900f400d0380e0b600c418801038010600900340030381d40c0081d01e0000500c00c41d001100c01c1071614480070162180705504002e07003448100341403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 99188219 1250 99186969 99186979
    0xc0306080f03091e10050c0601150e0904140f0a021c050a080d020f030106110f01020306010905010e0a0806040b07030501050307030c120312021309060806010605030412090e0f07020c 80
    0x1100745890000003d42e031548404a402d0074540000400c10380644030f41e4105681c01840503206500040d030080003c0c84020b40c410121082e90380d90301500341600980c40300ca0340c00642c040c8070360f01d950302d8260b0174070760400d000d0218103481e00910680e0504e0705452070380034502e07904070304504825845d207906a01c00340c8803424911501090319585031901d5013101e0b403004298502c0444c03d00c44550302541550b2040c60801000b55407540c407984089c0000d8828080039030244124026182c2945040c002e5134001e01c0180c54011009050400641d0040c0c01250080c0e0001942440043c585c0000c020300c900803402002080030605001000809a80381604968000d038010b200c2000000c000d17a894108071752243c1d00d042d20784049032a00711545090744403200c01c4980045503480400540003c4031007102c01d018801c2101c0c0f66a0488581c0303d400034852880890030910001c0c004c1680c001e200011000307036140c101c0345603480b50780c0c5039111502580d4020003058018108a052601044610464482101c0e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 99189469 1250 99188219 99188233
    0x5010813050d08090c04090f050d020d0503060609040905030a0c14010506100522060e0a17070303230d020301090e06131b0e04050f0705010801080714061b010c030608 73
    0x101c480e924450041164108501d220000311100d80902070850070100c0100288642086401c02280160442038240d955001d6000e100810a000013490f003200c2003507807209400d5541c1c400402545400c0a090340c1d400985440748030001035000d0005000714400b680f107600103040d90b82014403200c861000754804582c50042072010f40d6480d0300c44c1e24840490f52410b1a039a504c00110001c9030b4641c9816130f0310300b429446000c2007403908154101e56015086d51880560342d900d0350320300d25514140f0300c803040780d4101d40320034400f1030321035000f03420b00118420014503031403003c3c525000385502c0101c00391000760740031005224540140c010601e40c0b03c0804024046070510144005100c9111107004003070716000c00500c1d85120b18001000c0c000c080c00c09082c0064030b01824659241d08407111070101602942501040e190302030f01c17079613050703800c1032000300a6039041401181d07650500c0c400c00f0307a00c100244480411030601c0344803191007641000c008101c08036448030240c155451904028402c0e00000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 99190719 1250 99189469 99189473
    0x30c01060f180c03020f1902010e03091c020d05070608040303060f03030f0e03100e06060f0d0519080d06090218060a12180210020604050f0a0f03112505010813 70
    0x500b1251015140000010301506100020f400074810800309078602800840d000704005001810310b80301d00b41c190024444000d000080039201e114050f0250350100c0c80010041007810036110010100b803002d4641c6560440315107905107403020540c41540094070760010042015858010a00100301020f07455045605540c3c015206441012007a010880100e21107801550f0400030914800005241000b420320f000c1d10103901c40380111003550042000b400c1c0c100490510400b0103500307035001030140290703c680d0408004001c1306100c00307031800700b000c2c400301501c1c10803441014010a034504c1c00503030300c5030026072050310001d044d5840d0f441a0401d0020b0b002d6981c01c00c0343d03404c140106003000190384d400e41030401030307550894034043d4200707180311207580300c898001404501842c080c0341143e080c005c10b6905e4a4be07641c12440020080f841c1e03599040d0000707006c0c82c2c0c20344011207107105681c03040c2c10350001f4902003c40c10484103400341c5001020095540c000401d180c00445032102c51101d0041c83d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 99191969 1250 99190719 99190739
    0x103120f08041e0f080c072402030a050a0201020705010510080f010e0c100c06060e0f0903030402010c08070302150a1a03030f16031211030712090b07031808040305030c01060f 77
    0x18442940c2c0061102d4103d408120840d000001e41e2940480a151200c0c0c017540795503a0380c105030042140c0d000141540f03c0680b98064083c01414090b0340c015480c01440103c12603540c1c10070004c0c1001d541d001d200040000b10f080c000d103031040402210280b03100c0d141c07049280c5814180740030802c060340f60100b0f80003c000040380e00c990044069401a0a00340030000445902000120140c40d403442c2c40300201d022038150340f8060003503036007800c41403075a229200e046031070384019240203000c200d81a48440004104074003802d0759a0007030042c1c40d21000c41121440000d01c003200c015482d2a5204004a0101f11564810b512100300f50011814045900060b00c4c11703104513022042c0c0c40c0c281403801000c06100d6801e240d0b42903103a490601c0305000420030340482d50020303030740000822540489280401d403144205004d03079800640040080e1221034069000f0007010100312688034104c001d8102051400004000640c410340065980d2081c4005140c21100903400c0200080d01c989403c020150312 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 99193219 1250 99191969 99191993
    0x60e0d03050a140c0a0903050616020d0f090303030b041814010c030b0a050405250504030201081311040f061203020309030607050f040603020d0b1f0201140606180d0204050103120f0804 81
    0x414509a0b5018458170684d840810f81d84020b2152185d00c0412185a40b40381205001201c0f40c0c00310340b00c203c0121804c0c1d0b404e5019541080000d001c540040000c81d103c0e800c44000c0140c05400004d6840e1181d075808030100104005488030b0304403688014261209201c2d0302c41c020a2850200b1a406445000403d2001e00380302d01c45c031030364840d00490100b603045414604221140000c9502007486008094590f0b01700e44030582c081440c940018888a56409804240e0f9a008160700144180c140400006102104141c17414076a01c2d0000b06052500c0303000340701468002e40055442d0046241018500907009251600b0450709200c1c1021000c904021343d801d0340d1131414050b840e01280c0b51140c0041104200c80c55000031000005004000e0700d010451810300c665009109541d40b0030700080200d58150340320f58000340304000c10443c0170b415141d07100e066134005103e91005002600018261030f07082e001580c10540000c01303003040f9031300300c0a4007400c1101c43c2071402e020724080c0c48280340416 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 99194469 1250 99193219 99193231
    0xf1a010f120f050102091c05011103010f03060218060a23070209070f030e0303010603020d0b010f050f0d020405060d0c020d0c030206040f0224030709050a03080301120f060e0d03050a14 81
    0xb0b010910704100300c42034044e500c9142c4054806042d00c80990343c21307a44048a6030702500c09500c2c06202ca000882d8604c1280c1c181d5014000a900451440e0358400080d801403010301300c0b040201c0d23200f8040d03035503031030041ca0220107540e65010b24550781c4c401140c140c164480f101e00e4a03c0108189030068603026421903002303506041402c1c845000c1803094015014854801c01180800800412402e0b0541e002e480510020001086006906001520940c00c21031a10000c20303401c0c8080000140241700501c03035400010b001601380340d66a80481e526412000b9090030b4143c03502200d82071598100000c041070030607031810702d80d0f504407510040e4440170041c00c0075107e041800f01c042d06544a107900040389140c226041c1c0c0c1d1090601081040070341065030f807400024150070000407503240c21003901c41a260014907143c91030746400c052000741e0100d03420460702140207062038000f02d15580310301078121800c40040c241c12055a60010229680140150921884c02c0415413810b8001c060850b0711034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 99195719 1250 99194469 99194483
    0x17011505060c0f0f01090b070c051203070306052e08040317180604030c0204150b18150d0f0f05160e130e0a0c050603010b0d0b06070f1a010f12 63
    0x1c0301402d0500702414a00c81500d070b489101c0f64603064130015407040708094054141c1000640301d035081100e00305842d540180c8154000d4803640380f9100340000864220865080000d81d40d9a9007011590030045141d0364414111601e5155174603c501880e5484041241e01e41a491032400b66005050f0b540c1c201c18801201e011400001e01c6010b069004000e0b4134070200c01ca80c5d03640340500e00140040c5d2a00c608a008509012103207500b882607001e803c2c1a1100f4541c0a07041602c030846a540d800210846194081489061620348a07400380080c100000812404110921001484019101c0403a07000c04050702e05810407030070101904c07a0001c81d540300d280c546c1d07030303100140b001580550340c00311a401d00500e85a0300b504d0381100080c0303401899202c1d01401440c01e94504c100000f5000074810103141c81030401c001885140d4a500c0b5402030b403c000c00480c00c1482d40e8656801c1c080404901321190b240d5449660055891100d40301e005003c09405056042d0424148440004000600800301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 99196969 1250 99195719 99195727
    0x803040b25020d06020c0f010e0d0309111206010e06010c0f02130617030a091e0e09070e01170c0a0503100f09120c0b07090e0105010c030320041701150506 68
    0x60311000240c080c500c2d800401014011446040000003580280c028000030312450850710348002c0d0602802140c0301502d03000d00801c2c0c80005054000d0440c603041210300e581c02080d907440c695583d03c2070241001d188002023500d0740c103282903e8100140034000d03034103001c01da0412200240da00042180340550544c0c25510100040c81e410703028000030741281c00800c1141c102005d80402c00400b801c509a429650010140d98804e01240304901210155004040400060100c03501e0800940d411009801c00c852402d40e071900d03010108442a0002c100504030312600103900070080040c4001001c0c101c0b4048002443c01d4002640c5500d4040d08900064071080d8142c00041c0e198480001503800042007030010700b440300c0080491184c444115000d8451001103000d031845095a02c3c04e50b030751403201e50096420000151000841c00004504043d12054643c1c0c07620280021400401c0900703c0c0107441d00d0a06003690354400000385144500da242c481c070240fa41569201c0101220b40a40d00c156403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 99198219 1250 99196969 99197017
    0x20309030a05010c0210060509040f0510090510050610090312050714060906070507080406030b15070f02010f0f1e03060f080c1504031101080a02090307030b0103020306010803040b 79
    0x450152148469160207403807004424030006401000621040354243c1c2d081c585d141d00384804648290144e10780140282c0c001900044107014031130707a020300034000c6034010300400ca542010303a15100e008881c00e41080d907140400072001d0240300c0c1c101348110740368081e00c0c0c010800200b140146220152440c40f10942c50040a4060400c45102580107044035030074184d0480c2441d50b84400380c03401d6a0a210b11000908400d1050050b5103036640c0c054031241c40d152500e0300440140500072002d60f8051885c5500030035001a5100803e070301c80c40345910302a43d0285000140c030708564845400180028014a12191a801409251964403101c01410703103d110400440013400c40e030700004a05229510301013503820001071141785c1c07800112482c890180c41c103482401140200e20004100310003000702209658051000c40340e1041c110180141481180c01c002885c1080c9a40706640500c0c40400500c2582000d202ca64054840640207518182c9840051a400d100350f20308240003034800c07020101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 99199469 1250 99198219 99198223
    0xb0706050403140406030e0616020d05031905040b0a0b1c020409140109050f16050a05061e0a0e01120c0804140708100204091406130b030f01020d0203042306041202 72
    0x103000002038030b0f082d49442d100c0201034000c000b02c03080b55030345104540c0007843d400c628011000c0703210032590140c866a11160b905a46640019000112600400180c80c000041522459118034001c1301c0c0c55016090411400c021030718042060781c01822100e556000644180d210000c5080e41a00c001440c000c080c1000044070250741f941e8001942000c0044090180000f034101e54180c2d05401e0315640204180e6402d440601482170039000110070a08100310b18201d0b01400c02154a0741c41941140c0f80442c034001640c0c0304176442004515844046c8000e942e005458506040071204104400f141443e8043c1c0030960040004268901800f000200c981091200e10003c1044c1012940d04401c61401c40000e5045800380c6000f5070b241c005070b021151200081240034a201130151014900300c0040003010300b08551900350180304858020403034440902c0100030312002c4280058490402d0314254440350048040038501c1103580c404140c4900011400941040d0b0250000d85092178184080e8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 99200719 1250 99199469 99199487
    0xd020409060c080c03060907080a0b1002160b04030503030604020c0a060f0b010e0306160e0a0506040806071407031403060a080109050c0306100f170708060403031b090b0706050403 79
    0x290010308040800d030030001e140c0c004a102040c940c03155805683d450b65912130a0000311601940885010040758040e40510321a50b0001c60303103103011440c0c80015020540804100e10401c006910101303c6015070700c0381e1603019014200305030b4150300d414503680341c0a580c1c0c0000342c80301d0301c290340c00200708413204e4040240c0640a90710850502080c14541c2010000b00410204076001c01c0384d064036441a894042801ca109040501d00121704506401007221911b881e8452560400c0100e5030101d455aa920701420041001c00010b00d45842c114000800f03002c0c0302c081e181c1d44507205000003400a03030444181d0741301e545900704042c5c0381c2e0b5500b0002111074083d41c1c000380b000d518002802c0244500401e107a0840a0160102d803000e8580301c0e1462482502c44c403410181d00c0308a00180480fa0b403208004076415290030890f00d1040e181d49070380d41048407d9500f14040303a5603a000700201180031080707040e1854641007481c446841c1507a0b5076094403410f500281400d0b65400020b080500038031040b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 99201969 1250 99200719 99200723
    0x60203040504022a0a0b0f070f0305071101021309063008040f03110f010906090e040804080d0c03020f010513081b06150306010915030b040501060803031501031401031e020d 76
    0x1803030720413801400303da2903405824040d00c8000080000810b0170800c18501c9008103031590b102c0003160303080b58080f4024072014105800300525800d030708094040900150500d800b205d50038a00382d500d422107650032114117600c00b035001c0400e0740d5014103840030443c410304040404604400000140e240850051045404c03107161a030074100040203002142407140c01003072007a07c85500000303035400113451541d410311034640000d4000000780010081b030308100360042d101d082c00c242000d4440c810720f8200010316090000059a40d071162007416410080340c002d038005800200b0a5007004040c00c11186000d003000f0303102003000184000a09102c0614540324500c0d14143d808a04081c100c1304005040e20700701c1446842100008a01c03030000d44290885201140c00e4114001d2943d6541c0c5a000c1f8010820340700317550b882d800060240000c2c001503100b80c0c0a075003a18503002e1070710005801c44565000107100a22a4030060001803406206d10310700f041d403c402c0c1081c0016a100080b11030b0460600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 99203219 1250 99201969 99202027
    0xa0213030f050d18062a060b030d050301030c0506030717010602100e01060b07110d0501090305041a090102060601120e1203060f01021203040813080613060e030406020304050402 78
    0x80082803050040e81c9941c924881d000340c5441018410303045440c00ea214460812011481d4030030014140540e2a407848540b80000390103840f0118440843c0940141c00d059854039241d0a0003840c40c542800a00011320b441e0402c2e13411541151140c845180c3d5501419003c0c02c4e002011814441c0078080c0044036106480c002d00307166842d040000e4581c400508903101031810f2180f0030b1040981070080c0710564882c0d024a0781445016143d80079200803143d0842c0c1c0005c07500030000c01041d070038050452454001c0d107071140c1d00c034a070942c10100740002d4001c10f9001c04090040d420640e034041007654201c0030902c0d1030114083c0022030b10004141c000c3c00082c0a02c1450142e04440c80da640c041c52240000b2600041b507230000d5001a43c03035804a44212201d4001000020006078400002d4101c414000e5009904c035034403002c8440c40c0c4142076480424003111000c0003800c10810340507401c010200240a182010314050029681c0e001f140030301e40c456071300411041100d10785682000b6080b402c0c11a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 99204469 1250 99203219 99203257
    0x10120b0405041b0b0a120c1106091006060c0f11010c05100e060a180f030909060e0a0c05070b0f1005210c010926191a0a140a020903011409071706010510080a02 70
    0x48907078a2f60307207103a4403030070728100b01c000501c040c080c9081042840e00142e070b20315400d0036980d907400c41c10318450311641440312a20000700458002c000031141c0e011041c400081200000d20140e00e0030500030107042445040035003407485a010420303511501903221082040c1a5014039060b21510410f42024a25502e07040002800f0300181d503465000f405641000c21240c000381c4800c030b4443c0f2130418082c1110f004400419402e00031500150b03030090046110850680d1120001a0000c00041d0701e2000b82d02280100248498203008034400e81c0000d003030614619140002c0400042d000741c41c020071044010203014948001840010482c2e5606400107803482c01d00d1511050713900c4a040d00c9040e240f208400182440058820303002c103040d101003900080e070703100f0320860069808481c4003500b5540b40d107003621810200b82c0c551801000305074040c1401600b000c0c170121a000040640900d541d101000402c45500c42c55014000c020703032031901c246140e8483d06810b0191181203889240e101084c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 99205719 1250 99204469 99204481
    0x11061608130501080c030106090b0c01020705030d02041806060f120204080f0a0b100506161a07050405120105060631030c06081510120b0405041b0b0a120c1106 70
    0x81001c505441c42600c4148554880d5092080140402d01401010550f0443e05001d41314403071002d400b8541179000094640b1120b640c41c0c6007507402191499103040d402080c140015000e01c0158850342d5615282080800e00d0b02d440200100c00c60b80c801c0040c0000303148000c80889040c0c040b2805409141c0458040522800015585a0007000161903812204012400503070251030800f04440000703000c1030410304001e101e84240184441c00300c074614840c240410600810400f01c0b803080381c4a03140e1035207480c03502092140c0740355400110001a45468100b110940c0c60340c060b20301401c80704a42400b106202e214001c02e2a4130404245117545000200000f009080d110400070b54500d69260350b12600c914201030001c20003d80c0642e07100100c1240c2005192080800141c41e80a03048040788820800c4003080807034034151420380b01c0d01040410110360a1030032900350024003040a08924114035010b0083c1b26040310039103014180e071101c02d5070704820302c21124400f4000a07502a20010f040034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 99206969 1250 99205719 99205747
    0x2030405060402182a0c0607081006030c090e06030102091201050603010f09050a0f05010b040903030902190302090127020307030504140d0906140409110d0b040911061608 75
    0x2c8030100c1c82407030084501e13014800d5010050380249003001c01c201014503800e0304d907009400c001d5100f40035080c0900400146200c2000140d00942d503545502d00d41c1c2c00c2910b81a81210b01d42d402c0201414201040761540355030200c0300204890110621940944501d000a40a441481c10082d032102200b910f07000c0800065110a01408040b8001c110303803001054088103845000c000a0402e03040b0041e44e03000701d03003004080c04920f8441c0c0000606215400f00040c200c414140e01540000d507200e03004d030214180710030042c002210103084050f05c4c034030755400500201014010109580381c5822140d8200e804c0114510140380202c5007951245000c1c10000c0052604031008e44160085060b15541824080f42c822000d00c9541e41d454585410024241c460f6010340411051440c001c0000160004140c403405298403002c0b8403140e0b07a581c810411009032030740c00800750300c100c1c5032000240004007083c0402d16100820780c0d01c1a00c0f2010b0312218180400b00d040040e10038a00001e10540700c0e910 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 99208219 1250 99206969 99206971
    0x6040f06230d0809010e18070c140601080d1b0221010f0902010e06160c060306080d03020a0207211505180c030601030609080403060603080306130e060c030711010203040506 76
    0x90600300c000040c1002c0040c654102c10016010381e43c200111144c551261b80c9142c00d129001e800c0201120303c5010701d02d00036030105d6402001408004540082011044800c64181c014400a0055504180030b9945844891140000f48012004526040081c00b41d41501e41d98005105a00ea12689a4000360301d05501032041425480d20043c00450000c52041610182e010382d03d03100e05051100a01000f94032680c480702d061203071004503000248540c0403980c054481c1d65404035400c0c0c0f070304180614101c5080c2c045801e1500600c03118440c2d80e80050300c1002c48100015200d143e20200b81006842645460041c1510245454213460841c1c075810050049252a0000030301c800002c41064441140c800485d42c113801560042001c1030941d00a10503450245e20340b82e14155890352a071040791041d0780101c0d0b0750700d4003000b04030b041d2401c02050380312000700020a1044d0f1000b07450781c030744507807001303080b0064443d01101141182d40308814010352549000c000b1036490501c0c2c1403265071040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 99209469 1250 99208219 99208259
    0x81806010e15010f230705071d0708010b03062428020c0a030212030c0a15050708010b0a0305090f011112151008040303140a0b09011e0e06040f06 64
    0xc0d009990b8811540b14921015070000306a5502c80791001e509204024000d010b070022048690900c80000490004d01100004040c0c6040742c8080b100d0303021960041d584002c0c80682481510307001080130007051805c0380e501c0f0000f203d03080300780b20f81480203c0e2540c5801c4120b060307a20700881d00c40b098100b040c00c0b91040700a1402c0e402458820240200d80d100f80340d1282ea6084803400718200014180800308030302301585c14060b642407008140459140a003210401c6c0c07003494101e01841700d2540c051042982083c0c45140c8110103605108120026102d0000145c080694403c0002c4110b80c052100c0030346400110002d100c0a80600300f022260f400c83c4403003030b00d018017403004250280c8030990080c1010001030185620040040025900780e40010416000e15490300001000702070310004803446403007290703c001000034030b0109100028405811280c1414107496603595410310f0124148120340401c00610300c0750b80c5100100b409845003061140f110f03400c0120210306d00c60000641e51501d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 99210719 1250 99209469 99209491
    0x2030d0f1401140415060909020c1908180f0d1101020c21010f0e0a1202030d020708030901180309050f0a080d0201020307020d020a0b0c09040b10030b040e0f0c01081806010e 76
    0x80a50b9150785c00814040c800c54000c100c601c0410044401540c0240c10900f07240c5054a0740501541c4d526802d2018440c01100c1c55040000c0c2100200078a801c270050940040d01d09181610019010400d0302140308000f0b40368803120010b00c10143e10801030304011100c0949000341c0003a0103020030340000000d5403622060b5003400c1888440408501c80c0c1c40c00041c01c0c42c01800b040c2d0503074031b078160244a8101d04400f14002000404140d0189000070b1070607a21800040b03aaa24007040c1c48c07401c41e0340007060010319145010b010310210358440451010b5440031100700c010000080c0000742c103249554804041c901800d1441d0b1070310b54040d400b8500c83c1e4060f40944020460844c0100e884800300d030300081442c404180400d0550405d0005042c5440000c0c0001642c2141c090004210003070390004200080d8882c585110241030a00403440d4003580c280060440f0008a100700c0e454400900456042004d014001119003500030904803031010104142d0b0040e5031156000c6030b60f0b501c1116282004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 99211969 1250 99210719 99210731
    0x3050603070801110a180e1906060305060f0f130905070503010509030a120f09020319061118090619060c02010f090803030a0902031c0302120c0301030302030d0f14011404 75
    0x80007042c0645004034080301005840c00100712004d464070742600381581c6e040c0402c0c00022901014000150340a85100031140141050f81c250280c1982c025408ca08105414401485641c0d1540c22110782200f0003200d00036042d184180201e8154000e0030203042545041007403090501c40d020405034196002034000384850750712422034580c0c81c0b00e1400094001042028000c80096040e40081a4000c90001c00b08105845400183c6800d2201840c030240560105c5003008208251086c0e8100101d540f455509080c1890a40700600041c2c904450051049000050700f582d2448040415840d04200020010b9103800c0020441c0140240803408603c40107401007000e40540700000842e01040019841c590351025150302a000b080c40c201c0e014454034008401103e01041080c00c0d600040c0c3d0010f0721500c4170101c0c504001b00180800411203410030060001c26400300441e032409503030fa5000b14200c0ca1407082c8900505031404400100e484e160004150300007034a1481e0f0b80100c0c00c0300c0074030036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 99213219 1250 99211969 99211979
    0x30706020105040b0c070c0e090303180123060a03020604150306050405042112051608060f06070b04032d110c03060112021201020f190e010c0303020702030115060305060307 76
    0xc0300c80644020b0074140c10600028400440003000305400d5202d18501c51f001c5564490792040310304141c1d10140207030000300401810b0381da000d0042c03581403403160003480342d0b50030f007980f20441382403c0c01484030044401c0c0028186132210106c034401541d0150100f5952640c038110342d105012620342c5100060b081c00400169894580038440c00b60b904180310415400800c080c1008446035442100140a1103841c01c10b600c40d080d00c602442070b40300c00040c00030702003100001040442c2c0203207013501c03602101d0002140c6844103029504240ea00c9842c0300f241c0d89aa050507504072101c0481e0640c402c2c0360276400c002c0e240703400300e0300000b12429443e001e02d0504194030702074031000201065905940b100004004083c41d100309200e4160010f0b0040c03809882d5003101d642641e000c6a144840003000290804031000002d042c0e04043d03005180040d25031400c4c200007022440d018000ad41015000b05408056650a40c4181900b041c000c04852543c0d94483e4058058a001c9500030302c01c0c0143c8400041c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 99214469 1250 99213219 99213221
    0x7080f07061b05010b040f0204080f07030b0a0b0d0c3f03030209010e04020706200f09040515100201051f0b030402060307230c01050a0c1b030e04090b060307060201 72
    0x558105480718105003440000b4803120406400c0c041c0c2d120340d2120501444c5489a100c0c3d040e0495803d90096952800d0500d940e01d02401e0b985500c000d9408840d04001007048509081d030001d10403a4007046401a1100282004000301d401034900d000c1d100313000912104c1421002c8a044030240c08034101005918400f55151030403500b003401c40065061900003038800d500030580403c050406511004801c000f00c0c041f41c00400b4105c80b41c03656440c9036003030003101003c0030f0800d03001d46440da49010105038600d0005d0141c00b03140c42c000c0f034541c40410015031040106d40c0507450302825040c0706102600009001e00f2051340c084884200e08591000f0a1642c0c983c01401e07500320318079540c910b4403507900313103c444d81c0b001381010100088244503002440040c61024040c2298000d4183c8459440d000300b803c440016015800551808850b40c2c607203038108544010f0014480d0385135200010504003918200009400a580103151000c550b080240c1c5601e2180150b030280d0884191984803c0305034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 99215719 1250 99214469 99214483
    0x405031b010201022101080f030703020a0f030e040906020a180605070206030c0906030f090f0606010801060503041502130f0905100e0c040b040b0d0b0306011a07111207080f 76
    0x158140d0030060400911100c11000954020018400146440c0c003001d1842100c1c54001200f1440c58441001000b000a0401403100d1901d82c503400303103141202c0380d6806943c44000d000014001c0c101095a0014107000d5008141e903804050410703c8108101d00e0442c0c001d5000100f000c0100700e40100300746080718607221800c203075003a0380c9416241800076000c012041c1c000401c00b000405007000340054039100e07031000e940904512101c0ca0a41d0910791801400d04080c1c200740c1c08140d11081c100075044ea0320031031150440c1c0c140c0c14130310398a4460382030010703401010000021840c3e0001420240300071003a4101012282401c0090394444d8940c20b00034150340c1c003510300040111408030240001c03102164a203401440d14288185001d43e00c083c585a60340040e44a4483c900010410030500c954a01449000f02c1085000d03090f250304000c039070b0031045036008800d030740008081415403c000381c07401c906c2a50800200a50040034503808429a50100e44c020b001c0030b80244550410041c900191030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 99216969 1250 99215719 99215729
    0x907030201121a100302040f060c05030a03110c06010f1409090607050a020a0b0a020301030204050609060915030a050616031d0307170904050a05011509030b06130603020a0b04031704 80
    0x407070001024103920401030900ca55210900c1c1519040790f101d0b903038a480050b0103c541a0b01c0160701c036441d10000005ca2000c0c0d501c2001804001e4a076900000c00210864001d41c0f0507040015215981820144240c05100d010440602c0344200208110407144c8a2134100c5500e00f20b0504800318100600000c0c4000380c4050705140c1c024404034949601580140c4000c40661044843c1c0c10762039100e2418640d410340385507054030307400001403040d801c281c000c3ca94800c209668040741c03400d0260100700c3c0c210340200b81ca8220000910380903141c1c0d405120600b105904041200c010f0f0410301100c44030342401181407000f082c5001100c04005c6458901d84a16128600c0514105043e54907081c0d050302503601e992010420401842a4036079071407260310301460400f10001410341c10310000c1d440c040000407025050003043d001c01c10000d803483d100c1903402082510500b8800c0340c942898000350071141c1000350300110210001c24075030303d1000544101e034014a2103200314030409505803a1803080c0d02136 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 99218219 1250 99216969 99216977
    0x1602281505070b0a1a040603021e0616062a0804171b06040221030405040f09061103040b0703151203020f010f1d061026030a03140907030201 62
    0xc00c2400c0e81140200c10400141c01c029182c05550350391940c0903141140c00d603e819503a4030500b0f11110b00000d131100d20841c240c03010840c150540d0009000d40410b00d69401d401d545520b00740042e900e511041e6040c1002d83d5200307003d115a0b600d000400b410705419400c41e40c43c096803002601c2451004165400d010a4070b5a40c6540c03101e80312030f60150560038800140707140c00c1001a0310500d903495001304588000c405041d1a0801e80f04104140e02100b0340c2c42e041800e0141a4010000040111000c603081142c0000b4011310b1405900050080401d02800c224a0328000e841002e1034880254400c40c480d101d00111580c59010503021905a42034071600105d007042c2c00d0100a5600a6103180700d402401124040c10b140c00466003035461071807184c42c250391079100680d20320400440309050070381080043d01c12440d0948480c12640b010788102411140743d5001c850b03000708a800c0c01380306040c584003520381c0d9040c84100a0b01412401c401c4a00c0002d801001401060000c60081c0989034140d403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 99219469 1250 99218219 99218299
    0x210c01021621110a03030306060f0908031801020c03031204170a020a020103051e0414010606050c030703050a050d0507080f151305090f030d0501080f1c0c03050f1602 73
    0x901c0000c03070802c81c02c084925128001101c3c00980d00c00c0007000045119a4012030841d0030316800030254802c000b4540d09110131004140805840401940c0b00145e040343d40407464842ea1004030f141540e104000f40d01404000f40140090f24a41d501d03d2080d0300400c100c481d10b40146810800d14032401080c540160040c03240c5000543c4070340c001c0c2da080400004440500f002c0341e21210f08104054904607030a03803801c1c818580118081c001c080c014125410300741d06040500043d540c80380f04401d00202001000544540342c1070094041d101e00c001d10350800c000038031f0460409007a400003030300c4001c140c030a45e50014540d00341480d800450714070046d00d00a403454048440001600000d09004582c0c041c600004000074001c0001d443c3ca9615007901081e05d500d4502c01d1418001c0d00e0300005415044503a0001034496444803d0b01d425826182280b0501c070305041c100c82d14090310f2125404040300040c65541141403100c40e000c8103000712008000d64626018a1107140314040300b8412064140b5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 99220719 1250 99219469 99219509
    0x30c020307030c0b0604090203030a030906050705040501020c1c2a09060b120411100818010c051605120f0910050301210203010204030623060108130b06210c010216 72
    0x1420840d0045c4000d00080340d0401c0c60ba00180c1142c10600030180001d96a004480074400b403805115002552810040d203440d0504000075142c40464404500502c0590f0f010710f40d0042c801600445507410480501d46200303018084200f1080c80b00d68460112400d03080443e50441e10f124000c02c50b440f078110685402d21840c904103680074000c00503280c0c04801074400001c0c0c1c079507041083d9145500e540f4005140340840144450b0192001d001551b40e141c411158080c640241c11200615982034280380c0c011000c1c0707442890014102c826404154003c142484030f10802005032a00082c02c50f4a40d1111160210031a11400700348185138030600070006070312155107014200280d413070001d00054949078983d00c0c3e401c01c0c0c0d58030340e03c106807000e00d000c1208040d84216500d550020000d00e000b0440e81000041d030300c9500344480010b0604800580412080d55444c110686204800c1650540a80880954541703d00400400c54054050f60002881c121f80304c0c01c03500140c52a180d4100d00a031403103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 99221969 1250 99220719 99220733
    0xc03090b030f01060f1206060302070b09011404020613030501182604050d0507050a0b0306030708030405130203060102011509051e060d03050309070f0b0301050f09040339050706030c020307030c 85
    0x511503510501507821b0076030f0000c9140f4090400602400d46025130340358420718050b200c40746c0003814030000e07900d84545000d070300441d402410381281c1c048819585941c500302040c2010340341c0e980b001f000e561074800025840482d450004410501954054520555180713210500d00c000c442604850101000240403610f030203e4510600c50007031048500c070300d4540000c252180900d4102002586000c0f08108491a081150f10040e0480d0800b80d4103003131424007c82e41034100146503031003083c0c0100014486920035844500b000560780c0148605585e507056042c01002c055a0100114921b0094400b10124058419000c2c44014108000a00b060340782182d0a42000d8a1040306001d9440f0004c2d61850300190310010340300c00c0008030b40d01e5160504004039100c07501c01041c0180151307001c00010a8100206400c04002861161300000004d41d00390300040201c0d026514041502c0d008e48184000040c550701178a111f600e003001082d14010050f030342c9019480e0000c00042c80010701c0e800246503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 99223219 1250 99221969 99221987
    0xf05250c1509051209040b15030f04020d02060a0f09050406050307090903140307020c09010501030902010503041104020f0d1506020a0215090a0f03030827100b03030702040501060c03090b030f0106 86
    0x9880000c0c0d9228140e5503d42420099025640500c00101d1944050f01d0503104100344c9480498002c10807100318450002c80780001003490100c041c0000000c0c0c15500d40400390000558003c00090381d61003652000303000d00561041c1c001c006054044041200d0400b07210704000c0e43da00800505056140121030400341900d03a004508020191030020b000500c11f001550098016801030100400f40303030f0500155a00582c040e504140c14801c462000d41d070000c080b00e4005400000074003681c8400780c08180a0300c141c540c10a2000c0c40052190701c0648245e202d422800d8456440d80300b22540e41c5412662814038100c0070703511200740c1070000e10307600b64000100740c000400f400c0449210741da0fa4007601c084000b40d00036070104000d6010040520b02e202c5d5018101c01c0c80500d1029010071085c4550760300c042a001080d4131b01d5071400c120020350f0b82082075821669000780b00344041c3da1603490040c421444140c0441c00715035499000701700109240d068a2080320f900350080020780ca459800c44000b40c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 99224469 1250 99223219 99223253
    0xf0f070f020a0b03160302040e160903050d0c06150b032202100807030b010201090c0510090905010f0e01060e030307031b060e07060f0203040312031e0f05250c 70
    0x11005540c4001600c5903051000101415500c0c00d45905d84004d01ca21000e040e10280c1e8201032040105000e1401c25050454105103070503480b00d060080e81c0701c15242c140c0103400180291290900307260007103a101091080741485468180406010345908400035176103401030300c2a1040900000350001d011400c0b40c84100d8440710395079030f0030380c40b500801c0028002283e5480061401d00802c41c04039098002c0c07100200c002c0c4020840e00341242c5a18000ca0801d000d800d00c1091136900283c0040c0c42030140304058140448100010750303452801c0d8031480c0307a521824415180783c4000290311406411540d1490502401640c0317400c8076640d084459440940a00700a60034407200c02d408150940724072805c1802110007010f030346040007805054103400e00401741c01c650007004140000754208002c13041d03a0b0098240420024008280c0c8640300007010069002586084404022a01d1a0304070314040c62540f51250b1010541e20300c4140b418000b90390a2020844103500c20002034103000c0300b010451 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 99225719 1250 99224469 99224483
    0x307050105031f060c0308011e03080309010204050a08030a030b0312120c07060c0804020f030d09031419030309020a0b1206010e213301150203070b091b04020f0f07 72
    0x150045040c0909851a0001c07070000da81240c0c14020140c12251f01805000c0d000605550710f10010104407999815000040040d02c0c0400400c4400b030b000d4040d5006880002d210074400348d242c6040c6560394020001e21400242000c3d9052114100414070303503a41104035001030700d42291a140c034225050007424001a07801308003e07100c00300d80507225a2011200640d0b072902070742054010000308105c50800603100b42c004807142c1c42400d402000c0c180c01c41e54054003008181e40c1c000c4285040c2a00006500001000c92203214201503050740070700070f024422038001e4407647c2c40d03007602000c502418284418151000021406541c02180c07010710350b40c0c0003890b8000300058403200c50701321114a00d82c0311301680031904400d40810394101418110a8440a50030011200005046125810301c16007100040c04c2510340f1f41c0d24400d1044441c11608600c01c01e80c1c9091212013644c2c0c032400b40c00c1d14410b1011407005031105107454002c45610a4030131941c0b600780b8104038040f41d000e42c441d00e0202c4e00c0c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 99226969 1250 99225719 99225751
    0x207020a0911071109150103090f0b0c040305120f040e090c0604170705040e0a140304081b0918060a231602060f0108121b07090510060c02030705010503 67
    0x8a0041c2120340000415003520381c4072620f0302c4e0b82140e01c449101881420007200300303d18019583d607008035103038003480d021544004034103000310400e51303801014000380f03050820840f8050140004004480c4642c00b01c80c2c41c2540b0403c0254079004415032604034200c100000c01100c443e2114140d00440180d0546a00180034000241103510550001c01c0240c0c0604840710f10b4201841402d00521060b02e0500810200c19070071503c815000c08003c003240488442d0004c3e60801b041030340c0146c90108210b0ba0a1403060134812030425540c0710052103800884000b42489051070318121900b00c00000410b8180c807584a15070240c41c81d111440d40c41c1851100d01e070342160b900c800d51809090680b0002101d180e10401c001e0520600910088106880c04010401c085c0c00044200d058141c0f07d034582d8607143e48200c0300c2030201030580410307a07511440c640854140c50a5000c1406100c041c142c01584540c8c40c1c5090707905c4808100040e40c0768101042c00c10007540244000c56018038401594804 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 99228219 1250 99226969 99226979
    0x20309090106110114010e060603190f1401080d0c140a06021c06050603010b0d1e020307030b0118030804050904030e0a0803071b05030a031409030a05030304020414010506030a0207020a 81
    0x1400c24260b10580010b12181000b501d5402c081c811064007041180c0c0c02d50096040800e0011b0641c40500031a01601e000400507242081c0146030804602c1038030303024010345201c0d280c501c0203094220b0481054001403000004c2c820800191045200c08135121110104e40700c0d00c43d41401403541c000f24115008000202e0f00058141c402040c52880c4444604110720f00c00000408aa809420141c0280e2003000180030b9091500280d0b000314422120100360f60706600741d02101e01000120000b840340c00803080c0300078550181c0184451071400c1e6200b042001c03044d10141c3d100003081c80040d0244900700f00600c00c40c01d00b014100ea1042c0607042000c0d02d2294600414014582c5078444211500041407080030044140600b0a50703620f480110200305083c5070010362290010301c030040c1031280000640e81005603c0f010b507800e050005040d1500807400d03003055034807540100c80c2280b141d860003001004000321418400c2c113a070005000a81590307030f0050444000d51203004181da01500e1007000180c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 99229469 1250 99228219 99228229
    0x51005071803080301090b010906120b06070b040506071409060702041d0304030503120c0708040509060d060509150c03040c030f15050109060501030b0109060e01030f020705120a0210060803030109020a020309 91
    0xd40c4a2140d43d40c0c0d961402c01ca08080301d81d0355150504203c140182000143e502c020300710364215407a4800980786507502c00041c03c0e84140c400061035621a00d080100340240400c0d003030300c80e0700240c0312004010307070015010f200340c49502c00803680305d08244041009401c01c1c0e40304481614004209244a11000801c0351643d0055882221140d00004409140480c09550250014500402c00341440c1040e91131501c90701682c001c1c2c500030151180025010307903650140c1d02038035411081c10030090a041c069a42c0300c200448124004550410100d410840801d0841e40b0543d0004590800681155144a910002e0300400e4800031500000c24110407450701c101802004205000141c0300d1401002506407018103a01b90f06120003400200b08168100c4545021b80c1c109103000144017240705802002400f480c000a000c41c8203519080c942800c0c49030050410b4502a02160000f0800ca603400094983c21301800d01c407600107100400440c2e04680180480000e5401030303d04040e90a00410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 99230719 1250 99229469 99229517
    0x421020304090203130c140618030a150515011e0f170708070801060c05120c031c2406090306090303180302060a060611030301050d060605060d05011503050405100507 73
    0x4107559038402e41c00b410007070071b100d0351401040f1800286c040410b04400154080c01051905d041c141c02d4255509050f540a002081b0031551008400c140c9400d0f0580794401401c0131554031104035481c80050441c0c1d8028050550740000001c4c1a013907803a64030740c1c200c94002c0e0002c2c40509000882880032017a042c4140661304c0390040c0d60350392a552034035046c01042c656040e03000400344072008108002180340443c60711141e500c0b540740180d41b500d0b517880484c694840c5000e4420070a5051514141c1b848140c0c014152003050004822802c3c0340c1009505a440c11901c5188040380700800c040000981d01d42115401c6402030400159815044e802d5142c0a889500c0840044e007103002001741e0000c0074890040034004a180400211a2003071a5030f5480c401801030718440c1000c40c40c4042000040c0d0400e03005014080c1c10b1544070b60305c04260700044c12081c0122810a900c0340000c0f4501c80c400d1207090300c02c5400030018020030388204407c3c001400045c0c600c2c01044103103104030700360101358210701c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 99231969 1250 99230719 99230731
    0x14030a153305040c05070209040213020409050109050604020f070308130b0901051e060307060804020d080c06090f03070816060f020a0c02010201060801050618091903120b01080421020304090203 85
    0x210107190500d1504034410492034000a110700c0c584491032401341d51110507a1001c2e81e040e00c803c0c1e0741c0d40b2103000180f000161303203030b0089140b800001d0200b4450320306c1d00050304071906c82c2c4003800700d5168442040203a00824046c0001c401d014444a001319129402882e00712185242a0740e015482e520383d40300700c032001c0b110401e0682d1500d080c048409400355198400041401c4203041c18105000042d465084510508040040030381c0443c043d035944040030450341d139201d00680c0c1d945021002640c5c032801d0443d6503001c28010702e4481985058007008690000d94000d0300c040c90450108558a48018086000e89496950308402070030710b9003501c020810b826450310b94024a044501c002404d41c3c01541040400784d0402040c840c4984500c0c0060f45078801070000204260703510242c107450485451710a40015401d41ca4000605800100c0f050050b03034410818000c0b400c015006480c90780003a43d00070240e100d02e200320003450b59060f0340b0a400701c505106491406550380000d01c160b1b0425209 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 99233219 1250 99231969 99232031
    0x6241805041d0c0a0b0a03020a02010b0402070501090c0e040c0b1c050702010f0e030f0304020904080c0a1113140103020103110918010e070c080304021c02091003060614030a15 77
    0xc4140b801010880302c890424202d541400386401c1510480460242c1d0b80d021050540104405801500070b411039010b200e0050011900c58455040160180c5042401070710110750740e010110b1280300e03400c0700c0c920558011110704500e40c40d0503070401c8154024480e00510085c0c00181030034104080c05032902401017039001043e9110000c8007031040720034858a101d030130782c400c01c0050048400401520343c81030b011200603070b040e6210300b42a82d01c3c0c80703241034110090061100450402640c4020800c050b03e05582c0c407480201c1c0c0b1019681100c2044000320200d03400030004000543c400d41204119545411545080214410200e0394008072406c0010a0700a00030042c0300d400314103540c0541c44102450304034203070382040c1ca0343c100343d101c003030000703030144884115240c0c248030400748194180794040c0c1920b82a1604044400303001f001d60104450076414050000f07100d02c0c0034840c5e081a03210003400703000c003001c6c1c85d42c444030303030755a003202c1414180c3d140c1d4195000c11341c141540140c06805281 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 99234469 1250 99233219 99233261
    0xe0102161a22050f04091a070306030510091b23060f040f17070302010503071202040e070f0f031a13060503060103030f02150106050d090203010b030303090705040624180504 76
    0x200681603080e04030507401141b03016141030220b590140c1400710410f60303408031a5181c44840c8118058a42d41d00040d09034401c03000118404202c03688803d003414061294840365494000304200060003c0c8200255002848071030707035000c0c101c4030b071038074207243c005004500e003044400f0f180100e500300e640704140410303204500b0014003401c41904145652140c01500d8003909550010300300d400054131200c03c005c64108491007440712503040b01e001d422030301038400c000c0c580400c005003400441089030700003c070501070b003045d580d0090007021080c80b0700c40300c10a8401d42d07160600c219030016140d40100c150310380d900018551804e000c420701031802543d91644080e24044041d00d0200c03184162902519030700010018694401c055401c3e0210520010488107a5800064050440d40c4015642760100005100b481000022828111a0140c81c24404283d0f075154545a47c1c800f00000c51a0100c54240c281044e48120000e1810501107076100100c3c2d42c980c40440d0807181ea4140c0182040700d182 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 99235719 1250 99234469 99234479
    0x9061a031204030804060f11010203040f14010b09070507052104030c06110c06070f0b070305100803120c21040b040611090a0306020d090b0f070e0102161a22 69
    0x1100d0312490014072100380340790614564801c40184514810001041305001900c28003a2048100614050400c1d00964030303400c26007801d20595031108400c0340c00001e0501400321108041c01031010741c0c0c10041550701c040e954460251515445124125110700542c82058241c001e000101c0326034510750250360761106e00314a0b12002c00f0046800103424072441d2040362031503100004110041d600d040d03c00c02d0b202d20781d07494400c404444c101d0004040308885800c025555500d40d000d9442441c91a000c2d2140c40d0352912017640768840c1d100081c581d04010000150700100220060100005000344803050346000d000049140ca4103840441e0040e002d14148000e125503030050220700c0e103422540c42c3c580551000010608400c03484000e000c281c005c1203026608003140c0c0801e1015401c1608010140f84c20002c61101d4541100e01801080016814003120351001507011001004101140740181c24010010301d20586501c40e00f001f003800b04402381c0c0b107400e900d4180008646c2000020304082c104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 99236969 1250 99235719 99235723
    0x30209061c260a03090302070b040f0909051c050a08070e01080f04140706020708010509070b0301170c061603200a0809030304031202030309060c031005090a09061a03 73
    0x64400c91252000c05180329100c420003682404555000c55003940482c0d50311114042c8015450704641410b001145402c40300703415800a0280d94440d6090340d644030340b203070150340c80c5000d9801880d1450741392120a1002e82355641c00442041d01030700880380040040103401c40c0c040001d00151000407401b0600320741d0319070402d502642014142c14a0041081d84100007040c041c0010108c01c0700c954000086014444400006081c001b100c1d070540e6801c03a140c00d0060342d038000a1141880b298a480002201c0c91070110301c210946c5c1a0011045c5164a062602c6c550303101c0c40001520700740514001c0c07826035651040185180061a9480030001010303003400361041103c1e242c2d01c048030380354078182c00c100840882c1c0b00254a034002c418a44840901000c2465400350f908000c150350035402d0720203000c0f500080610700c11469a011603025603518400e01d803060009039a540d5120020312340c1480585000814203910207004840014502d400703840d03841c01e981844982403551040c0007281111404c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 99238219 1250 99236969 99236971
    0x19060b04060308041403010939060c020a0b04060c022202040e01030212010903081306060e070201020c06010b0408030909090307150b0109060e0604090b0303120106030b0405160c0b06060708040807030209 89
    0x100302c00070803a003843c503100e1684411142404520030804d0881050701d00d627000c00412180691012151201c4e5110b0501510b4049801c01c140e200e101444400640c8144110465094500310781d60000e4800055090121881c913510b40c450307001b140700d070801e2500c400c544050401000315040c2c080c099451801400945a0f27480010345140c1d0614400c100466080802250040d508040006004050b4280315000305002d41007440c1541021061110075035054001e0300c000c108007429221640d9031010804a188500e20400f502034009201c4440a49011412298001e48031070a0341d28000d1695190a0603904030b15103515599919101490706581c0032001002a0880e070501038001d480300c0b0005002800350703108084000d0745800c20002d8a880031b009561184250522052003561101001381c058625640c00e14001c51a10000440d13040c440c0004c41501c80e26a01d60113481203003500c610200d10300081c1015040b40302006000002404007000b070000700000400340411509502c10400050b01c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 99239469 1250 99238219 99238259
    0x6160201050609010b0d0b0d05010207050705120703023a11010207060e0402030a0b03030703020606041404030c0b071404030302071a07050721020621010602010c0219060b0406030804 80
    0x1c5403204000840c0c40302d58450b4151181004155154950b45010384094900c680b04940c001d10581041c404120781500030b089801d2007042a1440e842d00d0b00244504000c48642041e000d13030001c10100301505092445880b40c1030800038010000c000e594100170003400281e00b403005a12851910020301c0084035500350000400d10191181078541100240407003d0b25070440d01c0340c0d40c0040880d8016810381d000d43c1201c1c5000d03041c0c0ea00e825107401d002e0345850040724410301075410031018403420402c46500c24801d59050311043ca0340f8595440f00340c040e0500030400f106201003110380c840604c008402800045110354002c110207400d203080211001c0d42c41509424284040c850580042c0010602c2000d0f65118050011a5860030103903601001401030040d41015000912400c0c0d0341c145010041031003800100070310242d99a0004a08844054510704010303048140300f0560120302c400e458503000d0140034045034100c181000035044852507030040b80c00e0075000504010f00c0540d022940e071004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 99240719 1250 99239469 99239471
    0x180d0203190e0f0a060c060b10050f03070c2102010f0204080d0f170a050105090f061e0f0a0905010e0a020a090e07121505030c042009010909050906160201 68
    0x14480e441c05000e003a021074005090201c502c046091075101c10700d1110b66140c00a041481c4655101c40107000510107190603507103d8101031189080c0c3c181504440302e0801c2039a213031450700201131120000f940000c1d107000100310f0b000304180b021400466110311010514081c01d120610580000ba0842d02402001508140144410054108041050301d001c0b100e40c02c0c050301c82d480480007155000c08001d08881c2800083e01881a005256486141a0ba0040d40c40b640d06844003080d6018207082111415400340604186c01c0c40c1401c4d003101200d2401016004225030001c010010740300c0e400ca07400202c0a036276948010460f00c1100710318950441d80b03401c42180790042c82400100b904100d03004010340c41404d940480d003240d20070100420003282192080024005d81e4010b61100801486104d02c0303442642031f00c402c24a0b0a100306403410b49120340300c0b2035254402c02071075081c2d000150100d05110500c0f90005018007140580e6100350b03c000c0107011286000440d05801103143d001090841e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 99241969 1250 99240719 99240727
    0x5010c05030717090c04020a110102030106020a110402070c150504051e0a0f0e1b041205010f0510140d080c06070305040506010b041d04050102090616020f04020f0307030f02070605180d0203 83
    0x11130703003c00c1c100800c0c8070035140540d0b564042c0000b910840d4814180014640c1700100000d03441d41d020480c420542d204140701c820883c0c1c0b0b942004107034016440c0181c11402d5011040224a58144940000d0311207800c0c030030f0a0680e910000382800b0404000c69516a0760303034800514920303104503400c0c05000c85c0c036000c58015083c00f56507003015500800031404400d51004c00707049018000141c80041c00884c04103803045803d450640c0c0070789124407000b01c0c8e4504100108101c160211074050584440c0c10204c0f1160700c40f00d0070020081d03071126040c2c911a5041002c22030b49001480150311464954602080314207003440c040b841c3c164168001c201c0d150003440140308881d1121040b01800d072128000071610381325804c01d5030080c411080542d80c80a0000351108070701012041170700300f1a00868454604169240c140805d910520350000080c050400008491701d0095100320402c2079060300041c01c003902d550362002203c0b07041d200440c3c0307404110f046024002d020029514001d00a1000e1420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 99243219 1250 99241969 99241981
    0x901060c0807020316030302100c08130303090c0302120d1202070305072402190216030c0b0a03090c090b040506121c050c0105071e030e06010e1305010c05030717 71
    0x886291a44010003401001954000f50341e02040b200c0183c034442442c600c9959664a4040e5541140650110119007400c000d0b072003003405890314510a00107000200700c1c8046540d412002828500003c0b50460380445000c400b603241c4d014055000081c2c000208054407100c44003a00c0003001e010380300e07605d500401402d800250300c03c080d0340840f907110300e600a8142900c0444503400d03c0160420903401c0c40402c4c51108440071002c2c40500055680a440d15000d829004120036103250001070901025500200200d00c0c010340144802c0c411032400148698541e640c108685929901030703501c0030384a0380c941d04d651600380300c0d80340c00c8201207032070103c544010f00826403140c04481d0303031140556001d090248400e0160040301c90005202008101ca8a84a00301500309000c442c100a03010b080104009000c40c041d2062266440033840140084e178a0098198600c500c002e2030b0403800ba000c0b07a0000c0001d0401d0240b072210034001d440e215240d1400b01c0004081040e145c44d008502503d00e418000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 99244469 1250 99243219 99243227
    0x14010e012322140a0309060e12061f0f08010606080a0e0c0f01030209061603140403051b12010e0c0415030c030605060402160b1e0105010f0c0213020720090106 70
    0x1202200c80b5511804241c100440038464118200b12140110301c0b18a04043e0301c000044250364441d112503004409403001e2000c1c1c0312000420888940c80b1501003442145404040000c202e0001072240780203031540c0c0100d070406816404000c0c03c0e03441b2402803100a40200d1056030020081c0c904000a01c4c3ea0441030b0758135071411214074090f044a50010442c0d0344a90101c84a051000d8800f03030b580d0f0011054400001c501c41c4003900040d03044a65800c5200303a4030110f1302201d030802c0c01004401580e45180c03401d481400462a0b1016030719a032140d00074400c3c0a1102074040c10400380de80c4044a10900040d00c2c12040203540310880b10000b880000c0003004070906594001d80006641c1d66004d02080003403041b00010503c07104000400c0007040b603c1d0584501c9101c0240c12031501d00c8041112000012081c02803501041014002005c80c600c1103a40006050000340951004114084894200c6c0e0041000341e40010801549005003410011412800c0000307503158500703503240c410b00030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 99245719 1250 99244469 99244501
    0x61a030c071101030b1e0307080105130605100e04150c050f0f070c0503070b0705010f0506010e01230310030c0e0c07080f04030203070611010c080103150914010e0123 73
    0x2c02214041d410800240d00c29442918090409042610b40c85040500a000d056040a0481c840c2c0b082500102c0c01f408107000f01070007034140c500702400d4240180d5581c0084c2800515104491100710400200c00746943c0040c0c0c00340d03000d481c0300000c4209135072a5034103560004550b034092110030401104c60303c060608071032081868038900c54079401c00e464401a400c1c40c9511856240c4140d44c4042445c600d50f20080a003144681e000b00241e60011045606032002140c88070f0100d404896081080e50096031181d0354100d046408008100c200020319150741c006460b140d80700c3d05141024410421048140c0001d0031860344081500d1400b102400740c1c80c840d0030b86c004c1498070b0115450003461507400c241c4000e513070f000741542c0005858450040c62025003901e246441d600781040314012500400c00103050ba03801a503890f92940b05150350300042c0c54241401c60b10220b05548041c80e00e8401c0c49000910b820a10001c070f00e0049d407181e01116602d00301d50030b010300343d01e6106001204400b074100d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 99246969 1250 99245719 99245723
    0x30806010e09160f09050402120105131a010e03030d06171005220c090207081201050402070c09050903070b0f010e0f0106080a091103061003060f14130203070513061a030c07 76
    0xb814400350341084c201d4000000d64000c507002800840e0b201400380d038905007241a25410b071108a0894070700c0c103803e0103684110004032201a8003034800c003420b52142008540300d900c050100d901c8c0c241071541c03941c101c5099511a140000010984034001c03003040c0429a4140f07003416051159041c0000001c103005000c08801c090315200307440d4202000003400c849402403452640454031035a1a00300780c0d01c1680312412000303090840d80004070340307882c00e0b01c03d54088a801a6030b0109140c14440c0072402020b01409208041c07006102d000001411f29101612819061301c07211515403400407007074280782e03004c0c10300000c00318108010f010b016400a0410ba106040200116000b002810301000c81040802c065070135000c2c13502045090420b8881305000c580c442d00f0304100254040300b03880b0489001c2d1030b481082a00000c04038884900c100701d2600c03164002401e85460340d0350b503800203503140c001048003081c07941c4400041050010310b000b004034030603040d401e040c55850603038103e090a03c252140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 99248219 1250 99246969 99246977
    0x60708091c0c050103020c06271204060810080c01120204050409080c060a0e0a17040f08011a0907020309042012040605070305010b0d090c050402040b040f0503030909060918010207030806010e0916 86
    0x84c90281e0030056102c1c4010410700c206030ac08004140301c1c0004e03294004c0c042c84000ca0305070008902c514070080c05600c100c0d141c40b0040c2a185069200444200a0000c1c42c20260780d002e100210b02980c079442a50b840a114503030b516901da07058000c803410580c1c01059410820700c0d10311068091400440d200c0d003455400090b001e420f001e40c070407400300d40c0619044802500c1d0801c0340441c1d400d805600501c00305800350b50204094544e8402c102c1ca64000300c80080050b0002c3c000b61f40c56080c5600541240c00311840400034000008031504110f0700080400580c0e01d442505120510036103100303581e040741561906100c3c1e58100082c90a02c1e10619801010076236407a02ca8009020b203012501c8050031004100707555690341d50000407000d401ca4050b0703020a001d40c1e10000b43e03910380041215010b2801401912007596038008100502d040109100c1803000d4503004010382c1c40b400e10060001030302c01d840b003620500309040010a80c2004400540c05281c00c0720a0007440301903a01100c00301800c601e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 99249469 1250 99248219 99248251
    0x60c030215010e01290412060f050f04021c0c0b070303090b010b0a110f0717150103030512060402070b1503120c070905060904030905060708091c0c050103020c06 71
    0x140880c80c0441e800c48458207085250300120303520202030010350407160061452000c3c01512180780c86500c1051030001141c04040008000142150555080a034012240010f00e00301000303c04080d54000c585d03800341042603c0c10842103150035180ca0450004401855105030101d9545203001c50385400340d01008040807601404051113a0001034202d91710205284065035950f104e0b070216000400c040010801070320220744114000034a040c9500300400040048501d400507000e031980e032100508100740502d0440303921903400110318500942c481d40d101075441d50350721001007030f010010f0040d51045004100604c041800880b040d03810103007100c400101e908036140040d260849521345101c0216001c11807180c200c00108a0004480041c042448195600070412507146003c82d030007000f2691603c1d0074482800e150002e40380c0c4501c1213018a28125121000401911012040b100e0031300300000300c8010420240001c000400007802c080d0300303090000d10003503141c21004041030303070344401c990b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 99250719 1250 99249469 99249473
    0x100e04020108060d2102010e0a03090509042102070504061d1b090d1a0702060903030109020f13080d27182a02060708040201050a0305070c0206131d01050901060c 71
    0x20241d03154517134410000d90501c1401d42482000040c04110b1030013551030030200b0710320740c800407508500d4558142ea800d14428101001c000300f400b4013820942da60340d107450b80014802d0a8025040c50300300550000c2901ca494130003000240c503502d4009003884054101c8521a92440780d11194002c04040086d820036440041e11146178011800003551043d01217505e20140304801078016002c00f42a00e0290040d5035016050341d0b2600706440c604036542c002c00040091100c181d02614440810310040c514280c24100085440b014a0308601b415400c40820301c405035420120071820030b1240c101c4005d00f00907400d004803e01c07c1138401c400300c43c000080700050040c4554003400201c8000039001407103107a07626600700c0d0906070b0403000d405031142c000800c004500400d0810f1103164140c1d111071500300711807401c0700a8075004c0e00309424449a40c0c05603005035249800f8002a10111482400b424a02550042051100e00102c80e48000440050205488054195055940a04110001440354 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 99251969 1250 99250719 99250729
    0x50307031802060a1809091211010e120309060a050c18010504080d090e0a0b060313020d02030a0302060a142e0b03010b0301050f0306090703022202030c04050405100e0402010806 78
    0x1112000703500070f000240602d10240c22150550031401c0a4800d60a501e072140d03c2d0314100d911038400035181c2004000c025200c14800c01d0f0b245280001000045002c040a590309841c08003d00c3c004091424013004200307107001c0c1005295806903009405100b2402d040001e500781e80318414144c02c15000e0041c0ea4502640100b0407180280658001c8403214403400e9001071402c40c642c040c000f540690310020a110706000e0203804d0b006080180041d20310703211012500e000c12624807040740c210a000c1207120250790140212000203020750080d00320340c5070030400e1070210780607d0150700d04030032810103201c17008905c0c12080c201c00c000150783c030840c1d4180c000c458180001e1940070a008220000010814401000c051412600c0c266150b12150540c0000c05454260443d24841030707610035041003001d89421060f0800240d0700d016a090035480310040340050b680110350398248004c00142c00c101034102449000c0e482a00818844210303410070382421190725003e4800383c104082907000ca0034036518 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 99253219 1250 99251969 99252011
    0xc0b06060904061d1605130513090204020705010b09241219050a020a051c110f030a1b0501080402012c061204020f0105040b070305030a0e031201030c0603090305030703 74
    0x101c10300802c5080a100000010311411945c501124611032001d5035454064403d0b103c86103080c0203400115800c000600080308082080c0400c2a40c5880e00d100c00758441341b004002160041d030010a211020000303111000d8001b8184502030021056803c101410080c4200a0714034110384080586d0340c0400c1c070ba8644034104070700c056508514410142040390001d10076400c0e0b442038074121003855480040100490050010481c9a0301c8951302000003107072000390114030a0000e029105402d901c00c0031038034041e090740b012100081c940e199a02d804a5008441009020900c3c1c0028035191903800200403490400031807101b01d00190034959034a06804d00401e0000001c1c01c0c0941b590650201000c406005607821b078001c14040385083c026500c203e0840e400c0c0c03401e0f560f08a1a10215540469040d44020503d905641d5030304161400c45900307000400c6103142407208500c00b9411410420030322407055102074207151130102004000303600241070702d600c060241800900070403204040d400b0462 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 99254469 1250 99253219 99253229
    0x70f08190e06030c0f0702270109140709150c0c23030c1c030c08161109071e020705040501030507150806090123090702030d0e01090f020f06070f0605160c0b0606090406 74
    0x10402c48107020013515105100d040390700e22001409070684010402f444c0b008242ca23400d00003803a47c6005c1c80301c0008030f007002055021b1403910b003c1608068072612080d824035089140103850011604412416407103220900751411000740c611500b01c1400107119020b456885d2400d103a00380c016005040c05840c0c802800d0307421030340c6d076695811662140c45010714007240882d59050004044941c505148025070300c00c5103140c5821281518040d02002d0418221a890085101d011000310740e680316401024002c5102c0c3d401000040e00f00710b45419605c80403d40101006a000c0806c8841d90b074280d950740c11288513a000d00c2da41c40e891100d8071003200c0f10210194020303000c601400100c66001000703020001e1040020443c0c0d201408840c0d090780c806410141174102492070450251405800359680b0810045c00c140c50040380780d980c02e07000344c1004000d5801d681c1c3c1e80c00708130b104140b070070300386019800505d05805039044641e40c807102060050042401040085442c003a1601d031a4410300140c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 99255719 1250 99254469 99254509
    0x1b0408060910060e07020c060d063210080f0408040302040e06070917030301170c030a080405030d0503010b0a030509011e05041511030c070f08190e06030c0f0702 71
    0x49041c250203541c81d5000d8518010803481e10100045800c0d6003054a80940c003681d0182c62240170341030400c0300c5900300c80003450481c2e642c3c000004403410000070307242c0c00541400c005030503070b408480108105225849040d0190320400c040b240302d541d210000b03a80c0020700c2405840f06803240c0c1000c18040c003c81c0c00081d0003c5c54084819600080040e03c10311800352a40c94089084d15918a10b210207880c07040003586d80e200f0b01c010b00002400e207450109554036841212040f03811540041d203031051308030f02540c108100003005e1010741001d000c2c1c101c0c20071581c10520700d036500d80f201711a10380c410081403008140d500d0011a1112400f90405c039034100c4400c01e41242a9808019100141400d0301c04580741c501000c0540301d070501034000c500170702e06491440c070b00b50707942d0105603034680d800220100c400300010007801000810900143c003080035164484041001200c4014101c088825100c610800d814802c03c1000030829007160440c280e40b9410a403101a42d101003102d101103420201c500c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 99256969 1250 99255719 99255721
    0x3080f07080a05130501031a060306040e16030b0703020a050403330209120607020606090907030b040605060405070c051f02090a06081e01030b07111c0906030b030105010b031b040806 80
    0x1007544500540344000010444c5500169036400640896801c1303100354201c034200800b112194a003600c003841c1e201c00003500c003140d01180b000b41582003072101e60459160107003070741c0103005101405210551110541c2011842c1c210a080041c0c1180218031008000301030104a15035002e0201d11905040c0315002c08004410181040c0c0070083c0d004069214000c0d0758031307200501d82180c00250f09000394040d40180c4495190f0780113001d070300b04008003500c4c0c0a10481400000045400c1886441039005110003d050300309001004291480504082d04000c045d0181030701151011404071140807072940b480840440c405a100064002c90038080d500204805001601c0383d08600014071508582d55403038901c40028800201d001400c0c00301611a10b0601c000500450182020300b60340d10303e41c4111410304901d8481e54000309000101240003d824610403c01d80390117005004260718100d009014944c14012501d49074000101003e403591184201600000f080c501141c0242c896030bc00c0d5003003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 99258219 1250 99256969 99256987
    0x9040609020901030b0603011d040c120303140f040c17010e0106030c05030727020304140a050f060c07031b080705070e010303080c090907030e0c0a03030c02040606020309010903080f0708 82
    0x3500b10300c021901103404c0003081c5102c0e141002c00c5074181c4900c188103101c00716102011440c1034100900807203007844011070124040601403c8680c999100340d901085080c10380c41e05201d241c0c00500380004a1907200b080c000001c00200d0900195055203510f00494045e10314100d0143c050550289030725480c214000c02440b901c40c0c186000c2d608180c00f1688040d9070381d03521061516a004c0110740050b143c910100303180340c46030001e5400c2400781e0342081e00022020005030900d81c000d04201e80c40d501518082d07034012018442a5030108134407220b41e050050321746028007000380d0039444103e01e0089c00100002c0040c204180c64105070420121080700b901c0341c0144d20184d40a0005030042070b04040010890b4545408036200c00501505900d000c0d103560038103501a15241c81c0c3c08007180204500d40d0015251040e509008500a503a000000314440c010701c811148180c207c41d08542040180400e6039030001d00c0001220341c00014290b640a00007081c1c10940511700000b03165140009820300d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 99259469 1250 99258219 99258221
    0x61b0f030e010605300606100f0509121501080609070603150e011806090605010e130b040c0210050a0b0d0206030415051003032006010b0f09100314070c0209041709040609 75
    0xd414003045d010903400140c840041d5504411500b02e80e2004452a0002c0068402d140800c21308101d0304100d07080011900c005600000d10034080c1085a0000041c049040c1080440c1401800490040c0c451401c16152a5481c0c940c5400364205041d2211821441000034860b58401042220040110f80d61a020240d00300c50031a06080017403420440082982e10441c89000120f42c416180c8102c40b5115400740f09480c0528800006070039521004081d9a8071079000301d10011100303034043c0c0810b08118005000301c031406807261200618000c0032140e56140c6500b12107240390100c0b441c0351030382d03610702d03008000c1036104000d44001c41c1000180150400010b148405803032281d140c060700c030003000da84c0002c840301ca441d46011036031000e0010441041180b0040800d80080441e8901e0610032101041c00c05106440410010781d403800030300404650722203502d030002000d2811000c480c000703800003203881d1400b600c06841030400e9400107940d11401c03821551009000f82092004035600c40d1168 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 99260719 1250 99259469 99259519
    0x1207030b0916060e01090317190807120501030b0a020304080f0d061a031608060105070b01080606040e0604050309012a030c03020d030e0a1205040e0f0103061b0f030e010605 76
    0x40680140d07800f084a0b8003410101c003403003106030355440c12685541c0300e04804c002c01406825030a001086000d001c008802c030592801d50468680c03114504002c1c0000707002c5491514940c420340e18000040c40080c95414944d40c001c000b000000d0b03147c0d02d86082c01c600602c00c910354500000030010b07030460301080c6a00b018040701c00305200c03940d0350042c3c803000c0400c51004865140e44044c4082d2801101c1e4050044c06800007010314103141410b0156544054048003038015240d10350021040200301d2400e40188003176403c000c0050700311402e041d690700350380740500810785041c0500c90f00080785030741e00c1c1c0c2c070a6011261000d8107000203c2e25410050001c00886000742c005024174030180c50001e00034041c245080e0b40c000000e181c0110640c0700c02665115000c0b5a800f08882000b00091000e00400e040d4021b040ca0400c2c2841d40d49903181c1142290540304025495903017a0850b500c8080d00548100e141103001d0401003030740d0480301741c03030307801005690002c50744070380c4010140c564044510001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 99261969 1250 99260719 99260743
    0x9050106090b09090610020c061206100345151a01021f02071407090b03010b090c07060e10151d0112030203090d030c02031b0109051207030b09 63
    0x6004800d4a4220030070b101c1c8140140305800a1490340800e1850420350001c26114038648150b40d04424940d0000b80c2075484220013103a074600c030005100075494114031002d80c80d003036400c080102244450711103074205001032442c000e4940030b40d00b02e00682080014038550f0260660710703130084101031030020081007041c01303112003452809a08841007034083c049442001e405070001d08070264180350903525281c603501401d0205809024600c0010f140030840b820300301e80c070409002c284c3d0600c042e00c8100e07000300880621980c1485020031580c0c442000321500b02502503002952020181070805c060031010b00c07101e600b4030540d6100041040c031a40000e0800d404003181d61142a0f0f200e40d08040c580132000a003040d0f120020041010b4500155183d55461090064a052020490015960b0982c034142680484e4480b81c00c0000c500e8180100c00d0301d00568000ca00000180a0000f0440d64007801102e008002c8101ca1611480c410030000b4000c5a101003203060030b1800361403940c0c44036464004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 99263219 1250 99261969 99261977
    0x81b070b070515010f05130f02040305070510210c020c0306100612020906030c1b0715080f070806041503060f140603060f040b100315060f08031c1a0a09050106 70
    0x7140b4400610048850485d0300748030540030568241010408a0004411151005940c034000200a8030083c0081d0000b18050380207055903601e08010700255040008000040120501b120420b14441d0300c14043c900940703910002d4134070300e0018203038a0030011104250385072064400300441c42920000c948240d8a440c0d50701403100001c107060100f603018074200640e2015041c00000c1c8039820000142955101c7e012080002c0c50507944440d04040498008074041071690700181c04140d0828241038100f090583d4401007850500381c0240f8454015041034071071520741481030140142c003c1903001440e0001004c0140d1428002200c004040400d002d802c400038540015281c2e1070301080325481544c00404125040d074032991201000c0000419100990300c3c402d5001c030100ba034210360303c2d03041e0ba41c05000041c4107091a00b0a40118102d070302c07000c41948100200b402c14403108420400c201c43c4e1000c0414050a403e010300c80c840d0100e04256040b4200c48800614400c094015904035112038071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 99264469 1250 99263219 99263233
    0x1206040c150507030e06030c1209030a1b11010806040f020a030207140601030b0708101a07020315010f05130e030c160801020a051206010c020303180102010509060108060103081b070b0705 82
    0x1100b51154000c0c240050042403490050036000e0814038020344c1d202690307000c0707035140950000280c1303046801542d006e0980d620120b6443c2e811604101c0001c41d102000813400354003406a0340b04520440da00341070a04100e28607000c1041d40d111074000c0022103d96440035911080c0340c0e900280250400311054420100c07041020300c5502c2c01040247c11f898120740600c81586d142c01c010384100c00040e00c180c000c0380618000181e42c590402e0b100512601c0c004115130380d4a01401090301d02120840c2051010b220140100001050180503e08541e01a50b01c00c0308000c007000a00000d090000707581006010020b4602d07070018000c42c6801c1ca4440c0c110b0351034225030325074600600b02d000b15075822000c69800c10640801030300046481c0d0348148149054805400300d64003281c1540c01400e02010652102e241071000749da028010a98012125401441158904074405594603c1803001403c907a20000e1560305540c01028029401c41050044030190341d84c40c803c10b00a503010342016a82e60041207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 99265719 1250 99264469 99264509
    0x903140415082505031806070e01170c0319020c0a080c0f0d020304060e03011803120b0315060409020d050a030203030403082412030403060e0f0111190e1206040c 71
    0x161299000c200000c3c100f10280e110140b0540303850380064819030081756202c00c48410380501300021813041489917102280c2c1007061001408507460035490b003959184001c20444d60841c00e1050340e5005111402a010200e802c0360500020301c2040d0342c4c10450300680d1450010710081c40020001d840340142141c2d00030740721409440d10794481119800c01600304005c1080500d01c5003900c20119503005000140d40c44140c2d005a03d00d80840344101c022a1003510351000318541c503c624a07100c401038010700384d409910030485040810080200e48195900c030710410035500c0d0060040303185540b0400719440000305d03050280d5a03070422941100014401000a010381e1188008d0341c000320030300d11003c2442d14841040110400c4900c010711034500c000d100001c00f00d40d144c014640810480c1014005500c4003051060035640c4001c090305207203604020030801001c2040e280d1643c00b00c107140003142d2110303002c00a4000f0700c3e038800401481c450740c0e0a210070700106005080448609802510f4594030071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 99266969 1250 99265719 99265741
    0x30c0a0203250e0a2702040b0f0f0d050a050304030b1006030b030a0f05100f0204050f0103060e0a2d020c0105060f030d0315050d0b07020c0906090109090314041508 72
    0x146003209419001e6808000c00080344440c6a0042c04508004c610841200320b24285d00d42488000380004d41d0799080c0b1419810680305140c1c03094001d0390800390306a00328000c01d442d4441c1c05100313800340c45034012a009228051001c20b500325804010340303540b01d60703c0c14000ba10001c15a0003010454a200000500a019100d60381e0080c030064064112811b980c0c681d400c4441101c1d0096925029802914607509241e10880703c034000304550041c0c81d241048180a070b8142c55041d614141441e00714207000482c007402d0060703400a095040424084860f518941c220000111a800c01010b10b608110800b0241d0b00601541f034000d030000c000565904081243c6602c2400300f032a010703007091589880c078520a03048030800c5a94080e00c02040340d6280041540e0b2048030b4410360b401c0f0007000c144854281d041c44803e22030141210786034614207003980064080401840390300f441558601c124002c150048030480391805185c0c0b205c944442d03039000b503880800b200c0c035440e1000400c0c00000404800032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 99268219 1250 99266969 99267013
    0x3040b0c0415030504020a030209010b04060305090606150705010f020d0207111509120708030301090e07080d02031207020a060f0e0c01050c030406031503080f0d0c02150609070c05030c0a0203 84
    0x64501d110b081d038001c0005400400c8083c10581c4c03c0440101c000c409610707101c0d1418000d251141c007580d42c0b140381440c020215a0050900c00450f084001882019a156110344071581003050400344e44000c54517200e4010900031a29680050000c998201c4004117075018001c040e0240055480d5403d6002c1001000c400d00e07803518170801000d12640d0024140b2034400412900c3c403c085414068445080360f183d60001d0f80309038a41d40c3c4a0391020280c0b17074180902d900901403100141604913000c50042c0d224001e2003240b01d102e240c0400041e050700c1c820414602c403141c108008104074116501184017800748000c541216200c0c803981012554030400c00c441d045403070326020754246402c00c9011405007039414031480c2501842030b0b001c004608884003d02c17000b8607250810355100a9000820b0070351780e44013105002e40d00f00030380268113012090300099001750b0880740403c99a83c0c0205c00e030b902e0071a0364400b40840c440450044003100b000039604030058000c4041300c2c1c102d8158000c441d0b01c500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 99269469 1250 99268219 99268229
    0x4202e0f023403080408011b020f0601090203070306050d060f0b0d03050304080307030204081006080c090601050714010f1a0405010f0305190302010b1309030806030615060f0412050303040b0c04 85
    0x142d010700641c0300305181e401110728041c1205031403a078985824601e030300a60030890440e5581c0c01c1443d4191003000020303000c11094006080d900300b1010045488101c140f02d80d8250b01c0d0000000b03420240f181c0e0198000e41401001d480102069017040e40013406010008007407607103032a540d5095454401c000c0b4404e10703815650107140d59110703a100c5082e50409403c11061540912020401d082c1c1070001050f6a80c441d503000030270500c3c0c0101545441491000c06004a0b126028490a664441c085444441d00401040c3c82b10410902c01401000a0440041928504440c1c1e601a5595502c0a500b07200115814005640c070ba110201d28030030540310080c200c4d800303046100c1040120150840c6010301900000690b4002c11000c10b20065980710049071660f80d90303a0384010076400207001c940044007500104840e00c0c028150a40c5640d841c0d2020380700e010013095106984074044101d6000d0f045000c80d8240c1881700d4503003a42d403038005030303030884440080d10000f0310b82040315816541115 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 99270719 1250 99269469 99269503
    0x901051b040b0d062d0501090b07020405060d050f0d1701050102070501180308120105030d0305190902030c12010b01080108010e0303040201030b01172d04202e0f02 72
    0xe00e0003054030710325480302070407460f03d60b201c40c00010402011006800c000c40315096040011001c0c1c03071324064600b4150015818000c61a2040c00941c5000c41580c240d2523044d1800031f201c2d2150b0002038800500301200505501c190056500703100000305940c015078800743c0381d80d4448034003810056002d800902400340140d0042c07004000ca0740c8112510001c118110fa40300c86e50070b03165200d41126610401c174400e40417814038010009400c0402101c20309c14a680760030070080c202000b0300e00210490030b0a400109072144010805d641d0140030360f20304404d004080d8a40d10701c0207a945800b8152207001c550200d4084400050f25003418020700544584500141d8596030f03483d401980104110000c442c100f003481030803203a90841c0c491105004e815510408542c640c0b156401d03030a03526007100504040c000081c01e0100137011420300d07680700e042c00d65480161012050118a07941d452640000900940340103002000404004122051899603210281c11b01c1e640026680d81c036580300f5105d118 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 99271969 1250 99270719 99270727
    0x2121006080712030f051605010c0f020a0308060915030609060604050601021c080c07020d03030b090c0c03071202010e0607030510150e040e031303080913150605070c120305030901051b 81
    0x24810f00e0f40350803625260030842d040103031580e10b07007103075898030502201c0038ac0d03480ea6682c1400380c00c001c0c840c0541042d4801032120040c641d40080440f6000740001d40241c041f0b90211311103a00c42000414003100190481d0007901d400b02c0680d66805080d10024002c03032414021504951003c10804600503969208001c0350020980031240b1a00007402100122018000c14006a480e42032000c3c10034000d0307402248136842c0e1020041c10280290810f1a0320404002c0e5010000c0e0100988a149400c0080800c108000b02400e0b8003400d641109412603024001c03c00a5036030301640140c1c0240455003c40d04450345600d58959000788400c0300704081b0301111a0f000c031b645002d40080405050034815607050102c0350041c80f040c018150021035105a0110702881c036804d04411b80305082118242c1845440001c01c440d2554414a0150f81c00300100090880305004e0000104001800c1200030045e29006a06004005801c1070381c00d00c2e0607508010109800b223004402d00f00702101400c601c01c0c0f034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 99273219 1250 99271969 99271973
    0x501090207083408030403080121030302090a090207050304081c080a05060d151a04151206200307321e1207020d050c0a030302090d02121006080712 65
    0x101c503030258007000d0b10560100c500203c00d0315081c00e014070a841148000e440e410305180141c25000160840e10400e6075604484a515040e043c90440554040c24016a01c004082c041802d890342500001034141c0006801000c2100000007002100e01c7c09040c0c1c2c0e2200904005d9203483c24100c8501000240518049072128060b6030119030005002854489114044e0382c1d06954810345a42210a40355658402e40340d014034a03128192300030b0b0803034003000780d0042d0402500b04041c0e280a90001c6040c241d244004004169015030944030f032080340c103400d0480343c2c800400350340d008642d940e0006520242c42c000da02401004141103c900001040036004c190f03954510f130380c20024101000756614030804010440420040c8412145204100a149000c0001034581181d40c1609010400c04011518010002140103404107606280150791a200100010b602595280002e03620101010030294203210003d0411080381203d0301c248a156620102c4d00e40b900d04520138811614941c4030a400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 99274469 1250 99273219 99273247
    0x5120c030601051c0902030114090f0309030d1b08070b06010905010804050a060527060402030c10020309060a1202160605011a19180f050103140603030a1d031609050109020708 77
    0x5290071401380003950b0801d03500000e003580d200300c00000b400c51500d002e04c03117401070900050b012400781c40d008500c0c0150000203c4c0d41d81e041c0110010070445160740d5027000885440c00f0507903184d0400c240075118001402e002096800030740f5a0340c0419005440092207500840b0500c2c811030300180078080301c1c0045e880748806841d00400c0404e250080340034400128070040300c07040721480c0b1940142114601441450b01e8450108507261058464580201d1459800021541900c406481840d2100542c0c601942c021500440840390540003040e03035400680aa4006651240100014402a60f954424000b130f6144d500600c0c00401d001c11080101561250100c0c40400386860f024840605410401d0b5070741c145500b11107030503824400100003d41e0b060140b0f805209001428980e98181140040e980313124540c060300602c1030b00090150f802003071001d0b01c83c0440c0042c0c1520705620055000d28040c00950117210703a018940340001c180f18110b407096410140e071100c112071800407001030040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 99275719 1250 99274469 99274507
    0x801140111031303080904050a09020a141306030308060f060a0219082203050c0105030f060d05120c030a03060f050f0919021602130b01090605070804120305120c03060105 75
    0x4026200412644468203c451090b00007180580e5003e41c55003401341c1000150b031009000c6088081c203058141015036581030800742160252056011082080c0c0c0104260500001111440d2494101d000081c0b681000207544121000c0781d90303494411070b1401b04a4035014200e00b14005a02050762840f440c5000403650803071500540c4901c0c148107404031500502d0524000020400c0108070007001008810041e864000d4003d007030913400c500c0c01c41003111191000030300d4103100e1a40c88101005110051002c100100000b0280c10f5965019081d095502c3d03101d1340130500041d18040c0005003500112400b2420707108000c00341c2419038a540208040588041d280200640d46080da0040e880b03560300c01004140440703400c0c00c42e2480d050042101d50540e42031500d40f691300b44000401c1a0780e10501c90310a90348141001e580b81c0e400750410368424061504481900480c018402d4203054119001d859048851a40700a403941c0c0d0860821031800203640c1c1c580401c1044c4801d00720076051401d08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 99276969 1250 99275719 99275747
    0x15090f0a11070804121208090c150c06040c050a0504050103051b03120307030f0e03030f1609080f07050307061403060f010c060f0912020a03120b1503070908010c08011401 75
    0x49800c0c0b99003038842c04110b901560080f812a00090301400401100c944415958012402e0255203460100c49403a03c0740c0c2c40e00c10140c400c1103403038882c101006024098411920300344049510b985018940088c0f41019800384500c00c150031030000902c1e19141c002c882c1a29030000250185180260200039140300441c401a0305020310b1091422088050300a18414403081d607000c01c1c80d03141030400e4800c071984141d4807042c42d0810003c20035030a0030f0b42c074080c1e040310523552848030884000c10126020f81440c0c010103001e019416410307200c4440010005c081d10422002d68504a95407007059400404920b801520b4171014000a6114903084044024000301810b00c20b885d0002c40d6a20000c4410703480c0d0749045580d54144080034000410f00f500307107009850000307003501d224070f4a026040902c0a0b81841d01c05032180d8011010342c41d0459902000f881440030942c0f130b8241194080c0000145005d07030211b0b90310302140e585441d8810950a4100e0341a4034441c0d07420340b51440115041c00000d080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 99278219 1250 99276969 99277001
    0xc281a0c0f0a050301050f010f0512041b030c05040f020306030706052a16080609120904020d020c0f0d0e01050d020a0e060301120506061806090a14040b15090f0a 71
    0x1c001c1500307280100526182c001070b42e880d0764960504040003042200804400c2c100900c1d0702c01e492a0785c0e048012910360329148132803400c143d50f0f54a850700c030000409000004a0041c2da0b000400c009038400c4980c1a900100c4080c400007000f9030303010040b404201d921947c581e01c69001004080d01403001450340080b840340d90604542c01302e40041c0d40c00114480c104056019600d103c515500d0303240800090258500036004038200b40b804c45655003119140841c00c003500007581c3c0e009940703c0e8103c95560605240554851401005098076840303003000402142c0120861500701074443d10564070040016181e05050888120004000307401002c2c849051020005806546682c1d070000755000702100b180d900c50800503443e0440c00c00002916403809640c01640390030718a40580345256000c0c009648034202c958801813070601030107843d51403c1c0400400401c3c0818003d007401107600c640e00c5002d600b4230941134078042c0a82c20780b0403075041c1204614100882c20300b840703580002403926141c6803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 99279469 1250 99278219 99278227
    0xd080307180f06110a110f040209181b0f04090203070201020d0e061009060f060f02190827010c021207030b0c130b0f07060c140c281a0c 60
    0xd100300480300035801c102d0049001e003004002c0c030799015540700c00c0e40c104640039000c40f1869076524a03114071a070002c503100b0617620030164140e455940c1070341c1402d64024507011030314000000c5000212001e58024806a407039142d65880300060201729075042034162078440c98646450301060082d0009000b05c0300710b540800268089030824050340300c0d95078040002d4641420311070352580300d1002c00e62000d0580c031300f0843c1c108030102048181c1c600f1560503041200c00e4480a5208905045d8401d00700a11007008007940740500810001030710a8809030403460800c074408503120240c6951608019001402d0a003c83e0018104143c0764001000060b085511441d140c1d5900e502e8820704450f20b002e242008100c84101d901208200f0000b0000307801e030a441c200c142c800c03558a510626001914072501c8480208203607100301d035003102c400c14101203e034544451500103034440070710981c4504566080d10940480b400b40101b402081ca0b03000702070719106050005001c0c100c0030001c00311142280148 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 99280575 1106 99279469 99279497
    0x405090705030712140d03020a03060b0f160c120b090105100302090f100b0c010f0b0109050105180301090210080a180b010b03150a0b0c0601090504020d080307 70
    0xc180030300156800d040c200e103a00d2009003c00814804c3c6d110303610344564507501031300ea0140076075810320000d6903d00c1419450b001c4c0302c040c0aa0040c082008114411034500c4801109118481d02000d240e80c40c0402c800c1141c0d01d6809442e4a07070b1034020049000400c3c89103541c070410b080d0746850180d0640d0081456500c004081843d03911000e800b0a0b82d11103a2044000105105d2100c20759075000c0883d141c2c01b0780000c4006141d52401e080321401558000d40095084d1201a03407642d050404081d682d412081101c440250555a11140c14002d612101a00312648600c4e1b00d4440087c00d2000b400c60817118481c85842c0307080399260700a400210402403041c11106880005a100d440f2061105401c035404c0070711980c4400d0f10740001891035404005044e81540100503298540e81e904c00c24025030308200d9009600520ba0300020380021052409035410904510300510f080c03c00d9 = true := by decide +kernel

theorem cover : BRFrame.Cov 99100719 99280575 := by
  have h0 := BRFrame.cov_init 99100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 99100719 ≤ n) (h2 : n < 99280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
