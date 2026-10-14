-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1174
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:36:13.368441+00:00
-- url     : https://prove2.me/submissions/fdb13894-aa65-43d6-b3a3-16dcff536d05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 210971223 ≤ n < 211151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 210972473 1250 210971223 210971237
    0x30302160c05040c020d0824031c080106020f03180d05010f2705030d0c02100903020c0a05010206042001090e1014030706020c041e0e0d02010e010c020a110d02130f0c 73
    0x295200802e07030391f00180425102010780395450001c1032a400c038140401e42c01416248488002c002d40701c4046c070000c3d01400015440c0000058990003c030b11002c00d02d0404002e14a840e424412031000096070341800e64012000d0109a00400ca0a102d106001d2440d01004516001c00142e14900d040d036000b00820444101290440058400401c4a000c1f00903098003040c80c190a4606034208000210091411340c2829200c50030940c0c0419a0400075034119030480501d51510012666281c017198000c0102c0c04080071051030020f0050180e4042c80c05140022080c1d44802070a102c102c0d050381c0b401c00400d8041e50500480e0350060301c0c0c10008005800511000e0b103880c2000703554a5100483d94007981d62414108205d0450548441e03c004162034248440d541da4140196038540d00355802006518140c3c002c0d04c4800180202103503401568010300c1c007030500f5218211348101e8442d41c0356000e00b4103004200140c50b40388a03c0545054920000790541c4021010000d598950508104008503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 210973723 1250 210972473 210972493
    0xf031a030f0d090506090a0911090a090203041505090d080916080705030c030c012118140c06041401080a1d160e060907030b031f150e04050a030c030302160c05040c02 73
    0x1482e6443c47c11a8604480410b11104c0d038544aa00d52054040c060b82200f920800402c0200c204e40040d8056071192442003501c86c1c0c0e0302d5907030040300e00554007138030b2a420121201102a108540064011034601c041d5006907440c0d44100d041c100540d4007038810b40e0400401046185403d0108070070040c41030f0060080c000c4072000081c45000503200da071094000e0000600042d0955511007820080c0d41610b01d0541c04c0182050401110202e88811aa104001d00c58915060501c144c0e001c07145054492005001403800540740340c42c0041c0201d10190ba07038079604c1c10141b138401c1114032411400d0301034003622901d0b000111030100c454200c40103d0115a081c8a1b46444070b692080d0b004c491841e00142d681d4440c00000c0c01c2c01030207007045000b5802c0b85c4c010090382080d0307841030001c2c8059410070100d8558a02502c44070402c100c9019010790084400100800d001d006002207562117807030014a421103000c0740c80b14005040300b05440b40104100c00b480b45040c90310900100e902e82c1c0c0001c00c48800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 210974973 1250 210973723 210973729
    0xc030606010f30060302040f1a0f030307050303040c06080702060108060c07020d0507080601051c0210050c030c0703080904050c090d140f0a060b030105160f031a030f0d09050609 78
    0x300d5410010400902051820798101120407100c1c002c070783c000540801510461009011300100d01040c0c2c811458130b12040d20b054650b00c143c68485000d07000b482c05402d260810090f14104104455815000170001003002800c01c6c0001c500c036a118203041c4922909111008103555002815030096502840050150041c0000d00350340c0701e01039480403545d540311031001c51401d041c400e0004040740f28031600803a1082000c03c00d03a050344e9007518004850b03ca04651181242e844c500040c4d0490400742c080e001c1c0c10305c184014408400740004403032078000301101c0300c0d01c0e00d0890703482500c9100700454440002e00d458000e194100c0c2d4404d500900b002800e00004001c07900622000300b20481000813903070005000d20540c99605951001d80741c03000351707504002016042012080c3e11a501e0003000070020300c1c600c0040e00300303036145603140b04030b000d03460505a0041018010541601031301c0d2090100c1643d0401ca20343c081c0148002501d1842d601c3c00b00a0491071091700101d00c129000d2010f24800e807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 210976223 1250 210974973 210974987
    0x3040305120f030a150308212d0709050d060203060310020705150415021201030c0f0b04090513060501030f0318050d0204050a021b070e010e060f1002010e0d0f020c03060601 76
    0x10720100c0003d813018200030503507170130645036000816001c1c01240000d500700c01014402c16a801000c3e4141050f50303000240c1940342102405010166180c0c00c80003035220034088429070059860070a0f10720161901c00288510181010032501286c0000401c41da40c1014400c000d41c44420507002c0d4100200c1e6500c1c940c664a8003070445001407448400101807041c880c19003008000083d004540d201912600301c9034140c0d09000a03074002c44000d10009080c8041c0e9101012116114030740fa003030038101192100580009010f02020400340000381011070014440c041c0254454114a61006281e03d80a8184030380318081508010000c041003180391103e0710760441d015411030303001071103540740340c035080080c01007208146001d09001502c01070b4401c0010500e00b07440780d00364140c0e011713030740c40c0070161402d00b040750440d801c03074110040582c440c00e00b448111007210032400046240b914400149241030103450360f4800282001d0005c010942c0c06119500c503041055028103118034180002820603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 210977473 1250 210976223 210976231
    0x60b03060d030f020c040f090b10032112060b0325090909020604030611030108060a020306060403080f2b06090207110f21011b0804030207061202040b0c03040305120f03 74
    0x4000b6054010f4a003510910005010600090080000248603042c54008116211048a1030000d06000c60100c42488100d10100d950140002d0701c1044070201794031421541000003401d00003003008140e008207841c041c06001c0d0803429081340c1c0300d240600c50206208a1140007000001e0f0381500c0e1301500390f000c464001940c0c040383c03001c11164503e1012901500c2281d2003d00210b160440000f0390500f0600258101c0d848070301240c080303441e55030780c00048ac0700a031032075a4403c4007048108005000c4001500700800e15402d5242809418120303605111100c14044c048413000e00141c556900261040030003400100d03104509007855981e40c203030f90b0803007449090301c0f588c001c4010b60580c1c1d0310b050840d942c00c0007441c040d00300001180c600c0d0b4080c00701200c07400c080c0e10041e40d001e85000d21400b0000e11440c1c25500070044a0b00d4050180c0e2414444010a04101d1302044041001000d0b10000c00031607004d140115611032440c2031441c00c01c01010041031542c80c0c100850300d001c1d00d1440030383c1c1d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 210978723 1250 210977473 210977477
    0x10506010305180607050901180810050c13030f02040608030c011d010207020d060e0a020d0602072006031b042714040818061207050c0d0f02210d0915060b03060d03 72
    0x983c410a4006850703e09d036000c81c09003003401c2003401091481c0c004c11030380041034021505102a450342e440038411030007010403036140010400d60410100355040058106940051310004d2440e0703e079140d0070b08540c0050031084045e07446440300d091455a00002c28070401c01d40000f1814a4295800106800c00b0242d024007020345449030612898001e00c01d120301d15500400505000c00589041c0010703400040041e150b032038004444c0078600c3d01189411a040b540100103601c2c583c1c4004000f02428469801c4603140e500600020880700b2040541044d82c0313462944240c1803040507880002596031007462003040e8001c8405100005030343c0d6068070041002051500d800d00203141c0450914024600159010744492040c095801c2d0000010220fa20069041e81c3c030001c5410307415100b80201444117801070780003d50b4003401d610308041c9030307092040248040349812415044013059400b0742e8400e4420003c2089403004000c200e06c9503c0040250070001401c41c0340200c000f0385010030950700902 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 210979973 1250 210978723 210978727
    0x105040302062505180904152403020603102c011a09060a0c0804030f0b0601020106080c060a030b1809071a0409050c120108031b1203070e0d060e01050601030518060705 74
    0xe804003c0489003620717604090400302881c68503041000188854060760b40c803035842d1000300011442d0368060326000f10390300c143e401005403540c4e09100c540d0740010041c1812020010001c035010040034031b002c1c510030056650401d40407400d080038030f101c1810b0b4040e40184a0315908031074028941c505a85420700304030343d000e17207880c8949825503401e111720400405151001030080200049500c10082580c0201003000351343c0e8030400164200e80c2c8a000d84034040e8400320a5145030b29001c80100f203045442d15011900e0100b10011031211100651800921a01402000803090040082c40010f0140e956000d0700e02c0e0074443e00c032250703101d24020442c0042d11100012807580744a0101d82d0710780401d684820300b540c2c0d501c2e2a146c4075040406070340d04c43c1101031400006c16600281018188540c94010391a5454440081c2d803610454402180c024101c02c000b2004180305201c0c50040d40e0b29940045050f10380007000500722034004041880d003001111044a0300b050008000e5032216640c2406a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 210981223 1250 210979973 210979987
    0xc060f09121e031f09020703030c05180405090c04050a0b0f0907080123030a05010c121112060f090403051206010f02031c290906010c02030d030f1506020105040302062505 75
    0x140b13030320b500756002c0419441c4c821400510300140c1c0c0d00070888240299010800e40f420781008480c5442020005e10b0380c501400690b8400d40341c254002c81e000503542044070008455000420180c0b58111f850980c460b42d5100546c01a040051507900784035822210040765103810708011b0a111010700405d40110206410626044441040032014000007011110b10230b9040c03030b01c503002e8500e001a08002605d6441f107030200709078500404201009940c0214140b810744290070303080d040020305141d03108504000e401c040340c46018081740643d000e580e809544280140d9400c20720784020b09100e042104541a03208110390102c151040000100c2080c0c580e41401081c032000b80031402480f0031420600d0043c0d081e5900d900914003411441541e50b4510f42ea00c960042d24880c404840203500750300040d900e000a07605c00d03406021b03054074040000a00f807050141003408068185c1240b000f60795031ba000c0c0300078507030100a52941704c0c0302e0002c0c003265460040e08105001c2024503184e0103021022903a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 210982473 1250 210981223 210981241
    0x3030f09061308060a110c0c04020d020f0a05070c050102120307030c09030b1807050604080a02102a02041b020304060e0d0218160c0305030606030a020c060f09121e03 73
    0x4402d5004104030011a894494031103d860b40340548802503403901d4002c541e008614100140c4000070802c40c090042c1000120500010394000f80c1480c4c80e442c4d00700003d20780401c00402400c44620326544103511401030303242c54041a010303034004a0642d4400d071104584030240c081201d0b80800d45117004101e0f1201104250340102d102e40000345082403070800c000c4488080280c948103034440c4400c90710110368440901c181d500c214003074516141c10040c10807026007442d03207845041003204d19044044a5821405806c83d074503a41007040c203150b01005003015840c2c14056990306e20841000761648101060000e95640b150b840f50714284804840c00c46d10395920400c01e01c10660f009041300c0f00500d066000c1c0c035075503c4200d898038044203240c00040d4040348902034501c0345030b5160f00c4681c51503ca06080205541004040c0c2caa807540030450030424101c288842406103422800b5808641041c125450038008148403a03001090b0610400b881000144e64081240d00c43c400016520b44840e003503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 210983723 1250 210982473 210982477
    0x1103010905060901020c0d030b0d02060a02100c020703060f051003201206010608010803041211040603050d0e01030b0f0906060d0e0610080c040c08191d0a1401020903030f0906 77
    0x40507086000e400200010003030103400400940c100300c026104030b4240030405408503801e811800341c100b0600c0c40000d0041c02e00c00010700403006a4011a50401e008003094000e40380b00250240050700030320750420801541d405031907803100d1451003c1c42140b410404210040c00244070251541c41081803155001c28090041c101c0c46001070b10040d2807500c1e907907485a030340c0002c0c41084d00050b00318000092600002c8203035420f0307079081e04400c104481d81e40c880103100400d41b0200c0e1380c402e940c0c0d000007000800400400f00c07084841d84410b01254a5000050200c0b000c01c58028060b1207240b60a0343d8941e260349181c1c0c1d02400c2110a2f40e21440803000b1007000740300602040125208100c2400070001c1550b00740750489403880e04540190410030144030556004c400000041800d13000480e1980110a881c0540c0318011400001c01d600c0032160301c80311004056401d00f842e00f11800001c1032210800500f600e00c44904005d6103000d43d03240100c2d07600d11480c3c00d0003181c41c0001c920405a0b590b9001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 210984973 1250 210983723 210983741
    0x71d13030e1302030612010c1b050c090406090605010608130f060b06070b04060e0a030512040f05030406030209030105061c03270612050a0501060806060d06090f02030601020f07080703110301 84
    0x280c01c11104003002e5000035881036800343d1040306c40e0140b4510002d41409206905c512980d2448900301320040c0f89604046440e508030b52a01401e41101c03280c2e1140c0541300e20a5000d000301040300c45c0103040020480e40103822020802c0700c01340400583c03100d403500307251201c0e60003100764401c2403040c00c02d18000c0041b101419400702e03002803100103000d1105040c2d4025401813104024080b540152030740d0f0b8603e8420001d000c034500f44440d190384950340c00c2d0158054011040105511910307514030b070031644690400004070340c1c00704200310141424401c181d4000d40644005050b4488209503048506040c2c1c00181000b074900031024032481c103024050302156040c005442103940f100c00161142e042d40980d845001d103030200085c040b480c5805518101c0704961a41c102a4455a040c083c143e8000c0710200030f8291a40c00001e542500ca110301f0b071001c052402c0058490515074002070810908401040a030b501030a014030003000013254150440360701021014400d1032480c007181c050942c81c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 210986223 1250 210984973 210984979
    0x209030601060504050907023c0a0c061b02060714030c01060603020a140909040b0c0c06040b01081603050d1d0909010b010909020a05040e090a0c140102071d13030e 72
    0x200001060b0360060082d0040d584122401080d503070300c4a00880c0c2d20101000e060103c032074019504407884054411003030f81110140994020311005039449072615070703407500441c8c880604820410400d42e201943d10406040c2280f4220f1220b00340d00050250301840101038a00c00c000c00c64484216001c1007201c407501d0300720f0024085075a5a42d0054003d401169522020440e07201403130407118124012107210031402000720485844580b212150314400910020a0708410080148580000c00401d4800c40c820001030f43c1540c10240114149441d442201400c07052445003440040d002240a203107204403458400c002e54807454040500321041140c0c550400b003418248401501c0c11340041e05d00480a0303c2c0c6c00c44041e9220180c030f049200310f08032070b00043cac402e0200713000c030460505a9640004244040301c00c125169140c12040b00f00035400424090480003c11115580500c040030080c03004520107628140390800300136040000405000c810b0040040c4141003501a000908207c4809 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 210987473 1250 210986223 210986233
    0x309012007120f030e06040501120e01150905041e0f060b0d08040303020c19060e01031a270a1401030228080a0201030b030304210807020411030a0e0f06011701020903 73
    0x7608040381207000c100c500b42d00040e00c400c10b05c421400c0c2582254229501a03403032282d218400c0c040ac800130500030180c0201552540c405008510401043c10f003e00508100000c00c0d040600d4215401102c41d442640040c0568507820049080c5108911000313030042e5012510100050000300a041e02840c004c0c40030350b0100d004014150700080781048118251040d12410343c3c01900c041000440d44035a030001419000e03548010751080c0c10016081c0541001c0304091030b80e01c1d001500b0704100302054540c5e0320790380e8043d000196008000036000031200f80c040111980307030341e0440810700701400043d0140704c2d10310303035030341d0184440d5481c640300e040c04070b05905100c2d214400152103880c1100103a0009041c43c5034110140f6001c000c46080302c0d18443c1d821003103508100c0c00d2884004000c8151140a0140403103009622503000b890750408410840540e2850400d6048046517090240300e42950b01080102d03081e5240003400740d054400700c0080d920140c140c20341c9139000e8400d035020035805000d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 210988723 1250 210987473 210987509
    0x50319230a03110f0a020603070e0103020f070f0210030504050705010309050f0a050c15030907090e0a0b090c090915041502040314240f01030219050915040e0309012007 74
    0x88002c43d41c15001e52001a1448002445072050341e400100030060b500c10410400f00b020103015a80b031010081e0706041c05814541e2500c01384007541c012200070342c0c4100880b081c0108500c0c0c0385582d0703201c20040e408c0802441c00d01c5d4480da5075a81d035078043d03a4141076541801c501840301c1008103800c004280402c6070301038001ca10745551183c0350380b4601070042110380d6900d42950f815000b96446080510000e164841c500013a880c09460b400d2043c12250144640300404600c0e403204030740c0304900784001031100d1b4800ea02406a10307c2e004040891a800c49007000c260680800300068000da00305031042d003165000e4030b8280092083c0d5000038001d07980140409102e040214203401402c42c0501d440980e06004003841d110f582040f200da5a404100c080180010302d024022030031240480710f11101e125440340c3c08900d0300c038019070307801400a03100402609035140a01401804400c81005503060080c1c003030000e04400160140115080682100310302c8403101000240c006014600380c0170a4080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 210989973 1250 210988723 210988727
    0x507080d0e1902060d2003090c0307060f0203030601080a020d0911040c050c06190908031305070b04080312250f02010c1409061315020c0a050319230a03 67
    0x41004029503600035000c00014205030008158010342d0003034013035450719030070488580051030061b1030841c03500e810307140c49032001c040040030318443c030100002810491403500405d1f140c0030031544100b00f0010503110140200d80d000c0143c0b6044903081c240f08007541c55410b050b401034050b4a40031210903150004500034003143c0c020f40216001d068800304804041c0c00000c864512480701901425402000404c0745c12440c0d1001c134001d44a0360100250ba00350b01c1d500c0b5070450703200b510a505a4902d130724a0300c06111081c484c1000030101e400320546030a00c1c06026580b68022010b401000040980000f1015088600950440400c400e000820b003070585201070300c810140143d1070300541c40e090fa00c401d40d41c001d0001280300c007410b4803158101200b02d000c01440d640001c1c18030281c05446000003c01003820b045c95450950fa68004d02348100f05a41800a0700382c617035101d10300c01e50202c004410700105100c07001c0b59003500242d0103103803a5005c9101c403000002010b80881e4500c10a00181c0501d9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 210991223 1250 210989973 210989981
    0x4030f030e0f190318050d02060304050307060501151e0f23160c0f050303120403121505030111090603040204150b0f040e011d0610180b030405010612031e0507080d 72
    0x2d13119860b03954284541e0400440031035000d00032190007640d010850005440c001d8082c40d4002c3c401c1044a1030214140d603807405480080e442210849171086465902a400c40341c6020901607005000d031014100440c000d00001c180a815814002c500425400d07114408002c0c6c8003080c030000245030b499140144181000000203020340d900c6600c280701203540031100303100000b1104001c004505120804180349204c880140c011000d106d40041c0a2881c51301501583c00081031242107284442d02c4c0030185400d42c0c449049841e1000010050b92035035030b417400309407a046034040d240040d110288401d20158036030141c00c15010860003203059400040140010000e50f81c4095814107607036641c0600d0309924280c0c1a0101c001d0140034001200781c10174005207110000a8039143c0080c0c0c4200e6810741c5c0701c10660f041004070390f5000041000b03100e0240201c90040072490810b06040b2020f4900400c03141507204200c0c00644546641c40c4094031032000d40b10582c0c0c1181d49ca540d141940701c6070b00014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 210992473 1250 210991223 210991273
    0x21903050612060406021803161401020307020a0312032c160501051c15170c010206070207062d020c030606090105061b01111303061404030f030e0f 65
    0x90905002503141d0910045001c20388003400002d22a5458503034035a4003940142014103101550247c04110a03901006007440c15a40c444482c01c540d801e1082c840803188a400c26a41035600400180d00140c85006011088079003000103141d00344034220b000c8014101d0f4001d140030b2003508081078280b540704480005000240300d400c480528036140c100c81041e101900c90070740800c034113000d0004003072658188218010050300d80003c82100ca1428079a1129440d08558070b550500119525100c00c200410101d90400b40024100c0785041c01d4029541e03505805007004001c0c5107105029002c111905100ca142060700780a0f0703a001c99150000d6440000c51442803091042c48041859810440d000c541a598060815464500780c0c0007080701110208110001941d615550210b0bd114608040c10b506004c4030b02c82c1c4480c41c40d50501d0b405895116111414007402e180c140300000340c20600740180d4130400d05010448841c1d0180f102d0400c0c0701c0311003914941c002c0780402c4ca08000084103030006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 210993723 1250 210992473 210992477
    0x60903190308071e080604020715020f090a0f210501020c0703140610050321040812070b070207060813021807031b03090807030c050325060506010c11040e0f010219 72
    0x80294102e0b142e44e4044032905420021807252804203d45003060340040030304c24020000c0301901070a01050108a0380a500c41c0540100049401d0a41c6c4c41e0145610009003d00c205905420303040c4080d1070031012000e452000c0400407000d08000704442901503a50a006940c203440324503549040491030b180703c44002078854080e0710001661204144050780582d08042e004100601d0080a652900039042c1000414070600b4400020502c0007000b070051000f4080c40c031240c43c0d104620f007003a29004050121400d540000c2d0b41481f01c0340d8004a0141d02440d40c0010304800c1c50940082020540140d88071000d10b40000c0c208690580c040e04040500541d83e01941042682080b00300d044412008004080ca0310130410300001ca03200e040000b00382c0d40120166441e101c0002c42c916460504c0d4030380c040c0c81c0501b40700e5031000e1122030720480340c3c850300a007400741c40003131140ea07085440e01c071944042d8442c0d6641d41d180c0550002c100031815440301400021540c42144101c155058480350341d02c000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 210994973 1250 210993723 210993737
    0x2010c0614010510021c210e0d0e0a0605120c0f0304050a0c12020307030b0a0204080a030207050306070306060804060c0908150f13030206010306020c0a2405100b0906090319030807 79
    0x242c80c51000803580c5d40e46e107001c2c044882d58002c0d010104c424400070104c13003500c1182030100800106842c4954000c0c81901c0004000700c51035550083e01c0b00320f007001414072441c032a250402c4030b030f40c02008550030400c80c0203039035485c1d64401080c46890b0044164103007a02f100803003004100100024001c03001c900400c0780c041d81c13941c1d0303024450b02c50060800080d0190492181000012401074415400050042d0007600307164440740c071186000c40c50402500141d0010b181000542818012103070080601c1c5001d0150364202200075281c54000b0340700800d00f50791401242d4200d8070404c0304e00064003458085e0341c500c10001c020b0708012081a00c2e02d01c1e129080304041030111114030b001c0f601d040c2c2c0c140c0150007143c1c42c5865000094002c2d40440503540516200381000503000000380c00100c44100e5080500c15a05c1d1b00c1d4400c503580281801c444601410043c0072007940c03201a14020300b02120300742d035100c00f40400302c0e05282c00c528019007803c1d44c42c4110000c164022841c0c5104030303d5170346c0707001e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 210996223 1250 210994973 210994999
    0x3040b010e090a020402090a05091003060507081b090411042709030e09040c03020306010605041d040302100c0905120105060102120a08010603090201020312010305010203090c0609090106050702010c06140105 91
    0x425400c1c241e82441c0c10707900180140005080c19000340c00320040040c00c2e0310400766030304045541c840080360800c0c20008030300300610800c40588115a0040000d1030801842e1600402c103800d001114002c60005200228004405d552244c02c24041907200001070342e1226510303c1442810b54101400d100309400e42e03002c80003080c4041c815006c0c0d0a400d69545030240c42d04405100702040081c20580d08401d9001020000da10104085402000c069499640d80c910304142c4a180c1c0c1c0d00c403040c02059041082c01c0c04086030740002c5038140c40344803038800a01c0700055181992140700c96441b0348d030400c44070500030740c3d0300ad0107500c19407041c0002c1e02234a807902019409401c0c40e00c0b64414041c08a0406c200501c03407944243e2080c0c25851040c01180c0c5001101e0340401c1e5a003400f40c0c0100e4aaa40003c01c01036620024441100d120034161422800c117407034040020011041401146c0c20080b02103610000d682c0b049055181031500503038100a20302c12416034500d000001d0240c0390040c40424004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 210997473 1250 210996223 210996239
    0x1401050a0611030a0c0c080601080604110f010e150417010b0103060f0303050f250b040302190302061906050d0c030c0b2701140a0207170d08010905091207030503040b01 74
    0x30040260304070b405146080d103800303070542d441d6000307160a40c1c0b10700301410045404075080000e07038003070142c00d0000c01040c58203140c80d03000a030108e03081a0240950280351261641c20080c41c0c60f420004680a2102d0306810031407070301c54025540f04162125100e041a0004501944000c4040c1d07800c2e40c1c140100d075100c042c000500c078120f100c001c000443c1003104100c4400c000000d0b10722076400500c11600e441e002070000310700d60880101500d018003030106020801d40c0400c10307000b0f4003038181440445900c0544010303455450041c6182001c4a03140c410240841055001c0d80c09404010013510000920f400c0200a582e0b1500044a0703a00080d00c02185040c400420740e0381846890301941010507000c008410216000d80c5054140f2440d0142032002403a150060720481c01c4950040403154030f02414102482903c0c0401c1700c20341c110660345141d0316840100c1906584642401241ca0b458030900307285003150785c83d00c0e250005004500002059070110083d40590b008000d034044690700d803d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 210998723 1250 210997473 210997487
    0x90b0105041407140c07270c2c030705030d0807030e06040c0506162a090e070608070903060923070609140f130912170c1b011401050a06 60
    0x5410110301600c81040310351306114001d03c6101c0c0c001042e6800590b0700c10401c0a01c140d00b072104c00200e1070806030342c034010f00a84101802080f481c42c1141030f03032103408040e40c00f02e0000f03100000490700301d807281c450355102004440d0003058042d00b1105a82405100108540c005803a203000090510a948100020001e00c1c203010365009142d40921a01d4001007060a40c0407645c2035001d0746480000c17001080030700c8c6164100084840c00d4883d54000e0000d10303079014025401c0b0039021803074018601c0f0b80712000075000c0700351859030400040d03039102c8103c00d45045400da80000e001c1410700c840c0b581003150000383c0745241d03480c0050030f4012013034200f80d080d01d1311003038003803040028070440301040401c447d8840200700c60405484100811180b02c0481e01c80d00041c4500c0045070341364106070701081504c1c2c8400000e84840c0c6040c101d54900321a013480c45c010040c290344042d2002042150302c0d056011171200340c0c0c6031250000c10546109a20a42e0612000d20401c4d104000d4a480042d186000382c0c0707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 210999973 1250 210998723 210998731
    0x70c0302060a0504151109030c011b02090402010203040806070905040e03090112050604060b0d052a040e060f03010507030e071e09020a0201060f034b05010f090b01050414 75
    0x81e09203659900d10700070007010014826500c016100304011050b82003441040e02c100c98034810140c2e01c034100410703d490521440c0d890b9041080e85a008025561441d070780c03803001503048a90511580340c0d800100e2640c080d0b03401040040c060341c0705020306684c01412000031564261400d010300008404815145d010740b8840c18081000060781540d00c00c400d0348407507400040100006695929003a00c50b8480d00100901d0602c2c5907201c081c4101e00900201c2e58080e50701e5100004200301e2440000c3c0c2642c0554880d00030001214408141250303502114441c0300310014000308500c0c40d241c400280a010a00750956880c01a03920108903002440141e8464068444000303503401d141c048444001c0d0b00c1003000c44115583d0b00c0e008203c211008220000450040041418124680034050300c0880106024030070b031410030980c00040c55240c2181c1e0321540f0400c6440030004824180240508168802050f09510b000d5540c400c020180303520030705844003038604010780d0203503840c6448184811342d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 211001223 1250 210999973 210999977
    0x8120105090a09080a0305041412030a0e0a0c0e070c0206030a0c080702010b0a050906150705070f0b0405220902060c1e010204080c060c0109210f140d0f061d0906070c03 74
    0x5d050300315402904a190440e00c91100034070b045101c44002d0782003140600b116580490004213001d80d800b45400b034500c8a8524501070034030044113564642901c54140300380300082c00c0c280b00040181c2c0c0524140d208194001d0001e5680c0d2a02c8040c4100805403002e001003c29035136008505803600c14890041c06070006048240804c2c2040100203005100805141e80f01c2c00c10307000200350107941d8002d07000c07040c481c4006180060400b9220690740049801960101e0814001002507517185a500500c0c00321480c00c501250381e0650103d0084c01c170345200a5004040007440c00c01000001504ca40da040d0b150103840c1c1284460304007127080c0d1080b48600d040e191b0000c0385260742840d04c04010310310807401c240001101e103015514000c50f401c00302c0c140c0c0c40d0710b1521002c60345440d42001c9403a588400914095143e84820030b00c010f41401142e20b1000390940d5074481c0c00303900c5081e91002d00a003510380d6000b403928502140300c20200104036441503c40c042c41d00880d84081c010400101d0706036040e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 211002473 1250 211001223 211001227
    0x9180103111309020d05030c190b0103060507051909150302120103080c1005040501060509090303091b0301140901200f07020609010306030b040311070f05031e0a08120105090a0908 79
    0xc1c041110b156108030000180075610700e0b480700103a844048103414203200360003560312447c80c4500207051190360b205050140000700540400035207113440140c15241d1010001440362030b202400c450710300070b940c02d9092a48580000107101500300705203204496a00700400c64070b020284080302640500c0019080400d003080040c00050414005026456000001c8511400341e0310b520030f00b503503c2540c0607101655600d009004c20b0800908156000801c900210318606010a24680d20300c0018000880c1402d2004642a40da8080d0081d40881415104c00f10203403c0610506000744925030101c2111070452024400b086001015501880145001d01c2c0c14202c01d502846295880000c28a0400d5a101404000036400d18040ca0042e0b0182c1d41d2514402811034034540b071704003070741c001448030140f40c2401c00050b500054403541c0401c1d91290000d8148400030251700d440039200b001400c02c08089480f08442e4a103c134028100c039022507172503c8640310940c084048459800000e032054400b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 211003723 1250 211002473 211002503
    0x3030a0509060d021201090f050a0203090a03080903090d051506010e0d0b07030612060c02060c090a1205070b27010305060607020108062e03050a0c05090d05011b0509180103 76
    0x480c01400950180f2000503181c102d8044000d0074040d02600000e1840b56985140521000f041c030030f0a51040c82040f00710b107981080c101c0c080d0740b00c0140c1c80082c1000820300010b00000024001d03502e480202411007000c0903d585440e82d20ba2018290f154004c107807440000b41503602c00e070b14420041304003412500d40f9080716203e1100350b100c020420010705449040001f500113400e8a4591440d0140b40005154460702d24024100364029045800e491808e00c410780301e954031148002c0855100444d40c0c2c150b031b0030328500070341130090310340c00216030b4000030405200b40305282900f41c400703a505000e00309100101c18015402c54070f041e40c0b800c0d0400418000240154010420741d500400c0041c0104a8403031a21f2260010b80035a0101d2040745111410710004581c06000741ca40007030391000300b03104014036000c0043c40d6004410340248140146045401807090039440281c01c2180b59003883d200031120f41014000307034880c5107000e001d0b0210040382e40c1024a20340d2840c1c1682c0d40110340e0f81d00400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 211004973 1250 211003723 211003729
    0x1a03014a060a030210140403050d17150328021f09090504030206160c150b010e091509180f1c0806030705040e070e010f090c0206010825120b040b0603030a0509 70
    0x80c51081c5500e0304102001f020010403810042c0850155007a51581107101d040d501c01c1c580003e01170260101c0035400e02940010341e80114a6540e2080d07089803100d880c008880d806680112441006034201700c01024101c00100002040ca040e05120f466400242e55203001190403180101c6019006070010340110301c82c504c0d605081c220180451800303002d0031045884040ca0368141050341020300f40e8a000c41030403540c200c100160640c200711018102482c1280101c8800c5078480f0a451081c0005d900103070302601403034100b0308103020000c1160f1061066440c50f99030341000ca07035100185000159036140280c81a134400b4484c000113409000d145e840e00050101800c002403c3c40130714042d90101107405481a403041d0b000b81072440054080e14608400314085074068166030301190091401888910f03000103080c91005400c2040d02d4502180030f80803a203014084d00301c10154036445d0240c800703000103101c01e130b03008a01585030582c40c4d0b00d402d0101a03403403113a45440c50100c1ea081c00711170401c1c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 211006223 1250 211004973 211004987
    0x50a120b120d03050105010e010c030813020612040602040317181201020417071401020d0801060c08070b04080705100501051011010204091e05011a03014a060a030210 73
    0x680503164111074254022030604241e410004180040d55840040280d0740c0e000c0703103c1c0c09a050a081000f54030546407801403400000034002101e02010040b84011502c0e00801c445500e0082500703201036090515000001e5402403205940d007007080705889013088241c9007141d01d400d1080c00c3e0940c510300c080c030510645001d0500251300c4c55509000008800e0840d080201c000f00c407043c00f030940306040100c00e0304600c41c2050814115404403d120900320b80000350b960645081c0d041c180e221101915000b0350521443c0c1c0d0091040c0c0310601800304210300303a006002640d21450660300d0003000e08001030b0450300c0c24400c81e40d11018080302d03500d000c2d000301da642c2e00c81404c000c005443c0c03d071580c81030010703030f882101d00f07102d54816141c4898042595101d0345001d030080c01488003070423004404840c401d002c180a030702d07080d0310041305031006c070041d80c2a60540005411810210f2003001108040c04200c05141c0c42d1b43e4219080c0001c2c40d0349003010800c0180c950041c808444032082410885201d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 211007473 1250 211006223 211006241
    0xd03080a090803090c091608190b031f140402010e10030f14011805090c1002010923100203060603040f0309030b3402071802090d0803090d050a12 64
    0x11a0391103107041c010822010085104e40361900003008481180c4040c8540c410b0010301911642080e070075640b0300d07a907100d000035030044054031642d0b85105080340c1541c0141003910034aa4517110f428110324080b0720303d0380407011115032804100240502500380b001140021640280000c2d804400881b031841d0004001c1014641858000750600c031080c185c40460f0381030b030300c04144050600d00412480b4180581190030b004254814403140c104480e4559503030110b101c003a4803804015007200c107614800d5201c1001c454103ca202c10408415101e08803509040b025684514099100b9081049260303008a034010340340501100e02d15074607903c0700d041c1c1c6610350004804101c070750b25002010400c2198000c0c040c108070b200c00c0c130f58030302030445003260a108a041003c0c1c68071030310202020550082080b0080300c600c06203940d1410800c2040d10002d104040d00144d0016243c641c0209000e0901701441c8180d600320125078400e00101c505803854010070542c80e00241101d40304404040f1503401c4a280 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 211008723 1250 211007473 211007491
    0x6050d090501050a1d0a0507210602031f0f060806060c01020f040b0310090e0a0201080403030e030406020c09070212030a090303091707050c060a02032a030a08010812090d0308 77
    0x1090281e070745509481080c0c4407002c1035500c0d100c503c00900340144904e070750681414014507400700a0b43d034158907a4842c6c030400c001006c2c02d4851040440702340701d88400b083d9201008555920b441c800c0d070702c241c40d900c5080d440000036410b004241000c45a45640c160368482d19003a0265650404100c510350040d401c0c4007055400340f140241d01000b0701c002c1c0c07024081c1c040025440c0e241c2a00d542c00a10250b07807100300c42c1400d05040c103160700c00c0803c40203180380d02071030000c5580d584c44c107040c2c0140c2061182c25410b4840041c000030110f5010039040c415480803900d0742296103030f9180c02ca036500c80e40111982060b0080022402215455001221051090401192501558079009455880c02d83c600b0703241680094440c0400109008800101d4421561182080b2008800968900980b034074941500326010103440c003044000040c05030a8605d000b02c90b80d881c4065002407052000388901310007441080c400c0150710f010716080ea01403941c0500640e00c0b1029a807411a403068000c0e1500e1340e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 211009973 1250 211008723 211008731
    0xc05180d020405040b190501060e040f1d0304030201090e0f06010c06110706021b0a0809010e04060b130303090f03030509060708090901080c1302070807020108060616061a01021606050d 81
    0x1625540110f0b440b490040070340d04614134226000701c03800c810755000700031018902001031100a4000102841c94042076400056201012410f41c3c010902038050003a040e007a160f01c80c08032400000100709513407007a42c0380d903049940c40da401e81c22401c066518810b10b0071030000184c41e651140354201d501c1030184001198150703a86408141c02e038010501a507042d90000788c0811801c0c0150000615a076550004019201c0d26480740c084501a0050040c10030080c0d1110820659843d084500544001c91003299510503150705100300c40f0b403601c0b0481c0495045440001c1c82c100045640c03003101d07015194246092584000c01c07403a5400750300101c030240c0051220040d81c0c0c136002d010a0103007104100a00d1446811800c0202d00f030710708040441c0440c0100521000143c124064030441c60742820811b6280c0c481c140024007900031003400e424032b499114401000d10111343c010a0003194940441d8004032a07031001280c0340d4010b0000e004041c91035840400c480c034403410003040d80c1101a60002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 211011223 1250 211009973 211009999
    0x10051c08030108030a0f05090d061e020d050a0b010f0e010c0c0b030a0603111518030a17041e2303070503011d1203010f060e15030708040b0a0c0518 65
    0xc09950000e0b001650103900c0420403814058000740100c400d074100b420440d040030800b10020b007908002c81070003801e4a84504801031454a40d210004100280ca04250746942d00402010b008050440713070400354500380b0040607840d501030011030040041c640d59620000c0201c00041d07880c10114402114140c1f4200c40c0000c6904072000a03501501d0f1036640454460b165080c14400711080c0040079105054080408a0004010007142d9100800680c024400c0c01403d00180c01c017000c41c40041d215480b03030340e0702c01c1c5003c06020090082d60b00203c01030581400010f002c45000074140506554451109082c40c11218500c0103130b10718040040c100c0700519242c002090a681080b18000c407040f80058403006c1e00201407014480240380c0800756415585480300303080002106c1d10426050080c1c4d0800ba03110340e102c5c0c5400495821906658039074904102c1802041684201c9060b81c81c0140d50f00821101c03001405503a101680c5a40d45500784054403038603042a40c038107070079180d018503800200c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 211012473 1250 211011223 211011233
    0xa0b130504050a0f1101080109021614030c070617091c0c11060a0c0c0e0c1617030408040e160822060c0809060a02070804090b0118080d030b030610051c 67
    0x7013400280714010345c1c0c10482d51480090403a100c181c00c0f0343d0101c1d0044c0100f0312100150100c04039869001001000d1811503450340d90700754410032031400414040c0ca80080340b150340052203d0002c1240e066001041c1c0e07500c1c010306443c2c02005050700c1c5a0b41e03900c003001c050075100c0d6000116441c054030318405881c4104002800300da110365104400b262000008900348400c00402400901c1c0e282c079004002e150045454000744a40e8000c0314000154403124024402814402c4d1404840c0a080c4e0703540381068100380320650090710500030707030043c114001006035041503005842d594003600c824031140c6460540340040b040d40405c908043c086403c6120101718240941d0015400c291151546400c0c00700c5820309158000b0703e21544940100902d00000e400502201c0899a081d90001164a121b80040f10300c8015545540401d848281010a0801d00460004a0760303555450410141002e00305054440383c04561205048107020000c00140c02c201c03030b400e00045540300b81060301d007040740c0e40c2d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 211013723 1250 211012473 211012493
    0x14210604060b060c1b0f0f0901151e12061203090e15060708030403030c26070e1e0103050a090c03080c011d0a02030705040603082a0a15050a0b130504050a 68
    0x145201204454a44480300e00b0000f0b003490404c801a500000c000c1d0a59010812114040c8102c4d004ac403040d480e4107107641d102d245d0803100b144480620701400c0324007140c0140918505420f020070350303160501c00191550020084220310b6419100c00080034508a554010044010300403003958101c4680800d01b80da443c03005055551180805c6074590401d8100107003265446a401d80500c00d21000c00c02482000e0101c9170084800c2101d81d90041e91004ca04403208900c2c100c49507004114507040a02c80d00c0c014039564001c8800303070780c208216610007100005540051202801e851859101030001c541490001c24500304082e0001c0303a400070f09440203c88043c011002241500310059650852905203e40c2c00100070840e018030099007942c885184c00c0c803078117a0110704a5103000004481468040e5044100400c00f0203480c1480010b09000001c000e00743e20840b422403503c400a0f040100c0d41c0300e2111006406032502510441300d04502c0010007028005941911400300200e00003081e80c24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 211014973 1250 211013723 211013743
    0x210605040c030e010605060f030a050703110f070b060a0b070602070206041a13080105040c090b03211c06060915030b03060a020406020c01080610050a090f14210604060b060c 76
    0x1400189a810f030b92862401c5860031303086184180c5042094030400c030704203003e490304403921b588000340917200c81b40141c004142c1030a4113503000b0800b0802e802d140e04d8042c09060841d00a901040c21a46ea40d0204491a000c601840c0301a85061000501103111039002c1c0070b1542c8042c2c101e45c41c00e9194001480c3d0140390048200500f440091400140d5402141c40d800521061009024504295440d2182400c1600490320015175400c401501c540d000c22a04030700b035404800c426285503800c61079202c0ca0b0301155502c1040c1e15040c0c0e000031040e8040c4900300849903940d650b42e00c2c042c20401290651302880c0c848108150f2100160040c80c1e030144903540c00780c44a5000143c0c0c40e483c1520182c1091014034941d414404d41c40200030300c50b180c0d20000950b0501c103182c20359840d0700da80702c161000000c070341005170800710304c072030215101607040b5030144140000c603140701c1c2c10340000200303c1105003c42242d0105412242c003150000d11950070201302c5110052509090106a812480c0341c25050030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 211016223 1250 211014973 211014977
    0xe1501090f1211121e070e041103030910050301051e030a060506061306020106030201090e04050a03080612100501140613050108060d02060c0606130b0303120612060c0c0d050307210605040c 83
    0x90003c00b251111000804400440035002d03001040c5000451031011f440208050400c45461995400380d40d800d0080b140a4000180702c1a50f05070b0b8184014120f0f002406024003801e114804103c460050320320f0610f01010040003800c10340d2040d40c6c3e210240c0405405c40e80c02c101c0500a10440e80410311024001d0200c590000079828910700005010341c00ca580b15081d140c9200c03081c032020900100d07c0102c0b031074040c182911503850740c10119041d201c82c103050344220b0040f00c41e030072030680e5603801c424100c60b8100008070000000c1000c0118501c03c050400324070380602e2404211650150710982c2e88104014a01140b0701e00f1038011500a43c880c142800840d002502002941e00c0d2020044100241d82e147c1007002d0662440402d40e244900e5101c440c0d04074100700010026070b96400c00440d20780009085e101c03581000f0780c80000c650054052203049002d05002d00b00e0320340c4100103807480340d4026a540c0b0b0521a0240132055440c090310746861069486078400303d02c03a180da014107900c2c20b0040d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 211017473 1250 211016223 211016233
    0x602010905010606090605160201140414090618070e1c030509031002090112090c0801060b030106022404240c020a05150610270e1501090f121112 64
    0x746080c40c00c480607a04030f0014404421000d1040c503a00109440e5071081d26008441c6030981da00041c1c40b190031001c0621191000000d001c50394a00d807072038407010100140d030130300204e4443d0b0003000304040840005003001c1251070f00107400301d480b03140072812601001d4251100c2004800900050200203070080e0041040047c484005080410450340c1580080d030b011420322806100080504000041100040d901c411840c41800403801540001b044c841c0f008000c61a40c7d007880f0506500f0034841d0201502134564911056030000b098400141001000c009603075407281c0c0d589148104041071880c0704c60a102c2e084480c4090303841580c2d0a401c07a5002454100194680145840e00300e0f4800412559000288445525100a001d500c02603a003040c41000c0b050085050260000d01d2400759091400c1d00c000a840f00348d64a054050a801020320600d4000704005503088180d078820024140417295040200c120780f951050890f034480c06203249680700d40710014100b40b003c100c0a00309a001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 211018723 1250 211017473 211017491
    0x9100c0609200a08060c0a14190f031a04020309190b160207140108090a06090803060103060e060307140102101b032a030f1e1b11100b011701060201 65
    0x40e28403081e40c00312040302c03882d03442814102ca95440d4440504920a1488085500c62019008d1381103840c082a07030304007450f201d103400500c0120060300c0f01407200210380c55020801c01c0c03d100b40170b801c05004207003a0040c084040c4000f400300070741c402800d5240e1070040c400210b000c1c46410b2600201076004035040021810040c9a940e0312800350303602c0500303543c0510b00c20421012415104291181d09081c400c240d642c030b641c06142401c040880080005107040f284104024840000d18090242079804105d17681d16140442003400c0181c1c0c88035419807103818100070606650802d24650388041c41031ba8010040b545529013515850040c1c1d206038001c0412808409600d40300c1c4c0140d002589005e480040311001240d6021521068080109600e6210784800303d14950008c84202c6510980a14801750b9465840000e10040000c01c016082c20f41d1920030140c03090700c281c0e00c1622008050300c446c07058030380a500140641a4198140321001030701c0b40320b42000d058141d00800d0340d6000030070380c404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 211019973 1250 211018723 211018763
    0x5060105010333050a0605040602060a02070b1f05060f030609070507020d080c0106031a070f02010c1b020a050d0515060a1a030a0f15050a08070b09100c0609 69
    0x160021410989401c03883c422800902c41c0f50540c81c004403022100c05007401e90000b0b82826250007203600800d5084001510301d07030002c018000c813910340e42070f80d2540d190a07000c4026403041041c0681401140408507111001c007a402d4492442e01111544543d5990004200e0a0304044100c0b081c07410040704000450a11256155020741c4500c1c0003480e00056900007aa12804050050074849020654030601d0a0950000000e1a0890030104c40d02c0c82c903038620460b00342c0807158540041c9210444680c010300500070b4920102c100d803a812246a0401241c4224682d038000980c0c0c0050000d40028041d02d0b00d40c040b00c90a40658042e21902411038440050036101415142c055510514100711010b4111a2000100c0304240cc0c295261030700320704407010309102c4103012043e03803030002401d00d0784c0c0555002400b225000d0700c1c0b1400a1b41e41d900083e40342d445501c0780f080c1d118002c006a20b030714074140f0400c3c540c001c41e50400c001400001e4603800700321180c1003004c0700d4401c81015041e00840e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 211021223 1250 211019973 211019983
    0xe0f10051005031911040603110f0102011103070c03031b020d110606010903020d020301020909010b0418020423120102030c07020a12020102101a06030423070308040608060604031a0405 81
    0x90724001038a2030540703000c01103607551616403000d65041d03442c020b0403c10072a8000841400300001002801159200d0030004c4503580903050881c0329492510601400754010b0103002000c46602e403816003103503208003058640d00f1644504900b016074403403411400c5a01c81002c803007240c889500401824003005070140103030f20504c02c03440442e4001d008022123603a00200b150260795040d50942554491403010901a00a0041d1164041d00410010130101c05c0030f8040d004a480760f44c0050340841d820aa440e00304d2017903014644815040781d480c180d81103a4a140c000301c2c510080d1040d5005056010394508a8000741c4404204140008015003545013510300c0c64007034500d24865120700c255650001c2d640b603010114607503030035840c1d0f09001c800c43d14203030404e101018054003807a40c900d05442d18421409640c1104080ca5051446c049074004d00026181c060381d03401150304c4c1c642401c0580c00c1d40c80c0c0c0b4008040c258084000c0101000080080c070894038480f8203080d60201d981001e1502900b1b06c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 211022473 1250 211021223 211021231
    0x61d0601120c0506070201030e030a031a0d030206010308091206010b130e2e080109030e03010e0601080607030f1104091407050310050409060b0603190c020312010e0702010e0f1005 79
    0xc0d12410403480125164202c540210303003045515513a2415903100680141c0480c4807030b901140000305005042980541180015012001c6140e10141400d41040040031180402170010392040b8010310004200d0b5009044040c4000e00c1c2c3c1e0052f1551001c0c0d2854410243c200c030030340c030001281d85003400001d090781c06c01410840b41a89018904000b480d4425413840309000c1c05000788450803656001031a0b01071000e0b045030002030100d000720b800d014040341d10800107180207619101c0001002c9002085207416a07044101514254540600890103040d292950311804d5030354500a40c21090880002c20040c40040d80104820903503550b825200d1200500500c14420b0030420040c507072120f015454240d03942210001008411403d100000348001480715400050003c140140c5042c0d44082c0b5a458181e2034092100070300061049032039010307018807030649020040040c008106003826042d40700f00f8510000802c45c400d5040c451078890143d1240a864003d088000ca02076000d004140c2d00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 211023723 1250 211022473 211022489
    0xf08060406031e020406090c0914030a08070b0c040e010f0603050901110d090614010906030b01120206091c0f120207090b060403030f0c0609080909060103090507170307061d0601 78
    0xc00c51643c0c5805081202c00a08005031490f5050148115075684c4d02030310190120560802c1500f280c90405004a080c0d03000c0c00e00f0003201004650b115150015000200c6540404018100080c03996140c0103260302401592240b032062001090001565001d103009000c100c4001030040d140103009003c44902520102c1541d04014a01c0340c0c56031000102c403c0c0641400c0c001890a80e83e085c104010101c245003420141040e03000019a14036982180d003c2c0d80c002d80102c032460360786010030b500640c10380c00003d400a609100024180c0351400e602d80041100c41141d8003443c006654161001c110400100c2e0340c286002d20607038070103904200450292034a000204403000f240f600064580c0a9840010200800700c001507080c14030030b0b20580300300c643c000d005004040342850110709139044488410302800c90600040c0d0550f12a000b40c1d6055500071002c4c0c242c031410044a030700c0001d1500c01d8481d091108200307080000d500307031242012100e180c016007085465141c01e55414881c1c1070b402403031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 211024973 1250 211023723 211023731
    0x3051b01051b010c0f1d0108070203070605160f08150d0c03020d0f0c060e0307090c02010e0703030c0204050601030c120509031c0204090e03090303191404090e062202040203090c04020a0f080604 85
    0x704406c2070410400c6060340909000f503290340e843c18101d195204001009095505240511900d02040140582000e50705d490355100c034084007404070b0304070b00c084586840071003084400b8512820814200c002441c05441c1c28480c2c0703a125004584040c5c1045021a2910290310f462010700411800117406040d00d89000c08800b0502c40029581d0341d1315020f54030b401d650310001024441c1c000d40c0500c0c1d10480013019a59069a2410003610704003000c030040e80250300300f10000300c456210b40303e6184a08043c1e1a6a55550350b4000b80b071001701350003405c40810380320400c6680072400c80c0c1481000c00c00002280541c0e581e0510101500b46c03220050703003810700e50080c0240350a60343c01206585503048000c41c14140c10a95030000c60303030101c070850b42114550001030045007010b400d0308000d00c400307482c900720343d4161120b070707820080f03070034850400d1081d0841c144003e401031800740c0085411184072411a610301c245040024101d911810041c00882c9900c4601040580c000c01d02581c444000c640c100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 211026223 1250 211024973 211024997
    0x6060522060e090910110c1204120f0c05040216060e06010b27060d0e0d020d021216061802030715050d0903020a0b0f06040e01020403051b01051b010c0f 67
    0x2d000c0707001d00c1000750703c1904000005110701100308030400e131440c51a407041c0181c04040b0301940340d41c3e11000281c407c0d070258414113a03603200440c1c221000c80d240e0341c0c4840f142c07041940396a80c0300405401d080b82d0018000340e00140c40d65590000d840300d00754043e40030424401d185402c40440d00011074104694000303400400c8403001c40d505482400d03440405030224521000d40c20301c600d0601c4450268405c42c01b082d4841000c84503400b59014010080803a1041e20000b1300582c0e039003e180c0c0343c40b8016409070240b68441038421000d03080301c80d108540c800400c1c009a4800f0151083c0400e05e0b00d500214980040c1546000c00030ba90062840070420a0309800c010340050480c812a202c510075503441381081030401d8420071820341c1594100401421a081181e0549034100f0117444640c4100d0400c0915030380c1c640706100f00c9044a9106004041074081d101d90300482d000503a00c05810320100b0b2080e039030642245007003c0466035940c00001080800640050232542001e4251403c12400c0c444071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 211027473 1250 211026223 211026227
    0x212010b030115093f030804060f1503080d1e0c0912030c1b0504050406050718081e0c13021e0436020c151810020304150606052206 58
    0x201d41c0c02c41c0800e94240d0130420401420045da071079440340005001101e80b0311428590700c0303034031680618072543c4c2c1804400b240c441018107440ea95020f0040301e80c0c45810070000525140c004141c00000c014012464036402903000316503403002001215940d841f514040d21050344506600041d180404c41484000b00343e0710000e02c002400d03c0020301d5041101d286100e0080088165002880b0090007072000349032a14000d405810f0554265022070600c10345005001c0003202400c1c10744075218014031041d0103094038100f0388800a01c03510a41d004040d03a07186151107081d401048850400005070b5600404001851038008142c180c4800202c284000d100754100040702c0110211204a408000700308640d070201c0d1070080d20b284211440c030001b000c002c0d0560205014070b0b1610140f5002c0308503a0b81440c09024140a030342c1411103900124200309502903140e025580140c001c2a40c0030603046074054203001ca171641e0b00300c080072540225100301c020700c40a1b03052011800c4100d40241c1c0d00d00d80000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 211028723 1250 211027473 211027499
    0x31202070f090b0303091c05010506040b1e180709030308011a22180f0605030102092d0307060305060310090332030c0712080115080403030212010b03011509 69
    0xa5a004162183c01d08100ca42c0d08100340c40c04040007c150315880f02ca103128819690f40d151008803401c0d42000b00180c0d091a0901c03e5104038100540705040c0c2c40c020703075070380c2d046400c480c0d000301c0d4000c59800c00d8107044150a82c0341780c49605261a141c1d101d0b030071420041c1204a050b40210302c04070858000e6010220440c0c2a00d010346d0510040d1424494089225400f00103182c22140c001040051480f80e41d8046801c070707900c00480c0e50170820a10391030388185406d0380320ba28412500400110942d003006c0c6200b110302500d0030074603400207016610507400070f410005941d02420001743c90704180021454148605d0240680e044010841d559140d580a04600e9407800e20690240c4900702540b0142d1f07008200d07071701d420407040310695a850030310700300f0040ea008240700f91494480c00c502012414001c02d0440e040c0c1d80507440074110800301d8241140c1e45c5000070004c80405800380100c8200c044501e0f00300d030192107000b9a0945940c140090002c20000c0d903000c4a0030001d40100400074009a0700d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 211029973 1250 211028723 211028729
    0x204030303020c211e0c0d0201021e03010f0b090303040b030903040e150a030312090c030f1a0c1206040b030604121103040b0318010912080a050c03040308060d05010b19031202070f 79
    0x542c0203202001e000450107401810001c2d03599001c0d0707c81c24a030781c1d0b83c10360040200810b184042660441007901d000700350b0000340501d4003503441c040c000740801c11222000e0b01c0509001011646481e0300c410825030142c0090303e40854591020605001c3d984400c440180d2001ea0400d460980300201c0300000c2418030a4400641030001c0210131400c0d004064101d20042e540080c21903248598900d8078800e0a500c8110580f01406810914003c1c400c83d001141d0045600c010f10f5806c00d54500100c940300d280c098800744d4081c2d56031108071000e4400b804100c0c4a680181280e1055036000314000e0070310500400c61000307a4104000070300007450303820148c0b40c200d1103443d482410707010003443c25030051840030b2018008900286940c040c0640c418a200d10508203880c042c001922054604c00d00342c00107540080205000700d000500b01e042003007903a019a0b0091001050721810440130514554000000031100c040040043c02804000c03000e04e0302641c0684000c024075032500d0f0800b992108140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 211031223 1250 211029973 211029997
    0x50312060102160b07060c0203070f032615040f0b0112200c101112010b0723030702030f0303150909030409110301080f0106050f0402090d060204030303020c21 70
    0x58041005644204043c4000c81420404442d0707080d00d03811000c5250b0000c600c12650241880284030000b44040161400303582d00c03500c0c48002c400540e900307840100345501c0d81c090551011910454607040840a5070040b50881a010511144201404299000b01c0c46030750026007492400c00141c3d07030107100000001d88450303001031044040b41d99800d010210f10194020b0840115144490b05804100000c82c810024410000d122100840c0b01013402402c00b80640310368201e004224411f000302c0180340304c40c0300d440b40c803000444040d880e1044900d0000d1380a401c1c0d0012540c83c0440c03c040210700720180d1254015421131030888000c00c00000040400c1d8051003144010406a02d4100141d801401a420090103074512569040e0700c560400d10030000305101e61000c21500c44418070401050722005081d0740124440401404042d501c500000d94008641c001ea1381c002c502c1038805403004d50722a580160307807241801d504074038020300c4102547c0c50071038a00301e04144030705110890341c10f20a25 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 211032473 1250 211031223 211031257
    0x10090b0306061c0602070b040501140915010303050a0507140601090f050114040b0607061a090604091736011e05030f060105070233090d1103032a190503 67
    0x1442e11358068043c171000144440000014441040019003240c00c1038503222003503000d103035207035440b10740d03999055030900c031120080c10010f202203480b4100420580c003243c2003031450409190703180c2c005541240da007006590421001070002c0c3d4454010076009050708031061020394100a00f00c1d000148610010b0b10980da601b05811032500c6120030b89414541084e4100310207507041e06910030143c46624640d101d019081d000591924103403044803e50340d041420103040e054400c0b1351001c1940964200d061109110290040000d2030814441200f94644041d070f00300384e050300000d8080e4107074403a114402d42c004d4200240f41c0387e00805407682301d06064100c201c00c0e1518401070f00d00c3e10500b14069040803411200801060101e0349480c80340000f403016001030842c07084001e40d02d014030399420390b10841401d500030102d0403840140841850040035070340381500d4541d80344141c6030b9242c08806280045213044003640401e02401c01c44500c00c9501e45c80810705607075031544070b02c00d00a00c12850004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 211033723 1250 211032473 211032529
    0x10504052b05030c0634090b040605090a060c0206030c0a1404091407050a0905061308190c0f0303210b040c030b130c0e12010e010510090b030606 64
    0x80510351400300500300050001c03000d180e00b00741d80c4907806501c019440c1d105010201e0b0007041d0180c0e2040ca03c4051903103420544007028070740821100c02c600d0013070030040e00407808034400030084020001403c050b01c400d5901c52400c400e0081140312640440300b840007403207980c805030311000c04582d440300724480410703900e00c40300c1c0e825944429031680c9180c21100118000c1400718440c3c2c030480c1c0c4410141c40581090351a504102c1d114400d81c408880010400031040000303040020244c000c5502007000320103142e0711099080d01c0c0404003d0020b484031500d050540034010000074500c094054490680b415605686014118004070401c1c2d9059100303114401c4048800d582c0108954140188284042c07450058002c01800740d00f016140300785007c04511881038507900c02d69800d83c02c40c0d1600d90000000da0300f04426140c400d403a2001a54a460801c0104542032141e180b0601c8179944040900d2305110350142200c46840c1802d01962040003807182c02c0c1c3e644551a030142402d904841c1036585 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 211034973 1250 211033723 211033759
    0x60510050712030609020d0506030c040510090e010f1802150307080c0d0207060603150b030303060a21050706090e0708070210180204060f1509031e0f08120910090201050405 76
    0x525070702c1700c418188003068510a5587c45e42001e4007074034048040b100200d1103201004100d6100b95285407234042c1d195000c20005a458111140307105080c000010302e0b540c00f0f12804165140245c000680c1c070142d100160840c54000b1099a9100280004500b10b26000d100504060750244c0b00130889000411040300260329a011100101c0d400307030050051a9980c90454182c02001d40c2c003011031410810340480e1800e000054904c69240101498400d41ca0b100d40462401c00c60444525000e4161075181d010a10811000004081d0780d5038001c219403515045c1c0d105008050070b00786c10040304200340b00100d0343c0010101c03210760303110000060540320744c0003403003d540c0b080310009c1d0441e060600001e10282400400011582000e800081c1c04074050000c07110401640001080782c40704075103590f0380d20840f52450103503d21506072500c50b8046500e458801d5040065030300100380c0600100604080700303001a00c81e810451600f804505034540c0041c01500444c0140c0307000c0d2003406101c52100c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 211036223 1250 211034973 211034981
    0x19240b04060f26130f1104050109110711010e09010b03071d100e031c0302030a0c090b07110307050603040506040c0f050307060815040e07080c0a061b060e0f010e0106051005071203 79
    0x654007040d001411426494a4040ca8000006c407a100314503000001130108440d01a403070002120514092a010440c0d84450070400300f0006941085007180b10700c011600c1c1d030094607010701520b8594076140d00d0140c00c01030040c0d25080c1400900c00d19040c81c1e10850700c0d000c01c480c80d0000e25003080b15000010201091421442c070403900f0072030343c20340036984019030107a0080d070159841c01c2e000c0c81080c1402d50280c82c000304502ca10360660b803040260790082011544560005031004090751034545c0e41c1ca0002d0550b82083c2c50580c1c0541142092000b009520010400104001242a440305103007030002504c807035403440b8050600070000000351880c1c1401d124020103040043c8100100040507002c10313610041c900515220f482540c0c100807407441c00070304507400c4500d940d0340c070801100d10307409a01102c100d424040750032a40302e440040c0c1f8110305104010030400c20100005180d00c034414603d00b51042a03000502a01d442e04904220b1980001240c40036500100080307485004072108034010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 211037473 1250 211036223 211036261
    0x150905130209160206130c050114040306050a020301060e3f070305030c0607030203010b04060f11101b0912030804140a06090c090519240b04060f26 65
    0xb007240d00003005160f1040380010102c0c0c0d1551350032110700d0750b41c1188503469080c007a4400f5200a5060703004009035031140141441c0c804880703524605155503666500241c0798191a42402e9030340100050000c03c1c1d002011a03111141101c001540303c001d111000d00102002c021030b04902c6003111180618651485060724000c1004120b0b00d26a689080c8180c80c1d03000390305607a01a0042101140c1e88038880e0081e20f042c0c516003504545414a420404d031a08082c042e0b5040a0180701c0548409100b002d1200340e140c42003040010070758440c400b81ea0019020f400402a0501003400406d204010300740c00610080e96241c240f6005030b032140e0801c4003600301003048000d01c41c07151285060030413040f90400c01078603105440c20f20b10142c82c0c20710002034520071914605c1c140e8054681600c80f02c40b94103d1480040d1b400d030031060081c800d42000d40d0702c0145410000c842a4000380410a89512401c040c4104000c0e10300300c140b9a4400d4207440c030303000b2a001000100703002580410433480310101403041d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 211038723 1250 211037473 211037479
    0x290a031407050405070507200d0816020a0602010c0203090405060616030203090102010b010c03081b0f0a030e0609011103010e040c180b010801080319050f0d15090f1509051302 77
    0x35a400000311581c0d2240503002d0280114148804201403502603000c0e11011603001100225680c00f0342d0060008a00c04242c4681c0045480000f0300410a8000107101c401c2c0c007480300071803200c017600602c05201d42a0b406038007160b2400e1810140154040156101802e04882c0800c6940300c8200081c01e03030041c00c01d480342c40c0130502a010201030f000401010705110030b03002445103041000c0103448440b007a080140101d21a000060141c0c0180c1900701492010001c0c1103003000820050710002c0d40001c2501800302c6e581d145148120390701084a00c3e4020a2100240003016880400210f203010610980f0607441d40034001c101000480c5c6546030190400c0c10b040881e500c1a940305e080649080548103011507041e000100c3c10000120489042c40c22039002c1a694404010040b2000d038084070115810102c14844444184140e0007000880000c01809179170b900c2c10031003606c3c110368070000c031803807c0c40c603100c0c20b8100800d061040c00e00321658094005070300c0e9036800054410380074610380258 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 211039973 1250 211038723 211038743
    0xd1a0907090315230a09060501080703031713020d08211e010302100f2001060611010209010f030b01030b0d0b0106020f0c0303031305030f0d0209040c0201290a03 71
    0x285003644035084508507809508200d507500000d0780701c8000c071200d207104c0b685680c04190707108a54030203c0e5915500400000c0002a4850b41c981b100da0403034a003a00142e11640141004205160380031a03503003c4030f0a8406441c0081c205000a10b40318400400000d01441889003058240303c2d61a0640300040031020001941c69038030b0301642c0403a00e0407035030240740581d590304000b40078500d4040b442c16030744d000d070150f0454180000e0644180e29560000000c20804682c408608000b0f115034a20b1100c0070f01c0049071650400398003405c0810034482d440c15582c8140400704282ea80003803441e08005980c180001c04200e5040124043c00c1141c030392907003060030840928100305004440c141221041c6d070030344814070742d00403042e521003500c0544a985540280085120490307075085201800d0300c40c404881c1760542c24001815940c00022540c070215601007400d000d00c1c14030f0300486010003000e100070005040c44c400030300035003810490f03c108400d228400c40c0703c8544070401c40d040035603085000b0003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 211041223 1250 211039973 211039981
    0x2104030522030201030c0215060402091c060b0108161202031021020a05150706050a09021002100c050405100807030e010f0506040f022107020c060304060b090108120d1a09 75
    0x1400514602c01207000914000c50703100350500c0460311040c1c01600340240702407500e4203010003019400010500340e10400c1038148184096028210118451064001244035049a0005810520000c00c021040c11024510140c0e1940c04983c041a05d030700c4080041e00d0b500e80030060861302c40107401041d9180000d000e81c0c0e154840003149210110310032102c90720b02c43d4603242441565204164200142d420910000c0006038a03504260f9200d5006d83c1d000030207042070340001c0c460000000002c009a0020705907410845118061000c00e5849818040e2074070b89480d0126050f6016021a0820488804049070308148240c2040c81c020200c0d6009020300c1d091041c241e070080400b91502c5210f1494000c000300c100034940242c5100366450360300413a059650420100c85001c1c002c00480c11801580303081c40e25030b40e442010714000c0d4010500002d040d074a010030301590f590180c000308000d500c0035608400214400741141c5071100804e0001c1246651a90040207440240f2507890348010198200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 211042473 1250 211041223 211041277
    0x60112030513170d0f052d040e09060c0901140706200a0e03010c02030a0c05030f070b010e090604110103091b030308060112020702060403110613030302030d0e010221040305 76
    0x2401840c24041c00c1c4c4103c02c4903090182c8030b1074981c03501d54002c540140040682000350202c01c010b401c0000206070441d41e0340c1a41d62820354071540200342e0000300c03c402e106d030714002004003035881840784440c40e10f01281c55002900c50f401811240084600016604042025582003076045050f5019842c0801140c102c502c032980e04071000c01e80002d14031035040c40617031805000701c50340c04c24030741c01441c50038480340703011994012100303800c1d070b03880c4820081c1d1380800302000000c1c15218004c404a4030a5410003660243c00700019150440341e611007403d100208030796046e072100d014400d090015080e54a860310400072100c8400070783d403010300d1032800004e064100306010310509090341c40343d18081800b04040304900500304041d41090007400700f44001841c4c050406d90b5690000d00060404030501040c031600503050f001100103801c04659000848014007402029a10b0000203504008055424035240ca24281c03002c9000390401c0c02040905001f0000c442c4000780c0094032030f00420100544c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 211043723 1250 211042473 211042499
    0x13021002010b122107080c030301080a140610150210150302040c0206040b04061a060d0c032f07060b092509080303060f0f040e06010f1205060112030513 67
    0xa0b240030b90ba106110b0559200c2c0494000e842000000a07144140c80300714080c2d50319004284101c0c1c1c60a401c00400e480e204e0104040c60080c000c8400420303030800340d0300d4110b0a0001680e016031080d403204060081403a40e40003244240c5c1d2414111501c002c00304e010072880c080045080074000c502d8141e103840b008050f4500039064900030f9606116818002804903613039a02120041d2010010101080000d401134001040c040313884030f203000285c038200e00050701a502000c50611440d50700d242c80b048039a0980103c4043c044030484140c465000380c40e05600f0190040c1e0f014800103000101e9404100840d80b2081c0121800f900103851840c20f40b19140300c2d2a051024407403082c209105050b2418171070b139610703000d0310155006903082d62151410300400701524040964000c0701c160902035a529940710b900c42e580c0c140c2000300815407410744480c0201d001904004ca01c040030780100c41c0400c1000400a0444242e4a00e0b8400301e00c42d400c0c100c03124090210130000203002518002808070140301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 211044973 1250 211043723 211043741
    0x60b030402091308070b100f091b05041a03060d0c080d0305010b0702060406030c021507050a08010f030305030613020403050a0807050c0406030c140604030507090c1d0303121302100201 81
    0x3500c0065441d80c0c0943c10000d4014040280894401c1252000044480d81800d0f0881c4000d030320b540c0c000c0d8172200a0030b504001504400d15480d0b0b910f12141623010b440a80740302c0b20810b03051462920f8100f208030070150095401c002460348001022440a0b180c0e81c1e52a021603812410062b0a00c1d01c4084954903802e281c541d440019051800104031508110100c07a40d480d4000c02c0750740343c1403420342d0507009062409103020a5015003141d40d9003203240800060322a18040e90790300e81c0c410b40c1c00006061110107800c82c201c1080c900c0d0007800040c1d04801201d030002021520492080c50405c032400c0071380f0031600700600500541c0f00c61020400303184041c004081c401c13404e0b10b52a104410600044504912018004414070a02080400804050b1900010024000618058480c1c03070340c038070b8050f440d400b4000040d600c60001c0f00d001e40c003d0340c100094170500010001142c100001903036901409c49103210b025055004a18007607528060340303040b258080d254115110b4070719030103402000401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 211046223 1250 211044973 211044979
    0x1e04020c07050901080106050f040903030f1a10080105090403050310030507030b0103060f1401030201030c050c03040e010f0b03071707050c1510080a0b0c0c190803012c0a09020a09060b030402 84
    0x1030004617002c20180509000d0701d40150012011840402c20480904100c00055080c135598046107801c8161602842d45401414603080a2200840b01840124030385078041d1400c010100380140700c1580d600300d4242d0810b4241c41c00c940c42e504d4000d07118040801540c002080791107550000400c105490910303d040701d008000070006180300d0300c519030a68000b500070301002c0200c0d0300184010742c025800752400e000e49203440b5003020302d0701201624541c0301e60842c00080880500400c400401e1100150203040c12900d440d0039424002009040c1c1070640c150000584501d000051045200d07805459030341e1a481c0445000000c403911a80d4040c1d8141c800c04041000d180001c19107103030020706403107104d40c880e07a40c40540e6141d40c05220b050300051030380c19032806108022407108a01c401c00e542d0307150203101c6055030303540342851802040f0407081c1d034080c00c408417580448400d0982005180d01c040900070100e400621071000924101403600010300c0903140c000080b9510800e080a140300e10310036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 211047473 1250 211046223 211046239
    0x30f07061101140408092b05060603010b0105070b0a0903141207020f1b010315240f03050618040201030f11040303120203010e072012030405100b010203091e04020c0705 74
    0x100100c0d40143c1d411140500b41c0c100401001d03515050800002107104000d00e80211401d50181e2000640c8901240c1500e643e4004070a010440c0b13001c0c800c450045800342021803402c8940d0f030b9100382c890700c000d002d0075481d41d50300300342414107024800035528024428000f598842411484040300c0e40c090742d10307000600c281e01c0c140451042c0041c040c08d84045001c480c17003155045c000110090411944c1c1c6012020012800281c140303c0c401c0758400c10300d080322031010f1185c81c83e100104503140300800401058140310030b01c0300c4da0301d07032503101001408040442030242d038441c00180c024050a5500f09011854240c40d0300903001d103103003c0c000340d911070758445d0000544241d0010980c0420b01405a0a11650300442e00c03c034001e00010145102c1e05040b040d080c0100fa00080c14a4000c501100c40450300200700703c1000301c180240d64451508440400402d90341000003552801050030140c090040e058901098000d406800040590010300a55070b4003c0142581c1e1503602d644901070081c034030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 211048723 1250 211047473 211047491
    0x61809130318050901170f0a0606051804080409091a01030b15060301180504170403060b13090c03081308070f2606040807020d0b150906010f05090906030f07061101 72
    0x3540d6080b01c000502556599007012407a00e00090030105801d403c6c07107001f0508060780700c280141c0940c0740c01100002080c030f24040902400401d10380359245039000540c01c01001074020700640c3c058401e0107100140902103440c0a801200b002c900c031001003802c00c4000020031840e161514421010ba40980948909980600500340020700841c44414607640d1404000c0081e075000641c4140180c07000f28078400140520707101035006030026916542c45203544192800d01e50782040300301d14008020001c58400d6118031002d1207560000824611002075105d80c0c5101929a44c1c002c1c0140409850201e603940c3c0c46004000c0140c843d00804001c0201c039000c120b030000d14000e65100c0210041d1126943d5540c4019444d440f00f40c00302c2c0d02500c0e04424001040f52080c5151050143c0e00d13620700c1e11802d480c100020a10001d142c0c5040107005140c204d6100e62103000c3e9a9200c00a5442940c651601c80009003840d558004405030342c841c00740c0010f211640848000c2000514400802441003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 211049973 1250 211048723 211048757
    0x914070e03150a20120105030c0f06031f05060406020106170f150402010c081801031409120708041d0f01050f1008070306050a2303031303020618091303 67
    0xb64041c0300300c281c8402c500010361001d42d035411540307428031845140030149905402c2a0142e030444c160440d02c3c0540300b0b0050000f4101080702d507582000460b80800c0107100000081d585210041c0020351260411141042c60206804500060070000309403075100d60315544024003c0c0414815141c5170740c10589100030b40a8042151410510b00340007421021401040c207550038040a0012410405030708407540100f400d4070040c18508500044145041c540c43c00010160b510901241d100702c510401030000150000400c68001d80b03080c0202c1d0f0701d603031850410700c00d18003c0342d00081036052642c207110305e01d0004885017840b58002d101c0e90055a603c4a081c8a10400c1c0c08040b00d42200328420400080c1c5c0c05500c007607521820501d030100d84552150085030107101c01d81c1c0001a041410003140240c5030300d01c01c02401d494002d40007107080107007841054041035260701c4040d0040c00d00180507401409000170000c00302c0e0740a010401c840c20f1110700c00440b1400380c801500091405080088114 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 211051223 1250 211049973 211049983
    0xb011e180e30180d0326010e1024030b060d02130f060207050409060b0d050706020706080f0a0e03070b04030804060605040203070c02040f0b03240f190c090914070e03 73
    0x201d0484044007411401c0044c07009641400c50240d00b0702000c1403050b58030501c4041c2d40ca00c5c003a80000d1340c2165500d4441805100034014120b1041081000001d00c030000a00f002e840b040c0511402401040884007015401000c03075102840e084900019105000030403500206040e4155510500009617911500d0540780c2c00b07401004010307000940104068902138019104949c010280020502c042c400051404400d2440444131504880010026590188000001008607007004120b40c68261035003e4944401071886003240e03510100e8540100c0208180c4429507030081c0020410b08060074041c2c0542d800b21000c40d005800e040010481e41454002d60340620b45584814500203455404c01c000340040420711085107644000d100140c5c0d9041120100740c14103883d03103110065842408085062000707143d0500180c1944c288640c446000c0780340c21124520501c00620403203c410304841e071019903031007104618240142800a02030186885025600c030381c69010300c034034000301490344070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 211052473 1250 211051223 211051237
    0x6031e061c0303090809060705060f090d0804021903080a020c030c010309260c01180515010303020a0803100b1809013807080a0503040b011e180e30 65
    0x600c01d0400140042c1c040d0b00200c101c1e0344a40051030401e003d00001c074525812448042d00e0390362021081c0700b154100c01702481d070003a07148000307070100520070341000e02300c0c05018000030b0295104660452290017000028005103512600040d520300d40000004e40d00c15462443c41d00c00c2c02241d1103005950301900c0764610b9654044400701509000388454819801d10300b54aa204031020080c0b040d481c0b03002e00c54540c134811480f8104d200404142000e51030000110b5400102c078082000600c003203900021108002640205c44941d20b42d20704061000140e59a8414401140f000c2903100410708000020010b020782940ea41c40141e80e10403070100454035405210a44606980e14403c0394983c14161081c24014000e0051403e00941c1d0b8045942d44410120780c00984044244020049142e42007401010f050040021040b0741180510040b0f804e48210940d03540442d0b008505506645c100400d81c003420429070340e0300b52036024049500105c4401c840480d1200000d6844080354110503903042c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 211053723 1250 211052473 211052509
    0x1506030601030b1306061703070b060d02030322081b090702210a051e070210020102120a0507020c420403081c090f1202192006031e06 59
    0x1603d40207400c400c1c1484c5000140e4045072038860100e5103651824045400f80002e000556907802d003420080c0c3c000c880600b8040c464080350085030f0241c0d07000800c0ea50700304e0242584884070100001d604000c0c0c08103074080c43e000d000c1c8000d00c206c2c003140304803111061013003580d00d60400d80e1a01405c03130b01d0b051541ea084040300c154040c141801034110000c1c291000c000d041c0103190248412405d0862440c0c0450840c03070300c0002500c8021402c0400114030700c030358180000d5050603a0001d80d0758411500034100880c090f55800018440d0780b00f00190703040c90f5030142c42100921035281100308204000d07540c0a1030841c0303440c800b0b505840c0c0d0071041a003e1010444e42800c2a0555448004550054030351014031042c0e000d05c841030f02d031240f007002481881502c080e041011079203846c2d00850b803480800415504091103541070100c001c9208841c180d03108441c1c1c1c0d6280e070141c4456041050038010203400c140007104000d04117640c12401c0c6c048650300c0f0381c809183d80c0d40b9030030420242d0140815a503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 211054973 1250 211053723 211053743
    0x10e0109030f30080f0c0c01020d0504061401060c02061305060d0f150803070b07090f080f07050f0d0210030204091104051c050d1d1c030801050a150e180405150603060103 75
    0x488445e1100219812008002e038182c9042121540c2d903003a0782200802140c602d81d520203210800010348901c2c8120600107034a54101e626100c005018200c211001a000d0140058400c1c2c1103100c0541440c017a04005110315120310700031807548002d02c10f088000f5481341c5001c00080700101d00a010204990041c03004610382812a500d242182c40040e005500b07101301c0079000310b0890743d0200284050010080100217035014072a240d450014a40c0c802c0d0300500480a00f0306aa45a003100c900942c0e80603180c401c421b014900d4110024899640034180080c070340810180b20341c4280b0010400c072982100c805d2641100c14007458091042000002c296600541800c45007078007410482224004a03a040802038507000003003041e02250b0440c00880c0300321a10490f0406400c101c0c0301e40584001d50306000d499040104141280307440032218414070a0824030300c00c06507281c2c218800412400012100141024a4100d5680ca4106941014410309100280d054180028894100c0e90485c80c080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 211056223 1250 211054973 211054981
    0x50a06050705011d1c080105150c10021305030c090112120201060b07030c03080a0507022a120705030f060402060403240507080612030903070302010e0109030f3008 72
    0x16485a00c9403008503955500e0b0740c04c105090480d00304010071281550094180f01c4040115003c00c500c000b40301909010114005001d0740e1501560a075043e425000c500c1c0d5134040c0700001e149070038003404513902554000180c0d42c0790315080398500000c4941c1a0704444103042d2204c00c101c00810b0900480410340a8000b480000c500001c0c03160355400d98071b0000140c80b90311192804416031041c0f5054002c140d24510103803c043d0311038101a40001100f104000f54105000029242d840003501803041c2d550022581071034800180780c101c00c82a008100c0e0103070030350a00c41a51684110701c2a07921a010350040e0315144240890110f02c0785d54002d084629060039507580889040c44041144103500500d101d0311601d6905100d141e01a1180d501c5101e803a140c59070400c2100f12000c01551102c2d0400e00c01540706482c00550300042c2e960900341500d070041241c2c012103200203268030141010080c020040180f02c4a05024203801a0300144401c00015460380c1042c80d4044400440010724030310001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 211057473 1250 211056223 211056227
    0x9050d05031e0109021b0a0f0201050d3b0d0503060d030905040c0e040e03071709121b010e12060f04020619031508060c030a0c1b151401050a06 63
    0x7194002d54006070088a030348148102085504260060341a85500084152120b880c0001592000c681b600051580009581e43d10307180800001000b814401c000c00d026422103d00e400c48000c0b040b6010b0b4010307404032231040710703616140404101c4124150030590801c4034080030500c001c4500050f2561480e6849000038020320641c80407054040019501000c140780d591401003940031612a5221440d000010080008076100044083d00a030300c00c00c001000101c08107110500b084041502946070000c1c1804201e007120000d5000c3d13890b001e103050324a0605480c4410806d9800c0030781c0c4001d442503450007400000c0c906605005020f03840000001d5141c01c219034029030192014003d2810403040f00c400300058061103440e8000b003901d602c0c0c0540c1406c0d14907040307001001400000c020504024040040c01d21014050802041d119070505031201d020b03468101368546180024540340311781d8200840204803a80180e51294105405a290b04040a080b1410717500e0007010050054900001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 211058723 1250 211057473 211057477
    0x30c12170c1309050a05190c0c020405090a0b04080d0b0a050109030209060a032003060903250c0e010e06010807020705031c09050402040602060106110d0806060a1107150e030109050d05 81
    0x20480ba850814003000c0b0307180c081402200e0044100c0c440c00700390350401d046011181d43e58403809a2080d880c0106a01d015a40a14142d0f80305805448c00039041d102c500050303083c4000c4103006040189410144020041064021300b50418201e008100c507886200c1080b000400707174410180091a01c4100f030000d840c00180843e000030008203400c0341140d81e961140c0040307a24803c0b003036003245040c812008a040900110392f100b1008805180360000503419007090001d0205100701c03200c0007a5580701000b102c07460f103d000e070859a91603041503079151003000c00d42c0412a4a180000d08640c0410800341c0000380360b1040c1c070b1b801006070040f21518401e101c0354180c840c408104102400c040041c1c40c0d25203100800250140d0b501a20a81d030429074054801104001c43c504075a014481072403140303a1061216400402c2141c15030b0756903007060400c940010701ca04920140b8010000000307040d1100105102c240f12035522228a10421034040500302d5004241c05016900000174020f01a489100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 211059973 1250 211058723 211058737
    0xb1303020f0a0f060f1b0906030e0c1c05031209010f0c08040b07050903100906150e1306020f0d1401050f03150a02030408041d07081b0909090712030c12170c 69
    0x500000c1c5154400c00c0c0000500002c00031b8400f09183d168113000c4941e040c004e0301e1a03011544000c00b1410b480c44041401103400122070302a0041581c290800c2210502c111000a02c0b01080c1c2009400d100c02250300820b620010075403124503141ea840f04241c001c01200340300d0394100c03440d40c1056640000941d455400100d00707075494050044e4402c032005a82c0302c1c0d03803d4240503440010301c0902035040d007000700000d900181c05030f4205c0c5e01041021030b00748075111201c070740c0240007603260a98143c0030212030040d1050001c0e0a400c0c800c04e0140d1644d422450f90403100b04507541c00d03c40170080c0030f2544441d24414100300780101000003a201c0c80e5280c0045070054031030b0900a24060f1f541d405a60f01c449407a2030405c84401000600c2034a46c0d00c1010950072400c12415540041c512070850000c0d0310400755103600a00641c00024081101402454000d03c00000c003020200310b589001030222004400485044929a003102c3c0b9451003241c034466000504c07807000081341c541e0040400180c00c152 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 211061223 1250 211059973 211060001
    0xa1b0e192007080c0106050a03120509040207140307021315050d080405090711070605090105040302040906060801020307030606140c06040f060917071214041802070b1303020f0a0f06 80
    0x4000c0311006001d080007069035034012a5401d4036850080840c0d400d49a26900c92442002c10103030074000308001c003214013846020703030400d6a950603c900101f40a801106009081c0e02c414000c0e2500d80c2e0404001052014402c07190310b50915040214402103c0c2c0c951240f441d0010030702024041801c000c49044034060050303900c0c605140d41c900014441100c12a0210002885180503050142040020401503c0c0a0074194200600c1306c00003403e500a610010b8451a100c1c0c0c20032060121503404100a4000fa800940d17070b0349003c0b04050042e01681c803881000403544041411304090b1202580c2500c5001000740416072030355202d074590741d04d9159041d160302d6511855800001d01c00c0b104001920740c0c0f000f0581d2122058106620500e003035442c003505100031780d840864110002400c0340c09880c040e07014684400c03001e8580b0b4000b400381ca84010405c45810041c0b1944400b0b000d8400f00d07580c80b0b030342251902c00d55002c2e95516100b809100805c40d0740c00b41135203000501d10ba0400ca4040c0310310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 211062473 1250 211061223 211061261
    0x3170702130213050114092209050a030302040f050409020306041101021212010518040515100b0c210705030301181b0804140f03030402210a1b0e19 65
    0x54103001260b0240c60f2111501c442e04400700f00b6560842c0444400070300c0c1c0c243c12410801020086005032404400300860000c40e0181c0342940c0700c15500a4120640110449040303007401d150160080d40a80104008004e40040005071841c050003900c0003c1d5020b0701602e1940c0382e954810075101c079100c2655056000c2d0048802c0008641e0019110001d400c52440380c45504d400e050104c01d0b200401880111151901080003241c0006103803100350b602d00c40d0100d5030380d64140813549150807a422002421074005807403107402400289105003060410784035080c2c40c030565883c400034805c3c14001002a042800108415a0701008540100e03a20550101e489015044550603140514007298017007038942e414042400760103981c6465142038179008000c862000b01c1003556901000748024441d0040216017521900e4501e041c5044000041c00c4864903000340c60702d60307007200000343c0d00401d0499002c400a822800408058080c20800101c00040c40000d6003070b401618289800c010800a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 211063723 1250 211062473 211062499
    0x50105190905130603061103090316112707020a020d110109050405070309050d111203060d06020307120b03060705040b16021e031c09060c030e0409240603170702 71
    0x10340842c0000c1c0800e20f072000201e1505618000c021128010301011740c0074000e00810094071400800c4400701c546140514000309006d00d0078080d000c0903000c1c10754000c401107490218040032121100001c094401040f01d450307403990000c176a10b44a0701c0b40a0b52004110b8103c50114041c1c80b90348038a4031040c0b400c15803040c1c07100040340984900380c840e980002e80c0d6902a07024044144000300102c0c2e40c1d407810510003c02030194582d51208e8442c51041c0c04c00001c003055940d52440030b0010501c0c1c1c4040f0664603480c2c1000c000d40480005009030040134100070a1400301c2c500400c01c103104003840d03280d00e0f06207801d26800101641100303208080e48181480000096030b01d20034100300121b83c0410000b4001c40400c107142c03e040090782c0700a8a070300c0280340f54481942040d000c6043e11101c0c64a0a4400c0c0c05080403606403a403543e007150810b1038001c6203010301040b11400100340c6040d01900c000b07490480000000c4070542e00c0081e09a180701c45007441c0c000306c03820041c0300703150004120544d4001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 211064973 1250 211063723 211063729
    0x30921070e10052d0405010b040603110702100c020a1d07030b1207030503090111010e03070f0302031b0703030906050a0f1805090f0906010803040b0307030b180709031b050105190905 80
    0x503c6000741e000001011000300340401c04c0c00954041c1c4003080d0740a02c0107502d4204400c0c21401035002e04070503d511036184040b00030101c0d0550b03440940007402e000282c0c4919201501000000c841a80100359840d0b0218480c1124407000e010320f100c514003103c540e501c0c20301c100e00511081220b2648801c40b011070740c10768038041100002450060004d03582c3c0303d80c590005005041e100c211201241d0409200501011000c415100c003d40c10441c049005111494220304510481c00c0c81841000c505107003010021002408100f138a11a40f50000030a172240f00c02da41c0740c060341203a90b00203407841d0f000b84d00045c0b0640740c440d05031000e626602001525400050820300d4200c4441c2640706c1c1c48802c00400307850400c101c6005200d60000b651805003004c0042d03449100c011301900901d0b88403501413003141c590208408a10060409200b09030800d540002c104001038481038588843c580700c1807140d1841800c0070346c1118030503101c1e00d1805255403c4458604c0c6550041d90500414041c0055140c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 211066223 1250 211064973 211064989
    0x405060f030a0b0f06010f080103170f0a0f031d061803041d22030503010b0f0f03040b0603070e0c070204090c0504020403030f03180308010b09120f030921070e1005 72
    0x144210440c1e03d803494516501c1403100c40080540b0b040281040400c40300a070082c04d07440c10750f90403c0f441c5860310405110014140304207108041c00b03100000703202d00303008d0b03210b01e42854048503030f41c0510088100021034041c242c4807040c686a036030040c9020802030341c240841d00d00031355482000d0303a050650b58071800341c918150742d0141513484241810405c110010207a40b420568040c50421040c0007142c5000b08103000c14059003c903080001444180e000303111042d14218405a10b21690340d103040e01d41840112002c0d150039000e8800c101002c41e07a01c06c100712451050120f000401d080828079000c0001511600200b0754603100030071804146500c3d40c1c001400503500039103901d031205102080042c21a8404602c03c41c44000405d000030000b030380565860b0459902d61400798a0b910b421001583c070001500042c0143c0c425503031480300068010010b03040c1d90608603014101c84101c00d58001c004900052510300b1500f003404107000c0034104500241d08610b03520000b82506403141c01103040c2ca = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 211067473 1250 211066223 211066243
    0x20406080109020307050306010b0406080a0e0303011211041e090303060504051f060905010507020f060c060a051609210311030a021f0c0c03080705130e090d110307020405060f03 78
    0xa81d442e0350b0600190b003410005178004000aa0041c900d42d1700d0720f4002c140790700450180344d0421406c080843c0c001440350300244503403102002602d6880d41e48080201103560514000c0312407500e0701c02c44000034030700380c0304c0e0038580c0c81c11351400c041d50500182c507100240341e8444201c042c5542c1d01400303e015103440c4a442e200d0041d15204580e5520f485100164081c0c40f80e00c80d504100c2d00c29014401c0f40d9200c410355190550585060344481c06150021310f8a0284000e0000f09102d18400c00844680780d0300028092000001c030400c10b0309000070202c82605843c0a51030a801a80e00c80182c820b80d10750090400360f000345002d10000c8400000c071402d503407004da03802005900050001074040c00130b00e6048042c4204007420000c03222591806005011680b0780a018044100c2c0021380c0140140704803010030700030300000920140c9034225201c0e8800e094852008610a040e102ca94080c000d2400c107258441c40b6000f141010082c0c1e08000c05804000c0c5600c1d000b6a0014101e045910200108040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 211068723 1250 211067473 211067489
    0x308220308030708130302070b0f0d051005150403051906090503070b1501030b010f030c020c12030d0b0319060221160206070801230303070813030501050705031005010516020406 78
    0x50b03800c0601000b010301c980a0200c039450140b61414600003a000036000d400c60309116101504c0d80031154000109006011405008605013010805588040814102a02c000b150100705649054107100c0d0b09003ea0f0000500315440348041d203c001600f000202001480ba20001c18104d071076035212401c41d00242d8003141c1c0517004000b40070035a0440c0001c424401000c0c0390800212054030002405400144090720031725948480345014940b00740610350540301c02520074500030510b4440b0b207580e6440112a1103c8501d026500c0c0c00364a40480c1940c207801c40c0506030f100460341500c3e504020340c4a140da000c41901c0d42043c652003c1c0e0100030052040310603900092641c100804040c0c2040c000600000802403510010701803001801c804251001c06000b20342541e000c104c020a2641c8681c840141c440314011501aa003110700b40d45103025a840743c002801240c440c20030507034bd01d010640301c50410301c403105010300155100d40c000d010601c002e00c0b5101e030041e00d5038011070115003460f084980 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 211069973 1250 211068723 211068727
    0xa0204050d20030d080703090201090305010606210606090b2203150b030a0206030a02090a030507090213060c0c0e06030a06050c19052a1f0b04060617010308220308 72
    0x41c0c6401c068080002440b030581c0030b010002581c1ca0001c101ca41c0091443c1d0916030b41c1e80950382036902c1040c81101640d4070000810620b915003001621116100100c001c02d1410841513103100c840f0f81c05500c08071480b98645a81850404545813000e410014020084001d958940c05030181d99040445c000c1d4090521048100070f095900019900c180306414066800f00c840540107031166021640c0c800d03c80720300181c598503001c000510700200d69101038864800c41601142180350b682c0248104030407520041c0901d50381d40030548070304003211009441820300980030000401c6c0910282c0d80080b004040e642c000c0e00c107070342c1c5008a03501620307080c0e03810001103510084052515030b259160401802c2c010306000402a2842d00b660404500c602d000b400910881420356040002100c030070324003482408160411000b00005000000c90340784954180038000030384d01d01412000102201c2410006020380c21901c030450f882d0b210510407050b440d5030750410401d046200c6e032081e000d507210b007010b25 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 211071223 1250 211069973 211070003
    0x1050c031801141903050603011127011806030f0e0f0c01030c021b04020901020f030a0f0306062f1009030503041205031e190608060f101505030a0204050d 68
    0x10711250b50021003c1900704200507041001d5040c0000c0c0da8100c4262401142c03079500c0c8400310340908840c5404000502012811100c102c80f003a000c1030302c5985401e000e8441040302c0004440e14400c0c1d112200f031a10a00b102400000e03c20742014100700382010000c54010480c2003040c0c90b0440d4622044425089918031100c030f0b40e07141c01528800c1000341300500e044942d50081005a611a07201c1c90320036540081c5402541c0d00074440800c03100c00450607240c68040011020b0a84040c4030000f0001034a0600d011803030030b010300700d41c854101d80035140e810640d25502c1c504801450b61520284c1a1140007454440c1500500800081c14442d64070305841c1d0500c2c0c940b5509021071003240030244501070040222540d5208165140c009401c003c00c1100d4480c02341001000303080310345644000e0309000c800302d04e152000442c540038402c0038903140800c2c0d41e9039144084000c403d01a01c02038044803003040140038803a102460304000d030010014901750740e81002480196442108540720680c1d88048 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 211072473 1250 211071223 211071227
    0x114031f080d1107051e0f030105040819020d05090405040611030108160e0603031210030219052e0c0314121008030f090105070312050a061809110f01050c031801 71
    0x40b0803c001d244001d088003410140016803a19440401d0b01c095907102c0d403001d030240d031440c0c52079007040b40180c0204098201070a009100d5402240714212528085ca2101001480012071100c04003141e034419042401c4c14082001924001c0c0040e64816114031500030004c0c01d00c40114005d00c174001c02019803040c0c107400e160b0044055403041c2d04151004081106503100841100c1d50602800350b03400b40c03a510f02d035040101c00d240f0b030000303074000c4000510482901c800000300400e1f56030440380102c010003208441603811480340007400c24a01e894134030355403041c0222042c142d024400c0c00c2c004003240b80c0c1c04010b0320a41000804407001132240061044c4400d0341d034101006000e41078007452a0040500e4501c085100741c06400d410800b000901405040c41544c040140b1007007401c00f0302440c1030201030140904807030b004036040d1004000a00b500c8a03a00c0c841c0550807944104024010080a41008403a09684458505200e01001807000b01c2c44140014900b40c07200219030f2035100c000d4800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 211073723 1250 211072473 211072487
    0x2010c021014060d050708070305150115090506251a1008031219090c0602191a07050c150708071d0f0411040603091704050114031f080d 60
    0xc8001079407a104014000800c045442e03036100c00f069030450790b0107000e03140c441e1800c4141e91021660340520340d0f0110070001c002c00c0ca00008c07146500002520390700d41946200c03142460741218042081d18108001d5400d00c0b40242c01030802d000081902d1198060304550050030b840000c03174042944041c0f201d40c921042c01c04a030480f841070801e0101078144a074069980c8603039030040e030056040900040c1c00440b81040c01d00941c014003410300c150141032801d0551012603000e481d001d0301884089081c4492003501c0300d120325400c0721586110300502203d007054810050300c0741007004800c00134005800760401c41454102081000c4a02c0f80c41c0c02d20009100e00c0c1c005c1c0020080020126040790791a103240d50001d0184800c075005c442c0c40c009100058002c060000303400801c2d520105001400d2600350f4024885280511651702d540000164106103900c034078003d01d40803c2c3d002450038103140410014643c00510100c1303010000e110070300c100d00410583d0380b01a40c56448603400d1041c2c01da008103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 211074973 1250 211073723 211073743
    0x40b13021e0301030201080a1a0d0303020307020f03090d0213090b090d030b090708040b060a080607020705030c0301020705061b0c031306170702120c070f1203021902100e060d050702010c02 83
    0x807071419541554002403400c02c000d408408025168100c90400e07180380c0310b401225040081602e6082e615a1401401039001140d1503000750007000000c220050011044802441c0018000c91012503d41d00304100c448145a91440803560b03aa40ca40014426044c401d01888000005010f520540ca10003030942d160704a5403070061700300100f889880307034200c10320981060b40b11400c04a2541c400021542002e49640044003c2c07207600c003800a0240c0105140099070415030655410020450505080c0d21800d04000c02c6a44a0400241c02e0500100400d4044c2d6038800c441d4642610300803007602e10b40110344961090487c0e40d0040001d40d030089155507420124181840c410301c4c3c40d070740203510740301903074022180c1c07a50016100d240c440c428028030005d4201d2005141040d51100d04014a13100480f4003180944030310b5030005000d40e940401086003590007004190725000050044441d43c0c5020301c4140c01000034800e124600c00079010300707403250f41d4607800050a200500402840c10300f4100c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 211076223 1250 211074973 211075027
    0x20c0a12020a060c0c0b0d0209090411030f0a020604030b18030c101a1503150d0507031101021513031b0b06091602030d050c1b070501140301060c0f02040b1302 70
    0x50300c4d02d00140d00d010380c21080b40c4880340410b840d14440a58000680300b5521078541c0014010700700410803640300821907540d41c05a049078242907000e03d00076a07804c050311002e548090f082c0001c000040500e000c40750b21180e8401109000b214054905286420140c0c1050141d0000b0b41a4070a80c40c051042041010280045908003200440480e40301030003001401c1004200000003100140d842881504080c1c0c003a200202c40007403420480d446201d64003088619110011202c0c209601c0090240d0880000e8443c1c680103440e0303400100c4403000080001c806000b030381240c81048041103030741c0d040214000c0030001d41c3c42c6808003c00c10082c00040c00c0c40c45000c0c00c40d0749244d016600000f07642801c10f04020001e000d0700d554010502c00d0040481c40c400c85044070b400c40c2400507010440c1c1007110000e80303440010a44e400c10025050000340a1000010a004100740c04034007401c6408075143c2c0047e00005404900b00c1c04192410018403140e1a03083e0000b44401c5550141460003178105919 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 211077473 1250 211076223 211076237
    0xf031c050d0515010c06090615030b060a0b03060907030504030e0a0905100602011b0e0a030b040f05010b0306041a04060609111815071b0807031406060d02130903020c0a12020a06 78
    0x2e0381c0064170009a18801601c082d0b9529002010005207501450301c0601c030030490254640c0d285881c20f4010400c03200c15005200c030324000a00403030540217403030050303100500610490360307031500031030044c20010b105504000d441c00e6818040d80f500401036024005070100441c0506c1c004040c28142074685e4815070031a85002041018114410040542d0540314034000c1600210440011412215900042c1980845d142403004005441064101c910f104400902a4031182410503840340011100945030108141d600032455a13803426655206114400014010751121a11000c682168145a506400014409403041450003804000040880b40c0c0c07a4210310584c100031950064000c020845400108080301003500496014090405107080710b41301e41d03990608100c4100c0702c80c03103401c981c0244000710705c0344e01f443c07202010540e8002e800740d880c1800c510131420040c00010170550442c0190a0900f0003a40c540780040e000b00306801042d0030060250040043c0ca14455010405022407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 211078723 1250 211077473 211077511
    0x1403060603100c0e030114040b180d111c0f1106010f0b03071b0c0e0105041b1d0d0b06030105160210020703140d06081e0a020f031c050d05 61
    0x80080c0300c01140d8404000452030007440c03c026108064803c138290b516500708170014000d00501400144103901404290615071605101d00c012201040501c0003960041d02c81400d1107030003088401c9103014003400701c400414010504604405801401c000051000c0e03202c030400c04d5000310306401108101c00600300c1545420b4030001c000040313100c0c451301c0706008000110fa490048251407413900c9591509040baa01529250520191038054500c010700070390008200750510740b00781d48000b100030355022100000c100c81079400d5560414000c0b80c5e061155110361071612461101440c40b88940d503010440e091000804d825550300401403052401c84144100c8490b0f030000d0090041c03001c5401c016964185400c0c00c03110300f07a100c00e001000c100c5c00100c82c1481000da0313001d44100c0d5140c009544041759044610304103056030f21542c0c13101d030b400007210b5005440d10454101c1440030040132109180d0031081040450080c500044000c180302084c112480a80350082c190300410348103824404070b03c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 211079973 1250 211078723 211078729
    0xc0105040507061d09040201090f0914151027060e13020a020604030c03030f0c050d0606030b150d0b0a03150b0102070308040b0a090e10030302070803030f0f040f06050f0114030606 79
    0x2130384c180051040c62540b0100701564001d84c216009401422000c1103400c1c4c55410500181c1584084000108a8440000d42a00d0000c0c1d02d00056400103080a08007141c05200705c54004070f160210100c12203810f1000401c0c86400500e000810341d0345c607640c00d11100a010814a443c0d808003e110040c0100705c00042c40c0c2d400700e00940d105038181841010710f406070070200c3c014104440032818051810b01090b24598003d030103056030b4440c05801780311150312450200d050310068031310710703401103940c5602102001c00b51005c0d065210b811232002403a102c00100007000002c80398015035101410780301e04e40001038980a050100358007170004150252640c1d4400713145e0b102310f1069601d42000072900100143c481c10303c081c0108800d003810102403d0428003130000c403030244002c81c0540300306100043c401c18080280c2e4407503200c0361100319090ba5070281802205070010300844060801c0d0320100001641486400d01501e407025050f00c40c0d6040a03419000d01e0100082540b0942c4450100f2555175 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 211081223 1250 211079973 211080017
    0x2010f05060a0b0706020913090b0907060912060e060a2003010b0a080a09050d050408161a070812010906052b11030a0f151d030703030c0507080c010504050706 70
    0x15490103c00e0380d80d550794100399000780650785003540c0c0504a11003040c90000b10750816012207014aa1050850b110203185d6070703407509039115136004901c039281d003040032000140040b20440c1c0a80e0000c24244100d03400c0c141030810840310b5401c05942c5007001488011860700254030007004803801c61565060007401d0000b4024151000c0030003400c8400105d162070320b42c2142a45036400811980307441a00300010305190447d000352110b51041380340b4510b001030401102d400712400b03c1d41d1030781c108841c062060100c0e44142d800b61111a030800c141ca0b200c0c01a181c50a0080c40500e20010306141090100107100c00000c5010490006500710012107002c90046c0b4907a0a600245403441d1280c03420210b41402584180985044d01504224050000c0410080080b19110300108607041c0301e13988064040ca1700411030002035105100070340010780680e220418600e01d81c1030890030800c8613641c00314164000000d007201a5142c0041c001003002c00c0104038060304035420944420010403002c070400d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 211082473 1250 211081223 211081229
    0x304020904080c06040507060f170c091906080106140a08180f0a030809060a050903040b0705070e09010e070b03192c0a0506010b07080406030b0a0b0409090302010f05060a 75
    0x249260102050030002c90508642e41048208141d4180c1c0c5050306150781c564200f07216050124440c488200b0140d44640d0082140801208440a154681d40e208209682007100c54030b41000c00100d80c013104142007041440103020300d99900d41b40c0d42c1000c4004044010003100038000400910601c80116045417180f58014a1910050400c443c0f001d82945840640d005c181d030940100030b1034606150f807141d02c0030301c54210441101c0141d15100b4140d01118400c850f400103940040c4814880c15001358014110382d4001c2040361001c0c4d4981d51983e81d40d0605446024880c0c1d55071891046000b803e000c003100601c041e50019080d45009520040d41d140c00680b652466075503100700307800d511040200b048440000c03404e50340100031098460b0761f850072071020130383e0f40e48034480002070300c034014104407420b45a01200c5141041d24010b020360291801680140d8800398107107022800b1040800940b008224013800410303aa420703410040e08407000108218941ea050400704141919410601030403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 211083723 1250 211082473 211082479
    0x30a020a12050f01090b1614130f05030601081513020405010b03010e0f09070501050d021c1d070302010e010518030f100e0a1e03090306020309030702180f010e130803160f0c08030402 80
    0x4103699007c011500f065074540e800c900c01001203107282d00c0e01d13400e20702c0b5410317181032101c50b60032036440300109961031800744210070482d07004542d880d03c0503200f00002500007421100351001c4466603070018003650403d030407400d84064040b0040041c00d41c40d03829150001208604203016007030400096496440c0703405240d050010018824124840d150304a6901070500041c40003841d40c5107d101d00500b140460350540d40d1090b45502c2030703100c0301142941c01c90380e050b1244d6900800d105e00560380751b000505188980c8241e010300c404640c409100040c0c0444403040680101d060b100121001c0710000c2034845002d0384000000ca0006540008000c21441c10741c0341b900c0b01410318a801c44a060407a000145074034000700c20b0020b06e010000140c040140700b2a04050001ca50510400b0102d0080301c8200c41944080010044041847c41d25500300c507010410b000900010386070117030b80d9030040d2401085101d11800042c00c2c0e80e0b01a510f604091030b00d02c0e281c08403510984600b0614000640007070702c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 211084973 1250 211083723 211083751
    0xc0c030503070f201f2604021f0905010309020f03030c0105090624240c0d03060e04020603040b04050f12030f010509040f08030c130303030902010e011404090209030a020a12050f01090b 81
    0x180d03030f00079014444420607044001d64181c546c0403030840a0035090303804a000345810006448084c40c80204007078404504e40d2845401d0385040e0046025142444051380c0000d0090103075a85c684041c0010036440320404004038960400c1c1c007e0b24035000c802040300e150250b44040000900e1b502c2410f04856210032691030425102c00403104010035a6042d0071101e07000001482518a9004255200c1768012900c041040c6a41e0313001400050300308450095000808100280002c1e054420154010f40584100c0e0b0f000340d21132004916010301c415030045c04010100812900540f180800c0b40581030a5803400528107140d59003003031039042440000c10b001ca0200020701001440070659003400c11000c01d1114040e601d00b0f000e001022a028281d0025441c864450581d50042150440d805507403141c3c517103460710703143d0100002c0d080000a10347c10302854014030b000d6695580030201404100c4505030316581d007883d0407440d2a6124280c41016410135184070003048507240c4080c0e0002820400341 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 211086223 1250 211084973 211085029
    0x3191e050408040801090c0f0602011a1210050c1c06030807121106010603020307081008100c090513020c0607210b010c0c261501060c0c030503070f20 66
    0x200300b500841c0c00c00500366181508030820311052046400071104200c2e4a08d102c1038070b540040f4242e03003008000c5882c500115120040c0d50402100f1010034992174820780308404254a4400141c450543e50007840120129055952170303a4000700c00702461880d00100540b600d03580e240c100c039000d260800740145e2500c43d65800da59004084a012855000003610115a15003030302600039001904c010340015403110010301d4030000340c101c52050352a050f0080641c01042c0001d58003618008000c3c00c1040b450305400291038513000c0110b207408055490140e03c0f03004840b1010326100c4014841030812007004881041d14100024a00009e07042ca040410801009030041c0d13107580c00c0e84801400180306030000202207107014201f003409682d8280303250741500c8164041e6901e103000009030800c64005001000080e01601101c1070052282c0c181d89039a0b0742c2c03a161681142c10510040e0781003444000040b08000d0202c10b4040350100614810020403000c0c1c02155916081c071a80901d10350301701c0e10740d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 211087473 1250 211086223 211086233
    0x60103020904051f02070c05100c0b19020c0a030e0d111509030a03091406281404030602090103060911070f150222090603051c05040905040803191e0504 67
    0x4080c00700d6011815000c01391500a04000390b014007401c3d509082e402c440464036140c4541400b0306500e2540e2507a0709074185ea268903011860243c031990410941c0485024401440c0c00503101021054002e004041c80038180500b01110341c008103031041ca188420342d00092000001d00c11211401d4400300070314408018806494441d000c1229458400c41807814101944002ca140507948100c4050100901000074000c003805800042d01081c00e040c07403508804e461282c40c050b08041c0030b1514114243c00240e0804043d0302580040d01d055030005010001035803d0b0040000402111204010003100440900503500500c10010b050042c1c4030402d905100601d100c140c00c000b043c00c411551904041d5542070803c1c07070348441c49a102c01184000404103c54409c031012690070901516042e8444018801c0800441c14040c060210502c00411030032400c2c440c4d1b03482a445014801e90724202260407010080b000302d820015142410940c43e00301e0607040e0f464900b802804030100b11610b4910304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 211088723 1250 211087473 211087483
    0x70504050a180e0c0d0311070302280b03060d020105130b0723060709030201080603150a06091103060109150516030f02100b06090f0406080111070b090f0d0c02010203070b0f1501030e06010302090405 87
    0x2a61158104100c1505040d02f1070622900340c07042d1184010082c0c0d10102a607460000b01c462a9204000024910240d4000d030001d043d54520320010030001901c8448601946c3c0003400e0954490508a441a112511403868070000022a00c000d102038500308070010180c4c0d40c02e010003030400c11030002181c1c03151020440800c0e054000c01603408140742c9060820700510386407140c4d41506081c104100d05040107001242c1c024901a07440d07200460512500c090004055235102c81085020000009548121000303184554403aa0782e0107200c45414800a10304802603081c07070502850310500d20080d0380d84104070360b0419002e4544101740301480002600400d0654806c0742c203135007081001d0560080d20001080c68500c94401c4489949030804060340d030305002100282c07103a11000307810003e1070107040015003084c8144112450310b101907850340c101820580b07800003a04070070703030030300c88151900454031000010078a020045204040d488a684150602c03010307025810240100d4244801488 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 211089973 1250 211088723 211088729
    0x3030b03060a0b0102011a0a120c090e060a050603150a0f060503030f030703060b1204020d061b020d02060a1e0e0102070b190609020403020603060405070504050a180e0c0d031107 78
    0xc1654001e20740030b0040400341c00f80c0070300c1c41e005506e44101c0c0204100c0208150b11411000740001d190035007230810510302d142401400355444605504d00041d50111070291024058110b005401c40741030030034010341943c0c0064030341032194018a201070042c810801d031060b40201c010740003052a030844070b0010001c100d05c1d001181c060000064110984211304011406140300b60b40800c60141e5400c018113042c090181c03070764640c80ea1000800e01502e02090640c401c0f500545001030180042800c11250900c010100005a00424040488190140561544241c80b00010710040c680070381c041a44541c1e00c0c0c3c180845a81c1c2d69684850418254103495081c2d903c0081d040c500d00b000c500303d41070381051804805415080000100300c078000c6009a07800c880d4060221410b64465004010107010300030206004c03c41b0600c400200396851401500082441212102e600050b0301101400d45081205000c07050340407001c85910354449901e0b4100443e01842c020303407081e41c1400f42d14108441a8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 211091223 1250 211089973 211089979
    0x30405030a0f1e0306170a03270f170601080d0f0320040303020f0d090617151003020d0f060e0402010c080c15160e010219020409050708030a020708060907050d03030b 73
    0x4030308401c49030f010b6010a013510502d2401b00b00e034180368000030703558203d14280100064032011049100800400c030540710300400b40e20011103241c8800e01a03002805642c0318007400c0144040d41c40f00d00e0020b102c0c0c0d40c0900040400742c103c02403c1c48000e4102441181010200340e641d18a00c0820b02c1c01081c0c02862601c0d050a980d07031903550f820001e42e1180780c044c804455010703003a0100c0005011714200002c466603038403900041151020301501a2000410b10440e80c000481c2c02103856075400c002c000190a5602c0c0143c40b07181d50812041241d0612507001850b520306141409000e504800107648260f0901c0c104207103260500e807811260144080704003041c803543e03446444920b00d6008152154110031000d550403070166070120790102d400c10fa003c1c0580c0191001c1c0a88298100d00441c15138000380022034a4080755a4a0340707802555031056001c0e401c040b82c1e481a842e8107118120041402d44020199414403200058407a0b4041c072540d446004503001e10020103000f81c01141d0303903000003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 211092473 1250 211091223 211091267
    0x70207030c140f0409080903120913050604020c0d020106060e04140c0a0203070f03030b1c15020a02070b03010b070b06090106021504322415010c0503180312030405030a0f 75
    0x10346415000c47c1c218208540c482d00449440852200c51b100c02d803081e04000401c10a02901d00440c03990041c00007070b2509030055001c00c150119803030104681e8581e0301c400d500014901d0303c0c110700203011501c00010b0603c22170900e00c1d9600c8031000302484507004a03d5040b0b00c0e0348c80008003010307490361060f40d1004101514014104c2c0030305401d40c0c8481084001070b1a0030081c4845900110040d80c0c1d074000041000103e60020b004842e65035000d803640f548140100e0341c03ca500e4501b081005d41090f0701511060300009800320422810040550300010240e40c00c40ca95410108081d4403002d400d94002004146000080d0a2200444108544056082c2d29003020440044030308000007071020000e5240c46210b00702241040483c981d00e002c90301180e80304200b6250000500e840444032542641013104241d40b480c02f0039805d000030035818400000d0420004000d009041c20141040ca140c01c0c2c06106200300000b20704c011044a042000520b0003a90070418a0b0080d03c400c2c0c8002405500c0c8489 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 211093723 1250 211092473 211092491
    0x30b130b090a05010f020a0516080919091d060705070807120e040522033204090b0a0317071a090307050105060901030335040305090108070207030c140f04 68
    0x1040410a483c00b9600900040b4103020109040e84188070145d00000c408210117059010860a0380c0c043c90321030149140f50001c2e04d000541000302d5100103c0380020032607810030541700c0c14811440d510f056040d001c04003e40100f54507454000060070503003800ba001901c50200038140046500c13003640514540c003100709014000708031030f1702098024022450f007004640c0c212a6800c003000070307004003907903108144800d9601b00c50700503858000014403c1d20041c94950080106400c120b402082003c89480314070b0303c40d4000c00e66065401549c01100740c0c1d5070030710100d00404070718941d0322000b40718580d84a82501d0440c10000700408090750b0030440d501417058180b400f00041c5a0280214002e01045e200c2600708031100e00d080c4001800300f03000d003010b8000c01c5036007003410394042900c18501d501d40c0310441d14100c03102e00c2140c0450000300c00050081156801000c00c0c4d80000543c4014031400e800d40e900c051150907180580b9a04240907130030707110f040e80c0c0c0e2007250a003900060300901102d41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 211094973 1250 211093723 211093741
    0x1020d060e06090c03070e0102160909151a040527071a040e0103020f0112050709030c06171503031e0301050306060616060207020a080312091213030b130b 68
    0x9164010480c100070403402041d441d260400c0c04601664542c844c0d01d00d15100c0103001d0741c1a101d40c152441c194000d401d682034284080d490108003c0000c2d00c00402d207040d0600d441c482a458000e0301720242c610700403403070580c45400c5482100c600b8060320001101d4950108411001480060002c54611403115000800310081840400c4172058880c921301e0010714006005240280c2c05450000080440100054507080c03884800300001030410040c042187d040740c42c181d60007107640348045005035408004201001c10aa002000305141910101c210300c04030707000c0d14901070b100842403403c0b80480c5505030303024401c8400312000c850300315001041200c01550070f500f0074400d9a01ca070003420000792080c28544100d8054582c13884510845d15065503c2c58001d4000440598201c4044a000310b0350040400c010036070b02261240f03800007403900e4800c00d0b00c4c0502c10400075000e03020520095540000e000307501810740f03500280912150795080c01c41c00d0341483c8030388080c2a602d40b01341448181c038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 211096223 1250 211094973 211094981
    0x3080103110d020306100e060103110f0a090b160b0705030f1303030e0d0224071202030a020d0c0509130c0f0804110603070908060f070e040c020a061b021c0c0b07020a0501020d 77
    0x303c0004e031b507c40c9582c4050054048840d41ea05540c8100c00c2000301c90310303810480c4002e02210041d401c00c4613103076407185002d40d4a43c106a4a10310583c10f03103594101400a0501441e40c03010581c0303006455468110056150290060300040c002001d01c01c04030200340c01798001c0c0c105c000200c41154180030002d5402551034642c1442244c10108003040c0b0600440ac60f480d1034030501c12a16054507407041d16203c2c1c0000c0d40300428612149a0900001c20950914003480d1010042941c8803900c0e0f204034130800c5006960f00c144c00300340c20301e00401c0e400700d20342008000e10020143c3c245845940e50390b0800008940744a1251640004000704000c800c68010381e41c401501ca0445c00c9a03420780d20414480c0c65108283c0724100401d2514144ca6070134036294001d02da400205105441c0036600b50358840f000d03584803516a00000b000304100703040b00380c0e0400412221080303d407600400b44441400190010664000240480c102c1c40300188200707008000c01c1140a0b40400215518400e40400310020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 211097473 1250 211096223 211096229
    0xa0323060a0606120504080a1d0306010e0a15050f060a030e010e03030414010209031f09020a03140d0212090111070f0b030403090806060a050123040906090c02030703080103110d02030610 82
    0x1060704d44911601960403441400d1250b984205641d00d040103814058403d030f1601701d5500e414000d98a070034503003902d040c0700c1203008021030300c0366295034106038004206403015080350a0b00c45543c44003c00842d512065a001607180c01d496260b0303201c4000d04100d0142002d0700c89220158204090036095440002c0207502c0740d0b004014070100300d28030b55100c50a138840c1c03491555040d400307414003491504130318000009801c101c3d00e0024061100ea4049141e0365550362095607054040081410844420701c5070000b200741c9072029007500032208904184a000e0180024100614020b4148146004200b8040a0210710703100301c007181e9a0b18400c04160b8800c076022400034080d50700001e00088000380321802000000c00040c281c6003480c004483c880d000b01c024200c00121090381c942d420390340500402c09464186000306129003080030003815200c1a50f148402c40d402044824042984200054152030748261a19074544002c1d000801c060400040a076041c0140f00600c1801c2c0e0706041a07d0803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 211098723 1250 211097473 211097477
    0x18030f03030a150f050f010c150504030f050a0801030b04020a08070305060402010e0a081e0709020706140c040e04084608070504030b1f0e10090b0a0323060a0606 71
    0x1107262030600300d56848120300c81c440201c50b00d46400d00140c5405581b1414006040c07404034034105082c1ca41103040003100e451030070102da80b10140010316a0040c81200c110a03242811441c1c100c205100804101d01484042c004803010030116045543c1e820aa2000307000f40400c5a00154407410400d403a00c00c01e03201203000c5100c2040406107410080020001c0396000300c094a0030f08030360916250700700c90038420403109000781c00300403d06c1302030381c400340c00060f004001c0001d045e5841240001440c401505001c0b09940602040000e070701c0180242c0d50140c1e010300213545901074250f8441c0500000c070060101d02d040ca089281d10868094080405c601104002600711040d02c034056039907043c00d5803a0700009804010900c0072885211030a074201d00825a04402d20104c00346c42c07407951942e50801c0f0100c41b00311081c8074a115881c600728000c1c001034681040403107104400114840e1a0b803000070181c11007425086591381e00407035a80c0361100340c90280d410614003062106c1c02001c050040b000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 211099973 1250 211098723 211098731
    0xc0b03070203041e0f03020d05010605120304050307080613080f040302090c0903010506012c030a080409140f0603070501080601030b0a17010c0c020a030204110c0a080d060506070f0818030f03030a 86
    0x5020003c24504e8000c590456901c44285030131034083c040081803402c4191b84540d00e400d000140303030b01c400341c40c8198146040701558440d400d190405003800169444135207961701178000d202282202403180102c01c4e0340680d0082d0346410b40c0c507002d2144d0240741e001950020010040044401d0b400d0f00921560000710300070003803075032090015039031181d00d0800d0800147c11000341000251202c1e090440050000f41100c3c0314030303540e40c2c3e03101456019806c030071040b81d255104d1503001551140c18503004800408040082e1800780003003a5110182e1040504114280c008225a40d010b648041040310024080c611100d8441c004070040d40400e5801080a600e0400700c11504d030b202e4624062000c1d4018403101186196800b000302170181c010150361a80002c00c0464840030007000f04803502c0e80304d51402501d07800301001400869015038415030240408101010002d014010030701c00c100d50002c182c646458640600e81c800c14011205607816101e46029220ba00f5800230181d8420961700314280 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 211101223 1250 211099973 211100009
    0x105090606130207120503060d02060403060e0f0a11091503061503100b010c060906060e090a020a0e011805100504020f0d05010603090519051f0b150a0504060c0c0b0307020304 77
    0x1e02280302e00213001e40300004000030b149038584070b500116003140b00180340644074a941d030001500d03540290700884e00389507202045240e0074414802c01c3c02c2184d00d00041c0ca90340e1115140c180741d0640c030300d0101e07220f0900d043c009018080e061021403000344002d03088603014982280300c65503002100b08814860301c0340751500d101c2d9661034040e0232100031040c1d603443e600c44e41c9551400e0140400080498590307440c0c50b00880c0a2001c41e20039440340300c140d0010004840309005104042205030403025512001360010301c42000c0116114403c4440a0030000e4507a071030b604e883d0280a082e0b0407842d0300c070380001180c0b20340b45000750150805101c0d101c2d0030062641d89a0055045403a4030764014030507008000e00715004610008a42d111034045c00c280c4051a1201c81183d407204a2407440d1031001d0f03554403002c0003504101c1e0045c40396400400304107241001005000d4602d0141e8402c8108000c2d203c00741c0c0c01040030704803c4070000c044842c219501d9080c075010181d103a42040c0150003840707650002d10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 211102473 1250 211101223 211101259
    0xd030c030201330b041404020f07120c150203040215090301060512010c0305012306160f0b040303180b13051005010303050405402301060e0102010b300105090606 71
    0x440c101c41d0302480070540c6d85040ca0034071020b50018050145240403c2c44030b00041420313010703d076050709420351b903440c2c0c4851949030489180f40180e014032002c51050003000010303119013a5000d040c40c0d00c0c42105884140c2440024050305454219a4101e08070040e07942c0300c0801504040c00c100c00d107480c03e000ca81c1e2203e40002c130b079045009075004081003648008a0905040740100b001900c480c40790a1680415103a082036030004a008488400190041106041d8180315142d00c2d4184601844603406854544001d5000701401c2000e000307241d0765030b2208100c1c0030001c103420483e0780001400690b94a0030050201d0b04181300d0346000700d00b0403113034140f0401c1700501105c0c0007400c150078880f902c1c41148084188404031801d050341d0b030303a564403074608502600c80c095011000c1d41c8810300d0310b41c10141c009042d080c81c469481d05680c1052041c00071039403007280340700103c0000a0204900c100c101b10400f481d02d40703200d01d107045518100a100542c00e0202c2d2040c49910240c48110305ca9000c4102 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 211103723 1250 211102473 211102477
    0xe190905120c10150e06060a0903110a08011e0b01050304150c1215140402120408030703020f0409060608071115040203010b03070902030a0e07050d030c030201330b 72
    0x8020310a4022880a54030301c4503103006068400d4100c0110f500401c1c0c0c1c0483c0504888024450034510840c4410820020742c0f151101d40d8005415580c1c1c9042020300301002d46a40703080d0100034610070314030302c2014031510b42c00d0011000309001802800342010aa80e52600300100e54003040000d802c0103030844655000d0310441e805150302050f1010f0403503000000e50018162044010200700b00918094801803184c020786c07286940300344140202529103c000351140e100c5a02e401d0080d8018000403a424100200840e841030f0040021030341c1e40e44a0034120024860400d02001121001c0307408501030040341e000740306484071500c5d0302c04107403280c50040e00c510069500c4103042e6444030307440a02d003910004906400910140021913501d88010010341040c200e500220000340d404000c04c20100f41c540550781c41c0350504c801a00340395003804041000c540c00060040c0c280a11030b0180820107100354041024007042d80b242d2401c1c1e080c1c0900031402101a662107042240c5c691350041054900340701 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 211104973 1250 211103723 211103741
    0x90b0303030c090a0314100b0405073207050706090801110a0c0c0b0a020f1e060402100c0609080307122a0203040e01080f070905010308070b04020402070c0e19 70
    0x20350650b55a403034540d4290388140c0301c8a0300000090000000a07000c0c260b001a140000000b51100e64825040002119007000c01c29210b6403e003014001c1540c0c004001500162403070b0104100e5981a0445014230301c03200d110150720304000070703001050003004601c0c1001d0711456620107545a64502c3c1c95070985800b05400316120301c3c1000010301690240120181c0b09125a64031000180e607134041e400c20744c0203242508003607002071504400034142400602414000e216440c0c0385054006a05070750b03801d0040c4001d00031101100000ca0140c00f40518000556211009101c0189240781000c1942c0094906030007043d0140c4107507403105194040e03851059003416400c40041c1d1038000c01c2a80540d0850308900b507000401c800f2a00a0141001a000e0f10640004000582609105070710700042a809602500d2801005000054410741120a00303500aa4601000e80b59400010000c0c80354201c010015803417128009480301c261568544030320455600743c444801c200e410078040d01c081003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 211106223 1250 211104973 211104979
    0x3090806070504140f030d020f0706090305060109050c0d02040906090f1e1109030708060405060603150106030c050c0a03020a060b12071a09090915010b0f030a0f020f07060209030601090b 82
    0x1220601c12900360b04070303901c0380310b07030050002810704604070101f402c00481711131050042c0c101c600c00441c0f641c42001400000c003140d01d0b04240d01351075611120b40759a018000e230300000c0d4884021a08101d050b2090311121880003200310750712680e40d039100e0014002d500c108000e0074208080c08a0503000d620404020f41401c1b400042082c806ca456100280b81d25070321002c10329000c3c08040d840744c40401100c400f030540c15008040c3c0381031a0404901d0032100400c030600c294030510160042144044801d4111a440e050200782c03038416050075a4140100644500c82c3e1040d0144c0a090550000301281e545000d04400c02440440030203101100080702031960342940549000c104170b60381e401c11050030794100e42000d400c00c60301000040070500143c62540036981710601000d190340580c003100740100004447c6910b4415403141100c5940402000380329156501c50040300a20b11640480d8403c80d0b03031030b0a0542ea0311452074800002d4024591140c000d00c180b200205240080303200d0058208401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 211107473 1250 211106223 211106227
    0x70f09081e01180501050a1103090d140706050a0f0515010c030c020609030d0203070b13110108100305030c0d03110309030304080309010b06030a0b0102060a05061f0302190c030908060705 82
    0xd1446002002810a0000c0071503585244500c40d240b800d24140582e184200c0000c00c590600d01005001e8816074090101506420820b04c6981180022071080d004080d007450340d0002140e0440f101280101840541501d042070100400030015030700946031b111450000700201c0c3ca90788480c9101d403035185482400300b0580c94007100401d005070b400d0790180344010300c0f42d0301d0000d60801083c209800c08a107900564400308030130b420010150070007a4400905040d80119640741e03182c1201280c01503440c907041c0300002c004502c0d07044c403030204140030350b8000088aa07129000c8040655820741d41c060100003038903200c1d10340f07100c400100481c1d0080e0000300080d41507071a1600c40b202203a10240240f0301725980e40e111000c16498110146100359410100018402c02220001e4102203004203842e54070303880c00c000c02059550710001d9014030040300d00e03000410074000109900a2150b416443c86105002ca0303450705503135101511000042c420b80d0341071140e5070f540d081c00e50743e4001640e00030045002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 211108723 1250 211107473 211107493
    0x302040c0f0315290c03040e100603051603021b0708070f0608040803070305060118060305180a05120d060806090c04140f0105040b010c1a040c050a05010512151206070f0908 76
    0x100c04d00034940c2e0341e2400c0d215440c00460b00c80080c5107a001c1d510007a1020384880c01c1050400384041c64000408090406010300d00d00321115542030071094400c031007403582c04201d041030007120b64503013031a04140303d08a6680c079807030f9890760742d82d015648074030044504116404545284940740d02d500031030b44100700382c2c10f540701c40205502600c4020310b01e5042110009180071041c070654034400051515882c00142410b003150300c00b61186110004a5059001c000340760005440014480311800e0741102140d120000c4403418000740005901c0a009886030302d0511512110210701c40300350030011102009a00d5002183d820580e40803981c2400204100b0010401c0382040c2e000303603411a00c145802c4464101d16030350310002d694550200342a11908008000030096504200340150200300e61500302d252528000070601d100e00b4203045047d80500e00403400040f144141083c060f04018042c114407502c201340251fa40d2021201040003e007086c200c5c10700107000e5100d80c01a698075801070040c2500c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 211109973 1250 211108723 211108769
    0x160c02040c02120d02030708061002031206190305070e09150412050d0203131403090d060b0d0507080a030206010603060b040501030e15010b180402130e0c040302040c0f0315 76
    0x1c00381141d000d41c014550485400203800c401018000880d80740180c1b0307402c1c600c5004082c800700410742c60160500c3c51040c0d0311580c001040c0d60f00c090200c5034610784c603652035010441850701c2d207207a0f480c2001c2c8440040108074004c900c0e6030a42d4460284050941d440c06011170307403110000b088000526007036000c10080780d400c106e0102c149020f400d0080c03818401000c240105d80c0125202c4181346200c0391170314108058004c00382480700c05c0d0710040d0b05045460000950380300d0b8903600200825600c81880403180c03940e0246d40c42182c0c1100540f01595598450a625501c16030802c41c01402444008500503009101d04002c0d80d658070400c504042c00e00005500518071485079040c584170312070b010a00c03110181200f03406008141c03105034540994003600103d080c0c8a40700144603038018480c01016401040310a01115405591240e80e619144180302c00740c440d5800294005040100211065400110008100c820b40d80c0401c442540e403000302e10140c155008402c04082e00150b011100c0c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 211111223 1250 211109973 211109981
    0x1b0302060f0313020303070b040219030302061305010f02070507240504060c1a090304060f080105060d1d2506080609040201050a200a05070b0408070e040f08070606050306160c0204 79
    0x20f0b80210142d2110b4203250006459500034040031a03694600ca420801103040c0031180f51000a51059803600311419550040e403140b1000700900d00383c880602403030741401300075040007030301d0325841340700315518009400d102d03031505928010718006000410f102000500001071440c45c0c1001a030300c650906081100403240c1129618040e945000300c0e41c0c091110150740c0401c00e0059003658010b560340c91422001a000c80c4444201e9002e00100745c004000a4651100321a80d2180e030141c0050646410320301c084004440f1850021940700e1803404103800303401d0180d084100080040c0203000b1a42d503290444001108440898000b5589c8012a0040d4007c40151598000d28109152620700801d40440214030074004841507510030290ba02c18003a0a00c6000d0180503070b0580240f906041c10704580d503c038510303ca10580d1040c6203001405100301542c0350098242e00440c21683c51040d402c003200a04914041d144c4207000700360104489141003d004400300c1142d4803182d130104025003c0100030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 211112473 1250 211111223 211111231
    0x30a090302010c1718040b0409020a15180e011e06021005090f0d050d0b0d0c1502031308010c1814090a0f020f0c010c0c1703060a0504060603091b0302060f03 69
    0x356060281600c5640041400350148491170010884480d0030802004240e94142003807071b006a14205003507016884a1314500107940460724144000502c4400840d03d6012070300540d0303408410320002240e5166603802250490b40031441c6600d030131000b403650102d18421441504c02503030041c03098000200454100b00e6000c7c0c0e05509990304004000c00c1e80d07040c8445090348500107080000c5c20071000810f44104104e40d02c055071217600300c029503035905075441c5a80c0a0a14000036045014070780902c04c00c2283c03040304844517030042030350303480660718080c00c06100e804010805015000d6007004010203002d040f51742618001d40c0c01c804034070901805d981b0281000c40c2450f06c030b000700754071003407e400280681122580c00310b41d50303104003449608480720080000300700156842444003045291000d095001140c054036649d03521140000f0710703501526800103030801d08107440000d6840c0c241c3d000e00300840c007034114034900f03041100c244c552502840c040254400001c1c00f800c3e030041d00c400095544 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 211113723 1250 211112473 211112483
    0xe07030b150a09030b130305070201050d06120308070f030509030d0f0e0a30020c0f030c19060207080703080d05100f09021918030b06010512040c05030f030a090302010c 74
    0x1042003440302030621035210b11198004aa003d89040081003a101c008551216581440440e0303030b02075541c010010310503d20701a04005e404034203210060382540c0000018445003540500d075540e04c0c40d01800040d41103440201143c8400c040c806102d020380204c501c07a0f8103500c080d61510301900035210081c43c42c0c045050310603507100b8454040700801c004080c0d03113038002c0c0380d45421000c5c850020100c0c50340ba00f85141845689201811940ea000240a1a401ea0881d520703100c04e40d00d000030910340034403050280d0340300881400390050350404112402c25560242d013030356000f40e2514505070303a13601d203448020316030b482c200316440701466a54000c036044900740e680c040c01c030740e43d46085400540b00394000d91013456000a04051072800411a800007045a06020880707481619031508040708a1101919201c10b500024a032613108034100d5440c1d500c1030321300d23040070b081c1424010002c102034040c10b03019100d100202100700078000184c80c440d80c0103943c1d90700c0c8241568011207030b202c1803000441d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 211114973 1250 211113723 211113739
    0xf0603131b0e0112230303070804170a1d150306042d0212010e0105010518060c030f0c0c0306040b180c100201020307020c010e0f1c0204021306090501090e07030b 71
    0x390949044842c81c02406840055000343d8494207007000010700680507007003540c510b080d0b0b00024680c00701c2542da000105080c1018150341c2c605140f0f008100c58880040703090400a68001615008001610030000c000407001081c100441444a01c03130101113048001d010500004c1c1540c40e050700a401c00c5403000c0a1042143c1c042508280f0a00c082c00500c0c400d00d4021804070b8840301d110000c0c81c01012948200300480d45840000b038801d11590941c080c2d0981d60710a8800311303440c0c04040f070341ca03985010220303a600c00114030300e002c081d04507a2a244250113002400600346c0b030700184250003683c1010200619440c1c84800f44c3d261941d01c00340081d18060010450515651508158054600b9130009603603440c00d2000241000b2410201c181442640c0310040da690b00c4030100c419403403c0a49682540d0107010003544004807440350f00035401800010071a2090714101140011905c681d1600c08030581c50b000151001501c1c0d0160720841440200010002442500200710b010000b4140030303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 211116223 1250 211114973 211114979
    0xd0e03070606080d2601090236031207020306070503070c050d031a030d0e06070c030c0b1e0309030315180906010f060201020415051c02040806060f0603131b 69
    0x8160382d80c41d8000d070010341000302030401a0b9000602c040c001d43d0194038a0b20201e5a41e820003042c00c0040c0a4250b01a60226001c2c2c40084840c0c80c4403100041000100240c503203071030300c00c40c0d420402c14a2170301074007a045e000c1c00090390600a45900b40c1c3d00030080c0c8000e42d680c1b4000c40d1183c100030601401c0004008040011070720621442c000020184c0e00496001d000d041400c1c4c5190051030107138000c1e44444c24190b07035503610015850340460100ca1266440d00c80b0704103001844043c1e080985104045c610004010308044010185800c0060090340c20024031446400300b03000813204010355410800008558001401a8500c41c036002040303241c0101001449034942c420444801c04154046001440201c1c103100c1a140103206910081d490310303051285080301645800b0b50441804800300d031030741e03140800410380000701031980c1c0c0031512580d03284600786e075800040e40c030540180b0801d03110345582c0c00c021b001c80384980000e501a1510a40668500e21540e0000324942c4036080044008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 211117473 1250 211116223 211116233
    0x80a030e030d0921020d020a060203180601080c030708060c030127050a0c0305090d090b09010915030c0e06190e12070806040c0906260a0206041511010e030d0e0307 72
    0x5400e070a005004030746003148203a42074900342510b180e488043d1740c1b240c20040340c05540010581005588220090303100d031a02c0451462504017005032000c18040d00d000881c140100264550401c081101203416455840408644400c4107035030505c3c6054080005001c41020000580d90a91103085200b4200d02502c2c00c1070203e0b201601d0009005071590b040c01041035050081e1074200c0c0000000c3d0003240e01030070010704590024858030001c500d010a030781d03286030701074420380c001007140702070030700150359405402401020b0111550b80800c100340005003080c01c04400f0b03181000303448007182c0d041940006040d5003001500c82000e17803280380c162303e881c05d0b01400d022440007080c05c3c00040c01c440c28036103800c415000d031a030001703000c1901e46502044020b864141c00943e80310038001ea0010a41404100e40c00c0203030941c4080d4014900140001d14010520161034490406a4900d046618a10702c02030907aa0304011752080c0358414031031061a42d80a0303220780f507442c010008aa1818101e070340c070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 211118723 1250 211117473 211117481
    0x12181710060b090105270a030f140601060e0f0a030503120103030f1e0c06090606080d0813080304120504031a0604230606090409060c0507030f030501050a06110f0f0d021603080a030e030d 82
    0x2702d035445669144242088040303504082826000c2008e00000c0d81000c8004180529440d10513100d0010450440b980d44ca030b084c035800c0034540010503250b07100010600e8862101c001e100c200c0000320704c01c1407188043e1140c1c28491841071744e1400e0519101510b02e08171610400140240c441c20303a500d0000b8001401c80c0308001c024107644002d04440d216030030001c2e145040041c803440c2541c02c043d80303200009090400300c950003940302c080a1600c029003141152a40210b80000345410459402c15032203c2d0b00d00c00440c441c1c2400c83e01032045000512005010040f17044c619001001c03090b0218401d0b1a02c20060112200040c100003114010f584911040c3c6044050400c0810740000c0c07808103041d4000c0f5216950100c0b8102403101c0d51500300403e07954040c5210307174001c01c086110038040066050000b11041c1d400c0008954003c4901803003143c8031030300c08044801522404191403541001c2d1030903641103d4205040c030382860450401a40981850304181840380410030060f0f00050f041d1003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 211119973 1250 211118723 211118729
    0x3090c030a140c1c02040e0a140328020a0b0a0221040201090b07050d08070507060f1a030d1d0406030c0603140609010312181710060b090105270a 64
    0x140010182d824112410b04081080303072500c1c0100850140e82c29007280e100c21090303d01e64190303800102c00d110094400d007040b488440080440e0420f04203640440c200102801c030341e888000c0c0908400d00c0808140407410b88140c00070f030260700003040381c40219903513116942d0b2020180c5c902514016600300306001b0030850f4040c02e0108030240d401e10041d964000000340181100000c1d952500c0d030182c46039030307454155000d003008001d82d400000f44e2251140c410756054550108060001c4000c1095142c0644074414802400040c6a520148585000138020403840d1498031050b8503a0f04085502c50316042d01c1d40400c0d041900e0f00390002c00034001003500c030300a002954001410700e54150080700081d001900107407007425410010b10104121510f000e10040040c140039402504045c500e1002500706d81c8000b0b176000340150300071240c02012079040180702100100708004c603203a03250269180102100c0600051041c0700002c1502c4201214107000c13100c007140c248801385004006002c40c05160 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 211121223 1250 211119973 211119983
    0x7030c050f0102031b0904020706020d09020103050a0c2003131805060d08030f130b101a030114060304150c0903050c011106061302070203060901020a090f0f05040203090c030a 77
    0x544800184601444a00d1100040c40d009518500344040501d14140303c000c9100c400b410006000c90213a40d07141c0c100e40f07440740c2c40842552101c0d01104280002d0038a0070302640440d0400000880070096441040c515403450740b2088104094005414626680e003420441c8503c800c0002da285410042c80003c0141416000b203074200d8140e020354801d41f44081e0041e80201d40041640c2d00180300c0340e09495120035100030021884e07032604509007050440e07090107404607580d1001c0c803441400e14200d60f001d4802100034500001c0c04900e009507148001d1040607414580c0d00150380451070548000c50300030340288545070482d120112840708039084181f0040c041500707040d08108000c4280039031801074100b42000400601c5c9040010346901000b05402c1c070078101e074802c42c00e00e091301798181e41d0500d8001d021240e40b8074088043e503000b076200f01300d0781c07010401d41d0800003488502c90f420403050315801c1c50310300c80030340c54a82404041e40000e0103c0949000721018010709480c20022014114051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 211122473 1250 211121223 211121237
    0x106090912020d090b0f030a150803030703141b0a12020d0c1101020a020601150908120d0b0a03031b0f0609120909060b16030203120f0114011b030806150703 69
    0x95480645801c1640c4003400900428400400c4200c964206449a01b04041c126542e81d0366008800b200501607a40c40b4520318101920125982c034001003d103200305240c0d10100401e503d068024180d15404444214081d100210002c01c164031820140100c0301071410160a1032202d2801501642c2014044100d810b5a62001c00d0402d40d01101c00070880702d06400842c03400e8003440c8003d48032541406004c0e00580d1400805000038800c025010003404039a040d030300c260001002c032003515071141400c07050260a001861400345400d4030000100c07645501d8a50483c0e040b000e401c00d003075800b01419516070b104001c102c0f01180003030148800c0c40340b08409810902c907401c0c40103000d00c1000c1e00501060b0386054818810f026400c801c48404c0e44031410825000ca50a1404034a1440f1b5a0788140402e5218010f000c41d0400c0020511b0698240c62010004c16800e00011100d110b02c0011300400300c14400e40c9100846c1c0180d07a002d402a5014000c403443c800455083e0703004d6845464118001105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 211123723 1250 211122473 211122503
    0x507020a150e0405040201170702030405121f1b080c13030303050a050901051b090303040f081c0c0201080a0f061716050d0c1a162009060603010b0a0201060909 70
    0x200c900d403600200300450b020059030030f180d000201488001e6840c40c0b0b85540b0f010101d09c4150080098030000d01008003000e0300354130481101602d4a01e4682c604100e960807169101d415422070040d1003507003400ea580e04c2100001620100d4182c48041c200c0e000d4900e08120304689600c40880c850b020314001e031004915400c041081e14220791000b071940c40182d160005201d40d101c7d101940e400c5101d00c0d050510745030020400041d04610441d8411601c1c1d54181d8400219860080f800f44d0028004401c40d0a440b01418000e40b403200401e0030090004400c580058900c0905510106c020081c0c000700050342511207130702019000d0400d040b0900c5601c020041440c001c40702040501800b0180c4109480405541e5505001d500c2c0e40103d03120700c00b18010380412924038209480c050700a9000d26082d07000c0340c0c01c1912010400c0200302056000280ea903640030700f441e0704c0c3c0d82c0c01680040e1001d0f02d56841c0400300191070700806504401c654036103000044038800c1d4002c2c0a05140140807050034445 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 211124973 1250 211123723 211123727
    0xf09050d0c020f04090204020d0f0902011101050c041a07051230040602091216060306060509010c0312020d0203010f05090603070303020307020904030905031e0c010e030c0d030507020a15 82
    0x10a01001504000c034003a4071500684540100400680c1e01380d901194000c0e440c400a0003030f000b00e44030300c1407180c13404d03075448480100d5030800074a181c000e0720341e403034217203600e220319801d03590f00b200d90490300380003000300300000e04070100c50400100c01041c0480c01d2a88590741e440c00e00908041c2418081008241351005829901c264001400c04ac11440b8411108040c03a000021000380090440c07030f404a2150710944821105c0f0300e80405500c00c3c1e55500c40c0d5084521751400d5940280c200180c43c0c9000850294003c004a420744c56058441e010780f028143d4085400e20640007140202c69000e2281144892550000d58081d080f141500d21809043c03005006540c0070042815101380c3c01050104080713500442104c0d03850350141d46100d40341d502ca040070f484840140d44480d40503c15565a10080b1001040c01136100001909640030616420011200d0070006050780c1e81c03581040d12200740340c0c6020a09440c42c540700b800c0060070f00c5c1c40c42d00052005001c9074056510500e03a0403c08440d25 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 211126223 1250 211124973 211124983
    0x30405160504060f0302091008070e160801030f121107062003070c09051e1306060f1a07140106060203040f05030a030e130906020c0a020a0e040201230702040f0905 72
    0x2010542d4100585840d2545505a210303040c032000e8015420f070f0010450034008101c1e1000034100a104175104284da51405800051041b600e55040c5800340c0c24450009200b461414103c07904009004031030a850b8139503800c0c003d1000001014084800c0da003011240050080f0307802400241c45241050b14107012089515800200e4150185c00c00c1010341d002a00c845640d5042e945a013000060546e01c40b41075108050705d0303403103190704a03400804011101200705000050b95129040034800b01c1d54032040c07021a40303d18090f141203c5d240c41d40f04005100500040c040d07190261000c40981c00e0a0585c1a003118a141c005000513080014140024400e00f542480104810350080040c850252001002d1074154024280329485281000e80c0030b003621307000001400e41001c2c085541d92010700c8059134038110303c0402c038001c1c0c041c481e00244010034122030781c1c4185e4040c0c40d00304031820052181d000d003200c01e00c54115030040601c00c1401503102d5206091110806107000160020700e42485031404e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 211127473 1250 211126223 211126229
    0x31e0c1207060f080a090203060a1e110405060901020307060e0c10180303030207020f03070b0409230c070c030b09010f060503030a1403060103060e090606010f08100302150f03040516 80
    0xda031120710304106041d4003805000809038a80b401480e03980341c28080030b024001c500c401a52511511044c0714041c191940844020300c00c0460b40d00203040600490810f40b00200c001c8584288103001c03c002d2824202d00400d0041030503c1502d140c0ba44030341d80c100454a86100c1d500d000ea0110001c1803907414881d50310f522805803400d01028841c00d28041c0251152035000081c01c240d00407460100710740300d51084031212000201581d138001e440d0f03120b0321f43d1a00f15225070014242404c48880313a001035290b9040340320070f0f10071780d5104580d60b1110000b095170000104407a81d5244540000229010104240c010800000042500500c083c0d0450a8031025080584a50000c05c07100c52081d405c0344000300001c8811221645035030307030000107070014130059001004500c90001003041194012440c180300348402d88591030100343c036140c1110120400c50b21390000000e8108144054904030b59114403000c209500c1d0343c5401d040460044043d0401e80d0219030350f520100300304c1c40d070f480009031030006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 211128723 1250 211127473 211127509
    0x9050a05100e1501050f03070c110613050405090f19020103060609080604060e010b03030a030902040501090b060f0f04120b060102071a040b0c07080712030e09040f080306031e0c 78
    0x9400e0816185090b00e680181603000072041100800c2083d901030401c2d04e903e40103503c000340d02d903d801c541c0135120f0511503d0407181c481044000d08183c0c0307424000d94076200072000c1d90b800d4003030411091000402000d0301080d0544100c00d0300c4601c1c2201008070387c0801083c0d00e80240564010301c00581900d10750781190b820322000140c14008091700099131980035800c224041212210070b640103004100070104a80c0501000501d04d00007900354000c80b4500d0b109440c02c000c640c1c0e0b115031030000c40e00c5842404d54015400c0207501c0607409500d019110541203024003507e481c1c1d856208884001201c0011a100d038822020800c41e0340e0140038950080c07100d1685900100000c9220000900c21070080c111844008260180342a00800c201e030043c00c0440b003120103a5071990074110b103190758003d084002070034541388041c480c24207080c194003856012203003485903840c66803868595000100304070f0305403084071054040e010a810340b90414a0503038014140050900040c081d408100041d441d403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 211129973 1250 211128723 211128751
    0x60905090412050706091709090f0709060f0909060f0e1501050307180803040303020303250207090b180c0a090803090a1205030705010504080d06050d050d050313050709050a05 77
    0x4a501e4031a15511040b1500d0502d07a540d0061400c1001017804000c00b91040c0e6248201c00c2980d803800c00101041d00049403030038134699803035407030b0280044122400000a1409001000514019240e801d5120b450303041c0000340d01e84500c842c0c822184983e100c14490161400c04000f4802a0425075800030071034050640e4000e00c1e2400a0903503c4003410703580400403800080c45071110921045c10181005200740d82c0d80e42d6403820003d40d2500256031141801100540c80c47c3c2160310b64014085840981e0090443c6034130706401c4000424107925030a80000085041c04000046944e140d481540754449903902e401c1440700080410000360003e0600c3d500810034440c0b560f6541590f1400c0b01c8445042a03660006858214198080d0100c010001d40c01c000c140000c0000d0007000c0d29086401800c1004a10350f180b00708070411084010160064010b0103a40c52aa84624011980582e04a00d1035050800d155640ea103030034080c0d0b00c080c10803560b800900c0301c01c40366400fa240c0c2003040b03d04645 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 211131223 1250 211129973 211129981
    0x1002030c090a150c02010e0303040807090504030810080a0b040311010e010f0605030d08010e040501020702030d0201090203011407050711010e0d0b0103060b182a07111306080312130c08030406090509 87
    0x1500e4a13480c0040603051240c648054a100d640400031607004c0c1a907c802c2c0c41c5296070301c8964201411040c4c42c01c030085041300c40010008031011000c03000b10b807600301c014060580c41e034507492403040c0e0180007607007040250b003160310180000b40078440c1c04080c041d0001503151448034913202110b4035074028902c250051450b4080b2285c0c401c04150549107200c0205201e0740340c40c5400c50091194941c025094040c90003c8103078550107501260350180258024495007000404160301002c0071039000000c280240020404910080c2152080341c1040c100400d940e030310000040e42a8044040850380c0c404010014810400b00b40600b4201500503130316410030f41840c0312011450100184840400c1104800340c1e20340885007054010003010003c1202c0d074920301401e10408800d10008031b5402040c18000f2050459507501c01c05c011100d80d2809142000940c402c00e018828006c1e1414001d13100e002101c030007191001e02045c1c01052000003c0d951a232400c40050160503465000611480300c0300204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 211132473 1250 211131223 211131227
    0x1225110a02010e0301060503010603080409050901050f040f02010311040807060306090506010203160f0b24010c020a05150706060602030406021b01020d0e040216050d030b03030313141002030c090a15 87
    0x42500740d0900745000c0c00101c034408a13004101981c807580d815800d08100004ac021034000510956904e82800e00c03281c2d992521082c02d982094500c01003502a8400050100b900410640710040c030514000c20320a84802394071120f5003064000d054180c111480c2084140c1c0c252050b20b00401c0c03201011300043c900300700042d4807401900010006003c0001c0d00c04100305c050011002100c0d4084da42280a0801904030341c01040f100541844041c89a044851250b001d50711543c02158000d044806581c144001d02402c00d480e19030b050307a07030b88060103064000740150055402800b4654021a05c2e185003450091801140e4880c0d403401c4000c005180c1c41c0c590380441c5109c4020000d050200d034090080010400a1082c40e0b2100f92901420844004004000c45c0e8000218000c5d84e0610001c101d1004040e264070040e01c0c213440d00c0b0303490601c110003c3c106240710f5004850100549a184d00700003c00380580e031007120b4401240030300045125003407811080400107444100c030025144040e0700300c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 211133723 1250 211132473 211132483
    0x311010e04091511040b16020a1d0103110301060504050c071a04050d0513120c0602011d03031501030e060a0b130606050d0510150203180907050301061103122511 71
    0x110420284c880340d144150100840c00c42d8010003e082e0b140750742d0b844103000481d140c000c084003240729003210640040e54001c213a0a0b80c800b018140d0924000303900e982e6901c8103002d01448015010b5494800004665441e845070324450800f0001080e504e042c545021306944900ac40b0640c490007a007014003000c6100041c1000c01c01682d030034071603a600040e030b161a0b8000d03c254040d01c01d11840c000c6140030070504c50584002c50b90035800900003035140c9100f210f0190f800421005031a0700c10b10004e41070001e004110f030303513081c410304001407190425070045060a40c100d07043c0100646030a000605420045a04040484402402c1211904011000300395220b85e403024050076844a0210b50024100d41e00900101603204003402e601d0f01004000e5180d8204200506411201510b804c0f5241005800c00e44281c903603070b440500c1c4be07003004416114000300c54a0580301c2d11091041405a840303407a5114041c03d404c407000300d80d030305c0300d8a0056061580c1800800030003124003a00305030300200150b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 211134973 1250 211133723 211133753
    0x804050d050c15060f0a061205070203040501050a050d06090908131e090911190501030513030806060a0302040801020403150c02073005100c0f080702060103020d0f0c0311010e0409 79
    0x10f003000940c469200040051402c6205158070446070180021100d8024609480d0071305128014000f81e03581301c41c06d0b42c03070303014510400d4003040082241151441c8100010700b9640785078080066010307140c04a01d030458990060450f40018005862903e02682c651110014400d5070f144400420b45124041245030780e42c804c13a03c60b80e494080c80c00401550085003002e029010f080f00c45194050903280300038200610a06020a00c0c010100300403c8100b000183c18a03010380721006140c4421090041c1580b2001c5181d04041c2d007484003042a0305c081c0001c2004500880c00004010b04501c1d0740e100303d4080d0540e540c00d55000005c100a21500c484200c00380010a185100540c0410340c030184044c800f10000134054041c0d050010801d045550111940710556503912250a03400a015203800344195034038000350303202c40c004100500d4244501914a40304060428601e01241e480b6030a1001a40080f02c0074070390b1640c800c18031359000c4001c1d041c9080440702400b010b10661201d03014005003034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 211136223 1250 211134973 211135003
    0xf0d090b220f03020a0e5b0503030408150720070302010e01080411040b01050706060906140d1e0807060f090201080c0708070b06040b10020c1305160e030f0a030804050d050c 76
    0x800102c0c807d000031041c0180144992403179801034040c00595100c14202d40b08010252115113802048a0400200740c40503942e0400060030009040584100b4200006082c242008040b4610803141e40014680003819480170000305106819440090410104a14210304110307200c0100804116003105152048505450018044420b200100c410b4402c0c200044c00b02c03405c0c20070000c0c40c1c00c410391001c001c0f501d15074503030024000c0083c00c1041001030000050072708031803404100c40f0004c5000c001003031b0750f00c584201031a040c95691104240d4000e201c0311028940c0d038455440a40d60403620940d44400c481100c1458101690b48000d0140140030011342441418000521951030350741c0080c102080080000600018a02000350f5480615802c103004689004548103031241600407180103c82102d0340880d4260045002c588170390555141c0c540c1403050f601c0d1201442418031280d82414000d03901c5c06c91910b8541050303403800321040c40c08010801d00700600122800c011980c0f5019442c2c04d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 211137473 1250 211136223 211136281
    0x20619050603100e01270c060203270a030f060b090718030605040204020409020705060405160e0c280203130b071205030a06030206031303020f0d090b220f03020a0e 72
    0xc919654010243e00d511018950560200c00700030090006c46c002c080d510450a10102d0f6407601001c80e03d0703006603d101e1005000c0c1c03c4020317642ca00301d1411450040c070091b0801e14000d5494494410040c5002c0341035443c02d035075615422a40c18810780841e0310610754204990b0040110b41c4465640d0140e20000c1c0ca0540d581c808601150b0b100d4040382d000b0b00038000c4c01c0d5150b80381410419200d540c1a102111140315100c40306d1800464000200102c0f040d8450f801c01c2c1740d5445003001004d50103140203605213000100c920b00d015078440c200141020f0300d54002e54076503c000c0c0030591024005d405c246800407052145500003810000040c0000a191808603140c1d101d07a44d522010f018103400081d8804400310800c41050400c04401090174040d43c2210f1100491071509030701c98600301070907000a441d414041c03180f2070400c0d0040c9410207121005410160104031704003115409900f0009a12400301000c10640c0351908510010b801a500d081c031850400e40c6c008080c000d0070f042e0b11800709a007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 211138723 1250 211137473 211137491
    0xc0a0b0a020309100206092802060a03231506031501030222030b0f01050f010c062c0f060c130312140706050a0e0102040b03150316030302061905060310 67
    0x3082c800c2d80e81980c8082c0904240402604000c1e40300c120440e81240700e44503040000091801240d180c01c0070405200f194841c0080e140c00740f050b69406030680c102450b031100d4500034034410740b1101d060340302604850401d8a040c56030300c3e210080384521002d84160303800c1c01070000d4000517022042d8002c87c05d003001039582d1407040000e405034855040560060403e0ba03030010034420001d0141c0d200d02c0015000c01020380c0c990081000c41010724070801c0c0042c0303c0c400080c0016402d035010b0559200201704501da031515241551040820111000c98075403c071003000030f140b00d03041280035080340d8018481030414502d030301d4031000d001680c4001341c0740c0700300300b807400f15150300440501c461041da0411459403001d013400d00300e01800081d10342a6a0a00e0260711602c48070301842902c064804144c1540e00d55100c1c9480c1c038014000c00c99205a040c004c3d5200d0140d85014111041d0040d8480c1e00035007010700c4c0c41d40304010048000d00c1411522810032082181903500400e00c2c60821501c98000526424 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 211139973 1250 211138723 211138727
    0xa02090a091119090b0409050606040c050408010c0903020315010e0f07031104150f1e0e040608010617070609050a0527090a02090c0403020d140f060a060602010c020c0a0b0a 76
    0x520039040c82e000b0140c08982d0240300c0c10490f81e503050360800c104c148600c126100134401120003d92020f002500010041580d52416800c10907540510345410781c203064036580a2407c440034511600c0105400c4203003003045003024404030f503820b8480c0c01e01d400710b0f40c50842c004d20b500c1801485401d001071400d00041c24107000354001c012004074101d01907191529800b407510b84418004851380880c0f000e2901d4800b40d440340c40480900089034a08101c8008081d41c15910302040700111544585c6503940400c2c104000d1007007100416500c03080710045100c0c080410708000954205608000034100f00f405540c4803810707034504035241525024950000e20b203900305550700010700080001c56950610610400004150b803903075008a5086000392902034480700b96103d02e2000030b412480000c1c00402043d04010001100c1e45804169617811041034402170803d102110750a8019503552428042142d091252821805040c00108220380c000000500805607600c40d6020403503001400c060814 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 211141223 1250 211139973 211139993
    0x70e0414060a05090f0105010605040b07080708071a1005030705101e271203032007030305040b0a0506093637030e1c051501080a02090a09 61
    0x191400e401c0c1c5076a0304001005002624054a0000041c800c0104540d807201040c071031541296035945841d0300d0107291040b4003500e034010324800d42d05681c00344210408124140014404288904e024802555402001c40040000a4070740a08101c0300c2e2001d020366100043c142040d50011030320076040c0c2000703010890f0300c0201201001c00c125a060442105980c00080c165031310b1984c070b00080440100340300102601140ca22500f4105010f00e8034240105e4020390010700d00c106c400300c05800c06e0310402003c080551000400301e0001f42e94108010620040c08403035070300300300702180c14082e9040c8400050210720f4064900140024460440305007030810051112004580b05503501e900c0240494094503046900015a151b03240d08521440e0980507203007500c680300c20280d060004e9003454908549041610740030035081281012a020184401400d0103461441803008141c800c44040010010303c0c3d069014056581c401409103006a581c0700396554042c0416000141c4e84c0b0722410451820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 211142473 1250 211141223 211141253
    0x1b0a05061303150c090e060a0b042c0411130e0a110306010602060603070e090309090a090203010c0203091503130602070b18030f2205031626070e04 65
    0x1001001030038481e40c240e264202002c032402000d42c3c9200c0c9207903a038050140e03882d5580100000350341d01e0040c0400d107064201c0f2500a4805080005062740b00c8100b030510b544070b90016201515018100f541c0602204001585030304a0000e200c1d050420f0fa1f00c00b03110060403c0b525210354403514950a50304010340c8903120107984003045031000d01036411700340c5000000d107802a0186c0200070001c03910f5800012900c0c002c500203401810303c03501c0c00020000c404030242000200380010029410b10359130f50001a030140390b0100c03001031014101e10416003141d801d61204820f54100740032184060340d601c440c181d54103001c003404980e41c0ea00c00000304c0d0000e0410034000e00d00d601c080f480e0014071a24489a42c40b541d42103d14000c49018214826540d002d15001242e100c0d00c104440b0b444c004620540804005015030126801c0b0703114400281040541183d20300d009051301d20070054070b00d00000c482000441031400700310b031046090710f0307a468203164040d00346060300c0c4d44c0c0410b007000a407003002c54070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 211143723 1250 211142473 211142479
    0x60108090c090a0f06050a030f120504030f080c100606050301060c03020a022112090f12010b0a0e07030c091208070503040f0909030801080312010509070c02040203040507170f1b0a05 80
    0x24520f0b02402802c0189488484c0c00342103854034030301082c41d013040c0b10514141c7c0d0b0080880c40a00c3d01903036440007002da400c6000702c2040000c3c04000001461102c01d00f00d294031503900191200019010146048000c41d000b4030090308050017001260b80010840c2c1c1540c03007a1910400d074141a08040c0d02d006002e16000f50820960440d403140050240d00060007280300d1400d1380e0034024030821065240c041c0b4640319900c903c26015900b82c2d032a00340d403449210903142c0e0011039150030b00e00000346e030070050303503c01c80d02c4580841c1041a2140c2c14480c80c8045074560420440f40350808017050041e4892aa008056442c0010314030240b010410581c2c005101210f601080c0e0713a100e00d250005008880720440200387c164002081c2544003000342d0b000030020018030503060b843c10041021040000c0c15000510034040d101d50056221030004600c210700401c01407101d540362803c180c2c210403941d01c1003040c0c1e40101d05103034034010b80801c21400450944580f02444140000060400d8000780d020583c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 211144973 1250 211143723 211143739
    0x90d0c170c06040602070e061201090b0405010e0115170114010f031104020a170a020d0c020a02091302010f030b1c0303050a11090a03170f03011d0717060108090c 71
    0x10344502a590351810511032541600d0032400c80c041405114000c07400f4580158004840500070b0200034690039902400c01061310728101c10b4441c5d02800c45801c101c3c191080f40d030780c2e030030402402000d001c1c0d4441704a42c54004c201d85e03c0290780340c0640c43e10a0091065401e20415044414042500302c0b0f00040810b08400b440340d607683e03400b6800010030b48401c039421940701602147c07501d0913109440da00981703602d844811004480b0700f040711000003489028000d030301703001d1252200c07821300c40c155035100c2130740043c207101d5043d004000c50180024440c140d1070444038070305130060f64001404007030058075040100746d599801c0c00040b0324061780f14245600341030307401004041c0356068000ea400b940c07800030204010740c0c0c1b0107000303045441010400c9411944a000c2080040c4c0c3c04113061000c001542c6520f802d00500751540349480d8000c0e40716a0400b0205024902100340c4d02c036001c0e40041075410607511180e8109011b40c80414005d1450703042c0414080003175603017401800854400340000f007480c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 211146223 1250 211144973 211144979
    0xf030c022e06051516260a0906050319020901091a1804020c1f09050604030c060c030e0d05090312070b01080f0607020727050106020f0f0f100504021c050a1703070c08090d0c 76
    0x20340064003c030000544460b00001c427580102c040781c1c050643d00000c02c0c0c41c03404194a44000c0d6010500080c10840b4110001400845001120820115126215540f0703491643e408842541c18100140f06510400c0b90320580140014040d01800421a0030300030001d11400c191700600300700c10051300501540e0200303c10140c1c41251944460f100c0d01e0104200010304000310100c400302800c15200c0d50009890546a500500280c8031000000782101c01841001c0d0074501c007034011140840c1c01d4a00c00e401401b1504c018842000080c108500a0078645003801c00295110b0396480f50f8481541c070410080481c956010042e0009040940284869650307150300a55a400980101c1c1030342c042c101828611a001064070309540841a0091070343c4007030b1142030001420081c008a901a20203100e483c0241c070241100c251450240f00070b82140d0460341000c1c1068201d2186c0781c00844000c004201d0026004002003c85d01d400680703058039030f005040843d882c0c00740c803940a13100740c43d844400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 211147473 1250 211146223 211146293
    0xa0518130503040b120601030e01090b012333031911040504050405060702010b06040b041703130b130f0503030a0c03120905070f050901060f030c022e06051516 70
    0x2175010380401e903801c100521120132070900300c500804c0020701c114050341c0100a8802e8007000d8603808210803203295000480003000441d1200210200e02c100d000c0f1518200c0710712000140150300c0d90442541d00c1c42d524185242c51070900a48d40c1c0003407119070315070040304209002d03802da03005080050810040e9041504042d40c0d501d00c1240c00c0b00056080c1703500800f031402c241040e0303800c5500c403499040c10103050041d1059402040c0000107001d21080c0f088208100318005000018191100d919a5580d400c18003006040c2d12a0800e407040b14110004001d1500d0000032582c02280d00d10340038030300c00c102c4e1400300c408035201d0705c410f501c1c54204084031040c004045401c038101d484415803c10001e94520a100c82ca003030903c01c10001c0741d45038010000080c040c0d0000c03503041c2707414419600042d1089090b1034406818110448034011444807a20b02c0610340e1103080d0150004440c8800f02c42003c002042140c80307222121401c412040301640d04214a07680d01c0071800c030001446001e407041054039 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 211148723 1250 211147473 211147507
    0xb0a1b060504060605031b091302030d05040f0602030304080406030e10050a06090b0409080a0c0512270a15050a0c0b0705070b0a140103080304080705011a0a0518130503040b 76
    0x82620003614101c1e001611b45070018144007030aa006840e00d10111081c01040a402c40040500303501c04100b54207200140e60600041c403c111290701c40b0358803035040c0145402c1c7c003a8150015019988100107110216603880255811500c107840c0100707251282002050a01010000343e60032281850305026514070f81e07810841c15a000b03407008022890b4100c08000659102041c0541130410400c00030761031500c0b030b01d40c000d0f1003030092084074002e00d8240c10020346d81d4002840507409400d28180100d0f00c6000c140b10140c81041200c0c4419000e0804561100d4902d04d45840e205100c0c000900c080380a001c0c9c0720700c6064a801c48010a0070b8902208080c119500804080b02d0005001d030004521090921984140418a080c505004e030308545d202c120f250700c058000d4800314010703c0984002034090048651501032100c00b56003507546c3c02c092204074a1030340c01440c8585c94403e584000c60405070f17580750f4800d603804003c04190754a0b0400604620890b00103204520000440f106900f401000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 211149973 1250 211148723 211148731
    0x7090608010e010204180b1f090501112b020c060c0102090f06030f040f0201030b090901060e1305100209120303070302131215050c1b07031b0f0b0a1b0605 68
    0x3800b0078950307203408508034411070140541200c0c1c4990074848064090784071802c0901d0260090403054414031031111512122502c000009940030028400c41d40c4c010840b100c0301d401300b0002d041c08055080c5080402d200c0301c0320381e03008104a13440f10160b40d208001c000303580781c1c019181d0b07591000c001c01213501075400031061601540311488425103906103902283c7c410050406000b00035240c50b03441000001b03040380c00380d041517180d0030300302071319510b2080340c50180c5281c00c000541980f5101c28189132040060407464400610b51350308001c40c402080d10001e03440b08150059a503070348074002074046e08202c0200401484088204001150503900400803010b0003510402815522890f12414004030031004018031404101420303c92070340d41007290458101c00c1101d061045a0412040c08101041c1c0f40b801c6610000c41001400304c2035a100174420140d0f01042d031403a04100594985060034411807681000000304185c966208071501014040545803d034006213090902c00302815082d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 211151079 1106 211149973 211149989
    0x402030304032a0914070305100501200708060906060607023d050417010c0e0d260325020d030f0609060e0403080108060f010b0a050c070906 62
    0x24001c10190918139070000d442020700340b01c0c007044500600300d00d0904d450030701030100b44400ea90502080c4d440038204401e1302e81c070b11410100e043d051030301d044000b8041d070500072500031ba011034500c1c09030000d074046407290385410040000d98810306030000d51004203040c000426401400a4181d031503184030140105000180428200c01d6100c441440094000113060012407100100c0c1c140d8800c110000300400c902d00a0301618000501032254410f04010400404000c05907025400350300e040c0b403040e11000181c0b00301000035001501c014041003242001c40d5824209214500c005030020750080c10202c0b5428000d030010480603440b00b1103281c44410104280c00036008920041c118400c4500862800e820020001041a0812144c54112720180440c2e01000295141514043c031581545c90814020554440c450700c05c1c000e83c0c0340682800080c00310340301d034081c6003103800360 = true := by decide +kernel

theorem cover : BRFrame.Cov 210971223 211151079 := by
  have h0 := BRFrame.cov_init 210971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 210971223 ≤ n) (h2 : n < 211151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
