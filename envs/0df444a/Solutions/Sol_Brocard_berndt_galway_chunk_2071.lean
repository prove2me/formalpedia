-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2071
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:32.25865+00:00
-- url     : https://prove2.me/submissions/a5260969-fa8d-48f4-870a-a6b68fb9c31a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 372302158 ≤ n < 372482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 372303408 1250 372302158 372302167
    0x1107030210120b011e08072a031202160b0910020d0e0d17130305040b0d0c020f0d05030708060d0609060501080c1c0201050901021005090a21080a0f02 66
    0x140c44940341084030907495200c1600012003115250b040e96a41185541000000b0f9503010318610b2141c640c0d8280c41c0c00d4100003459441d03111080b1a0300754490f50714041302c0850180780104811144010f1816030080d985d44940059600030300d0281e1051081c1045410b0240c01d1000102c1c03810000d85400034280750445069a1078595103005982024014030059aa1040e40d03c01100c014040e003089040d052500c2c295010120700711130030415010f0704100100d00740040700d004242c05802110090008074040756240e41400200c840546007811400c401400f420346869004440041ca000da140c03002d8603410b04580d01c90782d0461b01c56800902c0c142d0f210143c9000341010078800d10500d030b10503014030030124180d810081118036200310144003a02405a40d031080080003040100045441e50910f00340781e49428050040b8940b140040640303581e94540000d1100d40000002c0d8666060320400c2c00c4c0340f81c88100b14503885045400700244002c86d0031100000c0f000c0c072082d8071000582c1249000181030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 372304658 1250 372303408 372303413
    0x3060109060c0c1a25020907050702220902090a02130617151c03030506100e030a020405130b0907080c01080f06040504060e071e120f0b071b0b06040501061e110703 72
    0x410038403042185e01d05e480341510000c0d030811001c015407060440c2022440c080c1e05902007540501f8805030004440300c50014001c032030303815410034121280c0082690060341850405c0702c009501418110485150006000800360b000e480291840300c8440b00030b40303865803039082d1b80010380c80c030340a49948032141840e424020340c0301c1070044540c00e0003a5400212031916100b404011a02441e54170301380700c620004140e40b035600003412200c699054401203442c1d01c814081404143c41070400510074a09541000b4500030700048171000ca5040104440c0b008400c4001520f132000701395040707662900140005041c0e81041e03041150820701c80c250006004138824415400c1c01c846030480740c0ba2095209016007901c101d01c6502c00905881019031440241c0d075a140090410040340041c80800e10900280455000f00117400040d004d8070006e103007001203850031024150f021180703107100b940350500100d0028031a22281c4c1e1400740941460a20094501d0150791000d030400e201c5070340d4416410007000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 372305908 1250 372304658 372304687
    0x305180607060203090606010207050d03030e15010e04031b080403022107080d090549030305040302060a0b010e0d020604091103220b150315070503060109060c0c1a 72
    0xd100e008070310050700c0f4141592900d040c22000b4041f541154000f02c0144040e50b20a101e40318142da0505002a03e82c5000c101903003041d981104290200079504000100c00c55005141e40c403c0780301e90740d1030320004600d000c0b00c4000082a00d014146280600080c001400c041007007500c503140c041e4140360204c81c0141c0c42d43c540a2a500400b14a40100301b1031190319802050710400f520044032407100c4420807210b1141d2600c81004014000c107024001102c1d4190039400107080c2c00c014020194941c07009050103030181c802610101c00510540c07000400c46195031088550b06001603440f9002916a0700400441b40b032001d1040e030b401441000001617104c1a4812a40c41a428041c5682c0320320340f01f43c440010303007400260307071620302e9508003c2e80008061a016540c00b11486500700c44503002d00d00424a400e40b0080c1d1a0309511502060080560300800034600c103d0090760b501c42d40b05c0c0c803464115180c0e51480b400809403884d400c800e1004001d10020242c02070500d84050382440404080d080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 372307158 1250 372305908 372305917
    0xc0c140a150b0f0307080a08090a0918122f0c0301090501050405121206091b030a0b1e0a090906090b0115020714011e11030d05090d020a020d03051806 66
    0x58085584001e0210baa0400850710b0304100c07400c038085d003421842d00c07442a48842146400030062800000c8051440d5907080a11000c0c04070f1907410031540c070b41241d120b50f811030071841c15100341900c40850440e081c8582a00168003100000c03c00c500f024041d404210304410f4030030703c0c01c2409101415038441e02c00b446290b0090707005c2c00010440f0b040030704145003014000d04070b0402000c82041948007200021074071640014065412020a54845104505514101c85880d0480d80c1c000148840d0710766642002c40d141008450700c001036180c441c0c1384001541a201d106401c441c080320704004452130b0342d010800302405030401190740b2403540e460b40920031003600413103104a210314140300c4540d41080f480000c1d201000088000c0c03140980080d248180d418100407400d46a16070502019100d04d01da070074420301c0b4030202c98617440180d4440018000c220754605179446200007280302c032032001032814211500540384040300043c94034111456400700c80d41c0406141007610790181c039110b010050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 372308408 1250 372307158 372307193
    0x10e011809091109060f01051207020307021018090c140d060b130e0c040320030a050d0203071a010605030f1005100e1011030f1c0e1501090c0c140a 65
    0x90701d8039401501000140740005c0c00c2903000720018902002240d81141c210b815003990070100101a0b65030000484c510b200c0c14000079081090003481218140d000b1190080c1620444059032030182c96088440484051400010002d41242c940b251104504001030000c1b001220010031140d403503820010b4294030031100480360000f0490100010315442e090f00d9080341e176450b07120740381500d15110300d00c0d150700a2440c440d0f1224486003079211f6a80c10032000c928558000d042d9010200042070180d26904000405e90344103e05602c03400500b90b1184606040c8e1b14903031142e80c1035484001c6001c01c0158020540341140c16581d10104056950441440482e18103a483d0b00c081074001051000300035000020070244003100410408003400401030b40c1b480e00c01c0000054480c2d019a156480c0d02400540e10358145240c0202c10b800ca150110305400b01580f20701e01e100035030340d0b1180c3d140115850140c4c0d1100190302030100000281c001c00c000d007400c51440c412941d241050752580b00010102c403550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 372309658 1250 372308408 372308423
    0x3061902220e061e030d030c0e04050a1a01080907090c050f0408010203071101180b06010903061d070f060e06090a08011a100c080306040207051f021305040209010e01180909 76
    0x700f0030b89261000741500004a0f50424401c2c0d140d50ba804039544100c0540400305150301c0703010b217000d214411410740c0c0d0000c00041060215007401d40700d24004002c0d0241403155004e243d00c5c000c000e9400780e6100390060440307000a0002a14141128008100314007100e4200030080008007e08140c80026102800b0345500060362801d044078041e0910300401015056030341004c2601850040490840217030540113486000907648601c0100c0e03078542103801c014011441e004410450880c0018649211282d450407180180c0e01c0f0910701c05c07000414400c080002d42a080401080c3c10203001811000d1000340050440c0d40d00c4821050035160a00b142450280d161250403c4c1454403010604c045007603030514002c00a07642e20b40b0096440300800d110f00445d00069000100001000220600c040300b0030805800307080e065404029501604a9182040c615500440d06140501c21908468816103894500c011070b1030041d41d8024489a5110300300f14040e8001a1384505c501880342064414010b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 372310908 1250 372309658 372309661
    0xc0203040e0403080a06240309060e100f0c0513060f0c21030c03020315010c050f0a030804051b0f0409030e041a01021b181302130f0b03061902220e 65
    0x804044a500d503007c00032051640c50358100344244d54000000301c030701d10f00c0d000c40e0b000030b2410445c024013000074240140740b1a0340030501d81c2001796841200c15a190039014400004002012695030082c50a90b4004284241c01000124022080d17000300f03440500780030243c0a2542c460412400794100d24040c070144022044a02c1c580c54403410200c00c1182c01d08505609280031074109001c0c2000c146418409607958100070320604014810101c00507a0466042001030310700100b009005460440303451244845018801000c0c001c41044088090002540201d04000b00406006104015014048400800c1015840703074014210010719040500764202164000285002c681000641e507046031594400801d9944100709540804049040700503616030f1a01d03010810180b802c000d600c9148520400307901c49150b0070a0f08800c05041c0704000340500f83c0d06140e00c0f03550032201c10852050b805030601200c0480da01920030410f144004607800d0b1450000c1408140b00c907000003008802031030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 372312158 1250 372310908 372310921
    0x304030c140d080a020a05130f030b09010905061302010509040c210e190206130303080f0702030a0e270c0c010e0d020c1c02041515030b03100c0203040e040308 70
    0x984180119036110081c003145602c1c1c24020a007400103401d0485541c0c0000d0040b5555200e041607400ca00500e509030400301e556100240301802403444112101c054207400620a00300c10b03c90748030f1301504400a00328943e580941001600741c9854100d0501c1824484809a500c03507200b81c0c0500315054950b0003000c511444901001c02180d400c0451031424404a8082d006000c541c03080d2640d050040b4815080580c80000c1c1d860281c0c0304401d0300b150050380c4c000145580640c500340580c0001c00c5041981c0c65102e03080b41ca81c49046449400b195100080301d03507501b0402a00c00350072000000740301c8580c054800c10b02d1000c10540d8800e203030802c00b00707403148012428070a80e09080300400040194250740342e0069198145180700e10f2290001c8429441034044d20460000c03000d40c010001c00003003440c40c2c00c400f12440340303000705078444100f500c01c0c03000207019204006841c08018020001d58401141e840090810114038100318082800b00141c00070818000c0c80c080c6110f82c40b1380d0424070b40007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 372313408 1250 372312158 372312173
    0x2041a03011b0f050d1820120a0f080f0a080109110708120603190b090c0109030203060a0c181707151b020609040c050304030206070206010b310611190203030301290304030c 76
    0xc55458403e2211000c0c034011600c0007e1401c41c26940540003006070303052030030090b0550141801d433041c01d41d00000c16039012903012403040c3c144c030b10810382004a6940e002c803107100780c06000070007400c3e19010480e000708604d216640940c006001411645081d074440801d218510813920201c800319090303c18400a60004d0184231040042882c2480026145400007a5a503001401e09070f0354564490b541f80d42d8a00c00c01c2020b44070342c0a0600d9001e1300d0740c0c8040c2e204001e6000120401c0c0c5010f901004a80c5049010b064907010045070b59881c0300049800c5411050304600700102c8e403014081001d407800c0d0700c442c043d0801810b915125103440c0c1c5400c1c00c010381270030b030028008411504400c0050100501d03280a90389084a01c040071181800605040e1000380010150032990016200000801907484003c40640303554540076124209155000d44510303031504400250b2540080c0014030080040d82c1c0c080448401c92503011001c4c0300b500c00860035952081d20288c000941c000181c00030b01800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 372314658 1250 372313408 372313463
    0x2103090c090507080619030501050c03160801060203091035070329012007090f050103050703020f030a0602030a0212011d07110a02041a03011b0f050d18 67
    0x6107405012074500640c0080c598040140880d200f001c000382e41313000203803014007118003559106000b04040c0c01c0030700100c0384c5d07508212181a0500301d0b0800c07165010303200784003ca040354801d400540c00d00001404011480d41003c003080100040c100455900410451984003603031071083ca00448540184103130013000d03d0082ca03c03001c1c03600b40007690b50f8002500703090a08a000b018400b06e614015640100c0300520840102c5420542038800404407a0002c60404201ca6202004208148003440e800c016a00240700140245d040301038104050304081c001d610038414010103131031007151682d0b90030040360030544450211641c0420442e0003400c1c40d40328140900038a00c10819400035502080440e0701008115104204001c000a50350380000c028440c10183d0082080c0507089000650074851100803450034031035800c00c03510800d4410610000c01829500b07641d41d41400032960000d551b03680c8440080d07a0865565148041848050f170702130800c0030f10804500508024120242464000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 372315908 1250 372314658 372314669
    0xb040312050f04060509060706020c011b03060e04060c0915090303090504053306070308060f060910030510050a090b010215060a030327060216080d050d05042103090c 73
    0xc00c10480b1001c00b40d5400742c2e003c540e0180740240c0d0f50800d640102d941c1d40240034004100718000700c0e16000342c10044d0400400c641040320325a0200c182c100040b01039800500c02c04014050050205011902c140c2102081305403d06124095a5a5441110342640040360b4a0b0003d03644980c14010540d011880a0040070215818003050a0000b034000d07031205400004008620717021448102d90040514100d89008020080c585900b03050501621700d40c01240e4003803158148051540f00b0307180007019100c1c44c820241180052a84e0060140c1c024070b8003074580400c00325000d4002880da85d4003a07110001d0314800c80b02180b4100030900280c5461502d00403c8106031750b0070104203082d1520401d03d0122030301850400186001800b9031840102d03064902000310005200c0490700640026800c0f590320b22034005000e0791a503030045036442c0c0140e0405803000a4082200c0e4001500941000d6009030041c8141028520141c80030400303c5040781105021035107421800c0140449024907800625 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 372317158 1250 372315908 372315917
    0x40213080a05161503020903070503100b130c142b0e0f1b010315050402030109020307090b0909072601060306051905130c14072144010b040312 63
    0x2d040c04400c0b100e08110721130322410540e02080c0c14540396800c00c420740040c24098140e80c10b040011440c0e9018040f140d49981c024004141c2e0600399000358402c407804080aa95994a04070306500c46108590144031048c51003118443c500300c805403d140301d0243d18031040e400103100c54a00d0010390810b12601002d42040d0004801ea0aa0a02c28803204808040920300003a44c402c0003400c0c41124407075a0001600144044004109441180d004500461898a41d000c110b84e844c402005503100349105c040c5c100d038a1070085041c5501808400c114443c611520440d0041000409402110700342d104000098442e00b0411240c102112104602c0c001da0f0100550700d410038010444041d1501c0c840c1504aa4542040b01c807503100d0340c80307910b9907441117007100e55540950030024540406240d170314003101c2122500c1d110307140c010b89110304003800300c0c440956036074212403640000303408000c121503150b80501ca441070084a540d41c15030103001081c82d10f40d22181541824011011001400c1c4c0500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 372318408 1250 372317158 372317203
    0x2120106030917031f081b03031810050405030102070c1e230d050a0804060e062505030c030408060906010f06050316090e04080306010806030102130504050402040213080a05 76
    0x20b50f001ca00c0d2141e0807070307144566503940368104481540c00c80380c1d42d45c1c2d024040c01900424001d40104021404484180c02003a04405036804c050301e030700c24045403401828940911007014201202e50003580091810f18a081c00d6490b008a0f082e07a002c020203c0b2613103542c1e981440611a503200b1660074840412021007a0390a00d0109100e04a245124000824800142d14400da45503040d6400c00c0381c1c0301c0141c0746400310924280036141c000703001d85d5010a07a120f46107059800d00d038050360041c03d00c1c1c02808282c81e2a800440340300ca4030101040d04c10b400200041c20009004100800003840c0f49d034010803480c80e18a80150074120180c01000b40b0341d42e1035030100452a8444141e0750800c55507010300c001d070075800100b81d8484030198040605001c07501c0811043c0b1440c000a1031140000780c90300905550340604041c203d101e181d407580070300c10000c40d0600c003500f40750380306c2c1768433a1014100502e044c81943d04840c4180c4a94011049070b030040c0c2e248000c20205100810030b0107070300074072400034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 372319658 1250 372318408 372318413
    0x504061b0e04020304020a120803040506160f08060d080c0f0f0307120f050c0607030c1e120c03020c0a21050702100509010507120302030a06060212030103080318060901021201060309 80
    0x450440303141d403510981d000320106003950790f5158804010140c9110351481d0b05187d15005041d500104c07015981d038041c2c0300002d00c12801c2e06031040c0c091411551180c100006100043d04c1c2d40c40e010f00350540145440c9000000913900200a090741c5940c48001e080038441c0e55003051508182074510f88668009101d541c0000d00d0308070100d10304140d2030824203010500f0742d44c11201e50040104d0100140725450900c00041d4059100c02c03280d081c2ca564621991344101c103846104522800003000161103000e03416240f2510303a0081e809905140360140c42c00003400d803906d24140c6070310800d85003224130700180c0d5414410136407400072001150400d1400c2c00307100c0d00010a004c89901031001400800a040352641c1c1c0f20b51b0494140b0765101a86038000c010015000303000750412078800c03c549181400124000e40000340e2203244e0040660445e00e180e0079603440ba202070300068035078280c08100c15075a0344201810311405213301c40d103100042c0c5070003d0907600249000113030f100f070b0107043c5401c81000c00b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 372320908 1250 372319658 372319667
    0x2040f060207031e0302100c0f0305070f0f03050a06080f060105010206061c030e0f030105100e0606040b1c0e0708030a0e0a030f020409050f0a050304030512190e010513090504061b 79
    0x40200300f40d2060703140c02c509810182e05000c0c40c00a01f82d81c0901e07212003646c2451300052080402420340c3e404109075070300c001054501c846000d9906011599181c03e82144510035044594044151031380805e2299403401c05c94505105800300d00f1a64000000500040d40e041042943c040e43c01c0312002c101030b124101205080c1c00c4000003404200c0000700c260781e903884480d90401c080d400a4000c00c00c2d0b142c544a450301683c041d000315540c20f1f0101d80401e02d10714200003a1400d0f11600c0d07407810300e4034804d2505d62044200401c603c2c0c0003d500c8a41040700b9a0f41403040384c0080600102855942d80700a90040c45c45010f0803602e48550f075107103002d1002c100c02541c00c17203000368180c90009090302c4900700945400c5d401030213002a4458100c01408001001c0050801c0324803d038211618211550320440342e5025074000502061540e20420303502a1003201c90700c2004006060030b0f1b20b0b00c4807605880240101c1500029107254407082070004202c264400c584440490081440c0aa240380c1703001003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 372322158 1250 372320908 372320933
    0x3030c0b062709251e030503030c0c0d1e0305100902040815090105010623210105010e04050f190b0405090109030815100c11120102040f06020703 64
    0x1422286940d001400c02c0c0c0325041c5808403541004034040c0000c502c080401d40c0c1e85000c8403050341c01d010340c4280c06000800c000d42c1c0600c115401c3d5200700310314201440103240b0304a41c01c00e1001006091000408160148000e50142100c01e00d02544c411640d1002443c02c0d040e07046810420078140300d40c1181d8550300180400d5580185004a001d8032203402041090b2801e8114820303081c070006000a01c1d500014040c8460007102d440b0810a03601c4000c41c50803500e091145a0102e942d031111480a0041141c00c151928a0702c0500d500b0b006802040714a150100074055091542c908014016582c001c0a56000000200c1d8203002c2480c184d40c03c0c4403003050160211000450780010035807442c0e01a0000421884064800c00c041e14040348180d02034600f00740103401091411001c10311080002c51032841004001c8c280045251604c9011a07100448070011307200da0250348405811a5070f418002c00303404149030000350300c1d1810701c0180110611a0f07032000d0705550141108000003081d200404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 372323408 1250 372322158 372322163
    0x20c012f04060509130e0f070f030f0611210609090303090d031806050a0501030c0b0a0f05031003050d020d0f0e1c0212030f071b06020a1515060819020403030c 70
    0x5079180c14840005c070703460b5410320221045031814107800ca0303095200000d0f42c28441d6408811a4155a504e0a000103a12841c1c00007401d03068182e48810081505604200010380090103060302d8030034940080740f221904003846120040e4402d0920030540b60090315650030a2018010b54036500b01400e0059a4541000d6048103064075240c18010344451400702ca01103a0b0000310500c03080c50820301d2074004000901044542c1c01000c00d01140c103050b110161240300f0740a4a43d02124158800b041c0c842d44c01c001c1040e0b4503264100404000103005001440a000303164009102c122000c0c10081e191080428034030041003010000c44200341d4440f0120504001901807031150b489480c0040b0744040703010342100040c2c0c800003842c0e41c60703140150002c2c01300e075004949244078211200c1c42c20050350801d1103048010381c801c0e5100d00c0850512910304c5403086448000103900340e6401d85412030000c0590cc29008189100304201441e12404c80364221b110000800718686400d5a03805802c030010030324003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 372324658 1250 372323408 372323417
    0x90102072103030b06250512070b011a090319020409150e010b030c030a03120207051c091406030a020c210c010b0a0305071710110423010e040f0f020c012f0406 70
    0x1000f00344182400844642d1042360129542c450550505c404445400e2041c2402c2c4c559130b0079410140c0c007103101a26490746e0003c010341140440b41d07004104252a01c02c059030320903581d9585034005007a040004400d07821000c804503c946884408034210356072070001a0107500300b0750807562507607004100c5040f8103034182841d1115144a100043c02030195100c010854480ca442c141080c52500001c10604001982e46014030b980b15400c0c4e100c0040400090343e0418000d04c08607012242e96009041466044421140b0340784042c000314516144290b04000c6400000555000000c028005c2503840c400507550b400e0541d1843d036896a565032107129108070b071141506d0302e80d03e1500a01007000c50f540d500e030f821300580e0309403034140c46103600521401501607e4540114030001c0c5074559240700080585030b980b001d4491009020261840b0742082e03440b41d94442140c4071100a501c0508084d0b10b01400000303864031030b242c4a028280614412120484400407003580c2c440494040b01c00340c0c2c0c4107240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 372325908 1250 372324658 372324727
    0x41d0f06150715050f010e0a09051b011b2301022712010c050316110c01051c1401030212030403050c0d0204060b030406050a0501050402090a0b090102072103030b06 72
    0x401650303141c003929400941a0a081c28031607603a05c01d20045058810003071060b032203616101c0b1008129981e1000050998103e0341d540c8840000198100386d455406040030000c011801d880c1401400c0101812503004200103411040060000a00000e80d0031100085291240302d40705a85400916000d02d44c1e03403000729007009066244c61050101c0b414546009000b0f4400b40c450141c041d820807034080c520780a81d84503225056205074440c040d02c00720340010b070140c009003000442c2e441e072202002c1000c0c026091824000000325206050500031919502005541940304001d4010301c00d2080302402e80c020302050000c41c0000c540340c06809000c844110003501c6038808140504030690000d04000c5000c4200000d000103600014495269001d003000144c0c1c864040000324003800b80e0f0079401403440c6030300307002d074403050002011a1041401110100d0369100140b0121002200031a410000583c00180c1050b4040c0121658000221742072414111441d03076803240450360080b50051001580d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 372327158 1250 372325908 372325913
    0xe090a2001030e0601172b08090f07060c061b050f0304051507020d0225050111010612050304090b2202030a1b0e011704020a1a0f041d0f061507 63
    0x1800030160400160540d5400c5d82d54001c0601301140c2e1244d040c1240c002d050740000d80e4012000700b200401c0380244080c130000c1010703a04980c03600b001819103c5621070038181031000c82c02004200c0082c40703d540e48510000c00d5140ca082990456441002038608107281c0f01c0c049904002540e9030b1101040e0101e0b1659a00d04045103080d00c003a401802d2501c2e0182402021039009c1000c50464071103400301c41030045400b1007210078070001006032544140009081c0151740c4a500c1c6600c25100d85800030400ea502d54070010b00301440c1c10411915903000103800c00c0861901c0c0602d0003030600c119141d51180c104080c1e80401c07100344c034400804050340000007a450281a1307110402e10003d04681c4260614810343c00740c0b51144464640d408504203141c0011850308440449210b298068071840400c0e00d0800c1d0b80403101002c80c802d20b4002c000303204141d0700f80c2041003e0030040c0b2041418003e109000c100300c0e085135002810030a611603075041000115282c00300e54240712021503d459564031200d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 372328408 1250 372327158 372327161
    0x110106151d060301061d0d030807030914010c050301030b0106050f040614190e0a0e06030d030510150201050f0106030504200409082a2811190e090a200103 68
    0x75040d503400b201c044008100345500040d05841c01910241100340ea0100c90100f089803c10b02c6d00060014072454001107090781b080c1c00c4035100b00d10928015149500d248401829113500500917800030710040300420038002c581e50103900401c0c55040062802c03000b010004081d20881c00b5000500c95041100f58410703202c80101d44129090300c000a034802d0f0f40c2c07000200740310451035170a0f00c10700c48240c0c0031404040c2da28009006803030040003000c1d01c103514142030b809000014899813100c0500080002c00d09003c000c000c40400a80d4000106d034988604e1301004540103810010030580341c00c0400001404051003c03401b004c100884501c000321440004020f000c548100410205e4003140e840320a01c40c64044510300c8203c0c0001200081c00d446d0450717605c50000b440c0c1060072a100c404a403a02c1c002c2c04042c68114000c2c0d0b0146401210a004620024642500d449580c1b5041108010584030120842d40245500340906003040075070f12503005580e1080c602d5003000c403030f20349400e241ea8000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 372329658 1250 372328408 372328457
    0xf0f010806010e0c0403241d101d0703030201050901060e0c121005060408010b04051f031707060e0c0102010606050a170a09050a14010b060f0304140a02030106120311010615 76
    0x11140d10355403442e4506100c000001c03204100d450b81808d2500d50001448051031520440a81790020480129941c1500020340903101c0c21168100d01c0744006201c40c001840094095402900041500e0400c8145182101c41e40e174480c20b1403420040600c40c2e0b03030340c250080301c010008607403a60a81d6122003419501e20a02540003030350015000038005060740041d04801c42044013110100202d1740c0f640c442000c850392b0040c01e0400aa2044030500c0051880890480388034130852400d810003085e580d8000c102c4800ea1022980d9501c543c0380c6904a6909004031006066189409810b0280c444009041c00c201a503240c0034482004000899111280d480a66080c0d0000d08803555440542401800000040c0c499551942404c1e1689401c1c1840000c5802e4040c9160030285569644c0d15280c2c040c14185003484030501490382440007607907003409882d0141c05c803032000e601450507a140181c0300300071081d80e9040302d90420720b04101c403a1241441e8206070300507040454245100c4840545030001e03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 372330908 1250 372329658 372329663
    0x308040317010b0702060c3310080d1d03031305240306010f0c0f030c030207060f0e060307020a0c030506060f04140609130c0603020a030608010207051b0a03050a0b0f0f010806010e0c0403 82
    0x490302101c01001240c440d8410407000070300e10031885911003030031208858410f400ac12286912500f0201c09441c4140d000c1400201032042041049452100080c207641c403828804500400c184010301451400181c0e002d00c904128207603580d80351449038445040d001c02003407241404401d05455200b103005105000c0d10303da00040d103004d00401850094840c2d4104238007070300180718503034000c00c15070700030404040000402d407108501e0050307003030401031568001841842140903210580d00010351030b14074600a5889440603040e80e1600005002004d00303643c0100f4811414401a0f840c100c1941c091583c02000c01d640005072582c0729208803499400d10100204100012a000507032141e1580c00340c0b045031020390b0103000c140d6440321560300782c5c00303280070240841d0002d2400002d5105114003000318584007030038038200c05581c0c5c1c031a18103208592009652440d8030108000040c032103039401030b61041c0c1000c1e010503d941000219952003005006859a0304941c9003c03c0c441100700381034800131607 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 372332158 1250 372330908 372330943
    0x10e04151508090601080709020714190308060102010207200f15090301050f010803030a050a1e060e01050105030108120306060f180315190b040609090308040317010b0702060c 77
    0x19600d01e400c418200d041d00034000014000004616046008a2030504131401c4100030000d09003441400c04c000c2d030040030704540e110b50318900b00500b40d0083c08502c0040d108000c070320311544030900707001d4090400100994110f9204000c60000545c03510079100f240116078078500ba00180c1c400100d0300d118030030035150380c3c880e0b04c0720041c0042408010040981510a03402844140c03101822040d40d05805e02075101c0c0d542003400000d20004503a070001c1c2c1d00601e11039021a0345041c15410008a8003901c1c4420451a191001400b03407803000000c0500612003071810901c0c5600d031130092500e44c824112009400c40002002c0b0754140e440b20b06451740c0003080c448159403840c2b411110003500300b4044410340240561410558100d500c801c51501c00c4c41c0040240c2c88032400c01800ba00104502d4402550041d40c50310040b40c18040c0f2322580d89003a00c0790f02e94405506103400c0262002a8809031419841540001402042c12003401c1c1d030481c0e64184d40382901c1d84c244400c1641003d00c000752b14203c0030f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 372333408 1250 372332158 372332201
    0x90b04140103082706070807061103072303040c17010b0619030515100c021903110a0f060507020d1a0c03011406070b0106260c090a060305090a02010e04 67
    0x1c02000010030f141c0f0107600c0c44004500c4001070004c49400c104035102d81c8104140110401300310054001c0418504c113090000e088000101e280e200c0b90415108400062440f608039500700000c1c03003013140301031250350190f03096203025900d05091260301e001c0c00c110b030f0b100080c0d203413506403007500080b04a00000b8001c80d1905148401c80302a0900569400c00003414000420003411400d10040c0714124090000c01100380702090035544480c0481080b41c00c030b50348048091803042c220030041d020b10300c12000c46c2e507a2104082048408032482d0090003240503217020030410142c01004a40e04030740d0584a01c0300d980720600b01556600740d0442c074034000b6000c10042000706000c0304001c4d4142c80006090003107280d80441400078074015002d0040c01d4240ea800188101406580c110301a0165010410f400d107441782144d011450090703c0001d91064041b582c0c0c0e200b8030345185044040c0840d45420000303854400c4606e550b481410b5000380c107000002c412880e040e00d42e50400542080341c03804280c3d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 372334658 1250 372333408 372333413
    0xa062403150e0c071a07090306020903100e07031122050705070615030b01270e191202060703050f0601030b03030c0d08040b0907060206071d09070507021315090b04140103 75
    0x1540101c40c02c45800b0240c4140445403170401000310b005500c150703240310003e800d540d01c0720020b40c880803a46a26100385143c05e5040d281a020340c11203480b110001e44030091440c50030800c4040f514440c0c610a91032105c503155072400880594660350810000401c0b04e4445900684071032041090103052203041a8140e131480010700106000c4034403c3c00407480503a41c407a2400c800c11303150418038450f1350f5074015101440116030003880c00304070100180c840c00984c44c0c1e51030060001c2c10310308480e9691070958201ca041d03014060158090460708040c001031811441211103c1c1c0010030981c14169280b0004400c1c0c0c40410695003111458000c0310450356841340040c220302002c640841d114038170780002407810355000c90f004044400603001000ca9403900c005c16111400d8103203c04d403184000b02c40b095159500c4169440c011035058840580d100c40380c1c014011440344500741201414200492420300b07011181a84045944c40b0900003a02d120301030004001c1e006003c8951078052840d4004422b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 372335908 1250 372334658 372334681
    0x10e07020607021b01050904020f120415090f031d04020a200703030c030f0c0b040f0b090a12180e01080c030f24040203010b13050a062403150e 63
    0x161040e4080301d68641c0c1e4200202e035241c41508040003102a028a202c0055009401400c3c14130030040025042944641d80c2c401c6035001018402c50500f402010b1100b4048090046c40c03220701031030f80a000301080380e00c42111803100010700a007002132102c8034489001540207950800040180309540d00c1c54034040080025501d02d0100da82c1341a00403c039035000d800010f19100300d0f81c1c07580b1100c480c45016203081e07461480c03205804c018001003024a00c00207003c110413900c41c500c41e8640f5001d00c0b0160038190100c18004051038814ac0c000030040b0b001c07525240c1032080c0d50f41140760040300c211140e805d0702c094480030b40c841c0c454500c8100021940002c0461210384401e0241d046600642600d1401951201e0101da03600170b505051207040d20450074031410a920a0000d000401c0030003160001c5024002e040c9040141c803540c503024041c1000850007558010088808948407904550403410074101580c82c00ea8180365903807030203841c03000300c0383c50304002005544040000ca01d440b420404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 372337158 1250 372335908 372335911
    0x4050105100602030712050310030804090204030b06011805060a020102090307080a0b100303050d050403090e07080609011205070e13020901120303050106050f0306041a03030a0c060e07030b0c070303060e010e 91
    0x40039510401c08140184000180c1380026000050021b4185914100761050b9001410901d10b409241d480480881c00f08802400100840d03000144c0d20f03072440c100311a8807040501420b04024190710b12802c070710441129031090f80e40407034001d50755030b1503800705078028850100c0141e054002e480000a145001040d400c5220780209001303041591140c0350000d440d60302e8040200419820301c140e680380c00e4603030311403a8010f01c01e0070140c4206442e094a401c0380300040f501100001c0c0e514082040318140740c0d1440d40100b035035007500a11628a99201500d44a82d0700031079104014550000b1000c03240079001e45100d580140810165584071443c03007182c011030b040300b41c5c0401c1c2040c000180080c400d80440c1d121200070b0082c142141c9900c400c00010b0300020900c00c0081203a42045540341c0d500b400240081c503565110b84041c0d40a600c0c000782511101041108503810001042001c101c1901c0c085a000d10210a1150340710010714050300100321b02d40003840310301c0c1200700100307a4100050015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 372338408 1250 372337158 372337171
    0x6020a030e0f1c060506010512150d081c0e030405030a02040207111009091103010e06060307030905060109060305010b0d03090e040f080a080702101b181203020c1806010509130207060504050105 85
    0x80c00fa91b9201001543c051103510b43c650508128440052078003448000300c0300760300700c00402045200388192030300261070b004420304000d0842452031609840300d032881180c10440c075940c040c5007442d02e8030340002e0702c844585202078000c640000d40002000070f214501d504601000342200d0039800d00d9880204071985130b00808040301d1030b0500702301c0750000c64026a0304844500d43c040482d40e4401b400c1c024075030070140c1514203250300c404030140028400c1c40320b540a410041000690a0300d142082802d642c03a10260741e005a060854000210380e010314800c0a0b161070780c4640d515500c480c9800d401c7d0f81c20804001e405500003042c24202e545d84070756003c1c01041c0c56403c0721201181c40c042e0408a07010034024a444d212550f90380640c4070b0291035085a8514808080040c1e688c1d180c0c142c403101c01682d0821401a000340b0946481454048021582c1c1200c08a050401f0b2038010000f0703050740b180881d80f42c420704000076911503100d5180c048034502a40401c082c01a03003490700e0014064501034401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 372339658 1250 372338408 372338411
    0x60f0403030f170a180204061e09020f03070507170409050f0a0b1f02070306060e040b07080c0901031e090b040c050d020618030106082505010906020a030e0f1c06 71
    0x1081036114603503c103401906030803c08400c0e151220302000030801100351855007207140c03241002580d10351145000504d0030846401e10007514620b2117440584a4024800c031070b10500c040f43c461050642a25800720103402d010350745490509040501d0031640c045030036140740010700070506543c540c01c254040d02a5141c525007603190016400161880c051440c0d400103195458490020100707000114800c0840c019a001c441d03e0340c54681c00d0781d030290422031204200000f40010420100140d650042d110310344440d081c10880d55a0b40907110f5a0740c094105615001501c0f40500e046000c1000070345a400d04008842c51407604150501c0120ba00f80c0d140b8220340000640d504220748002003859008003868a003c202c112003500418080c40350a42640d40d940d4040340046040159820f20950791118076022120058044001e02c1c5070f811030350412034900802c00c4100d8000034050112607060600d044120b83c22804030f020044480142c55006140060554055210300780c58110907016020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 372340908 1250 372339658 372339677
    0x3060c02120a020303060409020f04060801020c0c0103020702090711070f0608101401020d140408030a0c050712031e11010c090513050103032c03030f0918010f23060f040303 76
    0x72801540511010321000d40c00400014146141035400089550320080c903100c840c0200e0804036041754682d8100d13800c00e030741c0080d080000c10382c00c0060300320144003440d0030352800c3c40d60b40c0403811112024014400703000402c40e0300c60000c90b0034003620001c1c00b4640764002d40c0aa035510000c00c84501958082d0801c1c00400300840c403620300040f5110b020308182c0050184007420700303045a088519031101203242405000c040760408081c0b00400045030306a888205a264500705035040c019568000b402e0018404207141c0000d80100d50340c18000e1010424000e982181c0d81c040d03d42e9207007903166403c554078001c400400e96421170000c01c01d4410958000e088003042c85648000c850007804041c001c141c0a000000d20320352490010302c0040e914207454410110760f0400b00f803071500a5200f4904070040403484101500b0040c140c122070404d001402201545408a4400445510300900710180c0c0019100a000502c114041d070030040d029018039600c0c440c200313070603503a90000d010490000e201e544 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 372342158 1250 372340908 372340933
    0x50d1d04050108031b0a1505250207030f11030a0c090f111b070b03010603020d0e0a1110020c0303030406060f0b07081206040617060106020706020d020709090c08060103060c02 77
    0x421103043e074680030b004514200c0d144483e00f180d0408100c0c0da0074107100364035290300007881c1000d0b207001101d001c0708046014100107420003440e620b80c2c108039080c55a075100001c49142e0014200c03003101c2d001242c81c0000b64507800e101c01122450681c40f80c0509c0f4034240c0e54200040c2595140403141801410070014540c0081c81c0705503000154410a0000103201c1c0d1542c44032400740032000000c00c081182c281aa603105030304c43c0703a0001da024002090340800c95015000b8640224041c0c50286030250103080c03001d5a9408103c04051019405024007010b000e022900800c440714071450010b00300d0380c0701d103401e1030301310013401c014060000b07200d43c3c00200180b4019520144c45180340d00020141c24030480305006803071000020400340c0d00503210300c000078455952210707402c0808690b0010303082541c180100a031070300009074040000c5511a40803051055400300340f210654810700301c04a90301c9890b00b01820703580310035001481e50b4001d61000100b00310495002514480e441c0e000d071007154070440c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 372343408 1250 372342158 372342161
    0x2120d021002120103020f180f04050d0c080a142b0c080603060a110409051303091406041206020d020f0a090b120106120e1b0906120d0503070507050d1d04 68
    0x15480c2c8884014080f005200600e051100c001d0408009010036031100788038000020001c0c0c0940d4040c080c04107003c240018800f00b8840c0407605010b900344559042c80545d140d401606c40d944c1010200442422010b00e08011242114185038061400c0740c050742d02d100c456640869280080071100740382a81203a01c980c0204421889513800038043c002d160f0b03856420700047e09200c444001200010040820400c40034480c15009090000310f007074400090340381c05480d002c05070b04603011180c0c0ca030380041880d5460f6800c54041d2a2805903d16444075a494040080c1c083c3c101d402000c41e0000c181800c01c0806040504060308c0647d880e9440700340c0e01d203844029481010400281e5207100f10040c00785a002d010404030030322a6045c0020079aa44504c0c943c100030082c641800c000b02c09003c2c02c1840d1078251481900014102c400e00703503040318a0f90b10b5540302c030811008800d202c0003100280c1c2c0300c1e00a10a9685031500401139038040b01c0c0d00c0da401403001d01d50703402018400780454002d07665410103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 372344658 1250 372343408 372343417
    0x32809090c12051b03160507060507200111091e0607062403050a0605091e060106230712051c0b0a090e0709110706020f03090d1b1b0302120d021002 65
    0xc2034a285440b0f0f040b14044031010751503011b09110040102c00006400c51060600ca401c60360b4980d03000052180403040201603540418a85030f05102502050789000b00483d020a0000c40b0400d05281c11000031601d003041c0700700c120341c1c8400c010580c802404120b800c200b40c803c0d4101c080600c1c0c00e8041c0c1c11480c4903245400003034807562114211100144c03040d800b80c0c0d00b2003200c0003202c1c0307044600401d005080d44c010560090b00c0c1c100c640108101c030341052440b203a94031408846100c041d0b8030200d6002c5402000c81c06820b4191058000401d076005000319990707044021140101c0003440ca880c01d0140100000041c01204071281c00280b0340241d10550102036030090240c40c040b8a002415806080ea448003030228403010808040022020720003030401014a90003580c403490400051814000c0104c00b00080c000c5c0c01d41d100d1403130b6071165120a082c9901030f80084e1141c0210148612100007500f00039003108103500312070a0702100051560b450b04103039084611003040485a81e090307010b03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 372345908 1250 372344658 372344701
    0x180102010b0105071e06020c030304061506030c17040c080f280201082a0703090302150913110409090302030309010510050a0311030f032109032809090c1205 69
    0x103485d190420f01c00e030003000348403a25002d0400507017041c5411410f14103590060b5400c6403030546c0c81e448000105c12a0028000030242c5040401c00011890405041340201603100107031829290000b408202c074080301e0b500074045040444841c442c110001940d80c4084e9540c4822294050003541038900310100388000250703041c2c0d290400743e192017003062800300d294102c4824115842c201044508031030009410f40038040c1e6070309000289035005018a1015500040c10146020850600036480d142c15054a4013046100066403501e00d0900f44e02901450b007101941e2410110030405160740000914000c205080003001191500740ca804042e4241e803003000c1d000001440c003000400c032400c2e21801442009000d84001680c403003000750035540034003070121090381c03050b8500f0004540a990740394400080c10003545003001c80440c8440c0c07050184000501c46104009000c0c0741362050035040d0041c024100180110161810302900c000002ca001c010345038131741400123151024885442e001c0c1d05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 372347158 1250 372345908 372345923
    0x5010504050105090d0203010c17090604050613260c010c09050102071710020c03042c04020f0f030604050d0e01140405190e010f03060c020c030c0f0406080102180102010b010507 78
    0x901d4140151015001040c3c2903a01016040744d40c00561020f0248140800c0d1555031080c003200b060070f00c000541d50260400c05554014020000010000643c4640000071101141c41d490854501881c51201454880445108050001d40c1e0001c10b40c01030140c11200030300a02c11228011021104c1011501c02c0c0b900580c0710f1281001290800002ea003985c483e91000e840c0d8220140442c41c05a03481541202025400020100310413007200441c040809050355050422541109491002d10800760020788a11409881c804076a070340c01320303240c180750809426241685007904149031600342c1103588202003049030b0800c0302c456104039904c408200800043e1400d2606040a02203043e001418419200c1c802a001064808011141c2e03802015821410300c1c0c035505510380300301602c108911100a641c02402084d415035004103070460f18500641c0d40100343c032154030019018100580c0046207035440003410200740242c8440810007060280c00a00003030407590011500d9104081000d083d84 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 372348408 1250 372347158 372347167
    0x1050106270e0105042d2a081b040503011a0901050105041206050726040204150b030f090a021201020306031204083c010b090601080f0708070903140a060f062102040f060e10080106050105 82
    0x102c090001042c413270901c500d10300e0400d40c072540401c0c00c440c1c55003c00706030304442a90740441407401d9500140904420b10b4540e08003807400c4561425201510380041c0b455466100240100e84201c17600d070107110040381031030b01055a01c811500d00348415102a4095403c01801c14404681c014800341101c8071917204520359601c800d0725030812000130301600c2484c0a80c071100300c007590759070420000e01c2c1c1160000598909002041501e4006421042030f40710805201c1001300d110301040c5541c1c1c040c0d400e20490076404069403400020380c5100b00141c1420b4404040e800d44000550045582c00380c161403c040300e403a40c100550f4200811a84403030081034020010320200d10400c54250850818203106548644075079568841e040c180c0080d00c5254880200b54007401024001c2c0c00042e511400e041014605140f01c401041c0850303001525010340010045085440f41e80c0000116136020404100035600c42558244100059442c200200c03165070b00840e41803010720406084030b00503154140392 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 372349658 1250 372348408 372348421
    0x60207150c020d050307140c090c0d150b1306081b04063c1d090115121409100209030c010c060e01050106270e0105042d2a08 55
    0x801c0e208000300d070080081051500010310420181905511824503020860740003000c05203880d0070752440b50b00c11800a0148420007065400300e48275084a00c6000ca0041a03080e03401a24407080d5201040814000441d050a540c0c1e000c00ca10641c0c441c1c0d5942a43c94a4885040d00c0658254600210010041004002c0c541c028040d150460800140c00ca8070041d0451f00501c24020081c0c8000114000c002d4041c612507000e507401600d0006240c0e42c100c0201c10384003007007102c1c105005540310180d10300c1c90700342c2c018010146c141da403410040c820b02004040c2000b0291010041d207030003e2034032410940315040400d600a6545126001d030041051851002c01111600c00891040d5200f60f5100026400a0001e008183c080c00c065240c00100c80e0f6010b01021600100c0081581000e442a82c1403119892071400c407811200103d074007040e800c07460b1070b042860a0300f600101da001d140942d02c03614254020340082d8a0214103000a910301c7d80d0821001400800c221070700c800154840e0000b950 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 372350908 1250 372349658 372349667
    0xc090f0909031202130905090a050601030b09010e01060b210112060f0902060a0e0f0d031e05040e1303090b0c0a0f3311130b0a05090a061806020715 65
    0x14940640341200d40c0b902810f180340100c0e884142d803084107085040c0d080c450424a40255a00504880018030101500340c0b43c0540380d070f106020050140b000d2101140301c0303600940108a45520040003040b1b0a035590b43e088186070700c05130074090100302c0c1403805030005004406947c101c0c0c0d110441e154440c0c00d04c0e559500209580b10342704240c15030b501a48000341c0c90b0b050250028454549031500c442400c0020003456440420902c0c2c41642c450740401d00180d4002c3c80c1c0d00440d1804070320401e0b03486940f58142c500b4000e5401c5215074621940c10400694031100521707440f18000e0b2202c8401c00e8803810805914811413901c200181d005441c1000010158030910728020f006118580c0b000b810b0710b9809403818481c1c0802e044102c2c5800324540c10180d240706034051828050100c5280c4001956840c107124040d00c901c0c0000d00c400720304031911074022407c417000c81d000241840030854507000b01030820041c014100751100420100801c826000041680c03d13282d18600c03588440c10301040c110f4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 372352158 1250 372350908 372350921
    0xb0109031a07030f020301090902040b0913061802030d02150903040308090d030c140a030201050f0106020a0201080c190507060b040c0509060d1506030b090a0501060c0b09010e07060306090c090f09 86
    0x400c044e6203603604c4003c126148040d50203082d642d040070034964180e004000540707404921103441241c15800340018100c0c0d20009a070402c1c0d1104001c15403103903040c204000f02142c94006905401501e10f12114242d000c00c5d918800c4142d2017850301d0640350070314070310b940f4000e901006114540400403c0410300c2c0c40440018154401e181540304905a9690f202642c22018501e04480d445041403400300b41c2c087c01001d600000e00c185c0c2c18010742c03610307200070b603a28007143d0040d040c01519804580c0304450710040301c0c06040512054101b281e900400145554071010080d5602e51810500680d10300e818022100c2500c0265a042e0403c102d0104104240d030200c0e1603418031070b94903035a48101c2071440542c0401017056403800034807000c1c02000d001c18840024424025146028014455603030850300400d1020703008032140c1320300d6a5500c41d10f4010280850480701e00e22444900090183c1e1603003002d820f03200c28050900120000304000d0341c24130301070300800b800d2400d0240140441c202e00e6202c40e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 372353408 1250 372352158 372352171
    0x901170112080f310504090213090201050c060f0714070b180a0f0c0302010305060a15050310031e0210180b07020102150a0603120824150a120b0109031a 67
    0x1600c0c160038009240c035114800c400e20540c413101108410290841409107000500058405014250507a80010440c24000344444c0c0680e51707171410082503911a605545041e22800100e8810f828040c84002840c581180c610380000d481034a0004007020800030782c1d02065012149844a4031229610344144801d29650041441959440b00124011502c0402864012034455038440e0440c0001415100c0c000c1c40c50303009985004080018245280803003416a0a6182c0280c403501d480c7c15000502e480c1b580045c092001044080422a0852501028091086840c1255003182c040305032940341c0b80c10309402000d5449502080b11443e50401000700d00d01c144181c42c4400e0402d400c85580c0d0009441d0080410365895060007080820848400306090604005c0000d10305030301d400c0d08081c000a00c0b040151820100c0e030540b0345070941000406508148801c0d1102d200341002885100310540724602e160034100e0141b0a940a54640b1081d03903040400d8040c140003002140d0f16641c1d029108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 372354658 1250 372353408 372353437
    0x308161118060f06090d0809040b0f01021005101a09040f0b0d0f020315010e0a060905060d0206071b08010b0102010b0405090d081b07080a0e041e091e0602090117011208 74
    0x4501561b41d5550301155920a00341680c03a41408002d0008440c072042d0258010301030041102c1050b03800142440701c4240c0d8090105540d610b80760b07090030503002030344013250901003554a907150703c0b03183c000f07071850304819a03041101c200100018025a60f900302890b0300141e12036003400215404204141c00c09001400f2a1500900b80841c030202d0385090f403004080722500001d02c0001c0744103004086c01840320780f10501c00790900800181e00c03e0028000280700d01e5002403618100481c554184890101e4130128550490340c2e11601d5001e81414200c1c0350065103402d64620480c5441e200b5140182045c0b8000e0a024110901c192030319480501010002110030610200305100740b00101155403080c0c01c40c3e0384640d203044006c5c0001c240020b00c948150304042d03042521485d12442c1800e5031100006c00f00c0c0641c80c50401120040c0c9008410181c0e03011503036404140400c0d500141880c2c482a0384d081e0308500c000e5180c6140c0d10007802409400000001c05030b0100b622000a4040b840d5040b40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 372355908 1250 372354658 372354667
    0xe240c0102130906171b010819110931090804030c030c0f06170c13031a040210081303030f1b020f1908120903040308161118060f06 58
    0x1c0b444180c0d08540c0c880d9003c15110071040c44001ca2640003000f200074088020481e06075141c1e640e402400e01480028100208080042d01881c92940b1211803441d5143c2d00300314206850702c6044040c0c0c40002c0072806400d03032900d07100a2000108400d03006086641000030b4181003c1e07041c2001c0d002003a810340d110320040c0300c080040b50300d1a041070019403040040481081c0f6000d00e0340c4894100741d010a05101b001c2014007001150103500d2030340220001d0801e86d946019202041c01c05050790030207010030b030700410000000c00122141d580503d000b01c0d0030f50f208522a0a085411080440d031603030301d0b001004035040c0040c0c041e801c0b85184150013580800c0c03141c40c450880c866030307800c010544016401903190398401c4401303214101e03030a03001e100c4810300d2403542d8942415074442c4940c0205000300050000310014014019540a95071148405a5558040c1140c00c001c4007203100035643c0d042100c8011800c0d1410040013441c1c0030a8400b02e11880d520f450802c201e122403c410349400110402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 372357158 1250 372355908 372355927
    0x1030b030f01020a1d310204090e010b0d0503040611010f180b0601021204030b1803030c0408060105060324040603021201361203110a030203070e240c0102 68
    0x1000724480580748000684552200710001e010040b60049200306102c91034200e00c141e10340d400d49512405100f503400401c154045d200d0b04c0d25082000003040418800b00b004280c480c1e040e0404d03000c61284400900205207908200459190180801000b90784100401c1000600402a81c0190100f5100000f02c1c82d14258104042d0b62011321981c843c041018403620400c0546895035400803420700c0200030700300013094143c80c0b070f2140307000241078001413000003040039041014005071170b4078881c143e03a03c0f810940130b81c002c1c680081c0940c01c40d502a500c00401d04d410f103081583d101e550015400041c0100640c25034501103c4041c04a4210340c4400c2c0c04405601d1b883c51200505c0e0700080006010445c02c601030141005103500c102d0301c540c030784030b14950748030340409815544d80e0040070802c4545005c180513402004510401e044001020400240f035542650107988104036a4964440d03428406042040000e020998807070400390700c03003000c200d01402c40d010f8900854400001480c090181 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 372358408 1250 372357158 372357163
    0x12180105040c030312050610030e10090f0203061f03020f0102160e09070b030f040b0907030b01150f081e060a0905010305010f0e0d0e19050d0302060106032f030601030b03 75
    0x210340540d002c49000b00d0030400c0592180140400c00f041c494200050b0900b00000f4a10142800b000410151a12584070303074650244106079000b40614810041625180350040e08048a110107901c80e01414000916000f004c00c000c00c0c49040040c007807000d4030306581c00c10010405101100b41144100203a0504500140030160040e0040c846c0000241c40e040e03141e03502e0091680c100d002140018824400c900c4440041e19030407030350010030030901e5601c0c2e080c07503840c00e80300b1b0348050a4201c3c1c45c80000780b15019054540240285070740c0e052010300d08518150f80c90722081c2d0791902172000241c90802c03001704130b421903900400010207000080c2da8802c440d2090710400c0e0410307a116517503198a1080c5240030b00c6101880da8156001e44100421001c01a0064a1080009005144106a981030034014a00d0034000d010000d20044804072141002980d4000074019403011a00e03114480c03042002890201c42005100c903a100d41c51101d440c1021f80075000544140c1c10b054a6030320f0711180e603800707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 372359658 1250 372358408 372358411
    0x50408061314010c0c061a090a050603010b010c11010c050c04060308210c041802070f03030c08070206190b0f0406290f04090504022107030c090606020312180105 71
    0x356412001510701c41d00744100c2402100d110040160b2504122503450342d0850316400172203400000c001a4500c202150294010340d040e5115480401d0078200a0001900d612003402002c040d0020040c480a00c401964000c02072480603248330220402c40b0a50340c80b82202d601003a00c1081510384584400f0085019125260401c840740700021034600c1032207581c050100d010900d0300d03e1001442c14010074180242c419402591600c03c040031888140e035095070112140e03258010150800e51fa00d82c20000c000300018030545000818001c08102074500c0040c1e6a4040d20306010348031541401c44003c0d200030b0900300d1146400458002c0550701c0c40d50b4911640b001091608590911110103101140300c00c1030034075606004100034800c1d410031104a00c2030300e0555602c0c020010b4251114000142c8404010304205600c0840440f8000c40d1100454028100c034400c5500001181e00c3d0480102075a0480c080c10005074824400300480302c0f0500056604940e0752205001e242d4600b110650a4860 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 372360908 1250 372359658 372359671
    0xd0e0a060e0d110304140112141e0f0105090c090a0f090203010602060108032a0a0609080c0d03110901230a09050f01050a022a09040b0402100c05060f040305040806 72
    0x182d103003401c41a00200002441e035aa0380145140506108640004071007104405041082d80e0381214038141d00d0340c0c8860360545d064aa44141850103103010120b903554105001444003619001c80c1903400c00f805558180c50b00100402e49607560f0700840b19160300070148031640050301c00b0303001032003041d06016040508048003003d6580d43c140000a850100181e101c002254401c000782c00076454401101c0813010184007180e43e4200b5130000a03454040500c0000d4840791405031841c00b001513000081022840c100c080d60700c3e10800346810b4045680120044001c030387e04000950181d88109440610340c44c1d06038810702142165800258550041d03404240491840074007400186071003d0441c0251800b4a016843c2027603c1170000c1d00d5041e25020b0304c1c541094012203080e12084000342c01c9226401900040700391605003000441c1c0041580e060340a40c0a99407103081841c400d0071030548179500b16006104503102c481441c0e5410320010030a4082080502c408204a1400e0100c140543e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 372362158 1250 372360908 372360913
    0x20f07080c0105060307121704091a0102070f120f0f1e060614030d0f1e0e04050a0203040b070e011202180901050301022104140d080712110d0e0a060e 66
    0x4031408203482c21102c1c058100b51280d445820100000041c2400c0c6022456000540c0f42340003015101005440c0a103401454995061013980c0d85c140030801c130041100c0b0740c01d03070071110706a540f044989036100032401a0442c1c8410810180b02241c040c0c0f03880760750544942452038246959441307000d090b130700551355251266070b0902e54100340400c501404003e003220500c00721920020380002503a41d20b40740140020f03c4046002d407c901c1d80540b101d0f203c940440c0c0c0e0f21285000010800906d4950651b02d010304c540e00c0c00c1c0210b2041d010700e2090f2440b07690f02191160746030321040016240c200c91040c2103810401f140791644156181800600185008030340030291148004c0100101c20761305802446c02a0b1062148514070031800b074100b0010782010141040a0303c2e00d043c005c2e8107550541c2d01c0c000b18410000c014480692100f03810748904e04955405401c242110024020303151000d200461110303040c4076008074004a94811000058010100c1d01566850b41e240d4094501950700d0703c0d12034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 372363408 1250 372362158 372362167
    0x10030e0a080714010b0913140c03030d140903030c040b030a0b060d0b10020d020d0e01140309031209030403020904020114070606090209010f03060e010b0a091d040303180203060106080a020f0708 85
    0x3041e09005e40c800c2c1100441e0b8040d403525101008202613403501c040503224980703100742e51001600c20f202d812099000541601c3c0d8074407a07405483c0c064400d40c0e00c90706224420000050040c1800300c20790b80122001090030745820328058ac080d1250300060442227985139035502400c810343c1c4174801030403140461500480d11001d10130030009801245d034a0300066400c040c40c8c00140980c0468203441d40c40c11401d0040032042c3e8600101d5082d01207190140c400080001440b0301303031900002500c407071080c4034056000c4c0d80d100481c0035128000d91000942250074070020030011740c0600d11400800d99070344610760404003035803a55000e0326916440b0f240d03901da0008032074403556800188a0036120450505200d44c510b4110100740c2c04005100d004050000411505803052140a2010081410030010005003c2e2219006008081078904802084c60918100b4000c52040314940c610b03a00200070340500e80c0380c144140c40310800209000ba080e13508100080e8a911040302412640d401107031810b440703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 372364658 1250 372363408 372363443
    0x6010305100b04090c0e090f030c0604050c010c0302210c01020706090314040b030114030102070210021f0c0e0405070509060c0c0405090303160309110a120b070e10030e0a0807 77
    0x1214942034109024a041008034030228141d00c1ca20400c50305110a42c03501b07592020310b490305222803401d100740f8502000800b540203160003e14903001d94001c40641314144c80c928010340700c24440301d00c0100560000403100b01d00f2100b1810054141d41000d0072640303000c020f40c88043c2281c0c019001200c2c05540c0300c03200000d05620a00c2d140001061130003503880e06081c030103010418001403103501140300850a030016507803403e4068400e5a40e0180c1103600107e22904040d4560301005500343d482c49000c0c20011602085014080418a40e81c88500c44040d400080c8400790100030060028003100b0012140c0f9604d0340e00c000c20b903001c00341001d020700316103650410055038805000180d2942c400d0003400300303030700c0390401c5c0f030485901504002519040398030704070b0890b900e01c0b40d240303900010340080010210301407082c01550f00c1c4103400c08086036460036001d84101c1800031055810132202c00044442e1406680104c000480d0502120134545840d5500318160b4000001114401e031032500e080348 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 372365908 1250 372364658 372364661
    0x702060708060117060d0c0b07120c0803040b091f14150a05060d06050405010f030b06011d011817070f0605041d0a0b120d0905120309210601030510 65
    0x100440d0341c0c500510300d030800c54002804900c2c0c1120305103116205a01140d040e0761403003080300c074480c1c3c00b80c43e00d80d00c00d55860f80703a903aa400c10402614074151210b404100c903072294a04520f025480329405042d0744070790311a02807124005024039000c0c41411521143c503030500040e0b40310080300380b8000c1041c00311101200500480075201c20410b110040009005a94464910041c5d0341c05a071034980310b000305403841010302201c4c1d111942183c94080081782e80c60020b040b0740c00356401b900b0000c25607140c007401180c1424004080c40440d0341c1e494504403184d8403a8042800040301741c0c100c070711415154600c124002d42c10300640950f50388070072801c0185e1405102c1e03039001805d07642801d504107464084004590104140e142c0c0c0d0701201400080e4404d160780d841070740c251034041c0c500104600541c070329690f0703000c070803a9003800f091000038005035600e84001c124828201d82e501442c100000c0f9810710260400d0b490135404940c81000d14801d82d0502080f06900950060000f0715010009103150f00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 372367158 1250 372365908 372365911
    0x70f06020702032b0e03031b070b12151903030305060103151203020c0603090309190e04030905150c0a110102010e12070b0a110a0c03050c07030305040918051005090703120206070206 80
    0x400c1c0140781c21711710803d40d4044259074103200d00341c5805100074000b05116080c4182c40d0000c2c10541c0c2c000c6030030880c0140072503440c0c1c0b0501405060b0450048144c0802c0040c2460b810202d0011815190078400a80310b07402054005106041c0403a5a0040621303009240a683d00000740c541d0342510b1440626a04001e180b002850640740ca81c40d600b46450815228415445841e005014000b462242400a0003640c1d0052011401d80310f0241450b02d401011031400d8440c01e841826026168492503142c9400c072260070b4980350050a110005036074040c14010f406010301d055542e502104100f051003032103000480c220880202e580e07100da91403c0e500020002c3d14155035240b4021124411180d2003080718070712019803d165410310b50300d240441d440d01c581d420741c3c811406080c400101f090b0b0020054020f54000c22000c0c4030300b0f00f101c1881500962401000340156100b1040f82c07003640095400640c00071248401d03118401d4682d1905080300c41603060400041c0e02440403c01ca40b03905200d5507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 372368408 1250 372367158 372367243
    0xd1b0306021218060f1e070f0306090608280602120f070f140c120d1505030c0a06110307020315220b1803160302010b0321070f0602070203 61
    0x2c4802602c00038000f0340e10341c001082c0c200f500b52200c010544191106000310542c24150300c13410450307d48039030010702e810100800c3c0c40c082410220045010012802580305485140c1d0043c0241040b450900201003003d2040c1c01c0c2ca0031124046001044a07400140008003030034080301c0c007900b84880800080c910080c814420010140c80c14101558801034903080043e00c440d81984680c000014542010042d80d5007900707040f00084c0303a400072070f65a0400e402510f422015010125035030000d168071260904d038042d60020030068140282c50044492101e07200d00312040341d0400d000e079400b091800203800c21450800d00181c1c00c2141d00f5005032070100c0341d030894070003121650080d40d69446200300050700580010b82d4101c8950204802042900c4a20b0340e14060410b04407800d0401a000b000d0303910115000b03000702000050b480810412098803030f000015824503000b400d0300d494010b03403918642141c1040e002c01503980035079820001c12410b8141002c03414021400903100a0740981a10240d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 372369658 1250 372368408 372368431
    0x6090c06111504240605010e0a1503150b0c030301050f030a0203070b03060105160b010f0e07050d020a03090803102603090409020117070f02011103150d1b03060212 72
    0x2141040d07040800c0010007070018400122442e116442c0c9030a8241d900000603000e000ca0201c200480080c5803c00b408030b42c0281c840500000c1d0300000d005180c101c60052080d020340541c1c40810103032203030b03210b002e500c803140c086168a56214080b0314110382c00a10150f40603070010005011920f8405044240810220b0061007543d1066000c13039165000c1d80301d60321103024044001903103a401001140c50085880c5441000740002d46081c5540010a000e41000102c00c0e00d00800c001c1110300c00780780554800d450303d80c1080300c68484540a5401b5069803001c060b125601080003969407000b56004004101003131010342e080400c20480255840b40001c04034421240007460071030007004413500780310141c402292100d020300040e104100e2231031450030001c40344c10400c40003a0b880302030340540d858558002e00112046040304080d41c0400d440d807543d000d441003c11003185c0b0300142c0d5400300522601d260801441c41c00201030600c9240d038070540e01e054000800d8140c40740c40e85141170703015500620 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 372370908 1250 372369658 372369677
    0xa08030906161d0103051012050102040806100503071503150608060427020103090203070b07030c030e0f0132180306220b0a09081305041b080a0c030204080a06090c06 73
    0xc400c20b03c40c080c800307a1414181d4500200d0030b07808a001c9030070041c0c1301c17030100048114010f25056000303501c94400e0b14420b004100200b28202064007c80302290350090003030400c1ea0508461183c40490190b0150900d0703500c08580b0b66180c48000b24400034103460f254a0f0a616005080c0400d030717080d19800304491b0329407580616561103100d10702c084031902032900040c02c070b02510109240c20225003001d00440300100350318040613802807810b031f44c0d18480e0b0742d8503041c14440c6080c806221190f10307040307003c114100129080c50020311003007500d5a1240000b0010143c1c0380c80e801145a101c00e000e181d40314685505056641410000c1542002e0101d1007910b590801c0ea000100c029480a4014903d48640b00460303605000e9800c89620542c009a1413965408800314000f0448920308c0b44a000e6824485030845409210110b01400b4070f02c5d46032980c1c80d43c0c40210842c02003440d60b5035441030550030702c0085030072001044030010192191400003a51030301810031015600701c80c3e001504001c442d030f4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 372372158 1250 372370908 372370937
    0x6110f0706110a050105090d120c0804060504080909010f09060e15360414060403080c1608031e090a0c06180902030901051005010507050a140a0803090616 68
    0x80c014007100c84619103584414540c0c1c00306401e24900c0c0c1c202412644c02e001c18010604004118421403003010f49135000d403000e00c01080e00613949040c19000c0071404000001d000724006070080ea0340288215500d40c0341002c410000b54080c00c0a800c00d5080016040d000e000f42107080c0301d01c00180200404400b058601150b80128410b251f860003030083c000f2a02d201e040390328480c00a64040030924906420b42c180101c0c071154224100e405075401411045c40021503c804501c4500990305940d034080f16942d403c9034000b207035016017054203021183c486400042503828018502420352550303403400d00c0450159a49072598054464021508407400709000260010170000071036103a400e041c0281503c80605440c003101710b0380100d200b42e0000080081c100d07010b610041c41000c883d0510038115407075100440351400b82600040071a802201c134580801c0d0201d00404a01310700400300c130400002c40d81c07455140c0c2c02c142c581c00348035401102032106d100c00c41e000d080c0c1034500342d203060108010b02c0c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 372373408 1250 372372158 372372163
    0xf030312041401151401090e04050c01180503012c01110715020f07050307030906050a0905040510210b07020a0c0b1c0c18140f130f0f0606110f 63
    0xd04000d0400c04000c0e41c20002d200300390044095500b001240001140e5225142d06240c0c490201c014000703000c0328408200d0042450f0181d020715006030051034004d24400055034409407500b50104e0041d40e0b1240015140e8090182001d4450000341c60000c586605803914503549010464940b80d07414900807a1413104080706480f58141c01c0140351040c148040d0140d4000d00c62828044910080013600b1028450000000c10303010f4400d0b52100100b5030759460445641c000c880000000680c01441004230389882e07045a45c1040c0c285070711954a41e6a0340840c00d4250500700e44400c4a003403100c154007031040403034900387d0004032800a4946d211060391070f900484480d02580c3c070045404135603a1180d0a51042407042d202d0312120400001c1c0900c2c60252190b08040081c202800c02c0c294041581030907441d2100c90618050150142ea03020001001450b070101c429844545a440c202100e58000314081c007900803109400021300c0130f06042d0001c10b000b0307625101d0031080c1e202e00004d244603c3c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 372374658 1250 372373408 372373411
    0xc090108070c0303020415080711010e060a0b0a12060b1e0d080c0a0c0305072102030c0405060d06110a030f02030411010e01050c2b0f1d0d020d0f020f030312 69
    0x10302c0c24051044940c64240c0090050b500700b0320340f081c10b0100c0c105401d0340200c0c00318022101900d030940301d590f03401328650903900c580b10780b0640c0e078002c00701080300284150804c04a041c0000c150114541d15180e08280034000c5903c10303500d01e52070300f0f04000c1506025121103152080700850700000b8003404042403a85400d201c006101c0e8800007903101d03045209002962100e030780b04c95500c64440c0c0e281812607030386400780035030b103140c03000130030203c0400b00b40340410004903601401512210300545c00f0032000303000080c0500c0c0c1160b0b034900b080c000034941e841071078541d000000c451031315004625401000c0350404038204c00c4280c810001e10021a00c1800828409002440c1410100f000070004032030f58080da81d105006071054912901c41e2740c0c948a80648904800c056a29030140041d40c201c480d203c61000031804525400000350715100340d60461480300101a205000c501669804070340703401c030010802d0790283c070381c90105821442c102074580c0b01600704600070b6042401095104869000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 372375908 1250 372374658 372374671
    0x2701090b0a091b060c0318080604050c1e0d0209090c03030c0a1a04031b03031806020304110a031a090102040308070b0f0105060408100e010e06130b090604030806040c030902040501060210050c090108 87
    0x101d69400384001f100c1d81b901c03800905040f81c16150303141840e14090356108103050529200b00030251080e04261145100c03603100e1040181040802c0311796400b880840000605a80e001c0d0080c0c50b50100c180c0c400700010000c14030304034010400c0c110582401c4200300c284c3c01e110140b0185000500010a03800407d590380418030000d0f00c90350300301c6c0e864107500810210f564407200201485240b01030010030350144d4499806800720204003150201082600c2845002c010a4051101c40074007160340352624096202120f0b1000500d050f071680c8441219401180c0c08640030344d000c20803c0300d1405d81000040c0107010503200d09003000e040c0306200d5100c40c40101c1154200b0703647e1018110801094200f40000804030090783c6107030a005210720070f500c80c146029a48800400301003600e007100002c10b68032030380e05a5a510001e80700c0130704210140c80d440d0081030030552541300b41c50141e510342c81481d000b49510f80040c1048400000414143c0300010000b0000c88014402a8016604050360550049 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 372377158 1250 372375908 372375917
    0x606010801090f0e160911030105060304030c03020c1306090e1f020a18080105160c080d11090415060f0215040615170102041d2701090b0a091b060c03 66
    0x1c0440c410307800070841c550842a40f88174000c04045a01182070b900c80035030700c1c490000e02249803420380215480c4801c2c826035800000420000340481d104070300c030300c007454440c0c070588510560110001d618042c03040300466940d5502d040400860000e0302c0707416001e03041003000e040c0c894141d000340c8000703c1e030f141030b0980e0385500018280b003094072a0340d034501c03001c2e00c2403002c8248039104c1480e94001d107422140d641010300d04000c0e4012440c09110101ca400c1d5120710b8062030122a0104040500880300880300000401d00034500c0e41e6540f4002d51119018440402404c80d141403001050354480d040c800c000d40d004520517046c3d14000810482d030158100d440413038141500c0040450b40030302c0f64030848103200140f94070822600190018000c9640b2151041004211040c080402010036948504240d024805269401d101034403000080c11340306000240c10311403900d4140d004c800c00c0390007018803950b42212100308694940070001c6244943c9001d240181050009080340340e50b02c8010b000d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 372378408 1250 372377158 372377171
    0x60a09020a03060506030c0c06070c0c050d020604080321070e0a03080a0c02150a1d210c0303070606030512070507060809030d020d0b090c030c0405011103090a030c1502060601080109 80
    0x10b00a030400801040090500c0d544c91410440c0c40344aa08207000308080b50151001040320248141103008001f40c0060300e1450083c07074501000400c0302c3e14035040b60440c0003400005031007442030000c0c00b0300c00603240f6020310040500c04441f4000390300a04c03050a10110206070500c030303181d041034032040d69884003840340c1d1042458825a00d5040c00500294422030701102c0315003007407603d0084c000d21061030b20b4003c0ca01c43c0c004003000e8501e82c180b100f1a00030308280003010a45100c1e0034030f00b61415907941640c0b020480138000c00e00b5940000c3d400d60b86580c83d000f00308200003040084041e601c0103014610b0804400b40d4031540c0783c2080c3d200f5001089850004100b00c960113104a80b00b42d00210411580c88424201100151440000030b52054880e840011806282c0300d040303d103d013404950707036450f050500005403918646d0918420040c402800404c0e05501d5810445010b1030140701c2100e41517103041c88104540c20b103d052601150020424405541d0300011880c1c156940c3d82404240c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 372379658 1250 372378408 372378427
    0x120c1504063603080603160b120709050d0303020a0e1302130b0a080402010c0c0e07200a080f160206031008120403020a0605160c0f08070e04020d0b09030f03150117060a0902 76
    0x600140342484030b40480b415100140c1020340b64003c0008810f03003527101000390307150802aa4161001d00c202d54000c40c42d540c501c1c00103480703a8020001c2c200c0508082d1035103440000804c0b01040d003940c0740d0068507800283d1045a411800c440e00081000304004c92400120a100425054000e1302c000c0c180100c2303080403800c000044400f2006030002e5042299186420300004040e84694050010107804425003d0801030f008102c6030010354200c3c90b564505107090052000c0b5600c11406400c00d400103900c2c050040c2c1ea190001d42c0200051041006183d040c104100c0c20403a112180c001820001c010400c010b0b2194500d410480b9006c0c240301e034440e251258076842c1404064402403010307211a01c040fa5200480b101001542d0382801100c11054942401103034410082d60302940c0b0103a07d000201c0003030008008194021841c5094900300001441800965041520704048040360401a03003902d580c450780d651452145040864240e0902c50041881401c690041c5400030b500090080c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 372380908 1250 372379658 372379663
    0x81905010f180647040312050a08070e030a1e0c05090f010b0a03110c060417071703220c0e100b030609150d080304061d120c1504063603080603 63
    0x1075200c1c111024101d41346080e5852803180e4842d00044401d80c8075070084a012500c180e003900d030481c1319619004d060f503c840d4810341e003401c03020703400d541d16104810201d400a402966259009443c0b001d001e0101c480314070b8600e43c654000e030413040c0294004000c200720003c1c182903550444242c103d400e944e40b0950b03282100500000400e03050040000100a03810110014010f8031460180941036844400541d1407000b520a981e009042d2241c1014040042c01c1c00070011500880c26241c1d004100d03000a0303500c892092620410f4860008282c17041122500052641d980296032811121555080c0404003442d0301010f48041d0041210000061a0100b2500108003880009060316414880c034a002400d1b5882103604484d03c0d0700349400c055601001201f0315800540340e42c043c000c03078540644086c00b0b0750003100c1290818859111098a41e040641441d03000340d0042201080c6d04070004000b1116003000c4807601c0e03000810740018444448051015400e940c1c2c5460440c09680360341c8006072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 372382158 1250 372380908 372380999
    0x121407060513061119050a0203220f0e090c0103150e0403030603060f0e010b0901080601030305031003061b11160b180303030703090203060a09030f081905010f1806 72
    0x3c0841e440c04035071074000e01d4004090704980401010902440211040440743c2e07009101407070000d40e109000321210b0b00798102200e803842c600000c0346220640da40c04c0c00241440c0f19880104604405401d004286009101515503204282020f10980c4180200d0400360900c0d0302c100703541c0301800d0700440c080502c6500600c00668000c10144070b000d1185072140e00030000444241a03d40c071781080040d080c1801c1441c030f41241c96400240089a107982c800ba6002e030b01c000c040b0f104039401d1007008800112640f0079403100403404100c0e000314903000341e009050907080100b2400d07558001c05002c20300710f1442e548002540c101507401502c1c2c1d02c40d007801100c00440c61680075030600011043040801c0b60306501642c1041e000310100c0d00243c4491100400716461940c01400041001c40f10104283c0200c51980c1c00c03810352284140395190300000b100480e078003a00002d1040344d20904c1005044906803010022040c450030800032709140c5070603000340c2ca820b030100502400e0004003080c02c07880d6040014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 372383408 1250 372382158 372382163
    0x120b0409060e010506010e040612030e03030c0a0c05132a02191203050c03010e0610170f04050f0708100b040204050a060c12210504230a121407060513 66
    0x91025200d0410b40a010f400e0031903d0034001900940450190718090184104171003a591380c2c80348524507503d0840d030501d450261540c15100821034a900c41c24200040c009582c0140b1100c80c22504010070410505902d00400074a0340c01d0104440300410340040c071190900340081040140e102200099003454448284a0320790b000491030081404540c00d050980c64615542c1041300369110620402c582c04280a104406c209210004040e420b00e884481c8000d006c41c1880d05a1000070b98440b16003800444880044128107030a00c82003203803c112440c07011a4a43c0900300c40c3d070a03c0c040300c0e900c8086100a104042d02c1d0120100140c4496044902802000c3c10b06640e45031111000b07485c4064000c02141d101c4002448107429074400c88400e840f820300003150040d403654070381e40000070b4000580182c0e200200302e40380360049040c041d40d000791020b050000e0200d9120b203080c00000b80211503808001e00000824490308203404a088842c9907a00001c0050301d62100283c0382d0300b10080c00c600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 372384658 1250 372383408 372383411
    0x60f010210110d0c0320090a0509150111030306010c020d2a03140a020607030e19120605090604080f0c0c090112021e0604090b0310020a0504030b0106020a03120b040906 74
    0x10a0360401c803500c014070a2448551082c4070141d044c6604130b040300e2090320110100e003104001d00d1002c8404000800607980c00030302808032540c03aa400641c0c650320030f55004103140412a101002c40d60820003400c940400c0f00701070b40c2140340c07080020b0f28060404000a10400c10011103030104800720340000710100000d0884154007503440c40a20400c5020301003618113005009418541400004200d84503a502070609030a007081030364142c52403032500803026480038840b1403d8560145881210f0000c240054083c1d00c920744900300b08040b290040c1849403250080403c110210300f40d0b0084078003407002002100e03035800b88030501300d04103414800c0c03850b804692240001407034900e504142c210503000b2281103000500440d80002001c0300b0415040c0c100d0414003041000c00031507404021071402c05001d40c0d0a40803ca88210100d9100068910100b040403d061060000401006000d4440c50008180500341900d000e0304001d100d20b00c04102a440e5040403030301d6121500038035070255000780e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 372385908 1250 372384658 372384671
    0x31401080309060a1b14061003030e060702220621080403171e130b180f04020c06130606050303070b040204090c051215070509060708160206030a0501090b1008060f010210 75
    0xc5c010380460342404006d59902c0381c50046074092500003120302c22a40d250f101d011000b0516424031825402580042e41d000003001d50540148201c01084070080200010020345941004205800f030403094010108098130004a5400a03101800315803d41c1d41089007d8101d001305010760750207105041f502e6040101c1c0e038121103002164140545000c21000000780001600ca10510503c0e0241907502da4481c01602075290150400b002407a25501c0082c101607c1d2081c0403401d140b0303218041d42d4481501ca60403d0100c140805480b901c80a418210051894841d440c0c548040684c00a40041d210b03669500024040041f2000400000c0a010348185a900d03034481c04283ca481d414003450740500140400a0702c40c134401c00445030f4454004100c0c1d81008000c2e00c40e503c0b503800407030b81c82c0307030711001d404041c00075a49403409140305070140071012866605000d00e4034161170b44011600e002d024155031401c3c2140c1c00041c240e51060003138031b81544540420703004030b14003002000b25801c164074008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 372387158 1250 372385908 372385913
    0x317090604081b010f0e13021b070512060103020d060b0406090906050a0b090601050706110903120a0306080102090603041202070306050c1201050f01080f070903080f030106031401080309060a1b 85
    0x903220395860083c55107460101c29210042d1031041d0180ea8500028640c0e000c025200d1038842c0c1070007800303002c6140050034801c090262855000c214042d1208592118004002e0351800114400c0c03d4102c1c00f01824440d403456000c44d542c0c080d170410062040751030745d442d6005901c6070350101c1e0081042e003600340704001c5942010401400e083d514541c04900b0010000e145050150080303001e000c040c0e48507440d1201c0307a20b03090020503280700c84614954080055040f00d550401860a601907551182035580400ca0390140465000d80d001414590041c80b5501c11943e805d0190307944a82c000354900701c2c40c11a01400c905001a6410080841c0d11305005e0000354100140642204084401c030700500340d03201ea04204aa03c04407001500150380d50000501c19500611b10b0b80d0040401e003011005d09840f0f03958812150881c2200c5c241284011004010780e0350316010b0054412010600010740307504010159840c0c0c0718820a01d0300841c7c000680324000c0d03125075040c03070f046038000b00703080c08040051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 372388408 1250 372387158 372387163
    0xc0c090501180504020603011701091712150a050f040b0904060515060405030d050a021f0903030f02130302040b1908010207050c100c1704090e100c020d0801031709060408 75
    0x703010302560380248040392280500380e4403c00d4042ca40051420307066a10b00002c04d80ba408082c05520115521404244c001500e00c040c01034803940f0802d00241c031202c120021000242e00108035001044201c002c1000f00c0d00e65691400944605850400c036401e464000706000d0501441403e0b08104c6039403c010038403105901886c0501c000f00240000c3d42c2d0710104011960045005e40c41e40358102000003140c1c14003801c0200800c0c3e850b4010760b000d0030904100501342034140e201c8206116104c07282401096071612500711141c3c5246021402c01f840080826456222804024025561900000d24599031081e161002c8400102e4409080ba00c0700704c0075003c1e422620302215144542e0b81c1c0403001e46055250301030700070040d80d96541c0000700d82e115840601046480354041c06810040414031000d1400350743c180c40c801c2c600610b444507100c6c140b2801c40340d41c003031588119000030488003d40396100d00000d044a800050b0580040d0740020040f000740b0401c80303100d40c000d00c00140080d036000003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 372389658 1250 372388408 372388411
    0x11060a03020418094d090f0a050609090c191703091005030c030a0207030e100c051b0112110c030c1b0604031a090a0c06201203160c0c0905 61
    0x24811003400042040d043e08845d0984050a001c0c43d5550581529030000281701841d8500354407524a031132904400108401e0001034800020343c00c10b0400b0001602e0140c0101a000901a1900b203100e1400d0002c036600c0710315041d8a94400c0381c400a413840c20b41e00c0c0d86540405841e00040c155404080060515603c0d80701d2002e49000e41b040b4134005c6d05090142042d2403089203030708841c1e0b11f9980c0e046904002580114070407002d00800800c580c4c0b042d00d0307160640f0f01c0c00c045a111540b10070018140940381015008900140200382c2669800c80d036030007102106401548030f40410f401094070b120301007600402c480c1c0042448003041e2921286800591120001140c0110104c0300d8800c0381400154820b50001030280c0e00850504a0411100303203880781e20861840585445404640e82c03100030880039800b0500080c83c882c01c0780850306070b0f00002c2e60100d00540080000c20742d4041e86050902005110103041c55140718013121881c0905c15250010750300010030052140c40f585018001c050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 372390908 1250 372389658 372389663
    0xc0b010f0e0c0c03161a0a05010806060f01050a0e031213031406060303120a18080c1905060103022b0515010b4003111005030411060a0302041809 64
    0x1c86004103400c211080100d40d074001d890405546045e414088500c0c000c2200c0c4002c840003028070b1980206402000c0d0458065400c7e0310300801c0a5243c000040d142a4010345101d1007001e80d15014503041c1e0f003090840341e00c0707840c078180850040900d0300001d05207001e4841f140464000040d4140c40a40c142240c601640d10690100200081c00010b0998600003203994130b4240e032041111b11143c0035141500c03640300d040d0400100d1844c03181050410380c40c0710248129914100482c4401c520007007406200c07005601041e00c0c004142d41512400d64590040c84081d00400c10140c4000d0b400783e444c094210141c2d54980800c9951855103043d55983c9070412081c1c0702115110000708200c0700010071035840103410401e220b008200c1c0c4103103e592894400d807074242d41003c0c000142380d420080762502c004602502600d00098a108103000c07081050760307203400030000308000b000001000c409030010348013010b641164841221441c281e001b44107641080100d08100d4400100e403e07881c2d04104642403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 372392158 1250 372390908 372390929
    0x1104111803010c11030301031502162d080306090a02301005030a1709030106060c0204050708061e0616060b0102070f06090e0910090f0b01050a030c0e06010c0b010f 72
    0x850320f00c212415400c500383e2201c00e070010401040851042e107044d03086d007507601c0b0b40107280c00c0000c0300c141d0008918140490701300c2165035034072111403c8440880c0301c40d443e109680c020b0801c0c036a228140f510005062606c15400ca10201d44031407100d5040c0c6041602c03640807280440d240d1600c000e141d59030001500c0e02e0b4240c0e40f000441c2080c0e08601c91040f5840500185014106903488064003c1c07100041117a80348103105a00b81c56400b40a620000c18035900c0d842d00d40941c6006000503a000101080c090001141c140a0700c1e880700140800307c030240e0001182c2c000c0c03c140000701503118071001060366403613841c944010f00103d075010070f031081400d800312100d480d03585036a1a0307065018498000804d1841d88104800755005550030b40c02200b02069400c0c85200504d14411100001c1050300c020000c00f00100402a214046601403c41122203541c020328564641c500c0342050301407024040c0ca40c8011501a034080c0e065666220341c4046c180c0a1582c4481c1464000d0140303202c0d803600071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 372393408 1250 372392158 372392171
    0x1d0a12060b0303070f0f06150b071103030309030901051c061401031d1902181f06090e01060309030c050f01050712051017070305060702010204060f05090d110411180301 74
    0x80c41c00108885400d6802a03c0511014803500c502e0004a5011b5080c2c44c0701e61207104000e6031201d500c0c02000600310301a50b407611030a40e810031701c0d5880440713085680254810024001d40c5403000003500c440300c500b440c21a07a100d1528000b10007202c01021510341c500d0524401140388ac0700d0600009902600b80d074200040e0304c0121010114000c7d0080100781a0801208d80f400c543c06003030525a42c9002a00200d4811402600a803500c41d089034114907080e80d6801d01d6a90b0094407030604014022807500d0810581050140c0f58800c0040c82448140340c0d0794a81e00e4105806038000d80d169507081703c00e0364400c41d040c0c1c0348140139100441b0198002016504401d02c035111510580f402000d0421007540850304200e2030810074002c030b0314180940d10a2843c000001201081040e1041e09164005170320f551400201070241103801c1140c0341031081c14001d5070348544900640162868200003000300d184000001b040c005c012804d00005170080009001428a4002040c0075800c40103a0007002171 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 372394658 1250 372393408 372393431
    0x2220f060f0f0905191a04060e01020d0f030b0d020402120402010906110c060a02010e03221502061f09020a0203120a020a0c0605040515040308100e0105010f1d0a1206 73
    0x1900362050b03540020480c200003d200381d050202c90301c0c2611030282c0c107040e58262184c00f018284044c1c49440100040d0000301400043c2d070104680e600b1000a00080c84500c004407c00b0344420310051402e41090f5075280303032850a5480b4544500510b070050011590b4200440d90720181f49401c8800fa40411240d080000700c0500c5800c0070000c50800b080a8010713601d110b8204507136940000b51800840d034850800c44a6a10148002c0007243d441444450706110440600c2845401661054145210f001243d00c0000e801050b0305a114102c0e521650380001c5900b100544009583c0041001c5840882e014103580c1c1c001004000545150149034030a40d900b000040a03407189501030b0740062284888e040001c0d401d90230075030f005403007a415101c81002c1c400700e0408141003100e0a40000d2202c8050191002084650b840a4184122a541c0c1c42d8104400a003998100ca03102500300f00005005906100780c0200030044601d00030401c42109665001e010380d01981c140054030b08074a00300181c2d07034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 372395908 1250 372394658 372394667
    0x20a080105241e0c0304091a060304030e12030c070e06040903020a0b0c04050904080306010807030911130608071e081b010e03030c060108100f060506090402220f060f 73
    0x26280e00c8626800d00c80302484505810b5030081c980358190890030b0240d10401d248034002905034041100b00070354482d03144c40048020f44403840310b200d109202c280380d46000e907101e8404481e030040d0142000ca6000c18000c01107008030407514420396503408003090b1821480000314149088403080381c141115900c1c1d40c4104170440d24901c1000300036900106151001034800e803c0c035035010b20124001420141d9030000314092050407941154100030000070044550b81021049402c80c03520301e02009015100da0b10b094001c80405d00040c46825640040070207500c0540051019200748800c0c0c4501e1aa11403500318041480c131140c040500402c0310129100500060301190003050136142411011484015aa50b000081c9a00c1d01400200f200100ca0702e41000b0f810300a0240300000e100e211040407400d002c03100040c2c0c100c2e0b801c070704080c010400340d80c50200f69540d00c1001c481c01a03940040d220034410041d0640c0c002c0e0115010500c001801c0c1c100454510304a03103950b12607180a1654983c221b8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 372397158 1250 372395908 372395929
    0x91a100909060608160807120204031208070c05070306050a09051b030d3204050904030c0204051005061905070209010305240f040f0503040b0f07060c0e100815060a03020a080105 78
    0x40305c16410750464480e00c1083d9a60300705031a17050112850600021a1080c0d9001d90003e031081074030607000305d0a0560240c086940003071303186022400c031000c80d510301340c0307500007884060043d0351102c0c0402e02001003a8000c120031944042201c10095007041908440444118100d10034000c00f0f03004501e040c052440141e40d410340b07550004202101c2c02c0380c445003081051040e0700340d850900000c209074440001007400340e8004d84952010b14224030401c42502c0c8020507564512140902c00c009503102c007400e98215542011901002201c8085c088415004001e4040d50180031b04000000b880008240d920700104420b903405407205255503480c81c0254283d41e0101e071041e00b500041c1c0800c1c248005d1105007032103601541e01c0d10b0307036610a181058100c804000700f01040003855008003c0c40707110703114201304a414040504000e03040082d50849a0a241c642030100110001f503860040c142d50180c003140040440e502c41800d858018002d421400841004c68080000071555162001004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 372398408 1250 372397158 372397171
    0x21c150f05060a061b02060a08310f08070605130605070c020109030f1b14130605030d110106080102040b030402090702070308030c1b06180709110301091a100909060608 74
    0x1550840d04d4604d040300d000c0035090009060280001016005944a500505158407250b440d42c5803800c1c5180d5070b0703040309035601441f118222580030b01031016510340c545010781500f0500c9002402168106091144984000200714504d4a810015140f04000020303c855008000070400c41e503d0b02016941007040003000f80c0442e41400c01003002815807411801c0c0d0922550701620f8890f400e44500441d241190041180710b08050a0341c190b40c1030265202c010459810800e0200300c1c03030a4086500c0c2c7e0202030700c1e0401c02c800c0c0c0d12114070b14442500804000c001c004021982c0300d58950804100380c10070b0754224418080440403d105030310000e20712081d0713500650040d2554441c03084000903541300c20352440298a00c9443c0d070200324824812130f4419440d8054030307080d100204442718117183c5640c00280301a07151040901c2080c0b40d050590f815981544c20000d102840554402c080d065001c5030706502881101070303d1480c0d94001010003c58852010501c5440c0d2103010540d5281000c442e036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 372399658 1250 372398408 372398419
    0x9060f0c070f020607050f01060524030601030b0604030b070309020108010b031b03090a1b0503071a0d0c03020c1e0f01020a1d0a0e0c040807050d1e021c150f0506 71
    0x1401e01040000800000551004200c3c1d40740c00040c0d510941800010204c0001d165980e01c0200b1050410f2503c8003da0442c02002c2d91401c1c86826460b8450b020107070480d410143c0e80d0001109613180c1c0d100310f90107035800019040d40b52901440c010094100c2400490008000200021b608513142c0160b0b801661101c01c0394030300410b590b841c81e81d00e41000301280814400e104100c030103c3c0038180d60000541005240c0c000890814007031501e407034004d6000315414810030300002c1c002140141903c0803403003000d4002c107100c549014103c010303001300c48601c3c00c1801010704610865512025810a03212607c0540d5000d43d41140058200e0107401021004102d000700c0d140c01341c0d402c00380f030041c0d0760301c0040c4215081500c84042c41860102218590a4000d001600703000200c000c00007000200411112803894000030f6a0b900503900e000b2aa8114807070091500c041155a022004000d440c000c0c1d0310440b1210381400c10900d460141e402144c40d95251030300e04150742d061400340c0f503c142c2020b4503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 372400908 1250 372399658 372399667
    0xb130902010234090f050702160608271e0118150204090615120b0a0e090c03011112151807020c13020301031a04032a05031209060f0c 59
    0x5102103045603e08643d10030f030f2556558550702d6080302da070100c0a402e032036600148000440304034104807000900300c1d50070765000807040c006240d40c0403070413800d43c0c0703c41c82d0126a68403003000c1c1c0da01190310405029030440205854003850000064a208204000c0a9120f00c100c0d181074414201d40804044079042500e002c0b41e4800b04180441c4d4142100202030010302d801e503601032b807200301c4506401c044988035400c44c00700403d65010326141d070072901e001020070201d0304940008005001900c21000d0605001c000120540c0c010b00c1340c1019004050000d100c0f00320a00c1031580c1c103911290508004500d030030045128404005074001c0104005045c0001d103248502140e070404070700800034821807041d140c90b45d4150711101c03401403036880800c0380540c80754154a020010407400e428070480c1ba5211504000201c3e50207441a4002d2000a03044000607030b07009a0046140d8501c00b019100e03200010701d1101c036131310f03c105843c403880d046410342e1115111611030f44a24401038840d444014003d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 372402158 1250 372400908 372400933
    0x218010e010501320a17071707031b050c010606170a02070f050706120b030303040302060711070b0f03150a0b0a0e01030f140106020f0d022a0d060b1309020102 70
    0x15001c8016868456030806101a40c84804d02c0100341c5248080c280c91000c41c5203407495403c10001e03415200d12124013101e51401e081e0040603904050800710600d0080000300700c03201e0103a0f00c4000b091610f14003c022010583c600504642d00801c46519150320781000001c10600c2002c1c1c0107080181010007013540d40fa014200c80c003a4001c4030060700c0c2c400000060301d0004404100d094001d04194403410500c5000362000000c90300824690341c0030341c00400400002a50214989610801c2410881c0c24a00c030800f40710300d40004c542154920020015a413841c42c08a0b90246110b100c1c0c20000b4010402d004081c8800841988100c4004c200140101c898650243d00c42003003904041c9000100254906018015506840621004101514014444154184040c000d0b00c01e003070004040807403040d00000c0daa080c2026043c842c00128031052050f041508418418403d002040080c45080e41e0400038024240d05428501c54a102c0c0b83d1780c81c180505d4010b0114403a0160040e00400c0c0015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 372403408 1250 372402158 372402167
    0xf040f02030a1a0f031f110c0703050d03020f1605070506070b06130e070b1c0606030c08060901120809060f131401020c01201222051905060a0311070f0218010e010501 73
    0xe03941404094445801c0c802c0c10040d0f1002c1c048d45e0410b1310052280502e10b003840d6041012100a282c02c05004101d280c0540240d001112000382e55030950050300211420318900f800d4540d0005940b00c1c40008a59007802000c501c200c1c051141182d4a10402c3d40c980b01050071110300200188140e00408000c101000110029220401280050170440d445039201c00c4100d0315180c000f80c01103503540d40b00c0801e1307942c40480203500010940d410711055040204031011244010402800d18600158121064860030151900440c210150300d848420920414a45002d54040c0010040e406c000e105d8040d8400200b03d2660001a100c111001240e890031200c00007a000c0344442074400e04201084600112004117400c1040045e201142420ba140c450500c039250742c0058440e4140220311500d200411209100710b0780222130981d80d400c03c808094026107007122012003411800b0030000103203d15a2003181e4400e108540e40c448614181e410716080240c2805008680101c03800140aa94000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 372404658 1250 372403408 372403453
    0x70f0611010b04050711010507030b012709090c23061b1c020f010c080105031504021302071209080303041a130209090706020613110f040f02030a1a0f03 67
    0x300b00b210900c004203066600c203581031000658200080240074000f0b11030940c114496140c00e104150030340d80002c0403081031212151001100c0b11122400102e50002280105034070b42050050003007500f01030031084410f104a600b001c00d01a4246507484030031a4642d10454010259802c244502002402c0c100b11044007464500c42c5240b201038031002141d00200250f9164010411000300160660030b6882c480600024013103280c0041c00315036404243c440c2c507200d003d884c100c1c082d591030000031040c2441e9001a00c0052000503060240a0100c54200d143d0312680c40ea05000d036516000c0d55903070310045401400d200901280e0340401c0c4028481c0c2a04104048101c079055145c40d00010034001c0c0590f41e83c3d503075608c004801c0103403603010b00c4010780c4698541000c2207550a580c49044015030300601541c419080500c00101c5680d0715449a00e80e0038080200b15101d103041c0c03000340e00608600002c4607034540d45d410002a20300d440707249030210000c007034007400700c04a400d640121202c0c203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 372405908 1250 372404658 372404687
    0x1603060b0f0612070207120b0103120e091f050a0e0a200c060603060f090703080c031309090b060436060e06040b0109230a0f0509011a03070f06 63
    0x1a0724004801540e584006000300100d008880199410138040185c50803405502207485528080201da0100d1012000281140e4210b509001d0f0000100011100000c12940e8583d0006d4941d0a00200080c000d88203044010b40004c042001c0d6103032010041d030482c581c4104540c80e100240064049040703500500102011401243c03508524489400d150350001c070b10b456040da101c3c40412040f494104100781e00203800e00900b03022070924500303803030f241c21580c0000380040b00700061804008004000f10f58010844800840f4102c1e1204480400341c4040441074600310b4451000c02c1e090300e018460320f80365620f2503600c41800c402d4094000782d0b880981901800046c2114039080100700c1034021201c0038819640500034038580703440d007110014010b030000d0340014a013075043e001c0c0002d50a500c3c949101c80019044d01581c460290700b001d40151842104e945060000b03100081405401c038449120480d0805000c207400f9405261352040d042c45900031105a0070010051580a81c003501400d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 372407158 1250 372405908 372405919
    0xb0306100e0303041d010f081213081c0201050a06150f020307021305070206071d0906121605150906030408070314131505091e01032004090605031603060b 68
    0x46000700024107641190303111900d5401c1c00001030300b601d4420341c04035016061100103440420704002c006a6103d159480541c0e8143c030000710403041820f244017480043c550300d4101d03031510103540f1035150002140c40b00d6602560a0101044ca0811280901401c0d5200f5032a6000181d0b840001154416a0460442d003980805c100501c0076880754211568218600080803490b0f06110340c00a00c0e2140080c400c41c100541c000c0c8280c55282ca448410407840303c05c4030200c01681715503001440c44180081ca0074040c0c440c15884001900035841031400b110b0b0110b404441503200100051698130030720402e158425020000640015840b801a0000c0c90103807a1030082080400780d80000c0fa4442881d681080a5a80040212030f0003200b840091010300d14059042200d0a0701048001c0e0551280d101040188038040e40c5591003079000e0003050003500d030072400141980c06041e074a98094012000b26500b041c8000c922400d001580340e079018001509000e04a155845010003420921081a80078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 372408408 1250 372407158 372407177
    0xa0815060907051b0705090603150114040209090a0f05070504061e03020f0703090e07030207020619140a03150503060103050709020703030b280f050102100906090c060224010b030610 80
    0x711481352480c1c0d03040a0940c020101325060604000441d074004104030320a9120140f941013140703901c0d5010341152200366813844400c00d000001006030040031405034101ca814010015445d045410070450000029010009070300e42c400121114815402440003141111031100e41258a903281c9800003c03803031800604100c1d0321b80350844076078004c000a40001d04041014064011007070303c059045400c070f003401c510300941940401c0c46e40c0605040100540641c004420b03071a802100d003009110424034175607503500e416620182c018a100c450300b1804440b56040412103080029800c0e059079003040c01821200e14022194019601c240000c03010941c85020304802a151008a000000100390300d0b0482d89081c0d8001903140340643c0d21003130b00c00002c40c82c1080580d80104010b2084400e92801041c00c180b00c1c20100c014120096008040501400c00040c03c2940883c5018070304180071110000030070b08080f02650000c0c203000d482004803040001c90b40720b1400d958900401401c50038907000c40c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 372409658 1250 372408408 372408427
    0x90a02130e0304062c011d0102070504060f0807080604050703021005130308030f240411071203051608010828051002180604140d1e03020c0a081506090705 68
    0x2e50700954491004600c520604151042c1606201c0303500080766071002104a0180d070008081d4030550000c0b09000d100e580800341d00d40d1003400007101900c0080e2050219659940200340c0301d0040d8416101d01d8003a0500c0030074800004503035a03001c0c80d0000000d100d12801e42d02001080c0094044060501200f008003280026000310058002c6004140c40e9490b442c0401007084140402001d0100032009404591200506121100c1600d002594005000390394000c6c2e5815611a000000d0310071407a02000041c11540750b007000d8070462002285034800c5880d0501a501582c0078059040590404503c01c1078002d6041d8940440703040d0345854070394031710007500d445041942c4030b84040c9032660000707001c05002d03200e012101d11180c0305560403840d151818013080030050310031401b1403051615040300014032071041c02c0700580c1d01010901005100883c07501954501e05d00301aa0701600702c481c40025000e02c04201e103c20441c2c240c3c83c0e00301c1c50790340307900300210a40010031400c184601405000c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 372410908 1250 372409658 372409663
    0x21608030f04051c05150f0f090d0f112a0118090b0f10081f0b0412052e0b0a080c0f030325050106091107120e27090105090a02130e 58
    0x803000e0660b01c29801d01403000299081f000341480304404c1c5800601c4040d80000400010705040c61070034542480d900c0d80221942e05901c181c5448a00c5080b540302402c2d24a2000c43e00080007105403d00c0c6050700c4401581d100e01154203001d24030382c000f281003040780100e40185140f00070081442824a004400240b00a9003900c44d4500040a0104004000c107404075098200210345003060a090318100a89005104901a43c0b01512848411900b04181003000c404010071040828140d50381900628580d2030034040c10b00d84280c10900701c815a410a054414103460742c98029000311030b00b840a2240c5940700d503d4294140c4010025003245400a00742d440010841ca44e0084901d14241455401c1d02d2058212050040c54020721134000344082081b2030314103074480100d940c0e8806d42071054428585100080d43c00580c501903820005501c190192241040860400415180c24003041e00300c800c01c440600d111750269801c080580760011071942d1006007075801241d0405168000350 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 372412158 1250 372410908 372410923
    0xc03031803011e0c11010b0607020f130e061005100903060203071701121502040e01050d05120409020405031b01050f070f021002010c08070309050303040f03120903021608030f04051c05 81
    0x3c2000d981d900d686603809a102c0300c0001908803410080c005800d10f40c000580718480d181c4000e1255407017800c90044d9031140d5500c1b4102d1400284200400c1c401c0b160500d8480e00202c0c2e076035107090050340c9c0110f02c502d81202c00c0b00706d8a849644d00400c050445e500c0b50001d6002400c00428800110717a100b40055800c60040d01a04042030003014013040b910b011041c00184000501c1003034014081400403107960724a0504585c0308a481002c4e52070b59050148c01c0c01c03485000080c10600024000c81d400034203800400031100103808aa41c200ca90031500000002144585800124200002810001140d000d88100b5000c0c0000d0841006103600060050b038984000ca80940d443d102159605070300071807000d5200e5064102401003030344e9603881c00c0d02e0740b10040005040b45402a010000d0502c81c40c48907440b0803d081040000c501d490401a41d9009019580b03407000e035420700c0200d02e6171000700989004210001e03166040c0760505c410030055410f8000310442001500380e0382000f1440401090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 372413408 1250 372412158 372412211
    0x3040605150d03121a150a110604030305040b09010c0f140c060411181504050703230103020a140105030c0f0c1209041407200715110f0c0303180301 65
    0x4120304003d615526003502c401e6825840d852480320300b07000c2d0a445490210000d691405000c1da500d044907c419038400280781c1420b2428480c1c0c0b001c00c420541c25038009130207603019403034070400c035641c0410711820399815082d2500012007100360000c0c06405803481c00c0842081460503820b02d000312141074a001011103040d5500080540d804149062480c412003041174500381408040c54201c40d900c0c068103000c00c1490150741c0d24000205403031f00ca544280303441120030502104801c10800041c1c2d06600c02e010a80c45841320680010f503202450002ca40300403c1a16194155640e050300e8a0098201b0f401103400d2030404c00407040f40c41010302055025240482010751240e284000744402c561120310440b000d009800c0078003584a81008482e202200d400800750101c1910840342401c142c0180e0040c803400c00b914142080b420b411640e4440343c80d21200444803801d584090340c50355910f01d07052540e0135400c204031140150011168050241c20003900114100680c059801180480017205 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 372414658 1250 372413408 372413417
    0x20011205070e2d01020a0b0c07030c0c060815040e0c01050d06211e150b04270605060409110d03050418021b1506040b03010b0910050102070e090303040605150d03 71
    0x4400039400040c50310f20840001e00c01030840201076074810394090406440581925000300d02c820416200b0b182515145900040e0781004c40d58544d0081c20010056500354440510044c0014143c02c1c05d02c01c0c1020300f865a401444804004001902c06070302002c02464015142e090120380406861000e61420138080c009176800d100321f080080200004c00c0000c0302844130119001c0208007106040541b10400000016013001d44030000780c000c24403007542110311400c0316041d108008100d12407900f1a030244a081c00107640e240204001c40300c0714440144003452544007102305041040b5101e28882c82400e1492400d5180d0b070020b220180c000c1c030040021034001407081005201c032000c003a002c1074600000c2c5030401030302c0c49038224508010209070103142d07901c00c0089256001d4206810007140680650601d09085c106410403812070700401e8098861b107400002e100c22910f6002e441000180003031411a19599201c402901c00a841144444080900f003400f0f9550500b0001e0744601c40e888 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 372415908 1250 372414658 372414709
    0x527090c090a05011a0d0b0a0602061b041505030c12010b0406092102101b0c0e0705070f020d0f05100509010c030605010e06031e09010920011205070e 66
    0x81100a1000501e82282c950500d401082020110300c0c450200c41c8551070003544489503602d220f401030002442a036802032225100140f800e402207507140c080d0355104034505400d03c15036903100892060740300c0c41d040d40c205001c451407014031501c041c5030894811944580b030840c105504458404082e0007044500034002800c01c04190031010400080c826610b003c2a00c0d601520500e00c0340c00007580280c0206415401c909015106060804801c40f0300000249085194141000b0401c014001d0310404250039021034440340c0154199076076194010300f5080010380b80e9007030141003101640200c07140304400c5030010004206012452015104034000142403510b90060344c01d41b02c04642d5170007494985013080c881640c1c000041014900305640700703075a90f03d54041c00560b00355090301d0b040150201405014000f041904240c000b280030f03000c0151680c845000800903980615080d03070100c0c401414040c0c01184582100b584000507041036800704c5501c00124020100c0308942d080c10007941c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 372417158 1250 372415908 372415933
    0x3080a031409010b030d030c0804030c061526030705190c091a040b10050a050304050c1002030703020c060310050f01020f030a090305060108120f03250909140907052709 74
    0x2071700c0b01b4242c03600c0c05011194030700c2c0d0060841303207001e0405820040050503450900c9410382040326045072016140c62800c0e80d919000c1d0556a2507168146100d2186020036501080001907400042d0010060100010418040000860211002c036960700c0b5104001942205074403840f00d8902211000c504c80d41003040c01c101c100e61104402c1485042092054400380754001d0035110f45500a04211380d603034031780d410264940404101c0e031a40c891030300c48003490750701c0d4080b01415041c0e21076002c940e82803010504014a5005c02c0f110140c51180400040105150980010008a00600540d030303c851649802a085074008092800807c454940410801004000d1b540c01060844040c26547c010480720461922442c070218508400210200c3e4900100d4804c100a0701204060344240800c0c01501a151020900c038644a00e454440e441c0007800f5501c0384030748039000ba00040c1c11407030f08020400803054004445019008d800c0c03070000052001242c0f0081c001c110080051000c0305505 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 372418408 1250 372417158 372417163
    0x5090112110d05061206011a090a050d0f0510060b0a1209050607110c090606340b100509090a120c0b0c0c060105030a03080403081506070309090f0e03030103080a031409010b03 77
    0x940307801e285c0d50004004118012030032005d54080203c2102d40d49c0d5503101c90b000660a9807990700304076804548481000100b06c14040c40c1503841d0310074800c1c1d4030250548048103089465138414142c442c4c0741000142041171181c1607505000c2e00c851400580111503454081c6050002c1364018013103108001a181d044000f00424070340300c0c8086a200150b4130700030020842e14040c64001c01c00c80701c007140361390083c0d40344002070512600340000304030040021420950302c401c500307440100e022280194003013000e0070150704961144002c03900910360304910344da03560040d040590151003040111014072001607001030a141c06120401566503c0702d10101b103140c240fa030706a100380e20a5110003034640c0080d40001c04c40d03a016801d03041041096640841110320781012f080041e030300002c0003a000301015000b411000030383d030000307000300b1544000b00c3e580412030714880e030550090352041c801000007460f440c0041c42118083d01c0c01003a41c003008501d108035500150313003802e80369440c0c0801c54070343d0504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 372419658 1250 372418408 372418429
    0xb0a3b04060308040e040c05150304030f090803030f0c0d021c0e150c030604061d09060610020a060f06030618120306051323090708070f030305090112110d0506 70
    0x21582040110b15541c1e9036540c0d4030032803145511814450000030b0a000c1103010b414006c25000d02401002c1c070130000c0580d090351040302d0450114041c02e4403295005c0c45926220b040e40c8400000f035242d40c07240392000c0c4010000400c1041b009500b001282400005800502100d81024401c511000078801003407064034401a0000c0069001a00c903441882880c06520341007070000039103039541d0319010007003005031055411131280340c4a84542d43e02c0e0394266131200340c8600180b00c10784100340ca4602c04c00c15000c0c2c07001003240c0161b0003100440c01041099000c0d29001c503440c00c001a0b5a540c994601e81170300c1504045c072210702d001c0c0c1c03802e1040c00302034404544030301100c4c5400c00c40d41c0c0c10035000400c40b025171808480460356960030940340c0403254500a03000140c44d05c0d81581d030f1800c3c0200c01e6544015000b00d00d62070041c110006001c1140da806141a203616841d410b040c2200b82e4011a09401540e280c010f440b51680642c1c090400306a000b0b1801c070841100c0072405151140a110b02e0100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 372420908 1250 372419658 372419777
    0x3050114060a0303050a1205251103030703180b010602012702100503040807020d1103190c060305040510020a030b010806030a0201020d1220040501180f0b0a 69
    0x12142000310980c2c801009509403545400c000d6102c2200170b000325100780380d03548031011840c500000d208a010140303440d810203850006d6403032824480140e0840c0d40909881d4108400c0c2d0017400803c08043c0030f500302d00c1d0780101c40c0c0c42011140d4295202c03400010021707802200580d6403212502e03800303110030398031102c1c080c010310014200200640c040b41d60144030144010070024003001003020010141d04031210a078000b081200154811308289001c0d1002003003c6100e4480e035001c0d2208141c841d8890f11000e41c00801d80c034441460301000350003428008008481034000c002c0c4d1081e0a05952002d80300c207991a0350300041c1d00503003000141622002501642c440d602041e00c080c010303a070018511b04181c10394944840403903c90300641c4003510303110803d03104907040aa00010181c1030040600300300c66090fa200c0b10b5004c02c180e00881c81002e03500801140c200850024000010100020701c104211454184410030b82c0d254594038804c044018001c00c90200300c501c9828001c10b01c0350381806403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 372422158 1250 372420908 372420941
    0x50702010c140906070320100c0306030c1a07021201020306030106060e301203040204060b09100c050312040b06010e040606020304091d030a0203120f0c0a120e0d0207030501 76
    0x34821280c600b480c058002a10704c40c0c42d000401c541010300c00c00d03a10140d00301403000040c2411100070696190f284002c407032904e0502d80907001c51802d07c00c0c003a5000710703508a0aa5503d150600100c034004a044145c81c980c0d1100c2006840b0040e1940c2181032850840701c1c000584a0601d28105801e49045a111000f00300031072816002640d03504080e031a501e05009410040c0d81d02c140c11032a5a40c000580e15a413900400751080e44072103c0e40021445584202d03000c001298a8202d01400d0b400f80f044d8941c4c02031403003c41d085242d03015522071001c5900078811039060001d02c0655907070746c400440e01120ba045c804030500c821540c00500007000040125000d015403814694002d540740102c0c0310713a43c4070303e0f105c40414150306440440ca244107181d61041e00d65072210b074a00030359240c0c04204050002025040028412070300310b0040c0d8011074000b01404d182601503401290000302d820048192a540d44502254000f02080f01101102c03041e00604080da185061040c03c4131708401e5691401d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 372423408 1250 372422158 372422177
    0x40605060315042004090e0607092c0103060207140604020102030d24080106080615060909070516031d03070e01030209040503040806090a0c060f090b0d090f06050702010c 75
    0x203540d220192a488a603100458011124400c0001c2c094400403954215120504141204010301034006006031600800300340402240c1111080d40c59100b21422000291400024010001c903004404491117400c2101200c007980d0003102c0000c4c001c281d0086500c107038009120700c1080401c0c0c510080c0000c40101601c0a46020380010b03480f8412410101c180381d40c0c07544a00185075206201e20000005c46154506c07841c6c603204581d00a22040c000c0282c6840741c2c84c00030740040103507054042640302c050942401d01e2000130905c182840d02401c0c100c14001c09101c9500703010600341b040c0c0c00703060090351800700200103000798600781829103000314000e0b00004002d201010b0015816811685d0569140226035903034182581140900e40001c04907005031400c0c000054000144115800c0c080d0070012142039413002c0540300d105030031550705d01003001002d0410914500d8405420000d000c41d00100c3d074042140c3c1c8142c5251503c80c0c08035440d994403800e002407941d09115020a8004904003074000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 372424658 1250 372423408 372423419
    0x5101815020a0801090e010f09060207030806060412081602130b130204350303010306060f1d060d020f04060609170106060909050709150203070b15150d02070203060705180406 77
    0xf0014050810070689455040c1c2080400350300c0f9402c5441c4619040003c282c5902e4810041d40c0076620035400504d44001085070752a0000c111002c40e10400a464500c05651344d0351007541d0014881c202c015202c03e071381100561102081260001d52218001444039040700402241c5c19103244524806d030f01c144070902507541410321465154040705800c11807162800300519900b14014520304441c00044000420018181c200f10181d42c2c5034484507202a448000320112064200c900540200d07102001c1203490400d03141402515001811488a101039400441e0580b1519030040d000610000703002c12044010345250240541c0d0b0100901c8518540300c4000c1c20302c1e9060080000d500d5580000c1445140a01a840c00900c5400c14510f4000c0c5030440c041c0d1a078000d40c000b9502c2c80c1c2c2c00400102e19048548099842c0c40c030040c180c1c0c00400407400c0d952181e402c04082c81d40584e508105107030150350204155485403c856484a6540303400089102ca0355451181c1035000d80d04002c3e080c000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 372425908 1250 372424658 372424667
    0x4060203340204090809060f1c020a0e0f01170c12061c0813090906090201021615050714010608030301030507090504020906220e0c100903020a06030905101815020a 72
    0x4000b0340450b408202c9554500b0b102d00741e0311644040d0740d8845800030300d19001078001005001c208040b07d00c540010300011003690142d100b01040d40e00090b040c4200d11419180c004020482007d040c5400c902c0c0103030071701c500061020306403901450500d021500c40100b819421001b9031060b000e941c2c041c801400315800c040410011103000344682c00101d05034541c05006003906005084410741440400c026052050042c840d100060b401402162141c428500400e0074100803590032140c14081c010079080700700c40c1604041c50440d48004035811004568100b4080c0001400410b00595525451481d00d2850102c190340000542c9041004000260f500c0d00982c50384240152142e0b66040c0a000c0040441c40207080800c0c400e5190415009090b0800124200c41c100300361503000ca1140d400c4801d941c10813483c07200942c044c40502d0144202032113034004003c890300c03e108a9403610f18100000d0250381c10040c6d84866500c01d00e22103024000d00040a0070f22645c184811498024009030091 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 372427158 1250 372425908 372426007
    0x8010503010b011e050906070f0606030218060d15020d020d0e1501080303010e040c031a011a0909011a041208030601020d050a050a0f1101234804060203 67
    0x5005c004100010151207410848034500c0d40907810401004c40c0c2c2c80c1c10030040c0344a0106034081d010505a02e10740000a0382c51600071080100041001100d59072403225200c001c2c40d10001490702031144581d031088a0010b406602e401034030110308903607140a00ca14050f204810042c042e5402e100400c40d07010017104580c10340c2c5001114100750398440c10403403156103071548002d010b4082d50b010100030201801105041c0d40c6005101401041090700450007400b80c0f9016681c003081501c01045410014002e0241502c00d000b001424165030300c600b4003540071000001c5d6180c0100204001c21581e050180104092076400c109041c6600c10200400c14004c0c89941c006000881124003078050181c0700c000b145841c2d0070001e20440308802030b4200100340700191211180750401c042440d801c2c1c1480d01c400841240c4200810000f1510b00c00720b8240109a000900451171001c4544150002e0006001504068000350b07521003e00b0000900224045041c17066000701140d0140440280414039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 372428408 1250 372427158 372427217
    0x6180f0213171f02031501020c0307060c1109090d0206060315041401090501020307030209011d0922021c03110604080d0e1606031b020a150e15040308010503010b01 72
    0x1900c00c0070031010782038508143c3c01d1484251a03601e4403590b4030942d69030011440790f440e181801012810810059943d80142940f5983c550041d000c00c0c410140301e0b0500c940740314001c405d2006e049000c00089004213006a4245c005500301ea00554021070f01000006d4001d101940104070794075020581d68105140508010207040090000e118440d0003500040107036500701c4021503880c100424040c0087d03002081d02c901052034406801c10001442c07907941b00d14a005071035400030340d96040c2c800c029103668200607207400b12502010780c05611141c14441818012003813151403015a030601414100940d2404490380d40070346c0400c00040c80d0002500c0070520205400f10380b5902810f040ad05106a1906550100a00150016003180d2681000001c080c100004040740d1001c20002c03038075005019070140a10140c1044a1301c01d000c1c541c000c2201845400c252103130220087c800394014081a2801c0d8001746030b100041c8082c1c0303401e1041401c000300c00d091140d102206110b44000400104a49 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 372429658 1250 372428408 372428429
    0x30706030509011517120f180303040f0803030f090c010e061c0e0a06050132010926011d0c0907020a17031f0302130c1206180f0213 58
    0xc1200a0002d422111940035450f40200425445410b0421070404203004585c40d40724220700040b59800c1c250403549940d110044041c601401080f02e4a21042015402500f5100801000444404c030045010140c100d02d0081c40d5a8100321801118440024000002d123400c0b00d112207850f682c0140c8950800c510a83d0a661640e140c0d410342c035210728030702601c40d45c058180300c40c01c0c074851000b2550340802d51042e40e041010766200c0c100403003e07181c00803100c00c81d410000000d1090b01203411401041c00014900b0220746c81d144c403000000d60880c424070401d402640110403c4135602030040e041202803a04c241c2c5200d80307040c00d0065440301458030850041d0012400729051701c0c27003031201840c0c40f908000000130f0441d01000104a503803048802c0755070140c140c12032060001b4036851410840350000c02951014000c88100b03001040c441c0c00c02e00610a05613484500c0134280d000c0c03000140001d40245007800c0c60b5080001c1582d51805030003508601c108400d0710300d03460381234035041a070714000076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 372430908 1250 372429658 372429661
    0x2090d11010e0406030506010510050702091504110c010c030b1906050904060503030a020f012306041e0c091d04020d08030c0d022a121801090b0406020115060c020307060305 76
    0x1030b074042d6607046030389400c01c1c10003c2c040144000010224120f07101520700e0a442590640111614028030100942c000481030110f200002104500a580e035001000001e000c40c0c400d1500e1803c0c2d100107d4008903944030a000c4070b4481c2c241c4600920144161614000040e2a00c803036a041012801501c0c28084003045181540e00c5550004000d028007604880e611140c100b4061f581d940f40007918611582890841100c1d038480e5881d880216803204480f94442d221141004003410f540700c40b162101a04258101d8503c01038003a82100e0310447c0c81c0e42c0704981c1002001c45030029101d401c161481c07804010b00c00184c03140034002c0c44440e0880d80380740d01da840b411003180c4d240c42200e000c0180c0c14004904a29110401500126038000f45d07030500c42d014110094240d15840c200c8184190100107121884a4482c85010703051071003014034010007590f071148145010b903006030300305500507951580c0c5601811041b04d030f0f48020700510b052030090000c859002941c1c0740c102d8060321042544400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 372432158 1250 372430908 372430943
    0xc050d11090a0b091302090a03110402090a0f150e0d1e0b0a0f050a051501030b0102010e03030c21011206090204111206090c340807031d0402090d 64
    0x6603071100c0801801041e0042d0b031074103182e60540000b20a11320032425110031680c203c1c600d100702c950703199026080001c1c035031450b12100050303104542d0141d000340c1c0811402a20b03030b03116402c4c2d0001e0442000349620490030400c2c1d2030081000d0807075910502003001d901074000e0b616003071603040781580502068004c942160040e544424118401028500c484091002980090b0082d0041500410041202e5522288204259901544d66046004403074100d000c65501c20340040d0750b261818000803480c1c1c09800303aa5465984219101d1046000101d14004185214030b40f010040c04d443c641c00c5119418038611403250000020020301d0320b507640040d0350854495030000503224070408525a00c1d04100444040700a4007101c2640c41240010009814000c900056505032180c6210002e200c0030a0a014041080c0f841c400c65500d1601904030b80c0003038000c1c80200303241846992030842d03042014000b08195220710321003504c40c07801844030030100e403130716001180074507040008418103d5030342 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 372433408 1250 372432158 372432191
    0xc060f0c04180b01121404021306080304080109021c0203121312030302090301050108010c1407020307030803040503134b060e03120f0a0f1803140c040c050d 69
    0x340d22240d400102d8010494490326641c1c4054800e1000b03880d242c0f01095010410302c21500308200c60000f0010000208002d401e2808800500d46c19006000805580b2556041c2c40c64100c0c1d80000e40c141e440b240102e04500300b40300c2c07030312410308441804d62889201d50f0000c2d84484600d10f03403502c42c40c00450008980712250051500034440000070707581d04490390400034069480704891038040e40c00d02c0d0001807040014428003030000d074165580404145a10840800780d8440c90b8160707458801e240d004000306000000450080d4456002107555070002400c5140728400380d40b02e03101c01b442607044541c0d0391007a9202072a60034600754815a501c80c00e1140c10b00008031040045111070340d004404205650048503800407100c1c00c80441e0010214198556003d100d48041c80c0403450040c040300c03800700c1c00350b00070801500d014105040d003041c1040714001045151790082d5500d506020713031000e12503070600042e0b00740041902d0502242c6059500030388184102c00d01301e14066910100c1500980303a4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 372434658 1250 372433408 372433417
    0x1060f031401030f031e1d04020f03010e1602281a071d0405010315020a050708070b07110102070b041103210901030507050a020c09040c031209080c03030c060f0c 71
    0x3030000c0c400319584900f031000c20002c4c060821801308000c070140c1304440000c01074080c00d00d03125590b000f852060380c05240b504004000c10880c6c1080c1c09020703580d0341c085e00138007950203400000f000030002d1510090507a854900044128190f401c844031458566140510302c204101c00484031500482c1c0c9890182d0035800302040f4003a1030010070052008007544030b120141c0029140d048160048070450402c002c940083c400180201c101800300ea0250800b07402610040d80e180c2041403d09040d0307169044641d100c814110f55004901c010480e410750046140039840514038001c40c10b1414541d200d0040f02c0c005800500b45d103030f85039003900303203a901002105500107111441562242e004180d145c5981c01145078940840d0403d00000c0d5a24410001d60351051507541c02001c109020205000000f0790203081501c02c3c4421810210104500408401c1c06650682d500c4482d14038100038503007000500d4110b81e100340c02c00c108100f8032000000d41150806013500e0340070074541b10115884560b109 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 372435908 1250 372434658 372434681
    0x8030d050c121f1401021f020c161a03150d060204170106030c0501140304110406090e060915090307110f0a06020f0705010201051603020a0c050613020112020a050301060f03 76
    0x1003040802c04240e02c203440c2843e44101075214050001c1c0c4a02803112981114210f050060748100c0030701040c1079500301c1411803105c44504c01071412140f80b040da0b05058031010074465189000800700008540104400171603e00e004059082d400c0c08003010040300d40800113144204010080d603420b00032a13a040340c0003000e022a9020462289120081c0a404144001d9640042c00c202c00100395009000e03007040b4889055080c2e10319511580c078145452016030310075400c2540c84c40d01045003001071088441901502c40100740c00d10700f4200c500c0c54003409080c285050401c02c405d000400300000140e035010740d4800020110301c100300020076045d000411485500c944500c00008020382c001c00e1f5064200b0100098402c4251100c00580c02d0b150709540c000711425a00e14030303600e4140302c0c0d03028050000041c034004120500316110039240440c29030304009003440640b00c00045680140404032400185142076090a012800142050005100700001d02c4001d00484078002d1290380f000300c3d0700e40e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 372437158 1250 372435908 372435937
    0x7030b0a0513090506010504141611060c040e07030b062b02030a2a020601260a1103010606020c0603010509100308030406020a110a050a0809060c0f0a020312030108030d050c 76
    0x34000b01c01c00c06801507090a540d103000d084d0011a860a240c0100141c40c51a1405080309840c1d60500c0f44007040601036220802907040c5000d060800d040c0241406160a01d149a0b1101d0528a01040c00701d4082c202005162a10103540c80c1c03a101ca80030b0340d80000102c0543c02c0014080c40c61000c0d1180084c1070411818400810008016000c0c1d101ca40d9000480c050111400d9620405501164102d461800540d2025004200f03002d449000da40004607a010311024070502a84400e10340b0418040403200c0d40700081c002c4c12242400d10554004218902c0140004070030040403500070f03c010b00449005404090000700b07410b4040e256403008503070250296503280340504080c802500901e525200003401036252140d090313030005400162a800401502d8450225900c19074142c0c00301c140150004400d102c0758410000a02030206000524001b03810303521207070b10415040071a078245482c0e400d0414401400065000000e48141c21031083d0009a540c03a900301c2040e0728040c0d07a0b90104801e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 372438408 1250 372437158 372437179
    0x90604080d09080610050609010c020d060c020115061e051608040e0112020918011b02010e10020301032004020904020406030207110402160b0606070501110a1e050307030b0a05 77
    0x2418001010038900c0c090b035503502445912501255201c8030155401c4180541704201805a880c003000240f0f5a09014182034882108c540c0c0841d00702c0f001c6480030380e5107030b60b07446880200700d40a0042c04c0d803450701c051030180ca281c00c148004e0100742070b201072040c0c0e0040f18015011601d01403800c0720300180ca2210090202200e0b85482840d0307501c140a1788903041035980000a020b6030500081c1c510300e50091051446a685804a142004c0144c0000040c0d41d200e801c9003c0c0c4080b0505a441405090340c00480c040c0c5445140520300642e10300b45941d0584108010008152105044c0d0101e022134061081c041604100142c0640162081f066202e07100240000d50715815500400c00240b1580555606581c1c800c02c00007240500355101d07454100d6085614001aa0ba0000316404030004080e41d0403c0d43caa00d40c142100d652540c1094809070000300ca246484e0031280d01250141c1300e55100d00f140204d03140c01441f500001d0700c06002d06884c0e1107920015540d0031301d000040e1038007610b40c2051 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 372439658 1250 372438408 372438419
    0xc0b0a0215150307170706080423100e0703050601140907110709021305090702070803190504080106091d0105071d040219030630020d08040306020c0a0311160b0f090604 74
    0x10310001095461203211b00200007911500130b141c044c1c032841e004136a03a0b500c10b4410b04108035910071201c094080b8011000c98000c40c103441d10400f07a8005958005203207260862818500c2c00d0b40c10380268000280261640d04e5580d0749000e00c40c0d01924038503200c6190b40007002030500e0003411f1340201d84007500106902c1c5480c541c0204020880e042103602c034000303844002e1b045c0c0e10b0b9901409605a075400400804094404014100c2025500c1d0b01c2c0c103174a0a569000340e6400c407030b12a00940034041d15500041c4c211106078280450b607540c06030080010f803c14110180403101044a07491884010110040c1e543e551a41614284422009240b042016200700140141080d006036440403056910802060340d00340c2112001c07242c1b010481d55074030f105070200182c168081000b11080302c0304010200c002045070014100c000c0880b0000c196103803030391602a1200110360410007080e40011503001d0400980310071031045803400541c090341c034800381c0c1012074684100850f40707030898400140020b2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 372440908 1250 372439658 372439679
    0x1120e030a0f052d0702120109022701141c030f02071a1204140d09140d020904020108150a03080903010c030b0102030301030311100f0203040c0b0a0215150307 70
    0x144031203655a07070035000d21201c0c2070391a0300440c0d204c40344910301c400c40c2c9a05100014420b03024413140d064a503040844da0f5002402c14100c03a0075084459449207402411801c0003400494030ba5040301041e843d82402d0100c2c0301c104801442043c656049104030000c45440d0564980000c01140a554500030040d05000e0720760808440101e00500c102c0100166881030b0400165a510400c1c0c45c0368500100564500801c4001502c250f5004a009020f00c403000010404020556403d072100c0100c145411085013003052441c1000740512810a840380050742d40c140701503405582420045200d44501010100d1030720656107194111403a65008014018488050140458200c0090006040380039007102038030440d03811180513034018801480021301521030b241c03022000c10b088a621082c03040c120f10641d00000e1151100c0c81d800414032050042c0120300318050100345203140d1800254010096407122070700c0c1280c208078580c0f40444d80d585006c540899842d030300241140c009944900c503454 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 372442158 1250 372440908 372440917
    0xe120f2508031e0a020a17090f0319030608010c080c031312090509090c030705090403051c0c0f0804020102101a1807090e01061b03030e0d032310120201120e03 70
    0x43c9642c415400111007003614000c89851007030380e40c0e601c440414410400d0180c0f201c041e05040040c0541030f2301c8214800204081e102c02803146104030b081d00d082c2c11010f41101d49541005c01e0076410070a05243d21138004c81002d170040040885584d40c1e07569010440004590b03020000d01d0041082400400258803482c0740007645c074120780304025612807504082c0d69407564800c10b60980c0050741c04000030314108486990003402400c20920303040f040c0b10941c0e200d044142001c83c3c1c4030707038440c41502000c4d4000c1003403901d031a076401c00c00303500c0c181900040c1d582c51000c5141c0e9903003511a00540202840011514070091024103800a03101c810380f141a075001e03044034080300040c00340034001529107202c09568103c5029496a4150050303a00340398418001800041e004e150320741500300e0b00000c04010401544e50a50b40c0050784100b02014031010850390050b005240d00090b00f442500c2c0719041c00c0c00212041c038880c10510030001e01c01a100b604400300900105442c00100c1788900c0400320050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 372443408 1250 372442158 372442201
    0xb10030e0705010c021f0c0c1e0602161a090306040b010905090304030807030305062704030f02160504022d030901060f0803090f010912060e120f250803 67
    0x2501c94039158801103466804120001c0d500200c21010104c007982290884481c00c205807810003030a00b0303607440ba03001d8012240d0007212503040c80142501d1800c849103c540c0500824400f0304a52102c003200c6d180d03291014000c07911110b4442150001916407003003103810711840541070300c01e5490241400c00c1492000d01c03610700d820741404001141c101c801310481d0140ca0313200491034248401c0c1d403402c0b0000e200c01464290010022401e00410450300000718920080740c200b41440d9103040d00e001004011601703000e20541d44000c0300d401442045045001c00e440c0140d80068031040d4034120941020000f0040003440308070750b10010003803401c400040d0311454140300244202627941e0504600200140b203091060341040c80441340501e40205200700d8480c052400101040d10364002d14003001e42c00d181280e03c1d80da1900c000b600500d041c490b4420032946c40794620300300103450402040c140319001888540040403024100e8158640101031050390300100c241e501c0785000b0022041103000840c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 372444658 1250 372443408 372443413
    0x618120f07080f0a03140906041d15030105070c03050d020d02030903040f21060506150a0c050c0d03080103030f021f09060b0a0302060405100c08030408041d04050a030e0102010b10030e 81
    0x43c5891440010301e4010296040d0303510540300c2801c0c0c00c441000d4004034080c9600c0b44041100007400101401d600400c00c80480001c8147e085c940505041e19421000c8a400703a4104800c000c5455003148142c0a0300703401d414000c0c0e55442407034000c8002d2056807004038040e440813007071140c400000800f400541d204041c12040c2e058589020f981051001c00154607a10412040c10000808682109400c00700c050714090404051700344400498100da50310a002802c81444901032000800c4075622040341500c01d8902811541c030000d10300041404003034140302e40100400207180c03080003442c088142c800c1002d80003100100d07007030700a007100d020140d403040d0900801140e24030300240190103d035402850b00d40b4203840c01051000b2400c0c026280340a0004061500c0c0c040340c410350003584070b50b210700c0030350b07540d00d0030f000c080081e42c411140c03945016082c15040000064001419401c401c0c1c141c14020100b011190040740036000410049810004806102c100310350550410f002001c0ea10b4103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 372445908 1250 372444658 372444673
    0xb070c020321041a07050d030c0e0a123c061a030d140702041d011506020d030f060b0c0a051c02150615030c030f010b090618120f0708 59
    0x440c4094207030150310748201e11008000401c0300e800c103803448007804640e1400b0b50303017007113225181c02d030400101c0710703071700c804291140c01c554a11507000710380303074407520007100d400f204035080000d07201e01880d50100042c5200d990390348840d4091000010b00c0054410f292060700240d0740c511150305400400d15040300c245082c08061003d11302c9800201044020107001000102144481103c0120605400040c00f150400041c409030301c07140100c0a032282001411002c2003428411a800c440c0e10b6069060341b091000700c1440550f80c045103008800c0e0300f038640480c3c01078421000000a100c2c5501c803e1807070800040c070070103040703010944240085c05001501c010780c000350b0f03080c581c180d030071660303400180c11140002d005d4408c1c9036400c0e50460030142000c10005801c03100050268001d6a050001500c040304210980c001000420b002d011150340c05400c01c1da007200480d04902030862042c1c00034000c104044615221822042c020414180031116241c40050205481e02421300800340c26000e03214 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 372447158 1250 372445908 372445933
    0x71101030c0f020606010e01030f2901051c0b0604051305250509130b0409030203040f0602070311060706111801090f080601060f0c02031e0606010e030d030b0103090b070c0203 77
    0x8244401c2e00c2598014201c280d4510004560760012800c0c154180356960203004058803051140303d0b403454032100000ca01181203028440218190354400341004010400711989540302400303503c0000c0c0d006400300381d0302142000a1810300540c4c00c055000480407010b9802521142c01050203441c0304038040382c4c1d000ca194503080305070303055020b0303c40030400030061440a07061248251150f101080000a658450400040d007500e028040c10750050340085814403890410880f580c0c001c1400340003c4c5131035882d5941d10050043d030f00714428854600818103605100041c0c00000c01280c4c04455555a46c111032960107500ba076140b030040c0050442c01010071110911100c0d401505c410f8401806141e283c803000301e501462411011040102c0302108400584040050010408200c42d0300300651a804030064540f800084c40581005181810541a920007140d400000d1a45240c00700d1040c1c141001039001d00100f0800070204840c007001c000301c0035403050040b407101e44214281c519446001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 372448408 1250 372447158 372447167
    0xa0b040b0915011808010603030203030f0901060807170c0910080d090810050916080703060e0a0201090302060c190c03030206130c050405040f06020c010b0f040608060c0a0c0206071101030c 83
    0x21640505960380030140c41c5074544c0204625141d0550b540140c0074a0b80c5c45901407400d59020b64000c6000d41d00120a0207a400c00d10000c2c0d940c4140e1600c000c1001e98a020031907a904c524610540601c201c030649903210a00007400301c1000b10310301501c00d04090404540010441419100f41c0d43d1600990040f0314003a881000ba110440300240c005080c0b5010707008d04000103200c0a80302e000107201e54071600d03109618002940300142000009030020614504141303094883d000e021000f544c200854890050fa0840c02200c203480c1c05a40031600c505055503068034210b41c40701c04200d0552000d00f003104000c1e150b02c0d80406c1e0381c03181c1c0c2502ca041d01c8241c00c02504002401c1e0013042c10107000b0b410700080c01e041e48100d81c841d00448085250680c0c0b42c5600040385d1017400c200e18a030351079100788036a03400c00e10000d58184100b80e8080054a02d02000386498074000b4003a0000c600c0c0001e8134003c003038800c1c001f4190854008150b41e0755001d041c80c044080008003040c050110f800e0814000455005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 372449658 1250 372448408 372448411
    0x121504020c0a2907080402010315080a12050d090c080c0303090105041505250b09061306020f090418170301050607060914030d0603031803031403041103060a0b040b09 73
    0x34403000786507000c1d4650310f10b8a03198041043c140840000c1c003900d0007000b0b411440d41d00600e119280c803c0c80d4141400010b041d90040485040c52850051007042000c00010b541c106c1690004600c50760401c4081d0202c03418070848055010413414a200301c42880480510642102c1e0b903141200c142500c140305054490190811460100e1421301c01000b9540703400242e2804040c0c2031a1480c545920600611140142d010f05a06c3c45105d40c0f01d00707010001c1d142c48668000070034a00a0149103060301141c0245030039010f0040082e07801040d007040700322002041d115090704c0100b0510484000343c070420582c0703105541c265180d000c4001000c0b682104001204d05803000038181070700d40310340c0b920340c000903007464102100e40d005503a00c2e030900320708144050b080604010b20045011351131414010f01c2c041c0186100d18460b92503101c00c00000ea00880c43c2c04e00c220800d41003d461b80da90341420700c041001c03620002e4060003420100310340c1c44502c0e8800715071035034202c0d010818100342a0500000040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 372450908 1250 372449658 372449677
    0x2070906142d060d0e0d090803030c0c010b030d17070f09270f06061115010509090f03030c09130c020a08030a02040803040305070608070c3512150402 66
    0x9520800038001c0512400c48010010b40c54480008003051000300710a9801000c585060b95038880108035441c03424449181c2c1c009481c07030b1005081e810418011740741d110240000040ca000042c0c60140c2c0c00080d044501419401030a50f04042500107029160010840c4410007040724400000c1c2e0240c080c0b04100f003002d5044d901c01d60864180004130002c0c8503804a0042051020000d0034900e80daa40200c405010b015000451024504000a00f0803078132050841d0361900b021001a000159103042241155800c884c07030b848903140e040f20382c1e0030000210310401d6180400010003c0200510300100071400e825034888103190f030080c0c000000c81c1e10541c43d0710016041646050042110640070315001002841c0042ca820354500365245564410762040b42e0030f4110b030b00d04005850b00300b9007071b50f406441802d03e0620100295902201a00e00744050300c0c8400c1065180c2d2243c0000050300b000701c0021454483e5580c0115800342c440090448948025a8030680c9401c0c582c00c0ca0700a5440b801c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 372452158 1250 372450908 372450919
    0x61027141903030e04110c1006080f0a211e0c03091a0d0c02071509050312040b0406080a020706020301120b10080d0503060d060203070815040908070210020109120207090614 76
    0x10013010400585480516070740545000e010050104a083c05115821201c800001525600c0d0040c0f40f41030921520ba03042240c1c01221034840840e00c6281c0f03401180855400044c214445500190740540a0b0754203e504000803484403031390760340c102a082d41c41038000c1d1505816260f0300c1d000700a0f2040c00196150070315805220100358061103404c003845880060043ea0300d459201d09000c014101c24032042c0700000d00e000410812070070240b0001c00d40380e078046141031415050040001d52072207544501f90821440c01c000608101e107542c142c60856900c241c00755607070f507550f0500521615110030143e8403041c40d4408100f42c8900e00d042e010403550706901502031504d0b20b140a0300e075904018203444c2c0150340710851000040e41440114440d421540b5603c8081c180111000403140c14a03040034011490f00000f0404604410140c8055943c125043c882c81000c0b1202240942134100f4028a01080c1c3c142e20010f1b0f580101d024400da82c07161004010103036448100c0580c011120021070f4120 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 372453408 1250 372452158 372452177
    0xf0a06031e0f0203030a17131e0618080a120b0a09090206040909050d090906080613060b090a050105150702100f0203120c030412030506102714190303 66
    0x35a40700180101d03440c010070b0a03a61511041d00403e065a01c00800703030001482c036400b2000e130b0240c007441043c1c0041400c0326200c1c1c08040c1c5d41d00c0030f03074210f00b0b03112300d28001c0212403c40c1c04201080e005070414440032550148800c2c2540380c03880c01500428000c00c040b840c51954900c0c41e80b014460b8101480000300070001740c0d450099880000d040e401c1050b60000001c100201d568001030085401c114441c02c02000540c04240d001008000707c1d4208420302400d000042058070800608c0c141c004846402e1140042c000b80781c06c400510641c0c140d107400036015820001240e036250302242c12200f0a5441158590440720104401d11070010003d40c44211a6521620107103d040c4d07140d0f01c0ca041d070040341e181c00200f40030b83e81c1d680300864150403107000000c2000100b0828052120454060741018409030070210b0002d41c20284a1520508104102c440c2400071901c005c0c00d810450034082107040226203a04040e840e080002c407406003c3c00c098030110001c21501420314080302c1d099520300703862 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 372454658 1250 372453408 372453443
    0x31e030c060f0e0a0803100f060c06020d0b12061f1a16081206030d050a02061b0d1a0a05030a03120e01061703030702010c020309130b060d0203010b030f0a0603 70
    0x10841c0307044101005540c3c00701c1e818000300c01c004030700c0760b180510a07040e101d140c03040c00c980c003446403a0000d0300900d106010400c80d454000c410101c81c02e42c801c0c0b0161304d03807403c1e003282e074000c0008450380c5a2014041800011542011403444c1c000d503c6040d030b000c056203003502443e829004500c1660400d8010b112044419801d05000d007040d110242c803540f0300c52615441d103e4140c2c00296980e0400c0ba4110180320080ca0f040008407440d40c003d080c2103003030103911075010f501c50400401078002041c404503d0030070000d0031012503c5402d030140c010401d0901510b184007611064400c1580280c450400c045664600080e80c8003185606030780d583c0b40740d0030070701d6100064000d038081d80134990b4944501150449540c8520070700c00041400540e12485d04480003800d484094101c502590001c10801d22035855400d00d00d4640021081c01060f81c03072851020403041e01c690824114441e20100000c108101c0000045000300c40c40e503c401e0094544010302000ca51031480300402580250004203603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 372455908 1250 372454658 372454661
    0x60504030b060301020909041a090c0f01030c0e090108011e1a150c03040b090126130309180912020d0806130f0507110f0712080c070f0f031e030c06 65
    0x2800352020f8005814003c0c101e004c030b0020002503030110303021402c05074004111000714120a43c00600c110042601c20724510100340082c81509442c1e04041d200e41300703191218080c003842480000c0241c0503811f50341e51017010702d000b010aa4181350000640340e00143c01451a8020100240004281c0c055451610002c100850340394001a40001d6814071a1041c444801c4c8040d1000b01305070018596a03074082d00004040c3d4000381c002801a1044461310a10102c0c042c0c481c0d1307880502000204003040c4103040540c0c41c08002e43c05074040d10f16a403110a001c2169410202015102e0142010f000d50b4050301a41c8a90741e1900c0500000c07003000000f0010b00d811041160113440c0e0304070014801545a9880e000c0e100b08680307000c04030b03c5816010180d402d04228030038a580300980a4080380342001104c8c54a6207000002404025010861500c2000284030280042442c02100501241d4480076031a260040d0b00c1306944800c40010403a45002d0b070050408550766240e942d1200038500e5980702c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 372457158 1250 372455908 372455911
    0x3031509010e2a0711090601030e0c010e190909030f0c080901030c0504030503070507030b010816170102090d050d080a06060807141917011205060f0426130f060504030b 74
    0x1400d14180c004404550208540100313800f5000c3d03071000700d01c1408801070001d4040090720326030400d4a0160840c801e030300b001c03c0022115a0900e4800c210005203400103010306ca807601d83c1501c00118032070019440285500c0300c2540c520a843c0c620403000c40007002d60f07904080f12400f81244104005c000742c030b90701c00e40c012030803018682841c1382025126201d007869a00040f0b000c807410340c042c401c01c0c010b018032a60402d005040601c000d24004100c0d0406372103c0e42503120b503112103003070803a0402c5070381820b4040c1c400f0100d004d4081d5001a0107410030030307540c0e034480c003888000c40c1100010642c09444c5020b820190791154650042a455081c800c9440140d40006001c00f10414804600e80c103241c09441003044605179105803440b148003041c2940810b06030301c0b80e0341e00c05c04907a007140012008189a50b0015413541032a03401da07124200b130040b11a00c5407900c0e010201c00204088041581d02c09031060001e00e010941c05240c072075001000601c09030081501048040c04100b002031810000103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 372458408 1250 372457158 372457201
    0x2304060c0207090507030b030c1905011b050a200901050a0605030702070f1401090e0105150d090c030b1609050306060d080409090609050d0201050103080d0203090c03060903031509010e 81
    0x141c86060b61803c010040710419034003800041e807541025040b5107000c0020002c00c5108071031401c1c00448140040807a800c0c0741c818a418070802c603a0030b44004d0500e900301a070068000042d40d0300c140c45031900c82d0b83c032050201d4080b81d80f40644126061070406d031000b03034140c44002d040d145c546402d040c07003581c0c03d400c018041411881640303004520001a030060702d00810580365400c0c1d0a06501c0c0000d05402030b035070040d50551a143c00104a95a500e901290759605510804d59603505080f4004014100030740c0e019201c082c1342d8000000300229220f80612550324002d0f07040c01101d61650445200011f44207041e8194403950210701c25240a40c0300e00765144c8510345840c03600e542e5a4601080e1841e100301924116900e5091000388602407040302c1500ca254030081007598150345c1c6484040c091400d200641907804400140e240c001004140d88504008088400d140344c09101c455403036200b2110809000c40c500c3c88444c15080c04410b80317042e17825542d03042c411070b030320f840391400d43c58014842e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 372459658 1250 372458408 372458413
    0xc06010504020f0c0a0b06030c03060c0a0302032d0f15010e040209040f0e060402271f090f0b0a050d030c1e020a08010c08070e030d0c05010f06182304060c02 69
    0xc440d07444c8400c02203078a0b5140718035601c10342403808500709030400b1385c12000e590207600f08508000c140c1030705100302c54039405070741001038407a180d56424111030000f51b1a0502c9651641c15403034601480250b40d02c4c030803040903001c07108943c0c0d4440c0c0078104441590705140418803d40609289141030b4024000b02403024200141c41420b008030340d0192822500404001d41101050000358101414a81c140301200c403843c0840d07913419805010340e240010004500c00c11030504800131070b0f445085807001014010810300c030444910014000500845070260700c1143c26160020b41414441c1e00fa20301c90343c02d900c901c542c0100715119240b41c4141c071354200445c00140e1805000680c1c40004c0300c0080e04510000040c5040c901002509000c800344c180c3e800c0c041040300d0b6051581e0001144140300175a4500001e6400d06031404034054403d0710310f502c800600704400828141c90f109401c0707240408030708c0240300b103031010311622150f04030b00320401042c0c1c510b450024011600340c0d0010244110390b07104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 372460908 1250 372459658 372459667
    0x30907090c02100f02090a0e0108010f060302031c21050a0605030d020705011101020c07120b070c0f120e0907020c0307142d06070f14070f0611011b0c170c06010504020f 74
    0x51340c7c540c00d50488030865000c030006114181e800d201d09002240001020054203013180c000030354076401c01116081c8021107203800b001880c41180c80c1c903a10300b2000031142800c00c0c0300011001600741110412401441e20400282070721f03000030007032520841c035005880d1079414040111441c0000400d8071060390b40800800001840800541004003241e810581c0c4c1440145401d218a00b0050b01a0702000184807482c0007141514200c21183c2d5404008403840403c500000da40034a421003032681d12140034410001c41680100354401035103400c40940e602c40c2c1e1110741c100000d00210f04c1e03d60300300000742c401c07012401c1201560781c040c01042034048003e150740d100003000c1d60301c042402c49200301d80031044403c00c005045a28403044007000903140f4181032040044a40125100c0c010801c0380a03031007003c01860030340c0711110030100d6000801c0e606071408006000800c0403482107440c45010602140d0780c440880503103030320321010b10141c94141d02e8081040065000b11a000074258020070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 372462158 1250 372460908 372460927
    0x61009230315070503011802040e010b160b010602070f0806090a0609080f0a0323330a0e0708010f1a07020a09020d09140d0801090903180803030907090c02100f02 71
    0xc1043c032824559031455500d40c10300c40081820031072054580b5902c0c0c0180820700980c82118240d90544480290b40c5484000c01710707890b40c002c0c05d0b0b183c01800035607580c1c0010032103942c04200c03041aa01014203003a001074ad076001306a0380d00000c41d6101181e80029a00300001503568001c900e4560103440d1460603e50200040d113203a034080307109000440d64a001039004200c00c0e1011082d03004421040705030903d0240e520503001c40504c41a40303100c44440c094440c02030400440301002c0d0310302400039050075441d0445e1760389030001600d40101080c1c1d100000512000ba8400c2c4d102558044110b140c03404039105401052508125404c0b41d11221548011509842501c058143c0c464041004600101c1a041c10404804400032252031500b20405082c01035401040e06411124101400a044e0b6060300b4200d1786048206861711108121000000f0007100c00405076004541000541c0c00b0030742d075110310200311a071102d405000341e0445822203401500d260f000401c012141e01c805890000d400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 372463408 1250 372462158 372462193
    0x2609070f06110c010f0e0f030313090f0b030105130b0c0d05190c02160e06060c0a050a0b161e18060513050d051c1101050106080610092303 61
    0x180c1107840000e034030807400d100e80c907003c10045030081e8081c2040c2d4100d03d00150700400c200c2800308154001d000012001d04103480402c12034194640da00c1154004e6511050900090143d02e0100420142000d201e840326107010b100d11801241c00784007494035403009a0b281c04030507200814109071407100380000c464800c1203014241c41007201101410502c0110214101190750304500c01086500103840c001b01c81791a00743d004140c1d4858010100160748207000612184107161002d1080d002c0c0012000800c1000640c02c0e89080c811020203021b90b840d5440c648080d80c0f200750300300000e4014022030040a4040381c403207050f5a498035200c076001070054024150009a41e1040c4000381d0b00107020103062400e00188006844111420030581c1c4407a00c2c4c065135002482d11640114400b2004581000c0c000d4800c00c12680149000f44071540e51800041c0a4503011078030300d40181201d5540700d0203203101d1032410003680c80b0040041028002040f048440b90704450f600ca801d032044051265110724407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 372464658 1250 372463408 372463439
    0x9130203120901030e070501051608070215031012020d030309020f18011406030c09012613030806040209011e1704260f043501060312260907 62
    0x140000c0d242d407060301c2000103017181d8842010203015044411300b40001e0381c0c00011034000081881d00c0400404160800b105075204142c00254464010f0204000454248014521070509a400b07c52003d95a2140d49101030707004000030b40c00201d80700814000f80c0203034407001209002804100d07500c1940008260031054240075105145c241c080104400781c948520f0300c205140a8034024110704040252020a00603012028140142c5070841100c84010302c1d104510310a01400c010201e04108401c14483c01011074140d000411280010300d8608180c0226040410181e403070705180c041480860086011900040003041503103026045100c40204006000b14082d846070841314188116030202d0540811150303404541c04d00c00c1000c0541d042c02620708407210001d0040d4414043e00d1007000511928400d014803101100038002f40060552203902600d00c608440d500c4486107a100360345004144070700a103000602c4034210600400303203401c250050a00b104030703450f641e11030045021480340e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 372465908 1250 372464658 372464683
    0x1008010c0804050c0a050a050d260d060f123008060a0501090f090b13020d0f0f110a0c020f090f0709061706010c03090b0408241509130203 61
    0x19603010301c0240042440480c007407513000c6a0080ca443d1070140803c511806501c10307248110041e005030b0040c070207143c50084600002c201040c009524048003400107030840c16154120034a44400070812105a90701d4806403100301c0300745502c0c00803036910481c803843c1215035181504002d2180090368002c1000320900c002c6603840340e0400d8a8854144003101c4241e034841030400c41451001c000840c510b50088080d14201440818100c110f20003041040b030028000072622031000070000302003251980305121a0a00d0002800252000c0325107100341c035050500454201c00c100054600d143c02200a00c20a0344054040301a030f200c0302c00000d80307a0f082101c004c1c96151124040260303080d4030101060191040341010141c0203481c3c402048100b0005041c103040c05803d0b1104c200f494010105c0d040281050744d0882d54032611405502c0e1180c0c110304460000c0c0c81c8420008500c50360160b1400c1c80f40e4044144800380f2211001000700940340a0320407640703c004900740c000903032401c0c080d0220550 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 372467158 1250 372465908 372465917
    0x90609220b03060603191203060807060c051b010527190501020d020f030a030b0112050a06170f0a02100c05030d020a3c11010f0c02150f010504051008010c 68
    0x81d18005060500c50020051407080d085412901c0242e0f03440c8a200780c5180c1c11112140900c0e204c00b0095008040d1900020043d10a20000144640c0c0c49203180c1c21440c800c100303a40d0581d521030100c0701c10b4450f071366140780440c5c018000d842049a5004141459802c1e403181c10303030001c0e00080441c4803807145c0101440308080070403017400296010810105000301c20300c014100e032581a840d06484e8028901c00b10101a11548040d119a2054503001043e008095040019042601145000b0030fa1071250384a040511459156200310201d000c90045420102030041020180e00304a0100d842c9041c400030310100d50064004104100080c040402c03081000580d500144800580b043c0307941c00c00300303003445007032640715940c035408103c56502407440d540840c0348001060800d80302008240500920340d0b01c1e080c1d5070292480d00780c0251010b1071058080e01c0190b40c0400b640307514410f01b101d85403094541e43c0010880360410f40c0c409684030812402100c1c0650711000c0c400d003036410700c034003410015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 372468408 1250 372467158 372467171
    0x50309010207060903080d0b0a0905090d0e0d0203031b0a050d0905010201050604060815041410140702030a050a0c06060b03091e06010f09050a0204030b0c0d0c1409060922 75
    0x1941c04004580240145040c010240c40c07966a40385042d200303803c4040c210715100c150418941d2a0007251a001c4c020880c02801503140510302c1b05e070342e440300000b5100040c1d0450f102d000f6504040228503042c9401601840c0303850240c1c0300b605070a0380600d40008a030303c207482251000c2601400480401c2d1856503a0341021481d00000a094a0002d08128800c41ca448010030011074005a00f04070000000c1d0500060741c1c45003014103161015004155880c02403080d00c1007031b04100d500085016041d0701c050304075925081c01c00c90742da018881c403080c080352003001041c0c80c090254442100140c40344001081d41601c0c2c1f49000b88035001a949005158020b030202d00c505080404001c50181c031840090101d50314001954010106911a00a445980e0b40100d424040c0e030b501242d01842d0000032082403800e040030303042c9550340f101401851161410100700c40e813502c0b440400c501a2400b0614605180502e400c01c002c0360710000352258040c280c1610140c2403403144100c10742c880b0341e045000484 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 372469658 1250 372468408 372468427
    0x80a0c060206090d1205070c0c090903080901050c120c1e0405130902060301050411040803070507030308090a021806011e030f11070807030c081204110a090e070e0907120503 76
    0x10010003078429043d42d0000c42e20580410340c045000c02e100000d44030042040e444600c025584034044880107001110703e80000b090071600c0360008403149100f55190000703681c40302a82030072144195035955411100b0440141540800c4d50815001802c000f0402d00d13080d0030302021040324941b02050341081c240454208aa498a17041d1404c01040601c820701c40003591362300282152105000d154480c40d600c4200f0007000c0180d00a4801030320400c4101c0355928071500703015545510380e2004030002060180042c081c3d400110f004942c0d50342c081d00e03007407414045400650b503880000340198104050f6141c000c00a010b440486d402d220481c1e240000c81c0104040c4080584401d00b00c5144601010083c00001902c07a508607103a03260586414540a1164a8a80d046125881c0713109000c036058400d11041c084481d82c0443d03a9242103c00d40140da9958030400180e880404014080d604841410446003c0860302e0650201520064900301e03901e42100b20b00c1514240f00a031465400480e03104035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 372470908 1250 372469658 372469663
    0xc1a0f0a2a0507030305031f03260c0601030305070809030d230c060606070203071d07030b10170402030f0114061e030613020310110c070b090622080a0c0602 69
    0x74403888086001e81500ea4450a5682d6914800141086070000000d41071815540c10400e140100071181e00541d0713582d06142c0c141d08a00e071540803402040d91082600c644000080f51801000d92002c0e0040368a951010303a6550001c1c034061352440800c1002c4019a5001d00c05101c00300c1c440c3c3c4a03207414080c100320002442e000d81242c004190b2040109490a200004140d80c0c04102101d04680d90350281c4086400c2110550040c150324410140c2c446001c210411058424120741c4d404014541d800c2e000c01903011204483d40c0c001c01c1030141000910300480541540c0180081d003240d044000c0b070000035085031a000c2844920a84080a03c040784c544222000c1003144107460042c40042e080000030344031400507000c452000e03a210003603811502c043c0035120600608820800540c01c80c0301e94041140c0c0301d408107c0aa0144003408500344a007501510402d0310050306481c2040301c081440648040c40400301828002d05080000d032010081148945036882607041d1010245483c80103407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 372472158 1250 372470908 372470957
    0x20307060518060708060d0f0f0b01170f03040302131a0603010b07060e06070801060c03090b12070f0c080318010b03030d1b02010e030a0c060f0c03061707030c1a0f0a 73
    0x4008105c01880700650781c240c44104003d401c02c88480011140d40b030315520003611108005c001c5009000001107068581d4005001a07840f001035400039410700814907142d21503404020f52001442d40c400c0190031013a03000e440f41e1982c900840314684000c00000c3c5054009034003c040c200c0f800120031003000101d00038000301001d00001804641480b4001030401c4a050260701c04121036940844207047c46050080000e2404c01078090340e070304602d0b209003a80741d4100d400c2030100740c1407629803075485d04c588000da0b200d43d007025065056455801034100d0001d100da07210000b645d01c0d030303401e40c11aa0b01440204000b588454001500b11004074000306101504440356081d03926281030701c0030555010088680800b606e1a0155440c2c1045c9000300081c0300c5650340c10300701445c0c6403080b5895601a84181d0540e60412001c3c5800014000010344c0d03040d070340c00010305c1a0520741042150700c0b2882c048480152640f8601e900b01040700c00f0041e055008000c80340000340e10592810020070b145005030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 372473408 1250 372472158 372472171
    0x3011a04030c090c050d0204030b010302090c121b09040f02040905090f0c0f1305040b0105040e0f1002090414040b1023090a0608190b070302030103020d0305090102030706051806 78
    0xd05141c034640703562012550b43d01c50042055101c603a0200b1840c8140300712011804140c104545a98032400e000e00050800d0100306c0c00352158002050940325035409440003c81c000c4001e1f149507540b00f10f071304100b4500c0c65541c0e9015005009e00040c5a80f18024900481c8840740c0040c1c64038a003402840c182e030000350500045410100c3d0030b000c22000801e0418480d00c090384d1440d01c0d61104000b0942e180c1401041c11052803404080c0820480c19507034084c100d503c01c41d4140202c2d5000f404086d00c1e5580c000181c5525809800c001e814984203802070b29135024020000648040d001008590701d2030700321000c8a0303035004001001070754420041aa001b41ca901c0c41c1090000c9070040007610018180300130140304101c0400014800c0c041380e040031018100d2031069640b006264403440c0c10031141c2d02c0341124078080410001c1c0300103201c0d10a5078101e0b50024680348003c0129103081d1210b602c019129411800200030382404901c550044074003500110341d015906d40308082290742000000341c0107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 372474658 1250 372473408 372473459
    0x90c031a06090d0f020112050f07080705090307030b0a0608030a02100e0610090513150c2a0305070804081603050f011a0f0f1002010204060801080a0b0136020301 71
    0x1040c07100e032900b0882201090740890f614260130414001030341d41010050038000224104003c02c50151400d041d600e0040d02c41c3e031581c4041b500e0348a800c2c0e0301400f0b41c0e1314041d0181e00039203040000c280d00300b41c00c5030000e010700c1000a00d65200c000307003811030b84104d4040c005603103c1007a944030714416200345801c181d00200a01510b00b40500400343c001020311840c0c00c05134482000c10032400003558403801d0940c2c80000c4198440348a440240136012800100780420380c1c0c000780399851401d0b003c0521000008061590b007100040e682581e00360030101098030b00d4074081c80086044101000130394950301400712440c5416146142c600d00d44041ca034000355040e4104455030140704504c005c1c40e0b0600104035601c0315480c81038400b183c0011a20706810b43e015043c0c01a500701517406500030b20a0b2910750707842059681c0c88800c510394990840900601600c8040010001d14030204400c52240b0542011140c40300d41217604a240b00c446079449651040d13000004224051a240c3c440382c0c4c002c0d02c040c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 372475908 1250 372474658 372474667
    0x3120301060219050f06070e3607111506270115030b0303130312090b3007020f07090c0e060c07170703120c050a02040e07090c031a06 59
    0x2000351107258007443c1802c080c00801c2018200201440401415002141100e034030f480c1c050390081a0740d5000740c4490094481100c44608040c1615109a001c40449a000010000c65441e001400ca00404400810200110388586404240302074074103e4200803900701c103404c082040020f0000c0070425030110b41d401031400c1c94884048080e480c1124041401110f00c0750543c00c0c10b40180a10881895040c0800103420f0088600c400122054034016503521040b545080300030348141113035000360124040c0034080c00c40d2172840403503668000344160700030a514014482808504c854140d41d9400035030805a40c0009900c000c02c100380060035103034014802c4210307641000d012748090021030f6001ea80c0014807903043d09010030003400140782d11000006103405800313845880d06007600048030002078104070001464801c4e0542c212041e00a409040c00c0d12a56080000030a034040b07500601c2e024980f0300140e040c14a105d04486958952004a501062074079801c1c2d4141041c6030340340c4290020310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 372477158 1250 372475908 372475919
    0x1d07080612010219020709060504020f070602030c13090504030314070c02091e1603050606090a05090a09140d0905060403080f160f03050c150c0319090c0801090203120301 75
    0x64226082030003034860000c00a03400401c107019100b000310074042e000189080003407007a80081c02208961580c50100007042d00e4104002c164401c3c4c0d0185404503105120b554007141782d40d402140c100301c4801e05680740c5100c0341440000ba1909038002c0000b15507400820045c50381602a49c2080392521100319000d107400c0202811102c41d03c0340c0603014220000018a40440010f6950061090650002000d14005110804007580c8880070000a401e003070209841e03081190948003454030080541c82e00d503040030103004003000f00a20515495403108920008a59131061506030221450007400410b40c01c000d01400d80141350307101a0040808104c01c0010031920000d50b03000b00030340c803030b0903548400c40c03c0d4031440740c042000080c1c0700000021403038003010b4000c002810380c1e4a814042e60303040701400c20766038102c04003208c0514140d1401c000040d503011a0605245200411403c005041c806903103c2c02c81035030740342e08041c2c400e83d540d034221740a510302000b64a202c00c2c40c80c40c05078515810032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 372478408 1250 372477158 372477167
    0x6051521040209130305070506101d06010207050d020d02090c0408010c050711010318050d0504031104200a0309080c0d02010b06180405100308070b01050a080106030c1214161d07 78
    0x301305024041c400407855003050b1003038007260a055000f03012501d190425007207080c460082c0c0c3c442d855140c0b110950409440d60440c820610404058000e0642545003000f030102c80a2017a004980c046007040c4070300c00590303c140740c513806865100781e455142e90a180700103003180c40056900342400b03c2804101c00003841c5024005031a2020b1030041120540c001c08100b07a1950858000c12034090f018190010941c004003400c00c89008007001c0500820b10790a010031a02c00383c1100000c6110004443d544814030402041048264034000511080300e0311070380c2158100c029040403d410030016406041e5090080101958040356502d00e00001010001002ca6082002c01c0c007880e00c41c400500248602d0b0b0030301c0000c40e00040d4040d40d884a9103050004034000b4025a071080100c02e44c0480c50140510600c402c1d03d40c0100c4094040e41003010f0241d101c103040c1800c4540d5a05083c0c021824401441940e291441407082821540d0800304116190780c0d05034140000094403030200036100d40e00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 372479658 1250 372478408 372478411
    0x120e07051c0c170f0f0a0b0f040209040f031404090204080d090b27040c02010b010225031b0b0a0c11060f04060f0c140a29160306051521040209 63
    0x2218103480f0036035075042e140e08083e9007510348107040c09140d83d0340c010b561022880940c403e114030720709500c079510703014004c031541c40980700a5000f409010000b0300042c0314651914880e03000e401c1810004061501d9800181d020341c10811174290080390400c5403d05c00c000784000030f8220700b442aa582c1c2000c1140c007050080012580803107028210b8025541c68880c002418140054002d200160028101034044d002070543e190052040a2000c500b204400480c542e45c0c01080d84070308001d03480c648403a07414540882002004544e8000300007090b054070030040a03802d045461b1b1017481061420025618036022441c54000c4a04014a507208224a0304071410703502c05040295400340c9480c000ca40c003908142c002095020211040c2202c044001f801110701340c4100310100741210703a0380b2141700c014108032a0b802001010030104441c0110701031101c1240d412450009801989c81c0e0004807030a41301e09000c03018000008111030b200c40741d61000118442144290002401c0c60307408285580d40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 372480908 1250 372479658 372479669
    0x90c09051e0123060f0f0f03090f0a05060601110f1c0216030c120516090e0c0d1101030c1814010807020f0c0402090609040e0c09100609030210120e07051c0c 69
    0x140007419048400c032080a6418a118540c0310f00e46034682010340058648c42580d9442e25803086c403caa000070f590005034000001d03400340c00b0b8045511081c0c015940c1d403000c40814049402040c07007400da0000200222a00554031000203400fa07000804068101403c000c1042501c44008500f800450031100550003100c14046041151082e281050b03400c00300d070201020400007a0395000245907089401c84107030b00070580d040d9a1100032800400c0b2140301c450a000f40350b030380864500b480540c040e0744441020358280c10a22640002101952040165034000d40c10700090380d0501c029650380304003400d510107583c1c0010104241034440a55807601100c90480c072440d0001240c41d501d4445400359070035810040c10911038406940c0443c0d48507000080524040c0350346000088810a04036034041c03ca9510717442e80d512032802c540034402240d041c004008188404007641c0303200c02586100d0643c0c0704843c0d5003c0d10707d1a0038002007050200d8070400e903080c001942c0c00c465001c142c4142168003283c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 372482014 1106 372480908 372480919
    0x30315010f170105043201030303110306030a060e0c060c010506190f06050c1c030b090703020a051204050708160306110304080a03090c09051e0123 65
    0x400b0300503842e07620004070b0010001420281d2100b44030900c40340c0560b068003251020413441580c51041c04000c8001c000c0104140f41d03151290900b0355103402d1f4040e00e14181400003039601c1c01c3c00306001c5c1226a0311a00d4901500007000803481040d40070f4000740d111412480b000b4002e040c200d801c180078400080c14540d06041da0381805c01900c8210391440d801c14200203049031031fa00b0081500300b0070702c528980c0524807074006440250441c0107a402042000b07000041c00580f0308050895401e242c010300c404510745400c0015240042c1c1c80c2c00c0b2820790f5035110f00b0b10500c2c06010740e001140900466821000303882e821004442035038052a81489198018400da600310b100032903000c3c081d102c0910200704042e109030482403105001d41e4800b0b50243e00c901d44002203c0c0305803192614066481401101c1482080b0b405005100b01426142a84000340c21842126010380d0500c0c0f00300f = true := by decide +kernel

theorem cover : BRFrame.Cov 372302158 372482014 := by
  have h0 := BRFrame.cov_init 372302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 372302158 ≤ n) (h2 : n < 372482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
