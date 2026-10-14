-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0536
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:19:00.512441+00:00
-- url     : https://prove2.me/submissions/d8e43918-ca3e-4efd-9291-b29542bd0666

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 96223021 ≤ n < 96402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 96224271 1250 96223021 96223031
    0x7030e010e0607050303071d030f0a14030f040603090305040e0f060a050306060f0d110603070c0615050d03030b040b0a09060302030106050907021903050c030a0509120c0112021e0a0305060310 84
    0x346401d6201d1100800240412024041c288c03d01000f10701024485e150140c2103d000c4030305d200c141503a03907a03c500d047e164000b0001d2110070030003000040303660800d840c203c407609180c6404402d40c0500f94115048003400018440410000f0884c0790051040c0d10840079001c3c00c0c107203c001c0c0031200010b0340045020f82c02020420000351140040a0001c0384161070000f0608011b00380210058190304e03405034044400814024034030f1f072040205c1d49c41da001e40d104021000307030100b110000b01e55a104890b001200001040e020900a50183d000c6542c00f90010500e46c1034500090901c1402d500440c4042c0da44e942c0500960400740700b0b000240c241a6000c0205040c04040651b990103c03452031078a260340410000300300751084040d41c201c1c000c400201d90322404c4040015100b074105040309070140c80b1114000f0000790f8009004039407108183c4400c113040000b2002e000280d401405000315021043c40352540d45464070340140b40900c00e941e400240390904504250a040040303110b000c03518181 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 96225521 1250 96224271 96224273
    0xb10051c0506060d0c0918021008040b010302040f0b03010e070614040b0405040509150c070201081612020c070f0b03070f08010e0720010c0201050907120308010e060d0807030e010e0607 81
    0x6442c6401c6401103401d045084503a150003181c481240d089845154280003440400110300b1518017016803003140c0e500040e02c0c0c01c16007100c4c0c440d0226030141000ba8860010009810300b90701031500140c000e1070102d444410350012030b003945c2e00600c01c00c2c0d2507480004100b09090348910b442c5405088600c01901d0079280090684050140740a4944201d6542000c101c0c850360410420034a0014520601071600d8242c000903e9a0000c440503400300309a040056203004000e510307510f9400050702d52000340044031460314000c1d0403040707118bd010b1188000c04a01030590181980080c603281044994914118000800c40d48001407003100780301980005002c02070b4200a031036408429440c0501603405051400002c109844000381a9546481d9006641980c1908150300c282844c0045540c1596144441e43c091071482c80041c001a01c0d502c01444041d010240a90b003254006240d6120207019403501c51350741c0d214075021000304521641701c0c0202d58015101440903c0211841c900341011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 96226771 1250 96225521 96225523
    0x6081006080114030304150815010906050a0c0309051201050103061b050d091703010305030d1d1b0a0f0b04060905240d0f020310090b040903140a0207030b10051c05 72
    0x600408100800f903d012404640741001542c000307141158102d065540d00f120080d100082c1a2442038890b040d41018100c154002c2100104aa40c265101464440500700890b041c40790300724100e08008100d0703070005d00c5a83c0c1681c9554026040700001595504d10310f051003c44420420102600903250454040142c00000f6901c0314840c5231000315180482340350a141030400e003046c080a0050200020090103000006001c036120407500804c04040003c0c144c103440241c15041940542c000c442d645480c20040414400c40c00c40a4480502035032512100d040001003030300b08410a00000c41d08102103544500120300074841910403611a045140c006000c06035504420740c0d4194000402003140b6400398030000c414101d4481c01c54403810f0281c000c04540a142c400d42c00a6400c202d4030b9009494944182c41040780d00d0f8442d00c034507200c00105540c0c0f84c1c0001e4240c0003503004804000000c9683d0110803403107a00c45480840d1030500300810013110901604021350a2541c04180d400004c030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 96228021 1250 96226771 96226787
    0x31507120b1203040e0414031903050601020714040c0909050a0c080106110a080c03070f060b030721030c0f0506040b01030b0906070f0503090c03010204080a0303180b0105060a030209120706081006 86
    0x144484038100503034881c1407d0400030310681c0750703100c0f034800000d042d00401c4030301c070380d1161146180e036060220341c440d82c0049903500000d002d030040c5001b01e40002c12071450300c0c1c1c2c0203062400c0103007001190785658031950b408885040710510199074980509954055000c29064090000ea00f81034101c00030440c0001c0e900d08840c44010621900050021a8a4010001e0b1440f46500400741044203061b880c000018101138058680a03106900001ca108041020f01c4040b946143d1801d100c0c0041940301101c2e414480102528504d11030b519074804a1801d000c02ca1166000313001f00341007945149002868000010420700c5550090000e014034642e110300c408498883c240313001900d03500d9002c2450b04100c07015100075410740c1b0020740002e90761404904d030104039000742c804000051017503c58003000c2c4054400100700c098402c0050085160100282030110403901e80181882c0060300455081e2124020140555004d0442040080e501030b495682c0500300346107080a40c2d290102c081c000b99 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 96229271 1250 96228021 96228029
    0x307020d0305040c03080307110f07030302030f131a0304050c0f0105120402121b0a05010201020f03070f030906050f04020f01051801080405032506060f03031d031507120b120304 78
    0xda00c650100f000d001d030820086000e10b4120009aa49042100c0058651001580c00c030600e402048101007001102160041c12290541c01442c501004c2000075034183d4032824a080f8842c00c0a82c0c003080000308140503070203208801d01413550b24102805c07c2854600c030701c10507034800d580d012460007a90b43d00c00c042d20807001060075044480d03120342c40003902152002040845901c900005460615503400100c6000b25042e90416415500d48004900340e10504040c091803078000c10114884600c10000c16100c09803900d400581d104059039504180c4101395548603500490720305105c25850040016210840f09082003483c0c030744040f2100d40720541c12290300e070604c0200700000382072150030300460300302c0c1518400d00e50b40340100c14004800705d040490252402c91404101240355214040e03240203a9405841e060b440c010301040c212100b590411015415018040d1660074800c002c5840d64003502c210b072900000c04600b4075040e002c8401d540111407160203901d0611280c4000481102c0036a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 96230521 1250 96229271 96229277
    0x110c030a05070512160f020409080d020909010e010e0103031407080a0c0209060901030506180f010c200102071a04051507050406030e010b06070803070c1b0512010b0a090b12030f04030204060b0307020d 88
    0x12506d1740002001800c44010288c0308040014035203035101602d5000306842c4600f203132041c1150747ca5003145103041d4000d002e01c142d0031116500600101e4020401000c080303000c81c0c070152418049907288802500249000c0000c6601c200401c0c0461809520682c2d10200655840040b9031440c0c40b02c0b5a110800f401061070b024034450b5103182c0900504c4416030004030403001740960034031401d000f0000c2e4030a041c0d005001d20922390311080c404042c003c4500342030300018080c000c4109182c002008880c0a481154075108205614043c2e64610390003e209194988919031113524048014066800384005c1c009564944000c035081d42c1d40701e40c281c4030016042101c3d40e48035500d6450a03a92607914480c054210b81c614044500442c00d146944003e0302e0040d0741d00702c22000d4845104d402e844800c401a540f040c0b81031001c0c00a03808035813100c507180c0401408102d910598594803810b691248041c105072401c0000c050082d0b0510b0b0255034002e104403c83d2030302c0c520340b120340203441d541440300305020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 96231771 1250 96230521 96230543
    0x90a0c03080c07030611030a060501110606090709050409050601090605030312130f050a0501061a0a0c03111f050402040e06060913050c100507050106060819110c030a0507051216 78
    0xb9402c104482400b65901c040200840344425001000d540c004032290140369040c000c0100e02c95100320550484280b8040040100d0327200d80c410044031940040c129070800c03428400c000360076602e902403521010b01450151071a035061188101c160f95a40d08218065070080040226908011302c0d000e030701c8048034018241c440418030307105000c160450301c00391051144454440c240501036101c00100c1d050806092101c0c07000340c041102c903000f20000c0c040440d0f4408002804a03004038259540e100400b01036a101c44c4150645107031468203401005642030f40c40c8100011400c19218a182420707554006081d246000380005e042d424000342402502c0c100b0110700020030200300000d150003880180140c5c041c2400d80710003041034200134000d1300c003582000d0b00000c6031405042824054034008140c800b0780c4000701502e4000c0d04803103000c4c030441d200070000240c12141c240042d20008100366151503039000f80d070070131920740012411800781c1030340700b001034514101d41c1250701003031141c1c070465043c3c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 96233021 1250 96231771 96231787
    0x1308070b07030e0a0f0308040906050a030b0118090507060e1309081605070905040629011202090d061d0f01050603060601030c02010b09010b1c0209060304082b0c0305090a0c0308 78
    0x2000130707170b0241d059172810388000b004101c3d01401500c16100000c2c0b00300320782c40e501c40c01c0040c9000c49110107001a4808001400180621f24080110b03805100d0041a810b6075aa81c05203021000e0340540c0c0092103030010000549810760713006402c4002c80b5014000c1c8441500e0300c40c90b030700c00c84508840960300c0f541203008105090014000a0034080020030041c940f50810a0142607084281c0d001400c0c4040f4800614150303035100c1c1000709060f5280581070410f004054001d6100c4400a035000d010000061700141c4c013401405602c40c0300c81024500c03e9216450030385486501a0b40c6a0140d0404040080071b48000580300d80c40740e002d180c04a8284550017080c0d0040a03903004080d000072103075001151100341440140a2601c59005601e2166440c12400041380124001d40754000740802c01704000c00c0900d03001e841126000c00c484c0d81e00f00c040c2c1301c0841c43c010354004c40c0d211150b1109192100960944180b56000b5990380c0034060440e4555076504010459010040c54404c0220f0180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 96234271 1250 96233021 96233029
    0xc0507080a0305180315010506180d0804051801031a040f050d11070603020705060a02031e0a0e011415310204030210020a080d020307031b03021308070b07030e 70
    0x20009203000015554041410308006103144e102d4000c000030b403002400400180e041c00100130b03200c103105000140269081500304502640403000c3d4012400301820b9103041680c640c1c140c00c030b409203d4a1007a50f22403802c0c043c0448858899800489500c080340100049a105042109049100a2120b01c95590303460455090356007202c0c043d0940c441c0e140141106600a207070340c09446400c1c2c00700d6940c60303500c0b0411401d078802c0c02d00041854003e40302040e0010900e80245400400386040070301a0715014051840726401181c020032115250003095658020070b1207403500f001034030b0f01d000300c4500d0000040c0321400b598840003401681c000701258804100d1880b030003002d0300100c904c448085100ca40306c1000c0d40090105920407043c05800700240c5000243d940c0c140d9601c8003555040003401400b5000039000240010309040d1591107034074005201034154082c11400e61001620381268410300003590780c95420900d11540b00500502c004441c3c10f080d42c0900d581841c1c03442101520f0310110b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 96235521 1250 96234271 96234283
    0xd0804030c080706090b0c1e07020609032a04180b181603060f021603052104060e010b09092a090403030e0f01020f120702010b090412090e06030d0c05 66
    0x40d000c1e0b2004144001046445e40020305c2c103030f01510b1400344a807503502c2640000c1c0f2588800c84000c40c008224011004901800341070544d00042195003000e40000c0468180607136000c080c21f0320788580c0108000368541d20052121840d090301d0400c036151041000c200b5560404401400140d01c9000161440c1c1c0313401b00f03c02100400700240d4508800c2c40d00804004040da00085404506107070f070801480ca014400d0760842002020f401c00310203e035880c00d98141d0301542c0c0200390300724400710b8072000005103154070303020703620941c0002610300e41e511b050f6003100c0352003510074070030642d4e0700a22144040002d802800054840128030340150380a180911580740786440036004040d0000f000103068041e4040c1404980040a442402c04d0310b0440c9800c030b00c541c641502288a003406498a14001502019805980c1c0e000000d01250003900280c0c203c81c040760101c449648144400da085030780205050300422400c64044160f0900600003a01d901c0c46280e0101004004403120060080c20458 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 96236771 1250 96235521 96235523
    0x2090703020906070c060e03100b0a060c030c1406060f090603070b1602030111120f010f1520100606050702060405060d02070f2901030803190e010c091401080105030d0804030c 77
    0xc410f00750b030b42d5006c054100300090384190b10a0084510001c000080d900074602c030307210b004011716812070800c0e6041d034940551150031303810020141405800100a4415114107a41040c0200094500201004207404d06180e18a008081902c28440e41b0748002511505031030755801c82da6115230990240303440e0482c0d000c01c040c0d41582800c1042c44000c82a000414400080203500e83e0a599495032002c140902032140c0086e07100c8204040140c0550400c0403004903100740b03840100407000d8003400100100c042242c4a0a40149029440503169441601d00828003070030194103000c190740025682d4016845010300560000451f03052800c40ca038126400c81d035014201c182c02c2c0790b06041c500240ca0b0120398040300c43d82c680103004400310b01c80c00c04c1030490354407410b241d00d160340708a200004100c406840703181141d241c4010440c081e600b8050103950b5403442e0341d0b4031542c1e8609180d03040c0c070180a9803200d0601118100512690b01c020a140038545070303c0c203083c2c000d0f844030714041b07441280000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 96238021 1250 96236771 96236783
    0x1110109030305180109201c1203050709061d060c0102120901050a0504083a020c12030408041505070c030b090d08090c01030b03070e010906050a060201090209070302090607 76
    0x2216001c15030558041c50054445050107880101114055401c0b203191007005001c012180000c070f1610311030a800c00390310310780c050901490220921424181c4103040c207001c0b034000f1200c40c080c20f5003a5161045c2c650101c00f0785440d031a01490207001410f124000050b07411002802154011503444480448220207002c2d0002c55480c5000e1504070321900d800c0d11042525420400821001e6940f0f000e45402603030422105440e01c02c12940c40540340a00b90125050301203a00508c410309600420641a210b03c80340000d07a0724102c44d010b2600f0700c444c010001c00101c0050050001040340101910300340c6400c400c95a400c844006411746d082d0295007070090a01c0125140441000310000c1c40c60302034442201140e07004521503c040c0c5200c18112038034060769003c0c400d0028590b10a4010800407030b40030f4140d90760191a41e91801d100c0b07409800c80d00000c0e86400f8200203905010241200070000c40c80200f216010039800105020301c09071180d410150003040002d40c90382c84804a51846038080c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 96239271 1250 96238021 96238031
    0x60c080f0406020c03100605060d0506040e06040605160311071b0e0c04090b0d11040506040f050406051503150c0913090f060f0b0901030f05030f03040507140d03021506011101 77
    0x50009507154500c138181c60080c001c101000c011140346010b40c0b0240c2e42c00401c1c131414580388022880080030018845540180c8601911503036090902c8000d010720700555020411740b03041c5144441c03800c038030078480040614000401500240308000d6802040e440070358420243d1400a4100304480d0303c3c1c100d814150728810900071581c0d01c0c2401403044a10b650340c1440400c80c550200015032991860190118084581241e4289003550013550b01901c000c00000307a10345105120011100d0807203040b200c0710b0343c5000b400f8242900e0403da08000d0030890007400720150224440c07000140140c802c040c0000c0108440000d81c1d501e50502c00d010350840350410114106013004c00704242440d5041e658686050056081c0d01d03d0f50184200010024110b03a19131703461980c0304050008070910a80b0203020520400c10181500001140140d0069008007070407400c011081c0b02000368100070300d108108818400000940104500c5902094a1000c080381d5946800584080d070342004d00b62041e500e09 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 96240521 1250 96239271 96239279
    0x30f0912160b130f080a141c030e100e0d0e030c0907030221090703020d080f120702060a090b1303090305030a020f010b04330302060304060c0e090709060c080f04 71
    0x100c003803c01080000201d5000c0307542c0d6002007030265030900444070103400172920706001c0b4800507646010801c0450440d488109102140640c51983e445c403200001e80700d46000b04041c50130016180801000e0760104810303408044940d0f504e01c0421100e0702802200300c200040d070750381030140c0d1110f131102174414040391412210040007540b10819200101c00c240ca24402c682c038081d554544140c98000c024140a421902048034800e1092401c640c40c903c01c0200000900505000e400d10307400b1900c05011906000d00b0107070410400405e0030b90a0740c03400e800780c404144900203194000b64814a421407070290307414201c800c0349980d0006403461000080001490382d000501c40c504c02e1101c0c00801800c074003802000305803460560300340440c1c041c41c110250b50300e906d00c1c41d0b80d201405110008820340d030f4960100d0703480d070403c4038103450042c2e50720a00c041d02c2d9042a21500000822074455030b41d441c04860180c411031a078040c4108000d0300b850900d0401200c901114001e0700c00c20b07010741c4c075a999 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 96241771 1250 96240521 96240539
    0x109170a021305090f0a0822050307031103120a120911030a0b070212070c060e0120010203190b09010b0c0a05010e010615090e13022106070809030f091216 68
    0x7054840d2625442a0600360100180101e464100c0550100c00c891070000c8103901d23049020303034100e0450000d0303604d40b0b40081c041d0307420030406004501c1400c10480c903500600406040c920600c8034602c2040c010401d4034581d50b44042c0130758501c0042d40b0000b8212100381454100c0080e400d05164052089540c40c9e014400200d80d480d01c1100c455080b6500c00b15040c0c4005d809010b075070002411000550020301c850f0340104201e2406050624082009449010b51705000c10000041c85803a130f50300205002d091045001c100180c00c1d800d5100b07010064003071010925002051048100841011840d482e584c0c6062118050007504140240039915410b070609009001d18841d10300b0401a0714415441580a40b04640031544041c132081403903a00d1034039010148040c443c0481e0b1100a01002c103502d0020140c40805580110005010300d00e001c180180c00c05102030080e107140c0c2e000303200f001d40a028800442d00e40000036150640c1000c0004252072400301d002c512100c0c2502c0a4a01082c0d030a5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 96243021 1250 96241771 96241781
    0x304030909110c0c060a020a0203070608040506010e09030703120b04060b0306041b0207090e0c06030a022d04060e13020a02060702100b0d08160503040807050f0a050109170a0213 78
    0x1040e04410060300394107048840e494481c4210341c011a4004090184403440d0170405000a0909401540c0b4980aa5800682003001030b0300440041010306050009206041002c103002d40611032980000741003031944030382c0e0790082207401410040b00102ea0300ca6010150807001c0c0002004d0010f005807500c601014506420440f801c600980c5446049012104841c01182c400303c85500588122401c0c10968005402100000a594800c04203d0442e0b921010000d42c41904d040200585500162449845c03407c4070500c1d80340041135403060800d9098420003180c00311601418041400c0d1070f40d00c0410360001c100030300e8480c07640c40807640d0540550042486880703005540d085c2c0f0200c039040322421341112440143c068010282c5060b1000085446004040c00076001d110900a003503c1c0c0c0d2a5031455200f90044005500041702c03c00003400c0c100c3c10901e080400300d580d4028241000d000a00340c1d01c01d8441c09a0030307509480710854a0106220301d2180d2034003c1c140c2d150b54003e03e01544080d01e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 96244271 1250 96243021 96243029
    0x81804050721050f06090a140a050f070c0b0a020a02010603050304060905090f090604080a030209030106060e0a06170a05060112020c03041d04030806221a04060611030d0c1403040309 80
    0x14002c2a89450b1046481c850503124080401c030003001500ca460600034803c9009212180c059518004248440b4003076400520407a01c070310000c1810310b001980c203003610740b0280004050140c3d0f6038500d800111507201840d40300d000c5140060325082c2d40380c0c1c00c030301500075a8409411030200140100e00a90701170380031016039205845070181078445003084103545604940500c815000360000c2000126040014030744181701c4e1401504101e031034000039086800c55889000469140341c820381050414020700802020182006141d004034540f504104501c01485613080541d0382c0c000480e40c2e8003c150703144003055010000c40d211504020400c2c1c0c0e903805030044e5100140406042c00318001040c0c4068811540365942500e02d031122401d21119400f03c030004070010f55120f0044511000c3c51107000da42c09408210304420303190f0174060104403285a04100d00b0001003002d0741e800e4000c000102c0c3c0302d080402c8e0001803c02650300046440035000c00d24078000c42030000502040c590301c00e10150a035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 96245521 1250 96244271 96244307
    0x8061513091104060504030609020103140901060e090c0a0e070c080409050601081005030a03080411031209040c0c02013c0201020d0e0c0a090222080607020c0406030309030818040507 80
    0x80c40440b49000c5080c007aa00c5a100010b50030081480011582e401403001a44103060210f106407400381500c01e010000c45032003a0700e0b9507034102003011a1000000a030400d101e44041c20030102404049035107140540100b800c090304074004030302840c0c40b801074070b0b402c01d410200e15510385072502000e4000d4070301665824001120714021a00c0400405040000c030348000b40108920303a00c50b6001e554440c0300410175a904070617600f224095440c140407803040e40e1a44019166200c2e00700c0e0400c8101e42d4003604203810014019840ea0050342c201000d911200c0850803451100819000d03a1070600104909000300311030f03101e07141c010041c0c0540240900c3c4180d861305000c1560701240c40c1c2d90758111104803980c003d800b0b02041045100170b80c000e0130300098201001d8000f500c0b440203600c0038401c5521820595202c3c8080081d8140c1c18420021030030021501408858695100140400740c9404040d2454074001101f0720503004038040c0104440002c2c1084c0320328a015100684422619100312200e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 96246771 1250 96245521 96245531
    0x711070602070f031b030c080d031103060f060313051902030d11031602011205041b0803040608060609030a050106060503100807050901170a08030a0501050f03010b0904030806151309 80
    0x1850300204a03001034503280d128140d2120310350f45546002074565110300328491a01807020012540c0804200301410403800100f62640c3c10312001011605502f0034038201040520078805141c0d00c0e89080444100115a1180c51707441c1d000e400411a006000001c1c1541300302e403402244204910381448070680200c059032420822644150303000d00c01c030140d42c2c05c190410840050051040d18020a2440c010315003000104d0030810310108581d42a07a09940b0341501d0340c114121007000e16142c1c1c010f490000c01450401b0b00d058005880c600d03000c2c0646204200100d1014015102000b83c120340d90b400000900c40c2c903035913a001408650054600b030114080c100c90200e044200042c0280071190080d001102c2c0ea8a80001824407008000c20507240d8082c2c070b44c001001c241942c000d1030080b000c480c000a80b079450301040155100e844039a45000341d0515040300d0072039840940e015802a090304203005140d0b110000070301522100840d022842002090108950a03940a01025a1008841000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 96248021 1250 96246771 96246779
    0xc0c0a0501020607020d030c020a171206010c0c050607061b0903140f06040b06031c02061906150c050102040503030708130e0903040303030e01060b180108310218071107 74
    0x10300d80310104c0300030740568080307100074141910a038030417040440644180e419440003030703441e0080314118005565002030003142483e01e01044c0c07212550001024201a200da0b04c4964034000f0440480c0704061240e4000724682c01408a9900b00c4122908403d2504d642410400c41c090506003c5000649101030030001c40000c0300400140c062800741c6140c02811103a54a58131519119002400a5058014080b9542030040d030400c1c801c070000559006080945005220403440b10704a10324601c2d268104034041042c1c0081c002010740c00012458606044d40c1c4500301180a4490f5501981e0103110015010007844120005490000c032003104d8411070b15a90f1001c50003201095440300e40da60010041000064000c0d440107040014100011402e01da41c0c0f1001c60058000c6805c0048611001c24160415031340040803941c81000a880011180a450f0000c0d58138035070081c020a07891102d8100301c5c00c0d0355417410300c100c00041c12201030b0030500d4901001840400c8505084074030303100f4418041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 96249271 1250 96248021 96248023
    0x904020705150718050906040b040504050d140a0504090b0f120c0f060903030f0a0215160809060121030201020d0906020403050607091202010c060902090c0c1501180509120c0c0a050102 81
    0x2181d1243c0407055007000311705050401c03003641c40181c49681e200b5624001503003e6251409400c0c070039405400076100d1017040c000701030265512441464240c0300100200c24081d504241a502034803588000050080c00e0700d400301d00c80c0000d040b6043e50001800300e0300700076100300080710080d44805a80300c00e0340508070402d01c143c40c041c80e50f07000d5241e001400507403807160a00024010502840c030490380e1a6103048003215080c0e400fa140c085d14000010540c41005130010010342e001012100106081e40c54000070562054020501100d0110100c00b400c0a1600c00d40580d1a0029186000c010506051a1900095009102c1120a8002c480010300c00e1401002100d00712440174140a54044e040d44c011180c00b40c0900046401903600e8642c100540c5440c0e1a0602c580311107000c281d5181c2c0d0041c007141c82c298480c0b00c18890504184010b00024000f804080300700611a0004552510346045107814081d1040740c004a400e4085020b007014800007903c980320890946201070300c0c5481d10012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 96250521 1250 96249271 96249287
    0x6110c12011d01150b03130f0305120c03100b03060604030b0f040c0e0106090e18030c100513020d0f0606050d150f0c0c0f02030708010c051b06011212030209040207051507 75
    0x200088213542841000480e940500840c1d00441e80c84000e0f01d010080d0340c40300403203009184142d000030740124804d115404010022038010451703003411819441c01104c0344d03003207070818002c0c01c3c114040840810040e44505007601d002d1a400f0800034054507005a00070300b02c41c41200d041c0c80f101c004800020b504061150114140e0b2103941e100d114160501003251111000601402e00072100c107050115032110a00141028450650140c444009540c0303415060701c81c090003030001c1e81807081555006980300f00e0200201503128050449010490a003c030003840680c1c821a008000c02054000b0402100c042d0f01c920403034101304120410002000100711030303c2c129840701145652845c14085040e04040b1304035640300074121400d5684034201d00d829560201c0c1306074007041010814100c83c0e0381a003445520b00d2211030042030150b00d0b0a0b0a54a211101c8601420034401526a070800601c660115803015201800c150341c3c3e000c25140140c0c3d1002c544065403c0b5400c0c3e0340c08a42035078428140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 96251771 1250 96250521 96250541
    0x203130e040c0b030c1806040f08011a0406060e0906030715020706030f0615051305150702040e0a03020a031112040f030b06041a04021602040501091b0c020303030106110c12011d01 79
    0x5e907042c0200d104036151aa0b110100341503000009020010306501486aa0130150031140c0011864080004940c0001d86400314101e1055003020800c0c414103a000740400d400384003c40780108a0303210503010906104840e046880c03c00c0451040120342d940010303245084030001ea0f020891200d4120000c422a600ba029403038608000e9105000d10713900c00d4003e020318504500900041d81c0e510310002e61403101c2196003082203400480e031740084d45803a00c00c0048804600700504442200740d034009480304204040103041c00048d030050b21021a00f004081e141d61076002d042c40e910303134403503000c0c90402c802c0e48000c9400940c86030005039035040c18041c1001c1d100e800402691305455100070000a50803a0501405401400311094096500c0d4080d40d40200351141e4006a80d00e2088100d452981d140d000d18001d02121300c0d0354400588002080340d0440c3e03050324040124103070000007a42400c400092040d40700043d00500d211904040d40108182050450080d4011064902580c03d03621942c1c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 96253021 1250 96251771 96251791
    0x20a0b0c070302070509040312050a051b12220b0103060902040b1807140c0304090902010206070c0309120804090203100f05030d0c1101050f0409090b0609090a020d030203130e040c0b03 81
    0x4405c00050030824000d54010340719080007a03d803c6402d016500f25582101c01c83c800580350300a00200065001e510281004046905032900e68640500c0c640c0e940c0c042c2401040c0c940c0541070700708030740c01207502e003603195801070791302116585d01e041a40140032031510591042d45490b01103990fa2800c2c040d10340c402c0402001c076009554505c4801c3d00c0b04076103071032881c14001040000c410206424002032028001c25030f000925180389000091510000400c810300344008048040c1c003280d04076003090210360061203460702540983c80e1552641c0100d0707201d041068004410b200d000d0808a188106031040b031100002c50b159110205603036032044128610100c0c2c903001100c1c01042012014a110207018100103240005020301c1c4800c5500c5603000002081d6240b0b200c004008852703010320b4111004403440040c60404012044e00c540813154000d208a000c110540c0405009100359030039804140284407400342c0e510101820418122001c40d1140e004000c00300f07a0382c100400b5680a12040b02d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 96254271 1250 96253021 96253033
    0x60402010f031d1c020304080703112d09090102041d060a0302030a030f09080a171606060b090108130b041b090906020405040b01021f0207020f060a020a0b0c070302 72
    0x140054804241c109001d60800d511050800490b401030b140303c0303454a50800040c00d20782c201031400301d8590f4081c10ba01c0c1c215001004204051280000d104094980010f000710180ea0303030500103880854113000306082010b03c1f0b01078000614908480020b0322105a8040c0099039070110118200c0c425409000006201c1c0c1d100d081c0d500b030307600d201d0561100b000350150010540765000a460044061021400a911081018900360b030051100004259034401005454810b603074000c81c06010320034a240340d0001241d400660305400d1800d88426800c5542089101e032103030107102c80d56001001050119411101285031141410b0b860301240f0b4103c0481c800c540c0755a541d00300c4803001d11480c60021132041a020038510000d120305040c281c41050010b070f556182605202c207a0300858681e50554010b074002c040403c0d15200d480c0700707500c006080140d44071860702c00107110042d00580d01da08001c0114a031000c40b40c000a80e10f05150140c80c4291407036850042d680c089210b1018002c005030801c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 96255521 1250 96254271 96254273
    0x12061a190801030b0a091b0e0601180303050f0f190201060807050306040809090c0403061802091302010804060203101e081204080309090a020c03070609020f01030e060f1314010902040506060901020604 88
    0xd94041071b0b00710302c00c0851441d0034001c002c000c80c1410640e0043c491808440b4188401580c1243d100340700441c0d08882c4110b1980346440140241c000c0840e60041c0c05c0c0006100c1480880074070840702c501404061889503a40d540d440203000b00128080c41384584155480860300e841d000407940d04c1030740d01044551402010300705102c850400548004e07860700081c00040001940350180d20300700c0310110511840100c0600412490355030140c102c5c0c1b981c0c6801140c100260f68414500340d40140c10410140c3d5944400030104112010360344103040703500140d10000040d5949035203070000c4862480451f2543c0441081005583c82903110714802540100300982080c14214015544448082c2c0c006003080071160301d5604691008800f220380c181e507035441408528126070000d224080a29042003400e403c145c0d5969509409032105003d24524400103600007403d1903003034585c96203d00c2000d070150051040d140a07203000341080344124144000030b2001e050400641e242003005034010203280e221 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 96256771 1250 96255521 96255541
    0x903060a02070c0e07031401060305010509150a081905071a0418020f0301030f03020d030b010c23070e0a0513020f0108040303090203061603140105030d12061a190801030b 75
    0x842c004440340e84030300400144220424800030701c1103000e910701050300303c100c820428403840160048801d051404006224031b450386942c0300d52101c0e80740310400324003981d40700003827004d141076001000e0392142c00ea41d4007074084003a0542c1320032417241c0102c0d028540c9420030791505088071359107030340c1504007030000b080340303070400001c0041c64203202200524156075045180450342c4260000d40348100109141410180c2c104900d104041040c0360400c00540c001d00020300140c0388403030241003a03040500c003603c51003031400340a168200c0a0308135410750317640740180b1000354000c64201845510b010001040c1c0066148014402079008140c1c914138118000195000c810140007641003603a0740c041440180c404011303290013164004039005244d4250040201603036881e005030282042c1d110010001d81d280011016107190250400b01e40604110a40c0ca005110781e0b485030f1042c200f411100c02130010208001d0000c141d0001c2030009800038840c040c2d40f441800c0c07100030040000c1034006200044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 96258021 1250 96256771 96256777
    0x40e03120a0e0d0518010806011b05010f14070f08010303020a080a1e05220803030c09060c030409060f0611060c030c070f0b06180103052509051e010b0903060a02 71
    0x70306408001100300e04844958680050340b80a180442c43c0059240e454450794804c0541c0d20b0024601441146000c0b80001c05081d9030720b0b614900d80710405406000c005003900a901c40c41c18842040201b06500e090980c2550f205454220114407042d030004020313071107408002d050300d170540c0081140540d513540700c081c180e020b020b9040421110031003c0e540081c40c10800711041c8019580d80e500c80e00c0c00241c039055003030312034440b00c940c40d5010030800c10514080103507503000403040003a41d121103079100400c1e540e110703035020804a40400200407910607100da01150a1b03908004200b094aa200c08040c7c0f0002c21224501403503a00040014940421346001583d00c050410074140c01d15070140e80f4520041400038045898000d00741c20030489040c8414000042c0c40140260301042d45151122601c49070444d8840c118145445401c0414058050030346000b48044c0008010a180094100314a12041c03840b03c41c2c0c04800c8000000e005214100b5034040460041c043d140c41e2320341c0a80d10f4000d41c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 96259271 1250 96258021 96258031
    0xf0609111e070204060e0405070e0106020307021f0c0f12021b06120907050a060306080c030307030c110105070b01030302010f0c020c030c09040f0b0f0106020c060a05030106110a0803070e010e040e0312 88
    0x1030322140003140b03507088040240e01840c448c50080c60428248030001c1100c0314144c12100455206010100243c1d5a03c1201c503032100219203092618010103004850501c0019400361441e02e030050304004001c80b41c801c100340b950b103540c25030301841c403900c01c5500c8409808200c0759003c9801d12868682c011441c00a50300300c0d14000403520348696a0b0089001800385901280c042a5550230402c5212700a03c1006260030307080b00510b1411101d0365024142d003214190144c200e03642000d0b42442c5074010700480e00700e80e40041c8209029a502c2c90028060044020500d80c441c0c2840d80d5003520600020341c3c4141040700030050495400442e0030b100b00c81c84001c10580300c00d5089000c01d80817031355800003207000d01201d0040300c0075517040c000080e1500b42840da66074000d01e020408205170561010590341514154544030480461245125103001e40354400907004210001c1403000d819003240034151141c000380c90344100c16002a04100845046c0005002983c10401c480030070860000c4c1c04503801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 96260521 1250 96259271 96259279
    0x1060b130603090807290a02090901080f1e0c0a090c030c0315050d05011b0c0218040b07030221010b0a090504180303090302030403050f1e010b010f210f0609111e0702 73
    0x40e1700c0c0042c006c01620010740f404d403081c0f903001449055905000289070b000d0003d5500030f1000c98000c6a40e181c0c0c5101441100c0800c01d1b001c18640010031003401b00c042c0300b200061a02d040783c6c3d282c50700c89000342000d03410340c40401d01c0c0c804a840306a009000c2ca00344c1110391100610003c0c9410140080711700f44140c2298555a11303450700c4109400107400020b001042e5a4080200182c4d10504c409030340c48032003810841c072441041100080380480b015a00c40504e240158803002d2020414442000f45405041031803107a4001242d0801da07403000d0540e004c056070f40c0e05009503640c0207000441d092180307070041940980d0142001300b03010b07820900c140c03031191045030320f442d0f500e4440c5400d01e414201c00d584030f81c10110350394126800c80c5100d42000707071104000b0440d1010b00800a030107442d107081000240b0002e440407400409003c3d91031102d40700c0c00d00041c04400304070000107005003158000c1e4100d55207000710346140380c1112400d580d03a4104c640745d48000e00c035020701510703069001243e049900c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 96261771 1250 96260521 96260573
    0xc18050f010207090204031101090e1003060b1203070b09100b0102030708130509010f060807030c02060402101202040816120804090906090c03060524010e06030a0204050301060b130603090807 84
    0x8030807078520046c4011405119246160451130000601540841c3d11030f40c8020551801d018038040c543c0f01c41404c0729889040000c4201c0002d000c15140c424402d42c4000901002ca40c1000f80402001940e2140d041c800596442580e0020410b0885400e4030950303005910078014400041c4078000184031021204821101e501d965a00182e980e04098012000039841ca030b80812106401554441c1c004e84a410705001c0e0a03454000250364100c000c0c000780c4610400c6442212407406218a8030074407201140541d6242d45a503e143c1d44e92040721ba25140c1c0c0040700d40c0008500c003280c10404607403a40620300c02d14040c904080a006012903001c1a20540d9480c84c00c40005000c50b0200001144501c3d008103862828601501814031348201e128040f04801c84541d4060f03078004ec011034080307070494000307403240c445001410083c011604503580540c40d0140104600700300801030719454400c0390300ba20380562203400071019910703401c100400b007460500c910400606050b80101c0709104540c0c94201e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 96263021 1250 96261771 96261779
    0xd020616030f02070602130305010f0216150e0105180601050a080723060703080105040f05010b09101b03050705160803091219081b060606090f030a0c0605030106030c18050f010207 79
    0x7264407c113040854401d20300400c00c2000428000c02c180307203511080440c1800400c80070135040c5c0c022520010288045000ca4400040300766114081507881d0074020442490440c2200d071080700c0394030240c1e07101e00c40c0e64000a684e1070400c001005a03038844029003c4a4034189414281000360364101d22020601305805c0c04680350340010300100d600960321100103516003405e1104940420f445030300c2180c1098010301151b9500e00440320300080a0b40e49448a00e00c1003003c407071040c40d40002201d03c06d43c5000c2c000c2419440009019954010010ba0b207125529038504040e901d01886280040c0d08240300f00350052600c8850b403128143c007081901c22103103076012401c011100048084507040707404034000e071221000c0440f00c84955414001043c06041000010306503008094000b4403c4149448010403030b2014441100c1d2154040354860071542c0b6901c015201c0d1b0000d0151500007450f04441c181c143d403203520201000d00c0710050098286080030305012400024003210340c198840c0c16000a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 96264271 1250 96263021 96263033
    0x20303161e150b010e010e130216060b012703031808030a0201050108010b060903070e18120306010201050a0b060901030f110d020715140f04050703020d030c02030d020616030f0207 79
    0x302506200720908038503004010300c42c400710f81071903916504011580c04080c034070342d0f00a40f001d484110112503200c000b41d20212540d01920442c41c031300a40d1180c0700c031003000b044199040b001d68a10242c0310340607a403414814034003000c0030400b07a000141d44000c0080000c00d00070500c5150b01c00000c0356010340152618500c0d45941c1c808601200140e540d50010040104288900010004111805450314100301e0020366034203101d0040d404c800c55440081070141560b150905032025848041d00c40099001080c0c102d41d0300102c9105000d13500f032030002140c640c400d1082c540c00a200802c100d00b00000d8000440c002e1581800f4440c015580340c66845180045401402c5a840e00020150ba1045a0320700611407504580d410741e02141041c1641410f10300c0c0220283c2d101c0249115409103a0303030703414100c0c03070190168406500403c000000d4403e0590010101101c14003e40440704010310541d4202d030741d0030040f00d030800410540185206094443e0f0044503010a03c3e00015081c41c0058031a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 96265521 1250 96264271 96264323
    0x160509060f030403020a0507091506050c030415022b050703051602040e0703052401030f050705041401050909070e06060d060f060302070309060201090f0803040f0b040803060a080a02030316 83
    0x54005d644801710a008000c02000014042c0040b030a042c4168a60345248090050160080b641440740114503500d021904106032070090110f11003042002c1d480f20b80280d100c0c02d140d0300c2c22001144c03034900c503c003441d01c1c441298006c02c0250b071902e241c09070b01d480c125050342003c451600a04035198003c40903035210300450800c0c19080000d8101c01c4c0c80c6142a52605402c0303020380396040300e145404101d11001c80159811690021705551221000d8602a0700300f1f00e10f0380200d035006161500000c861035008140a05a800a80d000d901c29100c00c000140e40c5e480902c94400090351000028149041c014044c10300c400361440c002c10029111140b10103110385540002000035030120b00c501c185030f485180d58004210074002000b40c1d260517150000d030080c4040d03015016440000101d402c02807100c2400d40c10a8010140100c14207140c0b0741141c2a0744103030345031441405c42c4a804910750304007080b030401d000da005004516040d00e030b41c01c04c030502800e2001036907881004411030711380071000c0f090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 96266771 1250 96265521 96265523
    0xa11130801061401111e03040b0d06030218090a03030b03150405010b0306010512070e04080d0c18080c0a031709060a0306061b0b150f1305011805160509060f0304 71
    0x81000c500f888210307021461450301c107604004655001a602031004103044411054003803943c141907090000f01c9140d40714aa1004c903400310001150581143c15a10003407e0f240308440c900480f9404130400302401200f41c585000d1070300702c2c081040000e4040c0d44000080a4040d042d240d00030484c9407080c2c0b0120084600f40c0302a5119a082d00c41c524050250901500088a11070a10402d08140c940d0f5481d59000c1c1010b904201000321301440305141c1520b030702c958071030f000748188031520400034840354008000d039841030801c04010880140c0800c40b141120b0014280d207034060328544500030400c00481d1070341c0346a90204150600ca4071440014070b44504e442d200807902c2d40c6000d000900c0a02000d00350b6420000030010600081d542c900b4a6070818160358108800e3b0304c407600060452009174003083d52013881201d904007980c070a9040181210803421038a101c2034141c13031901e02556030450700d08000c00075400c4031100b001d02a0024013480712001d000c1600301240c00c010042c2030303030054030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 96268021 1250 96266771 96266773
    0xb03120405040b030303040b010e10050d051507030b060d02070c030204112d07060b0406050a09060905090105040f020d24020418111b0f01060617090706080a111308 72
    0x4050110b070825000e2048100c8090f0002d6296260903112450300c000706024401c03418240e0310200784201d0390b034032a403405072200524002d41c5500d589401d0f5500c41c0e0392001d14540d0362805000894a030f00074415603911503005071019150040100760307640207504c00c0500b103404030030710140800540c60300c1c8902403115200241c01c43d9602500c603201c540ca4240401c0701a0742040110300c04154034207010941c0c0350150301010100340204600001400f03010a600001d40081c160400054660543d4102c0400c40307078400000c0001d40c40d401412403e0320720403600a40807500d07615074000103052034002c001d03866004142d0769240714061001c50200c06c06000e000021190045010b1100e80d681403070303104030040550000c200d000c1c12601010001d000b20400840c500030401211541100c00340140b055144122000704045511340d000030300702846803e000c8620b80c00910015600c0000050b4040544145841d910034a0b9180036240f030240542030001160300d50140081c81968241040c00e10240407058 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 96269271 1250 96268021 96268027
    0xc0e0c0306030f060402030d031a10020d09080a020d03110f060c0912160b030a1404051005010b0708040b090a0b12070f03021608030a0b0a080a0312020a02060f0a0b0312 74
    0x181c101854000c0c072000b80190b80e00200d090000682d000240c4043d464950700307000c204a4520500c01028203042d5203c02d400002c12402c3c0c070325050380031445402069071a1510120a6180d807800c2d80c1c0c1e04406d450094016000488100109006a604d0300d0111955000c8401001401c40644d007400d00603140c45080c29130100300d80305580f91541c810781800f0003103002025407514044260340782c25042d00c20100c40320000008100981c44c2a0400c1407640c80c0e801555220303040c10314095075035205840420b074000d441c210000c40d68450807001c07250030f00d401807140c90409040003540003d50b4051600d855202e95600700c001407003890300029044006006400b50910b151110028041c401e44400481c2010310400c143c00c00c0030f80c81c640303e034440323900031011a44a03614000c04000a00304960116030060f011000010711000008408405910079901c080140303000f001840103034020340702e02c0009a04160005441400a0007030580e010030300700b20218059200d4030100707050604100c00041012000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 96270521 1250 96269271 96269281
    0x21303030203131505030a09051212010f06030c020a0b06180c03090f0105010515030c0d021c140402010c06180c090b0a080c06030408070807080a170a090b130c0e0c03 73
    0x3501c026005145040340d80030001d04c1c00354024998440180000d00c01540d0340203c10501604101014401d01c03030110403640e5140b41c040410303c2850901c5500b9406c40e8911000c42c060f4442d000307801825425400500c1400396554410001030300003440240c01260015840d001d00c0d05505180e4040ca850446a80c1d8038104228124141042020910031383d0313060000400180d2500b008101c1542070b00810303d0780701d0711a1540700e4000d05c200002004528008107200d500d1244061140f0003060381e85104000c1c8a584030036400f104101201c010b400300e44400000c201040d8517410443d410180c0d2008505c91203c19500c0c0c034032100d20ba03040003440e56555146503010741480305007000a01145001080d20390b01c650005180340c480207100414250700450301404002405060720485640403140b01d03121801d81c88006c18800d408030300840400b8100c03001c109114040e125080c49160024640c01066030352910105031052600c01c2107035506444040040c00c54266643d1500488201c0c50320380d92410f003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 96271771 1250 96270521 96270547
    0x12090819030b0108060f10030f0c0908100501050f06210709080111070b1501090f03051605040207110402180402040905070e12071e03050a05010f1808040b090301021303030203 77
    0x702002c581c1448811000d1000c5544c40c00d210b4420283c00301e94aa1315007503c0340085010b410f800c0e80013009103042c201c2220015030000d6a803000c1d200200200c0c1c030505070f1100702d0700c140e9070b0030701c50603801401050b0502210b04019008000b50802da007000241c28140c0310050207921421202a8005000004d0501a903242800352190185400c25040d040c114940c03074207140408040e00f41500e1103004030816409174010301c3d000c4003c1c00640442544159030342401a1075107150750020203030440400003c203030b0340b03858802c1d0382c10740b900104102540e80b481000d00009501c44494010030b0740d1002446c500780d943c0c80c0000c0c400707410003034404a218200214050944100c03d030a40d889105e41600ca1200102c00107103401c121394251000303000158103100040008076482e00044e0081c02100314010522105400c027003005100c00a04001811010304a41c01d0030106030b60080103104201b00400c490300e00340000c1e00008000600061820141e0090760b0b000350500c1d44200d0150b00003141c1c0181c1c03502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 96273021 1250 96271771 96271781
    0x2040501151710050306090105040b0a110901030e030d06080c030106080316062301090c0809010605010504030f110a0f0806070503010303080402010c0312020f0d061a07031209081903 80
    0x30403500e6400c1c04044044081d01c8030452622100d804003601c8009090741a4000032480201005400d03544ca608040d0905c40c040c240c00c44040d41e46240b208042040d01c109403042200d503e01d02c040c0c01d0b0502d04244011009000440250481d43c07109200d001e1040c401c51007410010f0000f00002d00000c45c10f0001e142c00d541584d4407010140d0000d01000040201e0341c460300e40c54a40c8010b0000b44141e01c2c2c08000e041d03030446016400c0450354140080ba52448951000055115941b9480707101e5440c200085c0c00d8a04500603280041c0f000d0000b0400103c2c00345c10030881903ca44d0900a108102c02c000c80d022010740d500a0090441005041014140520032541c00194a2030050300d59030464401400300c0c0c1000c0d10080c10026800d541006061103900001c80c802c01c81e000c00d5540d40d1b024282007400781c00880b100d62039141341010000300071400a401c11000081c41100c1410a1401d40f42901e50381c1000d004042e500e40c81c0c40744200041c4d800c07401081042c540b140c401050781419070000f01210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 96274271 1250 96273021 96273029
    0x203070e04060905060d08030403020a0501090807060b0306060a1701020c03120708010b07020d030c080903060a0e0f0703150c051201060c031704020102060c2512020628020a0e0d0f02040501 83
    0x81e283c401170001035294040b000320510380191400343e0f65111031404a1601e0805c00000e400b9500e40741c0d140041050540c001e25841b070140310107101c0f00c072214003016100d007000c1d90959440001d1000810440048d218443c042507100c1000500746011088080e0642e8428592001c000c8104c0c070800c44825081181c003405407008860207400c002407580403a2042e0f0760542c01a040c080000c210b00e04003e003280c225035a10750064140c4d0f030142010210280603000c90000400640582c0050682c08080001c0c0e00c0704503604010382d40e041016116503100207103491f05000e800c104003007110046191840b880c41d80245056510760b0030740c0205040c001c281d0340403e01e80740440c41c000c006120150703030700040d00c03900151710101855452144400c9100000b441901c0710700c02d44950032109050021070030b1142d902003a16025a5000c0ea102041c204060700c00c0008000054010103203c0100c818a07030142c24000310605021541c0c20306800090204c0c001c0704e50840b040140754003000114201800f0f624014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 96275521 1250 96274271 96274289
    0xc0b1b0601031e24050a05070c0302060f0606070506090c030d0509010e040f0e0a030c02040b01090302030a0807151404030e060301060c06020c0a02101e0e0d14010605040203070e0406 80
    0x19504560350f544030101d10303140100e10300007024101c0c01401924200c080e40e1144c0001d84114a1840403007080180c001180c0040c401450310700040c0c142c0340140307458440c0b03540c036038040c0c0380c60b9444480c0f8200c1c290021306502d0f0055011701032100060001c109a80c0246165801091684080e07000c05140c009c0711204041006002e20000d006641c0220030007800072411280411145080140c107001000c5107074000c01184108443d00302450b030030030218500c0d540252018000c0546080c019264407009120007074040c0d000c2c010080c08581801d0103082c00340c5c85140700107140b0344d03c0c40e00b480c1656a40b00b080580c0c120aa82800201608070306006007a1200341e410324195898244040d1150400d60300103444990001094a603164050010720340d0654018414840c00901c0709009245104802034004000f551030761502840780100708604c0802001400c0c1521009540c1e100362115107101c041c1c4d0000d649418020489680314005140301d6015695000c030300300128410403040d119180d00c06010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 96276771 1250 96275521 96275533
    0x10b070201080f090c1e010305011a0906071406161e05040504020d110f0403020a1a0d0b120615210304050114040308030705040e012705060a030c0b1b 66
    0x40c0d80001d4443c0e440050f04203001c0d80c1c0e0382e440d580303e0308110300e5045031503020814940c801320960000c1541800e6007030070390f000c002d1360703880d91154140c071550f0b1195403503410070074440d80c034241c5010030003084c085204030001c030412907100c0442407038544c0941d640302c600069941d10740e8095901c15083e071040c04088000302848143c2410281c054825805010300407074001650310f442a01c04e42005c12a43c0d10055815a29000c0140c6d1035138541050000300d11a814500001540741c1d107820500c002e005004410a10706220100e44070001c01030184500d40001c0b00c2800d5400b003840c240010780c4a8568034405840303802504003007000b2011901551785883d85002c0075202485000026182625401e0a02c0700341100e4005403103506014a520091440200102308a500d40e4003401400072228502088491641c0b541c0703400562280c1c0d0002c014100815107185d4100001e1500500d8200c82c001e010304c0c02d40d603260b4541003040c40d01c0e9000300079100c03c0043e140000b002d03006075111b42c69103401e01600e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 96278021 1250 96276771 96276773
    0x5090a210c0b070509060d05060103230606070309210213200a0c05030a0201090302010b0f09060d211806080903040603090c0e070e0103061e05120c0d0f0b010b07 71
    0x200300030009a002e040d0000c00c1000941c06801002141c58150700201072945404407040f40c400a4001102c046000034188034400b1202c0300d2140707a000401c8481060074a069494009000098104842c01d0b000c000d15100005401400b0300040c1c0300a01d00110302c085400200e0040c00032070705c590740c001c0d0100e40c03074224150100b0201c00d40c6c0910010319109069614920300d0821105050215006440781c0400074141d00600d40560224413103920030b8000384000c0140c41d007040241c0082500140d0400344000014440e490210b01e00c2c85400d214595101c1000c40c101c8601c000c4054494001003c5000504c44101c480300b1a20100d0090100d0314100310f0074640b28511988078040c81c400c060506441f0040181081000b01c011006044401c3c0a801c43e40b5000000928102e43c80300d11a010132b10740500851440714000d203641c3c40900c80c6d031941c1c441c5403401c010b0010a21070444070480303a003d2003030009541d64a880359140b0b014018810200702c0c018038104905810010b0b40041140c07482002000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 96279271 1250 96278021 96278027
    0xe0c0603011203050702030a0206041e0b070c050609030109060e1f090302031204031205070c0614010f0b070503130308211e130203060c0301060f09080a0807021305090a21 75
    0xc12940e6144c50003540301d00c0b035880480e191404088000f90710100102d8085a41001658200300381c0030268020b44c034041c1d6620f02c00388944941346000c0c1040444031780074445070070454018440d021006c0c000165403a02a1a560115448203402031001d07081010448004801c0660b41c00c0c65012006041120410b01c0e50b000e9502d1042032200880f1481c100002014540100e04110302034040103c02d00c910324240000034a200c102034070440d0024680800240d09402d03484005050320030803da0611082e04104045080d500055000c940c1e5120030020f000c008e41c00d85a0000080d8414421152640b21040098090241080b600c00380703080803004010b0b001c1d40052140881101b001203000d11031722651810480718441110282d010721a01d404d01c145a01540000c41c100c41065940d02c0009104039021100d01c0528451031107107a10012890010400540090078503034070040404440c58041c01415040e00d00481d20758030a030f00941071050501c8203144481c91211b0703281c050b810084140d083c0c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 96280521 1250 96279271 96279299
    0x408030702012a032004090603150b0f2101020c030403030e0d030903020405060609030f0c0108060301061a0f0417010f11040b07121202220503070501020d050d021c0e0c060301 77
    0x10401c01d41c60700100c0c09400c1d00c42c002009170800d01c0081caa5125110504c2a014002e50320040710108003009054070342100030310800c41103a20091018581c50400f03820801e114017800c01d168010010203500d842482000d200038804c0407010f801442c2c450b0304d9030034040c106011328000c0c2e5001c0d480800074a00000c2c0c0c0140c0420550780e04540002c0c90f501c07030802146c6e1134003801c8001c0743c0601c22010102c00030303d0b00141c040b0910304260307140b84071a0f072903c0905007a18040c2c0306040d411001103a01242a091400c0900400003a0340002410941ea41502e00508141090100035a0f59650071441602d0b480c4d004641e0016140b842c84d9103064600003d000141c4a40c0c100074110b902991b1358444400d202d00c0d4400a9104a440250740714060ba860031804440b00103800b0b00d2020921000003464100450340070103c40058024203101e01380d2041c10f5800c1d50100c403d21840e55400c01c60707440403462181300b1440350354280d0000a024603102800c14070f4407550f03a041c0340c07081d14144010000d0f0b124080403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 96281771 1250 96280521 96280601
    0x513090b07050d0207021314011505041a09030a0b0406140c09060c0f0709060f05030f120d15030c080118050d050c03070206070b06010207060e0f0111030d05040803070201 75
    0x70540c1c1d00c1c940f28404000038010190001c1d03121414600010340600300f40c102120300484002040e600d40d0383e1300e051001e044031090140700440d90a0104001d954034601401000000280140d49001414800281055800c940840300210f100050206000d803911503150010780358060042c242c24080d0400c142402200340840c403810000620500a890a0008a5410304070004880e0899100c0f40c146001c1c00560240b105407400c1c00702d00040704e02c0c0008034010780c560940040e0150181c0c09810344415400007080100c815110400303241e6222076100007900641c010945111400e08000c161030a41e5000d0b541c0929081e07440c41c140b004624003140e05070644446040580e40c40d00d10305d4850f07066004800b0041c0d44034034003240f544188040201d42d0380c41034400741d0a8407105603e0b140c05a6284504040c120382003003020224034100c0d4040e05001084141c06002c0320b0611800404045c2a0703042110100d514a1000c814810415024051905100f08044030091990100884c160300d0a050200c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 96283021 1250 96281771 96281777
    0xd08060a05060306010309050105090f0c0414040b040203030408150a0507020a030e0603100806040602090a0e0c0403020f01090801090309061d090f0705070503070308010e0c090d110102010b0d0c0513090b07 90
    0x4a01300340c0c0643d00c04a18244c3c040000d000ba8502001c2d01521102449640c40d098002c20321000300352b00e028410102c03840c03c0d401d0311880b2900d490300c0341003031144010070480c0c00d403000f080085502e100411a5411151418a1041c154a081211003007500c50144c141c200355800a41a0000a0b4001e403080a072000203441c09034483d5a101c19641d000c000325484074000740600c1050001b8404585c00600000209807107980c0e030706981e02041c0703090103000c56601102c048244070078801840d103064a844552070515050440a484411903800c40e00c1c0141c0032008941088400c009060300109030740e00c0d4a100b47c45441c001048000030585400b802400c145030103013030301d000600c0c881c0100f003601d620030380010489464428074034002d401d0307400c04c0c055045c8411200002400020268044582030301014005007010b0700c5540d0343c407404800000105042d0754a402c0000c00c0f03a216907042d46407150156400d281c0440c64001030141b4280c9181400d50130608007046007002c90903804e40c6a800501d98a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 96284271 1250 96283021 96283027
    0x206070b04060f0c230306100c05010f0c0305191107030c0606120c03050f01050c0d0903021005270609030306150d050103080c19051c1202040603020c0d08060a0506 72
    0x85050002050541c0f0994000e5182441100d0070940c003103041ca509143e81111010002130303512009203507020859089a01100e58a0004169031240769000809032041000cc1158550b8013402801d40764521507c0c000640c0d0740040228124a000c01c1c00000c0000c03400c200000c162081c400207107803080540140900c8135418140c0100001a40203100a00201c1001c01a0918519007620f620101b880143c0f000d225900c1c4121504106114090184040d01503480c988101c051624020788107014055040d0300840f0042d00e4040d007980140c0d8800c4140d006000111000504c00c0803540c00b014504060b164070030b104124941d0000070449400141c200c9080100221005083c211403181c0c3c2e1000c684075042c080000100300004002e807100100751010b0b10b43c0744928890580c2c1c0414000409411030b440318031200c800c004840d0b91043c0403142403800417803e45c040c00d20f05090380e205620403000030750300084041c41014103004001c1c00f41c0792071502c00c0181c10100001041c154150140385d108030000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 96285521 1250 96284271 96284273
    0xa0c09062304090609021b0d1b03230c01060602060f01030f0f05030f1b161403030d0216060c091811120a0e120a080c03040309080703111c0206070b04 66
    0x4402558003e20745401c0c2403014a8a070f51440c1c002e908508241d0901d40d100c141402204000803522101ea8061075a4103440301805901c01a01000f5500040c0c0900a044190710640c03070080c000103180380c01c0250055590344404c401d0702c3c01c550555208408541082c010312220480032825141106d400030010340e0008014144480e8034400114002c107a48400030b0784607800600003001d0b02c448050341e1100701c4a01460079085807039040c52250b8070314602c500d03501030103c0040e420a00c00040e5001d02124245090825000c007240d210f102101c5400d500821160b0804c1550f0081c01050002d074640035892500c0e0a4070301041414004562012a4030360f440e4520b0061608240d07580c402c4105801c442608003402407030b009081d182040c40103401450308807840300c0540f40c00c0301d40039211583e50300c106685602c0e400030640c0018100700e0401020010000301d214082080c80080c0d40a940101c0110030408100a0044440e041c00500742000f4400303174015990710010749011542054400400e6038403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 96286771 1250 96285521 96285587
    0x711061e0c090613030b0f011a0307081506040305030414040605030d1d150a0801091a0123030103030f0207050a0b0906030a0b12010c030e060105150d0e01020a05030a0c0906 76
    0x1420101000400c2c4504e00005122142e4030213406120100617180303080e600c1d141a2880300802c510040500c62040021400107071003460366582c81007101c002c0e240c14111083c009480c40d8080c0c1d2080e52282e1000c18240f00c0d40c0814055850040742c115001c000340c0b482c03c0082030b10350b0001caa0b90014051251003151342040d80e60200001058000c090001100003810b20702415007040c20007500003050b078400454800402d01c61111460200c4034070f2140703080e400c0300450b21482016070000d140d030314617203030400c2c9421028007035406180300c1e4075400078a14268000134608009540520302c143c601300001c00021100d241107440058041d14456503a540b002c0300d85003c0c0049040c40d41c1c01265140300780d13108940642c801ca090030030707541d0184000e15101c849599290428000c50f9401615a2081145190b0404c02401090444100882c800780c00100d01c5003260000303419400031510003c20010032a10310700c40c48520740c8241c205000c0359400c1c604001d1900c0e00c00300c00c84000044d40c40712401c107401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 96288021 1250 96286771 96286777
    0xa03020909010f0504030306060e010c02010e0d05031606060e0907050a09020c031902010e011a060f070201120614010908030c07060f0210090807020922030e040605090711061e0c0906 80
    0x140201340600d00b444d02c1c00034010101440341200040c00381c038141c07209600c900350040c1c241d42c0580d5034500480800d020422150281c00342210f01c3d10040001441d01d41c03560401c05d5125000720030004409250124030075501c0e800034030040c071941051600384910307920008600e0564640c4000161504c4045c5136082c075501c5003030b003400405000000c0280405034150081c20b8480d4003803009000c61100b280d402c0e0101c07901e19203440c0e4000002e01580c00684081310152035468014500f40605000000300d4604603125034001600c400464442062a540c004401c0c500400e203a40c000e51515100c40c0c01c09440740447d005903001c0011513100a08018820080000e00d403604441c2085802d0301460442c1940e0b00c00030f01203011794142d40014110040302c00582600058000107030a10301c20540e4101c8186074028515980030b943c4803404500c549643c068288559000d03280d100704c102c60809c0141c40e109009041d84400da80c160300301040b040903004056080690318100540742c440000004402e40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 96289271 1250 96288021 96288041
    0xf0311030405100c052104020409200406060507080910051e03010f0906030804090c050d050708041403040f0b090607060c0504140102010501120b0a06030c08010b1c020a0302090901 79
    0x1002000744010b010000c00c4844903010b00301000c0015240c45074007034a0a0043e00851840003000700440125000340d0740700c01e03174058801400041d6804455588005544100102c00309024000191005038245031141030040c0684d41030180c200000381d502c2481c0c1c4d02c03d1021141c050203041d848502c2c00d50045050301c06946496824010074509131804100300d81003442002030800302e031400090307c070805125503025250440803152421341489480405080101e008608100302046440ca60130298418640145041d5440c4210b50600d42008214180e04021610158208010800400340b0103045d480880c2e5040000945500c9280c00182040c0200840074103090b081c1880d2404550344038005005446500b0701c0072841c01040c100480c00c9500c00d008080141390045034040128400d0500c1581c4940460300108045442c1e40d00c060a06401d58400a005c2e910b03905124071520b084454650907500301c0c0341c94105440507800145102c112440040d000c0c100e001c0201c0c020361002e4110301011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 96290521 1250 96289271 96289301
    0x212010f0c020309190b04031b03060903260903030a090503160317070807090902090d0f062003060a03020108040309080607200105091c050d150329070f03 68
    0x601c80d03454040d45a9200d003036040e1081040000180d0044500d030300d0241901c003903411035401e00f0304581d60060140c0281c201140848022040003000a0740e0b40030f075101141c4240d851081018070035400e112011500c142d5240e840e0701030020009205000010340b6400b94600b41c010507000641e09042c0e0941c8036511120080c1c000d5001e01006054120f42c20065221060300c1009481da10404211030100007920f03080700285010008001b09071241e0040c1202070030003000d0613115a0310b50341d4500b40c0c0c94105e1080711116101d809901600c81c059280082d84203004018134514505940040c03c2c62503035000090501041c100400d051510801c0e44401400355003040b074669091400019100400c140c2502006001200030860150018020a03004028100c001c09020680d09400f100c4c00d00340304954030411005008602081c016401800840c034102d101003a41142181044815000b50326509074100c40a018100d030f890080c010010b80c405540c1c54451801004e41c001207014100c069003070254 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 96291771 1250 96290521 96290531
    0x2031b070b04030801051504090507050c1006090510050117041109010803030a0b01090806060f122a0301020f07170f040e0601080f010f0303031113120b0c090d0212010f 74
    0x400c091285910302a50080c2ca651013180e0b602c030200241071000444542801e582407208220807100c640146400c4255401c1060410b40440101464002c41092600100da1109410000c1074100c0c03045a400050998800b48840d09000000c0d040170107100f0301c2e5180d003240d2000a401d11040c889070000e55200240314180c0f03541c2d14803442e50f890700290799a24100340b9150784454650301506100003100d20620250607241e40d070001308035a49401900e0f1a40200886412011820040c82840890001c0381084024440208003000c6500313450102607010741c2c810050011032651950a40b2081d950042c8064103596403059480050301682c2c1001100010125002c10204c1ca2031640328422035083e0381390041542d81041d003a10b070a800303109071541d00c240c442e03060021a00c01d4008803021000c1071450341c0b034030901c2406041d8407595503011a0003500520507820801005100d4240c1280030410310900380308880380014628692a00028030500c100440d91501d903400703410601c119a40803404000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 96293021 1250 96291771 96291773
    0x1506060415020f12030f0a0c020c0a12030801290c03040302031921051903020909070504030c0b0306030c01030b030c04090818010306030b0a0b0d170406090602010b010c0602031b07 79
    0x580c0350508481c8083c1030290102c00d95019400c5000d80340324003d59459014551105115440180b0049402c035045000d0020704000b140c0300c6030780c6d11000303000016510000b90740bd070a0080440780103030048070105600e0041141005410310f500e0501310b0b041d03030301e01d541c5800e20f05159166201e142c0c002505030080c80c582d0500c01da0014602e50703030311380142c0403611082542d46c0b00e0119a100103100c140072580600ca02c009074241c1200381d4020400c0c60400616002c045030019000940849103c0b0016500140910800240c210b6440007031001d2a0507a0940c102100040d884607403040d02241090741d01d4000300041c0d6420130a0442010b0090420401d0104d6130030403880035885100c401d10400a048802a040d5200e482017108032504501010440c1d10380a030720b2000b800b2144e022030780c81240542008080b440141d20b0700c0515081c0e00a060340c851511002428540f030710707848041964034149040c0110307604a1619001181d12080041e41d9544401150030000702000801091210104401c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 96294271 1250 96293021 96293023
    0xc0711010c12021b06130608100f030506071b241b0806121603080309010603020604090e010605040b06030f0702070b070c05090a051b070501060506070605040303060b0c150606041502 80
    0x100c07007485013010840401044002d010440c454003021901c1910440c05c100402803046030b00c1c641000071119503581c4d580d946c4d0030004070f088040e0400d881640000081c414215000301c0b01c180c0f81c058003840d1204014064441c00c050400303c0748203c0d154942c02907200c40b05030307440d40580c501c1694120094085101241e00500c0c130941119202d005a020b4150040d44981c00900c80ba190b5080030386001d0301034191790316921640c00250030542d0030f649070080400142d842002500192900050001d110b0700102051425a0100c1e445140524a0503850540e551035840859603c991207440040c0f840d107480908920b0000d251707001e00750401d0045102e00030415403003041d0301205c0f01110401c0c103548400900703900b191030903140f05a03c1c2c0e4502d000502007110900150180030300031000050030302e03640d4010401503844100308880080d03413142080704160f0580b0075240a0080e0107019170078040b070f0001040c2c0e101802103640c00040d01d20b4000641c565907400c01c823006042d20300d0710289d01350103404010f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 96295521 1250 96294271 96294283
    0x9080c1501080105011a131215060509070806010c0f02210601092a02030d090b01030203010e07150509120304260a03050702040203130606032003060c0711010c1202 72
    0x4150035032000c00000b1400c005005250590700c45440c918030a545c0b0803401020f50b40301e0300000141d6603d608000070701114010300e1000345070107480602d10203035059504a049030400e82066200d21500000c1c4454140d1080d240e5070701400c282400d50444503d4204a207040000700d034003d6005040c802021959003107092075034030000400c421039165036210428101a10311381d058004c000c0c0c8a0142c540c00b1a180025003540205140c01540c0ca808095042c270000d461410b8019215080f40350010800c42c00c092045c0c1e030a580460010345202c40c103215211a003c62900341e4407040142c08684040d5568035440020203000800084964895640c01c1d9408030080d55a441c02641d004121071428410012480f180482d602d96541442d28203941c2c01c000c000d4101801c1d03081d001908841d07000002e007031445120060350040303590f45006444110b1401c0040741140354103001e074211009100c840307011501130350060799214420400301c040c0360b40100c4818141032009401030a1540384030640c01d8000c19a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 96296771 1250 96295521 96295543
    0xe0301110903160509130c0807060309020f0607032c0402041202011e050708030a0b030615040b100507020d0303110d020406090608042f22050f010b030103140109080c 73
    0x203807006031031503e880012145043c8151900304c580a0005294000c0e0101442107441c840d298401c40f690322680850315101294010201084d40e4440300400d600d4440c0c3e590b004024111001c928000c02035030001e00f0500d030380300900c0902a9104400800e04c100c1c588425110102820464546580301030103210206c3c045c07816400b248510101000922005543c1c2080100c15100c0728a032004980e03451960b41d00003084049025a101c403a14400d54050001500034a42e490319880403248100c2000211403e4034a00ca1245000e01c0106080d0760b00001503032009501101c442150400904080d000303865801118071140e01c0c0050341804a02d400c1e4058002e0340c03107996800c080203407102e0301070300c111100341c0c1d002d0107640c82d16005540b1030b102c04400b0121480001244c9201451130004200f5a0b42c5c0c80a000040325001010101c100b03281e4402c86a00c00b810700310f003c0740e551400c000c8003600e11040c0009010f08012943c1c00500c050250400d140d825401101c0b00e94548031000481c1d00d8400c4400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 96298021 1250 96296771 96296773
    0x9031b03020f01140402120706090e07180b0d0e030c0c061e04030311060109020a0c060216050609070806090c0f0114120a0e0c0d0b0105100c0c060905150403030503160e0301110903 79
    0x8492403c461f400103e8031300303550007912031040b070b0750074242a40c40c9060001c00722003c0203002c22140003200c1448040c04010700d00a0891600c0d41b84100f40902038801c40340003c0c0c00e5600a0060585070039000500d140c0c1d418080c0c90b029611350b851507200c4030060042d18004500603000400204140c1c0c02034030021184541c1e8240c0d89640d803102800000e03031240100c0540040d14403851035011481d1a40284110705041c40441202e1030203503030321805c00c40c040f1070001c1e0580100070100846403092158640c001c500801a01815110100180341d0f1541300901038100102045034521221401c003c403151a2010192944c0302d00c2c00d5101c900191155482d100b54901a1b05050720090070309902144495502c540c401130b06a080c801440700400c0118038070350400c4210090303480801d0303031450094060300c150783d0344c004401d0030031080c80500103a0300c41c0a030703283c1c41c200b00801c0441c0d4064207036500114140c1c40c8030044864600100c502d05940030340183c0c1546428038402170040d90100a214081d4160 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 96299271 1250 96298021 96298039
    0x30d1d1002070c051c0501051f060e0a0303030c02071205070303110313030204050709030b040b0405060711120f1c05060a05012d030e0a05010b01021009031b03020f01140402 76
    0x1850300026409800c1005009011059050080f485c150f020000d284441104003202510340c0c1e2582c0c1e0940b2400c0c0c0300889800010b45030001c1c40d41100c101c100140980e82841300d511400303280818190030a1f40b0010741010385e03891842000318800e0007424000d110f00a42940d5103030103410800c0e210545880700302c020031410203082500c0003001c026036603654501201d01441c03624580034800074000c010440403c0240d00440440002c145000040c00b0b140102da100050340340c03626001d071601d1406050181805200801a00840710000318044203400280a0680740c20340c00700c081085e0f020356105e151440c2040210859030405550000d440b8550031134020358581d603540c1c0150f500c00202d078a181c80c000242402d10340059142d4560851940091500040c0300003644062810420ba601d02200d5594440f480c04c550381d07030b04200d0407081d10038a1000300084c080304e91300503003001010302407801030030301b951441401d16000748151500e503140c4200a04ca09290016041034a86044404070700c54141c01c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 96300521 1250 96299271 96299293
    0x3120708070507020f0a051005031501090315020d0603020a090903271208090d3e09041a010b12090304080d12020712030501060807030b030d0e03030d1d 67
    0x5566024054640c5031030b05407425000d50240074041d14007841c40f58015010010008640c2c0310142040c01d000120b40d541d40d202d00b4054411010320514070b0304141000406103081c0041604550083d0142580c10f00060780c0e0540801c650024042551010b54862541c6800085403041500f0114081f1702c203550b020303500d0072000240744890111920910b1001060942030050ba00d41518003404240035085407403c100c208800a4281003400d5021103c4400c2c0c650003c494480721180301c0b001503024000c0030250580c5c003951850741900c10b02207030b12807020f050206083c0207000c804005807000b0080080e00c0d1b9a1621884141d603070220114000300c281280006444003004800d072016180c070380015140410060b40100d60301c4071294032034100d0b90fa08000c2234001410f0030706429140c03001031300e01140300d40c9406006031070000020542d0043c0750070800900610381d0041080160000103050a130fa5482c040e40101c0c0c030798000c0301c40c46e0060b1807a00303441e1745410500c2400d203444e100036441100c481c0494 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 96301771 1250 96300521 96300527
    0x910050103030e13060b070c06080903160803180105090601050f030303010f03060209061605010507120207020d02090a1103041b0f1503020a0e0315061306050108010e040201180305031207 82
    0x10901c00a000520003030410051450510a0315200303025804011540b00e03100c0c0780040581c0d04c0148212004510108100f140b550070407005a40203800401850a001c01205070510030002070400170050140000010b410801c03414480c916040500000c0180e8501071300302980d03660080c01090320619082c2500c003500e15000085030b05a840d0904082c810030b16540d18040a504031641c0035030700403020b001c5200d020187c12a21208030b030151002181606110f200039040c144907140745803149004100c8000584c0b00c1c240035462181c1d055481c14510b23551010650001c007020340780c11210810007c140014004001001c066007823800354040305c3c2c1a6192a00511516140300e4160f403408140c824030741c054001c3d0302400e030b000b000341408003c00c42948000ba05011058070104100e500501c1031012508007200038106402d201441000302a04050004c1d019000500c10506003100301d000003800c6910030b465407a000d008249490604540703924016440b50072010040391820034a400088500344 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 96303021 1250 96301771 96301781
    0x40303020a15090506090a0b0f01030809011103040515070506090c2b0b011e050411071506030503030f160906090501050703140f090f030a0309050618030a0b0910 71
    0x15150300140500c0c901a82e44100300011200031500107552040c0d024085a418850300d44a00000400751505101e2490038002e00c520290030b00c00702c0a00c0c607005000041514003141c42e420400d080c44800c40b003034071104034618810703a0031041e00600a050f0200350740c0341b07550141c4100c03803184081e10f029668544415680d0100300719001d84c441010045c2402c0100c100c040c1c045250391040410240144581302d4030b01d00130081e44807101030b411000140b40d201010140c040050308040340c00740500100c06128030350034000c5000242c0907101e19010b004003009682d116000039648030741940d449207450001c000a4005c01ca68260084002c2c245d135900e4680700b0340340300c4103556260711400c1e415400c0070300443c1c41d50031041c021000d00c107100d40514280052080984003007a811039209942d0341e0748109000000a15050b581d001f5442813220310000ba8000c10b05800b41c8005868a40d1181c1d00d0300940351703186259a040540500a0501d18014070020500391846072400e00308031030b00c26400011643c01c841c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 96304271 1250 96303021 96303023
    0x14060f070803040c03050a11100207080d1218030201021c0e03041503090c03061b0c0b1609090501080a0b060907020a03050f1b07051503091b13020a08010e0105060403 73
    0x216040012200141821001e950054000c0070b14504864403a03075410729010401c4815140281e04082104e00c62408492054046901d88003400c0300078604104035940c1c50140f0034002c14800c0082c00340c41c0b039188039840340002c0d01172001c20003a66940c03400c01074004c0d44a03a100c07201c80655a200d26000e50014050035030058503000c003c514082c40c0080c20414a1140581001095103450a44021a02604503140914015100081c1c8800aa400c00060460440380300e070a00064401603c00306181a0002d80c0c08820114908a071181444045804000540261900b07502d0b1000200d08440c00090419130030b885030191440c1511034404100c6220030440e80100143d0000360030f24006440742d0064880d032000101454241100000311030b401c9620507603012616030108000304824602250001c02541e50040344510318200900c4958a4996584d20f0401d00e21000c90004102d840d003005826907508030810440d201d10019100810302c3c002881070090489d1100700114440c9071070801c850450f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 96305521 1250 96304271 96304297
    0x6080d0c030e01121e0501050d02011b08040b0c0f01050106051206151306120c080103050615031212150307050f0111030408060405030a0f021b09150a0b041406 70
    0x5200d0a07502103034400300c1e080409041140e404044a66526a40221041c0f050660040c5031005054449003045841c164003640c0710b0f2640c1d614110161340c100310300451340070071900b0040c07003540142041c0c1c28904c2a98820038281400240130406000701180b6110072165103c0240310a980e44d0204a9850044200c1c410440303035001c0100d06140f504400c10072420b01d00c500326a040c0441114130180c0961264020300c0841c0142c1d2844018400e244114541c442d40e50504603401c0d415071319615680c11000389420301c283c41225169007e5502000000f102d012a40d06041c2d841542041e5011144016129100c1490990481134021300d004225403040d03507030280901028411034001121041120040300d1100c1c0400c00010a01d00d00510140340f065004a00a40e91101c544400500720700150b001c0c0030843d045964400c100d51003002d4204400c1c174040703500c41c080e52240c03200d0304125400c00601c00e51202e020440010240511405002214950070b400c1000441c074409000e0745100c1e5100280c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 96306771 1250 96305521 96305537
    0xf190e0303120a1509060b0403061d0a03121103040f02030d0305221a0403181403030703030506030f16050a090506090c0f040305010609140106230306030c0307030c0906080d 76
    0x90701e204ea0114650081d403289502c241070303075003804004441450b0490303c0b030034900080520a01c0002c3c0944030a842c80c03c50160100c0c40e03520500342d160508641c0050810043e003400801c0400740f6009607070f09504c00026181d0780d00741450404800120b1450490103402039888580e010340c0203204591240c40802032000b2010301c85100030340e6070b00800a04544041c8000061082c140c18016514416403081e110b0204141d4004080e2981d00503540c8400d2403000006c40700e12282d1804425624090360500700072541e5111100041e090065400c2370400a11408024444803540400001d0840c1c400341c4000c14456200c000407010740c0d000302d030155007140c0d0403c0410700d041104030040200035440b44040341465240c1c0e48240c00d5950a0344540040b50300c0c1c036222000706a86601440c010800c5003406030100895200c81c001003403501141c2c4441e2040400001c0ca1a00c2c00d01c90240d01080c002c00750b130301c0180c40f4030b802100e0f215140504903c551610202082402c800a01681081d86584902d52 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 96308021 1250 96306771 96306781
    0x5090106061d0d1101020f0f0724140f0702090403031e090b01030f17030a0203100905130f11041d01060503160b030702030d020403050c090702121206060f190e030312 73
    0x4404d43c102e445490451040b418880c06880051007500880c0800101820006181259099009040306400116201c0e040403810065070030190110a0440c2500c41640380c1c600382c00310b9501340c06461006500075881e01d0401c0109036042d8803856035081d4954221142e00101200c50040b105015030003050040d0590046c40440d590a0350320801500c150341440c0d00c0308444c7c201400c10340003907602e00d410716000300c00e000c0c3c0103000101e200094407080300100202d1070820703100304070f06610a60180a100090b40b030740003440040c00303462580c0600584280300d901250b04190100e109201c0920301107501c0e081c808540c078540811a081f82881d01c4900c202c64900f08211100340790300160210003944810000c11840e07a1507400600002c6002e40b026040030b05142042c00045000105500c046402144c130782480030180388207981520b071041c100442c1c25a07900300030074490710502802410b0800046601d44407075410b84851500808155542c4440354042c000317261b030301c0c021840310002080711040083c13 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 96309271 1250 96308021 96308033
    0x204082a0a060c0b0115080a05060f0303030106020307030801080303040c150306120b06040c090b1e250515040308131b030308010807060c0c141305090106061d0d 71
    0x22000e00d002000303189894924400903071202103940c00403001c114000802d07410f02220705811401016201a1003003120002c90f0000c01e592070040c000501d048d40c6d100800c20649070030141c2c00310500040d04881c1c0d01e58640e18041e54070b402c140c0c0110700140d0b059001260081021054a01070343c3c0c00000d44400e1400d0014a401110b8010111030405644d800d00182500d0907a005c41c0c0c5680c002c044003811801c4c18002d21041d29005403034035043c009205030400520460341c0845078040d000f0503e00003000040d810360021032058490203021107840e6000d40141581806200c00018860002c451842e0000f41c8502288841140d001c0d000c5403401000035069400c2944003001d82e441240442210b00d0401e2481d0404107082c2c0013500022180c100600c240c400400050001d88a141800c0d0070781c0b441e80e651040c41580500680785a400e5140c1e112000d80c403001c10310601544519810f111901e0000d0401d4000d1800d44591f400050402c50406203100c59032201810f22440034202840c0f40744641c40368 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 96310521 1250 96309271 96309313
    0x20f060a091401020d020301170312010b09010215161b0309060c06060b070320070302090c0c0712030203090414191d0a030801050405010e07080a0b0a0f030807060609020408 76
    0x80d0b0301002016a044405242807000304410450400016180e5040005c41c04c441f0b408090041034a40c010080700a00640d01105281108d8a145090b42c0d510081c000407820f0203107804840543c0252001842003002440d641e074014051243d460021031008801190000c03064003070f000c0c0c0416507014040c40001c2c0308140c00c0c42d400340144401310300240d0700d400800b481e501264061b0000342c44425020201e0324124618078030703030401800815021f815500054911000a0120030401400268801c480d44090000f20000c00103840c2a4a01d035015043c060340320350029071454800d9107808100400500d407070751018021004a0070b90300c118000468258028525680c5494030400301001820400e0410441840f88038401da40d6120396500d071009000c141e80301a0007658104443c90204103c040e48840f0307107640480802ca0108003030001c0804110700b1041038103d00002c02a0102c0403052040800c000d203051b44c850401000000e6031800107070100e00860042c1c010035048042d44191b8132080d0080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 96311771 1250 96310521 96310523
    0x25140d0c0b160f060b01090e150105090406030618061413030c0203011407090e0a0501060c0f1403160b0601020c01090b0a1202130312020c01050a030e0a0c030c08010606020f060a09 79
    0x1612407000692a101d0120003c1d60701100c46030385525201c0001d5034004440002400140311130210380c02c1018a0750380035030080d14814104100810721030140e03035980d0020001550014000c101007150300d0b801c4030000f540070760180c0b0554104101841100d86101c5902d200f040d022142038820280c6c0e9404507542c2c4c0c0640001d90303040d0340356060030134511400c0c1c036124040c101a88ae04203089240c02451002002d0040001140c2407500004000840d0050300b030086482d03004181c40380140d10361416021420091400c81c50138840480e945d00d281d514001c040e20341034041d01b5500c6043d5102001242d072040100c000e41c3c000380d10320004010785500c00000e40320764540d608010100892051588049030027100c82c15405c4851400d0400034009403505c20682e804080c806482c08554680000e80300d4420f03000054100350f565600e0002d180c00500c880303da1a5031100204010a80d80c2c1030816002809000b00a90365182020000c3c000340001400203007a4110005071107513544102c6048024450140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 96313021 1250 96311771 96311797
    0x102060c03070c0c090609110c0c040207020604080304030b040c17070b03180a060903180b0405090402060c010f1410081b030c0a060c2006070605060325140d0c0b 71
    0x140c400010880d55071000030f4008017400050961a00c819003050382c4814044d0300441c002040700c2c1c02001c070045100f1041d40340a0b01c000d80c3d981100e00c0890800d01c12070303026645600000c60084100040552401c0c00b49004034502540c1c0c5880314001c2c49400d0a08100e140503910041d020014071028401640c5e201c00001c0cac6910b14440c51101e220304110780d02c80201c43c590f81c0d403114101010741140c10403060f200a0300e81010794500340140510b084c8200d0254a00c1800c1540010b0215500d901c01c58024002e80e03002480705003ca552074a02400e00041c00d1440c4145035000108481c0050080100f02d60038280142010885014191000014904a90b400d8007880d00c00b05859150405090000c007540c4d544c070b40100308170382060b550090301c892003103000d80da900004c40c00360380da0182914000b54216400144035111000044e10301100d054904150b0302485c5960b080c0c400e000200300c1e080310880740801030591203290400604a600800007010007c08120900040c000000a08200c0309164 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 96314271 1250 96313021 96313037
    0x20606040507031803050d0f050603060408090d0606030b0621030702060d060308120106090603020301050f090a0f0f09150905150702070e16030b0a060206010b0706060e10061106060102060c0307 85
    0x2040c1c1013040080c1e0401a000300b80001581d41e55004035100311502d40d111040100000c0c2040e10003c2d46410014001800345600404c03000c00540d60400280750303403a403220302008942d5580c540208007003002c4410321310a4a05452090000194030743e12028104035a004d140b8100e03090707003005102e400040803812443c0d03441002000003001607004000382c00c01c550200070903601d4803400130850381031504010201401800100b20503203426040e1030303025008031070940c46903540003828001410a42c91070132815040c014503101d00340c02c2e540315040b0a80104040341c0c1d06454604641c060f12461040101a6400000c000e140d50701600b100c59048000f0307105070781820341c0d900d0745041c003c2803d23a824644110a42d00e04100c8030741601c0f410050820645400380d0143c940750019450f0074052140c110300442c00100039082080d00d0388110080c020003504110141024034016001d0030302d03800348001181050705620301c40240002c0f0b4070701c00c41c0140c0c002c00301c40d41c0c2c084a1100c6a0400b4207180b090141c41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 96315521 1250 96314271 96314291
    0x70c05060a0201020714150403050f190914031204050d14010507120501050d150f0204030203070e0a1805030304020121020a02010c0e120304090908090a06050301050109050402090102060604050703 86
    0x1103030003060201c51650000da1141c28901704070f41c21205000103444554041100420014215440390741d105802d0708010f82c49803e00c0350900528440c1103418100d09145118258400360001a1242a40e00c0c3c0c01025240f4020b00c03041c1540e4444101c19404070080a110030040e500d080088403a00c688079103201690400b0040005083d91420b44054001c52410024a181000188206801000c0880e010490010305440e00c403892030000c003002904d252201d9078241c5588440c1c0480e0004c40e40501200d0885c1c0c1e403400780000044003560801549824040210400ca0345101221349a03600100030f9469616203a00545201c1c00502848a0310a60108400e80507000f6101520304a40640c0011500c03070700000000b4203c0082c1201da501c980d180504c15040791100009681c00d6989a4400084484007820855401e001d80407089621140f6140d006ca944c0f684a00994103c1e0020b882c0c41c2142c0d0b03202e20412081e40140c00100c0c1c0103a0080300041c60310328243c1c203c1500004141000107100841c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 96316771 1250 96315521 96315529
    0x3020f070c0810020f0d090c120f140309060a0f02010b060c0109050d05160209061311040906090204060e010c0f1b0e16020c3d170103020a05010302070c05 68
    0x400981d10314200520420242c40240400d41c070510482e1011803034101000b4110b243c0e8050329041c21106580c0e200e0040410001a10502c050540c0807a00d002c140c100b0f180584004119500490311051840820201420000b0035100c1d00034005084500f01401e4160803689800754090103402c641d29025580c80c00d0300c0d103000405c2410886000422003410600b40285031903c0d0054180810000b0404201d42d003600c918004200c1d0340c11501300c00c0c0f0781c07104800200080500c042c00404180b07484003686a62424400400c202c480017036042c013400c1e80c1c07100c25100702e0181d481000c0115813403601d0b10016610030701c040d100c401c0c840c840a01c100c40850721003a0455245600a00f07041c900410144400c03c000324015601c440e2014904a0f00f03140d5110003034a0301c80d02c0643da40501221012803e060030707847c1c18101a00d01a0744c0110300c06185001c8825039054070303100c8078080f88002c01c04200c0025408006070583e600075008810080c603040046000307601c000307001d50744003005210100d42c80c2d803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 96318021 1250 96316771 96316777
    0x50319060b130915030b0a020c01020417030405100203030421050d09060501230a1401140a020619020309061f0801020c060406060b1204030509040b040513030801080102040602030f070303020f 84
    0x709440d4101a440d04003400700c0121051390700b10070501180c00004100140480b0703015544169036240150300c40014001c03a50190080742c00c6040c000d04540e80c40d0458290000241c81141c2c0119480d9520110115090ba22440f05890140001956100b880e40074804290380040c80b80da80c1c03030b00d2490941c0c200c0c000070071202c2200b01142c2254450004011440e002041c0c50500c6e00001c80711003004031070030002131080e5032502c070b14815095030b0f0078a07403203d0780180f8232850388645038204180e903604000340c02900c51004981c0640889110301050704081d82d98401c2d80c0c840e4103510020301d01c0791140c59102c240800b5104c0c0e1a44100d0401801140150302800a0a880b00525004000b68142071501d041541c40355000804644400c4c880d000b01500000d0f0016003007901410301a40e5040e584002c20064107211030929046400d2000f400804c00b80c0c9050136560703e0280c0d44100142e40ca4010603800c5c2d02c99807085000692080c080036440f07100351001401454842e00b001490500c081450b0215a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 96319271 1250 96318021 96318037
    0xc091203020d02280b0c041a0903070603090302100e160806190e07030803040303020909040b0a0b0603161206030c0803031927140f030d06050f01050319060b 69
    0x81c20000d014650650104030081c0f4010800580030400421100218608803400c1c4c0f028090780010f0000c20280340120742254081c0804c440100311146a40c06e90754a99408183d80e03a00034403800b040003440c01e10a22945035403a5155014290644c0d9021141c4090700083c040d8036100e02488103503030b00f40c1081d02c40c03810003030410b030020700b04510b4141031820910002d04c000c0481542003070070401c40c00b88003042c41d03400d0301d6214001a4903a100c900f001c0380240948a00d01c2d0f0015840c0040c0f00500c1744c032994040c41039441030000e010003282002480502e00082c0d5200580065805410350014001c4130300188520a1a82c0041c05694a8032241c0745a03440394840441c03908000f00b4002d0b0a0440c000d00c80c40300030919020300501e44006400c2100c02c203421042d00440000194110030006031202100c10309d02d415003102c003204409040345440340e00c651903d088080c9042d00000c0c0d41d040c00107180c040c91605843d0541036a59a406260306012001140c10050b80e4910000c201e090403440601844 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 96320521 1250 96319271 96319273
    0xa02011d1501050907080c03090106050316050f01031406011101110a0c120302030c0a1d1203040f0e0103050c09040f0b0c0406030525030e0708030f0d0b0a080c040c09120302 76
    0x102541800d4501c0304038181c220078026450001008045604506904d0b0041072160f25943d8a40d1010351310780c010441d47d08501e0341400b82d14521742106160301440c400344c4004803140d0070344244c4d00f401541203850194a03519500c80c01400039120358007910121514585040000c500c21a8441292820354040501c031004141130715032200074020508818480f450081c2400c61a50400c19804091401001c08410402500c0503102c0f89000d01c50300e401100350030103070042d0700e0010207600c141d842c1d030058021044c547c007049000107503e80842000a04a0740c000300070708801c0304100709108030804002c1050760183c01d40c1c0c030f9480004041209c0f0301d03c904001c405c0e00d44c40c1d5003030a500505455000c0d048403800c130700c03200c04a2880e002028100080c0342480c10001066003c1d000411f042604990011080d400003040300078140d100c0d40c0c010156442d071984100181403058007040b160484601540c10740364400c200010b194109a8000030020141f0305045d881d180c3d64505050542040c84011801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 96321771 1250 96320521 96320533
    0x31b04030510110a1d0109090203040c0503010e0106210f02090c03010302010212121305100e0c0a06020a03050d0b18010b0c010c0206130201080c12130512120a020a02011d 75
    0x1240d60320500203c449011001490921601c000411070380300c0b0055850244c81d508000f07031490b0301951140c07005102103c0c2c1903440b8038103820064480301c190f202d05402542030581043d60707010706110782d01c00d4981402c2e4826020b4a91802038504a03409002100c083d40c0b41e0b11544d02503a1107100191240c80f10800c4d1030350b00c0d810b602c0020300300400a480191049024881c04070303200401c241f03c0350320070510015426861214207140d490030022160300d030328240c0b509010031240395020032041030140702994a0042c1d1903a0f814201d0342c074035403540c0c00b6000a00030b102e00d1601801c2c40d0880030070150014514408134801c41150006d1110030380c00703250025000134480341ca10400703005410404526001400280c40c2001001181080d6a000281001003100004000070b02410075241c0f9180b404418025a18046160644110340d03400c0989092240746441540d1401d18800c407a4003a56014580c2800d85440c010300002e500100f2010080d5520b605259800c600f64001c0071109814680080c54 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 96323021 1250 96321771 96321793
    0x11107060b0a0b0906090f0907030905120c06010e0c0409020f0301061b0b06040f15080307020307230d03030f050c0d0f0501080307020613080a12110c01020a0206031b040305 76
    0x4101d908402000d4010070340351004100540c6100155144160141c070059a11003003200029100c0181d60500b580c030101060a10a4295065000048040c8160200c4800c00c6869125070428028042d0841c51035020000620401244c03800c100d4205000c9184d087c10141c440401d40141d800034070915040b00000b1004120b1030794031040c00c490628245182d091891103a48408500c0100188014040e0340c9403000c2c1180d00e0b200f80e2291441011500c08001c0c6103444406040d1a070380590000d0307100788104a000b145c98070703c0440e030b04034070307000702080d045480c4000041c42041c101011040d03050550b0749030f120030104a540203091181030080c48155982014400c0b540868800080d0041c10320b2900c80180241c902c0001180d03090380c1c04960040c1c4030340c403c2c0080c400707607401d54002c034200d40a04403200d802c120b070850305070b0001100d98642d606288040c43e8019564952101031034016031128898401504194008680101c1c019104842501e08841d0700042d60740250300864107544080c100360 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 96324271 1250 96323021 96323033
    0xc0b04030201152304021303020303030103060605190e130204020c03030a09022409060705120a0804030207050405090d03050c0c0102041403010515093114060903040b04140d0203011107 81
    0x7016144661240304014076000e9010128032104600e280116400211f110400041e9034800c00110781c0101100d540c1e6850b441e001000e4902885628003880c0c80d003842c0c1607102480c2c080c0409403150030040d07400316991203030680c1080e4040d14050384c000381d0070400a14035450038001180700380c11141010a0b04141403042c0180e802d8a800e000c9038110b90002c0e001141d0904904a48000c0421a4030b01c5c0c035040c80d801c059050a903424105c03e08160001601c44020b5002204544074900a400f0703640d2292b0703031b08140f0050318000c0b604d1a00310741004207000c041d03178005da0000ea04031040ea00b0a60500074042c403840c5c01c90f445038001c6036025003612041d000e00d1509005450344803407a01129819101c0403804500110005000c90307009072440c2038481d1000b0030310547c4980c11550369503822a05151400c01c050504402001107000b030040ca000200408000411502101c2c0c4514055103070903c0c11740c5041000d00d0305280c003a888103040c2c02150260380c0900880c1030450030140040d9449040b45812 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 96325521 1250 96324271 96324311
    0x302030601030b040c180902040f0b1c0603050d081b030105061308070b040302040608211605010501170115060203090d020f131b030605010e01050a03020912030d0b04050f160c0b04030201 82
    0x4820030a00401090000c61481200c483c102c1e0700c1e1005c1c2e1529410910100d8401c03040380cd0050400e40c0c03800f038001060010020308071680e441541c507461000e0b02c52441c60585100b070303034481f102072071030400c01048030f4180329005000031020112008907007521004854105416035212504c500d8020405200758a054425107000b011400024042c1003c01c42d9a5260001c03c0d0900011030031010030b40c45080340b001090541c1e0703164050000c000b99a1111110751403607681010031007683d0701c5c1500c25000c3e02401c16004040d20055001941080c1d001410080400c0550030304070f8201d001c400d01854603881c0e401c42840320400129011818110920b003180418a840b251101094104201040300d644c211038404c00e00442840c000d5036915401c4401c2d000b81c401c81348950b410050042d03008880040c04409040b00b15801e806c2070001900714010407055800a40b020b00d40340c1c58150109050655100c0b140025035442c2c1040900b10800d52110400300a040f03d0a8000d81d44400003010408000282 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 96326771 1250 96325521 96325529
    0x50102010b090615030408040803120714030403020c04021305040504050f24010339031b050a0510020109080a020604020906310609090615240302030601030b040c18 72
    0x2000ca1145444400130b00c50700c0796000300d012201400030204040c031a01030121409010040c007140d90390707200202522034002080301d911000400b032580300c1807042c07a10300450380a40d415a00a080301180d04040200079880003400a405c0040141c0004d100d80b40c0340580c500c03075409180503003018007420f80f16a044c0300038107a0401980c410b244c4500000c0c07042092041c150313074100000542200d140345900346603508191411a0320300b4000c1085c0290810002401c0903071f88a00c0140f03185081304800b00011165501482e54807103120102032105081180256200c2581d40c40041210482611741e07005c0e41d070008080d1030040c2c026408220a50400541c5160050b03420713600040e040c80e5101111000c105900301c003105901c50440940c0e407900007500013001410417400c04000c0c9089600e450f10081481080c0480080c42c2884c0000306201a5880d085124080071101c180e401d580d0344046000394801828a4141544c9400600310b070f4413280b01d0252030a0a984415002400302c00081115202582c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 96328021 1250 96326771 96326779
    0xe070b071103010e06010905060d30090503030a110102040e010b070c0b04120b060103090b0907030c080a03170a1503060b0916052a150f090c010e01080604020c0610050102010b 77
    0x1a41302004900098900e044a421242c0007a10380c40341c400282050082e004c1c0035040300d41960300c1803002c00800107071030700080040385407401c0605161003d50f680400c0348100c03a4560814410070710007901035002e12039805040f07400189003d8485442c62080c540a03000766103090000300d1644104000288060040d00802e10301c241001d140180703458907603031030090003403001d0901404281e00341d0007038000580d0300d075000b10113000360306e03200083c0c40d9103200c644002ea071174a01103440000e4034803000c205d04801c0c9406580e0903003400002c012111002c5800b400d103103601c0d81d844492000d86110b10081300c018600c58600411b4886034201003100102014009140000c2108254451140c2203412600c100700c65443c142080d20340380d0240c01c4110300c200b8607211035004059045503103a1100f64994403ca020342e40e2100302703880b60980c040d80c80d550707004064041641c0036241d03851503004103d129408880200050700c0d01d030620b41c0701c41c1000020f91f006114003058a901340030075a028058404501e10580b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 96329271 1250 96328021 96328031
    0x60810020319110c060c0a0210050408070803041505070203130605031302270c070302070b0a05040b031003020301090f02040f09020d0807050c1f080601080708070e03010e070b07110301 81
    0x282050400004460880842e159503440500610480d00141c6084032000030036503805180044045000e0791003070001741c005019601c8a000f03007540300d104150255400408150801d105941c488141ea400a4002d070741d80c1d0310300205005000b905000d031a1146209501440d00c2d036040218403242c80929410120920100b40104414401b40c13108071001c0c0703a01119003990358000c0691140c0302c0054480081080c07078004040000020840c001851014441c1d82116007080d95610414498080e40d01081c001482c10003003044400680d401070b41d000003000540c3e14120395603a000900b121400751046a40106020300401135152500c15a8080f42102d02c00f44072804641e40000c0d00c500401a0090150301c0c00f144a00c1070000c200706560031850040e103000d406400186110308018014050307000000c0c069800641e00d948660146c2c5e0041c10340742c444c1c03070250700c4040d000e40d290351210150030f4143d942c411302d00e21810003c102e80d000a20214880c1603036801c560801c40400750803000302038001d1f8102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 96330521 1250 96329271 96329281
    0x90319020a030215241203070f140102190e0411121006030c090918060501080303010806060303090105070f0222021c0603020307061808010623040603050d050921010608100203 77
    0x24450417000601051801141a00362030700060355002c2c0042a0151844049034420802c121030060421407030007604080e14181c521140c00b8240d01c10f0340c032000000154100001402c6011361400c0c80d01000c020b002180341c0c6055034060142d0303006200c6c00c926103030b0a131090000d034000007680348000d805245810300103a1542000608007101ca4030480400f15030740e40c909000420090a840c10380d5510900a003d60750b5614582a0b0769002030182201500821000c07c1103171130000100c96000e04180c4866040580303503103074030b1300c6000056800e076085443d8032400c20000301c1d01c2842000200c0c56910040c1c0f01d450305082c141280882e8006440c0f014a004802d0000d80d0b4002210740c216013030391507e00201c142400207141c2d20740c1c650307002070300c0d9600300780c004100d5011081d00000112030300c0d0080381a002000302000151001c1d48401782c07183d0060b56050505500c100014204040c0140403071240c0c0c1d0070f522005d0b43c00c6491400d01090341c0d554520a21400c0401c0c024004884101d9005505604003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 96331771 1250 96330521 96330541
    0xf0801050f0d03020c1005070512070c14030a170d0b01020f0a17040b04090218011b080c0f1914030a0f05092b021c1703090319020a030215 61
    0x4040c80c0c2074452030329220480b003014420403c0d4510b000010b030001141030070f10140030305a0f80008000b21094000c1102c01c2501401507810384032103075004428154058503107a0b558120480200c0d4041d01030280090f01808180d07281c45400329017803401c400c581d50390091075103401207901c4102940e045411005600310038090000341500c1468000d008038203241880081031820380710350b50009100c3c8202240021324454244e02401d03219200c403c58041c480b0440e001101e4000c001c103010030003d2400020703400400c842d000901903524050084520317075814402e00910307044c5048003840200302e02000c000100a0500042746440308103030000c5081101000d00601254140582141001404900804641d0315000b208030040c20b1114910b0071030101442d90207580340c24a50590082d040c2e1605c0c50715802e103845e1650030881d080219583c0c100c504a14142c0168000790145d65144002c0c00240340b10b880b0100c000c46400904c2c0c000703101408451402a041c26403c2820301c440d441414200030708400d0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 96333021 1250 96331771 96331789
    0x4090c110c0301140610031b020106081005160807050405040905100e030702010203030f040c15020f010614010c0204021e0a0c03020c030102070c1206091b050a080102030408090909150c07030f080105 87
    0x4802c0b42c00f05c030030804011085000f480c00d82109000180340049608042741c043d40100d0540300050191401c0c20b1240404030148d81c419110020169890442070340d68601c40d042e0355400401e40e16006280c16501d400003002d4455007071065585800181c032450860000780b0404c00c0313002040020b9402c0400a030000307074403404001d02203074a05101900260070000840c2055000e812403004510100d038040c40000e648070009403c6603540d40c030f0311102090014446803200c0d640c1105944803801c0654642c2403201030742260540080f9002040ba1841d0003402103030240a5040d41940e501000c84a80e04000f403915001c1c0d520640681d10400010b40440c0a500914054884103c81b4034100499898650014034034054003400b5410000011103203900b10002ca0000c80324200c0e0b82d51a0b49813940c60140c01c0f80300607100105810401c11525442d8201060090f074014081016079446d0000341c68a400611000c607036082d031420000402404141e040140450041d0140c54501490b41c14040891002a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 96334271 1250 96333021 96333031
    0x110c100c0b0405010f0906060302010e09091b01030f0204030f03090f0b03010b0f0d0603050105010f08030c0615030a050709060504110a200c0d0f0b011e0302060d0204090c110c030114 80
    0x910440014040c0303d000d402c0001c1880b40c414040000b25442c0c100140206003502007240080c00d020300c081450301e09a04c803240200340300c0015144581e03038001400c003004500030115040c1502e0f4601141e03010b0f9244041d1000714064038040d2044d18040c9802000d52406802292414400b80c00900945d82800c0540f03041d1142c0450481c0d55111001c01300e0313014026620781000aa08004020003040f0043d000a41220164030205507a19152090951240902d543d000c855522003000240c0c04c4189500c04400c0d08170140548050304042d4403403506052043c2c02030440c2036198681005241003920403078034162840c0c82d0043c101403002000802401e2040121441360000ca0034015480c04103008843e00303500c00408003e1100850328040b0b02111143d80291200304102d4000201400210b81141810043c4984501e1403800c42d402c010240d04a03142084440c0d5090201041a031031a100c0e61910303401d039490b9984c1b42c0d00b07401420b0b881d00313003210800e82c02641000d11200c1c2450181c00819041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 96335521 1250 96334271 96334283
    0xa0201080402040603060216060b010e09150109030206030705031032040f0c090305010b010831080307021f020a1403040611070f050d0e01090302060a110607110c100c 73
    0x5a1100d000203005002e0701d41006d040f50f03100281c038441100340510700c042c160b4440c0d038003401404603180c010b45134040c0c40c8522980140d079450001e03841c0c85018104000080050500c40a015226004661150001c4900e003000c41c00000c01c1c0300400d9031500481d0000c00044055039401c052105225030081040000078450290000140a03542d890350815031031100ba9113010000d003010a01c000b851030780ca0380b0041d501540b921648404035481040205e2007844c002d0f160040383c0c00c0003100f840c241142c444030b446034021150000750001d6101001513020b5003a0b81e004288e65040b20b02500c812802000c41120303481e104000440d00756030000360380e101084509200c0d80d1070341e030b81e420898007400c2503c080380c20310040000c20901b004600321000308034501680447d050b0b000081d000f074950541401c06203002c100c400030f080006141103401085601d03088d00e0300419407600500901e00e488000d448044c0400c2410704c0001c20f00ba0108110321040c41e080b110164000040300024103040300210004c3c1c81 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 96336771 1250 96335521 96335537
    0xf0303050603010f11070c05190501121509090b0a1a01050706020405090702010212150a05060d090b0103081c1806090f08070807120c0209160207050a120308060105030103050a0201 79
    0x1690342940701c9092162191018042880070861200080d4440c00c1b08a0f00006c020a0206541c20154083c001035031140d0840c501540c1443c0055406078880201038248030f848480e00c9090381c070a01813190041866280102e51f04880b8944501210002040c08411134a40300000f1100d40c50b144031080034000a08240340d642d080d40c188440079100300c2d00280c1d0070078201020306c5130103641540106032050b0f00400c00d080644074a880a0113000303580880300e0344208441004c0c0002c1c030b022802401c84503e405c00000c1c6080880c0c0e074080c1d4200d002da2065600090208042016500c0a1166640041c200a04100340b01c25000c280c00d440c081c00a002c2d04440c0d03a82c11001c104040c96113207042da6a0050425900c0e0f49062515440a9005c83c10071100110956050400300c0d01511090502c190300911b14241650749081c000c000500040391b03102107104500740005d894441403141c1026048411030151601170a04000c0d045010250000741001000c20040000c640040f61504010780d091a01c0c80d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 96338021 1250 96336771 96336781
    0x200a1d06120a0515060102070501020a0302070b03060f1215070207050a0311041104120501060b03010302061608090a061116030803130503190f0305070807050f091c0308180a0f030305 80
    0x100c2c1c4071507038030018101d12426000d00d40340c0240326402403140f1801d9007200c4a15440304c3c01282c039a03a03400d6004000da4041403081c8210031680b03000d10307480038011305040040340c618000180420b0340705066551131341109280360014440340105980c0058140010040145890041603410916100c080c000c00b4030810000d0480c0c0d00d03600a04900b54009903150785039501c4600250781005050401c64042d032034a03000180249501c01a2412250000c100d1414900700360982c00003684d0030b4500300d03010a030400c0042502c2d074601c030903400035117143e2b41e07540c105090750f90030140b80c401a00c01c5040c03004205030341003000800d900120703580141c1b602d2841d00e04060a242040c514051b40d000d800c035500498407101c036405d074060740480f903000e11660144082d803500031003500c2680f03040c0c4e440400240104100b9107403440ea98002c0c0b110b00409084000d00500c0c00ea00d42503485600102103002036242c4c8107104c10840d803020b40941180010014010b80102030f501c919500700880001414141c585002078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 96339271 1250 96338021 96338023
    0x5040f06060e0f0603060106080f10080316060e0a020a060f020307051e0d09050105030601110307020301112a1506030a0b01030501060602010e1204030b040c03200a1d0612 75
    0x4045168800300c280201c0c0d4a841c411000000d0444084034402c800400050442c5000210703541242c102c0c1d298040151607404480558100041110502459040307000a8108040000f05007940716080700e07404070800c5140803000e8500724110060395512802c045405070b84c91031017084c00c0710228205288855280c1c40b05900318082c400020300345015000301d907a480700d440c8041303c0884001c24180d98030b5008682050322805618012140051024000915194040c1160742c02041190007101d08000e0160300003800d4074586d280300e01c2c2c611300c045040c24507521424000c01c1400344010b01500c070718400444950f0b076180e411711030207503107444107011070000d4400f030051a07400e83c1c110516410039a180c0c10401e01a104500c14039006600e004100c0c4100903000c41d00c0c800100c04200c1e690300c1d0600c1d50f11101004107001c0c005441103401c50200000091030b00d01c060303801c0b200c40d012200d00413401e442041035644055010b04289030b0b900c0c0c0c04034141540450400e83c400021547c4214100e8085009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 96340521 1250 96339271 96339293
    0x32a0503070923010608070e0303160201050a03240501020f0706140d090f050a0b011208070209090f03031009051b0318120a0c110102030c03040b0a031119031409100504 74
    0x50f10381810140008a44aa406028144508022344501400880b44030515941e44246107400c1080040d02d080040150300c190000c0c0000720701c51601044400300d4041c2282801440380c2500140e1082140c20446940c05000300c0034051001005881c64a00d81180500300319145100020a800005110882810150701c00750446400501e041003464061a000d503443c2049a001e42d03481080500008918110340c0c080500b81d5440b0340c556040401c6503007440036009015216045c10300441d8101440084104082c5200d0382c030049595450524040828048a0025000c40380400c090020810388a050000f180d400480100380c82c2d910941040009041c1100d0708030394002041c00044808210794480402c001365802045014445c4555800680e0307a4414507000a8036900180b00030040345220074082c0c41c800f0818140414129030000700ea8030550710400c1ca6070b41040d2114450f0b56415030510900c0700400c1040078681250805e0480b503a034a00080710078904d5692210006400c105400c041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 96341771 1250 96340521 96340571
    0xe100b07030903080c06061f0f0c050109020415060801060e0a03030e12060106030b04060806090d0c240e1902060d0f06030807140607080709030201030c050c07032a05030709 76
    0x2c80e5140c19419451544541c0c0c140c50483c4502c8008d4120803003012040d43c200d445c10420f842c2c03d605a030b04c80d0000c0d201401106006c0d01c96540e20301c500c001680700c5006449030902c1000a107110070341800005480000706030411010030a03404014a01c0b0385426001c9000d0b04e4042c1058030004400302c0001e80350f1500e030380a0040354065030300001102c0d5059003000a41603002c07141801095110300106076540c82c1155a090241d1007007003220030880c040c0c0d603a80c2409010b002e102c240064081d291b41540c01c25484100200d0b5a2110010315104003072010303082035018180054214641c1da0006007403030042d9440524125070320605d101610042e9400350004541c01403845445a0799424002d1107106040b406103001c2c01490000748002e88104503191080c0159241e100409095400440041001d00109010f200c010410400000c1c0b0400140c0d00030351282c0c01d411189803940440c04c400307500005046420004540c0c3c244290350780402c154007512180e0318001280c1190750982c04440c020111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 96343021 1250 96341771 96341783
    0x209060409060e0c2d01030e28110108130201030e01060806010b040905090a0b040f020402040509100801060f05030319020c0d05010b040c050313060b031e15010e100b07030903 77
    0x350441a0000402e0000c1d00d50000c540b405107000c0100700685191780c1e6044c0da208500400d00498410358080e074007600c00c142650040320521700b11fa2100005c42144102403020b20001e0028a000308481c40403142030f038000c00c0c44c250320706003000d0034802e40126811000905240e1a18240c0c035001c8000d5100d84d009001c0b003000c80b002c9580d607010301c01c0c0c594410700030030034000d0510b000156980070010f003c045944d844a104007403603803039859585a07001c02c413078101d92080c1c080100003503d6a40d40b082d14043c180c0756440f240c0ea14500010182111016417001c01030000c100802c00090381c02006a9201440820382c004125136909822800c03d240741c850725501c032942809004c2440700550211403860b10513241017100c1c0380121025101d500080701d1a511001e58a103070980020b00c1c0d900900d0710400040c0031600c214155580740f6014900107000120264828080c030b410300494944150300418201d0440840b90616110640d115000350203400c042a00c00120790b420944500d07801d030015030b0000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 96344271 1250 96343021 96343031
    0x3020313060e10050906030a0f020418021206010908030d0b240a080912220e09031c09050616020a020402040b0316020f03091918050601021002040f03020906040906 72
    0x4001401c1c00c82c540710040d000c0c100351031080803024041d004403481410010500c47c00d550324150340001034410081e4605400360240000110441c4415605444a4160f20056101c0c42d2010b03400f40f1515004102a0411039010320811030801c0c0441241d61840500301d012400072800c0c00800c81842c0492525607451121b100444040040b0001901e405903107503640140944695040710b070f440340c406008000f0a001001801704c0c00401e00b031a020300005002072024104d540b00b07210b401c0d10303804589180c1c003500700080107641c1d00030f0041c8500d203201b007004040004038965150b869855000501a44002800d070510001da40e00801910340c04a0380280250355594480d1300100c0690000e03524000c1c0300b140c45d90042c182c0c0f40081402c5a2540c5c0c103900840c14101c00204219140280303c00000d805101d8034008285034030003140c02ca49140001d00c010426040041c0020b160002902404208070710500003400450302548100302220780484d1041499141c2c000042c0040080d5080200658a81 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 96345521 1250 96344271 96344279
    0xa0e0a02060f120a0509072c0103050d0210200714010f0b0a050603040210050f0c07080105091203010e0c0304020105090306100515070c0504020304060b180f010f0303170403020313 79
    0x4000c0020044150424110b13883d002660000da9000361758014480d007100d4030a2000c1c0c0e9100c0074203000d00403031400305c0640141204090402a00a0b0410340d4141c00114030404650340420001c840c0401c1c40c50204200d440300c0380510888a9100b080342e9003050006003440038400c00c0150360003080071501c000c10010540300342c0319004201140400740281061751001405107004000e030303445550040c021040821100710b00f11050340c003400700c0640e810300900080d05440d00804c03400024140c07200001800381041038075245049045822009041000c000600903400d8200b03140e030300b03d0502481e5944035200c2c4d10041c1c0d00c50013402000e43c0c252003003104010f120348110824604a139000d0b3f40c0503501d0b074030130320808403648070b0a4406001c040451000704401e040c281d00540e80117000da200041d080d0601c0c000942c000c041d80c403c281084407981e09201e03960310320000c100e0060480e5089020161b1a51b54050044d5200943c10b50a41002d0350020302814000d20803502d034080d80040c10103a032525 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 96346771 1250 96345521 96345547
    0xb09010905041b0b0702090601180e180304031203051308071101090501030209010e30030d18020907030209040905030c03180901060206010509070537170a0e0a0206 72
    0x100b12000d49200045081c3d826010302c208100c14291110260301d146040f40e9074090000207080500301604000140e0f202c01c90725500e82c20388602400c003c00c00b600803400d10311074444c00441c420200042c1a0410841000040c0c200e03040407420003580d040106242d03a41d19008d402c41c0d080320001600302d6800042c41401c000720603401c01c07100c217401d0301e484206a0720b94004400f2409805e00b020b01042c402c0d1441042ca2600813850007080703406940140340640141c0102a031070b803002120304401e034404038021000310858040e180302d0307966603030066008207900e8000400c80c0300040e01503802d066001a240e10b20fa143e50304488225034101013203a0b035603400580700d241d50b50b10040d25242c0c0b4800f1911a0b8015141a4040c030341259190f82c0107203200c0c1d08003010415140e10161082e070501ca401c104613210840c0030303c481e800c044c404002030680044070030302c52014411090f1443d01081040d00440c004804c01007980d0307402041c1d841c0c0000e55030050f444001e00c0e013107038804041d6119101058038622040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 96348021 1250 96346771 96346781
    0x1707090207030c0506070f080a0b031009030c031b0302030a080a021b100b0402040e2d0112030905040509060a05070302040519051f0906120f0903270609050f01030b090109 75
    0x1110b1303411600356a45000301290304044011085002403000d0b40810b1988a05400070090b00d08001c068640340300d628108007084410b2010202c0c0403460892f5000141a00400521104465102c1e4000d025105030b40003134582c440c581001c41030010000c08520801504d41c1660301d6203003440d081022000d06604c1c51030b0f950130745540000d00c4030f0134010300e4403076030805000303076000c58a0403920205a07843e5400042e160f90281312903d42e21040c004804001c80c1c071030300b802500030010801007514041c180e0600500708200c0d40c12090081c0d0a103c244425404000343c1164003e20a4100142c0d40e181c81504034041d12840c6d00241d4060b01100b0000f1401402c000c88904880701295503441f2506c0d454000405070312f000311b8040228007010b00c1003094500940c804a18903044480000300c00c5041c42c84031049030a21303136054002070300300c01d40c60301d4240066560202e024201d426102c1250314103900100703002d400307000b400d00500c180c55907401d0a9019030490740b10100007c104071021f60711110000c000744 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 96349271 1250 96348021 96348023
    0x312040b042a140307050a0302040b0f0607060204060f030b01020a0611040b0a170a0b03060f04020117040b060f01031b12020c0d2705010f08180106080a021206101707090207030c 78
    0x90f402c024901e0300244880c2100c40141066150b68a1034007000b0040c8402c5000030b03004814441442079980d919002000c800d48076000060701d89080071002400c1003606401841132618050f010003441ea0001811411a90310010210340c0e86001c2c0d410b50f81d14005c5030b00400003c0004030fa44548290010f0054002480c0343c00074091554400d00da50301039038a00001250150820808503080307101d0000740d254403d0041c10a92a6160001203401030003030201e80030741c2d4511404c030078800686040060b00e42218000d01c1d0a0050070082e904140c11b2034002107121f014050703641e11003000c1e5103950701a100d034440c0b04820b8904154812002504400040c80c415614800320780c1d816000300f40036030000301682c00c1a5500c41600061280c1510440800b40298000020480101282c00c0090160201500300340000d04030840e1684188404254699900803c54001c501042060070360480818100c86403515060104402145580d0030400d0641055a4903030000540106150304000c10f4070f011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 96350521 1250 96349271 96349289
    0x20d060905090321100510030504060b01090f0b18061801180315020a020102070b0103050c0a05030102090306270109050c1002010e060601050c0f0709060311030312040b042a 76
    0x1d5a16030031065140c2c4250380007403d1603151029010440036402d1440c40e806280040240c6050792514005036050443c0100743c07001039100c2041104110b02c5010780c0040b95020300b08102c4003030a202030151050303401e0084081032070000c101c2d40180d140c50b0509020500c000b50409503140340c0c0d038059481300c044440304d070390200b02c84180c039181090f40120140f04481e04452044e4800c064820400040d5000b403048030210b6400b0b101c003801082000782e05030300a602c41d000802c1c80b01c07494000d004050b1615407003d4843d2b403040c044d1851a8402150f203503400940a000c500b4203a488c0b042d4913400440c0c10103402a1903207041441e404200c400a00c000032003004480151828214040813800d0b1107009e10b29407515040600031503441d501135800f0705120315100c416102e03040c1018190901d08901544165003254540e031007003090100c030b201c05245400003a005185041100c060000f1400d4018100401103002ca00c0003e0030310541d91020481e00b5526028034105010b101070030940b1002d10302510881c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 96351771 1250 96350521 96350531
    0x2030a02180d111e0619030c090305060c090d0b07030c0e040b1c020a1d01030204060b07170c0a1502090a0504050106140309030405040915200301030803100306020d0609 74
    0xc1c5140410307004a8440d40242c1e803410000703000d010720004a2454181014240b20440701d850181d440c5405045000d07400300d0b4a40c44c034021600002d080d56540f0340a08148813140c08240003040000c5002e640c0b000c521004a580e41c1442408150f60407280d44014200811841c14044d26542c96000004d4500c025595111400040010002100c0e4641029a48a0404224420191200b00c1c004028500040500c03420351742d1840c607150344680310541c4134180140c410040c41145094490301000e405c0d400200d5013003460582d102d0701d10703100d99548196280e0001c00c060041c41010407048083d154050160035a14220340d5600d80a504189195071151003001008113147c20988189412248103039142642d201c48106c951251b0344c0060b01801047c0030402000c5180c1d100c500441800034410f189080c0308402404190040b65130b41d00d007000708003503500304100b086544001030324103481d0010040d42d5a034480c40810080044a175100900e101d001181c051000052640500100c440c00c0c601070003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 96353021 1250 96351771 96351817
    0x10e0a110603130b07030b09090a0203060a06030b01180e0109060603140c030601140316060206090f031602100329030d090b120402030f1009120219020108060f0402030a02 75
    0x81d0008841c51454008490070303142c08076000c01c1000d078005c204c03401d002a03000d1510703003c100861411128a032880c2c4c800070382e402c00c505003042005d0380051150b0041094900f03650350030410030b03418441c002e807402030300c030354003504500c01d0744200201f01d0440c00802c42800130f450310741d02420300307840140c4811050750103065000c840803c0c5c800307907180c00802500c440c4e03013400e000f14403400c40d07809550740500c1180084c2080c4590240380e28017410707081c0c009104502e000c80310700c0c0c6001c001c4001404035403c107001419001541d00403400e51150304403404400221384100860003072000840c0b920800d0403840d42c6452802800c42101c58000069090310300301040000c0650b4a0310301c0c1d10440c0022242008210782e01c110345080150402e1000b07050391041d00c90032620502d4031600d8840c291440780d072011036074200110301c09181411100e40c009410810003107040c0752180045100040d0501c070001e0000740301c0740d41c0c0d202d0010a04500800071901c0b400c01c0c22103a4000d401010b04046895603285c8042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 96354271 1250 96353021 96353029
    0x70306090f0b0a0501051b01110903060c0a020a030509011214070e010f02100f0b0a06110d030603050c040509030903030414040608010605091f050616170a230408010e0a11 75
    0x6542c100018040c0c1d500c0c2881e00004481c1907120101a110381d417500803140c1d29054080c0a1550505c42c4100700c00e8841407104105030820320003070010f1000f1035040010385142e540108121043e16014105075440d2074020780181d40c20442000d080d41402d240124200042c880000203074011413a41e960314200081a80054840c40d4080d01c101d8090f9000b04458810300d01c0d1500500e096161103040801c4081400300820540040d58000d0008500c10314141c00407400200004860300da000d00c3e0030b004561950b00c82c2610b6070303c2c5120341405103484400240350100104101c440d15940582200e585503680c291215403a0000d81c1054411410800d001070b0110f014001d84080d103c009100c21701c1c40d1a0400381900200c080758802c0119a144a00022617a03200030141c025003010b80c2c201851031040e0314007201551101843c0b0400d000c010312526051581c01802020f001012500f0780c2c18404100ba081d0200c0d00075075000000543c20061001d04a03840410781100c094440c11141c882d2040b004104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 96355521 1250 96354271 96354281
    0x305160305090a140c101d030708100b04090501050f04060506030c0609010309210f030f15171908250302030a12090c151b050c060f0d051014090c04050108040503040e070306090f 78
    0x80cac00d940e4000601a40380c3c4140e60301004000c03a0040000032010700710340d9185d095078821106100720401c01001c0105001c12405015405601140941507100f00c440016249000e00001ea9041503505c201603020055a05c800d01d17880140000895000704035a080200700380c502c0180e0354002403c0c08028180442c150041d0007080403003d100c0c08806042900e00752111040f80303c114414402c03514001074403016040011945801610015a80c054482035000311201a140a002c0340b0b001d5165000880c3c0d020054400070358941c907140301442c2c81c4034502c802801c44514041c0c0020b040c00d00000350250401da103103501e09026140e61494000a00400001480d0018042c00070303008403504128030325110008010400c0149100780c20101c1c0d5040c01d400300d4204464581c100b81c4c944c5810700400101414100184000b08c0300340c00c442c0303000f0380010903600a500c662410b100c101e002140400005000351070180c080c0c1d041c09805858011030040107441140324844440d803510401e004030b46010f0182c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 96356771 1250 96355521 96355529
    0x2010203060f1203070615240215130204050a0506030d08010e040602030a020f070c08100c05040b091203070609030813030203071202030d0c0305160305090a140c101d0307 75
    0x50b064094094406000c9071018040c04080c0c0c50200300614000110f03d44245400c811540007940c490714100380c40381d00c0f00030b4884040c030019100c0090b4080d0141e07000501c1203d5881c5500311900c05d4688600c4240301344401c54009500504007001c01031809200d510181c8907030011800c82c1c40680e00600140d07134119081c021100d202c420400010f01255542d0020b540003d0704210051415402c984280c1050700030b010700701c1c1d201c941c03040200300813001044030f107503043c8065400b0000d100c90500064078900c5603129a80c01d842c00810990103d0782c400d4041b000d60011401542e5550150b03241650007021500801c0300070820400200e80e0401401280e000c9030f540c0341d0011464945c1e03c1d1209180c074824080300c1e000718070081050010030700b058020344040c060161400b081e14180b00c600c20f040d07152000458410545032208004450f080000c201070b9190f0000319003d210207081040d181080000c0320304942202a00580d980f90300d07440450455041010751180b1200e110300410142c58486a101d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 96358021 1250 96356771 96356779
    0x1d0c0a091e0c02100501060507060f020306030304030611070203120d1104060c0b090c150a0306080a030516030e0d0b06030c030604030f0f022a0109080a02030a08070f02030109050705040c0201020306 87
    0x7210250030300b640030540c400442d00458803403483c207802c803609946003600404d000840c0480c1c07120401155000d1245200c03041d0388c1c19802d520301540803035505e0140d480f01801c00c5483c1e0000d4a42a1031316002c07111000d030041e055414000d070319084520594404942840d4107840c01542c0c0000300500f200396802c0c1e4400759280605050b103a2a00d0341000d002511031b01140c0181c41001e000c3c1e0b0341e082c0c42c942c94102c0222201e52501403a440c050100d40c040c4e1300c4031007107401100b07040c0c002075440030403070f01e81c0f545800d000d42105446050890b200c0c0c022007100d68210f030007074800e1824880300f03903c8144240b0f0210308407142400d05030189902c54506660050205100c07900745e0507074074086c4040210010482c4111000803881045485003000f15042401482241060341410740d6400b003011009881200014100021107602003030b038964038400d01404000b0044382000400009850020009030001e00900c00c0366580d007032a5480c1d185502c03034a4419854406002403171070047c001d4902c2448018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 96359271 1250 96358021 96358061
    0x103030906110d030509010213140f030a0c050105030403020312090c0901141f032a02010b010903150c210c0305060a050306010905090a02091510140306131d0c0a09 72
    0x10004d038040c080107004100d0954090140b070080d2045604014000c1041c48000c044200b101001d01100032080c000d69402900318101e8100815104440d0301b00711082843d25583d40ea4560800724190300541d00400c14608111003444802c000000d04c149009104990400550342d0b2100c100480e220306020b803541000d4007034200c030702540111a0400008205048c0070800c0c2010355601c1c0d81e03030035000400c04a001980800c40c1c090039030901c0340024148080c01c0ca0a8518259102c0f40c0305c84140810940110b03464109001c1154807644850003a0000744e40038600034207440c0240c5000c0c1448030102e2000914210004841d0b2401c0c2c0c5420303040720030240240c10242d08142c1d000024160042c000482449080039200058031816500c034820568100081e40700d5180e80100a54401d18100300341c01c000150180700c0700181004222a0048411030324550007403d20011031000c0c0980511440b20003202c1c0c0d94844e052000812290350707416041350002e640d2525100c80c80121080205060703291941c43e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 96360521 1250 96359271 96359293
    0xd0f0f14010515030c04240e0f06060a0507110406150c051501050f1e150c010501060804230c040606050d110f1905090303030a090605090f0c0d0f050102030f010303090611 75
    0x1ea07014590a800010200d4140c940104840c7c0b582a042ea00807603e8010070420020b0007400d203102c0c03c2d0441320441d14540b80282d00340006203140280200075120505c21344d00c5d0000c0b592141d00c41c0c0700820020740740c02c6001c440c000c405411400900010740b041d014045d909011840038581c0c9505a910050106400c40c024209101644101050600786140580c40d000706035500d42e4a1401500701100313155a441c07110125003825a141a40090207000030741082c4000910021541848410700e11424814003681c809200d14001901e00c07165086480c0c00c001180060b40080184031a0045c40014804104e0340d4620325034900c0780c586643c1e11440c2c1404240e41c03d8803650741c0e818200100f40342c281e04101580300000d065500a5650303082c800d90b41c090b0502008030314028507901046007000707440080c0e801e62140e130325851250f13040340c80351289641850410121101c030101d11504540210349030311b0960a0303000c02c15400c1c0425004241074101c001500e80c826400c41003441780c001c001d0070000271a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 96361771 1250 96360521 96360529
    0x302060d110c072408040f08090303120403030605031506091f0801060b2a070303050a030e190201080609070518270615070c050d0f0f14010515030c 65
    0x601d41c10307100100100b00c00c01410304200300d5203001d4140c070440b991585030a83c072603440c419520703c1c1c07038014824030508100104201d9008451510303084541943d940c08028000703819449241c0f40605402600420300081c90360640c48141070381d03001d800300c031074000114044c0c0503000b108444166008202e90001583e01800032034103121000c03c15102d2244a4036882e20f1403d4440c10b40112044281c003140c074900700300b0780440d4050785104500070011803240c2d25413095190081c2d4040903040c00030014569403054465800b07054500500340c00c0d40d9840310038181c1c101c500780c903510040c3d00149968010035003074a000707565140a041c40342c03902480c1c40d07401158800b070002c3c5500c685600c20001360f2001384a0f070300d4603c0044481100346140449180c510b0400446442030b810204988005000d40000070340342c07414070383c00d440c400c540c81007601803035180550f010020040000c000c0d04042c05400100048030190055102d5030303800a01c9140d40b10380c0e0640c1e00305107541e00940c0c90340c841e4031040610b040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 96363021 1250 96361771 96361781
    0xf0a0501171c1b08070c0b0702030a021509060d060801110c0a030e030c0405040b0a05010f0506041a07020406030f03120203070f050313050118150b010e0111010923010509070302060d 80
    0x140c14202401c002c0f00c241c00825808041e000103440d5400001600b1041110000ba41c40280c07540010150500107607402103955500c1da510006d00880803c800580c80203492003d40321080700c001c043c6552420007109200103010703548620202c0b0f40c01c1000040d1011088010303201176240d600c004146007006500c0494002401580054060003041c512a4141d1518081c10b4400c6001c5d0203110f44608040d00c47c44100c43c0c050f40000c2088001c42070601c083d564a13011601102d10045034500c88c000e5100b1220501e01c64050001d40c003500e480400000c0208158054203524000d454542c2c00318488043c132010783c4422151740002078841c9900000c154040d034041c54000710038060440072005503642c0c407821500d03445145038000107509000810800401c05c120385080c030540c0244005000c0c5030000e4031640b0000a420305112001540541a40c8250700902d4240d411649040407048212104d425200c6812074040071942481700041b11040f0010f2440c4c1100d40c0600a01d16040d840002c501c0208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 96364271 1250 96363021 96363073
    0xe030705060f0a030212040c05030f060c0f0d0b03010f0b091521030705060108011506020f0601054509030910050906041a130807060807030209010e06030f0a050117 72
    0x681c00c3c00200f408604100105100312300c500140e02e03905003080e003054941113130002c0c1c0d02c46c194888010480a00d5000c1c05a8000325820342c0015103500d40304c50707000040c10310140e10a40661808001d841c200b2913942094403c0c610546516134542c40302002c16401c85a140701707041d003042d0f02091030056040c0441c1c161020341c4c6580266030814605540f8039003440020390001146a44a01c000703000c2140603000900100b5035400145209910b0500054a50005101d640c0c4034161001d541e800403803000c1c1c0c14004180366000e007400b01d10a0f6484180f14050000c80d0f00c1d84070f850310b070001498058000212003217420010112010101039210840d180d900c40c020070758010005000009003582004a050080002e0035001519500c1225807140215003541c020101d5510808007088081d401c81a042d070090618078026a89400c00c40c0140c8102c0441500141c01076400401c018102054090312400b420706034000307101c56640c2e800307484800d02c11000c1c039041c0f035040104240d000d202d042800389141c0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 96365521 1250 96364271 96364277
    0x50307020c1905210705010c03170705040e04080310050a1404090c05030f01090b07080402010f08040305041a030711010213050d06150b0a02010605180c0703091701020a0e030705060f0a 81
    0x30b26103600200d001c0200c06036101c01660344100290348510001d1000c0406844203181981a080030b94070300400c18015503000c54116090500411071280c4500125000707040e11020030041800c1c60b142c5480503900c1250702442c10b070505900801d60b4640b0200d00000c03181a40c03505071034621124108030061500070000c403030003500040c000500b61024807003011000d130410300015180c0041c1c205014134480040080d0204640003040000507a00302001c03003007103070440c070f000c1c500c5594600e0f0070f489600c00c40d0425003861507a5607800e410400c0c80c0c0019413040d0f1450b60b44940c500b0ac0f100409090380103840c40b40e021a54031120030300950078040d004502d154068200403900603d185107006000c10142c000341c21351a80050390403101a02402994000c045c1a00d603469040408a0790195040d13026020043e45400001c00c0d1050511542014001e0401d202460240b505507991490007580b110105001052a00211403050318010844204640b00504101d28245003a0b11581c031070391207001c0381018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 96366771 1250 96365521 96365569
    0x3070c0501140414190f1404090c0b0304080903031201140907091505120106020c0a0f060e060705100e032d04030807050f0d090e09190209060120010c0807050307020c 73
    0x82442c84019610060401031b051484081c00c100c8100d900f10142d1801500072418a400c40c000215a40ca0041c11180120341e2140c89071103900e000c0c2d0051152141565040c440482c10100070300c0e0f07141d0702d14101e410f04c0d00d81ba10a10094001d004020604039004400f05000c0101080f234190303190101204d508440c604680341104003400100c42260030380007000142e0103040410001c7c00c20001a07400f900750000d0038401d440c9000c1d0010025480d0107010350113240003050140c10400d041111200980706040306104032040b00082c0d0766250802010501240c10307403845074400e9004442d0245c8512540c42400d03141508640720140c0039403040d88104c070284120680003006001c1400a2411070741140d03100b03405280b5120400008032030192100800703401500d9003000c000a9021602c100da9410381310420140d0398203006030395510105e462008014045001d100b20b241c819800280301d000641c0702d540507900c8030007085031140821900080980d0004e4400304281c83e207000b01c440c03210b00e49259414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 96368021 1250 96366771 96366799
    0xc0f0d06050a020405012c010f0c020d030c02010305061008040b09030403150618050603060a0e120f0c1501030203030a0c060204120303023c13080a030203070c0501140414 75
    0xc41d4802c85055808543c08101481a5030344240a44051100c0c000c0c840c1a0350010640f036a1000540006141441850110380c1240c03030107a4296668103800400861424101381806071603020880d000301d000a240000040040c0382064219000300010b941d0348071203595a50720461241c00141181000f44000c1c0000000030b084000b03440c506005840c3e01040c61843c11204100341404017200500250a00b0104011910001103c0e41d0240080e5000f0940150752150b490401280c00d0040c40ba90f80001610010800c91344000c01484104000301c034054010a001d2420301c213003c0c00000e42c10b4004112101800744150241d40d8158007940e401490290340710070301c1a042a1390703c030840c0031035004030f2041c51004884500b0520032503113240180031880e000c0180f540180e402d20843c003000c03030302040510800518191400203019a40c00712000d003606410301179500d82140c1d0085840711002d035008181544074410400ca243c41000300681000c0c1400c132404100b41d1440411034102c00c03040e110351 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 96369271 1250 96368021 96368033
    0x30903070f051e070b031504110c010c1e050a0f05121602060708010501090b1606060b0304170403050303071b02090a021308030313030503061314060906030109050c0f0d 74
    0x941078819402060741010340302c0352400182d4440d5114034030307400000081100c580c01c07100306c03075104500303080d4500f5580c206400180140090140401c401c1c0e40031900c0c0c00248815030003406905899100c0b155446a000c040707265400c0d2164442c0c00040c020302507810103900070b4041280702c10990503c41e0401c400c20301c0b052896003007220031080c4413405006a5112075014070001e60130102e1031820340303803a6050000180a81d1000d209110b511000059503a8465910015000c2c0950f844242400040c0d40c9580189c902d41046c0e0f42910700850100304c2c131501c80c000700c0c2181d040f40d9010018504659501001b5100000c03981000c00040405060200043c0e690b1204a4841d6408110058543c9150b074007030052464035400c552480d60042040c80302c41415141b10030038869251400701d640340c2c1c44c4008280071030052850010308030f0a080f03154071801501d10003079114034810b861102855460b0802c05081c0c60160b980030309170b6000101e1281007801c01c51902c5042c00b00182290040990982c1c0e05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 96370521 1250 96369271 96369293
    0x3020405041a10090c020c010801030b0901062d061b08130305010f09030807030c050409050c0f030c0405040c05030708060f030f0a06020408060105030a031e09030f06020901020106050406081203090307 88
    0x40c10f0f81c54155042403041000601c0303a4003050201e4401040c0010941c1d0020380889018000a03042c1c4507540700064054000350803074006440c00c032542c100c0c0c148107100d01910480c1440c2410b461080b42c40004500caa2180d10703030803006941481c102a00d075440e80c80d5500e140e0f0013020f503030f040b50182e1240400415024011070718a11030070307040010300d05024140108aa00041c040004040c18242400800e90344082603c040d01e440800c0001c00c0e854112001510388106008120704401c0441081490600e6a001d04100c9405035414003500d81000c0007103034580300440700350000c28001d0000c030790740d030500002c0306a0540b809011194104101d80c42c15240021150b000c54940707800080a02042c28203004181c01080254010900b21000f03940103080c1000c1c581c40740720244a03180116000c0b91007410305500658005c83d002800c1d5140742000703000f80d4070007000030b4091341c2880b10000300d0741030074414041200e0080000d8040c440041007080c2850b84041c14a041c03520081c085c0700c0125881040c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 96371771 1250 96370521 96370531
    0x11010f06080c0f03031c0f0b03070602061027091515030507080d0c02060c070506040906090e0d050a0c020102030f0d051008191e050115080111040f03020405041a 71
    0x602d000440541000410b00511070014001c0d00103009031101c268400d005041105440307280400c00d101c001d04034400814a42c1d038419410300c14541f00144064001c2078190103489911480160540c403501e07000e06a4504040071020403c420f1403000c0c4114003a4000e01c4001e1045508a038140000c040f82c000750740080c1c500c41040c0031450002c008000c0100801d44c0248042c3c005052400550b89001d0461205510007a000b40c2c000030b10000e40c41d001b80000030150500800709515503807504440c5000300118020032005503d41090b044c44494001340070f81c0b809403940c0d950303441c01d40c40301000ca0b034a11400108906610052220000c500c580e030b4007502042400301710001c1c141c50880d800754940040342c0c1c801ca006070003c080d28502101000c4e0850811500f03c504180c0054030701c3d11510a00c210100044d065501e001000e1503107100100035242150002402070008040c1c0e00210025032040d4881c0c41200481c1d03030b00c00c20050034190445036025015240c9120b400e00d01e0492400d510740b086074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 96373021 1250 96371771 96371773
    0x31b0105070e010201050907031b0f09020702011106040c1e05060c0109030807230a09080105040302011401080705240c240c0702030307030e061c06080f031911010f0608 74
    0x410003903942c044904645440709200034481e908100583c96101c03010342c08064407640c2e80c0e030034040c808084011040020801d02103602440d130f903200c0c0e28100035000414128009110b8840c0d00c40514000a0028000c0f0f800c400380100c201c1c5001201c40c0340f0440c01d114101d80e00c1c0c6519000a19940310400b91101d903a80c43c001041c80a11454010140c0340000c0c421410b00002c6000c190b00b02220603904085166480650355444510b0ba070705036910703000c0d540b00340303469820101004201907040d00302c17a001442075180c8191a98070703885076644540e071a005142d0040c0b079914104891028003480c0030940c082891405107801001f144003401d220420800e08680150000b0a09851403950003040d48a126020b4031400c0ca011940081d0700c80c458100e022b02081151418419544e44030411034048614484035807030412010355000001c0c100c1c500c1807001a001d41d2104140c11304000c800c41d440d0121001906a0b0311502c0141541d2036001084bd0b45081d6580707003941a081d000790b10680000d8000d09c1c2c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 96374271 1250 96373021 96373031
    0x6051509030111040f03060905070e04140c0f062215080f06061606050a150f080f0303060307030f0309090603110f0f1f0e0a03110118051f02031b01 65
    0x30505081d2045841e03001d8001c402048100300140c1004c0021003070f07075401107000c2100d170307018101949014004c0d00941000c280140a200c00c0044151021aa01080d003060311410100e41c4100004019807040003034210784200580c092115080c0120024418aa80d903456410345a000c0c07419413801c0d030008a008150351600340401c0a4505034541d030f11a90490b13580345001e01d00c07036046101400540005289d292500007080503e802d1f40c012003e84404641100c030103560340c034061100b1403058400d144035401981d842d440d030f4040210490b1300c40e0b00041c0043c881540307175541d0083d1180c807100044e01004a4400701003103070717010740c002c0c8402035009107046500ea050000810507010540c24409100d5540842c1d4165941c8401c04100780e2000e18101c00c1c50940c42c00602a04c9502034012400d50012880c01c011040111280307a006040d2801c0e81e82071901106402030001a8086000c0c031a8400b244410301502c41d003000e110f5101046161040d00d040c0444100000e8040c0036140c8034440c903944403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 96375521 1250 96374271 96374287
    0x60b030708060402030703150f1a0f010c0b13030c0602030c0403031106040506180c0402070c0e13050a0206030a0209130605010e06071502070516090203010317040501020d0e0301060515 81
    0x100031840250024002411541c1840d5000a80d1415948001002105101809040c1c804d003503005140b500c02c6200240304408041082c0304603400312482c018850056901034102c15481440c0280c030070380d070250034080140c43d003000203940d818051500301e0402540802c0305000a40d180051801144000b8840b03864a080d894090001d80d40245502420351001040001091001810300c4d0071560316264503c6011a00e2070a070304284000c203000c0e03003240c0000385060402c6485014002142d050600c02d014540b0380304103a824a0b01c80020250030365200706000360261506200443e00032140d03100062074003445401180c0d991540700300c0b00800e03c0d50f8001c01c202c19600302c6101c40002d5411150186080a07940d01c10300e18090403101e148841e035012410702d003040400c11098040c9501e40d000018140d030340e0306190740654400d0108448612004400c025010044800ea81c1038030b1050b00030705210342e80914201c8401c285090140d41c0344d0f4851400040546801c1da00380c0ca60b44066600c56a180d00d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 96376771 1250 96375521 96375523
    0xc090902090a0207030c1101020c1503010806061012050c0405040504050105151c0b06030a060e0601080f01090309030602160804060207140d0519081207050304021806090703090f0807060b03 83
    0x4002c20b00311500b0300403c9002c00083d84030100003411a40800c100085213000e0004034a40510049456005098280e103100c9500600c806503040380d00c4042216640e9603003000b84244146c18094010220310710400d800e4100281b0b41090758001c0d0190346450929584500003801d4901c140e030b00391226550340007403084801c0041d01d5004040410359880090414102c40031011080ea44409003140c10300d04045840359070240b110805050b08441f003400b850043d10000342c1c8420302882491201e00c42c5141506501c501809000744890f00358407100034031451a1582c20296014500340103081d190052003000103162240030f04090801540185203e41c01c140311841d090000f8009903100c2c1c0c1c7c401c00810000380e000141070400d01d81400720219a119285007070741d0b403401041c00312000e03490a501048840c6500c5000f540c49070f0f008032412816000000007103c2184000d65844d034000703008000252407180640c04c8800403602c5001c480d00b0041158590900c0f540040703104036181c64885c0c04103038507498 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 96378021 1250 96376771 96376789
    0xa0c030e0a0e01090b01120e0616020c090f0c090a060201021305040605130902011b1b050103051006080702030702040204030803010603060b04080d030c090e13060507051213020d0c090902 82
    0x3000d981c00159942050188540240c0501c604800c45480f6001e2560301e034803d558580343c0e50150b80c070600c0302001d440300d2151940000c5484038500324030081c01954445c0b001680410640c4003070b00c6500d031515001c0c541d084079100141246010601004040c0305502c407642074200401040d030005807210b68000d0400c070505840e03405244074a00313288003030060382d55030b1040801004249030300145010301440180d46007134010040045003040201008240305298076204a440300f107024100d8500e03215030041d000c80e41d054400814044200506001041c005c10216401c148a8012030341810041c0d400101a42d10542046500d00f10203c010007425415001b400081c10301c04a8007810325041000c000c0d036400103c01c0304410107485d496040f0801340215050400382102000c1750b80e55240c00c458101c02c05130694021203280340f030200041e07a200e2180090b100d00522103071824003e6142c070342e006006203054100507079000daa440035410024615280500c0140400078002c00c9a2942c0d0040008100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 96379271 1250 96378021 96378047
    0x8130305010c0e010e0d05010b12011407080c070f0c0506040303020c0a120201141602040c08071106090d11120a02060108240402041d06090313140306040807170a0c03 73
    0x340720303c0521040c2e8000560140c1caa00c140c5408508040a0038041e0160001804040d04100480c0031004170a0701900203483e02d81300300760102240d8a030500301300c43c4c0302000c841d46169800180316010010341030707825445145008002070403071644c480000601c2580700d0380c0101c000d41c1c020040c5103614101140c0e190300612401c03007049401016900040e100384820b07401011f00490000d0b0208802d000fa442e001031254018008100c1e0440a00313010300440c0054503d00c0c0403580c0e008141110b082e002602c94864170080c0007604803000080c0e02650b802c00b0303000c04243d031409240300175401d84c12804040c02c0607801c65402890154074080c80503081c80c150894020410414903040071058680c1c0c10381e00e40050741500c00062400d401810029225070444800249019800500003200d00000140c980fa4411410b440f42035039944000004810a14030a20b030075411160000700441d0406000d04220f0340904c08140141401c14500c001d140c0c040303661070020a856080000c245540b0514404c0c44c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 96380521 1250 96379271 96379277
    0x4020309010605040506060a080c0c030d06060e130603080f0c0a12080609090105150105030612010603240203192a02070e0c0a09170a1a060f03060415021608130305010c 74
    0x3101c40d2003002008071900500004100d0ac2c0010107049407081082103a100c0b5900c2c0fa004c00909417511700042001c00084071741d40c42a1070040c21659182c2551068900300c0794000d005070324055106140d4841a008000341400034003a1a002d45c001c108144c4400803020915a141081407400c041004000301c0007412b6070039540c0c54001000701e440e0708841c84154a20b400d0929a031282d541c6800642e020226410300005542443c0000040008151404a00071103100701c0b80886486043c41c141280001c86001c807605045100f001c0081210768890b441c0d141c0a141c194100c20700b40c0102d020307520308030040b540040e0b1000004100144c810340030980c025030460251441c0c203100360002041d01c1170700d0007080b081040d1403a9940e42c1c040c00b0481e1640044d4081c01158981d01045601e6040350021204903010700c1051081603030034a8081081442164070020411951031144172a100075001107144950045410341140085035445c40a002c07460644100d00401604501c5e00c182507880c1e1005207c14 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 96381771 1250 96380521 96380527
    0x1003060e040c0e070507030c020f0a09020c16090903080114060408031306180e0f0612010c020708120f030403030b0a05120f0106050108060102030403170d02130303030c080103020a030f110402030901060504050606 93
    0xc2d5010848d0410a90115146540d08443c8000124207800710750241e0070a610004082d165a8000b2030900c103113111910002c44d0b1103650b91480c00a6030b070501c030003e000500f01c20043c451000d1010071481c1007000a4151420f050f12006001d01e503601112504150070011034081100c2039002d842018509100d852200100346003280b07a42100c9005000341c0b140203904000604551505d0382c082d91601d10240003800b0b80c5081d060065222410fa0182c07610500958501680705c400c01c104a030760741e5015001c43c40c074503541c0b40c60480003040207608039030303000080300000110741e03807802c04500d513020401000d0035a048503540b68501b11020383d40f0450510171540200505030381c0102c2601c0441c0c1d044500c420700d100f080c5440c201c1d684503090240381e141d0301c040354503866802005540015030f0b00c03d4608008c03068402d0400e84030614240b01c020740c07256001005000040022528003406489200b4400143c0c0400001600f660011a0303800d40030b0f0f559000c01c11491801c0d01800c1d03000705043e119189 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 96383021 1250 96381771 96381773
    0x60f0b03040b0601181205010b100c05070e010b040b0a0c080a121401031e020307030204060806100803040b09040f09050d030f0b09060603180f0d0c06291003060e040c0e070507 77
    0x41822951051b4900016403404c40c000780b000a400819500b20020040b4032202c01c4040003030062030300b10000f40c2e41440740c05808941c2e00b60581134503059480822026080514001403001658040b143c2e41d010441d5803840032000070310b40c41c042c01004c015034403001c3d003501c240103001d02100e1000340703c2046e4401500041002c501036426012224555503411a0381c001d0a001007850480560b000a41051811070002184980410014020110740f02e00d080229500d9810b02d0b03a0b030103a402601510002046000c41d01d00d0254809602150078447c0480d5580c07203505c40c46d0801c40c070700407540c0101c1d444000401c00349201e4420030f00440c0089410f201c481c2010804201d0600001b80500403001c001c0d5010314202c8410000b200d844c10301807003107030001075900400900c031000d603100c100d68441c1050f070a101790300c0f030007000c440707848200c600d400c80301c50300e1802000b48a1400011680c2415a0740e0004195005059141403003580207001070319145280c000069800340e0002c2403e010043c003401b00c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 96384271 1250 96383021 96383057
    0x6130207020a0510171314030705060613140a06030c05030106031505060625020108180303040b041103190203060a02040e0109050408040e0a0504020109061e03020d060f0b03040b0601 80
    0x25030f01c041e81c0c01e01c80d90818040550759407a1500d20b55200864520400c0030044040e0055101c05115075402e00030507038625045682c902402c50020026005200065003508003943d5040302070450020110303454030680c1095501c01c009852003401f07503444d1b002c244140724400c1c40c901c0003420300703900030071041d4a103031605200c0c004c024035510492034442011403650382c2c81d907080c0e88408200d11010b01c0b1920300c403840a0a00c0c0b8070b924007240483e46640005100f00500c1c5084c2c032500ba10400030350315507503540d0f44175120b40703100520445100c25034820b4101242c43c10032600000040d079804c1d5030305041060042501e0030700020801101c9500401041c4600340d00081000d04450401c003011500f6103a500d003810f0507009581180e646e903e8848104031103403507a501300e140101e00030b0b01d58030035194482da01110a5151480555822243c0c5110144100d03c00c1c2c0c028a01c0d050b02c0100050400d44684021607103000944c049417808401005100902c054054001c1c0c2140d001d091a180400428901e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 96385521 1250 96384271 96384289
    0x100206071701081015050303041d01050405060a0312020f0f0a030305090102030105030c270a051501020c0922050a06020a02100506010207030f1b0e0702070501020f0c0409031b0b0613020702 83
    0x148410903110300940314414201764141001e17010040549480326100c4c481d540351001c46910004650360748000000d403070305080c40f80600685003e032001c02d1603030954560b6414105082d000c0c004500c1007103415a807054040c041d0b07401170030003d0040d20503403e15080050a403140a4043d0742d80d41d2041004100640e00004c0c01d603141803064410710b8201c8944d11401c0c00c06001003c0c40308403a0024130410900202d198461885440e400c031070006214001001207a0392807240c440783e600000d00d4000309d51254618484503c64402c5c2c0c0301050340e62082c03a03841508081101004540701900421961005da4041c04201540d20b42030008000311b24005000070366034405480054803410441490006003c0140031a520011900b842c0309a0b00380d652610000c605800c840004c014043c0041c08102c543c804501c46c000003c3d03140090201000003000c100040c11801005c900388103c0c01400500302e001100e440500c2402048093348a01c1c29405100440300035414042060340b0400c40b400c0140d980a0403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 96386771 1250 96385521 96385543
    0xf0501090b06280903051005220201020a02010305150301020708250b0a0906020c0102072406050d140a020d080909010e090a060b010302130f050a0e0603060a020a050910020607170108 80
    0x700401c030511444054404242075040901b003405080d0801c400c0b002c0b0b035005a80918090742008080701000e030303605403400e0a400700080c0142c01c6004420f01542c800c6d0003180c3c104180c07440000030031070108006400c9a12031081103c03034000118000883d022054086030500300c10604100740d009036030b0741d0114120001042508416518074590040c400b4590680d03100003005002150740305407a01300928414200403140c00f1070343e0700e151490a008124020041110005000d070ba400200560740c08240c4040c00090786080d21500c440c0a000d640c540002c0e6a942d805082d00343d80d1050307100c0034403001d54016088800100410400c0c00b410348800566407017415000000041c4100940004a0107440b4549a11001d01202140441c411845100603c122642100d02815260f90743c0000040070b0f204485155060b0050000550030a641c1d40051007600b08500e452071422840c88006880702c1c010240140042e032052040146c2250032504840003102110884001507241030341d00c65031601403600c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 96388021 1250 96386771 96386827
    0x30a020a0f05011803110105010801020c0d0e060c060f040b1e0a050a0b12030408010f0501050f011404030215040920030a0905070504060602010e100e07030b04020607060f0501090b06 80
    0x703241c060220a50111194007045000e80380c1c81c2c121030034024098504030300d00d200d0a5182400014070300005200712031603285408060200c0c0041c01324103666620b00c14043d1500318802b0020340013051001d1084900c1000e0124410b20303141003505100051040c0101480d102e004000308a001c2c00c44501c208030782c0440b001c231000c070b1180d03038070700590b406000343c4880c0302d40008121425000c0d43d0004405401941c60110081101038a4411044103841c0c0178424650070408100400c441d55108400000c02e0309203421000d858143d9076070110b01100e041c4040724803a008046400c0c840f1040c5030144441c2e040700880c0f107029030b06c4000ac00c1da81e1440003a00c4400b50b41c4da145090305c20484140300c4040180b82c010000c010b6550b6440010380a442c00d44d480c100180101260f840100c015845503040192540004103c418219501c00b0394290020b4420307607102109008010000d84640200b0081d200f5445000c1902d526040c5400c09403103a00081e1445030344c0070300040e0004210000c840c1c2000084c02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 96389271 1250 96388021 96388043
    0x2b1a07140f0c07060f030f09121107080316021201050403080a020a03060b03090102070506100602031207030207050f01090c05180606070219120b0130110a09090212030a020a 76
    0x1144201461040b1400d076480340c02090030010b082a000a407800109510f51024041c0c0d040c240c1280c4215071028400901c4ca5081183e00d090561150701541003074200c190840d01c40588602c00d152468005421240320225005801c40442c1480b4015595071184007000348903d0078956400b5000150007444682c1e0194007040075800c40b03100381c00c001b0042902401d0310340d07241041c84906002c6e42c8090030035186442840040f40c03550f580480c0701f10840e440b550195080103511044122102070192020017015020700c110000300b9414480d5800c5501c080c0d0000540181c0c602d451494051140d115620940c0d0381002c20002c00d04603026154014000c1395101d55a0748140f00191130041107658845c0c841a03840ba001c601a45500746803200180143c684481d07076a61900342c41c2020304c0e4240001203040714030504000c10001041c080340e05a110300d0f110055a080031003c1107003078417550300400032580ca4035145001d6040c07501119072600e080d04040c52415440c9000070355920710500c00102400210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 96390521 1250 96389271 96389287
    0x302012306010e0a050a0b07051605060304030e03011103010e090714011d0a12052b0509010f09080607020d030f0207020603061e0a060e1c0b010b092b1a0714 69
    0x113000d04030040d1800130019400c0310784036111800582c101d508212a180b25082d02d400440044039010780c221200200743c90b2840c0d07100e5070308558003841c11a00c1074240d901c031840100e54081d120003841c040c007aa50901010780c5400490030380b80c061190311840b00c0c00485501201c0c166800b19410340c0d00d048408052040d01e03400e10101c1c0a0a0a56000d1142603443c82266020490701080c048055000002603004d10f00002c0c2215080300c4190002c1004180d08010307160095000360310410ad01f200700c0c2411004260380b5600d03541030031001c030759001c016080b1070f1030f2030800d50301841050703104103480408505240300b030b5001c9400c905c07003d40309074403070010030b0560000c1d4044210040c5032982d000d8440300d80b0715a2450040c003040e180c1403696100e04503c1490f40e00108241c0c3d490b85c1c4190b041400702045074604400099168030808079190091000081410100514014420082141034141c4080340b4181040000c000050181180810420060003011a48401207541d132003482510b070f940d9480d034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 96391771 1250 96390521 96390529
    0xb09060f0603070f140c0129180405030c1006080d02071206020c0f101407110d030b0409020604080c09010b03040b0708070c0501090303060311060705030706020f09030f0a0302012306010e 82
    0x90038817043c9207030b24005130310522400b0640191340ca003849406c0260080d00001800c4200810400b2910341114084c890351651161b0460b40540080c024002e50780b03441c005511181c108a03140c64402c05094071520b08108081c020400c1c3c2c1c85502c0284040c10300d507401d00c2c0b0700010381200ea0704090003140d000714001101e10300c103001d03070049007400d030b0101c40400c02c0c0740d907860015003600340e4603100041884000481c031500690707544070034800800140c0000d0044070310035802061081d05180d0042d9403000100700588801c002800a841d08800800c00340612400b08001d80e28160046610f503041401440002500c1103040c80d00862141801d10300d03641c503040304852651003484080c00560070045070701c0038150954050402c2d24010300007011f0400c2e124040c0400d030300c56100001d00c581d05c200316503404100c20303034003034103481604540031858000c1c107500080c0b43c003c0c220b8002d4002d821214641c0201502485008040c07a0103e07002401050b864009500800307000348850b05212204003c080e00c1e50f2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 96393021 1250 96391771 96391787
    0x3050f0d0b0604151b1101030507030b190e07050702010c0f050307061a090105010e010504051e040c26070903020918010c050405010908010504050619020f04090b09060f0603070f 78
    0x240180c0b03610344550f641c058581300d11001c0c80c85000405c0981000c1d00a1060920307501ca0802d41201004011117902c0004400a00c00104408100360342c0f0303da46280c0390f5520003510306104040c10b01e0ba003610f04140c603034210071401030710304004c0c030904000d0900103076001a520217a10b034005801c0060042207040890851246150051840d46840707008045c19002403207210508030269140403c980c0c0b90320055801d45002803045006c1801417204001a1031725141410303401c03400d541d002c400806c44402240030340380c2c00045980880c0b001203001c5524140d04011011038010a680100d213801c260801414440150001130701844894000a4001e09030803460003408201c94004c00001080d09001007a0f0340042c0036490001c0e07900350b000190b0305014003a0354007681e000000303080c070b0341c0398640303407402d1002c111090000140d028020159034802d400064401461140c00c00f01350b00c49460100004417000903c25446040f041505e50741c0c80e101d000c02e0300c1d44114a400c1001c00f000000200382d618038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 96394271 1250 96393021 96393041
    0x3090b0714010c030911010908030f090a150207150c020d02130212161b050318030f07030317060d030206061002030d090c06020d0206010602060c0a0c0b180601050a0303050f0d 77
    0x9030030010418540c3c0e626074095643c8901801c000b00144100e40011a40651144203008051b482070215125841d800c2d401880b0008005200c03d090580e01d504002004030210f07100c0c00560820703002001400f00302c2c01c040169220502c0e088819440660009900004204001c1d00480c03180013043c03040c8040758116000c1d00e08a000355845480c0081c1c442561a06001070b010008060758855400107000c007003000302e444e512001840c1482c0c5500039414900440c0f8080da541485001140c0900031810302c40301e00550b010380d0b01e40c02c0c0014a800b92010f00352003d012680202c0b421181c540c0803980c0800c40f03642213103081700d107020b1003544824120325500483c020303e03030310510304044c0f442000806016001102c24540a40d140441407110a984401003441000b000d030300480c0016140f400d2842c014240b4042e1801c10802c5070400751100000c080c0700725203c0401c54401c0c885000340342030811400b4010001291b55441960450b600241940200701d82c00300b8086000c80c05241003038003600409101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 96395521 1250 96394271 96394273
    0x316060815130b030706051c05040503040518060102062212051908010306050604061a0705120412170307120203060f060304030c0b160806010f020c031c020601050d03090b0714 77
    0x2412103007240001810b055042d980b085c4181040002d4440c080d00c03c0d6541c0d519601c540d82059002400b010016000c01401202c0d1800204000300311580d84801c045066508244d20100515000c030001e0718019025000c158a60b845194124058200d0401007440760303408100c4040010f0940303010f4440e40107825100c22078000c04451907402d41d40c406c5605040742c0c010101803140303071600720611088907014051003195801c6405e07090001c0d007105004002d103901c11000c540054a010302d09a0603900240c028017009a801c0030304030b0601ca01d1003012101241000041c900c0d50400050180103101d699400038009500400022550b07910000e041c105264050000c507568078080c6001010005c2c01d08040321010142d0002c81d071401072a2039141d02c40000c0342c6459070141c440b000150ba051603c1080c039421840703a4600ca50340b6407024480384403001c4240200241440c000500039003414016040617000f06146030722000800c4e0700a404500f01c40ea15580c05a4419590401c4c450700d8045c2000301d015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 96396771 1250 96395521 96395539
    0x2090114040e030a12050c040e0606180a0f03021908100f0e19210e0f04021b031c14040303090f050706120b060a080403030b24030708060316060815 65
    0x203485d800c1001007800e65a07030308040103150f0340c10b41030b250a0b00a50040c0070500070b03a240065940d04044005141c0705d91010a00742c41d8042100001c1c05850581e0000343d03800b0b4070014100114101030761014180d009404124010074200070105940700041c6c0308211a05846d800300441d0100140c0c09999024a0f00c02a540100d43c010b50444807041c01c4001200c500001121000ca06150000600c0400c51255240301070b030310060b000c02c515010303180c03000c580c01603007085091070103040325000c2c00008803860007460301c400010041c56110004003c1021449050481800c0a0b40d45109080c0d4001e503d401c00040040c058106842a8105000010414031032010f012400580240c410144042020420b0040449290500205024000782207010607184000f24001138040e0700403044180707024026440120360040041f007009a02d003d1101c06042c0007081c41402c9078048002ca80c001e40580041040c1b00d241408404101220310440c010403800c0c201041c0d00e82089214001802001460444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 96398021 1250 96396771 96396787
    0x1205060109090e030a080606130504020f160f050d020705030703080c01060b1803010b012622030c0b070e09070c0c0e010305010b03010b09070e04090203010b06030f2202090114040e03 80
    0x90340f607014045c1034006c03542c100001541c42ca01107044030011099100000d001c2890031003400080d410010360040f44040500a800b881c0545528822850b8001e502418030035070705040190600c0450303804081150070008040c460313903c0004042c41102e83c0403440503a100b070018242d41c0100540c0d0810400e4180011710704915401e204030300c5031041c600724020046480d4032001035410880c1994401d02180c8540b44406c00710410309200d43d0f0122030700344004000c8421051403203c90030313040000c81c08220040c403008140050002802c5c2c0c025658108200c14034003410004d0030444000f0114001c10490f80020030420000c6500780c0b0040c40680c04160079542c4a281041c040c102ca092554065860f04520030307820300d03103a1410780c001c1d0095100d10400f4800b48041c8005820780c1c1100366007540d00d400d0f0455050322014000c0d48a4403140c2e035807200c2820702044e0350080307a100d42061900580c910001e44050394480100504440c5640314a203001c080315000b00d009411090368031501c602000c0b503000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 96399271 1250 96398021 96398023
    0x40218010804140610080d0305150907020a1506030b06042003090a050703230607050d02090102010e03030106080402090c0a050a0e1906020709060e01080c090702100f0204090f020a1205060109090e 86
    0xe040c0c0e40c0d0801039440c0d0b6601f1020850460f83c0803250325420140e0400024903500f0842c24441c3c00201a20584100da030031a1901c42c2d45140044081c421540d642c0400c20038001d41110441e04207900720b90070710010507100002d80741704041e00010704103645d0000103e03039100c80400010902075446410f48050542e02d040c95900c10b2404141d201d03c8041c039000040e043d044c0411001d22860030341c2c44045c140800c1211100c0250040c900752030540d940c03038046012007441080554000e00040e559044c1502d041e00c103004442c44040c20486c84204c0a11101601030f070840f083c0c4030020a149000c10080901d60001072400801c0d180500c45003840130b40100d42c05a021801109456400e00c0034081c080e5250244081d1751400d02c20384217180c00440401303c0b240341c0902a10b0300002e02e031048885054000204404480c1a480012400d6500050800450181d400b4406170380815000031402c085000300c0103440c00d513250b0001040380d6a00c4001405c6a07004094a001800d4a000100100107840e4501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 96400521 1250 96399271 96399301
    0xc0408070801020a0305250f021005010902090f150301090504060f0e010b01020d020a0503030c03040606051009030204060f060804060f1e050f0105030c060406180b120a0b0402180108041406 83
    0x500080c06c150002c0c20b0400c10300942c0c08084044950f0b154443d0011208484a500804000c0114001c500205000d12014000c403801381012040059482c031343c2108100307140c51b808624600a280342d040f00032140c03e000c4280c80c111450045c01144540c0c4034030f44100248400b089a04010346000d508200c8443c055200320f600107802e03001c481c0111000102641e0320818840001e08550040001994102000f006190414031411000c070780e0740d03185c1c0c0c000382442c4804802600040c803082020415890036018600040405004401180d41008001000317213600800113013107503440305e4840451148542c03026851810340940d03801224100b04121010b084c080d42d030b5250541e5048008140d0b45400b20714145410001025079161034541013007a01d15020701c80c2007150210050038001a5104030b0300c001c01e56000740c500034030307814034200454604441007040f00b2400703a803042c040c5101403c2d020041c1300d1018000d0910f441155603e20708503aa010b40c442c0459040d00546082c00b80c001c8000e910 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 96401771 1250 96400521 96400537
    0x61306020303060f0901050604090f0902150c06010e010e012310030e0f0c09071b0c0905070825030e2a0a06020c01090302011d0307082d030f030c040807080102 70
    0x110031214507200c010004a81780c2030141540c818402c010400001481d40e0001154080452000c18586c45680008a59884d0f01c440c2c2119890000b400c40c03000c0405210346400b511009004c2d1026504000c00c074620044140903446030a80445491a503880c0c0c0403d003800c480c00c0c02000c0d8112043c101400502900036103400b400d0600c034084441d482801c0209084040740c00c0035121104642d9020000c1f01e17684041e040d01030f118084172035038a002c5546001d20750050074001401140c6428a000f00802c40c2800500b000f101680d00704081c00c40c2c022120800d19480164500854102404140c00c0e09015402d00b2188407910b810f0718150f030700300700d8000240510000b01c8070a81c1d00c4d43d542d43c05030385a03130700c40380b00c28005554008180300540c0a039072000b104104188030100d40d0a15400840e10f0444941c11039061390b88131a04108190300d400c0c480e12606815222690100c00c1030840065032802100d0780014039003000b00c000b941d0040709005407001482e4800403202d086544204540c001d6100380c00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 96402877 1106 96401771 96401779
    0x1507060905060f010909050a06020c010212090a060b090c070f03050405060703020609060702030909010b0306061908070909051302100e060705070518042006130602030306 75
    0x4500c0904901c5040101440d060040e68000e0500c3e05074402850350703003070011100003d8004901c104000c0c1e800341c00507071156081540306019014011f200c2281640b0007040100b007480024140c40c100b4007400302000800f1559051013000e0808440000c0c0c0c9030310400c00280000d001c034824010041c000c2c90520f00b4251240c00041895005201c140e0060703000e0010311034070b01c2c020701c241da400900d40c1c0019480c007415580401c40841d01441180304003140440022959128081100c1c08141c118441058451080201520380e0f4426500c07040007841d0303e0030200c2d40c14101d104450281c4100134000800c0202c680c00c101c4a403074146100410869446550040ea40354440a410035910840c05001d11906000c240004c202c980b0310701c440100c0744042484040b81030700c82d59005606a085262280c4281100490301500c0ba020a04c900d21f1011500058240e5010000e1030090900b12 = true := by decide +kernel

theorem cover : BRFrame.Cov 96223021 96402877 := by
  have h0 := BRFrame.cov_init 96223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 96223021 ≤ n) (h2 : n < 96402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
