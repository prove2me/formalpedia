-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4321
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:14:49.764974+00:00
-- url     : https://prove2.me/submissions/cc815cea-d03a-4104-8549-ac1e41d59a81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 776978417 ≤ n < 777158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 776979667 1250 776978417 776978443
    0x8190504090c0e0a0b09011407110316060e011d060c010c080c1309090c0513020a0201050a02070201020d030911040f150b070302100228020c0910270608 67
    0x840c042090301520b02580d03611520915010b0b940c50b18210010f1681c41c03450180d4845140c0104240c0d0b81c0780d0040c038500c1050400080902d03203d009030318003104100d0030094058041c0c043e03240313803884581c603000e114000d0302e2440c0c6890401062410045134425050120106074107525a02c03000a43c5035140101000740c2441c001081a03060754401802c80722002e0042004c0354030410a00ca0701481c41c51040307040e6014084089078002d894204085484d416070807841c2e101c2d0700d1005455444142d075004040644003500203001076550b2004c5c2004a0203035400103809a003000303410700d060300e02c2a400040d10381c0c450740c200581c1c8248400854121003e03034a14004055076405908800d00c150000b1030020180d010341145880050b90f0003e4544400c1c480f503000942d004140901041e401406a1003d040c207080b4810001004000081d0b81e00c240702c40083c0100e03001404540740b0351b0000c950000f9603060301074500c0c1407080d280386085103a03c0308000103152551038002161445042c0241d00304480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 776980917 1250 776979667 776979677
    0xb12071706210f030a0f080c0315041805120c012007080d060801020d0222050a1703190c0c0e07092d06030510050301060812070819 58
    0x6418800a4488000044941560080e0500300452541c80c400701ca0003481c0312101c11440402201c003a285080c0a07030403004150301000c40c021402c69444400d480000f809941e0b00011038540446031031030b80c8403d0710030b1801010408030940c0f00342000c2d08080b800034002052000d81c8959510b62501300140032042a5914000013031001020b00d09001e078607041e888520708155039000051b041800c070b20400b00020710340d120100e1010b402440c1640440020300040c0002c0d9550ba441005020095002007100301030300803a8441e004142c800919480f054641c0030300752100d440d00701180c821810300030802c0c0107114442000b103150181c00d029490b00c5050000c2d25050b0b0728122500c0d141e80034a41d00d40110070b00403045d40c10805036691008801d011500d60704680c1c1c00c031881004648405800c0d5202c03410700300015010019030b2542c1640022311900d19400e5243c08603454100301070030780781144145403440d48003038002080d0f0210b50001b400124440c030b48141c90180d804242c03400d48007040b040e0802040c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 776982167 1250 776980917 776980921
    0xc011109030f070b0a0c1a0108150c03090a03320a02010e0f06150a260106061b06020a03180303020307020d03020408061810060f031403030112110a0b12 67
    0x1080810100040410798009003c2242c10400b080344580140080401084010201141409007648840d074005100a402030fa0035030311089000e945800545168054500740c00c00501c280c40490141da000e08428005003e243c5d07070b29203007201c035600ac140442c1c11980d2582070714208050803d00504040308116003090700d50030400e401a003110417099030494a6040340200c110440d00104460341d110b03c5005924140100070400701e4009003d41c1c020752510000c0e04102d845c02e001144003001390704014002800380c01c0e01c40008458000800301c441568100c000d0b100b00018280d42c024110201481c94005002c0c1c00d920101c02011b0400c00d01076000c82d600109010601e90b05129500080e005820103501d068174102615903a004000c00d100010320b01820107c3d1401418401900b8250140d40d003440b1072905c440e000c0694241c0c17444121b41c4101c010500181440010065904844010500601002c295269a650100d0b16110b26500494050001c1140c0c805840600810710403d04008454 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 776983417 1250 776982167 776982169
    0x90f06060801050c07081804090302010917090312160503041215060b0405010e19090c02191a18011a13050c03071d15120c0412060b060c011109 63
    0x31929a044001c00341d040c10708000700040003508485c62507a0024000d552032420300511010240300464469003d810300b802e40050641c15000716248a005d03820580b40b00c98032510480540c881c04140c2030300358010b60100900500914050000004405072850040c04147d071443d043d80c0c01078101110000e0b0010090b0709000d221044424001c0f60400104038071810405240c585004520806040003110b0610b41001d0f210710182e211180c1c0b030004101552521400080060300d0030319184070052284141500d20704103115030044400e0340101081090300094030825504000c0105002c0e06a280040c0581c0810b0007407284100480000862006140200302000060118503000d0b00116042806114400d100801103d800c0251810500f8416020b9140303182e443d80b044000340d50114081d02103d0f00e259141d80200a0304031444510046940c601e294544180118044c40c100c1d1210f11420300006806a804141e103540c0003482241001d03641c06086003920b0880c00d020a081102003000401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 776984667 1250 776983417 776983421
    0x315052d3d0f061d090402011206180c0806060d0b120d170a0e0d030b010c0516140607051518030a0f1e080a1104030c1202031903080a050c0409090f06 66
    0xfa02d070500e000c034000c891508011122420801c00a40b003000008040390440e8050b652a00f103440c003008080c41900e94541a1601b10644003034903600c007d091240c140300c0944100740c0c403031082400412035418045101c220074000c00b9080d00720740d00403a004550702558131040110301c94580c0c4c02d039941b500b901c1d80800c7c01c000180c3c02400703a030719007030074a41840d0007084040340020a6003200c0c500000c0104070b4800413610707440004000341160107030b10144100e0680207101081514004107003450380180c14070621440d0b01c60400e0280c0309400c80040110030315076040b2800e07000000305203404510450224200e00703603403190b0420b10100b00b07c202c40341441a00441e440709402005d1264000c8010103640291880200820b06c840c100c2d5503402d0f04014401450640300556002810a409583c44100343c1d01c1028010000b6480b92281d130f5000134a03141568242c0351550b51654800c040c989401005801409020740714007905541404045000c1813a07109802505000c0d0745107482c081c0040c05c102007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 776985917 1250 776984667 776984669
    0xe240a060518070807211b0c02031513080309060f0f150f03250f0801091703040204060e090a02120303060312130315052d3d0f 56
    0x401000b00040e005600c20440580a50081d45810180b00580c2e440d0012907950700f45070b50b0a01c5100d2520710010360000c8950120500c00030000b4104002d4140c081c055640c040c0000c002075040d8003410080c14558030208200b40c2020780072130001102c07999a40c42804039002100c1000407640807508103ca480c42d404003070380d042804081d41d00301d0781c2844008400d1542d4803010380c5025040301c1e441002103441c20071802ea01c081c1c00d02c0244407407000801481d2100c040a201b800d0b0800395521011480b05010300c10b001d4126444442c04091030100644440f0540004006a0380295502c00000c0c408400030300080c8a6500540581420503540c810003104220401d8000c000740d100b801045500d0300c000a400010b0700800c0f4820751100d117004d090350b4200019400090080c0c480118000c1c00344403d404c13050003a00b0048100d0780c2e140f00010303500900c40d0520082c81040f00e0413408190541c0301034044041c504c0c170f120402c02652040d4000c4c080f10036904c0444c91450f2180c0380080000392030002941c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 776987167 1250 776985917 776985919
    0xe010b0f01050405010e0d06020f0a08010816030320010510051c0b010b071410050604230114030705060714061014041e09060b03010e0a08030a0e240a0605 68
    0x220038000080940c0241c0c003442d070501501061302c600641c2c0700c03108000400c2d072001041d550f0b541800111f208981261000c10042800040003080301a400714820002c1c540e100b60040f0003500c1c42e1800c0b2035400201032030100f19051550000701404c402c0c00351a10400070010035039100c030b141000b800713407036140d591801100030040c50305a800940d552403114116588060866203403070141c101359062126000a0208606c00e1449000e120031281e00040c0c413650003160100b2145407100050341c03060422624540b0202404401400410f401204001c0304181c060200c445194079070011401d103a21000007591440c441e080041401c02e4100300c05980f00c135104881020707603440d045104c40c1600a85070f00300d20031929950003440540124001c6955002100c009100d00101c90401c28002c00035101141d001c3e5090403034900345a200090022039003544881400d00d960f81c2d0801d0b007001403000b4040b040460007802000710819050a1205030301c40082c80c6e642a082c1802c9492030115156a07000b6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 776988417 1250 776987167 776987179
    0xf0a09031115030112060b1f0e010c050303190609090f0b0a1830170a060807090e0a0614011404052e150518040203090316030306180e010b 61
    0x126038400c14500c1644d0464400254042070f40001c1d15020000c0c0600c51800348d00500e914503c0c011041e40b6146007049080d054a80d990030003100b0b03004460081809101420a500401c00300d800000c0c0c40c00081050210507600007490390b00c4180301c0060380d5410005540e0300c0c206640b80d5003807002402409030068250f01c81040050000c00011042c07119141015001c1d00c0200fa03010075481d0a00e00015100340e01d002002d100d016499006030010b0a28114450360480c550700040e4400d8540c80340300300340c9100c5001480d00c1840e005020026105020405c00385000f2254542c00080e180d01134100001c142102e14401036040103036204039013001440542c403c60410040c002d25131034543c40f049160303001d6240d0644030061030b800c900290a0660041c4845944011030b4074007564000090041030025190100090080300108016030005452107038058000b00280c11030035144151003040648681000b1440c240d0300c2605544c240307144442040c940743c4400c644800c980b001e100740208a20100c4032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 776989667 1250 776988417 776988439
    0xa0506013b070503042d062315031002030c09100201061401050903010e0a060506042d0c1707030f11070b063003070521070809060f0a090311 62
    0x100d20311456020b02600140000040410144622011611301d0540c943c08009641d8045e454008480803c5400940d506850241c0000b0982e1a0722403105840c0a019105511501d40794042c842c5000605011a031510075045c806107811300c41d00242d48a000b0409040d5203c40344039052045204c6041c41940859240c428244002c069011422403610428a4101e88808040000c80d0041403900201c10451158005a0f000c11060303400c0540300700310a440503c4009051405034881d0140100c1000c42450b0100501021290960007150034040518220440710607054982c040b000050340e1100c00079032950003840c9071003641c1c06800700d10440031140910340000740d00c42c00c0b14810701070700041c45194060700620820655048080e0701d9101d841051070030603100b2850940e030b51b1201c14100c030039000322100100707010000390917400c5000f1750080381440c142c61580d42e540658800c0c1c6181e0303400b84c01408128200740280000d054a0340481d1110b00304203040d41400603050a80c016028030980543d10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 776990917 1250 776989667 776989769
    0xf05070b030c04060f05120406050403110109030e04050a090c060509010201050c0924040f06090f06091d061c0602070507150c0f260403110102030a1707020a050601 72
    0x215022202c1300d00d40f0f2051007000e8a8200c820344182c08a20954030300c2c48007800309000d4654001c0740240c0c1300b41c83c1c00c14107004c00c44c0031900b80e40885101801064090407902ca07541003c0d04105e500c81051080083c415070143e0341c9100c8103200d070b0000000a840441c2d10b4220b540c091044c16000036107003c45a0030058020005918091144140601190311411700c0300c50181d4030050720301038290751215648403901c2d450300400d101c0d40c07803082d825200220034000600364010b04800c4255001805002c160a101c11100044041c02410980d000840e004004100b03404640074012143e101d40800b503a250700c9800c00600d00a03c903003080f069280120901c1601d140c01ca0b00d05200c0c590b014502c7c000402490409607c03c003003036508800507000c0064030f42505c0d801d0200030801e1300d1045040b6089a207100c00120383d2030040301e004101080303051508004034241100015030020700c0f0300c100c0e4071b0442030740c1e80d490801c9420307030050124020420180303a03c6040d600016502101075502c080f00503001c40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 776992167 1250 776990917 776990941
    0x1605060f15040203310c0605090102100203071710030503040b0d0b030c010e0103150e161707050f0c0f160f0b0304123203040204050114090a02091801030f05070b03 72
    0x17421800400295441c2030000c51140e2001e410180d03000800c1c41c00c52540c428019105034400d585160050185516120482c15184281c9000d0f000c0e5036a0751008607890458480c4049002e4a18503840601c040008005401000144040c01d82c0c2c41080c1e490701010700980302918080480b03544240c200340041900d503603218040c070440560910780850015109001d50480c0034841c0c200c40c0000c00302c40c0c1000030f1100840207030a101c580765510340105d06207829100440080a60b94080081e204001c500410032012010340f100525071000d0b2041c1401c8054041e04d400c40c0c8810340c4c2d40d0a64164000c11000032403c80c240000c1c0a04040d4038598070b40b07541d4201040590003e40c10500907506000b00c240c0d47c0302e020040c0449160403840c0070680c510080101a80c100b00da080348034900f40030000c00c00074007a510318100c4d1440a40066115120890124044c2d00324030b130400d403c4011300c0300410f0011b41300403509000b0340c0600c02104840c402c1d81002805c100086d0483d480225041041c055007100c51 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 776993417 1250 776992167 776992201
    0x90501030809091b1602122b090906031a09150103020f0609060703200708030706050717070c1110020d11160314120702010203041205030d020d051602010b060f1605060f15040203 78
    0x207003640c0712400c05448c10a80303800c4c05680000c90080e2400002100704004800c40b01d00e4075000714000030b40c0c4da8076082a16a01c803000082e4a1034100e07804010001410304854146120000921035800e044a4901054007900003a0082d4001020442d0012a400d50648a651842810005408103d0034211101c0d940d20603604024619956100000c20b054410300319008990305583d0100300301e0801d9034004100381c4170542c0a54049444010402d01890250210701c6042c400e0f802600714000440d0054402d541840d0400c0c8160051307481c028402a210803000003d0b43c891035140101259020310685070031900e42c000d4034004010401803000d0303038000083d00c046480305500103501c220036180c0f103400e6001d0004c481c618180049980b202c80303542c0307411003449071552514141c42c900b00000124281c904207800705400450800c00c904009503084001d090380211490911071500b9213994540c43c0003421101d4100c8404004140025059010701c22054036008072025410760815041d410381c0c401c14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 776994667 1250 776993417 776993473
    0x127060b01090b042c090d030b040b1807020c0a0801060311040b0a0b0c071211040516051e0f0f07021c020306070c14060108060709090501030809091b160212 69
    0x11000c0d480030720404040c581d110040c150703c1603003031818551a06d036030f2000000141d5003c64207040c20007021b402c2c58403603002102e100404424000541000c82400500c0c041c0040d003c40c0991280160340d070325914541001001d02c0030002500c0c0d03240d4142000010b0705035100c1842203042404080c01550780501300d100b59055584419500c201c1c002c00e8614041c1540d00071182c901d500c8106400384402100795511034501070b0b400b4095a5502030000c10b11031b03440d28206020800500200310b8108a034000035209001d840c4001d07283c01c0d40100e0f00001900030440d80741c0c40030380001d891811401d02042c034001540d0000620307020a189980040c1e2a500010440000c010f03620303c0c0e83d801e101c1011085822024181e0940d11656141d01c3c0036901c941c011a048004a6400350300003030f908081e07108203812603800c00101420450000c08005045101a2206070311480c3d0641b02a100500c203402001e14048101c001c0e40f213040644140070045007103009154942d04003080344e2002c245051481c400f140c072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 776995917 1250 776994667 776994689
    0x4111503060a1413111803010506010c0b0a0e060109050a060605040b0a0f1205040b040c140904020f060c1204050a12121809060b07051207031706030127060b01090b04 73
    0x404501113100440c24800c049515400e081e042d00780b0b807401d60000c00840304803160100f08501d0090505090350f03c1a201c07107000a0050503540c011800403082c2e82d40000d01d000b0082040050100743d01d1800c1b4080c0c1003541c1e010382c1c680a00c03098a440d881070600030095400e2441c2001d180022801840c05840040c9052150000545442a00c16002100c1c40b040d0410f040010b814141002c0703021000c100d504658001000030081404106403c519190000040001900340da40c2c0d824400c0a503101881c01350041410711920305208014000307401d00d600104800c6440303616000802111904503800441414800c081382008682061341c851f070340a102d0309000e02000700c0111900584805503000c2400c991422034007207010780320113000300042c3d406001202c42d61800c90141262034820100d004010400b0034080f42c0100c03c11a49541e40107000a00004408614000d44588110035580410004041042d40e4041184510452640c85400c0ca230260666060503e0032045214a0254a141035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 776997167 1250 776995917 776995949
    0x405100b0703050d020a0564170c07120513030210050403060501050a0b040510030908040608180601140f0a03290a0b06030402010309080c010504111503060a 69
    0x35004804030380c80e1070088001151b407251001001080b030340080c030710304180400a6046080d09049401d500307184180161950020b100ca02c800e081400c0d011442660800242244041c03410142c0340310b040c00303400c0760340b03c00410b01d6100d01484401d41c5d0052043d8000030041c0300380c0380810a403500e03a1641000c98100961764500c0401104481c1030709070b00c029441030b40782c00094072550b40440a0700840f440340b001400300b640c03a001040001603260140e528034034401d1100308020f03d003201c2c001030782e800700d41400500380140e621450f940364880e170000404140c450080c040081c1a0303481c10f508455840018020340c0d4184203240c80340c0d41c00010300ba84a40c0c130746001c42078180d6514000da80113681c44100022020071003841c84000004c5004403460600c032890029103030320b01a00486222890080c209459030b0f030707554015030050040181c16950881705001d802c044c1d41c424032239140201e00500e051b1081c4400c00e010007501000d040e1550041301400d100b48560307074031072142d00030039107a24044031440c0c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 776998417 1250 776997167 776997173
    0xc031023011b2f01020106050d0206070816050706080a15065c0a03030c050408031204050f210a030212070906200a0224040816050405100b07 62
    0x950b0402c0c4007070092029050100c0c00302c60320708115603036410562510001c0380c2c840790040e4202d400d43e00c2096000b420041a0b40f0051800750014060030f41b0034100301d818030141104050519801000480e1103502401e02404060340041000383c0c03103400d03020705028000504150300d02c610154440c03c0c040c4491803030140c0d583d0301c1001b40700c2c0055003090880c15100d284039040c0e80c0032820441c01daa41c1281d00614a0301001035003821003100030b0701740008103820003255a0031401420006629070400c90140004142104140010702c0c958450301d081c200036040c035061072410000c1455003250756500080d10f40d0b042220403080d940401e03407400c071042e07191011108160042d2181c040d0081c14149005d0803ca0000d0704203018405075600c0d5602d400ca412320906403d00714400e207181013076560344504210001032402c2c0030460b00d80d00100802080080d0392300c1600c0b01c0c0350007980000800e6040381c400e21640c190050910001003604840078005402c11008a9a105402c0e014001d07064000181c00014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 776999667 1250 776998417 776998457
    0x110405060303091810060906020303070e190603050a06050415290403050607020d14090913060606050a080a0b061e09031506130e06220b0c03102301 65
    0x202c504080c0c4100c1c9030078028404c2d000340701e40031a070b0003043d194520b00105803a4414a85681500c00640056282d03403211002903078800e90944145900044040e214648a034101020720b00400c219240031640c1e0500c000407a0546050340c200c140a5842d003802c0f000000328041d040c0b0308540c282035200310000080300003d461801202030320305407050300190020030400e000076050f00c0744103180d082e602c800181003030468445940391034101c507451003403007103030942e1400804558001c441c4040c140402d0b8040e60744d09c000c1e95525032051000c50341c04103107031101c56080a034603030344a02e0b0b0b9401007000d030541100003031a5010300010322440e900503403100d00020000310201c905540340181200c8010885540e80712002d241103840500038407419001c0c401c4000d9a003c0c01b4070148048000c0c007000d640e000000b1800c0b0b85000d03888002c0354000f903040c90202e0841c01b413040c0914061070045590b4a024415820340d00c440d54004c2105820000b05509004c1042e180149103a000b440e09040143c0c00c100c41c0b002c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 777000917 1250 776999667 776999677
    0xc0a0b09011215081203040b010303030506060d060b03090c150304060b0d0606080703150510141305091b01110d08190e0f0601080c0303030103150204080304060306081603110405060303 81
    0x4106143c0b20394900d00c4401410a4401c0740c6101c82102ca101020300c0903a91076000643d0b00400d156500c0c0018800240290007490784030344041c0035281400008410f20080c1c0320b032540301c24846c5200209010020b401440540102c18096580e03401042c1e0004010105120003000034201940d154150300d0140e4401c88050780040d044003044c4000b81d2249415031b101c294500c01103078083e80e242d46421040c031003802000d1244100ba8010301c0c425150100400b03800044150281d03004c1803070060b01c420320200d440781501600e980b80050540b000e17140c84500c2e42010003507000b818051203401906080c580065150310220843c54041c80380e031a0444404940a0651503c1c01c000381002600d4810400001341110601085800c50340d80346d03a92400c45880700c1c005440d094250704100300500104400500241c034060010a0041c6000c2d0b80d416030600359089a006580080d450703410400c5080c808004160307103c9540180125a0f600d19178444843e5000805242e0183e0f8940002400aa60900540b1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 777002167 1250 777000917 777000947
    0xe0105120c18032b14030a0f020c0d031a01030203010e0c0d06050d0f0b0a02040810090c0e09070602010f0c0c021905060406091802040305190c05131d0c0a0b0901 71
    0x1c1c2c50014140c013804001403c2c0003554443c5640d409120300d510b02c00c1226180780481c500610340395498a602d81e0000d05001b1400c02d60458003080400e00c109000c0203040d6091f03d8a90780007500e0340042d4440024103c950401d01c0c10140188014800744451583c000c1c1c1000d10f4020042e131301d20401c8080c80140001340d2045500a01d460305c1a0107021004005000c0360b44203080c0c10007036684100b5000120700550055a81503808414801e04009182e8071801c016801038482280469480032110a444800c40364440b054205010400034142c0900070f03038020140700701c802d01c100e02d91107400a0010003013000107840742c001403507514000084640e07000c025060150600b80d44a45505e00582003644900c01e114603a081000403010400f264800d4400303403540a805401210180c00311203581c4031100360251440b1002810000b8140d07505200305549800d20240070a903050303607401400303a4070b0500c0201f030080d41001e00c4102d815601c0c0500402640c02d1021469240c049580048502c515080004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 777003417 1250 777002167 777002173
    0x8180f0307150510030b0703020a0509030304030507051309050606100c20150405130209061224102106050307031506050604030f29160e0105120c1803 66
    0x2404140400c980c10071a118106014984544a0300291010a0310006d890420304501040c044d40c4203400500c0c11505600d0304500300b4400341d0020b402c581c001d82c012582680251010071603418551610001e4402e02c070010800e8412039102c031a11031030020541881080085010f030070880c02054241400c43e000001c1045400c148040e48442c05030a070f547c1880746c040458681c1e41e15a084040320203484024141151421000b030180c4040e411501083d0b50064061003601c944250012000b0300c80c1c0b040c0402d03140712121040c0404945a4609052401074080c8500a400c05801101e812858032260040070700c02040141d14000030811508096812300840d540001404582c6044400403017102cad07010480303143d44008110891013075101c0200074a040c1c0d508480418405c0001308003c02615032662203c0c0507441040b0b0b031044c400c40c1c402004045684103003092560143e00c20018038428201245000403190100d103002a000305844d07585840004c0300c08500c4800391400f14185c6002c3c0c11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 777004667 1250 777003417 777003427
    0x6191401120203090604030e060408070e090a0b0708150906090402090603071203050403020a06180909030210110315010e030a110a17031b011a060a021f021213020108180f03 76
    0xc180d00c8603021b4405500050061811800901c1d08404030340440e0742002c01000a245002004507030307800e00600d84401400f51039800d00100d00c600607040d02c6403c1e04d950f05101850301c0307500c9844040210b0300081c01095100100a41d5440d44041160003a404803050322041c0c7e61000040d02c0d00e40c1e2078004103804540c0c0941e6a04054102c00508103803882101c000d9103203521188125040408030b905180f505e0401081000b58000c0c5900c000644e0780a40706803501c0003424440501581c4140b040c0d200e040c48004200100c454020002d0000e1000900c0c0680c0c0c80384d205030003e030303a0312402c02001d4009100203101d8451070f0f985800300300080a0071658160080d42c100c40c180c1d01c82e041000d11070340305903014558151000b4184241c4e0717a10500303e2190b8443d0032605061004a070002043c0c0310540c031030741d02d52001c4803441504482c04082d40d108056030f1901d415821014241000e00328000502450b600000180e07005601c680d07001358540c102c011240c55003601145400050413680b1400c0c040050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 777005917 1250 777004667 777004681
    0xb040e030c070501111c0c030201061a0a030b030c130b040603051b01080106030b09390c010606170c0f1204030806180702100b01051c0e0606191401120203 68
    0x103001d8202c0f5003d0300e0350f844030001d452065072114075045121303083d860800200069075000c0d085800c0414028400080c196484140944802c0290f003841604000c0c040340882045500d8002c609170140290094036080c0044c102040344940c8040110300ba441d1506000300060702d0b203901c210020368000c0102c45190031006214901d8600c00c404090010781c0c420004a1214080c1c0500408100098050421a610716940244520a02804505504202011303100e500b10180e403804031080300f03802742da0f540c0c01030901c42821144554030110500455001c5d655101c02c1741c507031b1a9404040301e07007010f903078110503003d1400600c01c9a001921034200300090000307240e0b2000d4554420340c0241c5807104d04004450fa00c070241c80c012255000142e12a5054201c0c190480e00091a0b01e41f06041680c1440181000301c8280203180030118a0079031781d9070392000d03401c008009154000d9401c0e03505c0c1f940c841c0701d142c006000d01002d0180d0059003141614500c40d81e4403400080030304c0b0413800d0381192603061041c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 777007167 1250 777005917 777005923
    0x51b180109150e041a0c04080105250914040902040e07091b110c210a08070501110703090b160b0c03060a08031c110c03040308040905010b0712030b040e030c 69
    0x14000400c04002c1011441c4401c0e240c01c10f00442c1c00943d036100705031071004207a07035440004005041c1381c9070601000502072320074001c190203500d86121607521074002a929100d80070381010080104010140200306480054807030b08000c0e14142c81c0440c070f0000900104000c4e04550400d00d400b171081c6407000802e000142e01843c0e440401240c0307841c0c050701c11003048031000d0000c1400101074100790942c004902d80081090240c1181c8282403a401a4225401e402c0a2400da016280c1d01c10005144080010a10444500c070b40302c0041c2601b0b205141d1401008000b80340070301d030744070f410004041c180403285404140038a0341c4840114818680700c9800001900240e4046019000781b140214800c00080141d0320f00600c40100c4040000882e100398000d8207130039030f24843c410303000c02818542060900080000c1c7d8000d14407640d99528104410048900582c881d03001840140403800c001403811011100f00c805519010422151400000c0d004142c1c03c1d80681042c4400540484000008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 777008417 1250 777007167 777007181
    0x70813060f051e03040c0b0c15010e04110108180319080604050f061003020f0706050106021c09060806060c1c02100b030604031b060608010603020a0909051b180109 72
    0x40d54456041490340c480550751805181e403c160075800382039190a180d4043c0d806181d1281c000c0100d0080c03aa0307140c1c0910759607801811400e03400e400080301410003801c01c8001d50700400e0740744e0048007545000c4d160349903614213503402c4034104540301c40414203241601c94110850003105056a42d5080e00c0d404c0318140d480d403181c0401c0030840f000700141c001d1800e403090301d00c0782d10000008007059803640304214010101c088003000b03142d030902504c800740a400c00a4082030348210000649541000d0020b8a02980003c9112400301700040240040b54450103100480d04d40341890071399903c40d0350014540740107555a5146500c10300711100c0501d0300042d0b8180200b4001d80946000360346041044050759217840c100e076016800800801d0010740315400d203e140844a4040c2240c1c01e403150380c1c2c2010b49030300d0307482101c4581d1607450501c15444c140025600074056014100f01c02c070f0850340d98070b80750040c04540c810000b44410392480c1540340c407042d10004510f1010240050741c2c541403444014499 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 777009667 1250 777008417 777008429
    0x10030c1e020304031a15060f040803030c031008060121060603150c0906030c02030412050a1406040515160809070b040815060415090504020a030c031a061e120102070813 74
    0x4100f0f4005c03c0c00c200d240c40340d40a5001284800508162001030103026072080b2041c141640c0208070003d40e50005001a42c06522514101a0b0b03078289501507079000c640f15044440340c2c2c0c10100040124202046800015510b02d1180001114643c00c00000400b03407540081e00c032485030380d00340c0d0301c80300b0300e622518601b0a283c696000c843d4036503030120221051507443d100541c0c010082804400c00c0d1000e00c041e1719104000302d13100891140e40d03883c3c218001c11000d00c02c80d0f101100b40010800c0034006c802c454504016500c201c0c0c90320300c1b14400600c2040311110107009030341d030100d60f00c0c0c0780c14031540c0b000c0d1072403580b00c0383d603030b9611503540b0755994120251171400f003c45030104e1018a0203018042030400c4e0069500040d50810f40160001e0401510803a0700107210140000081c0044841400640c015840c0441800d00204c8210755504014501885008408068107082140f1090512490700c02d8401d047c000c1310707401d441130080c4250100a001d034840802c050f60a0b4007286ca210080e161 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 777010917 1250 777009667 777009683
    0x1e09020f0316030e0c1203040803070804060806010e01050d05090c0301051806010b040308120a060305010c050a081b1b0a05011a1906020709050604020909090c0a050f10030c1e02030403 81
    0xb2040214200c0d044040d15a0389030300410401d44a51920b0940c84802128903816245025a182c1c6d00340e10f1548200e104076414003001c503042060a03000291070b90702c00c40c00c1c201840e541464a0000340144528101480d000356210701207299901e0400c42c10030b41c910301034002c100a051034000c280080c07a10701e40390b510078400d4a001258034030b00c00003076900301d940c4010300c1810005600d4044149180050950502c60365507200000030074401d025921804481d07032540750380ca4203c50002800c07060001c008040c503426010100301e040c6040c20480d10042030360b000c0161141101c100d0b403030803e0310200000e0019801c10120402c0402c40341145100e1900803614100c8c15801d003515404000700c14801c3c5405070704020310421602d41c19421547d803003036000340014034003155440007408240065686040a5010700d042d031625050a0b0f0041001d0a41203400f03010381007500d00018882200300c80d00d8401c250301c0e00f049a01c5140a4040324140101c07000f198400d40314010740095580d0094441624124 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 777012167 1250 777010917 777010951
    0x609121d0402090d060506120601030c06030608030903150a0f1a03011409070614160309050a30170403060c08060d050d0c140d030603060c0e09011e09020f03 69
    0x200e0300c1d10840303c1280014001e21321508480c1c841c60000d10f802011550025140b0140d4803c07083c007400040c1c081c40c0b16a40014407581040d400038200e031415000410642c3c81007090624980c0c000600345c58185420b0078480e071540c0c0304c01d00300c40540346810510304207a007000c3c08040181301c2c4110140b00c5010640003040062502000700d86812000d07604c8070410b4100031018020700303200d07002c03664400d00c0354140c007850041c003050404034446c0d10103c01d40c0011074100003031001d0b2804030055402444801c444103101c9800c00c1101c4000e0b200000521009003003103403c1e00411480f45181d00741c404400d100140c403680d90741810805000b0924040e00000d10007400264503213441c412459a00703400c00010112103140013000d48010702440c409964002c448002040190300800c440340c2107c0381940c022891916616000047d070700807201c01c006004000c2c440828580b9001483d604460220030030040900c0c920916a500d0300303190300300a0071280001119039101c00350b500258054450a01001030700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 777013417 1250 777012167 777012169
    0x6050702040b0a05181005060a0203031501050a02120d09140a1502040f15030b062a03031e18010207031d180105060a030f1a01140a14070609121d 64
    0x42c3c0c0741e8069030f0761140000045101c201412000e82e0742c010306013203a4800700c81e1900005072154001c084254010781c000002c129824051501e449070000e404e0814500301036040c0800fa490340700d80c5690700310024000c00c036242d940490380c00503104036410404410321684019041c40e00d45030a610162041842400b034240d4041c90752003110100c604c05101049290308101d83e156141c1c0c03c03980900b0401d44c035110584c40c160b0b0380b04000c1a4818082d0782020358505002d01c0c680c600442803511035410f401c24000c010070b84881140ca03400c0c0c0d080d10300f0704001581e03448000f20007441501c038400e2000d40c0f0208230b040c20980c010442c02c0000d030140c0d21100b400120401049550315410b1041c681e1840c0d40401000b0350305000020700320500440c20301140034201ca104060444041c19206240f4030015601d481207545c004110350b59001c1c0c119506440c119407154050484d03c100c107680c0001ca140000c00c2024410700303500080751107a000b0240c00042c00d0048008000580c2085440b000501c800c51051071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 777014667 1250 777013417 777013429
    0xa090e0f030c0d051815030709050d082b051e25081008030c07210c06120905060f0a060807060e090a060e01030303020309070608090327030706050702040b 68
    0x40098860002c2088410f901011280740c2c00940718100d102e40001d040152542e10f00440701d081205c440c00300c588030300d00407600a0600126a0003035001309000030501c1c000c21240030440340030440b1400144440c5180d0b00301c0807265031001c0c40300140e4a29007024000001c20580b600b03a09205c40c00c0c11441c0c2c40c1c44848032440c0c800580c0301c40e548082c100702c980f03089287c0106800c6511042d000c81403501c440e900c086103030469100c500280e4203500481030a100c000300c0700c8514104640c0c02000b43c1000d003200d07912004803114501414082c42840a42015500025040007800e10b83c0141a500c0608000c080326007240e0040d6210010241012004180224006030860480f00199100180c80d02d880c070521030762050192241503900c0d05c0b60f9012420030943c1094a00031442a640140d691130303c0031010f800c041a54214000700203240040c0001c41d4000010b480d8400007502424400c0807440048102c0841c03044086509401604c100150f031b070350031401070803500c0c0c001c0d203050100580450030031103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 777015917 1250 777014667 777014677
    0xb070f033006051804110316090b040501090203060a0603020315060a11063313060b032e030201030b03010b090702150a020a0c030c0309090230330a090e0f03 69
    0x1030305080000010040703101c02503030301846c00b400f8041d80c0000700c241650500305805904a1200c50b80c8440d60300d017132030500d44602401050414000c60079401c0110008141d040540b10b04000c141d0040085a8145146070f070b4090841401030039903540d0750b205580640310604080078000c0c00e00501e00090034078081242c854600c00402d00a842c02c0782000c07604c41c150b091541001c160003d40c0d60090040c440c840c0d04c81c40c4040c1280b8001c080d201c0c50180c102181c125008800d0304214095144111b00d0601200c00003400d032642401c01160801c00e5102090041c52200a1039034480641c0702408000ca4012900f5003889031a0141a0116038a40c0155010b03449828112000284010042c0c40842c0c8a4910395080034403900d40244031588e64144007040e81c001c1820312900080c0180c884040200c3d010000c3c201883c261b906c0d07085440d1907800410051040140c401c0507141e140490070080b10101641d0071020700c02014465015101c01e9901c0007040500301a46280c0315011035005200c8000090700c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 777017167 1250 777015917 777015949
    0xf030806030f06130f0c14120d050906030705090d030f02120306030a080304031101152c04080c03040e0109020a2703021905210d090b070f03300605 65
    0x3c0540d841d60000301d4401c0e10500010317a02da03180580320700b002419420500c402460304100c48101f1040402c1040480811001451106e81c400104000100c1c2c0080644003c200202c5c1c4268aa50f101c0ca4182d40900c40c105510343e0091481856900301038100e100c0d4400c64a5541c2140d91920031242e60700250b120035a80030b680f650214004000160068006552140c0b00b450980c1d00410308100b81800d460349254410300d0454000801d20003807002d40c3e400c108641c0d049609110714140c140b440f6250000c043c3c80642400d100240002c1104410401c482c02021010001c003500c1da0b645104800a422503e0848009940100a0301d07681406131603501090700c10075101c4944514541c00c008004100b00c5808030801c0341032800040c165240382d001080501100b540c42d80c07414043c61040d0820a60180c0c48091000c0000c0c02d00402681c02c0c261070641350300904921174a28503081c141d800b020100050b01410001c800031100a0700c01050002806c01c1040f800d02845443d80c0810602c2c810030f908030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 777018417 1250 777017167 777017173
    0x40f0f05061e04180c080a1b030305030a050a02160c051f09150314090303100807151103190c05191110090e09070806010806060f010c0507120f030806030f 68
    0x1c62810f24003980800043d071400d2102c80342c040c00365030741e203040901c1c039500c0203100350861f0300c060f01130095042d4442c11a15240b01030003030140c20f40d80c024145020140c40301c030310035607104c0000d0059095a41111141c0580039540c00c8848003c1c500301c1d862140e9400766030f004292000140c0c0000100d43e030144440181d585034105481c3c01c058034403510545070a018410903486a908901c000c005441c600c1c000d00f00e080c00755a9138a030221950031600c2603a4007444907544082070820689120701c01503006980c9626016104070090b24501d459070013008092405481c00810b400312207900000c0e01c8040500c15003d85040e01e894259181c407540a400010300b11042d060306820030f03442d011040c040b041e229401c2040150780c654048141d840070403100541541e110680600440b0020000c803801400f61200900285c60800c0214001d95603004030715040c84046da160504004080c0514005410312140000d15050740d0b00306100100c20310b030401d0300840e411001143d401d04000c0b800c4883e4420440003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 777019667 1250 777018417 777018469
    0xe030c03070303050708090d060c020f1606050c120a020703020a0b0909010b070615030605100503011503060510180f0c05070b060907111606020f07061d0402040302040f0f0506 77
    0x4141e070704d03030b02c010012140c4050401030032250b13645580582c0e120034028000004c01d06071804000c1e180608503160010184e00c03680c4284441090f40600c00203490080c41d00030341f510400214030380313480d01c0d02c071010358030540114210040950000e12041203a008580b12040580e480100004510990b0400c0c0c0e0041c1c040700c0140001c000950084c10139500c03c040c0019029525007500c0b0840c0382c4c2d82c2003180d2898503079043c840840d08041d050030141408070000c01405039610704984544d08244402000c083d204d1002451107080c07a52440003e00c0d8005a5000e0f80b020011000002c107001a80c81c1c41c813600d440150f0390a14858402d80318a1984003203900c200340c80300420860810320050401c3d041000c031605220070520248212030081c44046076000c0d900d0b00b0414064200001d001c80c2c0c240a0703014410400140f5809490350121100308811180079800100c0810040d00c1a07410280d04030b814001c5000704a461a40042040340e07034040100410349455080001c3c604a20740c160340000d0403948 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 777020917 1250 777019667 777019673
    0x41403060106180b0a1b0b0415020a02070302040506040605030d050720061e040b1215040b010503040605040201020a2a0e06010e1c14060a3b120c030a0e030c030703 72
    0xc01444240c01701c0c20100a040c428178040701001e01c0b1410b04880310b60b805810300c001c0050040518440d00d002000540c03e00843c820020340d240c03024823020b4400d40d02c2c0e20100d0560303200c2d613103e00d002c0e10b405419503003111142e000182ca554031121b8100c803540741e502c201d501d405d0150918490400303030041c04c1501e070070482090340302c100110007400c011104040000040a03912503004148801640300f0150b413510340740407070100e5800300700401c5001d01c0c20040c424056aa11008603544540e011000081903151400101c0c90714403901c2c00109101240000048211842240414100800c03404a00150b4842401c91114031055407000d020841c2c0450303502d05854a074145ca01440805056114000c40d10b41b82c1005c2d0b0280100305c91801d400070018013480208502801c1680d50010104807503e486c0c907503014107a080104442c030040e100c280618066076105010004c0c040188aa0300307602c4099817541a600e0798003401e403103008141d8410403089503041c0840d43c5c01c00d07010000e02900000d85561 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 777022167 1250 777020917 777020939
    0x9030b0a06090c030b0f09090703020111031213020f03012c190318060201020711060c01020d0c0801150e060d020a1404030c0e060414190902040204140306010618 71
    0xc0c104104140d121140415090000d02c965001600719603808035640044405021807074806a400e40c5c01203041c0d030100600204002240c0048a5080c40c0c2101d005040041c5a41523005041502c1404480d14041c03000c801c103540c540c0401c290003103440c0903030301e28008105402c03038100c2c0300c138001031030188802d039100c0d400070903e0340322284426401e40720700a8680c024800c4020a091046011901c100003c82c8240040c01e20800681003d00003146072840d6511101c02011060401e54421900000e07030403c0070000790182c4028100c1c0d03202c140500f0ba00c408015242c120709004142d104144100d241d07200301d00c18080302c80200d0020305038520f81008203444601941c031108000d420f001d4400104040704000d000203000a502441ca82c41c00c50b402c10301401e515070390140c01940708608040501c240c80500c101890780040c2106503100440f0010300c24000a068550000395120380301150003e0540640f00c401c0020140403410366043d0707030b03d4400688102140b4016014800741c40d52050000e40203203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 777023417 1250 777022167 777022171
    0x221060d060c020a020904050d11070e0114060d0f0e1c080c03040204090210170c09060d150906030c0f060c21021516022a06070204091a0702061609030b 67
    0xb5105840031039803d500411500c52050341c0840d800c2e40f007144429060756201c1552000c42c030502010340151842d00302d107094400010301900b50810004050038425540714012907103aa0b1042c6410301480a455030900d00a104403446a0298082c0c1d080d00110100c1c01c2c0181c0086c0243e03625816025101d225426289410051040303801030342da2142d81d00941d0300d100c02003620118655070284549401c11b12803a00c00c0000e0a00c81a9820034041000d9640d20001510380c66000311800180c0650817084c1c41c280c00e600b40d8044441c142c642540481072024429029056840351221440c6456403200704450b10192010301038920200301000364a5400381d510402c0d0703540d002e40704a81960888a80c5244d800d0300650714500d0b4018041e50086c581d680600038110003552081c01c1a115150810407502a5640d00e0324540c4076400002d644400c6543c0e9501c2001038541103075211001404455541501107020781d1400003510032540019145030380303c0000c60724551032383e41c0c801055155507140d85c40c46c400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 777024667 1250 777023417 777023441
    0x50c0307240e06042a0504020d021b12220b03161701083708033304110702040923070e0105060901021501090221060d06 53
    0x10030896900828008885801808061114540c0c45164180807100b00d035000d0110100315003000003040041039820001002408496105034103080e00d0a80b0810244015002540c3c01440424054a441b405038044c10101621041159403801458640e5541e044922900f001c09142049204c400c0304c102c03540940b1149107400c0d40c0d05a2515a082d0007a5500b00b00c80c080042000c0448503814140c1c4079045511b600c121030001840303541003c00360390700d0780080754188651180c420b41c924011240818204003035110b42c941841101100e11380440158410740da602d01c102610080742081c0c81d8210f4022041d09804100d040003610402c0501000e40b0701c0d5108080c0c210018004a0050b84503401352040f0140308050a410055800503411003a90401965a40540c00040c0a204040761543d0940c1074510440d10300c2e44440744500100d1030310340e446030000041e156480000540d00065000707060741c07030141421040824030000c100a640075044950355488000b4140b01404560154000641c10306 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 777025917 1250 777024667 777024673
    0x80423130b130f090606150c0b1f0305011508060118050601210603030206070c050a11030a020d080315010c08071b1707080d02010603030f0f1808100b0609030d050c 72
    0x40e8511840c110b903c800402c1c21000c1e15010750400b0800b1034880c070340241c004a0008a420700140340b0007080c5400241000f0108001c500c04142e1403010802c02030029002d059141c82c4c1c40e0f03202c1c0f4241e80a000e01c503840da4a103500000e000b092202010071a01d041e2048076007483c591201701e400b2100540006088141400f4a01c1a145000701c038071480182d00d100202008030b68a80380d4039000f4070f23015004100d0010808101c120700e00141c80071549100b8a43c1018080c200b82d640712000a040c641d01130700c025030002ca18840401008500006180f10701020700d891000502c0c980019201e85004010042020740200200b8001036003200e1540f0050040328a07003400e070750325031100701d103003000300b04a112441d80043c7c0c0030081c08004021180f03103081c0c948002e00c240361950313a000d880010b1f8181c06c1070612140c4a03c0709400c80c80341c101c446810140b03191300760555659200043e02c07500c0d0040b180c24840e040c604000308606240040743d00c4071382c01400900f41e0b20380002c000c8401d60000061044180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 777027167 1250 777025917 777025939
    0xb041815021216081f05150904051006030501060c0b0a021608180301060f08060f042d2f010c0c08010203010b0325050706020306180103080423130b 65
    0x514801c103420f01c100c0c0c44031150380f00c40000a07806012080010501d0000c16180b01207420700c02c9203886464101c69040e00e5a94218501c50501e0b416405080d054940161800c1c040207142d0010852290407030340d00d41c40070844c507604c0d102c1c1100c803030070081d001800c1d101200004c01d02030b04582c3c0c005d04846c20b01c84480c0030800007513034400c5503c2d80180c2c603041c10140321145a05451030281f0030308004000740d07055000624075100100c0d480d444000c0414005000c03e1002a05000904644c034000d554658014800c80740110140501c0e10700740081a202c0030f0142d464a040c001c003680300d0300714090b100d8007d10441803070b0030011035900804038412030f00030513603c200040a08090002c1d601030403806100a890b0315102600000c034030101400c1c5640e9620305005001d40030781181c11120361075007005c40981d80340d03241c4020800320a0030707a005a100c00100d100000620070000b0141051712140e00004030b424101680f411a41420103080c1640301d150002c4085030310410f0f91180c40d0045024144c00811 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 777028417 1250 777027167 777027187
    0xf04110907050c1204080d030207031b05070e1501020c120708062505070308040602070c050d03110c0301060e0118060f1203020706050313110609031f0b04181502 71
    0x5001d4410102055001ca800780820340c05125000d040c40503000c105007010b140c1000039546500e03001100c0305155001500a007458803441c2c242c164901441e0340c42c585400c040c82e2566071402c15100e15100fa404035808180202404803046a851070140e00900b070240c81c5c2c078108a007908084841c0d4136607128034900003d914205200303040c1305265070301c82c000380b0407608100c1006c1c181c05401501e003040810403501c030009070410710250300260420801a11000107140c900c6000f0304c981c204541c00944001c10030f0800d0b6002902611102550703003035501d4124010141802d90340540521a40c0031403134001402800310707503203002c20303150b84004c00440c10301d40d54003407030381d240c0c05e1600051a03404620f400342c02895010081c0c000101010b02d4121b03c0e51170300c0341d003040804c880000c0c0182201210304c0c520301c0070b640e03082c00ea07040d1640040640d46803290421003841c003696100c14550039582050310f65022480c184c4111400d041420398412407030303115a6103000c01c1d01114860301101c5917081c0010300403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 777029667 1250 777028417 777028429
    0x90109090317091e0303041b05090c0a03150b0702030114011d04170412030e01020703030f050304110a09020702040b090610211d061005030705060c07080105131b0503060f0411 77
    0x800320100011795500e007024204149075142c0550742c2a50000192405c00c91a1a1a00f4207603000304e007a54599124100e0103000c50213010081082954980821000b18018410728000d0010900c00c400030403d490070000c00302c02c0780009200d003040c5a2199514080e203002032070303082507001c0d1041c40110040e03c1002401540c541154000a1030181d00307c18180800d0303082003002d260584240000c1428074a180e034010810300c10280c0810070028040040750070414011800030300040b00421303c089640d00ea00f0030070001d42084405034821807d000d44250b00742000780c4024000c0340c0260414405c201c80e4030064400c0c00c00107581c680e40c1d0f504180408000c0d0154402e40c0364055031b200000000503c1e1001c0c1c0c0d468441c010703040201e5900030200c03c000507070b0000f031014112101038414580361a40c00144a04203030156024002c0780d4200340070886004010301520340140d200d4202c0d11840071500c04296044d140d01c1c0621a010760240d00452500312404061551080c4aa150601100c9001c000315207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 777030917 1250 777029667 777029713
    0xf2a06072102010b06070201140c070b0d0f0608280609262106060409050a020a0f0f02060c181e0109080c0303071712070e09010909031709 61
    0x50080d50407280310141584521103440c5424051009004001c6080000b41140c40350380402414441c03500c034181440035603002641d4031480008182ca0b8100d41c0e9124640e840c2c0d20804400600c00e18140110441d41850321032181601c512400a01c0c6445400c40d100c200c0c14000d8440c0c0c0300d0400742d011094006000f601440d0003007813240c40d07800e003100b05844080160504280169288900500401c06507140703200c100125000d0700031910300c88c1e480d00c00124426200342d420040016042070100450401c1c1038004040400f090341d02e20a1b01141d401044a07030b03809900032400182c000b48081007100e0245000f0382075540d04881000c10310000c420000d02881141407800c0c41c00d0000034180880e0351303000254080208808805000b5600040c00020703124801d0b01c0f401402c1c0c4003008202d104240302c40d000d903a40c4d008245540c8400d4101100f015006c8240c1100140c803810b90b40e4008150783c61540507040c8000c0c0e1644901c00b000f24030707403449005254003d0a1085032b1199110070101c44102c4c0c0c030000d07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 777032167 1250 777030917 777030923
    0x90b090a0b0d0c08070311071101050d140103020a090509060109020904061503050711030c07050d061803051b0705150a0c02030709020d060e0411010c05070b0319050601020f2a0607 79
    0x31a0700040d0f5024180d20401003621040c14a01f40f1955550b01003c1c044070001b0364490105500ca68500005803240d0182d040041140fa00d0100b0346480d4050300403815042e44d000b03e540004103541d030304250b07064400c12a821000b82d009000100420039060300136044440d0010408960140c483c0d2840054407032001259000a07140c074140003200c0d403c02e800407070b00c0248a000c0c41c03421141080b0a0340c0c0e42d184c2c0c42a0740c0510001c050500503c0110b40c403240112994880402e20141c050500600c690408154980150040c012403c981e00002549008980e0701400e43c0050011915024585400520b110000e2100e558200720041c0c0d41400440d01601c0c0512005881c1c0d01d4600320b036400c0b181c0c650842001303000104180b01c045442070300424070310102460850596140c1e072030b1440c2001080e0340a0b980402c000300038445c8014407802e007510032100c260410445d0b41c1d01e05004aa544250840c00302442c0c009120380000440050b010040d01c0c60480c1e44007100e0102c0c900810615808a2380503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 777033417 1250 777032167 777032171
    0x2010f0c060c0806121c050a05040e0405030304020312040f050f190b210103020a290d1a030a110111150c1e2110090e16060f090b090a0b0d 61
    0xb21131401517441101070303c007640200310481c0385803014907038068906840313401d00c080030410504413440340c1c044502a104881c2d0409a9042614100d0740e6508140d07401c9101e80100400e0781595941c280c150f80c111070708504100c210a20305070134009080d507011f620540180c480312856140d410000e1446000f4041c4904550ba82e50520f03844880e5031600040810000d50004010070160751071500c0c50054070703409004601440080340041d818100c00c016002c80000c00850140d00c00c1065038024030041c0c1d045612450410240e0b4201500d130b0654a03802003102d484c0c00380c5036400c0e500c0f40030307401500030300a01100c0300301d40c101d151810f000c0b00458940d40d21170400105020b041d00d10f4201d440c12805204040ba081107000b02c00d50300030542c0e401c510349a66244000003515451054004001402c450508200f8005030700020f5403907200c00d110301c0f420f107040e007440016101d00c1040d50ba080656503a41d822103060030030311120002d91041481a5000152100102e8061425402801180310403000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 777034667 1250 777033417 777033421
    0x14060103050f010c080a020904090f06050a110702010f030914011404150e1b0a0b0703030b3606030c09190e030a050409090f081308100509030702010f0c060c08 70
    0x518640040c016100850340d0414010035403072074101c0d10fa91b0b0058448000035869100142c086001011500005014595000080d0091050540c007050190b861f0359000c0c003141500480c90141407098a03402400111070b410036445151081c5d0040c0d072001e10480e914412400c00500103400d650018030b02885003e4414280001c016030000303080c0440034800c3d4107010828080d000a6268540308484000c2030640c0e000727644a954a41b440800a480f07245a15602c0d00c8450034000c0003010042c0c0510f0080b44c0000102425454003080c0c04201c5800c20440d074101c40240c15000314452010700401d4240c8103500c4110301e142e4070b5442c2d207440f07010a1030061180311131130210750099035540b01e81690103400030041001c0d04c95108040302d041c1c4101c440085903102e143d1038016190103035100301034043d801c08142c0c49260b045400800080ba079143c8115030194011004c0203084500c1170f0340002483c0d000f0400e0f0401540151303003040e8a11414103215152850a8480f14182c44444040400240502c42 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 777035917 1250 777034667 777034673
    0x50117010b03150c0f130603020a0e0301090203100225140d030504021305091006140103110f070f02120a061409060906010317090607060c170405031c0914060103 71
    0x8104911071a08500408201e00314000340d042841d070290500d21584000220000300311140000c49800c1c1d141001e44201d80f654409000307009402261444001078a07900d0072010314a8140284c62a0580082c0a0030601d42880c40c807070000e502c881d0200310001e02056800c480c141c868500746023001d000e65100c8000201002050342080c00701c1704400c09041c41d01d8140405a1207800c0a072464146040300040c298460105041c40c001711004212003590400703074081902e601407041d8140480b402c0c3c07424884070003156480c0301c15008a03155290301440602901c40882d05044803001c0080c00600079105652540e0245400d0002426054864507142c1d07013035091085c0748120b01d40c1d10061150103000c0c6410850320094403403c040c030001e0500c41c1000200085915100102ea001800040946030b481449140c02c2c0e014142140202c8080341c4403002c100f04000c0d00d00400d51049501101451510300c0c05109903032609030b0345018001c4030340d0f150000000255a8001c0c0c01c05452120000d10442d0700d549 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 777037167 1250 777035917 777035921
    0x6090105190510031803180801111801050c150f130f020f040e07080114090303010302010f0804030c06020c0f0d050a0c0b1305060708090c06040b030a05061305011701 73
    0xc0d2159010301000e101e4001c070010340400c00410703030701d085800380f00303030b0566003421000340c50000d4120240e10b0848000d0010190001000d28050354a00610400c10750703039600b0242202e68000c100d11f00280100261070380042c1e01211410ba07a00c05043c000c0c1407520002c1018a400c05144c2c400c040c6202e410240a80d007044142007036031240c0401d004505045495a941c90442000d00c0000c0c01031500490401099032a034002154400100c0e085922083e1341e07032703041406490f032441c2003649076a078140401e00c0c140e8088200e034182c0f60180c660419804034840e046446404c01001a0100204403400c2800a01ca03400109200c0f4007200080c241c000202c0603039400c00d0a081e6002c0140541080312000c015088244513510039080806581665141c0303004411203105004000c08a0164400f000780080e000308003503004d03240d0a000c844200800c4024411548568003480d020b400d02400019400e84281d0402503200340003400c0b07a10041c181040300070a840c82a00040c6e000e8402c00700c0303040491024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 777038417 1250 777037167 777037169
    0xf0d080d18110402030402060d021b01020f09011107050603040807051005041505100612330e070804030801090e1908041401051303022701061d031c05030604140906060901 75
    0x211021451741c00d10380d0000f0000d106048507001e00a0700411a103641071804802181012280002599101400032a2901170b500460300c0c6400314081002421504030001409000d842c1d01420081c91500ea03521190065008403200302c1e40c51082c141b06600f4480c4c2800380900983c41124400c01d4070030741400e01011307160001c011003850308241c101042615800440d17104a01a4404005515174020700c00014800400701b00c660f03101000b070320f603101b14018840c040f003c070340d40c1d80b03010710658940342800c0303460740000e803401b43c006032004006010707244159002c0a10004040b0440307241d9001d0210100304400e80050645403001d0200e4204208800c10041c3d000d107081c00d1034400d2403d0144c4981c0e0752000c446000280c001e0118550b03504808201660a10300c132400410784201c03940e907403a00200381c0ca810310ba4000c80c0b2200025001d15504000440c3c00c00c1c3d590701c01c900302e0a8000b01104459980006240c0703907200c0c1d101c05c00400344c1440381842c0f50044030400701402e01d40c0780c5042800251101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 777039667 1250 777038417 777038419
    0x9021614240906040618061e05090d1e0c050a030807090f03030516170408010e0d030506030a030807140a0207090e0706020a11181501080603010b0f0d080d1811 70
    0x1c81010030503481c0c000700d01c0e5035100d40d001c0b00014080d9074140c2426642554544002c00b020b14022006e000b503c0f041810018045504a0900190307503190402c50322076841035a4040883c101d2240000045010080841d40400c507240203481d8020a03140c452904c81b01000a030080b8020030207100103180d1000704000030348504083c8620f02c0c2d2456500030040d2140d100a40040d000480c00501084510303102c90351000824141d5079141e64407101d02e28024014103030314080b18403a00c5155040c090180c0a0349225031001005400500f0345038605a0300c04000a00e031000300005222001514884a40500054686036000b80300140c10142007004803044502d00e64826404500d080004540c0002d0868419501c0340310540c4280400d004a400361005c8101d40c0c0500300300c0390410090b8001c00c085500d000c8001d036949071468070340c00241030807550107108070340d000b240b0810f400c001410000001ea52442c49461814640014144214204c81c00300c011001c03c003d800b6180b0050000144801a440d54 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 777040917 1250 777039667 777039733
    0x15032004180c0e0603071802130f060f0807080a020c070506030c040306050c040f060f090909080c0d09051f0e10030603150c0f0c050109050a030e13060f09021614 71
    0x4240c0c000070354440c120b1280041003089071803070f000411f809405440200c0700c0b00c181d112a583d100d0421007600c2400c4d0080f5000a400048002a101c1c4100903c81c0200350303540f500401600c3c1c040061020b03510501c0e10030200d11520000059644950300254401c2c504c0c3c2008544550440c07502d02c082c0c50000d0320361034903500d003800140161102c202820f02110385504081c425032240e040c080e5000101c84e808525200e180036401024401500020030b50581910261600c0130000071054030001070302e01072640c100e0210400318248045002090301c210341c96041c924605001003000030121440804c0c0040000d8590b4010001c004901100403030301043d42c0c0c024860018a95030040036500c084805104008217400600c00f482020360140800380e40000980c0c0c4280e0729400c014105200100909014200d145890140c034941071060b88155406c140f0a4054075140080240194100051000280e0541c0126a002480c3c452080c3c061039042400340c100c1103007621500c1c01114641c40c2440c0186 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 777042167 1250 777040917 777040921
    0xe0306042003010e060624030106030f0b01020105281503050c010305010e0903160305090d2006040308030604091a0106080f070c050607110715180915032004180c0e 72
    0x804581281d100c0c0d1b041c0c6000305c0040314111000c035040c141c9180b4a040c031000000108010358123400841043c5504001803085e0b00c0d54038012402c0302c604891021f2024095010340000e0f41c002d00c1401d180c202201000701d84812034440010030720100c4d500848442e4015070b180c08442d44c0501525006044003000000140707440c500050300d86c840c03046103411100c148250507080501440c10350303500b000c0c0a01400f020742c40f145482c220903c0c2600281e04180152150070742c80d803910b50119829640d00100e4541036171107800900c030141c050100102e07000301170100c880d03814102e8540814000c01140d0782e07441c41030a0a003200c41007000d001d00014208880b900070f2002044001550300d4000000345403c1c5c001592500000b420042c4580100f03840394a4941c5280105900c03d00d0840c0b4106400311040095565420b094210740c280f0131b200040e0046044100049507812031840304581451800c6107002c115680050702729a044900540b4180c7c07200c00481c1031280c8210400040c0a12030360801642c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 777043417 1250 777042167 777042191
    0x1a18030f0d0c0216030807020102150a0509010b030c01022a040c020304030b0c090f130e1b0324011a0f2115060f070204090c0303080f07050310150e030604200301 71
    0x807030203408080c01080f0002001d00c02c40e44204010b45c00203450010b040214101200c5020151030303b40c0382455a9802c20b480078011340f801007428903010304142c0003040800404142e58240000c4182d840c2850001508142c4103a141e5000345400030708147c0c00703036640c0da01b1460003003400500500105c404110038080c040161710f65030391300a60840d00301d4034085110000c3c05c00c00c0180010780b6501029005603095001c1c01c0707a03002e042c0c0d266201c0072801e450000e01510805102a429080f100c0b12620183c0b0042004912850034006403a50000d0100e00c1c6c0251505807072000d0740f02092403940c6541c2f1040d404681941c1c2c845180e002000c407000c45a9200000000400500400660f100038840c00299001199a00c4e4040709801d640032001844603566401c1c0641940317422220070300450942c00c005a0010311440c1202e10807450410000705840c1030004003400303200001010001c0c02810001c04c40555400c10030548190310440d505880702040300301e4a0714140524890502980c1400070714092 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 777044667 1250 777043417 777043453
    0x80c04050d060f0209040608032709040b13241109030a06050a061d0402030d0804122f0a0c0501050a02070b2d2101031a18030f0d0c02 59
    0x3402e402c440d020503846070701d40c041e500901c5000500ca80c02407138403000080f540c40110141803500e8080422019640d4400002c050382500d204a550740b100c50a400603000801100c400740e00250b425008007400501c80d40c803009a141208022400b050380a000405443e42c00e00031142031400c010f100904200c00c40022036540c000c254001001c0540724400a040e05007241c4c440401006174099104001c181c08140d10140d90065034281d01034011609410607181c014003015020320740c40240c1805100801e4404c440c104040e00d4401e180d5901c0d08503440a42004010b10b900300526080908081c1401d441c01800c629140e601c0a8144941440300266140d00442c100d002c40c2e409044a542d41d0110383e0840301c8100340c02404018000951440320518000c240142c503049402c1441c2c01d151300200551034005140074880288881c603410b4030907003c1e540714040c203a08611504410707848203584031003850554000d0088a00c1c800780c08a04814481c5640c00703842c901c2455400604100c442040e0514a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 777045917 1250 777044667 777044689
    0x30d0e0306180c031504060c0318120311280216231819050f040f15060b120f0705030711030c0d1101050f0105060a12111603080c0405 59
    0x4001200401c45040c603100a2203070320034a0200130296440e504001d5145000301d10241c40940d040c5207800410b144050003442001600350b0b00600c0e9008038541c5a450040c1c0c80d030003900b079804140d02c0d00d021854900c0300b100600b10011a01424880a024440d40e107010f8000f11501c04007103512823110a000365003819025819103c010380140c1130690f80c080506400702c502c50959401c18042d480d29040c0c058200c1c04a0300425600480d00240c40d1804141d40030b0b00e80c1512501c500c00480300c00b0a00289510a030b40c603089100381081d4822981340d111600403900a948020102000080c038039052014030502150f01841002c0708030214200440000c1050000612071300a1040003802e80520000400903140c0500d01d00045980f00c3d020709100030b0200d41001c040b85000e608040100b00c40e0400406128113a0750090203aa04042103072408131086545502d402400556a128000390005070342c0c000c025001c442003040c0e2a9402c42c0c9401032214200400c0000034403c2070000b40016510804455 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 777047167 1250 777045917 777045931
    0x11040f1a01030908160b0603100207050736050106181202090c0d02030a2a020c1314040f12020a0b0106030c0311130e06150334020c030d0e0306 63
    0x141c8040364900f8801c0f030705c074024403001200019001001046880c5080c68460f48085e02a140102c20038504101a4060801c00811a40250005100000c00803841c2c60720303c00c3d0149441c004034130310303400c00c42a070043c1c100e2100800d403940014400c1a402000c2c6004032501c2c4000752407003d142412508803c1312850b002803048084401190001500c1f10503078044040d500811941d0b41403542800004020b448900b607003844002d54003512075082800143c0398015990054240d09a40c001003010460051101e001140d68401a4400081c540503501d03200358490303030090300e22020b1420043e44414001a01c141194480e259660008418181040c1101c402d07040100c1c40c80d01c1801b040d00502034414488503c02c50204d000303002014000802003c99000b4060b8180d107031204818408800c00448440303250100820108983c4400011002c00100201d480840e48443d090148040c4402c4204406c0050b070207840b11142c1454240044103031440181824500101d1040100c0c0e10323550018105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 777048417 1250 777047167 777047171
    0x13060b0f121b30150a05060a060801210203011806060504050105040b01020334050d120b030c1e0a0303110f0a0f03050703090e070c03020601050a0620120711040f1a0103 74
    0x282c4400742001911864a013510000070149000c3e0780b0f0400800017210201d1044411407000580346024400550507240c00903c2804080c2d4003002420000e0050582280c0640d43d03003c805001142c24200d215002d40b2520002c40c4451400c02084203407903068204038400c61030030742d0080322a81c0000868030b60800400e888200111460104481d000b62020000d40c1003071390031040c0040040124039000ca1421a0b114115200030407040d110848201d621080d40607804410052045c1c80c2c55040d4105001084281000b03003121440842c0000300a0f03032080f0b02150b248082c00c4400d14050000e42c480c1188407000785810f00454941401c3d0000c1d24001078148079001486106041c0714a4402c00649290441480b0a040410009149120344801500140900c0c400814503242c2040c406048400c1ca50310840d403401c04021382200c241141ea0b4074810f52041a1848401c0d03040301c4003400c40c60b40140010184850041d061005a0701e030100d01c08012031070304d0104550410030300d84d03045020070280b1300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 777049667 1250 777048417 777048499
    0x40201080711060109020c151021080c0115080d05070807151e0617060f090f0f07180b1f0905060c010507031413060b0f121b 55
    0x36107042d1140304601c1c403640540b0300003060310072550300102004525030003101c030340c2540c0075051205a079055401344410020400100a800d400100b08040d8215100702c44501600f240e407850926840345040740141d945405070750300803503142c0300880010850800901860205803000800e184144803004025440100c0c079501403003101d4a80e445261000d2100300040c001500380120b03107803400c003607801c010303030400201251a2080c1000c6108a441c2ca00062405071200c0c0c10701d1595130310003046042c1611030980100c8001c5420000c4100c10fa9002025003121424035007000c01c5000c281c07a56518050a00d900480142c4030302d01e0800e06101414002e1808001e0300130120781ca14590350015500000c0420604100302044d84024003036049031318104450b014440e204906128222040c8005501002100006c69500d80100d51000e0b8003c0c014018100c5130750002d01040b400c07400c406001c4e403120801031071071041c104900360403c6003250124910400105010312500812444c00080f000d0303050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 777050917 1250 777049667 777049681
    0x1050a08071b0206030f0f090a030c02040b01020309150406080106051801030c05090d11090a0605130203040c0b040b030702060c040b2b02040b0a08010504050f0f06030f010c0504052704020108 84
    0xc0c030b4110b5140c0c02011302c4c1d62800d161004228050060f61592601d10440c4042503111000180c541951507064880811903442a0200401080f01c0070110703041d800200008100d5070740380340d1030803100c2c02c4415406450b20b081c80e500038031014058001c901840030070041ca0292441030215032140220074a00440c030300c0606c000880c0c084c00703810400b580240035a4241e008114528965035403c084c140c0e805501c40d0b64041458003a2002c0e881160381040d4010080028411203400550344075004d8a01c1c281034559441144c0520341c0142d000000743d0b4000300c2070101e00d940c180b00503a0000403c03261141024104984c034450352056002c82842d00040d0111000d492120b11403d03042011010011519240da90f101d141e0300340e11442c11980044e807088000b16080c901845014000d540c1e00d81da00202d40c0d070b4148544d200c44400b9001517071522030701d01da44995007024020303402d05041541d206502c49103032005101b000360141070140c240c2c0700d540030107001174a495003040343d110b902464030080903201c80d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 777052167 1250 777050917 777050957
    0x90a05210607020a1e1109090f0a03080a051305060c0a09050a03060b090c160b040206161110050c030d050612030a08041a130204020901021501030b1501050a0807 71
    0x6400e40d24580152001c21050907008074030f0b180d0181c01404000080c0321100810341c140810138500a01034030143c0130406075411714507001070740940001c040382d24110041d004039140054445080700004c44d18402c10482100340e01415410001074081001e55000b00d60750503460780710050001c0b68840020522000c501c2c0708030468001008054014131050fa00c07810200e010341102051240180b02c07850214044141c0c882c100ca01d854007101d0903002034175050303448440c1c4450252080c1c3e8400d00038402e06440302500400030005d0b600c40c80c1c4411400c4001d6051000e80b0070410306500500105000b14284e804011080712084020250001450340d40c240018403100329580d030440d898031021a42c40c0010740c0021481c0e0185000b600c0d44101600d04400408040e64200d03500001910207200420060030301c1c1d00030b024a1041401a07a0f0141d541c4c3e0304041c075a800980c020342e0211454014081c494209444104042c102844e1007031401c0408200034052000203402036081044120500c1500c240103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 777053417 1250 777052167 777052219
    0xb0d030f230c070e01080a110604030b1005120f060402060a0216030f060515060913111c0c181e03060e030a0f021c140f0c0604060b06090a05 62
    0x900300225000d00707a06903401d1603040410701c0ea01070b00ca2a100801c2410322880191704888481004144034112036135052100700c5110221a04000103101c0403000580044240b07104403941c405408030b10340340c441003111100b12120b0350080303900982c4441d03200260205550340e1054054074074075901c0d84083e80481c41d100b1442134039490183c2aa10100130462100030009120f0300461051209803140c01240c9041040c035540c41c0c6e401641000aa4103c0c1450304000720b003114000340000750042c0071090103407280e10490f84041c030208108480030030a541d510400c0b103c0200c0b40707002040280012541c2404403218022103100c050f07190b401e110390301c184408100165600500a104210002d80d40300c0d03480c0c10205092000c24100343c101c8000910000f50008000c0c0d481c0c2c0325900e04c1c0310b0030405542010f5800781e0070200501c2004001480b00c01d8138028400350810100408942c075040c01c0540c00c030341c0f0f58400144989401c01240300e003a0395120125055400842e07140141c42880e19030090f030401c071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 777054667 1250 777053417 777053447
    0x120501150e310b220e010b0916110d0c021905040c0c03020c0102060403050f090a120f030f03090809012a06061e0b041a0705100b0a090b0d030f 63
    0xd807001d0b0b506200b10103101580151808062041e080b0310010800c281918048002c080452400f481540c1099500804242c0b00c100d8000100040e50a0100d107040c00102c45111254040b10b440340003199021602d841d04500c0300010700900082e401d030082c0711001400d40a445200041e01d0008501070b50000b11000b0b0000800030444540410805402c10b802c508040d0090301401c0180c200703650004c200c681c030865042e0341d928a04044080d0b07481c080d400c231802854001038030550100360385560b0f000d2030310b00301c4c0503161601c50801c079441c0c02440c00720283d0380030041508007008000000d00f620284d941d00082402e0900341079000445080c506c0f0a10b842000411150881500600400d9802030003900c1400c92048046070b5000c010005445442c81603894a642c2044208451494461400302c90404100e04074507003a03213503c41e28076000d4100100c4500d10768803071031410149061300e2500000c0960140c05c0c4031070300e14007000030a1190000e101405100301b410b050029188901c02c07201d00844 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 777055917 1250 777054667 777054709
    0xd05191115010e0a0b0108040302060a0c020c190807170a0b06040f050f061507150c0509030604050312060a06120b0604050d06050105030d0e030d14040312050a120501150e 75
    0x1e5541c3c035001c0d620301c2c103440a02031203181154040301e035440f403240c5501c580d425400500c555102d440d0884014180461003170118020f0240c0c50340320790782d81000520b4448801c0040800503041080325410706015500811915808004489041c080802c440650540082c030150b5a680e40401180140c91200f450540c064030788010071043d100051034003030041c1d41c1643c0c0e81e42100517845482203144101d48011b01151003400654481c440280c0112425030b0640c901079040ca0700300c0000c0380c0b0345902035138201c90340c3e040492525080004107904542c091012140c40d01308518080003c2c00da0300c2e031383c01c0c50f02401d030315108081c01e140c4548040324000c20000d00340404074410340c10950010300080c00361510074080c01d49112040e0303108818200b514a8024040c14000400d4901511008080c0c3c8210000c98424040040418100607951840320305c031381c031050359490510000a10400700381136410812444c2c180140242401c4a00c1081d4880d164200b40c2ea0b4407400030001001980f4402000340961 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 777057167 1250 777055917 777055919
    0xe0a2904030309121d0925050d0c1806121104060906141801081e040b090f0601080613020f0904060903110705063c0301080d0519111501 60
    0x503859404000c409004d0503405a03400c0c0440011642030800c001309000d000c030401240202c61900408650304031100441000505400042400f003c4000040038404110007103031103151110301d400390240402061900030072498a0220101d5900194012982040418080316000021a80c4800704400085440a4071039951310001403011500340103446c002030034000581407424104041c1c0e104140604080c4200c841d180d0011035000c80c00078a541c800200005c02000c2d1035040e84103040c000c03805017100c107078240340c078101c4545010452011008554400401003111a1004c203e01e40c11814040714540d05ca0310b1400040c5002d4000251154401482c00c241b01c200000c0340d108904e8a486078850343d441400e8610401e80310310843c42501d41010080000c0d403600c071880e04811100c6004100d170412400f0301c141c20000d03210110485400e11030000030050140410400c1b0440c000ca115107409454001e040313000c1e072403070940100501c080c400b040b2030360f210711103080c080d200c400384e0304140180b419 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 777058417 1250 777057167 777057173
    0x30080f0901030e0a060c12090f0204090213111317060a18051606080619350105070e030a0c0e04050304080d050307030b04090b040f080409140f06040e0a2904 69
    0xd000926800700400c7e41132000740080300186c080d1074803064101050b201181665000d000146c40810401c0340e20400c80112152460704074410314000c05106d490039622507081c080306100c0001150000901c4070240911001c1d09500055841da200300e140802054140d91410503040c3c0356180b500c01015405110151580030103011500380459040d03541e2444036484c0c02c000c0c450b0480b08640b075100140d184003018007003170012074070720201e410417a82d09034618001c8212f1500c1d10741c1e034114001002d075150790600102d90f80c000480c3d80c0114044028091340640c43d1b0710100d4441c004d110ba010040741090005041c00028000d0794010840c1d00c09440c0758030380c09003004205500403903084010900e4000243e0560405110715884107600000303050003900c49480d50b00700260b9003007003140c0c56042040042400324407801000c0480c1c00100c08030505007012010050507060040c13000e40124030740300560021260000305440103030b801241035050781d001500410001540d43c414151010705c0344003800f00f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 777059667 1250 777058417 777058421
    0xc031f050d0311010506010c0201080703050606040b040b030f1f090b1305100e09070612092121020c03120403121104080607030c02100e0c090130080f0901030e0a06 72
    0x141c07403c64001c00040d40d6150040d40c80803104580a40040c0d200c00002c0c04090182d80318a4104c100101640d007856503480c2c024082d03a1103500400145540032051103d5000881c011940040c091341c0708042d800b201c04144040107540d40b0400342c3d0075494407019009a110740448865261410400784030529040c40580c0c0310721154820200003050760800100700c064085a000c054501507918544104040b19201e40640645103050781d82e00508280c0800200d29074011010701072142c2c1301c80015080c50702208404c6c41c1e12100c0d500096004000003d81d5403808800c582e1545550700125440e92610b0030200c03440404220465503062a020300060f9010140000d03004603840c00c800c07642c06503a1540c04605a41074201e0000159000c01c5040c0607981c00e0790002180d015041084034840e454000004811040070b91051590601c0062100c0c1c15040c188284441060b4803c2d141d60b8121180d40d8000c03541c07041c0c40301c05107444400308101c0d4641e84a07070004400a0295801c640c51380c98035080c2100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 777060917 1250 777059667 777059687
    0x90a090203070902070206040e0601110a05010506031b0901050d0f050307051b0d0c05130e010f200406020a03051e1207080105011d190b03010b0702011202030c031f050d03 75
    0x40301e03100707035000020880c54a00844190396405403107a0704081c03402d5106513101401603c1903051010f44001d0004280c4204601070ba4036004000100d1141002401e15041c50301000044001001e4660451040c0d00c4100c90103044440540300c020034406281041082c40003804001040f41c080090b424003032080c000b84041101210b0751810035888009003c11032448960fa00080412101c9181009285023844110b079644611800c00729410018100c60307401c5480c802c0c1c02c000f2140e56480c1c10341c0c0d081008080403e00c03a81c0c0e6520315203004e04200d030195130dc8007100d200504100000450622102003612038410724911011201d84407030038071000100c0842c04855500c00140034000000303080d803154452603005507406000820044400e001d1100305901d040744407801c8200300b50009041d22a0000543c020110b4002d02a01d5240c0d52000500414400001d0b581050051050000362002581125001400f05440c030110701c0c0030b90700003144440b0350344c02554400d601e088007800741608202254 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 777062167 1250 777060917 777060919
    0x14030f0c19030e2404060515030102221512050c13030305030a0510150302030a02190f0207080325021918060807080307030507030c2f0406031709040209090a0902 71
    0x10f80d20101920b10044e4203403000d24604107002868020078042590342c1d0180e5000010903913035100022182011a007641e0110710740764070890324443c504034101d0070402003802405840e11000007800c2281801428400d9a288000704e256490001c07071295941207045949100c0b1104100a41b95504d06018106070002c8510070045401c0c5400541820780c000d5284003035803148001c0c43d50243d2076510482c02500003c040c0511550f08000c2c0c2990500d00c003a00c2c0c034010b09140c1e50b4002805261300300a041482d503610284595100b0300c58151003109000340c5840032084ca1a2400c002c8070b0074000144d800301c0c0c11040e01101140f10f4000310303009140750708051b90322105c110240100c0d41c0d00d5203281e46c0c0b0100340c800c102c4150010702000000910410041030024068a080e00d18101180c33078a5821310445000042600d040d1007100d142203884056001c40741804841c1008030614585500c10441880d08120314103000002d61100f441c0d65590540314183d1000d444e10750f0740c1c2b602a001d44001d1207e0581a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 777063417 1250 777062167 777062173
    0x30303020309011a0102030d020a0c060501171b010e0607020301021b06070e010503040c0501030929160215011511010f0b0102210409020a200c0a0614030f0c19030e 72
    0x600b601414513400c46401308180c0c02540351900070000c4600a410100b01c64040140146030318010429034022240a0510100322102503201540e000d85403588487e15034402417603003040700c04946c5c3c0005100201020549505903200040c0c40001c1c028410050504074031241000c04080781200000d1280c030912640d1a01c0781170000d008011b40f03060108480060184075801d0040c40ba6501c00e07008201010302ca80c656114240303080c2c03d942d011000c404900354581c681c5034200044d00808071a407008000c00d500192441d0a61101144003070281401502c1c2866001080340445501c0b40d000100145da21703500800640c040b42204070f000d000c040d466580107100d080f007000110b05413074142c40d4042c03224000051515160040e881c010303410481d680c4041c010b00200503110002c10110030900e005c0080c0143c5035501000c02080310f03006085d040041044680c0c40754a050a0000003100c1d0008092200c4001c0c80e69105030100301d51103040040e510404100010300c2541d9095041203c00d40d00003025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 777064667 1250 777063417 777063431
    0x603270d0e010903151a270c0412111f0503160201060e130201020703081206040c030b060708070606080a05030310090213050d050109021e0a05062107090f03030302030901 75
    0x11a40200c2d240400f92200d042c4400400c6400403942c006e05410514a2110303c21205580000310708880045007030f003841c40c040c2c1910f04042482d06807190320001e801001801c260820b00e2814180031841002802201c0e41282012295140c3c07100ca01180078800d0800c80d44001e04400030310319001a04c2d2a840f103803140500c01100d074011300404054031207003010750295540d001040b54510b100c102059066028910002c40031600480040c0300c140c801301420301c0d05060140c240002c458125120f00101498141c0d0041036940300000c481556070041c1c5441d85442c50303410600024509540010480c3c0324000c100820850080040c0d4454990071010005445e980c90403c8160301c01d18244600404500d0024810761800c1302e040c001c018000c0c4000200b501883d07011030700c04480a641d50042c0010040040b1007803070850062300c05800b090b9100703030400400703241c2e41280580292052828003000d01c0080c084500c100283c038014800c0b0402d000059a481c18040d000754801d03034110405508081e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 777065917 1250 777064667 777064669
    0x2060a0212040b180304260a020f060706180b0601080f09030904051509010605130501091202060c0312150a450e031222020603270d0e 59
    0xc241c404508205402403050307507403070342e800d040528010100f07042e880801e00e40d2214402c040001d8000380003410101a00066500108016064202e010181a5211807207800041e110101c0d01c424001301603480c03544408171071400034050400c1014074441700106902403000d00c00000310440c0141002c0c0c032442e1064892280140e0380d02c0044448402c00d5108108020060a2603400b0342c0d07100c41c0e9070f00c0d900c403100c0c040000100610b5007a8401030004d00042920804a400940d10394020102400c0440d03009181190b0150401c541c2940a0701c94a404034000280400900407142c0941704a40c1c44070141c5003211100034507041c0c00350041d00415101ca0040f90210b901c042c40035504840f2041001031491072508800c0c0700d51408000e0300c281140c008455800c2c00180074070420b07000b84402454071400d1010800203281c2c0001c0c021000039428030036200e5000080c00707004030426010765030290340307954140007034010340002c3c0c210318000d0710416081d01000b1408100410403070000c0e5502c0c40d200400344 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 777067167 1250 777065917 777065921
    0xa05061c171207080402040f0e061314061e010608010806040b0414100f0f02040b041203031518061a0909060f0d08130518060120070b0a02060a 63
    0x25010303060618480040022800c9100a84040010400034034078000361110500b69000080da1200c02143c0c914082c0310451400b4007421540070107014040026800d07540803540d03140b10181107403428081e0b4906010031302a1100b14a441c94035014201c850909141d0354170021a41c40c0d003103080d48400003c001040c0c291080300494103d80351030700101429241d5844041e040782003c1e0080b58410400b0044030000300c014440700034901e103120b034000b85191078400c03d001910b07020422040d00031310420062103004165030990b4141c03491102c0601039483d0701e01d4298000c0c55000c002c4002001007040004d60191018581c41510f031460000340036955554000c00c55413a00303d0a8495a00390030700c50a07031142003d142c134552001000b819000d01c01483e0005c20340c4a50000d030140c0d04e000c00001d1086064a951030140e0041c1426200000802a0b40c0e0482c0e0028001800c050f0400c0502c1c0f8000c2000c0c0041d14080f000d140c1e50f4402c1d0f68020350b940c041e2181c194041c0d00040d02500a2200040e1009954 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 777068417 1250 777067167 777067189
    0x210c04170601030521040501081305010e0d020c04150314010f1a03190209150d06091112070602060a0e0307060c05031b0c0715140a170108010e1c0c021203030a0506 72
    0x184031801d05160800005417070080d0014005601c02c00d512b149440400c000b40034501c0900a818050050488501360003030401158020550080e0305180c400820206141c0c41c0804503904a50701c0d5071803400080c4c4181c051300c102c40c501200181031050386114082200e084412800044044401090800003148050003840d40043c0d03000c42d801d000030305c10003402c510031f005041d070041400c0f40d00cac0c1440d510041100c01c580010b582d0307003c00707090001140c1008a051011030a0880003031032054034002c00250740d00801480e00071030300e03210f21203203140020400640750201e500040c2032000c01c0c0c04040041264008039442500b0b00c2042d465441c41120040841e40f00c4020200603029103030403c2010036044809801d220204030300500c000801451082c0a0300c00c1c00c1c415034420900355600120302c000100181c01c4203c90741d140171000d81352040c00041003002d00303c00660314064000da81c80141d540c4d440000f030180d0002c0a02c94691940000480110b104424003032040100d61501d4081c03151801e81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 777069667 1250 777068417 777068473
    0x1703010e01170c01051b0303041b080303011a0915030a0c0912050a060c0c0b0c04030c060525050c04020d0b12071d130804090e01050a02210c041706010305 68
    0x100300401c0d5003a500c079a004003840102d80d03452650b044141b60040e07103198012601500c0d082d4105009415482046148600400c0c0b490011411075042440d100e40c0541400102e642c03070400055040d403c1d4607000c003d10510800703c5083d580301d01c0d140d540c1a010b8900801c50a000800b81c82010510780c091810504a00303412500910145081c1d643c0c14005204800090050148101c642d04c0002c15001c2d420f03106525000f0420348962440c58031b80c1104038140c001c4400c0c000140004080d0340e80680843c80c03424001c004a05040a41d42071403801c11502c162100d400500020f48582d000c84140c1100312021810f4607545c0c0302032100d01000b41c407089103014008a8103041d01e180e5040d528240700594200582445001030118282c1d281f080690159029166050b26500c3c000c00f01082840742590111a02e1819441e2104510b040c1740752940a104d15030181c000c0703501040140704550b00340d0b000b400700301641307000c240103280095513950703000d100441d158445e05021100780c5030300013010381c40c003a9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 777070917 1250 777069667 777069673
    0x2060f090327030a05150f0705090603070311030a1d030406051b0102090a1203030506040b1f0302131d0112050c010c141006140303160611071703010e0117 68
    0xb482c511521622041e14050b81032242c031140c0c0107600c035501400145031aa01c02d034000c10206d031120311420b40d10f0030014200e482c031461031801c029100c2d40000485d190300d203088a40540d6959501001e40007081c290b4007046040602100304840d0802c1c591007aa480901038507500009070b105a0341c02c0d0340707225500815000400500c1203000b241c1441c919845101c1c44c0e04005405d0040d08408102103a9056100a100788044501ca10505400d485543d401c46d1040e60280098031043c0701180e1070354443d400400c00c004000000b004e10b0741c400d6040d520b642c0b9410909070409941d034440c05520750088401030a4296403903000040b5034000c401440400765001c0701421911000a005541407440c414090f9021f0b8090368180b081d610080c025111882c040c44400075000741008d03003095400d06464405030291748100400035850100700703a42031006030301c504007043c1c2e2078074049100014000d21130b004080700d011510110460380c4403409141690030b1100da00016aa85103440c002c1c0440c47c440300a000d030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 777072167 1250 777070917 777070927
    0x901060b180603040c17100f02071a0919080703020d0f0e09150409120807030204050306150a1d060118030b040b18070801020d47040606020c0102060f0903 68
    0x1c240b100281d41d00600400714802000e07901c07203c080318400400c10589540c0c000003c41000203a4030b1061011a1504000441c01c01d4a1580c8540030322004003a03488010303c50000149074588100312254800180302c88011100b107003450500180c3e00405401c03400b500508450955080c0300e035001084a95042c3d9590199010384014007201c0d80300035018142900000745860042e031928043d0b40b20040c42480b05a0700e42c040540d00425003100a8807034410140100010070550b0740c0044c4940c0c01003071040b1170140812000001502e6409940e04c102c00f841c10704112207101520004805114100a0302d80d910784103d914402425008140001031126850001280210b2161071a003544604548000110300300c612024a1804981c0c0c0e00191550f07400251902840505000d0f1412400d06103170060790b140c5c0d51b40c00c00e8050400d08015220341500c007010580c4082010805007100c4100a001041030720341380c190080d21010301c40681405440790801180c0c0c101943c07040940724410110140d8105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 777073417 1250 777072167 777072169
    0x6030c07060b0a090c080f070809280c0308040f2c070c0b10080c061908090705040c0c300c05010e07170708030a020607050703051201030b0901060b18 66
    0x1011541d01c9a50005814000130500140e140310380001084607440c6d0b5000d03440c010700d00b4043c1200091100c410040080203201c00c11000150840000e443d031800c00b60b1944912040040720a04424060700702d54801b4000828080790800800546035408181c011450300c904440c40c40e81110800f0200d10141480721410400091000607000750852a117140c00220540b100d944082c001d858107009890040020442d091080000480451083d40c046003002e191240c003014028070000008140440c4100080582405010b494090500100204010000d01c0401850b08075110000c80e454a2844172100d40300350688a603401e001090721204201c008140ca08494003859000704441343d40d01d521072802c80410611426004e410005041c21420310500030709403402039940c1c441c03a072640003000b030000350550210303520340d2000260030100d5561041d4a03040380e440c820840c60b400a40d00c2c54001008210000741281d01807034003413000340901502d80703010350014030810300340d4200d150b92654141e9007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 777074667 1250 777073417 777073421
    0x5030a02010509040213090501150201090b060108071101111801030b09192901020c0909061b0f03070e0a050102030f07020f030109150b04061703070303200f120606030c0706 76
    0x8102c4080c001505201a0802c0c0c0d07551b600050708134075440d9032244c0040c8040710f0300308500c07000804148000c1c020704000761900c0c00002000f6100c0c40c10042c06000148030a80550104202541e41c680200052203503105402c43c0c5030050a41c950003407240102c03490301503110b8011240b0f030000080c001203244c0c030764001c1014580002840300110719180c4010b602214fd904488075000c500c640f90341c907400104140020f08094507103001c01d01c01d1744294203000341484006003050740850010492141c25602d18444407940c0510750181c1400d110000070444103d80c003100d1564a4402500e61200e029101c40041e0b881c0c0c0074014a601000e0014014000907180020800c2d0000802400000718069181c442d040b01c0100e809259030760f1611400540d006003014440d03000101804076081e00b0070780f0711080340c81e1203200300c00001d81010f4440c5000300c0c048003c100c44040241446000c99070b1075aa505160b00103812000c11b0160804d07400c0000745140c01e000088030700c00d02e0024004c034030b0507030380340d4401d40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 777075917 1250 777074667 777074677
    0xb04080d030c120c0504080601050a0e0c0913060920190e0a09141b030f0f04020f0a06090305060a0b010801060f03020d021204050c01140d0b01110304240905030a020105 74
    0x8020880c0006103040d00c5034801c4c4026080c0b1a030b29569521301b0546600c2ca410b0381a40100d0080b805190208000d8244443c01c5411042034102c1c145e40b0307400400015402c14080190040a5281c520f00142441c440da01c00340c440e1103140314841300da400028904900d8060162a81010840500101d8125106241742c03803092000a008521090311496003c08071044503c030440d2412590041c001541c0c80a100c903444c9000307a07960f180c614503204c0618641c80750041c1004000f01101c00105045644840c0c02c41b4000c0d001401451181ea958200105030341080c0c401903440b40104001310f51081c1c0c035806101c0710341406855021943e445d144007140ca6041e101130300c0302016824051442485100c0c00141100749890790309185038189420308606090b2042002d130705112050b4854001e9000380c4041da03500841000c3d0000d601d608240061b07903460409412074505000005001c07500c0c1d00c2520842e000201e501c0003082c440c00703002a040d26a29264000e891f41580001c02c090b0066103d40d0080c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 777077167 1250 777075917 777075941
    0x3070e030c01050a27060302041a04060c230a11040c03060f050f01050403050d1e02012d0908030f100503120301090207110904030f020c240d110307020f070b04080d03 73
    0x49856a06018170b102c4901c0c441d0010300019400040030400c0c00c548a80e200c0b07000c0c0000c030340309151600d8180e01922401100b1b0008001e41031849815040303c1015101c1050403000f007064035240101d40c540300c81800000e41c00c5a00c1203140c1600d05109510034410882a5400204072115241c204810410035491050350f89041103001c02c00403000030014405090442110740b00c1d21070448401c412000c0c0354440c48600c20031a803400c40c5480e0340443c0e01502004110118585040743c1e02d09154001c083d02105101810611001080c09400f082000038588a07895100c880d4524980300c50070581c03110b54880301307003408410174070050140280b294000d05403148100c003a84d00e03150140c0c0201e041d41c0021241580401e4000c850340e150140c0500035449603560803140305084048071198066824003506c64003052040116822903104116440050036145071111309481c0d2901000080d9141c81c10390b01070030607018000b40000c4000b400c409071025101d400c800f801e03220000c00c108600402e280b155003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 777078417 1250 777077167 777077207
    0xb04171903020a121409010c0305091008011e06020706051305040e0a02011e0518040f0501180e060601080a020304050c06160501051305030f070c03080f03070e030c01050a 75
    0xd09140c00c603480250445920980280c00d0495003410b140240c03c0f40d0741d10507000e011540d80c04142001c40a0202c881c6181e003402c0c040040e481504089500b030040c221980d0308440650700c070010103500410500d0480340d1941080d2200300301c00001e0300440034580700e0340026034855903091001501a0010f001005410800e454905580e0720000d815684a1031003218590001420b00081d5648490821841003200c1d60001c2c022110040040c910b21a503410901355020542802040d5610358110382c0c003081600b5003c1c0900d5840d100410205440241141481413401040c980101c43c0070481501c42c0205031120b1182d80c0d0b841e4a640f010358001441155903015000c22484555260005080d100a100000b05410340041c0381440c2100c4015200c92162403081410b100090310000464243d00d6003202c0300340d2070340400d1400c503a50003201e0700b0040410790080751900c1d04095034809544074040f0780c2e840032001c0b03121109060300c90195209060009208101c440350a130300503903248691410510034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 777079667 1250 777078417 777078433
    0x1e0a09030b0a15060314071119080c060f01060215010612020f09031b0f0d050618071203031a010507020a03111804081e040e0f070c1a0f100b0417 64
    0xb828804032540001300880e5450403440f607054000c810706940807006003000c0710300000c1070030311640d10041103644402a0030891820b004022658065540070a590f10440d00720b82446d980c44a2802000d02401300148034814542800d65507200b0a80c1c101c1e055910783c21a00c2114000b0803010758004a000040f100d010403620545490400c18110388004060360711030140325040400c89401080c8160600c00c004082c04000031800c04100c3d5500500e503031b07132461004803a054041e0705102d0300754002401c0300401c2c5800402e068058200b40b285808100c2c5020b40e8083d4140152400d000300c2e00040c4d004a401031040c00040c0c10965801c0c80c0b0380c4010a500241d500f0080812018002210300715120309005c6120708d80000c211100000400010703031003d05003400c04e1400038411a004102c04500014980070400c0d0038014003040030166000790f20142d160101072034004060030700b41c0301c00d9031151003680012808260348141c8826601340d00c1c1601c0c41d0070701c9c00c40d1150380110b84120b122502d00550107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 777080917 1250 777079667 777079691
    0x50f030c090d0b10090e0318061b070e010305011104060e040e0102040b0d02040806010b040302090a02130b072102060c0d0b04060e040b0108070b0a0e090714040b1e0a09030b0a 77
    0x610503208050004503c541d0500700000d4170300740c402466002030303194000d1101070081107480075100008081605c1d1987c40c1c000d00d201f0158101048d4068000c80c2c00380e62030100d00b0820880c0128182c038003660080c4800c005250002c00380340b183e4070074103000038400302e031000710761a040e005042c001c0c684000141c10141c0310440f150480d8850341c1c420f9101c90340083e04110703485c0103000941c0100030790310119007002d00d16008602c0d0130030001c2944190070303030000f5105026840e50114102511084002a4030360a02d0310f4007855003d14491001c84525107081c89101d0b80d480010f055109841c0c0880d09401c000310440040080d04d00800c070990b0180c0c454070080b9900055285107485036001c1c1360104d001c2c1d4507000c0001e0404440e60845489688104490915150402c80c5103c149805030307134038171440d500c0010841d00004050310b11050301c0c000090014011034801e000e05019407203000840e5504000d145051110712418440401080b013000c1d0810104400c2681d0710f5100c5000a40421514041c01d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 777082167 1250 777080917 777080933
    0x20f0406030b160207050301051005090903120408070b06090106090909110402030c041805270a0b0403030b040c0207032d060f050106032306101710080c01050f030c090d 74
    0x640f800381001200d503d16a0041d410002440100010340003040241014424000d0f00841c5004950040e11282c02107228520104110b0b00c9e6124060398000c0341c0c0c00d10345405102d552000d9801d50385102d004000c40e54916202c0d1049040326400d40380c82d010b061802101c00c001d019003110944820031401140c114030b848600055110744070b541021a034403801c2106000e60302d1509951044098940f1041299400d03550440000d10719890185081c2e00100b00307002490426003610051201036a801480b0415806400108414a04a600748288034084d08100d0341d4141c9840050804102d00390503503908035890429805a04103120761055001d442d0301d89105031b0722440e03a914a02a138540041003001e0341485985424182103079035191940038580c010f6075042c0080c1055102f1500302c000401030500034041c20b100100c00c00c19800092410343d0080481141610a9880318000c0440b80e01c41903124000311180700c08031000c00760030341e2900d07036440c0d04a400c0550542d401c100c0003001c150100f9410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 777083417 1250 777082167 777082171
    0xe090106120c0603060b03220212160509060d0f02040222080a030e040c0e011218110405130c0608100302041d10020903070b0904140c0a031a010c020f0406030b 70
    0x1110031081c0d943ca010402000c451203540b010f00700320418800d00c88015000b20b1107140001465400741142c00c03140c000120424102c0d850b00156105412105005040014084088a4040351030107010350320a4280001c0c1940d90320000c000002c4840900014a8654082c014003181034054210b4402c8580d1360711011300341c0e81c00c440324603030040c0c2c41ca000309540081610315503c0300b0346040c054103105202c0034056088401049061050002c030401c207000307150f481004000f080700206007e43d24207082100d12b0380807003050640264242000102018144820803035859070109201203e14a411f40445130180c0180c100040315540040000260f03580d0b020320040003012004a80391207900b65003061800c1c402c8041002080d00612400c0640e0742c002c94500c00b150b40051805035560040340c0020002e0144170400d0301c0455001c0e06000c00e1125110190403a0019901e041000308035202c00e203840700e280e910907540064441c440c100010b0401800c1742210750000b134408140c0030b0316607039012841001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 777084667 1250 777083417 777083423
    0x702060a080f1b0f1804020301090f060e0c09060c0106030501020a05041d01060801090c0c1a06030d0302090a061202070c080f0c01030509120f0f0703080118150e09010612 75
    0x1d964140052a54001e2600e80c00200f203c00c01040503c8100200340399000304a0310b08041c10000c1071035204e03040c4612100e403400c1c000400442d036035030b100d130354076001004401800c00c055450803401040c1c05400e0075403d406003100c0b003110383c03c0070750b0041046580d0f40719850040c1d03155281c520010000d10240060000da061070b44070181c4031406c000450341075000b11030302e01075401c1609004100c21900403190340c0c159a80e4100108480001405c00d550b03404205900825844c0304a00d180f00c03075543c20700c003e80910342c00c03015203100300c01c0440e04405074016000120760000082404028560003500940402c0040840150a141641e1241e00d03480075250b00410068000f002d1083c1840001e21401507041406d01302000907040c883e455698801000254130840100000c42c02c002d07284c103c064552146540000a640f00f45500d4024020038081c4144189a46034501224111025005480b07040c5e01c0d4006185007503240c00620601000d01411800095581d040082140300d0050780a41d04d00340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 777085917 1250 777084667 777084677
    0x1203020405040b04140a051b0f071208040804150c1a01050f1905040504022d04052d0a1b080609071704260c010e0c030c01140f0702060a 60
    0x2140c5014801583c0165803058429840c00c182c10a00407400c0c0c0d071064000314200d50000e600e41d224030494101c0030099945501010b004034880b0b0707040b01000001c00e0345074420581500c03c0c080c0810306480c846000d840007012003005000030300c02280030f5001c2c0d40441045180042000c1540c1d16803481215074042030f140320401d1400103226508100440b451510400c0c0c0b4800380202035100b01000e40310700c074020141305c2c50305c510100b0290364410309401c45504080f9001c0c505503440701889170080b448490814001d031700f0540000e61420084c0e06800700c84890300d441c0d4a14030300c070b00089950244010551070700c141c1e0307403110010311821894869855200a803680500f0707003800c00801040b808000d14a004020320aaa00300e00700e10b90703000480c0c0150f8004881108192280050f02c072440b16036000c180c9612010030710801c291030540220320210607410996182d400700c1800e044d11000402a0603010500c0d82040d90302e50700c0800020711810840310300705418080b40ba030001d032103544040b1000700050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 777087167 1250 777085917 777085919
    0x200a020c010905190306021c180302060f04240f0608010608010525050d0e01090632010627060503040215040f0905131202062a030612030712030204 65
    0x1580040c00075010b40002c0701c03104040c040b00c084400d00840704e804000c051a40108111695010921924921042c641c0092004460304054909006c614406c20750040c852440402c0321000840d06d40c60080d0381140414400a5040218803699401100c00d4034480e603407030001c074110505910a020203401403c0002c5540c2d49003107001c9096540c040e1900307448822641d07681022054000040c086401075042c056140c00d820800c9030001c0c070a0703010720381a550034514030408001250748003111a450f078814251000780305a4403a0034101d08000d2800740000c4103001486014020705041c0c4000d45841d01019507002d1000d5200e98840080c4d0144000c12408010322045141800c1c0d081c04100083c0c5400d0306092600c0c0142461848500c20320791003a640b00c0100301d0340d0b00c41d4240340802680014652201d00b0b0701d007100a540d90000c680d0114200074442c40082c0e890950103040302404182d8060034115210101008219044414460041d200400000c400101401085409500c07141c0300141c542d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 777088417 1250 777087167 777087169
    0x121005100512070510050403170714010b030a03030506030f01020c0309040c0c0b06100903060e060103050105061806091015030b100503090a14010204050307030f02120d05030406200a020c 82
    0x2100c02074015901c19040c028102c40312030800210320046030002c0340c1c01111010004d034140c07818469504003905807110081d1139290355442c800100780e0180b0039601d0440c54208948940e00f00c4601d0518070350b054119013080800b2070721a03044aa08460020b050701c00c0c40003108000c40c226448641c040001360804108c1541a1030203100700c0f07508600074100180c8138411a601c0f4040004010040c07445107010340c1942c4803080c45980b01002566006104003c0d1544205e8580d50300d1009103c204d0781036017000000b8400d0300700031105506012000e2090700080d114142080181d0000400400460102c50b000141a8601124180e100381e902c1e10002400c005010034810404840a90102445420400e1061301ca00015140c0d900c1034000201c01e00c20789c4d204204501900c103650001d03505200c1c8400c04000c0c000054540d2000e00e20842d520380d0692000035480d40c41d03001001e80603010807011310029010911740d0300403423059480041244000c2508054007012900724204010050b0322140d600303066 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 777089667 1250 777088417 777088441
    0x1801050f09040c09050901021c0e060c16061d16031208010b090f01020705190e0609161206080a0b01091d0d05130f06030b3c121005 58
    0x10000d416103020907246020340310039043c10891320480690b166500002403280b00d00f0b5040d94036555802c00e4038014100c3c518190005000c1c08000c100080c0264404984881c246070101c6244440c0908118a002c0c02c80e11040014425206c001c4610101c40303e901006440502160190300015000300d80c00c0d6083d401e041c20054403c1291000f03125a600050000c40c003940291000380004403005c048610220b80100e0030034a65a100c81c4d00018006003410148000040d45000e44007410303400c102307a55501c070070480c580d24156a412101c80c04040414003da00c1000e1441c0400c2e961040455610350381d21207127260400ca076400341c448140f2a801400029914040c0e0402d01c074140701c514600c402d101421030b407504481400c0d02c040c0900027a00c8840e070322040901000415549407000d440d503035901405000b505516400c0ca02c602421000d46034642081c420350500d1400c40a400c0e030309502002c13802c4c80e1000c070348012558420002081c41c620100c041182850220743c1c0240402c107400c044041c454 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 777090917 1250 777089667 777089689
    0x2032a040e012906030406051e0f16230304020109120b0f090a0c05061c2a090e0a020313060f15140112090c181401060302040b0306041a180105 63
    0x100f440d0b0b903000980c180d50f0f11801d44c0c0e04560801000506a200c00d00c020284d0501790901078208000e074810020704084042910b84903088001041400d040c2e10b21003252031840c0308204d04006d104040404440c0702144e000703564024170604060480e0350b100c1280708640c0c00080400c4035881d481104101c50341c103001c9019a048441c0c40003c010108095541424003640e13802102d000d008049441000c400e4110710050480722900010130804080907080010400d04c1a20600009124000c51020b540b14121a4044034401514510075843c2c803800350b4042c2d0f0029140c40e0810401e0030500c004140c161085010b800c004110004e0744424614103860090b0072903001c1d0708402044c1640c07079810b9800502ea2402c1d0400300b20009500d400c0e62a042043c09820b8200100503140c00d000218842a903502c2000d2490f80c2c0220341480f41c0c1e94200407002d0b84900d007c0d00c1e0040d1024408174a06060603009001400000001241a8441d03280411040f102194600ca0030243d500010465401e002000039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 777092167 1250 777090917 777090971
    0x3071211030c16091137030504020a060507080307050a05070b0702030706050a020313060b12010603050610080d090303030c0c0203100f06050a300503120a0e060402032a040e01 77
    0x400310174120000b07400b060185000c540d1969814140358010125819441205440b01e80e0a906448006420040c000c0c14211400c9029043c1014041105c03400b0f4400d5404040d44840c80b10301e15510040119000c0e04a031442c1d40500c80107000210008040d424014824001c0b0b0340210703200c0c08103050070000d8031405000340c41810300c1001400780e5070701041030000915400c0b00011541c203030002c003c41c0550030002d842844079440c00002004000d40422500d015a11186420360b05584502e041034444403840400c5020503c440e20800010303000381c01000c8844804c1c145080e10b000703070790007282c01c15034020841d15003180c0d41c0806051040541c820600a0081511402d0300b072400c210310084204070041e005100350641a185800704040d51506000d025805000d41c0d0f1030b2165000d404000b002e06a40510b007040c02d1032400101c00c00d00040301441640c00500520417001c0d60f0701803040038500c0b420006144600b400c050a1303240c407a8000c040d51950060000540c94000d40c9800a816409030111 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 777093417 1250 777092167 777092171
    0x60a050a0f090f090911090108061806070e0d0203030714030d0f1811030f1203060a0504051501120e030c1c050406081609051003060911040803071211030c1609 70
    0xa1020204210041d01520306a200c00075413088941003071040c1485506c40b41d0b600c84404000429584408a2401d01560441047c800402c2c00c8406298640c201103c035400040c0d50307017030045e00e00d00d482010340324a1400501a02d20740b4902e03880703107810386c111004e012115500000d440703100da040314801c035801440c1d5000304110403154061440e480c6001c08501400c00c45201d501d05004d5603040c04a100750040450071038007564404408980103030070031601d85100700d40c1c2c071710005814101401114840c091011581d864040c600c00151200c02d400b480b07082810346d903501c0350004504100010b188031480c100091201c42c280303200c0780000a0070100c0d01c0e410001c0c10302c020807005420254036074011160100440061041d6141141c0801e02c1c0d07408a42d01864410f07084030890b4065224100b540c1601d9401d004800c1100c0c003284291146110f0100b82c0d500800071f80c408107000303500700307034807c4c0661a140c954601c01e0507005103190000d01c0140c10340e400c8070300107540c40141000c0032030081202070301c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 777094667 1250 777093417 777093419
    0x902042a0201020403231e070501081506031f080703030e040e16090f090b01060c050c09070c0605040c0b03010b120601020d17070c020a150e0319030c050c060a050a0f09 74
    0xc0c00310707406c8503820f003403408106a100345003c1c003814415041a102d140e179101c1040e071600820103564129612803c3d02040c030303d2021480a2042c0011509906405000d8038503684076411003c05000d08680011084109110003098180b01030240c940194040c1d5660a5990200410803080302d0115894654a030f10110b83c0038812580543c111080b10303070755031002803d80200501c103005014903d1000307282c4070781c0200205190781c0000203946024000d008803028424070000707002c0021829207040c1d021480b0b83d995400040d203135030003143e4070610172000c540e00ca03603594102c684650001e812808a00f1400300d10410551613003124180e20120920041144c2c0c0402c443c05409190820006c20803003909100040450303000d91740340b00c0311035805007a210540f40e48000c41c21346078081da111240000c038800e81c1c190b5076140000d8aa9100b41000003245ca01443c55581510030b003c5440c403c0b03801d0b015981e224180b5996040141c071304200c440c0c40385039682d18258801009180c19603c41418072030680b02c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 777095917 1250 777094667 777094673
    0x181e1a070201170907030b0c0a0f0c0503030c070215043c060c0503190f020d021f02030414060a021305100906030b040b130c0f08090d0c02040902042a0201020403 71
    0xf4a00c088010600f00108164554650460400b203c40d00081e040c1e0015000340503042c81204014484c140c0340d503840804034802e03040c0440c3d801e41031180180031907100348049985c0c0385d49240241a510301c028856642203001c040b40c1c00302c941255000340700008295414041c102c101c000c012024044680640480340c0312018590701281040c0aa141000f425020580801808208a510440102b550180c261140020003803811980c40300d03000042c080d000b015143d0300d0000455020603106d011013282005030344200c0400030342000384261005030400c001441452001d10469010b26078401000da56054414540c0c02c800f820369100c5806052442114140a580031a650b130a5524030314000c900c00034920009005850050000d6901a0b08607180b540750300d1107a44884201111a160f155032003140b1102520180ea00700e031409016000f00440800307961161410480c0c00d0f1000b00700141c141d1142d0081001c545a09404443c1b0803210446800030030004504940c00071100e200a516083c1599 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 777097167 1250 777095917 777095927
    0x6040b030a0b0a02090d021e040f0212060d0503090a03030804051506030d0e0301060b1b06060105040305070b0f0f0d0207050c0909031e1605060a06091506181e1a070201 74
    0x140000010313030f40420340324015641c0445056507213030020a03007444c504081c454a040081d041c1c81051082d4648969101c1c8030b6400d00980d40205600d0f4806405640c0d904207220001c0c00300c8000f200e55010400010b2a650307110407804018502965840d0039500e40351070001c1ca41001000103a04000000c02000b916540014021700d507040c8503c6d108521100e400f01007409802d40da0010180c8040c0171944503450421417654401080a10013151803503102d0303800564541c071403804060015005128140090300e918002807003680a91084036107040c80140b0001ca403a044600b000009540000b8070100b0b10508121488804104035424071450400740c5442d9602e105154442c4141900c2d022603110754084181503904604076824480103560661034034503106d00c1c0482e80c000c141c600d440c4010640c40201d11501c49150701060b4612441030400c2010384190701401d10034101803089540c041445500288200141c0195000c605442400c25070300b0f144070307560340e21550001c003418071400f07001d40e0b0705ca = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 777098417 1250 777097167 777097171
    0x305030301080d140f0d2d020706142a09030624010e130e1e0703172704020d0908250c05062503080103020108010b030405061504020d1406040b030a0b 66
    0x42c500003d4881482c4452140401d04551306222006c010807c2003502e04060b001009018403446081290a80c140002c1e4015a01502c03240b5100040d12041e140c070b0340e01204101031600c02103440034185102400024a020411030b9140c445400a00d0405051110b07011070f0070443c1403d08080788050b040750085419010000c0d400c0e52480c3d11000c41d043c0302d480c14040004c40c64000d07030394000c003507c000039202d55030b4000d0710045981900b100521043c0c181c03941c082d00c1d0b100c140d502505002c11503824030851420846d8080c00c0d48103900f04000c50700a070051141c1401180300343d405c140c8864034040540c0701034020f100002c110155424a032000240b0110444042d514102c034655254514210300c0741010856a071002c00c41c00d443c2480c10185904501700a04a074800d0b82c40700d8581e80c0390304c000b03040d03030000b910000c200d40e01240101d60010120700b4007100d0f40a0140c4010b00300a1201d5034071041d1207150b4006902007206200340007941c1058000d408032080260010f1020002c5070391110b0102c100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 777099667 1250 777098417 777098437
    0xf0f090606030e0a0809121e1501060e10170a05071407080d0203040822030507090207081603020309042409110703030902012024091b0301060305030301080d140f 71
    0x400202c51b541c9036980b9000c015041d0b00c0108543d9010080c014642c6080d880b21050100b900c151000341c10603607480740b64203060311840e6480b0030740100d401041c003140c00100007001e000c1c0500d02e0116101585070b1030001d80300b641541c6020410741880b01c030140610003150515030400208111010104405c0700c01c44a041001100041e41e030b9441d400e00f2a81401007440801b80100a460002c0c100c403040130b1410280d90180080c1c8190654540c0c1c514224410361100501a01c0d0500040e8042c0044030607810300d007402401035910705218240000e017186c0560320000702c1400900020b5a054450756940000381803500b004004180c40c0807046909401188801420107480340102011640720300c0101c00b0500c016a0a01001d01c805401c194441003018203441c5541c065034003440580c1d810303c84460250310000003030902044aa072003202510035210070b00c0c1d0990741b01d2a00100142007000114000e060117070180498051004000b02000c05405030658168014890380407500a81d074111151921 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 777100917 1250 777099667 777099683
    0x80d0c1709040e0304030c05030c0a05120c060a030c170403140a02160306020c010b0919020c1e2b090501050a020a12030204060e18041b0f0f090606030e0a 68
    0x314a0600d200910801c00010b4029050615000c0b9011001000c1c000781d9118030000200b141d1200e05040c0d46510b00c0c1c1505501059400c0e00f0041424403401c500540010340c02a52a010000c0d00070980941c45400c030800080e40d5280310320f000d0740d032001c0c0c5000030005076a00d0f050f142c01c142e01c0040080c03500c01d42e140707940c100c005110130030f560003040313072800c0b0300c0d1001241d41e801c5030f890400303000075040031041c0743c295424055403860503d0210302091090200403ca0a400f481d401030150003500600090100c510420038140808110b01c030255101d407410600602102c09407060500110602d170007030b2607101d40b21848080f220ba4201c01c8100c2a140c0a182481d1a065489812450b18a46000c058804010801c0c0d0b103550726415001401034400d140c50b091030007640c402c01d11207003061032880d0924144520300403e000810410541d00422540c191100c0d035203444070040c000000040c0c1c07001d48a401d08080410103080303d40110001002103081c00c00202540c4900b154548001f03500041c105a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 777102167 1250 777100917 777100943
    0xb01020c060a0e120d021f020306030a0b13020d0f1101050715050727090c020f0a0b0a060f081b06070f030c03030e0312090106050405061003020d020f0a020115080d0c 73
    0x28582c441613015920005040752080e0300d5002c000b9482d9030301c0c0d0481620400f264000300610780040d0007201d004800c05002404581c049440c1d400105a000c1c00c1c030b44040f040a080b69000d179440300c20303403100103000e03007240003501720146404d0a4842c8202c0c90581404418408000854610100007075600b11011000c125550303200b0742200e49004c8088059401c0038880701c07881c07807001003403c0c18007a218035600c1040300285074101686d07107041201e50304a056204000b10030016851512154200c042c0840101d807541c1c440c15125241c007125004124103a001d880c03000e10340150070f45800b01c00c04042d03441902d406016200c2d0580d8003450302d0054140001040a41c0c1094882d60142100c1d00c00401942c0d104d4031608103d101154056583c4002c66003003c801107190b1900303128883c00740400404801450004500a501030740140d241310388003550900c280507042011800402c60200142d00001c0d880c850f042146001001070707000241198800c4001c2d100381c42d04215910056500034007101d46403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 777103417 1250 777102167 777102169
    0x190c02010902151206120a060e07050d0302060703110301030f02012f0c120607090e04030e060d050a231909170403140102090303031b130b09040b01020c060a0e 70
    0x151070075540080d004403511040300401a507110140500e01540070003001e4a4880204104e202e40f011228240c880c0c01c000c104000050303496011070081c104203010780b500165200d0000d071180074400e03400d6015811480c100b1002a6140c407601012011361210213042d941907494890302042c10910003030602c011510250103554400d1540390000201e0b0b080810743c802114003494856101c1251940103015a20080401d46000300720a4424030b90748d680d040d400f62916403100761500e0701900907824410b1080d0030b22500d4540e1801003014405c0c001000c901c5040c0f0703520020403520554040700f218070900d81c800c2080a50003004940111003400e0b9000d50521005529005187c41040100303080c5407118081c9500f2131110185c01102e000d0000e9601c04031900351994240d00c5840c0917240d0541041001810b0020315000310504d002d100710801c1c1c01c1c000040c01d809080303182034010605c400e00204195840b460301e40620801e040003840903012400700e4102198260084ce5032100a000d40c03000d4a07086 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 777104667 1250 777103417 777103421
    0xd0c12050115030c1d01210c03140105060703120c0e030106170c06031005210609070810060308160203011b1701140f041e020a0306050a080105190c0201 67
    0x20168a08003005256580e403044070803400000e4007000070034203100c4210b0040d409400407a1030449040e03001c0c900e01c51000011185c00000702d00c6003840709215884210709082500c92032030315200b46d442c001494828917000301d0142030140d100510814080000c3c0c000039a10014251090f001ca94011450240c80d402c2910b004855103601e81c2c0540c40c140b000107501c0e02c034003604100d8041c00c80a998102c2150343c144a450720089603211002c8a0b41082080203060003903101d00c850030780390001440c22a95483c590705014040d100000d190740700010a0200c41414450b003003001d4080001004510314581d980d83c0f2901500424070680e8280703002d0304040d514217422440003240d1211040d10242d00b80c3c4009403150081d0100ca1113501c40020010800702851610176004034030042400031940541c10402c805091069081c201101c0028401c06140800340040c000e664055200032074810304200c02e0103101941a880341042c0ea05203070500c80c5155040001046450080710f012521b0607000c2d2090340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 777105917 1250 777104667 777104687
    0x120e0909150c360405040807240e0d080604020307212004030b010f0e0c160203070b09011e080c071b030c030209090111160201020106031712011a0d0c 66
    0x190840c2180482c180f01220b203d803074510068000c25a14001d40b10024001280c41c00ca4004104003002c00c5920701090140309401010710441d00004940e494520036072044c0c0d8904a115140369110080301800290045440c41c0d1022090350210f0841c909500014004803403018104181914550050318881e680c1d0080f000e0350401e44520f4242801c2e540b003003400f5030300070300c1f05580111105002141e049042ca280c0d10413108a01c0d8485025111100320705c05661114011000320400c80ca41400140c0301401420014082030000c29140c95103040050040d1802c0591403040d045a5000c0c0303c01160801503464002c0c1d664072910351918290f141451000821007603200107150018400010010000a15401d5a10179150310700191074180d1054265203042d104030900030400d201d002001c2e89603482d4125945e00500c00032942e140e80f40c4649140070004404a14a490000b80c280f2003824004507070784c01481d04254900300c1c1e251111041d04c050180e16120034403103855045150009100d400700c05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 777107167 1250 777105917 777105937
    0x902010503150d0c08060106091202030d12020904090506011d06150307090b04090204170303040c180603020901080d08070c0308010909030e10020a061802010905060d0e0604120e0909150c 82
    0x1068161182011799840c0310074401d140001703071110004a00350040c50306028026078080e00500d103103015504140c2c0d60340610f030140c0d0700b055800c2c030034050341ba41c0b14040c82015a0041d00541070030750504032142103644100c002503500c986103c080c08440e494600180b07491085a00400307480e5100d168040f50764015680c0300d6681c4000c081001b0800d04159401081252200481c0101c00b001c901c00860303d90004890141114a404000f00071003280034203080031031f42410900040803920b0b40d000681021007a000f0031545c1c0d100001880da801d402001082e000412801c000d480070f50566001022120305005012043c0d44901601c0100f5015082c0c550003a0300c001c2035407039040c0e9842402580c03603101d4941594102d0034409422080000c0402c251207068040e5210600242010140043c5a02000603400e00c607a4802e03500103514801d00002d07004074407640c0302e40742011500b800200410f89080120303209150310300501c50007440014841c255130640300304040d460b0761507029443c01030107142510 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 777108417 1250 777107167 777107183
    0x30807030e10030507080714090d05030c07080604140c03100b270402130b06070807020a0305012c07120b070e030709060e0f01050109170a020a0b07060c030902010503150d 75
    0x2c2e001d150107030031844c810b034140c0c2e0390281035988031841124028440328800c52106010001c804443c1410001c01c01c2c0c15001ea02124079141d2007548140c5480b10350740c01545c50342c2104040c4020042403001d21001c3c0c0c840b0300c00a12944015030000f98850200107a03040c4015a18a001c090a07115121201484008603444422011440740da00da50b228003220200e102d00743c1ca08a03a80f21740c1d01c40c891100e40c2c00c2c02511203801e0204a50700d0308820340c010b105c20fa038005881340e00080011002d02482043e2260741c1c4082060720841d081c14510700860908489691700042c0c000c1c84250036a003142d0804507082100c3c0765180d200d0b41c030241ca100101071081a05800743d007001090594464020b00110341420b020764510f03580d440e20303400c2c4c420b100f8015603000581e4058200840c0305142207180040203000c040d600020001e60010340c0c079440c44d6000c805100d0700072502c881441500c0c4035946807280607050038000f01c03901d42d000070101d01c0700800242d00103403212a01c5219840782c1c2c035807481c02d40e808090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 777109667 1250 777108417 777108439
    0x109121106040b0a181a07030201060e0109021b030903031e09031509100615080702030d05040309031104140610090315150626070c02030d030507020c0d0b01030807030e 74
    0x140c210704e6201c00300d49008604040105039070b110150031000100e80002170f01207194a00003212220a60180740c2c00e90031036413101c40c0460280808c01d94a8020080c490f0016968424220385a6031206c1117004c0011a8205103c040c1042d00c01004407010f0382408044200e100d0725985c51003c1b68052003205540610501c049600798418900c402c1d03000350220400c50b580f4031030541c038080a0360301900442e260300890388051b104140c0180034154001d0200c0c01030300d05140001d10118100d41e0203d9050780040c0c40c501041040c40b00a100120b001801a102031011a00710811034500f1301e0090101c900a01810001c1440a0701c6446018059076200081a00c07078180f08800d80003800f25080c070004660b41380b10700001c81e1405060343c04003194450110b4229681f4410440c119010f00030400e0040c008291805401a50309105915181c20070303450020b541d042561000746414120342885000c4d51400300b041020a0a0b000303d941182e42c44184169110a42e18045441d00a003001d2944c00c0001455 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 777110917 1250 777109667 777109679
    0x6120f020c0705010806030d0504090c0c0b0906040c0e0106051e0f1b190b130c0f1e060f0504032402031617040804050f220c02010f0605010912110604 66
    0x500342c401c40d182640c0c0c040640d21000101500c51003400200d0021aa0801080020340007540004120340002c0c141010411140d880750401d0580807201003840b42c2201040008120750909001d01034041405055902e40c18290041c206100d1140707084030504001d100c210180300c00d0000c136014070b00c81c00030030f1740c44180c3d105092501e07030f00603014002c0300d006400758524001c00841e090015603411206a10090f2210b0303d002c814108611400c1e0f50000400b400812250354801c8020024049589102d042c0783c1100c8112034003681a401036001c100c490119a6400fa070710030191801d580d0060419480c4085c042402c60b083e481001c280c55280d0f0000c000c21107010281d800508000035103481d0700c04107100f21603110f500004100d800030041003040c0000e00c682c1c18040b600c1e8098041c042c2c007001066410042d40b0310300c001c580019560003501c3d140c5100010b9420b01900d40a104403005c1840990f080c100007030841704290141d0040e84085120b02801c1c40303c0c0c101d0000f81240e0140c501540d030f81d150f40e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 777112167 1250 777110917 777110923
    0x1215030a05033609071b080a05090102010510031128060c0209010605070b010918150506011d0a03080c030d02180a0b1603050307170f07140a0906120f020c 68
    0x140c8101c0400c200d90001c407140b800f403440280405480201070020a0f510714506840c1c1c11070400000c000a8071440e01d040005e5120300c01003c0f0301c14a51107254440380404002820344900901080c5203c096140c10000140300d01c111544030403040b242d01030401500c005581103c10311826810420100b51030009100707420060b003c12050090302c5480080c0c0c1c81d0801500c03184030303a100040020002d1303001080805015030040348400014400892145580d4560342c1c02100b08000707840c5a1a56681400755640c1c011620544480008444500000c1700400140f141e000350310020b0100c0000040e071115020050003200c1d29000d09a408640301c809880c0601c400d1454109518051040f0b06808200f0b6600343d42a00c0e034028141240103c503e405540c01c560a400c003901140500c9a0a10041d02a24015400b41e2180e0380e08501c02900c0c1c41c0c02500200140f204c15a07448103540204501800c85512040c200103840d050300b484010121681600c0004044010042640a101241c4090000c02c04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 777113417 1250 777112167 777112207
    0x34030b0901061a0301090c0903051b0906030a0f15060f030b1005090103120c030e15070528110d0b09010b01020c010207050307062105010303020703050d051215030a0503 74
    0x5008000042e12856500368070a081480b1070f0600f2014001041114032a4010585260040c82c00030f441c3e40e502c0e80c4161401894800f40c1040e5410b0000d000c0d840e04250340300303a9000700210018402d9510503128819094403078807024200010380603c910700151550801e00060244484c5070f031176a43e072400c111004000c2500c0707440ca40420b41d140040d0710b1030000e0440303060700d40288140d441c0c04000780d8113542054880f4011410301c0000080c2070b0150740c60788805007001303886800090f81d580003031a1040c10200e90016075042c0020700c1050301c40001d66580925042a4000b0191400051200c001210305c03d41c0e800080c0942000d504020340803206401c03040d0640c20a03005c0322040f4003110b006a850b07107414015550150b00c05074042208a110b050300c00303a0170560640515a4100c0103500c075040d01d00982099016920503802001040400c0005290074170441c0b03081e40c1444182d10791501900c00c06000505280c080c104801c045507030500c00c4800c0607511504503583c805264508540310300407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 777114667 1250 777113417 777113431
    0x90103030c0b090a0305041e050603010b070507090903080610020304180903020c0d12030c0c0c06050c060109090209010e1801090302010c09060305010e060d14030c0c041d34030b 78
    0x25030000725000280c00a000c4c0034959164803004d0420381482c0b02000056035a904130326844a40076000556a102c86c0019030181064100d0503544107801c4c28014a0200380b036100e40001e84c0b91412031404030b50b001c40a6900300030201d460035400611480220320314002c0d40c2044401d64049601d0005401c159400042224802c2d000d550109803c001009540c00d060038019103045131558407844414480da004070700040c21401c20051005041d1a2007a40c81100d0b04003002003000000c040d401f6030380c1044094018081848140080000d960100380d0300d2074180b2031280040c09600108890081c1700c00306007440b02041000b04150016814001d0103450b00c0c010762404196516008501c0d18030038001e840c1070b2480c90840380c0c15925000c081c080c90700840390040d41c1d0006e424840988444090000b46141c0a00c01e00a145408111007048200c0755070b8088000031034125946c5a0f001d02010820a203507519203240502100170446844480c4140d24940e03800e0b0401c40e08000c82080220b18800d4000c10b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 777115917 1250 777114667 777114683
    0x50a0603020a0e09060406051314060928060903030b06280c0c0524221205060703110d0c1205062409150a0e1503150105030c0405090103030c 62
    0xf0791250309448006007943c0c1e03815203400510010300401e030b0035001039400841c007120b905c000c10480e844041100170520032100c0e880d0880c0042c000409410807886200d030303c81e1001c48442c030000161100300702480c0701d8002d288d15244c1603440c05040c02980030b81c0d104040949101e41e01c242050b4525000781d1203140d46c1c055400c4903000e01d20b43c548a0202c88903039640c06080814090b080800f0044400f8102030101617424000c0a482e07599005031000d012102d8150751481c49098840008030b00d1260b180d0807000f45580a400c1000c0414400601070390000014100003034440d00c0c0500c50380a901c41c030f00e0b1811100b4203040f01c600e47c81c0d9101c4607040d0079420304d0404124540b54401000205540490200ba04000b0b140c20007200b94805002010011002000c1015640003918080d40b640c02441c40d0001280c8041001c0b801402c2001c80b0500d00c0c0c031207052142c503500e016220441c1030000204610b04102c00032002aa0003c5607408840207010010140d0000e036a5928004003c40380c140e0741251780034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 777117167 1250 777115917 777115919
    0xc0309030f020d050906030c09040e070801061e0b1305040c0c060b2e02031c060302090901151202060d020c1e0a0f0b060301090605070f090b0405090402061b01050a0603020a 76
    0xc0c1c03000c100f00004a1103592200c3c81c14441030100701b183d4101404410b07404108000c080c0050355603100b01d070121264440505001454400c4490854000d5800300b020300c01100c0b80c0c112014014401502601d0040c1007240d01e603d444413807140c00e0b8849400a40e04286040c0201c1029038102e80c407981c41ca8850082401000395000a001710310081280c0c109407901c503c0c901c2e00209460400f9252850305500c12030f418400308034581ca222582c402c0e241014160707200028410350900c11030a50740608440f000f4003140c0034158554480341180d01c1520200c0d2070288040c0c00b103545000455000c0c41d0f00305025500c50381400c1c513040e191100c42940040074580d244c40a2030703240c0c020407030180554200c003000855459030303110503503820340080109615550b103e42e0301000801501c5054001c440c07558030b80c1c021040c43c0d540a42000c506421014416400b84010001503469204170b42d03015034152900b94032000501d01a080d0b450823044c6000c85542031804002d000d078275550007a004c50b4000c41c0c84160700c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 777118417 1250 777117167 777117197
    0x180a0308130f15054509070f031104030f06020909250311070f0c03120c02090103020d02120d05180a0e0a0e07050d1110020c0612070e040c030903 64
    0x403400701c2c802c1d030302c03003140d1550340c000c0440c000c001810380710158001e01c2c962200c24048450007080d000f4001d140a0402d100c083d01070803401d10305c84545200c01c1d6841d400c00d04000c4409048100200c4028040544580d07040240e42070141c10398005560268218200603102d02d0700d40041d4120302c070018060351200000404144032403020f00f1190b086d03040d4003083d1b41c8201408030090301c41c2c280301c0e2000900030407581c2e00140d22103001e0204540a02e00308080c0600f140360001000080381d68440411801520440140c0d60365206241184e0b81115000d10542d03041c804100d94043c902c0c01d04055020742e1441e4101150010b00030200c0c0e20312075a0009a401c4900301301300c6003440318080c0c060310440050000e203001c03d26620034030010140d01c0840b042d156a800000f104008464801c64a41c02d140d0604080d60030241c034810320542481c0050305050300e00e0004102280200d1410303100729003800d808646410302491400441b66000341003400319a41130f0201a01920341104c0481c0003c641c10989100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 777119667 1250 777118417 777118439
    0x3021c020a0b0c040522060506180a09051009050a14040b010e1308041215020f0703030e0102030103031b150c09031208190914010204030c1d011406180a030813 70
    0x50b2400204904034038144080320b1b150710074010240302c192030340d00c91001c1038650b5820090240c0c25006204000200501000d00152407000c1d0b00c4411451705002c140060802070b000102c064914550000409070349000403d000303881b402c0e07140981011010709000c20300184014460507030328040441c40640c0ca680290f20115450320101406031101444148240503c0ea102c09401c00c0c0500c600c1c089005002207150101e83c008002d009000c0c100250110805070540202031200610400071410f5614503107000e4100e00c0811542144c0325941d9000b01e08206003003202210311481031b00c080052050794600900209400d0200b0b5545503141c1c034050710312510418140c1c4c4503254101c0300069100040c2402c0b806410500b008581461440912183c4504240b02038030040d4001c2d08850001032501e40880391a480100325a64011513800c0107003d400400305d070b141030440055806079516010031400e1000d04076040051640140402000405d1201190150107800d04c042d06040d440c503954081802 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 777120917 1250 777119667 777119669
    0x1030516060203031e070c0507090203090106060903051209120d08060f061e0c0f010e0304090c0c05030a080c0c0604060f0f1a10111903021005012103021c020a0b0c04 73
    0x400d03512600b00d03200d00e4585e80d01c60940159050a207215009200c0d61402d04024541c0c200002940d408420801100303800d00880f4018102401c18201c1c003030454840c182c54681300025004070000010b0502e04a8441c1002d15200d4030003081074541a10700b403040241400d409444030ba2190358117030480305007071070aa170460b885610380b41540700b0ba404429a80e64055007000104d01c03d5405103c0941703e003820217003c0c4013085944071010316a91410f10040350101c403009150b0208100c41f210031a400607800104448050500381800055a918404540380714440e42891a940b8010072041c48200310146d040342140c110092010310000741200d05200403903005c3c540004410444000741e100f00c3c2401d082003840300c9410300c0d0907001110ba0342c601c145026101e11010f641505c02004440a159041c0b0001c103161000e24003c2c0130035451314941d0103590640180858a00480726042c0080500802808940d503810b2400102c24001840019403196000d03181900d84885d074800046204c00c062040728 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 777122167 1250 777120917 777120931
    0x3050604060e04030f020309120606190b04230a0b120603010203060307060e04090c030b161704064712060408031806192a050c0a06050103051606020303 67
    0x10b00300c0c1e846880446804144074190001e44c00100011030031038881c0e149904200b24804010007032810020180700f1042c04515024082c1105044103100320a4400c00b00e50403183c080d9408070320450301d0058101ca03006103112241c1e115a4181000038101e4202c0301a10415501e5002c80d55695110014107090b0300c421030b100350341030b08082c0040c8509400b41c074007004600c0d005400007031516640d55824a445905403c152a42403040003001507041015445007100d0708285413000402101280320903003040d0140008103803d03102e510782c42803c441410314981c04207803d10070311308019400759500c041600712084070004021800003050203041086c218025048544020603090b5150b860780e00c07103504058180c4420041806540c10298070070040b842c000d0307a84802207076195030110f080d0700803100106001c5803400c0041685c0350505c103010707800201031042800c095542c0e1441c00d0040d41000c2c400383c0b00030310152410b0004030500200013220140c44204881c200007103a10340200b0799903804111010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 777123417 1250 777122167 777122189
    0xa0606080615160309051002150f0c13090e0c0901050d0f02031f050604051e0406021e030406020c150408041a1b01050a060501090503100507050c0d050702010305060406 74
    0x228419060801c1410401080d02d5403050901800080510381511001000c0e00050650b04081c0442e181c0410f258610701020b000030030750800c0c22840b82c5040c4400a0910071107001a00c00161465115022504a4040e55801064035910f0384910070040418102000051107803c822160030704001958606a4400500d40d40803450f043e550a050031500d084102c0c0c0502541807d0001c01d400070b0000340d8111803482012580f0b240040500049960051250910080000036441003070041000c1c0d5810541040c40943da500031298542040104000e240699a40001c100018401035a010300f81804141041e501c5004034412507080000e07007a40e0144c1103071401c110412400e4a4420f012021515600d0000e042c803850f004078071316203809154280460794440003000540c0103240700305005041c0c2428810b454604040210782d50301e0300d007944a40c8013583c410100311144d0041047e1002c50500500b201c41248940e2130090040e000b5041c01c03400300342084080b5005141c680105070a890202c100c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 777124667 1250 777123417 777123421
    0x120a0e04020d0221011a04051e01030e072d0b04090c14070b060f01030516180312090603050105010804020f1003152303060403090312091e06080a060608 67
    0x4000c0254040ca07003811059034200403540c40141003880003034030451401d903840702c0c0d585030008181c000000758085007219002040184070f1681e030301c3c0508a0394003c0d20741d9451300107050f0780140c00a03d005261030b8000e1055420014000da4800c0304a02414030358000c0d260781014400c51481c140390203009001d802d2000740010300c0103d2080d13102c201a0082031030800c01b14400410321502e55030000d0420794070303907600c0420400d007414880d622044500082c1780400c164942090105101000d003150601042281c004551096a10865000155401042d04c001d0301301c410b840608150814416100401c1c20310300006003a41c040e00d0140c2c400d0790040c200b4580c1104c91001c10001c211102c910b0010302d0350f56000305d019007542560b07a402420807013541c44c1020700c1c40c100d203114101150350543d100e036001c40d0422000951100c1013200712944200d21210f80310208405482c0800c00790044a0618009081a1140101b06c3d41c038104440480c0c84000c1252950200c040a8804502428001c206d840300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 777125917 1250 777124667 777124669
    0x9150406081801111c0b030601140114090324070807020706050c190302070501030b19030b1e070207051c03021b03030409020c03040503060708090c130b0d060905120a0e 74
    0x1c1411050040070700010303604044c1e0b998041507400c0407107880300c2404403030fa11418036001d80c07190b25041036045004014542c07424684102c03285031400328504204002c1000c1203180010300585100c8a8001c0681e000ca4501c25403920940c280000500010018940490003640c090a0440e02515556000e0054242020343c00d88880e8411100b142d540d100741407200c189030806811209907507102c1e50117050402d18000005081e51001c12511b0b218007400104807400c2c0002c60751240407a079202804500941d2400c10034001c002865194942d00c4131041d00f00920281e01040c1842078803821151500760594a441d59640d000c0580002070140e40141c0d4175804100042c0f0f410610070f80028100c83c90941c8030500741040e40c00403040d0354516880804e09000343c0c58207000d01684641640303400485441d068000695500d420071f001030050421002c2081e0f00c034450341145030303054409003200002a1844c9800c40c01018070b803170107580b64000c0d441c84411a92a45049688040459480184021500f8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 777127167 1250 777125917 777125941
    0x30708271503010317041d0906091f15050d060b040606030e0d20030a0302070c0602240a181209060e18060a05030607270b0d150b0c030915040608 64
    0x82181c90b0b14110620001858074101d50b00c086030102c4146410001e810308d880c465182c20005440c07882039030450360b420701503944510210352000ca404c070340100b441c01c05141040340c00741c400e811890300140c00c13a10300424803800c2e41003141001810360f030400102c2d0703031410120200c034235844112901d41c0084c60f2407210a0b2203842c3c0711442031040300300e01d4603969050243c2403565015107600ca01082c0c000c00e109091244d4400020024400c50000e023882105d042100b01c1b480303940e0011403001c403450310302040b041c00f16a405904006a00b8244c1604041c550901080e910326900686000804245010500d20712491f940b03090b00c4000351030000700449a941b030302400700004045a400c610b50350400100c0d55010440e16001d42d100b40c85401c002070324551030401d10340003802d540003030110100040100307071810422282e805059200004040807003070548a407041496010758120342001c107668180c080003000612110f5070455803100d042080c00030b81d031031078007441c42040d0101d40e0304000507405c19110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 777128417 1250 777127167 777127193
    0x706020c0d021902010f110f011d0613020303160c05150d0e0111041809170c06011406030a02090111120c070f031104020f0705011b111b010e01020307082715030103 72
    0x1607015238511640300c1040390708561101801200380700c54101c0c05540514103110450700030310780a882112002954020035668426a5080800e14100024070400c0c070000181c02000750500030404c28200a10042c1c2c1d00b002d410690100c88041d150500300c9500348014442c0003040c245213061181000e1829450280d03d01d5451081c40c80c3e40c0c0c035446000002409148490b078040c004c0c1c82110b0701d400c10303101c04620380300050f040802e004c01c1480409466950300e005a0340d11158000c03000d69039a00c8040101e40002d44403112265a00c55010700402c040000805056120200000ca4015075521441c07480640080d2001401d010031044400c1c0040c1030540027010107240d014019480d142c40f0382c0c0e4050031105603140c0301c0c0e00484200d402c05c01d01544010b0426201c000074008080f0255130450314101c2480b841c6509041c08020180b5041990090091724811074200e980c254a4440c41e10031409180742480d01c4103044124106824480d2510001c0e80e12004108421a82183e0071590341c45c01200300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 777129667 1250 777128417 777128447
    0xf03021c0c02010e01061d09030a1202031512251404090201021609020c0c040e0303060d290a0c0c051203040218130b0a06080a03140706020c0d021902010f 68
    0x202d1000c4e0340c48aa00f40951801006d190b056003002040a003103900c801c2c280030f008034181307400401c04030650350350102506042550103000142d4030380340d01c040341d5000002e03003803c0c5810070500b4885512a040100386041e079905005030407030a1005900c8440c4518186028078003603222a00b140f00700300c2c10303d544070110107072040c0122440c001c8030b00354010002009900c090a8a6000102c0d602010018000c03810000d0043ea010f02c50003d00c0042030743c803400000c14550194551510b0182800500080440f401c8103060003004000c1e001c06401500281c100c8071a003240d4148034001141c1485040c403500703000e802401600484604035505081d80c0c0c00500280d038004054400d143c4d040320900c1500e4000e400844215a251015280c14500403000820860704140782120800c20a0401b003034001c21140c0c54503185e204005d02c0300e00c02145008071403000d000a44042500944c4104c00030b04076080c2d043d95000c40b003000000c00d024680d21450998003c0c0000c03002600d00310302a0050150001c20a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 777130917 1250 777129667 777129671
    0x150c0703051b1204090b0306040f0f0c09050c04030501060f052d03120a030f060f0501050901020312090c010207090c140a0c02090907050a0e090a0b040f1b05010f03021c0c0201 77
    0x141e001c1240e842c0c490100f08291042400041c1000216104d10034645010340690140920f840c0c50f0321290788100708a01d010741540324001001040101c003160f110060943c4507002c00890510140e51000b82e0028001200d02d0343c81c000000c030341403021801910440f0347c01003007482c0030180fa1261181c8040e0300003103086045400664820555814030008001e80d480391003103030301eaa012060040681f6010000030010b6841d00c102482084100311000040ea0800e00b0030740e03900c200010040b4031f1441185400c000c05d00d04441031000e94070000c40c1c030460b181403d034200c0b140d4603283c240701c2c01100d8249400101180701040d10240d0005400040c09030134034103007414008a00181c008c00e251000840310310302c0c01d800502d820b20451829456040180c000c003041c213100c0d894101a0949d40707040c4408042d08405060001404000300703900496002548030191201000003280d82640340c80c103034010680407a00c04904005614270034405d890741c100d50101c4c814481c10000070000300500222617400c007195 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 777132167 1250 777130917 777130957
    0x40210020a0f201009030201080601091206230903070f0804150e1905014415010e090f1f06090312030203091e0c0918150c070305 57
    0x95100310b07001c2c0820b409418440140108204210a10803126007038a105020a02c40c1800c0c4c164025070315420303a0346c20308003410740b0b0311000010380e03107044103610107105610310090310f00c200103c03038100022070702c1c550355100d001d0704c02c4021540012100f00d9848041d54414000d800c0843c4120645801007400745480e64942511002003002c041040c1000301c02080b0a2030350080c450030042094040d118141010394030245c2000002007507801c0d64801c1e00c02412440110f50306100800e908440c036050591003030321000b0851240050b003100c0032030b2140c0c000340813040c820344154000d0981c201e068074024650401962a02036500d00b004010b44a0348804a0701e84941c0703140c01d400c5a804021b05040c1d11031403c2546903190000e14250301d20803610806006000303000d0b51041c0001c0d40a811610411008441c00074607020030710b010200036290350703c4240311060000321108040100f504981e030006490f00d8103201107404501c0c401c1520f015125800c10003074500468030600103003445508021210000e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 777133417 1250 777132167 777132173
    0x40b0c0307090b16050c010809150910020a020708011406090a0c0c1401150803041505030405010219080f090708031e04090c020c091501020a030c0f06060e1815040210020a 75
    0x6904656105544d00c44c1124012041c46410850911007800918058940d40303402d0082c01d48804120202040c0c40c60038001144159809000c00445032491070021034460b004108025a186001d2183d01019441c1c13140f006488054411001c6c03151502900342c1945440b1310500d10000d15000442170b0800c840014990005503940e004c1c1c0003400212030000c0382050b0041c0b10344082d5045d83c0d01502c038070341c0100001c010441008404e0b41c03041800e82403d5480c0e80c0c1e981003c0b8064440c02e080c41640000008410b080742c1d800242d03c41c021001d044030050260380704c0001c143e40382807030300a90641c0d92050007a1102d0100001b10000b104104150441c100713a941c12029054500114852026030803090500381c0a003000010341740e000030000980f410a40180f130001c2d4032500c9070030024003003240f5070f41c0b50740902c100c4440c00c10340c55a10240402c0b0075640c40001c030905c50f0040d60030710030240d803130031240410040005105071041483c10329040390380c036a0390800c41182c03044000f042c00d44c01200401404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 777134667 1250 777133417 777133439
    0x4181409060106030e1902010f12050c0a1d030601091109130c03110301060c02090a140901050720031b0a0510020c06060406380d1a010206040b0c030709 67
    0x614004402007466504080700501528100110f02403036074001965410100c10030f006400a9640a090034000e0922080e4102c3c0d04500c040e080c00b40310b03802d240521001d824458020400d00030720713a0701c221107901001410107028110b840341c5581984050300611411141e640700741100100c3e501c000c1c0c6404c90100210340c204040400181030165a101240b220542501070103862068800301d00d881c542c1810409415030102100c041d0040210b503002850003130803540541c0218003c04910001e034130345042c000303010701003c1354218001740c4451201d280343d28901c41c41c994541c09a5002e03505240801466801c40200200008640d2040142610100300140001c0c07400812448001d41e43d04440f12039a0701c0c2101c040c100d28022440c041d03040221500303111302d02d165070001141003800d00c800b00010305090b402e0082d40c0f810b0075100240d054240800da500c483c0010044140e2050b41d0364501c0b00680c0c5a200489026200c83d411000080b10180d81c103009691000d4142081d0400c01d0b1a0261500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 777135917 1250 777134667 777134671
    0x1d01051204141f02040e0c160308060d06020c0d090e1e1504062309060f0607061506091802040f150c06020d0203150d170717070501150b0c03041814 65
    0x3c0f0859001800340100a0b206200e50b03407103007402010500d05400141410010a1105c0e070190400400001244071580e450b500044803a410810640d1584c00505034262200c0459503080089000c08000040e014090343c040d07842220395100c0710560050a13000e61a0100000308000c0011690395141c52059a45100f030300d01620740e007035011180e040c00300c1810781441c21003941984034000150820200703070350304607111080365400d80717156483c0c812070719000025040e0044e10702034485002001003039a03980440743c1b000300c50780541001c100b68100350510b0104d2003103024a202c0c0b00744041050000200c0900c4a050585151800c1c20140c00103807651000c0343c00c0f0200d1040c2c19600002030100d2402e82001002200004459500505000741d482000d014903500d50810165408100d02d014032111094540c0c0191b2401902561071142d41b809600078540301c900c55502a004460108442c8405410b07241c0703503580d100c000c62405d82003100300120444030444d085c2c1441d8480d1038401c400014900164 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 777137167 1250 777135917 777135973
    0x140a032406020606010906020a020616020f0405150f04020325120501080604111207050f03011401090c02010e060c091908010207060c030606020a0803060906060405030d1d0105120414 80
    0x100580c28044c00060640304180d00c032000310740c04400454007595a090448000c1c208081100f0b40b080450310208940c9001307140c0d40d503072061a0500b0000c8a080d8a5a294101d041c02c40784695001c1040c82040100d001c19140076119018010121402c80c00c1940d0340c011514180c02c01920402c60707000c220081e200260800c0398140c1110042c88204400105180c040010803510059062211240030381c0d5204280308451180084100c1c803180ca84081d80310a6004640741c08400881d0303152007900c0b000d04084425480158030f40019203000b95030100c1c8042c0140d481070344961800844208020401100d0940e40750b00702c101c280300040861092008003031680c2f00d200c000c183c01c1000b610190450380158002d03810b40d00000d0000c400124a02d044940c001e4084440360010b8507894085002405250080c6415120359545900c2094000c900b08a5540800e0b00003514020030200445a502642c0041d40100c0601710100b00000e038242c070a40484003c010458000f8816016450360381c580824200c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 777138417 1250 777137167 777137173
    0xf031503071413020f030622090b31140c1e10080106020712080c0102040f03060501050d030804060b310506030c0d02121204170d140a03240602 63
    0x1210b03c1c10070200c038041c6050654002c500f8407a078203a0342a001c0c0700c0249002e00c41c0c196000340b070055075500d00010904149101d001c010668031441c0c0900305190644410713081c15168801c100042c401000c4040c9440c4030700a041111445581c1e407207940e43d904003001e600c0c07070003680303000c038a1a140d580c0d01607446509a54018100030703201041c01106240d1410143c00c02050344010311009800282c15403c69480e096425164402801c140010740103030307070905907113500000c5c0000c0d105400340e0003502640d005c0c110402160b42c0e900108102c1241120004010500203000a80030403091342c4154803900001c0e10b80c040480013a0110f106511880c20800380881d0703001c0e1080f488459510032164403002c103030020002c082607040010b00000664100038400c00c81014580a0403400b844000d40d01e01d545a0301c0e540301d41d20b800c061b16040410080c03c0b11240308007401c11499074800c2050b0034071054a6070845241454203a0200c000c1c04650300300c5800c04200788001052034105103075000c0209210703409 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 777139667 1250 777138417 777138449
    0xc0c030b040c090c0809120f0403210906030209031209031f05100e0108150702070b04030302030405090a050403080a0b0406050310020a020118210908010207051518030f03150307 78
    0x30800c12242c0c582509820018000c041001800340007c2820a070418082e940da21003c0c050440d420901c80c0c8d80006041e8084c0241142c00380b042c030700242140d41000c1e158503580700d0f01e90800300c0482c041e61843c960302d80d01a03074410401c00c0480d0010000b04802030142c5a4283c0c0f074041040c5100c8000f8035002200d56518100048442111030b010090044401d8121180d450401b00d07036540c00e0306a94071802c0b01400000b0074901802080703c10024040d1030165600d03140d0300c1c10080c0d142e4202d80305160140000e40000750721280e00d8414a8412917141c0c840c100b09803140307442074004190594409422559501022940e942d007040032000f603d5000c00090380e44c2e080c1d40c1e0f00034250b40c80c2d0443c2200c4403105101020008221500340c1c1c204c47d82d090000d0186d1a0942021a07250700298028644d03544002440340070710501040495021410b00500c1140e82c036400d00900360500c28846e281141d410500030f00031030700c0c1a10021900300840140000c403828035500000c1c01c004440e805515103289403a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 777140917 1250 777139667 777139679
    0x907090522060506041a0f04030b0711060a0b010507060b060906070f02130c0f0f031b050307020c0a05030a03030506060d0203010e01030302010e0d050403060c120c090f050a080d0c0c030b040c 84
    0x1540c010f400c0c1540d10700c0c2824a0404081415007500380b05110307014000c222005001c0f82c00090f100210703006030302201030741000603025021100410740c801c00e50083e0000280e4108140c0102414910b0694816290a00c151515001400703e42c0b58a541301c1c0d41040181d0700e5542d0200038041c95801100790201000a5104104c8504102c102c40f420450038203007411540e84c0c000e4604505a030403800d000002104c0c40e0001c60003060359104140b01c0c2c4680000c4d0103503c40d4071a01541c450365098081301d0440c2e0303445041202c550f2861081681c141d001010600c00244244c01458011001410f1141440416042c410584e003013600b0841b61601c1070401002030540c240103180485e0401005890380b02031204005041e07125500010740f20603154004550041e02c0382964900170000d00b08200320210380d5003402051440d0318440c1004101c28a913010509141a02c4180308480405004280480d40880190307941c0c102942c0548a909900342d0002c04503054414180c0300710301c01c0c5029189182001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 777142167 1250 777140917 777140921
    0x1106030901140106050c1005060d0b0a02040803191101060f060c080f03041202061e0f04152a02030f0d0c02030715050f0703140601110a020418050705120c0907090522 73
    0x1f07000420740303800c201c01d104007911070007510404950441721510407651001d088001138030855005080318800000c480004110540415141c9000c5948000c040300c2540021401e03502540280680a08100c80c1040081d0085a0100d6401d200b5000581440c0d000c40040c04c0d00d403c100d60654042d030070200c4000003158144941079021204483d01c00c0343c10150040d041340ba18009013101c08030858040400c0500580c000e040050082901040c80000144010300c030b41506000c510410414440d10ba182c42c075400030040e540c1ca98401000e4600308180c0000440242c110f040c17030403042d800208458004911400450182241d820f200401e05042c900c99240c40c10350000c3c01070f400c1502d8682c0d1641b4090310b80010b0390708400b0929100e0612004c2d115100c0c244402c84d14002d5016140c0a124003100800500843c41301d8042c2c410b54010343e54500a0151420f0044603801e6150000144030b80c07545000c0f290f060b04a00180341003101d641e15232020031544041408a0f90614044840b17585a02c41c04d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 777143417 1250 777142167 777142183
    0x3070b0c011b0207121109280b1327030228050a120219050610090e030d050c130305161403031e070f08041503091106030901140106050c 60
    0x11402c503109005008000a440d507205008031a0011001c803007030020310001a600b01401040180303c4481801c0c071010061010041c64511004a84000030343d0b418061103125500301301d01c0c09001e13445040c6c0e00c081607000400d5100c034010500c0040c1d03000d18a03015a080e503515407840c402c1d00103100c004289400c00c80302c18826002c40c000b803007d044000e8005800440c00784095984030010b4101208200341c183c1c02d010305940d920070f1000c0d10769203e00500c14006600c5005501c448401011a612524100700362913542181000b1540b0230800100c807802503500841d40311503446002c90802000d09500c05403180c90b0760065550b944005107004012000551000003000300c0d90048030b1505158002c2a124041c40030641c800d51140c0c81600f25a052080882e02415405400d40c0c0ea1080e007440c0441c030380d40181c01400c1c50b0050041c105100d0602074030800c003407660041e0000460308203800802c540d5500041c140000b6548602c0041c10500800c8402806820552a01c0e512284c024803a50710341442e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 777144667 1250 777143417 777143441
    0x5040506041a01050f01050a090e1504050f0708160332060907140d06050607060507300c030e100501050f0108150906010c050712030813200f03070b0c01 67
    0xb0b00401040d51005454041d0300f900f820103039107582c10744800781c0302031203540d004410445130441001184848540c800840741c0045404100c280c80d111108450103034101d541801207076170f06001c1011191100e10010a84529150100742c100391a442d01c1d840560342d501410b03085e0190103c41030b030130074510009a40300300c017902d902e6107520b4803500c01070009101d4500c002850b100000c08060704102c0d82c00180c00b0702000703818550303624035614200380113000850b07076140050502d17411030f03208200e00121002e51018045087c811801904200303001044000f0702001450781e10300d02c4041044d01804003004400142000003100d614000510605405008a10b030401026004200603010003100c06549507500f519458401d0f916940166110b6003021400707400c5100d140c900081e05040c1e0080860441d120340d81d010055201c0c0c85030100c0515000d4401044107040004440e01f8030301400d002400d9440080844501d80c0181c03000c00d040c822550031081c20031400041c0341d28800803d00035684d008075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 777145917 1250 777144667 777144713
    0x1806210105090f090a020105130302060f0a0207050307030804090f140a0501030311010b0303042d080d030605062503030b040e07050f0306061e01051e07110406060c110a03060504050604 81
    0xd440c03030000d61036603500c840007410308c140821120b41900342c1441781c0f0007459000d040b90755600c010382e40c202a42c3c0c00c007000d08bd005100c1c086e07020500f800c000c00e0260440341d0012105007082c0c00c00c1c401e031000c5c0080300155180103556200c1048845003140c070090041006920010700d650450600400d10044841142c10f16030421408410300e03180082214101c0300c55000702212101c08011820016000d00d40c2c002e10f414611002103200c0e00c010419501c081d0440d20100100390b541d074184500d07802409084403418020303810180314520000714200d000fa00c80c0c60001084615400090b0482e0f611000c17084079a48040c405120508049140810b03202d070880060805192800004508030440d51540c07003031900c204103c8070103901410948130204408010701440308000d13401da000a130007181b81580c82c4c0c082110f22041c01e007418880c48055a42d1583e80c28900003003910358400340c810380100d06800c049500d200101040e154030500d030140344514050b00f014100347c00d2170000b801c074544840240038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 777147167 1250 777145917 777145921
    0x51c060c12090809181e040809040207080c0f0d08040828050403020301180507180902040911010f0c0c06052b1401090b090601080c0c01060b0c100b061806210105090f 73
    0x10500044103259001824151b24507503194505a401805135242c0190001e0000c203150f41080100c00143c200305001c0d004881008407410b0569503030301e0131403421201007524a804100444d02500003002e220407503112459401000244c03080c2c012a410101fa40002c0000c9410701c1107180c28010b1861540d05640700c0304408100303071141601c0700200e114403240303103512100c0000885c1207604500220bc1d001441045500c0c49030421640c6c40501d03446aa0000710074983c1c01c0310850043e10a0101150820703000240c075070030068281c50316401001c041f00001c0e03c1c542401c01900d1110f500940700c0c0c2c03692101040d503414906485031900c81c11b0300b1200c001070900400b007020b0340707030126555400705091801e039115407a0350040e001140300391206100c1d076509019006c0b4160041c000142400520030044030000c0708085541c10072140e05081d01a4440010407245ca11660086600703101c01a00070026894083c0900e94416100200c0c0880b545494030352004104524101c40e0300703940703c115031940207894 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 777148417 1250 777147167 777147181
    0x30f0106080d1e03090302120d0603060c0804050a03030c0509060c07060e030712060c21050402100e01080609061207060f0905010e0303120a0209030a060f0501051c060c1209080918 79
    0xc03e030700e0790b40c140425541d00c1c2c500c42811703c00c21428110761110700b04241e1b50291a0110342c0900303200e00050740c0b807a00340032070103d03401d1161500c07502c035940000107000020000d58045000c0c221034412417041003c1406041119614100240314104181c0b00030001e0518000c0050620403600b001d8607c60f070072140741000617402c200f09240803203500c40b40c00680d64407000415508121804d0900e00380082c42203207017004014946c003031801345000301c0c4c089040071098881160350901440b50103001a503418082013080c10641806500064001c081c00010b0300319101c45494120654440000038004070101080c3c00c1d000b40c1014041c2100b131074403044042000001c20b0b900c0c4200c090180394009a900040e00b044c0c001d5042d1028480c008042d21440380203030034548042c0484030000d0800c140780c03c0000405107446c840103801c90450140410910125882e000000d0031400d44840038071031281682c3d0f1b902c0d00f0070310070240994480c200403a01c0e40844070030303c007110640e1004d04a2030b60500c4280062 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 777149667 1250 777148417 777148457
    0x2010504062a06020307090b03090312040611210105031614040b0405091e0a02010f082208040303020d1d101101090b16050307050720030f0106080d 65
    0x645100c1c2c02d1988800000c2c115032081c078181c004000703038100d070b010b565a010001d09030021405502959141036545850303100c01c0310f40c1e00c000c1d02c0c80f88480e802009000342c070f01041d048035948240035641c000380c1d400410080c2e40d0703640c2c045194030001803c0d010b0485001e4110140d0503014210a4008200e4003015401f0310061000a018012400d9402d00b41c80036150385c0c1c3d4010401408001e0014131290a281c1c03842d40da07070113801c010b000e400005039550481304500016032910203038050f5106c005041c42007030280c4038044050008020300480000c0142c81202c40c2413100522441804990f0381d851642c02c0013810440300090500420078110300c0c0501c4085003101d640103a444c100c503d0030350b050300005c3c1500c400fa405507154032075500781061607041c48003d048651090103460481c00b030380c400390a01161284411100d01c0c000c604280640b80225101c600f0006034070741da944503509000b0614000900c0c0c400071002038259030317441f224140031030328041c0800461a4141c1c1444500900b02310006c0c29 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 777150917 1250 777149667 777149669
    0x9060114010206180f07060201020408191a04021914540a02030402030f070f0b0708070204290406030f0b0c0f0304030306030203060708041a060f031b0f0d02010504 72
    0x41803140b0041302c0720f00c201032085c0250f44141004407a0002d50790b14029001c0d400c20320524100e0302800021154004104d054880031903840304601860488000540da110103000d041680c0200448035840b0303802521710802c00c040c005007003402c0004600c01081040000e101803290840004896200481641c46218882c003001c1c00b6602e082c000690284041c8030905443d03500d85920b40704010b108050038268019070041e4000e0b0107807030300030041c540d2075070b03503404107204089400860300400c000c1c51008001405c0e4607403050003418030b8202d030764000030140d031880985a0103203258510309880b00070001c101948220310640b824480c952954507060f000d0090000b02808403e14403002924415840c8126000c00f40700700541c0380c0780d041070304000b0011b20050204902038850000410b03c0b56014108852240d0341c8070b80301c04010000d04800d40c240c02c1001c1c20240d041980c0d1550212a0b680521036082011170b2281308c400b41010380c004221100d0003801d02c0c60f02403100f212104000d070b41d2000c01c582c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 777152167 1250 777150917 777150931
    0x9080c1b0a0302030d0f020309042406020607050a080601030f090308072a03031509090f0303060623070309151101050a020304120c0c03050604120e040e03041502030405090f09060114010206 83
    0x140200721106e00507400c52140e50012a0b00038035121541c01051aa884110721440280749003085882c5c82d00c000380e0f901d82064644001244c0d060141060b04c5101d071404681c8070006240c049510018600c0400c00c0d04d0071001c0840110303040c40200884507900c00040700c880039000e00c06103140044d010103010385c00141d500240c02c1603160360001000c401c40c00004801402c00840c100b00b0b000050400d150103044002e4101d001a043c0359001414a01c034900c001038809000303034000d071200444020410300b548880d60860a10071921000200d0402a111403407407056561210075011005090190840710000d14070381c03071280305200340004140d0700c013010300b600200c1c0c0c18007040700912801c00400c064411761009045120308000c01041201d14003813070107041c20b2503c0e86c9020554042c200010756070007034000f000650040c001000343e8101c14030010b16090b000d0060764034090300c0e1801b2860343c1e082200d411107690070a07814044072000c1005003600414076000813040d00580ca000007034807030313401900007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 777153417 1250 777152167 777152177
    0x10f0c0308011e1a250b0f04020d061104082b230a02031206041808030711060109020711010c1104150801090f060c021f0203070309080c1b0a0302030d 66
    0x40385140e9000f082c580d010305002c94141d9460140d40009008a6000f4035403103020840d000400d040810240701c1606a032a40b152601350700343c2e92148003280c640f41c001c100b80d0b072100c024400d94000c103a55114040090341c0307a210160b9207a05004030a80b414034021340c0301001a521000701078410b807042d1130f1001d0300c000d14a0304a0b40f0300394942803007092001850141861001c0090b507403140607000401803c502298003004c0000340e880707604202c1101c4c1030194401291840c41d18941c0001c40030310065a11802c1c0d8140445c0654040d1003082c5065401d0b04114645a80010000c080c40070820300d00380741003c240fa101110014540e980c1d907051000d8001d081c003441d11400c5040b046880360347c0710030161100a008201c2c01c4c5003410004060207801d40700f80c0d00d01e0301d441c45481d100d46c4082000c2012180d81c3c5c08035004001040c030040005d5200405500803d0ba8490580000a0300b14000341202c22140b00140090b03031040700d812403144d001046075846007850050030401078a010600d03010455840c140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 777154667 1250 777153417 777153449
    0x12090a050907030c08150f0909192316170c100507110402031512151e090712060902041d0102070314070c03021c050109030e010f0c030801 61
    0x1084804805400c0640c0c00300320001000091a41680b2643c2c038284070355035854407030f1034103664503600002d100303285600982241119040c9090001c166504242900205c840c0103141d00d2400340e101c114548110342d04881014001c800511107841008543c0700075005d003283c080001e079402c6854201e40f09000015031213032107810300b140303050180b030190f41c5014010004950841e40f0090a5602c040d40440d04490315114015081c201031003524800e07070041000034408000c00003003002c44150148403090034841d40d0203540702124100704407030280f42c642d01107040081103501050b40b00ea400901030f10290344240c10800c050300c40c404180c82043d401003000181c80740c0764008580a03000c0c0000d03250184208541c1003107240d20540c018000d0900a41d1800c3e040140418018064441c541000e82000581f041c14805403500b19021800c91030b4205061200c55010340c1d681d070a440405005501007910710b150000c003940c0100c0c18040010031361030401070034036043c1e0b8054005070042c051103211901c0f10710 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 777155917 1250 777154667 777154669
    0xf0501060206061225030614010b04050114040918120804030801050904060b0409110315060f330409050f09060703180f0510140c0a0507210306140102030a021209 71
    0x141900c0c000680c81010744111101720004145014403040312007602c0c0c154402d11668501a030141626075210501e40b8080c07070100110340c200c0b41c00c86a40400da00c10480001c0007083e80c0309801003110a08440242d081142c01c01c68064075a140031202808420000c000000307601100090654030111400350041d111030030302c0070003031140080160704685490780800502a4441180700ca8050450860700074800507000518962030640e0400d03000b000c62114864985800c840700004900112941111102c0849442d8101c0505200c40203020f200060144049800b901031180d11910b458000300c032904100c80a40cad0b4810b0014120410147d0300c00321180e485022648043c00980c00c012880260381c010704009848014031481c00e09140d19008410400d0f5650713040c454030a0016818445c10302c07201110a9400b0b03400a1070440c3e0600544034040d5407540305026a10302c91416581c0011440e0a01c030505103200c0030012058190b510500030324101541c009500ca4941c0c080708070082d03c0d205954 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 777157167 1250 777155917 777155923
    0xb19020415210e06041e0c0b0301031b0308091e0d030503010905010812310311090c0c0304090b120106240c02010e010318020603070509040f05010602060612 69
    0x14100600e64180d0350180354081d81d01c101408480241e4000d41082044506452000c5890840825009030031140000b000700d20345511802030b0700002d0103030070030242556581025024403900190140e110110041c806e0103010200007444c4004100c0c8485c259007582c861540c5405408800c2e403040e2075406565818242c0088402c12001029001c2e01001da50745c603019080343c0090240b46d148515020002890010004001100d155810002c40c9002440c82e001c8000341d03860a000b14640c3c0c480382002c0c00c129100802d52000314014101a602d2012038410090740d020040e00080e01d480b428440546404008000c583c01c60700958000100b4090a01c04150500e00c40305c490300c5554a4448009400c800f08154000c012200e8000f4880c2402c03190020758585400501c041d0001d84000b030425042d50096110243c03504d02501c0500d0011801d5000a58a900071604c0400007000400e020a0500b4140207070b214410b1880c0c0103008960400000a54410004101342d00c14280d01c150446116414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 777158273 1106 777157167 777157169
    0x10b071e081b1c030e01053111181012080a0e03030702030715030b0402040815060118031112150a0e120408010b0406080a0b190204 58
    0x594200507000041c00300c40d5410320800c01c01c0701d880400e044070070743d2585a541d80400c0000c0800030190030340b040078007541555003a000c18a0111188205070388103400540c1404400b01000342041600c1c20410054241c110b1084a512144c0d18008882c807446100c2d20645c50854950b00c038141080302900e03002c0586540c07010300002050f284110000182540d0050407242230900c203400190034425560f10036101114000543c40b0369075014011250302010443d421030525261a0500e42c4030b590141030031105401580020345240c1c050300d1000314003849020a1801140c1b00e00c0d08152300440708803101c5c842c4030140149000e04c403000070240320306040118402d0a0380c80304402000501102c440f81d811501960701e107190b002880602400c0182004000071507180c040000f408201c030580c0e0050045a084070700f204011590915900b82c10802c1a01000309038400c0008503002130280d = true := by decide +kernel

theorem cover : BRFrame.Cov 776978417 777158273 := by
  have h0 := BRFrame.cov_init 776978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 776978417 ≤ n) (h2 : n < 777158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
