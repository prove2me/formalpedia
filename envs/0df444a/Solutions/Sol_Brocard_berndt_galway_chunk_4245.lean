-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4245
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:59:25.792735+00:00
-- url     : https://prove2.me/submissions/871df0b5-1960-4e78-97be-748a2f92be9e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 763309352 ≤ n < 763489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 763310602 1250 763309352 763309361
    0x240a0c05010b0d0c050405010b0a02100209010c06020f0d0609050c09040b033309030405011719051005150901050a1409031c020f01060303020d03021b010e010204050306071e050904 79
    0x403a40c402c40b80c3d4060740030407145181c00e83c2901c0041c3c400344000d0760f0342c0d411440207020351500300007d40c00c5042d07888a40c2c0480d9001d001c030420149020882280c55446120403684200301103440c00e40f0009812000c0c0c0b40a00442c070092000d0541003009141c41540400503000340301c0d110b4452912890780c00c8150350208658403120080d04801d03081041000303581e41c82c4c0d0001d80b83d41c0d02c4219010300060340c1224007109580071508180c4501821368603890404566000c010300c3c4c5090700c103200b210419010010300c80c1c10701c95a0740f030042c02c0405e41810100310000049000143c07e21100708001c88007640c0c001d007512103001c06410003000150003130540c15601c0c042e00d240160075115015420f10350002000012030310100580070f650861a80c1502203090741c015020142c0541e2141a0022405100340e00a0442414068045c4030b0110001109400d40c1da00d6608020185c0d000300d000d0041d86000e208140e0003248a04202d04210440d0aa083d82052403140c56801c1c0700c404a003030003654445402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 763311852 1250 763310602 763310621
    0x212121c110c0c10031a090403021903020c030f01021810140d0213080a02011e020c0303120103030f0c0f02040b0409050d020a0b0c0c1b010e03030d0b240a0c0501 71
    0x84280c9031545042c205540f620094001c40c4151810f60034112018000d1050030440300748003422600c0c1000c15810b0044403107001d40114210700c26031080800b91002903078410041c0c0e01c43d901420700000380c0000c15182c500c0c01c865030611a44104801d4445a6004668803485501510000316030f22081000f6070b214804800c414503801c10004600c00c4491037580240543c40406142145081d12004003036502c58450a0007801300e41901800d800c40c2820441d200114100d0384102ca400800640120b401c60700068484109241031100510400d500283c5240c10303007405142070320380302c010398442034010003c40202034001c95540d0807101ca42d80b503a03002004503d41060485420361841c0702c00030355902c80c100042e1900d07030404010584004042c0100e421700d030341d902d004000300b1045007c0c84541c0207440c0d00b80c0d4103000c241c1e605d44109450500140c035495841d510005290310715081442aa00076100024500d85240c0c60800b124489480644406080514103c0900a5503103070903801040c0d44070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 763313102 1250 763311852 763311881
    0x20409081e1e0c03030a1512060f0606020309060406230313021f020c09090f06090304080d0e010c1509050105161206050a0308130e0a090212121c 64
    0xa82000714220070400901c800d04000500e540c01e071036021108001c42c099140303034204070741042010810070030310740d0001a00e4030064074089190701c0e036540c951030020b01c11000844065480340c3c6046400406441540c0042c0303a1400038516020401d0000384880c4a64050841445010003a08445484004c0003c0341902d4800d01d103070342c03801c210707072451030651454038220321504a502c04c40c00d504140305103031a60811030b03400614449031024200042030344000c284090074819030740d007072030f41c88410000c05004840000c095aa160306000c9800d09200c801c01c150740a02905190785400c03640d100361100c01c42904a5010001074410301030380b00150410311009081c40d82480103004070591940501c1c1e10004445d2602c106000c6140c0004056442602c19035501000c49281000400e54140003080e070002ea10100103101a00c1d0481d00c030604100b600d00131085130b610030340c80046003812540c104410018000401c0422814445140d91303205088148078503031070050403841081c0c01da81214101c0495071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 763314352 1250 763313102 763313137
    0xf021009080706210b01080a09050a0503070b09060108030c06160c06060e0a0c090803040b071a01030308040218040c050f221406190317070f0b0610051602040908 71
    0xd580c020441c1c682c2c0d01c4403402d9002d929155620039229441007041000040c4c4841c40c481c0d8980c0e08c51001080c54030380c280c403d805218400400900184010a000740c440c3c8005503450410400b07042c50404160071034100341d0710030001c03d8407005000961551150740074001c550501020181210303c01000c9800900850400e40041000030b0030982c21440b90003517020420410b07007104000c4070910120b00c078010140e042000b09000717004000c0c004000e02070140c0b03080c030151070400403c0003920300b0036481a070000740f540003480110f20f0702d60742040c041801c4428180050802d911013555400040c81503610414003d5694080d0751151013540c10034203982c00620303503098261314091010384006402c0e503013010080400104103103016a0841584141c11588007041820350f9904401050428522380300f000050010781d002941b42c140000004c0c2c401d15502c07007541441018400c03004c3c880f0302c2c08800e00000b0b0280e503c080c03040c081d9000840f038040b100410f0381f4005003003290041c41551091340f000c0801c4d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 763315602 1250 763314352 763314359
    0x6050f0921060f0601022803032705480a0e09280308040206090a090c030e03091c06060830030c0a0c02120615011b0f0210090807 57
    0x4100340348104454000d560a581d00c4500490315138104001f0501d0303050070400d5441060f202c0c10b6004083e50b101e424001901140303030701064007000d1403042d10210140303808a02410840144a03280282d4a001d4205030405601d080c50102d409100b20140441600c489501c03a008040010408c00218060a401985030710343c110301001034030449828005100e01c0010840341052881d602656480120440f280755220303a40071240385030040e0059034030180500c00c3c0c0081d40e9400406400810100c900020174005209001d01034900c0c203868a000e03034100348000b040c1070b110900910030340004402200298540d5180c800c2c01004540c01001c0b441c41001008460614920000386c0024000400100e40e405640361b00340c1d0a00c801c0b0380c905184a0148620003d0f540600c1d447d940140c4000c1c030711844059000b61040c0b400780c048904005200c500c020440d281d58102c50110070307080280d1103180d1030001503164030a4101801000074000e01c04203040c247e5444c0b01c0d0012501404015050740d54403941c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 763316852 1250 763315602 763315669
    0x50415020a02041a0301060e010e0f090f100203040b0a05090d030902060714070f080706050414010c2111070f06050c0307050703030801030c090506100e0103020f04090e070e0106050f09 81
    0x103c60740014021b40c42c00e1004104561900b0406048803245240800f03180c0c0c0b2030582803100c050142000f0141e201c2c43d000e00e0142d910902150110403844680140c9910701401e0014403130001500f407403072851920050000f40c1c9000300e903210760310200742004941018940701181440c854220050584405405410f20314280402d02c0e01c101c0c0c2c4031070011010b01e502c6c3c414580d2200010300c18507011070020441044840180c4031042400740b814101b4045004460701c0700d5024886c0303082d1010502d0130b000519a040c5802c000c1500c02c005262005041e41da0078010b103030300803d01900a030000d11402041e01582d902081040300c014a40c03010075124260f5503441c001d01285820701044680c410307108008030312a8054400c40d84604001002102400904107054519003401111241015020401004410701c0d01000780300030103400000148119060300710271f0070019941c0001e20860031840c010020302d136204056490312030401600e01e0b5514070314000070f40034182d03400840c2e0310840008900d250261 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 763318102 1250 763316852 763316891
    0xa051306170319180801020a27180504081306020c0114030f04020f060c12070507090b0102120d02040510050702010207080f07030f230d030605040c050415020a0204 72
    0xd1a181c141400c011a8400564803405903000080f9200411692030100501c1101130703210181084d4141800c45407604411803d9920026400c408207404034000316644c01c5001d411440160410482d8460070704115008912400004101000c0d03502c5c6d0012030188410741c42102c503400b00400f2450401590703828040d49413542d441d84240403440d4003075200c024020100840744a0207108003861001d40d1140c1c2040f085208054810350401c909001c0c0020790241041001400b0a150328029254000791a129180229a80001c03030030504051060800340d80015503150003801c60840591680c0c1c005a05c40c0003802254421507100ba0b00401000d421a0018010103080f4000e0f404d48a0260322800940c0c0d0310000c04118000340c0c0e101d9202003011810000c5408105072269200004044144141100e8428401c00040e02a00012154031050b90140300715402841c1c02e031400c2c004001c0480c030203001800b8911551181e03040c000103000740a4401d0041180300c690043c0104a4580203040001811 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 763319352 1250 763318102 763318109
    0x3080a0c0801050a0b0c0c100c0506090d0801151103030c04031103060c0904090f0203120a020f0c150711030a08180409080a0c05120c1612020a140a051306 68
    0x1440c180d2100591449460400d050f500d01511654243d840c0c000382141641c400070204180d030145080e1b40882d50750b60800d04001b40c1a80c0c0e03503140c4400300d45c181541403500c050700f040b03c6075002148a180082d04020100d044030300c1010703854440c1c0011075099480106900744590b03240800410413020184040142c8152402640122035500c65141403681c0c0354000d8904ac4a4074905015844a40c6000d81001d113203984592000a240a01176000c6883c000030803440707810700c19010410101c42d40c6c3c10001034428001481c000c0426500001c0820b24159a5512400800d00000b400782c0c144400990344a406046c050300300e65400c1443c0c2010240e17030b00440c091480d035003000161021f00d032a060151104054000800c0c40c81e0205c10a030a49880b135200344119003601511071540136102d002d00c094040c041e00440030740b012510b07221a02c00050483c2c1c120819040b419215900541c0f1580704500580d0f400d0307d03905210888000008030b440000d588181d034020b182548060065460307030042d800301c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 763320602 1250 763319352 763319371
    0x90102120127020f040803070f030e1f140c10060303030b060901091707030b090102090a091a090a0f061205060702011107201507020a05011407110406050d0308 70
    0x6a40c882c00315900104401104424120410302c1e140c41030388240e8018031441544c600300740d180079034840000e0704540003001c0c1a00e04140c06100101450307005200c80038420421201c1114005064a0f041c2200c1ca40103e030108100c40c071003a0003681004042140ca01d10800b4088400420059841c1805040c1d04d000890020381002145540da06020095425015058540005681c1005816041145212a1103a640c851a64000042851512034601070042500090703641d007641010301200c05c10315480f803000c40746020362a50102044840346a454841101c1511240d1500e01c104005040d030302c500341013042e00d46400054207044c03260030b15006910a2040e28040c0e40c44075011b84c200d4420a4010351540342c01c03c0f07800300103031404817605c11201309442c1c44038443e044000400c0c009111512074a00b403030f00010b182c00551800340780d1000244003d107000000c40841c020143c00c5405454402401c200e26481c9551195070703590450f402420000c1c0146107080c001e402d000f8009e81060b14820300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 763321852 1250 763320602 763320637
    0xc050405070f112e0e150106030c2d030614090106050708040b040e0105041b021c0e06030408070c060e030706080712110c0d0228020102100203090102 66
    0x50908090069510400c400e44444065034541c103800d45618036140c0e8a401180038414035100f00c041d0424403d440b0b080d2081085070420310401000c3c0c104c078603805c01000715603c03100724001440039030609981510000d14012445a510310000c0e199021012203201c1030b10808107000b0015003446003203006000d40c43d50148112940c401509240f0a441540705420950710801030040e107000e2001000c0c10351154040ca458295110b104024581064004a2900182000411051609010b0070004c074005109849000480842c080d42e034840300c4e1040c1e420461030151400c00103028000c80c201841e0050800d659a18180c1351000c01907204200c1220800710000d008502c4910500e02140252400790041100d5410418180c604802c001c00407020400c03520b0708004443c0040c0500801d1a2807004540d8941c8034840f01141440315072150741c0119409199604861903103d00b14180f03081c900c1ca034001c101402400101d007400d0b503169210a6030f80c00001803043d149030560003042e4101c4110340005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 763323102 1250 763321852 763321859
    0x6020a20060a1103060f100c1704060914013504051c112d03130302030d0c0c05060a0c14070905100e2e0b0d11041a0706020f040905040c 60
    0x9180030a8405c50303006101510307029924203044120f01210700f0f46051031070b000c0100d41e83e040c40040700710300e400c2200c000202d410800190000b007030f132014040759881441407039540700000342703d04008030140d02443c1055448101021000c0e806514400d02d02400307841c07525050030b040d50b4400d191468074940c41c03416a0300c04a000d128540101c2d68424038000780001042032000d1194000480d01d01d441e9450588410a141c0e0034100010560085201c074541d900a195004250030a508036044030b0600241ca0703071400001c0d66501c03c0c04240c44045600e551100e6403200101c4d6001380081000709000395500c0440e0313448a00090075001c9405c2c5031020f2101e55610350113090440d000d4800c403c540c50001c804074001d44401078180c40103142c0c0010483c0e0000c82c40700501c814100561040030180000220002120014080c80700c02030941002140341038034100c47d02194480001ca800160b0380e010841604100054040f10b40e031441e40b01c089900d8036254a50305000700016039085401c52040311002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 763324352 1250 763323102 763323131
    0x6031b0503150601170403081f12080c010905031b012016050c090109020c0f0a02010e13060302060d020a02190c1a130803090a2106020a20060a 63
    0x880550300c02501820507a00c42e4403124000110207000b80e41030000c2c40181c0300180c0d60000c00315101da400717940c64a2803410718002e50040d030028000e0500d4004140c49042c40903070404200c80a040b41c3c000b149075030342d082107400c440c01031a12090080032404001105c05c0c04040c107600d0346801180040082118400c0c1c02210410f4442545000450aa0031f10021025030013410800034611b000d001501c000800110000b010641c0903000301000030707404206603101c1641084540503a204190040803100420b4001809140700140c0c0a4454074050a41084100302034100000a540c0171300030740e8486004030607201c040e40007915450014440d458103440039800002c0341500c20b40e0030140070085c2e141044403400b0b103001c29054205584c0810442071014411240b00c0d41c1c0146411409141c4500b01c810400402610a0380000301071040c110012000f541c0303406a0103100d81c1d01403401691916580c2044e070741d85080c0d10b10704100c002d103078802d079050080106042d8840c0d1405d04003040b071400382958a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 763325602 1250 763324352 763324403
    0x501032102150907171f0f021315030b041e09080409020f07031101050f060f03010b0910080c03030f03150406050d060b03240a0e0a05070f0608010501080103120e040608100603 77
    0x650031882d8441c1e4240e0507106c05940285601c84020341e0141c500041080f01c58000030955101c131130300e01c146100b0340307065984c513119030405160112824001c1c0794402c160f000200440d0009940e00980c0d6800e40020071042a080324018900d015095450300000c3d082140540c01c420700550200711040c50b1051281c0061144510074003041044031b200d03854420501040d9802c4100c0e10f500341d90307030782d48100c0749566082060748079091001509110600f8220110f080c0401e04564a00070750082c0320903000201d000050720760250541100814154590340010083d0025602ca29008414034021405100b82a0401c0e1030740300090b411102c4a01110048254088000c031151060012400110b44031403031070307001310550300004400c407500d0081070740310b0f207003001d0b403176400340050701e121000c1080455002035826004007424200782501c3e614544810045454240d200030800407140301d00035045e50b440d40300401030034401d002c0b2060f043d0360030005c1c0001c0146010941e070141094001c4130305100351214 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 763326852 1250 763325602 763325623
    0x8070b040609060813260706020c0c060a051c06031401200301060504121b1206060509070e09070c051e07081618060b030f15010201050103210215090717 67
    0x3100c1d68070001a25903811006c000780b009600e52810361031580010004e40054400d1038002c100060355803a2020350546024a07020341c0c7c0c4e010768014425a51159000f42c04c0d07075850680941e42d603500c5100d4001090040006400041807103118900c044401001540001819400704501340d8982c0c2103000f007944039000900c01d000000b00d0400062000c1096030014040451080b8488400000382803c0e0100c2110250026136400c0e0030007550109020481c090040102800d07a000851414000002404444108415405403a040e00404c01442c403e00c4207084540d04041a0340c5a60013840f0070410020000d0201c0103035228140010031f60290224510003004044803036411001d00e800c21060020695481100425a407440f0019015004100543c814090341031690b01a180c04900001e841800300580c034116803400e40148001468480449800e04100940c040071a0084204030f1034640c3c040b0080704030144420500c8070662001407100c2c20b4803039609082d020040800c0c07070715039110303035040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 763328102 1250 763326852 763326871
    0x2f0907030e0c10050c06181504020904080703050915090102010b090c03040318031a2d01050f120708060906130503040608060406050d05100509070e0604050901020408070b0406090608 80
    0x160402d85910300900310341c05060303c5003400d40c145203100c0e0702030b810028201d07021901c0790b15082490314071710003d100740c0c0a071031500c62102c10f907410a500482e0311404001c0008000000c0014076500341406641901c44442004100045240c0c203000002050380090204902640c24a181da41062822181711807043d220300200c281541e0f01e0f44c400700c6815a0420b403c601c000c207c900c000c80460027280b265160742072040020902801c2482c0c26601020344070b12a46400c0007038074080030100c41100d00e86070458004840b40107072188080006151a44255034182e10b510809000051501c4003194051107140c40c07800340c0d4020ba907404002c04092040120007403182e04100014888140200003480d00900041c0001418a4851001c074400400e4400c1c01e031019800071148520703c0e4280c2c05015404a00b400242400c0c901c0c101c400d942c8517a01031704540c841c036100c0d000290f000000350b0580d002041540e049400c1d00d952503202d840142e0081c0115000144058004292280160116401581440c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 763329352 1250 763328102 763328113
    0x632070f020a060c03051213140102040303140414010c1721011401080f0702030702040f0506031213030605061f0507110604050a0b07050a0b0a0f0b0d0201090509042f0907030e 77
    0x203099021001f400100308804a0b41000020004940781d10700000c18404010001680d4030b0840c1005414000c02030540d641c06a400c00003401440c40c1040c101544100a00300390035a100b16140c503504a081e00d040000b288500494000c984910004144486d1454800300c0445a40c03505003000c020360040c4145404103440401162200340f20020b0240d00c107105206590416501e640050150350b102030900c9040f81d1203106008140c6402d01c1850301301032100c4546441d000307c91844810585c064440a494103a81d84c1c002855501d6000c20302c00360500c2c0038036500c005024000040d0598118640664a2049105400c0c4140c1814403c44042e035034001c110426203450807413646130a51015604480c01d0080303211020000d01041c02d014001e00e42840702264028180740004212241c44503858407a107880354003000981d07000044035059501c05d80e0f03041855a1182800c0260f02442d0300c04094001c00700c025010b403601010522000320b10304417030350b208607140c44c5c40480036100301224a90454004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 763330602 1250 763329352 763329367
    0x5100e0903130f3006020d0207030806011128060e06010e1305030d020f07050a0c05033a11070909020a0e1b0a09090e0c0411040632070f020a060c0305 66
    0x13104425115000070209864100c503560902aa0022038070600c00e02e4002c40c0d45000c0640210170070364050020310304550010800900d03640d4449059400800d0200003c00081d101003500d42c00b40d00903038001c0310500c030007822a1145a6220740920880409200c0100800c1994400e209101181a0020000e50404c6515920040298050f5008003000201002404000345042c042e40b45014020080b58184915100c1454240313081144850b400b40c032006501c50000c0400c000030361437040074004119414800c1300b401d42d0f207010500100341d00344c8540c40000030621442d4020981c60340c400d44110141c10f6441540c0181a403080d01d070150708514429079160111380d80005042c549019103800303e010b90341c0e0f0b005003044071003600c50101542c01400c80d0840c40e0809016484144080100951426241890040c8811102c0f10142544c40e101015254000c001e002d070003805141c10441e50359a17101525003234600760504042207010f01c401d6a0000354040c09842825802c036010f0704c8161402c0340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 763331852 1250 763330602 763330649
    0xf0e19060b12030909060406031b170c130c0504231903031706130c030603050c0303041508070924031b091703071a041b030f020405100e0903130f 64
    0x5d0003001540c109a840340c001021030300b03100c2901c01034a00202c035502241e0904260b402495904032141ca129403140e41ca0140b60b449220b8031404000e00b10000248510500b81c1c02c6407548280c1c2d1083d14010202030440020307001000041034910811200c894042500210100003d03909100160120f2060031203400503d0480300c0c3e90741e000f00010506202d4414a8a406c42103d06401020001940d64013090041007400c00500e5565141280154201031501800704086a803018680c01001805404240010f01a5064a01514820380d608400080441298200394403888a0b940002d040100c107421055111820399800d01040d6900c02555040001155005051400780303941c0e4481044904003080302c040780019610069001c3e104682403d0400c104410081c49503a5105950414100001035651951030340c29030f03041d1404140769640180d00b038014101d6038810030941c8520390400002040110051040e800c6072035120482d01d88490045402038558010f0807803c5d490080c10464600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 763333102 1250 763331852 763331869
    0xa0b03070207030c0b04030201020105310602071e110d0b01050103110705010203070801180b09070c020f0904121103090604032d030909141303030f0e19060b120309 72
    0x8050740102d407951a541d0f600c00c400720205500041a8000120b424401c5607420301443d80c1180200900c03407401c01640c041691007109040c14000c01c0301e4400100b000b0010540c0584120381d030807030403102803480c003200c0c01d103105503203070070200c4a85c000340540028034a0240d46e02c4d03d14540001100b00700c1d03802c0030015402011400384803021410103216440000c0c0c0300340021841446c2c01c0d030300c40b1025403503c440c11940803a0750081d1710740320741842244940740c0c03901140c180e8410198075100708500c07028004507186400758404660803c6280c1c003000240024180300001040103a07503940c9181d010701c851300ba26030150703146807136000e5000c0008102003548074410190850b00b5034860721600640400000e0b907200030000031004610701c0b100030807407084184a50304485200039800101403130411030000e2628a0488003e0501d942ea0102034112043d80e402400090541b008480000b01324042c400d80d020726200e0202e41280c2420307140401418012041c1d50401525001035040c43d018004201402d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 763334352 1250 763333102 763333111
    0xa03030e03071b060806031902040c03021b07061206050d081e0a0e10031e0911030f01020c0f0a0b0c07030e062122021302041203091e03020a0b03 64
    0x107110a02400010410b01d408004002c800740c00855405882c003500544280801440c1c1c6204c0d411860904407081641c400e08818568101c0e00000c291650ba10280c0007405950054030080241400e200800400052203200b030f641c1c281c03107143e003a8071111000e50669045008454110704c0088208000480020207070500c6031000418800032804a4441c0055070072101e031100c00038155603422056418404000000d0203014a014450751605c000e103001c0798905400100122a07071200c140c410700ca421070222008030002400d507034001c10011403482c041c0d0009100d60f000c4c0c1c0118450400c80e07520020b003c911166024070090800c0e40d4186088803c2d0b041000c0c290305001d0162031140d0541c0c0c1d1200103010b52503c042400d02c01d4000300b013918014000c000c1484004a440010500f40c0f440820090160709a04440150141c1c94180d1752001a0280341d20034280c40745905800d0007010340000071001501c0025828403054030b40550108443c00c45480b0207500003a100d42e0920840f8041002107900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 763335602 1250 763334352 763334381
    0x90e1506060909040308160503040c0501080601030b03010f02120901180803091615080708090c1e090703060e0906070c02040207111807111218031e0d0e0108090a0303 73
    0x40940e042d0100f00c1401045504500240030300c0200502c03443c094400303002c80c00c80d502d492402c62406669100e2620514000e040c140310700700c070000c2c1ea1b9a10030f80242c1c0040320050000e215805803040b03214084c0d04200342041800840f0400501d198a0501c11107820035803a20801c3d0f40000151030300b0740b95030700c040c1c01480203000e101509600c2410320400b220080289410210007510b988a00070400c1c140a0850001c10401006100030b048002841a981000031562009207848155001c1c42895414001a8000c0c544508001e503268156110008540c0d0a0b0066210741c2d07543d001d5541c80c1c40c02100c0f25404280c90b41c1800c005410158003500710300c6d10071001d450300002c02b200084d4201740c044400002038a02c4500700480682c0c4010103085454001c0300901c4000e5030310b0b0704208140646102c80301c10130b8004a00c10100e03a41000042800d20301d155264a00125144406071904028203033b070000b00e05103a44a0310254410740d04940b14036081400381c13010800d155400c6016118401032101d6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 763336852 1250 763335602 763335607
    0xc110607030c0501050f071b2a080610080f0604080d02030a0908070f03030608010e03030a2034020105030604110f1314010e0a1e0b0c100501090e150606 67
    0x3c00920400b80200b10b0845030151900e09803c00400c17154029000c158010742d41429100000e0501100d402041c2c03961445408004d03060441d13507003424065008146a204030400d0003660200010954191154003003540c07038002010300461341e00c000650380145802420407010880b05456405140c11500045003c00c8400c020b03141c8040a800003d0700351010b540100e003800c101501440340100074a812002070005070660341c040c40c1c890000900e681201a16030526582841c1484c40f01a003803190307421001e840303402003512701706034000284600641003a50b04150a982d8005111181407590580d180c9243d40d13513041c01d05c0041d14880d1083c1004071014000d000c810032041d0081c047e910261080c070030781c0c5031520030114862003600d011103051085400210701103450b84c910180644029199a0080701d0a000703c4d800c000e441903100103421100807a850803070345000305210311540e448510910450342c90700008812611941c80c0c641c2a90b01c107800c8009084900c0c64116405030000b44003d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 763338102 1250 763336852 763336877
    0xf0c0a0818030910020105060909071a030a0b1c1209050a091d0607031a120606010c141515040b280b0705030405030601080118020f030a21020c010c11060703 69
    0x82400c0120344c03604000d0f035100c80400415080c145922540034070034400511b40e8074505191106010448a0038100b40f1400200160390116941c000385c180780c00141a201a031000301c0984e1004140c105011505807400780314126559115108002c1901c05c000c0c401d1812502d041c03101d40040280c50404415101c0ca400ca0000a100c1481060303c9004141c4001c6000f0003880d80022071000d40d084518410341080f0070540201d41c0010783d00394003840a0070700c03c500b000d0300d0804084003008982080e8451058140c00240583c02c02000c500403041403407070615a449010402054980a148064000d040b81c10540900301003284d4480861700c0246140e40883d1704c03103822105517070251800f0340e02540002010001400e003009080d00514441c0003c000030700411489514008506101034072506c41030558410507a404d00201c20440e60080e03582c0740d03000c400c50380e8407001042049030358054010644c00e2806035000707800d0074200395802015904001c5c1800304011803a0001c0300c05804018510b010030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 763339352 1250 763338102 763338109
    0xc050a0b01081006050901080d05031008030a020109060c0c0b070f090b07120207060c0f0b04020105160b04030e1c08250605011a07081b030f070b0f0c0a08180309 71
    0x590103020000041d01c3c040e08050740c04000c3c0c3d032071580001c1c003802c0c1c072400400001d0b401017682d0342c80c2e6074280341c01542d03912404400154400d10b5003050361a0300000444010760b039015441411260310514041c0814010b251094858440010010304085c84c0d0200207200d02c0c0c0328403060a101519800c1c14807006442c1e031034180c1d075a00590400c642284d1030180b41810103030108200e00044c54145821210003072030384c1c2c0306005201020b000400e40c424410100e0116802142903521200c48101c091491071903e0401102e00c01e0191015004241c1c0440781035018100f0403103907000501040603100d01c0d1100f03940c403e8070716400b8110300c0c0720449940001590704103800020600302401207102051650401182c01035800720000010740030041007007a0300c0007800c0101512400c0f008440201d100c400110945819031180704680c0070314a400150500400c10001d0040780070300c41382803c0c121700c0d03920103400a02502c1443c8070640403e10080005402c0411000c140d10410756640c207890070b000600f03010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 763340602 1250 763339352 763339373
    0x20f031c020309030f0c0121140a0902040b01031a1c05030a050a0e04051603020307022e0623120c03011b0f2115031506050924010c050a 60
    0x103400050b080043e096120b49400c0000d1380111040f030703000c3c207035010b0400000ba1881d02c4600031314031031101803a03981c8042200ca5005511410707000303503904941d00d800f0014500074824004201d101340c0c03612003000d142c1e510a12035810341c00494207a4041c18001c2c5010003920f043c10b980c40454000c01130209200144003031014019a9030305488854682048000c00f400c0341a001003c240198030705400c100e5840f6241760698070700b112506005a69441c1c11030304a050a01170340140d1a0f1500404054250401c008461054503001000402c6260b0701c0f000c410800c03680f8034070418500c0070081c100f10514a05010121211128281200d000103051030200707003075800a5422408034140c1004840009400c60190b104002c014a0035114145081120500140052986011055890f4100e000342c41c4030038070807405184c0020800c941103002401c2c003070141c402070081c14000c2c400080031403400384440040c0c07027002d1103060b4000c40102800004603120421543c0603510380c8581035048001c01d8440f00b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 763341852 1250 763340602 763340653
    0xf0c1005041e03020a081c0606020304090b0402030613020c1905060105010311070201080a05180f0607020d08010b040501030515060c0105012d1203030e0f0d1403040f020f03 76
    0x494949420b04040051034408110504240b001c80d1641c00000e6020903c10201944444196210b8441c0766001000420300e0014403a900d1400001042d40e82e0000064012a01245e0307050040d0701c451001d120a90005841d2640c21003012a0100ca400b2203540142c45110000b40c203d9407904840c2c0b000d00d402d00f1801c9400d481c80e4220384014441c559050044c803210145581c01d4901c0e005507940000e000d6400107181b051680c1d5100d01090114540704040d500d40c5a048045444d20760030b40010381d0302c4560544482c005031140900c4251190b014030001812200344180c41c0741410b1800c0010360181100804040c01c0400003440b040f115922100039203078102030400001a03640c140382850b4011100c80c280756080700b0b40c980300c1501500f00c0c11070400c107449911003001c00c000800d1034150b0181031401010851401404980040c0b00e400081c60801d118166554010b03146481008540c14401900c1c0908180c110340300480141c203101156410180d17000c6c0803118400f0305085885058a400d60 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 763343102 1250 763341852 763341883
    0x40c030e06150306060103091a1f06050c06061906030c05120f04050c01030216241d060106030912030903110601080a0204140907120501020712050a1814060f0c 70
    0x14070034101400c01304016139101d0021700742040740b401103403a1400000504803a1000910003c40000c1e040e0151061080c42038002200091081d51100c60143c40d036004854400880d101c0c220000300180b0f0f000840401a5201046543c202c0d420210101c0140c81140500414170400b0060850340c2c0c2141e0500c1d07442a91000001210b90400e45031103030030424039070145070400d0300500803442016000c10300f07140400e610103c000420502e8007200358000f04824904881c880c41c180d64038503c031030344110200019900c8001e582041c4c2e242c81041d401c550524a003d010010b824070fa2204148c000e502420615000e42051401c4c42000380050385403403001d81051070190045000700d0118103260081d040740d0946061005601d141668a95559003c0d6100d21205c0c4401c120014041c44002e504441d0341f2a00501032b105000300040300680365501c80c49206000401104805009013900002c2d0307810381c2c04160488041c20f880208200254000540c110a044001c000d0245079410400c2841aa1205803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 763344352 1250 763343102 763343131
    0x18020f0301060e01120b010813021c0303140f01080703230d02100606090e0c031e070e0108060111100b28050906062d09100c05120c030702040c030e06 66
    0x59000400f0540030017000c01017075081c500c803c09148e8208100c00c2d4410b16518520791000d4050000610726011070a41031080300c00600340b0030038180d154120365002c48601201d610f540e1907100308521095000d04c12203486400c01441400001c0401181003208414428554075071205010002d052080c0d491004025910a800c644000c505a000d038000030492424100d007001e2070101c03034110240008050079038600c0b0000001301184429181d00a00302241410382105207803800000c0c017a1148942c01501080ca8400000c68941c85002c07002500e07030707605001c0c3c030304000002c07800e4026041403c1180c0d4400400b82c040070281c3d5803a05002494040f4401c0c000d412440c1c641448280d0101415070350040030104400120301450384100b484442e01e05001c8041c441180070144854002d000c00554040d85a80c070380d03400c11340d0141d000d41c40c403400740c0c2c00d840d025600c180c40810184210081c4854a8205000c0c03100940381a0340014203803a070a0401282c1c00000410390350034402c01702c5100040684c1d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 763345602 1250 763344352 763344377
    0xc0607030b03010c05040b0a1407050a0b0a020316080c0412030207090e0109050304062105011401020c01050a020d18081203090c0f09131506122006030118020f030106 73
    0x500a03441e40340307801e0b0004c210714040c514008085103c1e40c0122003000100080c02c41404d4454a003079000814080d0010307468100d61310300541c079121400e0080c0c580384600e50208510b90900d10032039001d06c428800101c048c4142400594110600038802c40d000f01081c0000982c82500c03040c19a0100d200354041c004860811004030200e908820030380546070702d0481c0c4040052400000c503010303607000b07007031500609080c41010200664041c103c080f9850901000280000b50340d1000884040260251036100070640c0c01140c0501070300d510b60300140d0088058030304007805010100c1350803262740c0c0600002e0341c84503100fa2520b1312042003010007240000401840348014040104119000c903410400d420445001818030213002d040700d40b0a00c15084e055042042508a00c042448440402d1120a03a202c0c9090010460a0340585031801281e000314005050b14a050303200c141d00070599425030b401d0080c1d40181c19a04130800c07201e90f900b0000c4d102010203074000746009001c1d41ea15030400c40e41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 763346852 1250 763345602 763345607
    0xf020a0305090d02150c1e04060e221a2106010608010803120a1506091a09060706020702030304030c0b09040e030a020a021302090402030a2a080411150c0607 69
    0x30082c98411950001914070707603000d5012400c513000b0848481040b4403529040130480080c0b2421141d41c29590210107000004003404024000716050f80d200c0604044000040c4003004d06089005504030014584041942080d98020940c020091082000300584000803450503030505401786c1c00c00c41035a14810b880b00c0100000c5015145074541100039515020714950741c0d0145c00340c4070749036010850000d20660300d03d03031121840104211060712041d90381c0c2c001a004180b58055400c1c1e800d0400c88086140405000300c07000344102410083c6007600548030f6000070740000d003080381d150004010000100d5440d00303160b0041c00380103403020f0380c13400c0600402084070705030214408603800c107202e162041070f0081f600c41e06c020380599114400541d0651444024454a008581e0042c0b02100348850030f0a02d600c00150301003280044240d151700e80b10407003c940810813610001440010015001689602c5d00c003201550142c0f0129056160b00c41d1080d403900440140340311030340b03e041049081035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 763348102 1250 763346852 763346861
    0x405041a071404050418151506090b1c061d0601030b01030506010e0f04061805090d02030c060c0d110c060916151d09040f140d080103060c020c040f020a03 68
    0x210030703042070500324203103010508041c0107070300c04c2c0c9100d503607181d1340c4ca540e5524000c510401650300c0501006000c261b504040011f000040045034807000519001c42c40d64041d0700e1304402d6442030801c03503003810088084440210401008415031036201d0b9000100300800c00c0c01130851001c074170100c0d011407030700d00300040c02c580c0d0024880781054284024050182d8004103169012542514000503a421040c0420081c1015901914140000b09268030710301c2e0007980300030700035801d060682e0f04102c0c42d00e03c1261f0300d0080142c851007980024002c03e2411901c1001040040208840881c10820403074106080790848940c00030f05070010070420081060070301808803228200c5034000d454600340070104c0c3d0302080003080c0200348805010030042e49481c607a01010300000003400720000c0e242514141036020b2403c4407c44100703030101c0940701d004c0f04c0458845070125107586c40c620113a1031074a944000c0e041e0b0550341c4096014041d403020450b1641d000b10705c8880500c03a80503039a000035020040864 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 763349352 1250 763348102 763348111
    0xf0a1106060d1110113a090b0a03090c120b160e041802150703080c030105130f0b0a1e0b090d030e031c03060e0115090302120102090405041a 62
    0x1907031484000000511640c6050114403c10b40c0d02c1e020031030002c14203440668280904c1c4400b4840c040c5025032050070a05d81c4c005015500c004220b103405840c40740070350007003082041000b280400006201c4020090f0107410b1421071031801060f80c48294680d000c013000b183c1c20080455640b42e640505000c4640005900071800d412180030725259004020481ca0000080c20f1089440761100d040044080440031344282e0020440c000c15200c500e043c9139150304c1090100e01041842000a410f0406c10b1300f6217040360b401804a0500d0611172a0420041402200c0c90740300300c4c0d80c0c2d425960192103489804000e040540608a43c0d0240a00c2c000d80310704484d4401c6800000410401c3d01c40c3c4c0700c1140b45a81c25a2509101c04031142507c002030401e8083d45ca214441d1456000c0450007030340c50342000048440018070980030303980381c0402c104c504090b000070314041341e581c0108000504112440ca400d030444580018100522000000c0580d0002d9409035000141c04080700d80c0030500d0f64040d80c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 763350602 1250 763349352 763349359
    0x40f15020d060f0519210b0901020409112b02040b0a0f11011a0603060402040b0a120515030607121820090402010804060b0f1f091512110f0a110606 65
    0x10400c0480c90001110070300814070740f031814422030600b03110340708006d800f1a1307070000001803d0300e0400700240c001c1d00b0070300c6002c200c82c1c2040c00b001110b1440804444039000c40f05201e802d001c601c506494050341204104510141c0c0c20000002c44a4070380d8042c007113800d110b5456200e0b001d2070080c001d2001c0d4021a401481d0b0b454003807a0348140412904280c200030080d140d03140c50f60b07100c800180c02070041c1e0b84201414000010001c21584c0c1c02080b400195607807040c00c000d19103604c8884020110000900c0360035520410100c0c505600a60b402107030b01101400120700906207500c0d11084240700c50f41210b02080b5210454940070341e80040381b24103c010340d0001c011703151a400081c0381c0c5101030005049070341e690041c002e0503259004581a42a00544003900c030006050004c03141b540468800c40010307201c1c610102e026048001d51220104c05683d40150b00e00440240300d0080040c14000341c0c005404000708030003624070501a00a0400c030340c485146820600091a06000004145078030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 763351852 1250 763350602 763350619
    0x130f11010f0201150905060630012903090a020a0b13081b060a020c030304120b070306080c060a032a022b0302030c09040905030a14070803040f15020d060f05 69
    0x140e01d011441001110091174000c02c05446000200e43c40340318281089c81c0d00c203004102c02001000c8421114010350000d543c5240b142e80e03401c0e081c209070001c2042e03810502540144040341002d2a8060341e003081c103207410f84010324003c0d400107800c1d40e603c1c0c1c800031a009000c204000b001c508118864024080480a4520340740341c0c6074500c0c581d500b03c0c50881e1140001003a00948107208100c080080180502280e84d030729140c0360201d0000300c0d5120100ca15800c9a40082d007118407a00800c0d0440e00600000c1c01d1000c50030080100e141c01c801280000c0503542d40e244201c000c480000c1103001100c003180031041401c0d85400034100b90b00343c95202c5004217a040050040f0400c0c201804247ca4a4600142c40782c481110509131445a09191944942407171000d0302441400720007001c0010844c2c80b124a0032820000d45060303030090203805817210806000040209203c440610a042e214401c1184005030031001c160072030300120b0142403100d43d544005e21103442244054000707000c2c00c903800074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 763353102 1250 763351852 763351871
    0x302210a0c0302041a03041403030a021b0f0c060f160602070204060816030f1103010c0207050a050406230d020d060e12032419061701061b0b130f11010f0201 69
    0xc894100c2d40d034210b4034100000002a003800306003048a0707234285234281030f2951390519285180117900220300044220a640040301010070000230150345007000c0c08007521340d2141d044100000782d0403000040060a004001680258840720180d0103031328881c00c001070312800d60303006100c02c0750425000010f03140c1c0704a1810401466480240c01140c1e8005491030403c43c0501c1d1489210f400c818034660550b080c54230100c0c6058003c00e030700c400c0c0d0b00d044e1002281240da0340100030a40f110741c41540c90004c0d1080c1170040d0f01c5216401c08441440142502c80840348681c003188801c6140c4109480a40d0740360b800201c0d0000c140906420344c818082c2031811410008007922a8079105543d1020002e842d40c40043e1648585880d039582020b00344840c280300742e41c1d0380090841500c8454990344409040c1c0085140c600031010701110440c80b01415403408419030b00d81e2540200a011710030004441025076002501a9400c98290b0b440b4960940800c07158000162100e5883d80c00c10342964140004003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 763354352 1250 763353102 763353119
    0x5101512050c070b04140102130e070f030b06040515040308040e010e090102030127060e10030b0606031006080424020705060a0b1c0201110703050d080c0c070b0304030302210a0c030204 81
    0x468100b900503034803a0061b81a104010700900c20f10181e41ea80c091403400000b000103482404601c40c00d4035450b040300c0e0002d6208100c1c00c8607020401c041e84603200380018442d6092250310132803441c400400c928a410b850361140d0300346401c1944400704800d6514014440f00021240d5a604840f444000b2343c01d5505050503103101919135036000c002164040e83c10f00700d10f0310a0b0400001000b90021120050170f0a40100555031403a0201762840450800403d0480c20841c085038450001c00601c100117505011080380c10603400b60094400d41c541c20b12142024074440010b02004452000042c1d450401e8500241070081c010202001107103480c1c3e00900c00d498120004c40d501208000503003000045200507a40b80c680c0da5060030042c81048004820481d0001e10309010b4442a00d80700b81541d1a6401c6090b14801d800b2a0221354000f803000b0440501080091904144603050150a15440c440310403980c014256000e44160540701c2805500704a07480380310780c1103a4a00d030541c9441e0400441 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 763355602 1250 763354352 763354373
    0x6020706050901052203120f11060610020f06152b110102030c0303040521070c03030516020d05102702270411010e060c1005101512050c07 61
    0x5a070500c00001010220032400350110390344901c244c0d00500a160b16400c01456003890940c0081c0030858801c9030748c55481c0203003214161400c401c001804a13503100000e06c12540c94400d2180207601c01d00360311800c2680709009161141e01c850620303104140b40d440401114044900604800c9005480741041c00c03030810380b000301c01603000710304650a03222200c0100c3c614414451840614000802800f04000707001c20032400341381580440186025504407406140e1103000c41c002c00e8103408100800029018802030404201d2300030903d0384030810b68011517080c0e030150130203c650b50014180f5523000c0e103003445402060010b441903980982d040c451085031003200024043e110344030f489000051003852803008100041182d5802071181814503000c000d001c108001c607404943d203190040c045040080c1511041a00c82c40100600003589504a000707090140118405202c918000304568401070b0030340c4c48001441d540c2d4260b41c1e0200b5a41d2040340d03c06014007a001c201000402c0100c0d02c582038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 763356852 1250 763355602 763355617
    0xd02061806152b050d0207230301110a020a2d030507081b10050606030c1206031e030a0806040c0203040608070e09010303030902100e09010b0903010f0e0102070c0602070605 76
    0x5540280310a0040043e1040040402c101e5100c0c2d000509419206182801c0c03e036000c1c452411220070320129482a601c0d0162401410808004400803d4586100e071b0750307a00c00c0c03e1015000003401e0384803180d01442580110304881c056400403205030204140403011448920300301c0016a5000c68007a50444440f0000c1d0300a01045000308240051102d64011507060410710b0891012081c0058070b09034a032498400c02c290b100c2c0c60600041d0b40e9040102c01c0320b207c1c005079076401d0700e400c0b00440e00c14900100a00074a4044c4158070303016004062950744922100f840c1001592a608500401022904001d11403070046042420044000e0380001c15201560b1036400d1518a030303600c00104442c10249008201d50140003040000306040d00350340840e103007074001d860203001403040c560b080d200b03002c0440281da0011b42c00b20041000d49240f40180c14007031402400881c0526150108800307a07580025041c0c0280d6000130248100018801c4102c020803250010300745c054600b11020303225000303072300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 763358102 1250 763356852 763356871
    0x5010210090c09020a0e120303061318150b0a050616080903030f16030e0409020f040f0b180105030705120304051c020301020a030b04050a0608030d020d0605120d02061806 75
    0x10a040800a01d0a1002c000e0301c3d115608546580900c0b000070902c070700409078240100b4a21346c0c035006601021080340d216842c050600915540344c80380d200024010304a01c00d142c281116440b0000850300390050720002044000450612081401c1040c1041d8903130140d07204e0a000c204c0b084502440d00d1119540300e8014010303a4603030744902c0209045100794988250800300c009040410040d0f5000d80c7d80b8802d0083e034401c1401d17074500342800304079100304101a60068404444425519040d08510200d5403103403800f142c031001080101c5d600c3d444516050090345002c2005000c5402c0800c1380d4001007034221254402c40041d0020a03450340300361b000703007401130300c00079449e030720100c3d00001c0c0d801e5441c1e0140c001c654541301f001c8010014445104810b00c0f840c09e05000c2203001ca414091013003079074040d0019500d0a004d000403807009601c580401d40314152a541c0000e600c0e5529000c01078401c85d100040c0c0103403100c194009080520051200701c0300785240c00103844100000411541c002882c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 763359352 1250 763358102 763358111
    0x10150c0c12230a2a322e090f091b0e01080114030a0f1a100b0d1d0f1c051e090d05011a0316030308280603240605010210 53
    0x1207801410003800d4105442e0512019081005d102d034224103958401c202032110410040c602040100f2100d40d20169640d0780e000300700b40500002c0500040070096158108003c900c1d40d518011440282c241d4800d6851650300c1040e0b48600c9200d012480386c0b0003845c900020000d00c0e0400182194006000b2402d0440003210420401d85040000e0b5007200d800024441440c00b0303070714020040b0a04402040e00d186226400b2900c40321084500000ba0f9406903291400d0000b00103680009080024180440440040a660f0b1034403041c030012841420540c0039003107401492084000e91440303050300e101013280800001c210329540103d24801c0a038054561640d81408000085000c00d410b0005050741d4030341510390400c0d000580b01d012041c0e5058048e15500c0d02212507100c0c0d010044e01c0080d01189000000888121100100480c0040740c0810310302c4a0402c0804442100c099070412074183d81c00003407100e8802001d1001c51410034103000306000081c103020000751100b8080c400f400d4005e031103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 763360602 1250 763359352 763359413
    0xe01020a080c030405070308030a0501080d0f09180b041104050a0e040f03030b0612010e0711031c0905030c0a11010e04021606050601030204080f0307020910150c0c12230a 75
    0x1801304200458011100e49d449051881001004000a204000461041c0d003a040c424600030241c0300000011741e103442030010710304040e100c01c400120110b03220321951580b55040a0303030707244240044900100081501c8500f0314003803182c5045a0780100300b010300607500304400501c5400d001d21281d90315240110703194001c030010405601440341c1c0d590310348825030004903902c01c140103694413808031582c507009841e000e01e484548a100782c1d04e4802c241c5850081055803500301380c100300f035041d1040084900d8001944070b0b50741040d4220b0b030100d5000142e40c00b40612983c1c0000c0251030000b04440c21441c00412a12007000400c0300907001b4412501c8200040c2140c1c0a581500c1c0207005580036258000050300406450307600404040f0301c607000d00000b00703940035a508140d50039105440e50040300341140d030000ba6140080924200c4248060b810040744c50044041000407113171013102c1440907031100c4006810049071900d040f0306150301004528010403031482000040f4031618401045418a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 763361852 1250 763360602 763360613
    0x150e0d0521090d0b070e191214030f09040524010341130f0f02040207120c0c0b0f0d050c0f280309020603011502070807180e01020a080c0304 62
    0xb40112840d440b0000003080d8040c004071204070713403040b1000c0c0e4600d42e140380480104a81d0381c05948041c03243c0209414180022581c811414401c240168001c5807010300800c4001c0c6507502048102100c90382c085a80200c40c00c00707004091304001081e58251003a40c55034811a1116400380010f810581c8410442d42845044816154030b02e84000000e05180540c8444550300481202843c09603c0e2a40000360101c1c088410314109036407104580b000c3d0f981d1030b1140280d003020600300340d80c0035600300251000101248640c4045010300e403110301c500f0ba1141881c212213125030340112200f84007040260508041074040342c620600016000a0b42d485811525220340110b98500d0042e260020705941e41000240d5850804914031800241150310144114160760040100030341110341840140700c1290132200024026109104a5100b271b179980365207602e0700d030465001b28221a40d845411005500d540900d01d401300082000794a0090700c00002054032074001e040c0745824a012000c1006c202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 763363102 1250 763361852 763361857
    0x150709032a05130915020301120f05031903060806070c0c0510090308041e090e0303010b0d0b0d0c051e0607030f0507050718050f040218070c020604150e0d0521 70
    0x40007414080002902041000003400744420594146240701041051011700c2d00849068802d99025800400915610758a0780003100104440600007401070b45100809134140045c401019540460300629010100b0304004000d8420010440e20054501c04180792401240845205594044a004100000b1128100d507501700800c4004001340000e415042903417207040e94243c3c41e0360681c40e940e0f82c0012800719000c2040b1000c658000b4001003207007804503030107040045681480401e443c1f03442c20024408986107102201c02c2458280b045c403007030030010b01481003001e1202484041c04100b80c0041c0726402009002020414841300c03041000f8030940903140f00c41e501074100c03822961500c0c43d04d581c3c084200b0001d49520f14181c0007036101000603c1c00e502658014004144005040c2c0e4561313441c1c9002840d04050182d00501880140c5590f4010702c004d100d0346404120700801380d04c0007498841c0c2111100d2003020003407500d00128101080e8400840d00e00050b4080d040c1c50000c0307004007030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 763364352 1250 763363102 763363109
    0x1050610140d020c100c02030406090e0c1b0a0311030705190303020f03010905040515270c10020606030607020606032e020d090605010504052a041205150709032a 71
    0x7400403421301034601e000682c81010844100d000c0c800c3d10f43c4104102e030fa0f4065841031400049519a04000741c0301c5141002d6001150616810b06c1c00d8200304401d0220000102c480b4000c1c0d0128070a101031560040b0103c2d0404d50440c091440c0c1310664480e20f0341c0304075407182800f820b014550032104150081d130440c1c04281d04034150603140d685d100303071100050504980690711401041d01444209070740c480b407240700785406044800b00d0743c04484119001c48002a040c59a40706803840c00c1119603d2011058111001b903000f44850f1a000342032600700344000d485a4255445001401010f903400300740c00f050014139a4030203108014110f01c0d03141c4920070f1120040c20754400a69a0800340c11600000c00035405680c00307001591b0703140c080c04111981121412204e0100c6281a070280704803006005401003400b04842c10581c441c0d582021010700b1001c1111140d01c05101c1043c003c015580182d03101d80f950902c03114081ca162100c411902d0451034a55200d61007942c180b500c0c0d00f609000d81e015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 763365602 1250 763364352 763364377
    0x1e1902162327101a0d0b0a082505040c08011e0306050f0402010206070e03210c012a0207061d0d1211071e0509040c030605090105010303110105061014 66
    0x101021030a44500320390083c3e901c0002000640b10100b54050103142c8481d03642ca1103010b240c80c4c65503045014004100b500026603014140c0c1500091880b41082400d002038a0381d03841c249260081460390f03914611550207580030300e0030807540040194100d0002c90440c1c220000303030140154182d1884101c00f160303400040c036107490602407060740401041d003184654801c0e000c807407281d00d501405603100340441d001e85a060f407058100c040011a090b100045a500e07407100c2d41c0c00c008200c10f0721420b40b8801d00d599841041c540046138250484007402589082e40d900181c4a50b6040100081481d40a403818140120f02c60b4001d188130740f2440103008800d80c21445c506600040500b0041c03c00070304182403409131054242c04149886100020484002200c101c0103d030380c6044180001c48034024020340300011003010000105106003d0540314030300075800018158114500988003802c02854089180c0c506000c00c4000d0300c0b0f4281c0c0e1580c18603107007818401e01ea015209040e59103e0142c20703065 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 763366852 1250 763365602 763365649
    0x20129040c09180f0b0915010e010207080709091b080a0308100b030702060613150306050901141e160503151201020a091a030402090c1e19021623 64
    0x5100d401c1d036100c00711100c9810405d1181d1144c4a00b01b00d0860002d64035103600000c14104106298007458241c4d49500040c0156602c3d150703114503150500080d13a2012004a40341c0408d40b0070817210070f4000d440c02201c0c0040301030340c0e07040444695945201100040038051a10301082450080c0041c00c0700418102c1001c9503240f03401f40300251207a00950f02ca40c010240961b4a01c1e6100d058000c207016100030140c84140d65203580c486001901c4044d2001c2c980307551750000e894211055101141c8100100719021203001c691004270618000e0051100306048a0035a40c1c4003002c0e0720504498000ba107205154507640c580d10009801c104101450b20310030f6200041e0b084040e07400c00002d0b002c8400180c0303040d80100c00c01d0382030840c40c4001c480013036008a1000001c1c0078400303400c0140c07032072040002c41f544151200e03040380b8207103a10048100741d130800d2004070488a1035042040902c898500d024544800e45001070800c0151104200c458103141c06111108650300e50030300014442102c500c6201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 763368102 1250 763366852 763366889
    0x15111c020a061d0a02061602030a03021e0705091303020c09150f0301050c03060607110a030c03110118171009260702030a030305071707080106020129040c09 69
    0x1d684818001c03040307440d64144055554030700c51201024100d91248009403418031141d9003006101c2d4403072960802c60268024407030015840c1040074590321031094004140140e00361000c1c444007440d480d4041042e500084041c0100d44031443e900e81c00c003600d40040c0d02c51100501e0203901f080c05500606811014090800554905088520903072100a0b19200c240030351480526080e070300f045502da9802e41c0100003107241414840020409680030703000c030241d2003910f81c00060750756615a20a83d41500c1180c014010300003008402c01f425002401c114032071242540110140c04e4136403140c040d003094070320f076002c420a000b0b01035003001c9150001d0030412030015240c69510608a007500300340343c0c10100482512a20301d042100d456580080090601c44025031381100034000c001c00550800c160900041c81c000b2041c016107006041239200d018256041c81002030845142c011070401d40c04404007030f1040e07420380d12040ba070714090544010078105021141a03802002e15800411010244a00f54 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 763369352 1250 763368102 763368107
    0x9170102120a1e020f181306060302190c0b01091a0603010b0c0d02150604020a050408010c1710120602090406122108040203032a010228080115111c 65
    0x29000201c0418201c0f00c205600f08400100d0048400360428070f82e0030425943d822201c01441000e0410080400e640b02c400781c500da90036182c8984c0a80c001c1380d00030806168403008407030111a0600360703180071904080e43e40c4415124507010710441d454681e0315a01171000007038500501c3c50808024182682c2d030759540100e03114170b80c0030400103640e40c00703a850a203411910101e0201c07032841c1002c40c0b001c040d440d454200b000070341c03000e2012070600004100006022400380103981034a1003036100c0c02d491030510204400704440c02402244040c5006209101d6521180070030160380b600040d0068903454040b0104005110503084131800e01e004820341010001190f2800200c10f00d4604580540c0c21788a006968664056600a6160304244810606540d05d04c03000d04c605910031000c0300d480b8a02d901d0150032a0b100c4002e00d2814400e40d440d55512820a0040e44940c10030784c03034040d20380e41c034000d60b07002c90480440e800d40400001940c0c664410008100c81c401c1c040140e02006052403810002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 763370602 1250 763369352 763369361
    0x150608060301060e06100e010207031515090c0203070b091908031902030103020d1b03150f05220210140a09061b26070507080105060312090109170102120a 68
    0x451082d800c014001c01d22501e5030031898007820010b030080140e00108074080d50100708026075641107126520000020940c001c045940000d0f42d030000103803161160740d14415044098219031001424403c480700788980c00012144410340005100e4074a46071042c005061203409116038103003030034400e0b00b1000e01407088025405204a0030724000000b21008204040c1e010903c0081c1d4401c0c100740c1124040781d20600b600041507007015050041d9a00c176501da5414884074031030416099610003043c0d00b601017a2080c0c680280308000074043c45000346030540c204c1108084000d00800c0141c05000285000300d070944100300c0c540c0b26440d19464900c200030032569062140500142240c0c0303940c503000032000240008940c0003580403030102c000341020b0040a0f8070624003255210304101000116405108600c042c0041c6070010130182050b008141c509030040700c0800614908000604043e0f0f000800f0070111400c0d100c001882c0c91800f00c20714028020950040e04188004041140e241140c2e0711 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 763371852 1250 763370602 763370611
    0x1b02010507021e03270306100503010b01410d0f0c05160803060102071e050438040b03010513260d0506031e0607090b09030c0d020103150608 62
    0x2101c0e02804030080300d08181540f00c0d0304a00c0c3d504104a0300e60b8201401c5803042058a5a84560908004010202c4d2a110b021178015400c81420001800540f50a00034880b024000b481d02603200210240d02901c2e500c2c1c06080a0441d004080c5500c25041c1544100c4415030201d0440640702e501008039480078007204010a40c28a180c10b5904030f0b41801081507401003003c06100750501e655540da03000c11984060080c505511905d8800603d801116080c00105200aa02500040d01d080140820359402e101c4003004031604080d003070040d25840e00501c055028880c2171000c410b203650b0103e0002c004025850703805500340320400101c1c644149140b42454400c1c1030107081c1e500d420100c2d51076100e00c10700004072840100011b0030100c0c90740d00900c0e0060070081c1555000c030490f00310721281d0300070b2001c4441b0640055080280190300103910100900308403040525045c05800080e80319410003000c07038490f040c207504020a592003640300aa01a024103080c0400c1703600d0340400751801804a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 763373102 1250 763371852 763371857
    0x1e030e07060306060c02040e070b041710020c030f070309091103040302101112220c062607180b040b072001081612060b0324031e011b02010507 63
    0x80000510342d102c0c1c400d040c2212280c1d651a01030240b1039080001800c41c50f402d0084074412010f0104000c003590300140018030050403c604044101c40c2414101507500010780e074007030310500c881d51001801000700d0386040c0d2410041c0c4d55410262805840c2012039420440d456854000030110700000d0030021070140f4000c0d002c55031040e01144000095501c1d08260404121007486014071141c114416071b500a4201c1c40ca040120408880403800f080c0d00420a8684841ca00c40800c07206030402d1012929480c1000c0700c250440702d030300c5140084900504500c08000401060300c10300c849110f2004c001d440b240030306a68941d500c9030480d4041c2c000700c2054038001100d400c12943c0300c1c501da414416084c0180c642c4203555590340041031174281c103002804207100c0082145c80344140c151040c40c010704146004d00f62241881c017142da07548a13103c4040b10034840503458400c0c8270303540021701c98a0030000b0120010391810321105e0781c4c0036020342103c188030703101403036403a4942c43d8044d01b00620031402039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 763374352 1250 763373102 763373113
    0x11030304030e030124140102030c031204021e010917100f05060f01050319090318090c0807020607230d09080a03050907060e3a0507090b0f101e030e 65
    0x1500003a00c2d28121810580403040101703041265202030a000040781c00140156814184030081442c1198041420303240200780000130802103140400b90400c11082c0c041020752001070140001c1c0110045000340030684940d5100781a0040c01000060b030a1000701500303101e00e5200035840c10140c02c0a490503881a0440e02800745075507c00c0051b24811102680b4030302c3d15441c0c4a01d1b0702c1c000c0803041e000740c0c00c1182602c0031a500c0d200b0107190f200204a00d120005180c149649c0c014402c920180001301107410603401d006103d54010100d4011981e440303400c5a4800c0c90719807280407445800012076219007002403940500900c607001d0120080716480512180d0389003240640c94150500511003c220500c0e0001194213100041c031328030107102c00c0703504404e08c10002074080a40c502241d100401d19203c00c0c03a000c00006001d41030060907540814040c0c031404000040031088029010b9029040c0017081d0643c0c1840345400d030032610b444000c124003003418403000a02900050560741324078402c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 763375602 1250 763374352 763374371
    0xd0617010f06120201020c0f0301090206040e480c0d030b030105010504060308040b130f030f0311030405012024010f05030c010504060c050a06180201031401060f080711030304030e0301 81
    0x40540706000c0c3d940c142c2c040c0500070340043c10000c5101c0c880c00308540541d07030b034448140107880b408000e20143c0303810800c0418500c0c107002d4802d003140c0040b0803e05005041101000d460085c060010006808108808442c80e0f006501040e903001d024000c010034401c160031141c010b03400d54010a541c0c2016002803041d60380318001e100986031903120040c0810020401082840f4003100a8a100003440304a0314500340d070342423080300028203a041950701039409a61481010f820500c440c21854080000d1420b2601d8080040c0525021940c041000c4030350003054a5015421301c00300d00405420600c4880700c45120f044c499850f607007401419181c1013030035000f0506140010300510010303016502e0318901400c0020848080d40100700890707017132045440b400002250340c062884006002803414400b0748e058000103095480c070400d030702c00b00035071100107014881d07200141d40c1c902080c505059000b612031101c00c07103e41e00515844415408007000b4802010340c0880ca94040d100d0440c02800303a02c21 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 763376852 1250 763375602 763375619
    0xa1707030801080c011707030b180a050a051621020a030b09092e0b040c02030d06050402030c03040f1a04050a02100809071701091b0306050121080d0617010f06 70
    0x41c05880c6006c9840381c105a8542c1c0c8204003055030205c221301d400300350000c038000401d42c00c400009080307000c69009010403a50071074511a01d41e1141700c05100b48428200081c1540807401420346203010800041c214901d007100042c1500941c4d81060350071940d8913500b5038024000e003594002c140c800d040c050040741c12a200040c026054420840402c0b219404a01840020001200d11000d1030f68403148050352a58482c803030000c4082d103d402031680c0d03101300981b110441c2c03ca5041f551140b0700c140103116090004100741c03584503503c016034a2208100e400c10800c0e140b591510840e4609070002048108034021844280240c0b0944920f6201c2c50440001e0324201c40449007458a5808000c04009481543e4070300584051a400009030407881c0b03454a58a5000300d100c00f0201440034a01002044400d20520b4014001618100c000c61041d410a2014102e010409400f20070b02041e011880c44080c4c2c0880020070154030341c40410000c00368024060a261000f001290f40f0308480010400f0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 763378102 1250 763376852 763376863
    0x110f030103030f141206010909020a030506010e01050a1418030304060302070b0f0f1303110d0e1c050a03050c0c0406081f0b0102030a03050a0b0d080c10020702011d030a170703080108 80
    0x41c0c131a00c1c0d003000750b000007501c000c0c0c0c00101480e042140b65500000c0301e4840344001c0c80d1440306035802107201d01d032010015041000e040d000078100803040207a0481c4507444808000b07620700d80c40015039070710802103095401e0041c410060354117020000340040e0803034055000307103490fa104208420082c0c0d14184d150071141011505000440401c6000a1400749660181d1030391900c40d0070f04078001c00500c90790a00c0c140f80031002c880403030010800c440c418075160030200018a5000558955895a40d894580703030344200c10300409118012980f0004880c080c40340507903180c00a0300800c451a40c1c2e51805a0f245030041c110305c00312540c492440c0801203e401000400d0764180c008600d800104a01180141801002c105c0626550b2096010560383d104c41002d00710700501c105902e0300d801410041c00c000540c48a040704a104010920050b604286d07820354101c0741d40342800b11550100301290404071451001800700c00000880e0400d45103000c051301c003190080d52000b100c1da07240c0c0101c55a41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 763379352 1250 763378102 763378127
    0x60109140c0c0a0602030109061a0414130603080a030903030e01050f060f0a03021818151306090b07032f0d0203130b13060c0507020a0b0a03110f030103030f 69
    0x400001e1601111035004010100070324003140c0d5079214a89a144c102d80080c0c212818880e00d4801c20040450100c0300c141300d005070682c8042c070305881d0000740c0c00e1172119a9229805994074014110540303245522100003035412006040d507840341880000c00402c2501000c44c0405d1908a00c207880100503c900c901c5088100c10324411034540400304031108042c0c4401c47d40c0051501800310050f16040320000d6480d8813070701d880905082841d0689101c25048029038095846007100a031603070044d21201d03800c10481e01d0402082d80702420480050705e00e00101515165a110034000703403551560200d41e0007a00101c18102000003203648610441d4001032000c0c05000600c0b0804001c01a0340c002d50700701280031050b1083c075072145d0304c001c0d810104803511145140c84c1b40b180010300c070450150381ca48405a1504e00d251041940c0080c100c00060300840d01d100001240303018040b8000c0e800030060507498018151100180c0114030307103a0b03009000450004070032900031448107000e2200c86804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 763380602 1250 763379352 763379381
    0x14060f0a1802130609060e04030807020610260f1b01090e191514090a0c210605150903190c140a0b0a08040c05102001020702040212040302060109 64
    0x48030907800300106150004078600c18940d03134520029848445104030703170083c5080500c402d15494141806800604018001425504494100a908984000e1900c01e4403004000b045200c440101003002d01100560301341c0d42c5114230b0603481d0040300c00280b4140451400c000c8041502241c034011204501140726075503210a400b030100d00e101381500380040108503134032000544d901c041c88000448091f82d034008003e8282506005659080003d5000c3d840005c000f03041c0500d90f01000003c2400f0300071440044403421210315044131036000c0d0080d0000308001001c10400c44090104110107074400145144240f081502c4000e00340da010380501d4102c2d0304102030315203143c6040b10402d041e01c0650b040c0c80d0f0002400b9800700c0c10403280e001400207005941d41d05942440c292034024001a0710b034001e107100e42e4030400c01410459004105100014000c08050004164442da65001e8044c4000081d0700600220324001e41044040445115034080d0342103c1140e41d84100517022221510b01d1802e0307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 763381852 1250 763380602 763380641
    0x3060b0909010221190203190f020307051603110f0c190e1605090312040806091b011b02030703030816030903020307060c1205041202120c210714060f0a 67
    0x8079100c1ea0b404c1c4940c06800d80c005441074030030240813001240e004440c02e14101d88105104c15203e400ba128020403030788419811403460400403000ba142d40a451207035800603004150840c205445090945429044036007154250a1410700d8580c5070408130b03c0c914001c2c06400550380390100c100c1e046130111904c480480c8840d480e848d0b8440a807161281540050001c100400c01c12510f00700a21061048400100341e00d680c2096046811321002500728005903000d000c5eaa1a0b031341070100c41d41825602402d080e03003030850206649010300c0e240342c0c0c060f605d4058900c00005154011411b507109880a0700510006204c410054048a44504000d03006070700902812001400781c0d480310000c41c060782080e0407003105414200d070903030384126011a00d05041006c0752900b2601004201030360040500d84904280300842c9641d544d100d92104c003171031022950841c6d041051070320201c4000341d81000140b0711812021020b076560b031200703882c1305191495150000709000140d128884030428590800c030f1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 763383102 1250 763381852 763381897
    0x11109040c020a38070e0f0d05100b0406050a0909061503030813080906030a0e1b1f03060302060f07020312040b19020102040803070f11090907030b040303090c03060b09090102 77
    0x2800b001c840e04035141842d4000481d20400c209620071640701c1d170303456502c141201a0007014001c0b403020810071540500000d1461000080c80860400c4903000000340001d20a5288000036000d0030165000541003910040040380c1c805458000b42c0040b809880c080c0952500c414501000c0d1281d48000340001c0c1e040b01c04100810089040046880e0050b4081400c1005c004001100ca81c000c4c4c0d00c000919070b13038008100e803410081c00b52030805903055901d565401d051034003041600c00c000107607100d00c1401078600034510f40685d106d500616005031036541c46009149030b02d41280e005e0306050303209200300044240e01400401c200c0301540c2120f803502d81084400c03088120003202200c014410341d5024400130880440401c05000000d0080e103003220303803020f01e051100189219604940c0152004001c02148a00000d1020101c90303100c03d14070500e64450400f20020100007500a240680c2004004140411900b00c07581804084178591295280d181c115400c0b44a408241c440721541e40e080103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 763384352 1250 763383102 763383143
    0x91501030b062407020306070f0507031110290904021003020c0106030803100311061303170913060801181e020102070308030f0709061b0b0402040e011109040c020a 72
    0x41e5002400903041c000122098000a800c0710003108001e0b0024001281510a41c5810031180d0b40140190a011a601801400082c07141c454420064188030303030b044503802c0b1500d0800c0b0000320b50710a640204102c440e0700f172008030802c00310202c01000080201e040c0c85a0310305011120300032a0700a00c0302038018080c41e01500030350480d40004015540c0d40800001141c1410001c6104088520011400b0786c00d515000c041003090107403190003030600380640d100c08041480801c090700d82200c0d40d094803050001300303c0c1aa100b140d10942d04684800403846061500d90800c0051700d00321002844200c516050075014104a20b03406400d45d1004c0070302c5095110307441c41c030301d00c00ba0040c4159814551a501d030b401c490351040d01c004039000c6011041254440d84602070b480500740b50318100c00384c4404400010b1f070403030500c10003401240b0800b022a0840d611948201d25281c45200203000054035001e554030150400c0340c0352401942000003034034032644045212514141d00aaa0704015207903001c98 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 763385602 1250 763384352 763384373
    0x903090e10090b12070e1e100909050f0a0f060b01050304020d0204110408011a01171603050c09032a190e0702010b0a081b0d26090406080304030b09150103 68
    0x1819003000d2540301048008a060141401034400705032401007500b01f500341038600040c42c071660784c502031a030024006106000e80c076400407540030203000308040d41e00c0d05007a41030940141d170001b114070400940508000c06040303900c04590040c10200a80b11400005594910084a00075030007001e005140f0014a81a8020007a46003000c940b50f041c00d4541c1e150b00d084a88045c20491b01c0c7d0941d05c509111503030f108140004991600c44e018103282440308243c1444005011010301307250f2624005425056510150780340c0c000010200c0e2113902f1925a0070800b0040ea49020a07940e00d10858400b41d82400342d003150310150780180440002d8902403031140d817100c02410302011552180b81084256a980850101600418001c1c00c04480c00c6001142d142c2407445c1326500800c07024903500e01050201801442020300780f100401000c2c2003066822441c4074141640380e00c00e1a0020214048000201a100362442a1800e40064440140713036507864404022480c640600d050051001034800200c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 763386852 1250 763385602 763385621
    0x10020427020405041104080c0f010210050a0b0d0803180d0c060e0a080f040603060e070503041b03140706030e1501051e03010915240b09031f0903090e1009 68
    0x504243c0c40301c0002c3c00ba80e004407085140650007050602c03010b84103000c0081d0824045800c0030740742c00c00700c001035140c2d080419100c08050307548001030140311658000a46201000b00603040c000300e180741010f02034105550409045190409600424500290041d0a20107d4944007600007072680d800303001d840138085644040c000e410441c2e00280d125406014045270358000c05403150304003c802408c032222544201e4040707020000f84444150820112900a03070800709a0301000b9800d03055403121440781d440101610701600b5a07007034110020560a060342d140b55404d000241100c105599207032000c2320301d14016106400100510318255842241000000c110198501c45076400603085410103401600e550440b6600d0107407400080c403402079080385c1d000d50072000a9145032410340703500090180c002010000124039590740d030b0401906a0840341c0c2e0780c813108218a200c0000700a42080e40e001c0780464007001010450841042c540c034414414022000031039450850891701402c550403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 763388102 1250 763386852 763386929
    0x7020303130317040335340306060f230306150a0507020f0d0b040b090c060408010e150403140906041d0f010b1303021002240405100204 60
    0x3418621030200d1072070318403440c020b0311138002035802042c69a90081d40d000c01004602030a910f154140c042080300d164012000f610203000710b50808480700313100701403010861000030587d0490b201481d4590020001d95240d0707070340c04510000c88101520114031007900407107460030083c1c0c22503104000401842e4441d500400030105040d0b80d4175170794520342c0000c07084000036600283c00350550600d040322070821102950402d05903000c07910b0395400580090320091505904c45c0c04a1382109007040603607550a0000c0c01266100d50f1b4080e018002c4c800b100d07119a480c0070709580c0d01c50200d1002010307841141c040d25802c0c0030569000c43c005480e444007510302c0c0c0c441002d11000c84c1106401d90f28007141b08031410740004a09020940c0b14030450141e0004450244c00c10201406e00f10b90741d106000c0365419a0000520f204401e0142e0034003e240085007000304603002212000d442e02c11b026801079000318140c405130115000003d09a2080e0301a000c080b405006036007504641000520043c2006030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 763389352 1250 763388102 763388117
    0x21070f021809010608010c0f1d0406050a08010504020a0902030702150718090b03010e1c0507020402090909100b1905061e0c0d020f0d0804031407050307150b09070203031303 76
    0x440c62061280e2040c0c50185081e907581360b042c454030409104c2c40d41d0030748203420201c909140d603000c0203005a50685115009000011080030180c0300ca80101000c1c02004000d11041e41d01c4520017402000103e4003a0300c0380c51400800200d590041c0300300d07801015030f603010346803081503080708403c1040050324410030040185d000d4481443c00e064540007900e00c0c1340c80032500d10781d07400401d801d403800480c091070300b0f4111168141045074446025090b124403030909a0b2039215038000174009001ea00c01d03075900211418100702c2004030104c0d011044001d200c1d0304200d1a0500350070f0000c0c0c820107486100c460380540c042407180b86000b40c060006030424026100c12804074041e00d101641188596006650140301c2030440301ea011300c030721a01907400000510b40b20400e201e0040c1030030009003014081c0b000b449004250580441c00704c0e041150000d04a0355501054a4811490154660766092051500c00c0800561130b264416500410075940118155280c1411803103140d0740b446012010300460 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 763390602 1250 763389352 763389379
    0x304120c020409060905010e06061f0e0310060302010f05041d0a0e01090b1902030903090906031e060f06090402010f05222d0b0304060b0a0801050a0501030521070f02 73
    0x8030f014009a8600c64180490002210f103401c0c0d0035940c100e18986840e800c0501040040d480d124070740702e03220903802180303e00b61003500400d44070207080802e01a01070003800380030080030b00302e43c1150040764404e80c0e4412034407280030000c130754900a900030009601203c004107908042031807021500105007000020f00d070b4002c0b095803401c449801508580c225042000c0165980c080a0442040425504150300d035240624000b034583c4109801c01d445914010041000368408020042401c41e82030b03a00075441b80e015010640da464111030000310015040c00103845c07030401c0080240142d40c107840c1c40701252040302c001e0301c454004545441c906040c0301183d00e2819282c042482c02010000301903c0798108012034405142c4007051401c2e641c4070382d00b00400101a1038011260700075040711380000c03030721107a84c005120110951303c41981d6600300740c240501000d20340d20050480384984111146a00ca64841540481003801c1c06d8040041c14094500840c0d466203403801c00700e10042c080d0018a84 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 763391852 1250 763390602 763390609
    0x412030c0522080105010b12042307080f100603050309010c06021c2408060106050307050706020a0206091501050102030a030506030106030606120605070e060316020f010f0e210304120c02 82
    0x1030340b19034009034020410100841242803007140c0c05848007000c1d80f4501050101180a21513001d0700c010204c40807c0c1214101c68032840c80000401041015501c0a60b5605401c0b5034907218010f66507038070302406843e0320301e00500b44540700c2242d80c06405141000392200056404a10314102078030070b20b80801012007014054070042200c40e401040000b2400220700a07115420120788010302039080352030040c0804400080e00604607506c900d8a140d070f90b51424800c0b1943d01800400138000c500216007110480d801045032071240c110b00044422003040c40320202c01d42c0300280705290140e0030401069454611a42081340e1005d0054008580b150356075035030703104480b6154416050380c41e21051000402c40c0601401d5000802450641030704030f50840022a04e11026040783d10050042809030041030080c0403000680c81032100030440e6000d0001c0342c5020b0400003000d03000900450070304242e1142c140c0006405049070740e402c0ca08603500c03551a440c594a103a01d0f03003030601200d03000d00c40040c0e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 763393102 1250 763391852 763391887
    0x31e0a1b0201021c02040803070807031218050d0201110a0e01110708011e0b0f01030e010e061017070b0a03150b030103030c0605090303162303040f0c0503060412030c05 74
    0xa8030307500040c0e40b0010120985110000014a06400c500412003001800c60000a44030229000b83c4c243d83d0311545460103440f5a44007800c1810054101411014015000740e0245c024500400540d50502200030b4100d00700d880d40c3d00740483c02403044c40741c01c01091003203111607940074040c10300d844140b4140060a01e00842507104000c240c0d1551407204900100e54070420002456076020700001c0f1460001400c00c40b01c0b981c103076040607660050040c20117001d40000486e1011041594224141104a2a0722100c5801030444203038100d1942410700c00700103002c10864014041080c1859a102c1d4100c001d400314020702410311403450f1001c00c2d84485e402c0118000d5100c0c5c0c03038408144000d45000000c0d120001c1900d00d460304240200207458030f040701882064036240c07070312002030351000c0c00f402c4070300000000d11030a060021040004001a0070300b046002800355440b00000b0ba5500100342d030303c030300031140102103550104034642800c3c040d400290410900d400c0a0781462110120105140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 763394352 1250 763393102 763393151
    0xd0615350f060a0b1806090d0f030e03010b030f060c3105100306050102101e0908071b03020d030503100b071203050115050405060702060c01020a0c0314031e0a 70
    0x720109000d10001d4900400b800e00180360100c68981410004500712407010600f14045014207000103051100303079036404a4013021030303001c0700341a10b04600c0d08005052000c551034460080d840c000b4221510300d00043c28901250b8010700814450381da00c138000301540c01641104542019012901d03c0741c5000d216100c540c03203140f07449400807a1801040043c203030031220400051501d03000c2d05020a0364041051a0360100901c8040380d0003440903a40281c0c000c90074041c4106078540b8a91404108070380004240e928043c6500f809103101c2040c032000383e5500b501c4000d600a03c1900c0c00303c0040c0c0980d0103582d02140861009030100c0e55807a41c44d000d07902413401220b00c00941d0580740e0780d4a4140c070038103000d400c550800a0b801d11040c000580030303205901500c4d10801020034014115500c0fa4102c41861400f100259221403017054040c3c100503c10208801007905050810841855902920310420400700326410f88803c10007640e8000c1c0c0c010f004130710031a03201c42e45490703184101c800c20340a9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 763395602 1250 763394352 763394371
    0x5120c160320071710091106070f02120123070203030402012001090f0203060a05160e060403020402070605010302241801110f061806090c060319110d061535 69
    0x2103030807503100c06081c58150403040010511b0000200c01141080c10050341411003034662a41d503c0c1141403520f0168569000254055007104408480305010341142028418070b60791581c1c810544415414901c07411203040c00140e01c144000340c059881a01404034002e812a0214410102c00303400d40e007580e0f9052303025a00b401c0c91441100450904000c00ca0b405440c1030f0081005c0d00306440e420711400c003803030803c10400461002c001c400da40c40303070301702c5005541c000c00071903494900f0714100c2d016101c24070003644500000311402c0d00b000129006401074014098401d071610b030701410180c4031001e11020140c10002d0118100c5d4070880108184085a07112400404041c030704406045c0d000400043c001070780380c0040b0b05012034201e00141c180500c03070044818588984d101500003112003040064004628140b5400d0109a00c0342c41c01480c00b040112002d100c02c607110322408902510100d07604c00000d40c4046500c01c25040d9105103007010040b2400c0039022880c41c0b44070740c010141624207a12 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 763396852 1250 763395602 763395629
    0x71b0609080714010e013b060a0917010212090f12031003060f110c0c030601080d0503130525080706140702220f06090501050909072306070305120c16032007 69
    0x401c4684040d9247d20002120000e01d00000761070000c0802d2500c0c8981d6100034008003141c47c88240039010786113401c59035080e81e030040c42d00e00e8181b582c44ca0920840b5030b450003004010b01f0041000c8003128800d01c03c4040c0100384a2944c2d076604028000d05030a000541d41e107159401d00080c9401c02000c03c4009a40200850b118402c105810140c0603030003104560b0000e006180440d4228003680e0344240020389101d0400118140720f030900701c60a080031044500d5100040c021081284c9403400d4800881c100ca01c1c4d0b80d00c5d6502a10030348044903030700584400c10b200000c014544009100036024800307451002594400c100c2000740c5944004442a280c1ca81e802448400b880b885010b004003801c4604852505000110a4449410340500c18a20281c11010302110800070f076190341e507540250409a0307915980c14028041d4000e480030660002400c000704128500b4403041c0c0e00e00a4980844405181c01030341c050303418400c51042d840c59150300c81e40c600030741c1009011810042481c08034418 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 763398102 1250 763396852 763396937
    0x6060e010602100f0c020c06090a0f06050a0305070206070e0f03012d050c0403020114181504140307050a171015060f0807020303070c08071b0609080714010e01 70
    0x1515603107181107080c146010044000b1980c005403010102c00c2c148c0302c066403925520b02003030381101a40c02a0a205034444e00c005603099000c0003c0c021500140c1e001c004a45a49004031f841e02800d440440000e1808088000685010a21840e21480003000002c9500c4040b0794281d0141380b24040307003c0003005c5200d000ca10304076405420f9011114110f954603203811a40080d1058040400302c404c10400032030240b0134a2050b0a0010b001c0c40020086e00303168402006032000c40e80207000340c41098000d518245c4083c14000b03000c0003547c0f0000e100c2100b903401c058020100291041d4900b04500c29402070441800242c4100c4000603030b620a035400080c14032102900060751748141c6030030824580c007009819030303011003580e030090801d20381407404001c1428000f100d80105000540722084042d00d003c04403455800041c2141c6042d210710060507600c1d400f0310f03140e20803441400c05001105024040c1584600c0b0003400011050400c0351500000340404130280c0c82c0e02a003541c1e854185040031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 763399352 1250 763398102 763398133
    0xf020a030c050c06041103031b030d0e1b040c03060b0c0a03030b0604032a080d090918031d0616050106090605041e0e011113031101080103030203040b0706060e010602 73
    0x40004141810300c14a01034680f801c45a5402c00103001070903006050380040040e0713030300784204d402c142d14180c40c0d96018041407240e180ca950050250b5880e151030408016014007010800f0541300e801c0d191a8a030544400b01840050602c4002000403d652002d005c191031544c0005080030702000c000401c02401d49150140c1100c1c10043c20900c510400e000401c0001c01c5142090403d01d0310520300c01d00c600340b0318070018625055801a407801c2c01200c40352000c156110702035000300d880300c2d4000e020194281030003e1910001c4400035000a0f00f000b000300140708904650f040d480c5025180c0d40c502140000031442c00d0350045400c032003503516143d04011802d014003d600250104840c01c02400914003036848107400c0c0801c0e242c02c1c2580b181c144241400d429403003014005100c16030245d64540c822080f03a82844a800111100c0003400000081035200d40f03141740c140c9615800171442c16040107506c03403007500407e03003c590460b20b800c0081101040200030398004d060310b8005081c01d554501c0c01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 763400602 1250 763399352 763399361
    0x3040c060206100b0901050403060204060c0c170a0f051c0c0b010905060a0905070c02040204141f0c0b040c05061c05060301090b15040204080102040609170604051c02030d0f020a03 79
    0x100c110350089051000d07040315101c81c00b084031407403800d007941c0c0d03440c480050703541c0d0080f0fa0020700600d00c00700d4001101340e0804008848507100d0b0500b1401c1c0c94a902080c010101c5a0440e0042070b0b1210f81d0b0200040c002c0d078109400316009208491003240c40c0e20821095001e07000c1386000007204003084608000c106007049000d072259403001e200510303011012031105400b80c4506400180c503400440d850034004c55940d00041d4019009550f02c23130300c5003031280322143c40c006c3c0c2a00034031040c04c1d81d104003440560b600d00040304d6551042030589054490341403044028000340d452281504001820340d8803800100710312011010402c640e144034662500481d0402082540a80d0411061000040c031180803540e06c109400d20410041d800d0342c000c075000340500e40041c02c1540c40002d01040e800e40007441c010850308102018880c1014050781300d900ca503000d880c020b20a91115640c40429078034800c20301c0c21209a44100c07400c040760040050280e5032064256407000ba0f00150848150358140075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 763401852 1250 763400602 763400609
    0x19060f081e0d080408030411100504151403040f0312050403020d03061410051c091121070b090d0204050f07140a12090f02030708060604060f03031d1309050303040c 72
    0x18148446001e0b00103000c000000304010054400000010204914500e06070050346024001d0880c2040c0110042c0c0039500c00d00802c4a222100c12220701c01c0c611072400003003100003d0f011035040d0348031039540760700000c1c04007000c60500ca54215140d920390075501c145407245019a008144500c0d24210207000c4460035044903640b4031403070048600d5901d81d0b02c40d10308101843c1c98950341c2d81800c1020086420b4501c0d407404c1440341004405020700540b010241400d03d4126014000010031001d240320002421128a0040c0c00c166400c100e0070b01024041c01d0951400f81007410444285e5002400301c910899607915510440001d0000c0301e6803190301c18181d02107800d020362a143c035a10015140c42c404543e046000c98641624004003c515100c02d07506c180d0180c100c41040d80c40b40c4809845002c1220360038002d501d40440020715401c1049184116501511035444501d50440e00c000c0d20301ca05246e4580110b01041c10b6001c200d114807174206a1406000590f8030303400c1c94030302641110225030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 763403102 1250 763401852 763401913
    0x24050a0501060e010e0a0b04171623010c020a080a1709010903020d0519150c021f0c091a0c1203101e09020a090312090e19060f08 57
    0x3001406a540c0000d00746201020134240030261489200001c1c010400300d400015160a006c1000254540c420741c0780c07081c2c0540d2809030368a01e2408100c005030040e151107003070050215601201243d010702e030b20b2800311120600d0604148c6005401203108200c1c15030000040c2e501140300c400c203001c88415070200002070712801614058103500024800340050001920030b008120b964410020108442d24036900f2443c0c852503a06424209003210500701c8800d800030504052070040340e144042151354028860b48203110041d090054004020706580c0d07008020f20803086408070721003002c201082a0268180103040e503548000176000c2c2054201030381d04006880501c10f210140984140c40c10542d03280c001400b0400103107a4481203401081d61002075000e01c006250075503591300408580a4078000c004042c102c80300306104540d45074192040d03a461403940da01043d400e000580f140d40100d040c1c0da0b0b02040e09526003421070100c588a038403401d9154808503090781c04080d6a40d41409811040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 763404352 1250 763403102 763403111
    0xd0807050921011a011d1e010201020903070801020d110702090105120a080304050c1017060111010b0415170f1b010323010608011a07020d0c0324050a 66
    0x510000c0c1841c062807034841d2041a00100080ba0845401201e250411008000b801281018400b0b141c4283c15041801c0c0001c6682c496441452483e410300c10034518003804420f0003200c07501403444004521080c1da0304554082120403003664040188001510145d07000595440d40c0346d9442d070071168200c000009210f41440080c0150b556440c4007811143c05135100a00c02900126284c00d000500034014210f81010040c0014840d0020305e01200c0c0300151140807a0310b400350001d944c2c004006642080740c1c0c010b4400a009075204200203504101c0103030012034210103801c0014140d0b1804140542e5140c1860b8080003034103d280405046040e03842d01030140c2000c003509598460140c03075100400740310154400781007030748240c0c0902c608007841c0365008100c681a0103480640c0d2000e2082000040900300081201b60541900c0c1015074a17811842d4a81030003a07090007401c00415409403032014000200101280345c030300ca888001c00c00304281238040c444d01d00e08481151806044404c41601c1c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 763405602 1250 763404352 763404361
    0x10e0105010207031721010e010e01050d020603040f0203070b0403060f0b0103020c03030703020711040501082410060c0507080319020d09052d030708010f0b030a030e060d020c030403080c0d08 84
    0xe031031000c1c224400717400c2d19a43c50300e4907240d410071050f0112198420441c20400000c501c441d201d48030b416524100109040c0340d80c2c0e04104150814200c00c040d500440030070100340021071044040040c54805000e81c0d034000d0381e0b43c50035034554001358010b40d0210b8a4030601699980d040c0700d00045901c1c2400c045081c2082013030000c0d070303d002c000c00082c05d265000076084140600b901c1c0109581c030008005004079a10399191903119000301d03503c3e251000080c0592004011440c03807681c401c01d402000d06080910b424821580169486410f450394000c040d40440d014006100401c014400e00d0100c50780718002d01802445c1541c10040401080802030090001da82c4d4070756440c4105582c0c0b0310181c61000100e0140c103c9640c1b005036107501d4403444500248040d03040d0000c05203c0340404040203c1c3c21b10009168582508a0000340005d2070207008403810318005024100074808000300504090000102c0785ca0b55000b0381090352045d0300416007060640b010815122090114034000700181003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 763406852 1250 763405602 763405613
    0x40b130b030f1912020304181a0901050f060d0b090103061d0d0e09190c210b0d03140c011e06090e0703060c0507021e0405070203042723010e010501020703 68
    0x42c1c0004c101e14451a07003c0e0481d403080003036038054031480030200725880c4640c1c0d41c5030080124034041d0016007440158110186040d0040604807980500b900f000d86003800100103440c3d21642e1403821680c0d80700800c09840e214043c40306d010307500c5000001440d00e0141c0d075500602d6074400c6200495842100310018042d403100800701020010b071001c0c0101e440d02c0002c47c644144d554052880c0500d020710302101c0a6100402e85011081d0030a080d02d014603050b03d6005440400d152103800a0300c0b0a0a20b000074031410140352101500352006050408074401c1c6404d45030001c950b10203066408007112490107030703481044010002c80408101e100499a041a1500918400a013500ea69020500f025500078011100d02da03500400d458442895003611403401140510514042c502d40b03000100001d00000c1114140d9801781c81180140304004400074103141c8a07000807503410b4803008500480e680700100d808506104141103010340d810b0000d140e01c0f510050f4170141c11944150f9003040881ca = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 763408102 1250 763406852 763406893
    0xe031305010c030507050d021f02070b1b040e0c030a14160e1f0c1203090503030f060604090e01090210141e160503070b010503060c040b09040b130b030f 67
    0x28400c2c01c01d240303195420700341510716000c1c40c0c4014100e405032035809403c50754040b90385c032140100112010a880b40c0079120000b240a403100084c240540d0501041600d00c042d0820f64116442c1c0045516150311055540c1714841c01340c455141e218008014010703081014010b44405400c011206102c41c0392040148024000c045488020301020808065240d25a01064480da0383c2c2c4c4031040741e0b80403403400001c040c041d040c0d20650702681d03110118200107109000e6114000c0d081401541540c80f502214100c2d1440034194681c051820400020544014000e000428101100002e1070701140c1c014090307007013000020901041000307a100c201095001083c1d070340718981b4002d030038071f0b000d4004901c20071842658035110001120b828000300700000000200b0f0307460301c2600c0130301e240d903038a400341036946c3c0c0e05903840e0140d10341c20303c4140102d4960030f02520072410300900100d130b2849000089003400002140c0c3c20405c5845d61085485800c0030400e1103d80d8007144000c110741c00c03030120303401c0416 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 763409352 1250 763408102 763408109
    0x80a02070f0f060f0203090703020a051e1c0b0c0307081308030c07020f09090f120a0914180f1b0403021806010207150305040c090c12020d1d010905010e0313 69
    0x1c40705142d0030b0107004251303002102e003110145045590b4200502c5559846c201844100e2181401c0d04011030503092140d071503040101422010030200e0105020084c0b0b075690020301d01d000480000ca4040030400c5200c8050007001c00d251116582c0c03d000100030125903000303018404403221024000006286581180d502c000d507101c100d0340703c4c841c2d880000c0001e41d000390202e40c82000541400200017010445503a5030340c0d03103411900fa00c143c10340246e51600840b5124408140b0328581007040a060040c0a50742c1600240035101100341c241c0c0d805011002541d05482c21035680c0104050242030b83d0400010403160011765003000c0ca1540000c1101d0422010307030320b48a50140100d0307401c0c2d000300f0024028240706d200c0b200c03200010110060051004690980e0000000180001c41217240e100c0e0304542c91659031207000d02c0422020001c0a5404080244401c582c1d441464400e949015000001d90542000211309a006420180d0a458bd80200d00c1c800c2c1c0c10800400a80402d00c501500c01c6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 763410602 1250 763409352 763409363
    0x6050f0904170c070f06021c17180d030b330705010e0d050307030c080103031e0233010f120f060f110d0e0d050f0f1902060403080a02070f 61
    0x941110506405005260f000384580c411030801165106041000100b0750361260300300c40f00d5640c14420581c10240580e5901c001c07440002d03180700301c45411500c2580c003032100c58083d18820600342290b86040020300c444000617540d8104004c41d032514004140c013060201304800c0c0c802c1011382c04038003c030010036068205030100190050070032a007900107084030b040307600944981d00d010030005081d584c0115440c0340024606052555028050341900f4140c80d0103070388090300307241c0741029018440400e10740c0c00305501c81c00c14030502c0c1c48800c0100000484d00d48100d840c10410b205454441c800c4107130050409084802401c0c00450048014041a15080280b88410006505280700104001401c448009080400118003c200a0020a560300b0135901c10030584807039900054641c0410391112000540800a141c84400c0c00005000124210000249040341d030381502d03d541c1c0d800e0031410003d81c100320200000d0581001010340d1004014009600d0303c1d41d01d40d0b03038404011810100404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 763411852 1250 763410602 763410623
    0x15080f0c04090f1406190603080d0e0a12090815010b070807030306030b0c1206090108060c07030e03150108060901060308071203022712122a071806050f0904 69
    0x5102d4203d04100b101900701a45545156025084540301d00c400c980007004605010380214515155201c0d0380304613600a848241050984000d0001400b010f120380c0e0a9403041d05842e0000c5407d0504002c07601c0084c3e01e4201580b89040c004a007481410b0b903480c3c60100903000108481d89008e4202d86000b035010541c16034885d61480c041d0010007241d0409496114004100b18900d4407a0005100940d2013860785101643c071501041840d01d0240241803158002502090583d03c4000141120307a00c6400c100120600060100f80f0700f102100b141c00a03c807170318004019008013480400e81020034640240190340c10f54444150500c42c01000401c00d10242c0c4c40244200c0c42541030742c148203064603811091480004a8102080081d4002440b5015103850303074105040004803009000650003520303052030f60031000d03900c1f02c640c6407942d020b0540303010480300c503109028442e4a010300040f148c000e4080b91150b00071021101e0681080307009122a505100305030781c46c080520351083c0e10901e9500d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 763413102 1250 763411852 763411871
    0x1a03040c03080f0408070602010b011d0a0506030a060306020f030402040b0d030503010b0307050c240907030b0612070518091b030a1401020f0c03120f06090118110d15080f0c04 77
    0x44030f4480c0364003100345c40c01101c1021440e681d042d040030000e507000340da811200c0104a21490b4400c114000035981c4015603520802031801c000029660010003c140004c1c1e039903490312620183d03405540c5640008200000b04021450a4812818000c1d000c0d140ca00390042241d80c081d10500c01070040c0540d00c4070200000f01d0b52403017001103404a01c01801a94000391140e0401c1690b4120041380d0000c000c00e500004040c4c403400982102120f4000600c04000d46450042c0000006c4000e45003100340202000801d05440b00c022071400307001b182010010b00d1602c0c4001e1414110354038210324103021000100078003940e00181d940c41003504100390050b08024101414028441c030005818980c10100b694414a034010001c1c1c8980406001d44480740e80d9001000d2032005821038100ea404041400148826002d940000d00c0312200c1000004512440166180c142d42140d10030460b265225600c44100411001400c001080c1440040c4002d80282c030015440302421036481d8080c1c1e031707941c1551 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 763414352 1250 763413102 763413127
    0x6070b0a06260601210303020d06030c1e06021f0e1606180b09030d050304050c0d060f180201020d1b0c060201051f0509010b0f0d151a03040c0308 64
    0xc0c480c14000345080ca031525001103042c41d20180040e01c5024000c00002c5106000340310f182c1d280d20400f40c204902c440e940d01900207410102c00a80c40759510031022000440c1981d20b44042c0001030742030000151103040307000c2c52041c141c101c28219040480c501809022011048642c00c12800c000b007650895914611b107041024140740e00e0078000d21400103007681d0045114400d007a040901500c0340c98480c54414000d10a090000e40c050340032090a03000584504081d5030410700c108140c0b24621188400610480e0600d001582c51695502d8011049049071050310200d2600000d03c00c4d0b0b4064a4002035180c1000d01088018090031807615040000c601c0030251071f0b281e0001444902c0e0b034403000f00a000f480210f80d41d02a00c916142402400304a04040074103e450003049a4620380c2005640022604850034248581106000042040410b80a1443d0f0480100d00422a151411080b5110f550304441100c0301749030304005000c0410051169541a00c0e00850500d035140c20490342c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 763415602 1250 763414352 763414361
    0xf0206090f1f09050f13021e0f0a030b0d0b190209150405030c0108011518090f0902150708070809190f080d050a020613020a0b070506060a0b0906070b0a 67
    0xd1580c00081ea6100c0402c004210b00040d80c2d10195075140e902c125220401e2007222001199007551220080c0610046000c00307030020103011140450003006444e443d40c2c8428a60048120031007504000b14a0501180e4944280b4031030300400c441d100c041d1000f0392141d0700da01d00e01030021441550b4440d0019030600c8250100c2d0750481014101d8007505a0b5071314011a150000e00556200380162603108045600c6812100c2c10b131050081500b40d80d01c0c40b00d070251354140c8600c0d508446000000700009800006200d50f1211403008000418249900e00c1080810800801b601d080c640c0306103c40000700e5000341c243c5444551000d4141e83d6401d9000000d0256030701c800440349e0342d00c0d00b0200450b280003d600a60b04480c40f20044034000c540222003910301f400f50940080045e405031700000c0700c1c1128524868241400039041e1400203803180800b1034543e00c99a016941c540c07200007446854108103072a40000c1c0485d80100781406005030024002c2d01c40d03140081c1040c52004041482071100e0b910 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 763416852 1250 763415602 763415629
    0x308190b01360f030b090f030f0304050712150c08071209110a1509080c0127090f0605130606020601180b0406060c110d03020d12060e0a06210f020609 66
    0x1840030016503030f1060f100c469942c07800200d606019032804140c0709040001d14240e0a0000d4016604105800d14070032900c0c0c00082c0103403220b00c1900c0d8001580c551000150944038000c200303132115102c180c3c000701d00b031729081038800e01008503120800842d180d200c948030178448000c4201180c039101a00305600d040042d10302451b809890310100144050103001402100003003510791402255560010031b0700d0340103040149021802c107509490681031070300781c40b00c2c0120001078048140368450302d182c002c8500c00c114280100340d4800d0180042e00d0810104031107841110b40030b00003613082980094442030184500c113172a0074000340131440e89500750030441c80e40801074020864550b644100516031000358030103070f0310520a0100c41d13001e070400c00310240465030035400504003100c0c088411070b15001c6004030481515138540000c6800c204040f080c0d1302a009500c2c0106d42141042d104980b120040840c400010061145180000301a210010030098040395407684603060f40e00424001d100d08003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 763418102 1250 763416852 763416947
    0xc080303090a05060705040f05090a0f150618080a0602250605061305040f110117041b1e090b01050409050f1b0702031f0b0d0308190b01 60
    0x30402048001c0060b00b8522140a003003201c8150300d443c80103070340c2842a401001180c012414003031001d41090762a4540060b44100f0015501c100002043c1c100c0b0f80360a0072200c004140d800400003a50301031034200e40b11000d50f0301541098030303008086a541c0e07030007600140120b070040b03501c2c0c00c039401d810440b108000400a01d0000740d003051801800401085402c58898550910702c0c0c2c00c40f011920505100c3c503802003a120010586403101e03000344102400e2241001120b940c0c0c40a070a8680c0b00c02405180f00300c447d52007201901e610f516001d1880d411540d0305100c2400001921900d000c8800210340100900203410382c00800103d859125503001080010306000901c0445c40548551034854070030411011503101d1b6800a03000e0314842ea80c000b96240d402031951100c900502c0c4000b025510500b640012140980f40c045224680d101200b41c0104041d0403c0000004240308031008103078403a0002c001034000c00c0c0003c2c2c09141d4182d07030180903025410052002503004c3c84e0b903100449449 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 763419352 1250 763418102 763418107
    0xc030b0d030201060e130f111302040e0f0105010f050d050717150111030405060f181906020606010e1c030309060f02040920040b070f0b0f09060f010303020c010c0c0803 74
    0x24100039000c1d011501c1011900d840b458001b42608890401c00c0e1401036200351140b200c0c07141c68a682507040c01c0212225401150326686203a1518140b0041009211010381c443c03043c41d010740e800300503007416800b1781d0500c41d00c80b031015680c0d94005c0403901080c1a5180002c2c0035120220200e1308a135040b40922904025403090090700510701c050850303030080c243d803204140f4400507011034507070280d0310525030000014000e50381d0012001d4040c0000c0c22040e4480c00a000b918000980740c65124100f02c08907902103441404850b5043c0400c0d940000300b801e11604401e01d0310b020900b143d152104031a1100040468101014842d401480740c4030b4005606000c1e1040050b1908005d5209114402c4194649955400885008040c0c6420020b0385111941810b2038402d071301c201130344010002c550108074640c40d01c0024940e05604c900600c0d00802803001850711107a80c1d481e1460140000d034800444c03030010400a5800a80312902400a20b00642e1004c0f01e071808079002c0105400904290001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 763420602 1250 763419352 763419379
    0xf0311100e211e0c0d150c020a06020712080c0403050709020306031608010b0f011106071413120b150d0215070506040822080d0f090521061506030a0c030b 68
    0x94098004000301d0000c1544c0f2449010300420840709a48140200300b4811280c10342c15140c07550740140c56411282c01038540d80c1e1015522a000c0360710074030b411620100c4c682011004190301c581e90a0340850403a0000c3e00d03141c21515003541d200c50f948141081d094002002588a40f018090310702114042c0c05040b01c107648402c8614082e0407504051401440c21011504440d03208211003c4051554005000c55494824040300e4000d0218000b28406c803040100c002c0300c403c5001c0700c0000703117001603809000c00c00c0f0386030032103071140040c0600321100846182c9114030707600c108400e004160b040314040702024610341030301543e018450020386140904010001408101401071844c100c00c0009040c000322500c085642c482c07050b003c0d0140c290721100c40650100e000c0c00035540c43d845141880c0c49d401f507032072001070b081c00042242003042c2c903405046040302d00410030005410000d60245080c1d02459000420030030f000c000c180030366450316110702d0710466000307603c01041d0b800082d00d00c40c000c50301c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 763421852 1250 763420602 763420633
    0xf040209060c0d020f0a0f060e0322060212040305030a0804020109050d05070504050c04061d0303040e160f021903080c091513140a03140f0105010f0311100e21 70
    0x40040c0f800058051250316010b020804141c2c0301d07041da031155a0308130603982c580380e007001040040701103101c0d84010014280e00c0300d610417840c04030420303c02207a4515030034800024208030000e00040c410302c80900044c00001c00c0031007035031100c1d80945084d06c2a0365903400102e59803005070f409140c04c412444141b00c10700202140520a44005550603c41911030304030f54182440340d84036110014240a00c21580d1140051520450a03802421203003443d448003030040c40c118051341d031003482102c03a0440d24075260f04800c060500362501e0014007241013071481500ca0014842d0001020040482c0000c1c1c0102617a4059802400c3c3c080c042012050b51b40101700040d41c810481c801039540e46010028020b00600341c0c001c0002c84c0600030003480e83c1396039151485040c481280c9141401102600000726409124003170080c00d4504e02050040e185081c0358007484040c88c02203003d26091400e100c0451b40040c0b0b940801281525507503016082402079410b501900d00ca011709034042c0c10f451080000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 763423102 1250 763421852 763421863
    0x40204140301060f080a02061e0a0818070f05060c0106210c1203120507170c030105130b0a061b05010c1211070203100e0a080f03010614030907050f040209060c 70
    0x15002041220f8964500e6040b40e03529100780ea11703962040c1c0c107100c01400c10354043e00d00114044411490404005004243c0f5000300c4420030010f0301400030003444032103045c0c112070a2071002005d840383d5800d004645101084a0140f0781c01944006000031138050309500c1840204108244080982a2008611a00c012100050310154000c601c049950b0701e01540c00c2000701d07407640310006507411848003039001d400020700b108140025000168040410400500e1192800700c05496482d03040c60300300100b020a108150080e03514004112015440c1d2041040503a00d8074100952000d45102b4114030044d650400200346500700b695000c607a5420241110301c0200600040c002440045c0191106000710907010f1b60590205c0c452680c903154540c00408402c3300c0e00291440e4071400e850b0800c8a40c0000c42071720304c802001004101c0c05a1200319003845010603032443d46582401c00d15290794600a0003014480e504419000307500395160b074102c0d424204090300c0c20380c4030f55040c0a065280e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 763424352 1250 763423102 763423139
    0x6101d06120603070803180f060903100c110a0317040f0c080c040c0f020613081306050702040b0301090203030d0e101803030c0306120605100e163f0b040204 69
    0x9128a25005c50702c0f07040441502c0d001843e500c0c801040700300c1d042c1003144102810159035001002003000681c992424020582103007142c0c407020902d840c80e110700a001c101075480d003000381c0d00301030305e0000020751008026800003262020343d00300f41c44a0401c04c50702e6600e01d000030324616683c50000355114012a4580d4042802c40d4208580c0440c2201a02c001c0c00c9030400b400103802c050700040045844040b44400c80f0700070003a01c3d043c4916490706170081046504244040b6a011a0020440c5041d00070f0703d0541d1806d500178800701200341c1c0420b03564001c084ea0f000050b034807961040040b501c200012510480d00f903105004140046000c0d480880265106600190406900c0f00ea182d01134010b01c0201d841e42ea060b40c0510f171860b210000286000340c41414905441c000001e11011064800f9001e25150307003600c2103030084920301411200310b2421349815090000310038100081000c42c0c841154000480090b06010100003e0f0010810007800d5640302d0320214000c14501e001101c03400c601c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 763425602 1250 763424352 763424359
    0x14040e0102090315160f0504060302070c0b04120c050d051e1504141e0c190506030a06080d090b0a03020c010b12010501150e10050a020321040c09020306101d061206 72
    0x205e07000c4080454a0310004089a404920100402c0042ca0700c01da00400b2003e000e05e584035100740e03e6086010441d030080d44840740c0080b10503034407400c1c001e040d0341c0c290080a0803280c1c841c0169041d510701c0e464240c1480c1d1382030500340c44040c204034100103001414001070301821030265072400c0d10b42040b0070254075100040502c506180035200d82d191020090055107020020440d1050310010400540c401d050100c5040040e880f00098945404001d540600c4041d0030114149040c100302c20325003250b0445010030010129810480c5420504c122580342c0c5480c5405a9107800426000307025107038500141b40c210340a03200704c01ca03034001940140e040c0c8140d40042c0840042100003250104940074100d98000070006825603654011001001d00401c180166401c0080808070400102160040203820300d18aa0070401080b442600340405072182d213100314218100b482c0403806035007040c0440014044024080c0710060001d00c160000384600a1000360343d145892480383c5100c1c800c0d9800c500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 763426852 1250 763425602 763425631
    0x1205071701050601020a151104120515010f09050604110703020d1d060f030907050607030302090f2d04020f0a090503010606050901050d050703020706022b0614040e0102090315 77
    0x1018001801440e000f500168010280b1016036140c084120246148034804d035640d0b005c000c140d0710b09110241c13000b8915032003102c1500c81e484c2005030501120709100d00c0c24000b8940144901145450302c4016a2209103000500d0741d40c5401007002400c001081d0203c1a4012501d801050760029402510394070681d21807900360070a01507011248950b0854a03802401440708546c07000000d400380d41d000001c0c41c111604a5a03c030045480c03070340424810b40000e074000402c1c000d02d08100070000c2d890901650514020042c1e00c882c0002002036035803c0d1000d0788107545c010b0590f9115010303070302150692440d641e5942a2004050000140c034411139010794284140025031901074402d07a07045004c1a103d00d45050200e07040c45008040080c15078003899424001075000c108544081c0125840e5100f46c1c40000c0038030010000418507401d1924107075410300c42e062101020382c0c090703048030250945012400c9615000341a0190041001041d0180300d0b44e0034410706c80c001801c41c0307401099070310329191 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 763428102 1250 763426852 763426889
    0x30105160e03070e011206140105100c060209040c0903060507230d0b0603010b0706060b0f0f0304030207150518030106060f0c08070605040b220305030106140702040e0c1203070c090c09120507 84
    0x1231216024440c0c150300105860492815500486016000794441c1c2801031409110400140c02c642000002c1000070300c0c07111082c0108081c0e031180340d400200c103042014441d2280e40c0701c00c40343d41104005001401c0301207416084815144c200300500c020040000d602c07580c481d80300c40101d8020f00020748845003400c00c00500c10366608100d8002100903d95079107800c20710071003001c6d40e0780f010b40100c04520035044006400341c16080d0030000249540e03501c0f82e50f00c4440c1c0d80400450b01005515100ea490414104107068208000740305510450609079401c03641820b005c11117004043c009010141490208030400480b01d445034460390109042c2c2a5a08461444500f01e0102000c000c010403001c10060181900404294844007004541180382448590100b020784502884801407680001c509003034600d0048210000340b21201d006500b42401500d510a0142107441007404080c0d071152001e81761032280d00a003000e001000e0034080700302614900140d4900e900d20828580071044113065 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 763429352 1250 763428102 763428131
    0xc150a110c03090f180c070201090503010b1018051302070b010e010f05091005041505040c0e09010b090103020c121201142101020c2406030105160e03070e011206 71
    0x81e412a09400d00850900f01c1540500254510303c0b404a54000018008104400c0c006101c05206000e507054041c3c03034a030188005815488903070410341c4642d040c07114480d49038903203501382ca0320164a446d0200b03181c001405550f500c0b0906401294203d254054003101d41d90043e001016541c3c40f5511126485c2e0741d41100f109880820701400e014001d01c3d0104020a2912042c0e10b03410107801b9908451550303484000404943c01031400c4055032010702c5080107035151600c100400c003a16820500380284400c6e00140452205010384041c0714408140000c180c1d100383d041c0c60384220104100d80d80e106419a4000300d80e0031880c1e400401525040000c02c180040044041d40b62070f01504452951400d8181d1150b5000418980d050b550741c01d0084e0642c414080101c0010503858460300321098055540e403008000c0300030315081c001d85c14403003404070010b000c0c0e40304a81d002d260300e4144140300200001070f041159035031100b00b903031040c81c0c00810380e2003100c4803244016205800403c1342e9102c20002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 763430602 1250 763429352 763429357
    0x1e020708060403030f23100f080a081308060906091002070309030f051002040b040504050c030f011e1503020a120c09050d0c080a080a021b091b0c150a11 67
    0x5090300368100c900401c001a0107a04808110038446401150340a1030700380d0086200d0546100301310b4000c079202804116140300900740d010380801da81e07081444c0d05004245603100c0c0e041400400705400054a02d60503840658075a01030100c110a41e40281020000143c1d82c0c801565068040d000e1280080c200901501c02c8402d4164143c59401a0501e141c42e01c03007c81c020410140c42c107004490b038420000c0b130b01d0b00c000c00240ca81189425100e80c00e00c1c05000459070300400fa810390302800c009004c442680c031058141181d00242d228504441c200b4554040c03900f095100c0700210a40e00c0f034000d00d00c0d4041e0040d01e29501590744000d1802d1070300b10500140c0f191110b5520200b070403603030144103605105015a10041c02151509140c40d61a60f88a16003441d00314103445603400419601107240d41404000154007070075510f080050070410014181c040040c10501070307490076482e00c6440c01b200f8000d0712407901c0380f441550f0b00703284a02c01c1d543c0c1514040711600402403400c0e0f48a4007500801e410b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 763431852 1250 763430602 763430609
    0x161e060305040f0204020a021518162d09140105040e0d0f08070509060f09040b0d0c23100207031101030e15060a030f0f030810050609010c021306061e0207 68
    0x20395005003002c135004d01009510810058085003d4280740e103100034a480c0c0000d00400884424600c200d0042d91040d0520f010944000c4050303101c050100302d504031102100c5605e001c0804149030400b8101c82070941303403a0325441880d000b030070510301c4003404070b0b60943d241c100d55041d10140110307240c0c060507640700c0000d01212000b040c030304d000d54001c05110300304143c1e115482c1e06055140041c3c07100040d105400901c0840880c61002a845c1d2950426001c4e950341c6440584e401c014040d440ea0760b00b1f118070040e0240141040e84801900c05401c0c0103c21030720b090303001620a416030004540001d45403e480d0100343c400c544944203100c0345520920441c0009003620015081b0700c03c040301d00070551080a040aa070250400b100400855030305c08121141d18440c1d0300180d40d40215180c0074081e030a000340702c0b5800d56584001002541c0b103103800c49031182401d10342960002400e10016240800002c00d03640d0301842c0ca01c011802030380041001804154480c0c0341d00802903100001c9aa0304868007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 763433102 1250 763431852 763431863
    0xb061e03030d20040b070c080a051b01020321041205090a091d0d0f020601080c010c030e130c05181c03180e0c0a170621161e06030504 59
    0xc014440c14a0b400005620301041400ca10000c3c5030760700391903641064001619900b4000f4008040000c5024075100030300f094009813242c031101c0d40b1040d0301c844800c52095042c000076988030015078801d1081310f001090480305a00311482d40d140c02c01114108440440d400c41100c8241c034980b0b40107400ba80c801207001400c005009050400490250420801c040001210541400f1120a080c0b06155829405540e181c0c01a00d840100a183c00c0d0103900c090100e4100c0c00d41349a559911406540005416043c12200d1080c903a0109400e06500165001168900120910110343c400000e00640420340012500e00076a9010000002d4040d0005c40015100720200b00c0000d00030019403004003c60304083e0541c1c0d41d20180000d801c1011182e170040107200160f5400c0030741e0407920b0300c5c0c3d543c001c07081c004c0c2007460a0400700d100b44450300c500360f110208815101e82d4070001002600c000101c8004100c0c03203280c1c0d51411011602c152100006035502802000c620b0354401d1040c01d05c2a034018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 763434352 1250 763433102 763433107
    0x30c0305091c11042904090b042607030203030408031f0f08071a0403060c0c2a0603051e06041514040e0f030301030b060112050403020f060c04141314040b061e0303 72
    0x44d0035604c2c20b4402c02e4540c5801c66104c8047c84081060b120486116a020361614901c000c0305082c0b10140c0c0d801443c07402a000410b011140c04039034000280c03644113600c029070a070341e0f03141c46180c11189c102401d00c100c10181a440b020620000c450304013000ca07003540040b50b21242d12114221030304801c0c001e01300d40c4c201040c0010404107200b41c01901c54902c080c1005078017410180c8504a900c010112218440e09001141c2005a0a0a00c405004140d40d01e010052400d000f0210f10104660040c08684401503e000c200b25607650303449440e90381103038800405003d0780d644071091000c2041c4d803144c0c822442d0400c0b0714401c0d1004104c90803140d009038041c500c0c60382540d80711500c0c107802070011030400c81d41421203141d043d0140300f00f0740500c6c000e80040182d15030b680b0041d8904000208005c0d00c41c002440704002248102122201018003152400360b0f060b81c90b0b1800005005c404240e000449c0c0400500081c0029003e15070f01444069071b105420010300c41c545a80b8048900d105c50b09a03008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 763435602 1250 763434352 763434401
    0x903140a3f020f070c0905010509160203180307090c030e010501060f050403030c0303140c030a0b03030a020d05030a240911040e01050405040f2a0e0c07030c0305091c1104 75
    0x1540c2c010001801d48203940e506050b565121070310110000e401c070040c050344d2000140201d180402c038036544481c0e41c00021a03c0c0045090007506c0e40201d29220200e0140c032041d058250b03038144040400740601d031202f00008006207900801a202881030741e1202c2d4684800441c0b4181b0441262109500d20744030b5525044c916a02114a203d90600c00e42c100344d91064094030340654404818010301c1e5144240380c0340c0c14410b520108480a951909200b40c1c0300304547d030f107115000301d001402440c0300c2c1020394996941250031030242040f4543c1c0d90485401c0740c491141e000b00d4050135002e8842c58102000300240e108440070705481140510070740c80d40800c004104a1802d500b216520078032400e01c01278100070542d40e00c1080716590383c0010f2040c5058030450100e103840b51620b0001c101c012215009818107002662a5100f01c1d0009030411060148200a0500a07004c407503c802c40545405185a1400a001502004000c0490729014000141c140c1454140105240803a01d102940019101c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 763436852 1250 763435602 763435727
    0x303051e09062712061305010209040e0604150911060702130905031b07030b0628180e01020a0806041d03030a09060b220903140a 57
    0xc81491903504a01000406501d8035084060304955401808118203c0d900001407006603c4094210b8001c580b0b02120500000001030f9245c0c02c0642c0c0b80c8184d000c6609800e20501910a1500c019005070401030302c2000803c0c00988188541c2c0030f0400c2444500c0b88c01b00c2d45041c2c1c3c1e044000648400814083d0310b40320714000c00100b444520081040e040268083c0c41c0b4001c0e5440928140e510b80c20104441420b0100c4040c0f00c0e07002e02c2080c01911400d41969900c445d40380c009001c06d03001c0c0d00c09081c00d10900a000d08804641c103454010401c01550300e41d1010300c1040c0c02c6038486502030812041c03d500100500951b101c80005850b12102d035690300d1f00384801005100d2046090308142520340034500b0040c2b0040d8042e1607503440204032141c1c142030074401d03685c00c0580b03207004802d004800e42c01d4041030300d081032010101000100e1901d00b98102260881441e610100740e80c0800101d42c41c610360000c556403401c110000521041ca811101c1b6820071103103107200016400c0580d03011114021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 763438102 1250 763436852 763436887
    0x20607050c1c0519020f0d03060501080c0702040b0a0314010b2e09091d1b060d1a0901061d12030702010c060212181213050d06060305061609080304030305 68
    0xe07280b40180c02c041950500d6811034003404100f84c05600701a102e100800000c0c40010401070082c10148059868000000c100400003881201e28010102e078581c00c560725600052412200202030f904540d407a0305021140d50f113880c443d10f6496203842ea003151141010000005501ea079004000c944034540e02546200d031440980e804204000030b040420388420364480c9003810910040c100980300f0342e9220603403511001003000000308500550341301c0941e5580003100c1c40c0c82031074880418040c0d0710902c0038222135402d03400c8981c004203a100108040e51310012544210b140b0072603060000140c0414820504000100480c1035041000440055405040c100728118440c4a00514119460800f03990b240c50030786000c0540300220280c0c99007000b08100181202040c03d10240ca0220090445038402d02c0511506000b18001da03214024055a030380030400075900300d0260707003003483c0146041401110400f06003000c100125070214008500200381c80540b54540c0b101480c24074081da400c0f8428 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 763439352 1250 763438102 763438153
    0x3050c0d0b13060f0302011205090618030408030a0e041404050d051303050703030801030201080705040b04180e06040813081b060717070b04060e0318040b2106040201020607050c 78
    0x42070181e400345040b02c0034420300004000e10f50021903001c3c190b10004200d0032040504480403414801030009803400400d0072034106010350078606104148400c114114003403980409101c0c04041109032005410002848115a04540403c41d0f59107402042e15280705c143d0300136000fa48240410742c0c2d6103002d0b400400c502c002c8100002c00442d502d41d502e6150103c113810840004104400401c00c558102c3c60083d00181d8505116050909088001c4241c1c002d42c82110b1600b0303d031500c290312070f0640307030f004c600030102c40b40075600945810b090080003644a02c030b015116100d80c0c080002c0590b008100500302c5c5090001890a0340c0381002007056075040700e0750542d90310440c0345e06451100d01c0e0400900c68a8482e19005580f4541410b00c2030031142045940041504104a0028031403400c07582c41070700b581d01300d038000350140c407030004501200103a807600c1e0203640c3c42e821094648800042c2051241e4801d07800c44855a03a00c0c1d604079440d0041544c4020740e68802c01440408114043c04010b02 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 763440602 1250 763439352 763439359
    0xe190b1c2607030e06160c0308090418110d020103090602121012110405181c030b010f0e1002120705070312020102091f0e18040606060212041e05040e0303100603050c0d0b 75
    0x1881b4241c5170704048045c2070f4800c0701c24001c0015800450700f072034000d4003952825003c4003088040e560302c418130000303034007451144902010082841160302942c0440c0b042c5400290840d1a56200480720640c100c094410180802c031507000041c03095840110784507001d500c2800707418003804075002c0c400a02b1010704054280d01452048440f8a2030070401006280d040702d00c40c04080d05454000b42c00c603409542c1440c100002c42441c000c2180c0c0100b0b4010b0002010f603000403282101070310480c14004c07c0040034681141c00280007050150001b540002c1c0ea000780303025034514405000680c00c0340b0511051982098407070010752070750141803520b498041d4180c00d096000c3d4542400081c0c0461803500140c410520130000c1c40188001c500c81c5501410301e6000401c240601c041051140d40101d1080314003084c0c450825240d445000342a050040038054800d002e070300f0743c00c95515240d4108580f01203103050130001c00120036108c2d003d418040c04c203051441d450704600391081d00250001521440c0c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 763441852 1250 763440602 763440637
    0x130803010626010b1b0f16090b030303010f06050c150c07051203070917070504090b090f01062303010e03070303050f070309080403080d0b22060e190b1c2607030e06 72
    0x5080b0042c4203080c001400142c0387c40398a400c0c49811012a0070005040b8003a80c0103000606c0300b6401c3d410380e0070a0300c40ca42812174480b103081059520b03081b03411016102e0341440600b03010b2180c421102500c4107a00c2041910360400c1900040c1a0380e0004030b5010001400c807980800c45147d8403040d982941c80404d013030700d0217a40c40f10007280568942a00450f980d464400400074036580a028120072078884e60000d02c4001d2420070004064600358150ba4001d90308400250890703542540a11010f883ca00c055988455440c100038004240c1200c1000800400900081100c3d03c284500e942107540301c00f0080c2810701b0758aa540b002e4121036a195501070351108040880d0359191801c0c01198400011ba040c41ca20f9070302ca00e400d0f034410764044d840b6142c2c00c800f801851102c2060900482460f04400269982c12400040b8184018510304421440742000c51041c8043d4028040302d00403041c003103d5040c20034084aa03000d100307000c1e01500051220310401c129140c128000c081d0551041362205 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 763443102 1250 763441852 763441873
    0x181106040b0a0c1202011503080c030409060909110a0b04090203040804170709060b0a05030c0c1c0e04060b1c0c02120a02010b0a050909060708130803010626010b1b 72
    0x7500c0d070311403201000828100229402000104544000305240c248000d000c18001341c00d062005102c140001886d045010401401041040055070000c1c014007205020140d950040c24004246840081c0c6d4038079541303030b0301c4082400d2490b0708008451601d02e40354601450420454000d41000d0800c0718181000c0100040d2034100c0d50300d42c4c400d002c0e00c0c000350019915110086040340c0361070b071000c0d468982c00d0045c03040340c5d600403054a81c03001d403050303125990340740c41c817401810000201c0c2418008040d44141c081651b40c481814018040c082c1c40070000c0e00d07115050b00c41c1c18050000c1244119101c500d0103d203042141c8c005021134100d900440d00401c00506841d8115004490700000503035407800981402e00d80182400000c1c007007034071000c80b2418140307440da444201c000d205000f030201131004103040d141c013669070000c015003051419480b03503160b4a006143e2100700040310b80c2e10054810300004000140e03025412200000d910f01c2c40c10f90b601000090300389070f00d021030419010307460490 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 763444352 1250 763443102 763443119
    0x3120b0901060806180105030d0507020315011d01140d110f1521040305190513120201030b030c10031d100b090a0c0503070507061b020304060e0418110604 68
    0x38080d22441d2504a0540740078424048400c071907052804410100d07500401c510b46009c5903501d019038683c50700741d03610055070012a141060702280c1420700003522000060140d81084d4260007100161034600180e665161104800380e9181d1241ea84059007441071000640c2c00d4007049281d00c2c010f00a60004003000c800260302c02102c10210683c1070001600100300700c01f29505d140143d0400c110b800c682d040c541c500a00500580c07107040c08000c822241c10507464003c0040c1c400c4800c903990741c0c690040c1c60385417000c010701100c2c000b01d005c03d00b0400c00706031a10b000710305107640c0c0380b0142107801c0a17600018200e010701450f00d440070907080042005028440c00380007088000500f8500441d071061520103020103004001e103031202d500e03d440900100c02e81d002040fa504480b40b840c0640d120350329410000020040ca00c078052501d0705020000d0300064021001e4400c5480e01e460340004641150144415100c55a15459510f00126450b03400907140c885440c0d540100500258201034a91004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 763445602 1250 763444352 763444369
    0xf030e0f060109240b03070f09090612060e06150609060d0f0c0f021203010e190216050d05070f120c05070905061c0b070809031e12010911030403120b 66
    0x41e03102a500e0b602c3d0014079002001d003038940c1c807264443c04d4138540d00e0320328007034010300001c2c03c01e41c104102078442e43c0da218030800381c8030080d002c0c2007000c02c2210380e038404a07005000026002c90300641040f00c1800003840103c5d80c2803080b4501403a03200d01906030740c20018140d101c00c21099100005200c0302d90008090f2140181c00c1041c8200000d00b004150001392074000100580c00466006884440341000c00c0f00a581c110384400c54408441e031074043d0427402185082030b00e140380034400b10300e84013080b40a12003416007a0052050342c411f048072040440710303132081c08000703446040400b1031800019160f0140401140c01e43c0307408000e041c0d140c1c1c4d40c80c1c24543d00387d01585403962a8000e0001c64030b0411b9031410410318000001041407aa603980704074085000b0310401c1131041901c001082e02c141402200c002d1840f0942c855101c8001841005040d0402c42c440c100810340f550012581114620503120100c203210346032420751f5690340d011110000300d2050000c000b84c4800d441c0a0f90b843d00c0b00d0303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 763446852 1250 763445602 763445609
    0xe030709060f03140c01020d0f0306120503072f130b0a180b100f03181202160b07020306010324060e041e0224040807080607090f060f030e0f0601 64
    0xb101140c0601c1c5061100b074002c2807090044164011100c0958280e0b000240107034000d20900386900f000c0584a0260000c0260354081075000040030b00020402c5404002011882d01c540c079000310703001000301a450300c0308c10b0741000410507134004003203201440c04a0711030484c50418600032415040520200344910f206a209460034440195941c14400f031901510b2200c01c030545240b80400c0e1005030003846d4003552540341c0c0034141d55120780400403001c03400300d075403d41d00444481e04010320064025524003c0c0822824141e044181c04aa2035042c0400c48203595001001402319908680790405031a20024182012041c001c0c20b15265074498026200248400c0b1074002180c90141018280d0454000350340c540e0300c0c2603280460042c0d584120a140764401110308110b5126030b10440c45903880745400c965801e11546e00c0014940c540022854030649542e55414440b5980d0010240460601d001e110b0200300701d18209100180b10754415040d107011501100e140051019845003004020f81 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 763448102 1250 763446852 763446869
    0x110705030d05130e0c03150418050321090303040b180a081e07020d20060c070305070602060c0d09061137051206060705161a18010e03070906 62
    0x160309412807441d0489030b0081c26242c1301e00c95545414102252588001082c01800d0b800902d00c01085841d01c0e8443d508404800d050604540c031a1b080981d81c1e900408480d012444c444c80e01e20f4a06184c2e00241800342d03c58100950464443d41e40303441400030014030074020b04480e500074500e40c40c000c212000d0410301802d511a51a0441211240d10380c041c44488501c640040107000010307103c0029952400350450100240c0c601070400e1030300c0004a1440d072603030107040401c8038400c0e100042111800c03284904100c413003907942d42c80203980340d0404a81500316040284000f44d0161080c0e00849d2042c2d1060318001145074100501246540000f03085035040080d190700100c101030389540e0341d40c0f10f590401310b2108c86d01200e00f000f4202d1045c00039500c0f0100e281c0020503540e40320f5906035100d242c1e000003591003400c0184a01c0244488620440f4400c40b41c448001d056940c81c1340407604100342e4062082c0744004140300640b0802038030b610860b0140705003a000a6182407030b10450300a044400d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 763449352 1250 763448102 763448107
    0x120e1005041409040203100b03030d0204090b0f04050606030411060405040e010209090108010e0a020d080c01110715091e05070e01080c010210020405060304140709020301060809061302010f110705030d05 89
    0xd10b000481480a22590b009072400c105110160781c0008819841c1c4090080201d0500702480200381035008241441c1e00c6030340003050105d0308800c25040308902c0f28090f83c10b504185050001c1000365201aa02550000400c00110300801d0164a0701c0c2c0c40d5820151500c0c0c54243d0f918042401c6541d03004048801d40d5011845621a01d028649075004000000003800b988984c0981e140d143c59a444000380304288450030f040400c0948000d0b100301082400080140000b038060010742c90340315031412180000c8022030310100d42d1041c400d0040907604180c03500065071200542c1451110303007820648103482142d10000c0c22503c00304166001c1c1588070050800e48038050300280c82d0045c0b01c00c2c000d40203030044c04140b1258503a0350589a02c43d8200d00c2c138115586809c410349007404260b0b0024008503000100214916400501d6070340140c2c003160446445d81d580348084828004202c40003800910100100402d0920030303280380f4007900076081a201d550756280b00207480c002d688015880403c101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 763450602 1250 763449352 763449359
    0x30c021c0b10030507181b03060317040e0406090515180c0109080d03023402090c0306030a08030606210702010525030c0504120b0109060f0b07120e100504 68
    0x1080c0d126030001c1102d02c4040712582140d44154941605004401103c10406138040c1022150f4019885204034056040f0391049a80c000401030705850105844109400010801150706901110100e070303484180003106c2d4071966103101c040d0000d0002034480340700c0c440320001440b00880e4480d01440c0f403818101e02c84001c3c01c40c3c0c241000e4406001c1418801035040401460310003107800521500d03035150043e52150b1091600c40ca000442c184500c8400c401e6240f410b90600120000c40402d0007262080d5055944c51107074006032100305e42d6607805070428035400740083c2c5040d02440e08200c00818440c05e2040c50721401401d00004400c20140c107108a0a01c07495940a20a6071340107100d10044141407078220030240c00052480800d10f040544d2000c6040d007652299064034041c22400c0d2080508403910704010800540c01e01a2811451800c100001c0c90060b4924840c100d0f1071080089003001c489440b600328020702c8074042d90502c004451031390916500c885420b41c540e481c2d038803003503111802c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 763451852 1250 763450602 763450613
    0x4092009061806040e0a0c060203042112031e0e0303061c030f0804020a0b0a0224070c020d0f08040320040b060f280f080c030402011b030c021c 63
    0x1000d420540030b03124054401d9005903441c1c24407a842001a1000b041000d42c041c07541c1d00d0000060700c050810740d11500041049a4084014803c89407081900301030100900c00c60940340e0b246a00041c000941400701c0c4250030b0298114210a1048400955000228948c100d05a442451119130281c00c0001007050740d1410101041c40b0001520600d44004803a9901910b00c2140342081824010000c0005e07085590780d00d11034014004207801c25484180907880039580d840150103846000101c800420920b00060303013514411003c035542d112140e4455028809100000380003034400c5504003440c080803031001c0000344010340c40b41c50304540c1d462240494040380525042c1040c852401c1c0260781c0c116a94020540d50640380c00c8680c40d40c0c40b0606141e92083c00710309095414603108110045204a4000c103030f00300307080003d803144040d40c0d55044403041c0b64402254020b002c00d00001d80810803040700b14126a060384a400e1518081103070703070005140780030a400e007921a04240c002031810483d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 763453102 1250 763451852 763451869
    0x30a09060201051f062709061508160309050a05070b0a09090c09091a040905030a0909062603040306060e01031103011a010503090c060403060e0706050406020307020f040920 76
    0x9a00c090703034080d01144407561044241a02c0b84804128240c2040510b61b8001e240c8842244460300140c1903003641c581400d009021280b2543c0e61414158040c88070550080c0280743c800c8500c4410b180d8011442182a8001e140d054011b80b00c61050703000441c0080c100308940c0d005080040482c94813480511001041841150429070060b070804203140c500c640c20040700380550782c0500011500c000c1042c1c0509191100a50b41540241400c44600030300c400440144003403d184c1e42e9545049072611b8148080c1c0b0000d1140500c1c490b40c01140c10104411000a810100e402409a92525603a500d619040e600184c001c5410151040010000c00080c081c2c082d282da10b058000340320700340001402464004050740118144000007001a1211030140885400440f005102d5034485850f0b0034204001c200c1c0c455203041c148181240850b03502d00680c1914115402070740103514100055081c0440c1120003054243c01c00c1c2c54011140024103101007501007000014040a03100002c50208003051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 763454352 1250 763453102 763453111
    0x10501170c011d0904020d051f1505030714010c1703091501140909190311010e0a0c0315020d050112060515011403060d0807031701050907052703030a0906020105 71
    0x4100a500030361400840032040310711000721151249540c5e0343c00412040356509200900074020b0101c40248100c4011107007143d002c03007003410020b503401d203145400c0340000c07401150b034142d00445d801c004992410181c1035400d481803414824880069403006c034400c0413081281900c110120800101e003008100c015606107001c0e60038400e55150030042406442250b06081c0038940d048000785904a0401044c040140944d1401031030361101d040040c0010007540d070901c5a0350030300b200500c1c841c1d80012021800f94205881b2013206180d9a1800d81c5401808170351403600307400b0300c007468003030311648180c5001308007400c0694014003a505d07010341120300081094600388141d080702c0001d664006080f80c803801100c00303050f03500c4d180c071000604012080c17100100300b0500016602c041680c0304019031244601402c0d50f14041c1d813500d04102551000700c80d07940000d102841218010300303010303012490314403a001c480b8041c11145030110f0700b540d020b4404000800c0c100e00b42000901d909114841e0700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 763455602 1250 763454352 763454357
    0x3240a03082110080f01020f0316020f030309070617070e062107080f180c1e0a0b09031605030d050a0c050d080711030304050c0f220f0b010c0b01170f010501170c01 72
    0x4004085854023140d00028045c12549248885206030481c0200b054515550400c011130340c0300c2c500000380c00e968041c140120800601018498014501e107500c0e40382c09801c5944a12aa0b8a4018180b11b25508210550449036801100c032018510007080054040d01580d5220326407841c00c401c608001d8035002e00b4503001030108158540380c0c6600403030b40c031800050440d40c042d120050312006503039038184d400a036940441c407800001000b500c00742c001e101980c3c00b6400e0302c10350303201c480002c0400c04040c841c1c650147c201e024007600891003500101070b142600d0800100c0d1350188e40324a0b15007041c1c820b01d0750100d0185000d21817550780103009000c54041c2c0f01c004610703600d05996015140c000104e201c40c094940c103102da00385a91441c5070600340303030800c401591032164001c1c00000640b01200e0901502ca2410b10102090f51007080149a0207400c11400d041d5a4030300580e044818500500e0300c011809840003805240c07500303005030750007011780c00c6103804c0110700114110304054000601390305 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 763456852 1250 763455602 763455607
    0x6110a1403060307030c090e010b0111031c0e1005250c080304110916120c0c0b060604080d03020702030123041e0f050303240a03082110080f0102 64
    0x14540d034050340341903250529101058803610394030b0110b0300e030525a401c02404100078030004140c59000e0391140c001816001c0c028442e900c00312006440c0344481e402014190b40040001c43c1d15121024050350380818000c00001d000c09190a40c1810f14156054100f141910380041c4001c2070010b030000720042c001912021010040d0b902c0203014000c03003907030091540101200003418030407840c81d00d00034900040d1200d0858600740d0002c0c1086001c10328000701042c0f1029101c06000258410004a9086034403119032191136925240b1030030100414460340000204004903c0f81010f011040a0000c1c545015031a0035881c41018203480841c032110150384450242005103510740b803d040d410540000f0003000c0d0058940e26500700c5d1485c41c00c041c03c0740200c1c01e2580d0401c000003008521892030340c1c0340c000d080901501048110345401c2401603019a14580c1400401e034950300074080a004040c0c407014116a40b81d840365001802c031041c3d0014180c4400402c060748007442001803035801c01c4001c52 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 763458102 1250 763456852 763456867
    0xa0503161704030f0935100905070608150108061c02130b1e22110f040905070e060a140409090803040b011d0a0c021006031401061a040920070309030611 67
    0x300c00b07072801959040c8007946e030007080030440c10710072221010307001c004c21f00070390a05081c0203030394580d61702c90840000d02020000c6c5000252424400d030b943c0c0169034035405500e550701002520106104c0c0d00300c01d90b14550000c00142e48103024650f03440844207012541c0c0b141d01d82041407001c1c6504041400100d403160a07000d0b5030780e0074083e150800c07120943c04542103000741d1100050401c1078842c0c0b01d03054000380055224400030003901c112821000103002694a807401210504414000705400c0301c0144030151811b8020104070300c01900c4001c080e810036607245601000d40b4081c0f0801e035034036540001400309005944070014050481400c0542460140360b0b0b40b16a039010003800a1b140d1699840d100039078074428024605105501c03001440b2054917401c007107080e00b644900340803040d07103002d000040514215aa50700009101000d40c1e081c1440d20080a01030000342c6407616840d1100e154002c100704106000d0655907010b5a141400706041d85455421540c1c0a42c01c9103402006120a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 763459352 1250 763458102 763458149
    0x60a062318151c0f2907170a0e07060f1202030a2a140a050f13150c020901030605130210020f070b040308072607060912050a0503161704030f09 63
    0x7a134000d91150800315a01c595400020907404c0f04c01c004221303420b03443c06002c9811790082d036a140c0001d019901d42c06e9604e901c0760402c100e03040e46814003141d40101d84204000c41c05648100459210b40c101030300c8050780241207604a0b07004845603e081a0f56400f40c0c0c00c1130b00810041d80c011121422620820100703610050190701c801240c5e40300a460001c2c812130414843d000b954248407007841001e440701e062402d91a400003440c040d0884241c660703d0719400c030703e11900000d282c60707801406024903642541c079800e000e010000c20325103212111812040058541d160707154011520781e4050401c1c6607040c1801030420045078800d8014140a01c0f0501c0440c1400d0211151154840c2c3e480e00b0480540000355820380e840148042440e20115098041c08050740010340481d1040c0707042441c1e42a2168103039028054440c50f21700007030090001030301c0e400e580030340380700d1418040c1844101440699060354000c1c40407034044000400080b035008040c0d82000a00020703046a0300341c2c8103543c0c00300d90300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 763460602 1250 763459352 763459373
    0xd0f0510060819020d020d0b04060506011b0605062404030b0112020609040e160807080111160326240a06120c05040503030a0809060a062318151c 64
    0x401c040b11000f0881c03c421542c0b0701c07000d04040c40d409000e500c200c01c654140702d41c052404a8041d00c14500340070000d02250f118140b500000c00c2c00c00e10503144080c81c4d0303c8900003008000d06140d007200c424400002206403180c102d01e418080c803485103030380d14114500b4400000d81a400800e0350081504014010381da9202502c501d800d0a60b00010031a044417074151a1a00e988001c4518285503d00401d10b08000300382103090320720074402030000080300c08070b040c81441424402c841d45011001c90b000041e1042101240d541c1d003407980c60100c4030014241d2009048152604011041000a80c055040034041710464501044032030122580c5040d0000d4000f1081c5041800d03203903540c1001d0000c0c9405102903030b001e0600034085030340311103081d400079103030348400d41d01c20826110b0200013455000d0103020703100940c1c0f403812680d01311400000901d070440300300f40780c0e031944695500e05011032020340c5100988558006185501001808001d02c503c0c16a402000d41d0a480c03c0c03103c1d000800d08514a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 763461852 1250 763460602 763460623
    0x601060206040b0a0f091118060f0d08040b0a0917210903190c060e06030420011e09031103030705031c0e030d020301050103060902030906130606050d0f05100608 71
    0xa00c0f05640d1120380d0302d402020016040d041d1a031600c0b443e201403060b0702e00048134801042e1080114030701e980004800c00842102c0c40380c1d1015403184021880d04100040c0300d401d910070300d1154201900e800b00304840c0d420603021080000e040883c00c00c224515030606080c43d4180314058101c41c2c0d1003940031030301020030a0040b84000340c00603c00354183c40400c1806920000ca07d4144d0401d01d11b03150000310020948030b490300081c3c025200140c1ca10b80a41264021640207490203100506089000040716060841c1ea040c8000c00e800580c60850b64603107030380466034a03921140214158a0914014081ca40b80c03070b03010741d000703000704400110300104032203042e405030401040a508103495a0041c050400503c2c6031800049503078442d0b00714940265050300c00980341440300d6a240c10041040707000840f5880305582c00318001c41c05d4110768030003003c4d80c1401000c006c601d10340c403030000c1000c6e40f18480c42211102913102d0758900b0f02005010000000d040b10205003c2180303040c010a5807800544c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 763463102 1250 763461852 763461863
    0x3040209071b06051e01060f1b0204020309010f0e010e1e03040b0a05042d091a041a1e011e021005070504051305040201270b0304080912060106020604 66
    0x400d0800303004080700d0b400b9040804401050701428540800544001c5d5501d41c0e00c20642680e080c119444da01c05c3c181a60026500d48048c440c2e442d40440d24210395820010044d4484041d640146e21a4001180705041a50002c683d0b0070728000f03200200d41d0480c50310411139140c0884c2d0b40300114049809110000a48501e05100e02008400c1c1e05620465005410509000803181c0405421002074000c40d9a5142001c1380c1c0031810610380004030103401c0e19800c44810170002d00c04c4a05a52100f00ca00365148400d5440d040f404020038226403034048a81e11602c1103030382a03011464480c840d04003d4505c0c1d620542b05031007160010b000d10740c0f80e00710100c0041e13819425903049031003040300e1949801e05400600c0b1070308100801408507807050007428010240b5071400c00d1507031840d0048030701456060f5500000c030544030050808040011101803c04194040c0000d007000e01704000e540030f030340a581c44583e2541c892041240349c644c10300600e1119004200100810740c0c0119460794400c1d00103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 763464352 1250 763463102 763463119
    0x10603111e0d05010c1706010c031209020307030c05040b1503060d0807050105070816080403090902031807090203100f0305070302060307110d0c2904080705030918060f04050c030402 80
    0x20340840309180618000d150300000700c401a40b05122054010340380d24503c03a01c03a00580212500c0c9039201501c12540d00b8042400c440417100080e110300104e0040c0c0c0202c0c2000214002280c0c002030800b000b40e80151100e2005030310500c19840d15215254401c44c3c01c035140c10210418940b014102d0000600491013041c42111800a20250030708030f421165212000b08050720f0040400341210800340e403240044440700c000d100071315019044890086400d80c848405240c9040d80c4030b40a94002081d503451805400d5002210b0101084210080c02031144050380301d290001100c145140f580c4d0202100c0d40c4106800c2020840c0400d40c0010f403901503481560360b5036400d03800d070703044603c0500d200d0b000d00c50284001c40465003c0780714142d003403003440e03a440f0122014001c0702c0c1323a40040c2001424422410003040008030b404e07000781551071141c0d00b501e00305040c2c1e00001d00701161034468950080b040204100461500800307200d000c000c00c40c2c0030000313410a0300c03800c0024000140b000f07000e80f540c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 763465602 1250 763464352 763464379
    0x30210030605060d140109050f040b100902040609170d0f050703090b040e0702010b2b06111218030a080406090c0506030117100b011b060204320301060311 68
    0x207a0072000107820003901c20355503450540f502d8402044940d400340000040000003051000d01c40c06100e009113113580d4036901c0c0d03480d02c0e2500010398101400360146418210700015041d0864009000246015250548030170b2500401c103802065003018415950016080041d1a94202100c2c11225035039280080c0c5501003854181c0e10b02003e03422028103250040350010b00d101c015908148074072041c1d4028401e030241d50050120320303407483d803569071a0b10006901e210009181d448a000d25800344401040d50308600c040800d00d03510071b41c4080a42003d8608014280d8030a800845d0780d00107400045107003c600e400004c0100401410080c9481d4580100b01c05002e071841c0c10402611000340442d030f407960740f0b0a5a0070000010319031120a8080d00a405001c2691072203180103560046c2c60b081c4a0510003c403446107221541c008485659088c803002c40c44016840201c4186e214454004c24a00b06100c00031584920015020f4483c0e8148682400021949400402c100d40c05440900403601c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 763466852 1250 763465602 763465607
    0xa0f060807050c030d0b131407030b0613060206040317010308041a1c1a040b2b0501150608010e15210105150405060a0305120904110c010606090816030210 68
    0x40d000c19038121300c0f0206003138648085075401030706030020445000c10f030800652a400150351840400c8100c6000403800222014000e801c01da014400c020001440c2402d5644c9510b0900d03240d4100400591000d001c2004040d04151042c1c50594200e200300303a190b01d03581d52240c81d8442c5025450841c401c121500030103009c11003d55000d9000c800c1c01903074810503582c8500040648010044038000c0703010f10883c044c10288202d540c00039019100c40502964504d52607100b5401d030482940304001100701b0310200380300f0300c1211281d8140c140130405a078a0000300a00c50030060704000c900e81041c43c1030020038502c0c03040300d0080e0202990307582641c0c0c1402e40c1c200b1410b20b4000c4c0c40e03e0f0300d508000c10403448851030300107624944c100712010401a100c04090000c000d540e400000c0407903000c020000c5001c0c0940d00501b0310f801d0020030128011030074800c928040d42124a442d900f0740c1d110760040c05015085a2805c000d40780d40b8000300f1140300b00b002107420740c0e402440081c0c011540c101c09007803d02d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 763468102 1250 763466852 763466857
    0xe04050f010f0b0f071b050904050d091d0109180b090106050405370e100501050a090509030a05090f061c0e010e0309010518060304050d09060c0b0103150b0306070509030c0a0f06080705 81
    0x1c0048c00b0002e1480c081c104161600c0100781c030180081c845080209101c204c4414001d1020701640042900da820009904010814465603198420240110000113502c564050380320713510800000c12690702e04404c7c402981c85c058140d00c03031344100e080e03841d8440015102881800079510008400300b005402c0f035038000d00a45110202a026215100184602a4110504803034013690b980e55825070310990780741114030599042c09142c00030032003091117500c5040500a2808000c15100340411003000140990b03001458103005244270216039140010307103108090000c41400020700c03001180407800d6841388195120340d41403240c003040320810210400320300032140c00064040c0380c0c0ca041c00e0030815640d004010303032400020184480810028030544520203070075840842c450103030b400d41c0d88418100c0c0007112040750050f60341001c01071507038003082400e014410907155140d0360181c080a26040c2820010610301400c040350702000100b000300051012500140ba0051003525010b204030344c1403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 763469352 1250 763468102 763468109
    0xa030504020121060608010920071a0406050402093108040503061f06020d0203030714070204111305030f100903180308270f100e04050f010f0b0f071b 66
    0x82d81a504001c3d107804003a84064242c40150b12079aa05a0361980020140e540039485081900301c4061400300c0c003c0c0e49005440f41920030150291860320780008026606001c82c1c055880da1345510500c0f0a43c14203040513504030f000b103240b240c4481004032689040f04000350810100700d0400030748106004110303007502d002d04001003e6580318244181c1811a81d201034181c44400460440002249400004c1000001070180c0142d0b0465031501800c1e0307019000d07003102c459076a90402c00300300140c1c0c8921444517180c40d43c1700034507101c0c03080781a40203001e4010303000359009034007038030055254500010302d19200050f011b00204134410a8902180d242e400c00e00080d01d400404200401008080f8004d0242040c0c0000222094001c42c00f082c110304c0c8800200d00e801041c1c81c080c0d00c107103040456036805144d2150600320103c0f2071800206044035402c865105403503600c00014030180d0042d04048000380ba070410000c1c01d000c0d036842a0313003041c80740c280000c1202e4241c1c1082c0051502c05038812006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 763470602 1250 763469352 763469387
    0x402070203190b060607030c11121507030b1012050402030f06090d030b1e01030e120f132903060a0317030f160207090b0a080102041220060a0305040201 67
    0x8103404036420072002d03211200442d425800400003400c4c40c00d01c0800d0300c2c01c1e107805031f5800c5941c00154485001c00d55042e60003e03002042401380120007c010843c0050211110855042d545130500c1d0040441d03105407455032040c444140c840c8c061750351240c0c00145031300c03a6440014032501d40c1d20000b0700e0000d03075a40140b020701034001044560500482c0d0501800425103050010584200c108046610000010390a62040b2103481110b5482948882110712030340d012500c90696606001905800901c80000c4003140000c030b000c21420650f040200800c800d03100c6211000350745617105640e952004808501110200000d6603690340e0040c040011500104210144155600e80b00382d150700c03c0b141c0c0200c0c4030190000c03803005908244401e020f008542d000d00401070800380454090581c10310340ca940542c002030302052070502840200010b000d00c000c1d488040500d4039201a0545001c121043c02110945040d200c5464000840b07001800038980042ca65483d440160f41d950300a1242030311 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 763471852 1250 763470602 763470613
    0xf03020c1e1c0206040618020616030c0b130611030f0106050f0d060611010c0e060f1303021906020601081204150c2a090b0a060f0512040b01090c0c020d030503060402070203 76
    0x41c03143c0100325140290300401c000d1003803207248445041e5031f00003070314001c1d040b010400004144003210060461081d20a240c40344001295032645c0c40c2c03110050701c0d031701c4000030f80802d940c040022070300c42c8440650b1041a0fa60447c904549030391660241441131409005000070403c4d80f018140d0304680030407180b0390742007024680b0303072074001d00d40d007e0b4103083e0740300790b207000061081d845c044c0c0c051192040d4002d210510b0520b40c42c000307c01c41d4002d11703400600548115004001640c4900a2014044aa0062280a80c5810340003440c11906034820400d503003000d040c1c4400341840a044074150343d4a42c0c0c140c1c500500382c2e0012100c03109890009803000c18408179481505031200ca852301451032540c0f1000009480f014440100c0d88450025680889540d13005c0200d103000e031014070200c0b00542429800d001400d01c89060a1f8401c980441d0707881c0c0c104d0b0041c80405181c0c41080c800b40746c0c42c504419640d42e507501040e00254415400340500c00b000c0f00046240da50354045584140d030181c01e40c1c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 763473102 1250 763471852 763471903
    0x50d031206080105011406120406150803070501022d040618090207050d1e0512040f02330406121e09080403020310110f03061302190f03020c1e 63
    0xd00070f21086c060360160400001010030b0030f1406c01c00b99041600071f2004da40581c1c80f95a03c6a00030600080396031603600c05400c0028042405001404445020b4000582d039a01d40c2d4004009840d082c882c07002c141020f8400d103603204158401510160345590a24070341309011f904035840d04544c0d82e8801c0c8202400050480304118000c100140c1086903034844107c0000400c5003035444001841040c00004c20a1240721240024428100e8005015030383c4c1d0007013003202ea004103411f085008000b0425550b94880d403060101000305020704044042000c905040c14000020b00c1c001070741154221554030b9200d24031a0340d8410300400c161094000003040041498078010b8010f0304603200503403090182c4640e168020040380030f4000728031a100003030703842c1540c1d104000c1c0fa260000b4000903001800781c100181c04200d544010100440c0310030320070310705e604040401000000e080c021300042600500640703258540010f0314210782556078002c80484510380001c203260044100d480d1000b80c0c5a0954103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 763474352 1250 763473102 763473119
    0x2030c0a0303020f15070c0305183309090403050705010e160f05040507020c0909030d1a03010b040c08180a02040516080a02090312030c1201060509012601050d031206 73
    0x8811031000201500c90f03409550094881c0e540d006c0310b40318049900424044006441030000f4640c4403040c2e02d1210100900601142c00b40c201e403030031024006034501240740700d405039401d11013000c0445400b0502d000a818086100e10901038001820312034041039000410000307401c8031000015040c00c43e01101007400001c03e140c401c80c42916950700c50a100440c1c00d041c94000d5070310406054008010b80c040300e10134402c0d8050002d05104042c001885454041c8001d406105001c0303601c012a800e201c94848201821a1810708185104515021040c115241c020003003a80c004d2412070742106000f100540036080882c8000000d40c400d20304020400540e0100d6818100303004982d603001d91595a01403224101c1c4607142041e41c0c1603215480401d000400c0340000d50788204641c05503170820107c89008880d08200307800481c0464004903207202c403568441e0803800b45400c004105d4085218101c4c0510004d001800360034083d6182c01c1180060500900a000b40007001c88030402401d43e80b000321 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 763475602 1250 763474352 763474363
    0x111e0901030b090105090619082506080f0411010905040504050106090c050c150a240306050604110f0f070507060306030201080c0a1b051c051b031306080402030c0a030302 75
    0x6503011902d4680c022510381080c10310355060b81d402a03d1002161078440802c019280c0c0000c0110400800703100c045000c010600c008000c141c5541705424138650050b1468610f1500ca81000c020000c01c48200810704259040c15074015030441c0201c00a80c40d040d0040b604030b50507400281d000340c1060700b40820040705601c084e007180d4444c1c1082040c40c0c1d8108080701e0034401d40b145030b1a190700c114100a440b50340806d403550886460722000405030301c44041c800e059903136003640c0841200520420002d00c9024010725178441d00071a0f003040200c8103102c040c0e40c03d00840d4204404046d0101e80c2507030304060309044850070760b001801c6410705540c1c1c210040c09031110340400c90000380c900012a45818810040d165017042c00d40f0381206008111058804240581d50180c07002e10540541249040c180c02000c5642840c9688080e82d41c032032003028411030300010751340c42d041c0d40c0100132120f9044101501401030751000d1610700c00c2a2a0b80c00000c0c03030710849181c1c0f9a031111610800000309900042e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 763476852 1250 763475602 763475617
    0x18060903260a050c190b0a050709051e0402280f0509060304140724090b18150c071203020f010b100c03020307080c030306011e020d03111e 61
    0x100c8110031680741c000384200030100400c100c00352040c41504511030080d005400c405a041d0100c4460b60b00d01400400c000c50101815a0300055800c18884583c680e40034040c2d000e00e082c1400140e4614144c0820655982000603c244100d8081c207108a6a5942c049403200003440204540c40e00c0283c0c10450790700d4094110381c000c140b01e44600b6401d00d00420551b145c5c190002d10a03030039076440d901c544e4404195a81802c890740243c1c4408240c0b1070076441100f41c0c03004134075044900b880500a01900b60861500a10742580c03050105000c0d1084112100e0701e042d40c00c1d40e810003c114254000410380c000c030b00010005028a51011030140d00100801c4981c1d0301a5080310b00c0d91503002c060508072070012207199007003010a030140386080d01401840496030303c6032045034501a0540c41e0360300c0a4102036007454894000005020740c83d80d11960b448040c05142e004110300c2171010034040d580e04408000384041c991034240210a600c0315400750751114503901900301010010407a0200154001c18 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 763478102 1250 763476852 763476863
    0xb0a090e0a05070c060f021e0c011503200316030b1b07150216290601090b032202330702010c06020f041a0c01062102040c18060903 58
    0x4000780d01d908403070040070700071482525005440c803090340381c010282c2111203500000d2134007002080540044076032a2404848513000980e10b444c0d40c00c1800342560000c2c0c40c00340403a50508001d1000c5914540404074110340300500b28850115071003c2400c0c410000103c981550002c0340010a202c07901c1d0000c1d1103003404102107000c9042c031514454036401211000380400030300441c1010104080d600822503c0302c0c0c80c01244050380240c3d41c011101c981c00140f80000c6a4981f03805800003140302c20940c1160f02401c01e019458181301003a002ea010043c44200602d0000344180c3e444455050a00349280d0068607100c14172030200810381850100c55072144400e10110807400003a0048010f41d49003907816920f0140208042d256400603400c5440e96082d450002c12000070030010001501540c03007004520607440b0303050303040f08a00312486540b1038074007500d0a10341d07100310808042d18410f071580e0407a40010200c4084e102268200c10260303002c40f80308860a004a5040c4c4c0103800002183e1161 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 763479352 1250 763478102 763478129
    0x6020a050115080309010c06021308070906150518130c081603110414061204051b0603010510051b03030c0d1d12031305060411100806280b0a09 63
    0x540204034007110300c2103d0681e0024400d62005610075110810540d00421015041140d443c50345042c0000030750000000c0c1d0701105040107004071600803074004000c7c1104036400c403420240c000c0c2141c40784843e648521605080c0280c113580c0c03030707018501c2a15445503081000109119015142c0da10a03a008440fa00314542889200b91113030003007480c103401c81503299081030310f070448c13041e04280922551680503409201c90240704004c264110301c250b0182000f44903880b00c0428000078038003101840e0740a00c0e1300f0401030041c2d0720703020744004008041c3d2924980e075920842c840d540c4c58103005000f050b02d0100000388400102c800b0040c00801d0251901000302e8001c20701c00820b15042c10030416007a8115001e040c0c010705a54000c0c41d4059002c1810362036415483d80c84a0501e1002c45003101e444104d51440381d031a00740025a0021340d81e041c1894009414840700140c0802079010b145c1c0103c2403060b01043c0c103070310070241d104001d0070000c0e042c680360b450906010300465100c0c0901100d01c4d043c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 763480602 1250 763479352 763479371
    0x706060608100302060a0e010302041208090a0905010f060e040b03010c030b0f121216060903051b0c1f0318050a021005030c07080d1404030e030c010309080306060d1506020a0501 78
    0x155200c80202c3c1da00401e440e180c4058400103580444040100d141896803c3c00002030003840364404000e610720986542c0d603101050400c012016130a0780220401500c1c0000502002003d00305d104180c500c86d0070414100302d0301a0014010701466180d0640650078006180c50300e40d09604031540040c1c040721150000703000c203414003d044040300124802c039840130303405080d0003060740c004150103480c8800c91b0413a00c81d503403100b0040c1c13403d0030812400101e0009a160041c4500c404524440ca481d50280c900030344014006000403e0ba18a40309004402c0d43c1c00c0140c16020b51320101001200c2d40e92441c000c050b42c204140c80c0c409000040c0d00680414400c4c840300740c440c02c1202d12403036070b8001d01ca04107010341e1244a00e03038009004140f1081d0781c80e2a11500721180501c0d0500c5140310ba614800d11503100000c0c1030400003004081414181002e012000040480054035400030741525543c2e1140c4401c4104000b400c442010203020402c030070720110b82c041d0f0110360611400c0c0503000a200c00c2c881c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 763481852 1250 763480602 763480621
    0x70602010b010504050f030f070f090b04020a0c02010f05090310020306031e06071b080f0c010b03060105131e0204031a091f0207030905040c030e101107140a06020706060608 76
    0x84010900340022001c01041c4201c6c0341c142d442c48841800a0229005101c00890b024a003151a0f0800c601b1403a90717038820040c4ca2450b01603060010001d032400c2d81002c684010207051740d07903041e600a05000d010b59401d400b491007074050301c0c400203004045900028480c04904001c2d4010754006010340a180300c40102054071003241c41c0340112410060565507128101251440d00c20041c1005982c1c0c07400d8100c000c651a0000f419183c4691100181d071a468981c806007182c500101700d034040e400503401048141c0e40e000c03440c0d6a441000002007072140c0307100c10080d0700a0b40b0850480c00c25102090110510461607010303031103410403032800400da803200018596100c692560b03025020511240300b14441e400da40250034210322a081513000c03103440e080024250b481d842c0308200043d17a40c9450402c580c200703308010a4495a60042000e030200c105004410320035960042c0c000355211000201c8181c04124904415400100440d00ca850710f24014001d0000c901c40c0300d00281c0c560000c91011355 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 763483102 1250 763481852 763481861
    0xc1e0d171c02250305070c14103b040e071802070b0a180b010803190e0f040e030f0d09020a050105030610110a020d05150f07090e04080f070b01060207060201 69
    0x12890080e12507194143c0280102003072080ca030803020040c080c0034400005141e4582c12014001c800d07003904076905001c051018408e20005070000b00b181032407071008607601104400c04c00c0301064005020a41920103080c40c8600141401500700c0d1030501c521040e1007000c500c46080e00c0f15040324015841150000406034010b500d03019045061580c0868030f142501d6010b4a10312041c50f014041c036100079141cad070840f04400da110098640001035400241c08006445112241e0300e13003007503000f000700c010200d4448a4541c00a90180e40d40340340f034269080c01041031310106000e010196a0b11351045205002802d04440224050701c240c540110380303507018030b0559100714400b030110700c004981d00d85d08a03800042da80c042091809180c80031b4026803035203080f0010386405880107100d4400d5420364050a800b004022000e0010403130107011304540e0100d0804110303006007450140d43d40729800c1601c003074070480081340001d800019115003002020303e8058104c541e15025030325004d07604c9105074280ca = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 763484352 1250 763483102 763483117
    0xc180b0a0e0334030b04060b0108130f2303030c040f050a0b0a030b12070b132103030509072414130e0a0b120f06090c1e0d171c02 57
    0xc0c2d03c0100c0300101c0b041d0740f65907034003812042040b50300c400d60380b615856184001542c050358a40d40721103900c080341d41c00a40c1c8035041642c01c0001200744010f901c2d000034174404540700521f00411300b055407a080c0b140d041455081030403101038999a00300381c030503ca5207a009204000000c1c82d020301c0002d00340380544d1280100c540d00c0703d006150034146540bc90062110001c81036101c080b5460980c10039000304610b0001e0700d5050385895452010702c2c00040b20350390981c083d40308040c0c5213000c0030000d8800c0002c8000164107007008a015102d1501d40e40c04c00d49150000d03101014441e0141c40390aa4110340705003d40071f10f8540c0811505084032480c114881c1c0e80720400006024401041000702010300a42c0c004004400091230000c5540000c802d1140c994292700035500c01080c610b1544002d01119800801c0c1e580106490304c0c241e40854290000f41d10b01c0101d4245112403060551112240b1054866004200da44100e01f42110500103412600c240391111440024203408201c1c984201c8804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 763485602 1250 763484352 763484383
    0x13110a09060f17070807031b120608030304170a2a0201030f0c0504050f01110102030a090c08030c19032102040603061a0403020411041d010302090601020d080a0c180b0a0e03 76
    0x7039034556500303031754038030380540302c0e10400da070301d05041d8403003003107003180b08d80d5441107070384052001e8030b500019400d44110342c118003041d0f0402c000b07000020b41031040121990040400641c1c40d00e82816041c1d0301a107254881d131004402c11000c10300c10040c0080000c0b05c1c82c0c800d88003000100300440c4a04121001c2c024180045001000203100344c0c03816503c05540000c05150401b80c26050200e821f082e60000d40701c0341030b0076880b1041c04c0100300450b023032a800b6020750001035040200700811180d9451070540014801894541c4c50030a0503c5203003112420803c02200380441541c17610440b00a51081c4203800001e0f240c0300000c141100081120303030a42c04580d04039800c182c155000c000042c001c21a101d4070b040390810000500070745403120307644490039070a0703407030031a602d54018010303400d400815413411034015201003181c0e90b41150780c0035001008440001200210f2840980c1c1a0900850301030181e61082c40004507800c08000a000d42e058a640e0102c1d41000360062554035003038800701054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 763486852 1250 763485602 763485647
    0xf100513110d0b03010c0f050405060f190f0905030a11151308010606120203070516060b03010e010203010807050607030f0f1407030c02030c09010b04030213110a09060f 74
    0x940c50301040d018954a03400c000000c0024148035040c049900900307900700e400b6215202c41543d45428803c002d000d4000f41050440784680d40802007440c0b1860284d00e21425002c200402026050025521414007414880740c54010f40ba0000d0001030103c03100200042281d4030209050502242d04200c9907401451050031850150070400b14101c86c8405103903402c0305011043d9154461030500300108036240c0001041810010700034648091507160500f007900400502c15525403080c00c5590209213841d00a9a040d403074a000405041d0401040d03905600300095142d5042c0190b00841c1210541821150929074413020b01269014102c40a0302140c1d0325102903c1c4640500321249a02c400c9103011465240c0007080705e0a543c100d520190002110044c400e011800e0404c48600e156104443c103030120340c0740442034012446140802030107641c0c8001a0b000104158101b96013980340c9070852511503c030310100404c506070394401e03100025030079250020030500400e920070f4207200c510f80811 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 763488102 1250 763486852 763486859
    0x50a060c141504210201060609050f030c060423030705010e011107180504120c080a0c050a0b010803190c0519022d030f0f0a030e010909050708040b0f10 67
    0x1500701c00c8540700100a8041c0380840090140c102d421035106500c138641001110242d0344540c4103602e1920b103c1c40542e071625000384405500b001080c02110002c036a14012000e01d100400c5c180f482d44181603400010100780401c00d5a800c100188850103040e44010b5601200700416644103180d1291b2400700304074425441e42c6501c40e0329812040c0c07034941d085824440d5038962848200d030a038001c40c40100da403042403208020381500d080380b903c40513243c24803210a0303588505006c0e206181940d0248090320401008214040c4605051640c001e040d07107045603561109651680d00c090f510170030603002050520100c501503065508803c1c0c00500602ca0070400c03104c0504001d11021099910000c241d80721400340c6004448880d409130001c04c1103821809040c203051401411620001952708842d22005090350002078030400c50750141b4240203031202200050b1050704c0c00c0d400020a03203060504100b0004d41006c015400359100e803145001c16a42d54040044600040e0794000040c0c400c044100f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 763489208 1106 763488102 763488113
    0xe120f07051f090614090715030b030a1b0614030606031803160309140d0b0604060b0705030403050d0921150612150603080a08090106170313050a060c 66
    0x10101410120140c0341c071f608060207009a4490301d064003c520911981004280c403c016094980c0342070750307052840705401800f148004014510740002a01c40c854001c04a03000c0d41c4099242c1162947d404101d060350010706241d4a04960f14111310010000384014080500041652001d54042e071801070700305407040d0b00940080113400c3e0030341d01c251103565401d42c1c0385610040404583e030341c510000340140066000b200206c040418410201b007000030080080e40c1c00784040701c0d0001c50300b01d01101c1c511918059817441d1104100d81d004800040070180d079920b44540b00403074488104441030421a1a19403180302d0701c1810714204000d0041019007603c80407000c0909111182c115240d4215a00c07070032002c2c0040203510b9000964516080d4408800750800c1a603100c10000c01c440410b0b036075040640e166042098802c00000c0500d010b40c920412036516440385002d000494554 = true := by decide +kernel

theorem cover : BRFrame.Cov 763309352 763489208 := by
  have h0 := BRFrame.cov_init 763309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 763309352 ≤ n) (h2 : n < 763489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
