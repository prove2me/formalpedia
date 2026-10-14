-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1686
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:13:23.960217+00:00
-- url     : https://prove2.me/submissions/754ac0e6-4a82-471f-a04d-85db1e2ff155

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 303057553 ≤ n < 303237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 303058803 1250 303057553 303057613
    0x12091208040516030c17120f04030201140901080613020d05010311090901050705030a090303060801180210140d1107061a15030f041e060f020a03050105180403030c02 73
    0x41030401d41002030a18500024008290305455010070018210403025000c0350000030700f1031514420104540d041c9050008040c28229000417600303071180004c4040c0c41500d000380e9980443c070740e5202d540382440c0f098511180c080780b04000081e1051a110507142c01010044c900581800403120321182a45c80a80045510b206c0c9000843c0341c9050200c0400d9104d00d03004001e1080e070520307070f40c0a0301ca03102c0940003686035901c0b0078803202414002e4001c00c0c020300700b034802003001c00c2c1e01b42ca0303a074040302851604a10410103150f03c0c034000346c13041d070460464402d5585103500d04800030311008014166191402984117050007007501080301c1c5d108a005010031003e0b0003241c1c07944e110170070100301d0100901418441c002d1083c410003210350318110340d015500558018071038003410b06c08025004400c0300202460700302000301c6104042c54001c1c0c9071004503902c040c400c590303c2c2d6080202811141c030ae0003a90070f01c0100001e01280c465000701d15413000038019681ca4051010821500b00080c8002c165 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 303060053 1250 303058803 303058817
    0x1a090d0507080303091b0d15050a14040b0609010e010e06101116080105010605040e0f04060e1204031502040b0a0e0a09020c0a020906040507120e12040905240f01120912 74
    0x28011b50401c080102c646040b1410200303039429075034000c0c20420107100148001da8840000d4100d403841ea10202202000c12003048080c0b134149407150700303a00308649240c002e070401000003c0c1454018201d0341a00c0c010020f89015540b000306000040705102d041400b0001d1b00c0400e0b0036025014800c04880501060301c8900180c03c082d8503909481040c1d129004004080000700206040d410140780c010406003901c0607035454504165024007010300d808004c5020702c06081c46a80000c000520840c1d00c03d000d80030a94100d102180c0403806a40b1400c594404208621000144602500803101000400d00c80d0415100c54041c4100c0c2c11000c00c81100380d01031100b0006624241c1231030782d4444005c65080c48140341040004240103449001f000d07006440d50740c51522901c06114094000c400d84d5009030301d0b10303650000b00e00a03000c00d81c0d081e070041c00001040760003024a901c0b04448401e02610404002c0c035400700445411a10b2940601072aa50304120f00010b4041809002c3c80b1459540b580 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 303061303 1250 303060053 303060073
    0x1c02010b120d0e060306034e04030807051002270d020d02060a02010b0904031e0906021e01090203340e010e0705070f05010507091a090d050708030309 66
    0x200e02140c1868880405601c40b4000c00390300303030f84407070350040003842502c809440752100d201003898440a01614119880c48040100124500c4440e40f840003d07030001d0031980303041110780c400c0b00305812811005922020030007030012400010040c100c05225004a030712680f090101d980490300800b1084807070303d80452b00c1c0c00111444a8500725201e9003151000c0301c002283d80002c41c0c14003130000003400f8032000b25039011014001e503c2010ba0342005031034004507160618005044085100d0303ca000380300703140380d4401d509104032010401e0325110340040150300482103200b080005c549100f07645541d00c41c0d0320100181c80601c03000800da8001c03425940c0710020007885000c082100502d102c602090011708004035490032034078504550350f03403c000c51180c031058400c460780c0c45003050140804140a104004104055100710310801080e941c43d03241d2034542c25001d02406042c401e0f0315211500307110000e600d06e0454110100d8510400c101c0b000301d6601d000f02402c60300304a4241e291034000011035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 303062553 1250 303061303 303061309
    0x203040b0919081606030e07090905030d0606080a060608151908070b04081c090608041e05070314010902011e020a020a060f0e040e06070c0c170309040e16060503091c02010b 76
    0xb071005d44020305080c4102c151019149139140e0051050400076a290f044c04000e20405200305d5010100440c414892103440d440c010308105401e41d0140c801501c0c2010001b0031901c600c0304107004601700050309810100c0743c8100b283c1d2110045020002c00e1031604c00040b0000100b005600410500203159103840c0741806150a0a880f03050681c1266500c03000c5a103036941c0402694103480c21030816440d540c403181848030f02400560a018084800e810000041c441c0029011007245d2245a140c0c011109002440b400d03130b07450f198000e02040d0480500c101d845103c61001101c3c0d8110720480303050507041d0700041c1c6901d81950010011a440d0b10105400682c0b2504000541005840a0210700b0310400f90580e04c00005104104011212100c1401c1100d8208500c00400741c1502d4841440c01191a0036266031162044621072481c01000301181d82000c50700f0a208442c007500742c0382c46e9103098000e0310b003544010840c0074070340075007039031382d20120002445408170000b142c3c00040c02c0030000040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 303063803 1250 303062553 303062593
    0x6280603140106090b060f0c0705330a12050402281502210c0c10030e15010e0601110114040b060f0306151c12030b1504060203040b091908 61
    0x5040042c0c05c2c41c41d030341903e031901d01c00c84021225600e400c913510740c0c005640c00c1c2014141d0f08040d900c01441000400d40c4410484003501d002402c1c0c10301d01c3e211000f040341004911038007040340003084040b105050f80c258560700056005001030070340081c1e08071003000d04100b442d49000c0f0301f5184200020501240d200307007101000040311400141604c00100641c80c00029401c0d45200308071800080f04e108540003400603017108007015040c02440302400d074025028045000c41500540f00b011001c0280c10219041c0e58122001103d18592030b880340001140c100346d10380c070100169900c90001100284030900901d02c2140600c4101c01242401410408909a00c8103045d1080d440304050102c600400403d54608a100702e80303d07100520000005c201131001c001b4060709180496455901007901a0000180c48008550b010300a00c4201142c000d00d0080d4064040164000d001c1400880401001402c5000303009005015000000d185904078010607003080d22150043c0c2c1c016420089d503846 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 303065053 1250 303063803 303063809
    0xe010609150f080c21040c18090822030c0e160206040201080a05090a05120421050606010c060b0d0c081002160f0303090b0708090705040b010206280603140106 70
    0x82d21a44290801c0002032074490050100745901200207030944440702054880300d011006040e5030320551829080c21010100e40303110b51030f07140b01a018010f0740d0144a10500394110750211005051441c402c00d05002c01c41407486001090303006440100c04103684d101e82800515400104400500d08442900795080022007114290740c841014000140e030000511030b404503c040c1300150035503440441c00e1030440c0c40d0b8800f07040c90080c008600d144412107c01007040ea9075194803090009424029113840b0000d11402600c5908201c010451540c07084403003c2c2d4a078040e001c00f250150b840c600045d465415420202c0d1501540d55003000200014003c0c992000a115821410032171403000004458072a80c0000b03190b400002c2b111707000c060007648021902a0040303080302c140c3c40c2c0100003800d003070015204c8181d07910488200060f9841c140c00b84c8003640360b041c5c0c09031040d42c59509911010078a01030500d19412100c4944130040038162180000a40c011200d0083d80c414004c1518215085a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 303066303 1250 303065053 303065057
    0x20328020111040b0d050402060f07030e0f0d03080103031404030204180209060a05180a020d0501033906081e0a02070c050306011a0a0504090c0c0b1602100c02070e01060915 76
    0xc441004802107102c29298000340c5845e02007801e90f21880021001e1141c4180c060280e080400e00d1800e1542c060703840011450207589801545800740200400140309540080005d542d070001407000a10503600d20507a8400608011305168483c0d0006094660740d40300303005c1104d40c5800c50010f514010280c80e410050640380d050045080001082c503c03662010911036100080d000b00750282e55a0341100c1c51245142010000380d61a4508850299584030110751500742003282c081c00a10400c21100e0010440d0103402400e0746040000d8079140300003004c0014036003403100b0001e443c8443c5c1c03815070702c1244400380059482c1c1c4a17150a003d8101035070842406a0f20510060005001d80c409642ca1507a158041c1601c8050444d0111380d14400e40d000741d20101d0600c2981d0200c1d503002990749a02c148134048900b01075a0b0107007404a80c4442e15841801a44500d0070014000800d9028811400703c81c819a003400b038a4810005200d1000e9004200244125404018580191016205101c0c40e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 303067553 1250 303066303 303066307
    0x806090103052e09081e03160804030203120106020303091e0a02061b030c01020a080a020304120e0a03050303010b040f0e0c030103150209120a060506040b060d020a020328020111 78
    0x1580b038040d0359082d40400100b814a14204440180c61036031030b2601c40d00601c20b01404a00c64501d010907580d000710044110b441c00000743e00d8010030b00380082c4e0384038100e45566141065a1443d0840700795101405c15400e5000401900b01600300a80929010b00380c0c58000350703074904140d07040900d01141c4100081480c00c04411244040001040b240c207143d40442d0f03c103460f03030a5400c1c4810246c10128501c0100c0c400081c0041e0030180640140903035180503140c0c29041d40e01c0f20142e009911044400a0100e00c0003207c4206090080410700700450020b00381040850300d0795640307451644281c10142d540400440c0400031031111800d030101800c00c07a0003504d038500345202c0100700c90006010062440742c440324070101d000c00070743c10f9501c0d0b640010501001d250005108940b503000c0200180c8120341030900040190500d40511100c4100c040c0066292841010f5048002c0d00201c0280c0114001044000d0305148510600d605045100000c81c42300700e82008040d01b152450340340c00700c0c1c143c42 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 303068803 1250 303067553 303067559
    0x9060504210c1407050a1701051803070b1504060905160c0b18010213140a0819060902030705040e031c050123010306030b1005130e120a0905030703080a08060901 71
    0x449078a440c030b003035031101c1e01c00603003180c1c0c041e2a070520700c03940c1102d604020030040018542c90100c1175903404503040402040f41e0f4039118296481c42029180008442c0c1c010440301c0e0000b4000808a580b12041041030706000c00c800c00040e040e200180d1040607030b15100e40c140152003110080450901e1858284001c03500b00b20303518036101510050040d413110151a810b00403955080d0119080400156034087d091b81c1c4581102e030001c10314000540c0110a182d101049003000010989854003910140c4d0001d01410381e41c1340054054445d00f240c141c041d2480c0010380c0e4586002d40002031320180c000e1600d980140b100c0038501c42e86407000800107403c010041046a080400700c2c4c1c070b280e03c15500282150324440040e4041e00f82c9520091440c924035041207100da45188500041d2202103443c1c1c00c46c100841110800d1741c110200625145d004803800c00340514100005011b5890681070140301140d5980c006402d01c40c1c5e030b5200303540003100090043c000302d5001002507403020044079a4070301541 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 303070053 1250 303068803 303068807
    0x14030f01060c0c03020301020a09090e0c091506070b0f06121c080c1c1b020a021005070203160909061409120319050903070201080c04030b0f0402060d0906050421 71
    0x48107200e00c10078406a00d00000034008018000c0c4051a000340c000e56499003100c0b0010300b501100c0c801c4280c80361900d41000055600420040440d00000740b0360304050300ca4803104001d20303444001c02640102e003008010300003024103482d44c0c03103652500b41405039032070041e080c004c40090074502100c0642004008040010300e0800b2a02414034a14124180e5501d607004d800e0544504000741c03a01d2f110f0011030840118031900b0a04642180131034200016002110980c2e4503404900b000b540701042c4011800c455102e4000340801500080c120f440a580201c521010b0703582c41d400005641744c071011601c040c00003e0041c2e603611015851b000c1c0c0c45160501c095a21a0500c0381050102d800c000041100100344c0603088080c141146800c0195003400e0400990320390043c041203021401100000303909041e2034040d60700f00c9130400c0c4410078650360092080d1800100070000c03070344400d0901141425119610030f1040040c410000020b0b030782031030300348207031052415a10004103000012031412419 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 303071303 1250 303070053 303070081
    0x171f06092a0c05030a0e0d0501020c0a02031204030308150a1e1a030c03070c1b080601030c14010f050a0c151a04381228030c030f030605060c0705011403 67
    0x3010780c540303100124021030002e001c7d08000030029000c0d60011980c500c43c1540407072103980e002c0c400c50403180c1d0210180f054100c64099488043d0103d1220800981031500d000992061100020400c000f02c0c0d4603000c451200c1c01c007d03091900c41c0d49000c1000d0000107680f0190800070882030001c28114a0911600070050dc00204400104041100301ca400c00040c20b200b4140071040c150ba002c00705480e807000399035031002440141d4201e8661300740000d10410500c0c1d54031076040d041e9a00a4101c03074101c01603e00e0b034003460101c070800041c20700c1c20380400c0780307141b025407043c40d4680081204d2079071100541c0c82c250b80040c5a44100d1401010161f540e50030780d000b0000390040c004070000c002c1c00125068031401242192504200c104d201903d180d5400300b00c0c80b52a003400810510f100d00080556005001003400090108880d032440c0d60100b03000e003540b521100d0329494040344040d03c910100c5d207d0742006901e0006580070510900041d0380248013940c070f000c0d28814090a5241900e0740d10120 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 303072553 1250 303071303 303071317
    0xf0b0609060a0905040e030a0e061602090903070501050f0702010b03060606040501030e0a0b13030816050417011805030418110706090c12110901171f06092a0c0503 72
    0x18101c002080d41a040c0034042140c001d0100420411040c4074072848541c81c1d9000d11400d50000e0003c0c2c0100001e0701e07101d01900c51040300f2803000c8203495100e90a00044502c0503050b210a07204c00e00207140007400c03d000d0180325820000021215082c901006420741c0c105031015413198000f0000c1100b6a20f6003015542110002d107400310312101001034450802011202c045c100040d5102000040310900c02c807811258403955417440255201030440201005000880000441c10001084502ca030003606904403080100009a48105203185100b020400102242c1d41d0700041400c000215440300400808010814144000c020b0368022a2151041c00780050145540c0d01240041c801108200c4015010780310b4510f90071452820110503101d1a482d1700d6100c0d0346c090001049103035107a06265101d1a100d4010024100000e11031b51901c90440c02d03a0724807a40d2844009000537403802246804007031000b89502600840190a45041089540da0107000303480c50b5040c0010b000200300d50350 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 303073803 1250 303072553 303072559
    0xc050d0807170a050103020a05060f070605040816050c0108070e090c0f040503190510110324060d06080606090709060f03020405180a0501051c03030e2e0f0b0609 71
    0x15a1105425158015142e8800300000c011104002ea080344552129050300c0c021107000c584c96585100304422071040b0036014020b0384052102d01d0004041d500300541040c401c000640c10140705801c0f00420412528099074507901004480b0b03565600414080d03088800c0e841c003a450201c03201c000c510240c501400c5034085000c00a004043e00090b403007544c000d01030090503200108210f81074282c11a00d601c5d0269203e001e42038400490300312501c6010783e51654503100d1400c66031780c19980048269503c074108052010752003003001503035500d8010b001020041c140020703500d01342001c0c18903041c0e0051400b80514000000d020750260024031000c100c44942c94201c9102690100880180c051a8070664015840f45072001d90202d100d002e0300d05c640c9410b83c082119a0340c410800c20f81080c014030103450342101101041c00719100381c100d441e0003d400320895010307500566039003205407240b92007400404900241c595801806001e24811040d400b601800401045e2001481d14805e00f03601d948 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 303075053 1250 303073803 303073817
    0x71109160c1502040608180c010c030c06110a030e0714010206010e150303030a0e0c0a030201050d2c0a020307080706120c020118050606191820030a0911010c050d 71
    0x10030005202d05610100d15481401e6449540d110000f421940080c0c07088a410b81d0f9000b90400c04c1d01002451000301c5205940d4a41c1025603500c00740d50800205a0079980725440d45c28200900d0003100003070500d40c1641e40c2c0010341041c00400c550410040340c00c900b511403040b4440405903a4001095410366640a01a500c0c0d51a84100001c0c1580380a00b11601408040100328101c0d44561103d0041c03204030007a81d4122590400308128000f003030000902140d01031100080d4076100340d014086543c100b5016007400c0ea2124111290080b1480d03400c10160f0080611b8401c5080501c5080010225500103008407418018050b001c100c4545030721105603951000c40404500c03d4008011164101c901d200c1201000d040403611890304a494034004d52030b20640c400c40d8100c081d001c40c101c81e81c0a88410700344511111110240c0740c0c000c0c1c080d146a5924202c50380d115600390082d8062200160001002d0180303140c01894080c440740303d0390520a8401e44840450008644404000e10301c0c50310403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 303076303 1250 303075053 303075077
    0x150305180106060806041a010f050c0703050a0b0604060f0608040b1e0405060403020d02030f04030609050102040b040e060102070501030902210319031409120a030c17040807110916 79
    0x80000524846400c81940c00c240380065407541000c49213001c0e000903a0107005640500c3c40c01b100002c0340c0d83c00e0a0000701d1080e560b4204500c1000034003081101c200030703610315594030b0311000c0c0b418000580c240c404655607002d00049142c1845050010803508040e1000c040c034040340030307240410040029102622900003d507a410b90034400000208814116030b210707003004c2c1481d940d1408219030840140c410800c2000710140004161911482500403951415080d99100d0300517110160013151690f40903c404104040303142c0141000c0d00c08000c0d0f031811460a8000240361282a9010030705051400c418a00561144c109114140c4055020750000c841000b440514520950303059012501864202240d4030f0751613007001d4003030289024014425194a0500e0b03031142c94646c400030000b03500308190516240603410540d03505183d82800c0481c9032441d5462080c1140c11101103130f803480b00168020030403035405409070b01e4210980d100f1290345401d8580302d80c40e42c0d4040b42c000078000652100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 303077553 1250 303076303 303076321
    0x50702100f02040f0e070e010801140d061103180114060d08070f02061308150906040314070503040f09050a09050d050c19030309021003050c12060609040509030301140a150305 77
    0x110004c0104480442c141c0307a8958046a00080a94a940004550300a041300940c490591031307060700e403810700300c0700140c09c40b41c2040040e4000ba0001c6406030f0f144d40c4820307106440d44d80654400c55a281c5030125644400d920b180c2100c10300b0164400c0d141e12001449005c0c0c80c0d0304041c444190b032000ca0180c0e181ca0341e04001e142c1c0110448000e61001c00002c0c0d01c10a9212a05500201c44034041100d03064924440202c103a0541103a480850354000c60000d0301091055202c1003556003090892032038910310f42c684606680c000d400200641c0e02c00c510400402009101c0c00d0b80c4076400c2002000460074590740c00303440301c0003802c1e08070810901040402d0210424880c0017040e8241c03130707400c0020403800c0c9806809803402c0c0600360711821445000040b414000e01525206139206141949000040c04000d00320407409041c1c1d40c0c00c0fa10901c1105120f403610b119440c0541c607040001c58881d8076201d4240c0400d03100204060085000308070030031841e000e800301c40c4105031260401190301c0d80c1d04200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 303078803 1250 303077553 303077557
    0x80103061a0a060320030903191803060212090a021e18042303070305040519050301050a0516090605030a09110303070c081c0f111e1b0301050702100f02 67
    0x400e82d01020b000b800041440d00744d801503800c0c00104081c4803842c600044991010b00040b24941c120342c1041152504072080720b00301d000d10660034186080400c404401000351102a500200c4c0d015900240310702c20180e048a640341c1c80f00d00d40c0001c0000c3c9180d580400d803150740c22802002c1039007000132206195541d12500c45011181340100d46804e01e03046c180440344040e959004070407442106100d1482c05008400c4a4100350540c58042c036140c6040f003400a09484803a49101c6100040c0c804a900d42d400c0c0505400341e00c1005012485081c64002c0040103c071001083d028424803c80402c44c094002042c2c039804101c140c1e0004070040e941c1000c00342c80381000718460745030000054813020083c0391741d5060242c40d1040c00b01e40d000d40da54540c04141001068041c400f0559160002d010244503180a880c0c08162600759840401c0b5100c2503404400206846405604035407500502e40f07070146460303c00644110000c0c010350522a44c0a07441354cc400c00ca00c4070b02c5444508810002c0d07002e0701 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 303080053 1250 303078803 303078851
    0xc040f060807021005092e020d06150801030b01120314070503130e071403060f0a06020708012306040207020d200102120a05030c130b0403150f140a02090109090e0703030f030c08010306 81
    0x4217540d903a141003840c0c030040a00c0d000701c0c110bd08400c00304808440c0b003204040c8c140c9501c40211062139003031081800c035251001608804004d4400980300d541e81c540030240a0300c80c4984029900c45240a4002130405041d0304481c082d40c00810421201a500030108820744100e1419503959031141c00204604240d60300e003840d00502c1981d00080c10560015640c001c861042c8000c200c00c2c00c1d2485014400300603030102c100210300141c0031031914034080d80104101c2e44010000000030040d50740d000c03004e000b1038035524017130343c5075204102c91541c06105061a8152105009240020030318020741140030143c5810303401c4074041501e0409c40c5c0d00f40d91650103040001d0809486540d01e1420240c2c1038114000300c20b58a09080109010b443d10b806800301604d40500c2c0342d1480da840e505000000d420a0107200e0400560520024903110a0320440d551000480054440c203402e40c10064001000b40309807030b04141c6044110000c10b0790180ca01c5064079808140881d40d1086041016210700240e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 303081303 1250 303080053 303080143
    0xc01030f090b0c070b07030c0c02040c030f0e2d0601030b07020304030f08030123030d051c023f011e0e090f0d050f040902030c040f06080702100509 65
    0x4041c03000700303480034010b008000d1045c0340150b103580d59000c084041d64200d004250214089041c2c8c000149001e0f0840419400d451800180303000030f0580036026502c010280030b202c3e4100348000355801d4016001d281c6e4003ca2102c2038900380703c450980540d00d00c014480584690241c00200b51954030900444005540000ca00f03600004582040c0364158428450340b80600c0e85968207641d103405594003210f103000000d02a0102003440c01d019216a8404007101400016036007143d2100003d13440640000d07100c8990300700e2a01c48003c03945014031910030f138901204500003204031000e62102a6241500e070082c041c1c008142e80400c001c640201c40790040401d541c032181c04c1203c1004009070381d10704485840101c554030340c41410113581a1240311042142c3c03c0f03042009122404590700296000000541d20074903065032200e040340441125001800024402001e1141c1c0d60f030304011280402c11455001c2000b8244200d03000e03501c40204444050507014042c4901d10405c09418090000d000c0d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 303082553 1250 303081303 303081323
    0xc0f07080d090b09010e0c010e030d030f20030402040605060f030a11070605010e07020d0305010b04210609081308030418050402010c02120d17070525020d0818030a02030c01030f09 79
    0xc285145c06000040031100d29845000043d158a6104c1c0c41c8481c0810005005010401d200d0041280034010b00c00300000d54035140c0311600d42007044100708101c03101c43c0da034013140c50741000c0c8100000d94080b54860f51041806109031900d081909048940080d04220300207130100300316021603094080c0701d4018114a140500005048401d00400d600c582d0b5640d0030749080d02509030003074003202c4081c09581e01c1c91809000c280b091100544502c83c041300f01e03544003c0110079a903644010f0f5182150102e580d81408110076000c4001d140a00d8007900b00240654103050804103078507403090086c44107200c0716032160b02150640e400780000c40101a00603105894140c1740300422542c2d01746842c1d25a000440d0075071803003088005040ca0303034060780e42a69080c0c50040c1d0342c180f20b03070b40c040b6407580500740c0c095084854005980e0f54006403d15441020715980303d510b000540d0222803007620780d1500036003118005000503270303001c00d92800c100f809003000501080d03070200d0b00b00100002003000300b0710b040c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 303083803 1250 303082553 303082561
    0x90503090909010f050c0405030c030a08090424060302130f030308070309030c0c0b340305130f08060a180c0611030c0613120212040302041e020a090302090c0f07080d090b 75
    0x21b0f0013402940c106a04842c4070304248814582e54400301034020b4042001482000c0c103629081d00302201105203107040c4000c400344607945004000f015400000401c1e40000c014500808040d10307a0f0082001c0400d045001d851034401510f00c4000500440805549070580b0f010103015540c40c14595030010741200e44503448a0072841207510259409200d442c3c0d0202c46c9801c2e6084802c006a080c2c10655104060032641c0d50683c2c1b240c010480d29200d00d46140d2010070508a81240c0c1c40007880003200070403090400300005030031544002040c03080c10181200b020007003418801c1300011200d0034a000c03800d00d68500b400d1402c5000d45240109a80650802d100e464010311216115650003182540b003036449000f0144d0396422006007152072413030248420405032031325500881c01104411949000100d9030310064040783e02c941100b50218016036024000e500b0000042540003550400003490104402c0d01003800380036400c8001c2c035801c8000342c1c60165418642150300c1f019801041e060f95414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 303085053 1250 303083803 303083821
    0x2030a021b0c010315120b0720060118050108031902010b060406020105010e06030604050604110103060e04030804030206010b0c07090b04180807210507030503041403130e0a090503090909010f05 85
    0x1118030b0760000b818034206128409903c19040110f5140031110381c000d085940d51815081801000300d03007845194901314082c4445c6001d0721000660b13044c00713401e8170340c104202d102f020705041044031146071901006114422001084680c0c1d0014040c8504070300d811900d0481c050b043e090390042e000000498000380c0d4640542006044e03450b00c0310340d2503081d0b07a1001170564852084a024100754000c03c04100420b2600040032440300381032401007003141e1504400441104281d8040b40042e0a5004200c14103a050000c0c40c05450780c06280c0c0d10b0312000c400312640c1d070351075409450074031030392066400e402d03070740e80d901a020b458420042241054514188811345421680742614a004010310051070381c0700c2c94081450724802d44d2201410190071303840032165500000e000300c2e00031b000c4800905e0007a40400c0070309188440404611995410110030088070300003d819282103a007480420400130300c000c01034030040c0c1416100d05007140d0341c00c11018054600c800ca8601c1061814040c82a0a8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 303086303 1250 303085053 303085063
    0x31401050904320609010902010905091b03100305060a050714090301091b030c06050f04060305130f05030306190308030606070c0b04060203090411030411100c021203090f030a1502030a021b 83
    0x94041c0c401e1368059a1220342c0c450a840c400b00000b400181466000d000743e1402d88070360ba03040300b12140c5000c0246111a182c40c0380340c0c02a2015018865004030800410030200314959010501c00d00c24480750401d5003014045043d1044043d052a2004c02c1d0079241e91401d5015416064109008000d6481d0b40f448460300310340300380004e41d220314401001044640c060402c480290265910030742c50540707002412002801e0181070403208402a0403680081074651041581c501e000d04080c43c2c1c0c0341446000c10031080d420030241e41030014003007010408681d00303505596000c4c03402e9480a43c1d40c0d00b07628202038101c41c15002122210008140840d850354000090230380110280c0d42000400d4140d404100907010440d0010300000e81d8110800351070410002e03044801020781044070b0b41151550014481c00100c5240740c07955480030032991494508080708454442c81074001e440103040640303c80040c928642c084034006500000070540f840b641c0e50444450005041988030505603001d1515124 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 303087553 1250 303086303 303086393
    0x2010b130b150304050c1c020d0b010e01090606020312060a08060c5811070c0918030c1e08130b040602070509040c0e0412030c031401050904 62
    0x190301441c1c400049111032004403800b030340d041700c010304892015200304800100195441a580007262181200685a030128190807500c2991000c182d0b6040c405a907080e4001680142c4105051103001c00007103802004a5a4640440c9080341d081e50781e600106030451043e07071080b07403d482000200320480e01864043d0000c507000c080015030702034031854203186650060015a440c0a03205490303202a0030440400074400318801041040011084010000c0302c201c50f1001c080342d64005400000c020214a107600a01903c031000c00401d1210f030a001420307400c071400142400b103420040d4040c030642c05d220645200d004803000440490a282c4100b164000c3d416001d5803504840000c030b0f400b0b0000d4103560580d0065401092030500e024100112200d010700195180400880701181c1402241c0070035104070b0143c85145d002c1000078400030704460080c0202000c15141c00c043c000c3d10f65005600030b044501c101d0b20f01c800d503101d6060003010201c1160072602d011244044c1113060901c000b0443c040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 303088803 1250 303087553 303087559
    0xb06120f031b1b0603071701080a26030f1003060204030f060e060c2b0e0d090602120d05040203010b0310060f060e0904060213171b0105270102010b130b 67
    0x28040c6254400c0d41c03114a10f84480d02c00d419104252501e051030030103503030300030810710703140030190030740c2c400701c0c440c00c07807c2c0c002c0310712908800800d50900038031503a2980c801910a280c0c100380c880f00e02941d0f82c14000503082610070300030750340840c1030881c96a0040025503045481155038603580c1c5080e0411646161084890030708151010750b40b0840495002c0c41950b000011a142ca0100d804503c04d0141c4130108003520f0018501d88801d1081d0b520854180d2200300c0010030b0281000030b400381c8070521603800f1508650002c4039440400e01e110040d940c020b0140784e0041269115480040e001d0107203405660703018814005042c03800b16030742d001302086440c40d03050818141e466a0003224444d4010700c4a5805c0403105e000304000070300c2c682c003c280018116024004a6441d1180501603540c1d038808609154415203402009030700c914199500034a007400d0107032400b403e42c1c6034040003c003144440354250070200f4084045900070b4000104802005009520b66039500703a6440c0117004861980d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 303090053 1250 303088803 303088837
    0x806071103030403021e010609050117070819030f110a1a06030d022a0603010b0717090d02090408040b040e101d16091a090301050907060c0b06120f03 66
    0x8114040200ca02494066020701b03001e008001d001d210b400101490a03410750740c0d94100041c1e90307000e48600390207025516400880d54040b41941407400000c2d810401054005d400c80d8840d024859980703a508661500700704003e000243c1e07050b00d248664018540b00e034021864a1010889075801040da0f48040c81104019900c0c1c0009056591802d001070401507480114401002a1120780742c1d2005401244540100407164001c10201c0e00203034800c20106034040b862900b00403150315141040201881c100d4100204140014a00d0f000d8800290281c48440003160500c1070420498001d0800307020b00c1543c8664400165076049000c60b0a2b806201038018007003114241701300300c800041f005006c10b503403580318060322600035000e90b552031040c840341c002c00040c200740101c02c000f6500c41d6840090744030381207401854290b65000b480003903680c0007410140800b5030000b52002440d81c101490242c0d5a0b10140132070403010404801c0d6507d4420b4414050b90a480007006201800d21501404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 303091303 1250 303090053 303090077
    0x70302010f050105031002031510080a051501050304020415051018090209010e19051c0209130209160c05031201051e10080408090a090b0a0b030c0a08070903050601080607 75
    0x110803280203010301076251b00090590385400c52940c02031a003050314485640d04848000e400030782145592003080d0013085002c0e08020011000c0d01c2107903804100120720200d41ca5000700002c0442c4401040244541d5684612080801032010403170040c0134041c2039080c14004c0b03160302030130260480104854030706000c5c0c00441c00707035180d00954440c1e61042e12000c6102481c801004081e50b51900b0380c0c6828491500d00044955888c0c90606268000c07803c0e0161036282401440303603005d801082d90649d01c2428580c000140c4980b82010351042801e070041102d056230a604a540155401d00a80244808507410b500040501d803110304a55048400e9826680c00a42000c800003000810f16407017940902c00c1e040c0c5500840085520074420026030f1328180480780000c100d00b03995000307003014668400c0911450f0070102a040302820304d031141c0606526010040404038030070085980b04000010303021410746409010340c0b1025591000503580c03903684409015917624011507a9a0028038000084 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 303092553 1250 303091303 303091331
    0xe030f030c060411010c060c0503041109150415030503040f151b021311070f0224030103060e031b060703060609140d08090301111b0105240102010204150507030201 72
    0x40d0741029505000d0801d80d80c807a1900100151800461030520040d4061100010071500c558018000d00da00c440d500c0381404e00704440451204c01800b0701a1101205200c02d030301454000746040c0b0b0003228045080c0d9a40c00304030041e01c0d803552000f0182c0c4400700d004903038130b000e000302c1c18180c40840800056502c5500ea085404d80006c502003801e02034080b03815805820310f4165149005c41092002c6008280c100c0c501d00780381d005000540300664410300940840c0740110039802c00c020444000d010f100032815500c5817902c01844002e20090b540d00304514450818000d441100700038440c4c0d405002c081140c034a4541e0b03022941c010000745019008506240150007040640d41d400c000c44c20a1b444c0501404445040190140c03800003080c01101c245581c03d000c0d2004018100d5035864485024400c0702c0e14080c5003040812203a41880d00b08100e00090381d1402d5546041e0703441c0503c0350101040140d0083c0704030741141004005c5804010341d02c641090061140500c640d000300b0003401c200d0300d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 303093803 1250 303092553 303092557
    0x1d0c191e0315231c060506030106180213030b09070602010c020304030c0b0306041e2712120f020d09050d03090b060609060f0a200705060702120a060c0e030f03 70
    0x310b04410a010300307011002a00c8404052825400c4000502c80700d03800c00a00400420102c8030003280d4050b964108100041c0100ea070482c5080c3d0082c8031007400c104040c80e0700b054030841641e04903800702c1c000c0240714842c0c041800850308100b5010450070030120715903c0c0c4400e8007400300590b090483d5446114070010880e0102e98000d150b0355541800c2c1440e60f540d503400079142c1c0d40e01c25145d0008504201d1454b20141461181c203038009400c003410400c4040021140038001c41000940c0f08401c0481c3c001a8010180c11051414004003c0417484084c01000342e950705185061000c00c4280c0f140c07400e42d01c21282d8a00540446244041081c012003d80700c2010004007d014008045161800c01c400501202c000c010721550030403c0484035092a40c1004000034006428540c2281804440041561100504a010b004c2042c2400007040c1e4520911100901a2807800e44d24150103005100000c01c4540c0f0440500c04000009402401c0c807001e1800300b846070044069400d0030040000c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 303095053 1250 303093803 303093821
    0x140a031b030218131101201b01030b0a031704030f0501090213290604050405040602040f080a050d0f03061805090c1c020d0f051005010812041d0c191e03 67
    0x4d24120211929501c40fa50000003e00541c1404a000910140e4095402113038011507145402031510211078802d120440c80c1c080c0b40d050606241c4084a141d544503d401081a03a42140e07602c080c003695145501d80c1072240d540040c0030580c142c05000100401900080346840c000c48007044450000310384a0700f240d440350720141040e40039403036400915044a01015070214014a5130741811340e60f42c0401c059803000c840c03c07201c0681c00202800011510020000600301c014010080d10b0265038a03c4d540313013030903036070306007405130f0301841180491090304000054203285022807101050345010001030a0300b6113040d599406150010f59260503d0310b14070b0300b02040b684000c03c6580c010780130b025410303a032a8010341d41015883c402c0008a4000c100a10342140071000c001565032414001030705010002c1180d1500207010401004600f584142c40c026090010959000640707c803201c010241c4201e121249801c040c8600301d2050076003103811001c0c80680418104c403841a800012411507030821 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 303096303 1250 303095053 303095071
    0x120406061a0a05090f0f03031812030a120b21010c0e0906060d020304050a0c030f03020f06010e0610020a021203040504110306030706180509180f010510140a031b030218 74
    0x70000110905e804208443e94043c0075101c110342e1444c0a0200341154030500c40030f0345100900403050b0990500e844036050300c14025020718104221208010078030b07204105c03090b10031030b02c4032403614050b80c5030300da800001c1c00760034103e03a00c1000603100c25010f4030480401d01c0119545910900150401040c00d62182c0e00c0145a43e10705a03c1902c400000d400c0a0f206456510440b007001e400503c0c15004080a035005446450901815250080c900406046880d03000c0d04a800108601c1d03190f13002d519041882229022030b010f00e06003040b460306130405000380d48800004031524a08001000900540704103450901184410814110303180c481690110b4041d8803041c41004024405d072103282c6151954811011060b40d030340e00041136002c0982e100041050001541c0805203400c006001e00760002400900162621120300e4903101c02c684074154100d085507400c92066030ba036110302000f965101c01035506119401c00088034444a80c00228060810b403441d1683c14051103101501c50030002c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 303097553 1250 303096303 303096307
    0x50603060613020a05071a10060224070c0203010606081f0308090105030408130b0315010309030905060c010608030c0f0705030f031c0b03060f04061b090504050903120406061a0a05 79
    0x40600d9500075408207130a4003c001c030a00c40000005c408160201d0325141181c040ca007241006c094200804003990701c220f0940d8404641c0e012040c1010b038005020391400c849031026a9180c803c1a0b07981c0b04404402941035103001804103450f070300b00c00c8490054180c0d240c9140420040b202c1d2455219140c0405082001d062001c140550300c81c40095038010300c540c4185091031504100c5070340d407083e207402076280e8040c04410080c10007652504d05442e1003003440c05000e05011030700e014044007094002d681c002c010011766042e802c2025044500205100400c03a9175808078034182545400700e40c90316440900400e80c0025843c40d0010341898101c006901442c6810012824080c00c0303480000c480d04001c1d1141c400014695041c031000740700346218001441d59141903d424412186013000c0c4840102d50905a0402c00798001e6142d0162003003071b0b500144a444054005245015508001365800d0248080104012080e0069000c5406005c140005031104410301d10250194030390030300001e401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 303098803 1250 303097553 303097579
    0xa110c01020c01120c03061a0702090a0203010b030a1d0a1a1006051b010b0a14040b0405071709010e06100303121b120b061303020307080d1707170a0c030506030606 72
    0x140e4800d45c9103048604000855540d44e00443e200300c100e2440018804202150381001d5040854910740c0c840016441186158140103200106020241200203107a0303886030101c0d00000c006404152080c025002c44052006624004242c0c18144a0201e80c1d58800c90116203047c8600d1210800c2d070391741c0d13210182494a09034011400c5184034034234070070564039103800d03203850744401d6030380000303001c05010105c549107500701480190f81c40e198a49000e1480c040401500b198408d41f9603070b451f50500111041501e920101c81e000d8003448610b0052406100e0a00c803032084520302c403808980c0301c0d8440c2d18201c0c510003000002c4640740304800c60001c0c201e592504a080c4101c0018001c010210350008401844401141260304140070145134065119030510642c80c082200708002c0030340c00014a8803086082e8000d007a803e0844191701101e03001d01c040380140340a13030b030809001c4080541071116880c0088180c0041c0000078100c0300400d1400012400505021600d03034450a405040d0004034070b1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 303100053 1250 303098803 303098837
    0x90105011805100e100f020c062206020a1428080d0e01050105040b09010510110307051504020f04141605090303070807211e0908030a110c01020c01 65
    0x25000c0000074207503003042001c5202e564458040341d801c1c40e150341c0c0c4400040c9203010b0101101c509129081030003805045041040d900103105500c183c02951101d890300c031142d21001a02d00240111030049041090104040b980052000441e40c00f440d4000c000100c00c00c007541d00c0b00d01e60003c01c0c20070354a9a030018800340361003e90203170b03007403244c480e01d486e1001c5840740030203c2d003840e24a056036075107a82c0100007078500b90040741440001200c5198155141c0070000340c1c20b9070035180a00c01d000d0300410a032442c070b03418020385449503004403d440500008006040108104480491080ca40101810001e060602c510442c4211400d44480707540c4440400c2610110400410001c0190400404126881c02e00150042c540310b003202640b0340300c1900e40100b1258151449101d10540b005890103104c0d481205486261139070a44005007262400c8200c5140341d0360f030080116440005418003101c0d502c0020a43c00360b44030010395006203030f20001280c4a0503440b103064005500d89031900c810301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 303101303 1250 303100053 303100067
    0x190603020a0c02091806091f0902150711010311030103110d11030d02030c06070201020903070308090a0b120604050903091503100f0602030307020615060f0c011e020d060b0909010501 80
    0x10115040c02d2440000d10b60014100c4041196000458203003280b50240c45441001902d8002d120080a0108600118070000804961520400c1101e40390350f25030080d9256000c4c01c0e403903007401c140c955a40c0c19440c201031841b0302c180103031140040d103040030007210030703048034240c90580e0350208a00603e4810319003000250742640105645e94a4683c8403030407599010081403103080c6c029000340d500e855050412034141500284050f0035640100020035090b0b4000c610f901c1a6548080307515119641100410100201a0460040c0900004091220071140c0098910404040700c0520148e500c00c075405440b800f074031501d00e400030b41c01c2c0103c45800c410360b0050b43d0310481d4038030059100e41c0d5981240c0c840113815400300e40540c000100340400d241e0305000003030b03025015076080b40c43c1c41441c10126901d40300d050782c0740c0c100c090084cc411490301021b400c8001d03032031007503404605040c1c0d103402d001009612200685c1000e62070208009240703502c4034280c6a103a040103203100c40d96031070000191660 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 303102553 1250 303101303 303101317
    0x3090204110408010c1b11010809151302041503020a05130b0301061e060e180a020c0703060c0306050409021c020112050703090c050607051e071701020c060619060302 73
    0x55200d00408118401001c0a480240000000031460756130321800a4022a0500c4800042e1640141800042405c04c407142079511028600b151080c1c3c3e0b000c058a00701407003010384804860800d42030019103070240c100300f09600c0c000c81e4108031030741d41080ea030324a80d45203100007504998000c0e01041645880d0110740340c0d0a0441c0d0000c1100c0307400400080c21941d00350000c0a8621000c00030503413030244418820080d1000781040480c401001c40001e07003082499402d03410842e40305e00000c1d00755801d50141c030b00e08012002210f1350345032a890b001000d009405010030019280880001d082d00e414019082940d801600192024840700d850010040500000360306112842c0d40c0030b400e0384024401c075403043c40c01e0359002513411000c1c6030200c00d001c0203902091054000788a640003050001c51541c0b5904201600850040c52407e442410001160f000c501180b01030b400780010b1070410340040c4000c0d4100c0050303400c03541c0d0306170405c0507004101ea101c4400419041050080c41e010394024000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 303103803 1250 303102553 303102559
    0x6030209030313031a061c06090c0323240c0a020708190203070504141303090f03050604060e0609070b0f0f04080a0b0703020f0924040f06180b0406030902 68
    0x280c80d05801460f50144000c1e402166010b2103c584c0619020a00c0d60280c0c004108603680e480f5400024080810406074032405031000e6a030303010a00030064880da011004680c01040303d135030345403082d21410300450103964140d40790096800303605003544203501c9000170f03031a000411201d80c0c0b43c010b1010501d40001d902102907105103000459003e004000e00c8071401260401d00da0429068810305062076041d9110901890602c41c8901c0d08001c0740e4900340e071015003081010341c030b60350318142110600c4469100c24200f40c114180401071040100d8070078440c50241340140440c1d0008141c0c40e0341c0300e03030454980c0c0c1d864101c44003e10450f0580b20050004000390f451040c105801d10055150683c01f56000d85000d501260b048020404580181c44d80140581001c40c180865010043c086110b91030145103e030790322103958801c49103000524882129110101034845407140348162405005000710000b10f1031202c02d914800100781b05003029511854a032906061402d035041c2c0242c1b009585c00c9034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 303105053 1250 303103803 303103807
    0xc0f05091302031305010b010503150f0301140a1a0306010b19050c16030302010b10050405040e030d0c08011d190b030a021207050109170615031903090e0609040309060302090303 78
    0x60840060001d140110301350450340456204a00e402802c544043d0030b0541405000d004001030b44891000500f88a10285e0f4805002103808000900401204401202220303006003846140c0d0f505501881c606070741c21111010305c001c0390080541e5038500740704ac030071940d07010854865054602441074600c4586818254206202114034506254105850050140c9000e9040013403541c2405150504032007903071020181c40110000410501c02c5001b05400b603519031030f040c411200f04204840034000c004800704030400d01d0b60002841d9010a02c1660590701140340640381e00c02034141c80c9801104080d4680003a0a01400c07840042e000b025421945400740c1d4800c0c0001d600e0703d04161601305000405403244c18102400540800c029811001078060300e409600b4010400003200340e002444042c041280c10f4a40b00043c3c03a10f41c045101840c03101200078080100f60300080d0710800d86007105141259550740c0014822135500c11980a00000c401c2d440401002d8044c0d40101886400179058034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 303106303 1250 303105053 303105079
    0x60305060a0207081e13060318030e0d08040f03050601060f0c110a03080d241d0406092a05010509030d0809031b1b0301020f030708060109030b070507020301050a0c0f0509 75
    0x300c5d0211204080100325980010034910f9001107002c040c000e002c01d400c040080008203010041040d0038000014240000d0403664445c41d541c40702071401c10350f84140810368864849802e40040180352000300c44500c900700010a031079000f00c0c00c1025000d2103513034107010054251943d03e0884042003071160440c0340d0800100116411800810322502c0c1c2440100e000d8482c0c6c041340d000da2020350910b40901540c1007047c03005190506411024206140b184100ba0302c1d5418894010500b20000922080c1074085074428201d103078001203462401461401851a5101c0064079248a002050390307060308a4480080100d0003480ea4981006104045900b81120001c4005811204196040d4950b00c41c803040c0090059907644110000307001c0d0000e608200400080000c82e01000d00030300c051161020004405900c07552120b0011a04108002d0040c140104090400d91248905901030b5081400003080510070340200080300d02c003503641c001c400c12040003c4803d0f0300000d20b034a0344041a40d40320 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 303107553 1250 303106303 303106327
    0x70f1517220308062d01080a06050402030721020306060d0c0e03160807150534032606090a0b040e1518010e06070f020f0109050304060e04060305060a020708 69
    0x401801d2194482c0807140c00c003a002c200e0700c05c3c0107541c18140386011062031184c0103001468203403000d000782003104543c2c50701c0c00401c029050b550407094000d44040108140d459014a821010020b40191600d940800ca5107801c00e03844101c4010350000002c21100da1000c074258011900c0f01c00c40e01d000c1c1040503000d00001c2c00c21061000700c0e040700504d104103105020050000324000c0a0207049260800100880903015000c0d030b80042580c0c1a044c62810b410011480400c1030480f48010040c601d4030091401600c034040f040203105a80103502603035410322151f04091030241d6030060228000e56034021707102000d801c0306e45c40c1541142d02c030400112042c6007041170714031140146103420040d10340701d00c011213030540d040007440c540d170706066841d40c08000200358903800604525115900c2c81e00720009074902400d107401012190700c2d00d10301400b8031001101920507074400d03585d014181086c3c107040009445050101401035007200b000720f1600c604607130042011f18483c411880c01c0c8141d50043e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 303108803 1250 303107553 303107611
    0xc03060103150e0604051c21050f09030a09090e03120103121e050405010806150c06060102070803040e010e1314060105040c031b08040507090e070f1517 67
    0x4407542140e0b00c01c6500c0829960290306508501d1038010040303482d1645500d40e070385d81c209645900c0c842e129501c04109a10414110b1a12850400301d28030648034018003000800c4100e401815484400c80400c850200100c11240c0d4840e0f01da0b075502c00c15051840d400024403030b1150a424612040191841ca4000c5524039802140184428002c2c0c105410003d410003200c41d6121035208101141c082515402109031800e850f42860b041c034843d42d82c00049041c46280107900c4c1d040d42004100554401c0001030b0b00ca10a0f1000e9007682c46269840c4849643c0780074a002e010005100c1400500c103116124400c9544101c101c44185200000c5443e091160803200c400503141c2c0d001a401800542020b010704290700505240c10000d0b55980341c0c4458201c008918880308120f00c40e0041014170804101c44000391410300c0040103083c0c80790000e242d548045109041007515a4080050014200c0c4000081c5868a89440254020690a25460355402840080b038400000b1001341c059110401d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 303110053 1250 303108803 303108809
    0x50a060f06110f01020702090c0d0b090411010905030f0a140307021002060703060b030f0106080702010e031803190c12080c06010b040e06040b0102030a03020f070f320309120c030601 80
    0x2910603016960b03210060400f03001020860040c0c3c0100030640040c1c07606441c25500c103c0e0b011075251a55290902c18000c0c1507034945940e071000d6407200344010311880e8600c16031440b009880d2200566601e10926856200c0003880d800c00da0070564086c40031800c194460300c40d280110060300c2c50925650700103241c1c0c0300318817449001a408441003160707607500340c89903078094100102c60074290302d8030a80784c40d6407510500401007044002e82c00700740311500075040541c8200d099010f5a0300d4590b8001440e00d444100c49441b40300c0c3c032445c00d003070980543e00b81c60500071a4000008450b454100640d42501d400303d81d00440d9a41070803c1041014035052041030301130000c5038080c1e80c1c1c1e41c0c03a00c603440d00c001030094801c5110b107241070364980c4140e07000401c07680c01c083d00303041c05600e6003080260b0b400d090003001409010309016214000400400e24440c20201d0b1002407940307801c1c1c0c1640c42003000706418807450b00456000300943c0055250049070100b0b030b45640c0c0101d40c41c01c039028000c02e0030000e0a074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 303111303 1250 303110053 303110057
    0x11107050a0b040e09030c1c0512010306020a1b11040e030c01020f04180c0206060f0a09020d0b191a161a060102010b0f01080a02032a030411041e050a060f06 69
    0x407605029414000d1140d0f0741002d41c00006505002c0b03444000c90302d8990901c048c902520203482e10303003440c6001d8419036014200d04074258941e5a543d003080390195100e822944c00055803a031038070304120000405e5203042908090003600111080040c803008001940505003284018000300b080410240018060006001c6405840300d16103c81107e0030b1300d040101030303c86414041104802c9a0001c0c029611801c210380e40b010b9030045102158a01189030840031005000040305d0b07900300d5042e003098031124400d86808055818007412400392403954010407003480e005611b005d03200001030303014140d082e030403d9031703189001580e17031321807a082091801400301e0914103c1000300e50741c3c084c8160090310200381c500000e2190200d000070085440200014601c42e404000706884485003014071030019a008504080d41c0908000d281103600212002c03240650400c840b52580e0810740500440e11980d801c2107502d9100c91104030016240c014000030300103a4030300b40040d1210822101d0b0006101c20703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 303112553 1250 303111303 303111307
    0x403021506010813030e01120c0302030405071215020306031603061d0d02070501050c0c18040b060604030f06020705010e0706090306060801020c03030c16020d14010507020a11011107050a0b 83
    0x100c0d01400a0540051910b03041c41422401c00443c5074514101844096052400f44980ba01c00300c010798604040080d14010750780b410341400d5415030150700450140f03002e82c04031944a0303074038190410500301807000140404101031401031404459009160000c0c2c0c018103071500c43e0440b0341e680b12103403955030055415903282d50861940d01f81c003520706a00d03a11140060300b00b120700c6000c06991001144a0181004030000e4080030742c0c0c80500080c890110000c1480c00451030041c1805d9441001340c42c1039810100060115501e86484030454045a500020000c11329005444c0c15000350083c42c400d4031f240d52520f00c2e000c481c48007400800060641521071f002c80f00d007142001000c88060f83c06c100020313031040140b50310304000002626444054180019542e441a89112440c80b40128000f0342214023148080c040011200a81c030300c00d144800200503030380e2141e0f4104c0c0c0d241880000078020330001800d01c9241c0d480f1f10071090b642d440c120100d0390819602c8004c40c1100b00ca80d4080e41e0b0400300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 303113803 1250 303112553 303112573
    0x6180f021815011b0807230a0b0408030406021201090515010e090103260a02030423010e1903020d050f06010e0903090d03030e010207051e070f09020f04050306040302 73
    0x4145003020008550003000c01c0749031400080c80041c80800031107060001c9286008a086244544038908a034040328143d100d00c0780340f40035038a2007030f500144201aa8040802072130002d000800300b00f000e03008084586c40b9260341d26001c20951016009a440729001c1040c0c014683c8081100c9008204011001401d880d0510401108500040100741040901800341a40d99070750b4000c00e054a0b000041d032800d645101998019588a00056807a012004a05aa5160380101c040d00483d820119803107071100c50b182c055550307104107003c05c074003240c0b0a0f904c1026a0501c00c034111030f410003111606025039203a4002a015042e52a000c1b5600d80c8822515561504240100c07030040101c403852960a05058406a80324007e90400e640100c0762044243c081c103101c0c0d0070101d82c040d8010f0086541e0031050520075124210080018000c10460f00a1003508a0010390ba43c100c60350201c4000c111030030300c03034600c01030340c00700d2040c21b0003400c14000880d0711354050050b00d000b548207030010080c1c500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 303115053 1250 303113803 303113809
    0x30515060103050c040e0402060c011803020c0a060302070818012c121203070c0521072f0f12071e080109020108040308100f080a03020f030306180406180f02 69
    0x100041c05131080000c1070000b00000307001410f52542141c3e04461031a01c030100310b10100e00410100d04030b202e002c8940100b410074150042010720501c4820344403040039a0711003000350300303034894400000c0111a04005401b540049494100b9110710140341024002c40541010014440720096181c1107600c80390f2002014a003c0c05034050418882014090074403030003170304020b107020042100003444080d01e02002084001e021084008441e09a0807110074018241a0110b410440d400c591148805201c0401445100d4130084401c22848800850301480803d01c0b58201c03001c0d0b0626085554080d40d003404030000d10144010344080080c0090b12490138440c1441610554000015649450010300250741d024003445d9015415080465564071070780c0c12880c000202c1e9100d07050890612101040700c40d408540112881e01950072142262910ba0210392a4071054038082e9011342010102c115012001d120568080e001d0800018a10501d803c8c41c0341180e080314084444400c030304444402c600d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 303116303 1250 303115053 303115061
    0x903120603070503030f0d020f030a091109100605070201110d030209010207090b03120702061204030206070f1817100207030f1413031e050102070812060303030f0c03060a030515060103 81
    0x4021001045814030b008013207601e9116103504000103642c00104216901d145804032103100f040c02c1c1086560346005070482005000d0800100d80002260b916020340f0300e0003c01203800352200b8881e00b5060b41c581907007580c1580c440082281808080b01c200003420704c06108424030030000d9103001d66149140d4000900300303605504181405480e003a02c40c442901c0c001882c2c3c0b80f0750305490300c1965607240c40c00055124042e4042c1c1c1110071040d142000304060f408079519000c0c086549910810b9840400142d41c08030030104506800c02080000708090100a046c2c400801c1451060352200c460311440d0000741ea001c0c3c04254041218414000c0c0800e0344540b2940451011805041c00c1003038541d000910440148806050440c0b10008080107210200b41c0800f5540e10100031507954200781b41010154202c004800501640c07400003e40a04003c008c41c1c5c40ba20090102404540e01c2c001055100e030800303811940c0000b003907c008030014604100c220300a69032156a054145400c00004050f2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 303117553 1250 303116303 303116311
    0xc101404080109030f0f050f0a03021207021609090b0a0c170c070201080106082401030609020d140a06080d0c030201060f08100e0d0903061a180f0a09020a05010305040f0506090312 79
    0xb00c503444600a001c3d0b400002d8600340d403c642a200e50750489c1044c11806800780f180300c5880d110343d01040c0a08150005032000394122010542d007682a40c4020308401c807031078164003030900f00c180e00029006804680c08401c0e03021040c2001303000084043d40955661208898546200000288203401d540c6c03c090458010515803619442c00d1903e001183d40e420040300240b40032051040c0380c115070b60b00a401c464041e00303110b10110344541031305d214880a40340c0c07501110640e0400c000412000012406400243c800620080c0f40400041304129811a003440703080e8115581c1e410b020400406d413002c0d607402030090b5030040c800d014200c1112400c5416103962a00e00368840044080f07810380115411044941214000440d480c110441d0210340b01c1c41044e0a034400d5520040056042210b85941e0040040c1140220a69a602d040c0c500300c0e40e0b0004040d500c244101010416984039400269019100e44605032180300242d4416162580c10b07250786005030008102c4035010f2108180700d0741e00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 303118803 1250 303117553 303117557
    0x15041a0a03050a020717030414010f0227151e0f07050c100801090f1401080f0712020609090a1b1e09030b07111906060f06030b030c101404080109030f 66
    0x140c5503842d590806e0007111001c811100c5c00c0c3c01b0000409115140210081a0400d50000c2c0452185002004000c3d8041d2001a0040080c021000d03142030801c02400c1c07442401500010500c4190385205000303402207400e1004a0180080d004051803108020308204400c0c60070240d01d0f0892441c00c0d504244803840d450b07000308050685d4010b4290301505d0355044580000c00041c2e041c030031452a0001e405142c40761807400f0f050500010700781e5000240c80c131801c4481800c0e2540182c541d0348245036085106006503210704240080d114a00c2c1602e10550041c03030300540010f090801108100840580c400c4150120350400c6440b94100884c0c21a080024103d00e0b081c4052070451342e45008201c8080c0119081240c03440500c0b071281b108002a9a40065101c01c3d03401941103480c040c4040c0c0498041c180f000c020064000800b240a401440d2030404001c025104c004009014080342c004450032200402c04445a03e01c10640e140c2c0050024003004000486d0f5851a8100502210280d40786401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 303120053 1250 303118803 303118807
    0x30b040b0d0210090302120703030807080f01030303180b070c06060b0708031303020703051006150309020d021002011113080105010509090d1d040615020709020f04030215041a0a03050a02 82
    0xc2596650341058195580c1260f403142e403001291800c5464940c00d42000f0f4204102081c0340608001c001035070340440e446507a030a80d165855042c03c68000400303032100f01c181205200103200180c0a50803410300321010101c100310001c996190310216180a03100040403a01d594400024000356004860203030400b091480e1901c1c506585400b0710348001170a11a440c03282c18044420944280a110020368000707088944600351003c0b03c2c8003e1036240700303020191124001c11020319009000b6880c200d42c000340900e604503116000e00064170900fa411804555031071040d0340c3d244103000040d225040001c2c0d084240c0710f0074a1062400c4801c180c00061042e007011081010000000a002c0c4007112103240075418200c412490b44007040a50a005521038180400411942206019013202c02e03116401c50343d0542e550304580c0200c0c0b040100e1110781030360801c414000f41c10810190320b040c2d188480720b43d280c141e68401d8015140d908002010007620001520004194107010351504407000701d038114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 303121303 1250 303120053 303120071
    0x120f0f11030406260c0c060601030c0512070e060301080703020109050a0b03270102160b0f2e0b070f03120204080a020423010906080f0303100603110706150303030b04 73
    0x6559004501c601820007900d0701300c1c6540340c0441d484080741e069641c180030069041c051010a415000802c0752400d91066000042056100c2d00078020341c103449441d8245041d541d4901004000e070024011780c00d2005a02501c42c840d00c0d01c42c001d500824000019100c45c504510006054400f140d004d20310078440d1070b106001c4070004c00212600300b018114501e800420100c40c80341c80c0469144111030759480443c001441500038010b4000312841441c00c448030b651403006082c4030040a035100c0e001145e0750050502c070062000300701c18081200009040f0303e02c0e0f54810495040e4003080e4212040c02c03015180d0810590000e000d4100c00c5880300701503040604102ca802d42d1648140710192061752501c2c11110500144940c200840b58200b00031541581c4400c0c2c00805803107140f09004040c495044007104e0120044241c0b800f813841c0402d0041c003d484c01a00305c0140550300600d0445150400010740010400c1c0b288084040540304000010342c0b46007005011564080c1d070f094000c40c01d00d0892 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 303122553 1250 303121303 303121337
    0x90f030f0303090f210901020f031201050a0b0a120b030a0b01030515161d060417010c080603010209061803070b030109290906100e03070308040504110403021c030c120f0f 75
    0x31441e170452002c0469290f40204004070320f0f118443d0488031030f1b17010005a8420706c0240c030400724107890042d600c1600b6696141080030041c804c51205200084004840b158108813a410180226900608803a0303906007079100c50004082c20781c000c4560368011480b42a8400800703510070b41c86880c6c60507041d071222102101071301c00b000c0cc2c2042880480c00c11f50b07550043e03541342c0c142c40282942052078200c1c00540a036090007410314480002c041041d2034009496881c05000300c0710008806042c0d42d09000000382ea415003012040b146503814040d40c08042107101d0343c00d02440c002c0800c00784c042046525280c681d03201c2c070011480e44d03024080c074101c9621585c503081540c94200c002511030078650940c014048444a030704030041a410300070546e000050000c03502c058401c0e10001c443c2000811095442c0b4642c91041d0710009402c0369080704090001e030725096403100a58005e040c503401c007804a03540c0529a03030035545000049a02d441d081000580d000c1c44601d040c1196090a05841c4012040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 303123803 1250 303122553 303122593
    0x190506010503010e0c0d09030c02042004090207021f020d08070503010e1f05061c270f03020f030406170901050c0d15120f0b090d0c0206090f030f0303090f 68
    0x8484000c146407000c1424419170703008072090b04480c5481008180042d00d40106404007901d011f171b2156040040c83c000c1010841c0800d000850646003251500e45000212000b9401409090341d01c03000748cc0740d08800e0000a510541c41402d1680500003000c4820340c0076081001c05080c2c2401c0040c14401030082d000038014444e005810043c4851400340e801d00000507020640d00a16013004c00030504183c0e0003000039440e113072101c00c440140300c40d440411400418840070181c12a02c03145640e601030100c0c052040480303600c0d01034410788403c040303444080385c610307807065025900090504001031106000e81d80015000380c0e564000b409030f810006c072407221038010b4201601c18196540c1c0202e0340703401811801c100910701074180340d421070003604103004030403481c6106845030b00406000608101c0045448040c100140e00d40254440994081c0010b50b04a0280c0c1a080b9624800c400c101c0e5404216801d41424103400465030303841d00b0324849040052118104801d0307888080c03551010741c43c0400d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 303125053 1250 303123803 303123809
    0x3020a0605060d140f120708040b09030a0b010b09040c030b030a0b0709032010020a0308070813060e0d020f0c150c0114101e080624060a0819050601050301 68
    0x201080780c0d12103200084074030100b10001004044026030300746102d03c0101d410307103955000b003065034114414803480e80014030811a000b00140b004000c240000103d070030103007680280150031501d0700d80441d40c0301d485000c2c080e04006204080410102c03a0741c0351074002c200c0038500c10301e018400d800e10b02002c0ba030ba035441c01000400500781c00300002c802c1d5202d814807500454015106103c004045001e610b00e0080c01a41c07607004503603680303150502c6e41c00065540b001d143c0c142c0c3d07080c0da04d60b516181144c41410140007000c0c00c80ca030302180d40104020740540e00c0c0c19490003000c0d10120044580c0030385449000342020b080d64222558080304c0d40d235a03604404090040140d21a5140b40461501e4010f14005032003d1003801100180441d00d42180d00741070680d002058894000007813003003002c2613080c4621403a1001d9000d06d0001301c0e840e00f6903406400c00002c550a40c20021100b50000d4083d80181c0f1101c000521044100800c524812000581024082800700304034181540028200e00c8140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 303126303 1250 303125053 303125063
    0xe010e0d020f0d03080f150108010603020d091208070e011d09091006080a051005010b0406030f09020603070201090201031d0706050f130609031b050f0103091103060a02040f06030903020a 82
    0x15000d80250340b074824001444000c02400014644803514001c0c0074200280c881c4d281d0b205449000800303502d00c80310565078031101616007920581c80e1040c118081c0d446a04201d0703009442c0c4d0ba000000a00168250241d4011612001e841c1c3c58000f5006082d000c2503240103040100c1d0458600e030043e074511205810000c1aa0030040c16603a44c80b10501e801070383d02130190800d01d0210001094000810540c05891161040d00e080008200755482540ca0078050b54500e840200420098a07002c3c0c0d00081486201400228580d101d40d00020308170b030012100f510142c0d440784010000c569140c410b82c413815080245902e403000034285804c0d52021507010b0401442070003c0e01008902200e0162428003640c13252603151140c8508009062115038481202c4a8000090001c5c450f0f0702928048240c40d005001110001c185070011009410600e2007520f0900e02d0381002c020701e40b402c0c44103a02c00d07400498090380d12842e2401300c2d280c0070260ba208104252134640c5260010780d0201d103038801e054101c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 303127553 1250 303126303 303126319
    0xb06101409010e150a09080616110f01050703020d0b011103070b07110709061403030c3d20030c040302040f02040504180c081b06030c090d0507050a060e010e 69
    0x300c40181c4640420b98003441c4c1c80301c01030751000004c0b8403e00c0101008941c40d41c868010f00c2d51031b07a402c0e560368400c0d9107040301e10440541e003a800c584604165100d03920240201d600d0b080030000f07510b0841d40143c4031000000d400099142c01c00341c0c11b004041200720203203040440c004c030244400b44c41c0e00514100070200700c1d01d1008624071a10400404140003002c0c400e44001550b1504d841c0c3c000d00182c46442130111500c8010701003072401009231240c0c0c3c201200074042c840402c4801010385106a2102e03080c510082c00400302141c8401800e402d404010f030000a6003190143c0719030f0180e0310440c506200c040c420010000414031480550b001c0325415203003c5020100720020102074040c540040350400d2414011403006041c070022610341c2070042030038581c8261034082482e214a44010460121311450304107417101d00340b18000395803000d107040084c4c0c180500b61000034002c0c1e0501d201911340d5444000240203615000c040d003401000b1074180a6808800b107400039210f0004198281d120b6010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 303128803 1250 303127553 303127567
    0xf0312180a0503070b0304050105060a0305030a08060301020c16170604080a05030604090803070302030406110c0304051c120809010c210e122b090314160c120b061014 73
    0x1070608010007500e001401c0e03481c0c00b51030703d0420805c0d030404c45090341c5940c00c100104210703003046034428003900d42003030103940b400400c4881680c07201d00103403225400d50350070001042e501806100380342d40c032801102c212110a1500ca1448410b0040140f507420a0f00f0102c180000100b0750b50407034000951604180b0303200d5403a940000e004110380342c80076194810000c104052740e589a03000310f200e5445030104026441790104040140d0048007144501a44100410700c018940901b44229003108501140c1c4c40c1e1649994002d69080501000b0001c41c01400512800d036000780290200c51000303240c20001c1407849440010142c205c07131030310b01115599001c412070f901424084031501541d000f503403c0d990003e201da80340003050282e55152040710761301200c0003940300c0750244110b51501035842d41303841600c00035214016800010481481c00c401c00303505000590340e40d10203006100c42600c0380e5070701a103410540c0c01100000c0c066031198090300d00b00b003d0150803900c0600b43c3c0e0101802580c490034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 303130053 1250 303128803 303128809
    0x30210090503060f011e0e07140d1b110109020108011502030d0c0810060302030103080708030c070f0609030e04090c0306020c01061a221206110412030e0f031218 71
    0x50300d0700015050702540b4100804829034040380c41c100c44411840d007111100c0030343d1380b11241c44240917444015860802082d6454032402c12072040da100f01d100340e45415030150561089500207404400980c04d425441000c2ca42c000d0740154040c1a449c000340403004281d4002880b1400501903440b45109007004800494420402d85100c841038501c2044020801c0c0030290082008840400658170010320106103a0711030700036217040340d51214100d8107081d446d90ba00300003038100400c000881241880000f02046407a00c03400c030042c1c0111000941e84c0000c0c00c000b06000c00d82c1d036589003c4e6042c90755a500042076401706404032500640b0051b1140f03000450103001d451654000c0c0800c0107081000b00039403c00304001c0a04603020f59003580903110380c4001d01c60084841c4254481d5070780a0142901041e1a41c0100d40302484441482d841c0c1900c4141900350301400700019030014010485640701d5040c9541483c02e181d0040b03008040d244000c9400c0d00e000d220721442d0380c01c100e4000050030160b031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 303131303 1250 303130053 303130067
    0x1d060d080c01092d0507151107060906120b031f020408150a050a050c0414010e0402030c0d1104081f0b0a1502100213050909150c0a030f02090604030210 67
    0x19074140000d02c450354143c00d14201400d8042548400041c84034480c0032104554520002056440005081560324000b0010740900204002e04140f000d00303184101407580c1400400c01402481e00e981c0c0703040e03050500052078102c103120701141d014903040020f60310355000241a960b81c80c241801400340241c29400802038051684841c59510452403038070324039500070009611881220808000c1599812014002e4510a0394a034580403070401040c064012440c5d8201c940c1c00040c146840107224000108040703900803910a02020f001184050b062002030080c4200d8006204c5000c1c1820b003815085500c810300d04a03090850041820b00300c0654545420911883d907008007110b00c0c1d80d0b6110304407440101c42e40100d00041c060312101d130340e10361543d03c240c8002000549103000802d00342400d000301c00c0005003c009141c8114042500a0072001031010712840107013842c030761546100d0f54094260380400d0482d9050a005011107105a1a0203050b5421a03030100c40100b1070401d032a406880503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 303132553 1250 303131303 303131317
    0xc03060801051006110a030f050a090807060c050d090602030a110c090c0903150f04120e040e010b0a0902030f0f071215051e0901091d01150e011d060d08 67
    0xd942070100f00520002c4004031102101d0440e150000380841c4202800d1b15045d00da20014003207025940e040e4035241c8103a01500d480b120f50f00384002566210b045061070100581e100390b001075200f800e140c0800006000d200c1c1c034600c1d9424100303030250421001a4403402213000300800c12400b040980c0e811181040406043c100c098042c2031740c0d060045030403d00e0350020300c84030700030300c40c1c1c80c16003030100d55140302e0341d01c942105160080746403681d0303031242e4046481c0300480381040440f0703104500c680c0d5144904112001032a0002543c901c000c01440305100c62540141902031041c03007089a03182000701c401c0d074080d058610016156581038000e45042101d182021481031400a42c401c0c00c00c035151041d0140c400c100c616410207a00300c40c04904410204941d15000721a0304010420f098071500544a1840c07050071604022001d104040d01b15014080d4501c460b8a15243c1040240c0e6180504c034054040d81104c9445003c6c0b4000e0071003038040240081d4014194a81c1c04804d0005d40e1041d6124 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 303133803 1250 303132553 303132569
    0x120c140c1005040f020406050a1203080618090610060f080417120c0d05060901050d02041d03160b1303050a0c05070e010803190302181c060905160f0b04090c0306 71
    0x1d4189810882113010000d942240541e103441404952480d2007440c41c1c0c21903000c0c0e0214100410950703022902580081c045640110028000850b46258003141714401c25604000341030f0351420200e800c024004030380c4148140044000c4c4081d105901c0b00c0240c1c1d0240c1c00c00498034040242c529607405512540310511600488041071040300c41c050401020400c101c0c80081c80345407648410015500c9080c450703a81d01984001c45c400050030540c01070a04142c400146008130081c1c01728890859011600704400703038144118002c02c00040b508101e0b0007404a0201c0d01c1a060b072a94050954814480345000b03010b8612a80030801c1410040b420160124410040e480c2d65a041e03c0780e0b03280c100c204801106208001c0308a0428401d10130f07102d8070300719005c1081e48c0c0c041c40000e004000c80218282d020030a00d80c5c44a401080881c000c000b001d0f48079000601c2007000c0d614564603801c800d50000340b0782d000d01d0b810030411040c4880540b000c1e600307030b030500089001600c2025401400d00d588a004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 303135053 1250 303133803 303133811
    0x10c1812050a0605100801110f0a0e04141609080a2609130606080703050f011202060702120f120705060a0e0a02040f1a01140a0e01200c01120c140c10 66
    0x83c0c41790718944210845c2c00200080c07201d40c0d1021844815402450100e1441290901480c0f082c188112412013035240d0280000071058044070136001001d0b01211100c40211800070101d8045a211520300010309910001d080d102c0c1d26551076481001042880c403003030462920030780d034440c00490102c0c0d140c4240105004100c1116802500c00b07080c0c20300c100c0011405890000d841c00740240a10307485072039000e48406541e03090a0280740040c44180d0161b800a5051040000603241c1440800c144500308004040700700042164900d00301aa0560100c54901408000b000401c001a120381000501d2000300761040c00385100361070403004040181d0b0003800c01c00c41080110b00c80d44840d00111000010140500254005450b190b0441e02021901d140401c050551148146082d01d481c3c81c05141854448011518040b4443d410b8802c0c40c0c0c2da0f400c050020404c0d5038001028035003000340e848051001c0910a5006032840003038041201c031342c03030000a00b03428003442481f41c3c1400c800070b920200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 303136303 1250 303135053 303135061
    0x12360712080d060f0e18120a0302040902180a050102070614071712040605060402040501020c090703020708071a131109150406140f0103180609030306210203010c1812050a0605 77
    0xa02e1140d640c8618850501e142d40422030186c0f550903102d00161340d0000401e410f01d0041742400507940901c02d5001016801d0001180107800c0d40000e1511084100381c03022006140c03030802148900680c00b0606550040c402000610b80042000d041c001000d00d0440e214845c40c01c105a01c6260608540c2c0681c400081406a10651081a5000c7d40c01081d0400030744d5201804e0004901c101d0040b140540d01130115130501e40b40c0603a549502c10000d01d8054280710540e500e032440c942200c2c40c110303841c6111000c00c03100030007001c15050f480b0180824020311881240c45489441c0c0007541458000c0c10600c0020f8984040d00504c203803c040c001c3e1040014956458201d0510008241c50520903000301d05081d045610074012006096058103003030303005c0e54a640d5400c0050404120407814543c5400000551464584081991710030700080b2403010b0600d0300c105421503040403030b00418400c107518000000c6980340000420b41e1490100800c45082c0303814998540104500300070000da003800c0c100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 303137553 1250 303136303 303136319
    0x80406020a06050609060a12080c0a150f02180d0303110315010e03060621010917040518010e012105030c071706011d060612360712080d06 61
    0x10a014040402c440d454404c1004910401604c090b903200900c1c410600158202280b54000d40c1d106008851130111078010007030038201c01510949101c2c00c0700003071a481c15114096203004100140c01145400e5035043d8076045010747d0360320075001e007168210301c2c410903000e54060b648500c400c000c842d80344e150039001c103650742c0d208448043c005550114400307068100002c015000f060028a13910f00040b5452242d07101e50391400c9090440d648580c21203004c41d00190b028145081c14200c9950b03903c2c1007009001c00c0d026030310202d00360b0145440c0108190040340c00c0c41c0b0f06444100e1403401c0710309160b40340349284012424001e0070a010004a01d800c2d010001440700845020301507a040c050200c0f80c086889140074400c442219070390060920304d88001c600101e611980081546052000086058280c203808444080080044c0709280c00d182c1c43d00d40c142c5503001c00075070200e0300c2c40b41c110000548541080c440e030301030210002c413a80100b01030f11080d541c0e40c40701407e0130880c1d25910101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 303138803 1250 303137553 303137563
    0x6150306060f1a090d1a0103030207060305070f0f050a200d030e0d05370201151220060405090403051908011d06030f030a0315090b131808040602 64
    0x20300c2c002d403070344004005010503c020300c5921031106018007609061202c0f0034460300d030403681c20403521100329991b2a103c070020a0b83c1580070303500950040c44011304100f07001e021264054149001c1c02000403005418507405802200400c84a262103504c62103910f20548007182800741800c082c2c280ca4a1a040601c00028900c40d0b488081c0d5040c00851400c1154a4440348034060660005108004d03185c0320783d503280c00b170814455003c1240d600b07203e0048035a02081a00032138240060351582c408640180c800c00c0302d04041c00304864400c80d180041c0c0d5420089404441000903003c001d03900c10240b954448064034001c140c00fa040680d02c2c41c3c42c0c40c0080c2154854a02c80494240c820a0034108501c00c000c214140c4040c140c3d100c42e229200d51ba0030011120081107168144200c0300840320303441060019085041458402080c1c8a541c4d100f01181c981d21600007991ba5407030078414480c0c594510510101c40c60007010001a034202c403d03002200c3da454034801604e0340740c0000b0001252580014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 303140053 1250 303138803 303138809
    0x50a0b09041a010c060b030c0904140601050a0803120a0905030f03010f0e010302060702120a0c1d0a020304030806060a0201230106080a0e1b011112130e07050301120615030606 77
    0x142003080c40d4000e0078480b60041480c0380d807400268000b180b000014440d03803040c000200020101c429102c3e0840000d2003000c0c2c211000c072070007100000000303100c050401c00c1d0741c05050121a1320703100f10300300081143d0f0384c022050200c01601c5001c020502600c9154040072416401c035066076070b2070501801070f140344da2081c82a009091500007001035aaa0105500c0e410390703900134281c52418a0329020800c954a21048074000d40c040c0e0103140000aa0510828009003482409031001e0385490450b010040d400620208009004008020000e544035144550104c1c0446980e0740704d0740c0f0024122700601e156180255200c046030f988007c001e00d0388a140307040700d007240e44103600d95807024000015141c001c0ea0504a55010340e100811403c49590801a440c0d010301d070a41100d040c28400c1072a00d00c000580c00840c820008000c0c1402d108141c109000d0480161004280e06107200010101e00c814494038075040e440400c2c060420140d40c02005400c0c5111108008450302d90900b8401408684 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 303141303 1250 303140053 303140059
    0xa150e010b1209120a050a0201140f0a1a0f0103090c0f0b0d0b040c1409180c0301170607020d05030c0705060a2a14070215070f05071a1e04050a0b09 65
    0x80d002034003c060018a01c0b082d41c0c3c060503558180141e60005503071a80000d40300009554032940b2a80040c1611404c45205030b41700c400004142c101419903030b04443e410204122884401981c0c0d010a031500d4418070344160080ca40080c0c0c01106041c01c0c44080d12503000750f50120408000002c1d102211000b4001c0b01d041460100f22041405041208403040c0e0b6012001180c004100c0c01c4001a801010b05075408016050203200c46c10040d0001d0b001c8030440c1e1810210801200501c00a04070031755400300e628203000100101d0034031a202175600c0240c400d44c60204100003000410701d105040548a103142e0020442d04541004001075001d8103440300440d09190303098000303a003034a174107040c50310745100907880e00600511402c00740b600c9503001b00c0040e6045109109120190103204d802411294000c01c403006e03150340703603140682c200178859000b4a00e41115425280200800030105c5905801c5114044050190080680c40034000c035440780364017480d1040000f50b00d420b8003000340700c1d4040c11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 303142553 1250 303141303 303141337
    0x304121407030e0406063f1104031203020f03010905070e0a0e04050c04020301270204050303040305031b01060302010e010c020d050706020f06010b0a020303130311010906090620030a150e010b 84
    0x240780b0491f49a20080145085001c164144c10003c164034408901d01841104010a41c43c0c1964010303819622180c482c6904c209000804105100c03840307a401e8880303951850254a0483d642c412208540810f000f00851980c3e1640410401c5010b146000c0740040d01420881e50b2603910303103642454000480e0240d44900800c1460510f900e42842240e042e22283e904008144030941107101046500ea00c2e0b14401d142d00f0000071885941c05c00280004610480003959641c0f001a11145401207414000d031007681002000d1005071381140481e0000d0318280f820030075805039400004c1c0d41c40062400135055025260700071500640c0131400030001d5894008458050b640d840100040380f045501070b80040c2c000340302060443c4115046826494020b203014244070300149001408c403400c07140304565a0b503450300d8080c00c0108a0181400540d498501d0301007943c002400c5800e2880700601105d030850756610741e002c91400e07280d030040242078608400b043c0c568444003100f1041d0300c01c807051120709840e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 303143803 1250 303142553 303142559
    0x201180321300e030d09210c080304110d0606030804080d02070503060f1305010c090f0905090601140d080c1506100507061a0409111002120304121407030e0406 70
    0x2c04080400840030b95103000c0e501500201c1080d0007001036402c1d4407400d0100300a0070f4090f000a0140c192614055542e01c10140078400b098280e0200c070b2606201071081e502840c0001ca401c444c01e60340e0141c0c0007040c03c01921a01000034072218000d680c010000e6161250100034010004041d000399001031080b030ba01c0004c03800040e0390321100c82c4134440d8550700c6240000c0003589040d86080c1c00c440d00da008002400b071181e4650782134400030700c0c4150000d0030716803040050103040039243d4014656050100200d0408406c25915031605002d81d43d65020040320040740ca8031501501201d440c0c0003070319191110b540000f92a242c1e65803028003100c203038920000c1000d502c2c05a0600464071243c1e140e00b49019401e03074504010700204190030b49403165103c4030b001ca94a8a0090051840c840c80301750343c4030f000c0042007017030b0107110990540031035029140b52040902034400300c2e90404d8101c000000420403524007125240003140c01200050303008540e00c2c00b0540c00907070090340088221001d1060680b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 303145053 1250 303143803 303143837
    0x60601030603020607140a02090a0b010801090c0512090304050a0305010f0f0203070c1203090c030f03020d0201020f070f05010f02040b03040b0f04120c021f02030403050f03160201180321 82
    0x9002c1c00040c2d8001c004010701400a254148039140d00c00c2d0180c2980d0540c40d042d00003031000f50080f01c1007828540c50b01c0d007100d0a50b9101c81c00501400d000c0380200300f0114100d200800300e0045a0040807448032110201e456481c0400c00d0720000c002c010069600341d9240d103086800b0703201154084c4925402c06090240000350b9000341c030b114158542e030782c2c01c50301611340f41c28031004c100003070790f005050351010f40d8000b003140003020340003a500408051391100340d41d1400038030700520300400d8001c41e441403004e030340700070000000c8420468000402000001a0741492801030000040100368a84001400540702d035041d40514800e50003100c0d090200d43d92980c60010b211805c4400400b000f9460326550003450003001c40f582c0650001d040c0d03504004920458076121195801a40302503400440d0030810424200410790a0a175540080d41c200314a00c0c0346407661000d62400241441449c540d8161a115500788960041d900320128800b02103906000d4003004030700000381400500c030540c010012075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 303146303 1250 303145053 303145061
    0x14030609011a0118030b131e020f060906131e06030204030201081305010f06061808010b03211608090f0108131709120114010509010b07030813050f0d0206060103 71
    0x6602d810b0061600d251004552540d480341c1c0365422401d03140c2e40070001c80d1115a440e44074400c01604e2013007111040c2410400500080204004013071b0b50320003100103031541c004030009040d05454181d00d0b402840002107150040009241c1f0170300d1011000203142131f03418046811010107042e542540e90302c64000704c09174803031404040c3c0070801c0c0c0340100c0c82c4801e41000302c2c80a140500c0c0001590322444e8095010340752140d00c0400040c20240441c44c0303030814440d2900040c51300a0007001300d40c8548000c01d84507a40007485040180451241c0114140180103c59a5006000d44003031811602d05e0261190b810505040d0b0080c180c0e0a4502c04a500820a140c05804207451480d0304440c6651461a50b2014010a4400082c18081680070340c458010940703a5402c2c0034000710722900c02a41415208505a01440c402e81d1041c00401c0300c003100c030080301e1049800d45010301081e07490403801d81486a0001c0020124811465060b461300c4011602075140e05150307095810640f1040011000d903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 303147553 1250 303146303 303146321
    0x40b01140315280f0b0a050303161403040302150c0d08010b220504020403030c05010f0902330a051c0b0102151b0c06040512031501030b0f09011403060901 68
    0x908a40300101d1901d0b41030050000c01c41a40c4035800304051250000e110585444403610000300c1d4075204485c656141c119040009484194015030405005402403078004082c4e000141020b40181d05280c00d503a410f0045a01030358002d840818805c0c07500c2e05501c030b60b9000002c034648038011010692041c07481501101d048038613245102d820440b44050000e80c0100050445c0c0e0b51448440000496840d0343c006000114020b445100b9456910704245007502e07030043d01208050314003000c0e1001a03840c0c1c3c0340603448008040c0c01d0b0402c5071607090500c03140c10699030100d01500c0c0118801516550007801440c0c40c08000c0000c0c6170025521404000340c86803c49036501582224242d6111080400700b8145e0040e409020902080c00c04c032114100391f03201b501d891146030040010070080c41400c0000040405228981901e5490940080350709003020070301103810162107010034055542c40c001403002c8410014511409540e4608013400c40403801024240640141c0d400105250018841c0d8000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 303148803 1250 303147553 303147583
    0x10303030b03010207211e12060b031303081e13030e0102010b060a0c0305120403020f060106020c0609060a0507301b061e0f0207020117060d2306040b011403 69
    0x5005044942850a4246c516908022111080d81c64400841000c801e6514480d1940c00407200c06c03890101c00d440090300b06203810707141003080c000d19000c02d240b0f800b492905454016201c2d1a0400c0c2e408540f41c450403007040f901104810300c03516080306065401b00e00d200b0340b50800e034050818010fa00b0307280386080b0f00364003c001344010b403011030044249003080d500c00c0c5013491402d2181c100a02c8600029030b41076006074000440c07500036142c10400107000d41014001420042c001c900000c02600c20a45000e0280c0404641d0280c440e00038015100003039840b1544400d0300040101080200341e0013601c0d052501031010f03403407500502480820440e10700e4009107403541011600d82001425083c140301100d540d40c0303000c0c0064544148a161541421070380096a034081c00d00004142220050f5130310f5140c81014180b02c4650b903810f03a20034080340c0c4140009915483c01c036010100442014005c01c80f80601070400c820400178101842c181c582440d00900310b04107502c240344c1c2d81c100040d80400c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 303150053 1250 303148803 303148823
    0xe0708010e0705090a150807020601080c061806181c0201020604020d020f090702061906060e010804030504120528020d030806060409060e0604060510020c011b02040212010303030b03010207 83
    0x1108421124005500c0995030510030300e064015000b01790a200e40c0d5211042c03503022550f4a055641c3e0282d40d6a400003000d200400b119414070001e02e85401c02006000d02c20311001808480c1588101d02c541000f000c000c02094540d00c032403044420350403180501d544142c59031400309501114540d000403240b501a401411140d0f559820f21003805502c0f41c080e60b01c204010000c103940d98852654601c29012a070191905080c40780d1510700700802c0760320b04902c45003014801d11941da03010103c503101c1182460110311648880c203090f81c881c822500400c500d032a01c9031020051120000301d00c0c0d039485032082583d5403001803070f03840e02070b000010700700a40c043d0003c6482d0300440d101e107542c0380c2c100c00d005006914050b0713118407044c21103180c3c1d4401100e6030750754410071206117058420500101003c0d61341c101e4901c0300c8440292901c145010050501654921040c60703900100c041c01c2c042940580210758604a41c002d12020110901c17044002904000c40d1802d40e08045c0251744a071131b4400c152741 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 303151303 1250 303150053 303150059
    0xb01181a0c01020a200a020603040303020a110106090c08010e0126071203090503060f040c0b22030f0c140a091d010f0606020f070315020f13081005010e070801 70
    0xd400d640340945460030318401440300d904480000c0c40280500074181d100d0b02d900210340d01000300f00021039400c10002e13400c50000d00f00036844120440b64803641c186001a90703543c0c00401a5003042004208030307050361800802240303240e00784d030296200881d1516002c0403a070740c6000484461409029000c01281010042480350f810f44602a0544034140142c6101c540ca0b60f681c0716540500420603000545048030821032801c0a0000507003200048030190040d1900e030311403004400d4284214042c84800251440c004008800840700400000d1124072036683c0e030303080240503080007a406a5030500032050005540c00c0c0034810040500d0040c0066130864a00ba041000900320307a9200d1021801c040020725080c80c0030300c039041c4421041900000d13814108200240340040b4441291025800841d00340041500651202134941c060702c170140c2d03600003e85142c0044d025603030100c600c0d10b440c900d003c1000e00c0040750011030300f51226810480f40e130740d9000c1c4c40c005113030580d190400b00d50140018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 303152553 1250 303151303 303151319
    0x1410180e07170a32010e1b271b0304110d0204060b2d0a080406090524070224040201030f1107030e030c010f021504031e120b0118 57
    0x40b00480300c041c4241d603038042242e21010040034103e0103140344c0700341115210600a5031101c282c1c0940c49180300802220001b41e20035940c2c0c0c064040d5400c85002c148001035859070f14280000d16041006003011503000000c90315180c00302050715107214040c0000030707000900c0e41007819284030b01c0c0c01150410036840040700b402004103000b542640c02585600011a4181c0200002c00c00264266804854900c400c202c052981d0402000c89004e50020018114065801500c00e40c000c0c4d000000060546480c0ca0410300e401c210b4001141c802500924180810680c81c072003602c104081d4003501d82003848030210300d03450702c1d07900580d0b906041c100c8040390255100340c2c002c5072444549200003484204881811907550050700045001035040303c10044203080a001d48000c40c0000e0824924018200f030002e0b40b20b029100800c8607071038141001809051181683d658541d070860800c624030583e800e00109403800701c402e000801c030304040c11042c25500c40d0030b00881000018071002040303418800e01d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 303153803 1250 303152553 303152579
    0xa0203040503041a0d0b010302090604090b030a0b16090f0501202d1009020a0e07030207080a110c0a060503070c050304030b010b04050901080d080f0402041410180e07 73
    0x94885100c02c0c440440c4d56410546869101603000740880e4440c0e407456201020b66801c1015241050300620103006107441d0f800a030b41c291100d070301c808251104c5000129250410200f8041c1c06029040c0c00d0003415030078400250080503d40d5070b0100d40e15256904d12030b501890348110360000b02c401d0b00b006036121201520018045c110300542d039040c20443d038502c0601454803001038080081e500ca0745c400040400251040a602440074000600180c0024181007401d2107450405d02c8420002107510348258102c40c501e60b032080d04544c0700c00b0710795002855030312150502e40903441150b0b100c0d04607281c44a0484121441555130924695038080110b4407010301100450b0340e44814000400020303035841c0154040c040384000760323444515040030400b0701c40043c3d00c150a90b801010700501c00d2640304d000c46a1089d007000c0e4031000ca8a0320b1001c17078010306401c400d80b00059211414030001d40b2101243c4001c80348082140d502c1300c00c0190300c1d07004540000d0301c00002540b0002c030800a048895071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 303155053 1250 303153803 303153811
    0x306100918020c25091805070504021e0c01050601030608030304120e010c0c031407120b0403050a05210106020f0708070e10031205070c0b07080a030506040608010e0a0210030509060a0203 82
    0x2090b035401407813804c014000303902940884000c2003511803091011a116104551801a001c1c822000c6008103840c3e0310340700c1d0103034020360380950340029050340740c03400f20340c40802580c44081440740e841e0360880d40700d8000c040039524240001c3c02c190002510801c00410340303010310b400c94080005801d4501d4141c3c1c80100302a40c035414803000c0130545000c00d00741c8140d01e00446c014589281c0050b107074050141402c01d2074014884044644000350007007584540c40c96841b56140c14200e0350b402d10800280e072a4010942c21030140717845400c0d2500000b0740384000f681280c006800321200089241340c82c3e500c0b9025800342100307a6200d61804c1121150f92602c198000f248050000d050039101d0b00e918889200364411400410300024242c8100201058000e0041038441e1125040039015540c4160900ca8444a90209a04d480202e503880d41c4581c001d000034440e202c020410700d0095440340d601d400d01103009a100c1c103040c040340705041c1e000b40175103846a0740760000740c100d560786d0b00182d40081d08060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 303156303 1250 303155053 303155077
    0x10260c031303030605030a050a14070e0c0a020307060f150512030d0b0d051c0806010507151e06080d12110301030813360c020d030905030c030708030610091802 70
    0x44000145c64a007800a480106d00a50150041248904100c1111480302200d51015031110900704240301000042c107400242045840b6a5403822000403403450255040282c02d0502d0038403020709215840d0b01921200401d070f044506115520010081d11500705100460660402c00c5881c0d0003d0080d030008140b0b40c1c1c01009280c0d030b130826454540c9440a007210145040b9035191000c9400d176088482c403a40010309191842c5010042d690386010048a106612501526001c480340c880a0403500021034500070031042120b242d86182590b84d4804030303080c3ca000700f0715100c0d4103201e41680b402144031600750809018956403850b07590504590101d03200f0403440c04004808291070127005210f07050f84150851049504d50803004a10f0340844403001c6038501e500c0e140300100e13110380206941c0c2c054002410005481c01c200c0c2012411031050b40003070540360100040410401590704061405808180c654a00070004c0010648041140d03010720f00b840e000354900300c01c000107030360000c0c0b03c015421 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 303157553 1250 303156303 303156311
    0xc0a032d0903061b021b040f0f05010512011517030c0a0302071418011a0c0f0304060323040b060a0e010b030403030e03070c0302060d0e010207060902030c030a2f10260c03130303 78
    0x23480c080d000c8410410030f0303290880e15900100014540b4029600840f840d060080123080c42001c030300683d010151149104004000e081e0a000800510a4640007400c240550710410001d24000b51500c401e030041c0c0481502a9100480c24104003405403901d4585181d6803516900b002103194400100104141030342c8030411149440741410312074010b8403980480116191410300101609590324541c20180323400c59400200d00c0c40020350074041d0820b400002c032280d50b80310a0082684401c11781c0007001100700c1c0d0000007404415240083d4403e5000780d40400003034640f0b000d181d0303c9200d52180a04451145041403015141010042510111041c00014062814030100b42641c000120588001369503550301030130341c1018010b41c2c07252a01103000c1c1c0503510060761001039045040c0d0f281c402d0041c1e201c010803210943c0741c2007191540b100908106000a100500501001080b80f129001c20301c060300203049078090101c880d00800d13520003c182075a444d510398610600b0550410340c00c158071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 303158803 1250 303157553 303157571
    0x106140703021213120f0203010c0809031e0f0a1106090f07140402120103080a09081c080606090d0822140d0c090606091403030c0a032d0903061b021b04 67
    0x400c50400461b841001510300820035801010300315000d4100d010240700620301080303000038000c0b00300c4a140710301c1e02c0250582c0c00d680d01142520b010b0302008901500b00000c21000b0035400c40001c510703a699030401c0798030759581c140300a9182c1c4d107000041c201c2980100382c2070002c0860582400c48000c00a040103003841914200844401002ea0043d00d84d16000641c1200803507110030302001a00707000e4001e0520921020780030800d2044404270808009000c00450815500c0c0300494603e1070000700200d071410824180460654004107010a04400602840441000c200c1c2d503003007103d07851622108442001000d0101004a1340340485e41c070313019a40301081180c203510400c00985003982c0d541c4509400c1c903007501d550031410ba414074469030042c030265441140c000750703100d1440d41c145401c0701e815000840d010302c04800c08200c402d803400311500c2c500c241c581c4038001400b100c1c0035120600c50780102c031068540300500500c0160050b0003000e141000b069094000160780da00103040040e000b01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 303160053 1250 303158803 303158819
    0x71205031611010e041103241503010510080907030213021209030406030b0612060f12030a0305070806040b0d060c0504050307090f060f0b03040b0c04031a0106140703021213 76
    0x201040121400d919011510455580c44400c1c04c1140e00262020070900303103510f8072500b44d40001052004601040c9078240300031404004c00b110b030302030040d00703001c42070000c07200c0070b505034100340212800b855000031122212841000c490340a131080e03401410000313040d9000e12410404c1040c1c1104025020402c003080c840c07038242410b100c3d0f81ca0001031a16181407100040c1515501d51010303124041c00d010741c2246001e103202083e00040300302c602e6880b13044800080b03180b125403604800141e00010683e004a030303406420641c4640030641d10050039603240002c100407561006071032a04465403a0175140003511940c4111802003860034040c2c01c1c41d66881c0002c0c83e01009401c0206c0d006e03211040c100324000c450180c2c802524905500c1c20003142008000b14460100400c040c0c0800c1400300843c42c2d0034071039011140555001100400b2044e90394038a6000c0090078800c400c0058400c11310700c59100c0e0704034142d4a00650503409002072024000e5554620780054480c90f00400d401c2500003a055 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 303161303 1250 303160053 303160087
    0x2070b041a0c0f0f090102070b0307081906030b04060e010204120c05030601060807082e030605100626091903020607030c0201331a070512070507120503 67
    0x3910600d26001e0103a001026441508800382404580000a01031080c40d03280c298295040d041005660300e032241d0307000c40100e10300552988683c9030b41c8000000d00031392039444244240304031aa02c10a43c202a0007a01800403106948409485811424041000104181c104030341c00e050000c009420035071254005e4080d0154440c0c121a0b0300e0300035000b00050f003024490180101f005007030107000c502e402403000e840240010b0040a00c50b1150034210b131030342000c411041400c050000c50071142522031402d44020b140c199580070350949800c1d00000d00c03503c42c500d241d164074044650170210451a502200c071100010b0610b4403507000f144200c49686010703600d4078551b18025030060405003800070019040303d0580681c0000c590405807580410160441a0742880e490510346034404c91070b40042441e4501150014210813813801e0104001030240702c098617241d4010001e480c200c4041c00c040140e280b0a41000030040e40244404004101501c0844101c050244054034503060b40394800740495 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 303162553 1250 303161303 303161311
    0x406030207030c050d020c120613030c290105042406030b042306270c0705010b030106030804061101050609150a031202101d06041707020d0c03020f0a032402070b 71
    0x16402a01caa00302d500d062414050b000c43c0410140501e401c0142110700d00001402024040c01781440561080040c10469000d88500710440c540103c1c0540f41d030502e51001c00c0c4542441581451038042c604505c8200d803854009144007479040091400e00241d0250034041e40203540913540703d61003442240600910129a442c0070070700d11ba2444c0240400111000400480000341e048070303103816060f8041034006d034100b510502c11544441c403070b203001c5025000c0100016015420070100008114420000e00290380c82c0f9111200e007411000c004a080f00d4049904a9018014502180c03499040e501900a00c4401900e160051910780c0c43d1201c8805c1c3e100d09010050344039010725556021244605801205001c0f0742c1c1d4030724000f140d0095503d11f0080c1000d009052003030524541030024208840c94140e0213041c000b0458110f0400601403003803480280c2c02440d804584900900e00030307480d030095903030045800c100c01401aa00003000c10760303005000041c0e0307801c1200d000801d0180391043d00c0b03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 303163803 1250 303162553 303162557
    0xd032d090510022e18022d01050d2306010305071103070f03030b311a01030c0201150b0d060f0f030b0702030d0504050607140c191104020703170c09060406030207030c050d 75
    0xc856204e1040c03208104940d01c0c2c4a60a040035000b1102e9180f1f036031070108260304246842c2c0e03104c00d604518000107015588424241c60322200000d4062941d403180c503441440240c0302040340d0765a00006032074a074503031048203c079030300100a010b0019080150f40028180a882c000031422404400f0030210a00241600da4048c0e2501e003c0b18820084140346c940c0c6034417000300703000c00050640d19104440948004d1818152618444007e091007503100d0806c3c1078484a1840c11782d540c03160f0600c01d6900907600b02180c11b05000b004204d0f20901003105045403500b500e0002547c0c43c6895010070701c3c20103017a880442c0410080030f54514418014903001700d00900141c80e01c2d0a2194000d44040183d0f10f16010f510390901016104405c04505000c0c108892180c0e004c00101614040100c940070f4071034254840d01c007207611418140c7c40b48041080440c920102030f0941c40c4c10704c2c007402c2805000c0320203901420800c0103101d40c034800d8001e0724526102c1d04084510040565034282462244010400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 303165053 1250 303163803 303163841
    0x80f0c0a12171e0d0b40060b0706050105100807110313090e1009030504051005070503030403020f1b03060103110f1026040804050d032d090510022e 65
    0x100c099003138170500701c2402d0b0445440b04a03105090032110351041c0ca07100342d0b19030400d414034403d005400120394a540b0401d0320003040000c0c0c0f20701c80884075070044101960818a407000114407810401c01c821854281c5071584d070640d6840402c2140c0168810015800c0c6000601c20303140c0300808101041e0140040da0710102d0381314441e9000c07904d00762210004201c5141450380b01c401281e045030445098800a070f45100781d215480c0802d0310148618900203049100001c02c0005041c6d01180142003c0040d07015074075000c40350300c200c000f0b424510950683c10313000000104001901c42c2c000c0011204c000d13040e0f50101c444100010710000c50045844089440c1d15030041509405031004442c1401c074000d44010b03400c090303e44034000e01890041c1c50181d00d02c006400d05240c003904211a095000c401c500101d01e510451180b494906840742c139011070306c0004080354502d000d00380140c880c5401d0b4002d0005101e0107544e4804071a00129155040b031811481c100e03a034202d400b030090100c0c03404000300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 303166303 1250 303165053 303165067
    0x210110703050a06051609060509010309021804020a08060f0c18100906120218060c0102040b070f0506060f010c020d260418110a050d060b04080f0c0a12171e 69
    0x162100140616181c81c004d6002ca43c0342078000f0307c2441600c0361440c101d6190703410100180c0080240500203544040c11807060350798032482c10a070304e2040d80b09495403800c86548418803a580e030010b0301c03452500c1a00c0b00000da40c44009402400340e10441c024a29040c8668030082407007503000c00703103400c00074008030000c0c48000e803c104400c02c0b1800c00da030300310310b4503103081c1540030040301542c003161092800142e00000e045094050310081d21000202c590f40d27810324640300c0520340b8004812580b034000c00c40052103600d03001c1d410000320f2034180c5038101090807541c02c01100e5058030b907040354501e85403c060010107410f1080c01e130f0a01140d001d400da0701d60070070302c400d4151500340249002080c180b060f00050380301018141d60740f80036542001c0342c0b43d031075181500d03000d00360b82d4001700d10303207800420700140441d40001c0311549640148269000b901e00a0140310b00700b40c0c2d50062900c4640720380c01d07200000b03440c5201d44940036045682503082403000c480640b41c010341200c60640c2040e0201c0d0130 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 303167553 1250 303166303 303166313
    0x20d080301060f090807050d0f060f0606091509050108010b0a090e070e0a0b03090a080c0f01091a0f1005010e1305010e011503052a07050a05060a0e0a0b01030210110703050a 76
    0xc0002d170400c1c2004003681d034a000001003070081c041000800b48002c01034000d08002c0140c105481d603c0e66918288901529100300402e03c00c26445482c001a0324036034000c0303055000305250b01c00d5400682d0f0f003c010381e0811003c60000e604c4107241004024003007000040b000203584c1c2103801061550348101c170f098048010411180d03c1034120840a030810002c2c800e40001c005441c0c101c1503070181350311392600308850380315060000c440302d141d100b0b50a03c204c000030444188100c1d0140c000084c1c040402c2d0701c56150003091b4030300031120000811a850000c2c4103d600034600c1d0401b60340d0040c0200c01c100c0880715942c0945100727a02030160400305000600070740c040300c002c562210610381740c200f1107458010424188d105c3c044c0940440f00b010105401e102c40c0b1340d40c2c11074845907001404c40e9a048841d140095807140d084800c01d8180d4a4000c141e1030000f008140050181c1d08460215420703400d5400300800500c41c56000f2082c84034007040e801c4e01d200e05104e10f0000b1030080010f0400c48002e4140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 303168803 1250 303167553 303167567
    0xd030e040c11060403110f10050a0c0509150310170609011b08040209060d1a01140102070302151605120c0d050a080f040c17010204091d0712020d080301060f 69
    0x1c81c014061a968108902074001491503406505440e1405c00d8103d464601d40c1801095161101b043c01581e45000140143d900080d00030001d200c010000e68003801c00031901401540c001903804003000c82103405412450001c3c47e00205150b20305004142c0c3c1c1e58a019004540100c0c50342160450b000f0804002c00030312546026400c84ca90385242d20f40e10550041003c0c000400080c400d1003441c0c0810a03a8603281c40b4bc455569001101307810040404a5079000315400340300b44620b945d5040584021544080790300c80132030fa40a01101d02014801044015036008000020503150051840c030380851800c0002c20f09411988074010b54591500344c001d400e0806110130041030142c00c01103040c41e95400044030fa4482104401592070b91520700c1d0441c018402588280d42005805c104107a4081c01036004004079489203408020450740a5090500c09010303501c060065003040c9400c020780d040e54081040c9442c4000c120240d180d1840d5503545081d0001e821010000e210102d8801c11203410000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 303170053 1250 303168803 303168821
    0x530010605220207151d030903030f0f0702030706090303020106060c0b041202010b0307091e11120408090306010b030105011106091e010209031915060b070f020d020d030e04 76
    0x402440600d007030502281d0700c80d00c50318036800d90440010788580070212540c10f45140641c001850b0807886040310b01500540f0b5003042030400510815039040201d500003045a071109005405103013805040b21461110717420a4844c1c1500602c2046050300580e020f0181c80080c24182d2540c4103c0c0c1e0460400a086444d61b40194050001100700d10012a0315030303802e00d62250380450000c01c070288140c0220302500315410100d8040c45840808140030440343c0200400c400c7ca800f00c00c103080a809400f006a8819490303416030075104010203091600301140e1281e0143c0a00d80d55481c0801c80070220b881c00700300741d210424190000c0010b114643c1d2244c40110b011590740010309580c1040047d17140c94032006804094541311004411070186029010b45105031001000c0e210440303c8500c80c4004081c110004403102803045900d40913070b00061040e0303030a41c0e070700e0755040d410a5103650340e40c0000c101c0500c0c00c0c0e07401965501c6d41c80060341c0d01640000806d00c20390b14544090700200c14081a241802 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 303171303 1250 303170053 303170149
    0xf0b0a0f02010c0219260901030b0103090b010e043e03030a0e061c0504050c03190b060105070204021225020106060c020402070609080f0c071401050a080a0605 70
    0x10f4a902c2d69075070005182d0141002c19100c20700070380991034030780c82d1108040c0c1d50901c2800e41e0307500040d0382c0300071a01502c1c0c20b00080e00c0510003001c2d0400110700310341140c00c0080000803000c00611401222045050b4082c0c13040c1900391108a04040787e204a818480b0382c020b07880c0c0e5035130000341200e44000301120355000c1030380298108122410040e0101625214443c000c0001150102d103268442440880344115150100407600309800e02c292101790021340d40d4080d01c1010111064070600012220031070390040d51a007400c1d143c65004441c1c1354010802a47d1013502840001d00045202d03500c5802b4441003804000d0501180c02d0000201c2d072212450000c0da49000420094540c02181060846904507801a910003140c50600000c001e440000f504090001c01c4615103032314003100800440944004131021140d450050920f4001007501243c0080d9040c02040b4002c0e00403150950484c0c4d241c1c0c0701050361600c40c0041211100280701c814082c241c20608207400d00c100750108031382c440c100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 303172553 1250 303171303 303171311
    0x80a020f06240d02221104060e0301051f14220c020606060307020c0402090303040b030c0301030c080c18070903050d0203070b0a0501050306010512030d0908030142090f0b0a0f0201 79
    0x540014115000d1170407440c20429800d60b10401030072640c0c0c4100c42c4003640791441d42d200c07074075010700078080c03c100c0b0282d40c040d41c03810740450365480c3c1d210700f05411440244103050020782012168030980900c0f0101c1e40d000814803448901c01c1d501c02101c0103291074a400005100a0300c03580003481d000020b0b002902034901042031100c1540c0c080364a4908410540d0003503510a00c40c400701e4910301c9968409001d4541c00300074001d0907980b8034010f6048a002d04600e10b00c003034860745072075154460210750503840242c0e000311b0300720200000c2100350700040030305020342600d50b03a0b00c5490415200810110040e007000450304100802440d21f03907040309a000c01000690304080100e90381d007006000301c0f032040c03950b82502c0780d00319020412580580710490b4184006842031030107071040d41080c051664000c1c071000d0030751078020b83e0290001003c0d0794003183d801840e029600301c42103620782d05000020048010b0f40402e401200621810003402104a001c0c0c0e1a4a030b417900800500400c240301c8216418 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 303173803 1250 303172553 303172579
    0xc02010f030b060d050a061a0f0403060506040b040e100e060105100804170a03050a06080c13020c03040807170c01020703030c0308220606151704080a020f0624 70
    0x40440480c0300300015050026208040500180e81c0e4051608100030840c01d1600b00051040c05800940c202c86050113a078510060a560b01003081c041d510700c51081030802d0000700040350260304241c0d04088007600c001b90b404401c001040030345107189102403003a400700c11051070500c0684920450040320002811955040200041d00954181d00080810146201207014040c42150031400040d071084d405503190000c0d24040c0107044101e810308007040c42d00100148421003c80c03103519844000f0308180034800b000c40002d000703420184002025201c02d02001ca130507030080002c41d020348a070703414004002020040c0729182600030150f03a411900322410420000e41c010501e828025454101460700755514403600300500e086000f921200300464142d1001d008a84c3e1140060b5040c042c210301c45030031500c1003503900408000c4030188048401000902061030340e409821400c89601c159441c078003030564020301d411400d4449410046807118250210400b04504020340e06050f03400c1010060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 303175053 1250 303173803 303173807
    0x2705100e1014070b0c090a031a0f07020d0c0501061206050a060b0702090a180c030b04021306080d0c140114091006060e0103050402120709020d05010e1005010507030210060b0307020d0c0201 83
    0x610f4100a00309605900400c82e030507a480b080c0d030442180034040e0303446136540b401d12a44501c064900340d600c4001c04404590000c0695410341d2196001d50014084440f02c01e100b01c40e48145900140c6145d5030b80c07500404d68003440010f00d64491701601010449040840300d4800322603050b8016916074208000e900c006856070099198010601180080c401c02800d4003214010911000100f10b031400400c04001c008400d00068016070081d10043e03080142a4180400c46215000b10b1945501070030302c00b003070280f18451402200c0e11840503225180c0d21035001c60700b07440010b543c1010408049041000d030000411684201440c82401841101d140c1440904030080c400142810561100002400e5403102c003c1e1442541d0300ca4225525580d540c80c01c88000e410004100043c2e42c201800084d0b0305850715501030041411410145c13156203850015525680200012015170041140d40501240140b065500400c1101d03002e41d03492404500007400d0615520181041c0f0071640764800150b6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 303176303 1250 303175053 303175057
    0x150303020a0209190903031a0a060e1c05010c080615031e061c051b010c0206030106030e150403020c01080705160204050c070501020c0c01110d2705100e1014 69
    0x960180e41d075003402e449110102c89044c40340115003d00509220b2042e0070940e05a108400190040d210010084040d40c2045100a0340703124140008104000c40e000d146030101201c000b54042c080040b00c4407103155201800e503004051510003045240c0b0400400381007500c080c0d00c3c04070f960f1411502d10b2600c601da100008080d1501c26140c41f0315440000c405403202c84d0605c001d45502148082c0001c4149041980c42e60350100358441c0c0000f44150600c130354040c042c6c1641180e03008018508582c2441000c400401920400540601c501038003140d8401c450144107004502130390150808020420014004c2c1030043d2060003048020030282140c82c030106540d8484680c1220041190b84900400398014081d1010113003180d440001d501d0203126000501e0848500e0a0f242c041205a40c84040768640503140d00c14002f161400ccd010b03041c03440c040c8208800010146c4d1824200c282c650380854051092032080a0202d001407042079241d140c05004001c4221541c0750200c039800100105134114 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 303177553 1250 303176303 303176323
    0x81506100207120201051b070311030c0105041203090509040f0620030402040902220b130509030d0216080706052a04031502090402220503010b0d120e03030c070501020115030302 78
    0x410400b165002c45e07100d40112004500814020003d41c02d2800305039480b04850302c003c0312821032007041e540b22803c0c0420201c0b450382d41611a14213061409801d01c2c005118420210100403030203401280540e180010f080c061b901a088c01001e510443c901082124144c80d580d100007004846600e25180e0004109c1e0741c0254103481c086440c101501c0411204503002c2a4007000301090b82c030000641005030b11041e440340b0119032004520154560b4002180d10640b903002c110b801c20030090400c0340582c0c00800c00c00c6075101002d5051013160304c0305866900007890443e000c64441081c40341c02c40041090b202d51041d8101240d045000040078a84c05105a20004005481e20380500441c0c20681d41922103584001d0410344d51403541c3c198080440b0001d5000984050845001007070908052156403d01c0f00003904051200c80c80e615901020744026030050704000324080342c880c15031014405001980341e0b4800a10000e4100030019081d26420703e509904109404d104001103540004e1844c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 303178803 1250 303177553 303177569
    0x6090613080c010608011a04060e04030c02010507211709010b0f1e04110915090108010b070f02040c030f112802100c020a020901060503090c01031a040501081506100207 74
    0x180d1086000140e0262800340d100300c51703e5103401003420503502902200c0c2e10415048408000349a1a01c02e43c41010350140c50150004004c80654001540240000c041c40c034050044420f44004c0c1c1070a18a2140b020b04440001400c0b01a82c103407200c0411004540000b0030307d000b8030442000c100828031140d035644075948070308048100600f80d0002c4115030654a40040d0051005061015800e1003d80c040c500d294042c00003100d108070703d59401da0a039000a41c050391181116441c0c8030480206d900003980c1980d089200c8010840144e40702d104030111504140c401107201410340200504440d8503503500102c503201001007108101240c205090104280f01c10580102c2490404a103096241c6191045184c90302c00c3e0011602e40000c0c000c4d90700d074800c4071112201ea0b280c2d8000c0700c40780404e07104400c1952019224544942c0283c00640004202c1d0140140354100380000a0580d6000c0c3e1200180f9048410309054402d000e1700309550104c010348060080f2500b40200a40e82c071628450440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 303180053 1250 303178803 303178807
    0x80f120901050405090c0a0f0822060e030d05010302242d120108010501060c0f0f0203030d090605091009121b020d060518070b071b090501030f03020609061308 70
    0xd103580c0610b0644016250281882c641c2c1d01d0000c69841441d40420a0040490301e121090705180c1c1c8101d174090b21035013a00200d0f1000004c03061003040b441030002012100c1a403a81d10306048880f04002038200142d8248000c503495143d4010703c01c0d148410038101c56080324405400d00304645040440d402c81520600c882808404406041c041c04401c04250080703000c000380394000b9040c04026941641c14440003007115136600c84094403c0900ca040c000c0c40100151403410200d0800e0b11407440150019060f2450000541c01c031800311424485c1c1210303c90b603284248240507900b042000301c3c2415095042251403102e0305c6030709481002e01048010062100e00b011104c110b030310f560429241d80a442a001d91039186008400741108031014146100d5400d43c503e0901b00c001034210440c0c2e100e00c1100d24240c21071320350000f03032810400c001e01d600d0058140001c0107101441218021401384002d4000b00301c207854028200310010b400108550b010f103083c4512400c5016517184020380c031100040d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 303181303 1250 303180053 303180067
    0x706020f0d060b1e18150a08010509060f04200a0201020a0810210510020a050c0c0d080a14070516080610080715170f06030d1103030c09030f0610090501080f12 70
    0x11780c0351a80e040c40c0d030004850702246210007026405003503d901141ca8140c010717030701e5009004210318101c90300c1d030307200d038442c0d0484595003001d270b1000c02c0c0249042201e50b274409201d5100c0e20241d100c1100b070b80040c0e600003404c4815917440303080720760000e0415040c640c0c218640b095229911382540180e154801503c0101810005c040028000d00840c0c00002d54541d0359a030000b401d503800180290300e04d4010083c1c1019130b80343c030303105501d111580b0800181c00c003608a4012504402c0b10403019031080020045500411403c001e2114105010744122090a040254550400101400c1500802100001840310301e0303011031500155001d40303d01c8070085040140840b4160342d003480d840e40d458900c0050011000340c000c121032259205070704803a0803200e05242159503643c246960001c5400510119090422a1000f030a099200408488444d28040c1c3c0880c20460161803042d100911800c007001542d0603400765500414914001d04030000101d25460340f1024010085400084005040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 303182553 1250 303181303 303181327
    0x5160201051c1a0a06030947041211030a080c16060c08160c0b090c030318032e090206040b0703031a060304120c080706020f0d060b1e 59
    0x25007601034003038814058a805040811090560742c43c02c5030040a91020100c2c0d06400b1b406102c100550100c0a5940b54042d88000c40e441c6107400e0b8442d9200404060900c02e200d2030540d110903030f1a140070481414140b40c601030024405003413140052059211280f04808804415218060b406003010317040382c0d40b100c8400a540c40340c94040c0951103c0c45001c0e40c144003240d4000c200d00d071b49648ec0c020340b540b6a040515021065101c9903400203200c0002d460019841c010090341004045003202c09000c0c0d0b160000b42560006d000b142e841d8400d9003c07010300d515080000c1e0034488002103050706010502200d40e11504c906242502c0d035130b0b40321215a403c41d25031804030750081c00b2050b8503035201c03104c624004020301405900c3c0030501d24408240e00041c98040100c230b010700c0c0d000c01c0c00704031504591810380d100107580000b80e507151810b00c022310200d902400200001981811380030341d1400c540c8001c800321032007034021185512007401032071071540c80110321440c0394085441c00e544890110400e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 303183803 1250 303182553 303182587
    0x60f13061404030309030201050601030b1311042718030804080306031c030209090f061014090a06200718110405040c050702010818030703032a0509010f0516020105 72
    0x2804071a80140c60810003419815481054001d1295000303001d1a00c882004406031000c019007203a101c2662034048244000e540c3c8003c13000138800200d142869642c5051101100949040d001346c0203810001e80d8501d030700c500c6000d10020342000e6410391106107440040c69403a00500080607050008082601543c0c1000070468100020006130181c11005c40020042c0d000060110b0083d1300240200b442a40351042030340c424400a0294442c58082503000c0318001c80d2101c82142d1a00300b040f41e200c2c540c40300320040000c0c0600b502c9900e00d40d01c08242003408108000703001004c54005600a10060070040000003c04028545c0410050800607402c4034610031640055805031800720041b5540c1e41240c050074400b4003d072142501c69440804192031262440d81020180c4c00c200407043c0040d000b1b03440041d5060802641d8030002452254000503095041842804100c01080f01c000c07070340c2c0c04441002c0200462808508009910401600c0340c1400f400c002e040c0b0402081c1c081602c0e01840f4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 303185053 1250 303183803 303183821
    0x290417030406090b0c18040608030a0c030903080408010501030c06170414070e0a05180a0507051e0603070309060c032c03070b01060315060f020312060a081e010b03060f1306 76
    0xc104ea910308201d0081c140c6035200704800c40e40c0c4260b00103201018609441000115010701c8040e618200449030201c1314155150011824030079a00e0700480071400b1400500003070710308540001519415070810050303c400d1b0781c1c854002c0000308403840303400c8903200e110560171a0b440500c140b0390074504030b0704c1801d044070754220f408044020020070600c04555006140515200c4983c0340d110b107590411182c0b208451400500f150703111039010011410141032081c52544034102d0a0313900e1800000140c0d043d4819a09080001e0b150184502805043e100e070344902212030404004060f2200164100c540c4078429200c8400d0007141251443e25041c0300300c41e403460740300941794415a146c80d00580102084c162645000034421000b250940c044c980084000201d60000d5003030010140041c040356a00502c01354010182441c0000e450808100520400610140d0240686400303140c280c01c4443c3c20000320700c65880700d414071039011140301505401c0540c00440311318141c4241003941c05099810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 303186303 1250 303185053 303185063
    0x90904080f0c0102070c050102030702060f03130606091b0801051507021c030801030b0609070909020319060f05040e0102070b040210110a1101030f0506010504091a03030729041703040609 82
    0x2c1516031080198002c1500a00c61351011407082d450700300481e601d00030140700941189040081c0c4025050180240d035200040c2c031086280000c1d15502c1c0350130343c1e12a500c4010000e40399440e1074010038840d078684200300c1d550f160050641d131401d000a0080083d1803205120070000040110664652650f01302a04218288440001d2004d142c01411840c0034030055810040c0c03140442c540b460106aa240104103580c2ca8240c00c600b4412960001c0d440585200403151509890340991450350207414014564180304403805441d0009110507503030782141c1040264410480580002e461203081d41d0016016680b00502d4507009805480c2c0b000b404020f40013601c541480c9000300b090000b86018160b00a98040c01002c0840c035070482520700c1a0ba00ca40485d4042c04113004515680d44842d45038954551054000200030001ca800c640c80031400752090700800d400c1054404910741c01c0907040c90b140040340d003545846d490340080742c141c04240b1003c8290004c0402c003030002c50303081058810f0b002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 303187553 1250 303186303 303186307
    0x906040e130c060f050909090f0a031d06040807120312020d0207060c05030f220b010b030403030608030f04090207080c10051603110306041d070602030903061308090904080f 76
    0x2249661000303100a0760844045003418070109101d40b09092821516060362151800c00c1448401c00001090040680e6068402c1c1d05a0180b1504204404040c041c001e0300d610b20110420b00104121010125401d0b0040d00c080108000400001500e0130490b41000c680381c5001400d49800c031000c2ea4030b40750408402c2d0010a42090002c07465005000702407040104000010007410140e400b03010440d0520a1403140c880010003803d0400d40c009110404911503408404c5580d0780e4407135000c400c2e04500501c1d40d004c020003080503094800c08001e080b842000b903003041c46190b0004441c0c0700c0c0b8016602407540103d0354500f0803e440d404da0b00303012110780036500b101004c800d51000400e411142c070a00c001e2020103506625000344100c03084003807281003c5196607242c6040c031000c0c00010350340031514407003032080307007812034040c02818051302d03040e4090359540091340d003010315100f0050708a0000d03240c07601c50300000601d41c0044804007101582c148010703039120308000b040c034061160301040c25100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 303188803 1250 303187553 303187561
    0x519050f07060606030b0108040b0f09030904020c060103020a2412020403080705011e0506060406051b0f0601170705010516062004030203120301140108040609170418051006050906040e 81
    0x1a41c3c1024099616079a41040413080385001151500c41c290b4000d402082d0443c045042d00c1c00c0103204a40c08400001100c8c5800112000300702240e014203d0402d15400406c0144114600750300110000c0070300c400006860324002624110110b030154a5109122902456001e544115010740340110740140b151902c031034950825a0191903807003c1d207525844c1e1b801582c440e0b1940e522800d4002d01024000c94141070602d04182c8490f031000200112402c02195002c0f0380741810404401003a9545018180652500d10400c21880c8250ba4102c125007185800344070b5a6840001d680342e400402c2c0c88050000384504150004158100002c0d00c0c4c454a80700c000d81c2980c0303480080003140c1c403d604860400d5031003104004107000a004840e0004540040110158071468003a40c000c2c0c040c01000800380420307519030140c00740a40f04c00801e140c02140c10407092222000b010401c80300800b0270b00a40c58820203d80301c1d07101c0350142d001848404142c003032a0784c0b2032030259004bc0002d00303000c01c06428 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 303190053 1250 303188803 303188813
    0x110f19020715030c0e0a060e0f061201090b090a0b030d0806040f0c0518030601050904111903030e090a05040201090501051b12090306010605040f140103090501050a0e010e0a030519050f07 82
    0x41204d58100c080303a404000405c8500b440c3e0801001c642040da07039091009604400c0107088400c50304469800342092061028440c002c0741514020108170600140303030351010041c00782880c0010111410145010a8044192800700e082031411070185000381140d03a840d40090300521746034a41c003880c1442e108102100a8100380108040c071391658204241480d61070405a41d454240941e80c1c00c40030100110700000c406a003001b07a400002840410025211002206032f50403640c4182c00142141c0b40c1d0311558102000c00030342256500308107001c1482d10f0b8001034104e004901c00d0504001d000940503804642e01c020102c01081184180e90041c224803001c603195800104115100380202d030000103499004ac1d044500701c0303411250305001246010001e210105405245034107140e02c440716030707001480030b10440b031050084090005440042080ca542110601d44903000203602c40300c41000801e41100655140d181081407000034070382264400c0300d0a001d50100905003003008108041001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 303191303 1250 303190053 303190061
    0xc010908190212100c11030c12090a03080a09030b010509042105090307060801033c020f06031305060115020a02060d0e06010e0f090105041703060a05060d090204110f1902071503 78
    0x291680d038a46c100141c2c90711400c0e449204851429869a00810303a00c0341c07507101e000180204031401031240d404542c0c5c0780c541e005180d110320094000100c040030180304200c9204074840c00751409890600d85807605542c0c0302d0003040d803100d00c40c10307504107643c000504600c140211341c514040075060b10285070769050041d01545080c00b00319002e940807095038035048411a420401d004030003942040280d001c510000300080d5510044c0e0308051140810326041c0c41e440d00840c015512100d001130740010b241049400d0081c103801035000c6811040c44501090350000d40c00e103006404680d060781d548090b0001c5002030002c20070101140c080c100000403c05812010240725510174403480c4d903e655244e0f00d00742218400c48000b440820a014501d0070150b4102c091580054060f018000c920b03201c100107400c6400c4103500c00c0d036658940c0c4240d0118101402212500c20741e040d071007420b102101c0501049030040ca44801c284800201c01094507a00c20001500241000d00e49060400c44450b0010090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 303192553 1250 303191303 303191321
    0x322120e1201090c0506031906170f070e0c0f0c0105010602030a091403030f0a0e1e040609050c030a09050717060708010b030610030509210a020c01090819021210 71
    0x5152201d80c6010520060040c4180719600040d02a1054101000c01015401c090501c06156440e8900440081040e01c6410068140c6a40c91186414000ba041e4904607121110391030b030780c1100e00d040295a020180043d00003000404194640314400f41400c600d000388012100c4660130034000054181d000320082081d91503654aa10b00f00c0c2e21400780202e41950802d00c603400d50300400080352000d41501c0038041003801840e10103c00c01c1a9400101100d0900c127000c00101c5d0002c007015882d2030240310701d030010043c00c5010b112900e40780300403800c5070100800200509403942a5007040280c28450500a0300a48900f8581d2030401c410281c3c3d01d120131141e41c00032a12040000c641c01081c0c406481c800c1c5402020208545a4400c0803405024060074440cdc551041e0900c8412440d00e1000174000d040060403043d850b1401036000924000b04240700c0d0381030050b40c181c00d11101d6000300300c031041082001440710302c6540d1440070466081d205d003225426405070142e03c54100909402c50303548 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 303193803 1250 303192553 303192559
    0x603060603110a180203151207082116021f120c090506030403180f091a300717010b0306010e27070e070203030f07020703080322120e 59
    0x2007184a4083c8070107143c5500441d4080400200076407281400c5030000c6900200030304031755040c00250008143c00018180481070315802c94030f0180040d000c20400c05041c0e403107112541984100900c49076003244a0091f400030001c0c42909410b041d5110940c0b600076240002c1140030400070080002010940350381644030b002c0e420301c090b8000089c0f00308880350948800604003455901c0700da405544034070005000503115034045200103030111841c41e003a00100402c51002ca2440c0d4007071030304c481d4018810551481840310b003d4042d50a0001c071030740002035070a91031a030003d0100d00c0c001440c00030039910120110010321000e181c9072106410440418030144c003101c6050341c07203850340c00f008942126001c00d41d0382c0c4035240c81c035601c00c40100d80c00a040c0d520f060340d0382c0780d032150481820110122104d10241e4400000c0c802d00034042140b0315800081c0c2e00c0504550b505607554850503110141440c08507412102c150601d000240400282065100310b4000d6030b0b00c4a00070180007100709940e0780f84 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 303195053 1250 303193803 303193823
    0xe10060e030c13200c01020703080a0c1e0315030c0603050a140c0a03090b040f03020708060907091a030f0705030c010c150504030210050a05101e0e06040902040603060603 75
    0x49800c00240000810030000c0c0714114045440d00c3c240300514245520081034084c2c000804190a41c050003054917a02d41c0002580e91100c40c1009008000017500750004580307840500411541e211522207000064018201c20001d0000340c00c07005498044080910242200800810040e211402c07908880312900e003405280d81c0c076100e04080310040106411140c0e980c070700080c41c014080f0010041100075050000707044400b5100c0390f400803011102120015110342040c800c1c15010801e503401000754800600d5107207410070000d0b4486850f40b140000c2c80e0745034810001d00c44c00103c50102406c401404507a0712960b19a41541d40705550321070b8078001e0045412880c0a5440746210f001019000428203c2e07100c0044080801000010300c154218000c42030100c0e1005028010b15000d485288004266420031070003408002c8510360003280c4484000c80c4808211140794030620031940d103201c4c00c4034182d9913040824050411210002c0d403007803601c1d04c0401002220f07071000007a2806240126 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 303196303 1250 303195053 303195077
    0x5060f16050915090111060c030405061006120b0a120605041101050406021e120304080a09050d03021b01050c070b04090f14040f08131d07020102040f0608040c0e1006 73
    0x1e00c1034810010055001220002d950000c0c21002c0c2c014490084103150185081c2000403e01e400d1031010781e080f55001d0000010b10040c400104075207030300310113580d00c80701c80d2614114000e00f00c0894181400c010a8680308908a0f907a035642d001001841c0c803007442c1041380711900c2c11a000b44800c9904448003202c65211121552180c4240c60903076101da0010042c52150012242c00d0000e081c880b0f40c1980714039804d80410201c040302540c0034603c0361181c2e5894146050010f050708050b07800a5001e00714015209001c00e90008045001d803401e00c507030a140503e00001202c241c407400140d0b00c09441810000603000d1010f4005004440390484200f0001c1d03080c09060b410740d252102a003007201a01400305c3d002c40e0b01c5090b2a80b00502c80c0c5a542c2c82d000030030000c01c0210040b03500503603504410800c4404080410110160301c64a10700c0218981070a01070518615003680c010401004501030000b0100407252402d0005448103122480e000e1402c40f10200030a00a401000c0009010034030b04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 303197553 1250 303196303 303196307
    0x5090106030f0f0e010e011b05090108090f0f16060206070e06031317091509030a03051c0f0902030607030e10020c1207061b2604020105161b2702031305060f16 70
    0x1000b4050328039902d0a12b452520401180c0c0000007410585d885d0080f54001e0a04c08c104000c010008000c01e005072401c221400340005c0c000c815030b400704095420620801c81d4031688190f000f101d0000031100e141d241d45941a4580d50f08031b50701e1008104d00c0c007040c0f901047c00d0100010303041070803040310044000039910070b0b09080350141c10690b9815501071480c06001a0040c0c0140031082c0c201d10081480741c0c41c0040e06420f94041c01d02e1440003950714071120056040900c4203035030151a504042c4042d05070300b5241551a40c0c80203ea441144d4013048413241d41c0000e1258001c411900707520561500340d581003840040070304900070f00d06a100544007085a03401204200c1c071075030f00f60b02940c202002d2202c05503008a80104103d0400c03a0402140007906128254018100d0242041d28203c1411a040000680c141d410030074410704d01c04d4040240d036100c000e0710b2408491007400540c030394072a99074010b03e480c202d44e07000701140581010080c40c0c4103055401072082c2074681801100001c40102 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 303198803 1250 303197553 303197591
    0x50301060e070f170a05070905040203041a06040b0405100e1602060f1003051e010b0d11040f0b100c1106072a09020c0606031605090106030f0f0e010e01 67
    0x9000719090300c03200011821805860b07000c0c042c0d071240c108031011030100c003509451960126040341742d456032a411320020f581d0140c1d280025040648045103103080507142c0040481c0d80304c1003600141440400991a0b450b6504002451080940240311074100042074180b031a4650080d010801c40350740c0060400c41c0341505848007a070068000c5d00046d150070001c242c650400509000030341117501c0340040040d408000f0242c1c010300c8002d00c01400400301e840c950946074286001c42c895103000f14100c01050205602d48003007403045400040d0560607940100c0909003c118159000300d00703140c920721650b00f12407d860a070307100d0250950100d000b00104843e41c081c02c0d9000d41046406000c01c0c2c0040f05441d0701d03901c07260300c032007800207499541d05042090768040001040c071600003c042c85014201000014100bc00c101050440309007030102140800c1e005104510405071100e500680300352980d40030541180020710240038019010f170030300d4042c0c007500204031030f01d611700000007024035a4003034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 303200053 1250 303198803 303198809
    0x8060c0405060d05040c0b0a080709060915051821060a271a01081b0411120a02070204020a0e01110d0212070c05030604111504050d0f050a0b0c0d0605030106 69
    0x8516400c221041100384004c042c010401c4444440240e00814841d04050241c28031038565583c5201c0f82c500f50500030030301c103400c2d81b0a80500400b050240428410010b505a0a001c05d15110b078890000381c50f104c0c04400390000c919040351403080d1303003010029071b0903204544580c3d8008595260316403c442108407525680b900b062403010050f10311620720340c014403058450040d1080298048401101e42610100f0707441500183d10110100450402886842d0340d00d1008407820000c54405024162013440356020140d810302050001940405060707064a01d6950090401c64603460b000038003802c5c103603001541340c2c0890355000300c42d401460001400310300030486a0207445003080c1d00215455540118008892005002c00c1c0403d42c3e40b01003050510a5000784003900c40c2c80c806205220003620b00c00e00c8040266410001031110703840380a5201400c03540100f5100581c405810024108001c40380700070140340102040c0305c5112030441c0581050400e400d03042100c0341c0d507602098200d4103588 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 303201303 1250 303200053 303200059
    0xb0a260705011e030b0a15090e1911040314010b12010e0a122304030b0601051201030803061f1805060c250803190f0305040b060d0519060608060c0405 66
    0xc440003c0403080400c0f54a03900258240400d8942e0340000180041711160001140c0351002c5c254000781d264482e0b18000208480e95421005040c91200c2c00044400031404089082e211440c01c401400282c0884009507008048030543d240c1c901002800307040c00c44641c40c40355a681d0101110084180b2404c403603481c1400c0204810707031090356074070111a03010740e600c1d0911450090070142d452030004064600580080c2d0745603564103518001145500113003071941049001d00403038605500074401c1d075065035041800320342ca0340e940c640041c002105c40b284001072103009016889840da00032022905030380209079000051a02d80040c03101c9401001030342100c642c444e400700d916440e07002500390490660039958480080d128010580b80d58000101075000c1400c051880604075801601407003010103510703044c001c0c2d0410307071104110410060562441520815000c000b002020420b6041e20800030b00314040302459410410001c040b24403d0f05498086c000005510402500407141503c10003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 303202553 1250 303201303 303201317
    0x120615060c0d030b010e03011d0d090305150415020c1b01030e0c010e18091e010b012a140a0c09140118020f0d09021809030a0e040b0a26070501 63
    0x2c00c4110007a10354000c103035060042c0d80b1034009590700e00303010709002c1c4610441c014682079000b01e2514030b02200f0910010420811090901c0050001320390f00a8007268003a9a00d000e464904080c003105400e03154503000e01d0b10001c0c166650501c0841c1c610000003941c030560258061000054060b5500c00c901484c164205104000700fa40c0508518100c050000e010700c450b00c12000d00415180e1070542d0900303000d902200e0405a90142d0342000aa0720003100700902044441034006400002410003222049070b020341400380001a071504800c036150000f20388480051258145900d51021400a651880c0035075408554084280a840c1010001030301140450707207844a0320102900c000701441c0d00e59000c0000090329240000900312040c800d1000043c3c0c14400c3c810407604041c4202010144400a000c0064944020090b5203003024a402d00889a94240380020001c112603c0b042c0d9014555510128000c46c20700502e000f80290903e03d200c884c5603644001d55550301c103104050000b031078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 303203803 1250 303202553 303202573
    0xc090c090d110d0b010f0f080a032715030e03030103110906010903060c020c04060e040c0504050c0405091504060807080601121e0f060b0f06070609030905120615060c 73
    0x111180c14a807070207a1489000c1c000c10750002160740600c100f09484141007440144400e040c1c0000c040014440e83d08141036041c5080c440d5078503007400c00d00180900034403001c4180160401034050464090a42c2c00141041d02c4070b10084d035035441c0d1220a000640341030300641c41d051000003228143c80e000740101060442a030204205003100034019810090603580c0000056102c0c09002c1c00d8410540140113406825820704c41155182d03406400b4414055003800003181881c2101c4060301c8003a207000c0381d00c0e9204a0340645502c00c607030021341c0241740042000f05640d08038a080c040c0b040112000c1c0116a5140c100c2c541e0f0b42d0f02b60050000c85c0e08908010804200c85485505d1014440e0300041d002038074048207081101e000710401c0c1e0303c001e0701d0350b0090108019489564406141140c5000c05020640046502c40c01340e2480200645d40c2c03001c142080c140030f1303000e00d001001c0061001038441c803807103002a103982040d2840e8600ca800f0101c000700174030f484000e036600c1140345d500414070104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 303205053 1250 303203803 303203809
    0x30f090f1809081207030501152a230717060c04060e01030b0d030c0b09010204080d030b121e0f15071b150e0609030a0f08070909050a05090c090c09 65
    0x400b402240e500f001000304c050f582c0c1c1540e20040c4504000e0b04c000515600d407403000d4000c103100302c100320204500441c001d2408030b140d00e81d0042152185108480c04d20651505080c000d2162920284841080515034054140000c40c2829140c0c0070b020505940340b81e4101c1981c440003600d40c507083e40c1d024881441014400c400c2c0201901c414500403070031103a610041502d203555102c0980005900d0a41107061002c0b10188030380102c0c604000318030780b91070300d03518607280d42c6031100351020561903d078140442c0d43c4030744581044454440c03d0f50280904c0050103c01c0307003c14401d02845024035100a5000c00010400c000044100d1400e00f84030303610f0081c21605540e680d0250050b4110400f0030780c0204917203004070701410700d541c0740000d20030307034103090347c0380307013150050000c41d190b4820010140301e154880780e0344081e8000c1e0300300111952550030080d54601015000320101c14076007010440300380465040180a8040361054a0000317410005010900c0000c461000c0704100030082c1000c503003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 303206303 1250 303205053 303205061
    0x60307050d150f031b050a060e04020c0d0c0c0609060507060b0d0b090127020a0306090507090e0a11040b09040b071b0506011508160315080a030f090f18 67
    0x82625140081d031005203120070b8403603010503040750302c0102500c0024010400580315021440402030704a050075403030b1200048048402d40034200c10003e8030810302110b0344a5070191440b25031940c0907a42e001c40a06070040020403800340c1036071100c04000000420742d018a60031400e6800d90380e180380c58812031b900c410010b440c030104044d1b0445402c99100001c40c1d1051880c50150801400107c0d44041d16007020b400204110001030607802a034025000680d10207006000701c0382d005c072010401e03402c17030700b4014105045603201c000010b04100d1003180d250f20128040c0b10980c8280d9074009580085000d100c21108007030185a0001d0f15040071402040c09282110390003412407801914655140c9207099980400d014115610390001d00140103030100b80c2e00492481da4645440380ba903241c6000c0c82c1e0042021140a001031560340c6100704024500b41010324060114242105c00d80455494000c00140c190034802700002c108680218283c101400e400e0210394241e082901c902c2080b414504c024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 303207553 1250 303206303 303206317
    0x70912050312180307050a0201180501020304211211011b08041104020904060906150c02030d08130b0705070605060909070b0d0605040e03040801060501080f2701110d180206030705 79
    0xb19884400d1552503041000244035103032080c000b0301422107c0d0f2001410b121406604172899100401007071140c0d99001094404507544980c412203024011850070728000402080900103080d0551340c9002d081d0440c00603191180600020005c900c000d046040c58ac1051402c4c50340000c032040003150225107074446c4603540302e02c000c20051401d00003e00080c1200e2a40d0300503c811511541c003080800290f40410110343c0050400c2d2880d010a0f0b80040d0322058000740007000e000a260105151040403410400d050390b200c68200c441d8208114068490b80004070112241401c040c001000d80c140714501a000301e48a00062400030b00f0404145c15a4104000c0481e10310740d549000a520b0f42d41d80103c0507034130103120246030b403282080c035032030300b90344480c0c002a040c001d807081031140f10801d45040030391000c030a5410a40c0484001e69a0303005a510b801c010741c01d903081036000c2000308606c100a00400000131340c1084008800c52515038085024580030703602a0081c80001d4545001d44020440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 303208803 1250 303207553 303207571
    0x190506070e0d0f022b051203090307140f0601060e040507020d09150302130603230f04020f01020a0203160918390801050103020112140408090f0612070912050312 71
    0x612500744907135074105d41c54002c030710403848407540c818410701100f40920310800c0c00c15181945140b40030001e10360f40b03204180008100d021030503180340b9031010038001041450401ea0640b03055507510300c00209006414001c1c40c0c46949440081400280001107004a03075001c0e484052074540303840503003030240c40199240814507400700818120340300b0842c1e0300c01c050a0f881c0c0340000e21202d00d00340034072000c0d11311100504c0c60744114140b10260380d8164445500c00c1c2d04441019005100400403070801c4028080203405200d15802d2603034007080740030540240c481c030300c07010001ca00d1080281d8803005e4054401030141d940400074101b050406a0150f900d0000b000c02c143c0c0c20301310060201c40d50220f1944030240595440005004541e4410081840321920346011b00504042c905d040d0843c442c00380c0300030180500054030520750b4407501d60f0f40d0400000200400d44075108400c84000c0c42c901107410310000f900091b00400c0040044160a8007550840021818105614142d03110b031a80035001c481 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 303210053 1250 303208803 303208819
    0x1b0209010b0f040e0f0901110a140901141314010c0b0411041103090f0c040203060609010c03120207080711030303041e0f0807080912031c0f020c190506070e0d0f02 72
    0x80e4004c2d004001c04d000345441c4019111510b0541d40043c2140d603003c014100d0b0240c01c201242c0001e41c80404202c0c1414061803250340d643e241030040e942002d41c00c888042580c1c002c00d042e04aa0031032041c04044410031141006180c05e26801142d00000407000102581e15540100d404110341c42f0b59405104c0e0302420000c3e82c2c0c80c0c041400316141e0401c442c0c06c5103a070b00004803480381c0d05050001c802d22440c01d840540c10342c03c0c8030000070300c81d000700e40c1c03094108941202402e040c5440341c0300b00b1900c48510341c0d04550300c100c03d0401c0201644a040c0990f841d4244c01c1540035541800022240704540081d0309014a803000580c64580d2000500180e40d03200c07d0303400303160103d00742c40c0c002e08100c2e120380c0902c0c3d40c42c0c5410051001e080720212498656410620260000091031402c81d8140c0344003140000340c0c0105601800000e0280c030f20441040c0c03042071700c25a01d908030500304c120340310b005408880040e40d604900711041c1d40c0c0c8031f841c0f92b0020300c02e514260014001404404c180c92004008403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 303211303 1250 303210053 303210059
    0x70504060e1005030706090e1e01090212420303031305240106030b06160503121302060f0304030e030d02010c17242209031b0209010b0f04 61
    0x90a03910349821000c00e0781d0100d014864152181e01501008220980c040d2111500e0b004c0c015042c66468440c0400804508000600030170b410f1810359410103c404c04100296100c813036031030094200c125200c5410b07030200d0119201d9420103034519800d403c560941c0e4441803501401101c40100000480304119580d880c2c8201d81e1703014000345104246845401e45800094200a0310700701c401e00d082d10241204240e44048a040032040074190780e56170501003601611000891042d104442c070300c4220b24001c0b20700c641000030120041400309125103016115440e1080000c40c21011098003e6000908204c0c0d4200e01220710081e541c02400b03400c05110390280d00b00440d0800d940c0f001181c006175520545541d80079001401c590010180c5007440700e40e45000740120900c60399180c41d500354000c0c42103858003665030f40c0c2e001005061b09500e0941500c480c01e160500688207261084000c602d6291211684402070000352003000e030010700d0b0740c41c00d07482e125060328150312401000003400010031000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 303212553 1250 303211303 303211309
    0xb1e1b0703110405180a080c120301090e1203280f05091615120908070c0f0513110a08150418060b010f020604080c030d0c020607020f07060507140705 66
    0x400010740c0901810310880c8680303000c000c01ca82d4010200301c0d01c00350341645c9600d080d81c002030101201d5800100c990340c40c65000a80c603c0c0040781d140451407100004004980d0680795002942c2268641d8101c0b41c0f6080d5030310180c00c003400201c5858039042d29000e009400c50080c00d80704481600d01e03000015410302c560801c04140c0780104c489100e40c1d4070460781d41c12840d0b05008410010300b1a100b40c0d0f50b810074507041c020801d481c40c0703030004176142e10340150100717020000c0212244641c3c405400a81c15640d81044140b000681c4600c0d8070400c9160301408042e54140260304a00390068095464402907000550350030002030a030210201880a8107001030b200c9110749103081c8111040d80c00c40440d00c1c6045020340e40102c0006042000b0b4454070001c980d0000385260f04a0303402581c003511101c0004106246004041032005074504014051110980100d042c03802009a682520404440d54020642e100c00034441d800000d4001c0182d0303404a0f4010915031040302c601402c1e180c2160b903c41c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 303213803 1250 303212553 303212563
    0x170f0405090c0a0e03010501140607080904151401090e0a050912220b130b0f070b01090c0215040c121a0f011e080303070e04020724060b1e1b 62
    0x1d01c2d07881420010300d2441c0c20b50007042200050100f1802400250304100c440100304075100c0681d409001d01007600c40c01c02c031980060350413031302000c1d1040000b44500c040124079690726220326626024400e0b1800c046500c00d05039403042d20321002e40d080380c40d210101c150700200801040d1003a54006c04404405c2d10003818000c01c0054250075a10045d6402400020380c1d100a40e846211060010404c071810020216030303070421106e02d03004036500d401c07030b0030380c2001c40c2d12030200000c0c9154040c030700200c0c0c03c1c0042e03409a0f251a2440d400c40781d20320340c0025040d03c3d0380d100391006004c540b8010000c2100c14140c40201108a10443da40540b50b10003c0c4103520048090724034040d80e41c0c24400500201c0d0340302204440c140310015001000526000e4100c2e12840050718000400c408901c2220583c0c076540c0480d000d40c0e5004042000019581e80005880b11811240104aa0070b183c1c1c00203103884000b054070120010341c3c900c104045415403081c500e540c4808142e156251035103014020b09081802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 303215053 1250 303213803 303213811
    0x509010c05150a0e03090a0b030603030d050c0301140d051b01090807170c10170604021603090e0a0204050a120c0803030c03250509010809100e0c03010c0804170f040509 74
    0x341c10b60650514008000680d04045040d00e5a5842407040002540e02c018840c0111070010340b242d962230321244042411442044800c445180c109010704c00c0401c40725005504840440c261030060a18440402108030441000941542d100f666290a29030080d540c40b0310103401410440c0425a07244586402c1c100300b41d103c01011070b02810038291485c000d11031107011440031200701040c500d45050281c407600c10f6007002e03401c03654118009600394995504499101c4274105001c5204c00304d40c50300424139006806124502640c0e040440c0550145009543c00e4a17001000100000d0824211110041845034140c0303080d54030030030004512205000460007641c41600707a40d964503080c0e00c021071218410108105075000c050030300104a6100d0f0075074903801401d1802d4081a2034a403c1c0601d071007071f00c001c2c80040c20b2810f529008a410f0005214080d440150000d025514100e0002e4807242c208540c060503220454005400e6a1001e80003490f90f40c181c3c0c110141065210360210300700703900c121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 303216303 1250 303215053 303215083
    0x80f010b0909030f191b050d090b180d0203100203071d10121d010c180b071112011808030603013c0b040f23040f030509010c05 56
    0xe00d28004504128410703a500844841c029460001c1c0c48650143d5442130a070420072181000a1512a0b24032a1842e80e03842040c5240888400340319060094440582d040c1003000300b5141180024501260f0040c1d6511500003140c401d10300024030f05212031400c41e45412039160180000e14241e212051024501982c00307a592481c40300c490040003103403244408100352141ca000c084501c50160300c424a20342c0440740e101c0c041840116541c0c9a1042405c1d48407400b40c0b94241901030b0942c0c2c0d03000c1c3c101c1826900e020007010007251303242001c1c50f0b01d00c20000064509c01c00041841c600c0d007003240c580600d80815400009000700c09010341801c0300820360701150400b100205010841c9024003e0410800500d44060491004000740c40080e403401454885d101003c40f200d015501461342c06200d4410001d0b00c140000113149104400801c500c400d103000d4150380301030340032420460008081c819031380a03405030340d60402030700c0a68840c0c01c01603200d41040803032a4400b001650074071140038208601c0f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 303217553 1250 303216303 303216311
    0x3090102060106030203040506060d0219060315051504120807170306100314040210050c01020c010b2b02010c210c260304020907020312040c09050105010e1305060406080f01 76
    0x4040028181041a844003040500500c18003022880201e450380e00080100c60940841c6040d20114904d80d20f09105800384a00060002800680642010304880c59080007003207a82d480d1801c00110340c4603a42d100400c09800d04c000d00c82c00149401e1040d000e03025500041c102509581c0c2c60400c42d203007010100710840b020051107114108001d02140e22509030900b80882144ca175180b01480c10010b1001e8440e004000151100c2c50040341100c110500103c000d40d6229024400640a03000f80c61541e0702800c1d010081d1000030030201d2100440c031002143c8604007e22030b80045541a142220603120307a40366540c2c03a94420742c181c480d14444a8182ca030b500c1070680351300f804c1d000b1401c150483d840756030312980304e04441d142d000c04881d4420b03411981540da5032500c41d012403560140c142c050302c0c000c00d90414842885844948101241c2c0f505034180306607a21a401103030220840b150032908202290098042c1d80c5441d00040d501c07400c05000041e80555586d81c4c10310303040580764400c8469640f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 303218803 1250 303217553 303217567
    0x80a0303050a02070b0a0c0509040c09050306060301020a080c0f1204030f2706080c04031406010f061403060105070f020411070b0a0506010c03051e0301030b180a080901120b060c03 79
    0x18010303160b0081d040c40c030850415003140c50340d502c102d0740100403051080d40c0c3c0d203c1101590003401a58a0201c0207001003101e13a5208801405a9900d07001d01c034070912926000884520b414021540d103800b00744d030f0318020b645070480142180c3c0c006000d01c208a032001e004c0b611754401d2022005115078080d959401e40748a00d80409048150841140141c0c030100310046401e101071190520304a5000b860b01020f0f81c1d80d100c84103200b6000c0c075000107046652481e0103268280b03000030001d040e19045011245001d0341c2c0e0005903501102d80400c252009018400030342990300400207040c0301809080c40034900819640003600b1941c2c07c42603010000301c04920b017810301c04040c031075542c454000e0a00304520b06100b40043c007151800000282045400034200c40c81140d0502d0484810400b50f02d4142c41b540c4902c1c0c9500e0000080710303401103821707424800031841080080c64803016070300907031032074540000355004480c07120340c4c1d8158541c0a0348030352026515854240017800300d081e0381d101454139034034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 303220053 1250 303218803 303218807
    0x80307150c1425080c0a020114030105090c03091c0201050106172a0403050105010e060f01080421200102040f0501020706120218030109120201060f0e04060510030804080a03 76
    0x4225000200b00081d810720380115100d01c1007100c0020480140c41d03401c1c03815003800c1c14541d0740d107520b009040d482c000c504c8021581e0300003800814a031003600e401d400281207150700c94960000b48a0254002c1e11600403071180200d86005640200d51001518032045030584200185141040c0c4040141c1d541c03001004403aa21010486a021805c80b8050450910380c40b2014282540101041e41d001c1e04040d4043c548040821036005651001c000e04c11503940301c2008016200880c0d00b103000d401c000429400d190310402519106683c40341151201c9102600d00c0c03010800300108100c2408003514108501d107401d10704008031680407070005a83c540c00d0030b540101510b015440581558403040040c403241e500000b40500043d02480b00580f0740410500c0c0c10303404039506950035019460440c00b01e09002c1540da80c0e50a50f400c41d002801202d5491042d290700c1609481207401e41700310240480c00040c4603400c95034004106007025103549449440320384d50340c0d01a520a485591011118608140d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 303221303 1250 303220053 303220061
    0xe03010e0c152809080d020a0b0c04050d0b07030e150117060106050307110304030206120603060f13020d0f0b0c0415080c04140a030b09010905010e1c140408030715 72
    0x50b49000c1e003182030008034803074522042d10034048904004140260000d086200700c464000070301c40c0c0340c202d1344c0c482e00304100a515000c2688040d141c43c0180c80020305a141402d084a0841c1d0002d0000407001c030840c0c0f10b0075248c42c4082d0203102010f49a092002c03450300704020307000384403003001080c551035403606d26940c017501e000c449180305a800c44001080410b4024050301d501c0091402c0c094924110030509a085202e03c1c3c00080d4008000314840d00f01242c0b1030102e61149c501542104c401e504c0c3e46141e10010302c011034405200d161000e03d041e005041c00d0180c500c3c034510881c0c03a4800444141d0b966030700d9200880314454401804541000b03c0021031110080b1321095080803c02814124007a01c3c0e144514029010b820764440459000303500c944038190019900001e600c00300c0d04003000c2c6076001c3d00c510101950076609001559440d80c82c041000c2c617042070f00715240c00c0a003d600e403059070250101e210046140b2020700000507480340a1008003842c40c0f2984402585100f03080d0f85800b21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 303222553 1250 303221303 303221329
    0xc0f020606030d0e010c032a02040f1e0902060c070b0a1206030b0105150d05180f010b060922090f030f08071403150d0501090605010b0f0403120e03010e0c 68
    0x65409004983c0b9690f40000191030b02c4e240a06e0100c1da00c42141c103081d03401c2c0314800c0c51502503441d0300d446400d990320508518007165208031000c0c4503c2c0d2a680099042e1409000d100c0303d0b8a5800703085091712a150390201c0001c5102810303941c20000c1402141d400c000d070592000c0d4041000099000030140e20110307841c0c214070f01203c100100e90441d00c40020114050054500840301740b00c010b0b01c16850b82040d1141c2e81085641030000b4070780040c0998000b1000c0741000a03d1051120b02d15003681d042c0901040c4000c0605030905044032202044052103ca482000d01000080b01c1800c900016005041509014008070116003585140080120f80603a501c00100244e2000b4002d806a002580101c0e66a00c903c20b241c681c2c031824a04200d601940a0305c50b8040900450305003081019041144440d001d4402080036a03620703103c0711414440c007411031480680c104000d0001512074054a030315a030003880d0005025200f080070078211980781c050109540d1114a02c41c5844c500f0300301000c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 303223803 1250 303222553 303222559
    0x301020c1b120303070309020f04180510200706060f14090f010e1807050a1d0105013002120c0304060e0f07030b0c0d0219030501080c0109090903030b040c0f020606 72
    0x78010385500300343e80300e0102030103160415445101c00380c15940c3c0ca9180180401e0000c004000641c005440c050503120750000480341c034002c4080c0c40344030030030521440e855203100203601450300441036103e04460307102150441c1c00503920a4082081c104000045014112290449520502590030007d00d808020042442d03c007100c0014841350b071444a0041e00040014445003081d480204498100352040e00803c1c1c02480f011303000280d4650343d95609021124110202c2d0107641c03140300441c0e0001559100c0b0440040500710b0002c1986055101031082c003120800600300a00f25000301000755090340c2c0b858001ca008001c1c0000d001851050024a03480000100190002070507880d40b110200c0c030015010f4480d02000607400b03007210301259001a40c04200319595090041c00d0046a444c2181c1d04001038035001c0040b80c418400601c40300c880c1016110422610700e031110030405000d00c078400b00c080649610750310629071030380d000d030503066940350301c0303c0e0200119080f000b0b2a02e81d0041c08184 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 303225053 1250 303223803 303223819
    0xb04080c1c0b130212010c03180302031b010605060f07060e07034704140303060a0e091603050606010e0603160c0302161e2418050301020c1b 62
    0x248007058441e56028582d441074103a00c4940e0750520703858240c00709290280d000209076003c40d0507050190b20014612090b1b480c100402c001039084003105000e0500001c0150340100041c0b00b48a01c20002c401101903c2030000c1406500e500226140c0e80110314054100c0c04e000c03034003604021240c022988040c07120801003580528603281c81240252020400034190407215000000220300240c0703040c200001c03001000740449400d41c189890400300e030b0a82c0e81c807800e9a00c0c030901ca6804401c4900494004140610041c00c007552010349a80c080c000d0989071296042ea8184618401c884100442c06113025002515040e40050b2400811401c1544646820020407407030030b80c00c2868180b503541d9441d2400a0103164a02a8a400614001e85852500c95240094100d040c103401c03610341c0210452120031559180a6803405801c1d4200b04000c0b6a5600c4103105158812a00c2c2142c43c1851102422065510004a803ca0340003851810154000e034007102c02d0180b40492602c0c5010b07050300e10306 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 303226303 1250 303225053 303225079
    0xc0c1502030d1a0a0501050d020903070f031b030803060609040b1305040b070207060903290a050402150c1e19150c020307030f030b0d0b07020318010905010207060c0602040305070b04080c 82
    0xd14046076801170905000c8003284918411107264161021800060101c802d89516004410310750501480112506000058004170040b44401c40804403a40051181d083d629400100300c1d03140c000c07901480e00165142d0720002c0941d102400c101c99a960940000307000c1c03c1c28248440e121070014074410a55009080c20401180d003e080101140d42000e8580a041240e04448403480310010741c41013000d415201f44043c0c031402d58400c074002d5100310758102070024054401c60300703801040c0b0000c0e41900f2800b2000f01039444519070307090300c80180054542e08000201c0040c046c0158400680b204c1c0340102d411012644244105a40c80304540011810640e180e039004280400743c1e81d4030401c160300d401c0d401801d0344079600d18451459102d4440c10705440c01c000d00079540c1d0080010b90400c01031640c0400d40d15401031650030181c4030706038040c12861b41064400c1d205d014040300304071401d035400c00000021440074060480030341500741c0300f19503ca10340f00d4030501e03104c21800c030b0500c1142241d1001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 303227553 1250 303226303 303226309
    0x10e0a0503031c06090c0504080d080c0405120a050d050c0705060c0d120905011107120908060106050c03070203070306050601170f06040f0e07030303062d05010c0c1502030d1a 77
    0x203503d01c0b0010064007840500580d00f020094401a840f2040590800044c20780e815009405441a290301d84110342440c40e41c4113041f12254403d071040220000c0401080c4011300b840d051540010082d0000c0724125001550b0700392922961210a0000907808034946c040c4d90300c20b11008009000440303c2d01d0030100010b03a85500d50034003140007010b10101c1002c45030840c3c42c5400201d101074104000300881c401c0b0401e010201d40c4503070707811605c02550001c10328182c1c0c01034458a050781d00c0307200100066030074a50103841641c0030b0f5020100c180310521000c401682c1c20003441c00550f02c1800301040700e00b01400050201e08203410b401c60009010420042e1008500300c01a07884482100c000c102801c04041050051040c240f102c0300b54090032501005040d050b400143c1243c0340b42e04000319003004d030f540b2810141c0d40600500c054011200d42002658424070910b11031a0080204800386951003810000154184030344034096000450120a40fa62070311903000c0007a000031007101c003c2440000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 303228803 1250 303227553 303227557
    0x1051215011e0e06030606040c1707090f05060a0f12020d0501090b0301060b3402030a0303141e010b09010504080613030215040218042a0314030408060403050c0a0f060902010e0a050303 81
    0x42340501e9036087d840145c04d201e025041000660000c51442c40d003002c2e2001004407915009003031009081d0040082c10b414480b00f1200040d03082d98846c0b0600f29401d504a820290920001086a8092003044044191841414024907000c80000780c1d1407024001c1c1429654103a01841c08880148141509481050100c078243c00740f9104c04200c0d080c40704d05400f0710035031010001c0d4042c460070107400201340d05540400b140b155860b410130220390701c4807100b075810101024540d4802120100410841d203246000c2d2500780c40504046003810b0300c2d682c10b00d181103021a8100501c4d18a20300560074150184400c00c40c48034507451400103850079030041030000040d0303d8290303840064000000c0501603035524650075400e902e66042e0b80c560031021102d80b0717002d02d80815500c04844d070710042a484000400c45003207403c190040e20741996541c400703450542003115240044d0040314103840028070340183c1d004505100301c02c001400c185500006041192600c40d042c0640b294500034405c0ea42d001007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 303230053 1250 303228803 303228811
    0x108030405060415121802030609070609060809010e01020c030315040908040e040f0c080703112b080702031009060e0a0512071b061110060b0301051215011e0e060306 73
    0x1001411030414601140d0128217903980244840c64000c2043d14025424600c2041e94002c408452080d02c8084c1b484e51910494826907000c070310152000c00c0440d0181401641c010402c2d000011240c00c00c10603682640d000001304d04a581001003000111858981500c281e10001e940c1007043d9015680d0b65405407007640903102c0f9860700d641c002400c120881810740301260f070050f8030007103079a1380d9070410b80e5800d2140000c9501800030000754515041c0740380c1100f0f10280740c1000490b0f0b60811559a10071401200c3d0907940707440200300d0b01001d03031020003480141000e6040001400e00031400d240d0202c5000780d40740a4150000101c1001096000441c0c420903142005145d1b40c039150f40c60500300c1a00310311991a4001808900007d06a410016081038203d42c0c806540c0801c0002c903600b8121107483c000c2003c00300d070034030040c00682040302c0c118650b4951503044070a682d900044c0100c00c4a001d034400c00c0341030702070038400e0001241d420051000340910821000ca034100480000c0d200e0038010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 303231303 1250 303230053 303230069
    0x20d09050d0803040615030804060f0e0f01031104030c06051b010c0c030810120f0501050c040806070e0105040e09010b0a15050324090f04030f0c120f23040e01080304050604 76
    0xf0000c075040c440c00354000c04082d103040382045442d941da45441d20707603074215100d40008296540105000c16010356021203248500038a003080c2d400c5030b00b00640041604141102240006100c0880003480c1e58003500060843ca886a0b610307a20b0109000f081101c0c0410141c4a0b0390410315061403907601f10300302d8482160b00d403c2c1200603a951441d0515041ca080c1d00040b0021407a4064105004220004654050052009120320307550310b401702c1c0d640e115a01c100400c1c0d6001d00c0c0041c1d03940d1704c1105084030324081494141c0c03401c1d0380c8070403201000c0410b0700c0c600b0139a55200000356482c500310500300001d00302094180700448039240080d020740002004122042c8258140d044144d29400c00c00c821001c00400d1401e0078107102d4400e00340c400088804801041c018059841054000c160441c18150312845449541002c444102c50f5900030391602c5052000e0014112811645200b511300d00c03030303900341d413840c4c03110310b030004802c910b10b8180e2003103000e900200020310094071280c04441c140d40e101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 303232553 1250 303231303 303231307
    0x19080601050c01020a0509210d030e01021306020609060f090d050d1d16080c090105010c020d0b010b0c150603190f02030607030501092003180f0f060403020d09050d08 73
    0x1050050351140300b0811a059254400500c4010090b044405490f80740001d603155104551000c0c56102404009080080356900c000703c20705400e0305ca5000186442c07058400503090007420340e40e900b601d600d00c4d0012401358100344104058410100301c4141e000c0c036064082c18840c01e00a081c04d846040203290801000b90000300104000c20340d0700040e0440e0f480074200940100d0000c6440c0d112520b4903402421052004400184175400207041d04011000811592469207014015519140e80d502d040fa004640c080c201390114204d0880395000707005845000340d490041840c0c0c90f04001100794840700c046a088240f00c110388000a0364101404c1d007019002c40c001c030740e0820318099840010000d515200349010000c2c080e03850b41000741212484102841a80315094600d82d10381941c00c450a010700f010700000c0c08450b440720440f0404640e074400d48208a800304055400d21640031106405075010a0070301c410036604202000e000320842c0380124000c0c0c1070800140e04110b081602600040380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 303233803 1250 303232553 303232561
    0x14011202030a08070c0f08030c07091e05090d020c060711270a020a2d08130807061401051507020613050319120903080906030a090803040303050a050601051908 70
    0x1c20400c4802c210f420a003440e03114004c91920f084400260301900701d0540085c240000c0d440000015518009541000b9103001402c00ca02e510080400320b0902071104020790b500d90003c8007034402d4900455400000e0701d02001d4178000a0700c1c00000d400b000e406884104424004101c0010b012030010900f05c1c7c011882e40c480202101d07201d070343c5940d54039a0890706418800e4540301341c0d000b0075410200741c0b24500e0701e0340c600d08070340300c0a1102c0d415034040c1c903060008220140c3c800c8030101d0b8400b0302d541e204840fa400d0342e2a0341600e500301ca441290b42ea80d441064021030645103400900400f01124401307401000b16513418214042c2c01e078000d00411021030520b05044240701801c0103401d0180440310001c0040740c020000c0003001000340c81d51201d21102c217040b141704141c2c190540c3d403c58001441e14407914140205075000400742c0d2800c035601e401c0c1500107590400203502440c004c0e03502244170305044071040110340f409850319041c0300d0100444203030344591490000c403400c42414090702e03d80d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 303235053 1250 303233803 303233809
    0x5070e04030314070c0b0a0c023403050304050a0807081015090c051209010c0c0f0204060e07081608190203090f1606030608010b0604170304030c0e041514011202 71
    0xd981d0320300c421019010401c05182d9010461130380e51030094101b0341503a2100c041810803103005900383c00043e0451201031007a0720700503003048240600c5806411070310164030364030070399000c46030021074950f040001c08000d18500301c4040000303004010040c2018514060103a5a5030011141d091100e58481c0c1a0588070700036807403034800820200805004100d010440240740b54848100003510308840c84c00f2035070f42c039014880d00031880c6a07511550040d0445440d000601902c1186c12a4880c0d20b0320350106d0801c200b112118001d28072600c07013040c1810011541c030301110b130314a00003003040740050801001108840c1c1501c012200c401c40169691500c0080a00304400f081d1000300305d00c214100c158405090b00c18503070889045640c10041340340c844903c00e007030721410322045610410500003488820210f8200e412610200e2007164a0155250340d014a00c1c44a9405480c0e1014071004200c188003040a403101c0112005000304071071002d03002801005038060007071101d850b01100d41d01e0f003151 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 303236303 1250 303235053 303235061
    0xf0a1202091822020f060c012004031e0209040602070609020a03031d09060a1e090c09091103040b04150609020c06090f0d05030c0307140c060a0c050705070e040303 72
    0x211014208510888240b4500c52140d0b8050b5403000c84400caa02107084050514481e0621081d8020701001800d603001c0104456900301407000ca0282d561070303850710142c0000200d07124651603081946038940b86035041c6020070780744080d0400010f04250503041c0041e034840807040c3e030080d4041c60068031081b65040c82401050742010094121800802c0407061507003044289089550801000710341ca180b20003072001020054512941085210394240320324070382c6900d44010343c03514200700406260344030316820580708000c01410109010385414080141140518448041d400100d41d2850900da0340d10b40c62448000c3c00680740c160004404d005c4005a50810402040540f90943d12a840880f00a443c0c0600fa01c880b44a8482e50030b0a240c0d8036030129112028071042d44ac0c09095aa40740e01014041d40001d140b03a08001d21040084c11800c048000340c1440c00c41d9400401103454114081c104583c00031181d81d046c4041030107003c002a030005226800d42e14079003289074850f121490154041c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 303237410 1107 303236303 303236317
    0x2090f0904060b03060708040317150415121b080703050a0305030a09020907020f060f130303020906070609050a0506060108040308070c0c050405010b1804020f0a1202 73
    0xd181190304039500c14014000031500e0341554000a090180480c0c3c04408540c4110500c0f041c10b900007500405204100b0404186080101e0043c0029030369441040c4950b445020000284613500007990040036800b983d42c120707102070300d8004110b191000395031a032440b40a900280d04080000c2d15011660072001038400c0ca0802d44003162980c1c0700606082409860303038010401610b465580c24407500241d40501800d01c0c81b13424203400c0050141144066110b01401d00c00b1410030144142d00c600d03410f090050361200400c02052881c040c40724054580e9141030354900c2800404544030580b03038402d20548419aa0711001500e01c520161009000200104001341c601c500a02054a150f40501801d00485030785c2d0001400392003098004140c0804040368482201d1220580965450404c45043d810035113464403401460180340707141c00803c103001c0c0750744c9440c0816604442d02 = true := by decide +kernel

theorem cover : BRFrame.Cov 303057553 303237410 := by
  have h0 := BRFrame.cov_init 303057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 303057553 ≤ n) (h2 : n < 303237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
