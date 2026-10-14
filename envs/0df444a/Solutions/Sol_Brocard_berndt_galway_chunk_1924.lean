-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1924
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:10:16.042141+00:00
-- url     : https://prove2.me/submissions/d0eb4eab-8a5c-4f2a-8345-8dc219e0f84c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 345863309 ≤ n < 346043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 345864559 1250 345863309 345863321
    0x135010b0915031b0c21090405060904020d1101030603050102070c030c0e010f0b0a120212070207090e19020609060a1805120a0b0406021605071d2406130306 69
    0xa846040000c80c80ba14000400089074050350841511402d81240344404040c2d0358410040c042452140461845201d1040c5213400e20894080c03040a40c0c42003c0010001a1000908900d12541d041d50500005035a10b08400d5021584640c401440008240041e40103019660000e00313754000122902002988503824041d00d100d002c03022100360312046024070b190000d020b0b00d07000028140e42401841c0300b0030041d002500da00d141c9441758401c3d40c1d100790260780100340d00d40c005c2c0d030941042c060b003039805014001c060200c510081000b0f0102c0044603503104959206100104200031410b825525801c003100c41124018119941e9100f43d064020000481950440c4564074031002c01308041c0b2b816102d402d2000c0b02c0500512401c40103485103400c812002e1b108446040c0e00300004412003102e10100c18406008402400c0094a03111040e00000c41e0680c40300c0160b1001d07002c02c2407000010300c3d0307200041ea0400e07110142415000101c0c00c40c2c402d4803007410440c4041440041080030580000f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 345865809 1250 345864559 345864577
    0xd0b0f1c060c11031b1006080c12031602090c0f0a2a15051008010501080a20030d11010e01020f0913060b0414030c100201090b0f060135010b 62
    0x1c01920201450807140d0101c520000740e0b65400800c0803843c0a40f04000c0c40180c005c0c040240c9a907030350800c20800440d8160380c00058039401404441549243c42c8003500e032029000307006940342640d05454a0b40c18140e40000034031510800001ca20660684410340d00d44180140302103540b01c0c1520f40160403081c240d003640b1040440c2c11190509201c00c07a41402542d50b0001c0e107181c49081c0d2444da4009000001c1c02401c8511003141c1c002860002401401e008014a10140c090b04100c4e0400da01e40d01014451040c41d41640c2a03111080e4500040d8004950607510707103156259694002180503085060003001c0540c00805d400100c0035500b4001c1648580407a00c0011401201031101d0544507a03110325042d164050008004410b85c8507030841840000500b40e50307003031095800144054141620f40c0380181e640d011054108008111015000224072506920b90714020000809001c24040f0322600081c1503612500b6118404020b02d02c030b14040380c10407801d90303120103a80034180c00039907070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 345867059 1250 345865809 345865811
    0x210c10051207050f0a030b010201090f06050106020706050306031009081c1a03011b08060103020906120402090903280e181b0f0301050d05121b060a050702030d0b0f1c06 74
    0x442c0c001405042103030400050341c000c2c04d060031643c030320503002000280303101c50542d5240c40605c0009070581c030300c805130248541c10000d0194103044000340f43c00360781c2c1c0011050000030018440159000910000d10114001011440b540d0603e03210701240140f000014a41d901c0446022105200d1340010714421031004409810900c2d0104050036180712203000c2d40312803c0f034552400068440c19406520001c1030602500c1c100541340452080d600162043c1c26200c95a0103000861401055a07508085070340d00842c100030300c5c1403e07143c020b43da003030445595400d06048800a54041c0112004c0f5000c01024a000f080380c81301c050140b003c040b2098407004080d03a0101c0c1d01030464009a0b09825000310400707086030300303000130300c40e18011400080e6514480d04050211030340511000f44003080036540d14105031030a0903551481d141001d480f10f40340c64248410401696400030540710f0303804980c503002c40c2d03003003c200200328a030b0b46c0040c00710741001e03010380c05613010768a020850308440d10503c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 345868309 1250 345867059 345867061
    0x60c080609040308161b03080a0f0e250510020609010509280206040b030c0406030b0402030403050706090f06020408030a121a0d080408030310080105100302210c100512 74
    0xc01c00c1040001110003c001c1084003001c40d210503000100013000c44440d0804944058032000c5400700440d51079000c600045851003004001c100e54051810001c18006081c04814242042c1c1600c40c103070003105004d1010150036003001c507150f40148200402001d41505070199482c44020345480080380e41c0c454942c00c05001c281c208400050304c4a11241d8a03848401d90805100c1d0040070000c0d51a041c0d038022000e00c00440c210319588015405900c1d1808500c3c2c2d9149022000f0342a2481d441c2560f201e14814010400881c2d004401c0703d000c01c0e4041300004d80203e4a10740400500d800341009480311388049004107444500200030710142100b47c6503070380744240880f0600c4c01e5400010000305041e250080804460070180c1441c00b08601c10b030601d40c10305441d051520702d90b4000312442225035140e08010070410100788540742d007150010240e00746941c20f5401084030040c2660312080951146503644e103044000f480044181c0c58002c040c0da07000c00c0346070001001d03500242d5a510001840038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 345869559 1250 345868309 345868321
    0xb13020d051b04090e1c170702010e070614070b09030a110a02060a0e12060408090a211410090606050a060f0806011209050a0311062208090d0f060c08 66
    0x10102d001d0341078a20055280038100000140604182c440d8082c0704d128100400c0c142144195511060415655417920f541c106c002e40044502c002034410419a4545840c002c80d055000c600c0c0c1c0156101c41c24195200d020309c0802880c1441001c2c009030030765048a0500500440c040300514040c2c130941c0e540301425240505080d1901c1c090f0744001d5001408004c412440c5004030016245030500400c00c0100c00c000c40c0b03441c0d040031400c950481b442078000401d28064548502c4100c090018a65102d400400e0304032000307031000036540b010b0020020002d84a8500d1010456100341c07034580b14040c060602e092074804064504c81c040e10b842082101d00c08100c10344601089070681da101e981d11f1010742c85200054412564024003109001d498802d1000413960402c2001503142c8070390f0312601102c0549094138140342c805003048106c501d11401748898450040f0400c3e50042c1c00240207a6110208000145140441c40c0c00501000801240e5018040d4540c0500c140d00c03265200c503001e5555603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 345870809 1250 345869559 345869581
    0x20306040605061e1c0f0b070903061a01210e0706020c0a050603130611041203080603011a0d08030c090415060806010c02012c040e0a060b03032107030b13020d05 71
    0x20051074003c645d18801c0d403441e07034591041500d02400b60703540d040c0b45083c50b02d80035401a41103415038085410500f04104114a62250b0488003501c40b256180f402c070300c1c01c0000c00003242ca0780106c80f03c5003540022145107074554440289204030004440102d9500e40000e5107070306000380e283c2d108005010001a050400c00c088900c0750b001c0310440346000b100c5039500c40040641a60040c0140c2051101003490244003100d505a0744c000e4070350f03103018035201c5c00305425120201840940f034024120748805507196002100c905e41d03440340260b0b480c0d648044070380110b40111291198003a0515142c001040c0241c8013503c20780d4042c3c0d80364103203a0b541000661320181d07000002400100d84501500c03a007101281701d40340c08008010410000c85820b00002c0545580a86098550f003140410340c0400c03200344203940072050181c01550408225580030292500f90f5a000d0702500c02c0080004c0c107280c0f1070303400360004071002002e0780080c0c840040f03804000d401c080c20000c02d2600c2d090105a0080c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 345872059 1250 345870809 345870859
    0x1c031e05071407030c020a0303031a0f010210090201030b090403090303090605030c1603230c0708010e0c0108090708030309060114040e21070b01080f070e0f04110a0302030604060506 80
    0x715110740c5001d070300006424109500094040d41000021400301d001651140803420045000e554003007992a070b000318108a40c58064000d9100e080980220380040e6004039802c40202980daa0001e181086800180e001d0040c003407206a1100c484000c010405400c0b8030b0b50402da0340646d07035107006a511480203559038402910300c0f08100c8428000c041e0701d4070b00c1c05c01c0700c0d00103442171030000c1410840b80c50b51015510080c0105000d16030206107000c0281c02003000c00000c08092000340581450202c070b007174888030303607159581c1005a41400a0721b05202040504001c2110300b0840343d4a03c0e101c0d913031648602007070144080505184290034607925140c081d000a151340c2c0400742158013008031700d41c0f001c0140f011314000700340b03028000d080c007207002d0010309802850948050a560340958201906003280c1342c1055030326951040602021184010100d944030342d000b807000089101c8680016400303502644000d6061098070100010000160414ad0141d0402e0fa5407901c0c20400d100b0071400252 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 345873309 1250 345872059 345872071
    0xf0a0b060603040b0f0402060d020c06160912080310080613210512190f0e06161707030912020313050a0515090607050f0304080d080112030e031c031e05 67
    0x1d1944c01013110043d40e080e2003a0450302c01408180740c460310222580580e0494210016190040030800252182284034800300e0030300c520f4104010740c20042c2481510200b44009840d1400c00310000b2004c0703150a81d0f541c094000c40742256410701c1d20124041c150403280e80300300c6a44020b2403540c45400102c80441e02039140d251140c03030400114038208030041070010008181c4910748120019409160300c0741820001e5407880c04107480d0603c111b00c2e460a4170141c0015200741c031042e180b155590344114025030704202180c0001c22600d40c1d4400720090304404c03d0180c520314038a4001a40d044d0004020f1221180c4003445840035070f43e032810070400599501c40c0c2500801d8a101e407452605ca040020051000c006000030b0615890b52500c46c5400c08040386841203500002d400e103e51f0004100201c00c84880d40f03030040035981400b40c021f5580346484002030500159442124540c1c1d0b09000d121295070300541540e650280003032008018141000204a001d01c02c9040e0007840301c0036014180c880c0b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 345874559 1250 345873309 345873323
    0x301060507030c030c061505042901110708030406120f06050907030e070f0f170105070f030b06070b040c06030605010216050f03161d01050f0102071a0c0f0a0b06060304 74
    0x7a126142070f1401c0c280c1080440400c40f10040c40d0b400034049115590400d1204c1d00004410340c01c000c1400112081d425011419202090362040030300d15031200100c620b1000c1c6031012582110141d401c1c07900304260031502d1240004580811110762000540030414040141840040070a00074901202c40794003c0ea6084110180000d072824000d410401410005000304c50001e030b0744510b1114083e14540040422000d03140b4200850404840510134010943c40204003034108020080d010718202503140c0141501c0c1c005002159039040c040e6441c20783c04c07203e565040e140038900804004c0c15401170302c01191800f4808605548002074505072120225483c401c0f0303601b803004004407400c030100c1555052182c007480c40d82400c0700c1c0052600524141000c004540c4124019110646050700840c1c00f0702c5201d20031140d1a0b03400100740301100c1d10340013003100f00030743d8005c081c00b50b208400b81040b4610400540042100c80003480e07050f104d018015500c19a102c0004010281c482964060464 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 345875809 1250 345874559 345874567
    0x50103021b0a080901080711070302090403030b0d120908010b0a0302150c030d05011a0f0a080702030423031506060d0b0d0c26070803040b0c030405030105090703140303010605 77
    0x154000d60081085007041040291580c0d0203880181c64210342401c12510200b010035400c00a5801c64a03180c1c0001d91410f0030050138100500a42d0345d076400c0c1c80040e214948200c007107018035000e6401410281d03000307408010402e03202e013400f40341900362108140000c0e03003126001802d001d06100d801404100141003074078083c90b6808000004d030a0f02c032006200381082004030000001040200b030400602000480c0c690700d400082004034040e101904a8640204218144840d2501c120b6404e900b450808003216143d001d0700324510300454011180d9101014002c1100068007041c031503d010081f8100c804051045401046451082d00c0f4250081028410200b580742e46070002440410060800f0b0002c1143d615940282034255000f8211140356104035a0200c3c1e00c030305400001d604280080c801c551a145800e6a248100d10a03d00a0100802ca407031f0410700900071107004080080003841036081c034030080364585103d80703c226402c25500495024500000c81074034100c4600386c69150078 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 345877059 1250 345875809 345875819
    0x1061209050309030109031823011b14030408010510080712050a17030610021b0d05030d020c0c0102101a010f0302070f06051501080105150901090906080109061a0a 72
    0x6811000d4044916020a006030031503034809101c1d8080c40c0303000307540d103554810305080c83c40c9030415240c202c00c043c0f40b403141010600810304100104528401c0c0f92461440c00381c00e10301004840e1601c002801c00c095400080c0340d01e080040907005aa00f2600200002e49480712401c02690f4117200b0940340f170704010010429031030046581042c050060f01920004d511581c1e84400c4400e0485070440020004024010681050808011060340381d00080800240d5002014070340000c10380b0f07141c071508400c0243c0040080a20503150800081c000c1075444a0180304020f40300c4400800040c014403a20344151010510b030300400310a41040010051403011104c0115481000144c0d80e000f8543c08206040008903440c400c1001d00340100000a403c3c00c0c50100581d400051702d801c00d0402c000400103010030360b10f9260410343c11521444141d40d0b09110303001038901126541c4070158041c035284000402000c19007008440360b100e00e0701001102460340703401644842c01424a50410f80103403041c04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 345878309 1250 345877059 345877061
    0xf0213060c020f121f0207060605012c010201060321080601170a02030a110703090305240112050109020a03050705030d0503190f0609062c0402010c241b1403010612 72
    0x70f132200070400e41d5075800c0c8402c5080068854000851042540080c05106200882c0702d20b5000d4074007480c00208000040c1031440c00140c450803800100c10101d903080c00c00740e00035800140195030080c1881c50810000f0312030514146144003940110b04d2000018500e90710039a02929032006500f110095a11060440002034200800c4100400e5840001016043c40c0201a00e0028825540c3e200d00c0740c1035103005414468034140c210701175002801d0300003817640d03101515815255500d180c2c07514814241041c5015100d820790107500311313602110100901501141050030364400fa003c5414100d0344000440b458413040307400044001907c0e1880141d0042604854204540680b012900303030b07210f40400048a2180d4032200c0d0449400c650380c440b60007134034055141c14207400561003452501c1d0300042e152643c2c2c584010203450203001c0e007182d1103c1c81f410410041e4400882000a00780250429035180d08400c0564042000030781c040e44404a80004c0324160740041d9030300101c00d0f400c0310350701c1c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 345879559 1250 345878309 345878329
    0x519050604180b04050d08060604090b040207140303160c020a06080601090e0c0d0501080705010c020d08130905060f0316180e01050c07021504140108090307060f0213060c020f 77
    0x3580c01629690380c50440204182c40d0501030b401201d41024034145450003500c0c00e41e5444e000000d101500007000041e41e030710b800f070b40c0450341130200105800f190400000d000340310740c51000b03241c0035880346498902c44000000c0c510854000c900d030100b15080c1442a10240741101c0000d40c4140511000c3c000307644680003058105e54181000d036800c0303460b9030a240c900b68084442520200012600342c10408680c041d6500500150740030b00341c0d82c1e040800007001018901c1c0c0180c00381d126490322401300b186c18011198030700c1301407403541c030259120480c1a001d050103030340c9144201c880803040411443c0200342442c110164034219880c07030b842c001d141c002000a40d03a84202203661842804040781c02030040038401d03002d00500c00d50302d04043c4104013400b0011010040c03120710a00c828444c00a0414968052940909040d40c2c642e0f100d0444501d148030705400102241d0500100e07010324010368002e0314041701401c040742d4a00f51101c1007140c2000c050440070354400c81c603032005081803c00707081070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 345880809 1250 345879559 345879571
    0x908073c032301050c190c0c0b0a11010e03040e011e15020a0804080d0f0c031202070c030203011a090c090105030a05092103070201060b0903100e1908030415051905 72
    0x148003071980342c82c00c43c21100215035a5020b014000341180154850011403013200300c641c14490300c4102691903d03010300d0010b0250b52083d200005003248214041c40c04411140d49a0000b4040742945100880e1650002d114880c4203140420022134698108440740c019110300010001c1214a40905000e411076880441c80644c0541d441881c0420542c000030009811200010000414150350041c03020710a080c8881c00c0000d078a000d00002070780480040c1c00305400140140e2980c0702c5041040b600e885961000b94950b02c0c20445811050b0480540302c51401c1c1103e0004550366280580c214034400c0e0f004080c0021801c00004625240b141d00c2203801800c81e40844e1580218610100d60140d0018500269014044108262960309000e2200540444a842d0b8140640403003ca603450014103151010551074844500960b8000c200e4a80700b5007140311803a02d64402410b146050790300a840071b0710b40c1d10300d0345030601220341c00740500e43c0184140c925083d506106191084018031016140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 345882059 1250 345880809 345880853
    0xc0a0e0a0b040902070b0108010933060602010f050604020c03091c1a09011a0d02060307170a0b13062d030203060115030b030a0302030d09030908073c03 67
    0x101241c1c081c451000791020304188000140c0d600c034641812842140140e20000e81130303040c8010800000c01115086054654480c0a103041c1d03200885c1c82d2040242155603d01103c2c5411800a40c0950540081842c40410794040040362180000d00050b8031484070051041e0784100000881030405a01d0400030098200c190080702841d655166010395100840110b210740c51428401261000c1c49030115900414002c00f07102006200814803843c05038401a1007200c0100001c0c180c0c038040e41c01021243c11001103070015140000309203004020800704580610f4501074003546000d02c1d88242c4090300c5071603205490f20000040c0c1000b09410704d4641d8402040c0003000000182c034208401e41c06000740100c139402041c407100d03004044130b21182c14148640c1c00343c2d05110100f6004002c07206e41001661021851110504095600b4151540054494440c14034001034a501d05016001c5241c00c407495100b281101d4861000301d0560144070f2032414801041c00c20006000e80b41303c01440b03040311a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 345883309 1250 345882059 345882079
    0x3030c0f021f0e0a240b150c01021308011e11090603040c03060e1e010507080c091908030a0207060810091d0604060603020f0a060e090a0603081603080705030c0a0e 72
    0x100050034071910784001c840f030750b031180d446030305c000d40300b290780105000b0700b010810103145c401e00001c0040c180c0340005900c000c400510703405117120a4040740d081c040d000705100c0d000340d6074040244c02015047c04100070501d940905820545450090115a00d203540c407590911058104202c43e907800a00110341401190000000150860003903c00c2519404060f0452115440c2e00c10840119100320340c60b070340d140504008070190030020703441d0884c0c0001c0303400d500d034140e8401040c00000c0d40084002050b00c22603001403442c1e400001405148001e40c2074a100c1c6940c2c1409940580099454042c60104508148a0700b0203950015660b03901c24409021049441c08109060030350545080e109503482d00c81c1030065040280301a00710110664201d40810b1502200404074054052340e07030711071040c80000c19140708480d001a0061a001111181e0342c4601103000d20407010348003c124089543c0100080d81035025405a0388541014600b0a2401c00f445a00700d030320710074a80010741d111010702 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 345884559 1250 345883309 345883331
    0x2090903070c1701200d0c050408070f090b06070c14030a1502030709050303130308070f020301060b03100503070e01091d0609070e0903071a0a0b091303030c0f021f 72
    0x300040005148002d4408143c003400c00d50242034420801801000e5100140a1002501c032107081310f4082041d000300244409001074200c0d514400d55102c444584100034001c19122101e0b0320f898101d90140b60700708006007110003401400c1c00b4145001e002134668600403c840d2410031510640100020706075a600485031b03680070000010207034018840359002c03040003e8a5000009100548000c800079400c200e106e12560926043c2c0e4000102039200c0400c0490810a64044c440c00d420741c020028400389440da001030078980c100300c1c0d04484c039028103000010b031410041003101c1500c40c454200c040d01ea0034590040c019040d4484c021034500705030081e100030b5810620502d4090b9002c1000b034400c9910703100090b9050400903100c004160810800000020280348214050390b180c0c4050704c040340ea424090074010009505807982161898081121840400881200403803290f2800c00200f01c50582c222801d211141440b0090703840034a002c541c2501d200d00001241c0f00701580070900b100c0b08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 345885809 1250 345884559 345884573
    0x20c091501051602040c0f110f19080903070e0402130c0504060f0e030d0f27091d120d06080a120305060a0305071701061a16020d0b2418040209090307 66
    0x709400c01b0000713040c03c11500695901ca0402c1e10260616401441408203010300103444106c41591611899042800c1c0000c021078542940e0094000601f56014035545074502e07080342400301c40c228426040034100d00c4c080a0b00d413041d014111490380d1942e0409081c84011ba074610b8101480405204d80f4440c5403641795000c0005452401d000e613201100ca00d04000b000e4041c03009440c66038262111300b800c00400c2e12210461408680d0b01050211f11079020f0000020844621b00510459000f800140340705010705030024500309030b1003001041600e50b1044002d484d0002d0ba0030081002d030041526980440c4a03400c40c0d0740007403000f003484c0040c076500d40d2007929154030395112400e03444603070000403030b414801c1c4901030041000c3d11200000e040405d540ca1054810a00000040b811012080007591603241e00094101d9110034102481c0c2800004c0712100c80c2040c440000c07465013240040c0060600c614418504413002d0302d1403000d9100c660800c6040d100051501d642480180b00303c101160306 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 345887059 1250 345885809 345885821
    0xb0a1d0408040e1312021b060a030608060f0114040b030c0f0a0f030501141501090e15060438040527040b18030301031a0a0b03010c03020901020c09150105160204 71
    0x1080401c5041c04c1d2003841c3c42184040d80c804050103542000062011361210040004003044045885d1959494801019402410550403105080c840e003010000d01c10b2480260030705030340400744841c403c40250b208020035100d01c01001a0141c00c11103900f581810680f004010000d802040c0100d169218850040005200c0c2c0c81903030300381e44510320801e4040b03152515680084c00ca000840c4c0b40c0c580d8400182c02d41710075101e0025800400720004803880c06101e4081c05580e4010410b9544035a59413424512644000b444007000c01520800c0111081c4000d0400c010320451603001d05040c40c0c14100000c01160388140040c0001c01c60400e20710b00c0000782514411031103054542e0040c01c103280c1441c211500703044100e50980c0108010700c0491940c2c0c4260b800360114501c1d1070019618030542c4800b500e4040007040c0c05d50b00700300e03120580c690190058030808800b0303403c6480081942081000305001619407140001018007050300951045006105152500604184e5003585034081001c40714 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 345888309 1250 345887059 345887071
    0x618122107020a140c0a0909170f07060c05070209090106051309030207090c03051b070308270a03030e1015030b0705070c030501320f10030507090209040b0a1d0408040e 74
    0x40101700341010300d44044101c0240c041c000d010403902480d50b0340c8020385220032842518101c8040b903d03024000e000b60850740441e90228052004080301b00c4050140e8200c3d4000b01e10a010180000ea001ca10504c1b420301240c000a003803040981a03c0c0083d0700801c5c0781c52007034085000702000480e00b84614062250b0001056400142ca468600d0301020001c200c0c0084103451403040001e003010136884500550040c0c019158800d03100b0304e9608082001c50b000c0c85050450081d101c0c03070000d042d090b0b03000511140c81030054401a44000d00c0100456125010300340815410340028004224030585c00c03a0301a203903041440c0360021981b40d40740701851039802154269111140b1441445030301030008958000300c040c802e40002001601c0001e42001828400381c0703c4018005189079055648010045411009451189450310032180107580115a42400382d420141d90341c03d07506140d01c07000c08a90300300901e04000001100742104407107001c1c1c01901c40c034034188004604080450b5603540100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 345889559 1250 345888309 345888313
    0x207080c030301080f0708030a0818061504051b0313030e09010b040623070f0309270e060105031c031b080601030b0901080c0f060c0618122107020a14 66
    0x241c5400001071402c03171001003103038a58000e2001000060000001d40351120894203000034161303078a59145e100020b928414211034810442400300a0220444010b138241e41518180029502c900e50100190509980b15005103010000900c04c2d904160744101040d10910f4040255068003001a070b24010a0304080b141640004003040318580041301c0e0820740c4d000c262210401002801010b210740079004c0040d000b08101800081054410480c240c081c0c109070012034210f0b0702c100210b0071b00801070001c5916452401e00d24400c4090300081d61030407104020000c01c0320603118403200d490365400d040b00409058480c03181d41c1d60144501c954000d01021540c0384040c5180070b40c0014169580341c2e440e540034180140043c080d120000c549040110000d485d0b20340890b00032808550759104800e080c403e1400340805018601004c40ca110b907803503a0500c210b80ba00001e0341c1495410b44202c9114500e10030b00102040b55400000c2041e0f0ba00082c0c1d801510000d440c151101055101c404480b28595 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 345890809 1250 345889559 345889561
    0x40e1501030b2a0f07050a0219170705030d0f11060703020a0815010f050f1c0207120e0906010305070e0901080c1c050303040b1015020114160e0906040207080c0303 72
    0x40302900b0995080d020b025070b083c4840b2005000c0910b00c0744000c0160303120000124403003440000c02c41c000d05030754041c20307203107d4461003841000041c031540943c8451414103d01007900b604002784503000c0e500000c02809006c0c0701908240c8000002d9480341060003840030034083e043c4400e00100b4410b00403901d0251b1780b204103000c010b0030761030010701c50b4240000c0032481030240e980c00042c25548003a00d08046070303101044080300003c0d0080120143c03010081c18a400c01c80c002a1700600705007842010703858600300c00c4160680c3c015104810080d0024905000501c0c558030a801c05500b0400380d08140c80110b1000010415050091f000300405038415080c51841d410941030394180c00c0001c20003071031145001e540b5980c584c03001030800b81503009031070049000101e2140c0d40f00c0007800300d541e45003003080610380302130b02a00700d02e80b42a4980141e000040d800d1011007840780e440e40910360312840603080e490100305110784050503107500150300f8001d01c800203030760340000d0251304a06e000840d12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 345892059 1250 345890809 345890821
    0x30606030809101e03020c0309120a0302060c2817070e0f061e250506071701030b0601121112010f080715050901030915020a18060e040e1501030b 64
    0x1401603101000c041002810b136840000d4044001440300044034600542c2d070b4050510468a14001e103810b0a5010039070300d0006014940006420610b03070b01c00d030240c0f805595280c070345003124003580e81002c010900c4c0c8545980081e0220281e040f40000b0b504018100810021054a103920704035843e17400301c1d001c140500030610788185a1418080c04a4a0610781060759074002e01103210300c01c2501255002245136403200c0c5840750b542d50b80c541d242146002545490a28a27500d450030750f01c500100d4a0b2031841074070a01a2152035060700d4001564a0382c98407104011280d00c000902c0d4482d200e07940305221005007200c04010700246800020031030103541400b8070f80c03a0481c01d41d80f0000966100120400584e010300c180103201c1c4840e4148152103071140e10050b4084e0001c042d0003403030000c2910f00010a200c00c1d0380a80302d0710310303240d0703c0803440803000501400000040c01000d003c00c2601c0c034042070f1490144c015290044503a000c1e01d40e1030300c2500340101402402e800c02c03901454a0820000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 345893309 1250 345892059 345892069
    0x10e0c0120070f270524041803020d030b030c10050c100626371a01140109050f040207030c050d0906110a020109050906042004090b040b03071707030606030809 70
    0x1166000d04e001000740b42022400421410502d02c881614121501c00d52030f0346a4855010252001110480803420003a516001303407100103640072000420f10706003108405040000b01040c0c01c7c2805071980f0700c04a0140001d4840d604050307155103607480707440d000b0a00404603014200c02400015110761902688010701e049003104020204202d600c014603031000c40c2c58505000301c01c2c0340250b42c24022115441c0c1d80e00388e49900503501400742c601400d0100d002100040ac0c1c1e41c101c5a591486003030703002d0500c00458084415111300342e40014500300c840500d181c070341d00070034009101cac0c18028840380310356503080e04240940c09a078010a400303140c02c0102d0354104000d01c125001d04030152080c1c0002da80040c0a2140c10b01447d0f025000d020009490b81c0c6440e4030041c1001c0c03900340448204101c0c0310010810394061b000c4ca451503400c0104178000d6007014094850070040c010013030020142072600d65201c00081c81d051001341d1080740d01c0000801d009100d042d000d5401000315560350038070341081c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 345894559 1250 345893309 345893369
    0x231203190201020310050d0312090b041103060423070513141b03010e070309050f070302100c03050d020c0313230a060c14010e120408010e0c0120070f 66
    0x9815039004004000040b11400c4404046c2c0700120b42452143c5c81a05046810480c988003103548246801101c90a0042074044184102d2146c004050090700d4001070540b102800d44d00100b2a1811429901d88003942802d550310029030303c02222a015a58400a20300034100400158007903901d56144c00442c0324841c103281e000c00c01591400030000b103190780681510051040181c0c00c800300002c10001486901b0081003107810130220380c03800e6641d50520b610b0b0030080c0b00c224400c103084c2111410850180f0002440c0e903400d52111400d0031000d080010203944a03000707004031070004101e00f001c002c40c01d0501c1350184c4000301d400380780340020341c00032900210105803040c4280080c540c1081400d600000110f0746a0340403038104201c003240e01003a40503164582010001d401140300400e02c4d612400007a201f150034800c02840780c094490442500d4540c2c1100150015141031b446006a000300769080400c060b0540c201c0324010fa40d42d40e40100400190410003d0014a10803032100314010b070000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 345895809 1250 345894559 345894607
    0xd090e011e06050a0905060f0a08010e060d1106070b0103050709050a02130b070606031707020102010b122d060c2110060309050f07090c09080c0901231203 68
    0x11680401101c070300c0e060201c010701c194010050002401c41d54070b44142010401031101800050726528a030103243e00710b03040349a07280f0004091000000e244044200080d01070340300980744484080c181d480c0c06020b4400004910780181c000c00030711000400e8451164000c40c0250064482103052481450581c1ea000e4507103d06240184444107a0920110f07803a000c860040403010395a10300c525046000d011560f001030199800c088999000e402100c00410209200364004c10120a80c4d030104100c1c10080c1d24056010340c071040d122500c8a0780d11101c414140668031b100b03004442c0c520941c5192a20841e50505801401b20360041912002c0004120328414801142960b141078600107160a0b807078803031001010707214034165051020038840c10103840403d5054884c000e031030704004d101401145444034001250030300002000e540200c0c4000c48485c00a025480e181d183c03500310327a59039140380000c0c4003074028455040aa035850070703a43c1844101031401345850b195a150780d40d00524414100d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 345897059 1250 345895809 345895829
    0x80706050c03040e0a0b0d03080603071a0f07030c1407051c03210f06030b0402010e060711040504110d0506070f0e0d12090e010603060f1d0a0e0f0d090e01 68
    0x728500c4040003005407020380710034211091081e42d99002017400b40c81640c1d83d90342c00c400410004403e06074081c0d01356208490907011100040e558445400c44030305020803a04040200340100300645840304010810b4a0191418142d03140454640750150b19040d20442e141c0d80c40407208211500b40306544c0303841e1186140c10541000c4903903c001e407100da10b284055140310050b00e800c2410070b0701c41e070180d025484551800c2081d1034903490f210700d40c40416038090340400e600049602071031600c6011a2a03c50f880340d0081762205003201448041c0c04042e00440c0c800070800103404d250f03202d022210700c00d0340c01000148440c0c1031044c0c0180150b01c40e140e00d00204100850010000c0e01c80b0070740200382e030368420f8469040995800c01100c207003581c1d4001c4802074071a440001200b80e41a007003e000e441c6160707043d28815558000c07031100540c03010884a42071504034000b0307140c5011540320007104001ca07801e540c0ea91001c800c2860420a00c00c00c00000703d202c90788280070201a078041e46015100500e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 345898309 1250 345897059 345897067
    0xa08010b010915121d0d09050a0b160f11090a0504030809010c0f0810030c060914100804080c0109050f01230106091a0f13030b100302010e060c03070206031008070605 73
    0x500130582e12800d05401e4001d92a1020b245180d244c14460909090505040c0c0d040c104681900800601061140e00d2280307440c42d1000c1030300c1e84154200c0d880d015104051605686280c0d0707a1030460020010305803922004091030380030b50780310881806d1141040340000226883c3c2854082c0c00c62002505111035680741003c503400352a04103601824080e51401c003e00306a8402ca0780202c640c06540004100c0c0010b0040003c800340c000803010140c54101c8407500700c090f010001e010451030003002c2c100000d6a00c402140210f54168004e0641d00b60b20400403c0031112612280d1400e8201406080760360364903240180c10780c0c0940c0402000a0420003c0b90440d490480d004001000318081d20344041038a90032180441025001c503150401407100d03658a032081c0444c100703c0e40209101c1680c106034410700182082441c80e440a0036a58144c445000304140340c0706004850300080d201a24034402000602c01513a11100614810000600c082c804681032060b480c0c24400d40703a00000522600f44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 345899559 1250 345898309 345898349
    0xf0c03090b010504090206071a040203070605031009050910092414011401050c0a030c020907020613030e060c060a02190903030f03020904142401021605040504060b0a08010b0109 78
    0x51040b81120001c40e0003081c100c0e098000070350701e0303c61490010b05400c0d201000412000052281610a0703000b14160340031b05540f85015202c0344000c03582ca0141000000c401e002411440e404242c01911020842c1c404505003515035080300c42401c0d081e600d1040c07003250000e84800310b9906070360000d03448406100141c0c88200c4100c41d440d06015040c00e00746e41303440303904143c0d200380191601c4a040030110340b0f800c81203050250400c0f0702800240e02403100c0c600021360305270000414070300170098509201c12088640c0c804440d100350500030560311142c00c000b000e445440821100740a0200c1000060f035985111100d4522079410180c00028003070005408c0001c01e81294010110500c80c0c00c0159941d180000003c0041110b440d548103151880c0003404101c1610f45008004d2002440ca003501d4844540300590741e40c0100c40c400115900440380501560500d80c00a42d0424402d00c00440d82c00356000004250403556040f444280c0c7d512030400c40d2075a802141000140070500344641c00415807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 345900809 1250 345899559 345899573
    0x607031505040e0c0906011103070b16110618010e0102120a0c020a08040b090f130f0b010e0f24031602061614030907051e0a0807080a1b050a090f0c0309 67
    0x80c101c1d917100d0380013503001a04503400341212500368200c3d00c060325501c640b9480c0c0104103600075200060304080d0070a124805500951402e102c450040d0020080f40c1e0b604400014044560500a4030a540342e80004a401c1d100340041d082c4413500502c11085464144040c100711121b08606600719485005241e0108003400219030a9801c000e035103035a075a0401d008542100300302400c503500700c00c00d4160b045c0701a146502c10841e801212000344001080c11004640c9452602105d550204003460035001c9464001701088220342e2003490a800c451801021065941046901c02002c011801d81003100c598180811503211481d003003078080c20013185100400320687c0e40c000d0181c6000000204004420400940c2e004010051407050265104140070300c20001940c0254010189481d0100d202a00411080d0507210f0142c000c2040150315284c042540300000d10641c001c040140c000b1855854102c103401c042d004c100030102d00501d18011410460b184079401d1400c242c42c24000e40001410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 345902059 1250 345900809 345900823
    0xa110f0714010507030212040f0302090a09030516022d120f0304140102030d0f0b1003020702060702010e19060c030f0219020f0109090f0504031b030507120903050607031505040e 78
    0x70a180513500ca0300c0d140703010f0f45000712607041c405640b130000ca0006080380c1200c43d020142c0b4800e903806651904c030312846005550f15404001c0100b0402e00076449400000c0790352010f50b600003070031800540345440d040742e81c001d1000440420001d000c840c07081d2034101130000b445000380b400020264203414000d65a201e0003280a101030380e904042c0b0b507481c40c3c6c3c03003041030b81d01c40305900d5400c0061404000f0038400410010b04503d0065641c4861002a940a8800e461110f40c01808840c0b6191199004440c00e580752415142d018044444661441c10080c0d4445c02600542d10384d030044540506019059407400440e6108562180b46100c02c240c859140044070154184c0e5507680c0300000c00c0c01622100610f4005040e418a06001e10f40c11401c242c0000d40101d00070b0300c64400b1692803c1501c24003103540d24020740415410041200040c0c078403e1b81d80000364282c03510b01040340d100d581d02820614190740d20070000362034803c41101c0c03120038000e0b0740003031508880800c45c140c0300c040025241c4034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 345903309 1250 345902059 345902099
    0x20a08070c0b061c0b0f0a18020a1806080609030703080105090c0d0e0c03100902090106030507210b0603090a0209090606130e03070203070b0a0806060702060d0f0e030a110f07 77
    0x8910001081c003a0300d4442850300030342c0c005032031485454501c40380f4094030411034000200b14108023922418003502c2d1415401d0356005010380b00c0103410589000c0d06190091024401c842d0380340c00010300c01d0024071106004000341c50140d9554986030400030580071068100ea0311554083d4240101d4101010481d1000404007502180d4180e40031100e6003001d040c8904503406000f8407d405030303994016885088228800c0714030817a80d907203881d002c0302124811a81080032461001b9220a184451040001c8070b03041d90740f0100700c10a5030800308289801c2a101401280e008a0141007180342405016600201c1e0030000c121034942400000c00c00a290303640c0c00040d80e07940108101000c400d0085496641d00901140d80d503036550f24010120340c1c0a445210000744980020800c82d1400f141200d851b16001043c0c1c030309084503002c804c0014088c00e41d0b0b1903941941c415010107072030020300c007910300d98071030f07445aa400c501405590307410f00703603050b07101d030380c1900442da09010080c401207030f120f9500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 345904559 1250 345903309 345903319
    0xf070522090509031c050609061e03010204032103050f0c070f0803040f050d0305101a0d05010b0c0106051906030c05120907060e04020702090402040218060706020a08070c0b06 77
    0x2000305a1400d86181094201003025030900b020802290780020007040040c0e40b041402013241d207004d1400c8211081903500700d5200100b003020408518080d103150040d24607000f160140500d0140009003241c0c000d40c02181e03040007441940301c0c00c4d05034004010b403004103420140200d01d0300058900c5210402003030281342c02c50200c0c2010900c4522030a20790859800034095642e41004c1c2080044040d15040442e0355208007100250740c14800e0041c1c5000b0500c10b0007600c1c850f030410030a510f41005010803c444040d085c001c0c0018419580110390003040ba60340202d507988032119066083da002500080e024856910180b854503110202c2581280e04070f28000070015503442c82210103100c1e44428841000c0244207000c06d04001240100c00c403101e0352030f604110742c50702040c00700340c1c0100000654404140303400140581020f0f00104500060b901021840f154000001046500701c0001903400582c0800d40b4801603800c903240980000950600d42c000300000d81e240c20840c900240064062 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 345905809 1250 345904559 345904597
    0x1d0c01030f02090402030a0e160f030f080f160501050c07020a0302040c0c0f03020106060305100617060a150c170403150902210604050c152a0303040f0b0f0705 70
    0x5400c1c80c0e042c0d40700c00718010402d66890601c0140703040a09440d480d520558014a1074800c10350324111030304012512001010190245152a05440e01c0740c42c0c0400c3d5030001c4100000f013804150280107250b040c80e4001c200018020500b0f04030700b120b600800354965900c00300111800750380c9865420040365130465001c22011103048003110b2282e4550710081030700500c40105020103030190085015180983c0d02007040742d8950b019440450070328401c02000c0b80c0b100803070300040ca0000c1c2141f41d2100002e000d04a40999407203101e40c00860006615002825102e6454100100145402c100c1220005210305182c21500c45180540210b1680d403402c0c1e81c1c40e2051011034135681010800f00d400351180810051041d6640750702c6138000c980880d141e0080c40b550700c1e2a450302004152092080c40c0e02d031410320200c0015070a584448074081e2408000b0300e02c11041c034010410003144034a104e06204054000c8501e0141d40d041d10141143d20b04d01d80038020400d01d9130f4010192100d40d4800103940d025 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 345907059 1250 345905809 345905831
    0x60e010b01140d0b220b0306010501080a020c2d0c0405090304060c0f0209040c08010b01020a0803012313020417011e020315090106020d021023061306181d0c0103 71
    0x3c01c0400303065a0094405d00c00010010386170b0080501100302c2044c00d21003800c5510415480f00d000740030b19804144d01c04049a28140c0d01d0380a81003c2200e04101d498040b89803036900e200b00d00361a840d17141d4074110204045105c2040c444080ba40d14160f50500444c1480074100d5140d0013140501010080c01c801414240f00200031021005500a0b1100d103040c140342c01c2110321101180602090396003412940c0702954070000788450b0480e005002c2e5802d50342480c0c2042100a400c00030100c0500410403d481541c1d01c10f0198400018020300050b60349150484d07a0b981c004810001d090706924100682c00f040054040f03802c0d030308040010059407503580b480c11842c10b031540022107070095010400410f40c16000541c60015109540881c2d40300c0125410004c199000c0004100c0f207642d141700c83c00e44040c0350209968101000a010b806114051840141212a0b07a8080101c4c48140c41d401001010036201d842d4411410101c00d0461444044469039240c2c14880e44504240e030740c10043d10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 345908309 1250 345907059 345907061
    0x50607020405100902041409010608040201090905070203040801020f130506030705040303050f071202010b01140c0714010311070609030912050309130605030a0b040c15120c0c0c12060e010b01140d 86
    0x3000c0c080d151011034545487e82070007602d2100c0306820354041c81382c000c00401c00c0c1e40a80324984c0b04540c1650360702c0406080071541006440042c01c1030b0709512083c400410004021b0002d4485040c140107460f40b100b01c01106030981000030b502450141e0010001d100d034050b840230484040d00e0f014207082d50760b40d900c4100b07240e00e4421400080c2c10313201c1440240510583c1034000c415130700000d0b40c4100809500050414903031040140002c9036038080d01c0d04004e000b4120001d800f6420341410000b80c108040150b09000380c0c400c0000310303107169490500004141c0c20210170005044406d901000e9152142d4505036248103200109104041b480d03403c6c40e840106402543c0074001c00340c20b4801510f05460440e4000c034040e0340881d6044c0c41c030b80c00800c8041c28032500703c041c2500c654550110f04030240484004060030a401d4003041490b52450380440c544844140c001d1881940c00310380a02d80e400d10008444d699000f04001da410540100c4150b83c0c445120140c49000000d2070390354060110345c000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 345909559 1250 345908309 345908341
    0x4030809160303080406050f071211040918030f050a0c02010804210f021903080c36120d020601050f012705030d0302030903120c1b030c07050a050607020405 69
    0x900e807a9030040e0120030554030041c082c5c019441100d090041c0c3e11904440000c016044840d80c00140c03a0300200e002c40c1350550081481e40f01c6544c500f9240c5a140d5070464207841980e0341c0018118139030500001055801416440d900405140990500100000003030541103c3c15020741001160307800306062003100080004035680240f10720503000e4606002510117407884a82d000540500704240c8003001e206089440c040d41c0c5680c0750422981c90000304000d41d00208141d0004180321110f00804207085000345480601400042038a00d15440812468043c02c14180502c2c0d001200c00000c0715400207545070540310b003104c0c0500c41d05400c9004949400030001100c010307030600748400b061a04800b5404098480c10340c250b6543c00b0961f10309800303922054400b80650344c802c0090345000f1000e1a09141c01c0740030250036914100041c0f402c40c070800c07c940034140d0150400522240030280030002c2b00018481603803180100780c0b030240000c696010310300c40a8061900d0b580003480c01440d040b102 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 345910809 1250 345909559 345909583
    0x70501021902070617130303110c01090813061e0e03010f021210050603040c060c0602070f0b071d0d02040504020d1709010201060e0609160519211404030809 69
    0x30300e00501241d00007552090307a4481c50010401c0e862401001c1c640b0703540c8152180c241e82501141d1070103d40d40c202d0080c20942600780712044140401d505103603082c0901c038001401000a651201d01c034002c0040e41103840d621800500040c280d0481042c070132080501c00c403d01c01d0600c00b000c0e0040d0302c00b29001d88810b8104e9200075200194040507901d4030500b09003e03841085020409a071680203200c0f191009030780141800b140103108000091083c0500240f440c49040094141401075846c20043c41410208441c3c1c840c0170f004005c066940200a10401020511845007006071074010600c1480ca8881c080e0086450703500040640d00e80a1100e281c03190301c8100b1410000080b0030000749034200f0050140154280070000401a4032000224050103000304991000d49580300e0010030740e07503810740b551f092200030700c03402e00080f51140c0c400000301c100382c540860804110011074030b00b01d801620407030510704d04041440750b031046040455000b503050804a4a03034032502002881d0040103030407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 345912059 1250 345910809 345910837
    0x150318031218060509010c14030f06011205090c030f0d2c030601060528090e07030f05161404060203160c12060b04050601090b0d0c05090a060203190207060e0607050102 74
    0x6080b00b0001641e1040d8803c1601c039008001d68142c9040071100000301160325484c401041c0042a680000e0620b141d800c0310301414a600000100c05e082c8041c0d0302e003220350404540180740000128101808510b60240c0864058400c40c0b40d0300d2400751000b03040109074100c80180d05440300044040d80031070380e03280c0f40c02000c40d012980d445d24000d115622100c40000c0401030740c440401c51000904811800403041d448249105080c181010001c1d4001072507842016103800d0724220800551181742e00803d010301400c800e90701d0000c80500b03069075410340026508420841040196404019502e1003108001510310b00070075401c00000442040d0003501c64410f400d6020b03001c00c001c6600049520f4403c0d18107124560b503a00040d1440181d40c0f0030400600001c00840c1001c44907030b0b04c0038408210605000e400c3c0172032240407e03081c1c41c05800240140e400042c041c50030340d520015042c08045948014042076090900040c684c1d20701a6403140600b00110311001001020b4059480c10012000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 345913309 1250 345912059 345912101
    0x60204140a0803043b0106120207051f09020d0c06020c09040507050d03020f030f03010f140d12030f0e0a0201030501320a0b120609090106031a10031203061503180312 73
    0x109214000420b100d030b040071232800d007150450300f4098002d0700c91660b0420060841c0a0101c2d04070307000c5442c0858803102c8255502e101b400117aa9541523150450700031042d002006051010103880c0c40103080c0e1541c46024102e007000001000020007038240d80d4269411022034180c1c1c94140c2c80c1c40c0d4180319513807080c04081400004459140040d60480d1520f40d0f0048407281d49001c1e49413007140312388813560009101012034010805884010020b0f40591030300290464030120070004076201c0500050140c0c100e49030038001d56038540100303030140040003640400c0c41c07540c01060a94040c401c0d6104910320180b0b4100559940d40e040c090010078161401603907803003e10640c00425201100d51921034002000458002401489807c05407076111b00c0c9480840d10501c4441002c52005040c0d40b040200018040f001500301c0010b4100c440303042c3c5011400d5810442e0380c03001214440008410180791455501c40020b150354180380c030030b40604294480200000403500035000600b07400e00c6a02c0013032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 345914559 1250 345913309 345913409
    0x9090807050a051b010c050c041a031603021203090d1b03080c03070204150f0506071401020408030a0305060f010e1e041a0315010b0405100507020d060204140a080304 73
    0xc21854101d69030b81203540104503c10b801035806d0700407001c0c042c1450b400404040030600b469408020651486880208401d00c0e100002e0f1420304c2d840113100110008840410440c00c200004100d16403907400910308108000c00402c0d80e00704000d10180410303051071290000500c06039000b030040e540202da4103035a0295072050950380d0f80141c008900403840d01c41d01a0543c0580310708001903031052048103916501d01010458140c0103807005a80c0b0456004d02080b50030000d00c006c1008004560155441e45c800803c0034045444c011729003402503028400910580c1c1c0d000401480444040707640304802030361403160310858050442d04c1c0390040c3c9482444c0480d603254131103900886008070100d0342c605444507580400c161003803262595400c0180018001c511301310001c0c1c41070a0f15032801d68100840707500016050124804140c48442c3d00140500c0034112401100860100580e0401e440341d24000c0401da41e44220f10804c02034500c0842501c42054003141a80f400194000040003801094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 345915809 1250 345914559 345914563
    0x6041a1c06061106130804140612100e0a0b03030d0f020705070308040807080f030706110c0303010b190507120509030106031538060a14030f090d1103030109090807050a05 75
    0x8120000080c0300c4d00c000a41c80324003040324650440e5202ea5aa410140382c03010480c10b0315034130102207600400911030a0030740803020091603c0b5108501c1d001c0800781c031740401c501c44003502502c200d40e200c0c20b00004440c103844c00030440e0040368030040700041040e20502048008d0007030302030081490182607400818400010050001e0381c40c10400d9815041e44c990005a491452100010413a041840402d01156080e0700000d0030314145020a407400340050030090035039000340c000e09250540410002511000d0503013008600400d81003103807070000c65803190000440c010188000304040001e1203502c1d03860a41107240111750000203135000f00707542444100070b401e40031040c1001516603251090850724800c0f5040d5106850311500c05007a01803c1441a0381d408801c27a94103104c066100d0103803d12840004510414051340e031142141000080581802403508190080040d2900031020480010044a0440d074181030001212030321171078004010b00881c0c00142c498014061180280880 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 345917059 1250 345915809 345915827
    0x40605030a03120b190b070503120f07170606121009320402010f030903090b16030e01022a040b04090b0117060403081906080111070b010506041a1c0606 67
    0x43c5030400c0c444502148103114030b61039014290001c0b040004010401d40700301500421a0300d00079429241703002c1c54100303810f040c1d0030213945900c1d50000e80001c1141c0710f94826808180c1c084006540b200c141801c90010350795009481e2425070309040c900105500c1d18002c2009002012464018082030054141d41d5039941c0e0f5040075003100100158071140c007805d1100d0f0070361140390b0503140c5018080c5881e10880040059880450510400300408204032210310094110310f040740100d490300c03030b081c1d1030020a0030505d11070607419580310308100460981c800c0c99060a4406000c000b83d42a2001c800050282a08170100c2d90814a048801810b00010003221816035a040545103511019000301c659500c41c03c03540600001e0910000c50030308880d02407207400c294076001c1d02190141e00d40d0740b45403c40e20a06e1020f007001400085180070004030710807085c0148011500300382028500003a99803142e85103a0100980000020285c0d03080c08400142840d4030a108803c00601392140809840011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 345918309 1250 345917059 345917087
    0x10f0e2d0a1401080c090f0406091707051605030706140904020424090602060a0c0e130c0f02071a1e1204060509010c120e030708030f06010e010903110906040605030a03 74
    0x2c2c4600200722010002400b000351304000c0c1120290350740e000008520000041c0040b544203032a4500000800c007000d1428160a03042c1e18519652003862614501c0c0c1341c145075014021140750001088650f5012401108403607260400f0b01c484218441c1e0448540314104c107481c0c5c028404900071039112607010300c401c41c296601404618131100c0200036646691144190310041e88203000141d809034664000301c0c14000c507401c06c0d0f0b120043c400b001806030380410f0b90004903503554060807240d003a8002c1510202c41e025002610400d8180708a030300d034020900001c400c00740800503514020300320f03041100303281d20180d0207129164148540300c444044010784003a40c88034101804900c3c004011303c6410480851070301d455100354555030031000540180c110306074550100303000c2c1f540403c41010040d80328610300a011202840c013080090610354140455030f040104010050000030000c02485030300c60700854030011035a4a00d000100a880540c00a6815009119800080541052040c0402c030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 345919559 1250 345918309 345918341
    0xc03010e06040f0f08040e04030e04051503300f090103060501031a0f0307080d0c05070e01030b0106120b06071a01170a021210061d010f0e2d0a 63
    0x18464001035640c041c26100074080b040100815800030780f440301039140c3c06200341071160800c0c0c5c0d107510203a4128822034003500418005007040485140c00d2041e25031000e4082d400010001090700880d035109119034074640307461032020350360303800008002240c0380340c3c0880a040e070741c5c9103402c810030ba050781c20483c038540c04203060081c01b1480d58024055030802d24451921a002400400d081000d209061224240c25000f1440082290308040c0611000d050807512032814541d5503142491800380264440d41801d0340000050000540000306241181c17103030310304400c0d10f01c91021468028405810280c3d881480040c140c003c00c142c00c0d0802540d443c40380b01d11445a81c7e03680390320490030050310303070040340e40c00041c154001850181040d07030703900c150300c8103d0b02d0000c0854540d004951050700509640c55001c160754021400c2700c2d00b0240074100306914448001e10300340c0000b29003d0040c02102550708070808400207807507580961041400e99221074070300381c10090101c500401c0300c001882480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 345920809 1250 345919559 345919571
    0x12030408010e06150103020d091b03020a0b03010b030f1008060f0115080603120a0909060905010f06020a11090702030913020901030b01051204171209030406110c0d12030e010e0c0301 80
    0x402e02081d202d220f50008a0810162a012801140250b01541c410011036036101309040101e10061404201b0b10008200908510304500410481801541c0326810a510400060003400380f90b0040e00d4101404032036503103190b150a44183c0301c0064603049172403144164010800d040c000891250f049403260000742420600414080744c1240048540300d4041d8401140e81c1c0c1e518150034004c280300c903803a24000c481d02e5221f0107800e0a6403038561002000940750b20052086e010754028140c010406070005001505040c3d465104009140c0101e5100d40001340000d420346000f427080310040e000003040c2c40b02d00503204490702c000750000805030b40041c1c6032580411103940101d046817000d81c0c0c1341210745040d90316070395124a9207a0840d80c40741108018800e0180a500c0d64a003580515000f00140d5180d906200d401450342d000520440c01d15405050078124a07111401d1520400390803800380c001402d231200e41a0007410300c0c2509402550b18001141140f100045581c2c02c0c1d2050480c0240300f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 345922059 1250 345920809 345920831
    0x1a0c0a1215032003010501080d020d02061e0a06090c031505030a081b070b04030506010905060904211107031a0a05010b03070309020310020c0a1a0112020108060f1203040801 76
    0x100c03094210504086004a81c041c00451402c03240c00140c2d0360120b100e1400482040082425070341300307a03c001c000341d10003400600615018015a40d0f00c6450f032004040d140741c00e00001224840500c40030507010302d91307008034042c842036400040c040c0c10341c0c40040c8100710500800800a2058860203401d03e500c2c284007140a2401003246044650014030540c1004168440040c58440a0740d0401e52380c07080e100002501c01c0d1a40140c0019801003015107002e41c988171b031080507100001d246a1040444204100004001c1450506500680a1100315014202c501900ca40b2707400c0884195601c5516400010070101c800711003846060822541c1280c1c4408401d8030503101d0a01074080222800c0c0001480984283d00c0328510780d0009084691082c113000c4090100e07032052040d8000b58000091010600000341a60b420345903400d0028000c0f0f600d424111007141c1d0308103800074104075041020404540c0c80300343c0880302690042144d2402d001d500412a5294001d03c103500595081c4000218 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 345923309 1250 345922059 345922061
    0x5061006050909090a140601080c100f0804050c12030a110a0b01030201140f0f0415020f0607051e032805101701020705060c03190e0a0f1a0c0a12 64
    0x800c035052034440c1d904100030142009070308a0001c100108a120702d24400010404401100000f0380405010300750b01e504001004c0d0034201c071718400c00c0c040d0101c40d60f02030001e540019030400341c191502d054021620369142c01410002c04070070084d480741d101419100208008001810140c60075142c070012400e5481c01a40c541009140181400090758010009940900314150751a16040b0500b441d0a1000564400680168156901c0304502240910040310000389120410f001030004200800ea616640da0740d52000038103207020405e001c125484010141d20001c03c1140760b04040e941c0b640b030030a02044074003040804154040c52130303c065000c218a548180c0e40a0200da14040c8500790820b0300040e44410072041c418010740d401c00c414004524188686401850440c0615541c1c0c1060604502e04220b080024007449140000303411650320000703041e1190301c0d03025400c10a405041d05065002c0091a2040c0d540780c1e08000400010314407100040007022190344030203606c1032042d00c0640c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 345924559 1250 345923309 345923341
    0x20c040f151a040302040507050c0d09030204050106081306020d110f0901020c220c0e060703080403090510080a09030c0803010306090618030e130216030905040507110a0f02040b0d030503040506 85
    0xc0000ba0040005001604040d0000d039442501c0313040c5149002c004c1c2c1185460040400d012400207050581c050046252274002d10f0f00500c5d45140140e00d40c101070703154119511113004018030041e40040c00780d00c62030f0540c0194401014500740e80b61a14031541901906a018000c1c10340180217403c40e51400b850032811841d021500301540003903c0702882c1809000341070b64007801b030a1001e80c12000d0146d03038412000300065841b80d605c07544503041a180203841811545c0010340300708082c4030440b0905034014200c50384109a0b030703008201a0391f9800c041d07a041403541809490a82e000001006201403908032889007881814100110550020300780b25048640714024000b031070303180f4172134002e00c0d1640ba081c202080e8141d00614244528013014a60120008100c0c00b00d090440104401e00d000d20420340d000c002420f0454101601c0c030100c9440342958940244012904420101903403a5036000c1c20320623401410030640c141d030324200904250400c0305c0841d454441c01d40000c5030007003403403209 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 345925809 1250 345924559 345924599
    0x9060a1a0a06030e0d1e0c0606090501170709020a0f0e0d050102120f0604020906040e1902030907080c03070f0b03070c051207050c0d050c01030902040b1e100206090d0f020c040f15 79
    0xb00c1c1c0441d81c4131b1085481103c0e8190a450054644c000440c11007485c0c85054000c04c444016408403507100c01180c0c0c00c01000b5809220598414050741c01c90580041d0080c1c1c5e04181843c0c0589000d030340c40e000030900b84004002a211303600c0840e04485d1060715640c10f0740207a40645a00310f40d6a01d500c204002c1c3d201309540c0541289041c40304100c485501055260418003080c8900d01141a0307440348012030300700b150184e440b544680340410140000740020703544400154050003540e07081c46500b180d95070780707442200e140c0c03040080043c80c65440344000300c01c01c95010303040d50540210128444001d07001001e007994a40204c0f014000c861034056203180e06680d211024107502400a00150020114020705030781160304c80702030030300c244d460342112180d40710001904c40000761140700703020008405000340c006560080050024a980000724036203010034501d4811040c3e03003440f00807402c00d2414041941c0040c00d00700c60001c20a000c1e04005034401c5c10140482d843c90b81e59100c4007440ca040201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 345927059 1250 345925809 345925847
    0x501020f161a09030f0303150a0b0304030e03030706020403030c0210210b0d15021e03070504030f110d0510110406120f02120f04120809060a1a0a06030e0d 68
    0x1044409400125054000c400d0b52641e0b062400c800007003802c0101d00c00f5603800d00d810000401a0714138190f40181110745045d2582d05180381400020340e124440a4000703400d100d5281d10340c821a95040040f6001607522010942d103403540d031314010f03103c0c0c098190103c2c8100048000300030a54400d00280003815a640901e4281c00d00b41c2400c0320062071303007010031600800c1905126011071101a14121007001e804801a601c00704c600710304000900f01032a81070b13000030400c140001d0030361100070341e41034940000d49160452035615103c03420324001056941c0100070b6115040038040302203000b26944501c2401482103000b0744601c911240b18501031400840d1201c00201d800041d142c1c04003800d44d02e1040010726103070814401081900301251a1458100c8241c100030030444e08441c3c152900c413060808510600f032105009490700401002586030980c0d41109007082c0035043c4040402c203030050710500c031030b03501d03200c00501818504114010502c50517086581083c80380d007041c0304081041c40b07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 345928309 1250 345927059 345927103
    0xc171b07060914090a09020102121201080c0109050109090c0c0b0403030207051219140408070f0306060f05060d2301060201090201030615051c0b0910030201120b360901060501020f 79
    0x501017005100f25401a411441420341c802000c04070100208440c800003103003001c3d42c1d80352501907454070100740741c524100109c02c007003005980d8000d01c290080d60000480803a801c22184030032074198941050140103020304030700f40414103030164002c0000e0741c050020750f035006803a08a00350f464400d081d540300040040751101400340d449020b0074041d2103c02207a6a10f003555414540b03141600c15003104c1300c0409206010810090b4611034200284041790300300186a10703100004002d8024403403107201311500c8600442c001803d108000d00d06070b010316141c1402d0b58403003030028000c1c4840d80c030885c0401e29046001c82c1d89181640f0149201c106980c0f030381c2c60711010386110181c0c800801500b03210551034041e00c005642d00c0e24511882004d11104880f422841e60000400b01001048180092454a0546891a00c820b000d40d40c03801781040c071148001682a4001100d483c000389101d03000c081010034000c400c001904418200c9400b40c0c03c0301c10003410582c00703a4440e400b0600e0b091801c1c402537 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 345929559 1250 345928309 345928321
    0x1020c0103050f010b1605030a111006030c0504020a020a02040e0c0112060302030a112106040c1706151302030406020c1525030b060a020d090b0702010c171b0706091409 74
    0x1030051070324009181c1012041c1c1602d90780c7d0b80c41c5400014500001c85d1080c042c4004000040000310b2441c20840018030105140d038848401c940864000d23240200d4002900d58140d60007080744000466025108000c00070380401600d0703c03155200f04490000f801c00e40c6144251641d03000d102d003900d070000c3c0601020201c81c0d40d41c0440c048542200ba80001003440c024451001141d840007c0c62417080140c031044ca445c0c0380c0088000103a401658000241c0d2442e0031000303400044581c0d1140030301c1c5143c0144001302000070861410485c50345491800002004200280ca40207054035035115411a450f0b44c0603481c00c824106412034803040c5803076600d02030504800c24140c13444004000742c04c000413104c0d44180400c0300760380650000405640702d56402c000d4142d1003100c00000b031950307244603414030708144d0000344083c030030300d10280c40032117140c131281ba10b00601c80803258540a1101000d101035180d80016031100030034482c0e02d0208421400c005801031018100e00072951000f06901185d40c3c5503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 345930809 1250 345929559 345929579
    0x50604090218061f02031e03270f07060504170703030c0605060f060708030619120305130806010303020703030206060103050f0a151503060f3512070602070201020c0103050f01 77
    0x402240d07010b01c07800c0300400b1308598844000d8140c1da96a01459844060708214007004400d549803240450041041103008c10050504a4140300700c1c1c043c000c89201c4010f415032034003060724080ca80e54010f4850000b402504070b0000e00498004400e400410340c805409561902090f00c0058042034190301c001e800100c190f401141e000000034582c03c291480c0c880461003a4001800071078a02e000001808150302e0a07008103244d0b2070f0401d4102d000704c0d003402a1030100f8100001c0084c2840001304011610500c00150b00020b07101280840d500c3d9039407424002d41d161242d200642c09070142030003090107540300c0d010ba280309895090085060f0b449000544000b004510203200140700b4400c0f0210b0510106208441c2d481680d42c4d012405500340840030208404c40d03805084261a5a100329502455001b10380c10080b20340c2d01d91041600310303404a1802e1003000319004030081d0780040e1040c10400f4644c084c10507103000784d0840307041c208040300640858a05581c1041c120240c480108104038003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 345932059 1250 345930809 345930811
    0x2109011a060d0f15140f060f07050705030111040f090204120f081c0e01060e04020306130f0c06050d1407020a0b0703060509090c01020d0f0503070828050604050604090218 75
    0x100c80c0d00051160004003a407040344e88503910500031032001441003101004076111091921000c40d200c065044440c0b0005096219848209107030b000085202d200f40300342409090000d001c00780c004d0000c8010020980500d6000b0302038070800e40010200880d00413114829141030f14a40088404581100c2d247c1d03c8c0146514501129154010048202c038041c4000740c09800d010360032000b14822a98030401d41c00d450003a00115011044201008096a070002c0c495411800d4880540c110840d9403c0050006104180c040c00840c4660307070000d00e06a01400400c61801d8016042119812805450300c0707803081a1642001603000301c40c0b02e008039200040c01c682151083c1000918a41e4820200b00c00450495101c0e2454002c85403440d1755580600c4901004200703031414480744a0700c208054920300015004078100030031500080c152180700e41008000c2d031044042c40440500b1165190040c080440b002c90103281450045840d40c00d1500031600749503801000051040701c1d1500d00c201e2628 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 345933309 1250 345932059 345932077
    0x7053a20011b1d03070513061a0d050f0402030c460902030f130c1d0402030c01050c03070b060a0f0303050d06050604030c05061605032109011a06 64
    0x404800015840002d1042c042180300b036401e001480161868050510445001c010b071094030300d0704000324640d03000b0030f0460585034110b0710710080b03000c0c0444100040c0400d03000002590070b428003d1190000c0302005c0c0180501481040c0080c2e07507a88000460303184144c6009405510200c964491460210245907103428240304500200c60300e08810701804846080c001161244040c01d04c0207c411507003400050800300b0000d43c03460400201c0e285070600c0040802211050b00d003003c004225440310010010070302a00c010041c009140300c01c02100b00148d808921a101d12107100000c0c2d4020000e807070030f20810802031410445a40c80e841c400c00703c02046c0f80c0c2d02641440d00810085a41d08415026501a80e10551180702c0c1c0d08650b41243d03041e401c2148500c00c2440200005000007200b801a600306490710394403000b03030080b0140d101824800c02002400041032504500a03080030600c1c03a40324400680c070150311000005802c80d00d20000c0401d4528001c005842c1d0750900c4001000091 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 345934559 1250 345933309 345933347
    0x1150e06070f2a0b04060c02010c1e0305180109060f0c061104081e01090807030302090402071403030603101b0806010c060f1b030c081b0f07053a 64
    0x1490780e43d407803c42094141d44114a000d0a4901d4810214811401026040f0003c040d8a000e0400364080c0001242c00d170024100039280c260907040000320514214a1011a07401c0750140200740703009007546d005036601201840a00b68290320f15849180410226812600c40450b01100e920040303a00d031820041c144c0b00b041c2c031400c00210039001d99000300010100c05010300013803224031900ea0746406504030406a00d80c144045003010414500441d01c00c1ca030300d4213005950781c04a40108010340101d00300546000d4a06500f0021242c01000035071240c0412070584008512400001c0b0448805030320b60754105044a050100d003034040d000e1503401640504100c03003204503070381d9140140d85a0001c08000a500c600724101c2c043c1c2c1607200d01207800284e0030140806d0603a40001060303a4030080081c9542070295068a1610000100f29002c551450320269680c00303a5080c103076580c050b40c0040543d0b0602c4034241c003900c502400084030010702c0020b28006110454036003200d0b1048d516149007600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 345935809 1250 345934559 345934583
    0x91516050f0307020a0e070203032a030a1a030a03320a05040f060c0b16051c090c1a0a030f020909040614010519060311040e011d01150e0607 62
    0x1240301044402129080725004554a02952040c0300c1407407420fa0040c3c0d161001002030000441d008001c1d254040d8110300760090414043c2d220241c031108515041a0004002040c0400c0050a4009000d1003003401d903065104484e0506250fa26000958082c2c00a8144204000780701454042c0b40445040f22510f444890a5600710386120b81c08101000d011600000c0c02708074150030303000303000010603050601d000c8203d11a11461118940102201c2c2140807002505001c9809501903500007004034203250468190f505400d030080c80e0701c04080d0b80d0200e950b107000600d00d040030458080c03020086441410311180c0c81d400e5014100c2c80c80d014211540a00c91404280c84481c40244298011800488c800701812240f812800b0181c01141c000c449249600d20b48000c68076949007102d80700e10b03001825a21010350700300c1500541e0010860704c02c2e01c8000003061014020f00240040381c01040b010507981c0c920345030200882400701500401c0480c0191040c0d4500b80c0c000d401454007844440c0c0031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 345937059 1250 345935809 345935813
    0x105011b050a0206031e07020a0201050f0a03060308032806081519090b0124020303180708030f09030601090606020628090602250f0b06130204060c1403091516 70
    0x4c00e8008640301c110359000f0000304068451801c0341a50800300324009014100000d4000a1040c0315242c140c0302d009400084003e0100e101c1d40c0100021a0020280d40d26030802c02d0308060144a98050b03120740d9089042c9821780c001c118407800c0b00711000d1500400740c02d0b048600c2c911034500c0052400d824070301c204840840000c005c3c007030000c20511030008500550b044c00c00007200d0410b44944090000300041c14900790b16000002c032508842c0300c0f8079041d6225480c0040d18600700031504891824080481d1400101c0440300140403160411410b5a10396a2101006008c4035014400e2034016404800880c0d4441c0c24020142c80c2202e142000c2003102407524809010341d007941401b2240c059001540090290300d031074201850000100d01c004000e001a2140d51303444800c0031025050010503008228940c1c5c03002500740c074040024605641320741d9180000b400c42030516005a542c5902041c0320a00050044111342c25010000e2440d520a000c0070741100041c3c210301e400540380c0c840101c0c8800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 345938309 1250 345937059 345937069
    0xe13080f04080120180909010e100b100503040f06020a110d090501020105180a020411070f030c0312021213060608070e01180c02030a082d070f080105011b050a02 71
    0x4090b140034000031443c0000403036038001540c2c1030b0308011800003091200780b01e500031104017143c414504403503440c5140c480340600c42c0109610450240144215940560b4940054101400300c035402c5402c41544000404180c6082c402180c0040c58403004892840015809134060084400349141101d0308290800e8054a401840c40d03401e0082602d0000c1088690790901815a2011301e80304d030199141c202d40d441581e03941c004100284210f403280b8004103c07414842c2a03d0601d50400700c042c09007811818090040c044425051f80042c0d0480074541c00d420a600840e2003000d80560a00d0340c959507082c40450b0200002821500320b40c0711000084c3c05101002441d01504200c941d00c200340d454400e580203160035903455115568181840c88180c01c1e0040184c441100c441c2c00d0000c92562030040041c8401600c0224018199044400b81d2402c18031180c201c2c0b08000d03940320a00a90009a82540ca40c8824030815000a4980485601b194501255292814828005c0310503102d60366000030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 345939559 1250 345938309 345938317
    0x120e060703050318030901090501030504060207020411040f0602013b010f020a030e010603020109150c0c0e0405060a05040b070c03090b0309010203090712020306010504020f07060501140f0108010e13080f 89
    0x141c00540c001c0180300400c0d0303803050a54480b81c08400254030380030300100060310141d010f208030b0741410ba4440014003400203c0d0101e966465005004202d540444884402aa0440d0086541c1806040e4004c6010742c0144288241300242c0b080f8518200c0d9060b258030700088080c180e070441146601d14506181009004600c40128400c030003680741c5080c204002c2c03c640c524400c0d00940d0717041010800250760082d12040031f440340c600740345855440400c419140d607014000c000301541c04030743c00042c00405580050f07010b20700c51b03030030fa4050307448075211030064410543d0b0180041c2070322004103003410301454a0140262103401c000c40035555808224043d40c00450311916141d40000401201030018410300e00503000814010b00b036412a03030082135641005000b42070080c1e0713000850800501468050364861540300791f083c0180c1d03842d900c16014810810b100d490041c0e4440c4524a0707558055880d480c143c908140b80220076548a0300b420301741490480c41070310095010408800c0d0314415034028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 345940809 1250 345939559 345939563
    0x18040b0d0b0405030d0c0806130b1f090302040537180f02011701030b0a020306120a060f060f030302060a0b0d0b01030c060915020307110f0418021e0d120e0607 70
    0x20310f464500451701581610320480a407010040b8060411010b46e82c0c051403152400414180001d26a10041c00f14141c1607001e02c003011081071f0b900013096103540c000d0940c0c045e07a2003a10140a95103426030310030401c0c225480740403050f00d0400389a2807420b41081c105248140d0f1f100004c28a03622072010760500a00d141c00c10f9903610341c040399400540d40c001e10600344414043c02140010741c590744074a0012000031f00008540c0e0b4000020418541c0c40c0c403541240d1080d40350031350b144445245070000090440c600d9680080f800c0450016605400798a50360440360503401400c00c5030340361b00c908002804000702841d400b402114200d0040740300b8040c41806188a0000c4022107802e007480034001d28642e43c04113000807003400e1004046a03010040d11240c0c0e512a034400442200d800028041d50744030070381d40d5017041c0380c540c8520622402030988104980240c0d06001035007004d504451000204080442e00724101c0400703000040c01422500315000000e141140040c40361100148a81e8888401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 345942059 1250 345940809 345940813
    0x13090603110102030309030d2c10050105150708030c0d020f0406020c060322020103060801020a0504030c0e04020109060809190b040b0a060f0612020d0c030e06010b18040b0d0b0405 79
    0x50003004005074280761580400d000850452400c0d804155036031003202d1000301c07045d0301e8040112000c000110b0308656400c880400982d0280400d82e4150f480e007042480780c103007500f0080001214200103a180311046c0030400c003207103060004d440d14900c41e8405081c030320500307104110a10300000248041d0046100c0101d0150b603552800c000203143ca000140741c1842480208240410308241200c440c8554120300e00c00380ea00038090006800524840e0b219007801d50000440c40c0000ba07010008006a03440f40c101c2c22001516a9514a0390315402c03100240420403a00d410b022460041c0c0c04940e103d032002044441c40c0c156030040c21000d41d41c5c050110b0300d144e000070900041100120089030b011424000411001c0e10300481402c5980307483c442c0c1070a10840300d0082d65880c016404a400c00494074030103000c801c000c042c00600500c401d02b006441406003030700100318406d00b02c0c00c4403007403040f110781e02d1881c400c3c9104000081c44e06e40f50b460350008242c000340c0000b9900c44034441c420380c06000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 345943309 1250 345942059 345942071
    0x10e060705160f050607120314090105091e1e0304090606120e011803030c02010f05090c1009080d120e0d2109020d060b21010204090f06030f0201141309 67
    0x202d000070b25a03801a9030300044000090207145c40b0102961245a0020744140d00c0600700c11040e030007004105600e000c183c503100304111100605422041c050104002103652a190284004201d0207940311484150307041013110304401d51415076801c0b071154a03503041d24601641d0b02c000d0000c6840c980d0088000c90040078954020180501c20542c070415188001d000c41010480310451410707221800800f81907641c111140c820b4400d6102008016141314200040d080c0580c1150340d402132110154443c250586903401c0c0a4803403c01403046400707900007030000e4407258030305403048100599495000d41c0e03191944031a1a1007000000e07828841c5440d0310a2030240380d035001aa41c3d0030840703003640003800d01c281c035130058540010708101660070900c00240c10f5800c42c00120443c0c0b510aa03c03194840400448035501410b50081c4101e881e1880c1c1000000510020001a110b4a00c805009640319034540400b40d406440d42145039245840c1040c9403035000040b1905e0444a90003001441e0303640c203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 345944559 1250 345943309 345943333
    0x30a0908060105010f0c020103050c13060507050d02010e150c270f030d0e0609030703170c0601050108011809170a020f070e01290d090b070206070e09010b09010e060705 74
    0x400a180504000c0c642503c901741c61034000f40101035440402410035aa80c000183d01c00351810617038050103e05d8050ba030340c2983ea140d0040c190b801060082e41c03075000700340751031140724014412035a1110a0102900b1120030016407205030601c010058100b003a8208240c1900c82401c035541c5586001c246a03001c141b009038000d102c0300c001c450308403a0007a0700c08503002006c00e03042041c240402108540d003643d00d0044c540400e050604a51005100148020480c1602d0b14103101030144c0301b04610440301c05d42c1e07840004660240080c8503094102402d4106e0380040080c507080000d40b94001c8103088120850214080501c0d80030155030b00060300080d0305c0d40c661210511040c3c4c000d0051010b5200075505045414a00480c00321104d000d10b020f400821040d401c3c000144d89000c06000c5041191055030304140c008241c0c03c0b074000c1c0041c080c0000042c2480d019001300044c1c12005446c21051341c0c00d0880f42002a40803c03520f60502c4801c0204280c150744440040c0307005403080000d058044410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 345945809 1250 345944559 345944563
    0x403020111190806090c0306120c0d0606240503010303080603030c060405060105040c030b15090a08030706050117011b030213170109030e10020c041e02031f05031204090b010e03030a0908 82
    0x141c26035100d402c0b01c40c28021b40c0d00e203000640c0d800030800ca45074407414103030700350562803c100e044040b604100e4602003a0180465507010f40116000a183c200d55551210048083c2650358100c40c07000c02c070144014808284100384c0154858805011240341c500d85107100f601d081c0c1c04407021500d81e8000030040c00035042902075025001c8090605011410130303007000450002d00203c0d2030b042c040700801c0720071541d644c84081c44014440c0c1c100b501d513550707158208480a04000d00a05840112180389450b5802d41445070a144107512100d50100515078803040f0040d45c072416900c240000382003c041461401d055080c00802d56200000bd0346c6045490060710590307160302142c0c846c0500d807805503903075500400c2400c0014401c4a00281004ca0640c03401d2440041b250814a40303032010041012800b8460040c5001d080e0300c1c0041d002c2e055907070003050307594203024070400d42d5203009100c10010410707150040302c00c5c40d0f014140404001030b40e40200307145801122a200002c0e81b1325004000400c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 345947059 1250 345945809 345945811
    0x506060103150503070506030604200a0318030e28090504021008010609090906020d020403050d09140d060e0f15040c05030601060801060f020109020a0b04031b081504030201111908 79
    0x140b20081ea1070310f1400000a840706407074400c40780243c40020000700d8a41e01ca91160380c03980558140d40c020503441d07548088440c0c00c0459a04003003450800384054000140540103946035055461091510b8800c06020151090a13180d400c1040b00b010341036004807018070b450019041e550000140e41c500790040001500ea1090401c0078082890018052031764015030401c107481c01d040000ca000040c0740b81000c000d200303034480c04084a201040101c100480030501050000039540c5804040b034603166001640701030b0002d4698411100c0202c9000240340750020300d00c0982c164142c1d41d440d440320503840e04000350044040c0c04544804104001c010310a003050019003002c1c0c3c0248a2981801000381c8040d0060091000340140c4c0d01a18072458800d4000e204041d40c040e0003a180315070781d5190301c003c0740c100c0e0204a40d03442100902c0c441040c00c1d034055a04540d900c0c001040304031001a00c032410490094400d8046548520707000a8a58041d0010000011203030f00c100301080107002c0c000c1c22008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 345948309 1250 345947059 345947081
    0x30120071104020711120c0301061701050708013b010306020403021203090d0b060d0c06030f0b0d0f080f220e060405040f03030b0a0317030f0c070b0712020403060203040506060103 79
    0x40306000c0200410485503100b1141002a07a000c1090088811b5181c0f4050b551151641d0640c01c1250100b058480e83c1304d03402c014101030000780455201c0280c20b4426070024013a05144201d5010403c1c0c90100c81500040740302890505060070903509025074800d40002d1304203850302500007408004500b4003030094043c40b4501e001441c00c104603100041c2d11544a903101a00d40032855000c501c41d5582c5411030180c465101c0c5e261540c55a0b60800070f00601401003d1480322440c0c045110b103582402090900746640c04803c0784920708140e9103000c00c940000b00000100c2d00d007803251030600000e01c242c0e143c41c24281d80400b84080c3c980802d03600c400300e00904840c0030b10705002c10301001820701c2844000c00d69150402007000e401000106038034092583c006048280710001120706440500029401002c581a2014140d92507038082403a5118414000300b010000100086016108014020310210f5030000545415500d1300d41c002a604251030564144c1c014605001c40d0390303010b1088504400c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 345949559 1250 345948309 345948311
    0x80717030a050427050718141323070207050f010314160e06130e0601020a052505060a030f06062307050f0a050f0d05070b01090209030120071104 64
    0x103404070006109000c0c0344562010002ca5845038601c0400d94800c150b66a07070010800c00007480d0a46000344001e944c4102c0c0742c00e100c100341d000b0502c8000824140c0940401800c18841103400301c21900041c48422101e01c0b00c500c403900038074142d041d42495140101080e5004061032810041080b0003424001c1106060528002c80c1040c035494003064a54000c0c011201d50b05a02e80303c00c415a04100800d41155005100140d01084c69020928480a881e140c041140c3c096603010300599485942d00c03000f410503400340b00d116003044124443d1070031180d840f0080b00559607686021408540001303000d040840c1d2075488a55007071819225102c02440c0c1ea10b0b00c80030f49070b80c040488809042c01c915100e080d0b5400a000d00a03c402000002d011001010445a1202290400c640c0f50848404201d20394007481032080081c0f4814820340d0450f0707130015800e1216034604040c4000075805100326a8055403a01c078000070b50740d43c0000c90925103141c24800c5545950710300e00f241215001c844013502c12 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 345950809 1250 345949559 345949567
    0x2030a08030a1a0a030206130503071d090613021e0a090f0b0109030c1505070f06060f0801050403171815090d17040609030c0803010b04180920040603060608071703 72
    0x1e1303a901c400000840b5019140e00d55201200000790181e6030458001a40612070040c0010700c1c510b003826009d09100c400500b20b845515024083c07921114191842d0100440103500d0780302525004584003d10071001c00580300604140000c600d5030704840c1c1c0035010345903450148408064a03402141d40d100803d2a102040c00d0031039680348a1401c00d03002c0e5544c0100d0700403440c0180c2e07004400316180c0d00d07042121415100c10a20b007580280c4024001c0711010400c07048001f4450505004507401507078980c0b1074424550102c5010090418000c000c0f8420a0300c100350300c041c80005012882c0d070045507451100c224607240007494a041c061740e80c1c0c0802c2240f09040002d00410500642e90080d500c07203400710711580c45003000c035032401131100d010f081441c00000000c0c0b4403e64100410458103028602002150404210422115481c0300549940101071310081150390740d000400340b0750b80013400051115201c1d11920300f214030b0303030308000d041d0380c0f0190b030a1042c0ca1225844076480c0b0740f900300462038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 345952059 1250 345950809 345950861
    0xd1406011704150e19060606030b09040b040f020609060a0e150418020903070f14040f05090c010806040f020706051b130b030c07080d020a08011a16020d02030a08030a 73
    0x145100c1e480281404d5840b0f07001c0c40d54040520200c05480038079088a40317840c882c1c0c20080003c1c2106d100308030110381740032035140b0142405140d05128a030041045207607692036854031003100e0ba12003c1240c1c8404100a80a410baa5106c06411001216500e0345403035400320050003e0038868151507004004180405c20889484078100c0288403108000541c80d4450800800d03e0554a60840c1611000404010403d01070720020300c40101c00c101d800b40304400b07290842e881210070540d400c41203900301031001e0040b9406091032a8000c5130140c400a1400c01e9040044102c0c0c200305030440743c040e21907003403002a000f1403804580041420181e280b901280e100304010104583c4590300c001c000200008401c80b8403003003550200c80d000388070751782d4071041c0c035524000950060f480c207004500800e00100d1002d000c11301e160495100d9222a42c54100c1d402c0c0d540a0b0a1603100c4101e9000a054000000507181406141c04062040c441c4507100d080021040043d0303125400980b12107100a940700003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 345953309 1250 345952059 345952073
    0x60702040b030106051809010c030504080931150b030c0a0f140a120e0706080a020706060521061302010903030806060c01050f0114030a050705060309030d1406011704 73
    0x104298100c4001a1094150002c240504001c1d800039078005030104045c0020542140a90721039a1400020072041104140580844030705441c050f140a009000e0741002d4201b010250240c0e490011030042018034070b801d80d204007243c8509035600203407207641200245000040c2078024241400da1281540b415140c0e2034824000ca08c450400c119000310200501130140718000c45208100b10240e40d180000f00f00503186281525040b00d03806d00e003040e141ca815801185d4001940c07447e03607841c3d515480b0198010040e400c071040548110366141c42c00aa150760f40c0700c900322081c2d007010f031045000c0070108615007080e10003040c618005401d000101c00503070f44140303d5015030750f143c01c2c50740031a1a8a00451828058401403c209601e86010b01c4440b0b000b42d1045412201e191910705c1508040300c1c1070586803441294001e20580c09824288540e181c05005154000c0348002240d042c0003074601c01905555403040120090001c000074010b4559100000001603032892125040c0c60800d60383c2d0903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 345954559 1250 345953309 345953317
    0x708070b0f1b100218010c030c0b060310151e0b0405061b0607030e06010503031c0203150303040b03190507021c091725061e03090c0306050f010f0506 66
    0x2000a200141c81c501c11207a8801c885074800030303001101c80c909642c1031010000d44c450300c150701700c0065480441d50158440c00d0032841196240d551070383d403c00140e5a1604014015141c03d5050060380d12a1140d03100b24443e0115100c0000384010500d494903401c0c401c50010321000454400069009200c1911604105c5040300c3d0300f55040c1c0e0340c1d11900700030310489160340384420340c82e40600000d01c842280e254103c801c040d444881540e40a07643c640401d0340e84e12504080400541c40026030302a101515406140c3c0581c04508220b10400305100180c21030f8466000700446a02c04424801004407005282c1c10340072b0701d03480801690400340c8020355580880f40c02410440860f0341780b42c14581c40342c0c9a01e0014201da814804124421450507600e41c0d4103c94008003030164502210360099501c01c0103000c0306c1e0700362103405a4512a4001c5c0c0d1910f450204c070301080c1511543c21100166090384248001d42c0141c100091905001010041c2003a042c0d10540c90021100001e0180d5640c0104036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 345955809 1250 345954559 345954577
    0x102040f03140c0a090b030c060a020a290c0c010608011802060a0306031202010b090a061401050a05041a04170703110d05070e0901090302071a03010b25050f0708070b 73
    0x840b041e00720000075146407065414980d500142e00b41300000300741540c0e0b048100840c0d412800c4c2c0e2031008264041c400140518899840181d0001030350602040b0200321024030b1401c80d14025502d0101c125a8007072240c8103503000c2c01c0710f41c0c0029a11010303640c01e2141001130007030b1600030310000000f810112844a03c20300040d105540004101e68183d00079030018009582c040a8441454002c100183c02040a01d581500600104c0c00060f664403852107480c1c00d44504080300071181980300c00455503034001d495514248501000040b4108450b04903002c0d442c5040414282e4031030428880d0000c1034540d03020084543e000002c1400040e641040d40880c54906a41c01c0c8000c0c1c00364103041d03140240ca54010101c511107103003800b80d075500c19003146203003a0182d000c50302020f0383c81d90500e00da15044003c8441c0c040081c03005010702c868201c000e004030000c10942c0b450904600c07214112162141c03a04030313415800140403201000c018006000100f03510400b800e5964079084100744d0b14460f041e44 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 345957059 1250 345955809 345955823
    0x307120f0215280f020a0e010804020d03050a200703110315010e101a0a0314010e0f0402060c0d0c060f180f0302070807030c0504051501021009110d0b01170102040f03 73
    0x5250308108100c841070042d10390043c0140310100700e02c0b024100a40c040e00c1c0310800603440300040d500a500a00c041405654060a05100011151012120f5412802e0254100880100d65079100c06120703c1107030301d0000c14000703042d2051452074a07003080055000e0302802508090309155020301507045880c11694480d0400946540d80a84181d0500b174941040c0042102d407040b28130001300401c003412440381c00e51800c002c040301c81031030300c00c160000744188460f98034584d00043c102c00b80001c543d9001440508550305195161503401e00340781090003d1000290440041e0b014070130540030b038090000b014107007045140030741c040e009034050408078007814030081083d920341010310170070625004040d01000c0e5403525449281007003514110f44074081c45030f03003007101003032400940c1440301c020001d058005000c141c5690388040054480980103554818403829001e169031960a1002c0101384515004511907041180000b46001c1403042018242c0c07051100388514600c803421142030381e0300009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 345958309 1250 345957059 345957091
    0xc01180312050c0c010c0810091103070311190806090a0b0319151d0f060f07120f02180306010e070903080304080d0f020d0c020604020a0b0a02010902030307120f0215 73
    0x1400c0021813081980b060000d40c070307018201c40400d5000520900801001030318511480c6d07610205810b56040c14030070500300b201080072400300341c0250302c03018210001c1046c090920300c0042d0f02810804000c0c00741408034032007804001c6039290034450180d100d40038000c100000d2000b07601080d43c9400d480c61300001c01c86862540d40902c2040801c45000140360351007804442c401d002c02804604008850380291300c42c100b41e0307030740007800441d0052040c180f034900248183e454220899803c20a603100c54660f56480e180d8400000c0e0900003009444140c4000704861101c100601d4038004051b0311411100d8070000900c400c2e0f0340d009039900f00301c90b08496000d4032625503007820540e500c281410030305e90f9440c00200c880c00001a4010b0071440b48003030303010005d4000165050b40c035483d048038005d50004e2001024030046a0400207008081c080e40300010384540c2d02e42c0400c2ca10382c4010000d85080780c0e08460700c0841c990041e41050b10760308070320142080000120604202c82d0010700500b1002000034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 345959559 1250 345958309 345958321
    0x8030c0c010e160501140a1b020f040c081b1801030203040201051b0604020916080a0c09081213050d030f081519061803020303040302060304260c0118031205 69
    0x5040b000360403450b402550039004024070310070101111446654045100210407401c3c0c3d03199841038850030412926903680c0e4410181c00c0c9a134240b500c2c4001c85e888041400c40d6882529035210320810048907440746001400c0c138003070003c140000b1640c10402c1d03031000c0100e480b001d4810112032075114005e00b005600c80d2210301c01603800b801844030460342040440e181c02c01d4030b07600141d01400769000f56856081612003020804ca02054941220042601103002c03440420b42136010560f02c0003246051010151201401e5051403071981084000020200340380d50341c1841905440e008210032101d546200b44e890307038040d1901c1054607020302802a441c00042c0c1c501182d00c1110000800240445003810601841c01e5a02e401406013800041000421a03801200d9035801401c0e2a0010019070030a4555800c2181660000f00115003101e81c0052031100000025070a042d1001e00b0625591a2113480071014211108240d560590030442e150620200e50030101d00c090580030759001043d03a9a4072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 345960809 1250 345959559 345959561
    0x318030e13060b1204020f18191d06100e040210030209150a0f08010501081003060f0204090903022a1806010c020618150408030f03090a1a04051908030c0c01 69
    0xb941c40800400f9000440d00d071002c2000130118810707031080f80c0c1c40003852000414010300c162507031030300c003510481c0f00d011680c0905407003001e00d85c0e04110700d8042a405c1400a0300b5188a44203001c00c2580d0740070342d041c41201d46400704800701030010f4001900c1145080c1e0002611001001c11000c03d01d54001a84215038a45041100d210b81c1c20016095440e18056030090038445110f084400085075140042095841410164051100d40050382c401c14119228040102075503402260038036420080090071002034000d10080501a402500710540750790140d8a4000042c64540d950402000384c505459039201c0428074000410b0740003940940c0c1d4040140d8050b00e0b22040651f0101000c80d00d42810070303400b920560002c4042e01c3c400d08440078450300b10344a00490048001c10b800c1844006a00c4800c0f00c042c5030303c954010700312001c18645458400040440c091a403d60300b98050802040c043b00b04034a4080081c102d228401d0006030380c0319203046001c054030120480030300141182c0d0072182 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 345962059 1250 345960809 345960821
    0x2d0215030405060f0a061238010603020c0102120c04061101050f071202090904080c070504090f020d02150a120606050a09051002070308040e0603060601020303250c060c0f0318030e13 80
    0x25400c101c0d0040403810400400c24a99002c512840c8d04004203840c4180501d05112003d808c40c5490b881c581d00340441500650441d50180740380c1d41d400c2c808140d40b0100c2c001d0300c40c0604c141d1119145c2c2d540c00c1c080010440205001826040d0b0704040034012001404800d0550104244c80d0040548880c030074880064800c8020b041d80c401c007070109110030b100c49480104924042202100c55490f66841400300303580c0c1006015104082d0b18019001500703190350a080310510044c2107200c440e80c0e0030700b01516600181e01046c0000c0317015646070904000c0788203460241400f070070114104405240010011061409036500401c220313070800316150b0003040600d014550203585107407602d480e10302504011404503100ea100f48120004501310f0750020007164000c7c0141c44103c035241c0d032100e04181907007a4001d08602004184007032000450001d124042724040982d036054420048c040008050b1500319603045012030004a8207000243c0202c074103e4840010349a8001460707901c2401c40c0140f02c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 345963309 1250 345962059 345962069
    0x7180e060a08100c260109150e04060c0906090503030a0c03030f0903030e0c0108011212050f0d0c090e06210a24060906030f030c2d0215030405060f0a06 67
    0x442d203408480e81c030405410022201c2241c4c0c1d03400c00c000c01003415209008031883ca8040d00501743d80d005100559098000d082007680d0018801d96071a614148981030120868080c2d5049645000326181d081d40712120b88000d00c4540361000d59241024006900d030301c140700980e41030140307a1a804003054041e400c070240d000207000b000c125024403030501402801140c00144da860240c801ca1440301d600581c001c1b41a5841e6000d518642c11460359600c3c03908803001e201030b080c0031041c4460030740f203920500106201c1142010106001d030b2061344c00f5200c000140c0180c94628014410018180c5810050340c0402041107080e583d5549c00008503824071840d40c0003c0c18017860450707024006600610020500390300300404100465444450104a90305404000c0041148402d03420109200d01141010180a85000040420300c00d03940c0070071112402c1d2180101e4404a6800c3c198a40200001d0394030090555a074514601540d540b5200c03500100b12100400528020a026800302d501801c00341c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 345964559 1250 345963309 345963313
    0xa111201140a080607020a03020709020307020c011209052a090903271347060d0518071a0706180b27010b0a03030f0e03100605040507180e060a08 64
    0x1051005c0000e4640b400b421040c0c02511640d0f60000d80d4090600c01c0f684902400d6000d4a4140d403c80c1c01194904000d54189000300e4550022030b012440520002100030403040e800d4004654080a041603210f4404d0064860b0502000b00b0900e848044100d40a440021450a80100c00800701450044a11180f2038101014021441213400180d2142181e0301208060704070407104003484006150481903140f140b40d2040e102c030243e40c0b03a590218a50044020000382c00d10113401041c03002c6443c2203420303040d43c848925540004550030302c500405480003c8140126054020760b290a902c80c4010041c0300c07075580c011000180514103a900c00f456800500700301981400c404800c8411410302c3e00c59400d415000c02042c42240c1403040c4030003001d001d084d00da00c0500d962019644100c003080044240314660301c1040b010b54042c01507040800e003082d00021424180310a001c21035030004c000c81c00380031216200360401d81d04403c0ca007049448050003a0510768405c00456404003090323000581d14 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 345965809 1250 345964559 345964561
    0xa0305100504060e1f110f070317060105120c030901020c0a03050405100903030f0815040f060e0601030b0303030a09080714011b180e0402030a02060406080a111201140a0806 76
    0x10034490304a140070714000c11081c05a1071001e1643d036100e102c0000301d041d826185503043e8024420a0b0481800402d481d00c03140d00b800078100c0841059441480300303d00142c0c0c212803160a6084a5880c2a0001d0082ca80301c0d0070300741110020445001c01826503050341001100082c0402c3c001d4046820050410b001c1d02d41c00b503c01d10340076040d9086401502e110790440100e54083c13a01c03e410603400c0366015030318004400e0a0400540340400d002e4031126120030484607070801902c0d00d0040800341040ca0b08000b40403843c003402e030b16002d03038080d003007070f0415040c082c20000d41da0b00002900c2d003010082100041030b040764030b0540c20741c1c814000d004112412a02001e4504081035010358400c46400107072543e0894803d00848880c00b002901105895001c10244000b03403030504c1c4603900500c041c2c1180e80d0b0b2a81c1c1e07000103116420071342c04100010002c004010b02e50520340101c90015034045041428600f10821000300e01a05000d1042800780d140c4240710b0642d1a20701d01001040f01c0000d03504070b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 345967059 1250 345965809 345965833
    0x10b0f190323010c02030a1e0e1017010506070309030b0703060e0421080702030d0902120709020405120c180c1b01050a0e070e011703041505030411041b05090a0305 72
    0x1071403400360400e001c0e0f5482c0a07a01c480c281d00201c00c84030002515603030303214491040400c88100c00c0c0c854100c01c00b0420b031414009129111941c02d1100840540c42e503148900403004002801b9805820050150100703002d5400042c1c3c110300b005003036036403100c0742201540d282c0104500415141d808008613010450a01081c004540740e42d842e100d0245200614200100c0c00594080d01c050b80d42500580c000c005100300115507501a190552008001c0317002d0603844aa12861702c2c98a4120745206640002c040055180240001070300d0300c0780d50702914002d40c503080000d0030b0b4441c4070b441454001c144000121031000c060f0444030f000702d2181d0003041c65040950744034000c00085400740206440e00501c0c41c009200002c0201c21602005020101daa007400c042020940303d901440d00349200a00001c01c03040c11006052040300090f9840c691245071600744552410385031000c140c0160b1510402c5c41514912034007845420340076042c403540ea1603110012030444e0015510141060003480e0541134 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 345968309 1250 345967059 345967103
    0x6090302151c09030f081f0308090a081006050a050d0b0703110706091103060601031413020d0b0406091505010305061506040504020c1605100206130f0605040b1008010b0f1903 77
    0x11204074260303101200c590751100001c00200d21210308002c003411412080000504041c0100ac0414000e80300601096582880c249042a046010b9105e075450714000e105500b003541d00c94000300740440e1a087e0301e00305502c41e28042c41e0040c1400c0101511085118030164408007101c070410b41c8004104501c00307031170a004441050300d280080c40b9001d600040f0f9407170f620038003890354580503c0c00c8084541c1c60f583c0110f9480b2402d103000301e800089682e941c0020401c80f5a41510480c0038000218180406140c51b8203521103000c0e817403110510745001400820000202d859002d40c0d895140311003007010000148450040390f00c110343c03080c000034001d200080c001c9404004c040d00c0811881c0c41a4031202007140098465802d40700581c003060004403180d40034814002c5450145841d04000641611450284ca40444081e1001100c15045c8901c1c4500d20147c04000c082000c0204541000d40f400242c20405913100c8520071240c804000c0070103003036007240c50021644210b014004041c502c446070303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 345969559 1250 345968309 345968327
    0x303020604061401080706051c060f180c0c0201210501080f0105060307050303030c0a09030f3818031207181a09060d0e1b0a06090302151c0903 63
    0x440302c908004468150a07403683d8458160b03401e52001e05402400d1001c111101d03042801d582013018810504048040c20a2007204041d201620f00c03000c40078140b04c1620540c0501c00101140c2c10320b891800c020341984000c0214005509107008a19540c040966001003902c60400400e003602d000000148118005100e0310300911250003880a6a104002c05449180701d02c2419059001000020038040f01000200b10840d1642410f410098590b12041c50301084084100e55a01610524084c0d90010ba0010b400415809954140014130380142c2c030300009000d480302681c0321a0103480107440100b8015205c0c1000070901e901c0c00c034a00408020590f00c6149405280182600d5010400d61900581e0a54152281d10342ea884d181d02c0000b407207903d42c485525003c0f80c50b940d106541d0750010034083d07100c0242581c0e0002d4200d1000604002c19400315600034800c1c825081c1c820001a01d5031250000c003007085080e1320362224850528190002c860402000d50245040100001c240d0001224 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 345970809 1250 345969559 345969563
    0x20901050d03112a090f0a18060c2309030a110d05060a060614070b0714091e0103051005010215101721091e03010b130509010e0109030507060917040303020604 70
    0x444d40d240207a005014080101390343c050b1810040c3d0300002e404103a01d402c0341d0501c410710259400d1080180e100e04080341c00c0d41d88038800098060045003514840a0301054038451015140c40c50050300742c00083c2d40c1c17031a88000418980b42800314640a0741d50030008032030786400c41e0590300740c0e160001001c0700801aa000303440100c0c04d06c6910410091001068842140d4003c450360950b403215002510851510b06101c1c020300d9040114a00b0b507155a00e041d0b0100031604c91005d01031620b4030002d01661001480546200131350b60080181e80c2e4002a59000c20107408000c81c0940c44802703109410031a01e811441d12041c21064604803c80000741c10507000c4031805151141e00d000d51000305c0b031440703031000d0b09502500c1135500390215540384a420240c3c840040002910303184030004240c00c0b0741001640c14010b6034410821902540078080c020540030004001c012120080c0da01400b64010080050050742c0e81c2d00f00d502c100604150100d81104466114035280c982da8500299556411201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 345972059 1250 345970809 345970873
    0x60203060306090102030603071e03060606051c0e2808121b04050a17070e130204060503060601020d200106090b01230913150b0c0613020901050d0311 66
    0x201864410f2007076074000e010040262401600c0d011054102030076440c00c0c801e2b1a001310f17400000040d024803440300240810b4a5030358480ca0203507005968140c40d019004545402c2100c60a0001d00102d102d69401c0009120000102007007480c0b031045a014460007400b07440300140c0c08a00f500e13101c10301403013803507800140640d440c0c48010904040c0101c2c8103554108400010034054862056941103203900d0903011507501903642e4800611405090314480f04021080c80038901398100750181d800a064107034020256420300c040006e5645004259000070041104141d4014252a03842c0d6940081014028403440e82c441c4140d0004001c01251140460303510320281800c0070b000303134080c400f442c058083c0500b401c5e600c0b0140028541182644c0c55236666920300100d0000071709100c60701804009490540712126400300e01d2828401400c4403900c0c0b88800a007600680d540c1150a05582c00ae44042c03011a985140680300c4d58503913103540c1c000740109408482c0c440c01c1041082003580750341c61 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 345973309 1250 345972059 345972061
    0x6071e1407030809060c07020604030210020f16290409020306120601030303020307030b0d02030615061b03031006020f1c090b160c09090305071e050a1a0606180409060605060403060203060306 84
    0xb80c502c6c41c03449103250003904100305000800140c07900716054403500c503030b80c0103071340e002d400b02d00720507041241c1107105890720f80d80c0316020b0114014003046218402c50142580c00e0b46001001d55001c0b5005500c51280640e40000c002803041d200c04031002e007040d240d102141c146584a25005d00079400465450000900d0140c3c0418103280c9038850086207038000d0003900c2580c030390103000c030040510000d12540043c4100801041d81050700352000170304000d04040d584170b040607100004c82091907130040c1c0455200c0313524500d142c3c0010810019049a0161600c40501c0d5180b003500e4900d4960710481e1084c02c0070414000c1c4201c02460300110f988665401c030662034840c18850111000e9401c0580011410710a440018030060403030408200f10f25905207600c181d44d40c0b02413400184682c100c401c1c2c5110001d42070f07184910b6402940060f0102c5486043c4a9841d2005103460600c50b0413504c41e03a10b90390600c0900c0441e60103a40501005010207554070b4480c20000c019500c207507040c900030701c1010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 345974559 1250 345973309 345973321
    0xe15100602060c1c05040602092e0504050306151807030b01090b16080d0b0303211b03060d030e03010c090302011106010b070227040f060e06071e140703080906 70
    0xd01241c0c00c00841604d00e42d1000d0f20001c12500410000344211350641d42041050a15944c005013035075050005550000c030708002107004041134490340d807104180141448203000c15500450304603880b00c0b00d004001c56583d034410001b01030b940d503901d032207a20500000c02c3c03255242d4075411000c420f1f1400c0e01c8010910f5550111080c01d03101c0e00c1c010308400d2621480580005800710010a02c00c94a40b6021030b419403080006400c60744401100700311f031030803041c4604500b20f040740c209900004002406071f060002c16640d807814800140514482e003202104201018018040350300d81c0c600c060002c220300040344402525514203400280e000ca2a6850500c0110700000340150603603049610850a005490703003840a1008200c50204000a0a21041c200c4d1000048014071481c01390650440c201d4040c01c000c011198104a481303140d400203002c00c981d45402001c0c01001008801501c0c03c03c5843c2242214040500303c06030700b504a0001d003078001d160703101d949140100308440c250341540c3c40e05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 345975809 1250 345974559 345974581
    0x3010e011e06020d030207052a0909070803040303120f061401120506030337080105152803060b04030c030c080d020d0e01050702181005060a120e1510060206 69
    0x10710034100168040103421102c05d00c250090042244200125064000d81a04480d40084003e025030001ca483e5072260700a4546000184d40286410307000c0c000300c0c0e04001c101d544038403c1e4040903003070203407400c0790400036001c0e94483c0c1810f1940e4103040014030340f01c03c504504031201d070000600050014407103070465001c0d441200c3c01800010011807070805903124821540c00a8004480c1d480c5a4050090016142e45031800d030303c41c190b0f41c51181d0783d8100410411020030a402001c60b2400c1071012030030000d0000d1850011401241d0980010011880100e01034070041d00030080860010800008002c084041d607015248240b00e6143d0498448580d070faa1620701000701e40044e4010070158090a019000441c03c103041031401a1030182c0036001715600d485c8840c2c0307107520000702c4020000098546c2541102920045496900d044a5081d004224040450f0841c844a551ba041c11082c4102000115111780340340340107008524010440d99070750041c91194001601514000070410891 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 345977059 1250 345975809 345975869
    0x2030f040b0c090a0302120f120301031a0c0a0804050304051003020705071a03070503070905100c03030b0a05010507081317060103060c210507020f030f090a0909020901170a0803010e01 81
    0xf0152400c4062031554007045120310340350010000394000c40071070b0810300d8410f201d9840c03441c031014680303983c9524500e07210780184012810070340b03485842c170140004884048204e60f10052a880c10304425185c1e03040041c298400c950042e548200d01c04240b0801c141c040d005880c00c42c0c0038000f41c46e016991000c0005002c90f02d00d00080303402c1400c00c00110303c103004601640d081242440c004105075280c801060518003500110404034410307001d103101b055814000c0001d164001c1e00d80000c01031500002909602032041c0007410001c0216158103c00382a6521500501c52021030841c5e1141c04460b00d17885001c01e00050794403a080c05e13100c1000300c1c007858401840c14007000490044441c5010000c1c02024084c10803c21401600310700b08001e54100007810403410501c203003da85840140801040b050b0702d40c050603105003460840009613072030000c2c0c02d045502c0d01c00310321192841d5802c4181840c031317854070040445001000100300d04c07240100360750503960360710070f171041a124801c0d8607046050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 345978309 1250 345977059 345977077
    0x50105031615050909100915060203160f080318150402100c03030b101e0e130908040e0109060501030b040207050706200618011d030d1a030102030f040b0c 68
    0x808a200700301580c0c0707507098444100c1881c60070f00e00f4654001300080305400f050322083d0812074459024000c1801c103100301e034001030b041040b1503035403480e001d000307500e038054410544074100c5100d007480e05209000c00310000e120340c03081055584c0e07d841e005100107c0008140401d03a403007000c41c0c144501003a904014001c035001421240403000f0404201e4581044480031010151100c084c00050340341d003482040d51403020344641184404020b02c6401c4e00500d13190000401c80301c00b100160640304c1e44111500c0503102e090101e10380020f820160310a05c0b49030320855906407030348000150303400154001801d50b00266004c0c414041520b0802c0140c1c00f40e520081c0c160b0f04098400c00500f4010243d41060072520030108400e5800440d8640c2010000c881e0400005880801ca0102d40f00c00e12407030002c405e510458080369500c460489540b40100d000398600642c0d00c0d1480c2e08401140c0c55160440100207000759900e01d032100f03c021951409850031901c001b0301c0004101a42d903001e0648803105 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 345979559 1250 345978309 345978343
    0x90509160308160618030c050d0314010312030e0609010e07060305011d0702010f02270105040b0414040f06060e0f0f0f15070c060c03020d050f09040209120f1005010503 74
    0x5012221a0043d001c400b0b0071100310342c1e9050682c1100c2042d03003003c440e0900a44454500a8442c00d146042514036400f1004040c501410300c0150f10441045c1419640c0004049060711484d24060b001030105c0c3d11401c18612800b010803942300c7c0150410390a0074849010b855200d55545016000e450003030040001c0902c0718200e0703040036200b804829a010400e0b10000c14080e0340d0610030000c903480210440d10303054000b01221000300c1c403134520103021007080c80c02c03a141c2403412045c0341241c0121702070031442c500140c001c40d8941c0c2d6140c005200340c8010320710420041e80d41e010b001d088a03100c1340d0000d0180320010201074003860301200b041c160080240864405030141000c0000701c613007604040e14004006c2c0314020100702201d10003400f4180c20340750740e0700000b05800c010b403130240806084400c203c0b003080300b4542174000c2d500b6104d91910030f80380540c6882034040080c01d40403074940740300790510400322455440380d40020944440ca1401d0380400040c1d0701c80c0b040c1a00d800768404010f46803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 345980809 1250 345979559 345979567
    0x5030c04030f0312050c040807150f0804032109151a010c0f0602041d0f090307320c1c0b0c0f070611180409050714030a0c090509160308 60
    0xc909040314854041d4840d1134964108012801c446045400650b000c0e004000045414001d0764020130244016205030ba5030b4000111070102c0c010400340b0208200c000300820640801c0c2003501945180d48116450b0380e807054100d03400d4000340028130b203540d401c1d1000e10064050b51400945ca03c5001c2c1241c201c0559001c0c02ea039a0300041d101e1010b40d00080310b80c01c081d14424004030b25944003034000f4040d00482c0b131800700c2c2540d001e0301a80c0380140c400e6a01803d40340030f02010076400812124180d511000d8410501c17404204044d1262134503001d07141e035800300307181e00c0c50a03000810b440c415501c04440308022100600341030320724480010700c010002142100410342e0040d22201900e2282c5071000080d02d0300c9400c0e6140d4040d640c04a1030b01c41034410120343e8144050903043c461301c0c2c04400b56010840b914554172015a5900d6510621002404101c040c1c0417a4400707115042000790801e40180c0314580ea4480140200b83c104d0741d10900d4010110141314080900c00100e04994128003840d040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 345982059 1250 345980809 345980813
    0x2162315090904050d031118040b060904020c060709060c0206070b1312050301030b18030306010f0e030a03021e0303011a09060421020f0301050c070809030a3005030c0403 75
    0x11150340d034400440401402580400d684114000e44500d2041016080d64140018043d042d100c000300600c0b14038500340100f41c01c111380300c0089208001d0440d07010604091910105496106401860760003d0000490280c8030b100045e81074000c8a166407a069425aa008111240400c069000394021410030081000c500f001044581142044442e00c0300c1d1070441d90744840c8003000c0a00c0d5004140c0110040007031064205525030300810707400188080051079003815071281310090449040c0002c04141b014000d1148811180c100406411a085c4402d1414065030760040708a000c29500c503001c00c0c00180440c08410307203040f10702003082c14800c1c00a9001d9001c194201104840c4c02c41028080054001c08074040d00c51013110b03071030400036881807900600241400c08060a07000c0da0400b02440007140e00d000440d081da64001840e1500d5050310000241007004000700586030000305054207281072000b00d054440d044000300c500e02d08600350402a540c6000449410751130300c9040c003003040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 345983309 1250 345982059 345982069
    0x30b0d020f0414091f05010311040f2d051617070e10031b020c011d0a0e040b0601080f091f0f05010801020a09060e0303030a0e030d02030403021623 65
    0x425003000400c08200d91060103d43c0d50751507412156811341d0790020003070042c940304508040c075900c40789031018410740d81583c0b035002c4107042c10070415001d16501d50706541941c03615446002d16400080340e50001c415100018504120009541508180381402140b00306076480742d444088031240d211007a40c80d0f2041d101c6000c2d41c200800c010188000f4200108032a40d8208001511110035240040c0103400c400c0c0401c02d842c0001802420f5600250101d4520b82e041140d003655400145905d07000d00a8150225031158859400700d20401581070522041140c140c1c0c04500c980d5003030340c500d005559001d0703026030500e2040d180520143c0003901035540314419420050140300340c0c850003003480c00d140d014001c1211000d80c0051060307540410040c58042d4044002001012645080d00c04e09031b000000986038030014010180080e5541804490080c0070702c151031803544030074003c54903458a0308000e5212541100e07100010801c0704000300b8025241030981c41000c9506800c1c11081d1114000c0c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 345984559 1250 345983309 345983329
    0x4060608240a03050a0b0a11090d12140c0601051009180b010c050f0c0306060a210f0c0603020406080109091a090705030706050c01110408030d020d0f090602120601030b0d02 76
    0x182c01100c00340000c80420000c02000103d01d2041d02c800351346184c103d00507402c88203440d140c40050642007011240580d03c1e50300b07030341c45650459000503a0505441c801d4582d49203407c0c00400c22003000c10003801d464004902da80c12076606480d0f4103070700303220704a085034031140900030308a00c40d1203100000d010b002594401c1ca20403406040500140d40e44e6144c20f8500041c90807008401e0303010b00c00300d40260800340201900503c0903100c1010030b41c1040181910205845040701c40c810700c0001345000d126002c05a03560494200240154142d21854003c0c0654040e00070000441c8001d400025510141c0c801c10b1803054000c82c814102c505040011041a0809481101c25101d8500c0208066405001075001440b46d901d8440e50740103440c0300c0d1030a494400b801c3d1700084a0a001c100036103a1f01000316030004508400c0140e9400b141c0c2c0744000200990007440024a107403140302410003269600030940d40c119101010910fa460100460540c4c0203c058140c1203098440544018103050041c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 345985809 1250 345984559 345984631
    0x20a090c0512160207080c011709030f0301030515061503040f0303110c0a050f01182301020d0b030c04061a0c01020c0f15090705010206010329041104060608 69
    0x14509401200d00300c00b0301d9801e0f580b400625400c11a80328103140c04001c00c0c80101540d9015015507640c0d14006081c104c0854203000700d083c0c00038000389003030000b031044031102203460f07180c1600da58580c101a0b03650002043c0e01d803d03001e5070402084084c40c1540b230b1595204000074070189590750301d640c3c0803844040240e00720140b503200c9500b440040c060070050041d140c507410041c5182c2040303040c160714055850303071081d82903498258000e44c0c960340c03070b901f64070f5071500409412601c030300400381300b4468403084000404651010860861642c0c80d50024800c011341181156220003c4800300f100315007030f0b03100f0f60503c40c1402c1700c07183d8040d00d001d02400304010144001420710b4232182c0d0690401c2030b180d40407200b540000448041c04400001025000108000103000c404e082c500042d607a41c1040c00050712010345074445d150720854122143d1001003111142980a0400d45400b81d201502d0340041c920031800c00b480851803a104810440c441c292150032120340d00000003e1039000c074503065403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 345987059 1250 345985809 345985817
    0xd05070521071401020c010b01030207051011070b0403020a211709010e061e0c0c0712060b0d0c050102010501080111030420061215041107151b02071809020a090c 71
    0xa210003141e01d120b8010b54442100001680c0c4102400401f0b00319800000703414181071040c010080898400180015002940d0100040b0301225480166070783c09840c1c1c00500e04202c10080108050340801e5480e9000c0c4190224604000b00001c084480c41c24070444000145400e0909010204803403d804d4224600c2000004d0745200655982d04058088985280c12441850200c216051008405501040c015a4581014821a074a41d1a181c0c070b0320460380e500c42c60b10340b6507060002960005080580007021030003904254507110300607600c203200b801e025520b00b0300009275904060080c0c080400302d002c200352442d961595000c80d41114107500700c90059801c42241c032030b500c0b00700040131146008101c145041c60100004e0240020440f00103008904055000c041541c004040d01d20a40e1700180045940b03800c02c0303990000b01814081081401010702d1402034050b008110f0300140d400350034040400704042142d61003030360391005c4000d4000a001004004450030f543c000740d085102894 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 345988309 1250 345987059 345987067
    0x5070308040c170f060105150d0b0411190f020102090307051324080d05070210031a0301020a030b010201050f04030e130e1f050601080709120201120c030605030d05070521 75
    0x44044401e040c2240550b07440d501c9032640d9008084100201e40c010441148c0207144035010030000001c60140e100d808214a450f04007000b10340c1d82e550418100d01c400c0940d41e41d01c90300a8200100c98411a20480c00031a40b050304042c205841030003140c50009e000b500402d0b01d40c0c0380800348528954400d0701e19107025518170303185088a4641141c40700170146101444401400c1240050401000841100910100304008401a120140751443d00720b21801c0c00280c0e40900c0c481020b12042ca05900d075415480004c401c00590f13010350110a04950a0307008110540c0c034402100d0030b0440686018010803030800510700c441c941045010b208045c0300c0404103212190b2440240b40190021400e000c003059178034423414810341c0d84111380d4000781c01d280003500d030304080002800c40d040d580142c21884c40d01d140c8200941e4016401145103841125040115402c80380c030007401030080d801458881c2c042c00b05110011842807041d625480c2d00704000c1e00d60101c041440900441c01c5408640041c030081c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 345989559 1250 345988309 345988319
    0x3040201030b041125020603010905070207060507050d11010f060803032202150c0a050a0507030b070f0c03030b01050f1210150f081302030a030909150b0711040b12010f050c030705070308040c 84
    0x71008c1d5008042c6408e002c1101c1c14011001f03810700f102c035001442004401c0c40240d0100b44002204001d1010718103040e00e5000c40d00c0701d0036024000742a044030845d820030344000380e54100080154402c902c281c0c04003065810880d0516154400c40c940658828502d0b000020410201001445400c00010031980081c107180d0341c06040500c10041900d164000035820014050f1074801c02d03a00c41030300c1c544042c1d9802c48402c090180c07a64094090300b00340d0f81c0c039101074003039000d1411202c1000c81001e50541b0385000c00800009a80c08458001101c1c070040c80001c0d24810109c4d4420a000042c1c64012528202800484031002c2c024209014012010300030740250300d0074000c281d05980a40e8400c00c02c41c2c14800070105840c4034901c40d100341c0034105000c2002c2c0c0d848600351603c0b294411040040c0c401903800040203450300c0c2e01039a81c00814407c04a40f503a80540c4280456401e404045c0101e0751400c140301018082128070b800072a10411a000009104617041a4024410314400108030b4441c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 345990809 1250 345989559 345989569
    0x408060609102102030118030c0f050327030c060a0503280504050114060108090304121506061205071b060c02211308060108120c070b0f03040201030b04112502 70
    0x41c0407043c185045103491010b50030f0038003690b2a100d0b41c0300c00003a011902503800401c040c804034030181501c0c0d002c1503003d04119081c4229041c030010600c4c5503106d0100601c610380200d8410000511a11441c0c40040a40c1000c6056901031041c944400d800c5640e40f0f0303502080761803c00c44408000c9022605803150440a05c5264002e40c02030000140e040e041c0340000507102d0003e07044ca41031011031f108100254100200716425a07081003040b405465452030409a41c0080003100b061507420702070701042955100034151001858200144a0343d12071810a54030000040c04941c06180841c3d62200800c011f0f80040c040e036410303071040703408000c01c0c0031841248010300718480165020014140200f0300142c111072018100c0e8902412080d40f5103e1001d40d547e0603554800c1d11000003003202c40c0e1842050105030005e00b496020f60b940d0b981034405074101d0741e1046074101e01103481d010030a10942420300c201d100020820b03040a20b00500c0808150030001000080c0300202505914000140c0360 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 345992059 1250 345990809 345990839
    0x90501020712030b0405010e01060302070524040c09020f0a1b170405043b070e0109150e13023001090203120a0906030c051b0f0d05040806060910 64
    0x2455001c281070003402e8001c00340c940e0755100900c51400e010051155801c0015000e0454070f15050041c1d50b1160707454640d0401c0c405d0b0003d90348103180701c010400c2100b02e80c29010b1042c1d100394101031480c1c4d01d8510f482c080b4050348981e4042e1080c01e000c9010140d004424040c21140f48602801810116039118860b011500c0c1c002262108042010041313400e1900424480201000d000580800a001020584540748052045400071403807402e1800506004034030142501d100c448085686840c018001742404030000c28450441c10750010310f404041e0921401500e0b01c83c404012424250200b00c10703200c8420030070f100300d22034440380b9800500009a600a0214040c004603414141d0f004141c20070b601c100640000c0c100400100a80c59880f54003501035a102e410300080f1001c0c40c2c4d904880d103008080118500b0310f4280c402c04500100082c0202e24080c101c01140c0300080600801c45a0380900c0c8110f10b9254400004a200c600e0710000b00351b40401400d04601000c2c3e510000c103081492 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 345993309 1250 345992059 345992063
    0x5060106210f0e0d0302070f0605130507081c09030203060703051f0810140103030503040b0703020409111801050405030d050d0b060a050a0806061201031112030c1e010509120a030905010207 83
    0x243e96007035000000c0701402160f920000c1ca040840c00c2032420744800381d84040186004207002e03503d10001e0614200801b001d181150440201c0d1000c1e0b4480003c03954540f1824075148170074030840035240da0544900d0203402503980c0035000d00041d0f1900302041d806000060111205400c400060f000c8000c4d001881c04020030703584c002004000e20320045481110030811301800743c250010014004240c0100c1100d401c0b507404100070550703a480000c1280240190780140300101d0500f035030140d4050400000e414071203220107035654418800700040d0340030703c95442000d07015007018042711101c0740500040d00080d1111180401e0488021002807880c1d400f01003980003241011a030241011b0b40711214940c070200503500b00d40b5101c160b0f10040f041203014480141032203103201014846481e04800c40e143c1020b507a08a9458106d21070391241c5600456100500a001c0c50200d0071b02c0c5841400342501450b0404003801d500c035008600a40c1a13480f40b00c4000515490f00070710700024800b4401800b0044c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 345994559 1250 345993309 345993311
    0xd02090a091a0a080d1b080403050a08070551010f030c09060b3a0c020c090f0103030f110d0306050906010c0b0604020a2705010201140405060106210f 66
    0x40090410424404141d130449071081d0702800302c402d030329600b1201656403088a90155500020b140c40e10880d03038411a00300030201d025500013042040b40c2c0c00090b05100b44a01d00f070320000c2580d1160186460001c00d841d200c42e1100203050022140050141028000114100b1111084511803102c103140282d0004204190030340040050007101203801c405011000c80501249260511607035142c000c0e041c1803030241c0901e9082c0402141110034018100007105069030b02403448480ea400200000103109003d40030700d18004400c3e1820b6005c162240309580c4000300c181e42561001c56411524005060034401c46886880d00c84408000a00001805590200d00a41408148464000b000d41041c0c10705c400322000c540060b1049184c15440141907400580715100d90350210364440b180c3c1203100074403080400e980c4910700240082d0065520a800902a214001a41c0e1b241c03102c040728040e0650f0013090040c400c1c940701d00c440391440184841a07040c0300748a902039804451a04491004a03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 345995809 1250 345994559 345994601
    0x209041a010e22050c0c060709080c03010c051c180f020a0b0c0607030c09050a0605030105090106090503100f15090c0207080f1506130504030804030905030c060d02090a09 75
    0x50341e48000740e000c0800043c0c990001460341080080e00d1040c0c280340504030241c580c00040d850300f02203420b40e0f07031031240b04088881505251401900e0071410340942c01041c00b13520078200280c181401400752040455880e18980000c01100384410030000c8581f50016403100100910074005104182a0340d002d002010f00480d0340c0c1c8108a09040150f00240800000307205d010301c03c54011a5241d8001020b08012900c0482c06104586120040d0840c0744c1c003494014003c104c407940100514141d55050b04c4000e0b9998036800180e40420361441240e030305900040030031006441c0394200301100c00c680c1c00d0200380041d10368241c0040f04040c0d00211400743e039a000100f00942d040021100406d000400303070541054401440391266950300039000c82c1105000824490740f02d0900004074804070003020046800c1501c0c00800c0c4100564090300022010080800e4618000c03c03840382d01c00c0010729951400ca461140003020350443c403030440c2d114040c1c40d000146c0310303002d00401107503140b554203580322 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 345997059 1250 345995809 345995861
    0x90a0e01030c0e15010e01050903120409090605010b070519031206122001050405040c0c14030301082b0f0c0b0408190305040b01120215040602031c02070201020604060b04020904 78
    0x214074010031141c940000340302132070001d0340c00c5000408070007000e182c06a50340300c050f00403a140c469011403800e00c08100040020300d4000d01d500c5a05014030800c81808542d92f14001f0440f5809103010141503034000c1000303a040040402403c0c4401780c82030a00280300c0030191481e500b2900154002c12041092280c3c040401941340c4241c4ca81540009080c2c8404501a000a02c28015409035600842c0d4540340f8855407030003030214a4256500c41032205d0b09600c580290307600c2c0e030420300c02c0200a100d05a40c08424405900400b6541d014910320b80b40c80b4504644120b8a0104100780c240520040c031850b4400b240c07000c0310301c81c8143d0185915a17034034a411402d01c0043c00184d03002c58201407034203090000240182c41011b0444a01585100c40030f0740b54000074032400c0141000d552038020001e80001c132503401001070080d08a044500f40441506030a9200a0b48607421009006070005000140020840c0d8000114644090300050619031860301040444180110302c0c8030045000464504c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 345998309 1250 345997059 345997079
    0x6031401080307111309020d05010605040c02031e0a0918050718030b060d050c1201060f06110d0f140706060302130c1e030b21061005030c0105090a0e01030c 69
    0x8010109800150f1801c8032580b01d0b180f900c000c02d41d0041c46001400b064907201c00721500b06200f41500101440340e441445c0c81d08a000349514401c1074069070901d030030003060743d00100584c0d0740c084c0c12000d540d291460001c01a0309980c0114112000c0c010782d403a02080c038054404002061380207030a40010303541008040986a20003100c400d2242d0220b03010203200003a00d01090b10b0300008150740c00c0c168500985009410992046810364200d03048072000188030b0f00541003042251109800b104400c3d448000449568005d420034a41580c00f1004c182c3c4014072550584c682c11032189000f2a1002c1883c0b007610250384861000d5036005e44410082c800d600c0c0c1090b10080010340c1d054108190f030180180500314a900b4840014600c0040c1100303a041406908042e0300d00c1402400d1166600541e800003c0c0806c240003184040e1081c8000901e6098080d85528195040200140011f070344a9004540f0740e481200500d42041218000041503038407204100d010b580715001c0e4008a50820324065 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 345999559 1250 345998309 345998311
    0xc030310170c040f060509040503040f0e0f041209090e0106050405010807080703080703050909040f03110d0e10050d0c050a02120a05070818030706020c0f030601031a041704060314 79
    0x3080003054007101e0a015000240036440040292070120300b5050300901c1000603c0d140d4460b942101310103082000300705000c0000c0043da144114144000b60301d0702103d04038904c0807075030b4042142e030310004213010840703003500e10042d00d81619104180b00e458440c0340f002e413041d150350340030f80b0f0707440b040309001d1803416020f085d025000140c001c05145103050031a642d01c1050380300103840a60002404814148200301b02e82c50444007400d034084500b014030300b00d007003c282c56030140c0008170001c0d503254030400085011082460f05544018060040108004009032403510030014418204500c2c900b404080c045d860700c10b503560b150503403540110203003e404d2614581c211300a07014100002916150002c003030306c8040e0342140006896010350050709400162503100580d05101d5500c00103084c5500150341d800300070b82900c0600380054100d00b4595034140a0100406c41501c01065001103805411501da01c18004c0480c40752803030744d4880201c41a48180c00400000c0e0f1119080803c40442100107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 346000809 1250 345999559 345999569
    0x93c090c050c2e02070b070311030f07081306051501080606040f15050f0c0c120106030201080115020309100f09060518040b130f09110603010303020a0f0302120c030310 74
    0x156182c4411456000e4036440302d45010141c064545a101042220390f40c802007040300300c804119951106801c06d4003d0f001d04a8210b8002400d11010700b10f4001c881007900c2c010300c41c21643c01c2c2907403150035080c0d401000043c100402010041e00410205501d40206030007210042000120700340c1c071074001080020000d203882e0003203000b04010002000c00010100442d00042c00a040810609208442510605820078081c69001c941c0340e99074040491041045082200d1007026030900d040c409090b5003803488003a01141805c0010081488003283e0b40030140020306c152071038900e0640015a4020104d00100c000914200041d522660003000300030250009042150608803400c00c4c0d02e684002c03030721059010f59180c0350f000c03501da1108401d20401c00c4072a6401c1c0202d40054100c1c4005100c1d400094440d5138030f1094a00041c00e04c02d088038181da402d035002c0e050500b80c039180c48441001c0450100c0440c4100d400000400859a01800a00000c3d00280d079603820142441c00032400c0503080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 346002059 1250 346000809 346000817
    0x312080405060f1506180406081c1d0604060203210f04030c020a151d090403140304260304230705121f0c1e093c090c 52
    0x148400301d800007a0941e4071032000c0070380706019603455035080c00502c840540c054001c5800714a203000501c44400201c140034044c2c80030001c884e0b51b858400e5840102030300000075092400401c020403441040008180c00100304d450394540c1c1880c02081d600d40c02580403c0042e080400c0403024011190b0144003030964032000c0c0011420f0038900000c40c424081c00080602000848100440d03c2e807140340802000d07901c0210f0b84188038007601a0000e000e00c51020081d9109502d800064a0003000c45806950942d880314510340c6560751100241d1320140040e59941c0d0515000c00d4840c522201071540c078144110003a448e802d291030500504941d00300010707123402720280310007980500040c078642115070464400c68969055444141004c1c03862494101c0c0c4020050a546030701c04940003880707130001950760000d5103084500140c0c0c200303c02c40c03404030008201440c03c110174451480708480310b50703050760392080c00c0300d04400c400c8410000514140c2140f40080307080080d1740702803041103030800c85410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 346003309 1250 346002059 346002061
    0x1303050604031b080901030c1101051807060c0c06081824090a0218070512010b070b0c130b091f0c050f0a0f081e0403080705061b07060b010e0d0804031208 68
    0x1350318131312800b910240d24105a500d54404030b089100d0003424030341e55041002000302d410004038a5180349144a072030fa0440c0f166100c0003500750301c40c0c10070342134a54004260064803410414210303601c03030020b80f04200346500c0350b09039440344505001c0d0001840c1c6008003e01e080500040a25802a00034840d00303907078002610480148e159900300c4a0a03200ba454880076540d102c000035201c41c0140c0d0320300c11005032008004200500500300a00e82203008012140403a514001c0d08800d501c1031100880b01b83c030b03400c042007010100d4400948040c600c020183d400c0840d059820159020481c04140009030101045900303000080c44902c0800d134a50300500600c40e203e44411000181c00700004040450015044000744800d0400340c4c1003441030800a65110703641e041554441e008180151041d008603408182d0950380640c6080c3c54002e06c2c01440d04000700341d214507000380f202d5110700741031051000c1076503120341da07071120607007400e00c201081500c2c0d500f1418001010140d40c0100020301240c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 346004559 1250 346003309 346003313
    0xe1c0503040b100801020a0305010905060402041208031b22091104030206180604081014070c08130b040609090b0f0603011e030210080a0b03060c0a141303050604031b 73
    0x28048039070164015149180d00d441c0e860440120a40940c0118642e51020842d030040c5581138000c0d60403924102c03410320540d01e4640801040348200d20580310031440c14801d040000c0c0110000c0c40d880500c0c2d925011400c3e400741450403555100500c44d1456040c00540c0e0300b000d1a50090315400f1305110101004803071004060103000340b05500001c0c2c81228042034140101c070f05010682c2002c10040c1c4a192166a80c07e00c8c00d5559019800c20b010280c103007021b092184600006091007282d083da504080c9000d580c5440c4815444000a2144a075086501050500790340c00200000c0403290303115181a8900704003002160b502200c03040c425401c9051032402503541800b86ea0540d1040c210000c6620120b0b5032a0b550703013420740e000941103484124030710031840e08030202034407a41001c0d80500c4000b82d10030030940c45507002c0fa8a80c82c88601400580c0940d446a9282c03000d13040103010072450302c80051121940450300341d00486091f03010604000405a100e080042595000c40c1880c20701160780e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 346005809 1250 346004559 346004567
    0xf15062802061012020f0301021201050a082b0e0405151518010f02100c0306030611070314160b0907170304060c0206181309050106051816210e1c 64
    0x512444d856202e05500366011766460a40303003078103200010000c550b01c3d509035914160a503024803607980300301c0644800240b956008500c200800d00d040624403070700342c03506a0130402215850b2004080281c049040c00a40d01c45204e6540210241850812a0740d021810040010032013428039202510500c120303580d80d4004d2819a065801c2403c1200b8000c4c0d808030124074103880108400401c50800c041c003106540c041c0c1c884010b0307a0250505005007448400c1412261045040040000300c8903544a103202101d040942010460b114504000d0b5840d038460100c04041510344045d50341040e04c04110703c09425804120700710903200614240b0749031010150860200c1e08010b40652400038202410b0000e1441c1da6000e03110003003c43c00b256103952070b894024500024226180c1d8070300744c404136031481c060900140c50703103003100d0740c80311680d0b0440042d0381c6a0555810f1800c1c407100c0900c034440a840303108681c60720030711070600007404032440aa8600c4d24040c0d0a1001d5054440348440e0401940 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 346007059 1250 346005809 346005841
    0x30210050c0c0c0f12150a0605010309030815190914060a05091602010204090e0f0c04200c01020403080f0a0306140105120603120406020106050f15030f1506280206 72
    0x4103c2d4500b10000c1008042000c040456100c80358a000d102c40ca801c0400207107146c2c60207011010000c220702c80e00c9000640460f402110702402003804003002583c41d20a144e441c241043c00070344244608984a1450351910445800c4124900c0d12411b2030b50a01a50ec1040359100008a40c0301400398a4000400c240143c05010790703024000c200010701284e4000d404490050a2280d0108004090307100219203031746900040c602c40c2e006d0510741040d14641405102a40381c040c03981d8000301201c1c0706800c0c030303541d021060340b0806540a000020100301c07124007800114100f20328441c1d45140c441c0006080725143c0d0418900d00c4d0000300c07a01c0150368000143da4a00d107250924401135100d00000916200c600034441000faa80060041601c6038190040011140180d50b1159804c50a904106144803580400c9201c6c05082c00001c10385031003d0645034001c400c0c01e00341105411600041141d50b8401040070710003109824018440c800341e1f101d0700442c1501880604820304014401d61082c0c80703 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 346008309 1250 346007059 346007083
    0x306140a14011101090f0305120a0c0207140f13060513061a0702040b0a030309080f0a120e01120e0307030809030703020703110a05030303041203110a0212030c04080109030210050c0c 80
    0x5008900d80304503e095003e24031098104e032080e00310b040d4600d40201164000900b000c0c800403103d001c40c1403429540541000b582082d005003070b100c1d09004450f0020000304020303c1e40702098012806590b00c2d00e04021040da010340c03c022940c5400c5c03070284501d4a810030440782c081032903e04200700c6805200c094a040d02459003007a0b64850040c00020007030150106101d9201000c00360000806401c00306640c2241c803110143e0342034280320b803a000c0e00c4205100c80901002c0042c0e09000c1090301c41c2002401704001410084400c4d200941c220045036484410f41e80c00e81d1000500c0c1c0d05154100314282da02038003000081d40380c21100d0b03030300a4503510039101c01000980b1034004000030755a4040306401520010b81103d40700d04e81820640a542604481c00c00800d2400a0480d84801d9030720855042c504c032034005184507071302c0032040541940f0003003071424451021312021806400a005803001c150007075008100055014400d60105c500142940c194a001082554030b8442d01044581802c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 346009559 1250 346008309 346008317
    0xf03090609131b0e03071d04030306080a060b0414243c060906071103070f0801050a05010b040f06030207140105100303020d030c050d0203040f0b070306140a1401 71
    0x10781c00e80105044a109514601c1e00c181040d1504102d40c3c24410406008102591085108025001490b860300000d000e00d120015103200310461411040341c01035040303031003842c0014048e0340c1d0341402401c05d0035042d000c03119a922516115402e15240c010740d82c400c031312002a81190b050110700c83d845040980d0951460100613404004240c0d1046c1580c907980d0051208401c9400f8500c0c41002d02070312100c10642004402e0000e40c219041c45410703900d8550004e00514941610303234680b015404e1241841c036a151140f40f5004c139000b860542408020702003507001045904003a142d4034141c3d20160440304a8a509120070032241030a403030040100e036070600340180d44110508100e90480401c1d0803400b155800d00040c4080d0103a4820701d04120781c000e5080d00c0c020201e61b00101e09465000c83d4030400100f05000ca03622040b82980103640062058003a06035941450b0390311050030404841800109943d10410000c44218500070040e0340030869400d101603045c0403a0601c03c42c0d0102d1514104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 346010809 1250 346009559 346009567
    0x5030a0b19110d09060e0123010b0a050f1b101e05041101030902031e0d0f02030a050304140a0605040506071103070b132a0306140f0103031b20030705030f030906 71
    0x4405d142e40900d250840003402448400003912003121410407012504600701c442c4000011074030640c00503211040c0007540c802e440c0c0b0740d5200e04255107804c03500600701200e82422180c58201020401070b8108220080040750308580f03020070710074002c04000e14281560504041200084d208400c9005c03041c001d0800040e23407042030000c00c1c5411003040d0685420340074014079850680c000240070000c0e9400b40d840c00d0440d8034030402281c4034010394003410040b40d0700b07102060000f10b100300c452542104000455504a0040d00c510061310700945042c0d80b207800c210203000e619a8001c407030302d070460903510045141100a03074903076800920044c10080750840c2c8004c00c8007089604200c00540800803004003140c4600d00c024000154031602c0f040b41c0c004e03e0500c0d030120312118a00051f00c100d40c03050240021341e1035130304c0942d8406000c42d00c20715404078034480800041c0c0300c609044440301c002c0381c0959186040740c09041c545041600414800d62001c550503840490001c00c40c1c005080681e541a11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 346012059 1250 346010809 346010813
    0x15130b060d0201170a3305030a20270105100e09010b0903070b180a0504050903030612030c100509060c030405030a0507020f040e0c090a02040518040c05030a0b19110d09 74
    0x42c20850001e0202e404a40c0c0d00300070b50450485200c041424900e104421650380d1000c241d52000582c0c801805110420034510300c00c501cad552800c045940181c080b40c011603524200b14413031307541c001c40c071200360500c0700051049041c640b90743d81d840b6180c0d0801d03006110060f400a20000da0500c141404c450001a84203000c0c1c8041c4104801000b61503d81501c40e13506401072180500e01200190284d031060400103001d2030a4010f0a000e183c86101440c40c3d03841e01c5050021100c61501034800910081005010f030303143c20404070724814038594002465042c0348002c60b040020207001c0c8182c1c02c100740280000304401008036140d091250410655840c000d2020600001e40c890320141d220b4909a4a1030a075440410a08c03c403007421181c148131541e54a0b550002ca00403406841d8100e0380384000840720a0f0300d402c51a400c18059810301d21020b0b5a24000b80c600903404d28200e407400100e074140704800c0c2c100d103624600d07210a014240620200c281401919000301c2e00103c2d000740d1a0105d0301c007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 346013309 1250 346012059 346012061
    0xc070b04051501030c210201140c0a1b0503120c03090909070e01030b220c060c031101020408010b0316060e092a04080d03050103080a080915130b060d0201170a 70
    0x20740402c0c125031030901c42d0303074905184c145000e240c4112000e42c4002e1102d60001000308042d200840c1d4140c542148182c2101020042c40d044205940d403248a003a00c01c03408945200c0210000e04407100d507040705036048c04245420326000d00c1140d5402d0701c00f031181050b1050003000792018200c041d9a09082075940c0054280360100a234426070481e581c0310004004e10460800192189409030290002560080480c400020003800f0150150403021418442c00d03210744c62000e5102d000745049107a0540c0f0744000b508a9001e0b510189540c0e5650760402490b080a1107040000319030090a41007280c60940083c1503081b801200b24030a005d8007001402216416110791115820202c0448154402401c034080c0d503482405207016030721070f40c00100c485c14801c0c02824140d03603200d4010f9040c00200c0000340e8081c24007424001c4240030b801409045445e600d0030451251018118400c3d0303410380344c1010081918098503c0f80a00c00716000b400c0544d82250009589607403024a4824680d5800b01c508 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 346014559 1250 346013309 346013323
    0x5090c070602070f031106060102120c01020f0c031801050309150a0f0f0501050f04020a050412031e0504090f05130f0303020421061d0a08070204060302040507050d05010501080c070b0405 82
    0x204020302c0031440c0c40500c080c0145a100c9180f09845000c2d0304c0340d10403090744c0d6603141103d840d40144d1190320011800c1d001000a85900c01c004800903040c240d122860744040d0300411074032402039001107040ca141e80307145110700025610a0800310718504024004035155401c811508d80e00c030b078007407001c0f03070082920358442550782d001510204201d030700300d41040e4007910b400c0c45894400c4086c4607102c9036500c0e09100f11100ca0107030792115440c0c05c2c03a0101c0d286041004070030030303028040c0031406d00850704541400d00081c0211030381c50035505e900304452902250a200740f8126001d06c1e0a0810101409001d0032094064000c6040880706a032403070124060306c100d400c005c001c68080c4211311220403407054a06c410301c3c420201406500b008600c480d021658510080b0b0865204008032030110712035500619016002030004a04a5101d8001c2030030344006a0b001000940300080060020f5050300c0b41c80e0140000b4030b4090002d040c18142c0034014010b00102810680d01140490100f000405c44c02c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 346015809 1250 346014559 346014563
    0x727020a051611010807020c0a030b0903090907020312010801060605043c030302060a0b0d020607080f0310050310060303050421051b01020f07061e180311100503010f05090c07 77
    0x19581841c8038030f420544a035920800d98049a032072030202c0d00c01400811031429425010b494501742c2855a128010a64000703000f021040c0400c2208800c01c0e1a80100300344035030700d542c00860380d440445001c0768580740c05a1184860341d01d841c40030f1290340d61003400c0341c04484e00518040703503020074891034031640c209000c030306c0175000b100c14017011f0410074030320640702100d000381c00b0351b0004c0d43d98110b220b058076440149107900103400f002040051400201500e1114010b941007030524401001c410720540c81501d403075802c0d22459100300700b14a02004050458144034030300b0301c45d987c91590050f2550107240542000c0c26500180308000110081d5110a81034110f0100e58044109020307841880c0300904101e03005010b070480c51064020300281000841c0c0e116075902490035941c805d0850a02c84ca041c044040000060140e82901904500c00000e1801030703240300e98010f1044104a50707060712442c0d4605000301800104134240007406401c1c00c441c0305440340798042d0b88203001c400c643c0c8031782600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 346017059 1250 346015809 346015837
    0x1a0112121e031b0801240c080301091533030207020a0306050601170106090902071a1f140a09090812010e010e01051516021c0803090727020a05 63
    0x15038052582d02d03403c0150b0400d0070b1081400542e1840404413141e480074012840c0b4504948440000300e98134414400e0901800d02d4283c080b840c1503038851010358420f03803050040300d498a029109100107264118024a810a05c290354020340c2d00f40003079200c1c1500095500741c454001c101d180c1500a804803080c0b903900515600c07400fa00e0307107007100041c041038601500041d412a841c45e00100d1805415060f9009519110074092a200c1114060b6100c4101103495421405403000303841e10035096140602c03120052603048000c01540c3c00c104940d141d01074500d44080021040311916100038400554a0044000c540400345061a681c14407504d90b81084101e0003200010380c0041032241035050360860022454a42d99440c1005850000c9504004420b48200014000c41595006110800748040c0907401040c049101c3d40e8400f600168003500c1c088000800c1100700c03d81408140040d21101c0707500d030b02442031000c03503052041e11095900c0d80345074002910744c184ea004005550316020b40d209 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 346018309 1250 346017059 346017107
    0x140708010c1e050903030d09020d02120a0210090f05060d0e031902011406150304020301111c05090f06191b0908060a05010b03190e0303040503071a011212 68
    0x1000801500d00020442c0985031103014814496124004484144000600460401940c101040c00a1403100c5041b40e004500300c101c03800686503218144001064103001e040380c00c0d0580107009030205d01020083c2004803e02062044020303a40791b04058940540e00e1548074200341107064000c18080300c0701140da100c041000103200c20360310045001e50155500904c1404c62203030160039102d500f51015544030140c0e000c003150032107000700555171040c00100086441c64426605694542c490690b0503100d1109160495840c2160b005850708140000700034091b140d0700451807034482e0301c040c11001d2050460000203103801015080400b500e00c0d0117240461144002d41e0103803c0034480d11812480740105000164004890300c01c00f4100c48110f0f00d11480c5540c3c0d600360030310800f02f82c41042190f0b544c1e000701043c0300f14100090340c400d034420700055036210402e08001406941c008044081c8000c00360044c041406680710400340d0560101614a1032407400314255941049422000700e50481c0f01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 346019559 1250 346018309 346018331
    0xa0e040612290a020a02150702030d1d06040219030b010b1306030b030d050d0e010203041406130809010807031b081f1d06060f030426030403080414070801 68
    0x1c01810841c0c0d00c82c0e40700320082c0b0696a2240e500310425801400310604032400100b10350307843c0d0014040440d591041c2c1c1c0c044611a41c1015070300e8410707640c080040e032010403c524811081e1051891403094001c0d540346650106080503928440104000d0041307909544e04500024840002e00145910403900c2941d50b0b117030780000d1020f811121600740300c6160075600160f214002d110341e42e5445009000b500b8004003500040d50b0b10b5102c40000e40304c1c640e031450b201c14071001c03c0c40558080d52080504a1074049008403d900c2c0582c05480341c000010980a0400011452012243d0f6418207080c121800d0341c0b00b103815402030250600300311240c1c2d1a56500041581c1c03081a0500c55002c844075102415030549150750a10f015020301d81a01646031524034150303901805013330340118000c24962410701c99014280700d036001610b044a072034407001d000341421074804104550039404401c940e0700b0361405890041080743e01600140c40b491001061704003000c4144041d00103000103900034049200c9403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 346020809 1250 346019559 346019579
    0x209090d0e010c051e10020a0c02040f050105030712051c18060809070303140c0102040308180d0c090e0705150c070509040c17100c0302030109050f010312050a0e0406 73
    0x115100c10001190035440e0841c030340c010f01e0710301c81c0d40e0f820a005100050703500c0d42da40030000d02c0c0f800c1c80080b0701c641c0309000c56490307a42c002820362030b0841c0d40e88a00c0070058414442520460140c0510071400c01005001035100010820100e42d0781030041180b25180b418820304200c6610003280f0445085900350f241c46402071500100b158202e070008011666480c800c450340c44090782c08900f144c01942d420000b091080e040d00d1500c100503c10300c0d16201500380d402c1d007242d0040c0c3c4110780302100030503d0603007002c5000101c954940142d40744c510300ca071039542d5154408000d003d025105560341145440074041000300c00094a000745c41d22000c0b20300100000e142e600704014592180c03040130f002103842e0401c0904180916840180728a1031401d05460008007045083d0649a0740706244d18800688000e000d501244c4100381ca00581e0382d410a40b40d141901d40080c8a01c1404001800400c001a01030001407800d10080c50f1030707030b1104642801110403a00e007401555020341000300c0131800c1854 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 346022059 1250 346020809 346020823
    0x20d140706060b0921120d0b0d0f03080f100504020f0c010515030f0703020906090429190515010e0102070902030c040f0510050717040b19110106080307021c020909 72
    0x101c4041503905d03100310305100b04d0a40309403102c480e43c00948001003480410710142203562034504000c14418460004621f007103003e4207007580e40c40641c2e280c8c2020705400001090f04426080361440552614840018190142c0e2003800d0103554000340e0f400381440543c0a86940e1054980203001c80c2c00c01c3c0c4000303000e42c0090a0b40b148240110708207a498a00c0c0040c0d00805c403036002c1c0140c1031540c2c414007080344a03c0b0003007054030f07080c003003440300e58001c203002d110b20402824140c070f11195030411b205511010a0602e40700c0240340e207041300340101041e00c048240c040742c100f440d2003110002d000c00100e007054680d52060003002d00201c02c0c44500310105015000351040004101d1085503541c0402100480e803118000100744200b040c00b020500c0010039410030002c4080c0f540c94280e9400342400c13998000000c40322440b0040c1800c00d50144d1200c0c2800340c00c08100c0c0203000752030401003643d80313034030454000a1040c03805107684d4429400c808040c1d80141d400614403045482d02000441e12040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 346023309 1250 346022059 346022077
    0xb21090d090902071707020402070203100525081611013602130504110904080a110d050a1b1a31030309021207080a11060406020d140706060b 62
    0x401e400003241d01c01c031030701c260b0300b0381d50300560075814444c00c000949146601c0018140d80050b0200403100c0036850800403005041c1c0e11510014407444c003040c00d50010408044450144088500301e03010f65940b043c4101d40080e21403c000000c0e0100c12410307130303105000c0e0440481d0340d400d00c0c07090341d0301e00c4010714140c50f24548a40c1500208005003c404031641000c00000c4d441040d4850304a42c0d074042c3e6011070b510a10071003130400708204040009035076030703003ca03001c507036030b5400149c406030690340044503440f10350984006200e890310b812009069400303051400410041154180300001000220120038690082c6a000b2501400d5584003000c2a08980c3c1a0b041030560420400302d056000c2c1500c1e104070101e004501c19251503400300d0180c0801c110980e0b00413103031500c40c08451001d12041c002006c07608005c0c0094000ea1500c41e8606800100e10740c410f2105020410119801240c690040c104da868840e25031800114548000d000d2040702424007864104042101c60385c00000b082484 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 346024559 1250 346023309 346023317
    0x4051e04062904060c12030e0a1104150311040b0d080c030406020d11030f0702031623030a122a080405330a170a020901180305070b21090d 61
    0x24402d0584440382c0d1040740300d1a800103240203036100110b49441c1040c04400018540070500d20700310340e922454041c0b012000d0341c040b5401403800025140c1445050300c49055030451038603a5266885d0414011303240d11b002e9008948036040244507548849043d40c03e42c0e802600d407078032910191041c540d660490300403140544140c050302d1143c03d005032070451a08424400442c078190101d1541581500001d000b20b07014800c6851044a9040c2150303a1000760120410f00c0940407241c003c407594001004e4500c40c043d401584002011407003c07403c400e40301d107281c2069504141d0107843c0d090440031418165611035181c41400d0204003d810040c030440e102216a0406044105c103107074821003104050990441004058811540b4100701800c60180c413030914210a106000180304802da044501c0c5100950005814242d5a00201000d411803041140e030354909045030741d61035071021300380101034030164080713a110840d0800c41c200c0c00030f40345241540c0700c541c10200603003a0340c0c103080c2920380082 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 346025809 1250 346024559 346024619
    0x120c0c080f130b0d050609010e0610110d020c1903030c020906150a11011b1d010306120303020706140103240b060c0604030f0f2a0506040503120903090604051e0406 72
    0x50b1910287d0b860603114000040324480d140c0c0d00800403440003440d0a5001d004070b01942960024090102245000e0150060140f0054a404000b103c01d501024189041140c440c1031011075400050162004d81c1a43d00c118552503c000203113281070050b211a40c0c09000041c0112042c0e40308101e00f4080b11a80c3c02480305034401900204500b00c10041000051100c3c04030751401e084080c598050b411040c140020b041d511800d00c01c410608030030040d00400c1d000951700081140c28415101408200740401005506541d200741c03489803e154074039201030454180d01c0364100980c0c040d8405800c010720496854207050102a1500c000f16002c0c1d011130103980e81c8402590149211141e0744a00b9910701b060300c032007880c00308000300510b181e0030b40314280c1c145d680c1d0005000300101800303940a040216180c1c1c10444c2c0c01030890400500a000c9a0030034402071885403598420b90703060720b4040354051800b00304584c4030548604004211540181030120000f20440e12440b4510844030750070220b400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 346027059 1250 346025809 346025821
    0x10308071b05010f3006060206130c0b07151b02150f061c020d0b16030b030304050607020f040501030c051518010f110d02030a120c0c080f130b0d05 65
    0x5161860b11500b0f000c15100741d60040722500c5800003007100c108440e50541840031311900703040400305805400d602565245428094141c042040f1b0340d00c0926082800050001d80c0d403030320408103642c4501c0150310000b203104010450a5081e0012400c02d04c0010015000c015440c43c1c444185826580054000e60200261100100210340c1c032070380c40000354140b1070712420140200035100407540401c070040c0381c4200c80180d40784404020102e00640d00041107003840740c00700001440190011062520301403440360b5948000c010788040f20307402c40d516520b44440f0300101324540d0b0340208280d0b000b880d190000c82003041640e01e84090715030075918a04030241c15100c181e000e1098109402d03000c1846164403680e98490b41ca01c000300d41243c940201d80650142195107421000e901c4200560804203003d02880c1e482010500940c414413400e00c0080c0030600c1c0a020032600900c043c08900001400d00105040d00c01100d4680a1645c95100d00569605901d40d01d60405244032648a0405003c640 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 346028309 1250 346027059 346027103
    0xf0f010902011e09030206131a071208010332010c0801080c040b1e0f060403030c0210090b03070e031e100501080606010207060c0203100518060108030c030418060e01030807 76
    0x481e04015204e1545180c2180c08009858001c1076034a5000f075400c0700041140206440305070074108a54401e03541f075085901d001007031004a05041010044e04c0c100400100d002c0300450941001d50043c0100c131800c85150007042e501030007404184642c01c01c43c8010381c6070380c0201c1d404d048441450585503030028840805c02611403e03c105070740034602e42ca1002c90b2090a01807481e40304002061100d64118000218583da0410751042c1c0106460004c003d09606228140c2c0c12444001d00e0b09030050b600341082d04a4a000180104003002000340b5510b80a803010408040041500e9100f90044a1000c01e07195840a9501e50311100360b0500c400002d0354000090080d00464058000d040d440b41005401c0fa0b641c8143d04041e079040c4188030701140b50b0480c0b84a002e01076103080c6002c42118114038402490007006030300c1811b40d076108001048402001009880548500180094815040482c0b0340c0180c085034000031640d07140d9100000070071654100505220b0b114903505804100c68140c0700f4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 346029559 1250 346028309 346028357
    0xc03151d060a14040f0f060321140a0f090302041a120d0c02060307170103060507030b091b1c020409020307090b0a12050c07051510171c020f0f01090201 67
    0x103d510200305209400c0ca0183c00903c0094106107000400300e600300080c0713040d20304d198401c1d81c0d817490081c0c000100340c0b180325202580c4040340c03c01e0054481222114000ca100301140c8500300001466001c143c18800c1d40325030015034008009015079191407590151000c09800b0f060b110f0782c628502402c4202c408240300a45651030344942401e19065020f05c902c95000034501c80030018850100c80e80740310360428441c084c600a0704002010300d0f00709009011104043c14540c4500c0ca0881040000110f81e0104336501035900006e0b51211945541002000c5144007844100c90000c10007098042d0180c0c00746125031850780c0e4240d03000707549010300f80091083c3c61000000038640c00290070341c120140c01154101c0e00c0c2d035108030305d0203000340c540c14213000d01070140c0c0789600e00c0c4c2e00912500990795015503020344440516881101c004040060b40d4015018019a0115005c5170b4190141c3c000e00030030340200041030640d054012402900e60003081d6800089000c20f002521882108070034074100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 346030809 1250 346029559 346029569
    0x405040f2301140f10030c11120304032a02060a050d0911030c15121009020c16050301020c19210806090f0601020c040905011104060804020306060d0f060c03151d060a 73
    0x1036a0007100205c044002e050021240000c0c811040ca40c0c0d0383d24401000f1a0034410440720240d41c03a400e141c03030300030310010b05040d1040b400010544071560703a1880c10403080c449c6034100c40069486075942425a454004c1480c07400c03149107003000c40c0d010300c400101d44140603a070403829a20082918410401c840c002da16071410919800e005114049034166a0540c1000c15000350410013a92a18080103980c40303456203039143d42010311201041404404030102800c03089009500f03185507129041d41d42d202007000500d641442c120050184900b1002261a140959240b03c1d007181c000d0001070a00348007580c00c00c4c0228401000a40c0c00c0c0001040c003406140164058203e807203d410800000c0d2183c0c2c04240c0341075590352903082e08460020028002460140c03035500241c5014010581070030300c000d100901a079191a022000900c0b41c152100304190700c0f600008400c803481c40304400a00b91446c050700c041304400004102400144a00103000301103070340591040e510b0000b4844107030340174414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 346032059 1250 346030809 346030819
    0x200304020a0605030919080d020403051006080309010e01030b060705061008060a0603030903030c02030f010203071101060504060f030201050d0b06040308091311030a09110d060b011b0201050405040f2301140f 91
    0x1507410580080c81107000150147c0b61031070504c07000354000e001300e0b841030344101c41ea07a01a00200140300c0d145d00a40380284920701c0954180b000c16800a030051034548a840d0405569a440e80142d40d030705000d031462160440e04448032880c01d01d120303203003a8225001e82c40c214803c440020b05075440381d01036482a60b80c1507640b000c202d4619a0305403100d40340c8480480c2c2c9801420203440c03910201340701541c8140d045955240340c03400b070300c0e0300342e8211126900120300403400c1410078060319600d4400302088036428038016580c0c0b03404508507801001c48140d40c65110800290000a008020b0302030b1a402c0300440303e559461880d04105c0c0b00300e800c0c292440c01d8400b0140005000592a680602c1106000c0c40200740e400e05e00d8000255240501002180c41c242e07901030010841d680204541c0f00611213106d010301c001181e40001c1d00754040c0b031150610a40d110342d20b03120070008507004010030146401900c1040c000308000702a08000900030021088089000302d1300e90b05d0080da90a0100c10b018107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 346033309 1250 346032059 346032073
    0xa08010b0c070e070201020c060a05011409090c060c0304090501082113060813140304080609060906060f01141602040b1e04050a0b1f02010c0804081606200304020a06050309 76
    0x101c40081e03c0c4002d0006065541c00e1004c42c1840c83e0a00c4941d03c074005140c00000c0c85c0d070605a0f0301c0b9180c0c0745006018010004c0008002e040b000000701141298401c035006c0303031541c0d104805d2505d5407007150001042242050000036401c080098003080300003590ba019000c00825244204c090f0003144a4079200d070300d014104004003401110415003000010b080140301c8022511540340b02030815924028640c000242088500c4042c0091504014a0b034040d101d58180069400e688000180601e4071660120301200d18580c040d0512183d0f6505108101da02e4011036001e000b5829160f51080c2d0042d400c003603a544440c5031090456070b00e12a541c12007812032450b0801c0c40010f0a0040440011139501c4400b4600395031640d02043c4204105c8940c43c2004d40c8520f802400c2d140000c09000c10301040c0300a110011b019841501c0d000b4010b00118a815400d50800002038404040040040c0c1165251044071445c100300841c4500e0090710402d401d9030f9201021905417008988203c09504100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 346034559 1250 346033309 346033319
    0xd0309030c020910090204030f02030c01021c0806040212070f0f02031603080c12091614060406080405011506050a020c0a0f03020603071e090501030510080d030b030a15020a08010b0c07 81
    0x1542c02500a605503507804d6895459902210407039029402c1580c5107200c40d44d0500c1140fa040120f040403500a2000d03250031520303240012000802c01134034030b0621904100080e40ca4545a0640341e03889a040003200d51030078420409856001d0b0302080800140d41d60000c0410b6a000200b114200107500301b80d185c01600c552800c035a2068054840e840c400020041c10030b441d1483c030412401403004c0c002500181d10521355a03511488564405441c1e051003506240003a5520710070745041f81c0c070505200c4c02d10303a55407810f5401803030303206201c006481c00c210010510726401030161540002c0c079000c42d9104074590f82002040c3c0c125106160002e06a0041400113041210145030082142e00b047c043c611441d05204407a4041c00c0c28140001f41d031503204006035a4180140c980282d07845003402403203414000051307160307221846410f062685824135001292000c00618100d19080190381920041c4a200b0340e019510409103100080d09100010032010002000c807513070550f82100030400c0921300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 346035809 1250 346034559 346034569
    0x3061005120102070b1f0806040f0f02011b1127010b1b0d080a0614030c0f010c0512220b12040804120507060201231302120d030506030d0309030c02 65
    0x10001e15840d55000c0c44003200062581144600900d04003807a01900c040813a100251280240d00a400706c0c0c4c030800a200c04100d403407000825860704108890001c0d001ca00040ea000319152106244401000c0101c0003403281031018481400011500b4a0745c03031902c50342104500300c51450b14500850140c4c0104011141140188485808842081d100c5400b00300b2080c14003403c6a84100420b01d02c0c010405403080c80d10910002c1c00c4980701d0026041e0700040030139501c002c1401c2681c0240443d4044c580c142c0e00602e860064a940a0100c071382c40074203801c0141d15038001c0d040349080354000a0091104500d00c3e2503203000d0351140f02040341041e000000304086910003800c20f03248008201300c045412900d0340c0320402c4160060004102181ca004002404c550004000d00001c500e50400e00c7c8000b4403069009070031411203131408400289500018070400802c0360b40700d507688140041a10301075015003019108180c110203603120806009400c0c0d00b625000b0000500080311908600014584 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 346037059 1250 346035809 346035829
    0xa090e061f0201050105031011030a05180109050a140a03020303041719020c1005040612020c010b0303070c0801110f2203140309190308040b03180d091403061005 71
    0x401c81120038606a40c000710141c11080c1c2580103035141c000610083c1410000300380c10100416080001e040f1070707001f2031014013010304001003403a2600c001c108254101e2407240c40350030b0030710004c21110b07440740780c216039513840003004442c09060031005034194000421a032a1803605500a50700d5566503540d501907100c83c2d071061141091050000c1038540016070500d0040100f1500200441ca14220400c5282b443c40d581001c10804200b000f40b00c10b9500c40809009808500e0026841c1c07030040008501512008803082e0300361201007101014080640108002c0f40c508500030000b4506080440156115081d0350442040c4100304d5003200c50410180d4041601a0050307000c0f00503180e644600200743d8240c46d440469001080c030074101e28201d048003802d800703010708411105180d56600303070b40d078055031043c2c82d0345c4080403001030602d40e28901485a0000f048050310b0354070106401c0904540c880c0d01403040c074243c40410b140c186080019100e406040d924068402052a040c1000203401d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 346038309 1250 346037059 346037071
    0x30a0801170102190e0102060a1a1c08070606170303011401052203030206070f05040f09050403020325060f0506130506030309130b120307080306100903020d0c1404020a090e 76
    0xd401c01c840100508040036030401c0c0d43d05942d17940320006500780020300d407c5000d0490740c80c5038174003400007025046680404034200001da0f110f05029007000114000c4001080c40504030ba5000140c5500300030242d030110b0180d07160a0300a0300060f400c1b89586580380400d01944d4020601640307042d01e55030042000c0c018540c000b0101140321404401d03110900c80003030b8400c8001d81e02150511035456041a1107a001c0310080c0782044c2801c1c500300f040e100c1f1480500c28134103002c0e541d0001c9001c0c103100380200d5200112450b030300002c02c1c03e5805001425441c940054071032a1404d580c00031400060301615004980c0281406204121a058100200400740c13283e90305100801202e007094550303040c00f00b00040d2400000a0101d00082488055120000c08091035081003100c40b00152902c1c090329000501a520200919415403040d01c43c0d0420703400182d03020703550349414801c0010019586080d035118800304070b0304000c56001c0c0401c0e801100c0d02030005c04ca02000c24040d2500c41c0b40c280c1d030f102e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 346039559 1250 346038309 346038311
    0x30f040c03060c08070905040e06130c0e010b070309090209130b040e100912020d0f0f0504050a0e0703061418060315130b060102031201051320040f0503030a08011701 73
    0x5a0340d40e41c4104448900304040e022403c4c0070100050300c0c0d0800a408014401501e041c41904c20480200340c65a100800310f4207644080d03c008802d0142c01c00c5048080c100204007407946584440000c0c55070340044c903003240013910b20640414002d03058025914101e4002d4040803414040d08420f8014104103045160000d075552408a000c1108100e900ea9652360305c01c0c001820403950412041030492924010255406049000b800540c4074003511203040052500b070403981035900c4115400e200d81d900059011041440100e00422400c44c4140100800c0d04e003041a203903100c0c28224102000806190b11803a0b003243c007103100502c0000ba41d0702603401019521810040c1c111440c88603025034020303403607005140d02d034810020001340d8030b6000301007400210b060480c21103906403e54014041c03607014600215115000440a1700000c1071008444107800c402d0340d100070040c0030345d0000c0c0700b8030080da642c2000000b103504001c0b084843d0a02d44c2d90301c5400a85c20070260036500007248154980c29 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 346040809 1250 346039559 346039583
    0x2c1207110d0501050c04140f06030f1b13090f060b09100201060b0f0715050c042d0b0903011104031709010c06020a030c080c09090403080a0f140702070614030f04 71
    0x2d8420b116080c40f5482c1d200c162038030385050078198034068035080e840a01031b00411400700d916039240300640c0c0e401000304c0c084440f10782d61041c2d01c241d01c3c44c2e00d5281c0c00c1c84a001041303000e2100d42010800041d01c84114040000e100c40154000030384d0514807034602c4d11901089892814109980101100c000d18000400c1e02666401d210501d544044924403604402141034410002407068040051a240d2420b120500300302c0100b5100c0c1c85140310314a0044003212401907520031802d00a1150148a40822129a5180714805c0291710140c1403d200754689500e5001100002c0d003541d0907a90013030800c1d0b00c0d28140c840b0104e090740c0140780071070611a80b20002400208540014001c64069036000f140344400101d02030810b04003d004601c0030002800481c8140e01e840c040340354403d401d4500b00c04142c40d00001d000042c0722506000c5595030070603500b80b1503104100011800307045141e08946c10944e8a40084071240c442c1c0444030707159141040071620f081e22944c80c4130781040c010906040c42c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 346042059 1250 346040809 346040813
    0x92b110601120c050907080a020304061103131e080304140f030a0513090b0d06050606160308040215040e07140d060320030c150f04092c1207110d 64
    0x1a2940036402146904410464101080507224102004010666110005081c1b081e4007030b102040041c51012080c1d40031000805000498001503a00d00415105540c4ca007032041030341c4107034990400196082d03281107010350340840000081960564000d07018501319115079a412041c2d0020b05400f07100b51042185e84041c0708420b1009180c1c40040e41c4a190f03464101641104541a01e9805040b41604c0c203a100e0784961901401c0200c070aa1000000440e5901e00c030000707106001fa41c0350042d8010343c100146003015000440503028038000c5880034120719186410458504c144c0c00782d0340c000e282550200300514050a10b90690364040814941130201c0d01c0e00c000202d0315294000e81300e0000b05d40c103110701c1c4512848664600b10080e00a0700ea07140200d00032400130640078101441e403040020fa0141000390030025035000c0c0100200603c0100d014034595051400c08214103480c8a06800f1107880407607000402d100300300c0354125018140302068552400540d20508015040646d81600c840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 346043165 1106 346042059 346042063
    0x8070219260301171005250203210a231311030708010b011e1b020621160206040b01170a080f0d05092b11 47
    0x7680700c0c0101c802100c25030070303800107000003500480007041a0350200e4641203002c244c40211100c0000c0124000c0c1120010b030741c00303110b40740f02c5140c503100080c5842020b110100760b80103903401e000ea900b003420a802c40e116440030b100030440007044a52461440313400d91024290100c08961449660640496400030701420142001482030341c04025903849810081c00000d02524441c0d0342e070701d20240c01f0704821002c0d94041880303070400506172002059840d852903003035529a031085107441d0484400c0c01c0000d01c2640c0041003080701c4961842c240c51442030025400c0c0701c00d2200d1800d645180c001c5407845000100310342148003804017144007004007906481440c2034a03042c1145a1203214504903160703500621045001c2030510700078000101a100c98051081e082c012659070b15041c40d02ca0b00148002442c43c0600034410001c801c44494510f4405243c6c2029004103d2031202a8 = true := by decide +kernel

theorem cover : BRFrame.Cov 345863309 346043165 := by
  have h0 := BRFrame.cov_init 345863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 345863309 ≤ n) (h2 : n < 346043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
