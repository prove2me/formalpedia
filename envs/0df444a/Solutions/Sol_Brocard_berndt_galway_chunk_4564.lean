-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4564
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:01:45.503977+00:00
-- url     : https://prove2.me/submissions/c4038c3b-5a82-4c56-af58-bd4fa99cc506

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 820683453 ≤ n < 820863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 820684703 1250 820683453 820683463
    0xf0b060118090e013201050d0503041503020d05040501050103140f061602150711010c0314071d10090504050609061309060b100807110609030a0c08160503030108010515180702 77
    0x4465a102c0d030000d01c0044020b124511000c800740d84074003001782d000143e0b524200c00008505030708500598a0981424980b00c1c148a003402c03000107150b0208180c0d8000003c40c45128841c41c011000052154118030304035a034030701200604c01d86d0f54030146500d01281030200e8019088601d134440300c0706448005030b090303080c602c54030048500c149141d070800c501240c10503120380301c000b1803800070420000d025000398200e40c07031006081e00008045000078106801900256021881c14000103041803105c1d000070070760701c0b10030040350006034060410045802c05010b0190040c0c3c0480d143c1e0110b10b270140220b12003040c0040c0300705146466100480c01c0c065164031000c01c414001d002e4060031002440050000c00c000d40e5504005120304203541c4815001040090240c0c0b0b221024529081000e01c048912030545c001c01ea512410030040c1100240c095200c8160300307840349019584940c903050701c0c07a003151401000b02d1100a008131060a19030741d0354101003682011a40181c2c040d88500c03104910341 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 820685953 1250 820684703 820684721
    0x23030727060513030609031110020a0c02060a12020301090608010f0e03032202030307060219080c09041e0501150915170a0e0a0b16020a02100e120304030f0b060118090e01 75
    0x282c0c6816408000d240e84008032414072301c0440c040b41c0d00026600404022071141c8441c0c40300003400921078100601c0d010000f4540d0320304901d44484070000030ac24610881c2e00070b9204940c203650390302003000509004c2c0124107020148440410000d040c082c0c1894072440001c1911841c9811502003070321020640400304040d60f0080c0481c0e444181c140360490095014600328102804640c1504070703924401c40c205441001a4200307a03046c00d403841c0030300000d48050002c410000311082681d100000d15446007600921003001140040141c83c4805000d8101d6a000090682c480d4425000c00341d402000c144001e580d5100b0f481c120360381c0c00c241d81c401400030300743e003410303e01400c014441400050600b89004124440719240030f000354420a03070360340e00c807520020b402c064254094032840f030140041d0487c21001401c0c130b9140c1c44280e10620300b16880360f0011210181202c9040d024480c0100c2c056500207006c1c200f809100000d0700c008001031180744104034045480d950000040e007000e401915032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 820687203 1250 820685953 820685963
    0x40b0702120f070e150a03080d0e12042903072d09050301110c0c0d03020f0f10050f0114041a15041406091f2303072706051303 56
    0xc540c0d88000a54a515080c803601c0749140c2e01c00c3c0400c009011740c9030b20201200b0001c104540c0369295a5801d011034000c02d68041d0001d0b03582800da1820b0406001c2d4100b440a03c42d610780d41c581c204611480e0280c0044541044d050780c0e044603044041900d403c0701d07003010880c01c2009031070394001e0fa000640500003001400c90b543c046031100c2101d402c24901021740741c044000f441030808404207180c00303014160040e400c5a120b0010218a82021640c8410081c0a441a00c40724401d2611591804604041d180346503400b128001e110310f0003d204290300030030414484030b040c0d494028250900e01d24015928403451781c5200c0304d40100b000d40703802c45401e030020300740740810b042181c02c40380640c000b031080070b05012401c0600d0000c0d01e0074100315042c2d500300502c1016070a001d808100340d00c01030090000309100c09403800540c0c8800d0504c0044034020006c03606640c9161040c4003c060321100f60b00c104511030340d0b1600c140e60300c0303c0e2120103080ea00c40f403400c107848100b01d801900c1040200d07032020708 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 820688453 1250 820687203 820687213
    0x1020619090c1520031e0408030a0f0e03151f05040507110115030b04080a02010603081308160e01060f030207140616052a2a030f01060b040b070212 65
    0xa412440d0f001141c19941c09031075440c0c0841c0030405500e440001105102074a400401c00255801c20030300600c2d080f01141d0300341c41c1c20b00340c503404820300c7e42c0c2c04864a900881ea034451030781006541310801d0030300364600303030003800215541c480c00740040c01d4041d01071340810f007594a0309149010741c171b0a010f005000c01030007400141400790f800b0742000822104103040b9400c080d0b40c80e44100030f11840e1011130750302034441e41d41561982c55010346508010203060071075403100d9002000c954090301a08000c064180f4400d09503180005191506140c0140f041c0c2d4045000000c00a2a4180c20381d941101d070700c0d00781080d0304c403501d080c00c50083c81003600007814a0707407506c0341c0010220002000c520031032250048a800c900c94035000c0c0d585000d5040003c0d12401c884a01000800304240d0710508031220720f0440b503034414180c5000901079800420503100c0703082c2030b805a04510b0708208050903070710303074100030448a81000040300151045000381032500000203400e0b02152a40001d44d1500146682912 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 820689703 1250 820688453 820688459
    0x180a320607032616020f0f0601150c060203010902031e04020907030b030a0503220614040621140411040c091a07021509100e100309061b05040504050f0601020619090c 73
    0xc102c000c04ca00c00302d0018400d0504510b5045000a0340b0a02c003140b000003002160310b401581079900e00c554183e0010004007554000025040e800990b010b84901342c400f40c0c491a110350b5142c08150003042c82d4401e03d81e880140009a19482c880c2a00f045c0305140100b091008440401e00c1d1286100c3c2c01030062100140c1d002c10000e403507400080407880a90b054004035500c0350202d030000f5010100c3d445520082108003d80b50081c0c0d4040510400c45c41d81541c0150004201d000700c9801e041004c90a01e80b0304200020481003540340c6641250488040264030710902005155554a01680c203803002404e07801710810038400292481c6950040503c0900300c03405c0c03007000294200c210140d019100c4001d001d00d00e05e02505085290001c09005a0580c2910440880c0a044c0356141521125900e09400b61a0b070015080190b9a042540b03540741d88a20381003d000459400070140f4174241c4c241c0061049582c1d002c00c4180e08014103090f041c200d0aa09201400148440140201005c1042da000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 820690953 1250 820689703 820689721
    0x110301060f0909300302030405121b0c0109291605100b0a030b1609180c14070b0f04211e030501030b0c180a3206070326 53
    0x207029103d10940c0394110b13501c10480302034044540380610341c41d20b807289100000707030b684a94003a5a01601034401c4800250440150920700d600000e25031a03c880d50300080c80f854802000103613040d1200307180101c0d0b02843d03c550131108010b00c601074038141c558250303407526055075501611a0402d074500e05010340001032800981d56500d441101010b5402d01d420981c0302d1034429200700c1101d80010072a0210b58441c10007102c1c020380321251a0038000010004210242c8240780039481a009180000b5164079003070014046203042c0428088003a410000342001a44240c2a5504100303085a140d07940c0d21a031800b600900d0503901200400516110500a080e60200001e00c01c2c0940070340c10342410382070500840541e10b003404064144144000442e81104a10340101107910025225000039000040012500e103003c0e8030020340c03106c1c19481c1c02604112525a000003c100e507030050801080c0b01d0108440d070055050150602416074480c1d84070010301492030400d520b078601c440c030301483c0c02485 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 820692203 1250 820690953 820690961
    0x5011404030b2a0705030a030518060a1e1802060a09180501090c1106040332090f03190209100b030a090b070504211b09060303030b100c110301060f09 66
    0x1514600d03488480c01d03498083c05010880710842d401c1302c00b40d86803400c03105041e0007901000e0643c0c580c0c04070b0341d42000b00b0000103001c03450165400f410301140c9a944414000320340002d1001519085180001503010b001c111001e07420003d0307059030728549a04032844140c8403400d55910503860340c445803051100160f5240c1c4824140d41178043c04006550302610101c510004654042c050b45d4032440200740440c1c000c8400070700382e8403000d0b400b400c03262040001040c200d42e1454031070420640481d03100e140d131401d030380c4000000009078000c1c80720f1941c681700414280e00c180300207030041b44090085141d1041d002614000b030001c0c004010b0350307030030505600b07130041200320826038044903002c0228906511810855003295554a201046200c0b6403c210030020401c080840b1540314901c1c2c1541b40d00581448500100072441c8001103c51460401070262540702c44000d118a414081400b52503400429103004a500202c1c511003400302d01001ca0300400d29500202d0510340f0441c0c0004071300140d508 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 820693453 1250 820692203 820692241
    0x1703040c030b010f03080306040b1c0b150111060c09041d030c01060b13060e040f0c0f090e0f0c0c070302030708010207060b030604020d0b0421080402040c0e030705011404030b 77
    0x50b40405981e40c829407640c0c4003400e400300505035a0100041461450305e40c00880c00035100038080c49030401524400c480c20f01a030041250030300790100070441e05594141c0c000d886c2000030308107201c1d008541000345844440081c03485801d9000410500e4454445920a204029072100e81421016405c0c0c1045d90f03d8021340500c00e00ca6081180104144110b0300c01d03500a880c014000d05480380c00e006041d241d01011500050b0040c1d03031001680c034044254064070b2001c920320344407540312500429009284184642001011000250034000d80380c800004041d84081800a207545508529801c24104162507001960520840c100410030342419401850681d2080208212502c00207091580710041102c0103580091989040404184140703242c0b0340c020310410452101808030708182d9030200c145030031500000d06941c100421410684104440c1c01028103004500803c3c1c2ca000a030340e010745004090405c025180c8502c00003000d0426140070b90f520419190a034604500791500d181e000039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 820694703 1250 820693453 820693463
    0x1a0603042d031e0e01020304050f010c082101080111041a090301090308180a02100318050102040603050114042c0f10020d20041e05030a030309121107121703040c03 72
    0xd030403c0f146402421103581c00300043e005141881d01c2c0c1010080e000d161101100d060103514006403000907111401840c480c2a0107034884652886640b00c103448801c160440c04050780341803201d01e043c0c80d0725000e8a0858040011050040c1e080d0001da0180d030091400050f015801c0c48414400c050308070300c2052040d040c241ca20701e00e015031501c601d035031035044110203074000c2950901c00008a1003900b05400000d0051b541441c52182540d9440c02c99204da40001e00003a032712030050114602440078440c440700200c030180308601541010107204201501c6004030301c0845d807120703c0740603000e0200c0c03000064501c042d80c0f85500054404000396100e160301031841c5107007508140c00d0340c4d919030f10800c0408554845906240c208034000f007100b88481d4203456590200c400000c0e40d0b941c20070a8150052103664003003201151894401008024014204107000c0f4a00d41d01240b1400055120100c840398000d0b01121101410880808480301e0300300c1c2c0100740000108818005030301d803582d007200d2280c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 820695953 1250 820694703 820694747
    0x1181202070302090a0f06120503030a060911030f06040e0a0b1906030c14010c0b13031d03030702090612010903020a0b0705030c0a0e010212041205011a0603042d03 72
    0x1404040781ca079001400000d51001c6650089603c614081d80701446000f50840002003060700e0301c804410000019100326480e42c0004100920f06980e4090840144450340061198894810200c2824013000b081c0718059510040018801d03950340d081540c02c004c490080c0c88001029041c14601d090003101c3c2c50760364040c40c01a100c0071084610580007203980050041036483d0510440304809541d514180b410800031440c40c00202d40c2803c826801044084501100e051862501030881d001e40d190f071050340e0070340829460703007a1130120840d8811941228803021544d80d8400282c11040b0b00c0c06150485c1d0700e815143c208264001854451440c0240c0107038440380e50ba00000c0f104c61208032011411174074280044156503004c4c85074400002414015201c4400d0440c0c44408181c0066000d1508030003895042c10034444284913510340c01401c4500305030150f8065010400324400500b00414000c88204c0784015001861000111007042e90103200740141c03141001000035084e031400d503114400c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 820697203 1250 820695953 820695983
    0x6050909190e070302150901020c0114070210051c09120e01180806060913030e062107180501080103050613050a050d03020306010f0804031709010e060a090501060501020312010306090c080118 84
    0x1050380c101f024144e000b050103d0a510044822051450380880082424812440141e85001c0d403103c1c160f4003680c4441d20b80001c40c0085154040040c00300d02034030302d03180405000c217448903004502040760342442000034000000407240400030310749995000312002c4d0042403080b00441d00e98083c40c070480381007280c0d840d222350a00b160b11488000801048840494240300e061020107412106507104072281c1c0c0c1c842030b12044501e000d0855820740024030024144e0040500d030078841c0003412082c6003200141d0b046035900baa955401806100340c0211400c4510b0030032408000d0015426480800e46200051a00001e4080d40086e148140464244010040c100384580304507845181c040d5582e0141d0103080594546815002e403440610f5500c0b50115071b500e0400f0003916000d51011900064108141d0070302d10700b11181ea0704524115001006183d0030a0000508c4905690304030100081c503110501d8086040d001c640d0080c0019400d0141c420500d03800c42c60300303020243c000c01c0c0303010407101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 820698453 1250 820697203 820697239
    0x7050603010f09050601051c06080f011e1107051507030f05240f0d030531030627080306030f120708070c0b0403050718050106050909190e070302 64
    0x200340101410790342c4188007000000c00b1030300000d070003000c1814480d01d040e40342ca1249110041c3c002c07a08140c3d9484001c00c00801c80100030500141c60084003c000309031144107521200300d800c800090750f160700d500b5050803202c500002c842c1076550000841d8043c407840c0408a414420840d880d43c0400e24120440210703d840d030090a10520300ea00401d41403c4080300b000300c011841c51280f0340c102d0f1580b00d15000355280c7d201c21108160003525070340d45a03d654866813154400004101841c00904846004c1c031111003002c500a895011b000480c00245030150b008901592000710044840340c1c011a40520640800840c0691010707403e0755000711500c030401d6a2041d5803045241d100a0030801d06010800c0140500101c1e4032502108041c0341c0d494000c2051a0032580081d54036402403001040064940c1c61501c2c0901c60a5030140a298580040071b000e50154840403801454410000741009a03004009001148480c00800c00803448805480d590105800f04074000c6d4010b40445034018 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 820699703 1250 820698453 820698457
    0x2e02100c180e13050d022d0d1407050304062006070503150301020706062408040804180e01062603090916120212040605070c12050c03040f080f070506 66
    0x80c200c028000c907140340800d80d40800c1c80040101140c0000080b90400103402449a8402411544d00410740c00c0b540c2e00c3d4200c1c2c501030301e03d20046c2403001c14800900103c00030500144080c4141410750111001e4a40d81070244950718009045c0d020010b00460304542103241d10603100c41038035110441791030300d00d8480e6640307406445420105c1d034180300040a651200f10046000d20015002505100c819035503503090740e01682010601d607070710240003080c4040d00c0c4030394041903255190500c1d546c00c0c60b0b03c0b0624944598010a0070300e81e03c5081107201100250040c0f19103c0040303008010a0b640c400610001d103441c007422040112901341041c0c1300a10000940d5104400149400000c0c0c0313981e1850402c101403134100d4014004560a011401e02c1a8030181070300c0c0d00c1460540d007140c0340901e072040c119107004001c0c1040c088810300389800310b00440307110344e942c6081d0305216940315200800945140a01e6103c0084009001c402140c0103002080001603041213000b01c0705101c0c4c4482c1004114 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 820700953 1250 820699703 820699727
    0x1908070f170a1802040f0614060301140f04060509042303090a051c08070c0f0504060b0a1107080a060905010b06090d060b010c08030a05061f0e2e02100c 67
    0x210506400b2580c0c00800b9808800e00940d05940164140e815502050681e030a0030521201103980e04420800312181c0e02003c00902000c91b5007a00e035604000300781000b44040150f083c0104012100040180c9484d03120402420005116003154035007490030000c07218500c01120070695043c884030300c03520350000655181c44001414040503608000a1140d0702c05035125020315020102e404402003000705000f801004c1c081c0707550105150810581d209141d02c1ea0303000034026490f0160400c07052001805407190300c1558a80920480740c2035030f8085c900307803c0380c000002502031050780d84208003c0e64000300070319100300c009100d81c01c40b040801001d8041c0e4040690858200384890001940c660b01403210042c05050080d1513203c1074941385910f40040368075800e01646c820031301000349800400c0c17591094440c095025074a400031001000c030b1040d103a6a5020f050500c1364000c140409044041c0c9030780040a40300c500110324003000b1f5441d00c81121080c00d492a00d640e5500541c0b0402c605504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 820702203 1250 820700953 820700987
    0x1b2603060d0201120f05070513060228021908010c021005060619110d05090111010c140a0e090403021606090f0e06012007060e040920061908070f 64
    0x415003500152121310421208507011584c600780c404034400d080c450b1500070380d416580c0580f0340f80c9400020001000540205081d5888103004402d10030550180788400b0020903040c2d8040000351000c0382c4001e4491207a050041410140032441800542c402811401103a080351340a002c20481d000880b0001e0b038606410103000c201d050035000c448e0352032040400c201e24251003030800b0342c0b480d81c0c10644061520070000f00c001402c0500396910194000080158100070003c03400d02807005004071449000c6400564004038205510394081c4650191400025000303070150b180601d002525210340b047c28103c420701d01c100102d00103102e12405c4040e41d10443c06000200d0030300d0401400c2c40c90007400b00d410403001d45068a0390140c403c01100b401b0b903c89000b480114140b940140400018605190046140c14000c4000c28840e4118010401c40c50702d024032110403202c041031452281d004107031004c038a001f0400c510140d008810501c070303000075600d041e008111070b001100d41050715040d940c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 820703453 1250 820702203 820702219
    0x60411030103330515090c0315040f0204180f11040627030f0f050705100c0210020c19092304030f0908010c05041a0f030112031b260306 60
    0x9200301e11108041e01800341c1c1e00e00b103083c00100003642025901e0465404110100480307015030315061070000c41d5005860a2039150542c680b60310240480c2c00c1c3c8440540c480e07511904041080303001c0354129409024200d800005c0304e500d00c2001409015a140840040740c40c00c25040960b03214034099800713450455440c4200c40004020040b141454014080c0c59015011000030002c3d4020405c2c141c0c1a1044400a1a213641030030040d0808046520040c041c0350a9403950b000c05134082d00c0c1b60380c156070407a050441c002c42140e040345000c1140700c0180c5c012402914542900d50065121421211448010b1100028031040040340b4003101c440c0041200f0340b040802c000074010003020181060030324000046036501d0184500b5241052810804221700140901034591144c604822802c5d10340c02c100c1c03400040044240303051005119462440308518104410035104290905d0003c0c1c0c640340e00c408016040c200031200f108500c180d141c1410030902512080441501524401d260044c14a4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 820704703 1250 820703453 820703483
    0x21f090306020d11070f0201090510050a20070b12060102010605060d020c12030a14100506190201061e0503060a0501080d110a120804021c0c0b0a170a0203060411030103 74
    0x4002e504600025440300b601d0782000c0e910075034060050b207071107402007030245810900c40c00050090310281d0401e90150301c07d49583d0b44825000740449420b01c080740b40c01c0800f41e48004440f48001002401d29640340502c420000d2000720820290030202c108c00602080313502d41500690889020344140c07500803809010101c0702d60003641c0901045c407205400d17034454554041034489560300c201d8925103803c1d510348115214802e46640c06078010f030300348074107002c0710705090010300c03180a8030b00c0c09000078280e0065010007510070b4014a00410311400118040c070039401c0c1c10902641d06001e07050182c480c140015400c280c040c00784604961031440500044c00e54030300211403500b26210170b10940d1142c40c91030070010703010030300500713104a840e035aa0350320f030404d0320420004000301c100401c00072417071010300030214240c0c40c01344049501e030002035542c1d1683d0305d000b45c03030076a40301a1680e1414006010450014a00d400841c80303050f0807101003181040c003110400c2c05001c28000036024260020040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 820705953 1250 820704703 820704713
    0xb0126010b030a030f020f151803031b2b0f0b0103290402041805040c0b0304030503070305060d05150105010e01142a060108011a0108040210200304060507021f0903 72
    0x170003001c90b400d1050700c0700b60920089452405603502c9520801010040400c501010751046001c1a6051100035501e1400c0c00007100c6003100c04902600c021203000600800c010070801d006030803079180c4440c04403046202c0c040c140b00401c0000c00190519040c940710700700d9588a84070348800300200100100310034101d2400d221024030100344081e001a403c10011070700510414034002c084a860801040c0c9117070a1402d00d600c401a44e110843c000d100380140400242c0190a0302c3d441482da14000405540781d40006400040f0404007910a0040311441e2458028800b48036041ea0707802e89500b09041f55040c01150304080c00c01300e5209196083c0500c0c084140c052500c2c100b40c404160301402c20300c0484600034101340081c8e020211686d501c1c10804331565280040d2101140c0c2403c000042d46001d8001ca1446141c3e0300c900303400c001448240741521444c100c080c030340301500e2078100c0c1c0e02c0c7c60315888003900ca1303444075005030321400380415513602c150440e40c0b807111400225a11606143d00d16910 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 820707203 1250 820705953 820705967
    0xd02031519061715010f29031501030c021204140d05030c0a06180b01051003090b090f0c040e1207080705031201051e0102190309030b0126010b030a03 66
    0x200d040040c0005806001c0c0384a14028040500051640b6524118034001154a0440f0408015056136426030040184245e040d8011048886284024042904d12800b41c0711030106032003001d000403008800e0041140f000000c018620030283c03410001c104104109030307520f900b0102c5d8016444c00070041131010004507402c000d0740300800b4007030b070020300110784da940d046030000300c0030060680c03100100600303015450080e0443c64006c103401c00c1045189031154442100140a164020315850400c20038061195100f50241030700900307498040e0170074072401a11280fa50707080c0d40711440743c50f280c1a040e181521038102806441e400501c1c1c2d0b040c00e000c8030306458004a0058408403800c0c05408045901400103001480101c03403140342070360608082040460324400b00c0c1c2150541c15a40344d9035640c002488100420314210751a51500c528030b0110380700b140980001b4500321506000088011680d040198040e0140840800341040080510700b01c0300128640c5038194000c1c1541001309000e000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 820708453 1250 820707203 820707211
    0x10c11120114070302070b0a05060d02090405160b09030705060f03040611190509130c020604150207020406080c010816090303140409020a0e0a08160e060d141005060d020315 76
    0x410803081d420b9081c2880401280c442004c43d800050340c100b08a00803184650112003000100090704050001c90b07a40d50707411100038001c044030000300c1c0522804008a283d1502803828000c0360381c0d280c0b0890f00c040e41010501500a1142540c0440c5a15020059550706400189803038103650761612200b02801c1143da0b420900b1307008100c500c00b40d03030802c600e4000852040d141c180d40c4e4001702c0b003807150130701d500d80082c80641d1a0807180402d447e030129484e034005411050004004001e18103800092055110095009140960005000c480480c0e900da100fa0300362500710060762090501220b84042000702400a400307000240300086c0958801440b44032800c40345401e0940b1641841c00302d900c4540403101180002d9058056403400900400c00f400101e000707441d0440f0224840c0e401403015000d15004282c0030740c0000c10588810340d42a085903006441610b0700c0d01010038154440400d40030b0030800c2030030000090491f0030184120b00707030140d010303004164081140400b0300c0c80c820064 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 820709703 1250 820708453 820708489
    0x40b030417040513052403031e040801090b0613050105100c0303090606090b092a22030f0606150801030605130b0114090901050907060c11060a05040311010c11 70
    0x880041181d4640c040321390000300c044d40d80000d281c01c1c1030703e00000030012101d050740392009125000040751030100035510003415a607012100481c400720850b846010320b0f08110042d6103003042c00c90a02018415860244002380c0d907506609120840c200140e070004d010300c44d008a000403540c4803c03441107864400090080ca0700003960042607403030b00c00703540741540000d19140e05c405006043d440c000700610341005072000032011038003140200400300c2c1200c016002c00b8140105918550228402c0031700e91801d0f15542011515407246080c10109552105c1078a2280c6844004a20031051031500108041540c64007415030386156a00005060010712924001076a1440000042d0304040042c1c041c110400000e5403008a40d01400b50701d510051442c02c05a0600301405100030002c00c00030709482c05480c1c041c0b005592400e100301d03100e0900c5190350304460000350f00045198840301400035203100c2d0125039410f0b00a6001141c0a5a491802409580c034201c202c3c901441e120b80e402014207400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 820710953 1250 820709703 820709707
    0x41205070c0306050109090623150d0501050721060506090621010303021b190b03100324060e040221010b090c1902150703090320071a040b030417 64
    0x2a543e00c1c0076610b003a401040c2d00c41d01c480c000c0d000c000c142d010380e10b0645109504900100d21102030f800c6032041c00b522042004000415481450f16184285980250040300234802410500d0009140c0800341c1d61040050800c1c41440190138014052081103d400821203400c0c4000101042840d90040c4003841404031400741403003900b02082c940c280258007d40141c0030f00d50741483c000d1841d2455000b203500c0703400b03080390080031101c9003082038054410170b03560161a0764400b05100c40d16005500040d10603030314540c02d0f803184240450321140000705d240e001e104d815600c034007440e0285020b54009501ca0791040140c81d010001183d4a07140618220000c00d0981c0e0203000304490402c20f4400aa10303050004214074a40d03c4640c0c4809202d501d4030080038040c8261315414001300003c0d044400301a101c4150005252107400c004881c00008100c0d00e103201c40107400e040d0f4400d10f510030003201d684502d03082840d40420109507011079255580840c80e5a96035078a20780810002200d81c0d0008000b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 820712203 1250 820710953 820710959
    0x506150f030a0e0d09031b08060f070e1206150927030d11070209010e010602030304080708090a0803070b090319180f0314014203121d09041205070c 65
    0x3000750700c0710b95084d522001c11941c250308100620104461000805120f18030042010260000e410795000c04441001c01054581900855442c0080140d0342da100c1b80c084069111140c020400c940250318105500c50301c10403402c184074440302d045481c03030459901907000d07140000045050442d445072900c2540e20300202c0060301c2084688009040e0841d5001040020850422040070b078003619500301d04904039071405e08029601c2c84005c00061005102041110401490b0400d640d202c442c001c2004440c60b840e1044143d032508103180c1078900070782440101d0f49401000c0f0495420622048802c0c80030711031030342d007a0b07204070310841d270004e130802c6180c0c0000d4510684850b41c0007851081c1d02c0300c059055480b08182c01c0d1601c5000204955452455824400b40240c070300701c018079090b85400c0010440201d08841c2c013445940050031280090103146040c9034405406203584c04115030300741d03040580c038041c0301030354a04440003010070f1035041c0e14216441c0a000544a20391041010740c8006403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 820713453 1250 820712203 820712231
    0x10c0c05040204090b040f0b030a150b0a1203031508061807350c060702120102070204050a0b1003060b030c03092e0c020102090a0911090910090506150f030a 69
    0x4001c0d4002005181d80717440d6814289820700071104400c0020609028003d61040040e89504c11640002c04201590907981070060268018402d00000100b000000c15a5010315840b540f2094908038002441d00d12600080c0d40f000c5001000d8621141c000c04aa42c0c4044490000524034180c00142c1d10450600041c214040d030038041c1d004841c0f04d11a81140d41e18461940b10700f82c030f41d0308800c803508400303c0d181840d01c400050352010368048810072011048071032107600a20408601a41180c2440d04004dd0910f00d070301709560008054900d41608559401c0880480d411406020866042040410348840c20300001d150449458010b8402c584d4000c021b90f040c000026061503403040c8168090150100c00380700d204101d55040c0020351902d5241000200d04000c18080c1b400e855a940c810303130340506c045600b0780360b500c00d000d0982d81403414081d4442c0801c024612410740d0032410000081c41314184208070111159080d02c9103030901d904200b4400e000d0b00020100084280c1e213103012003001c6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 820714703 1250 820713453 820713457
    0x1b0e0117150102060609040b07030b1c24060b0409050c16031e05090d2301020703030f060801020405060d022d1c15060309110603040b160206040809010c0c050402 71
    0x35460380041d10741c0c206038600182c28140c000f406507108411b141e08100114130013891050b444481450700003071400600c8002501d100c2d115a4030481c094180f40d981c1e0420094144001716903140070207031107683d10500006020740c0c009000350f5400206c103120070080d052064001c59080050550000d041c51046105a407081550500070703000680500c0150a40303140e29075600c291200c87e4900f05280000c41004a10141503e000040481c08090340710700e4201c8044003c54480c08031103009564a164a040c000d015002c0b03549002a840c0c0742a400140c46c800c1407080700c04492000c0c1c08107041100d0b0b004400025081120100104001003881d1742c00302800f400c0390452006070303c18103030f168040b0780000c4840100b072a03480145907180c881c8001616503149503200c00c442192070b003c6a046078074030f00b151034180c0000d071040d0420404402e100070881e001102c01d10034600800c040d103c17071440c0300d422a80e079101a1405002c104040100c901254403426401000b2809802d90800303655031500410120307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 820715953 1250 820714703 820714711
    0x7080a051b011b0f120f0f0608031e07110303070803182e110711090a06060c060207030c050d0f020c030303060a0e100b070503030105131b0e0117 64
    0x100d00260080c40d1205030126008400c64003002003008010303051080c40180443d986840500c0515650a81c3d01e0348919001d9401c158661002c1c040c8500051015015000c18040e2a80c9a4207146001c5034802c0004142c4400c0c41400003001c0320117a4000107000e15601420055038002078482c0d0200042c0c03000c00041282e03034802d00b116640e0f407900501c4a0124003034400d0240c4960064030969000c0b8102e2814030700d40c1401003048401d04050143c40740002c0005101000d80901c01082d03c1c018004090a81101d00d1020340703100c650b544e1111081011900745005580100302404140030116003158080d1640c50b10a051034450980c00d070710342e6032928011100d4000003510202d01084401d40c14492242c03502000e5008600b0740c200400003802c0704581e4040e070040001c200c400542e416150100c030710000c15005100954850490411039142d50090141c18040c2c01014501c503000c031024820101c20f0a0307801806440c60044050459580620740c05003810860486050524550a2511a0f0213 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 820717203 1250 820715953 820715957
    0x40207052109090c09030c0609010201090c140a0b1204030c0c03050114090d0f1d0a15050705010612050a02010305060f130603060506030f1009050319020c03071a04030f060207080a 79
    0x19000d81500308070301420700130400040c0140c240f0018400392000250303510f80c81011200715407100c3d0700b080100c0c010041403202600da5515803d00246940800c0e03208410000f041d100203040644500c5011554800e004903c80009a1200001c0210f48a402c0d0361100340c2c452542c010540766a6110340b03007541c118150b0007410004440a0043c0240c00f001007500803181d608181060709030544001e4030002d00341860102d42c0c180360040b888103584109410026204041491b0118407203207138001c00d5030300101c400b11095881e01501103000e403103001d070b00016250f000300184920035103980111301600001e020240c00c82000c40d0440d1305070780c4444023000009025000010306c0e6113107041c10750a0381d0300170b00f00714005d82010f05125802c04012407114034088210002040c80c0d6240d141c503e265200760300400448004c608200c20b6545e44c0810399a182340300841c120f0308203540f00d100302444110604031901c010041000100001410540f1030303949280901c0006040c000307543c0b181d41b0309600c0003140e200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 820718453 1250 820717203 820717207
    0x30415050a09050a080a0809040f020c03030702060106090e04030f140f180405100e1306090303020c0f060609011502010e1005100b090d1e12020c100314060402070521 73
    0x703407440d405403098006020440e0100c9510345024101510f40d41d003480c01406110303000500144503115608958915242500304554aa8410b00070640b00d41081da003010050164000000e000c80c89074117440165926007070007412039291580c0568115007102d03118030070300981000d03a4030720490400181011840140b0300544c0c031840703061250010310f50043c51138400c600d8002844142004c1c4038005003541c0894030081950344600009000c070362840d100051a1074101003110042541c180c01a05060551404554030500c0c488030503601c0340000c4034001d07084901d04004020030341180c03040040c0d01043d80000104200c90841490900e001c004119400c582c0398814011a500d103c2100b20040110403021814803400d17400080c4460140280900411140c51b203280180c1010048246159802411860441924100a521441c85521252203444001c0e400044903002e40180d0003560004001c0c034205564180411000750000c0700152090701c180c40500c03001c0d0800e041e16007001c550342038032a9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 820719703 1250 820718453 820718467
    0x60f050a020a240f0e0d14070c1d2a03070e09100608090601150c030311030906040c0503120d050702030c0304030308090705010f083106020702040b0a030506010e060303041505 77
    0xf001e803048856815074079842d1150402000802041000130f43d60b8500e07000d00080e0f008401c000d814025000041c21046504000040000d44030b011101b624107031401c1610306503111403030400510745140035000004446010b41b40041d005100450744400141040300040c0da00e140814003044c000c890300f1303440301001c40d42488900c0e0402c0b490b5610000f0b00c802001c0c90743c14a007800c000c2c4182e003100341c01481041e1000d141058080d411401c01c8078080e211682e00c0e0f1419000c42c69550005803400c1c0c940c00160b0030007242e1070601250b0030003012110340c607051808240c281b80c6802030000505c801d0842c00180021404d4160070701c01003000f94082c4da01c00038141012000070b400c01c10281e1010303040c0f017040c08030340108640004880d6071006000d641402d400c0140c4003490f00c075415005201242c2a00c101c1e58000b0080654082c000c400d0095408001ca05140b009200e01c00d1140c0c04003030041d6000307100402120b2401061540d002c2005070541c1c0c201640c6108402000d04405002004510007060740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 820720953 1250 820719703 820719773
    0x40f08010905010f11040b211302180c09220e0724082e0602071a040e1b090d06050105030c04051017070e0903120f01060f050a020a 58
    0x403000c201141d8100300140889040048040d10a51144954024020821010000d00354001199040c0c50200000e42391401544031180d408810104074070624014100c9a405101c45000d00d105034451103800e072610400720108040d809945040940d0011148000307042081a80242110315202c1b100801040c0d0905009048104001c041c10704071184880003040c115610200745a0809080e07080040c3c3c400310a541100b083c0103503407041245c1e003400400020202d50000f0310204641003d046a004401c00b041e500c2c105105a10a00780e002d460f0801280740b40c03858810b80382c80c914120700341503d03020098010400c880320300c0c1d500b81c1790165a0401000b05090074444036080d287c1c00c484c108410b107011161052011011f014400e0362012800c0b48040c0c2c2079080003510082c0c004000c8051301403030f01c0c003047c40d582d82c8584403180800c0c1030100826031900903000d100d03050355641c0e240c7c0c1500d810900422607a982180d0301c204110b110f24424013020944009464540409080304c200b4805424996 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 820722203 1250 820720953 820720961
    0x7060c170a05040308041e021f1103160b1e09011d01050907140a2706240e060702060a0207090c110a0803181207020a1a0d11040f0801090501 62
    0x441107a060104000000358081d455544c070a0f48142e80c4500039048401074401d601e01c4c47c20003900448040c48010204109504800d0300d502c3d036039284403900c1c40071082c0c50345a00802045c4450b18090024113400a1811560968450b01d8518488004010145000c1080c0401d80e529a0305942d10180150f50641d02444c400300440c8141c0244028203002110390303607486d418421034880c4079260f10782d1440c80c1e890b40110001000c1110018060400411450195007070300032040300e055140c010000341c03403440c100c42c03135428207034114255402c07002e00d900030365009200c41d03500741e403008040083d0070059484102a00f8080c80d181c3c0100110707400c25100d0340880e440c030800542808440d024107007a408000808000080d4464480c644a85882009070400500460040b110f80245070091516014280240002500881d40807008d644d4862100580b186210283c03c640390040100318010360250b00240c44051402c00b131149442d6031200e6501041c83c1941044c2d81c40e9440d03012070402d00100b402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 820723453 1250 820722203 820722211
    0x1719180509071d01030612050601050f0d0807080c07050409080d0501060518040b03011b1d06040e0a0b210109200105030402090910061403010c02010c0e040207050307060c17 76
    0x40007445424a08070207454a5500c0000103401d0908202a5642d03034460b800a10040984001da081c0300425450081e486401c240140c5003d1100010100c00c00c0c07503c40d890140c2e4a800c120004d2a140711629802069844440382c96184d03c0343c076800007174680b43ca100f040e00d15030040080c41d495801640900c0160740c01030f0b11620810809024010304091007030105a6488001ca030001101072207040404d025100041400c03614036019510380307511a4010300200104c2003903013080e41a03941248200310b0140241d008007082000c4c00c0d00000d207081d000343d0085030300c0c0e600140f1550403c0c44901120486c4841712032a580e00343d440750200303010840070f51a00071400150040702081043e8000000380365001c0240084e104031442004501100410310902e0042e4004039024410103803664400c800d0700700c4e00d40011740a98a003107100500d461040c4202072020307002c0d40c1da1121406030002008040c1d0060a01a07070503000800441002130064805e400d02540c0b0741c0c440842030340d0b83c0c03440d07116010f000030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 820724703 1250 820723453 820723459
    0x50c010306052b0b0114030d140d05180703053a14130b0a0e010203090d080f040906090e1c0f080a06050907180906030f17191805 57
    0x1000c14800d40c0c3d1210b101d00d443d441401c2600700d20701203099900314003d05050018081c620741d0000850203081002d060303e0300714030a070304480c149440450708840500c03400c004014401c805025210000b43c41c1d801c015009900d040c54508a0380001008a0512845900c1241c047c0c0c031088264104007400246c083d16101c0020007a2405a2000a1050a00c20004c0800c04001c512a60700d4603c0500d50190f5044007000c01c003480000c0e48550178040300758480305e69000450f5000f02403a07070540c400001c40b0029000540f5403407110207030f560780c144c1d030740c20150400a00b014184000b007002c40301c9219000c010f050100c40131035090700e2104101d0400e0000c0024003030702040008004096a0020440d00031140349142014090303550321019001080290017165114070050240140b09500ca14101650740f001032040c20425560301c01e0604a440901c4000d100d055044080d1000ca4090000c410352401540380180c5420340300800b42680200500000d00400c0d00321f0210051065111200c002814045d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 820725953 1250 820724703 820724711
    0x13090606050f040e06030304030f0b0a1a060913180507030b0702120f030606192705030d0c060b0a120605100501050405060705010902031209030f0a08070308040c0302090c07050c0103 80
    0x2e14000e541c510482c01450710ba40d43e035001180c1c8985042040750010340c0c2003011143c0c0c5041901e8482410314040d1441d035501414108840003001d1110300000600c0d00042029240c41c190f00f080c44402007103100004075199840c0c880c03840181c4032840784504070b0b120360040c7c404203056140180b18240050800c47c2198844030441c1c0c2101018021210b18900d691030884c2c5969409000bc0c41354800c4070f00142240ca1000b140b9010a5009080c041114082c0b10074105c01046044003458914828403034168194414515002058050555010414000c802c041141041400441d203005180c0d1310401550707080d0b00d82030b01806403d1003403d07000800003100d0540d482c0742000080081c00f8038051240304120008041d41004000d5002c0d100a0b603002c2c05842d16240100200c1356070386c10030039a0034001d01a400d00400f481c031011542d010065448404c2c5401c3c0030042d00d0485e01d0210041045405d14443d0201101603038810f032500c0d210310040301070903940320340a1070024104805243c4042c10f142c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 820727203 1250 820725953 820725967
    0x309070303110f0c011d060a1707140409020a0302190806100f17090f010c0306080705060405030a0305071a01030b0402040b030604021f051b01020a03140403140a050c031309060605 79
    0x401c000d5400c0e18246041c0d0354940d14081c0500761010306d400031940c404000076100040319040000c00c801d040500c280514543d40c0c80c0e100b41d1b0f80c448074141501d00a8001c0105003c03a5034154050324061305c0c6441d006052440c6113248103640300c211415032010940140401000d40303004414080c0d00c61051800080403a804800a0814400c26500c0350342c03055034400103070305800200084802c214004009100c0102000e201a0050505021300400b902400f840440c240c24036004460803500040c00804601c03041d80c604507480d4006007404c48040c4107402c0e4058032904243c1071580a980507014130791550400303204010468000380e200c00d001307401540401c400b50341c600f10f074560000c031501141c00e0105051801181d40e4030405854080c1c40d483d071050f48560100560140c0411007060710b0400003908031071a0480342d4001110001c0c000303030451343d0880b4141c10386405440403008500345941400014031481d070840c6c001681c00c119415220100f000101c040d03000d4000101031a00380b071031415030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 820728453 1250 820727203 820727233
    0x5011205030a0f0c080d1505040c0504120305040503030a1d0a05090f04260c1005060d1103150103062309030a1b0c06021c050a0905100e06030907030311 67
    0x9101141e405000e084400f4140003030003210011120341d0300c4a0007940c1e5604105650004089000000c4c00c400d480c0d0b1004035460400d845080032840c0c00f600d696040070301d40569000d1440085404030f080080c14400024185c5041010f840b5141e01500c81582503800f01040c0c070300519414806a10514900d04100700c81d403a01c0c1c5c0460342000030f0300c401148a40d00d0341442c0c12558180c500c202d000890140c1c02002e25140c0398080e103240301d00c900a50b07641045208540094900a07917445500014070004240010300c0c0d1400c0041507440902510209140d103102141c8840b400d910958016450300d01924000403079210179480368180d9110002075042480d03840340c0c1d0b03000d44d4110b903041c8010400c2e02c1e84000324100c4480811584500c0c89103499899900c025140d11030204e1040d51421410007031440307036000c3d400313403804c504441e075503500d20910b040304002945402c2c80808050010740a00308101c0d464040c0214070070b031408070007400882d00c2c524008106021641c81c40c0351030382050707552503202c131 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 820729703 1250 820728453 820728457
    0x19032d150510120f020f030d030b0f060a0e010f1206090203010602010c030504030207060e040603210914030c151e270603010b0a110307030c21020604060203130206040f090501120503 80
    0x140c001300b0007a01c125003840030490030000d81d64425814030509411600d410380c560030003007034070000b6603201c1c898001080038003400340180290000410980c25404035994031807941481e03640310703d252045c03001400980b908201c490035088405403540010050006980901a0068603ea24a4100300c00c0c0340c581c8000351603032f5060003a1400c00141040b03081c9103a9894020a020b15088000984407040c0d0160100102e10340c4409000070420f694400a50103030b40a01c90070485d076001d4054400c03210420100503805249000241510f02d0501262052109201e0300f00e1449460208003a500e8054003400d80204040c00c16946c0340b4410400c10300e0507610303110281c0b411a44129100758540780740c1b640640b80e1468205c07144a0601c40420b903c5c0c1415448406108075038091001440e180800031502d4110140c40206540542c0c88078003c9000a8442d42c021a48003040c8904010104026800600e255201368440e002856454100340600901e500c5194014120b4485040310010b0f103a45541e2a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 820730953 1250 820729703 820729739
    0x12d0f1e030c0e091003032010020a090909030f0311161101170411090105040506061c06050a0609080610030f0303090203011104120b0619032d150510 66
    0x1a210a582c004560191805030100c1c0002800c20020b0b2a0000342894901020310090740040c3c403000d482a285051442a03902a503c5100a0000308480006120181d4404a42442004101580020303d00000c0c0b01e21760503984a56914a5030200c80500141540c0507295001c807082400c0060f5103041d070381300000c0c1000990003c10280260000c00040e103d041c95240d01b032034207944d1a82000700300218402d0242c8081c00c02c8035501301c56600c1e038092100704c6104032001504201c0800925901030032403452800c8005003000089096030b141d82c00300c2c0c844c103115440348021820400d01403001410034802c030390b0300c0200c5131075000600d4595101c82c40e81066280e070140074144d60754034000641d2402e4212417029400d0b104140c2da91551803103034803082030a4400984003549100c01044042c41c02c10390616150f80c11402d480c410509585443d01c0800321040070880c500201f00040422082c41c1c44c48050840c02546c840c5600e808605121003610401040c1c0c025103005020b0170700028075103250350251 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 820732203 1250 820730953 820730957
    0xb180d08040507080f0708070902041a03040f06020d0b120f0a1227030201021005070e060a05160809030708030309100203070507051606120e07060c02012d0f1e 70
    0xe88890600b603007048520303003001190780100321500070000d2000400304216030a030301c2221030250381c03180d140701280128041c090040318a68412020110100082d603005030280c600300440c46003607030320a002c80c1c0c040f90411640549071150031403a4504420741c09c01c0c12140d80090886029080403203911030801120042191a0343c1c240149000e1107542d85416039130502410b0010b940c0b100160646c0044107110880c014402c45031201d118401d40d020b068010040d80c0c64843c1040760030020404950404d050001c2084824040c090182040031002500c9078020300700366554002100c00d05040500d01e40200700c00d58030410a101071454005820b4488148005c0b00503200d44400e01c04940324411004082d08620a10190603c4120700240802c11a000d035101d00d01100780d41c5042e4010b0381c0550030f9041646d0880c00c410000715000d00c040c541c0852051400311043c644440e11407a00101e641c00c1d0000d040d4802425201254000c00e0140c40303605242440414000038184001035482c0c05000502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 820733453 1250 820732203 820732217
    0x15030c0f101e02030702091e060f010c08040b041a07050309060304030e0306090615101b1703010306020a0e04020c1b060c0106080313060c1a06060d05010905040b180d 73
    0x3868422842d07035607100322905041c010442540c0c1c00954a030403500061f4499074190000c03c40711700e032455505103d90001481d8102542e00c4030700304070116402c07101d2035050200364003040c0f00084000300180003904007220b000d40c40b141004201610742c50040c4184480c22400c00501021900000656903003a008031284e41d92640c0c0c5290450b2006140c0d5403c4c1d03094810001401400071004c10030300d105210500e108000305024400300480c40c1c00740b602800110741101e011030b181d50140080c283d08180070b810006014a903240d01000d00c2d50090707100381e4142e03501003800d0101580c0420401c140034030407901541000008541c05481d904c24000710019210700c8545103005031640c10a03a00c0910765074000b040456542d0501390f440e94400e001282001d403031048040345490048210742d00700e0b6040445c0b200d072000c4003030308080c0490f005068254041818003400e05802c04502078607000e030080c10b0010a99003020b00d03029036151400741c00d81507003007443c04020781003410010f40150803011910b0300407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 820734703 1250 820733453 820733479
    0x403110a030b070203120703061202011101060b0a090e060607081204050f01020c0304082503330b040f09080316050d02070308011a03100501030c020c0301060303030515030c0f 77
    0x85480d00160300007003034031000a0401901c0c0c3d4022000d06131840d036a58907480c250342d07411001c40c01c40303c4900074040d00050307800c00b00016501c24039034922041400c03400011002e885001c4a102a088400c01c1c50000c0c0a41a045c480f44d0302c0300c404503410034019901d803414060540e440c40c200d4011300c5080319a101100000a0501004004441076049000300031540c2e80f42c1da041c010345903802402562198810240445a40e52111009400d01800d960064007203500b10798070403088808007062112001f0025080c00848054401d142e28801840c840c0091003140c400b0601c003d40d0b503c0030081c50032500e00721120011820f80c0007229401001d1070031200305500a400c0030780d45030086d820381500d918400b1078003008254020007058161181c1428260384800220102821803004035140d0740d003507481d900c0800403540260031410002030140181c40742e010710034004c0f1f82128881d0f8003d0700001e48400074012403a06610510740200401e03005032803061641b5001c6003000105c44810b5004102007c015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 820735953 1250 820734703 820734709
    0x40807030203090a0e010f0e161b080a02010510061e0e011b08090901120c03110a0503101a011107121115041a0306010219150e03031f0b040311 63
    0xca0000f5802040004216100c07110340c040310409000309404403445410124400302c4684a070380c85000c003450084201d00007028110b900d11048aa1254070046080980e4000f40300500a00a4500c60390300000d11071804000748512134010b58441000d00000c101800f80000101c550340300d1342c4019040503178203103032100012074000b40c420703001440308050b1003015010000240010b002c03404040300e200e00e5598a4603049049015181402400052000b0041000800b8051230200d0380c0720040460304810fa55402007030400ca080b05501d54459521280920b9980c0c44004401c5a114280f802c040980b01569200d070b070700e1100c1d004201c12064921100801c220320009003442e40079003e4482d21100f440443c0c440c200c2e03045800b80075000700202401c0d4020403081000e507407143e103059000741502c9860b000d90401e907104038401542c0200144605107035105880c02070b409800302c2c0c2e000070342d83c030b18148002d000740000b40b070803900c18404643c00804c09036052000b03070340c287c9400081d004010b1641d0000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 820737203 1250 820735953 820735957
    0x30e031308010917121801090209040b040204060e01180506030708010914070905040f020d05101d1005090607120f0c030204090b030a120f020106120f030207060305010e040807030203 80
    0x304080010a101010503024410340003c1107552113031800c8400f20088024800c0e06000701000d094502824a000820004c200865580316695210000500c0140da80107d0307125241254203594513100e91041c0070031400e03c5d118131802030004030b4034001554140b1607204040510814221030494417040400d0b1039580034001d103c01060220003c01001103285442c61400c44107800108250062600000e42000680034091107036030301c0324002c4541c480300e500f000340c883c6846000b582d491052468044004c002441881d050040d0246804021850340d0600c1e8581111032040389400b50811041c0f00c01d07a1000661150805414100003031400c100c003c0540003054559a81c0c0021400c100c1c0407018190140e0082c0180e80c0d00d807400384094410030040c1940c614061800812340500c9090092010b840703400c695810040a10010810320380c0c8101c0c4a55014402209650401003c03181c00109034040220500030102801c05000c80e40c50256407105c0710310000d101901c64040064a00101352003441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 820738453 1250 820737203 820737217
    0x9191e03053706180b070908060907090207030c0c0b040f050f18220b060f041515050c0106140103050f1b09011e020106210b060d2907080708070f030e03 67
    0x151484c20030300c140c2000314921905440301d030007244600300d0200c1c000c01c020454a12500d00c400c002c1c200d00c1d10380741c1d00310001e5122020070b8040048510042000482c1104a50002d060100e141c43e01c4a0408190b0b141d20b60741603014a204002d102507034019501d41e0f101e417084801103115a040c407a60f8170000e4800d0604500e041c100040c0c003000e10700040200c0c44001b0341c010002603440c400500428014403007159192207102d01094000c107003c0000303403030060b0642c0702c5d4015480d18500f002c4c40b501517242940d0080d0410040320382c900110000d1564141300762680b080080308034407400e0801c80200f5003480e903450b01107000c04038005540030b001d9010b0494952a10b180c1c41c0761810760544088000e0003003a02e8095403041d03008030007004d07050f8083d40301c03590380b45034104051a40a0700c4070b41c2000800310704400100c400124820020101c411100b200048800724075144502c01d1422f500010460b40c07000f0301501c1807041c06410f01100c90780c4200c02d4000008a4100000e00d42c00c10a001440c6000711720b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 820739703 1250 820738453 820738481
    0x11a09070903140609191a101208040e06010e0d0303050c070c062006070207141809030a0e182403011b021c0509191e03053706 56
    0x200c800d184503900007071350500c211585000d48940c81c041c0414200840441c0c3c0340035094502c030f4003004003181c50f00807203281c000018114107a01ca6986804001140f544c103001500c4540c2d004c5010040c204c0d550005c9a4440402d180c0b0321010146003000075040080c2100c0982090b84d039100107202021540304880c0d2064200700800203d59031400014150f80c504040d85800741020407420060000c0001c12a010300e0340b640141806900f0f080c008900d1900440c042940308008418140f48448400781f4079014201d514065699440e818002405844c10500032600504103560700001581380c8440c0e06400060000030b1000d02418140c01700200214140019415464007110104086008907074603c040710795029a000504523002e121201d0050442e03140200f2010000501c4d00d00d0080301c4c0321100c4411040c18030020351600401009010305118460840c2d402c10360920601908110700c041303a00860243d041e9000c15000c1091884010746030101c2c5000d130604000301048101d8200750040c960391 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 820740953 1250 820739703 820739723
    0x9030b0a0e1b0a171204060201020a0206010605070512031f09020903010e07050f09180d020303070e0d1a090a140d030507020708070b0315061c0e011a09070903 70
    0x1590002000700300354032002155100710048105144050102840040c2e4000c0c901c04101d0700e05044520ba5140003d55490203000c1c00e11594a164441000707080500310690005841d0905418084c0c90088182c00c46003c2c0a0b083c4800c40004e040000caa440780f502011b071194494071148900c6c0da141040e08900250082e0514001c42c071231540da405440c400100310002d11500000c00c50203070310f42995004880d0014900b0148070040d040041049800002040458885d4041842c1d01810b14814002050050300000113200200e58004401a28480e080f168810b103108103a4176040e0a01c15030082e2144500741c6000501090f41c14460180119001454048035884417503505440f000303050343c10130102c0d2038030b808100301c0f40c1300207211000e6a000100820440d400c101900340c01e0f0700000e00e041802c1c580d08149005030780b20540944064450708840d2010b0070f600e20508004d47c0c070342c0741360041c40c0e0789031409011044000c0c5c044c0080030b030400e44484059444000040700d0401e501c5c1c001a05011030f07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 820742203 1250 820740953 820740961
    0x911040503150907141507030c0803010311100807050a0c020303091017010e0402060409090804170c01080f061005091912170910030c0309021f02070506250309030b 72
    0x100007640c2c810b000f05404d4070207094841c1c0000c02040c61013050326400a04000318032903101c00810003070207100d00a00b01200d074a421a90760a20b603130320036081241ea038803131101c0d642d1a03810090b00580b422102420090114601028014403a004a04c000d00030050302c2e010b502c041d0f49050007122211b5201800754480044052006032170101e605400c0000306c6002e0000080b41031500600c1400741d0741c02001c1d28580391910038007802800299009840800e4100400244034041c50b01e10051445800c2c0944031868056001400d030502c01042c110703c0e00b070325504100b5159035100c00e61280d09054101503445900b52000b06164080b030041c0b265010813120000f041c1030012452109135a4403a041424064102c14020030941c010b00030041c1d00999251900b120840c0640c000b080c3d449114138000401032000e4000541900320144448425103a0b00c0a915803d80d050042c503020303000650b4002c4c0b8010325441e400928480d10221aa880100c004650b0100f600c075507550001550800040401410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 820743453 1250 820742203 820742233
    0x11030f1b0c16090b030a0305220303030b130b0109180207080307110d0c030903062a0f1d0622151701061809020f0c1902040b03160911040503 62
    0x61200180100d000d400100018401524080c001481c4400707000f0781106e40ba6a9800c0c0c480303401c000c0308030318104070121002410040f10080b0000560003690003003540c0d04c00d10188200050021aa0102c01b4100752907440c15903000104881101c0b00d4034041c41d408141810f0290090040150040040b00e00209008510368010303002c0c0d5401e49000156034840445036000e8840c896500c5006012601078401000450b02a41c130245012110080c2c5403a441161565609000c00d105401008640103221000038540e0003032036002104114048810381c0d18000c40000c200307000b200003010b2940c200c0d40c004104802c035115100020403c840728042c0c071030745100000c0c0140d50005e2580701c8503100140002400c900c03402c030301c0780c1d2406407401a800d00b81c10300716204003039403156403042000a000c200c00310700414104001d680c5041c1002200c2d826980380e02c1003005840c41840440e100e03903c00788a115568507160318030340c00c6441d400030008400c0312814500080c4e0080794005d960501402d102550845 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 820744703 1250 820743453 820743463
    0x9090103080903030918011a190e06070807030309060b030a081606020c1209010305070504180905120a0302070213060302060d0c090b1207020f06010b071403161202010b0411030f1b0c 80
    0x40c660240756603015030040d6a101c40c0d0300502041d000027402c40c241c10702c249401814004802352000e030055180c40e105440d0a081030b4441d410840019a40f0000403080c08518425049510390881c003520440e00d954440640d01d001d1550403040308940d9845001c200621a0b04803003162025806032140d038240e030558100c0d9500a205141c1c0401d05000000e11394610440480d0203681071114501c10000488400c000142075207a01241c082c4240805050348070010740103410461841d544c0542e0384d040c90f1040c04107450311420b064070141e08104090005989090580301215580080040d0350341443c1002c40b413140d0f03c0c1d0302002ca0002d0014002d003240f585c8110f8580b00b100103400321580454400b0200e960785400748204034658009011100006803426089402da140c3e22044a00304000e903001c3c2004142c400c87d040394041102c070b0742d1a2405c0c0d0280903041070807208690800401a0001c0b00210603c80145901c0041c81100700140301101070f001301c071681d0204800e4094540d114020340c20390719 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 820745953 1250 820744703 820744709
    0x504110c0c0f0a06110a1b090e0303010e04020d050c0a030809041b0806060f0c0706050c0601060206010620030c2d07290c010c050d110909010308090303091801 70
    0x14010740c0103101d61070030441081d40003800050070200f50b1600d016812a00b40c110040304401a010301c0102030080f03100b425842c40904140310004440c6454108503500311552607540100b00d42007030004024151020f004103a0240c5c0545e0100056089407400c01c0c2820920040325a1002e00c80c5408810b10100c1c01c013402d10500c06607420003481c041c207240c11854005030304507800020b01c0540051543c2c108080036052403800c9103070300c5040003410ba040e13034203180d1180c016100207840401c849041460170000030b40180302d5400a841554103040c00203180e02c501003a401190483c200c6c4c805040c2030308204417084002d021056400c0d201c0000c010000c41841c0c4520201c0c002c00440f81c65194030030124120089130103a0303035000104030601d030744849480c600c40946882c1c400b0a04c0740e0380c0604400c0c011064014200d9450711381d64411184540100c41d1300c504081c155840901080c8043c0e102c07580f406066036000004107481c2c3d4282c200003840c0d40305038a4029004010800c480d000800c4820040d070603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 820747203 1250 820745953 820745977
    0x110103021b0723060712120204050a0803070b180601140d0b070c020f041a040f110c0109120305061804261209060c0403120e040608030a030509010c1202030a0204050411 74
    0xa50f14001e403c1080c03038011000041d0040d9003a01500308890f00032845001c12806000d000b60074903994100003080e440c0320354403041c41c58000213541810041e40d600075545c0301c01240d4890a0a0441100070b5584110501400400c9443d05460407001e95030101c0306060694800700c00381713031464110002400d410340c84004034010941400640d0080c5828014510080c4107030303485424070f41004c010400500243c21041c4441d40e40d59040d48800813405005240300040d01d00086050340d5107250080d5641c0e00200044101498007040c0400d0b503130340300c908002c40200c01c0401105629141014011000300031040c0354140303c0d003d9841801d074800c0b00a8807030a146526800d806a44005030b0549411086403e0500407c00304070a00001c1c01040b5042860b00c007a281400c2e0301031540f000700b011580250020304903a40301041005400354140101341d800903840009004e10f80000501800300c0042c0d521060045402200040c0041030342d5041d40d0040c03400078414000c050901c0c1d90b00d54a0361040780300310f43d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 820748453 1250 820747203 820747259
    0x40609060f0912030b0310050408070209090a0b1b0405010c03111b0406090b060921030f0304020405092a040f0c05030601080c0f0a0f1e091d04110103021b07 69
    0x501c0e4042d2003003c400ca180640a007d0206081c0c4000008110090007114440018400b50015840c0c3d14440d9105103842c034014005840c0c103061032542100c00a103940103d030651150851a030023641c00ba10111903003803e185d00b00140900d802c0d5582d100c0d010f005651031140700315140d045041c2c0f4000800290003994100316164844081e18282e40d41c01c6080c98201404101d40c00c99814111400b00c003603065801580d07000050949101d0a590002400c5099501c000c401e20065190a20580d5041900c0000030640b10000c4111108200040d4000211044002c0501000c584890b000310341c0c0c1a481803810854010b09401c00341145e001960b00c0c90025182d80002041903410404648480c0031407000c850401e05455030072116010403101800c1000011006d00c400030034500d0f0b049400c02d00c103868078050700d400c10141c4032541c0d604030201b45100240d1014480401c4000d150212000c070300f131801581d110404114617040b40d40000383d0b409a4030a403e00040e040100f006820000000e00501030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 820749703 1250 820748453 820748483
    0x5090d110102030c040b360a06030902151b0a0f050d02122205091314011a0d033c053a091a0601050c07030308040609060f09 55
    0x908030f00003121506035220041106000080300c5102511102d022158143c081d1651001180d00d070b129080410b10401c0840a034219461600824480240c00e50b49400c0200c041c164000032203a00d02000c0d117451130a40020800c02611882c51a5110611000700f20b801e12904c519204910500111060720b417030040c3f2031380c95503680c40800c24035441d400c04d034003280c240101c1d000000d45440300b18144903440100e4040004441d101e0440052066040d002e04542000d06800c00b42c84142c603007016010540d15240c00c0010520803e1382400c408002174420103080c004500e000c0c1c4804100c2c140030341a2402c4440102403000b1140250f020040c000201d880c400000200700f61140d014184042490a407041210a40d045003000f84505a203d40700f0002e1802c0401e011100c1150340a604c25142210700700c0150b000d455117140322540007542841c1240c50305214149054031a08140001810041c4440205c0c0034003210303400440055030810320400c0440d0b4401c0c45400200816031044510020541c1c41c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 820750953 1250 820749703 820749737
    0x1f03140115030b011e1703090102010b010516060f09170309120a09060315030c0f0e0105090f010506070f080a110c01110c04090507090906150915030f1505090d 70
    0x541d049950100b60340070a0303420091100d070018030400034005251000c0c040055203061251800140202e180c0c040c642d030340c896900081c290340d00c0802c2c00c1c0c1480010031001d964050b010020034a016000403002821644061230b80d00a000001c1001d0140702c002c4905486100a840055005903c4d09003158288003008101540c0717805140c010710080b42010308104403a42c001d8000e910802c43e288030243c40c5035101d6030780001d06d030030603044050884c401100c14020074044095003409000c007107500c542d0034036120f40303560034251050044601583c808a060000c00a42852203c0340ba40d000300b00303c0d290540000e000780390300d0788003225424504c20018440007650043c19001007518441c1e0290403a041008144000b070045500c00700e0b8644140040004c0d5842c0314410791040e9407090002065485041074920040400e0b50000b0013000d2500c2c030383c82004210300414104880d4401c00d8101c202806003005180e060968a01c28240f90801d8104101c00e1310104440c4140825521403403881000300d008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 820752203 1250 820750953 820750991
    0x190e030a0b24030a080d0e0601030606090608070f09020a051b0c010f08040b1503151e010515070b040201050906131703130302060d150807050112180303051f031401 72
    0x20b0b4982540107600d00b100418085801481075196420b030220780101113128861070003409038015259039583c0c48040c04041e94a0060900a00c4040001e0041c10f0501d0010100292580708080317a655000a00c5a1500e0040f0140c0e500303041d903070011041e240000d000302034452031100901c03800a090721006140950003020510b0241e900100c2d400110f9444003100714050f1001c0980940c10b218440c030001070101041c40003440b80040d61504202100e1280b90724481c580180c01c0b1a00c5410120040055000d010066603402c030340024260845807242e00050741e0500c50b222017035400070b10001e4550b40815003082c0400c00c0703e95005201c1c0c160b0900317006603038481c064001a06a401402c0d0820409444c162000c0d100e03006030168000740c61064200410031075a0306a1103244107400c000d80400066810206e0006490003041003406207030b845080600d20600129401070515a5907030200d06960b954010cc0038034101c5440b841346c1c031140c41e820050304036645080c5080320340d82880251041c042e08500d17 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 820753453 1250 820752203 820752271
    0x180a0303091d04110f1201090809090c07052a0d05060403020c01090b04171905150702060c030f190f02040f1406030423011121010b190e030a0b 63
    0x401c40c080c0d6004d0341040000141c2da541c55510660030001c03010007040c00c0c461091083e1007060546d0f5a0308014050101035030000309002074414081c04100c000c15000714024400d4100780050350074165020690643c0c90f8049840c0035004104034140f0301c200074001404501581c025000c80c1c440c0c86245004503840e000c1805502d900e204144000c00c20301c0e5041000765500d000c0c142c1034800001e0402c50740c1c0e19401c1c4d02a800d86195109102c202200005c0004e0345400c06442d101605a601d001c443e043c85911000d003a504004203000c0000d107220707504440415009601d10f40920018144904140c069046801041082c94004900040200025801c07000710036015141604603070703d5844040f0b8056558040390070030b07408008640c548840a202d42210800d040031869260502c14854540903224009030b031802401d40c10061045242d02d8080d01d0b01d0a101241210310b01c082c1c25811540c2000008840c1d804d4443c072034500b001c10980780e403030300d11484990100d910001c40f411104581010641 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 820754703 1250 820753453 820753463
    0x9060305010f1512020301060506070606060f0c05031e070609081902011a040917070c091a03060612070306050f061f2a080c0c0f1002030f180a0303091d04 68
    0x307030100321104c3c2c000301604200740002e0000031030301d54800110745140d10528044494607a10304040c04155045446042c40c03910515041e85003000079921a5031b41e11507070050f05680c2c4003200d00d034501d0010781c804a9501661107071050240c03000c985010020350b0020b00c0c11140300b54a4101010107a80705201e40864208060040d0040000100c10b010040c44c500760252000442032046441e00c14510300188120341c805c90b80186e106e0f01c0c0998100c103c5040301d60007240071008109100560b0303800582580c0051080b956903001100048400e49041e046034002091241003e003040103000d6050042ca216020582d000141482c2740c24107802540c144042000c046441c011007482c02c80800048003030030507514024604222a00e45411603590840d140381103046e84920300b14103050600c94204940700c601034030a4818460f03414000303516802840705488c240307403001c900a440006590b01d03400c0002c0019150001d03040d140c1c1001000680680215403003c07080c12000034161803481080c52259400c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 820755953 1250 820754703 820754741
    0x60c06220b0f09010902150c011503050a060f0219020c03070602010e03040e1509041b080d090b03130c0f031704051e030f07090609050c09030a0b09011509060305010f 73
    0x41d0002c2c810b80341e0050030b140d645660710004600140c4400203101c4015030390303c01c0161904108a14035095522001c004100c9141d0b40c181040040ca002641c15810ba5001c036001c5008580748d94110005c1c041c42e121204130081d0014490695600410715040d500019804c1e11341a50300c030b0b2070036400c0e104146240e4030316034420001003004c0c4680b080c860350803400c07104242195060140c00950460410303602a9101d4880c0c01c1d4244094140300c0c0410001c2201c80003821800b00c107a14054100c0600703104400c44014000300045d15203282101c01d00e500355126800b01030040d2a0261306162810600045034450107040b008021a40b50100780c60032650b0007801c0c4403444100c0316031800107a691122480e010301c222441e1114209081c85403101030041500e00145440c600340d44241074a60140000d40d0090040150241c25100441c45010254100c418501c0036110b1080c010b0050000074041c0c003030590004008107450542c3e8001c8022240a040240005080e00c0e004008840c00d02c51803140842d00c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 820757203 1250 820755953 820755961
    0x1050406080912030a020a0f18120309030203060411280317120a0c1739031f0905091e1207080424121505060c06220b 52
    0x100d00c8560340c0c0300000000f660207103140d01c103c40f0290380050f41e00044564000c241c4810155000c1d01c901a10441454401c08002d058502e030281c405d481c2c014240300d5a0002700d560181801841d0b00f00045601804603401071806041c008544805480040d00c54000035054500c0f020000e80a21b030b240302000342e007034071040c0346680e0b4144049400a80e800705030814020100030b50709500c2040c0c0300309080715020906d82d80b4050002d000140138030a10403240c010105001c01860941301007010449a41c0001403445910880426248540507003804000000401c100740007550100d115044031400350444025600e40c1000416202c0440c1e084010340e0110f400851b40d500ca80b0780c2e448501100006840340c455241d40134010740d034041c0d00e00f91a09040020100b190940c1021040c10f44c0048054545420800d92001041080d08034034004815450300a1501c50007800144e6400130100100301c2a964043c00c1c42403511018103c031488003210130100002d125150100380c0c400b500780d01c00d002a40d82ea40b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 820758453 1250 820757203 820757207
    0x120e0d11090a0e010510030201020f010915020903010e0d090e060924120d0e1908030d02091f03091b080a03030e01060e010b0c06160e09070c230105130201050406 71
    0x780c000d01000d061034860b440e03020407240a01c80c05014402c80d444004006040d4000680f07019060b68a03151140e1600c41200049041c9000045a41200f60fa002d44d40e19042c000090241031480c00c2c1d140e25000303c01e114503815402014040032610400080300c2c4507a42c000400c41c54910031511018203011026840c9901e142c1007844044c40d0307400502079103204501c81c0c6100d1a1010300341340e18021072a0301c180000d55107464502d0726455000c07014518901d5040a1406440380078011071300300031a030040f0703000c1c4807645ca011079a10351607122402d001010714104001000390182900c01c2e034612035003020801003c06086901300580f0714000c018241581c05640c2140242101a6400f81c01d5684803000300d00c02502c921001e000300020030f0310780c0c1c40c2e00c160301400e414030b0406803c0c1840da03200c031888040100c0c1c10201c4038803201d00071100a6229074032103c054941c2100348400a000d502020504807c04d020b00c14489000411030000300300c181e96802c101ea1051403031020203070120f0340500040001074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 820759703 1250 820758453 820758469
    0x10b090c160b010909050f0a0c1502071a030411190b0c0f0307060c02101401170102090901080d0e0d0f0605070c05060403080106110d0f080601030b0607120e0d11 71
    0x522a5106941841e08a49440900b12000c0e007000704400c1d220410036043c03120070411294030300003000c080c15400d0b20079503803040c4c5000a80709020140c009007509903403844c028054100180144000c4800c0d6807c1e40075031070480c0c0e10884003162040880c8030844024207000200c9a80c0344c80030050b03940c0c041c0c24218014180d400c04550103400d4460207008845002050001c1c10455205460101c0c3c60305007400003a0400b90140e440010407031a05c5455005c11180000700c03411101c036005110100e5401c9a46680644a524030141d00b20b41036900000d00f200f8001502014040c042d60346124458020b0104004906020301c040c10300340d10746510030041021076100a81108190400c0013400c440ca558450505100716015004640941c004001041d0484800c030034030503001c0d0150001450461000e8102801182d0410801040400140159002e540b00044c0940c0041c1100c4c1c0b1001c99103880c6c4059041c0d201c01a0000d54008014101c9081100c081c01030968440e200103042c24603102800120 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 820760953 1250 820759703 820759717
    0xc020718020417030304020405010e0c0306010305060a030b150123071515060e030c1507060902121f060503070302060f031f080f120306061602030a0503030c04090e010b090c 76
    0x181e0308000000380c10314024030f8400c1000c8800c1c00b45445e032170980108003c5030016403000006080c4d4108110104c0c007000100c0750f0010090070300180507200c40d40811b141d583c55400007403184100c4401d219074116925080803881600f680c0380c500501e1807038080c401a0030782c0f42041c44010014880d140c0080c90880703460440d584202d00c0018940b0750101c501c0c90302026603002c0008501c0c0d06170b80000c0c0e0f007801d124080100c00180d400d03d980c075071156100761a41c032a2080281c0f0032503858102c50704560381c40e251030714071000c02003c60710303e0041100c200aa0440841441042070704e4940c0009182c01c0200f034450440360010300d850704101030388006220702c0d44000c052041d00264240e0b0200d100d031017901c000001d054004020001e400403000e14510b0700e81408080480b00703a0a00070892141d80e040115042c96401c40500c10050b522440842c0c0b0704501410010074600000c000c0248015151018004448003400148148c5505e094000e080f1003480c0c503d950070800e540c0000e031203070881400401c40c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 820762203 1250 820760953 820760999
    0x9020a120e030414221e0605030304050a0612110a0e03070824091614040b0405010e13020a050324070f050a0302032502070501120b06030106030e03070609060c080a0c0207 75
    0x4a0450a90320406c90300d01000d0b038408084c02d04040b400b142ca981c49440060102a4021890a0706200018020790f00511600b800c00071007410142000d902a0048465400c1d851601030300c4800c400c07405016075a0401c0d809000b4410b40c640002d81c14400a10f9031985410200541d00035413040d19840c0203002c005000f01207e118071076403d5010aa038000070401802d402459503030019502e8200000e89440710310381d034850780c01c04005000760a41c03041e406401c0840c51010991100091000c80c2070781c14960300c01c642c0b6009000d082412000305e40d4402645814001104500e41d845110a03500c00400e03a03480e03000100c0c18080c1340300043c060b80c01503800c41e1704411120705403802d014030720300400b01e0b0400d00001030b08074140410039540c00c002070307010049004206208080f01440810044d00051144400305a154a00300d00b124900707104565171190442020310410555007000000345c03ca503440c0200041a90b00000c8000e50345225100351040700350301400700e961400e610620740c06244901860 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 820763453 1250 820762203 820762249
    0x10b070f050f12030103021e0102120d0e0303100815070c020d030e0904050706110c0f0d0c0b0c0a030e0f030d03050601021218092a1309020a120e030414 67
    0x103910b1000300070b038080e2418151001035985d0b0441c41442401c6072441c2d12680c24200050364101107a0300855942d02c1308481248103a05c0b00100e00503100541124181d0710101d0200100740000b000e075400d0350006030b4a0700c0084840f041030300183d50013511422210000061140d41e000001480c1a018251a00d0f004e0b240101820203040c001a10241040c1c60849459103c40360412000c0d0300320301d040c01803a84800290201c0c0c0003840c003081d803200c1d00d105040c0c400c500c02c080030010400340030f54010140582501c0349403905690138080e652400c0161058022804000c2c48524914060145402c80c800c050040e1003203042d5805c054001e4800941454150700449151040c1442c040d0060004c1c0424069119110702c0081c0c01c0c005000d501074191620344160075822011411840c210001c00401d00000c180c0e00c8448401d41000c41c078094202424007400040c0740b6140a5101450640721011100304011000500b038106540380f00300d1190000480e004078041d0114600305004000080271009082 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 820764703 1250 820763453 820763473
    0xa0b0a09060621150b070c1a270a1203030e0f01150e01031a070216030605040302010f0621020d2315090303160c020a08031e03010b070f05 61
    0x5410365200d0742241e40010f8021140c0b184000000d81121540070300d802040103080340511102551070000c0c013a000322a03030006250030030000019080002444125240c07400c502441c1c4a00007650703c01c3c8249032440c8203800c41d014421702c00c2a145a421329000b402518158903286d00d05410742a10720040d000d0540d101c0c00d14510440c240304c40b40182c924600002000f0380580e41004e0780c0700c400c0e001440034000740c000500000e4000000316450611880340f2a129a4850070204d20704481c00d903102c5038298903a00e001041100315000903000b01d109400900c00e40d51841010021104075200350444908000d003060611849032204490090000e02811070361074098884005120501d2000307001c01e6202048015095018050301c030300c4888802d04102036051a0207075966a00000d48551700351440300e2001e090303260080060b107480d151701510ba041c18a55038000c15880741c00c00490301c07082d81140a04081e2890071441264140c52050440b0760902406888044542590200880340e5110b480580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 820765953 1250 820764703 820764719
    0x21005072001020d110d0c02010b030a0318080706081e070c060c02160803030a050f040803011e150201050a0608010e071e031a06011b123009021203040302090a0b0a 72
    0xc0c030401828015095642e42e05110381002c0300c0e40c4c0b122203c00c43e490510504068be50101d02c2500d420703054a403c00a03100c220348001d1042c001581320141c28401d00c1000a0329582004c4110f01c60f07004440914005809113010407550a02102c90400203031810b081c4c400050803a0713100c800c0e10311980c811642c41c480c000540c030310f840d507068004110f1075201004001041c80340340640340c0d01c02c0c98a0304c02d04807810f10766034543c0b45002c1801012400c030066214101c84642e410803010007045e41b603d03113002100034184042d000700002d5400740705031801c1490205840c4814000e2100e6603041c14010300541c0d01c0c040c820707022002c42c03070080001800440000000705103c1c154802c0034108110711441709050044c00900001b4050b142c4511740810026082c01141115882c1248203510f4142048040183c0e21454003814114142c00c5800002c41d00c0840c50301103d0f8000744400c1d01c04d903044110024803030360789581c0f4022440001d60201c010310010f411901c440c0c110f840d02030f5002d0700749000c03d52940d81c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 820767203 1250 820765953 820765961
    0xf200307030c060e0c060717250c060203090a06140c121918150210020d0b0a0e010f15030e030403032c01050d0b0a03140d021005072001020d 62
    0x10a0380042c6080410310188020707403103030507004c40000d0020081e46081201040342405811409010020340c0182040003484010448003800349400510a6504010301541e00b5802c00d841d060741c007000341c8140840d2050001003140d14007440107100d8624075140520440e201145008000203040081c0468542103004001164580400c018482d40b038009052510602a0910301c540c0d08100c8007a41500048011080610a80d01140140e00140002d510705920b002c503050700054505100007980100410744d40c0c8441d8800008075451010190380b400d034101100c0703080c020703550784d1a807014007009990b0400001c07603d4610b00d0705011515803040504607080d50000e84c402e9020410060308240781d0b014000c41050315072031046101440540e0000020003e0040d00707000110b49990f140d48800aa032200d850b140159488402e0740305d038140300060303c1d0f00d50184bd84038030003500c508000e1400805542c056184100e1040e03944c05c09980ca2020b00c0c041e41e0f00792400090b42950700b0081e065900d006401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 820768453 1250 820767203 820767217
    0xa020c0106050907092909040b0613091506030e0c09130c0303030f050106050c0624120c10020607140a030603060525050a050405150f0304151b0f2003 66
    0x1902030119240c1912601e808070001b040451004480070100300044481d41a00c6000f5400c0d24000f54404294020507607500c5a0071200c04003510400c40001c0c1d007070054010458002e0260180501980c0e5514154262184040c92540d41e0300010001d0b40706080c09110b5a6102d24800fa001400c1030759916801c0a0031460342065000a4840c041c54a2442c10350050303030300502441c0b074546d00e04145500820b48810020b418050240411064050713812610b07201c444d0507020003450701c0c2c3d8045440e02c1c15a40c40d004144150702600c9103103c102c8040b4000b080c1c3d10700c20711880c0c81d0400d41580440b49590654010ba1707014042c5a03852a0220115040b0700c00c440c46483c601c20304600030010b5003030720904c00105412800412400700102d48610f179005007624210787d0241d9202c01c0c14075445507401160301952000c5803030714902104010900c0006107920318603600203e03003000042c59080c040001500c83d03250b14004640001070183c10345100d24403070300071400f6035010080080c40d04250b043c11540211 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 820769703 1250 820768453 820768457
    0x70507120c0503070b0c0d0e0f0a0e010f0b030606041503020f041401090b040f0b03091e07030308060316060e0d0501060b070b0a181e060528060e0a020c0106050907 72
    0x906110b00e0404010900207800d0201d00c207810468566100c66075611181c40716001c0080c0b0311031000540c1c071210b50b020781c01100105030161280d10b500c01d42c40c034078109107d0300400040380c1714002140050401100c2c000c2201405840c50542801c54446040c20740c07d4030882050740c2000355400d0000d54030b0151002d00030300100000d40003618400109012003c1d00115041e990421007000300c0b80b854002c4404554009120315100d90702c0d503e0050400310450314015000c0c0301e86109509610003c00c011058900c20b4075002c4450b10381c40c0502d903075404580d403400070100c503a2809010071802618000c2c0c2c0c04500401601030f000d0b56980e1a825a21280c0c4000080079000c03403003008020300241c90b41c1c3e01c00c8041108000e0385c0d48418034038042c1194048040c0c07401c3d045507013520400201c82d10b80807640d600700009210b5818a82004020301d1030084c00e0f201070f100340e0006814213014901400301160320750380f000c3c0c4044c1c4a2040c128029401040c090140d590f907050001559200c1c0e51141c2d11820b065 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 820770953 1250 820769703 820769723
    0x3040803090f1605010315080105010e190225021c080a1b0209010b0a02070b030c03041101080721021c150509041707030e1f020f1f0207050712 63
    0x540803103460001078010008054004100711a0903e0000c00c007503040b54001d180100c0c81400e1014008482c0c0402e0308141400d50a0000104020300011040350164400504107100c030452a140c8000308c4c003e640318a00c0088980740c2088031303500c4580300040d802d400141a604408102c420403413521000b804204da54000219141110a81141c0305800d604400d4200004808040d130020307207000c9e03050040c814526400308580050074400c02440d8013034840d0322100da03600c2c1031102d02c91312941c1003100c046817200595140843c0d60351244068070b000b0341d603a84441c3e003c1c1d4811820300401c41c048003002d4640070750900801041501d25000010031103921003001031880c00d502c0c50040c801c01207800c0140142c6202c414040040d0b01c40082c400d1000000454030b466440c2890102c8002c2d03482c1644962101c405035504000c0700c00c03000d58090060541d022a10000c103040b2000f81c840e001589603650003412507059000d0300b809500240030052151f8190740741035442d002d200b1403401d0003d01c1500d8240c28 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 820772203 1250 820770953 820770961
    0x730060b01030b0f06042108070b0f060103020708030a0b060f1219090209240d0516060f02070302060903010e0105070816031a060d1407030c031503111903020603040803 74
    0x5403203140c00c05201a10420045204034010608a00c500d01c61101ea5a21f600700340c10207415508045500c142c0e100d2031207030382d4000c1410702c20b40c1c610003500d48045482e0060041807442d8028400c90300a558018442d0b1b0440c2d85130740070500109040324030160040c41c204036054040d2000d1004000c04010201a18420705003a68102d00300009a8041c4c484540381030712000240e035030b02c0c81c1594004100103000700c01c0407101d4028500480304180700383e000140300307a0820400030701107a10b1026401522004003840c1d5519000c0b00c201c9092105400944c210842c18805814120010030407100c0207000800e031a000b1848039400c59404985e02c1002421080522062440d4500030359480312562400f031011000703500c8800710554400090911401d000554803d00d00c207203400586c2c21a80c91800071100386020308000d8083c0c00a00400f00c0002c1c9040b00740081c0c071402c80050070940340c121900c00c3e0000c1c400420700c2001140300d01c00810a03180700200100680d200801580304d503110303008254507810 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 820773453 1250 820772203 820772207
    0xc0c080f030a030e0d2a0804060e030105070315051216090203010305070603020a02100203060315010603020d0e1b041113030309061b020d081b030708120906090730060b01 75
    0x20405100c28007942254140522459001c4032555200401102c10910086e02d4028150b064110700d00040c403024022800184958010414280780c0400307038000d201c035503107501c400c80403a000d00c4440c5c2c51585400c4403c0c012420142c0c0401040b1401404452041da000181012402c00560088500f10740000040c8204032081c171008004102500301503040624100740030752261403803000fa001e050350100015459680030844045400060088202d4550b100d04004020354400d4040c101078500f8048040c0c824070000410301491302c030250404c480da0a5602c10000617000740084004000c8090103480d2190081000b2000114031075101c4058152500c80040d1034a05030846840a04840520100150300c0302c84058048540c03000c2c645030741d0306118034482d0803484007401e024428400896000c0400814074000c0003241c403008a1a40140d6806400f151f40c2c0d0401c0701c0108003600046001c220010100420303e004445050000c03034480e00514400c503180c0a102d500b500c071540c0b90003540c1c2c5103503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 820774703 1250 820773453 820773461
    0x8090c130506190b03010506091309060b0a1a0f0c0102070b1524071412040b1e04150f021c0302070c0801050702030a0e061e0705011a0a060c0c080f030a03 68
    0x100f00d504850480c54104601a00c0c00305206480c020a00090519080c0e038075041d060607100000801001805220704040f001850000942c2d4041d0083c16008124002140a8400405ca66030344492814007400b882c0c110513000101c03500b4241d902030049034002108541c4c918401d000002000b41b070106034900b00315040e41c0180707050340202515998132a900d0700d030204071132807590000c0c1e951440318894041309151240c42140d04050f18404074001c5800301c0035400900103012011100d00e1429480405440144264822100c05194050710f03140080d0007804011810300442c01501c41c48150b5030a82641c603000c5c6608940029800103078841009841c488040180414100070041403420140182d901c0c4594440442071028141d04d40c203007551400212a040b0701030306c1c40401c58103414428007003190001c407000c403015406d113018001440400c0c00203a107a800d0040c11000340700c0c901101901c0f04a448030081e10800280d50f00803407198000c02199a0390041c07540110340c0c40810382001400c803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 820775953 1250 820774703 820774729
    0x10030f060b0c0f060c031006180e0c09040b040c0f080a06030611030601020d03090c262b1b1104020702033708030a05280f05010b03040b0708090c130506 67
    0x103201f80070503c80302d440c016086c0e400381e04007101500d04602054140c8030540d4040c01c0c41440d000b08202d290240200076003601d40f010f840c148038005070710742080280c485158040e0001035500d4003452060b0f100e07032000b503003084800c540014a41c0e2a42c450f0410743c0c2c0700341c0302a82c035442d001091190950f8100040711007111176160170041c154890381c0e00800b80c00c06100c1c404200c02030000440c060800d4030302c0c07000c0c00c02e413980446044020034074010581c4200d000219114000080c140c0d215240104040389c1d80103100041070614003010780c1c4654207464004151900942e092040c0d00040c0c504000c10202da803c030ac0c410b01301d00000315140503110550075103109446100c0d5160301000031085825203410580014001c656070f500e410001c11040070034480021903002003000f045981c100d41c1e012018218a0038010301103a03032a101007651502c0192402030034580744130000b6000c00d110b007420030b8210382810151502026440d0010760b4a05500c01081c22540e40da80c240411454002800346507 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 820777203 1250 820775953 820775971
    0xc1e020d090e0610030507110f0d0915050a0c29060f06071a22060603031403010b120408041703190c0302071502120409050a0b030c10030f060b0c0f06 66
    0x498600180415000c1e826104e650003490303254808100103602605100c181030340d107581110389041c002c40109540790ba4400c560000300d001c540c40800e5100d640c11002440c49115121b40780f0385014140e007210f1a40441c602600c008805080410080c041c1d040e038104e00071099000c0d400b003804d01c0410480c11480742642e8034802c40342041260001000d085216650014130310846a0581c1c4450014090500d441c2010008848188030300d01044115409801a00c0c0a0743e1140d0400480260481c2c85201c2800b030134400c1c02040c002c20324004903500c8a5a0304c94410b44450b4101980e400e05411904002c0c050b190b10794101040054582c2082d450130b901c84100c5140065000d0202c0d200651515454007401c0d076100c00580710b404800b4020005110213095628400340d499a403101c101d0010300f4203032944140d65003860101e00305482d000880031146007000b809203604c1050080d0a4008080d034841201d44a901c6039000070720038881001405155160b00060038007440406410341c20a0002000713118 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 820778453 1250 820777203 820777229
    0x1060b0c0309040c23130f030305030702010b1905060a030608100e010e0c0f060d061a03010914071e140c0303040b180d11010e0106090c020d02030c100c1e020d09 71
    0x48a2651991214400c0c0c141c45e0b241a40c0e07a1040c2842c4080200b01c4c0c02c80140c1c503410f198000201a4020019803241700321b5070081100d0b031000e80802c0583d8090b00044440442032500034056032401e540107248100307281c2800240950713540c24050603d42109500c00c5015503548042101c60428068880050b40010107010340400050005003146941001e07580100740104042603202c100d540042e018105003c481c400d0050244440c034480e500c02d000320542c50303003030900da108148032011074140a1403003902c50303024101c103984510b0328592040102074104814401400a1019034800403c00950160051680d0740b40030705002c4c1000300042c004000000c1c0000080b40d0955021400000c420844e11788000c40c00076503103410f4090907074880c1001c001d518000001a00c91101e52024040070429020780e03101411810741641c0328002e8100414541d044044203040c4c00d881d41d40b0031040b454480c00d1409018003a0703204010900180c0300d4680c00f41e80000354800e0041c2d04601c61500a15043c16026 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 820779703 1250 820778453 820778477
    0x603010e0607021f0b0d170403080f1306080912090f090c120606030c0702130906050a0b01020d1d0f060403170c06130203030706050615072001092601060b0c0309040c 73
    0x90540916991b003d070a4443d00c0d48540c0c119034160040f60b00458110400310740368044400e4260480d803201506180c554922500000c0c15070041034110b104083d0380014100301c540680500e00703154030141840d5030204103010b0300100341d0384a41c0c8190080c415440400d88030303007220b88603000c4400d01804403842880140b04010b01c41009000710352000d941550f49001401c3c0780000c91300507003418140105144c0c204001c00071642e007503a101c26a54103003642147c80c80080400195880704a141804880c20540071a080450405006c4400442c10182c40070749420741d039403941e400146007800320a2400307070000340d2041c01e500304000082c0c01603d002543c550042017940003035a00e00c01c0314402040103442d48001002a0b03074014000c1d00c0485c041d5107030380d40c0c4d026070318010b071604a2580c00e030f581d40011a1120100340d446225080155501003040c02d240c51030044601c1c64210020b0515121592101c20100c0c1d60341181c0050042e0440340c600454a070801e000c104800c2e150103030151400c0080c4a2102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 820780953 1250 820779703 820779709
    0x2030303130519030f090506090a0e040c0302090705070c060824030a1202070503071205030301050d110a0f06120510090c030204050604080312010f0807030602030603010e0607021f0b 80
    0x32a00948640308005008070145407003410282c901d0159245451582402c070103054000c240d821844800341e650907009501c0c1c000b0407481d40070351451240c00c1030100720184412812415000e801c940600c0c00c0700007465683d8001500040b0843c0d81c900001ca0200340c14080018010040014140c5410146014904034507101c503200c00000301c100a44040100c00007840d1018443c010402d90032407800c280b04d1040c240060364a00040c81014080d10440e071000514880207040100c0842d4040c02540c50341c0d10b000104051101003500c02d59040c90059904245a80c64880d940002d02e5080c91921303004d4541800900b0301c0130010008600541000c040001c1e0104a45211050300c0c50fa00c40007690100750b9804400a000e9504219080040004e0100c1e03002030010103040032050345030320012140c0e00e42c401c0159000c100d00c2103003050740c400503040c00090180d40107907a03c818003a00028042e08050101850080142d9280c2c0c05a00a00c82030a500c074403844990010721050700c3c1c1804199110404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 820782203 1250 820780953 820780957
    0x2f12030613020d1b0504170309030d050703021609200726070602032406120109090303020c0307031101051303020c060d020408100c09090513022101022a0109020303 72
    0x8100d940c1c607400940000008055885804410391400c0c43c10102094441e01408a60090065580c001205407400c03172034101c00400c031a15108041c000d02030003d034484043d162604400c20881c103501414010b46071501481c0c58210080005a50126900c03848200c49550740c1a2101143c0000344208803e80202d10070f00e00500044d41c3da070706c0241c0001e1030114120b241d0701500c000182054000000d1024031340344140c0844100001c0f100241c0a01400020410948162040340e070a030210200100301d16209584002c03615030190a02500d0046800342c1c1c607085500140c2c041f03000c42d90100404240c102d00b485190351044580035105500429510041d50320100702070528032814000480c80d180c020320342c050b603000b0521242201c510903051405600a041c1842115002035020034000401c24a5130254500803e003207002610610801e409001d503054444066600074210301814041080c1c003480100300725021b0308003800b1414224060f01240b100c038001208070503070410107880003517031340881 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 820783453 1250 820782203 820782229
    0x8032212081024030e0d0504050a05311805010c1202131214060f15010212091c0c08101506050f0c0f060c040810050709090c2f120306 59
    0x4501c1e0441d82c0c401c4412005130080c5074440fa000e00a01030101860747e007207405002a24000c8803500450fa403101c0600280c509040e100300d581002e956080c00a01c1810110039440020481c0d000c03907510010780351800301004007a0100c51680d5a890300314001c540c448400001c40e10898400e516201d001c46100011540900911410480044e01e540c208401114120444050441030342c0032807418455109640d101181c442c04508400312401c0c01540c40815488010b60924400c02e09001e02d000074042020310b8000d40500100f00d558040b070200c0d510031007000050071090002c01a14041c1d84911040d10141c1458143d00d14071b10b002400610f4101e029680c40d201c90340b84282e154200c00c2502446e02c078105080c00114007600c402c1c81a02d010100090050707507241821504003144113180da404407032049880301c000561200c410301000e45141c101c141006101d203001c4403140c0d5100b0401000d00079241903c40c980140c0d05401150a801344150014045500e00c030703904524207400400c4598881c81 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 820784703 1250 820783453 820783499
    0x708160e121e0109030f1404030314090d050115091104142103040e090309030703031803153617120f062b080322120810 53
    0x9240300380c00c01042000101c0708a690b050304982c00000d0451600900d01c8001c02d0340001e00da041402d20a42c021002030f0100b0725610510384c601417031914104c440b07080340d21410401c0c40080040201c1c5640d07070f0310041142401207000180e000040b0b00400c0c1c180807640d000c1d003105030416141080e107000d03400c06c0e1021503d00c200041c130038400f600005150b502c2408c805c0c0b01003000014040c00004000030240095454560700d41899480e035850541d82c03030181403019545a840503c041c00000d114903c1501004072084140100329101e54030b600b6010107082501c9a484d59403000785030100b1020111460209440e80c0f008035007010043d071800e030001c1c401809001040c8544032024a00300f4401120003120300c190001c06181444001c042200c8402e603040c0384120401c0d002484500d1900740c01c440010100804003112007000d603519443c2d0b0704010517012161401d946801d401040428515108074800c404640c0c070b1640440c00a0881103020300040303150b82ca020b40c140300b40e0140c6156841c4010307a031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 820785953 1250 820784703 820784719
    0x604110c03391c02121809010b1207031109030114091002251104060b030f0c0a050702041e050f0912090a17070f0b0903100e0d08090114040b0708160e 66
    0x21401a45031080d17480e9003410204001402144044030980301d0307001100111402c02407640d86071041c5403030340513440c51102c96509610210f41003134000c5d8410f1120115001000c1d04219881c40001d0071200300f04459800c0c0c02c3e41504002c0d0825040c00400406440c4400c11070600c1c81409a108110500c04a00c1000d40c0c0b58032910030600481c0310b072002680c80014010f0116a0f01c4503140034a0350004e442c000005020a0086000e0004c00b60030349020b0189031390340300d0409403035800300005002c9400c644000884015050880c051080c002c00d1b105400501d88426141440000c1510b003040e45511141e100741d0034005055590750340c2c000001242e101102d807041454807a07004606200750780d07100102c1424401e40000340007800030041c000c400c400f00d0540d417800400c0750700c4a0940c3d00c6c40040e020690010300703a940081e4050381480e074102e000d880000a010344012041101e0034820350b0180c4110080304104030341f955002c600c0961100030100880300090728540048c04404503004160301c1000300d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 820787203 1250 820785953 820786003
    0x150913060501092a0e19090504060c0305101a0912060108060f1006090b090619110106090e03040915030605150405130c051201020d060314060c120604110c0339 70
    0x40c1b4509030007e0070071000c1c1002107040c0b5203016001445c1d041c040c403002c01d062400249019900110400c11100f40c85141d10304200007180c00302c0d0395880200d0241d401048940600504002007100e24081c0410100400c0741c0d003413407450100e040b2001885401440d6808400b8003440d544442c00c041168201d00c00d06803140c80800000e000fa0044a0b2030701c070440c000c00e880c01942584002d070f85c4010ba86800003006582d84511103801600c030074940380340700c0c1d920800c81003103040c0a43e4007658500034505501c0841903100e50b0341c00107903401602d200081d90494400c20110b460306108242d001000303003004403882c200070f0b6a400303043c4072148941449400000c0c21104158020b404403440c040e90304c2400c0000070745a00e4840210181d440c8410760511820380012241c07502602205c490060305c2102014560302d00c3c0801000e4405400a140b008406000705048018108050a03504241c414034401c0315015122248414040b403036000d4010010401205900c100440c1c02c1200c2c2e0084d40c05100c141135 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 820788453 1250 820787203 820787239
    0x506061c02090406090204180c0914011404091b061407050a031d150705010509030c030f070c0302090109141506070305091c2603150913060501092a0e 66
    0x88001ba401c5401c05250340704c074013003442001402510801c0340d4190543c4580e02c210845058001300a25108000014420115104030031071170390358020004100c01c4001e42d00d807040b2040c0450302c00e20390341c49401c0510466422644d1448140c118803441c606201c41d80d118569210482c9802030240200318103100301e03000051040f40081c0ca406025001111102e900c0d108855004100a4402d54603001c04a0385504021084a8407203292000450400d40018503c85407035004400840d000c5200c08400001a202c50b18202d000345000319000400160a44412400c400e008000010000000071b070050700c2e035241c50076681207c1d0185030054132401c902d07002c10040b80e1200240012024a000c95a080203200390360341c0d24140c14482c850400d59506500c103407042c0000c5e030750f200b11182000712015982c100034000ca07900040359011302800200d1521518101d440c203800c590740190702c0768002070702442c01c1d4502c1d551509190104031a0040c5288004000f4002000c03040c2c424044004da01c40450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 820789703 1250 820788453 820788461
    0x60f090b221d01230604050403081602030409050c040305010f0b09071b02030a050c0a080706050702130b090405031b12090f01110105090102130e1017030f070f0506061c02090406 78
    0x10000c4000704280b0089101090407401d50a46207860340d4401000944030f8140f1f03014040c0110340c1034440da040c580303400076020302c0d104020200718210302c41408009100c250a02500d40901301c90307800070355602c3c01c5062036400d44054000c18180d103404c02010205a48503128030316400300161828510302416007601c140011030002c1c001e90301d4400c8840010a104012a6030f01000e0000c480e00c9586542d55103541e9101d07a0188078203c04500d0a00c8a0400b40c10041d203114a0300508000000741c13503680c400000e0081002b9a4181c43c01e50001c1200c0301081804244042c802c5003000007420780c001c1030840c440341403003200f101c00e010311762000420a20303034010703903104004200050080c080d03450288007860003504101100901d1092003a00010045000000d0380e0094001241c0c07000000e060142008030762061070107020b440d00c010080401c105114002820030984944441c3d40b0010090030824589180503280034401c2d4103484044103210000850001c0c6964141d51038551582d450425200038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 820790953 1250 820789703 820789751
    0xb030603030702040908030a05011a160606051903141605130e030708251a040507080d0908060916032a080f1e0a0f0c030204060f090b22 60
    0x40703424200305c901085480800342d88282042c100401c8107070303a503c0c800400f0361107601d02210b403180d04010402081a102a06640c198042c1001296003940c92001c42d041720f94107042084081d00c131400510411048040500d0884840300060040703c1c040c4046000240c0a841441e106040c0403d01681c06501d5400c0480f05241d01026641c0307a08090408002039031100514803849002800000c2103680e41c0c414100303083d6040103020028401c80440d0880c0c481d80900207032090b00c0b42a40001e0580000c021074804030701503a450351103080ca40360000d46020005012a581038124400364410320790303201850070850b9042416501000c40321081030301d40ea001c00c06908151408140003203401079000a20102c5107400301d0440340049070181c45a03608080410120368240c0046601901141c1c41c6031480a00c14000c0d40baa0b002c0301d40c2ca13400a0111040e990045c00791001005003006401d15900c281c84000c1d400f40c072501001400c0200703202418291410442005a90760302c85101051448506090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 820792203 1250 820790953 820790959
    0xd06090c0e0703060f1805040f05070b090405060f03030a050a09052706010306060e040c02190b070906090e010b0c0115140f01032c1203010303200a0c0b030603030702 73
    0x6038075035440381800709003110020003082c140300000411a01501c1c0311030031170342d10b07068460942059560f2000038140c094420385174500d1000e0890040344090110b08024165481403907036403035101051205071000101114403901c032400610400c2c2e1400702c21602003c000d840c000b55104603a01c015074440c2c2c0346802c20b0b03800032600d60303101314071180010080000218000c1c41c00001c0da0b4880c011400c0d1040c1c1d0207100000703405503031000e0301c03401e0940081e40124018015551342008080c4003842c4540c3c454415540240c0000610412a82200603a00640340d10725041c580c41d410f00c00b80d0b0820341c00c10310810450a50000b1245500c8400798003042211242007043d40c01c003070307441c4501000003041c00c0c6000e2040391b05a0400b56a0342c0a84901c500c85944030041c08100035050341c2403da000040c800c0c852081c001d001c4100c84e010666801580a0742c4640c445000c18901200c00c0071089807100c502c1200c0343d21584c000b00215850702440340890343c491504036036a50368000440e045018982c03000350 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 820793453 1250 820792203 820792223
    0x612021521010302041d0d03020a05070b040c210f031808030c0601090b0a0302010215040204201e271528090609030f0c03020a121407080c0d0609 64
    0x200307004508a19048074000ca03000d110781c040d0380d956150725800a0803011b0903940040e0200202c00e01940161a4600307080c00d1550400074161980c00e80351070100c0b021145103e5080050060708407140c00141810b20010b10b1840700f40e8a9074034100124000007028081c0314085200340729203405003005002400000041e03940350010225125500d45082c01003c1c0541e0802941e4046410100540c4040f20380590090160828020010400047c0a88183d0b009034503000460300c08030141d81d1104000580d481c1a913a40c40d260708000a28080c4c0c0300c4508401c08040140032600314147c0c412000710034443d00035507146140c0c6400590b1518150300ba020fa041c60100319081e000e019001e51064181c0041154026800101000c903411300d0640500c2c008070b48901018008a91203822001881d4400c09400c1e840e00d403244c001544d20b02e043d0b07011145008088030900c00704032102e190822204c8100004141d068200145191140c000008050080b6540d50740f403014080960444155150400c02c40780f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 820794703 1250 820793453 820793497
    0x901050a0e0a18090c0611150a0b100c050105060a14091806090c04051807150e0d060e10140703110f16051203041203022b06060e0406120215 62
    0x34000c1c1200d040203440300040800d0006e00e443c0501a040d040c5400d51024059a100d812070329001108083c01d06044150340d20102c543d039880e10400b13020850b200b91184020f4180d68a0054207403032008111030b0044404000c204001030001d19100d8403a64210307084184c41e03a408480e922803100c5602181601c2c0300758420700020100100d0100d4891500b40c1e4180b1599a440c1c6840c00308002c0c00312514295841104c0822003486a0138090302d2195091800a165010580c0006c2d4207198940d002d0302c0d01e542d20b070001130b00703d902081114403030701003044140642038680f64220304510004149105160707d803a44c0448450f030b803c4c111901c100104200549480754410b0300a1103190482088600c0d1140591403001c1800290640307201d10360050f440c0c2180c40b4210303403c40207504003087d0a240c000a140281e0451a40d02d0060702d2102c05220300000c480d071518900030035000701d0425213401245025800c1c000001c81040040000e50159011640107482c90914400391185074156101e60944000d54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 820795953 1250 820794703 820794749
    0x50610301a0705040f14030c060c070b121008010504050d1209020904060b010e031216020a170120070c23090901050106020624010e01020f030408030c0d050901050a0e0a 74
    0x2500036a85c031124030304405a00c5290904000161401440e030591003003105480c2032a04800520080800e87c1c2910f642aa4400c450b12a80d007006015607400c41e084002c0280409c2e840d10910010200b41000340010304050312255260140d40ca42202002080391b41c9100400503908440d034190390141c042c1d08185410304081009140e0b0072140ca000940019617050603140015140c001c05981c00042880c202c182e448003803440b21300700301c100d03000b0043c04000221020580d5200f01c1052942e000400d0380c003c1d40007017014003005a200c5140c030038002d11070345012a405012441c00e4405050750008070655551800d100c122043c0b5050303a000040c101000241181900150b04031025502262603645400118601c04501d001d00d00c0c84460f09a403040d00c5641c030590341d9921031030060050303c0c24843d140c1c100b03030306541c802c0c1c01071005e5500010f07220804200030000c040c1c401101c1d1608908003145980003c1c2188642e4000720100b0903a070003400456907600d0091801840d01e100c0c0d41d4000380c1c010f541 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 820797203 1250 820795953 820795957
    0x140c1614070b27061b07090207080304020a0609060f0503131e2009040201030f0902030f0c0307050619050304060f050a0c12050402030d1119050610301a0705 69
    0x38010a035680c590f1882e1121800548100740035100070240c0341013008618890000042d206030001c0c01c1c3c801d2010006644c3e00901c010248140140e05155891402e4014824002d4407540400c04110b2a54020004141d000c003841442541503c0e1180d5a612052600341d060010600041c1c2150030f2081d5810300c1d10b1420440d80695841222b401c81050300e040d80d8031002001c00e05455030030030035103c00500158426405088405062540003d001141e40c011900c0c10400310703040316065020610b0500e044c42c2c200302450041c201242c2503480d084081026000007150301007480f007030103004808541000403c2e00032040038030080204010310700d003a0600c00041c0c14100314100104e09140c800b14051a46401290322458003d0000c0100032103400341116501c2e101c4420350710031b0145840d03c04514024045a44002d13020b03800a1042e41018000600000d10a6000105145220380020340b0010403281603807407000004080181c481240c00c0002e00100144008020501c1d018200000142c00c200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 820798453 1250 820797203 820797217
    0xf21070303021618020d1404150b060c0a0204050907030602120f060f010903030f0512010b03010501020115031e020d0516090e122a070602010e01140c1614070b 70
    0x20840c0d1120f548000400c42d0807400f8064000c90450942511014920a4004203c041141080050a280e612408010040f8280d6003211110b0302066406509180c1c0d0203100900907084641c81d2920704030400e1541d5410214400902131070725000020204801800681d000f590042c805568800c418030100f8000d005c1165203000d89a20080400d1060808411003030007850b06031504081903007151810350352460400a0941045002c00181007440100310000307000b840400409510380d418000064255480c4100245038070035150810004198070188514079142d002e0109054203172140081829002c0c0005d000c0d00e9845869503a05422a60104060032240c40030700400c2102424448d194a8400d04500c1e544241010b01000e0a14402003034504038001111a4181184000e00c01d11403d001071680618050713503544440700c82d8034000380542d608030f61600f04204200d1620808502250241400306015504c0b00031440003001321241c040748441c0d42c80c008480c89030341d88210500b102da02c424 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 820799703 1250 820798453 820798457
    0xf050907030902150702010810050306280f0608011d120d090c0e090c0405072a0507030b07140301060503040813051c061d061306020f121608060306060f21070303 71
    0x107000100027807840c00400f0280c0c0c2c0010b01901d49515020b52016440c007902e5081695010b003901103101002e07040c401c509a81000f080d01156251a2014803400c5840c41d14414407401419101042d0010021034400c0700034048102085d114643c42c000103004002091b00100710901071040804e10031156414244201340c4030b4100c48a40303400303a00744004d440059403102c0115403007003d440c002d14108060102c030406028802d00903180240c4a09141020903801a071301d0240078414000c0103a4448010703600c082c00d1401c114555494400001c1841c40000e1002d0b04107940450b104022154035044040200b80041c00325188510051408801009001301224003504d4442124000340b10080302541c0d102c400f40c0903164660b50304150b0400c10f441c1c2030341203400315806c0040c1408983c102c00500020290030f40740c1d560620780441455550304400c40c9501c240300c0f01900b048856680010415440740741640d90700c0e0084414804500c4002d081a0100058110958105c88013407000511104880c025 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 820800953 1250 820799703 820799717
    0x2a010605180f07211a03010903050307021009120813060c08240a0605090d06050c0403140a0f1509060603150b0a080601030303021323190f05090703090215070201 71
    0x401e059030300100d001c041500c03a0741502c1540200c0c414545c800c031340c1040b10b1aa019074440840d00000d003120f404d4217048022a50103c141310040da410000503d0540c07221104014180703640c0c44645200111074440400c008041000446040c1b18032000c0d141c180c0e10681c140406d5605a0b000703442031200b242c0412510b500005070175a1000440c0b40810304250107172007820114209803044425511910302a40c00180c00c184000014071180700b6103118400d5051b52984072030851034000d4011009001c050126032214581c000421909811022540d602c4686891428a80085400a00a4000054003c524111001050001c0c421080c2d050500b2800104408900e400400051010344d0003090599032045005000190281c0c2c02007a080c404108410036059456442400100d54104221a01070f13000c0611060742c105110b41c6950101c1d02c089030a503a50512070f100a607616184641c1e40f00390080f1011889090280e4400c0d8142500903041c0340c07800e205491000d00c65401a00200e002580d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 820802203 1250 820800953 820800961
    0xc05060a1533051e091f170106030203010e16030e0706031d06070c060510120807151b030213050a030803010311010206060d20060c01061a2a010605180f 67
    0x1107041140d45604d008525003c0c29001c1580000e001e41103920b0381604002d80c000d0402001c2145420000480340540e80c0c4d1608222004c440c214941d010fa0000c818180140010310000f1003610b05941d200020781d184424480101000b10b0103000700755202c40d018091070f000415900d500d80c0294002450048200d42601070524140d9910340040740c5090000d03a81d1040b600020b034898108507080700d0441520b1020a4590380301c403030780306500d40d002c680300a800180a030400040d51a80f0101000050040040d20303504040343e408200300c41c460b041010b50011341c2e018010f00c440507039806030001030080b00040341c0342d140c5071500c1d41c0280000c1d544202e0303140c40f5121561001501c035109220260001c1c1c1d041079940e0711442d1f403100407090302010402c8a60594a15103540c8060f00d0001910030012801c0d501d4241c140d8030010b43c885c0c0380c44c0305080070000104a03910070a4100e10340100b00343c819035495007505800d80140302940040354030940c1e541e81e140c001c0c5602046140608900030a81e2000d490b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 820803453 1250 820802203 820802207
    0xf03070e10050301240b0a030b101115090c060f0c0d0305040311010c0e060d1d16080f1905030c0a050106180506010816111e0705010c05060a1533 64
    0x255100a00c54040c200b141c0c140456443c100103040e1f00c2515080105d00c0c000380400003103180960034480000220103052074200f8020070000f00080d02c0046600351401d091040c0d800740c5034602e020016005800010300710400c0c80c0441c00300c901d40d042e204141c90101060303201c020094a429142540002e08125000855880610400c4440c010b15101c4040d21007550007840415000000c40134200b0f42d0750054a02841113450681901d810306e18050300041c459106614004412600104117651010712450205e1000207840d10380400704141d6201e0840c100c3c81d1013407651241c40044882030044d0380e041c0301045815008242500c1000282030710046807000c0540c210351040321030701d0018120001140b194600c118030018460300500d03120312203920621300140390204409030790b030419207006100d01102106001c4080505402d00e8034404110050f00e49940e10700b0098019400c8541c2e5001444075090701d500320400411241441083c1414034000b2085224910401e05110241c1c4c00d10b8440d00c64 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 820804703 1250 820803453 820803491
    0x603070b03310b22052104030210021f0b1c170a08100b0c120c070f031a06040b0604060c0206090a1206060e04020904020f03070e10050301 61
    0x303286200c400d41980d880302038600c0b00d14250405410211080003440d0b8080410400382a055401405480c903a0704201011044402022405602840c1c5412403140082c4002c9003007001100d00070715201042e4407840c5c9081a40c42164402584a002806110695a004038030700b08003000e0f803075101e5002c0100d0b102c08030a030307080c0c0a8803903406a49020349001c2c130340301c40e12000c1006001e140d611102500c074040340706c99640007501500110b5501e20402521524028a40d4080d150300744102e810198040c80441e0349110b01da003408840c1d0303800f10b440c201f8010104003610042c55130380c0000d21324030394a00b0404002e002c2410050007181e00c90000840d24101401001088030300079005500d03007854290308039a00c650262089030712100420000c1030503074801c412400508000049020700007280c3c98490110781d61030340010007551030107003040056910742d00c40301c0e403154041d602c07410351a44420001c1c1c00d001e0a1b800400460702d901c4140f00c014108a001601515400d4008014840d501c0341821989 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 820805953 1250 820804703 820804709
    0x1150504050d020d1412130b040e01060503150405010b1b0c2206150207180c050313021201090606050a080307080403030f0228031d100503060f030f15060307 69
    0x2c0d442c504070801414461507240c9401c3c0289680ca0544000344005414103a0304110182e44c2d2501040580c160b64014080e080240400c8001500d420318041e4200010503051140f002030180100018481ca8146940c000d217920006100308450741e16010a9210703500000c0000402119000740d02540880002c0c0812a2540080c00d201c0d280c030518820b44c0750211020340c1e80c0d404940300c040024070421070070355100c59900190040d010301c030708205114241d50048044480b0082c2400d282400b690340040403603800c45100c1d0200031109a4074004218900600c00c4008280d618002900f408d0095a40c01002940d404413242c40c10303550b42e0034150360389008019028109403010082000064000c1d41d00b0f480c46c20490040e203072003011140c03007299046000c1e408001c2c181e10404001003016070100c041007219024005040910310010040381c0c035002c0d500a44010321100001003941640c9405403402040300050860354281400300381d564030f41c04a24050120118848049402403a02141d0030040e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 820807203 1250 820805953 820805959
    0x601030c0918140a020301150519060c020f010908030a0329010206061c050f070f050109180c03060b07080705060c0705060f1b03040b0f060102010e0c0411040b0a080115050405 77
    0x2002519842e48400300d40c400d007603030f0b80c0344c070440c481400180c0382801292107015000c00c0b400d41ca11300d09001c2c014003040381c0301085480303080f101c020b008017600034181c0c0c01e10f60380540b007176002512a0740040c1ca4503038040d08054058800170601168842d4141c0041041c0070468052980b54191450551580403043c5041409a0070407000280c19040100300018081100c1d01e01d00c50130350064481c0c500340501d8030103201e0341e50080c20050100c95010603000d0b0050000303282080115240c400c00302c07804140c5201c80c1c009540c07100c3c02030310500d00c650485009000c10360001c0e55507806610f1728690580c4441000c803064044c43d00021000000703001501c842a8000001e440380d95101c800d580001c1c00002c0801001034411100c00142c0880d0f40091442a84940740715142d605003030b4160402d0040081000d811603040002c02d02a0710302c081001030000030141d9002c00c01c0b08000c1e1415580d400381d6080b041c0031400c080b40b5588a90780c01300900307040f1307104000c0b4203545800c8820110f49901c2140101c1d60 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 820808453 1250 820807203 820807241
    0xe06010917070603021e07080a0809070f150210020c070501080a1a101b0b0f0f06100315051e01091a03191b0e010e0102010501030c120219080601030c09 67
    0x9202c3c000c1d0014046808550020990071b00e130714164440641029106544100d404070300105a55080100700d50031401d42d100400f9460b14054080c07104403180c1c042c5012700c01032a118080e0950080080d4242c072102071a081d902c0e000100e09040e5204042e210b0340780054407210114885495a1080b00004a090314400c0d1005101c641401074101281c3d14140401050a18440b81e95000344c0360200e045104804000c0d03039060401c0712404000740a003c01d80e01c14901c0040c0017035a03540f2010448a10f209007008500305040c84e40c3c400c901e00780c940c4800d4110f01000700c0ca514405907200d10541c00340c0b0980740d450400341c0700d800312001c100205445d892865001c03c0402e0014050b0419001e50031240f601c04074161ba0480c802c9051100c9249070f40012880c0014401c6866802a24107070448100f8030080101750314549a00d05020701511445a031700c0161100e00096444080b902d80045007184440340646984000b03440d60b54209120684134041400d501040480c01c43c02611400e10910300c10784 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 820809703 1250 820808453 820808459
    0x618010b1801020f030a080a0b0303030f0a0b041d010203010e0c03130b060d15060302010f0e0607110102030702190504051b270301060909050f010603230114010e0601091707 76
    0x2081003403154500e035040d84134070035025410141c10401014400c0b1075541d03500060802042c1c1c503094800c0c641c0154403030f8105204000d05c04807240c98003a40800e07c3c2402060524449000c40c005050b65045d1521600103d09050032800054000714100d81813100e0400d80750341c5044040d0041c1c0020340d235014141c044480120017050544444940081c1c00a111885401a81d41d81c52042d06860b407030a012143c990804009544c0c0062070710220040342e08181e06c0040381e100024070288100c50b0b00600d1011300001544869208106840c4000c0d800f0b480f86100400514001602e1485480b0303092240341060300080042200b407020080500070308103810b0402c0203481c84111112038905401e8050a40c001a5640540d4240541d1000b803410480002c3e41001a051243c10300b0030a165600044e81007600810004020690440004440040222800040f0002240503210b6038101c40210130300c2c0310000c00d100b50180301d0319005e481c01741c8407012007a9582c0b4a80120400c4000350038032a41041c2810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 820810953 1250 820809703 820809727
    0x2709040b040b0406060b0d0e0601050108130f11040203180d02152a0a030c1202040302030316170403141011040504020703020f030708040f170a061d12030618010b 71
    0x96a00b20f40b1400010070046c0d01c2e445908200d410130350074040281e440d074041c0310614909220982c0900400e01e4400003903e810749422501c0d02283c48014000001c40449205001882e00b042c00300341c40082c0250b40e24140807400d118a1090451001c18501909002540c105d00014903807480b0900c40107084000c0e40c8003d01e035142294004546034803040d03d405002c0707070700e0490802484550441c0d10300250f020400007005000b0341c01d03e41022401031040000748050394000098444990b1010082c0310014003070315000700d2410a40c5184c1207550b1002c13a01008105100c4018044c1d01c00302e2040307402c03a0500c0b01300d00c4184c4c2c1c02241d0880201400700014419400d0030b400628106010380121501159417000d03691a40d4402c0d482035030b40400106041c0410360745203081000030030031403401e68444820b40b5001602c80786080d8005003401c1e584d42018404104a00700580c0a040300000c2d60080b070441c07038628601d035104850783c9200300581054810061248414581622040c00340942004041c01c08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 820812203 1250 820810953 820810973
    0xa140f0105043206070302041a0319050c0f04090c11191101050c160905070207080d0305060a05040c110c030a0308011404020f04140a05060703020a03120f022709040b04 74
    0x403c825286883c03060401d1030804100c52409a80740b60340c0166518504044488464250701030380450300000c000b408091a182c2e8001d20860304080c50000d107a459150f0051003d00c44c034164039401e042c020500241d01442503102c0350f118040d80d1100c11030341441084290b1078080c1840c8101e008c01c281640340d00846c01c142c406042c1880107040c40e44c0390190303c0c40868035060f044080400c00d000b07011010f000c9a03103a8083d03290803030002d00003442c529040418068581c0403540c4c2400400d50b44a00081403642c0d10800c44004003400780003000720700101c0c00c00405500710181100d0396841662100710716410000f5840d84419010303900e1252590070183e024541211070000310341d00940074080021100c00c5a4028001040c406000100c003512103014404a010f941d44520301c00e42081c4000004030f5004a1507840c6198945059210f440c40b41c1082c0004010810305100030074808129000014440140700408010b004500b4031030181c0782d01001119581160700400090381c0c84040b400040c90300507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 820813453 1250 820812203 820812263
    0xf030b0603060619030b060c0a0c05060910050a090b12100f080307060504150e0a110d0c090f0608011e05010801022107020c0306040c29090f0607050a140f010504 71
    0x18006c100c1294100009103241c203c40b40c80f904640080c501501045104040c550007000180c0b0450700b002c03038402c00208010760410000060000004400c0401c902c1081c140000e440d090202a4540300c209146900e02c0ca01241d070003800a000031000300d411b11450783e10700300300c880d00340040d0300e040807a07680e18029100c040d20450b01d03291082e0095041000f43c1c082c0044c03001c1160000c00341c02c2c14034184000f000d10f1a107546402040c0e034024410105222901420540d05c6059000c10290184005003000308043d610070022035107000d800c039820304c5100d000b0040e0350384581024000c1e41d80f199510f500b00e10404000ca140380e80104400507408040d000c4460740403182c1c3c01034a000c090a8000b20382440c4003128100d403065814002485250024480c80030b119041403002c50314a9000b01d506030706c51151184007840795003286148006a07444404690382c0f10350007000c0d03c1d100340152420b04405405500e0b1314035940078500c006429440144070307540c42940c000101c00400361204c0551010401081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 820814703 1250 820813453 820813457
    0xa080f0c030f03040605190e030a0c1104050403020c040605040212130201090b0a0e040f05100e09070906080f0d0c0302250308030f0402010e0a1d0705040f060f030b0603060619 77
    0x200400682e2035010340654401c40c082c8801148a1501110000c06000b81481004e5004d1402c881c800102c28000162281d50f04681800082e07582141007252403200d0b4082e007254040d082c001004105036000c5601c048850095806001b45030b16401004264001e5551300c282a11540000501c284d410700000d80c0e08d58018104800d036540c139a20321405c0740c0d02c41210780c0c1c0030420701b0b6481d80351070900344070302c20300300134605020401170902d03400400031080c46104080d840c820b40b4002c14503110f81400014000e1086400800480790b0f500180d031386a100500f4020341d14085c10100381c02e42070040c48113406282c3e055004d840201960f5039141041e17241041d03060301c0344011490100004450300d00450044901c60340704c5205190a1000400181405c0c03000d60103600170030002c21440440b543d2044070000441c550b800c26a54090045581c0d010b5030307111184540c1c00007400100c2d190441d910392001c42d815581801060201c80503c00d651000750b48150300448100201e0000c554440c1c02c40420341c40314 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 820815953 1250 820814703 820814707
    0x2030303390307080a091a091606020c120619110f04090203151507030c02040207170c28021903051f050f0622110d05010806090a080f0c03 61
    0x903042100d00d14509a40715080300d04000107106400b50403401141d032000200303405006e401055920030316903211003000c40c1c5d90b03046202c000c0b600260090200b081c810015008515020b55900b800070b5559070040c6c040e0b405010002608250b0500101c0e800d4852100c4440100c80b00d880190a48002e08511220404580c0b05014001c0d021110800030402064980b1000d6144d0078044211000410030840c41481130700c0007112854460200b40c11b5800e02501410f00040002003400420302070f110b6064000d0040a00040100035420303240e0291165040d481c0856030510316070004144154665858040e615842c04155001864030824030710b0420510000114855901e40c6c1d9189441d0100c00382e800311108103104080c038142c1501c11681c0c00406966552214109035010980b0a1408101c800346099038481090a80807030350024611007810100540d03499014001c418000d200038095109103002d0400032411070440020b44030405500000c05601e040720705060201c0b00e40c460015441d2602003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 820817203 1250 820815953 820816021
    0x10050a233303090d020d1b0f0206070c0e0a02040e061003020d0e0607030c0305150d0f05101401050102150f180703080904050702121c0920041802030303 67
    0x10041d2412501d6004081c0e40707a0501494207820006084011011036001822003164141d00c5101c1031000384114141038010042c1d0b0070042d205d01c0b024103010750001000900c51f000c210103c5540ba089400480c440303076954540f0681c803000d81c0308074840c1401d80940c07400030408901d4280c00056000074141801031400c400211244c094801c515880300720342e00f0200800440e25010b0081b002410070a00c0d01704001d203400300e4144d420041c032005007400380c04621101c008011459100902954000040f51541d030201c00036040507010000014400d41d258000000d02540005a00c1c3c0d481507044242603c1c5070383d5044140f02080000301500e403501580c40e5140801ba500380b100d42c000d1405580c04030341c0d0741e2a0130709020a0307850280c1940700315401000c0d9850041080c02c15552014030070341094070760400307501d0450094104420043c200704c000c07060310102121140c040d00c00c5104151002d10081c40000c000030191802c7d0000a0b4141e001000080c0314039601301c188880c44010400c401c080401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 820818453 1250 820817203 820817269
    0xb030108390f18040b010603230a02071b06120e1504060f091127150105070c0e0a1d0d052a030c01060503010504150207020a05060310050a23 62
    0x21450b10698901d10f140d00030700c0107000b540300760b050250000341400c0c003240c903800c09050f00210201070108649004800070881c07032011034045643c0f154125945851070354904416004800b150701c240c401160f034101c001d203c042c10b1802108420384422000e014042e207040c2900c00e00d85c0c80104121445662400b000c801100345110f607102240c007800c0291914104141808035000413040010f8140c1800001031810030f01740450507a00100108650144034201c0c001aa498081c40c4030082c007140d4020004070b00326601f0601140714642910081c0403d01405240c203488824140b0b0f0101d00c0d41003d020481700c2d40c0140010007003403541c4442c680f030011907195822045c0101c016a00010f400001760341d1411070090096001030700c400c8000300b0041c14503548540790030f07103c403541059168000c5074460943d555659890002e00c00a0802d640d00d1400d10210407481075039003e214424551540e01095040c0c1074128640012180d4184611768151041005200705c003c070041c210329054005101c1c40f42c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 820819703 1250 820818453 820818469
    0x50a180602090127030302010e0613020d0807060c0e0f09070f0c021305010816080609071a0c0d091a030402310207080a2601060302090111070b030108390f 68
    0x130030249001000c9078110700d4003d09503041c410180c0c40c41d6000c0d00601007a0b050020000b000d6540c11514142041c1d468500851103011300e0001418013440d00415600700c0c0d4004221404005040b42d125a1507080041089003811084d40c4001c000750400028121440c09024003550640c0001c0000900d8560344c2d0001c4103030360098102d6a00c5401030031840c416081180700250242115001401d813518009404c0340c1d03644054401c8866941000c00003001001046d800c5036203880251080d202d0b0302c095100090b107030100a124007045c0801c0c600c02003024100c0c83c03050741e01441d80240350403022146690541607145400e06c1d089400140c1c0d1000380c0c10102c1500c0148201c40c40b40c8441d540304c01c0c01181c0a8102c406190b00316180d04a00c91100140c8010960741c507040d1402d5080058503104c81c0001200d4407149002c08c0c00203441044000700340b07e8a101c000c1c0d4102c1c2c06240403078221640406110b41000320080030905003421804200106901b00d1489240b031140107889a1408000900094182 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 820820953 1250 820819703 820819757
    0xa060e011202011e050a0f030f05070e1509010e040b0103060b180a0f14040911030f0a0b0a0b060a0c060906180b010602010b18090a050706050409050a1806020901 71
    0x81d201d2081d0000031035070401c80603444000b801080440d2500c825401501e0b0b0310845a803c01003103c41032900c3d001c1070081e4003030200043d050000f00404d2502c0f182c040e045003000d070309452081c10414090281110340380b048410900707040e07480808421540c000d20001d400c5095103e8103140c1c4801d00405e40d17004110240031840c00310300c0e030081307042d14100601030207840710b400100110305590020710074209000c0d40a00c0b41502514002003140950411070340c0da0014410300c1e503250203420301d101031040c1c0000c0c0d141382050003800303900c10607201d5038455000c0350b40c4030091702d400c030205200220209000700603070440c1c00c0c0102c0c400318500d07419907200b40c100c0703c2000b8031043d490241150b61007440038413a8041e01410450008100c07120781000004c103041601940140315040c1d00d0005008a00d092004400d62a40b12080f00c1e992601e90401034515000f5009082b0791514200c0002c000c02d138540101403c841d03051840004108080d15410003075404500c03850305001a54414550340c0c105003201541d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 820822203 1250 820820953 820820969
    0x50c041a0c0f0607090303030e0109020105090910030606060e13090209040215120109091103060705180303090603040303290a060f0509030a0309060207090911010c031404030b07092306030a060e01 86
    0x1146c2c02c40c50064103d0300040c0708603050f81e141c04044801070340c0100c00c5820a2100303c52003452a07544c0721120b82e80000a800c020001d6050400c000f94103070f0808070344424403004845400d948624595800215819040d02035402000c803c042000350410603440c038807802413420300c0303803902c45a0700000d824035070b0a80c4a42c18841e03903541d030360f014050f003460320740020201100074001c5810035540041c42c03402203504000c50034000c1210407009560400480710000c01c0501819182d00d0316082c09001083e40315110081c6000014940072042c403010080c2d001610020310241d205400c04200f1113104c0381016010342400006c2012448517075080141255070352080d83c5080c811400c000c0c000381040301075031101c40d800e4100020440011541c3c0b00c04410a00c0c20b103001000402c039800c0440c0c5c1c0500182280d00c540c0400076000c0700780300c495004c039132041c81c89441d00b602041d501c00d003020300550051148200a081b4190640c660b186c40e0f401550002c0d040310340441c00941b5054000d031a684286c1c01000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 820823453 1250 820822203 820822217
    0x70c0305100c02010507080705090a08251a07060507030b0d060501060f0504050d0b0402040204050904060911060c060402040c05091e0a0b0906031603110c03030703050c041a0c0f0607 80
    0x401148075000318259442184000c0c071071030619620250604501030840000d000c070200c0c1d209220b40300d080300440142180811917038440c031082201c0d4266184011701031410b103800380c40411080088103240402d0309190220320302c1c102c0c00c0d894070780041c20f0203803038901056211511400c859440c03454145142d402000002415490103c01820b40711764444003009001041c4020481c40d525014115007464104c843e90805645c1c03440020024401d54000d95804007994090000344a1203900080400303115040281c8510008000c00c021130240c1c1e0740001003039005000140c01802c05030030100344d941c1d1900300755090080c550001103400c058880303203514031100759219294600e0100c1c0400c00510b60a00d01c1d41c60031961101060042c0300003005482c84201c84008180390505c40d0f444104213800c40850b8036241e082e400612522a0300c16180c00700085d0910010030a41c03951001214222611056403400300040c1d520b0749103042c0c02c6024200640d0103660010440908241700700d40c441e0a555951007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 820824703 1250 820823453 820823473
    0x1209030c09091005060f060d090602040b300c160c05041b030605060703081b09041802180105090a09050c0a0603050910051513090203010e0c0109050427020303070c0305 74
    0x88116130004013070900c1059282c203c410030b915200102c84190b01d001c0c0d0046602019030a00c0c0300a03124a0b401188028400a9a0720010329901c2855040724008a541301d5040c081c440d50107090603058a41981000c0d01b044100010300c7d4481580c5880c0744218074882a0075518400941280c2807910408440312102100e500240e41c588209409840c00304d9034142494490b85005280c920000c00c800c074110078104091000300030f90010f4a8507840000c1043c04039640d1001a005400203421049008035a41c83c0c00d502400d9220f44100c0c10307141c025040741a10b40e181006180906001101502c3c1c40c00b44462103101c40d06e8460b0090054140350f1004216401c10004240c5401a50003000c8100b41c034020034092589030b0540700d50000c81c82100c01c0214070807982c9416000b0171481f0002541903203071500c1c02003101d0010401c0040020300f600c0f6115641c0e075400a001c1079404404000c89001d0208099140e14000510000b522a00143c00c8a0a0103115507405002c50184e400c140c80981c0b1a40800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 820825953 1250 820824703 820824733
    0x60f050108070806011a070c031e061107031d06070f110a0b070f022419090812220503030a05070204050a09020f090402040f110409110901021209030c0909 68
    0x500510203c0000c003d01e40c90042880c0614000141c019072803400000e12030140500940000080c40d04102407080100420070079922800f013032401210b2150070905400f0341d16041009070b458850301078a4215240044103070800a281100310511350000d010300ca0fa03030102e042040121149031241c0403110403c0a000d0403c00381001c56880642c06a004100110028440c10980d42a140c0d041e50004610001420042e820128010500d220030101090724880d0521420103905c1d41c6030951a0b0180182e150000a030321500b085214010524003000314000108110440c0341001701c0c514000c0308a030303499100090955000080ca00002140403a1860540c1341a204054014000072800c0004e91910790200d100d4510341804c041c411440304002409644441e00030f038070b080c0070302a01000000707641c50320141720b500725000d1700140c6841e04006140e044004001c65400e100c05070002d040d29102500c0c0810341394080442d03282c240c006c0b88a6244d00d601d4990449004d1959207001d00b4140c0c40310b0b004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 820827203 1250 820825953 820825963
    0xc0d26040915030c090e15070c021008010b0a1b08070f06050705130302100309120c030207050405091207031e050a0806100f0f11120c060c0a09150c060f050108 70
    0x1050198500c41c1d5040000131205402c840031103101d2200803400d00802007155040c25201c5500c490100800000c00c8107446e03000d00f11108041c800c42d5414580c00403000c007240c0340403007409044503018041200c44902c500549040002440c50244856059480c4d5905441500310301c40498101803050b0f51340e13007040342c0340c0a40c03070740034003140707846170a0208158110b0401c0c041407002900548407060018403d0f8400e80200c4040740d0001508030f070564403200300404100865000760014002d02d2b5003c159860705010303081c0200103030001002c8151001ea501c80681d802180110140845001140e0001700316030000d1200100b00c0c1c9400c1e450740c503025400341c44060014141403103001440301e014a160b40100b00c007000c1a895140c403148900c2003100940d0300003c110035071109841002d40741401c880d59400141055803084043e03501e60b4554a5485440b80507a81c21640414160103090040b04074a8111000c0c03541680b40503485801c89403603d03411038100024896038652907030b00601240c0c03000c1107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 820828453 1250 820827203 820827221
    0x30c060a080f160207170a020a260a0213050712060b041802090102151e0103080a020f060f070804080409020d062603160515071107090603050c0d260409 67
    0x4100402d1001800d0002e4640f2142c0c01030108040502d40600000326040041c80147d40c2e001c0c1c00842d00c20345518252040e1601920f503240940c98000b0020806600803403100c02c1e5542c054002c0d50a416100141405401c0007040c01e8200031303280795070303d00008840c080d030f038014031407042015900d40c184051130f624615009203000d000c900400501304d45990008031010003400320641380106481c1c0d503250001b0050190700d03405402c4031020020041c4085500203000d40260f0340c00315100d040c14803141c87d4940c40122004641d007460100003800d024080c1803055803152241c1050780c905030b200c0031510101c0c1c1100c429400115525141404800343d0b1840b1006030b82411018510a4141e404401d82d41e44120a0319080c2c080c00030080004022041110340c14030500703001d03221078618200c40001c0000000c061800c44d94800c1070400180000d4911403442503139000005402d59940070006d10400591254084030041c42400c1140320750180030340e10240300e0602403a02d40d559480c11440d101911030001d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 820829703 1250 820828453 820828471
    0x323040e010e0123131a030105015f1212090607020d0804060c03090b0406050708090d1709091f18060e0109050405010c030b010f0509030c060a080f 65
    0xc1c1c01401030941300400e90b031405040e07101ca520307000c04160118602c00c40205484280a0030704100c00854040340c0210a440d00080d4020011030707a950310565501da003400c260f100c03141e43c1d2001d840303035141100c24812003040290b203001c03800600030320b00340d6410b02c10710464103040101c09a16003280d05e06400c1d402d103081204402800410b4440c14401c2c05481800c0b81c052003084c0000f51001191108440e1410507074001c0b00d503613100c47d42c0308405066003404a00481c0044d50381c0c0c202040700e51500c4203460585280e5944c4a00b0710307070b20741c2c1d507480c0c65800007a070740d540150207505000010f6165010f043d814811031f500c1c41e484000e0b06041c0030091a019150102c6c0b048454020700c44500d95440c40d000f15105050303960061a0209014001030010341c001e10b03103400300c540c0003003610300454000c580103602c19402044699100c00b41101122229104d2500265680c00b00003011031107040a0407a500000781681c5464006000140302076000c44844c0c4049030101042111040954003219401800e0f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 820830953 1250 820829703 820829729
    0x11010b03030d1a03060a060620030307140c07080106051206010e1314030a02070609140307050108090f06040f02040518100507030f1a030106060207050f06070323040e01 74
    0x544002500c0c1d005205920040390354071800101d1540342103c1d10301c003103c409410b480710340c246a003041c000742c0114090a404035a140b000b10031581481e43c494490488060080c0d810b5850f03100c42251046012038035408001c074107106400e82c01f0b406100c40b2004214281c000070f515032900040c0036180c9d4030750707411441d5500144010058101c681c0c0c0c0550b88100903501c2d81131204a45d00d800800340340d01108024a40c400410324220407500003034400f0540e40340780c591549403a6101c40004014401c0c0b0722694041e000403801300010b50007490070780d410000d0781c420f9604502a070401c02e45090400c650503910f584002d541a415410144600da4010852640f011600f0124600d0039030343d8000303500b0708030b40ba42d0ba03000060051407103940002d0f024000e240c018814046110070580400d046039010b1441380d442c3c0380000500500000b00041103580c00380c0a2400b03140d8070b104206140c2c11000040c0c1c1404240b600e0080c0d500c40001e40c040005c400d42d071181d500e43d818154040302c007401c1600801188055 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 820832203 1250 820830953 820830971
    0xa0605070306140f03120403060507170c0901231c05090a020a030b060d3806010e060705160e1b1809040302150108070e0c0702010f05130f090603031101 67
    0x180200c407143c079203010740701c80c81e2001e4001c0c0030901d041c0e1030300c00d59104000040f0780441080042e411071800b031401c994503040c00c071380c0103294032811324815656404030003800c014405603940242440c1028100c00300004d110700820032062041076002c0b10a00020032941c4100400c03e12652113041e4000031240c00801c9210044d6010654403142808007502e0742e000347c000030b141652074044000c1c01c540e20a1502c3c0070901c1d0030a80604941c0c80d0b01c2d9a585004200c599240642d050288061103240705030348503070b51200e6502c2441401c0d07101300001e071803d0140092102c089000313004190020030105200e030300149080d020810b6100c0860300030480507002000452801c070070100c52858101400c541841007a05c0c1c0b480c00f0b81c0390080c04004035000c3c100c090b0000504880100b4030804598041440c0c6020b6034418071180c00911034410020301050001c1a41d44a9034401c50141818020041048080e41c0d1212440d00c002e556940c40184425201d00051080590000d5401c01091401c8001d110501c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 820833453 1250 820832203 820832219
    0x8010f0e0103030c140312152407082104120f02070b1b0703200d0c060315090906021c0c09090b0a030b090a050d090b0d02030a0b030d020a0605070306 66
    0x301880007504005458469206001c0d289400c05c1d92540c0c00c404aa81d0b5810380341084003024030440f1a0f1111048980d01d222090500e070541c1821402c030040c11000f50400140b600c8000d800c1804190fa0120741440304504000c00303000c141e00c40903c01110300245107400e00c0c0c100000c542a0103000b081081030118192066000500042a1003590700e1094071505198070301020268100501045031103246000014001510071050100c20035800c0f41c05450301010521090907090b00b8000c100c038406c1d000800070140319612601340502e21102c5040900e6443c0201c01c2907a9560ba07003078414650010f02c42070116136240c01c565048034005814040c40b001024041c140000728811032041c1529102e00700c095a0311410303103102031648030044018034100000056600c0308145411140c5114440c080041540107c2c00982105c1d001c0940c0c9103486900e280d0700000c0c0d00701403c4400e2103034a03910040a50f075000d000115a800441c0c0c0108100c031500c0c1030800a031080a00300c507041c9403808a0500000c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 820834703 1250 820833453 820833479
    0x120c050303150f04021c0b031f09020d05120c0601090608030307030c090b0708220e04142b0305010b091309151e050702030f0406110709060f050108010f 67
    0x9519060580442d84201044208a060040d00d5000d0710010302401a070b0f0741501108080c0c00c8010080041c3d002a40c1803655840f40420380d52031700502440c1c0000f8108168204000080c405007401507402c1881d9a4a031501c440c4040d0f9000b1000045058610007408101803401400c2800c42440010303e08490240c4034071002d4a91810141c443d035240090324068510800105121109036507600002d091150142e0003013000c1c403078000e031003115906900701e100c56003a0a40b506141c0741c1420383c9403a55004a03101c3e0f04031606980740100b1003802400000108450b900001030360401034107006060004040b180140c200d01e8002106200c565210346072841d541d01c00010007070b00005c0310740036418240000c101070400150594180b1019005030b1020075410001c00044120500440c0c454050a980343c2c012940d02d440c0c07140b814881048450b02c03e841c07004102d1840341c02d44e401c60703413100d09000070341b01c0940100101c0c0040c09410861545e002c0d22441c01016002c80c600003590916044035041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 820835953 1250 820834703 820834711
    0x16170412080a14090c040b0d05060106320c06090a03140a030b10031b142a01050a0b030f030306241303030e0f01170a020c0f011503120c050303 63
    0xc00d00001a2104215400605450079078180c3c0d503010324002469595459800c4a094025418290901c0c00c5050421b50034421030342c003501801d016030901100f25818127448454919a1540040780c6694210304504099980183c01401c0da131455019141c0c0d01d843c0e0007914114856000c1c501c00750209501c50340e803e07410405400030941e500384001c0b0440103000000c0107664010a119144440190182d0080981e16240001141905a403c04c181d9029000c603c1c10100e00f0b20410000341e0490b0007a101030045c1d40c810101c50200901d20340d4541c21230700103c85182c552559041070240b589800c000b1504081e110000541c40d600e444400304904000094294480d4480c0c2003000c070144902801307980e012507001c07150703038111581da080003031100b480c00395000e000c6c1e2001e0441301a15445110801c164212100d500746d9241c43d118512802580b14007070910a174019840d00d014146070a00030914407a4005600645036800c42c101060140d948851041c2800f00d1003910700c001800210540b544 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 820837203 1250 820835953 820835957
    0x60120070501270f0e07080f060f0d0b150a12230a0f03020604060b04020a17101809021302030906010603050405030d05010303120608010209030309150c0616170412 72
    0x31400d085184140320315074166100c0c07000c0c0f20000300852041c01c850350302012100710b02c991181176140e21034140e500d20003c2d1030340c100300c0c1798080025100b800e15402020542201920041c810100c5440d9451000d100359403000200540080c0c3c410030340390005182c00607205201030695002d401340c0d280a10409800e421482d003042807100011041e500b07001c0420403540080352045444c2092034025100d8000701d50845150303250ec2d540380214205442076441011960300c90b240301d02c81410441c003284500602035008000c8042c07012868100280c031000100ca10329101241030742140c41080309440c828440126040d10500400c0122500010301504560541c10001200d0700c0307c0c2405419403260303100c50b0192a00700000002010780c4049a1100090440f00401116494041c241c1c01d03441104025581a031003882440103600e81002d800718203440c0000080c0c0303407000320205242040e900700c90051164061585807000c05400c00c00322080c401610550308900d10309070fa103d0500070440c80495007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 820838453 1250 820837203 820837217
    0x16030218010305190e060a061505030c0d110a0906080901020a0e0907050c0d120e0601030b16020c040c0f0210020301050a0311210105180109050c01050c100c08060120070501 76
    0x10200c201180d0030406004051105d0109188119500c0300c0507501c900d03103603103817030350000740e04c0c00e1041051005036841d5a01880c1d82c8401c88402596000f00b489144040d9a510510049103003110050201c1c04a41d210180c1403460081c000e000c1c0c0314020700c20340040e401000f1840300d45a000a840315218800c503040c10464490400498590003080711503da54403801130b111078110b401c6170b550403844d4000d00060103502e503441d40c8562a602c003844001c061464500c0801c84034403007104a030400d40350318170440300d0464480000601342e812180d103c4000c1518000d01e048010741c1031281481603250400298070310352401c070203d01a400148805440c2d8011219148515603d203140e42c2201c034898400300c03803900b0007001594020082540d001d0740542481400c0010103106000309628650005c01410240c5026001514a03902c011044040d0b030041c0712001b101b01425104040a88031240d072001d200780317041c1001400d4080660700c031880c900500c01d0110981e20300080c08406943c000e10f0100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 820839703 1250 820838453 820838461
    0x121d101a06070828091401020c0d02061813060e07050a020a0b0406060308070c080d261f0806060f04180f030e0d0302100b090702060f07050708030f16030218010305 72
    0x13400b51507440180d1144603000018034089581d0082000054450700b02d03020406e013071400016a41c071003040c0c1005400c2103160306458054034041016100c000801001030460741006400078000e540c000c420902134607a605001d00038108002c0b520355201d900c81c1006072400c0044500030390344e0050349000510101581000404101890704181d004640c4044075680b640c00a141c00b003a054000d001d80c2c1810b11800068810081c459900080002c0d266007003500840d18081e086051400300401e00140900e0010410040000f003c00320002840800080d140e903003884002c2014680c190245070788102d0500f01042071007a1503000014100e0360089060000d00030514003514401c48003015030f40d100100015003006d05801154154200200b100104511204041000031800d821303145000181e112000164842840000301504003046040031414490680d03140400f6a01c200c0e2900d800881e0034041c0300e07070807002c2ca078003902030941e508042d402c0101941030003d46510300c0703076a82d04040e02c07207001c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 820840953 1250 820839703 820839727
    0xa06170307080c100906020a030b040606050909090c0904080c1b010801150e0303161a010323190309031511030a0902130f0b150a0c03121d101a060708 66
    0x28003404d076041391080c01403402c1030414030025007200c0340030800300303013068020155850244940380903100340d5240c00b8107000da04000d10000c010010709811492095400300740381071b5280c0040310310031031161483e65900e80c000200c0600b402d5105803062003110840b5880c0c800341c6e81001c2c2142c19240280026504038813542021514175025203001c0f601400001107084a01c2c1079604108207450040682e1141403003400080300c1440307000d00c00900075400880382c40d007888003d5003004004c52028421210f4100d40154000300d42c40c0440022000319081c041d04204000206c030b0140920300402c0810020300d07071a061b40c0350845c400107240c500074503071395541041103544d01401d41c81d440c103c116041047c1124050240010f0004a034039900c02c1c1508040c03e220041a03004841c01c00303142d980c400741000c62980d020f441c003040300b01f0400700355900ca1000c0d440d80d80d500400b001d1080e0540300180303503603408489031108481c5090340c0b103425200094040800d50f103488080303401f29984070b4203043e5605141d81c50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 820842203 1250 820840953 820840963
    0x515040803070c330c02030306031005040c030c08011e09020a261606020f070f060e120a03020c010e0406050d110414070c03020c1815041508060a06170307080c 70
    0x100b544005841c18461315846002065800c0c0407244e6410400011000820307643c90008907500c07540741d030116034042c03100c50881e080150400e1040301640c51031926981c80180d481151f800c42c14403603646001c040c41161503c40155070010b2599001c101c880440c1d004202d40f0b580c01e00503400841100d0718054002c0d0415514640c5c1804d604043e50301c816181c03031211000c48064455000144a607040840f50400701103440000c8440107810609401d1900d6002d035400b11103c60160703480303545030700001e2500c042030020310808e41c03207507014000c0382510304000342620085550290040c0d15046040c405900c42c00c0400310b0321500840c510b1500705808001038098001c0e2140b2183c1101c4020901c004075400c0120006854400c0e001c2c0d501203480701c003e00840301d490b200311400308104213020882e85000c0b40014281d250014002042030b004090030040040d0749a442050250301030010000c01c210700c0d1044401801240205000d0b40e401108000c1c0c3c0c0380512480945080e000203040ba02d002e008000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 820843453 1250 820842203 820842233
    0x115170c031b1b0a051e0615030109080406020f0d1b020402031902070b0103050c091006050d0603060c2a0803040818041a0301140f012601090f0515040803070c 70
    0x25500d12602c1e0824412516003284c044100d03061700c074004c452a4a4611070180c500f04c0c001da0001003003203941d144003c3d43e50004a90099416551b07924965010a400c0d070010000b4004a0b0024500030699500c0285802e62480d002001c00c00000003c185c5000400c00003130066404640150300c1c2d03203416111000050b104040c040f19248002802001c110009050a0407a80241c043d6107450301d0305414040c1845045441103415140b07000180a698010b0000c0c04043d8501840000c1861b22030783c4000448280c40600d4000c2940e0240c40c2d01e41040440c070403809040704c0c0034042010001540d440314140400340c4020044040882e007d20b02000c1d45546000c0d5000c0100288107481e518030200607090005a507184c042e508142810222010013a03000b070140e500081140c805038600310324020f044a400306413028041c401025a00182c000b4001c83d1800d50041c251203003c01018a0998074040091210a0700c1051641c10040820f10b03600c2500c0e881411414074102d21042032a1125a5001c081c1e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 820844703 1250 820843453 820843477
    0x1c12020d12022214010212030609040b090f1519020c03040323010903031d030901020d111f0b190b03040201140403050d030b010807020a0b0a0c020705090115170c031b 73
    0x3c100020020007404040c00780c41420380a0341c0815111140e0b900192104851454000020201060000e0822498103521480310380680c0c8250724481303070681c00e1500ca158a00700c501000d0042c060480d04910120440340e040e544c0441c0380c550040b0300700b0703201d020b14030000d09a118441e25100000c1c070050526002200e611000b004020020300d005401060070480d82e46192031080500d2410180002c00c803036502c1016002030041d82c0e442001242c0703503140c0400964240c040e880080c030f0740c0361101c0b0f00c8594441c006071000c00c0c07020360b841c01c0c4504000304010300c0e5800103a40300c08102d61110f0340100d80e0840d40a1902c9895980440c00404e820711035075100801074807550000b070182582c0740e4803014a98400760385041030360300c4a98080f40d42d401d21320805031039411040082040740d4041d03070214140b05250b00513641e14643c1e0340c0c000340c100c0101340d00c0001600400d070342c00d070012640011442c0c1c02c007440c02e1101009050000400c45180002460701030402503071285004201640c01c140c8810070444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 820845953 1250 820844703 820844767
    0x909040822230d02032d010c0e10031b0804020a030b09010203060a050901050121060f0b03040302071e090902010e10091d091c0c021c12020d1202 64
    0x1d10011107000d9410760b070001c540428125401c4642c03810600e000d05494005000f0041138089240345c8015441c048404603440018040703100052600380528090005103031a64024081d100c801d204160f00c0030043c0c00100b40c600f000741003040d44080242c1020165902c0c5c0016a90749a10104403004141e80001c4d040c070886c80100844184150001c621542050f00c014004580d1582408000d00d03080c02020f02040079140300c95140d0810003c0586240114078001c07500360b5884503a201241c449030080510140c00008100078580c0401158008007501e20302c494080155a044c0c1c1c1090020f4001c547d480c130b4840501d00c00307581c130407880d440745184002c094081182c400c11010f854820540300c3c0c550780c01091118510103001c2a545984503c0c107200152075000f800c00194192030040c00c00c2d0308180035030b941c11100943c80b21010000c0d45000c0c1720400c0e0a0092034203160b143c00c4a0504040119030144010520701d07a400b10350501b009020030400350b200c0c0900c00452001c0e10b03507036004010001030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 820847203 1250 820845953 820845959
    0x70302090a021803010603082209090302060f13050c0609041e020c0c0a03050a030c02030f0106330210020c10090602041a13141f0806010305010503030909040822 71
    0x18030390040060300c0e1204184001243c40909141c282c0d556484041d000c52402d00403141044111409500070b4074641113002c0c10b140d15442088111840340d88145e00680c04442003159481c2c0144140341c22050310301e101c65200031107079500340e0f0311501c0309111401544040f80202041e10341c1e422040002a8130f000c03048000f01c1ea080c0b044000d4010440788101131080a401d90003a040c0b1007000c3d02070b25000707400340603402e180e0f840a90b24071a44a0040b0380620515064001c3e42c4428814030700a00718100e450b00030700305102c056030038442800043d50601140014030b0f959aa4000500441e03004280c10003684800b00741d50503a0400c0e41601e81b400400d42480180e404201295008100707450703a0400b14461000d030100b02e40b42600890044034a25650802c0510090b802081c1419100c00003c0100c13010442c1c00d42d41d0b10f1140c1c0c0050580700400c070003a003070042d9903070540505030140030203800a5041204c0f840c001134075040007410143c5101d90000304443c1005660500350000f101c240850910155 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 820848453 1250 820847203 820847221
    0x909010c0906050a080a090503041806030204060b1809150d080301030b090607270b0a1107060509030c330d0f061802181e01020c0d030503011707030209 67
    0x4680c082880007900d04540030070003600650940718030002c40d0395080c44a0780d0f0308040c100100741404c0280e0b00d0303100a0000240007070322844403003031440910f0f4001c50500d00d10b01c144410355505c2d801060380106c040c00200580740c82c03180c11ba0940141200d0760b41d05131726020250b03001d0703501380707e541d58114a01c02500000c2c45142030046040780e1042c0ba4205069407500022a160041070b10394100041007a08001206010080100a040c103009226158a42d4600c01c0c101581d01c02d51905020031032940291000010a120403c01800f8900704030b407804481400082d21100d4041c11107104004041d48032801c4960044101c2111002c4100800c00058914144003990003140d151072040382003590304c040c47c00850007110203d440d40300da407142c10303181130340e004020390003840804000c08420180b00c020343ea00c840300c60781000000902c1844900c4080002410034a0600da11402400c4509507100060760040840b411990201c42044159069880c803504000d03040e0310181d03101403100d0600000c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 820849703 1250 820848453 820848461
    0x6040e070b0c061e010b030414010615020f0105070503060d050c04020a11071d0c07150504120311040e0a090212060a050a050105010c030f1d030114040201020c0d1106090609090901 79
    0x50016400c5072442d907500580043c0c4210014135070404035070407030700400c20129808041d50b08944142c03085a03228040c5075002e07003145c250768004401102d0b42c400c61003a041c1c041c41807003060000c00c0c00034052850006406081840003405c40c50140c900710500c58103000003440b02001c0607030020419580c410440100904014a00141c0100d90140306000600c0c0a06d004005820303a0224400c02042c5d9185001c01155400c2030308203803404240440700718074444062081600c141d1150095846030400150014220381030420390340c491050411041c02007902202151303900401103800030440d90311510200720024201102054584102424000c42a0041d04402c1c400d1461000400c51681e86100450b0701c1004401e015002c10101109075403010b1203002c0901030a801001c05102e26141080400c0c2110f800a0340459148403c1c2c041c00210740e410700055048020489103144071504649883d800d040300601d903c0d10546c40040e04d40c0142d02c50906480361048001d2402901d85011a0003d02038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 820850953 1250 820849703 820849717
    0x9030f15040b130309050105031312020708010c09060504031e151e020a0c0201080901061502012415030903020709050f04021003110405040b030a050a1406090106150806040e070b 78
    0x15440641c006442001031078602d070380f25a015580d1319201c1307160200554003a4806048180700c80c00300c1841002080f1507180c211075803200c5500070b102092902810a0840340c402c4441c80410401d22420000740e54000241c9080d03940101d0800304180d030180316544c0d00c10280b64010405000070350501d030648c1960f4000c4c12454520740038910103050303296001089210303015a5801181c03a2400700005940300b80d440720b038085d0301140006407454868810840d840c10358032203500141e4442982004c40f4112201c54840c0c2004c00310701d148128102210000c1d0f2540201c2030f482050399507001c507000e01d807003009040c0c0203040104003000709081c0041d20204c1d00c030040700c0036401040404806070800d0701c203100301004000391012041c2014140310030803001d02100b440680e4148209500e0b000410b406100707082200c0c0c41014941c440c164811120f904140000748a0001a49490001c000e40c460f07901d0000b00200311868071200310b07a281800280203040181c4019014460300c2808940e881c00003008000f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 820852203 1250 820850953 820850963
    0x40203431e050906041710020d02090f03070b0712031103070e010807020604020f190b030c09090f070c1104200903070b0301080c060307120f09020a0803071709030f1504 74
    0x102251441c0c192094800c5208003a08410708200c10002d0400000079411051522010381e50300c506800203407420384e04003400204009600080041551416003080e121282e000d4018241c941d1420140d20038900460802500c1f4411410002c04954072179442084120f10710312106890b4204003400038141d004420032280494041c0000c10045400000c1c120701ca0780d40240302c900c000e0300140501c81071245c03025060000c0340500300c000c42d208411002a620644c90603d015031900480c5023003080540d409414222124020818088103d5200008507200c542290505080e0441c0b1008200140350540d403d11440a41d109038081c0d0b08111801040f14070011412915404d40703a0703102d145544000e206200e042e520511003a03045061000c0510340c03180c1182800d50002261240c400240c4040407400c05025982d840c400d0110f00d00310310084050041a0700039400c00c16150358000164100014501c0d0088021070f20114a6030108030505000d0705800a50381c0050701c6459a10003d43c0958084907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 820853453 1250 820852203 820852247
    0x70c080628140c0c01060504050420010512060409170712030608010e030909090102070f0503070201120b1e0303090d1104180804060f0e0a061d04020343 67
    0x5810a000d2008800548071104160f501c1d200c060064640c07181071800340c5035490b0030000550303a031035100d098400d60160b43d03010a0147d41c005024285081d41035500d05010b4140302c092076603090710145a5010314142d4000486002e203003003c541c4090006150740c42c000e4002101403c224a22208800450070341d1002c4c0700d140c5e01c1c1c0c3c3d000e0f07090343c0c0482c0040105901c10f101c9a0481c0c945804d5480d00000032a00062401e00ba6407078501070101c415005a0380342c1e00000340300342156803240e60050002003810003003003454800000103171956800790044242008000d610119030790b0a00460314140c0000380380900010f81450f001c5501c0c8410a01035216514092003011190030100100a00c90761041c0424035080c01c00c0740030f440f11034240c0c0c80501009070305401d0100c076489100354000684440c0d244c00e1010351860300c10103000000030049034065801402845008900a0f8100380c280580d04044400300307a88000d207840704c060242105011090f200e0605007000c0e00b01240040c1415a282c01c10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 820854703 1250 820853453 820853521
    0x7050a02070503060c0703031e060b04080c150f0c0f0d03270f03080a02160f0b15060409020a050d020a180f080d11100c21060f0b070c0806 61
    0x16891340821100325011034403c00205002038400d03407080c0f11070148a5411030601581018000407111079820104840c0000602801120010021100701902c00c440c9241c2c00b1003248180b50b06405018094246403a0114514510f001c091020040d003000070303021549a00d01d4008020050000c0841e4820115a81001101c802c0d6640e5420800d6607040501c0b48100482543d044804a900a0154031515400d00a40c408070400d50010105240250703c40c01d112240c0b07040690101c1800f5149003141501040c0c585100d0702c0780016039086a659100041e214a02550709a44034410b10180d11f14980c8001003003a1400c0e0040704441c03041544100300281ca40d22021944281d000c0d602400b50164003480e0b041c0c00e40c51040040da42112840000d9600c452405403c0388181c401c0c41a1150105400c0796014044851011201a12010517002070102d640381c00c460084400c1c041c014605449000240b850501c1400608400240810001c99a052614840c508101c0100304031f042a6000250040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 820855953 1250 820854703 820854709
    0xa111215011d01150c1a0915011205070513061a0d05062e0c14070503060a0207110d1703040f02030118050d0807121401080c0d0b04080313060507050a020705 69
    0x210b8180d42d510fa64130400d08030b01440594148080e04000c540d8250684600407110750001c41c21070107601120001c112403446000701c0c1004042c141c102e19141c407601890341c000304200191800440e40280c51020b6a600d404054001070080e0760025400504410700d801c546050034402030910265800c010405074588508004c42e0f01c0c1c4036244100783c41074220881c034a080c03c7e903480c0103560a481c10318440d55012640c40348100140c1030059107541c0c01040040003241401e00580381c1c000054002103142030060355812070a004021005030240050032586400c10600624001d402084540115101d1030039103800c100300050390500f20300070350070300c0b4501e20a8041001c03c0416940d2201c098803045160303c500702c40340e1100503c12400c002c021443c03030528605501c2901e00500307003410000203a60401c0c801c60306c0c00c910a680c0c5405030707910003c0140410704259860303400c5a44180607640da034490201a00c034015900c000900040d1604d0144002c0d1034014004084400c0c1075000e075428242d42e8020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 820857203 1250 820855953 820856009
    0x11070914160302160809010f020f0a110a1a030a0c14030c0703030f240b04030309180902100c0311010509060c1c062d06020a11121501 59
    0x15503804804480030035100108411150040342081c900182002c2c0350824900600350101000e4030911400524005103507840315410f840848540001c3c401480901426a5600c0ca4404080e00d4454a0f660303200e5640c0c1c642c4030300c0000701070081031035800c4800c078051601503a00507203d00600e01e1804190080b607a01500c40e03064030060380d60031581075030380344130035806a0381c0024012010956111400914001144282e07043ea001c0c500b03000d03951103d201007800102c6e03516001106105d409000400020ba032120041c826212803502e0421040030860800018042c0020000d6009500c4a102c2480c6035108400ca80300e9400f964070f0b001c0c0b9035a09512542200d0087e1740d1503a01e60400b03000140d080b4640b0000b0043d2203da1030742c18104101103d59081111115000203c0c0744054560102c1c00c2003280c203e9084680715901140b80c542c1c9805006903844e00702030760080a950108c0ac4c3c0d04982d540da8205100d100170910141c1d1007030b80d044810702c0d81c050003d01444900700420344c0040c1307841d5140c40c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 820858453 1250 820857203 820857221
    0xb0703050c16061b1e0507050123180a0b07032d0903060203150a0905060f031507180b0a1e02070305030d020306060f0a170a05070e010c03050405060406110709 70
    0x30b6035882601e45000d48540e00ba16040c0940c1e80c0d544102441c603c038580160400f4251b8060b002078240c1c5820400018a1803032410000e1544035108104800b1140b0110200e4151b01c5107c0032542c3e20848080c007050202190750301c4600c004501203980014103412019a10071010403001c50030a440501c021261105005561540005c060036010300c00078246600958001f0251034048505c1805070f0002421041c043c4c04c04848140c41d1030030301034103060609008140030300403000ba0400260f09000c001c0e402e04001c0108040040c8400e003100034100c80b00015011b001c003007125550b0f49801200c040c1213800d03000c049a0345203103209000c500a5101044072000c1d250300c20007641c230307254628817840e006e5040544255031003101040385001c403078900401004c6011843c0c80300c1000c04121203030004074443c003c0c1412803c1d4204001c01031003580c02841240d49a00c2403c00d031040d0b80603030504031031034040c5030007160304604002000720b40183c0100501581200070411148030750303103c0c46d0b00c0301500c040365 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 820859703 1250 820858453 820858457
    0x1c090e0f0411040b04021b0d0305010815060607080a0e03060123010c1403030108100f0606050f180307080f011d06060d0302010b030d050705010b030703021005130b0703050c1606 78
    0x500401c00059100c0d81691200e4001000451803518800c00141242c0c0602a01c0c9a0180d03a4100070100c40414051069444c03002c0c10104071035850220815259807044140038590114040090a00d6440505484009400101c030503100c0e01b055402070a180d5005910b50b200e13200302c600010310200c140e02940400c5800b0101050000d40410064901d42d29050b030444104c0520054240304440c20406140204132842c01051596442401c00c000c46041d075110b4074485040c01002c1c08003a03041401c842d0035007050b80c0515520b802d07070a03000416485903401c035035240c000c040340029507560010f00d00201c9000d110003041440609101060090400181c20300c80d81c002c00b001074054500440c0e00c040320750290001155400d0030070001383c1454010004400481d00119034203003400000d215585646106070020104141560009003005440208800c200a00050350400c502c1c0b0107405c9900600c103103020283c445403903142c0901550800d088031403241c480d44c04c0c2071502c40003224405044032065 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 820860953 1250 820859703 820859731
    0xd0914010c120c090911040f0909020f0f01050702030a03020319030b0d0b091c05071104021e0315060309240127112101050a030213020703111c090e 65
    0x9550400d0250410f920300c01c0c00d00580e070500041401041c06004514212804110340d41d9080c14148014a005500074002580c50500201d0041e251104c00c0041c415048800c40010f01039500101d803544280c280003034041c005c441c0420201a00000a488130340204d038a54449110500c20440c1110607407008a40d01444840303d0501003a4031030801c0e40c024112009403070b1103080400640e000080445c0c0c80000243c40060780e07000b8446100ba10900000080b64294a054038a800c035400d03400f401103001c8060400040490100e5a4980f0b98210000020f015151a8600403c800b44c407401a1020300d00386440c040c9941468a0140520701d05032112404040c010031103211540c2d140c1c034100d8900380c1195548000100f9403842800240200e0500e802c1d0b074101000300d0f4146071a010b60103a00181c06400000b0081c801a0360f603103500107030800d400d40010b84038402400c0440315980c50803204c03403d90040002464443c0903039044001e50410513180e0426260307542a059900e19011540310114103a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 820862203 1250 820860953 820860977
    0xe011a0d0f0821010302033a030f11030105042403060203040206040518090f060c0703032f071406220203010b0a1e0503030f0712090b0d0914010c 64
    0x19041d0307203400190252800b60304040d00400b2204091240c01c2000d488646824010021031034104103881c2481c20300c1500146a08881410700c16260303100b00c16a200d400c0002e00f9095051203903210030f800c400d14200c14021030301c042c01c05080d00c0e4003e000301405542040d10701c000300c2c0250044011003403101c803c40800d60745192039120081d0409401241d00040410000030281d0758500521450b55802c160140d05090404096192001d0b50451400700c0c2c00c41c004014109225905842c2c0c43c1e5010b08001c1501c080c0c0302170b80c0210350000408410300304520080002d1821303808028101c41e92152401c240040c0d41c1d4030728540c0d140b104440c3c13000d00640c4101103140100c02e0013030341035a00c0d1010300003107444000d440c0010b41c3c1e8400c80c1c00150880140d42e50f0090303040c4246c2600c000902041d0081c3d890000e072108aa415481001405070980440301c1c2c10548040c4600c131f144005000c41c1030300c50384820405941c81c0103409580c5045c3c841030300d40603c62500348030620980c441414507440e20141c01e42 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 820863309 1106 820862203 820862213
    0x20a0f020a0b0106050a03060902030f0103050d09050f120f0d021f091104020703210c0806013204080609010501030201170c0a0819020a030e011a0d 65
    0x1c420360303108010502e00d800c09030540d00c0f130389091759a0f8504850140c0240c4004d80c0040c0881d4800810032080c8000e03200c010f4180c902c0780040c2e524070142c07c0e1084820042900440d9401421300c03004082c940741c4052003600201010090301d1944007105502c50601109004c45c401507080106148140c0721001c4890381824544032003000303001980c1d01d030b100040f22200007143c00781e0350000786035003494018519100e1034408903070070140940c10b00300881c020342410300c1c208001c103003d480803e41640c0100105100088620480111000c24480c00028901070f0103102044103400c01020400c80824000140329030203440000c14a54514400140304400c0e1300108521980301c107042c8003150020004960b201384680c0f4003464141c4841c1901c111000035000404140e505c001258549990140c020020032071010008101380c104aa9200c07031039008444400f540f0040c1c40982c000011 = true := by decide +kernel

theorem cover : BRFrame.Cov 820683453 820863309 := by
  have h0 := BRFrame.cov_init 820683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 820683453 ≤ n) (h2 : n < 820863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
