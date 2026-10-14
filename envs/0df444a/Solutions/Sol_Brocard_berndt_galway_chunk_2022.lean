-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2022
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:28:19.905997+00:00
-- url     : https://prove2.me/submissions/671b830f-6bc8-4c0a-9572-0769dca3fdbc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 363489208 ≤ n < 363669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 363490458 1250 363489208 363489233
    0x6030b0a0506090106141603080114040b060306062104051c0e03060103021c050601080303060a060c0f170409050a0914010e121c050903120603030319020d0207021804 73
    0x1520001c014034101640020040307881803280740100200c8101c011000304581045440703141e440302e941405c0300000c0c680517000100911a901c0d422803c0680c2c203509080c14010300c0210301c0000c18862840c3d451004004098205514400b100304010349111021811074000c030340a107000d00300030400850171b5841049110400b0f001101040102011f01d04240c03000220340781501c1d4111104a240007030700340301c00795030920035038040d081d4400c110000500c12404002580101e10a880011209480790010703030f81d5200050000345102100703103400000c1082c4465410034091401441480c203569002d040080e01ca09550542c16540c0d921016820490f0255101891180101c020710a0030942c84082e900c07140c010749808240940003800403290b0043d403400c480c0f0f02086010401c854100b080580d656508802c03030200b46040c500303000c10000c1c580082668070030204510ba1748110040030a840d0065000000c0c10607805401f40700b00c500503607075001e6035800c0f0b4100038001c40c881d00e000e060400d10000d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 363491708 1250 363490458 363490471
    0x92c010b0708040501031d0321060d0302070e1f0602010b011b02060306090705040515070b100807140303070c0b220b160507120b010f0609140405190f06030b 69
    0x20040080041c906000f550b0072a07100b4200001e242c5526400c0f01d140c106513100c4184103010016a99504080196200c0006404210510f0b4a0f5440c00300f0b000068810050180160388460401c020f40c50400080317541c805081d1074501500c44070ba9040744211b81c2590801c80140c0d440b0840c5825550b03000e08500483c1d80301078060403070f04407a600840c80c0c0e88800b03800b46009904000010380203d000380e08031402820050040d60217100d00d40c1c2c1c1941960450601143c0094020000c6034032221368800400984110070094540149840c403009080c8800c9a0140e4050000340001000b141c2406d02a500900c81014403594842c0c60b0441d4802a04009400c242029111a01071280102c03a5050ba60040d280300002042150030f070800600d40f0446070b00040340113002e0309055080242941c0250b0403a82010085414076450307a40694800c80070f4001d030034030394074403804c43c0c84d00d4a0240c10440d00320100030742c80080000d0b00c03a01e8074141c0d103518100c181099100d4000700100306802107242d50052 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 363492958 1250 363491708 363491729
    0x50d0810060f0c0c051224060913032105070e0901060509040b03010f1109090109090b0a020714100209120102030f040609051c030501030c0806160807092c01 69
    0x40c28003101400c94806180700c4010000c41c10521420408080702c0b030400703000004c0100146010030365206a9441f020410b09110103125080c0500c800200c50100b40241802030400000c1d40c0c0ba9240507044268110041d010020040007690064041140c2404494820b01001c14685003000d00a00507400c0441124042c01c0400010000594044299085001c04036408686010028006405804601b5004943d01e00d0448044095a5158002e01d0100c8041e254403a00c1daa0b81d02d40c10301265450b50016165581d10000a0035187c01a4003c00c01c043c4a00e01006030742d992842c11504e040441c00415505c1907000604004602c0e0400e04500c16801e144025480c601c5c002c101a10050001f820007401140c4500341d890030400103103e440e504074001c0417143c1c0e0007000071500801070704082c40b056988400304000403843c2d5a011844a102d0300388000391a020014042d070449072880024091410000d1107640400c1c54100003c201c603144504221000318014a114243c8a0030b03010303403050780da50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 363494208 1250 363492958 363492991
    0xa1115030f060a17060703020310031a040b010e2e2105010501090605030c040b01030b0d08040f060903050d0804140307080d0b0907020a2918010b030f0c040e0f0a050d08 74
    0x7000000b01d65a06c0700342031a0258036901c0d107050066070201c490302f00a02c0e003400050340c0401505500031036441a0301400e480c06080c0d903501012000341d44152211306032424812038038815442070040f5109401030084c508210982e544200954a043d001410644140a02480e00034400240515809050b88410402c011490000020355a404140340b2a004a46450b020034041e80640d00406450b034014100b07620200341c51a254503a03034010f01450b08050203030b443c003041e0184541098400c2c3d9600c9002400210f90740481501d04580090040300d403c14401032204000a05001030240345110710f42d03454076a0b81000c00c40d07042d1040c00544a014510000030044050790010b4002c0389150003e51160342d6600045816001000907107008181207600b0f0180140c1d405103007000004881020700070000d8010100c201601d561002422084550008180d003005e85031540c803c91071480000b084a846e40d141d40d52007420544103041c00d0320380340c00ca03100f181c03100703604101c1a40d4007030400700a01c0c4c48d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 363495458 1250 363494208 363494249
    0x110117070c0b2d1f0506180a0906090b03061e0c0d020d05010b0c0f0a030909020c070503010e010c1403040b070818010e0106080c040e0a1115030f060a 66
    0x40d5206280050403060309030780801c4540101841c2e82c0318400e00b266010845150500c60440c000c541926001c1c50403070b80011141c00c1c1c4d07042d00f8414050301d40c002c3c1494600700c0340c0103045d02640c202108450b4018002d8400003130144061290000400840d400800c040d004501010b040c01801031507400d55241104c6c400109807041c140b41948000e0021025440c2e0b00d0740345c0c1003402030140315a10961180341400208010740b40300d01074499504a00c08903481d0959900c0745644400034000c0040100d90442400c2c8040e02d00354002d48560b1880000300c407515503a42e0002401d5402581c0c80c42c10f103954410500c0c180c907a1118604103143c0214000d145142420381e00e00304c84960040010082104000100390444610034001c001030b50814000d00008400c2c04480307000700704e2480f4580e164429170007005000d04060041c0d00c030010f1000041d00050004c0c0d2182e481040c2d8110002e6480b1030500320341007082114030042c0d80580c081140d80801c501d801420310007141084e8001044c4103080c00180c408 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 363496708 1250 363495458 363495467
    0x1030e03041505030709120807061a150a0201090512041d150415031202011d0c011b0c0b0f1809040b07202e0b0d11011b11011707 57
    0x48890072403a0040c2d40f0b580b400c4085644a246c3d030440480d03070115032044001d00035800050314680e8001d1108108404c92142810b501101003070072950080c1e010f08031000710030080710151103810769600000c01e000240355541420017a01c1c03662030003004030114090104030030500009038407108010031001c183c02c05002c0c54140f00e030301602c2180b140e52030b08500c0940341c810f0302411000b5030f80304500004144d03445902034003808440e0140800f5006014120340b82c81c1c000a00a1f00281040e191003440841da55070205110080700810b40e01e005c8440380011f21844803200400d03460700780d0b9100340c0c0c989400710320340c0c1d180c20f18030322003244500020814070011400c61005c103608120709041010b0880304e5010030521403803d920248030b2030300840c070f0000c1c01003103c0311028004c4030040c05081900420f07296610101c40d1080d812540286260b0000300025180c10410040c0310030505005000b401050740c0c03449101da412900710b51440e1604044582943c010402d40480d41e80030405c0d512a14040390000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 363497958 1250 363496708 363496739
    0xb0301020319092303070303050a0b060d1512051e01110f13090203130204050115050a210c0906081b03160c020d03020d020f030a120203041a1501030e0304 68
    0x340b999545865031002c010681444940040313113004091424401c03940015125000b219082c1c0c003182c1028005a410300e62403003030f107600b21802842c140c105840b290450000b000d44c0a00d08180007501c100c041850301001008141c2288110010001c0440d03d00401e8a1244d20526071100742c2c1c14500c2030103004c103656050b5041050003119a544403040101280502c0f0025801000014400428449414201c00c13034018118000d80302401680d0380ea0320010f140340d4000d080140041c01c140126030240b44510030b1060346c600500c40032403c0c001088980d404880700c04103d000440d42981c82004490380161125601681a042d00d400341a0170f0040342105100007000504500b60030b60381c402d0341e240551101c4c4156900070b42003016515891401958032000c0308410000f610805002320300c003090010840724542c5440e0340b003050000c4a481d441002e50405841160b03c240031b80c40b0340100c00c5a4007161886034962915648c0000114070001d41202c48070900191681c10402080c8044404221443d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 363499208 1250 363497958 363498001
    0x905031f140f06150717071b06030c080105030a150b1503010806010501090509071b02061b011512020916181409060909060414070807090e010b03010203 67
    0x40158210000c003500604100c032040e0055694035040c0310002c482c1a10107486100140c5401901a2510a1000f158040c41000411030a50000c4446850804d5806400032074440c210107124482c0c180040b828802c03041e0003000000740d40c0c00300895920750200140340100025006450448001d450342040b02d428000080060760b00c800001c2c00a484004880307080d0f4000095540e00c0b075031181c4c1041d07200c000c01e10801d4005446480d010446290042c40c15015151985405a82503020310b0307409000a4180c03c1640c0c02401404115018a02c1108034001c0400d2003000140b604001075101428000e1900b2108044501d44d013400016165008041d40060710324a401c0600080810704880c4801a40391030b111000340d05100185107546180c0c84400700004982d54070041c0e44003414001c806108982d00e06460b1311142c045004030705000509025440d0071019580d40641342c4d00f243d86010100d5002c1081c00365560b136540303041c010038840e045040400703c000b5840c0d414550f280005107288480701 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 363500458 1250 363499208 363499243
    0x2100305010506092215030507080606130c02030d091101200d03150503031912141302030c032401050301020304030e1023091809280606080c010f090503 67
    0x6a1881d4007806040c074111050040700b444084140b41103849a1b05c0d040c07000300c0e06440b8120000c80e0100002c51140e1084001a0000103480220200000a80354032a560019808100208006030b4400e00812000030b004040c201c102c0751f00c4200044c11016451640e00a00020298030f641044010400d00100f4000b807030040307005080301c403045043e89030f1a4003a40d03146c0300004640c0382005020f8880340c0e0090b03035601c541c141c49405040042c00c1d5150a408a06c501e20300000140c5803c0142480c0c0d06081d0000c0e040300c012070068000b09241009549001b204084007401c48809041b03098800d60151100368020b509600309654060070030341424121500c103181101420303250381c1c031401d00010a00e803644481070b00c0361525a5100e11991001503490b0084e0310f6842d0f01c4202d451416070340e070f000c1d04040b001004c502c00da461144a0103041c45d0180080401400c1c0080042005809440301406071400035166070f44000e0005007130703038030881c0d40c040c00d204600004000329a0082814640c00c400c4041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 363501708 1250 363500458 363500479
    0x130b03150f16020c0a060f080a06060f1101021e0306100e131e2306030a020a03030509060913020c01230708040204020c030c0715110a080706090f0f0210030501050609 73
    0x20241c0c180340c01030b8440758004004c4500059070b07e6200e0085c4048009030748030360034240c0b40e800000b030075120315001d000c0120340900f00950b00c8900c140e11140040e41400001410310204110a406d0400c02d90301c1840741007408420f1201c10b140c02c00f080c845c2c0c080c00d070611140c9000102c02044958110b0080c460b450399540c50001d082400c1c4029903104002c1841d41000080c0c4c405031644032000c03107001505101116000010300c64140000c1d40c0d00c2040e00144803036801d626596040710968000d0040e550230443c24092203200d40c8130100c0c038008a142c45880580c40c0c56045000500319030101510b8070b01003480e10919225181199400c90300304203c1d150004a81c3d40f0740c00410080d110b103c1c5103510718400040c40c49100d960105112095506400003400842c280140840f06041c0c422207100440c1c229040d100001840e440007400e50501c500e4000c00d5880d81922a2461428058000e03038a02e000a5051001c61404040040c800740040c00c00b00442d50401c070200340c0078024620b017940591186078 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 363502958 1250 363501708 363501751
    0x70e01051302070f050a0501140708040b070306080a0b3408090a02100f020706090f05010c02150304080706050c040f260610030c0e1b0a030902130b03150f 68
    0x40443d0201c1d81c114105080100061400d40c0c0c0c0c0728a180030a95242d440c0c20811044007540c1028a8007840c019500d6103042d899039102d01c101258050210003e0543d144000a07100e00284801d09410703002c0c03242061640750401c0b030b180c00900240c1d88803c07800c0240d46059503800280b030900c0350700506031a0407861661541c42c55072030400a41c401950182844084900090340804800a04000380e03082d185050341e5800255001c40050240000491103403100344055480384050422490005080324003141c3d5480c01080c00c1e60080d5015121448002031420a05c655401440d802001c0759420301c0c60b00f460504000406080341c000c222044408800421401210442c040040059002591900e0811044000c015100c510084600200c84070000030204800b2000074420b07104c0c0c480da18420b070011103500032a80c0c080026a418950303107030310190260701c4102d50030380400e054140010f0b054100c0700c00c05151001200e00050018078520403c4001c50038100700c0f40c3c11440702400040058a1300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 363504208 1250 363502958 363502961
    0xb01090b0c1002040312110a0201121a040207030924021005040326150a1202330405010e030c010212180301020d020a03060608070203040e04030504051306031202070e010513 76
    0x842d0855030a002050110a00420041540360400152250a01c4020141d0400c0d21064080c0c0c1c082d002c1049018410703000a1150003500340d50f407030846802d500051010000341242c01001c800c0d00002c0003d5014000501d81c00c0952030340b0a0700e0f080000c941d90300703020002d68552051101c02106510785020608140c00ba41c3c95074440da0780e00300114074020781c400d802c6903180421155100541c40d500e0101c440c1d401c10030b1a13030f811f640700300c3c0b6402e10083c030781d03020b00451103001517440599030901403012000a028070f68280c00042c0602c80030707130f42d1498440010000d0140134595407081d000079440441b16078000948800007210b130030a50b900e954002d8810000304444690b007680650000a400005038281e0340103010320f6006803010000365454100845440078221152009039000f007009010340c0103168480c1e0b90142c802d02d0a58601501c0354007098a041d0b2100c007540109494940c180b00b000501e0760704c20410306951006284991802d42e50000e950810312490b4020200c03640c11500302c2c3d526 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 363505458 1250 363504208 363504223
    0x71112030c0c04051b0d05070e0a0e0108060a020a0516060f1104090e0a020303030f0c040f060810061404060e03070306141905010311040f2a0201050a0b01090b0c 71
    0x90059945840300103800d03644400c0c0c0400c2c01885245020300080e0040c41d10002d041001440812150409503005080f03c001c00c400b414003020701607001000305d117030383d20008a4005014070b0981400305516202c1000e00d00315000c3c0c10750b400700b03005100c0c21030026030003010342d84020511b81d42e0400751b111604004000300ba10009808080341450600110080c0840003001100c0d07114504106580e8400745250300c3d45442c03480207508d5001000411026502039001d540c10090b405411803820b661800b82c1480591581c0c003482c08144807004000000b80360140c0380004202032b043c502d00d8031001a0840c100d501c2580075510501042d40f03118078480d10100032440141da48000c0400582e81c41290366094904200d5007a144c101da1000740c440040807034010581220703481160782c1201601102004080e00a6203070010b803403603440c52119100f1402a40c80b800d0703c250860b514090740107840e002803e4500050100c0ca1340d90410a030704c459640d000c40680c044922000e9501d4071042d5070300c0ba0a090002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 363506708 1250 363505458 363505489
    0xd0b150a0e01140403080403290a0903080604060e07141b060103210801091a0307140f010c0c0902030c040b0a030c08150d290c03040b01080a080711 65
    0x200418021800c41e0000301c40c540c2120240c0300c03280340c20380d644400034091296000040540e02c0c00e010800004409250815902c0c2e021130303120100314515000400480c1085035448115600c0710303200001d041e00200e41130303004801500c09105160608040c410318034405054201081900000750103460800020741301102214840140701e5840050326903510b000038041600d00302030000b0144c1640c00045091000070b08144c98050f41c40c0e103000031990050039000e070320740e00000d44000c541c826940d040c0205406413050b80740e0310824800400a00c285c039244018130b0b40c14052003400c94004546480c0181046540c2c500c4056aa80d035500c44414507030080e03a014040600300401d2030341c0c2d41d03605038020202104090b55902d10a07039034942c070074040003007607084150004c050034121404510920400e032185070514808c81010207200f4000e074a03100b42280e0392410703808044248010002100b4001d80107003a40d00040904001c1903c54428512900300d00400405091840a034251162a19040d680302d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 363507958 1250 363506708 363506749
    0x12020a06050a060e0c070317040201140703020d120204031106071b03030804060f05061014090a03080301170303040816170301080610090e2802041b0207050d080d0b 72
    0x800000042c05042c0a0080d00e03120031012002600b02c500e0042540c0200d9016601c000e80328480058508003c100038005174100031090344a4454451040010b240c0c0c94440e0b4000c000c2e0900e00d0034024103403c0f550a040301001e00400040020901d0b0322a0301098290403940b107940d0742002d15000da0070b05498030380403818020305480081030503080341c8181e04c0360b03000b00e0003070000031200007a58003115011200964007006600355030f8a002d12030381080f50b011042c0005145002660300002d50552041da000315141c0c4400401404800d91180601c00405000c60095043d030410342e07900c070f60720b0240280400b109108800301c10709003c6090008086c04050090703844d5a543c6510280e0f4644500311161260840da1402c0000c422a40f44038450f4801c86480107044540c0b102c98680c1011304491003180c2c50b0417000c0800e9005030781c443c4500d0740001c0344060480003141034180042d08104140c0e1089110b441d105c0518001719883d281215100c260070080040ca85241c040040c0002a110600002c0300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 363509208 1250 363507958 363507961
    0x30f0f090307140f041814070e0a0c0c0f02040e01020412060e0703050c0111150a020d0c140a0c0501060918021e0108010506092d240409020912030c03030a0c05070b0412020a0605 78
    0x1f080120f420001d661000d04130401b00c2d9104d106071015103c401804500240c0c1940344100800c1440314543c0300907200800103e038011940110500b684c010b6001440c03d801d100c12408100641031040d5070410817644081d0050520b5611600d40720056034080c1c5d0305000e03103460711044009051141546120300040e07900807a0070160407080003504844084000e0702c0c41c20005400b1a8066007da040403201c8100051030141d1040c012500341b1240c801c1128590340300c101c00300e144469802071108081c0c80015005608105004104209500c95103520781d444000c180104587d0b0f01c0318242e030640314196101d90780c481c80100031410030484e52000410fa42e09115007402c1c514480003000d044488200c032009031070300c1010141d503102009010039446c035810400c000c2110708459006003810000007840221f8454100c03889604582c0b11703444003410340d00000b041100c01e9849120b45080400145000ca08080070b40c1c1e10b17980406800b41c0050007050301003002c040303818401c0001000240c5c0c804800d120f035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 363510458 1250 363509208 363509243
    0x1030b0c13030b071d09060d11060c0f06040314040f0b1b03071103010f1112060a031212060611030a030f020f271f0809030f0f090307140f0418 63
    0x540b1103080756510741c84103e012a00c0706150001156000c0c500043c4030341e210708056030b1040180345051010940ac4032052010540745401880611600303400d61000d08154a464500103160129100328844c00d4070003403006203d8141000c0c46076068401514403a55100c224008100104c800c1201030007841c4000103d2400704100d40c0b1a4510b010401e0300240440c0b04807005d04d4050340c00c41110390010380d43c10310500c281809542411900002e028044038502034898032841303200300d03104984502141d542d4100b44501c011900c104030040920b4600480010395a03018640c4a1240c1615941016100d0705401440d14103a030450b0238442c0d00c014040c0c1c3e2185108020715140d01c00b08000107074600280d885180a041201c00210510491052001d0308010341c20103a880801c00b038280c000a210910480c0b5140900d00010072041c0c00601d4030760b4030754a000c2c0801d8500406a0801d10b100222008030300255141c3c10b00e5041c64200c1103c001c1a6424010040b2100030300e0340c00082c110041c0454003030034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 363511708 1250 363510458 363510467
    0x6010b0f1c2003090a06021b0304030302061e2211060406021f020403020d0b070509130203010302030c01140d1a030703120f03050103080307110c0a030c060906020601030b0c13030b07 80
    0x24680c0484a071610031000800c070360b24060204031a901220b030015203510300020340c0e0380d00801c02c0c9203031034541c5e40c111341408002d1460354019800440c0960700c92814400c00d04030514441e16029500c0c1c80485aa150290b003049040504072086ca610591f0207901104001912015180b40380025040a441d00d907120300080d507940130b07440c06210302d074070b5140740c600c40003028021602900d401800c8001070880d141c0d5100e180400c010701c4682045000d01c151036803590b074040c0d03018002d501481c002da22941540101414086411400c0341404915440c0c2039030544108151405c42528000c0018841d04a43c240d10140c082000042c0e494010901e000c010000b10003603200402d01a95502110b104040400341d040725001e01014109100c00d0000480c62071180b9a103c20454900054417081d10415010a002e106103030400c07100741580e21010300c595644214510001c0400d07100422855165032614181e00c0030103090300f5101c26000641041a40c1c890034084000e65100101c00c41a2605540050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 363512958 1250 363511708 363511721
    0x20c0c100f031d0a0807021216050a081506100207050d0606080c0d050c091e090706140f12060a03080c0f01420b0d020408060f0906010b0f1c 62
    0xb207442d20708000180c0d24650018610303044a00c00a00d101111600d903540c0075004041e04aa0000718198454041034042c0300410100b03040c0103000611a0401e400c00c0500e2019401030800c0c0ea1020764810f0003201055074503500014195000d5848010421040342000c10540080740c101a812080000700300450f8409400ca915101c10755174008132210030030081840706040038049901400e8000303100c0c41c0980d1380742d80200c410a5141c484500c41594202000011100880d8540042508111058000510345038001d040c1199520300981000018060f010303a0f40200c20015003500026155260b4461010155410001468640d0700c9048450740c1c91541903894021365003040c950308a2010032510968042200d0002c030300f41040311100c00d888003042c07084089102c0341c006200061007140c440040c0010708409a02507511801c00c003001d481c180d00600646031a0003624204080724101007000c80c1901c10901519554022030080c00506001d440c1481c00000c81070544441e1904060b403150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 363514208 1250 363512958 363512987
    0x70b0c090301020c0a0606080706080103080c0309121b030c130506060c0105160306060e2b020a06090303090e2206110a030e1509120c0a0b15130e030409020c0c10 71
    0x21710803d130701c0d00c000275140c00e0944200c401141c0d100380140001440200540b0703090700ca0f10101c0c7e0400031443d0008230882a0900e0b00242904907031400c9190411030f0000c096100b40036001001c01c03400c07000100d280403075500d000f0804180c0d20000310790a641c03043d040760305100d000c50007844207040001c5003a05030340d002d18042001c2441c0020005100d406099082d502c0d2800808040031401c151903006032030080c102c44910003040082810300140d60312a0080c01820045d03940c00c0300030b0700703600d0060000086a046258140d5a00b000c1080701c00c08a040b00708407025100c081e0b20a239400f85007003009803640e0700c03003201d0b101000309042c1d41d49603140c1e114541e03030040d91044680c4e4074081c01d8041c842d050300b82c5030070486822000200026a40d12402856280892401c0300c80c10210360325560141d080540b8000c440c2803082341c1c0ca0340d85142015810600480d4943c08002011071800a107a0b0383c4558881c00c0740c1a500130414050003a010b018030705a2140140080388001340c1d8030f8005005100501d0350303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 363515458 1250 363514208 363514211
    0x180102011e15061e0e041509051b0301211b0312030c0f02060f180106030b090f12120a090204020c0109020102190321090c060e100c030203070b0c090301020c0a06 71
    0x500c4520501c08040342c062403101100142d01c915100320380a10f140c9030819045070b02c17581000d52aa003140140e03001440038020000d07950801c5200c484440e848102c0400150b6012f200600000400d50404040342c03008140c500030705504d5241400c0c0e070b01031500154400d00308012000052050f502918030440c03501d0b44c0c0c10002055080c8041d240c20034100c10100041c4c1c4000002000700c031100c0702070350704088900303201581c0b84030b401e42040c2960565001200c1d00071500023405003819082044131410200c5001520442c1e041444008013802240c05000c064001c4902084c02040a0b41c0400da0030341d0090419591521802050340c00780c52881d00490040c440d1000c4207100048402d5211020b07549613403403090302559410384143c05240001e1311960503a4424480b000591030009500041400e61181080c0c10700c100c6c10801c032140b907410b8150a10411081100c0000c2e0f0103c02c44000d07a510481011143d2503880b2400b405000724070000350950710001d09240c2c01540000d2502040e4030a170b40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 363516708 1250 363515458 363515501
    0xc02220e060a0e070b040b09100e03030f07110f010210020f07200a0b090f060c01020c0a0b07021501030b0c07031e09030615030203060f090c041d1011180102011e 71
    0x380c0e80080c8114403c0b1003a47c40284800d15183c42e180301072034070266403403401d0aa101c442c640024150350120f00c000d21000c03400194141045184000201c5c5410b00b15803a1500c141658000303500c9201c0400350080340340e030001d54640c1c000048400d440125402c0800d111001c0b000034051147d09462400310340c0301c0c8082c03440004e001d00d0050222000301c803000c0e103101e1100380200107000d190707007001069103401c0d5001d0107d001050b034200724203000b042c02a42c2520302e5007843e0720044d007401b0101c4c00b0640212001001400071405d8055072a40001480c00031a9a507065810125848404921041100350f400411000025884240e040560740540400c1165402543d0b5a211001e0079110094042e04010000703810040c0c0c16129035803064502c0103580800e00e81d00c0006081381c1d4082410312840740b03080c4030165140f104000d820706035008524100142c11484000b8012070003000061042c0c4440382101c8102c0364801c2d00900024048c01074058291211030b404074020f07010700252070703009488044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 363517958 1250 363516708 363516719
    0x31e010e0f09011b050f250c060e1f021c1d031603030c0305070f030206010e0708091c020708010513050d020d0c0602030a0908160b070c02220e060a0e07 67
    0x21501e21040861a144108108071144c195032940040c0c90300c040781c180c00e00010303000380f1a4081015801d45c40d000418054103031890070031030620303a68008500308020000c00241d640c503241482240740e403125101d4124030a100100301d00e81500702d11440410103c0101818120350400e54809850031078a80200d0300040d204140b41c1e036444041c003089490301c1a62410800319010b00383c0300e00b281e4000e01d4924601601501c0d034030040050410b0450043c0c0c0700000401950b251141c6450b0080c603a1b207440640341c03c01a808641c2d802449461035110b2048a16050100e0b008003d102e008144580c024800380c903040200d08080b6a40800c2070b110b0780110781404004500c049031008207243e007619281c040500c0d54440c44005e40006007541001c3da500c0c1080c03400300c1c0361640980802c1408a41d181a03808082c54001d2a0300ca010346050140003000e51001c1c01039a40e10070b0300c2c645040910740352117943c1401e000311014204091645907039010740780501c0b11111064102120117102c02046681aa9686 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 363519208 1250 363517958 363517961
    0x130c05040f05090618030304080f1608370806030102131e0b04031a0402010306090504050610080c030304030b0a0b040c050c0f060601050711012102130b0a0203090105031e010e0f0901 80
    0x707017070b628950001c100060000c0c000320090541041d50b1203c980c10054018100d10f51088403002c2980c4043e40031981100e1140356415141d100c0c0da0000f4080014281049199688161030203408184800440050700701d4400b5070540d01c46004503000e0424444d5a20302c01c82209030412112100755010100c040707030a1610307204560850b54006001051051a0040510b4410020700120304058995400094282250040c01c0c000c0340102c01804803410f2000e203900040b100ca922040b41c41d00f003590300701004d0740d022040e40c00f11380e0800ca2600151340c0c1d10100324014040c40226551040c03030b181038200c107145c2c03040c043e100480030b00e13089503681592001d400340d842c08120350341800104200030304000101e0324001c0d41c00307521040c1040c1d00f82d1010310004c0000101544030140c0410b60218258915600f035014070f10040074080c00c8140b401d009030308001c2d103d11559000c4ca0612000001041c0030041041c2c15903c40c800e060285c1000356151400600c031110140d030716079030000710032000c5001c00c04103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 363520458 1250 363519208 363519241
    0x90403020304150207030605010b180301090302100b1f030209031605030601060f0c05011b0e0a030f0b0603070f030501020703080604050f2707090c2303130c05040f050906 75
    0x1034000354185443c0c980c5038910f0442d009070000c114001c5000000000300d481c041c5901918145260681301d80c0386142c0303645409140c48000b4402c0c1e06100b07000e00030980100b015241c9441c9034001260187e820303004544020b0702401d00e0403406009594070070745581d05601034000001e08506070754401c14100e01d100d0659803a40541c0f5855004503004004680c0a820309034990001410558101c1d552602c0301402c40d0003078808903d00c04c13490700c1c40300f90b159030000030900e031194125030720103505095407509a00d040c1071040c0200301d03501d401e01080c841c1c1d804000501c01084281c2000d548191a40b034414041e411a02c000c40c0440c2d680c0c00881c0e52840c1034020188680b40c4c80301070300d480d07a640d40011000000350101c1011000b02041d404c600d104e5081c04000e02400c200c0c100810030004441005000f0303038642d8501203207800102c0301d0303401521000c8100c9800030081040110051518240140c5c99022079001591042ca8040001000c1324660003246c030600c851400c2e9222035595502002c131a81c507 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 363521708 1250 363520458 363520463
    0x60215090c010305041a040c0303090609061e0912050102120f04080712091706040b0f130f03090b0325020606060a08040f0c120c050105090604030605040f08030a0b010306050904 78
    0x41011944150751180d405198170138091000e000c1b88a81c4151581c1d241c2c01c05860a54501a103448284103064221440384002d1800340f9201e10f500d480d21000031300ca90740400c0d03110110751107071500c2248940b1860450000e031910413102410740c090351805600030350111116039504d50703156000810880d5180c4c556031140c2d030001102c0d840c00c81107649011004103440f1580c1d0602c00c40311000710350303501c000802c0d55118690000804075410541400c0d003004c0f8005003510034000340e003800c1028500c690032841001552099860740c01c0801783c036081c2e4403200103400c5148241170220030480d91028541c07281c07090200032000a6400f507001d04040303880b88030884280d03400c1801005030031005071007001680c0e401406549002803038481661451810801d60380715514003090380e01441d0a00c6130000d07813400281405d08265113841d0032100403071018019848040c198030b540b0b80005080c4008d81d500c48603a0390340020f84a41d02d2404801d842c0003000c1003120140003e103030100200e62418016002406281c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 363522958 1250 363521708 363521713
    0xb0d0f1109091312020c0301050901060609061101020403050613020f010c03140903070e0a09050d0f1e0e04091209061409060304050a081204350d060b04080706021509 73
    0x810091101c041e0700905250310489141c96400007141c080c13803404000040702e901070030103042d60b0001c00d401c1d40c501405000071130349890707010400d06802c15410b2003110014108402c2d064181d41c2c0c0303240240035590010300303140100c0080061201d05042003251581c070032509203030b441c462600110f4440f20ba00900801242480b10f100c086c81000c00040e0042110080032500202c2d1542c2107112a81c0060303413520012615030102100308407052205401000091034404034650840400a210300d00d240c2c100ca810284a10b107911046108002c0c41c400c2d604c0142c0144130700001860002c04400e0808802c60000310f0b010004203107103100c2c40d1380c20711041c001c101d010704006c40784003004403e92001d00b080300d05201d010700c030310700050321640179144140394040900202c1c5810300340621440d60325541c905904500c09000800c18030070300440000b00d2501030045480d10345400c8a10003c000e250400d55458101080004503c5000200e840c15625294285c070031080c1c0c0100d200881c400151030560b07554 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 363524208 1250 363522958 363522967
    0xc03030129131701090c08060124020a0f110405040308010608010b0c030f0a09080a06020c060c25031809061a03060a09050a091e060e0f03160c08070b0d0f11 69
    0x201060b0b0f5011484944400082e405d506941c1d0000c01003a65844868250811401084240c411048902c12a254810b18900404401c0b50094981e43d0400000f000d8901c14040d690500c0035000b102038010030083c200700711030b0609013000b80040909100340400030b041e0500120315a058a411360f10001071510046091240c901215000d80d00980194402c120711101e001800c1501000203901050040400507075920341d401602c1d0800c04024a824500c1d0400c01c43c180019215541c5418103d14001c81d40044400514003200c00041910a08518a510705404600c0310b207107510001c203e4180a100300c500b145030761210100d5010403503020b50f01c01403525041002524540205a000100380e0000440442350343c1e5248c00301d142021103203010385140416108000051041d4100c40c000840141244021030b4800d540e607100b070200c0d140c54134000d08008810030445c0d0712504081c00840d03058440d03c03512505034030151380080d4107010040782000a203c50607240340c480c8660302c81000845a01d1f1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 363525458 1250 363524208 363524219
    0x2f1b360705030f06032e150b130e010302100809010902040c2703030813030e04150e071403060d02060f0a08100e13033002030a1104120303110c0303012913 68
    0x486c20b0b4101800b9058036502c0752003411040c00d1144001e0702c00114004d0300e0b03aa08001d5104804510382080740442c03003410040c40541d440d05c640c8212a0041d01e000c0d806a41d0300200f80307007d0b1502c044000c0d085814906102c1d541a0003a96040130014074000503051555600e1921080e024107200160215240001041c9200102c1100350800c034040c1c1071403000011003230046001c4405442c080c400101c002d00f0107000910305900e0850300503a03103103810410391340c424a648201d8403003c2d14440c4213440e9100c0200841d19132f0303c1030f00e00306020040d00a4450281c190082d00b0000d044402004e960480500441c0511403401c2d090300078189031280c05818005d541e0182e5020b21500304600848001031400024007a1184040c490020079250158882c10506010001c0c1c99062945985e1884103100034082c050304e020702c60140c00c0c0c1524010440f140c00c1c1d617510159103d807901b20b03c120301001002040a800c49401600321800c074109110005083c03c2c040780040c001c40800915400031503030300b0800e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 363526708 1250 363525458 363525523
    0x60108060307030f0c032003061801060f03060b090108030a0507060f110a1d100c290103060204030b0106030207021f2f1b360705030f0603 61
    0x500280c040e040700c0a054407500c90710070b0b08410034803c580c0f02c0c40141d8188200701403401140060106610540c003c0c0415074006601c40b08000c0c2003400803020300b903001d031615400b5003041004051040c0d510900c1c9489081c480040d004c844c480c3d60240000c40000624481c00004032802c903000c66076480d003801402d40d42c5101071322169551600680d11850001c4000c81100010710694039680c94400500c180008108202d84090545601ca1030041e0041454140c000b50203100d01031b44000d81d60000d10182800b4044030b52440c0258001d0440da070004020040c0c25802071041c3c074042c801c0221140c0c0c0ea0a011010784c8100f080081d040302c101002c45604903480b10189840c85142c0c14034400e0f645040d0035405030145030600145104485000c18121030609002c2c1c0c404100080a1020301100604003250a000d280100070310550000c4500d080c1c480c1c2031020100c1451180ca10402843c104000028a20b0704151400c0c00309134418008100d45150000d0b880c8900840311582050070401c3c0030000c030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 363527958 1250 363526708 363526711
    0x30105091503030d1a01110111070b18030705100501090209062703010516080906040201270815060910150320041706010807030c090203090a0f0b0711011103060108 72
    0x150188802c0c080c440000700c1c58052030328071100005c103d02c0c0c403840600c00140404012403861440d03907d4281c1181103084040704480394107804c040702107402e455800c44001e4084c1450040d07c0240400b140c840c0c01c2200208084842042c0000305125a90f21503144108910810495544c0064104460111041302d844807154030490814060141d45022000c42d01b9548211000d40620b207a810a0a50454000e0b45c10307600414030000402c081d103010b50020306505e0403c50108803050818211040300c0300e00c10854030240609409403650180603450590400e04195501032045030f00d00c000401e15401e5915400454606402886640c00500b805500402103a15141c240f10320035900000c00c0d010500050004042c19821810070303910302000242001c0c01a04031190a41083d2000c10200b42d2142100f010b0f9100341400507600c0d00d802c806503180010285004105d00620382c1044140200c820300c0502c5043d498a0703583e0404080c4040a08031510140c0ba5090000c050000c10490351007500810b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 363529208 1250 363527958 363528001
    0xf0312020109020a0e1803040b0304020d0c12060c03060503030310090f02040504020f04030204061505190c050f060a060603021e0d060b040e0a1404050a12021c0801080d020303010509 80
    0x40c969042d6004102d00d415643c015110b41c1c954a0b0502890510f40e08007860b59502c076002a5042904211491805100142c4068822605520302509200c41841010000d145035481c1d84e1900c1000d02c3d24030050300315241d514020a10306080003034030342800b1007101e2191083e00705480c45035041c03001440007052200d01038103605609002c041960380b264802055100d43c4ca5002d5030311940b0310310400055a14640103400c100d02014041001c440d0444240c4000ca8440c0700100d98261505400b02c1e224481c0800241c1144a18402c3d240806030102e4024028020b40e102130047e01c0d156501601a4860f8000910305040c45055500c00c3d444050b002d821503800c41d035400f1038229a2850300e100035030003a4100c514090b0800084c045851518403070581034003130080d01c0410919191300e81d10b44a45c8407603800f41a02c071010340403080b054030911000010705000c1c4078580c0c0307800003c48001c060010034002c0107490700c50180101c410b0fa0000090307138100c0d0780007040554103680d455944912000840d0a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 363530458 1250 363529208 363529211
    0x10815061611040e0c040e0307030815010e1f0f0e0604170a0f081903060e04020402090d0b1501080603010608212502090a05090d110705030105010e1608010f03120201 73
    0x300095542c0c0c1c0c000c510740f0090000080035003c003040100811102009107d0109520400116000035088256640e1209010a416480c500c03141d0068486814542c41d45600010050302c00c081002a40b17100180400c8564481642004007841030302e44251141045030301050610040200c000c501c03445803140102c02c000d85005541c01c1e50307925511707807103224115801800410018011003031514001051406450305201c03152401103040046000580082d0240d6000244070340c16855a4a02080b400c1e888941e400c56880d01203410311070307080b03071446a42c00100b850002c5121840c4c140200c00c00e03640d0040151070384250007e044441e0350000354521508d10014400e114601180da00d4100442580c0c4e400d0741e014031110720400c404441d0040c10700802724070741002c1c030000c0381d070005004070740100500b00541844104040785181c001c150740500e07859824140007044089110302d0941c024040c1c02d641020191030101c090390146000d01a00c440ca078200003080002c01c4509280c4030020425000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 363531708 1250 363530458 363530483
    0x516030c0f0b18030708040603090602090d050c010f0216090b0a12150609180206030703090813140d1101050310150c0512071e2d020108150616 63
    0x441d031000452526003a9440c2c07100504004000f03808002c44008407042401842ca0720220765208a05c50003140100800c05640f2502c601c20001c8982c121040d4100050594515210314a043c9642e20107002582d8002225111240e5840c2e000052079101d020840302d1035410142441c101d00001d19803020910b500502102c0300060400c5440380101000340501081081c051103080c0107429075029500052240d8540a0305000300d030082c270711250b4180d90484c0c91555a8803503000c102c001e04800c00018244100000701303c65144411141d0f107085501c10404420003000c49005c00180d803d000038090f004680307040c0c1d00429984148000c541c03103039103203002c0c40e80103450f4202c076602e90091112003000724070000821400d00c0820000020400e0540102c17a1820800b55104001505c84e541c241c09211048e0038200104142c079885490b02e144042c20701c2103c20314500d1a080b60041e90241a4045000302022030840e00d000d0724420744660000d03100914010044056030103540241c403080d61020103011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 363532958 1250 363531708 363531713
    0x50f070f0c03020d06020c160501050720040c020a020f0a0f090207020112020705160e10062f16090504020603040f0318080705040608010c020718090c0f08060f0105010516030c 77
    0x3402c00010a015120050300c7d00c0500c05203d00d4110044401080c07148000310810150b07a00a040b11060303035000c504002400d80c4031700c448503e40c0010440ac1d034854103004501210a5000852030301c010b0088441406280d625020b120070700c80d460080c18900e2500300e00900c04000f4a8000785402031061502c03da144107402e04100880c1c100e4102100c403900045290b04016000c03080c03e0016100740071b0081c4803400e264588a1000d4581d22410040c005c1c5000514414080350200d00c00700c691003c101d060040c41c0100258507800f20b41200d01c8032440481000c214105548185032182d9805841c103451510360703858218a82e0f0015208408002c224030700c206030b251300704030310781e00900782e0400a01d0200d04100801094a446030084911a031508200703000065000501c5c0c8221a0410050102d40c0302d40f00e4040081c0400c0c41d0060f103224601040040ca0740d003c3c2084004880e0401d09403069a218a0148102c81d0420710400380010000c0c850031144408604501c0318a500c6401d02461000869 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 363534208 1250 363532958 363532969
    0x607110c0a03230c09330a05011d030715230307140705010f0f0c0206060d0b060303070b0f161806121404060504140609030703030c090503010f0e0d050f070f0c0302 72
    0x4550000c0911034451114000c20307040c0c0e86008205c031400c001b800d0101c6070540800d01440c40c40c851365041044e41c01d8041440c0c200410450300b411030241c240e404903929034404034610703070204041000017541003102035000048404600014542c0d444103c0c40c5031250041198050840550325028030310030002100068824454030064441450001c00d64540c00c0681c202140d160309003110964101000708000d507a20258051096a80118411465110704022900d1801041c000600300d000328014000c100020700d1104d4071480d00b01c10000c0d413603900c03403030202c83d030300b6017003000c0609800703c01818080c10740031f184600c11030595040002035440401d401c60150704820340b4151000384c0d440007400f040c803620403134010740018244010003d5040000700b096030ba114400002e17040607616080459803074860018030004004c018000d00101c80820360340c5000b800030301700c824100d20405450b81a03084c0a602030b103512031200c4900a0402801303840b40340c100840c0d02d00c00c8856a2102c40040010f80d9039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 363535458 1250 363534208 363534211
    0x705120a05040518040b01051c060906020f0309010504020a09110901030509010e10061a1e0904090b0711060106080606040302042003071707021c030209120607110c0a03230c09 77
    0x803145451301030a1904161485c5001038004a025103410313030241c0340e807901510710a080303694400c40c000352420300d500307240c00280a403000303604406d9000014013400c0c0f081500150b008a000302c0706182d071a13039503014a00031144c090070b060a81c0401400844202d41c0251b00c0640d00a01c40400411a48104030705103003130140020902c00c4041c0e0300c0100380300d50502d408585c0000340c8094900c40c50680303410010410722501040070040500001103003025034945030040165541e22403400c041034104070402500070912907022000c584143e4000184591041c0c50460250001a250350719080c2541c007440301601804043d90500100c105000760f28034422802548541d419070358101c440841c3e8030f0074010706036000e03190004542c080100040e01030208104161744d840c4506005a44040913804544c41084004110415008120411680541040e1840c038070a0400c401d4519044504007045800261404068907034401c0d0051042025518494a40300300c82100c12980404007180008100030030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 363536708 1250 363535458 363535489
    0xf010c021f020c1c030b030a1a0a0c0e011101110c0a031404142b030302090103241203090e0412110c090a15030209040b0114060705120a050405 63
    0x4032401c0c0301c80382804009a002801210300081d4a855012482156200c00b5400b13003042400010556100d407a0003580980413803200541650700c000035606084c1003131040101e010001410200c00102c508120b032003030220726022034903040c0300320009200441e817007584a80d14207286d660300c62420000e4614000070340219002c00d001020000d102c1e14000341032515601d020051100103110a020079070700e100250031f62a00507100a43e02100700d0402e00000c20f020018180103510410164040c5517040d0018075007940f081e201441039a04584440b44a82001400351034a00703039404d4113000c0c28011140c0d1004090181ca407407560a41ca07480c5c00c88205a007a141118801010321203240f03600d8114280e18201d21104010340215002640031400d000320080106607015502c0d080848402001080c0201a680142c14140c00c0d1600b0700d4200306615082c01103c20200080c8103003078951511500f1900401e42c414040c1c600c501c03000200321044d800c85100b14060103018000490181c940110060440a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 363537958 1250 363536708 363536713
    0x5180a03141201140307061706040c260a0506180a0b0a17100c0504060e0d031209030503010504110a17060f060a021b030102040501020a02090c12010b07050d08060906120f010c02 78
    0x10604c81007515200442d4421340c00d01087c0c801c0791000d8542c0181e010750011051740c01040741000c81900300c0e80c0c110602e0201e008000b03404101582c5500741d50001c0d10900410008001070340300e100c1000017988882519030200144000000e034594000c2d004031010714405010f0790310716a140c0528840c0355140c00480c1416900c0100c100d200b803082d82c090010f42c02c0325803c105141c141000780041200c8d45000c642c0d80a6466445014205440340513500b000c51840f80c001c0003d04030501d00107005500c00c3c86520f105d01c1c03c03da848041800d110007251158051900c071045100361000c1482a02c1c003000b0040d69008020000036000c5480712001488481c415501516110000b801050241c60181200320b000780c1c23040c0401d2080342d0f000038a4504182d0115a580c8240c0c1e41c00c2c0c00510144500e4032505501c2c1220000024403401c04409091558440c405032180448a0003007250107010803583c15038082c000c44041921070034140d42c00f83c0602c036280c0aa4a041840303075001404e49140041400060303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 363539208 1250 363537958 363537989
    0x7060f0204120b07080103020907110f070906031112030405190510030b040507091415040504020d021c020a09120807022d010509090f090f070b0405010305180a03141201 74
    0x200c3c2124a680c0703c01942000c1c80594156000302d4080c00307005200806202a9410456403070a00300468000707421000125400c885e00c41340725901410a82c402210f98489842c4a042c3d18601a000e010440703010000071401c044ca094100a0000058866994000500c4201043c01d40b506c50b140062100c40352808641e0359240c070107210403120020015001c00c181c80405010682c0ca80741c035280d40110460b0004c00c4c1d80c0d44141145172074803444d44482c0d4018800510310203001e50070b401500c0e51680c0200744000d5210003000541c20303841018203140c00160711078024451102c4903030103a104240108600360610101341d01240c6801041e0160070111120825201011100c0d43d10104c9081002e1800340c1c10444011b01103500c5410144c40d400c40c0784000000164002d408204c030000861008080300d20055440000010550003401001c1c002414140022a070f4401003407080e01e84c4030350700002c18903241d6580b01251030010140c07442c00011401c0101ca10188500340401c0c1c043c00350900404042e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 363540458 1250 363539208 363539213
    0x20c0627030c0718090c090b040e07032a0b0d020a0c02040c200d0e0d060e0d030207050d0806010c120909020c06060a050414180c04110a080109110f07060f020412 71
    0x34240134010020703282007038018030014000340c4a00f01221f0320040c0c081811075040001402900031985082c1c03140c82200d40000c240110940c1007601d80c868412000c40e190000422140c4540d00c902030550200c00420501062944a5008000414040c513018103012100c3d4009010390340d25014600c002000b1404209540e001040c0e03030120a00860020b00c1040042070007d05841e07210b030040346c824404650014180729494000504401d40320082c0c6c0c00041103880b0190007500000c2c0240d80c94400c02426064050180b182c145c041c480503100c04159500300e54801e50000550700010040040c040800503d5508600181c00320072203c074003402d62843c0030802d0240c20480c99010505c19401c00103104100c800c0041115004490707188651400c00f00c450b4844e00d005101d1403041e402501d41140501021403c1d0090b00070b0740019602c3c102c00366aa00929029500501400281c9643c10841c2c855080c425800501c0b013a0b10400d004250841760101c0d00049801a50081d8016003484d00318804 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 363541708 1250 363540458 363540479
    0x20d0f0207021f120b06121e0906040308240a0602031e0301030f0b0c0708070f03030506030a030212090109150c051225020301140a0b010e0103020c0627030c07 70
    0x2c2c09079442d407003100640c21450002c0c91070184507501e044c001d40c1e66440303034000c1c0c88900c111140c242952903c002d190a002a510384110014104102101118004a0200800400d010340a40c1e0159a036a0045c3c0310388016807a00038000c02818551a02072425084a846130507000c03008200305d030069034507061401c48600b4010703090300040101c61002c00041c40025116000f91241c030342c110780c15841903900d43c0040301c9a4400c001f005004104040360810410603100590a0b0241c460303602401191283e1052555a011854000340540c001f441a41140c103c6140a041070400501d82540d0903566000c071101e10300d991408000c00222216400000d0040401c40d405864803801c03032403171809001070303954254141f80d4043c2c001005000c000850a40d5400d400c0001006a0f00c0e1800d035203410034280990042c0b411341501d070b01290000364103a900798040d1081c1c9080c4640c0101500071556010b480f01c614458400520b0f0b20a40c291079805441c410800140c4042c9400308002c141160400300d918a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 363542958 1250 363541708 363541729
    0x150203010e0105091e010e010623160305040306061806080d0c03030b0301060f080303090c01110d080a0605040e01062606040605040f0813050112020406051617070609060e0102030603060403080604020d0f020702 92
    0x701d080d18ac21920742928250005c0b03410f140680ba0100d00c0c00c00c014031341110742d40718651000e48500d01f00b40001c607450840f456480e440303201400303081003840e948155550b01c0e14004c0810101003103c501102003c80d000b5001258114801000010344a407075003009080d0b546e41b0b03040100594000f00812200040c1001400141c00d02428038a800c40d400c01003681c0c1d107001c03031a170350000c0114010100e040510242c01801c0603000c000c2c414400406030b008041d000342064031910700b40440e9144420001803107031111100d180c4510028081aa41d2515020301030000940101d501180c18140b1401161154000d410380d40b0303845046d580003501c0d241c0014081c500b2200c070311102ca44100000c01010383c200040304c0100d542030506680c0c800d6103003820340710007401c2225110540c1c00041d03110f00f041010340c09100c480e48035040c1001100b034000001800c07400b080b2201c6401d5804400031401090198102503400301000304003500e009003d12a03003043d205411a160f170144d8011640038114034000714080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 363544208 1250 363542958 363542987
    0x919080304090f060909140c0a051503180115090b0a060807080709090606030e06010e15010c05011b08060f120c0f010c0c080604150203010e0105091e010e0106 70
    0x150810041584901c180d204280800707603079650010a0340c0700ca4110800528410344100581e09050900d40c030b0b00d0845100f00051801403a07403000142c0f4204103004161781c03010300b0031444090b072000b00004540c00a400142d22503108400c041085009000e00c4015900031520340049500d04031060f8142ca10401c1307980d125110a44091040562042c50070340e218072546000c110030707113441100351078071080c580080110b24100b50010624070340503004440451070382401c889650faa180700b8020541d0041c2c81c1000306c8030410135400b40c0d6607c41d182e0340b031045025400008040c140300a001c10010350140400c0d010448a204200043c80d2400418024000c10307a0340f808195020512551600c803880c04241c41000301308110b040907446000050015a44140e61061031a00c030050640c0d2140200c80807207150200b60030400c8505982c2c0242e034100c0b01001c40a40050b404c01040000c0020f005015001ea4107a0b080d410700c0c8000c803507458074002c0081040c100301c00d504104000345a0528586174 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 363545458 1250 363544208 363544249
    0x1b0d03020c0c06071406040309081504080d151701050103030806180711120c01061a04060806010c060b060d0911030313030209060a031b051f0c02010c02150403050309 73
    0x41c03840319070109411941c0507044984907601c20300c5142c0351030a070700202e5000c03100303104030b6040204168014018209171000e01c01140c0f80821081d198820200c4102e5000341a02c60600004040d0107003508120202c0718031020041409440300c03040c014205108001d68151ba4580c0010000d01d5000031030190080000e68208181110b00102c100713280d4400b5100108000c0c07030f000016034080341803000319421903400702442c0c0e4681c4080c1d16a80603041c64080c25403107410a981e01110271403601c003180d080351215165007000b0768486005503520810460140c80154940061034003a5035868020700c65150041400a00324040341040030000d044100c586000e83d00c1042410300c0c0075030030001c3c2c0040b0f0b503049403403141c1c603a500f02c0440c0521190ba0300050103008140b81000101015a8006090b120203807030307401c001d10070700314114140001c86844d1000b291031920a01c016510528510001e1070019100600d0301032481c000a016601c0f50b1b01c1550580c001040965580c604500c00590140c1c0c001d03407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 363546708 1250 363545458 363545467
    0x1410020d060b030f060904030e120c090709080628060305010c0e01050f30271c1107050618011704080a27170616321b0d0302 55
    0x22030109282c00385c000c0344140900320005040501c02c51400d0104180501021058084a02ca4594941e0782414080c400c2000d41c00207242e01e842180e1500840c0c4440c001444203890b021070448041d200d04240035a0000b0300d400070040e520541c05007100551050000060062203c1e10080001d0241c5420030304008040102070b080582d92402e40704400240c01c10300c0e555848260407002d035608250b40441c40c0410758010010b110000609500c0c0062040d003115110203442d140150700d1303140d415030b17206070341a21031141d5809a101c1c0c18030140c40c1c0e17540310484422030744803c00190f0a030440745241071040d02c400c21410882d68010007102881d0030000054a1508103680c0b0032070140510000f1004000070b400c00764640701c40075040140c0c03414a21141b2820f858036000300c0c5954500d60700407000c20f0321500740804d121103240c415452601205036076010b111100b04600c004440304c030002841c003c41101045d00802c0350001c0c010319005181000009441402a48441c2042c04c1120b003001498414403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 363547958 1250 363546708 363546721
    0x8010c0801050f060d02040302043818130f0b2d162003040504140402030d080a14010e06030f0607050a0c290702010e0c03191410020d060b03 62
    0x2981d5200011080b510b060f00d0718640b04145000b07008a5001035407041c200340c15100403d100c6000004114081c5e9010054400009292f000c041403208d016030704100f903c10149004d070440c004841d01f002c11282007010851076911018080241440165080c11294040c403180c030480340303820300034179a0350031604140d01c00c95038262580d0700d4000c140c0c0c552040d80640313011025100d0300c189440700007850030410341c0c14801c044043d41c03a00107005050059203060800003c0d00c1d1034404040c82941c0c02801803d034841c12900c115034041c800340500f81e0064031510514400401204494087e003c2031703900180394a01441010719200008d025200310f40c01c124244169142d014088030002046420029102c943c6460030002c0d014030201240620304007a00f440800c03a0240c0081d50103240303107a0003480740c0050703280000e481d8944040e0035a45984030885c1540300540120205920901607101000301e614a04042c900700408a0610421143c0c0010b04040302d08080c4208000b41c460040646d09515094 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 363549208 1250 363547958 363547969
    0x11010b010207061e0903080c0a1104020f070303090311031b06010f1d070e06070f0c050307151b0f03020a0c0e07092105070618090e0a080309210408010c080105 70
    0x40001460448a145100c11075401116100d0046031f101c581d40351348410510b40142c80302c00890381110140c00185080010303162a000f0b492003e20071468503480c05d0304955056004000f1040128188013070a111000105c200744068640456849032428041e418925001c2c10b00301e05811085461200d80f9060128075840010803104059002403040c0c03640303540c8400d41c0d603820004000c56000c040013a80740304004580c50f00b000c00c4d52050a0254145840c7c40c20151504054005c0c1010910300d055020041d41c0b040d12f41c0031040c404c81c81c00d80d84c004919211524409103446041e0056481205400104a10341d20040002c0043c0c0c045c0c0300e05820100e500400e42c1d1014400d0480c102c0c821003000000c40d81c01b24001c01180d500c01c0488010340d40c0c421000e0400c1424895003940344003500000218100503004142803074030b02c0d038003825000d5203035130f240003040d00041c6c091850352140b001c02d83d03004200c080109e171716040a4480262114545603240d4251119003c21078100880c5030010052511034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 363550458 1250 363549208 363549227
    0x50705070b0c130b04080d0207050319060e060f1905090c0d0812100f1403120f0409020309061819021003180809040b0901141509090711010b01020706 66
    0x700c1080301c520b44030b80c11400154000c00100c12031081040074001011155080180101d603802d0050710b145414284003aa00c07040d82340b1407540c03d5044110046071007160b041200d03503114480c840000303c0304840c0c0350f07952a00d01d046444041c3d020024084c8400c1450200100c5032509000303000f48414035085440c1612048094103044c011a2844602010020180d00707540307030b805030300b6103a440900c0c00a00d05d074410805446208506d42145801042d0f51031816000b8040c1e490180060505140c042100c2c40c1b1544462540a50b5640a11011410000900081d80110110002048103041081082441104032031955195505c901440c5c44141e00c4020b10b1000c607a011101201a250010f00c04c1c0c001d001201c01a4204045000c07908040000741c901604003040d050300c04000074040cdc2028425020000c5c000c2d0182c40501c1300280600f881d0520782c0c0300454403031001c040c0c14080e104000c1000203c00340c07651404030714040da000b042ca240c00d118401000000348001d080d6140342c0700018107054103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 363551708 1250 363550458 363550463
    0x6010e19060309020f041401290414040209090405010506152b021603020616080112081c0908070b1501140c070e091507020102030124090b0d0b1305070507 68
    0x4030783c120802550380d081c1d0600c0800d0b901a00520400b00c404040021211b0240140c00d040e100c45030307144013a840390b40d0441d18480c40b5208440c0c686410014803900703100c01059810740c00b03a0200160001d980b24020003900441c4170340700104141c00d002c0108561914035211499502e10240f208405405080038545100c10024107024880007900b11004040c0c401c0a001b180c00140304108070040507070000b040740c892100b0301c01d40c400710b45070301134100c0700d882c820b2103001000800c130b080541c0407403107180092080540c4260701102c0c0e042e0030410328090b0b40e203032207054a01c0c080209980c414480595490383c1e001c01e800c488a0072132001d0400281c002c0c410700703810801c0761901141801e8020003c00001c8040c4c42c1c3c00507031a18031300c2c088044c20f585070314907803030030b00040c42880200351998014000e13207040e00d400391308941448008022510800a013000e15604110704070000140e00c054100043c00c1c1000700c2d410200b01c3c40000c805124003103480103624458685004100305032a54880252180c055 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 363552958 1250 363551708 363551711
    0x130c03030507020112060627121205040806181c050301060e2b05070f03030237140d020303010e0c07030c0602120601030615210e01090b06010e190603 66
    0x2d40a00041303d00700c0c114008441c420703240a01c08941d1540004024019121f0910b802c540c076400300d0718404030b4421600c614083c4207810032120000651010200b27501d042c00c1c0c034005c0d05181c1d840c02084c3c50400103a56100e01481c42c5044101207880c240941c0303800001e0440741c100c251241da140100240b00500c20202005111104c1498560381c54101074022804a100002e081100c00e43c9018906000c4c641200d9a106440c07000402d059102044070850303405401505400e4000032201c044421010100b2034041e00b50341002c0101209000541a00c6004441c0307482240c40c0004900d00d0051400d495105651080c4010442e40200d10917150340003584c00412038940d100c6140944001c410b2240050017580082040c4100300f840a000030311494099800b4440941c1d199091300046011000b1000021500740c1d0507044845002c00c0ea46d914050400c000800c1c5164030701403402c6036901c1404880200c11003052028542c1e1011881038038031303000c84491901c0310300e40b00c03034415460b098400c01c0240f6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 363554208 1250 363552958 363552967
    0x2109050c13110403060c0305010f0e040204020703090312080105030d0e06091309080a1e0f0e010f02070b12010306061e060e0402040b280212040e06030703050f15130c030305 76
    0x2803040d000081c5050b1510300b520f480703507102e02c0d140c4080c03c04600717280000380c80c04000040c41d0012242c5002203d0a1082010301034465409010195004090590500c0004080000081d00107a4035944402d06a641c0c542e00c0c0d41404100f505004a048808007004008001d038405681c40b4402c6801c000d4080359488001c03044011071501500c4007400c041c00b8101c000c65654251078200046841507005140850030081c1d0148003680c412400c607002600041240aa000180d409045011041c1138180100c2d2400d941d0345d03a40203131a074401c0301101244410640100100145c0c2e00079030300038011609400b180010210580f2055034800e1142034204949040c240000382c80d541d0485000c0c110304c2030700d031355617401e081e1561000c90b0060007c509401070b0190406100361011558000e00c3e00070083c641e00d0149005800e006480300500550b0317041c000e0090004c0000d6041000c13109206070000600001421a90107840200300108200e9214030ba0a074088002841e143e615803e0300d0781420b200303403103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 363555458 1250 363554208 363554239
    0x12020307111e2101060f080705010302031b22090b01080a0905060f1e0c0c0d03090b01050f1206180609070501051b010b0a0311030c04020c070b030414030301062109050c 74
    0x241994a29600c043e54603103940410005d0030a4104d0090700c00d2002241d405559441c0114200c1c8004c5602c1103800265050034a4a40d09140003041c0c0000b00c07461010102559a08444642c0c0701035210068245e610012000a9600704200c0c6621402101d8200320820454459a4580900412840c1c8c48041800003925440c2e01c01540500f5aa400b82c400c45245490041c1c03e0a503031151105517007500c01c484504503258881e0141701000c5070302421500d03940e4640414804202100089590b100c0f212184004020720101301c0e541c070030528605071088481511444509000c13000d05004030701d4100007070900c180c2e40c000c001c403403070b1134910f01600c22800502038120740141030030880ca59125403600000070610030181104009204110180c1c3d40241c2001c5c200401ca01c00e00e000e0790a2a00100010061a00384001541d4032074015a5102800781d1244405c5086a10036000000480e40d028009828180340503109125811680401c03c004121910b490307603646006000c0a01c1004102d041820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 363556708 1250 363555458 363555499
    0x301060e011101150603141603020904090602160c0e090a030813050f070f060e130f1e02130e1e0702030d140108060601050a080c0a0c12020307111e 65
    0x5642c440002001102485807452840c0c021900c18400020b00703016820407403002e00384415024180c0c100754202544041c0d02c00f5400382d0840501140c0c0541e5074124130f00840c0b4180024640781c14403480100107c0900d01d001f00f518206900500c2504081c44200200011300103040c080040d05418800c109070b86440101c1ca4080d202076008250b4040c110300500701e140300140100540ea050f107400d0217416114002114045280d4920a0340494100c01c041044005640306481d60302c81408046070a031310301c100c01c185a0458181810000f980041d002181c2c0031415000c60181002d141d807881ca03401c01a0025990b40c1e030b0080380c024500b0f84a40418015402003003240c810031422034061205418001c54409281000d100b460054012000012450f46c030540499043e004280c44040054075a80c03042030958118100d080c4c1800700e0390140c54046100034403001550081031340115a81c00e03c034030b00441c401c1c940070001406030742500d440311240d10b01e0003101c1d9407405090f140c4282c80c1c9415410b200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 363557958 1250 363556708 363556727
    0xf12030c0f0602070f050d230f13051203190305010303050702101e02070306060b0f0a08090a0204062c0c2d041202100512010911071205030a0b0904080301060e01 71
    0x92985e210650804204040410307510b120f089aa101c01c0c0b00a40c01002e9280312a4070340e48450b0350340f54100851208607120310041c03c280d00503622038a02183e241d80124080800e41c00354814a82d2022403480038200c8441c15241c5404003507d0305000c0e40d495603501504a00859000034851502d03008502c000350311403024403100711003886074800f502e2080c110194075114140000d030340f1542070179404580c4070010b10440700700420400c1c002d071038892440c4040b0741c8c03203102401f101001c3c01180801c4002d696140900005048000c003c032601c42060000d405864000030301c0c1c000c0c001c07082002c001402804009944401c060b07003002c82006256a146602200440300800034030030008200414400c44180108130a18800d03224010b040942d8403050301c19010301807082c5c450340d4000b40148600c50250f0442c01c810118640c105041040594035190360301d40900c1c074040012408010446482c0c3c007406600d050300d206039141080c9050075200d40307003030707106c140203403800c5c4100c0b02840702c1c050b4425500503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 363559208 1250 363557958 363557963
    0xc0f04020a0c050115082802040209190305030a0e040e120a0c0f080a02242410030507020610060518060c10060617060108070807030221010f12030c0f060207 69
    0x308a100f00100d0f03250460070140c0200206d41c45104c0c1c002c0604c0c0c0c1c200a201c00209004440764070f12416660801000e503000300c0f18550410180ba4080500320b00000496000d944210080c0d622072a1041c0c2c0149403d1407001035034032940c10008007040c60743d40440e14465000c03100032404e913101c900c5c1c0c2042d60b009a0310100180725040030380c1090180500756010b040100701c81e9003501d1500e51038459224841d600c4454000c00d0413120404039510b0100c080000421a803076110014540c0b0007240004ca0b0f4041207140c50010030b440340e0400000b15818000b4962104283d600ca034092420541c0080a9019a8006850036540d10070502c0450f96240d007610034070100101103038105126a030346140540901d11444020401d070b0742c0c031000070030005402244a49011b039a064075942c0c03032000494900c1c501400d00d00a1560070400c0e15003080c400d20701d00c0c3e00d100e0400c103102d100d54500041200301c020b079980030f400480c03192141030001070303400325010f03400d01d401200f20b0300b81c076541d0304002c0020f100e8090b00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 363560458 1250 363559208 363559211
    0x170f04120e03100608010c03090309120c030b070f03050702190818061c0f020418020a030e19030801080604032304050a0e0402010e030c03100915050705090a06020c0f04020a0c0501 79
    0x40781c02e8803c4a03003041e400e60f0355900083c0700c8410458010740585058101c01000700c1c240101c1444018a84001500b426004a2408045640d640c441080c3e0b04000e4403e08005040031201d007541c142c150280c0754100c0342c10b01c001c2c407520180322260100f80c208100002c0040d08000f46260b1188850103c00e821136038001c000344d81c0d614410913181c9042140d40b021130030703003420165070102c00710440c42645c084880d82c4c641141c15041f4109040000e40c4100c1039442415628612048211000c0124103041c95815040e42e107912594180900202070580c07010a05a00040030040000c0e03100320002004292031420154048140720a980d8034012900b0441d048800c0003000100350303120001e2140154000e80310300464808a80900d034807500303004922501980030f65002c0f4502011a03100079a0580560f03061048440b00716804402d81c0d4099454200080002c24090901e1400a4002000304010700007048207005c1d050225003125a20300ca0346d84950b0f4040313030605e600c0f80290b040c3c26945621030b00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 363561708 1250 363560458 363560473
    0xa030207241e060501021009020315161b1109060312070b19020c1f0603060911040b030d020d080c04030506190605030a081204020f150703170f04120e03 67
    0x800c080181508082c00400c14004002c03285890345912031501500c006078040d154004014400f08040c10000d6400c0380c2512801200060304d40e6281075842c00350f4a885640a80642c2400c0d0003451103101110700f101e4001210750a400040b000e0090561200d41951007124a58903800040c0c105440304c01108607180000404800300310300d001c101480b42081082484520743c5d41c00e8400100e000b150503504150380a080c1d04800c82407281030848017443d000d0008a0b62503184d662388001d9035401401203c11032950070314030703200f4907040c010000050000e400a0100650b0880003c7d074542c030204c2010280520340011498119400c41214017454001c03084904078101428501d01e81c0b03141d01c448400d5076107401c0c1301223402d18002c642600040c0d0400240350800d8010310f07891203c072101600c02c076030207940c0180710300c440d86a800c5165852180d00d00a07585a840d40d05000d40b07400141002d200110000c002000018101a541103404c5904118189442c4600d403074140c07500004080043d51610034803d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 363562958 1250 363561708 363561773
    0x40c23010e0d054603020d120b10030203040c0902030f040609051009031e0203040b0405060c0a0507060c1505100e0a09020415060311120c0d15240c080a030207 70
    0x1e0b9091040700d00c0c03500ea651200f8018048200c1309040e0008006030411040d1a5015105244403070611031040340000340d00c0040b000040100c441e011302c50001c45c0d004030400c010320a00104140c01010549015882c61511103c1001c017190014002484c0e19907c4070440c042c080c0401c60155255440ba10400c030054843c1005040c0b081c0298581903044141c40307004800901c040142d0f0200c910048015003040d09180801130140c10500200640d0302c41c0001000125908121442c000c00e2a80c550700c480ca174850a0542c01074204e2040440014100800d00c02801c4081c0c01c48011100201080d543c5501c8150610018107680c03072001e54864104817000c40c810080e0700111044415a444c10800d2001010034404d85001e0f20502030449c40d0030742c0002d071010b44020010906d0b92810100080c4990074840d0003046031806030441104d00c850078682500c1e4a040c0d41c04e02440c109141007076020018a540c2d410350340d100300c0680d0400c058011840034108010640094040381c22038014102121100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 363564208 1250 363562958 363563023
    0x20f041206180302060a110906040b0c0714010c03030b01230c0d02060603120307020709020a020c04060b0309061b0f071a0609100302012303040c23010e0d05 69
    0x4050a5039018504000070b0400c0e940140b401c4240c07a0306070040d118540e51000100c00414001d0094100070354200300d000d1990b50780400800c003a10700c1001c0c00780c0b00c1100c02d1980b480d00c58540c11114030780d02e81204d4804a0b80c0c014a400ba40c0540c10301d8007080ca03100b510012119000300041c86170120700c8100840b2030012400c0e0207040046030190031902d2440c101d1004070b81e1820700b62501d81e016007000f807101e410410620029a440403240c0102d0320060350758400035080b64018425400180c109207500f0026141c64000c00000741103500c119811824244921034a6407000b8000c1c3d0040071034a0420340c502e5070b00c08140d41c02e01e8605503181361a064581040080c00c0081c404c80d8440d0848240000c0301d61905078100ea008060f0303900c0008400d811580191205210500f09801c0d045071422100b081888960003144114400c0b04101c407800d01e0406105058500c1c03034600000080300c1110790380e450b40e100b56203500f1620215078611003440d103070501c2e6081c2000040d47c401c6c04803640a000c00c424401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 363565458 1250 363564208 363564239
    0x6170606031014011202031207030305010e01090504110112060b12011e060207060e0a0510020a05010507080601020322050306040b01170111030a1d16060201050606041a030a020f04 79
    0x280d050b01c806084180b101d20403600d24030f50102000d81d6140040c07020710403600d40703074125a1024003201e81000d0082211201c03034201c0c2200b01c00298880006209010580c0d01290060011010511031401c09545001540025440c1c0e20f040100f03002c0307003009d280c401d600400e0041a15030035150f9511402455400000002d00894088910101c0c1440b0031118891118049602e150301501100d400c003038040f2400304948030b440d40d001441303074408149940d0b0b1601e060001c01c0c43d0b40007841842e25500e01503007518030040c0b416090002d000e0403c107490f6004400c071004404002202d080c2d107140c7c1214025100c40c0c503040180c16208030001c000402c40800c1c1410b05071f4403095128054291104003040c01da4270103084141110710280302041c0d680c82140c120112030110031885d0342080fa032104603140b503c110502408102580311004002c80341c1c080c4910350304200299070452400b8142001e0a1212214200f40303210fa00e400000190a00642da040c0c4410390740c0d403840c4640e00e507610220003d42548 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 363566708 1250 363565458 363565471
    0x70b13210f0e0a0302011b030519030606020f06010f140301020f0307020a0201090801020a09050d021c03031a01110d0507140a08040303111b040e121c060f060c1104061706 75
    0x21000418034040c644030940c0f2085a605a5494100308400d41a4500703600d03640c90110103000061000c2600d0304402d080e0421340d00d0701a80c000a600d072a0940c001c2c0351412100c8500344036080000140418040300091209a4101081e02c3c1041c4038440003190091041e104051815400402800441d95021030109280c0c1d000f46d13929070310070342c466000130708034420340060401203001007404010038100306110441060000f00341c224440e0041c0800c00046c42000b60440000e0b644243c00005040400407860080c0020308c0c02504007030407013031050340e51410b440d800400d0000201d00a4100200011803038421407003501035844641e4980f6100310150031034001100410380350b0700c0750f50841e08000380c1c80c01c1030841d0940c0d0400c1d05044205000091060303110b84402406000d04850210200100814000c070011802a031203001100401040b0b031490b40006645003000c03a02045015404500500703115000700700c0304100382042d400900145101d0b0300030041c03070ba4800c4003000702200200c0c10038030520 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 363567958 1250 363566708 363566717
    0x20312033c1806070e0d06050a090c0801060308160c0503330903030601122403050c010c020306070302030a0b090403110708030406050f07020301021b0a1205070b13210f 74
    0x49a6681e0b07210b1180d0394100030081ca520080001d40800c0c8a0a02000300300c50182c840e91700c40040d51100c5060324000c8812680e400c0c4c0351481101006000d8100c2d00042c24000020040c03541155502070b818460102040001ea0192000000b4003d10940c03010081078002c0807540c040c1050350030900c0340c082054241e08203c40c4042c0c0701c03614041c541107042c07082c0000307000b56140d83c0d03440b00150740f84201050502040c40c1d8405000544461000e1f610650180d0540380c03586461a510f44070780303011421003446040000d140f1542d4010f80740014801d0308451582405600c2e035603072a43c0c030f00040040d81c403c951300000110622040c0341d0010059008800c0980540c1d84060712030365895508d1046100b9030b00014000c100d0048406d50b2900a0001940700600240c94500c8410760a038185008540403011a00902070600800c10907040a00c0246001d050044c00c0681c591150707440000c00070a18034000318081c0040040050401d00c1c010380740151034142c003003d02d02c600c00a0280007401281c0c0040b9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 363569208 1250 363567958 363567961
    0x10090c0c06050c040f0b0a14030702012708070305030c120106030f0b010c05190510090303020405101404030b0601030902100518010c050a081c0212040c05060304020312033c 76
    0x3443c40c2e40480d001d49003a0a08150414600000c960700b95100800801c2000048203841c4241400d0500450040005600100d140f144007560041c1034030b00c80012130f40603000c01000100181980044e03807507454240c201103480340e90b0451041c1841c07242030301d010108503c03c4008628141c1603444100340d0300000c0c00804c22940f0140c01503403110307034400c4003415540c0400745100324008003d00d8406c40714400e03401c1d60746908040b002070040c3c07000300c03c0440c00700f6000f141c1030005d0300f0305406d41c124540240c40c2c140c2120b101495603080a1007103010140004203030780002202c0d131740290805100e05074090702b04c01014510b000014000c1e0007020002c030600b1514001254158424600300003419082409030030850025920740600380d014001c841486402880500200e45503031028000d00d4210a01540035031805140004181e03045401042c03260a0900c1840056180092062032010402c51240c1d900d0300c0343c9404256003000340300145e00c0304890324100d205802c451121001070350540348040d0301d603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 363570458 1250 363569208 363569221
    0x70e0604031b1d0603060c03060d02150403050f0d0504090b370b0702011718060903120109230408091309050d1103070f0807060f0506030f010e1510090c0c0605 70
    0x41c0071044d00c9481d81079011102242141d2041d50003503421041c010102c940070501c9501160a14a80041480c2c03204000301e001c0040c81800e00c40c0d11803042c0c4290241c0381c2641040c03400b41041c06107004806000341d450030340d0001d5031141e10146952041a4852a07001c00c034042c16980c01360500c00d060307560001880030019002c03003441c3c155280903a0585680208142c20200722111a00051144641000100e011142800140010fa0144030402c02950b1380f006c405078a100310250692225500c0c500d84045c0b62502c01da6102c07250071202c05003220350a00d44943c146416180542d008040c0d1101d1080e5054040008981c02020700510981c1a03c205d0807204406640481070034110110a4204000086c0041c54501c080303010107200e20200c500302811900e5030021109909400d4007102e07514424810b0914041202117803c000d0361000340040380c0103500342da071a00c07e401d100c003030000042400300c9c1d00391000c40030744006825240342c10031041000030380042081c840e0304000d950715498117001c910f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 363571708 1250 363570458 363570509
    0xa0e040204051309050a0605010e04060506030706081315020c0705040b03030708040b07060204210b0906042006040902131e05030c010e04090605011509050102010212070e0604031b 79
    0x1c0b5a4020072040c54102c040c800040038100c1c1d842c044400d40a1340c0b200400141c00c9108450180100d006403c0841c9030625144080300c101500075407080c6c0c080181001800c0e80100c03002c0d80f1030f03110002421144402e00d066044003120081c01005030b03001003691105900d000855508440c006c032024440c0d46544d00030300d5268460750b10041d02403101080f05000e1048050b00800c1e247c4d228445c01071400b503503651607010550011981e100030302181e1b0700e000309004330112115013000c2c4800150005091580d6940c01810081e25140c29440602402c51410b99400090394010400c00c00c056607601503500560141c2e202a0041000d0002d800502103030b1942c0401e455026500003400030300301c0c05a02d03001500c0f803d000018142d03000d62035140080c001080c1e4000c141c002e01e861085410701c0240518054001e219640055045a00c180001e86114040501c415005880d030f0038803081ca002c20b0004243c01c0d1150350805000a40407000400c4c0308440746041c7c004540114201d8090130714000d10204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 363572958 1250 363571708 363571717
    0x1e18190b0603010b071a0408042c040219030c09020703090608090a0803042a050a14060304111203030708060102060705160209071b05011a0a0807031101090e0a020a0e0402 75
    0x3038019074203200601c1100561401064014002e43c04503002e0440308000401401c4122411600c81e9070114013001000d090740e044044400c1c0c50301103140c020103c403c2c1d2140d003560081000c0d00c43c03412012141800c1d08204100c501542d00910b507850300030389841d1410040d5200d032908900080740c0880000354503200e0000c241c02064050080c00d07205806480e007000c80d40010b0015102740c0902c65980740b02031250b00d0180001844c611188001d64900002c0060301202648400c1c0c1c03410750003013404141c0c1d8414003200e40c4242d0006448003114980000300311900c00f030014161141c8030000030f0103e043e0b000027000707100c3c01090b402c42e00d2582c0d404500b140c490140c1244500d41c40b103a00d003020018070345054820b50054107450005900b0301d1308a800300500441c0030054840380d545003214014020711041c8582c0c02002912103594142c600380c400381d0394025a210141c107940700c20b0802032042e846051040010a440d40c481011418003814a600a40c0041d1080c008120001c1060300c7c942820700940703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 363574208 1250 363572958 363572981
    0x50c03070501090e0c090901060f1103030601140315030307140f071a0901140406090905010f0503150a090606031112070308091318030810090504080403021e1819 71
    0x1188a036113802030002c40100040c101e0043e401c420700c00340ca61a100c44c0c040302e000300300306c1e034414010145541c0b01402003034102d4100c0c009a08200104490759030003011440b8003000090701c03513560ba96134140688412001e041c0580c0d040c0000100c603c2802000f54030740b1103005a4405640c0c010142001c04d0b6038840c03e52003042e41e10501c4c10034a00800381c1e8180500400320041c107080c003540149502c00010f83d4025003041000c076041c1c080074400780d1140e1142c640509245111405880e04010019503034000e09940044c012001c880052141d200070b4000850455000354144985503da180481e1280b0780d09038040d0142c10348084500d21080c000070315400b2285c10550341c5181c00848800d118082001c05c0820b481d164640612030003110464400580b00b502950300c0144504081903064030302c105a91058204c0c40c101014000481c203160100d0302242d5041f10008000490318040312403030601c04091a0f44200800b281c3c01038054003c8404d40700d021442c0403410000303507801d0707546c0c00c5588013580c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 363575458 1250 363574208 363574217
    0x2090a14040f03030e0601090606021b150715060e16021506010305060f0a0b04050a170705040207060b21060a0c0c02100c14030c0c0405090d0305150d030507050c03070501 75
    0x101d000316980000e807006080c001e01d0003180d18040d015102e0700d0310b9000c1c1c2c01213003c65a1100200304480c1d041c40030f54030001e09030706486441c4200c0070001e0754104d80107a0000407107030001044010006680080c0094034810802885015507c181116000340e007200c254184182021524000610108200103000603e483c2481aa15280700460051800a040035048500c816120b0420764400c5201401000003440f51030307585051400b4808048203d0780024400350131044803041d8080003148001c146d440c1954010307141c8826007410005800500e4500350008001c5c0603d82d403c500726200a140b020a002c05c441058a8a6610b00e040b200010598000280c94141800c01450f0626880d01031131101e140400000300c003a29a4159100b0000703101c210b50b440003505464044040c000d0480701103080b01c04102ca0b20b42032070b0003a1220a5282a1020180c0d07130f000044102c005110031115215001c1c0c801102c001061501602d40d901030700b002d40b00c0c1c2c0301e007902c0c20070180340014841080e9070060b0344 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 363576708 1250 363575458 363575461
    0x50d0201231503030d090809030d05090607030e13090b060a061407020f1915021c090e0a111c110717030a0605090708060108161b0309050d080702090a14 67
    0x1501450b1100c280c0115030600040021040304e920078003407811454001c08000c0d60f5000c0c03140415281050300f0b0415000c1c080c080c041d0354070b5540d035101612051501030030242c03601c1c10603e0000b8001840d86103000b500d81d140549000030320203135130080d6200e810b0a5900389030040d103c10081d5004a8211a00310850004200a50040c1040740040d11015005049802075109401c00c0051f05c1035140c0020000301c6041d00d00d502255030400001c0000b604180482190700d0040500a21001d42806090344c00f6000c0d9012407526002c90384444800e440b003e04064490504114482440b6006011410441d00741259040c00550420488070310550204880700000e81680f900002e50700014416000a95134520005e62626003001591095480d6a902c0381d00d4501740700094001480940790701440c10b2510155100142c010031085410340617803500310b501c5002842d04840c5072005421243e0400000500082001b8150001c0d04480f0702c01c81d20032425985034001d0004603100b0600ca41c07480c808000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 363577958 1250 363576708 363576721
    0x210030c05040506032a0310120206090306070f0f0201110d09020a0e01090f0c3f0f02040807060c1a06040b03010c020f19020a150e0a03050d020123 65
    0x80c4021000ea003641029070800e6503a50004009400481d408071810903000305c01514014070170a40c05401c8141c41c007180c01c5003092401198400f0050190303201100b04448040c00390f6507140e055801c1e20394010121812890300c048000c02034400c3e03250420120b410359510711032007030040c0148035500090790801030500740c8220400c0080c1051010503038000ca82034401040041146c8240f03070290003500e5000c1a0170412103020b1007102d0001c107030380c4104619203540345200344900703140003201d02044400251480101101ea00d05240c0c0d0001d00588038a00807000040f801690060030496a40300c082e03a504595a80041e6402c0308482d100038003400034005020f011001025050741c20540142c00002d40c4040c00f00480e01b180d003021044400741c1d00c18a08501a64010030640c0c0d1050070724404503001e04d040e64003041520409004004010300b049030400900351041480303104201c002030404d00304590383e0401c43c0d103500f100c0d0308010040d404c00800d401031404c210210750100001408001d003030340c0c912 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 363579208 1250 363577958 363577961
    0x30c0306010c0c080c0a060c0809040c0e04020d09020a090c120213030c0b0318190807060e0a0c1701020310060507020a09050720061e04030c12090303110703021003 72
    0xc01140c1401034150300103012a500049a0001c0c0074440c0090080c00711200400c40c1400c0c07594042000c201c82c240c400d40009440d00c098402120b419500412901d500c9202540d0100c101c403082a00a44040f0f810900400c4903000368090b40c2c000d840c100203d41d10b5800780002e403400303041d070b05002c64450401201c03910002c0d801405405c0940d440a04029103a6031003c0341200346606c0b1131002000401408001150004190803028040380244032b0f5030301c10307440016441c2c01c0b11809844490081141402d001ca250029200080c1c03000903903000c2006845c0c020f540101354041c100107030703020011094a85005108a80c019421121031080003840d1080844031603006070000c88c0c00540b5000d0020b0f8400300c0b030013403d0290910b501c0d09d00859050315004007468100d080140a580e01000c00c0c00305c034002c2500c006929110340762500a40e41c0d210b05083d200c10300603c1008114030070b2221400341c810360201030340302541c1c801d81d601c4260781d5007034a1203582c03005280030207948000f0201040140c940603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 363580458 1250 363579208 363579211
    0x9140a0509100b070b011e0810020901120908030714030f0c072102100b0303041a09031f05060109090e3d09020f0a0f23040e150c0f030c03 61
    0x2207045440c015403507100c40c0f5060342150360103d68180031180180844001010400c0d141440000c8142d5924a4020b49503654142130243d0300740b05600080035155640f050320036100001048202307020780d03205440c203c4080c2d441101c101c0005811440c139610010702d18812039003d01e44070201101c02e0713210358009122560201400f1509075043c1c045400a0400d180d1104084505540141040384140d01080041c0c0310f400001c1440b80d0810001400740d08640c0c1c0021040103140c0c8119915402030780042031505060995190303401c01e0100c02c117000f10300d540d08114802c0a00703a03a81c10459035240351100139256503a805080c0364202e209000c01d8881030f224100130400c00c56400f003142c103079010f0188020140e0300c40c0641801381c450f0005800c2d400c0c032980181d1003110699201c03600628110041a4888880c05001d1002c4c483d500315104040d0758040c54417039a14014420041c150210b064117039141b07d400f041030b8503c01e181000995485901064900394020400b025185d035070350703500c5001980d10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 363581708 1250 363580458 363580471
    0x908060403030f0902190501080a06180b0d200f090c1204050c0a1404050906190b0303190e030d050903120304050f0706022503020f10020a14070609140a0509 69
    0x9a0380251805a41c40050341b0701c441612850441d0b0107800e0400050995200401403600642003c07800c0000c2441205401900c02c00c1140000c0e00c007070040c3c00506203040251000d0084da0b00d40c642000b100450014183e100c50003100c45503001418201802241070003140ca03d0381d9810103002c40081d4951802c001d03a0311038880d40980340017903007880014941c402e858001500c00d0f0103a25011100d401c00e4800d80b40c0144000005001b149401ca24818198028801c14100c0383c0e140c0721303007103925141042a5119020242202070302e120051034018000040203000360701c40d104000c1807144650180003160002c102c00341c0681162421250032031440d07807020300103e0300c83c400c0701048503c40d002407180501611203a4003404180c03e210441c1640945101405883c0c569401c000300300603070b00c14007511000c0d04c06450310301d03004c940034a00b80d043c841054000f402400c550310b5a1014440c0206120094407a03644400754415110f41c01140300348618000c1982191840308103010300d103060b4050b580d02c02e1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 363582958 1250 363581708 363581711
    0x1a09010c06060305010e0d020f032b06030507060e012309040207110d051c0212030703050c0904060b190302070b1b070503180a0b130303110f1507020106060908060403030f 75
    0x50fa80d5981d5800c48880e80c2ca1000e054202c14070003014139505109110300c4004a030019420505c00c004d045100b842100559911030044810881124045401c5000119044419500e100303580d40c60150002002140450009480400c00703d03481d5500c00c03040620403610306100d418840c0120611000f54030004056600c081e40180b80b003001d90301c039209416498458400383c05a8011151408829030905c004401590414440300c240320301d10700c05480e40f00c50340745400301d0075031191b030b00304541c3e8850035001503045810110086050f082d62002003440c00c100c004030014203180700e0000c40c1240161840102440040000b01d030040d80000d40c44200b01c1d02d08921640307030205540d155807850f400394180003501000200140d50b9403402c40f40f000010a07270290306901d800b55007041f28040e2820342c04000d0038400c5110030741e02400b00411008040900303c104442800401c0f411208034040b04958003401507007070203070104400380f04802180481d0752030002050366403101d59098010342040d040040c0c41c01d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 363584208 1250 363582958 363582971
    0x130312021b01061503051b090603131a0708310503190c1110080f150604031b08010b01020d1211030c0304031d0a031704030503130e011a09010c06 64
    0x10002803140da0000c026503010302d04c0380000e40d08050705450001704605409880c0c1080c100c4807212000855424241c202d50750742d500da43e03030b1414440030204110060b02e81014000d4401903d50310441d1140261050b032901c04a03960b5010782c2059003e1074440b0021519a4001c502452000003420380880612070300c196401c0808290f64070380e1049a20b0241800a040080c294051186c1d0310200f040344035090300c00b0030599201401c090a42100078003a01c620185d03d0f40051540d21110240d200c030400f000b0409940e95542c1e0504001064581c98625050b4100910004007642c0c1445400c03003007803068000c1c22800030300b1a400d5544160f0040c650702d000b61a03010094152110900462040005120316500d074141401c0040891022210000126103101401185075546006600c116603001c01e6241500a1084444541e070245900040c40c46c4030206114158161510b01700003981e81141502c03045a0b680d6640c1d4054184003007198101d5071080046000313951150320114940b601030700010491 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 363585458 1250 363584208 363584257
    0x307060509070f06032304020a03240e011812050c060a141605031807180e0f060f01031101210209040c11030a0c14030d0506010813031202 61
    0x159882100c4041c80d580108000380901d0507070a00080180c4010b2074200851500c004003171030103d0740b060700c0407454800c80300040c0c11950340f44040c0c0041e5034800e010044031a0081070701095407100804c01841c103810300a4400910605101c0c101003525101401e5a103002542c0fa03041c203003460040b41c401003020401c0444442c280030085030340280740900c00001c2e40140411794400118001e000d4002c0b02d114240305a030301c7c9510900f039036003101414100d02d010080d10f6a8007407a10400d03602c14052200341c04000c20755100d070740e80304801d00440101652041c044ca0004a43c952400710342d00c03150101040010b001040c0045e10f848035444041c106034140c420014801c0a60010281a2040b1950001420b200508141c000c0380382a403864100090005088041d058507801809524010414640d080400748a0751001c0e140040b115a401e1369600c8481c00300c000c01600044a807580801c001c000418180001c2c0000d41e02c07500d1b0156111230311381015a00c1c2d00c020b5840164440c0c0c81810700c1899040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 363586708 1250 363585458 363585461
    0x90504030512160804150f1401050909030c1203180a051e01020a2c18070e0f1804050c060a08090f0307170304020121050a0b031b0111030706 62
    0x950081e110591540107a41030401d020074020b02d101124010025a5400d590300048100d402680c400030800c40c0c5030810003004018000305842c0340e00142000d2100b00300940043c51306044e58400d4912000941e56040183c3d034906c07591071003001d140d100030208540b40e1002d9003d1900419240104014840c1e0054102c0c541541c1020030f6819070096805010700c07415a00c0c500714070015010080d800c1c1204518090404544d840101070720746c400048195400280c465614100c9000500e010b0744040c450005101c00702c000c568010110f0588000d40c0540d1500041d40b580798be50044c40080040880c0720400c507082d030301400440e00d91040030b03078000141e03030760b00041d1141c0390301c0e541c50300064501728000600c0e240c0c0034820130304550001c0142d1404110030904608030400c6241c034050307882d152440122000c02c2c024041e00300e0400051829039451a407500300780c8c0103e0320440c0078081c13040603030308041c0ca800520b90540c44907000031036540700329400f40a00e126000e500b0010703242003280a468400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 363587958 1250 363586708 363586711
    0x209030318060912010c09081b040203090f01020403080406080603060613020702010c1401091b030308010303111f0f1d1011090405070201060317070c06120e070b1b010e070905100905 80
    0x281d94654082c6040161f1022900d001010001d008003401c40d2542400e0508401c801d40b540d0046800100051030a07404100452422035100000c56640f540c0f820320035900c3d00107003d054005600000451507611740054a14014440200441e0902d062149012f0096102d418200d0500c2182d04444001c00c008110342c040c42480c46001080303c201c0340c5458220080c5610114941c424840001e20110790702c88003080c10340c1d07407500340041e04503880c0d04018a445598100180505c0040c3c0a4648072101a04090050710111009100d10016540c5d1540444400c0981700101c0c2e01540d442c01140415400c0f01304c55020203014a460000200d020070142c88040b81c1c0c11015039100e15007042003210801c0180301c040e03e020342d643d04090550b07a901500c1041403046804112003290701c0280c1c0c1c42e0b0307940000a007a1080088402190b0b5958a0007510f41003d04007440600c0c0a20500840020602a800c00c17001100d0251a0160405260328010100036090114451180e48041040d194907c20740d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 363589208 1250 363587958 363587989
    0x280204050424020f18010c0b070914010806180c09060d0203100b0c0a0f020f03010525050405010801120c05030a03091401170f07030f02040b0304050f0102090303180609 74
    0xc1464210158040c0600c45400c0c40200c501071040020310891601d04c0700b617820141c0b415402100020010004899090304000064403140c40c032014001d41b00d4101081c041181c85201d18070b9600c07000e0707900545007414102c5401d900411a0070043c5298030032081c43c80d0f8051500201d441c144544040070500a40260300d11200241d0b0000a02c481d0b8086400010300074055007103640d10b0105e10404a07030707c5a10100f4000c00039442c0301610340171965001c0c07454441e1000a030080144d40385c03403020054006200184202c00401c42c0302080e001034890b0302218251070041e110b00d4041d91030403c0343c0e402510130040c20b82d0802c10101c3c001c00c0310350b800c1c48000c0344280a0341c0c0e01c05040d800c11055078659111001c400c1c0c180000144410801c40c47c0071301142c0d0281403100c981c3c411baa42c1c228150003802d40358107000001c2d4800a400b0610211441c080c6015900807000c4035070704282504d809080303118a214840d40b607070050001141da4107024458041da2240a000f039810503100c200411710000600500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 363590458 1250 363589208 363589223
    0x5010906060f081b072d02060724020a0203070b070e0a1701091212050c07020f011101110a111002040806011a0c010609050402040b150d2301030c050102070b03092802040504 76
    0x1c40442242c420f401b142c02c84200c06001c080d0801a0b00054442c464048001c1004c1a0b402c0043c01174010300c2c030002c0c06441d03644010f6544004810009440b580490401c80f1158140f4000c989050711a0515a00500c00a01012807580c141240f42008000b0300000103069074903403101400282c1c14210705e200f941d07190303141c0c0105c0c8400c1070522815194001c15a440c0d0722403c0c45024050f9882d000e013412070180a0920b05004080c46601c140504280402c0290302140080d9003122a3b07444480d40001c240741c1801c0d503058130410071214080c1d1056200303221441d4046030052050f02c0311080500946146880c20501d800d071800301003801d640e640d5211340030381640c640811040d804c03c0e02840104860498803c0c4600b5814070758015103000d00d848030500c0640e140b281d02404a0489072078242800003001400c81076039240381035000080c242c01450300501a580002600b00d280501742d80c05041040c01030b1000807480c0c607455100d900642800030303031401e90b4112316005d41c07614031549002e075014205 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 363591708 1250 363590458 363590483
    0x40b0a030b01062a240e0c04180b040303270602031012030906210207050708190b060f010c2f01020d0203120406021306030c0305010906060f081b07 65
    0x40c00e030940340007601484c04002d122421501c419065020f510590000030845030420302c2e0b4000044910041e10b07a460036240144040d005480040c51188204048906100624001c00c5005503040302c400000d09a03c60301740480c0002e0f000340c008606404070a2980301c0e60941c412030b0050307030803c01c0c0d0007522215400014402c4080c4884008009040e00000344000d002c115680103100003094400c038400c019800b81c07450b4600c100036044034841f40d4052011b544414141c2010390b101c510501c1a5483c0748074482d1850a00c94a0031143e540ba260080d000e101e103540d030901400300c007a1081c204281000b0f0f8665840740007542400c50312400124072002c030f50103400c14410141c116044412030364159840700d44013551031a400402c4502401607030070320801d0b48d1910314040d1f020b03000d0107110780f4050b0310b480000300d51b40c4c2e85584800800c200c40d903414041039a850070100100c07a01030040034001504010804609402440d005402154084400000420a03007481015030884402118420074070710 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 363592958 1250 363591708 363591719
    0xc0b10030506100305030304031d0301090803150904021e0f0406081b2d04091208070801090203040b010302010f09030b2707050105031305010209030d08011d040308070e040b0a030b01 80
    0x10860381e00065000c18100c003e42503440d840e07502c1c08001c000400300301100800d0720303106000c40020b1422050107030083c0000500781c0741102c40c1d03420495a45201c2c1d4401c4049442c1807a080304654022074014140700004541c616084800d080060032103a0000a00c04014151307031a14030441d402010681c018140440044400c0301c4142c98140c1202d214141820896540c4805a45000b04655080381c01004c000011004500980340400d00500014190780c4414607032600004098810845642d60080680e01c0710150412800140d0f0042d0256201c0707401803006501440181c90b504c00e050900c1d0790b00a5032a07403a8010110704588140c210304005081036005c80851284640c01ea0500015103980360070031000070668040200000d8207070000410b20014410300b0741c111064000040c0640f07c82c0c0742e81610143c2000b03030a00ca0703a85808401d14003e1344151601c001503000329070640c2c40300701985030403000700c076450031110200d81d1003030703803100811490fa48501c14507001f184540e02c1800e5561411 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 363594208 1250 363592958 363592963
    0x60207021c02030705010f2015010602070305060420150415030b0306060105090d060204080724021e150112060b010c050601050607080d1806060b0f0f0a0c0b100305 72
    0x10781030380322807000040c440300141c0c0d003c624081a40c80070300e05100340d04c14041c4c0031502800b28500c0031610100d03001e54030542c090041404500d0304940e191110090b60b882000300c0c0c0d10491444040d050b6009607010400003900d01e04400c0f140b0155414200003001e9000008024911801030a100700e040003408100c2e1381403101703803850b4101c20b60504004003204540132a845800c010527242c1000000100740600b42d54004c503010301550000c00454440d51101c0566603282c00314001d00640358954401010094030381d4800703800b5070b00709038040d01b107400d0002090460440548010070b500d00544094001d03105002d8013203402402c1344000c1041ca0011801c00c00c0c01c0f10040302c4250304000440e108800840c4e030002d4660304590041e00e92a5980040d420078600a010340f41c484880c0f1424004080c003140c404400030a4090700840c41044656a901400d02c1c1d40d01c81e0f6954100828401e000350107840140b400600010385480c103000815400c00d541d03884210f1012680348a41031162034080c41840000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 363595458 1250 363594208 363594229
    0x9030d08060405010b090d110303120f040201020717101512030909110301060f0f0302070c0e060103111903090602130e040605090a1523090f0c09010302010c0201080405011806020702 80
    0x3c0c0d0541c6c501040080850012158110013400c080c07021000c45070281c034100112600c071041060741886500b00764400c0703041150141c40c1a030040c858080082207145680d00c0404001c000c00d402810180b24282c07852001d048007010402c2a021040340000b10383e01004c040d512214420342d10802040d00300411071040303e035610241080c040041c0014031040c0d81181042c4c414070b00c41e0508000c0713228882001c5011788200b4100402c429181c0800107a0320703034490010760042000341c0781444000680b88081c4428014081c190070020794020080134000d0103070780310001c5140204805442c090032402c400400b001154040000f6103a41420882440400c0c82180d41024041c0007400007103400340c907402c2023690082c030103056055481c0f160400d51140507040040c1900310383c1e1043c156242401745242c40b002411102030260082c021a556a4900b01d90038a059950503114141c494446400440e05214028800c440c0796684483c10030308031345101401d40105115a901603070b590210f1051248c40d503074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 363596708 1250 363595458 363595469
    0x8031009060f061b1e0f03020c0102061b0c0127030914060304060b0423100602010905070e100b0708130509061e060d020d06060905150d1109030d0806040501 69
    0xc2c4038900340300c425070140b40c10078100820b0300400d001c1042c60030080c101151041c122120610401d4900c800c10144011154015001c3d8098680d80311442e801a030b2980c804440314120a00703847c6401032801c0d0b500300504240c03245c8200002c1c0d607a840c0c0100704461040d404004401d40002c3c0c03200c01c00c240d8050b1440d0b015010244903c00c102c1e4054011800c6804080c100034070080d01c0d07071112145500c80d40c1c8a4444001002c402c049246140c2d00001c0c10140c00741e40d050100368002c400415003a0050060b54180386e402001810304603d4400b0f00c19807010050121080c0325262500001d0084d80600a8104180200c000c5661002c000841c41c2d1340051070f0b071203a07005414880800c03030b180c0c0d2460a030786a800000e03104202c40140701c0b800204144510031004500907c00300d9119000a40d9078046000d0300d90b507403120041039442d0020405520040c1280b80a40e0301c042040700c00b107501e107070410480c0c480556110307410080000d001900f00000c1060076000217108008010180c9440c1c001d1a00615 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 363597958 1250 363596708 363596729
    0x19051506100504050105180d121202040e0a050901060305070608071701050d030c030210020a1106060d12120b10030f0f18290f070e09060a0e060d0803100906 69
    0xc000600107400c43c0607504c41d4905020000c6052142440c1040708020200d5006080101d441c40521301800789690041100d00001c600f002500c09001c00b030320854007962124201a0701c0761307a460103800e0203814001d140d0b0b1003d540b00c03040000020010070003080580100d0301ca0794a00e00c2e00240007400803101c0e50f440c465040b050300041140d501c4180d01e45000035014603200c00c90840c141401d0b0f00c0c01307200c0942d803200607100140300241d441d4015201035030750341440250b69864a51008004c100c84101c40c3c003514400f060103c0c0350113a4000d60050510b4054410301040380401c0e03800144a500c1d659000703002280d241d071014000d00d1428414181080141401040a203c40115112100ca4605d0004040c5030a1704840042c600c040711014031803081805500c141850100502000036000743c1d0f80d200443c901c01c440a05601d004441c4034421000074020a880702e2a00900402443c0702800c4150003115070300c1d0201c003146562000b54810001c04080c848080d10340000401201d0850344148201c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 363599208 1250 363597958 363597979
    0x705011b09030f14100b03011a1c0c0911030f07020106240e04060305030909102907050607020606010908120a030e1218010905010512040b070219051506 67
    0x580c00407440000d07280c004420b00c01003906841d080c1400119414248034911a01e840c80350303805410b41180700c42403010f80080c00700c0c003a80102c0100302d15800150540c8000310070340e0300002e02040c123104800b0ba4082c0d100e42c0c07426560383c01c01070300f21110309501d00c80d014400800c210b103001e81d00742c0c265008003030b520003003000074078040b02d00d00034400342498001c00c00c607840d401e180c005102c0c3c0b41d1900950002401004843d40e00d1804503940c0d40b00030f05c001d000741b52040c0080d00144d200c4e40810f00310b6440c0c034441b980c1100020403034014038000c07840850424805025540210300c041003118031454a41d002070605081400014040140660025115900521740665110704080c140c0d0610350040c100420320010251540d0300703000c41107040b40e90f20000441c4601881c0948460301750301000a0301c3d1041107684074801102c0c10b206180803100e111100e2008070300051004003400d6132201c100d106445103024003d00760030002070f088100340c465601181900e10028030800318075030403040464660061 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 363600458 1250 363599208 363599261
    0x2070212030901120209011709060702010c050a08190204080102030f01030b0a0c021002030621010606030501050f0d110a0b0f1206120601171f051b04080709150801050705070501 78
    0x40703040c0c50084005045d00412101a680d004001c040030b13008610191039406d00c1c10b00341c800d580e61000c0780e481006600300a800002c65015200700c0d00d0089043d0354200741c0365106d1018002d14803007000c00c45001035080000040d800400c1c405540115540e42511643d0751560070a01c0b542c1c000503045008091420002c1000c1c01d03000901e001e0926182e081c09600c940d03807100000c0070801461509451520b4050079800d04140640c17241c020713107000d6141040644d8030748013400780d80c0010b00d91180d01b240c428140c41c8081443c916524103100d0006024851042e125524225186c205250701d079100c1c42e001c11801ea80458140c0e03e00c0d07001e0016160503864041d880c0840b80d5414040c4603c2500341c5a8802490801c10240044c6402d0b640b800d400d0340700204010b40c003000505040703e280702e82451450070481c1100018044a007116105001840c0e01e42c2418080030060000081c0d250205003806030004032880e00b8040c1c0c5201c0c8416459481d01c40c902c1e421300c642940d8034000704607240199003841401c0f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 363601708 1250 363600458 363600467
    0x70201030f1e1d07082817070606150905010837060b0a05040e13020102100e0106030f05071e05090417070213060635130b0106020102070212030901 65
    0xd07071241c0800003007070310200741000044042c1c04091000c054000d005001c1940c08001035078046201c040f90781441b584258000c1031365030b8000d00000400c6924005c90600035400940040d00c00d150081c1c1c0000380182d600c540c03100b8021010f030414000310341c4001c8200001d41e0803880c5294001640c006036240130b0341d030303907191940c0328011003418175198200d184200c0d642400703502c100046c00c0e0005517603543c0c1d0000f150107091034015100381002c43c0340110000b14240502900221a25410f0f0000e003542010000c182d400350148030b480c49102d40d60340c2000004a581d900c54080400d0150004d41062401d000c41c2200811940b0000c0407c00482c03881040301d038560300c0c0001d0344950400c3d00482c21411552043c21603104031480654894080c5142803070080040d4054000c449480d100c08407240c4603900700303040c407842d480c85007131404c0f50b1000061a030000b11102654001d0300380350b49a01c1c009541d580c01c0c041341d40030303042500140c0d408504a0b0440c00e02404040080d0a440011420b081d6040002031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 363602958 1250 363601708 363601751
    0x60c031106100f1403210c0105040c0509060f01020d03181a0a05090607050406231306080109090809040504020a080601181a0f010c060b060403030e041505090f0c130803070201030f 79
    0x71b504c0966040043c000d52080c0705070717160080c01344024009800c09003000d514121290080c3c62050040c540400c105190865107207080c914183c010380054440307444281c0080001c003007200001003c42c0380031400a8119000f200c066000740145460310705090a040c41187d40041c9841d5882e80701e041845502c5803c08182c408440c0701e40b40080214600202800140300f00c11814100e211000c166034903641d85100003034041d111b140d038a54810307aa03103500110960790310110103807048008104990090038507030040d07680a030001c2c1c501440030341d80300c2c241313071405600341e10003a4505104103c802c4645440d000303440d408403681c60400324180c0e003000000d50942c0b91408140c14003265080d4601084059084080101c1005004079111075881c24043c1043c240d00c200d00b8401c41c505503214002000c40754a40c000c0d540003a0031411b950b40c4c6c802011000036800307800784690042c140106c81401c00c50700c0540c4044e000300c001854540800340b0003d02030743d400580b000d0051b0b003800329002c0008102010304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 363604208 1250 363602958 363602983
    0xd05090715050f0304050106090903110105100506160602041a0a11070e0f09010621170408120f09040504240606081302011202040e040b0a02070804060c031106100f1403 74
    0x29681c0e81ca0703e00e032980c01003050364802795225050110700350905803c950700003020a4818001e020315a6801100c21a00580e80203159100704103010030304540c040d0029607450244a244018585901d80c02362008001c00b80720000600c0000056012807540d1144500b40360001c074a00030132660381006224881e07048024042e0f90324401c40c10000e0080e5000750480720081c8805201c04ca10148050a01d54000003210003e42c0d46104000c400a500c2e0b10355811a41240c882a01400244a100807082c0f1550b0110482102c944402e1040401d240c2d554801e003406039108a036810b000d411440c2d105000c0d0404544041407141c9000c02c2007100a401c02620383d8040341c41c1c00c0c0d560060040b032006070b0700c1c2a40d0900040300a80b0101300811189006080c0030f001c2c1d03008a8101ca919994020140103901c80d4100042809500307100800034103004200d0413507007134440d00b80644181340201020340351510458a590821741d107044100314500145000030050300c0c1d4501510301e401003200c080707603403281d980a50 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 363605458 1250 363604208 363604237
    0x18050310090807020406121a010b0703050a0c1a070e0901140d03020a1401020913050403020c01030b0a031a0a200d0c03091b14030d02060c070f05070602010b130509100509010b060d0509071505 84
    0x30301001d10321440142c480168071401400e491105840110701c100c0e000c451c85c0c00030417040345402280c0e181c50440b0718101ca021001d00303070285802038288130302d0551001d07045080d8480d11400ea000680ca8a0480d02d464007440001601c41681d0401c00c4880940e241c0c908120030700e80018080860350124810b2501c81742828041a56070001004c2800303070700a503001034603d400901d8500350329840b646149004000c080c0c5d041c001408601d007038500e01304081d01c0e84e2034031410400c03031030042d400311b82c101d40b10211107400c0c00202c4400c0c5403900a00fa200e0103486440c10241420300348150700101545080d859000e41c001d000122141002035611180986041344610340400d99204005000f00d800f060b60354403006469031141d03100300203400784c801203100c54072545038045501c220460780d1042a118020010040881401070400f0900410000c1d21414495403203100b26607054958500801668070341d82000200e521304030141034202099900442d030f440800201410025601c10700341c84d80198480ca0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 363606708 1250 363605458 363605467
    0xc020f0f010905030a110901050105040b0a0e150705011e02031b0304050c0a060f08061f080603010e120a090b0309070302060a03290118050310090807020406121a010b070305 76
    0x10395030041c640d0310190b0b251045c06050002c004004864107104070b410b079613000c0140d803104c2c015070b002c0c09503022304032144001303200e80f8249034420441001d01c0403003c1c0445003820020b081d014026802824180c0c6c483e0344a0b41291722092000ea00d035035001c8000f100c11411400c081c45600c011036500f04156039140000710100702402001e100f0701c40c06c107000400900c480f1396241005441d072010034005401280341440016014100201001030f01166001000c111012140007503604840152486816650702d55000b101c2c002d04010070b00c001516003002039180c05942000801032220b036000b03400b480805100384284400000341140c1900c0e030407644036454408011081340209060070026002c48007404101006505a003803680e0a507c080e640d40442820b142e44000d074500d514414070f50540d202402d22414080b240d0f00c07140900344205031072131400c800c50f00002c054414a8000762024400301c90404100254502642c02818005010704110f624012864600d8000e55030043c091000000c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 363607958 1250 363606708 363606739
    0x4020307180b060d0e0d0503100501110a0f030519051201030602070213090c140d0b1602010f050c030a0e0d0c150e060a090b0a0b0d02060f0912010c02010b010c020f 72
    0x2c01890a9502c043e00c0b940c0c6032206100d03100080c080c01d2105d0707121402590300602c102840750089074854406002c16507801c5c1c0c071342401154003d106052101c414041c00c1d0703459002440800500b0f50b454080da46007500d4254060300c4403901461b81c42d1000030301c20100602240303010082805030449401043c016100c21807030002c15016000c08030380100003490401d5100c2000fa0603010001580c90b100045210600c01c501840400e03010400d024106800030310000d19810303d03c13251365203411040d01c0042401e02c8421606011f549003901c0c00541d07072030080308104c506401c0b07104030100c0c1441c101c018401d001003030201904412102c1000381242d012000041c004203c690003910380c001c003480807681742c2c0c9000d02e0488000c0205a40488803d102d0401140d1212680d0040c03880145000703100005501d11503007040801d600004241c0d882ea075081c012100c4c1c0366110036025030b07004407440001c00ca41720150802801c4035025120300e414041c400d600800580c9407010740c1c01d114a41503540c0c840360321459 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 363609208 1250 363607958 363607961
    0x403020d14041223030f0c06010e01050f04051906170d0807050a03090c170102120c09210c040905030703270306021308100207020901120305030c070c1521050402030718 74
    0x80c1d0780004c452000050980030a1301520041441e040f008054407120398940080f00c0c0750710820f12489900c400c0241c83d484480c9026032009820104260103c804c005170102d04400f44c40f419400354903002d0b8120852135814005004210000c2da01e450640850704d4003540281c00d0f4002d45540a003095070302d140c0907040000d6080548090105011030550784042d140445000c1c1d88503140c1c0906103400100400c654882181c00d0301c40b4120700801c2810402c1c020082c06c105041ca4040d00003862003400740141841d2907912600241501980246907205454200a0461000305640c2848038050180621007000082501d4017031365030020003d60344110740e82060000c1c9020350030450041c0a880012400122558001d1110324070940340f0380390b02d80e07039050800d00d038400740500540419010800220002c06210092070070910458803403400c0340d214111105446030300d6403074901150306d8900c02014520b95405040103251354003001d2005180683c0882c0e00c03120721388640d004801c8408240d500c5445103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 363610458 1250 363609208 363609263
    0x2d06012304031a090d03090803010501140f1308061f12020607061b0311040807290301080109060b0f030c061b01110d0501050312121e0403020d140412 66
    0x1aa03d01e05650252100501c03d610030303582c544a40c40b50301690700c00c16000f0700032000c5203a00a600541160300e0000151804002e8000742601c521080040038a1168420301404100d0804580d510703a250900f1640e07403920001400d481c01c5507000d004860354a0b210702c0224401da031030030140d883c1800110310106601e0f004207500200107608014100300c0c1c0841c03600001c0e852034400d513420b0241d614206c0703271101144130320b01410070389800c40c410510094030014000b4500300b110b040c0c21030a201030b858a21140f60000e0f007000f6885d0b510340d90650144200c6000d9090002c004668883d01100c5900000e541e80380701c084458051003001c1220710f00c200d07800c01c0102850b440c031030003030069281500203808198406600e045210340f40c94004121030600007080c0700201c0104013400e140195400d1112010b01004060141e400b4907020b42c00b510241c240920380c0031302d11030340040414104400e0301402e219500441b2040708001484100002800384070017144890300200181208800032103031000f080310 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 363611708 1250 363610458 363610463
    0x402180301020a0c0213110d1a0303030708061905100f1209050312010801020a0c060b22020c0114090309190506031003031b03120b13052d0601230403 66
    0x2c040394610050b6000401140024400c81d40340702620580a0f2410840d20702d4184003010f85800c0c00000c1e840c1801d640115813400c8030780165100340d001c0000080c0b550f03200304c5650380081c0303014043c00681d0401a013000c00107881c00b058601d400781880c011503034540011424404128401200c06041c500131210707245c8208400e5014040300700c1d103040413035603a030040071100307404c24550f000010700e072506100380c1d820201e0b155074445000703c072612002d02500009601e21b50084445d107511080400403580540c01510112001d82c4031880700790800d00b1500103106150034000b080c0c0802001d2000402101c108880445480b01d96881071480c84000d14610b410180e049080001032107010219183c00e0811240310799100680f5030003842e400b009040407450002c0c0400c50000b01c0301e010031116000f901c01c501d4058024008000001c1403903058480584a00e400d0028886103024250f49038000402100e49152042c0894100800000e1540b00c20050a00e21041d01c448001e191003402c004072001140c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 363612958 1250 363611708 363611711
    0xa06060519030e07080d0e06030405071a0d0204090e0c100e011107030f080304020a061d040203090c100f12020f0313020d0611030a1b02120c010905030c1501120f020402180301 77
    0x90321030750840d698454507200d110200d0071f0155004464a4040c00306d910441d486006031000310301e44543c6030901c14a02c55600e24000b41440000d1510702544043e2000700a000f002103544803800741143d081805807030b54117010300041c0c5a62a07000b41c110b034003640380c01028a45201d0309010350740e801d41410760342d40000f0030701080c51040b00d00b4400c07107201950155000325015810a46d84000c01d94242c1c0d0600d820b81140c0b580ca441302002031501e0381c05558440304000c08c4d10700030200400010705200c41c0320104000f141210701c668903001da10010020f641031200c4011460a00c40d1a1004614000108520b141c07941038200c03402107480e60050540384941c811000d00c031686c282c5803003503126007084a04100e80782c41e20340750520022100e0644071000e2074940103003607802e0b00c100c404071030350b80a8021120590f4036000320b800082c03403c01c01092070080b0381d4040c10700d0f404070b02c00300d031402c0c4410790114a440000d024031002180c0d02c031144080c0c4036811580141d075020100100201c2140450000307900d035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 363614208 1250 363612958 363612973
    0x615030109021203070b09150105131d1c0f27050312030105030c311b0c0b01270203090a0f05010e010b010311040512070504020f0409050a06060519030e 67
    0x1850000117801701d05c0c031810010810b0740e1003408450f982d1102d10321249940d02d8030b10040141d0b041208500740300560008002c1203080405100c100c4c0141e280301a5040341c1e1103050903400182c4071388205004d6031101c4c94403854100000c20b0040510403c146120f1440c406050703404103c0c0c500d084034400801000d01598410525081c0488240c1c009114240c001e00812105104134500700440d5100454200881e0a40120a03242c0b02044040c0022242e00e00d80d42f2401d55404c810960400c0010001981e40c04c60391440901d446185524181c2c4215134051041d03411451003150180c0c1030303039100103140340161030380d640e0f0038000c1c42c1c020096800f600c6150200c45038010b2082c1904941c90242052009024801c000300045080311015240034101c108103120520062424405404090003071500b1644040d0303e9100040480e44070381c840c225140000101088000e42d1806815840880365108001081c50f00070013070102c1c03044a403810341402415039610404d42c000d0744140d10303809000080715800d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 363615458 1250 363614208 363614239
    0x91a07060612031b03120b1203041202030705040908070f17040b0c01051e1503010b030f01020a021b2b050d030b18010f12030512070905090c0705061503010902 70
    0xc2c1e2025141034000903070440c1040c4810031882100c110b107541c540e40305d40c2c0030059810080000c0c0549903015900069001311403031210400c00250001e400d05000d04c00c040304083c810503141908961204e401681000c60718404100c40c04162a8020303008204c5c07800b88446031603d40d442ea0b0801e106140d918501040c041076103076910020709595010140200850340310282c80b050814402c094a02403201002c0000d40300307905513401c008090402400108004072800d0010741444002448042c060398082200800c0590400c80003d503070385041c2d135103041c4802c0130022900c0007004451185502c0407000c5000b080300f12075424101e05540000c19120820103503080100030300840e0340550310403001000c602e1402d17481600b1181c1201d2141c00c18a501c06d1401c503907034400f003900e41341c2074091003800d020001a10710b00d00c1e82a8451030055591007039550404040080c1e802000c0c10801264005003c200001760700015190f802c4403060840d074141500d0000040d000d045104d400039000800c0315220000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 363616708 1250 363615458 363615479
    0x51615050108032703030f07150c050c120711090f0103060f0b0105120601020115030804030204060603090b06040e0709060602060a0509010e0a1b0e01030f02100906091a070606 77
    0x202404405814061a41c0e6800003035624020745a1032008a842e0701020758140d041041d8158030204068152810603108113980c13405a00318901c15a640c2e606041149800f40c0740b0321030035003082001e040a40c10100803041c07041c1d075142e140c552403501c28400602c0c0c005021144240388143c52008250a51030318207000602070404003840704a031b41e41c2c1031003004c0380781100c140a0750055600681d522410300306010503e084031f02016241e0b6041d075690304001c0014200343d010384400b4501a5401d540c6d03581c5540706000031180e060b03000c8001c05203800950340009807024409c9400139000c94000c10304403800314040341000001e502c031030180b81c5800c2c4001445034010449601c2038640c00400c0151b561003c260600b601c2002d58004102d42241310403e0008000030281c400001300440400c00713580e01c803601402c5189080c7c0040d14010760208070f040841c90301945084035141c0314a040034071036190403805401803085025020400405200c090fa4104c600c206a440343d030381214062140380d03a00d002121 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 363617958 1250 363616708 363616733
    0x110406050a0e03190209040602040b070f0b010f0b0405060703110607090305160621020d11040e0601110316060902100c020909010e070603020a0e0d0605150d020604060c030516 77
    0x180401c0862181c2e61441c03501190b29180d070043c1402c8071012640b1a800c00c40107600082c001ca801503828040803640040e0040074015183c40307014501110381a43c10011603416059115940070442120107211104c6003405980c1294401e96a00d03441e0401444d042d9000d101802e01d5044600c0394004204580364400525001c03640580207070b4111500e01807041c1905141070080c80080f82101c4d201c1c1552460014800001004001006041c82e002c1c0c01c81c2c009440d40007445009018003c00c0620128441e0720344150010703400d003400460007000301d4507540c890060310360a1340041800100c0d2814440c80b900200140d13036008056803529940840d000d001220002401e03401040b268001500c9200c05120b080120801c0200800c842441c090048010f0343c0314540440400400d620005216118554088401d911604002ca01494440403980018220880451091801ca6041009602c4100849080d980203241c03100c40b0b0320850030241d46a210780048410720740d01007480f00092000161240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 363619208 1250 363617958 363617977
    0x6030d03020f1903020904271220070608070e0f0913020402030c0315220b130e0c120304030b010b0702121e1903170415060b0c2103011811040605 64
    0x40003d40115000b02601c401e003007807140f0443c2c185081010124070181e48035a9460384030310307200c107080e00001c1ea00c0c140c00c1c26074080c500340340d8400e030814004203370001340207544100f00d032516080c0074407141e00103078a11900c2c03101d4a003c1d40380000815009613514014400c000e4010700199039074201700040c0c200c50f41c412210043c5503441095040c000b8508605030300b0000014620381c0110101e6000700c00b00800c81c0048540e4403003042401000c40078800d001d482d0017140300304040c0140e070f0394102c01c1c00722042201c0140c003101d03001000103000242c055100c41c0e040d05d06070305100751150558400702e02c1003106c0e107042d07041c94401d040445805241c00b1424075005c0242c00260340c0d12048142d502000100b00410050100301c400404107521038a00d0411a405030040030400c480411114a905c12152190402004550001200c446031841040621610000010000c03100d200300c0c0c0c40982a0300060048031101c2e4108415202c07210010380180c10300218040a5960340d035a509030190070b592000044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 363620458 1250 363619208 363619211
    0x50618040b040b090c032a030906010f18020309010204080312010911070b161808070609080304140603070302040f060e0418030207060c0c0807030309170606030d03020f1903020904 79
    0x7260035504143c001c050024074042c01001e41a142d0071164a8540c0008012150f08101e4542c8141d03260890400d040a18198018103035881c03c1c044c005e103040030b4050300b0880500c40d28100030800261214080d80700c115440e40c1c01a1291100401280a440799612200144c0700108809a0040558440341e0403108004000c0140f5003110020a0540c0102e0360b028154100105c005018031401c00f502d1540c2910529050320030303544060b591a001c2d280b503002491594000d41c000d0002513003011000b00589039441c000c6003043d2070407110000041c107a204c1d0901034034000c80403036042c5000c0d0b0191005800c007501c6c1424903071340360300b402040501c034621264030444c2046000341321900c3c03002d1003902e0710303401d60b02410f00c1c5c0f0306006080d02c0c03174050315400b25050910b50f000000c20072814440800514032a69510390200e00e06200036030001a42403d02d0841d4001800303004050f900010410b00003511410096110306460601700800c0c0548040c02c404a4040302d2103d201640c554020300c42c0ca8400c940 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 363621708 1250 363620458 363620471
    0x703020d020706090807090903020a06050108100f0509061807030602120f010b0c06041217090109060b030304290d0f0b011206080a02090c07050a140105060f0907080c0405061804 78
    0x504071141c4c1801c0c410300b181c94101541c1400310a415030855405580a070040300c1e00d0304403d0303a8100c100d90090b4401081030300200080094201c0b580220b9682c0f0515407814065401c00701c043c240c03541d5025000c0000e80100c1d800840c4481c200b80105070055402c40d01c11515807800d090070205004c4116411801d040d280000440c010b91640140e80140080708000c0103150b81d1541d0f0043e600c0a00c24042051100201c10b40e2501011005054030a4040000200d903101861130b240065880ca000302c030f40b081d00107010a10503226582544800d0700056400c4074101040b0007085c000612440c41c1d00600e0078100401c60410100b5504180c584c1c010030390759080359000901400b01118002d0140800303540100c0c00c0900549020780100d0b41048800a9417860030500340c0e43d046c504446032000b2100001e010020205040c002c0c4180b551015040d03c40c3c031400060750300061441c49000f0b00c80c03001e0000c0100410614102c900640e8041c001c041e00903a611174490055080c0340c0403e101d0540305500703020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 363622958 1250 363621708 363621719
    0x21090c011403041211030f0714010b01050415050a03020d050403020c1008070e060d23150d02010504030201050c1c02030d06090b030604031b0f080306120609031c110703020d0207 78
    0x101100c1c0300e60f40242c0020f0f44500116021100106a55502c103010711042c400350f03c1f04400c00008152440c03003951988082102501c00a00b90b814500c03040e81484410710081202065808184428000ba494019a26090b4003010f82c001e005240c40e011040c1d14207806c0004050f0009035a002d046400c80c1c84201010343c00ca41185d8800d011110400000e614543c2c030aa2070800d0005029080c55540b404500403a8245c01920058481440002045006000c0c8100402c0c1040c2c88200f000302510307200400480c680010b0304d248198400281000380c0080c1c402c017030700021b2019859030b4422070350345290303214641c030002c0da0f82d006030740385008c454500880010341a155100350050603134050043c0c0b03030036540d030b407400d690884442003541d03071681c225513255001600380100c0c0303690389100e200165200d050040600020400004603824580e000c8401e0040d0100000240d40081d48d420076180e45145501c00d02c0300c050400c0c09450589060041126020180c000c0350091024095500302e5003240d035101c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 363624208 1250 363622958 363622997
    0x1009030f0c050f19090e070806090d110f0303010510230301051503010f291303120e0904110d060218010305100609090c1b1103012f21090c01 62
    0x30f046910051340488420030000886400c441003407542c00064901c515664030310b260412800b1500c4030080d4202c809000d1041d42c00000100c1510f5948004100c0c64403c44407040c0d0fa840107000c0c05100e00d0202e0141c007246841070090040690302000c202d0304203100e42c868998590028007032148100e0100f04440d41c0103034200241c904079640820900c400501c0c001c050091004507403241c200c2e0625000958507d110300070014200052104040c01060340745040401c907100c50b03084640c0820000e080e4070308540d40c0e20041d03580c00c00d42000c0703c80781e4482480e000a440c100100c2d001404c0500201d11002482e80501043c410b05001f030300d0500c2070f5070b00d40c001c01030803200a006007000302d030f4040300900ca507107000d42c0980005413881c107003000860f1210060710014181c0080884200c036403030781854100d04080c003585003104581c40445500c004290725800c3c044101c400c40103000b400c04500884c803801041c04114002c030482d103091703807035051040c2002d07107890081a0703a50120745001e07800e04c0d941c0982c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 363625458 1250 363624208 363624229
    0x905040908031501140403050604020a050a1520070f0906090204050102030a0305060415151206060c02150d1503050706020a020108040303090203010e0d0302361009030f0c050f 77
    0x882261440c40d501d103051681c43c00b410211450400c0001803d03011410585002000510f0081000b8240c5141c6881042300300b1016800060240b0444042040300540c02040c40f00501850300340302c1d035030518040003030525440e406000c2c00c2910511800040c500b00c1c400c80f40099803602e4005104094540100e00300364840c6204843c01a402080301012451183d880f20707811602c0180302241002ea011003266103440d844e00301c80c8601303108081121b140340d000600301e1a061781500061003c1131500724058404d0341d02130b1010b4007a981c68820010040d2000040710090b400ca10400c0000d412408001402840140000c075124400c4400202e142d03400001d601c007610394141d4030a1165504c42d6812400b42c844804200c2c0c044d901c4034681c030760050303040c4041c14880310a40e40c010b8842d5240da500c07041c0806443c2d4000e600352442926007030000f007103c0480c0c042860580701d038085101e00000464807403043c2d030f2000d0000c06005100b80100b115042d03401c030031200d00321000c444c0c0250f02c50801c880c09c040d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 363626708 1250 363625458 363625463
    0x11041a13060e0f071e0f0e0904020a05010c020409060507080117070513020d14040516051905120f03161502031005120705030307080903060f09030304080d06090c030c09050409 77
    0xc590740080d80c60f040c01e00b0f80591194080c6860494030f40c00e40301c10740b41c08885c64517110108902c4060588410351024001503800c1013180d00f000035051940120b610b542d071501a10741003000c41c01f0700ea0195240c03904000503540c0e010400300881d22b40044003c020200c280940d003e10f07481006032002d01e50b1700040078004c1d02d0303006003020702180c0e140c00ba850095100d801070416440e1166080c00340002c14080b003074031440c0544050304122002028586000c3c1d4160841c522800c50445000215200801e8000c00ea5000762100c100c103421242500c1c0c5032000404a8a4441c840001ca50400b4580440c500315058454000f07140e01c0c07145003007490180c0c081240c544008446841c4204424581b001900b8080c0f03480d48180c80f070b880d48038400f107411039002d468180c5004800190080081c1030030080290310500b20720360030141341440300b00c0644900c0090005030a03110089a103102e4901e40f40e008000901811104010f91042241d0107006000031229080103e21240400200c600b03084c0a1452041e6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 363627958 1250 363626708 363626729
    0x5070902030a0605030a050c040e0f0a0807020a0e01151403090307060b0609030102040e041703010302030a0f501216080408071703190c11041a1306 65
    0x5040005000007904020711840c1416180c140000703540d1001d21041200601503c05005640100402e01c019601d1288007000b0a070f0004600307100c01c10740814400c958a40c00245144e40f5520b41c0001100019141c001448080e1a500006070415030085003460403500c540360781605031400010f0840c00d0000300c0e80020503030820085030000403425071080321680f500500450074072148002081c22078001d0b802c9641c15107023000c188014409154100c01c45068030700070091440d07042d035022039290f51007030303e00518000701e01e00c10f07408110340c00c0749400d406501c4d4a84011840104100100ca01c0d003440038440c0d00c1da42c1c2c4681480704480c0a05003159110403400207103a40c0700607200404031580203190709841c05141030310364800a1894070040008004a81c002c014860524482078001a1074840211079603100b0003e40c90004a40e1210032502540c5041c6070750503080c0c9080c440c00e4007000381c10140d402071030002034180c4554800840c2c251801d041d652441407140c86481c540c2260b009004520826 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 363629208 1250 363627958 363627973
    0x30c0615060819051605031b040603090c080111120a02040504050f150d030e010c030908011d07080705010806060f0c060f0a0b010207081c0909140a0b040203130209070c1e02090c0705 80
    0x40d00580080d0341240230a50390781070659429964044c9608590030420010352100e80c0da100b071280070784071117001e009520020494040ba180100c3c590744170704040141c60b1442c5500060361f1400550655001380006041070000e0b103006901d4446810b000c41e4266030100e8003000c3e0701e0780307400d2414060b00002d5142c1c50702c610a2501100540e5000c603080e0044040000b001c801003540e007802e0050a044408954a01900e04152100b050814000b90845281a8007081e020007041e83e010b40603d40041058a44e00c0d0b4030f001103e841540c030700c101c4c0298600d910a003001d1104074100900124850313031075484200902c2003114012a00c4045c6440b074800507500c88030340c00c1364441d201e0001c0206100c05080002c441640c4049a40c1a561100c0280240d85140b904122110b0b48600440d950203104a804510b549071511040402401c003c01c041c1c05494440000780b4024052010800304d140c11002c0c4803100703010040c2088408003c104c08074010b19410300440d4441203510700760f43d5043d5000e005810304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 363630458 1250 363629208 363629251
    0x909140705030606041a03010608010812180d1b03060e0c0904060b030a1403071101090b07060c05040f081e06040c091829160c030c061506081905 64
    0x840d00083c00660340312900704800514894028050615100c01c01c900a8807036141c000041d0081e80e05078064442c64000e800c0c0304901c03200030380031901c11604008080c1001555400031469900e500316008007400e0a101c2020490b1002d411040c0440303101342c0d0180003110291200c1619401084c1d10170703400c03609001c0441e00041e03054200204000010b01280c0680c4c0c1e607515100802080505041603d070030000b921070502c032a5846130401d1580030300341165050314194000003030b4410b860010300a81d0780d50300c4c29602c06225000f01c9004000d00c40a45007a1600d0b4071143d61503680c2c40018400e512640d4080003d0420f000c100d040c401ea0700a8821400700b45041d2041f0050640e500000b114111030120050010301f10401c41d403042c18481c1d000c10308d10b480c100750040e070089010701400100e2281c244181d110f15070081d001c031031566242c80c0a00d9018100c1ca40380010b004000e4810440c0812502d010400c20303030000042d071249143d07a0040b0a180d58a13003134002120029a590300340c150440408414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 363631708 1250 363630458 363630467
    0x5040510080c0c0d170106140a051b06010801020406080109050c07080703021203040b061c020307140a080a061e020403080706020309030903160f0b12060409081b010504020109091407 80
    0x10711030040c8060700d10304070414854a013072100090003000814083c1040c00035203044030303001e280504020308004100b0407141c81d40b8512801440810320400c9800181d12500e407012032018054000e5141c101c0c0d602d961110304144c080d411902404001030211400002c03c2e132500d005450060000184581c80d200080d1601905036011803c150154424003182c1400030451800540c4254000c80201c9801e003446d030200003c0c0c000c1c402e080402104c078040c1d5600980e402244131011500c01c204200e030720f03100040c041029030825900500c10f03401000443d40510800741c0103010164000812415480031040c800301c100d020382d0101800e001002d01c001d80016405600458009a000f000c0b41c0c107255105001903e419142c3c8014020700325000b4040000e100d180ca50780c00038001c0c2c0254a414490f035800500e0700310100408040c400c903105d640030014401b100e41150240c40d0456980755030600b90b29a44d41c043c000564080307001031002000040c6c0b01d10b0354860b800f070300c0d80d00000c001c2d03064071159030454 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 363632958 1250 363631708 363631711
    0x20d0b01030c083c0703050703060b10030c020c060c0a0b01090c140f040b070c170a03020106081209040c0903050a12080705070203030703030f0213030c03020405060415030f150e060907060504051008 87
    0x10154845d0711804404203500b00b103807030000c51140f400490702800100501601180142c64041818140802c1e1f04400b0f0300811480408201500d003141c403103407202e40c814a41081d000d4003510304140c0800129819240d60880078040710203031610344507040245281641d034407515030b400f04c2d2800180070900040c0a94001044801e0254007030384e41880d00c1d00c1011000d51090107800c20281e10a00c00d6030304054080c05584000e000070406080d0111500201e2001440b418540b6403207103540d481c0c1004514090341c1c1110140d0341040440308002c58a140140c4080700504c41c4c98041507049002515003031040003100c00305540980074605252060f83c0541c0940220303080c422015400344000b443d011140308000008600807640701050300c3c60760060108451000c0c10086c012410065250351b1003070301e00e0800c41120741c0140800410750040c24940009040b490075820494140005806200d500050840c014071504007656150355581c1015511071069104aa41154000118540700d900441c0800e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 363634208 1250 363632958 363633073
    0x819050a0b061603080a05010f17011107050a03030608161e03122f03070f0821090d0f02061609030f08031807060e0d020d0b01030c08 59
    0x441d640c0c1003080010140e0b00040480c0da003004041440320140f6a11140003074002c00e00110400a550400000d0110451a40922000300601d2134003074804c3c040941c00021080340201c3d070103446400600d0a103071a26001c02d026400a414000080344140b400704504074450200e00a0010552600030080d006092941d06441c16242142000000c1203154200007035040842da20800d185030540044410404421071070f08212022030210184584004110f806560b0003401c0c0f0742203030400d03142006140c0700e40307940c03112492845140d07100d002042150407070140c000401604c41c410256001102c00d903042445040c0140d02c1040032450b0781c00304071141500c0300c41038030700194629101d813191141254103000c1103c1500d00002007040003017030341241e615001d417104060480c0358608100148603194012000c0c0c40ba41034000792100315524480d1006106920518202456a507030901c00404400c82c46503082500903414048800b1102c562074600c0210040071a950b80117030420a0300403040c0c0c0c103090 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 363635458 1250 363634208 363634211
    0x70e1c0f020901080d021e034005090a090f0b070c0609050f0d0212031504020403020d050d12022a1501090b010f03050105010e0f0301021c020c0d0819050a 68
    0x198001d40c079109405070282412400415945140304002071428052060700c0780c811040400b00b40010001104480710810380e061860b803240180c0c0561003501d0103010b5001d00540c04000482a40150130000604880b4111001112075a03605a080292461800000c20307a086240c1d10000061003030701c145811004a00d13040282c03840540e2018104e42004c01d054800f40c1c0200c5151648c03000800148400c000a03101170f2044224150003040e841c0400750926a806280c4030009520740c0722641038800460b00207108201d407098074208141c4840e0140c141c040000d0b02402c82100400090086545c1c10000c1e04480485503102071102c0702064030701031400540c0c050040459401e940d118242400b80c0b2030b00c00001840712841c0300142440551080d25001d00d801c100c010000350781c0010314007582810a899081045c41d200e0b000030700902c00e00c802d50040c0c0d030741c5440c01c2c0c015038a141c3c0901036a4614404841c104203807014161902c440442d080100719961802c081082d2105401081e0028200c120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 363636708 1250 363635458 363635483
    0x12090504091a06010c080703050a14070803190506060406080402031e160e0705040e060414100513020c060c0a05040305120a170106021903050f03010b12070e1c 70
    0x40c00380c0d40c00080a0302c03000303400d910891941000c00c0090350001c1e02420568a04002c56865000f5800707040c40140c103004011410f00d913542c1c05450401d1010030720728102a0b40d5001d52601c000d040e0004e80c0e0303010000d0103905402901300850b1003407d01a180003440e1307d003040c1c68034404490794000104100d03010b00407c4041c1c1c0d04c01e20311070100701e003032020100030f000c2c00308c078040b140101040164464840d001c40c1505000c0402d80202c200c2e804e948403040a00c0c500d5540314003040150407894541141d0b200303d40c0401c1003075513880074020301361801200c0140c240e140700170705502030303000303042e500049604664080f0748011000302c0182014022420410f04041e502d440365400e000c05002508420b0500043c101400c3c0d81c00010101c1e0504a00c40c0481e00b0b5051680c000e60b01c0d00504001d02c250382d03030540d10509040c000e10640f6500229080d10550380c1d03840d035101d452160040403c2680d0031001d0004242c00c1402042841841040a40003000c081e5100002c214103420340d41056880c2110b405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 363637958 1250 363636708 363636719
    0x10522020609120c180f070f0c050d02011d0106030b010b130b0d06090b0d05060c03130b09010608010b18191d0f070f050607080309070b0d1e09030c1209 67
    0x6409034074a810100184c0800e41d240014030600c801d800c00c0405295030003c0c10446140e5000804a0f04094103240c01c000a240c0782d101600e01d5520102c02030f100d40709071325001c400e036079054020754000880c80008a880240114001e0300366242400010f02510310704005119130811140a882124088503c800300c00c0d0351551801c034140c0c04110f8181034291608814001200180113510207184151041e1f502441c080d107405071100005802d4810510b400800704810110728041020055007140ca08042400c3c92400d1500074038103449044d2041d420450750780d0f4186000950304000403103904c407104103a50340d031881980d01e41c0c1d8050080d103200d039110034404a03400c01301c0a64941861b42d9000b08551600980041c4c6041501c0d03110401c60b090440c0c007440f80307446010640303071541e03849081141c50ba20385030046410883e80d40c1040f40c0d01d61000c0b5013691104050b801001000340c1c441c0340b054042ca5041c134a50261440350001401003189203200c003000a6040d0210b0500d000c652034515003590b1201b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 363639208 1250 363637958 363637969
    0x306050f0310022a0604031d0303090d021f02010510090e1507020a080f03040b0108032b02040504050702160812030c0904060e1e09010216030c050f120a02010c02010522020609 77
    0x2090140c04c0fa80c8550208010150020b055050960705107111410346c036a240e0000341e0300d01c910b005040c0202d0750604080115100d070280445204890782d116401c035420038600900819045130001d004699000000a00030014400c00300c0000b00c06001c2e140c255602c004008107a0005070140b800c52159106490208540300301134040001c140c040103a69041608018042001c1038018580c00c1d00100040c1c075031034180d10310044181c0c24070304205072000b48070080c0f0002409a1340c802500181000d0030006000c1d8003007481080c51300c4034400d00010540351508d5940d19081e4a0004170005401c202040380c50501324050884204000d0020583ca500c0750088d07a40c3d414240c400c100950841043d0610354a140d40c0c03403641c0320f10310500860400c604030300c14540803d07070400040c003800340f414112414071400340015a40c4045104c105d0307201e8100c0d201114070b550b01c64005c0c4401940380c0b002c250005403041c0919401010750711000d9030050b030b09a0f244000180307600b1017261b1200d4200140542500d03803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 363640458 1250 363639208 363639277
    0x30201300b010e0301270303090203010908030912090901051519110d0203070c0b03100801020c0313050103051b0f040806010321020604031b030c08030907060306050f031002 76
    0x5000464410380c07000000d0100070f804110b2a2003039041020700c0b190400f46d64000008071807041502c22219000d400c05500411448038040c0d015424261584188104540154090000042200c0d021800c5a03e1b2801074021500744641c842d8031803004020701e05d000030380c00800c00303000c03140c0c9882c04901c1244d4820304241d480110780402d807914541c080c0c6d40c40070702c505403c1132441c0c005035141401a50750f4030400245c601901c550810040b021412a0041604250144c010350000710f68952211515980ea80c03c040c04d103140401c1018404102c6500c41e0061034003c0c1840307800d5180d20301d000502150305400c0003200440a0405110020750340070200f1249000314010303a01e00201005440b41103800c6422006018255401034081c0000280e1082c240a4038400080c1030b00100049803a00312210074410300c01600d960710210a0052285002c41e09008441142c0c9041100b40d03552014003680c40c3c151504030754144c01100c032034a41060507030000c1c40b4218406490785070316200604910060940c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 363641708 1250 363640458 363640547
    0x8071211030a0c0b060d0c090504060b1c11120a0f03030219051c05070c080901030f060e0a060807260c100c1b120f17160c1e030201 58
    0x41d600c103e9014003468488194110909544072491442161030329074000030035103d4184041e580b400000c0512140d948085c0c0048401805820802400c51120441500d140d9040e1110203602a6030001480c2c003404d903a040c407200d41c000e41070000c0b240d114856041030380d500943c2031680800040d44829404110b4890110281d2205074075000e80704501000380c9901500040001d10780401d00c266503401c00b60003280c41e603000e0550307580c800761400101c015000340301c0e1110703400d401c101010400f1384c0c025214030303c10742d060b40e802c00c40c1c9983c2c4c4100c2580d07116144aaa00d000b000800d69113561070240c01c400d04010000011600e0004103040426111050714a8100000760307000502001c2141e8206445481d1229206c0081d2507410484002c1c01c0f414500f00c001c1c0300700030310f10100d0b040000004181c850680014807250329144440680c0c00081d4005004888481a4040108004074404056100911100700140c00c2c0c909690045d209450100b02c5005e002c4c9541c5132a00c40241038030140c50010a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 363642958 1250 363641708 363641717
    0x9180b090a06050c07030e090901061d010302010e030a0b06060c0309030706030e100506060406210e0f0f1203010b030c0f0310150807020d0e0d05190b060d08071211030a 74
    0x12040c10102e040303840190442c0702808003041042d0100764480083c241c0c08000321401c0c100d42e102c0d403e83d0760041c0b00551000c1000702e600c994400d6100f110b1084207049074001e0322102001a880020162104a1858010032140a0308041140c0c1e041c00300203405c8607480c0130201c0703240c080c2c0c0d040002c3c9001684e030701400c0043d0300c541603500300202c1840402c4d80142c802a040c005401c00e50300184450046001c1c240412041024504802800103c0b070420012417080c10440c41040c826a03544400c2100019002c0e446201c80b0790b0040c40d400501701c035000c2d1000b59428116401c24404064940c0081c1074101444400d00c14006801a120000e50281c0b1b902a1413102d4580f074507020a0310803c415980d8024085104200801c030794000c00c0102800c1c1c00c600c2c204181740808030000c0d0495420102c05080c6114100520f10045c0c010a55000d40c00d00034140726000c5e55036103040100d15040c404c00145503282c1400300800003039201c05201d01030800c0341031242e983d00d100f2007482d1443c0c01c650072000008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 363644208 1250 363642958 363642973
    0x3010501031508060a02160f0b16140304061a031e060106080906040b1b040303030e1002070807080309100504050c1f05090d021306060518040209090109180b09 70
    0x1036030544a101a094002d0b40392214052818038981d45034070300140a1060150001a4004102d58a11040050a0b804102c0d100c03d4903d07818400d00302681150194121400843c6200d400e9001e1120702c002c18201a10070386c41c640e50b96070361001400714034aa50040c800040c10b03003101030740d00780810050310321001c0c502c1c1c05e21840b40c0c0c4120b2508030182d0242050000b00c2c424400150008a0700c554402d1300440c45640c1c6850718100d036151500402d51088030818046404070405902d9045940481000000c607030744500380850b403200b02d1180340c0d0001c01c900c00401512001440980c00f559120409c00103541c0d030b010711103c10ba01555030481c2c0441c0c0507000103040707196a1600090035945038800c02200c01c21070019034000341180c441c0031001e80c030039014128810708541d142e6202783e8402c00340031b00600403a5a200320160072a0400c15002007000e00ca221280d00f02c0c201031080e5403108030018101c184503407a1101100091955242d4400c010001c09500400b003401d44956500a0719800002c0c80352 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 363645458 1250 363644208 363644219
    0x1e03121602071a1b070b031509091605090a1b03020405190303120e0f03300601120b0609040c05030108120301030503030c1c050106090302100503072a080705030301 72
    0x2c0c01d4494010000034121950b0110f8a85004829102c41c10300403050381e442441c0d82003541d4a04500e507442541c4800000040000241804455455808043c1ca80c441c042c0c0791440310b252100d1100c80800138028a00300c0401491408030b00c5650001520301c000108903c140b10101c03843c0c5000b10307814000c01e07000074080140b030900d0600794402000c2c50004001d4541903507030041091441400c2c0c6107146481d1280740428000174080b04242c01800001c4039900d10790383d600d00148044070050684000540300d600240004004180381c452501603444500c0054040c1c0407800800e04002200c0e0000401d21405241c2c0e20341d48211441640b81c1d0f21741c0b83c0c41e5072401c400280b0700706030f0481100c0911000d0004000046000054a400c0180e1498a030303144c01c940080720a8111100e80301040301c2e800c2034000900c030703500132400c0300039a8000e84211644240c0518240c0305440241c2c0c440001907440e81076a80d20503281201020946240c01d400041c0201684510100c0e810a880a94083d040007004011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 363646708 1250 363645458 363645463
    0x121202031b091243050112180b0901111801050313050f1c09060909020903010213090e10020a0c02040c11010f0f0501140d0b0c04030c0603020702041109031e03121602 73
    0x411140c0c01090710f03080c01a48482680282aa1046605102005003807e030f400c45290489081040d0140c0c580036490f81908040340700f11025158034805510b0328529241c00c00c001d0088442030600c40c1006601042c0e401c00440c1c9a610040c051442c801000700000b00280081c40741c01c00301d40103038000346513064150003002d1070425008484411f00c4141c0500f040101e030000c405004880c0031910050716003400c032022a0180c490428070800b0365071244000314000031780340c0c884005903041004444ea5605008102d00c124407814605e08007044003415281c00500c0c0940200205150070700d170543c404001e0007581420758900780d0700c201d0815207030303c04518800b07101c1c0b05541c010406259045035003070104011030300807103110b2405490b800c0d402c000030765070380320b0102100d000b1a0720843c110200c0fa60351400900039000068220722443c140708015041c041c00b4415a14090001405002c1c4031600403000d20b43c0c082d0442488090340014400c0c450000401c41c0c0b240d102d0031001c070000c5402c0220384402030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 363647958 1250 363646708 363646783
    0xd05010617060108010810050415110a11010b012f06070f020f070b040303081302060a050c01050a0605031009110a0f1701090803150d0f121202031b0912 67
    0x40c10413002800400013140d002443d151070303051044c0005499125801c018010841546480440d541400c00a08019000034000c202c038048a60700c2604004007000c42900340e420100b002d50000300400e40320240c0e403a0758001c4940c108000496034160000c1d0b9000c40d0704040b0200d91510104140e8801c05d1803240d0180514200e0103018000343c4001030034145031100e24000c600002e01041040c000050110503102c000b50502038000306155101c82608500a145a005036001d101c0d0354284030100d040211540110b40550740c004000d841d80e140198000302c010010440c068884200e080b05e4a060b0b03444145005c400341040c802c160154a0800c48031801100349070301d0f00a02685803110b50800b0801000039260403003018100c1c0c14000d4200c0c000201c0320300c0c600d903010700081000303150002000413101425200c0002502c914607000c9070031150404a02084400d103241d21907081d03008081c4006503004000c1d5240041c40448176010000a451501c0e00c6004034124002426401e85040880c041000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 363649208 1250 363647958 363647971
    0x3010b0a06181d150d0c12060f05040302070b13051309060b0102030a2f010e07090b010e130902010c0b040606030203150105010e0f010207080f01151208030c07080d05010617 76
    0x1000c2c4001c3d01503040048010000381410002a50b01d1070159612400e803031406400c245803040c8181c950340c21101e65400c0c2d40b0102c0d1105e14003040355050405c5401114800d5070145c018040703481c6801d11020141d072042e1207596070101d01c05800320701541d60503105294020070340c000282080c558904001190601c402e01c9055500500428802c07541c4040e884618854800c0d081b420380c42d91460300582c131030004040100382d5013848d100399544000060100b0440b1182c1e6000c0c060a2011f000641e16080024480c58001c3c2c20054000d4105a26400c40d602003031061414080c0c4020f80c0e21408a0003030140c408448080d12000d00b081585404c000304101900340c4845032006505d000006000c5c81e2890704007901074200c5000342d08060b80284800001001e010041d0388014100ca01c03028000c0c100819442c1181070001e03404503140805a04210078240d2014842e46503840d0701c051101c094000c0d88003118869800c1000ca006000c03603014549c006d040c9620b0341400001c14120109030600c004045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 363650458 1250 363649208 363649229
    0x118050139090b0f2106010f031107080c0d0212030606070201030e1f06031505010825080d090914250e180103030914030604060b03010b0a0618 63
    0x10301006074071060035000c008119160010541108103081e12000030741c1d80500300b800d401240f0101c410000c0e4000b058080100c04900c00740010140004501031401e0f1400c9000a10000c4290b5182e4001d1b401191207a008900c02420041c16a5a13440709600c684545181a005003a45820700d41d010443d0500c1c910300030724034508528016010910900640034041d04054440c0160140c03114180070503184000c0008034044080f1940241c88080c0041d8031080f00c80f852001c43d214a2240e151041c0c505a075014000740420070b001c06101d0789810064002c010fa0040046000160001c0821044040700180d44841507881e00d0725002600b00d4500c84142e0003901c16520030007040207198201a40b0900e8090100001043d060074200c4100d44035011294100480000050000c42071790445070482c2e00c259260b90855444503c04924416081682c0750181d1040011900003560340e003080209036406400050940c0c3c511000138041002c0d50300800210b550201c0c001c0c600c0506942d100041c1801403c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 363651708 1250 363650458 363650501
    0xa020c0a32031c090201170109050106020d020102030f071116090f0b040e070b0f0f130509070c0f030507082502100f050706230903090306100806070f020f01180501 72
    0x1402030f81200d07a0310204040640d6083d030881168001e0600004289800d01c100d1525038403014801c000303200c04c3c040e110140c03203002403198440d84140210303441008107000c1008141c440681c00c0d1980700300c0c8808102d45000320f000d004a820519842c44000b000000c0021850816141090085600049800e406103090074400d0718a03000000d8002c0c1145c000b550107039920100c030300000c0300038081c15541755040b000000c1d00929028804204805075042207a10052a46401c41c080d0f03034203941c1c02c00c01171800314010b06140202e40502d0140680b0380c042d0a10910300501d050b62100810095028100303201448504101903040102c0c0820301003240d402d02402c0201940302c00740c01401084001072903580c942c1500c0000b01c408a0004d0104003202d801c0b48201d081900c449503da03044a15224004e00c904000618290309c00122003040b2181d0300050001c645580204807402d15201c0025029407050b0100580c0d2100244203402000ba1000c1e4440314102e0302d40340c01c90a64404207064803002d0040030703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 363652958 1250 363651708 363651727
    0x804170d08090a0c26060c0301050a0609051f14131401051e0c1501060f021e12031e0c040311060f07030509040b1e1504050907050d0f0c050c06060a0308030a020c0a3203 74
    0x4441e1400c50f1300300c004000400b0000fe20485404403410850910b100012400a41100071050004180c0d06000500f000c00c11411004541078003802e05003076a03030203142c02300b0740160030750400030f100ba000f12000392100c80d000e041001c00d00c00800e80c010380004400d041c240003010303810310000104901d00c0c0030104103030f000c61441682d00c020590308a9200180000070401e1210210f820b0f90120180701d1121000d4540300509901540080c4000d841020b8400c940c500c0c103150030011078950000480940d0b08202d543e8601722401c1d00a1000035800039a0f8826148040ea130300c810f21221200d0b480c0b481001c504034242405885110751151001d0b00a00740000e02613652444176a0781e0288c5145030007500c0c0c201240604000d4645404160000c91400c040c1d00b0b0000da00c0402081507500d440c003141e401761500b40600c00152210b10014200d004144041a0001d41c80d4005101c00e010150490314100300c0380d01ea00f4404214200700d10900d681c207203401c40400d40c4500390b0150060303c200c003450030010200b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 363654208 1250 363652958 363652969
    0x90a0e07062d02030a090b0a0909050a09060911011b05060105060f12010605030601030b0f0d0623130212060103030210090804170d08090a0c26060c0301050a060905 72
    0x14040e560500c01d201110108040c516401c0c0c00d81e40c0c035005260480c88a4462003e0b44070f40c0814030503c0059403400021480c2c0380003d04071094901c2c4c1c3d40e01d01081d68a0528010010900a403284000b030762240c9215000c00c0d0280180c03039200340695000c0f6040d1004074001f4107070098090307002241412188103640810b1000c9941c0d8110381c030546002d940d070106046409400d1003040c00324010350140d24004201103030321001451003118207803820400f4021640030845c0941441a50b2688080410801c1e00090142c0c0c1110b95074101c00d02e40c500c411000c10984841060b011151045202030a5010000323618120010f0428001040080c0c8910350444c1c500a48400c44085e80c803205545030a500c00030064000300b218001c25a040d0715940340703809100c4ac2a2183c403a0318000d40000c40100224160000100d50712010720350041420721210b01d401c80300b0506201300d4022040a10b00c284180200794800e001840c4540315400c0a20795940c180410040c840042d604100104000751a0500141c1c82d0f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 363655458 1250 363654208 363654223
    0xd150b041808070b04050c0d030306050a1d16021f14150303040e1015080604380409230708010c080609060d0c060224040c05010f030b060315090a0e 65
    0x2103c0c80c030804c1e64603400c1091808280289072500040400c1c480001c3c554107501c403c00740d500490703a9030070007a030b0345d107409a100d041040a07205420411003c90f14a0300b8650aa8682d40038a0041d12010b0241c0a044109200910f84101005484402241d400b05141c0035075980170340a0039001d0340408042c00400c0e940c2c01640210784d260348003040414000751f020b11081d03000f0045080e81d00e5000088020060010300181c03070150160382004d821059840e851030312541c0208401700003d5005851562510014a1a043c1aa00b166a45c0c001e03501080340240d12101c0c140003030b10207150040c00c51040c18903040190b404000b160340f42448100815a0100310303e50083c50454400c2006e0b224140011a02417007130380c0050411710002800603504d900030403804071803614941402d51400550080d4600e03020207d5005060000340701c2c0c1405258069107202c0f035610068a40000c0c02c00c1c02001151580d88240c41070400703044c66100384000f514290042c039500c00e04803c1c5c103000c00050f08005550382d511 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 363656708 1250 363655458 363655463
    0x6020f011d0319050403080a0c29070c21030608150105010c03030b1c12030c1107030201050c190f061107020a0510230408010605010503240d150b04180807 68
    0x71a56a003c500901c80ca0580c1c0165802c41c0e01381390743c0c21101001070480e04a0003412500b440c030f54800d1520350000d170701d49014100c40f8a40410445d0351002c4003100e038140540d9048941281018164805000b0515000c00c1051103480c0054410b00f812105450052644c10020045098030010f02c510f9900c141d43c0c2030901d60500340850741c240c403000011000c40c038600580c0c0d55582062407401c2481141242c4601c1381c2465142000742a10006080b20303005a12001c600f19680842e00400055105400401082c1070000c1980c4041c82d2481501d80f018411407030581e02e58032401c3d2614144100c03031051040c96204040b1080c64010300e9404201c82500ba8420741e881024400b400707442642c00780c002c0003524403020540500c1c500d460204617169800074007402c07846618111011405500410840c0d0060710f180c1504100c504044408880601d055101190803140401e40280010250035049039820000d54011400e80d01044c10701c411142c1202041e0841001080000042050401103400d0942c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 363657958 1250 363656708 363656737
    0x509010612051b121f030206030c0a0c0b160201050c030123060d14010314070302060d02070314030103050303040308060102190201081005121b032d070902030106020f011d03 76
    0x10b45109100b032900c00010010107a42e480000c4001305000c1510585106015400062074070348002958030081c8401800002d400140c00c1010400b0880310b400074162031291403500501500c000d035100180e8007070a46052900380c0808040103511034080c0207440c1d0001d10070000034110340c036007200402100e00b403a01c01c85419011032204611511120112407400f11003600030303c040700410b0548144008240700c180c0d49900c5c1049200040c050120340c0804072500200001d04244081d02000300a61200d541142030291111030300f020200f86802540c02180941c0c080d5460b8941401d0141074808020103071030441d040102400250521100d401c5001a0203103810f904990f290865072554a01c07c2d0007003640041d85110300358a03400000740110940b50710160403200e20b1004c00a15942e000700e030030b0121070141c00f000786824201c4480da40c9500c070502c500440f00516076070240c0800300d0f0700c2a04650f005030001500050541000d0081c2d20703072800058100d03082d03414040f5081e0780700d000e9003400a2022 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 363659208 1250 363657958 363657961
    0xc07081b0a0303110114070f110616050f040510030519271e060618020405090606030405010b040f0203160203070f1707060606030212070e0306010302151c090b01050901061205 77
    0xb00d01c258005200c406c00c41e4096015070900000180c8401d071511038100014090f103c4082c005100405c0b02402031a0148250007013160362201590740b900401e41d401d00c031303d1081c040000c4a41c0d55441a5201703c010751000582c03030610300c20714031550506028400b001ca040007240c4922520350160340516044070f049100e110b040a244c0f0540680011000210007840203200c903082c08104c1c0d200100726a00d40e4003601c0c155500c2a000000d90240744a52580040700500040e00d074100f180045178130510940001500303444020005003110490049070032550343c04020040074140074050350510200c940015400c18010303541d4810552110000200307003946c42d07410080201359604c2640d404582c40032050241c0c0f910307400020000c0d00a010010b1031014400d002c1030005001c1c40440340e0309103002d006005141c0c210780038040000c0319070080100c0700340100000c0400960b11820018012a1f0020100d0ba0390307484d04048041c44c4041e040203208448040040004581005460001c180c0369180440c01c1d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 363660458 1250 363659208 363659237
    0x5031f1a0405180d0f050301120204060b030a2708030a020a0201090c080d0e09071d06090d0b0117010b0109141903030305090105010b0a050409051b0c07081b0a0303 72
    0xc0280c016045500542410709015082000881c901a480303c40700c119607609001980c1219641d80048040001c200304000602c07004215410001d07c190018002080c03940e0380f00a06000d6a0085501c1440556a014180b50041140c00684600c407550a00001e182880742c54010842c071010b0020441d144e800a441d030102030003034001548094010300c0700184590360b40301680c1c480f100e0b01104d400140c1d98402011799440d1103211140251803070794440c0501410950595554201464581e9201d06c083c400c8107030b0341e61400c011814542c4200d0a200680d454196585001d01070f6003880103031641016903008641e680031824034211102d590b9252260039640e000714104113008005040e400044072404414590140c0000d4090381c40138000300a00da036210b1110005002e40d525070300c00181c0812041042c5800743c2c100d10b40101510b1000d000d4140040300200c800d070302851070103060341c1001070200007103001072080268032030007441c3c241a202c18a030001f98072070030140001820700656800d103128 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 363661708 1250 363660458 363660491
    0xc0209072d020606130608030a0804060b0306010b0d061e0603090606090507050c0f0a0305220e0c070b1308040b130b18030d030624030b040e07050f0109140907020a060203011203030605031f 83
    0xd10760370250540f141c950b11042010880e80c419139600707920b242001c00c00624004601400c800031040355210711112414601d04401800002c00192145619807401040510003842110f0007400540c072501d80e14954151003038100345d40c4400c9900c040c0c006c0305441c400f0942010488030030341f1a4400032808106482c4592801395500d0700076800e03c3d010301c02006880340c8010020a030440c0603000203030751913540b0342c100d000c0b0b1114030700028007615040c84100f10040307a540140c11041000002107162548511110f4080d41100e00da40d0508260025001d4090605200d141c5040c242c5280030702500b070900d00c6100b42441000750002c00e1074135408040113078500c203921294401c84020414400b01d0700c06915070ba520440c80c00342911074000d03400c28001d0b41d8081c956002c200c41484040810024086040101c28403000740010294050251204001b942070b1000f0b40c00303041101c811003101c0d920750500504a4036207410090183c0d01c0300c100811402203c01424151220801c0045003a01001c5090035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 363662958 1250 363661708 363661721
    0x60c0d1e050c04030b010b03270a1a010e06061305010e040603020d0f050705010507030806100207080a080406020c0402040e04110f060d0911010c0209072d020606130608030a080406 79
    0x4400d1803a1205216070040800000e104070780c015a038001d1282d888a0101040384001c1d01d0081c612140fa50004e1501c503601f07400305a00c00203071020b40f5036403200c0b600c1e00702001104007020049c0c0c08102d40140302016a00e0403454120800741c1d00c880c10050705807a2120290701c01d009013418400340b5802d480f81c542e2940c02c8203000c1c56024000c1c582c1310125203000c1c00d00703080b9130354120755030700a10b0004146544070740255050aa016616030940e5101e1000748507540d02007072012000c41c028408041100d4004101d10382c5600d12884c800c5548500d80840241007680d82c1c0503640c8602c2c01000700304003030101d00b0516a04244c00100780c0d00446d0b00784001803213849400c100c01c2d0300a84003240e0149040c0d400c0d07010440250144040150551310b8100460718049410402580620333040041044644207403802d420107a81303416410340102000100c0141c0146600c00ca000580c4490f04100b45030a00e03d4140b04950341e002d40a202c5c040c04c01c1045616400740034510000c008c032440020381449100e81141c1d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 363664208 1250 363662958 363663011
    0x1113200309070b0f133f080a0903030305010803030609011401020a140f061f0605030702030c19030f210e1606080129030601050903010e0d0e040e060c0d 67
    0x50341c4204c8049105000d0300103202a02d00c2c0d8091260014062860343c10603082ca607030810002e14170f58003180c55011421001c110100d443c1200300d074203070000307640d540090440441a44400c0c2d181441c4d03180040a44405070070001481d0401e000707020f09515405509419a00102c44000d45800c4000040b803401e07903040c1000e42201c1134544017200307079400410721484190405080e10400d503211284402c001d5012101420780100398401007210034440c80c081c6810501d284181c0c2e01d0107030280d00042c541501c0c85041c81e0481d1410034204209900b10304112602419070030702800c84900782c0c091402c03d407081c0e00c2c050001c0e903d8841c1301980c1e40c0203000c13211941d00341080c58002c454035220700402c604000d0094100208448202000191031059028481c001400000740746503240001103030f00d80c1066500701d0301036403143e0072a05401024041c05103951007582d034003400c00100001b0001070784d0003007050b42100d40000c0d0500072040000c0c001c480003420040800f052650317403083ca08003c850700a001c0f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 363665458 1250 363664208 363664229
    0x109061a162307090203160c021005090a0902030a020301050414040b01060e030307020622081603030f1403071d0d110907090305061f0509010509060904080c0a111320030907 76
    0xb2807136140300c0d40031314050340d4668590000041840d070301b0b440165001d40080e41c020385064070707081c1662296000300554000507000110080e510820071060340c00a4400ba40300580101c01030120b422310340f0602982500d2005030040504054690545200c0c1c103001d003908100160486000325201001140c004542c003070f1180f1f0707032030010740800750407d04800d1050900b030761a0000010056000590010401484062000c01c0362665800751a07003500c8860581c180701c0f48080350025500b500010314031070307039090f29810301c105c02100030076802401000c200f51050b223031059520085024490103017410f90056a8038034180d11108020340310b640c0b456000502510480080114840d14141c11a1150b502990030403100f0f0b8840040103030101e024007840390400d421070001021031806405540e081400303014001c5c034003038200c510b83e420400d4088090b100700442c0c080c415414244107644000144d14030b24104060180c0d0700c07a5062041a00301c0c805a020000300106241c0c200030f2040500511400e1170 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 363666708 1250 363665458 363665473
    0x5160201110a150b0a03150c210b28050915030106060c03020f010c120b0d0203121b060903270901030c1805091002071a0109061a1623 59
    0xc11441c6460384030f0759402054144100742d00304e4104528101c065a030b200240782000c0361030300c2c1d005008101d840d05290402c440c50102c640c5209504090300788500a40e1001b041b4480d00c8000d200c01c00712011a10f15014200229a414050301c0020182c15290226420150f60321411041da120004440c0b141d9415464001c00044454100350a4021280320390240c800d089104850719080f10509242c02c40030864030b0051940350a034507801000707800700c0108003d040e4901900424640400d02030114010180040c1441001c40000c200307000b188030200041c049490548800d03901c034020010701803400381524891484408a84142d40c2c03c1c5100038100303e4840d0b03560f0030704441500c0c0500c120103181102601245104a40e4080c0c944240c0652006144612103114210000d40c8038030400d4815950f80b01d0500b9100c2d80710700d0f100380201506600401c207213080034100901240e03825038600c1180410400350f4020140b88103401c1c5603580221600c10001d034040f81004100c0c808240081c001e0184a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 363667958 1250 363666708 363666713
    0x10803030105030706030b010203030f061306030506011403010b0d06092d11060a0c0b0606070b0906092a011d090406090311010c0203071b0803070f0201170705160201110a 75
    0xa1070498100714111810b60740e17542410f43c00c90324011040d90040c0c00410000f4891201c181a05400030b80c054a0001e00805c003100d13185c120746041e001100c090b08907800401502424101035581d0800c120004c001800454000a140c4440c0200c004c00c119150070044090010704440c20051280f4018110281d928500100c100562050400c4131240464004440f040c1040070560b00d414070141c5604040b50581d45811481000040110f607010404120310000228104840d0307008102030001003c45007085ccd0041400c0280141203210018001c036030070902030b50801440040134800382880c1c2c0311018604400d102072002c2282468009070214240400c02c9115806800307a203000e0381d50b80c0004030454030b9060988035a01e03c00f0300164000e1041c00085035000c950b69010141c83e81078040c00982d10510107007960060304080d103075100c0350703074040d000d55070040c401e02803010305280021043d00c0d141801a01a02542403243c0c00c0b50010800740781164080c2d4500c00100203214104c9075050700e5031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 363669064 1106 363667958 363667963
    0x6030623210106050906010f02071a040b07050c18090a03030e0a0b2505090a061d030106140a0f0501020307080d09080d020a02150601020c0112020f030108 68
    0x425411031215810140360120700c0300c180002c03d0840c0b40c00c04201c64280010a00c46c103018418640e8042980d0200f8040166084c01300c46041c401c020802240b0280a01d822100c55080d00140c200c09124000507804495541264401070810300403c0000d161031050b41c51803c158030481003030300024001d4000381d204000b4034040b101c000d500380d00c99090340d09080d50940503801c00f0728100400840381c0321010000c0040c906281e0700c2e00c416400403d84100103031041c0c404001e140b07492600c0a0303080801c0d01d04007120041c000d1001c90346489170140200d40c8410720038484c0900c1007000030300c41c0c0251108021250140c02450505403103803a50303603050740110320f01900f60b60381d4030300071001424040290001515440740145c68205814000c0c1c070340886038041e210801d28000c03c00c5001d80c0d001888010f401800c0c41c0400c0b111039540d0004000e80a041c3e0454405580800040b0f030310f6000 = true := by decide +kernel

theorem cover : BRFrame.Cov 363489208 363669064 := by
  have h0 := BRFrame.cov_init 363489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 363489208 ≤ n) (h2 : n < 363669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
