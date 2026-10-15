-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5489
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:01:35.667989+00:00
-- url     : https://prove2.me/submissions/0380c886-1198-4c6a-aa22-41251170e10b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 987050359 ≤ n < 987230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 987051609 1250 987050359 987050371
    0x3300e180106021c050c0a0614010b0304030801180b03100b041401080604080c0f0d0c06140f190b040608010902120303011a1b060411150a0e04050901090507031101080708 75
    0x1012842103a0102c00321305a06204074070180001400105030340c4e0130034021206c00d2032042800003121082300e0b107502c001d404184c0000007103940500030400007075045051641942d1094408000c04000d0044240181c81c0c100242c0c3c1e01806184060550111550080861410b00b101c06102c81c01c0509441030021109200d00c0195078000b20126004c10004002040d40104002c20f4400d900d00030f851880c901503685007040000b56102e08032030144011480741d203c00ca00c411403914224200340e0204280d0050240042180400c50701d03040701d02c841e0701d510094540d2000350090043c940d440503218020418060147c4c0500005011960311050100c00c6905841410a0000e21400c20f18072038065a040240740404403000d066014501d1402007101c1f41c419845405640e9a40c540c84040c00044092100043c00c814021300840b128260885002d01e0300da581070710000740f140e451034105800f5082c101806030150003021008400d0204112010760f5100003030700c42481d02c1c2c8490b103081724040421104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 987052859 1250 987051609 987051613
    0xc0c0b010b0c12070302070f0b130e071706060d0617060a180b041b03150b03010608033004081b060105010c1e080301090b0310020a0903300e18010602 66
    0x4030b2190424030f400a008054000d1049443d0141c40300706c000749002154200a02c0000d0124084c3c00d00c41d000c5502c0405800b0068201080382040c020151100c0182140381c00c001200400113105074503943c09031400800e0340c0200b4001d699441d00c8128114420024080c00d034000c03180059204180360244c1a1072400c0c501e00342080d031566440b5403400e050041c0040318400441840c01c981c800d59210ba440c003640c0511034603061100c0c0c00c142a4220b511041c0a6402641000020811a80044107a132481a000e402034180c000e500c0c000d80c21074029180c00380400307040700c0d802c3c041400140c0d00034100c6010805010b18070b50395440d00c0656110030900c165400200e001d0b500e1400200712660415900109001d0300315520030039a1402201c1e0800d80100c40c5072581c906c1504c516280c100410b0041e240184421031401d031401200402e000d41e64080a06590307a52018031b02440800f40500c6a409910703021182e4003100031a008001d80032800c5140d1203221200e0046c1003503407a0120080c1280c0071900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 987054109 1250 987052859 987052873
    0x3040605090904030309062a08090d0e0d0203030d0204030b010603020705060a09060f0c020d022104090b03120a09090501150206190e070e04020405011d150a090c0c0b010b0c 76
    0x208200b402c20005000b2820580c139007000c000042d280340503042d000c6d401c0341d013100030080b806100002d805d00101d95280807c900e40081c82100e0340c001c10b07607004a1125240541d620018800403c628480f5868004c0d0144000540c0da0300c0c941003035000d0002c0d03d03c40c1000050617640d84500314140d01804c10041d1440d0003080102e011407078598400301d031a030721901d0080b410555041d8036130100ca6000c4e90a40258200d0000a003d50350b040c00316001d0351812650103007910107088800f100c039002e039000744612070b030303a41a5850059a0410449030812841c0400d02e5441d0803480c8000d04802041c443c000300e140c1824008034011001c4107210355604850b5004102940c1d803121075041c00f007080149003c5090740d0304081159030506002241c060321200c106821542050f00c140002c8a0301680003404440110040700804619260f055421040381324446d62122500e000150050354168080703500945040310700320b00660841d810050f40c0f0300803900180241c0c3c0e2240f2849892080d40c91000030354010003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 987055359 1250 987054109 987054127
    0x306101b15092a0e130803090609060106180e070c0c1d010f03030f0c02011b0c150306030b01030323040e0612120702041508010509100e011103060112380303040605 72
    0x245029448a98864501301c202c5d0a074440340c19540c0306880c0f40103290400c1040140c0001d040120500603c02483d00d0f02c03682000d0340d180ba0004245018a00c1c00040c4e6001250060784100b2401080e03680040e10030390300c03136610a8103030409c40300021206c0c121901e49000040106c4095449001c894154480b900d8030010712070300310b800320850380b012418461039080402280140c44c00640405100319804011982050240d8002c9000ca5080310201420103900340009034255145a04580d45810b00d283c180d910098004881013480064048558000c1800956001303183d11f0705d4004c48054a96007511110103069584606881a0159024804102c441c0050416600011400e4810104042c680740c17a000c8503801d45400307552503411540903041c41e00f0707110300130711403012612100390081144210300d2140c140c0601005148605000b442214042d8049287e0413803212900384208001241460314184100001041b03000f984401c81d01c8010610b5040000441d0181c4409895007800c1200103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 987056609 1250 987055359 987055379
    0x90a050c09240112061d0c0403020f090403120f0c1e0906050a11100c090801090b01050907030e0a03090627031b03151b050306101b15092a 61
    0x1400c0c0141002030350044512103801a1068201429400586e0340c40c880e855104602d4800d40030303041038601c070390810040005a494101c00803006c04161120841c2e513540e428140d0742151580c0d65006074504200d01107803585030ba40c0c0804114140c070f84030442040e902000072001030031041c0d1b0f40004501503400a02c041030181000d44401e1200d4a040d618030b80300798089909108260701a4011981c071343d5000242c0507080358110010f8401c02008202c9580c0c00e4441c410b00070018440c0c540120a03120214140f144203030090200c0300b00300400ca8440f10124a002071600486106002c00105100c480781c0d20b80314640941d42c1c0d00303891042907143c0f41d42940c80f10190250348030b4100c0485e00118800100040d480d40c922152001030b010300203915445401a10450740d4100403010401104001300101640c1d100c203024030046140c86d002240340005042c010118065085c068051080b107021001013050581044036460701c42c8848825010344004852095449416201c135406640b090034003010703100c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 987057859 1250 987056609 987056671
    0xf030b0a29120714071a0604060305010e07140a051e0409150c0f05090d0f05010f0207110f041e05090c06040803070302120f270306090a050c09 63
    0x1c5203040c2214180c281120110b6101c104025030042280c410061040d03041075103243d103502c40c00c9515192000ca82d03a208800700410349401c1120032610085042c0791101c2d88498055540130008000351700514420170b5560a0702e101c0c0244028011610704414184800e42c17404669016004141c49005200c503020a600030504803900503a0303460303060000c178007000240d82d02c60101c11800510b800c0c40100042c29000c0000200701031020400000b00d03182c40d0f050b04900c103507070002070b2012410450301c1c041e40949a1000e14480103400840e141c03081c0034008284220780c6200702d401524941e0a601444255450700d011304500c180300c2d031044491424950400c603803082400e020380d101041c880300054031640080d08018019480030511004040d01007141c16070b6040a21025814150b42c00185110383c80780302240070300340002020380041c00518146001765040001c068601d10310701202011394030080342c1d00c01e0b0b513075100d00c0892202c9400c0c02044e01d4000c00b0070350a00303003002c16000040959866 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 987059109 1250 987057859 987057899
    0x304150204120c05010c080f0a0221040e010801050705041a0c0607080910050c1b0a0204050117060c041508061c080c1216110604091503030f030b0a 65
    0x1010a04022010014401000a00203010a02c02002090f0826203a11002a009241441182403258021810301d00c103a810180400308041e07074a40000100b00d0a1000074109404107c1030b00440e20800000400079009445200d80047c0322681d8a00c821403e98005840c014086141040b0501c81003030712443d940d080c00d140a1035035182070040403226161840450345800004c24820030301240c0030b03050010031300c0c0c007440c100c0c18031043c2000c1c0001489480307200a0713442d05801d42d00c4112070011090001c1c20110340c000b0403c201940e5208043c00a00d040491000300502038400000d981c4496030050300e00340d605501460303c07151030050040d90303120406492036502c03600040490700488080c0e589145a030348a42025034036510008a00e500d01100c22018075040541803110542c60300a5844890300ba0b80c0110b0310084119402011440c68403540e000002c4e02800c2100d58101d2411103896001120b1103551425000980e08000700d0032509013895255008640607010400b10200702e010900c5e40c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 987060359 1250 987059109 987059123
    0x60b03010b031f120b0a090c150903170d06080604030c060b0427020f0307080a0f11120f0715170903090301020c071d040f120e0d05010f052202060304 66
    0x10300315240c030036865007941d07104094451414400703000308800c8170002a04038408220034001c50a545e1b8901c0000c241a020f04104d000b0380100054030140300b403161000071b5404c06a0030075a003030701c03211030381007640000c1c59003020350f007080000900d035800010414400c0d40c065481d040607a015548000162842d96140c0341e01944440b000345024210403001100c04040d0700c05101001d60038414000c942d8000042d0a220b9000014100305541c000b00f80310991a50003c0e144122492920b040540d05074000e601e50b4102d180d0007400b14000b500014001e102c001c442c82150a040e035582858000c46400c00000390000d151180038880c4c1080b000c1c2102e42200d2031400392820002e071800403908907040b0f02a5081c4540c0007410801490403940c444c840c01c1d4408450071043c9103044e48608250030710b80c20300104034010360100481c0180c450303513084118100c0100324410028549c24100c0c0a840c82c00c035040b01c144c0c9801c0210300c00d407056540f00c820303080d41002000a00a156000c0101e5604000c00a941b03e0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 987061609 1250 987060359 987060391
    0x406020409020301060507060b0f1507050319080a0f05130f03020705130b0418051e0c06030f0f0603010b010f0f02030f0d0903090e04020904060902240c10060b03010b03 74
    0x50308050003c1c42c040c141d81d51340d503a04c1c1c21003410a041580c601000441c058002c100b00d00c00991256079035080d04010306404280c0c0c03401c0c40d203890340c40c0d4410200706190b1800001804e0318030326440703118103010351903000c0c1c10301031200c80c80303a01c4003103490035240c030145125001d038103400040c84045942030b4503019005030742403255200046088416441040600c0650350340ca220750516180c414906803100e918101c0341d04a4030b6507103156441007031480c00158040c403030b09440d4004100300305d071210001c1d000d4040d43d2241012a107454148005940f60541c490000e40018141e050502c180b11420b003050751200150f01d030300301094031a01d2601e0b6044086010070031030000c40d01c03c100005c0c403188080030310001e80f456690800030110550b0b0b40042c8081c0d689107040c0000741e41c910100760f80241c4c202038002084100c1b0b10000f03a006055820828040250f010000b40c03c1c003400303024004660740320b4103071190240344115040454641c1e0046c800740e81c0040c0014803000464901660b0322507000d40c024004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 987062859 1250 987061609 987061619
    0x706021c05120709170303040804051c0f081b01090213110d02041706060d08041a090301150812040608010e0a0b21120906160203120d090203120703051204060204 71
    0x182d54086900a01059443c01c0c100034000812084118041000c00a141141805e503251032582c41031b44030f038074894460b1a02c0b03056006c5c404206c0c0900301c0d0b0310614190480310f42c0c1c83c02070320a801081141d5607422200c0001841a801802680b007143d500500c401030001c01880141d004004550910130514020700c0700c030129120900c0204068540f01c1e100084544c1c041590500d8140d0040c0964010000000303086d002a039a80180da05544000c03940080c0d6005948401c02c0c1d81c02801b0310158076600b40102a48075000b5440b002055907040b100343c0b41104000c504005041c81144180b90014050400401c0501003540209400210400011414040c1907001070081841c44481030000d03a40840581c80512003006254044d0800443c5581001b41e00c0c400501c01e0700400d0310f00c14021100400311021583c0070f2080f00500c2140c104036907201c0004180740d43c02000445800c0f030280c81010300034807403484607a0580d0826503040c0d80741d0346400d4801d640c1c0c039034182015000b00c0e07002d03800b03100c0030034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 987064109 1250 987062859 987062887
    0x421140106080a020307090c0804031409060a0c1101020606030a0305030a0603022806080402100c1a0a0204032a052403010303110c0a150309020d0501020409021b0706021c05 76
    0xc000c0c01e070180100f1a840e5140100b60074028281d00412065103804c490000071904a0b21080c0d101c0e0300341c24088e105414000707480c0781610404284950101000030602021500310304c480b5441400b407144405000c2072100166035548050f0749959156002da4040c0b40001e100c2d000543d80b100790f403800840c20955a50200c1d0342c43c0a145079801d0210620004075520f45100d101c51001000305203030440c403900701070700850038004405080500300000d40b200c1d80144956070700812a203601e00c151040852030304200d128025000381c0421985070400d0205003d5400420b010095040103c0417000c00350b52424080200d04901c00d268a04010815404a01c09408800103180210b005c3d4a83d240e1a0031842112410f240819281e1031045a461100340101d90305001940054055814001010344036800040c0d015004504010203075030002078049503148881c0c019002141840029101c55156102081c0d00e4010f2030007004010703444181540141403000f244444030440509106107440c080f034103120 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 987065359 1250 987064109 987064121
    0x20406080a1a0a0c14071a0403050a09090203040b0f071e05180d12051b010207050312011220151315020106060801050f0a0e0f0f010b04211401 63
    0x1d1480d842c002008040100a00703503040d8000c81098080102000d000005000903419030120190140d000c0f800001700040f031003002070002920800800b036071900e854014100e5000c8500540040d003004000540c02c00940241e07400389510034550740c0c8030b40e1024a2800c81c55401041401000014101294141203401808040c03880d541c0d03e081d51208201000c48290328140d400e41e020301c040700e0071180401c8200c480d1007004201440d0050380c1d8403090402103014041100300b00410351002a4003010800b00100030403402114505454080c0e07a40e03c044047c096400b1005410504030f0848452200d10407007203168501c8006203102440e0700c6056440c0c00c241c002c03000c2035911000c401400d00941500703001d04580810315200a02155080c0750740100811018415240100000052042c5650b22104105d000d0711491503d2003c2d45881d0f28450200b44040d03d009844490b49800801e101d07105000311410386206040b600951621504680300b6503401400c1a03400c25940e0344481a07210081c0501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 987066609 1250 987065359 987065363
    0x4230a15050306030105010614071b05121c03110417070f0306050709150f080606070f030527180a0902130b0f04151205010905120307030e0a110d020406080a 69
    0x254891410f84103060841e04c06800c001c0600c4540103d00d0070b4503082208490605601c8114190001c448107102410411241c01c181e0b807000212000140c00007001030800e91090f112038200c81c0c11955010300350121025200c501c1c0200e10100070500012010b22080c103050300000c812114a995108148645581c1130341040b184161180107022805900c200f440024000345000803031912034100c004ac0c2604605400c00b02801003141c0025031580c0c0d030005840391103400604613028009286001880c0d940441e6031300c00d600030142c0301300941d0b8807450603445545501034004102040701d011504030a207402004c10000c191a40b030702d6401601c0c4d00407a00701101d01d514000c95140040b90410230b19202640419001d80d241600c508070001103101140100d85181c40e108845124508240d070140000710405085031042803420804c2401a41c015441007066903020090b001202c50841d0300e414920001401d4002c0d492021001071400c199480040c610052001841d40d540c0d205d4503045c54925a01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 987067859 1250 987066609 987066617
    0x3030c020c040522080d0213050a0e1e09250914060d14031201120c08160608060a180b0a080a03080a05074104230a15 52
    0x8440111038040208003664001260705101e140740c402d442540c07094030920510a80c50500e04c1007401e01a2160440d18130000b420819540c44654079000e1805116912035103002c0c1e55a240700241c5807107241245801000c171441a42207880c000b241c04d151490300500000c4407401003400019800c10380f0007640c90409020b000f42e07a003441ca0031100004031003c9903812003c50156904114440c2e8514141580d02c1d070344145041c40c82200488007070301e140110002c0c4000141541d0000c105005c000b0418855035100e054254207660315000d000d92644100c004001500003880c0c2d0034485503029544043d40b10001501e441c81c402c1ea520807080b504548031032000d00c51641c4050444003400c0881000e0301a001690003032040c0d08045da0001d11420000b000074144680c1d5402080e00700e8402e100c520002e542a214000c0d2248110601404509051381e6400a44821200f1400c0801003d801d0318120f8995800b10481404405500b0344110034203a44254824980900030600c00790407084500c104c4600e0355 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 987069109 1250 987067859 987067871
    0x1e0c0309330306052b0209010b121e133905030c060409020a03020708040308030f090106060c0b0903070c1e050f090117100c020a0c090c0c020907110303040303 70
    0x1030328a41c03540c035800c403000400d81410b40030704c8a42c0710036002c3c035403031001400706100c00b4420030200c4242001d1010025482071b038141c00052694803c0001e401d4828480106408544442072008103e804480c150031080204c10b0008864032030a01181c900c0a02030a9010320310390703943c400c00c00314001844401c10f840003955046c00442000b43c030301d90080c180540080078a84610000150b0350b00407849680104d54001840100c0303a4800c4e015100c43c183c0c002c00c1300c0d0700e42c1e8030383c9041042a00304444515001c02040005011030205008040854406480300700d2900c0050b110001c4840004210014a11080101000241080c151b450040015140190340c101c0c03041d481d6036203058281d00544c40340081032039116142e52031180303a0b81182c0f06074000d1400140011241403c00a00492000c2c0b050718101b100c0003215008501a5411442004c070303443c0058550350f0710390440c1c0b8460303d0071000580721a884801030a0540031036800040c0350500324040810842800d2665108032400c80010341c03211 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 987070359 1250 987069109 987069179
    0x50a03020a150c12110c030a020108160309060914011808030109020703260118050708070305062d0f06130306020a021006081516080604150506070803161e0c0309 71
    0x310824040c61b0742103000c3e001ca001580c00090102c0e0b000703000f00e9034100c1040d40760b01113a8080d034021125580e00c0300091045581e5802c04005450780090309107419400c1100c0b541c2d9509100720070f0380c034066201d8412411070f42807801920007500300c9081181400300c02641f4198038002c500c1c0103044079003030b0f12040340b0541c1011410103c4c001031540340071800d400c28083c8500e094200c40034a42c408880c2c600018255141000520354034400c41c01c401c005010f4014110101d0381c00c1c200c08400d00000e55810b40c0c4602598140320403841140711840984d90000814400035072250024201e82c3e1403881110003421314032440404483c0a40e00481e4107074030207030360301c4482003035000710319400520489000b1011307005903000f400d9a140100031034031841d80c0c3c1c90711034042e10201464001601010b007040e0b441e4040c41c903100da4158000da03910440e266010a501d08000d11a80d01c20264001d082802089046010f41c10384000c1160b01c0700310240411130002141e419080b422100604540c1346040121022030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 987071609 1250 987070359 987070363
    0x90b22170c0d0f0f080f0c0705040b0607050703021014030c040302030d052805040816090e0d0537081006031a0603090312100e01050a03020a150c1211 66
    0x400039540500300c0581e4107000b045554204100c21a042100010401c0c42407924070058403c02c40406ca1a40740403074070f00601100001d42c10700b030b10000d035801c1011104210403c0358034050018014140c1d1300a450500042c201007050300351210190405902608109188000540048401d421001c0010804009600d002c2044015031083c41c140b19181501d4107902c01c4d20b12452800010006c144800040342c903074407a5088800500420f0281c50800200300cd029245424500c1402d10035818010b181100c103001189041c40040161101850b01880318234448001070811400442c1760060b5010b000528000c20444070041c001c1c3d51102124540314084004219080e00204209481d12801006101c0741007440800c1c14001c40f1001c0e100c1d80c940c0c200700c6c03071881500f0219200302800d2081c002c40081c07034070302c1000303880b4000301001c150303038071a0f0603c5100341d43c611010b035100e01440b80c03c003c2007103840410140341e0400c1c584141d01d20380640703c181c034000800108078000344103001764020403007003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 987072859 1250 987071609 987071623
    0x70902090f030316061503231203070f021005150904060e030412020108130305091c0204060b2d04060c05010b030a03080a06060801030b0a051e0406021804020703090b2217 75
    0x105001040003030854546031103602c124120500d0aa901c0c0b8034071001e030f230400c1100000700d15059441c00d503a440c0c112401800014080004000341c840d5840700c1e00e00f10064064984608000e4441e000507010031820098566806801034035016540d00c0c490141d00e0040c00140b000d8004402d0580c000000c5100043c13180d11700400c42442042e151804c0c0000a0348001110100344040b0740703940c01900c0b00e010364020000c0d0803000070f511900e024030000b00807201c2070280100c218114110303c04d10f1070a802c0940c044c03240614515400c0c2c0104003e04c08203004841c0405428040e000000d82c48001c079001c81d203018000c00040c3c010502d00c80800940e075025020b9400074122510303100c0515451a40c0d070098180d030151942c81c42c01d0b203410020340340c40040b0b18403902100c41065414110b05041c10700d00001e6103d458180000d2003030804e007516a040234001c6480d90b55050781c0d165031180c6014047c09480d000300c1d48800c101c1c0e4040d0764002da030309000595100030b072030320120007481908204001464056 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 987074109 1250 987072859 987072881
    0x3030b0105040837030e04390215100519031a040c0504090b0606070f20010e0a03231f15120201080114011b0b04050f0609070902090f03031606 63
    0x702c0e41c8000e00003c0d80c01000104850783c151f030b02064541030410590b01d1040070300d4034418442c401514076140c61100416126201d8101d4007a16001c842540e04460807078411500c1d414144035084080195040c9107426954041104da262000c0da07880360341d101144160303020121202045082840700b4404860403440090004941c03c0041940e5a0ba640b409000c0c010441032080001003558410304c12000844c42c1d04a91020300704140c10b110714030b506092406018a03a0010742613258040d11424407480003000c0e00d0b0484a180d0818520743c00803138087c0300c0c09920b04c54070b02401e007000c3d20b41d08011080c0a000705c0c1c80640030414076071203000d055030401160311191051550b900d210300980d130001d1095043d100b101c0c8000040c0150b0600503100040f00a20000007400c0703042d900c034140070034801c41c0da00851060041c1d40495a40032401d0380d42c0c00c1e040c0c0b10681c2c0f03500294801c1147c4801640144240f40002c0c001c240e40110140000c0e0071504404001c8400b4001d000c411403c009651041400c41e00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 987075359 1250 987074109 987074203
    0xa05060307090603090c030c0e0f010e04020a12020f1e0102010515090412091505070510141f0305100608120a2a0c090605010e010305090a03030b01050408 68
    0x2140c040001001a16140f05203070605555000302c074280622202000d0166810041180704140c5d210701004002c1c80807102c41e05045001c100106003001032041c0c090095400500281040303040020740402e48003031800c2241d0250b4190a004c00a072203448181c15008000c0101400c400e001c0e400181c01e40c0d00081140c1c1c4030b200c1c48444102541e030303081c80c00c43d00140c01001d42d024001543c241aa030142c7c00d42c104064649501c54000342c030340c0d40280144a942c0c403920036542c80d04424241c0d41e00341d13130201d000f0100a0b04881c0000f070120190396135403c50f070613130f000000b00c00980c0c07500c0c1c00e4240001903c4690754a91550340c18400c404d8100803c602a9100201203803410054040007401ca180440d90000704170702d003d03d0001d2801d085130400c5403458000300a240741e66a65031720341000300014480c2c0c81c04110501401c200702d6019105140c071610116012340300f400f00c01e075021401400031105480c140a4240808601001c040204001002040b0090381d146949503011400c04c05010000c0c040907 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 987076609 1250 987075359 987075361
    0x1509050111070612230720060f130804030501060b090a0e240411071109010609030c0506132102040f1e02030a1b050403021c1a09010608030a050d051305060f04020d060212060a050603 80
    0x80c4d40c0c841c40f92b0700040107445006001d070316242004541c030903070740064410f6081c5180030408a5400d80200000e0300211400c0d00700942d50000d50700c851004880140407a10400b1124001702d201010b0000043c00003040082c00d22a4130702d81c040c050700f1507030702540d031170300466003040e00b500b01a014140500090b080280090380ba55075007034481c2200b4001c41740107500103c1c076126a0040b405042021f4003418031248161880090a0134448005070b50980c1b0076800e10031801190012481800c6021503442c0c0c0c0103414510404c07014002e54005410f4240300d0b0f680d02104d03003500020600301c1c89082250b503101070f515860350041090b1600e13040380724240000d240e041400051403a070201c000d10309664012001a90752401c0b0700d80100015800444103000014640040310390020040c1501c8420b44c80c10041500c55440345200c10100000c01032056215002040c140d034505804260700a100911100441d00780340e03109003e80e0894a12040b48400200074803400d45071800c041c0b0090507044d2034403030075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 987077859 1250 987076609 987076621
    0x30b040b0906100c0501140421050c0709021606090b010f080309010c0f03020c060408030a030615140708070218041101020d0206150604150905011107061223072006 72
    0x15455070043d800d802e0002d110701040802c0380c2034018610031010400303800080c0c0f40c1424844c422500f002c13000400c00b0405168041803070300800558030003910241c01443d00c10f041486000003503000300f102098422801c0c0d004c100003040b60003015581d600c00c02e407100865140a58240c07038801d168100000c15001070040c48a140d91116080b0145c680282c0c9000c2030b1130090405905140c6020003060b0000d4001070302184a1b0f0000004062800ca2660704012466a41010250720910400e00d0400214004054891a0480d4000d860300d00d000b00b00d8149810a9940013032503464440f0b1003071424101074420481800050410008403000c00e00140150644441000351554030042070100d541c00c0020508070f05403200b9060703030007a080ca43d906080e1003c18450141c49851181708a0780060500c10421102c041d0204250b02190510784540c0503400c0c11105143c05402081c6e1052059a60440340c807000d0000302490f01d0042043e515550140300295007400d405400705218150503070b12001c14098 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 987079109 1250 987077859 987077869
    0x310060503030f0714010501091b0c02090c1e0408070905010501051303023003040509070203041211281e08031204020105090901031a0601110d0c0204020c030703030b040b0906 77
    0x83d401c26210542d98442e424030301140e4500e800c0341e03d18010362030080081000c01d40f0382d002d110146c50100e01c84010b42c403181030403203980003103105c001d40050346013020412914442000c0e0000c00d61000f80f107081d10200a81c90030746604076903c5194182e000135010003000c2854424680500f07800c0ca031440ca07106022603405220030079880028028190b154000c072a840e080108400441540d01c145650880b070341170000d03a01d030410b005252003984010f01003215540000116401c03500340070051500401720f0744548240441000790141c01121030b2619820aa00011002c010349105207000000c01e0f040c403070150300f00010545060040140780718240520070000058a10081400100d01550381c0d440c80100d07010b0158040c40c03604400b00300300100c200412489000720140740a21101d0039030b9240c0f80111200001c040f0010310b50740040c40b84d05003083c07003544001d03140c0d4000b0707001610f031680000c7c1700c514552285106030002544d40c83c10400502d03141c0070b4205140805c86003020ba038182040021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 987080359 1250 987079109 987079117
    0x3031c090f030801090633111005010f09090302060a0b041413050601090203220606030b010b0a02060906220c0515091c0b011203030b0a090c20120c030f0c0705031006050303 76
    0x41d04e070b05156207d020b01c94400c68120408801d10340039501f0115011030114068071080c011910040e8038003d01044400380e170311820f0b00c010b030140d00501060b220389100c90010154002c040b90056100c030256902541910301a038041d021201e070110300b00101d42846401c055060700b00441480c010428841141c03002905940c0c401a48001b0008020305454000e0003400c0f240e200034030b003074180b0000150060040300076025031810740d000e07a80c081d80c1d503090094a4400071600d052100c004d0080501c0529a015812a0003a10500200c2e01d20ba840b000010380c20042c08450301142140001c1280f1030b07013003049461682004a0500351074030076403561801400307001400355240300111510701c04181482600301c5e040d10a00604200221504c8403402009002e001200d40d011075180082581c0501d40950750015400c10940604295100e08500d10040c1e80202102c0c2954407003444a03240700309a61004208000c84240200742c0c10b442c041c240350400f0070261001c00402d2424004020304d40b008002c032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 987081609 1250 987080359 987080429
    0x3050901050d0f0614241902030d0f0c020c060306030703080a02030f040306140c0304021005030c0904060e040c0f03030806040b0a120f020f0d0203031c090f0308010906 74
    0x1031070b203072070b55040200c005000c9101e00100c2c00741000e00008880c62504c8600403a04000e4030b0304a03c061111100500d00b800b00902800800410415030100c80726010790300008000a1065920b4031030342642070010703100c1c3d08000152080c0c1d254100e0060780d070100880d19003080c05545e418110715207030000030f880b40034a10003c0c042180008003456030900c20300840c0c9865080e04681d584031070b00c80c20550010058001d428102560b001c0125103003010080980c2c0c8110340c01072480d2010304c03e204084800c1d4002a01d0308007000001c0c000750700c180d501e5025a50103809070a400100c0303498a070510394400001d0764856604404240307002d2001c00e1303010341100c3d4040c209440204507480034802007820140c0c95805003800d554030004071070800007501129289a40220307181c406e03004800b4200130a0014406000b9031560040120011044064000000c086540d800000350b0070110f4a4000801074801c10440024445c14010b0106440720310600001e842d064550340d208144810342030b186032261802e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 987082859 1250 987081609 987081617
    0x1050f0312160c0302060f040303080a0203150f040209130b0906150a030b06071a18070503030a140c01050421050313081c11070215120103140c1f020c010c03050901 72
    0x148410f0151080c04003000b9507024202659030980c00350b81046640050200310300062054000c00c8894100d402940c1c02030144080c080c800c0e032041c800704007000c641c41c40902d030019000d002040c181e595050500c00c46001100300807441810704010029018801828584075420100d181c000311300b40d030b5003a20080c00450500144200a12001411078025544024000d0030741080c641400d00041120078014015960700e0760581041007046601e6980f18040e01e90154420310502c0300da00d105800d5407e99250308446170340740c03603101d050040c256001120159403c1c24184129041c482c140007000616880d41d2600f1401d41c2051a90f07441c4107030302d00f500509030800220300c0a00c4000c12a400e00301c4481072074000c00030180d00d601d41300d4168000510992207150501c081c0090400008202c3d0f00c891421f540c604266801e40c0e4800b5440c040c80102c5026074401e034040e030389181d12810341300e042444424680800d002840040207107001c81040740a8100166400b0010000c2d070080190344e09003c007420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 987084109 1250 987082859 987082897
    0x60b0301051509041805061605030a1104090207030c0c091b0c02120a06150b03011d0702030d020a0509090c07210318080a20030301090c0507150501050f0312 69
    0x400140280141280140d11a1905008203090f2010941105005201b00143c510640d181e40d10005811590851940490b6003000018007083c040c0d4032000e0360f60906107905040944030891402280c1111000720f000c1460b84180d5801c2c41110313030780400148040d010a1000003070342e40e0040c980c00360741200c040038001c5989003d8219550405040040780b40d00d0300703c40f000180f50422101400c00c61100d4290740080340008076258a1360b004482c140c4050130b8041c0c05201d0300d4814a1003048004107c9021400103100b0383e200101c4500042c21807100980d00c0342c0e15070b040601004a171000c00740c520704e4144410001c61000541404500d01d00c1d07402c920ba50003402e920080150b0140051380000041c4043d910a00e0040002c0000502461503240e034403030440b00b80e140e1111703440818000c503290241d4403d20040040d061355401c144596007451070181d041c09400e9441c415a02c0007081001d03400f607154001030240382810561801800c0d41280140700107008104128841e03c600d880d50724003003098030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 987085359 1250 987084109 987084139
    0x6050711060f0712030b030f0601150504030c0f0608180a06050402120304030515331f0804020f030d1704060603080a02060403032406030507111204060e0301060b030105 74
    0x5080d220342424110b000d40d528003140c901150041602d0203000302003864200112503500f0001101c001624160700101040c1e4281035a40318076810300d0f021401081350410022001234510b004480042401e284090405410100040c0400200820300425030a000d0440c141d0b0780e0000811818007500700c500081e05407a51b0000c2503481111041c1d90b9501d2100190000c10440009451040c03200985a0300c4140c1d00c03045040104481140001055050400300040801c0b400c21602068400c0051018490038001000c112800b0501681c407800315148904002c1076041024000300000c508601034110741865030009000f42900a81c942a600c000500041c10002560300c818090354220814036101d112100b4002d40c2c0c0c000403507045001904160b0a6540c11011a2907a0f0615212090001005062a00440082400070402d400704044908019241c88040c0319043c0c1807100c4a03002c5aa581c109080a003c8401c1c1b41d0718540281e1400c881007064460800a0781c0c1941d40c2220103c126810030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 987086609 1250 987085359 987085369
    0x1050f071e0909020c07081002040302061b0a051c11070620030f07060510140603150102011d0d020f060f220602130f091a1207030506091e030406050711 67
    0x94011900341840018424000300000402c00d007150707c40c0045902c801203011140080c0d01943c48025040301c418054094100c424a200f654104005021628080d41945986240074041c0300c1b201000c1c2c640741c5c00c0c500e00d189e006040140c0500a00e0003003120341e00d821401402d00d032415646106030422401400ca90403014001c464882130710401c025280c0740c440c2400d400034481980c294641d40440c0c0c0c80044c903040e11300100c1c80384000007400c050442d9640540780941d60002808a030465507180c00d11084e04200c454402c0c426841240204101a103250001e450140c40803c4172069901400820002c80d00c0805ca40e60300608507070500e402d210300002100c0200c06070800080445d40040b039070021202010040300b044032050300504017640e6458003603208071b4007211558108102081e0b00b800322030825840004405800034202e0321103e03540d03201c40f401c0880582d0f20032142d82104032030701c0c20040c840d48444408a22032000d9460149840c1003e030181c414504003d011070b81040b0049216610 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 987087859 1250 987086609 987086627
    0xb1921020405010b09030c1008010306050402040605060c01140a1503140f15100e1314030c0307030302070c0609050d060c05040e090c03010e0105150613170f01050f071e 74
    0x3014200b0321842d611084545040e4000c2d140e01e600038404d04501030224070f081040e400c03401c0c80503100c420659095031507a0b400341c030006209a1300591540c40c001100c1d15031078010005000b500c000054003114001088192040141031100c0040c00d000c40c01c4e004484001d11082142d600c0f50811207a950b1250f070701d50400d404894145584d0080d402c0c01c410607146011614418a050848003081c00d0311240c03a80540e203000e81c2d0403001100f02131040000110303200d568070260030015045034209003802400c0303032071580311000480c000b03900807500c0020495035480407005448181004c1000608190114484910f0000080d040603100c48001845500a9044401030405e803d032144142c608840c095a50380451040d442c0650310b4400c01200ca407406216250207020680d07080c030450006e20301040b0081d00001060034660400724000507200c80d80c00007038070b500581034000e08034031040c04ac605400c58000801c05074005003280d00f007080f180c2d80554000c014440c0b609002c1c0320307801801000c86101203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 987089109 1250 987087859 987087863
    0x10e03030403110f2b090302061303030306080312061027060206280c1202030406051f050906060307030e0a0c080120040b03070c060908030a0b1921 65
    0x400410710042c1944180790b9403040003d502154803043c0b00014050340d600346103500b405404001308039078404158a0b80021142e400300d241c18580300740c40350005609680940c1454214a0001400700100b5815005040c01409030402030350900f1000b20b40301c00344004c0104618455560b00c1250710180380206540e2a08a0917001c210403001c000500a02c1802c0490090902501c41c4000140d01c4a0000d601000b005440b00f541e40c00750b80384d034400103024008001c00303d07041c0580f80780d034041c0f20b80300d80c40998460b9010303a0340401c250410f41c82c003001e904652035910600b440c013144180b0181d1100c001c1260001400c1e00d0103542d9076600c0c0c004a00801d2a014070304594060b0010b08020f1013100508481542d90180003000f250a0304950024101a004401c0d001154140400c00024111801466001c000c40c1480f00781f40c85580d80b0401140c48840c1d04480280c1c2c08814411760a00910400f906020280c0e58100340f803640e501c030640009020b03c61030460814022a40031019010112141d91503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 987090359 1250 987089109 987089113
    0x209060d05071211040c021f23100e010803031b07080c0a050f0c151b060901060e071b060926030f060d0209010e150d060507022e020309010e 62
    0xe89070440f50305010041ca0081d1481c1d4030490302c0500501d8548103010392841e10b500280040c0b01c44100c40702808100070010013076150f84030078080700c802080d03a00584e11100c5160f58100c6190501d00b004c41d9040e00d030003848113510000018005540000308582d0000c0030304800c044603845c0607026a0313261003468401400711001180d00e141281c00000c08a1003c0d02c104147d8070390710030030518980e4030a589000e055100c1c0b14a81c4408600c800d0310010011800281d03c00600d0381c4581c9607480c40c0130381c10348417100140c4d036a5808100004022480301e8004240d4a0030b80820010743c001070390f400c0e00d80c076405000140d0321010042040001d0002d1300c17404400107203040d0000024041460650003c64000600c05801e1002842510f002c02c100c400132940104205400e03400c1508407040c81c0f2000f091100c4c034503020b440c81506941d800c09d6110015224440c0824103141c00e40000b4100f640f100c43c2009181e1445400441c1000b40c808490310031000241c0060322560381e0030b401d60241140c0c01d158a264 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 987091609 1250 987090359 987090373
    0x9151424040219030e030f0909090f0f060f0a0c27030c0f03020301051503030712020f1005071e2a020603010e01050315070e010806030f060906060316080a0209060d05 73
    0x10340703c40109601c0040164504100080d190085251288510380d000351031414100000f40040c80e04210003500804a07208481003001c0300200603191a61308000c041c03450340074034100b201600f91941d100d0390042d40703028181b100203100a005424450616041c01481c04032485011013804102442801150081100c0d200d02d03079510800e40c1c2c9402c45010a0b40130b94240400108440c400744504c01a10801900940ca84895520359128413900e610400c0c1c1103000715412203c0324402000303a0801d14000c420300017a1070030a84000f40c00c1c40170054103546c0c0210440c450070b40c0960010083c003582e2400240104102e00aa00c0c460031909080000a5001002000105000d101d6030100b40c181c500a9046580702d0801c014140020841121a07100103010801e4039441c1e0f5105400c0960048009030889031040c02c1901c41360b003400300498800d0400da0118003004000e1804100d2070744603101907a40318941509045046484020f40400a4002ca11600100d00c40b230701c4190b1404407043d00f180540d20300d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 987092859 1250 987091609 987091627
    0x91511060705030709120206040b09060f0d020a080a0c0f05030c22050102151306020f040513091b05031e19080901030c2607020c0d06091514240402 65
    0xd207800c10f8404c0c0000841c04080030036901c074403c21a88000ba001800380d0706140c58a50040d0b110b6110400d456005901070164100c03014100014000001164002681760300344d6400007420000010b061411140c101408142c0d0150080c48000620a1600d48030f03507a980c030900c108600340f00f48400d6440d40e81d51a2001c2070800c0c0441c4251054808c01d81c00c4e10355000c007602c14590b1524054406c02c441688080300b520000f42d42d580100392050303500003080c0c189581c03a4009441505802c00145540381c903998000e04010b64020884d00c01d048000f0f04402640c2440003080d0f480d210401c1d620200c081e0b110907469629003c02040080e54403541003220102c07840e1070310851a420140300240802d04000328261002d004000a804c89965000e0005804140c1c000e03c4901e140d0140450040d40250206402107844020030400e183d800783c103011582818030310b007903030750b280400043c1040c0501d0600c100444c1d0004a1140b41c004030707900200c0034144407010300c1e0340700b8600540d4000e81c403620000340411 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 987094109 1250 987092859 987092867
    0x204061203110d020d0f0e0102101d07060801080c0402160b04030903050c0d1101032f070201020c03010c1e0e04062615161806090e070509010915110607 67
    0x2040c102c2c0b41041e03840d04411414266070b100401040080424001408120340320f104414203002910148102c0300f2100720508101c08903142102040d1400c3d598409001000004000c1030006295510342a0343c00c2d0b00d04807405443c3c0c18501c5410341f20340d80000c3c40c00c0040740b0705442c1414950f00100c1d601503a080c43e117006400904584000c0300d240c064110000303610324040b21420340710360300300d04201c000c00b00001c01100101111100e1040c1c0d84520100c0c001440d00882091011407000b03942d580da6680c00d400064a484091b1041c3c51103130381000c05042499512529035912a100d90040d074800a01c0d1032403c1d1071101e1900d03011504545015800101000145c20307130f0020352481040d0146284040301c141d9244d4402403100e000a854500200d51517203070714400000504180e1070101aaa410b0926003000207083d58021800544800300c20301400d403000e000650840c5860401d10f140c841110006020000c4620401062110101240905501a6090840c21021135040c1d420381e1910303180280c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 987095359 1250 987094109 987094127
    0x204020a03150f05090109051f06050a0306080a08070210170a0c08060f011d0301021c0e06010605040f03030f050f0309060f1317030a060e0901050105150f160204061203 74
    0x59100029480083c501c0740611400b0103441010709140300603820000010f0203854080c02000c40d150b8280801001c3d41910318204000d00400d40e00e5964030404084000c00381c80c40c0340c0109103070350045180c540c002a001e008a174201c0c5c0e81a01d01000020761404141e4441c0d580704443d030902180c1c0400c224081c8000ea00030118280103494460070b6407034007014000d562001c0c0c3c82d22404925204130b0783e04c10300b0a4804100c2e07103d8005002500d848c0c10020b8403001a0540820b030f8502c0384d01d908403a06036440901049004d00454500242041d1a0203a55064020f407848081c00348000000c900b11083e00c10011206420001c4810a50301d00788001466030b540d41c200d5400c2c0c605040b42d40490a446683c1c40c80004894102d250020300d0303c1c08400c044103d60000d082c2d500515a03070280000c0200881080c1803107a101600005819890078052110080a020102c4140d46041280300d558407050300940e03020b440c3c01005500061040d1003c100141699000100107482c00c004520816030700003080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 987096609 1250 987095359 987095381
    0xf0406050a0902010f031d15041e080d05060a050a032001020c060421020a0e0a1821090b031006021204050d2634150e0a0204020a03 58
    0x10442036990100101c11901103410007400103542106200140d4441c0e00020354401e044002d100c848200d00320241c1c50060b1858440400400000800c014000c001c10111450b10403030030968400d4805079152101882180118610340350340f50007052940e210142030340050207000d4228010700391603003002c0030340154001c20f050462400f8071103800a03520100b0600482e020141040341002d081405c1d80c00010080400000d1000c3c4041017200940d5801c1d2404000704440380000900d402c20002c00300650b41c91891030060914900e01c070780c001402c0c02075003095505219016040149520320100c2d242042c9034030001d0307c90008824088074445074406401118090f070215401019141c2c051700321801030f071150641c000c3c030b040d442c1000f080914210788292080d545024041c05602a240b480c181c02c418010030355180340c400e0200007610102c440481c050303100b85803040042401e81d1f0f400c500a0504240801c0207443c3d00000030146001c0082c908802d900801c00e54869002400c020018101d000c41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 987097859 1250 987096609 987096611
    0x11503020d021308010c0306061d1807050c060c0f122a0c191e080d060905060148050a0f02041d0312130204180201030f0213030620030f0406 62
    0x49070813074602908c290012102c1035103030842c41c880020324070b20810b058040c1c1075800100d000941c403801081c22211520600c426194161035410410030340b0b01c1c24800401000c481e04003009281e400030620416180c4008030b400d0300c9481507450f030740030300d0a0500c0035525540c100c235030300d0f006804410024054400400380303004681c2c0008458801900019240d103001d000001440e030f103015031910190308400a42d00429885182002211a8000311140742c0e0110101695400c1400800e6a200340b03440000381000c540450107040c1201040705a4881c1081511201819500b41103001070020225492941000035903a9080342c038141880d08034000c5800700c0c4154501092100000b020006160410a03458011410301d81c80024103d541c00c2c02400c0900d0010703250700080c006a031240100d01c80850754150201c1a170b81284005010f60302643c00e005c540320700501141442410414662046035004000400c504100340341b01c4e0803c4203c24250310a001c800400c0261915400d083c2c54000c911540d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 987099109 1250 987097859 987097871
    0x30305060118030204051e0a020301030614070516020307050d060b0a0902070c0320090a0218030303060f011b120207080c0105190509130c02011a090103020603011503020d02130801 79
    0x1004481000c03042c0ca9000642d90000024009401d080c1e0115900102502c0c500b110501c1c222050b51140504a1f0021182900007006200f00a0540203440b106529a040c2a01a0810401c050454016440c04000b00c1c2c3c00c401e60701d03041d55000c1011030700502d0060a901141e009a0078200081c02d40000035600030f625040001444d403070b45108a5424941125030030000d142503507203101080441c90764218144105c2c4082c0c2505664034545036018010705940103903210030140c0003006840804960600c41d800c2070081005640341e4844610400c2824a042c01d511540032214050091a000340504081100904000303030b907400090400a41d000581143c020103144001101c00d403048010030340d4107070f6007050940252406034019142591000b0f101e6000d0b0b0ba10012200708892280d18030b080141e440d1034008020b184011140505490255182c0400358110740124034184418401c010350790511000800840b132003541510501121840207545e61280454944c00002d260701030b081c3e0325442c1030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 987100359 1250 987099109 987099121
    0x13020f04090525110f1005010816081c2a05060903040b0d0506030a060c030b12010513080f041509060f020d0e010336060b060a122313030305 62
    0x481c83c0e40300103409481070312609908030f0b0b04844c1a4a0302c0502c89140c45440c03005600715034240b03c080c2c0e0b441380702900000c05625100c0b00705d140c040320302e4420f10703140f0030317a0720920051201249007007504c1046000701c1d092140c03a500c11118000740c04412414961000c1903885461102d030107040c545401481140c40648407100e03056100d218920984411a40401c03c03821a4100f68000300c0d841040102541d4000e0025194042506d040075000700000360f66144d48016407408101134a1000410700c002c102900e00080450581d41d50b010001c0c0c41600041901500e400c503030350803a00500300101007a45010640007001c1c0c510680e0f40200004602904200c0614520010301241d40f0141c5503070b00440403a0340001076000701400300880380f801100e1f055500050881d03040101d030b078100059881c3e5a081d00390910100b150040680d181c4120b03c20404007070456841400c40754666812540040c001da600412202d00d0042e96800c80d070801090020400c40b0014016202c08a0b40643c5042c81903039689 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 987101609 1250 987100359 987100381
    0x90b0a210b2d040c090903080a180201020c060f09030d0302030a1d0a030c060e011e0c0203040605030a1515021e0c101115042f060906070213020f040905 67
    0x5240c0c0302520309560101c4402c00314200a50003e01401180401a486000607405d03900c03011001c6d0003141e541814000b205480384500c04400083c41b403400b60a800681c0000d40318940490381c288074078400b1500c04c10035a031040407558400001800c8503100c208003440580a904111002071030a45403100b42d00030594213215042019006d00c001d000c0e1520701d55000d5a04502d18201561120f90324014000e00480901c0b60032605507a1a1404540c03c03440300702c0c54240c9910350902d03411500140001c0001e5a000425650420480400800e040010341d100d809904001ea00c05041241d00300c220606464010034a02c0c09018204441d4503003417020302d05a90b13516100d00070b40740c00181c59510600303501e00c545420030111100000780d404403140c02d540c101c00b1000549003a6140380c240c1035621241c444680c159103e21940100700c250903010a80080c2941c00303142c8100780251000500e0340e0865655100c03a4005000381c0d20b00315119205d035a031030180340c1c0282c021521071600c1c0402050581c3c0e49 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 987102859 1250 987101609 987101641
    0x6050a0f02130305010b010e1302031510020124030b0105061809040f11102f0a050601051f09061119140c03120f07050a0c090c0f0f09090b0a210b 64
    0xc05420080703d642c00e0500403000f5440108044440f00cd00a48000b66546030042109401e50b00d070700200701404507541400120302906903080c95490000702c200005240000743c9411150122401364440c03c0e0701a50290302e21407220010350080e5103100300410040c84ca9542a4031900500003102a51040310602c03020200301408480820180e40b00460070303940743c80f81c0c50070f0900b0131040021110383d40783c1054540401346030101c030580c010000500c03140c05c1000d40f0380321643d03a2418071404480c03205406014421140102d608000c81b125800206140c100b26000002004055041e000d807038506180700340c405900c0d0000c115008810040c445440d0000e144080c2540d218683d9182041201c001d1003290300c8210101c0300b41c0204144500480c2502c43e04000402c0807107404200d85075455001480b0480300039201044c84142031501c0701040d030150000c03041c3d98051400041c0d400403040052121200c0303621804009031808046031203440702d12800300c655031140d00390401c2503c07074048030241905 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 987104109 1250 987102859 987102887
    0xc1e051b0409051c050c01060806060108060105190509061c150603140f06030111070f02030607030905100e030c010c09030209010b03010b030f0c070803040f03090e090a06050a0f02130305010b01 85
    0x80604d003411310050039103400c104c82650750b007022031502032000001429206194401c2d40b054024000300507045d600803c00315445102440d21038681a0601b5031050036840e00c48444040120100703582c00503031598400c882c0ca1414880c40703c6644001764810303c000c0e101200d00702c030742a202c04000280c001d00030302648140d4668018020f540ea51076841800408000a1407958950b4891605101c0078003442d004205207401201c55003800d0040340189840d20b040079040004041c50030711800c0101e00d010891072847c400745600442c06c0051350028a00d0341c015a80c407203055500c0c1000000b4400d400c005a00c089034400e54600c01303070740eaa981d00410a4002403248040065041001038800075554403400e90190040040c0c60170a04e1b0303525004102e030001c03101110702e547c4079030b5021f043c150461080300c020b101c5001160220300d00300341003035241d036009040244601d8950300031415400c2c05400c0448160340a82d011034951080005a92001906210a8a1551a0440c0a90300394032440f05642858 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 987105359 1250 987104109 987104113
    0x1e0501110304170102130602250509160c06050754030b0a0b09090609030f18030d0f110318060319091b08010209100c1e051b040905 58
    0x5841c000d64a01860f0030140401882d5500708141e00c0f03401142c3c8540301c05000075038014500040c200c0080800b5001d0200c1c1540d0890780341c2c0c2e040006503692069940e000c410004259050711550b00252408050000002e0005007040f00708001194804030081c9201c11048001c1c120406411110b00240c0d140032451280e00041f814045280555603004140c1c0710f440402c00c000031350790f1340310042d15110560f0020070701910381092003c0ea1400440158110030b88001611003806c0000c621540d034811154114028000841d4018800c0c0c444c0d040c4244800e000340c15181020b00320b40740241204000400180807070822500c02421000010584591451400c01c2007041e124410402000e500014000c1104030b2003030140c1081c2c0c01c50f038041c401d0890721841c0d0b06440c042c0c2d03042420303519010f10741040c001d983c03041c469400503a541641c0c01f10b00b500141807132002d211050908011034107160f02241c0107084950f81c800d0400100045101400e828a00303054104804001000180c81110001400d19 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 987106609 1250 987105359 987105367
    0x20160f05010506130527100515040b0405071205060f061b061305070303031a060a0f0e0d02010912020103060b12160516030e0a1805090d0c021003090512041e05011103 73
    0x840b6a8804444d900707459800307e818040c030a000f40781c01c1d1101124031401400c02112008542c0c20640030300702100504030340512141c5003100004000390303803843d4511842503d450109059846950030000d2060014004941d2144000117401926045500c00751052003414001110318203212403841c020307070380800686460743c69514118040e10400241c02c1020b2884480407400f551403a004000c446c001e500d40f13030201500200c1c050030107400c40100a01070001c4410320b0005070380c0515140f095a0900c2d09880da403460a0004800410b80d54001c0d40c0c0c0008002209100b10740c0c2121138030300c00d00441100c500000300132482151540202160102409421050680000d020702003864041c203020744848002c90342c8012034500850000e00d135444180c0d45006120810009110b43c082c03000c80ea08000285420513030100d44032250300d160bc841017541c2c541d4036004000f03062240300f6081a4512400703407035586a440e031141911401c881c2c3d122018103100006180d5014801d081420180ba0000d1414 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 987107859 1250 987106609 987106651
    0x200402160f1b18020c0c09090a020109140310020d0603050304120606080c0607030f030e071d100308070b040c050d0804140103051501140910020d110120160f050105061305 75
    0x103500003a108041d80d009a034021a800d847e805280c0b403089080707000510710300600b80000f400350780356500241c601c02ca5640461405880c0025290081d070111040181d44080000c1c19100419464100601c1800b000900140c00b210080c00900164010b0b44208030450341d0700303955903a0b01d44509030913800a030107016510110b0f000e085800c800003070504000ca400840c944180303041c401c050b00008440080d1040301000b004216416690040316544080465070560f10740190768064120010300f100c1c501000541041403415211004010141c500c4801c1d41c5c0c58030b0001c29541040c0164604c2c1c81c1c2403005914036601c00d0203114065074040381c18189541130f0800454895418034101600d01800b04046403140c1c44081c18054000c7c2c42c2e5000e0a1544d21001d00140041b01040b10b0142982c10700001d42c1c91103101c1845d803e1403100c007118844e40c030903a03003409039400c40c05204090807008030762a106060142c1904600e124000444a41e000b101c13161540100315902a65590140b0b41d4042c00c20107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 987109109 1250 987107859 987107861
    0x62c040f0b1f03150803190504080610030201080f0709050f03011e0605091f0b28020606040c03060803180d020d0614060409200402160f1b18 62
    0x10a039658004040780c42100307800410800c1e102c11211211100480c8000d5420701c0e0325200c0c1d0180348a20555009505190845d00c0e036403400f030f54481078603030130000703000c040070b14018000c440041c80d0100c02e8500c2d40c50105d561701400c0090344800d030702081b004400202040300d43c4940304d10942042d115400c041e0704101c01c1c419442184881690190b6840d03400912440700000d00d00d4005c194135501103451400e010501486c400d0240c004c2080300b003000891090b4500c0e42c0710040c1501e0400042640380e5203104809940b50001140500702481c1e50310755010280e0b40420074034816841036074140001200000210300701c8820b4400d401403600188000004002d003140219009540148454004d07850354000070302041e5024400c40d401680c80d40c008000d282010031180d4041d01c115802c104407441e070348981c1041e207007a2014040580300c2c007180e20402d40d00c5605a4200140c0c0c481108011996450101c10004400c4820b85542280c2250803443c17428060380310f0b054900b410b507503c05206405c20490 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 987110359 1250 987109109 987109121
    0x20c0a11040b18150609060a030e01090b01030f03090807060527150706060605120f0613150812180108130816031b0b0606070302032101062c04 63
    0x3940c800e03181c50540416a440c0e500803104401c40300e01282040c1403884004018840141c5214055141403041005035614081900e0311010b8274240811705148600768140140072102e00184994001c000100a002840c03101c10a000e2098944520b85610b880f1115640c56003071048a001510401201000d00440f117070f105820b101c290884004200040005040c0000d28034036101c114101040042c24801507005040061000b0700b07103203180141c081d0305c002d0f25820043c0360100f001c449002040b00c1d40c440c00e44414801c0d030079039810000d40c080c0c00b05000c0b42c200640300300c42c2188524011107030b04420b00d4044034400341020b214a800301e104031005481408004144804800300c0302010070106045c1d40091130002c560070b8442044515074503014000380c81803402d42a24a802c00d1701c1000054507001490b4001030225400c640710000761504a01e144168402510b006c050030011051541943c1c0307155069400c00c1d102e10344c8694500c011108217060180c0050000d851085814605080c964010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 987111609 1250 987110359 987110393
    0xa2735160b06150f0d0e060406020c0d030c05030609091908090f010e101b080c0703290403050903010e072c0f1612020a020a0303180b0f07020106030b0403021609020c0a 74
    0x101d11b20144560003401c0c86011641541d0040d0006014841c100041c8070a00d040c2c1c0841c2410403084c2a118402800f074040140014000d58540000c140130a0082280720451070750203603c0011510140f800c030304650411b80b58180601801d024640181d800340b0001c408800c4050440300b240c4c3c1040800719850b4000080a0355464144014103012501c030100a2240e1179404006007003103403862502c002201c41400b483c0c0211a040145040c594034115122178016405240c00380d21900b81e60000b034010301034138400002d0307403050310340000d40340000c08400c0340b8441c0004112041e034070a004066080701c0d030489a964140d01000c002480b41400c0c1c41400c0000e03508d03490320703020b00703403a00c00810300701da200318203080250380000140350825501d4000c00c584807245030090750142c486a0703220845480054680340b448819080040c02062007580214000c0d0b400410040042c145401d01944803c641a9840c082060b0f02d03002003844840344c02101d000c4510403005000748103044e1140b011450617500d034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 987112859 1250 987111609 987111611
    0x40602070201170c040317030103050309040902040f02040311120f06010303030c140703030b0307091e1d01050c0729060904050f060a2735160b06150f0d 67
    0x9041d0380301e41c000d5504d21402d101a0760790780e900e013941800e0045da502c21003d884220400c000600010720044141d800c0b503001541c02141c00c9003907100040107848540c107104841340c400b10f400801c0c0980e070502500048015500000b442d441c100946071107144127003c0c03145950040004100181c4a58031003132050300c50b403504001d8aa448240100c46520080c020780003ea00c52040d000c0174541070060b04024004008100950903482500d4210240300003030340700240350383d00c0b51030750b0a0080c590751540c840c0e0a000204201c0ca07010b501000d0b6034012503000e4518030031040190603507186503040400d44102c0428441440d0307a81070200800003070010811203040c0a0003060340c3c10410208140da004118650011075204661074003180341012400004959503503203113081c804502d09074080710408946c01c8040f013040004da800c85640410281d803004001000003203511301c4d41c00100580b90550310403001e0000d41d468040800100c45440c083d1603029034420440c0c12084200701e00180103c4c0107440c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 987114109 1250 987112859 987112877
    0x403021903020627030706020627030a2303060a030b071205070816260603120a021506030a03201603050c01090806010612090c030245040602070201 65
    0xb01180c0c880d00100f5058a1641e8102d010080740c0b594081c40d0321610798160b000f020b01c40d2900000070f513a041d002d0050440b41d80000900c0c2003010b0400003c16811801c2c0e400c50781d40d1026a04001c040b0b035440c1c00342c0105400d000010070380110600003101d0240500800d400b10107400d41d1224407403080064003000c148840d0401040303940c1d00d00e0080501c188480c0d1a44055031810310050005085414106400c110610001c1c580001c49000040d148420420b5040c00e43d50741c0c080460300c1c5c8856112080e0001e440402c84012403a400a040b00d07084100100c001c0c103030b8807035405040c0c4e1085a050700501182c078810082101d100000000308024403032504403110310030f541c4a89094030300c054005903070075000440700d43d880756000a200c20040948a0007070180b90f1401700f008240181081d03804011a484010a509000c10005020099a001000c88264034101405000c191003c0d908500f8500b24030b02c1481c8003e00079001c403050207200b502010a081d55650354074002580801800c0741070002c100b07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 987115359 1250 987114109 987114113
    0x3080913090b0f061e09220203100c02010b0d02062b060806090f06011a070501021b0109060605060c0c120f0d110106080705180907180b040b030109080403021903 71
    0x240403103014150b02d24078041242013100c03d126680888240e03944001c07030441c070407034034a482e945170141c5d02ca1500810100d6111841000e60a4502d11400207941849136a440f020031010941c80002d02d07040a030000c22103001d9203410300a10843c498000381d845501441b968241958405402c9800c4044a1111940c0c4030f52614200454032190446806135100d04201b20b0340a0040001022a92100004145561500f4154950345040d0000080a104045040c404000c002d40580c1c0c28244000440c0d1555146c61968900034103d84005613016800c0140014031401c042c02100d4150107443c010700396000d1541d05104000c19140c5030600c1c1845004084000003906000f8002c0000803a618481110141c0c8400382c00d5804540001803207400500c000c10040d42e5148031400010075103002018680e03155204a403d190142e030102e80049564103a23112940b1450307000c0802c01e40d003240e041141d0864001454203c03001440c00030b042140400c404e001626206003200d00b0300c1c400650140040d5229 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 987116609 1250 987115359 987115373
    0xa15020d110d0b150f070f1a0109091217010605070503040e0f0f01090b0a060f020a051524090402060f0706020d1a0d0b2a03100609060203040308091309 67
    0x6003480840240d40d08040c3e02c2e01c0c07900d030201905100c962903000d41441c42107000d01c055441004001440044c03018525410020b03d040a0050300c00210210b10040d079481c00303514084c3c80481d804440412403d0880c11616004034246068107006620f2006640e00313059056941ea8821748042c0c420b444140800101a44028280340c0305000c40c0c601e590940c00c00e07601c0c60480f2070041e0402104c007030600c1849400d80c0c60304601c17001242d2592a2080302c49240356002ea041a0b206400a0168024025180e01002880c0c46c410f0140d11004085840c180013480c40c160b13801d40c040f2070258003400200125016107808806001044070003c203552410116907502800c0703a01c032004613400b55031180c013184400702034216000490036080e0760040d0008003954588036520300003896075003000c81c12441500c0703520f58030154500c07160f01c58003c15a24103290305161500359191040d400003886e403030341c089603503403010064500b1284d200780c406007015005e104000003240c0184140d80f01e1580d44041e58081458 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 987117859 1250 987116609 987116617
    0xa021207080f1c050a0c0203010203090a030f0302040501090e1e1513020c0322080109080c06090106080703061e050a0b040b060a0c08030405030d0c050301080c030a15020d11 76
    0x1440100310305841d0000d690305002c1c0d00c0700030328500c0c0c00c041a01c3d42d400c1e003550700c004010403261070140c1e5244008041503038170502003d0b01075010f40c401300030012410701c002103a514143c082d4407113180420090604070241c2c411406141c3c0020710000b0f00704004a02d030010613410000c00e00080103c0d10507691350b4948100104d4840781c084016070719004043c1001c03160040150034554043d8034251420402640e248184580d0f82a09403440484007403d50a00c01c4890107460700c0002032044c92001d0608501c2070b041480318120070b0107586d0110341806414030407038040320f460001600c440d40c619290840200321440c1c110300204850003c0e440303001e0782d03441494482d03130724020f00007a0358641c41c00b0b120855071901d0400f40a00b03020014001c1c15500305101c0c0d24542d600583c000d0380c030741c0c0c0c9190503415800380c00c800240440c20082400d40c429000005107050700d8140d002c594400c0040f0741003698030030782200d002d4010000f0320010460300201f1f4009040c500064072010a5103038001412414640c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 987119109 1250 987117859 987117889
    0x30904181b0f080304031205090409060612030912170a0e0904030507061b02070b070503090303040b0306030d050304080f0c010b1201050a0b0901240c0b090601170a0b010510020a02 79
    0x1e180000340b0003080225005800f50001e07400a504060a607034036460350307904012a40702400800f05504072550f940d03030004110300390300c90ba0070b000d41a505c1010b01c50420101c6401c07008254490004501c24006120580483c0d4202646a42044a0410f03240c1c00303600c580000700c01c0007400c010f06003298440c40c015900507840f0b992010b80d11802820150304913150315100b000180b0b03146003403800d02580003903031100b03075007440214960b103150b58500306165204114815405020120b400507800a030344024500c520025800e82d1701054410b035049500b807004440041c0791301800c0c81902007009440000d810000b1f036500002a1214070540040c40405052040821680d111000c000108800740100c6103003520a03125111154103003045a0135200320041c9040c002e1000140d0322900911690341c0180d9a50007001c00052410300d901201d4640d0310074001c0c24140c000111071402d844d000090041d041e1034201000c400701e41d081008002001c1c00002903d0f0862254400050240e61034040401d4440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 987120359 1250 987119109 987119153
    0x15031003031b030f1209140106030c081f0b0d050609060403030b0a05010e040f240614120f0a060b0d020705061503031806130b070c0506030903090418 66
    0x2500d140750080c001242c84202c11040620503205000007500900c0805401026007042c00c01000890103003c010420764130054140c0401703003289070309240c042d88444c00303607400b030082c50100585810074295222107040050000503181c0906000c902040c0d40b001c0c072010306c0101000ca0001407500d51614200d820340e20b1100c0f0f0307081101400109501403240c911221026984801300e1442c2400203460002204640b5003d075840d24400f80b81100503a01582c0410141c500022168000700050f2140c0d29a0f4060940855030303403940c400100300c0d0364040c0c4a1a5141100110086d41d520405041c1844081c1c005903017a501c45a000c07490721084005805801c4402e900145c0740c3e462030030301c1440c041001c0d280c01504011100c141043d51404030413a10b44541d1080000c8181a02c040421828854122400600c24007002c011826010200081410131700850700d100001d40c54a0400640344004e030b540703000c5a84200001001400d05030402a000120125000c00310119030300c1d0441ca070341403113400359888 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 987121609 1250 987120359 987120391
    0x7030b0c0a200304030b0c070b04080a080705180d02030a05101e06050d080c070e0103030914012a020307030209040803010501110f101d010c020c030c030c0a0e061503 73
    0x35903481805940306840c281214650ba41e02441d0094491069000140418807401d00046d04000d0440403141d006501213420481d52410342000e40c2e403030700031807440d2002032a0b60740490061071241056400780780c8542d0090880852040c00c2140b00000c00f60100d0701401740c2e007403840109030207204900d21035408020102e075080d2040c20a070f0401001d10307030800305107150030810b101030f854000280301c2c050780c025241940c441e0900780840c41d201444d40010405040f450000c003c156102c000c04080758212503611006004020054420004200220b001400501c0155419602c3d410078030b0f0500780090141c40d46c1035140e8011901018048400f0307100e141c80000100020b59112120040d842c05403005021086211241c0c0c0b80c0312040c0407144003450781c9601c0030300240e0b40440700c11400e51002800820a0b00b4001c039000e900e5804402c43d1511a0065070040c031f202c0e04011910700c120007001081d103034600f401e01c1c40c0c2024200303002d41001c0d0403800440995211000000065006e00c590342d03200e800d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 987122859 1250 987121609 987121627
    0xb0f0703140a05010f12050a06020c0307060204141008130b1b0c1e07030f080a12021c1b050318010b0d0807050618060402010c050c06180a1508070f0207030b0c 70
    0x403242403503003c0043c040421201d000442d001042c46230159500174000750791000a000305920b5801008406802c40784001400030f01401c00da041c1800320001a075200081d510801e1060700e0801d011109403203040000400c94000510071078095034040b0003001e107980110f0000802600507046104010441e038007200c00c450b03040e8580b010015a1014020060107081d040d50789052048100b14001008010301081048849010300c140f1001141e02c040e00315120450910600b083d1101c0c0c0f000283e0030340c60714036000b815081003151058550b01c030b51511495510361104102110351091040c5059540c1c134803030313801650fa5640243c0807003801480701035220807450501d9800c1c4640507000031001d20961a018035042c1e0049140340c0c0c40750702405c05100600080c00c1c00380c146496040ca05510050020b40c2d0705030100303408880440020151283c841c41500c0d01d0411008005001005020455000005100522400b600c812280051040c0c8650b1035072644e420012800540703034000081000701d01420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 987124109 1250 987122859 987122879
    0xe0a020910060906050a02011e1a0609220e0d09030b01210201031a0a27020306030307021c0c06050a26013003050901021501030b0f0703140a0501 64
    0x34100e4850440c61207000c1c60002e01910041503480380700180403000c02c04584d040d00070b520000c0924522400d1400b1032003060b0280c001014002800d0f100d030042411130340190f0803d07000342c070100d42e800342c00c0d104940b4910b01514840e20b420206041c9480c0c0310031580b4140341091081e0140305a182e21050910350540c9803a8502c000141c001d4201203103c0c0580444a092909140e81c8003502801d0014031503d00684008410522020003030f04510915000030380b80134451a482c00311207040c00000d07250400304010405031f100950300c8980c594400d2000d0390140c5071a1500402800613140ea0241c000e1084d9510a20852158071070800710343d0101c0c0840c080d540003004c044804c15030800300d20b1410700c5000d0340c188615040c080d00580040110303880a00b01d9454245450440c60009445070982d01842c009001e07510540c0c0c1140180100402c020350b49001491007810303a548a083c0300c4aaa0f180320003918001002000c0104258a8914101e00b488640701c0f864090180f1010200d6150f043c0802c4031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 987125359 1250 987124109 987124111
    0x370c12050d09061d0409050c1005041d040c030221010f0c08130b0103030e03120d020a03230c0f090d060606080c120a1a1504030614060609010e0111010e0a0209 70
    0x4003030103007160a104c00b9000005840c0702610007194001401441410503031700d0900340c6c000c0b05811071500c3d0032a040407a0014040c100f210080c1c00c09000f070500e50151082050810755009040b80c1440070140014903104603425849401101c41c03144c1480c4010001c1d080d1881c1a810070710741599800310321012940b00318201d500490310200d820030080036a0b44e41c0241901440081c041140b002c1d11018030307030340601429928080d052005915440300181080081d0710040001b00400d151000d4005070141c1303010300505d107080b603201c0c4517103590384e0440298140c2d000301b82600401e0700800c14500582c3d907141e46200030500650340029428204440684500e402401210100c0380c00d1010300040d80043c031034540c0c0141d080c4004100c01c106031116180c400c0000000951017000d4503002071104451402a00131203004800600c0030410018400c4140308042d42d42d540c02c04000c000090307182d4000c0c00c0003000d500741071401c40c0301080712205007400c540618100b072046800c89841c0000754503120b1086d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 987126609 1250 987125359 987125369
    0xb040c0609062f12030108060a0b010f11030d06030b06131803180503070b1206011b06050411040c020a05010e010506012007031e0203370c12050d09 65
    0x5544407606040000c1e01544400c1c0d03415038101c0e001459040001c2800d08280e500c1c002030070440d61241c3c500c00124060707030405d00a10000d84101000101c590740117004989400806031030318054440d41034021140b810503182c2100c4c041c801041607245c007011500c149002503002c0d4a0400180c1000c00401890301d01002c00181301c542811b00200b489401020900000c1e44c1c1403c0604414041014110300e40c5515400540d141c042c030f03d000102ca40c0100c0050101001d440902d104c150f40c1c003001034900c1811809401007400c04100030f040010340c07642c4110303009030151100c41d1520b92040700003030a848d00c0d02c0d150001a041360350031004120342401a180784060300c00081c021450841c000a10454000b00f03201d0318450380c0419040c00c078805200b1b0001840d0005c2550010482900324000000740b80b010480c0207108481e590b103040a11344500c0d115109019118a071040390340720040280c040d603c502a6400782036850001030003030740468040065486100541840841c140003d040441590301c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 987127859 1250 987126609 987126617
    0x7060507023c06040605010f060203040e04110d1b063513060f090b07030911010f110f01050a140906041b05091009051008030f0903030f070b040c06 65
    0x401e022654105810341a00c015010742e84001c82000c801400c607054511072070400d94007640c4244014419940c01650689150b040055503a03681c0d58001c1340d80744102c1c441c51155041080102d00022150001840c00250042900d2084006500d82c15544c08118040c9141c0c61301d81401040f00540005e4242e625a10ba13442c0490b40803080200110a001c0448181821948040015410300402b8460f102c1060b00b100e0100100302c0c40c03100d1240188100340c1c0544501c0d20050000300010b2181c00741c10041c56000c40100302426243e401940c01c070b01c5450020003841840001d40035280403c020340b40c841400c0c0b50012a00d402c0200b0340400316103400ca5003a12034480e07242004100c40c030000703844d500306900c229015000700c4404004004604c030340c2c1044d54013003d034209001c0b0540505c00c42c2c600703031023082e4010856601c9513134a524100e0703882e2003440c00980003440f00184d50703d0070740013170b29071240080c060f42c0ca00824141c808207107a019603411241004c042050209001c048445a8050300c000e0030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 987129109 1250 987127859 987127873
    0x181f090b041a0901030204181a06030402010203070609030908030a02070f080307020913030912060b04050601020c030d0503100e0c070606060e090a0b03161706130308010611070f0b0706050702 84
    0x162540b5840c40c40b080c2d191007900010002c0160340709070304a400801c1702e40240465240c2c0842c000000c0c15500380c9988440062401a542c01d181c6182203c0c006c0d42d05800951922216a8400c0c0240c0b208a0341a024403110580000b4440c800b880202420380306940074100c82c1c0d043c00c4500c4241502c030f4000d0003c0342e2060040400584505a0086d0450709102003443d61643c149411504a10320b44c101c0c4c0111a9640034050400099401004207200115810b0201d40c1d10030004a981d00b5098461580c103a10407074001c4d800902440c002d503000000400b000701000c0d01c5c0c0824200400d002d54040e51816000520002444414031400014040620f403041c1481d00c07110003d91b0442c4060610800c640d51040c482070140c1d4100041c0c594028006e1448074416921403422420390207450044c005400341034000ba00340c8105405140d005985600c41025903420300384100c44240600301401c0092186040110388810b4680b481030081081011360340e0b561a151420350240c0d1030150009040d50701c200707 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 987130359 1250 987129109 987129119
    0xc0702030f03130b030a2c0c041506120b10020601030b16020327040f0c2a0b19050c030402010f18050402221e080304060203030c181f090b04 62
    0x102c107040c00c0780c0c40c041000da165180c070386c10703035000700b40c01c00c08104400c0d40780000310582540c40c0444100e0301190003d0302c1e031070765004090200f07480c3e44101086041e0031400040c44030f50300401303041e140643d00082c009405404a0007040c105582030b0031000241e031082c030041042000391240325510049110b18040c5d8680104800b9503207004080c14400e10300341114480c0b002c018603d9103800c1d031050040080c48060050302c1000001c0054404100c0003d1000300a004200c008034600e44402c0c9080401c0601448c02c2e46a011181901030440c10907008103d4060728500c20a0007545e00400700295500e41c0ca00382440058400c5400c2c0180f4018032a9801070700080c008442002803ca69060b0303009079a80561903c880c10649200c1c481c14000500600040349000304184028050b811400d20304910306d0b180c6404542c0c0780200e00c100001a4410400545980006400340c210320329565400c00a10b40030f540091044080c0c070360b6a116458400c24805100c40d03120031004010000c114405103864141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 987131609 1250 987130359 987130387
    0x1312061d0a12030504170a120c050418050c120411100c02010e0907180b0c011503080703050d0f0c0302090102011d0c151b0f0d08010b040e040c0306050c0702030f03 72
    0x80b40550a15645400040a00c9242c40400c41c098048400d02071390345401c910701800b040c1148107084c001a29040003030040e54054422681511050342e40c00720521800c01e900c00140600030000c0b5503814082c0480c40b10341504843d0180654030820a80b01c20303000354024801da40708805c0d194001c1108504030700b00540d8226011030342213801521450306907507800c1004c0e10110119880364200c020701d0140000d0a030410030161141a050500900c004e000480a01ea00d40c205404090118681009a0400079018100400bc0403c0010020841420444031a0704550124021001094002540300b803a580c1c284601c3c070b003c0d44c0c00301c0c120392920100d0b04c8469480e0641c010b01170003112003129a02c404d008410a0711803032a02020344905079001001c503907442c0c2000c0d00f80c6400314401c140c0d10a580d54020f540d4603050b5000081100d04141c908040b80d0750501c4060001d0f03428415408010000c14039074010741e0b1140c0c120845030741c1d03a00501d10505140c484001d6200707899810501031241c0c0701e008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 987132859 1250 987131609 987131633
    0x150b030c07050a05031303050c0301020a0f110c04091203051b0a1815020708150601020c041e05041b0504061a07020a0e04061a0919021312061d0a 64
    0x199581d00d8554501d8128501510a140982188008101c21100b603100c0c20720042528419402d4501a50078001418240d01815000e2008182d0400c803600b4018420118241050080340c00c4840348100080401c0440c2c882ca001030720002403828980901640600072650041403103025414103d076841e440140798060007900e0001c0010502141102c81e08402d41007000e05003a11750300840d40340495019548400c14030440c490340c000c00202c00b0040c0d1264260030b02c00c04040e0040d000d10500c10041000030810030410404510040350781201c4040140f050303501c2203200e20341596480020607014802d00902d03921a40c881c0741021300902248010f6034055200c1024961700945032100e40c8001181402c0075040b40441030000d5003000140411500142020701010120000c240c801105100c3c4e2000101c442ca24441d900105945c0c000c44154010800302d2410941202e2183d110070a04081020541042c1c078a591182211a031480c00c00494000d5050800000c003c554181c0d0355190780d041e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 987134109 1250 987132859 987132871
    0x6130e10180b040201051c1503061d06040b0705071203050403021c0504050906031c0203030a050601030c020d0c140106080f060718170a060c020f06010e10090b0f061c150b03 76
    0x940030600d00c600e000c500054100c005c52011082c00b239002c6100520200ca107841c40259803c07820700e5040840d82c0010906441114004006450749a40340d450700100e80c00041c0c1070b241000001c00405000c00e41600d80040d8120850780d0100d0316040c42d09000741b40c5490011001042d492046a07560565040b4007118202e480030744180d104d65450000081c240350550030052540314030310151103603044e4040001c511440340e803002000306840d004011401c4420a003140130141e440034601d0400a03000d0005412050320400d0004488040c440c4081d00b9101203901c94401c40d4450762841407036072030a10249500c4900d903d8030010342440c03020003880d100040d11403001102c0c41d0300c04c00095004240302104400d60800c0d0148503904622030003e60703890034981070604038000c2500108100e041b408000f0300031814604000c0c505420008c60400400b14000c1040d8480c18001d4690816103945020386000a0340100c4400c90900f00d00f001d41c1079410380404001403050740c91090066810a5003601d40101c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 987135359 1250 987134109 987134117
    0x3060907060305151009090f09020109060302070609240e0c0d0f030905190806060f01021c0c0c030503040303080c040f0b0c010b0a08010203060a050d0804050906130e10180b040201 79
    0x900c4540603080800c200a401e55001445d941c5c1141d0401d4000d48544116114494104000d00d84691100105e5103503000003400a01541010000035100390085d050b0b05018101c0000e800301036030b892098007a0b801d50001034002e002c44510450204900c2110310003481440601440ca01c2d02c80015550b415000006101c08856100442410310480d1100050100580081c40d00341c0d49031021524050700d88600100351050000080c41400e0003d4036200980c1c060b00109020f41040340d0300301e40510310042c030130104501c1320784101c041200240b45000960103030300510b03516400c40c00c004100ca50020052920000100310812110b6603410103a0110b9070289000741d03d400d80c403110789014240c0103419a0380110000d101143c07545d07065008500940f401c0328052035007540c982c10f00030040e01005028090360001d001c10030140c24400403d0743d000e40024005031050410340100802c40300c148141c500300b0781c13160102030302c606403034030440c0c01703283c000c22821941000c15594440300c038100a0000b4100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 987136609 1250 987135359 987135361
    0x60303124d030903030a0b1e060f0904060e061008150402030c0d020c011b2109050a02030d03090303060b12181c0201150b0301080303040305160c030f0302060603060907060305 77
    0x60207100c07010660216100400701d42e24140318460f2075998006441c5007400d1450100c0620031440c00160806a4480c4146000700c1510910200080c5130030030225045149020098808259520710401c0c1c0034211190390710009083c03035010300100040b66511502800284024848004002c0001c4500308001301d40150f9a665104030b43c0c05103000f02c1034401d04080c00031a44030032801c41900101e50103c100c030b549980406450170200e540c0a044650365803401400b1a07a0614482ca81c0c10801c80e1601400482c0c1d40501254042413810100b6104a000256900026001c06d6414001c0900906c905490181042010703040248580e00141c851040030b425400040800322051050f408148140e0710945494000c101001e40600a1000e002030a03903411200401c0c0002000c06881c10ba0303a291005606668440d50141c0301540301d8000301c101c281c1c102911400144448402d080a5032040b03c042401e170f000c500d00a4a00100907251503c070350410706c100306001100007208404c8070f201785008030751 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 987137859 1250 987136609 987136721
    0x60c0b060604051519080601051c0b0907091e0b0919030803070c030806101e0318140105130b0703150801060306140a0212270106030312 60
    0x144182d038000c980200102290300c910034000d10117458824992122003160f5000307030300200c40da03400440d682400700d0707400e0200c84e8684060340c1c40252201038940001620511110015200c141c0c112440c0300002c400b190305102d10407008820998285800701e00d07070300c05405c20034102c0490080703e0b2144c0c000e141201c106464100030389246401503030010a43c40d40e07424200001055002e650f201030300031900380030204026080007001ca00300030901c1c0d500d083c540e110943c60320110481c000e504c0402c041d02c03000306000022907204816801d910038130140c900205045034141c00c2d18002042a004101244400000300d180100c0ea41d80c0400580390001c1c20b00303280c20b200d4002c05610f03045202190318014000c001c20429a000c10075000b09c4600d071110960700c84065506034400e1400c1031142902c82c3d004540c01265036841c0c00ca201040702c0c03401844240700030001e821918294000d41c00181c4940c411030800d402441494a00e000c0e0a41070207260b8866005103401500744000b885a0a01c030414900c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 987139109 1250 987137859 987137869
    0x4080f030a0b130b01320318061e150f12070b0f04080606090403050f0a0908030703020703110a03020d080c121201030213020a0e0d080f04121a01060c0b06 68
    0xb15894014201400c162658002030f00a044803031165001c200740d03202c1c04036044d82c07401d20400342c00343c00341a403110f4420001021001d07420180088200c8411005a07240e01c050a2181c1d6100d0414421580c540c69500032103d1306150000e8020300d102e18404004282548842501e07802c03901c2c003601c11031070110000c1c00130742c0b4040060341721044000740815100c130390101e00b07801001158030f540c0459034207480782020400c7d490342c2994014003152080003da0381141480c0302502c0c045100e400c0644d041643e0b5451941190720543d0202c00680050350107004002c81d2054203c2504c006a0300303d0652429030313001c55011852080050003141c800301b482124004108201e48581c0c0c00448030759111f2004486081c01c950080c0005c034400c420525003459510080d2080d100b40c0425551a0b964940346407062180201e00c040c1c041e214448200310481d40760452800800042c55100d0300841656410704122903080659800061110000d80c01048155404486420400e41045270705032580c4810b40052 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 987140359 1250 987139109 987139121
    0x305270102063103030f050c091f090f0312020111040b1204151103040507060305040312050711030309161d011e08011112070207051e010203120903091804080f030a 72
    0x3a03040d8100f1a000704240e032681000561013856003060040c0e03140d6000501e228040c1722001604505014042003040d41c0b4100103a0b014000741c100034a22544441714490b09034040d81060340c4203a608085a02c01d664244505100c12802c0312000342418241004d20301203116541ca03041a06d440d060124007401135580e1040d00014145000b04600748513040030710242c1e0000c43d420f44090203018800642c20f4000d000d03d5220319071540e9440400e20030b61103030100401e409060881009164402d54116203030410080d8062801d4000800c032110307250002603403505142e08a40e00c6c00301c20f00000845400d00c0c0410313605441007101002c882101d48160341c1003440140c0e20400ca25828000f03141c800c01d403a500105190128001d02001c10b503140d500c1aa07960b0000d01c02d5a420242200d40100812140c20700500305100c1441600e203441c90031a91420345040540b4510180c0e040015107180c0342c80d1400181c2c646001013400105945416210401d25008241c28101c032494000b0000300d851444d50310003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 987141609 1250 987140359 987140431
    0x5090310270c120c0315200309031e03010503011d070902092403060109290d0212151801030308070507030c02190e060616060c1803030527010206 64
    0x8843e01e49898101544020814031040d1410241ca101c510f224010a009100c00c21034107600e0700343c0d003001d4840c0654250b8002402c0e2580c0780414414402d00320042106d00301680d8443d01c2c020307102c4d410075040500f100d0030035007081c500f1000e480300c3c42c01c161408113000f012119600001a25020200003151414030510705101e030145080c07440b800300e02c60a00196004810a076691006140c855030792411000c241400000102890b0000c5624411020300074012211032040150801004614011090900341d407074881c1c1000102510301d060504404c010100a090700a0b0005035155880c0a016582d001d0500801c1000006d41075042c117000f048001a4980e0140802906004030058100803180a014041c07000000c02d01040c45c52800b00261074082c0300c512042c00ca008501d80e0b410000b042d2000820003800f05801400c500c480d100c5101c14000c40c0203850703aa5032002500c100983e954903100221130103204440b41e203a61642d000a5455001c015450220042e000d07403002da5051568200741 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 987142859 1250 987141609 987141629
    0x9070603232d04050106050d050a261c230414070b0301140a15090501051602090f090f07152f030c0f060105031207111005090310270c 59
    0x10404509814a10f00c0745014100802102d0b8403001003103c0081c0e0510060815800311000501007101d11a4410010489003130101c5442c09111001005400c8207210781c40d44800c5020304070502449004029044010400660a1048d4410151007451016101421010030300c601c524000208100c02406055058003158a070f69660306000103514110141600034080c40500040e90b02039807142c29205005622a030b4146400d00c0c00440d11504a10640d03905107411180600141c0ca800d006070b8040c08402c0b1101c9401c3c42e0440d4000e00d8001c0b074010300c8110f58000f420030881c1c0c00f03114070b144401d030140e031501303100c000e09101c81c16422035086412203081040c140440006590004010207a454108042e11041c66000b03000c2d989415007407143c9034042e000034010400e92400c0d10002c01101e40710740814165841e2100200d0365007188085c40740d0220320700158012182c601040000e440384018141401a901d01d100c09100391060804c144a07245a484465410402c07000b404030702800c007a000e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 987144109 1250 987142859 987142921
    0x13120f0204050f01240203030705090f0a080109021503040f060902010c02030607030509070603051005120304080a08071703240f040905060703050708010b1905090907080907060323 79
    0x7031203103c80c0f401c0c8100201c0041801c90540829101420070f1248445500594155501d08006890135408125841d030311800c1e1100d0345480c1d90b11042c20340e0161518000001b0071903503034410b00c000d168202542814030b142c240704010000750b8150101f400c16501c0140411800410300c0140c400d941f408030025418003038001045201c40d03140d4481881340a0700011194070544e1000282d04945041d1ba0301e810360f000110381031009090a486074a40c034100d142c01c40345010b07a1050402c0c2410745014040710101e40016820301800b94411090f03458240c045a46451418082103404403038cc0d8099031880f840d180c0860000055881e0b44440007204401f6105000c940300e68a0b0154503000100d0750080800d02d050701140481e881034216074169101107411910344070000c2c155204200d607924000081020421510105840391102e850141146440d4885203040604003a4101403480c4c100404140c5820002014652440b01c04a40240751a851032515250451049030b00c18030b820200b0016000c0e04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 987145359 1250 987144109 987144121
    0x4050607020601090b06120705190522080a061d010c11190309060e0607080c010c0908030c100b040609050103050a050d180b1c0c0c0c0b13120f020405 66
    0x8a0818851200c6500b40c403426a22954903100710b55206080d26000b1384107001e8103800d50380d146581500000c403403d221f41010030041c1c081000c5510f05031201e000074000b0a182c4c01407103800102d00741d5003900303000284106040100b0203607500140c69000c0c0c4a1600c803084800f02074518070340c440190401100030b002c41d140114024028000202d403102c071034400c00908100c048140444a800d440e81035540c04d41035490242c00300c0e011022401e40c950310030000c04c80c4000107200d1034000d1440c00e0141b0008a64201440000740c0003021310f0b808a41313140c1040104c4525200003250114840c0c40c0d50b140000d00d00c4951000c90700502e20f0b50044d0061a103804000f20078054001036400405101d03c040321482d002e4070301304440001c03080750f042210f000d0031203040c822941c1a401610728642845a070b0004040c030000400195480c03201c005001c11a0308030301d00140440e01e0040f01c05000034010b00f51402c2d6814485600028241c400c1325000c080e0380d0010800c10030b5640300b03891001e4008005101c941428 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 987146609 1250 987145359 987145363
    0x30420040e01020715060e0f04061413050d0309050d030c1b06141f06080402011b120f140904110c0a03030b040b040e0d050309210c0115080a060917030405 68
    0x1e0b05050742c690a244c80e1401d6041d00500804046e111071f14144c00c10b40e01e907138204020300d50001e401125465102c070100881d40303640001682c0300c0c4407160050700000b1100e0078220709007038100c1c10000030541000c61020102da00001d00b040401c41600e00010f0380840c0e10022620b4859101c42002880d403611210ba09001d442e80101e600c200e201c0200003015150b108032401c400701204541c41181c10340d240f0820640e03001e0311f00c1c4d50703000e8018100307400c00355030300d0f02c0071114400c05001c1211040b1000d82c4800034940c0c0610340014030400e6090514001140d200b040b0700d140607199410740708640722030808030144102400d655000548500f2110381a100e850f026000d081d01c2d0114500480c0340a4131104ea91425008110780700d2003010250030400780c0000b00303c415901c010701c13102c9248600012120180100b08403440e030780309122441512040ca45c801c06080d0760400c0c1103e02e481ea0881418440c4c440045501045590b003e1400608540c2c1440c005500040d140c121141c507100200400c0140440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 987147859 1250 987146609 987146617
    0x90304050d1b120c060804060906020309010e16032315180d26060402190c110405093004030318050303180603060301020d11040312020a08030420040e0102 68
    0x600801d5140c40d88031030b5a004500f030344a101070f05051030346200b0001c180c083d2094a80080c0610000314a0343d040c2d4030391900366402600d8801080e0341d29004110107990038041c50b032522212000c0928000d02d1503e0700c0000103a82c7d10b400c084034051f00440c144541f4200803101010781c0b51541e40b03506180c87c0601060074080e10040d41618000c10a220340054415483c42c60500180034909d40c0c0020011200851000018a5542c005a0800000340f0690600000e0091f440d810364901d1841580c0d840e1440c80703812000030340c5d80558100418011150000325443e4508101051800c05002c904041c0c40300c00014401144a00070001030040141030744013011100341a01460390388019551441495920710903094a0610355295510088036071424200842e00000010009410301d03d9402801007169040c20f112100c4c6080041d040041180b01d205440007039a0b1400a08a11002600c4d001c0c014400180010000c207160009180c030181d103200f16889005000e0001c002c4041c10007402070003940 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 987149109 1250 987147859 987147893
    0xb030c0f12010c113d0902060d021e040e0103030c050a1a010521030301050d0201121a03061324090b0703060f08010b10032d090210030b090708090304050d 68
    0x2622082800c50701d00c04441c000700c500ca01c4c5a81344414030108a203a54401a0b441207400641c41b00d11a802580d00c0f07401804940c84c400f10300607074030b50400003802c6084043c038100046401060200f000080c84c616440c40c1100d0b010304242d1100552494000e0500040b1400105500c100030744004145000b160001d0613074405407000010103c030080003d904030b9401d0780707854980c0c1c4100f0040c486d0b0b081c012502d0500a2040c10011080540d52004100f07540005080b844c101c10703400389050541c07a082018541045200010075581c840e140c4176940a00310b6154101030213052013280800251080d4810340c540b0340c201500384001d041c0070100801400181c81030114004a1034000300d02540184100203c0e0b500003008002c0000c408041940607001d00201c03121090348141c082070b0064001203076520100300304d100c009094003a910400090180c1485624105490100340c4404c54540d0b40041e0341000403410040c07650f56440c250245075101b16001680c0140f01901c0e440e081140c00c2d2896001d40c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 987150359 1250 987149109 987149113
    0x20301030503040510051603051b300c060402010e060408060702060f090f0c1e030f03041d06010c0f0501180b04110904120302030c2116030b030c0f12010c11 69
    0x4001040441d4540250803407c0210502040454002400f460080c4421800d9403810001d01d482c800c1242c0c03c00310b548684010740d41b03c030a003501c420f10134030300054105c9561601c1e40b4242156181e003241e50380b00003840241800355142c4d0700101039a401c0240e800800c98070040710031902c1d03e460001e4494005580c08064035138080081209048046003c072010400c0070002c0888102500410041c03403003020400103102c004210300012a09c05200d611031240c99a8000d40d590741c90680c405c0118001e81104001c0500d144d17041c04071f16a44060040d1034035801000080314400f05040130760040c00406100300400740d400c0308040400c054042d11a00c924091001f221040500b20140000b0800491f00146125003c806002e0958065800b6641000b00d2040807401d041030800054407640181d540c20480d085640c04115000d102984042d4100c60941b50511903103240401080e940e20922a64070b11810b65485501d0040e00c80c200d11203540230b1548000d120305d0711328107130103004055a4a0b4401c0b5034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 987151609 1250 987150359 987150379
    0x1021206090601020309040216050a030c0507060305060916022e0f022109070527070309050c130228020d0804120f022e06090e0c010e0a090203010305030405 69
    0x78500701c11028401c00c01078000d9403a005142042100070b51000c41850346042544042c400401c0c0104003108101e44a6245c1070f00301d003060301380300c0d2070300d051503004000709400e00702041450384400c50780ca130704407040030450840601e0101c2d081e810722401040440c48029904001d03050348403d09680c0c40702c024803400400c5a4400c80c2c1c02d134800e034403500b0412703044840c401070441008200a280142e0146142c5d0560b05030300e03110000100c0e515560184111013513142d0201c10010311102c407607180c20403058101000b80b10b0181d03031500d40700c1f843c81e44028818220402010b4030050603404441e030921341c40c0c2e46c1402103520141c01150360b146641c2c21800611803c10191011401082503500480d04800c0b81140d00201110845000c50880840c3e800c601500704002039007100c000d50800d00000300c03500800c200142e03d051004a405039400f042c82d00d401e086c1d400f402c0daa400718440d6900e550078600120348000310b03000f0989000e403552149007101e10020002052000c044041d0050369000c407100051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 987152859 1250 987151609 987151621
    0x12090a051c1b061b08220b0c03120f16200f0d030e1212041113050103021c030c080f27040c141602041b023d0e07030b0405010212 57
    0x13020740344200040034203404100d804024095211050007a450301d0540d540a42d807604140f200c503400071034042055500204124a400140c540c0d0540c2c003000b17040c50071035207280400c0550040703864005008144005003101c52900c880d00781e02c8904000817401214018402208050f643c1c80c6001c540c500000d140413a6504034101c081080c1c2041c1d60040001420092801030341002078002038001c48140e1341c0d0100400103600d8078070028035600e0181800058962550040c40480a07014102c1e01c810b515484d600700c0000c0e00000c01a10041c2c0002d413507030f01c8040e030300a0308009200d510101070054145c00d41e4070b004140c41304aa001c00c044140c90030f2000c00030b10f18041e14886c031020391045002005004a0340075030310941ca00e450281c0000d0000c01c0306d200c22a407041c10507040c602c0bc1c0d4016002009085840300d840a0a29211055200c0c18981100504e8020010240380001c107003040791a001c0000d0340396400c00c504000b864103c25841e0b0340b4145854524001d5200f040ca14591801ca0300005403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 987154109 1250 987152859 987152897
    0x207090c03110a030b0d0c090f2d18050f07090e0102030123030c090a0f05010509100302090426190e0307121403040e0912090a051c1b06 60
    0x44000c105056a810070541d094244c015019400c032964010b03d9560320318010801080c0c0d00c00050088800004200c00b030651130b8000c0c0e5030603000648461041220078485048031004a0004501015001801080e4178400c035000550000c809030442c030907244908800ca20104684080710075040d0204001040c3e90165800e0340001d104e0901c85c900c9901d140d00d255014440f0607044000010185c61015101c4400643d130791000751070840d4481d5a072a0070b030801d419144122030252030110780c040c01d20300d445003559004640794003000f070095a03101c02107030802400a103174078410030744150000c4211424411811003500004001c15004100030035417607407580946c0102c850500080c0242c41e6081c2007000300182d040c20034500701c0380c1030403e98807281101d0062000d0b01c06010302e54010700c11410b080080500d0120b031198180d0111000300402c198a40c1e5400c90b810481c3c41c19126039000954484083c003515a000d00c0c0900b400c9100c6014a07003030700d04900348000303442c80d42d03c0d11416034021512000e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 987155359 1250 987154109 987154121
    0x9090c0902390c040c12050103110f032d190602031b03040b0106050c0708010f02091908031207030f05090f0f030403031b0f0c0f03061407020c090703020c0d0207090c03 74
    0x502c1c035400440c601e402a003000d030848501080075003049800104040144412180241c0c41500c10122040182d070140ca0290703400510004214014511411988500f100500310141d280060000d00140c0e0421008140481c00302c94002076020503d034138080c24404082d5004490440d03076001d61200c101115800181902c1c0a560450121290f5a082040a46582c2e02849070680207114409000682230400d001d041c0c1891401e61000d40c075070341d4100512881010000110302c0c1d4a000f8071041c8940100003045d141c9034508110500038171f856280040d00145411100c0c2da5045080c4403c01144034030005804a0403203941c2c3c201d58201d4040400c6a840c2e01850000030006416a4607606000c03944114840049000b4081e00c0c0c1c40200c1c554500e64510015030103060419a10b003c1002404454071901040398100410300c1560310300400001d4a41038150341c0390388694000008168140d110764140c600d12003c04080f0ba000c00107108006e940c1c1c890351700c41c011400781008400300f481c80c801c2c0070b07036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 987156609 1250 987155359 987155467
    0xd060302090c070336031a010e190b01030f111222200a0f060905100509060304030c0c090209040b030a030c0201080c0d06090b1207030c09090c0902 65
    0x581e00380c110034032444c440b000d90183c41708600151045601058400040c0c0351008500c030701030791314030b91203461456888450140c0c8080da41095800412184000c80002e5021003840e80000040805000c40160001c1200c002000029458142c0e00142485c0707040090405c0c84510030707500210341d1044104098078003005461160303420300768142c1e000140740a102039a40b61141c0c86070014010504003248581505500c00742a0b8020100e00f0404903070018031f000040c08096964445846100a01404034400d001c2013601078000040003030103140c4194100c0300720550060b030b2070211990b2910148080d410034100c07284540d107410a07161071840c000848032041503040c1c403440d0f641e42440d00151600c41c0000c00c03074644e0480410003c8441c601030311a4401a040c2e8410010752104a60103021040c4124484603146030301c003400520104180944503001c59100403004186031150b450410b91001c9540d101000c420f00214150382e0349044c110000d00c1c3c12511070a00741d804242d900c40e0444e03102402541c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 987157859 1250 987156609 987156617
    0xa2a090909060608011a180702031207020f0a15060f030b04080f0c071d0a020a1706121501051504030b0c0d1b0905010206010b09010219020102120d060302090c0703 72
    0x8200000c08103604042601405540001403240c0d94201c61403d56007000c00f010b216060385222070b51245420030154910001c07046400c5018a41745a000e5030300c0c0f14200e80048003000d140005404140300b00100c0c03003400380c42c2c1c054030103034a41881c00a88000368118841e070418280035010800303241182030641100c0c0c0000c00d1450307948031901c2b032103075551101c00d29506012003041055000181003100d94024408020a0342400b811441c01c0c03400200c0c0901820800d0303004118411900b42e00001c0c0e8400e401d04170502103107688075500021f102000030a01104507004554580a6240c4041e400d41d04884059402001c2408000442d07c0184501d000051028018030702046098142d48042c06108180c0c80000404003000e450070010380311044940d03c005002854144801e507818804640100b81031105039080c05502e0700081e481c0d0300c01021072004e04a42401117002d680c0708014101a858000078010358604005082c8000390403240000c2e0300402c030002c04540d045443d902200d41e074541540c0c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 987159109 1250 987157859 987157877
    0x120f02010911060708070f050307060515060304060e0f07091b0201060308030f04020109052d0123070215040602101a0a0509060d081603080a0605030a0b1b030a2a 71
    0x403c50706400c0708400780c0e0040400c0c0b08040000d840c0c0241030b000c0601910007141c0754940d07807500d88192000100070140e500600c1c11945141e4481c2c81c01d90303030881d5029101080f50490000b1b40c614125035100c1100f40d034491140c0002c0d880318568031600428941c0b03491141b41c102403d01c242e0036507109101c02045c24208000248a030312003241c4a5402c240305240c100e2646550788000341c0039044c070000c401d000d40d00c01418215446d034044106c140d50582820300614076040c0401c2c400c215124000a0242032000141d003008650303030300380d1625400d81607908450310b40e52500c0b0000c1d510391241e00240d03652480c150710100403c078000003060360450020100c44c405400c010600c04003003001740c281504148a0110b4400103912603000d00408180560300c84509512420b001f0541e180141200074050b1400e5000e001d66100403a211040d0361300050905103580341d409a840c2c11745414600450a041c000c0180120b84c4807a400030b040c1801881d00c43d0304103007441041c60b01c08036007800c941800316215407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 987160359 1250 987159109 987159143
    0xb19240306050114031c051306030c20030301170c041503020a08070305070506071401091b0509010302100309050f01091a0f060d02010e06090402180a0803070302060a09020f0d120f020109 82
    0x20001d2400300e919407500c5800c1950071520f46604171302c83c5d000080440c0c1c4bc0c2da07046108590044064000f0420100b4940b180303003600c000c460300c034030040c0504000c640d15400c0b100094035040103002c00d07509019004000c080c0c02c9402903030b034010300c0e0300040340304198040c2c001442800c00130b248000e5a030440b01800c801031402040207495800b0a00890381c0a0303070b60741d00e09000c1d00284524004140540141c0c410a0102101e8017202601c64011a2051419100604c05130b2a21005643c10b401c00c2e040014002e4841c0c1040d5290101c80e1016120301c0d8241100d280801c1030311071480e504901920010141a251440340d00102d080450b00c860300007160400643c05036104192500f0b1080000e014140340102c200c0208050340c2c059030b50001d04a1000060404a040c0300c0d64803001049114050760410806a6000f51912030107004620b4641d140c3e00b8441c1950340b0032005110b0220000c01d041504802440c00e64105942121240d0116501d98034000e1494010700a1807800c59011b4500580e646c011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 987161609 1250 987160359 987160393
    0x82b0504050f0d020607050f011803050301050904080f1801020615011e03060b0c1c0201021c0e0c10081e062d04020307090e06040204030b1924030605011403 69
    0x10090043d8880c1038650110702580381e8400070046203000d0805405d01034604a4443d01352000f1000344000b02d8107003c031030804681c1c4442602d0544000300e92561481d2101d0824101034000e02660300076031000002d405150110010580c5010142a000d403590769841002c071004140c403c81103d40070a041e090400d14980110f25043c5450703850b07040018885443e44103d034066002501000d613140e1007138200481c0303260044140d0184182c20320083d0b05d4654240864a003240754502d203100307203a807584112070349200c0520000b0552000a451100c402d4186e0000404410301a9040c40e2200c150340900c1400705092000d041c8115030240145111440d5413100b20201c54400e403080c4408948030309003e99940da940021070203626070b591144840c40c01e02500e0151040040d02182c8180d10402080000400041800d83c0c403110802012034800320314401040030303081e24070741c0c007480c140c0d24181d103805901c1640902055a000300d4040195a803101c1350040d4221024000a605a11a203a001013030f60b03c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 987162859 1250 987161609 987161629
    0xe220303021b010e07170a050d08090a0602070c03030e0a03032a0611030103050d0f1d01031e0e150105030a06020c1c0306230d02101404082b050405 65
    0x408104599000c110800c890f084a1030b104940c501c94104180c200180013040240c1440d105803900642446031080d1341d09540c2d0304e0490030110034030400000280e43d40b1414005c1034032250300007000359a100790b213103052001c100940c04101e004c10280402c0501504001d400740e000d80361300d611100d0140c3c2c600083c030344520b81408820050901c01d4400500010000d0107440713003a02c0030070106900c035415031414034104034807202d080c0e0402000d000341001107548003440d040c0c06401c4807407942c1c04048003030040303010705035401480c0c0c1c2d44038500302c2400101c403084c0e1000d181c3c01085000c0d2200c04502c4228140e0100c028428550b0540c45038104001180301a80140400035001e42150840707290ba400007103030f0306601000c03580829503c500c03c0001c1101d003941340800048207039405048000b031200080c0411a0058003a00440c1401668444240202c9001341841103c40002e81c995685440090307a0f0724030f01206111400c41207581c03886c0c6010b403203010f061160003511003906060a1006000800e06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 987164109 1250 987162859 987162877
    0x402090a080a080406031d0d08060402120f04051903091802040f0905040221030a0320040902040906050603070c170f0d390513080f070e22030302 64
    0xc0c0d40480010056001c21810740c0c05441541c165441301d1904102500716010503154640b500110000c46803c80d10204016100c4141801c0260180e1900e20104000f40200c05e0350440141c032940510500300361154020b0300c22441135084649960442d1020400050b0000b4018042000d1040c10712482040550545119000c3c3c5001400c05a40303000d11080c0d1b0b0951303030000202c955508144400e60a1900f0394160940e03c40b0861a5018001d0300e15503503034896083c6410030190b0ba00481c0142416204d016800840790300340712600d4584a400c00f200a6005104010445181040025550a013002070320b01c1010709480b0742d10070b0304046e101c1d02000001010300020100c410040c1c903419032002d0b0088d040e110302d03541d400074001d070205000340c200304513841441c5000c080c890180d503c03c004002490004811501d0241d4407039080c18211041700641e81c00141e014042e01079901d8000c9070008822045643c098003516042d11106555401710038191440282200c012071007002090180c1c004105210f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 987165359 1250 987164109 987164119
    0xd0809010905060f0414031206062a0304051e1c030c02100504050f090c030c18091303090929010e090a020a0207080c0d0611040305011410140d02040209 67
    0x841c6581d2000d08095003211100c000142e0001031000348042a00311030b02031100980151301c1c00b85203843d10f050601d802081203102340340c0028140c00e0701c5440784140c10400c0307008c092101060710305507038a42c44e9003041c05a01d015005c00348808640c8450154040b0b80410040c0c24101d0502a0000c0c03103102d000d400300c06038140b003d0f081c804c2d00141c441c0c0f031841e200340030300341d032400c0d1101d0401080001c1440c2c1c0948082c0704880b0042801301007041b083c1184c1c2c0009c5080410b5690304a004100e2491171000201d85501248070002c01920350030240c101d09090b4803d699440070691615054422109007104036103603440035107482040d500c3c0b106140300f400507050500708031200d180d400107590b00c101224412180340d000f0441c101000c0d0104400c0000d030649070301034481c5c03210403400b1075840924013802420007a10340e211071040034a1142218050f541000c0280300711204295016200b060544486c100c0006004000440b09101801c48401c1000205052004001c680070000a900054140c1e45c0c41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 987166609 1250 987165359 987165371
    0x10e1506060901140f13080a050705060306030a02040e0a060e070303090b180d14010b041a06210702070305060f0105090412110a060f150e0c031b0c0c0a15020d080901 73
    0x109008000c0c151800c5c1c20011a43da03160030004021031a04168040386181d4003440c0c040b000a000850b01800755502901c2080d1a9034400c000030340351103203402c4080d400914094041c0118030380850300c078100f1801848240001407950840e680e84141c6484090002002d03c1d1080c4028111080149a1069030018941200400000191040198a034201d072100d143c103003200d8244030700380217070075000c1d030101ea003084100e000c0c068244075106401420ba2045500041c00c100031a9245082a042409117a102c4828580541c001e0b40e00c04a901094440b07202d007000049487c0f28400e81036051300c802500c0801c894070b4035510604441c003000d034241c0a000704c803201c184103810100b104460003401144080307442c3e0031a03103545080f1411a10351030a000b01901f8188001c0b80034922180e007116000410030396a986840c0382540d04070b542102c9405a0b400003445004101c0d0019049090b150704a0b20111905d5031440c8858124540c00d1001c00940c00840700498580d0161a00720340c4041488004628 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 987167859 1250 987166609 987166637
    0x110c030d05060a080709180b090309091b07060e0a050109080705070b04120605091e010f0501080a03090e2d010311010e031e19030906140c190602120c0c010e1506060901 74
    0x50348c100f10b1b41c10440d9480480c171300c1401e182c40c4c0000ca130412100305103428105100000d0507190700c1040d41c0030301400d8407800f02c64144601086880d500130317000030080001e1040c6141c100b90030340c00800140d95620459201140b005d9150b42203900715042c061141d48007690566810010b428000d004151500815400701402c036140915040702400034400000c0c42c1c04400c12240c112481a0071840c2c81e90700c0203400c540001e4008801209590118494800c4c6030b81e100010100d0045584126408804402c0f0940710003c14451050507030340701d140805010301c0e01000454444000f0840c01c0c2d4954040806844140300b8202e0000d002c03c0e5000603108203441200e040d440500100707100f2070001e030703141e0010025103a0202284402c4140948090300c0d0082c2101c10035a6584400101d1400b05d031042041c808200c0f00f035045820600c0c52840020541c0b9190400c11441d807c0079840b8040307035003400c00703185081b20042640100ea040703508403030065407201c0d0f05110240d003004070841e05000055410f01b00e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 987169109 1250 987167859 987167873
    0x90504020d060f0507110105060a032607030309030e0105030403120b0105070501180c0b03101a0903010e100518030d020a0311070f0c0b03090c010f03110c030d05060a08070918 77
    0x190300b42d40c0803008516801d1117000245060440c48148026914200502545a461002c250100c0382c0012403000c0703c09904800b00000196481d5507980303c400020b05104041d05a00800003081c000e0325601d03488400000150741522003150010001000f40c004207620842507441406070360b8041c586181040da069503140d003100d0015150b480303c021340c010740c60304100c04071710744101a04203180d00c1801c505092011b0881704521740501026003080215841203400420305442040ca4018024002e444982014507112a0480c0d8031101c0181044001030f44a90801c0f108881081801d006500c2d040350884928002c0d0042c2c90b04004143d210030f46100000b0050340540078090207550051042e5000b490000400c490a41c403040c8401401d100300005400d0229070300c030092200f030a281c0e050307002c061811401488290103c0801d41030100e0600407425000010f0140700d244154200b000342c448104000c0403040911034015640d004034000d00c0450f20b039410901441c6120300004005103010350703840c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 987170359 1250 987169109 987169121
    0x50c0a030c0509100605190c1a070e0109060905090408041a04060219120c0f080c010e010f1a01180b0a080402090a05040b01061b0b012706050604090504020d06 70
    0x6191944030722010701c110b00e403525803180c028004901c590a458908140a00f590260a82020341074100c0124903c08034011300c48111650b5000880400d0001c8070304a40003807001c156404000210201019469540600312080079070b0100e440e15070f411840c100400642050060085a5150080c400013990346812421410b421958042c050b441c1d5007003110003850404071200181e201c0e0307450301a00c3c0100c0d001400340c40980c4007900d4490382801d00360410001301001b43c90010a59080061081404e1a0652101d46c072608070500902403c0c103c03840d1001a02e00840d1103090f1007000150907045580180d9000e8031301414070711811101075a480403180c9540110218402266086d0b04000451904021465201506c05020803aa0900352a40a50744030140514001c1c002402c103940c40302102d5202070f800c002c0d400fa10311602580c4489840c003410b0000b002d54000803480c00d003094542d24107030103440261a0b02920850509281068480107404098802d982100b819070a0101054841c0944 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 987171609 1250 987170359 987170363
    0x5100302071202010b01050409390e0d020306070e190603140f090604030807180f061b20010c02040f0510150c14070f15080c1204030c050c0a03 63
    0x10384071111800c1540c09004001d890b802164036044101000d60380000540d0261070003003800061081c281c90207049c4603001da000012421582c41061540c1c1d40b1a400e040d5184103084e5104441808020107200a18000300030007581508a200001c00c6c45201e032186020030503005009a41c0d00004c0051000c9401c521341207040001d44a40350742c0c1002c4010042580c20040c1d107000c402c084d00d000007540d526150041e02c018104583d02e00070504251043c1103943c0040c540c85a070f22111075685003d06281440c0340302d02d030046140600790010031002e2000485003a038010310301c419940c0c2d404440c0320040840c180c015040c00314031451400035884038868040114640c240002e4a03080c280c445403140056580000c049402c80031910f0003542e4880000e03c2000da11403c0f800b05103404041443c14400144c0041840342c1c111800000c14401c0e851449090042c0d5440380c030040d842c1e010b0248064481d15510344215038070140401c1c000ba100b480040002070045060b503803004000c03070005000655503441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 987172859 1250 987171609 987171611
    0x209031f0e120a05070308060118094502130e030904050105220b0f030f1e03040e01060c0f0503032410081f0e0c1b01060302010509060d0204051003 65
    0xc000c2951100b0080440a07000c0d5102c854107102625400910314440c04000408001500d400f00d04aa400388081c143c0405101a01c903000c252285c02d44002000c03081000c10b5030032902d0a411b40040e0f4003c1440100b00e000c000040c030f404400210340040f80311035203030032030300005030711a0a08410514031031180820615009542d5490050b002c020960300c06800481c8185101c482003529581800848103041c44c1e109808554480788030300051002214061003a0140103113490780044a101003040645c80301ca401d520f805405007101d015649001d81e008451a06020030018031038680502c0c2d00c0c1c07518600c20a5801c03014800750f0340d206c0c15034005072042d0b00c0b5112780e10410504c0c400807101140d030244007500d00d05034128400f200104840700241941c21102519502000200444002c1e907014280305c2141814908000080c41c003070340c0c0b06801d421282103003150003254000b010f0080700c086a0b0140c1d02c15040400da08100000c603808820000c01e601d508020001c1c0d640c4074030b4401031010002c0d8130 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 987174109 1250 987172859 987172871
    0x210140103030e01020c221d0a1707120804051f06050325050906011e020303150f0a060327120311041208090a0315060f12050c040209031f 61
    0x10b405441112412803040c150740225004004c1c6803100c050b00014000901d0142c0c080d1809904004014411601e1002d01d01c00c0004000c644a0000100440101d2042c1c11a0a04000f4050440b1043c000e0050082c00141048440c681d0b039440f40001c1e0340c000e805441601c800048505684030502b94807030600c051180c486004001070301d8203001c8074115105003080e859943c9007101d08140702092031702031544119108800301e07a56034401d003440720303034440c80d41a040e2080541b400c01a540390410bc3da01d2400141e0469501110b0030144115600110040c04c4036079140d042100550190010083c00002004080325022100c84091510008a80101030702d800c08000c030170000b01914a26906440b40038030400041003003071007108042400350340203428161904101e60000ea40c0c045c06600140201414021801c00341e907007588000d040302d1001000c00b04c3c1680e5580322502041e030743c08010b04190054040c030042400c0070b07002403042e090010306941c5683e40f8101440800f140c08040c1c0b01c3c000707030750340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 987175359 1250 987174109 987174113
    0xf230d0b0111010b03100c05120702060a0507050a0e13020c0d05071703131731090506030a15090c032001020120130b041701050a0501240210140103 65
    0xd0700003041010030b10000c1c01407560203400301b03030b075040413581c030017000c0755945240c0e58854428000d9030750407600c4081e04c50340c900300400c0003550b9043c01d5401c110702514200202c0d950074003440c06c55802d000d02c1e07100c10618801500030020383c5410700700ca581000743c08200c04940c802d000e1010000303080c02c0c0e444190700c807031b0329040c8142d1480c0024428403031454104184904030008204403c80682d00903c05d400c0e82d041349010303500600078500c3c40c504501c0007607030009035009009070548080051580340788405607a0181c11050341c00c291031445e096040b40310760b50b011580441031400da00004110219200d54550b498050000456000340c0350f0300441a0040344080000d05900c1081200744000d02482038a50304400c446c0305456007180c03001c4400200b034100450401d410b44014181041c1d413a455590754100d0084800400d0504406541f03041d0010781002e8044c810b007411b030703400001d46000162031620118401200d10200c0c000350320881d0f41c0e01d010b5181a0168100c12070b489402460654914 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 987176609 1250 987175359 987175367
    0x603140105120613030212070606030b0604111e0c0313051801080304060804020d05060408190311090f0d0507061e080f0f070306030c0803041a0301060f230d0b01 71
    0x680001d441903000a8200b60004000502c1507009142c080c10416108020f14017a4030b480800728000e0345140002c07a21009100056102000311390203041d0030045176541c00708200460f440d00951840d0510305001c4208100c451003000105449401a1a0f1600140c041e00c0d40c40d64011034901c100f40705108605000320b081203803004d68202848800300d0600d5050034009605c03809a4041c0804110407030300098250364a0340581c522654104c6c090360390038200350510125a0b40030b0307484042100b400182c8003412038424840c4483c00346a0305140c03401c00115034104143c0400c40010340d41d200300094a030384c0c0481c00c24003000c4000e054503114105110661001150701100e00044d0f0424040d4040400c000c001c8241100c907480140100740803010780e6048800c0d00101902e80025011101c040c03000325003600000300030301c1581c840307507040c807140c2f842e05114003840c1c8800d000300400100046902c125607030054020304044142c8508441c0c0d00c014401c182c402d982c0000881c015280d894188199483d604 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 987177859 1250 987176609 987176611
    0x20c0405010e070201150b0d0504111807110c0a0302060c150a050105041503240612050c0f0a08070b03070917102f0c0a02042901050405010f0e0a0b04060314 69
    0x81080d50000c041c500007047c40c0c40d0180c1d0480d810129242d0002404010a540f818400d9200040c0303003481c001c0305120a00f030800b03800c5032004041448070040100d04070000800340e15003a0020182d11483d03040d0f90901895801911910310948501c09454a158025940c12441001a580c0000d259813500041100f138070200c404121941c00d14050034808540000190051070220162044a240c01101603400401c0103500a1100c0d0100040c0e030b00800c1008154040d401008845d55200d045841d0104035040a0030f10403011340f507004171001c00032018000c0c040d40d0701440b00c0c01c102820542e1401030035410f20201c0103d007500d401c5540314250000c0140f1078510108040d103400041c00506510352441d034010611303100b44508012488076041c2c1010401c0b00780d225800350088c0221000c91910502d1544000e0745208042d40921441c82c2c1d5512910941d01101c005a44210040c144207200362441e01228900a1700410460000b064682e607180c001e00050101d03541c00a10800f0720440c3c0079004034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 987179109 1250 987177859 987177881
    0x901270f231b030703020a18080a1b0803041701020c0715020d09050906010c170a090503071d1501110708071d13030302131d010303030e240601020c0405010e070201 72
    0x1e103000d55402402e60740e06a0342c2c408585e040041e0b0350000c50078240c07004001c0c5444070011052100380441e10800c003040320704010344103100035200242c80c103101004089007800ba10b08580d000380801c109855410b66080d4443c20301c200011b2501501e010b900d4185011500b00b800c401e030300d9181c80001d1039410070102032481e442d0f1416200c0c080c01d020004000304405002c081c10484004003040c1406400c100d0310382110016680c0b0366030b4600e1340c1006803209000703209452003409240030025019800320440b00811035248400380e42a9210703000b503d20b000e99041d17042d040001c0d2064808001004001c9007000d800000e00030b00722a40341414400100c0d020b107042091a04550003800030900762610310302440c82d41400d0150702e90b4213140c46000712030400d5005041c1c4d42127403042c51842020050744141a03e000c1d640070700c40a14102401c903601c1004510000d2450942c2c181d104100420f0708049400800510545085110060018043e0740c0281c011010155240081c801e51a80910a45201c50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 987180359 1250 987179109 987179131
    0x106080702030a1706040204090f0603051603050c01180305010e0a02030709150512030c0628050105220b0d030806090f040f17190302090f0901270f23 66
    0x420001004041c00c07013004215040c0c2a2020100e100b075910358055801401e00c44074100041e0886c0000100541201e20082d00c03d4040e045002e1180c0c5842c0c0a050141c0c1c0d0032400410b00384a402d40111480018940480c0d1085600003010000400a004952004505000800c020020b90040504040743ca40c0982c070301d607203404c4400455a807506400412148100c0c0d040d0804462000401c1c2184a504100002d81c007034070040068000320718281071000d600c185020824088008a654115082801800d070f2007440c1c41000c4110301c0c510017a828042e121001e01003280302d81000810003803503032008200c0c0400c4141c81040f0407420660280e603440342e1003c88641d1507040a8032030007045c0c004040094103100007039148207850111142240e41319403000301040400615403030014004e406c60141c19100c0c10091003241c4071445c2845921303040e107015503007182e03100b5485180172084080034000d0300303031301c54841213078070f110b0240343c407d2001c0d0050010110391150b1548008030440722004101c00826 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 987181609 1250 987180359 987180367
    0xd03060e090a020607051005130c0e0705040506070318121106070f0f0611040906090e060709050d05070b0403080307270e180109150b030a3503040308010608070203 72
    0x3080000842540b4a50161040780e42c07000e8604055051400109002030b025042800388003c80101c05552280e0500401c0320440058803a0440c020102d03080d184a00014001e000030310442c80d00ca00148011031003400e0003041b0f540e00050500300300c04180e0002d0814254552001c0a0001d0302c0400b03400e412080b078503a490b04140b07545068008170041c0b409030442c088207149904000640d071003a608103075504003254070707175a03034050080242071140600c18201e42800d2402c17201e0080020054007428060300c401d41414141018414001410442520705200355100014100301c0c201c0200051400384588981e03c0c941258080d06020391006480154a107a8243d0000f84d0400e100f032a0540341c9404010406031500c44076590f9071031091481c80e405510b03011410040008400708002312103000c400c18070007612020200b54079141548005044200940750f042102229041200000300c200d5420081c0c100b010628500305810441d412030100301d9000050164039004003070389900165502c0103602d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 987182859 1250 987181609 987181621
    0x2303031c091401050c09181501050a0932010203070f020f04022b0e0c03031207051b0124050f090a0e030c1518030a08060103090209090d03060e 63
    0x300d8040310014440469450300610300300300309022003a1030101c144000b448182480455425a40d100700321842c0700c0d907041c03001810680c1449442512072500803a540a542c0f6040b0010744241e402801d030002000118600860706103107043c0c1d00c1c030380c0102e4407612400b01020b5030340d503000c000d0f04000c800303056500600c1b1902c0014181c1480c0400e140e41500d80f19000714000000c900640540749140244810440030a85040800c8040c074000130752050040c0107030300402440320340390300010382030381e800d504204854000358420101c3c150b0060307654034040c1c0c41c0c00550060141104446200104035035115001001e8a428201d01a48010480403241354864506400030303d001c0c4440350300c3c0f80101c9030200095924401a4001c1003000800302c02d89a842032420141d544a10301025002ea104180c84045420b0003205208000f00c0880c00008510f00341da094000e0304c00c800c00600d40c07810580c544d007445c00103884d000e030043c1c081d244800040c8991407071280060285c5e141c903044811284c01c03403010070403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 987184109 1250 987182859 987182887
    0x203090703060b03071a090907030b01050a35070e030601050604030f06110d090213180201080910021305031015120f050a050c010f03020405030a02060a030e07230303 73
    0x401c4076802040010f10514200210f400c20842e03a00504d4400d1440700030100b60301c811030081102d01000c03581400300d581c0745101501201c142d250401e000503400d015080c042c078060350383d0390601340041d00c94100c0342d00c4004040c0c01034942040c030029816440014000c0070342d0444118031351140704802501c01581804082085c40c0958400074101404140000040c05465845030648002404400d86d8540b142030b28040178100c0a03100701d010301d41811691841c1402480303400441121381c0c000c0d4001010640046460f0b10010380344031420300078032054a180500b0381c07006080068120241d000c0c0d40386004201410206041041940682054440d810415510036080c0560f010541a26454021420407180a81c80201700905030720401c40c4540c144000012401c01c000002d03604d410120241c410102c0982c011440340581507403180c000c8000520703040c409000030000c240b8000589207030351142940307020141c0d441007401c404c1745412071f40008035200c4004d000034425401945010019082c100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 987185359 1250 987184109 987184123
    0xe010503030f1b060412111f020a02030d0c0e1002060403020706030c050f12010807050d0b04080708160f0506060427050c030a0305280512070504090c21020309 70
    0x40c1c21500b00107840d4045001400480b44281c140d0b00c00c85600d403400d03140c03095000c0e18011050001c84e001c40c00503664a03200141c03803884a1200c000b0b107242070180800c160003a4000c0c1c0c401c0c0082d40000c1c0000000d401c590310406040f0b540300d6441c80c0011032440203220944000c43c3d4a0340841d005101004042600052003500321032152900107072044061070103d495004038039504401c0100040e0f10b0070640701055086041e203180c2010782d118940c3c3c4008014008100090003000c840d503900001d0082407040d00a400c1c80c0740103104507803800b94076881031650a0f06501c4100c6520080068820501000b000000c2c1d222a09403020000e0400000111103954007042040c81c094941241310303003c2040500032440035503005400c548015006140242480e004410301445002c105d602c107003d500303d8040b090001200300e446d45854007401d00f038450170300d0130010a01130030320004000000320010244a110100c0e0300135600d800034400d196156440013101c82c0c601c01c0d10140140107019040002003206 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 987186609 1250 987185359 987185377
    0x100504090b1504150602010509010b010305041a0403030b040204120b010501050918100e100e090a080f0a0306030b09012406020c100207150804030e03071a130317070b010e01050303 79
    0x2000d50301140740c00040c068070a1942004c509511407100180050301504010b010b5100ca40007801180703646801182141d400705d4000d4500f0712410101c0c0c0c48080b9551100d50801e009203004149080544d02040c180c0c0c0c0264400b444814103499800d0500030048038403809090246410351500016000054440403480341144140301c000010551580d07040e0070100081c0183d070440310661030442c4103203041c40041e2098405404c6240000b5404000203d2681d403143e901c00e0302d80d401c00713203c01e55668998000e01945410f01d951013030b000c004580000d142c0d82c850307140400040f40c800081d903106070b01019403502119814a0b960810b011032070b00860000b058903010340b800c02003c003560744d0803031178031003103030301c0542201e0364207514241c0c0a51003c00a07110340d000303032900b81c8030141038030605603a10205d104099442c143c80e02010442a0003e000340400402c101c0c0302c2071196200d4548091144c2084201d080003040082c030402004810701c440f600500c02c4080303402140d0f00d4400032a841c0c3c40741c210b803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 987187859 1250 987186609 987186631
    0x6090b0a1704050607110d0c06020c1f05070f090302090f06030a06020703021507020d21020706020d15050d030e01030c0c0b040302061b09030a0807020d1208100504090b 74
    0x11400505100e105030001121030400c500c1d105080a041943e107400041e200c04001a000041410780e060001403101545c48042c2e89640340c403152074881400942020800c1407940c02420a50f9041020000c40005101c4401c4030010b43c0d8280808007038445d0756000c026000380128088100050780e51a66402d0380700218051207040c5a903540002800c003e402180180014401704943c82810350016410488903011281024691940d4906903500c018907214600001c8031105c8a2056112088019000030700540000d410017585a50b50300517070700105c25009030340380d0f00c0b8004200c4901d04401c0c0c01c0108820b0352640344000042d00c0c001c24128100c0203641c141078844c0d05501c00d45124500140a107600300304100007030308042c6002034507920242c9810840030300d1024400c030202c0009040302c4580348020002d010201040d9940f08994112080583c0e0000c54840c181c008070f12003441d00f001c1d0020b2540d4102203403405000b00c01c0c220309030b40c0180307014604e0103049900084010228075008985602 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 987189109 1250 987187859 987187867
    0x111070b0708070c170c120a031d183c0c0d0615020c0402031311061218010c02060f0a180512070501140c16151e0e0706090b 55
    0x10508101e101d1900c00030412070004c24005000f10400780c6812000c00c080c0d044c0d0b0103002d040c04c01c010907642d085100f0310b82500a03003640400680601c84031100c503107514101c04c0d59101d004000034848009560580302c0604684100010b16520104506180b424100d6210001402c5194201143c612801280b503c90000c4040307004803000c1c000740e03004109400024801d1980341c09031a804140b02c030242d5009842080785400c00d0f0710b002e0080c1e80c801c80b900d00d00075134a40345a4403410100c00000c03070300d02c1e04200c1c2040002c40e0480301400140c0301d41d4020b1003008120700c59401c8103003181c4a60f20008110340050041c44a80300312034a2082e0006111100031031072062068076040609a086002081481080b000804032500e4102034642a409040200090041d039640c42c003484404441400940c0300402585030480202a0010440b50081940b14000c0e868811314004a40781d40460407010310745004035500701c04150140c2407410540d4005060b400d0318181018000c3c00d21801107001c4008085 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 987190359 1250 987189109 987189113
    0x120705030f1602100c06140c18010e031b030d0203040e0a020c0f0d02060a061a0906130f030c03061a01140d0902040216050c0909030304260c0f0c0111070b07 69
    0x20040350b00301d640003880e400c0036801891024116069a6104461607802d003a8034400c10249101814840e5580140c000d01c1c1c5030140c286107020413210b0742c1c101c0c140485c5068560b090b8030300f0040710b01c40900300381b503101c42d0a1540c0e08062920064100c1c6030110752081009214190321001c1060f00700c80014001341c1c0780d40035880b42904041c0340c00620200c620440d000d040d1070503030001d5102c0c0590341d08642040425140c2c0c0c00007008003145610244283c1042000302c90a0401400070114114000a95201991141003130400311003140d00a0740e19241d00c0b0404e1081c0012480b408194070301452100300c00c0080400084c1a418100842e541604030101e0402c00944068100c0c2e28202d038020310456071100702d2126003042d010702e8401a202849a080c04142d80c1c24021409402501c41400442c107654650b0740341c410403844501d11b03060211280c40d094428428a070003400d1032901c000042c0004c1d08440c054a071400c0b41c4130591a0402080c6504101908008503410b419140c2500c0160740c0c5100718 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 987191609 1250 987190359 987190387
    0xf06090c140708041214011b1214040f0212060727030302060601081b0c03070c05030f120d091a0402031006050f060309031213050606091909030c140c03120705030f 72
    0x9003004016550811805000c3c400445030401c40c034180d2274030752483d105982001c2408580341c42c25060001240000403501256000c80e22010b80391000300702802841034000100e04003002030703403810301145450b09001072241c2e5041189840d020780c131081e05a62455520000e50390403010307040e00d06010810700401d4034031490b03039000c3c011a1040c0c07410650310f05410795444c0e503903440030100751541c401010740820180340103d40703002e030200c290009041840107815101d0f807aa0290302e05c052039642c0c0d4441a800140072407810500da680e18881c1c45d04a19250050604040d880c0c910340b483c1d0362a0140902c02991418260f2400d9402501c0c2c03a5100e556400c10a423851042e100100346220112007000800084040c21502e180d01c54000c0c2c6a96446000611070071240a4805511780020340b480d103a8207880b10b43c0704c2c0c01d04c0c900a01d4100741c4210310b038039146004010000104038640020410440a050801403c1030700702d548040d16241048a031170b199181d0040044620880c000020080c5210b840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 987192859 1250 987191609 987191633
    0x5191701110a170c030408040e191a1e01050f0703030e0f0601080d0503101413050703020c15060d030c0201090e0906220c0e0a0f06090c1407080412 65
    0x107610034840d9100804003015003c0780c00c0c0e43c0880701c560f50358800901e815001c4019207000e40c5c2e01240300d40c00c25007000720100c83d80d00c000384550004804031030086411801401a01d9190400f00459010704003507505008a45070328039000004d040c4083c401c0d00796640e02804465000e515901408e4503001d41e454102e0180c00300400310b500320310500482c3d00e40c00310045980d42c100c525000456041701443c00e002e40f000c0c0821112091000e00042c004c100d1004002e42c9040d1511004025924240603d0000c02c11128180e07106400a5404220754881020411011590030b003c01294030b900d14140000991945178035130024104041108031504590190040340050401c000c075202c0f01d403802d500e00319a108001ca66a50300318400e040840c0341d004142008062003600040c401c2c400d6400c02c110124600405030180e141d540d62060a03000c03289075842003202800b808100402c05560807103001307141020a0030324a0850508005140009150108482c21100006018402d80d07040b07041c48241d10308 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 987194109 1250 987192859 987192881
    0x206030c090d050601061806020604110406032a06021603060f0603150906060f05060a0c140a051c0512131a041115042d08030c030a020705191701 64
    0x2d118280400c002c0c02040c0d850503107146039200d0402d052803d01494800d203440c811503000d40c001c00082070200d9004a4032902c00d80000e0000715581c0d0b0349a54103210f0801c42c401013030303d500b081030146c5003402480c0750f02001000c1c1d5200030304051001a00000180c4040e1100801c2c40785d803104003082c1c0d11010707046500110b811180f00000180d40984240140008281c212807061820201003a0280701e00342003010703a080a00400e080c095441000d48051800920135581e001c40f2850020721450204040e0150758803c10162042c03000d100c0655a4480e100c3c2c3d50f040611006018803010040c404103440e0340b18255601c008240320b040d003015100b910b80300e4540a81079858400300802d010090200e00041c0d502030b61250407985000c0c142c00c10b0382c091401403001540007101e0094048401040150030740002c00c284820066030703584410b02d5903000744117945180e00003098140585805018000007000c0c1a20a11004079114a0702d203040c0c002409640b01c0704c0e054403182c3c60120f400754007031a4004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 987195359 1250 987194109 987194119
    0x723220e030406080a15140f03120d050c0a020a031407052e05060306061207150c1401110702090a0906240503120405090402030f070f1401050a0c0206030c09 69
    0x200c6032103005a00c0c0d50140c003480340468011130215148107030b0b512581c107441400c10041030320a8149030b003000315800b184001c96800346808803d1000e6a500780404440020f100b10441c1c1d8a20318140c902003980e03001000c0032a035180c01d000303080c150341c0c020403d80310407039041c500131030040d080203400600d9001d075000180c080c0c442c8100b140803110f841a5006c0c005460355140001c00c0c1c41c0c500c80b4405485c0d04907601c0d03800d5006034000c60020b040410342020b0020f021026101d4894540034a2a404c000300d120000028152114810a105101c9404115640c0090003804106082070841c1468428044000c1c06080e1841c005a0900c080350f0000c0a80d41d07001505201c0e50700c1818480070040501c031102e014440584000140e1740ca8000b40114100c0301d50010345041c5441c0000f00541e0315401081644c050044140001700c180050007020702404400d10b00549450502203030b244d0081803680c80505109007045a04002034002070749090700355040712100e940e40d440c0348100f10f80380240740c00d0365001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 987196609 1250 987195359 987195371
    0x80c031e030a0b102f0316020a05400e0705100302040f0b090d0f121b1a0901061206050f0f100b070816050f072322 51
    0x2903580e00c030086000361a681028080c0441c81c20802182d000c950400d00007140003800610103021070342c030380400782d81802042809070a0301c03100c4d03050440d070043c070390781e00d8018402c0c4403407085140807485000645000e5469a0030340e00c2c41c03a0070050801100003060386050744026803004000c895010003001888806050101c115459405c696036200390142c40e109580d2a024460f40c1886032083c0c4046858400400b4242881c0548800d01544004140c0303801102850f214008a07800034020410107208400c155140e01e04080010128229225a00410f2404d428203001291071200c524807620f4071408902c40a440305440cfc5401042c0b50b40c482d8a4110410803414140a40355000d2403203a4422490120243d0390b0fa11280b40121003111002092072401409002c602d03484070141602510031081249003c03c144c802441c84440f40390222100e40c490f10200408003414080d040091840801d8110340608181c40c0c2c1c1643c0910700c0c0402e0144941c0c0d0605003071850075102401059074141070030801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 987197859 1250 987196609 987196657
    0x305030919030203070c14031908040b0f030915011511010b03060a0f0501050a0b250615051804030206061905040e0706140c0d03020906070203121b010e0a080c03 71
    0x345d80101e1401d550441e17403100000b0312140106001c1540c054000c1c050f040c0d0b031513440040c1d80030246200040c0c49803e000e00002c104442800018900c168103c0c040130b860786000182d1914004508580b0400c81c03501200410005109001d000303480d1110381030942e60200f41c8a40310740149010300110307a0500c07840d001e0028070240d0b41c1c80100d010690501c103102d81d82c1c0314401d2103e503800e40d100b0b55421500420281896101103010301070348103030f902d0401407050341c5903e4800c140d40e00c40c482514594182c3d08100310514042442807440c103c0c00c41040c0041c9080e0301c010303448050041a035030151828080207070241d060340703240c2c10240c0402807041000090441c0d07115030340c2045000d50400704946c118666030420285040d220403083d84401003040710101c24040b4040e4201c064a190800e0b010f100c03a07030050b90144810900c0c07010080c980c1d41c8950500c000c0c100f00c1c003c270a4140506915265a560340424041103030b030034294011003482d548400c2e0340d4440f8614824804000300301d01c400e06400e41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 987199109 1250 987197859 987197863
    0x51003110c0d0e0118050a0515190201020d0f050f0a020a03020408011d0c0306131b150c020f010527060f0c1b01091d0702030d0212010512060408040303050309190302 73
    0x550b0b00303020380c1d0b004025442080f000c045203105c0c0c0201c2e030340400c68070000c00503460201e444041c900001e000a074100f0300d08410300300401c4107090350580541d40102d060f031a01c000700e1160301d10b106802c3d41c00f440303141000c0051f02c0361910040c4c14911080d0b00090800540d0703011740c0440b40203103c0d400080040e0b108849500070344030000000c0d09082d00a449082429150000f03049001c1e540105402d45176204a640c3c0000c031139142d511200e02e80020b1000000e141580d885000142d464645070380e401600103204000e031681019040768180001803184852042c9814154000c030401908142692546200024014040c02d400c80c10648000555001044400324203d00307211511155039201041c02d100640b80700a02d0300403144001803901c0516504010340654540203130b01ea00681740381041503130240099038080f0207840c0c541014000100500d0803c2140c1011780d090354405030880303062039610450303140b0503403001404109002c4040f54040d0818000e41072a1101d4801401c0072043c0c510b40a5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 987200359 1250 987199109 987199127
    0x60e0f0709061401020a02061c15091e1a0409060212043807030b0f040516020705180f0703020408060a0b0f0108090c0d05281407051003110c0d 63
    0x621104000f0b9036036185500008942c1400c95000340818204440d085411109011890060540070344400080050100512141020b051040c902140307210341400300c450000300006541c00902d1400d0700c02080041d03407900400390010700711000310382035400c2c1c00c00340e020f4014810074403080c41c1744209100401035a4100441c410103002c0070314004a0000e40c0800925084120b040202c101040c0001e003614840d0340304038000d0b200105034a00d69843c8001150840e01c044038080703480b4900c8510b01c805642c0401c888001402d007160301009001c440040340d03900d5600600f5010100700a08003090406020b601624040e12410302100d0a0f0b190010040d0047c100b04a1414012001c0c00c074041410b51045008510801110000742081d010002c10310021001c440002e42e042d01646024404104402403880041c03699540d14000d954114100f001c4c14051421803441d82d80e0101e001000305465404c0c0c00d08111201e030074009007094400759580302a2003100b50304a407501440e4100004a0b800462031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 987201609 1250 987200359 987200369
    0x910120f091a1003020d050a060e0102090f090105100f200c040606111c0201090804081c0203030415020a2601031103150c0c0a0507030b240d060e0f070906 68
    0x348011440310710a103034104400b500d81003c0004012424030160504051140d1054414400c44500f02c0c0c1540324201160000415084d9503500021410078502e804246030085800458194440d5494580010810076030550300100b4440c07411309001c0c0c0c29005203e019080303040d104d958040380d8003c1212071340355030030105020303c0342e49480004107110b449030074507441c0b0080c0900100240d4190340c0c0415141d1001011100031507483d4107440b4001851a400783c0010a102030040c80b05100c0800c2c41181c0c002d41021100031584203000b080003260904000014240800d00010781e0303001100b50440e048220003255207000d00200c4142d40c02e81c0903c20310581240d01541d40c0c1030324010035904054072603c09440d00c101c162104404600b0720000c150040584881d080c0450310b41034442c0d0b40d080d040c18080d07401605c500307210344100428082c40082d1140d40b804094803160020309614005501d21609a80182c641039031a50041501c0d0400c1007442034003400e4508a403401640c0303480c2c900c0030700100c0c0a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 987202859 1250 987201609 987201623
    0x210627071e06030b0f010c0203160806010f060c0b07140d050103080c010509160308090a05040c090e0c040f03031115090a021201020f032a03040b0403180602030910120f09 75
    0x24019103c1e10071801045002041c1240e408004001102c1e00078103c0c0040c0c0e40b50242402151001d070200000070001d100f4070025282c4c0b98501000080c5810442d400407061003d240200300000b140050300a80c030000c90f0502001d41080300480107400c0c09110400380c2964602800401840115000b81020b005004c0091100f83d45003940c494940300546850583c2d0100c285080c00024001d0001d4628400050204205582d640d00041c094a0b0059050800b1801420060000c0b03446503503800d41c8040412407040ca03240c500200c07881505000d00c80a8100840183d41c28020300040c0b00d41d500642e48201c071024503003000c0580c55110140900201d211b45071200e07201c84d8410040c000e841c43e400503140d0250a559900207108041300c4400c0511031054484194144000d1034040a03500840c020141d28a0354907041c50088c0c0003d0420400e2603018400308020480c856000003102c0040900b540c004010148540c0c0c01e80740031a45c0c80d800c3d4901f0b401c3c00310b011450a1198031480c4100c1c06125 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 987204109 1250 987202859 987202919
    0xa080339060c0d1d121e040e011a0f030a02070f151e09120305130605040c0f08031303150209090c0d0c0f02190305091305040221062707 60
    0x140c181154004c200c0b026501da00312030580000001600c0c090807550701d5850600400d652001100801580300b03421440200e01608014803450150840c0f02a94000507207a15103800c201040c142041c1c0002440e1035002500013031401d04100d038041003480342c1a4062030080052075800c0c00080030b040081d11880a918243d8000c010a0341280980f4080b203400c019201c040441c045022030243c800205940210341c1d1406407180026964031440d803049002e418005000750038000311040c140303100e501480740d651060041100f009100d981c500300700c0f0f620194000400c9900b880900c044d020340c401c115401905175080001074546c2000428035610f28050030003206403284000c0e1510601d402e465401a40900006102c0e44a05040c0040c4103000341841c44c2003214000010300b0541950702001d2340961250240300860400703000100d252071a2a199503280c0101165407651518000c0c200684100c0c01e51400c101c0617803003107507000c15980e05c01c15a5001d47c1c54409115407080c0c118032912109003884 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 987205359 1250 987204109 987204131
    0xf061d06160909110403050607020d081e0f1512070e06010f02060114040912050c01060906053a05061503160332010603020a080339060c0d 61
    0xc030400d80c2010765100c40c02090706140300c40000b07001d03000c10703400442d0040102101152040040ca0702c202c003568001e01c000008084d0040083c1c0000c0c000090023441c040e010304414010000540d0b1104124200381010b45e01c01d20411803004201e40004d401214007021010948404644001a80c810300c000400d251207201c011203a000c890101c0000681040c07005004070758410750319407066031000340003180b140040e44524509125004010000c00c2c00003822015820f000c0c000d400041005c40401c12226180c80c0201d0f0a00c600751580c50308001c56030815810310b0100201e49040c10a80448002d1445036510744079646003025210010708400b0924003048070720740001c6643d40e91076103d9141c110310b4a0340c0d840302c070018014044070b4a2041d00c0c00c20b2410341c056008219440310f1484001207109407850062014421680c2c010240c0358100300403e8888503004d01c10502414401640013280900c406098001a020b1070100c0d1801e019800074012007078001c0c1e000e041c01a2451b401044400b01c42 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 987206609 1250 987205359 987205381
    0x19140c0a051e0a0b04080f0a090501020c091005100504090608060421020a0201030b181006030e15010b0c1002040f030c0e0f06040b0a030221010c0206150d0f061d06 72
    0x280d01c00500c198050a18240028240da00306174110f03100d04001c900f007203003107206030242e41c00022200300001e2205008105075a13041110741340c00501a01c4605007800c16078124102d01c00c40380a807034064042c4550070360b20188035404650003000c210000304401b51300c03002c0042d02c880055500703a40d003c44ca44c800c401c0c04001541c40741801c4800750000d01c0078800b5030740190302a082d640c80701a4400118030070b125881d1014103405100383c14032200e041c0d800e818407101604461280107d903031941d02c03d05005d08640e4414804a05440303225600070348400d030341324489151440882540f8640c0340042000514900f1080d010416039204441d1211502c1c1c49000d03030038441718216905032668400360042065400c2c03662012581c9500a0814042c0f03030b17140e80200b030a180d41d00d03a22a455980c2c440756440d000d202071080d0b00d640ca1043c8007615107801d104032011100c9401e203115034850300500107e4820003500b0140407003940c1e4481c006200c0990040c00d0b41e00c20b04040d00701c6c503542c1d000703890000e0000400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 987207859 1250 987206609 987206653
    0x10606091d071e1e05160b0a06170a02010906030b0609010c060e1e01060f0617151c02040b0301050c040b031509041209050a0b19140c0a05 61
    0x40110800c05811107009511070700301000d44490148515080080590004225410421111a1103906001d014040c2200c400c0c024000303d0010880c040c820881e0140503458001982500b052180551351100c40000c0020402944107400e00301000e00c0440440c540031505405230f41c000d80b40d05441540d50982074050b01c0c40301080b00d138031603010410550341e907000301516102c80d40101c0c0c00140440700040c50341e10b41046541d11040c0010107482107803807140240950005400c10140c0040e0541c0741900c007400050980e25a000148904000944c1036003801000051001004007901070716504c000c00046d01c002c030214164020307814203031050383d6030805004043c000c500343d441c3c1c0c6181518012403502c49402c05000700f00d00b22403c200c203c03c80c4c0d41340401240164060070099101c0090020040e000c21610307401240594500e50080241001c00130940761802c0c00002d840b04507003030980e411a400300341c00f030601000c0d21005c580321004481c0040c000e01524440d500f210719807800a0b4000c410058 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 987209109 1250 987207859 987207869
    0x9031502040b0f0d090837200102070506010e0103150c08010b090d050a0b091507050d022a0d030e0102090a05011b08030a050402100507030903061a0301020304050d0201060609 77
    0xb003c0102000046108000b080c50010307014000a80043c1ea0769008000d07804102c042c090030464189824020101810503041c10510722400122842c0c800310203003030844405c1204540c0c052003290344c0028002074040740e8040c1d6124068541c13075a150b10495001c004207000503103095030060000f0801e2115485411814000e940380c6850aa00e403010095095011a40054200000d0b291840c0051820018a0b880314403800c4c5d0b100e0b040c07804028040c5002c4514000a4540c48070388284000c2a070050104e4102c142450000351356900b450180019280400c43c00341444040305101c400c0d0b845003c60282d10144955400340120301c056003c15003070303000e20400940c2c0003000c080c0c108200d40c0108410012a144024007900c5c00000f0745500f220368008840d0303da981522071081004624080400380c2e4444c505089c404c0c142001a10018003d14150000034051a62948801078040d101c0d65113902c1d06070000c000b5580e0381b400f440d04548030528416104050743c01c003400402c0c01c0c0c4c0589540700c240c0e5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 987210359 1250 987209109 987209129
    0x61810060e03061311040638031b0d060b07030c03031503170705010e12040306060f120b09010b0402071b0f06050f13180203040515010b04030b040516060903150204 72
    0x80c030703440c5c0b000700503082500b09501640ea0b40d00060394104610b1801341c4032002512401c12101c0d101c403000c601c5000000e80381c00c442c0c402c0040001c0d282a0101e1101140400d4a891741c1720f01220700403400900d155080b030f021100001c51102c0806503c81245004a4803a64050094200c426550062060240002045182d4602101d20840b01c6000030f84001c60065001140c0c0030030720800c0508005001d01200a0100700080a2082c07210031301510000313000c5501d2180110f480d0205ea4170040f903c0c0c2c01e00504002100340454041c003030035007022246141c0200115610304061910199404525a000458035482980001c014081ca18810103c0c0d50513111186040000c81294030f56034003a0a0381960744440707807408a108158808511401c0f6400240140e0364285801c003685004080305030348074045102801804184611800c0d10100d0740e110060050704e071100d2a000741000301c3c80e14000130340c40c41b03540d0010310300340e101c100542102d000c1e01a402080500c41c180c2d00c264411030048602c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 987211609 1250 987210359 987210391
    0xd0b030613020f0d1e120f1223070528082a030109022106030d0f0c080c060415020304050a1e050d020303090c011106070305061810060e0306 62
    0x2509102038410740d110801404240b003165556180c0c0410f554009201d20071021755130300703d41048a02d090a4102da2002e003440c001d620b0706914014020b202600e0100034407922103019005805046140420340e60110b080da00700b501e00007500a00942003902040108041c040847d45c08183c84a400203107100a035071821000e9440c1801c000404900904071100381005c3d144e00d05405030101c01840c0680421040543c1d0b42c05e06852a0420800950520300920042001d109041d900002c1c451000e0909007080801d1f004080d5040d107443c4611140544800340026101824410115144e441944114402d8414001c80c9817100c3c102d0008890042085c4d114039466408508215101710003011401000706004d5120b90f034090401811400c110302607440802440104681030250049408086c07820b01589107001c80142d9440070040d180400341592440405c2c4281c5a00510b07040840d001740d0120340506092080f00c01e501e240344507900014441c80d42140fa1403601040c1a030265400b001000a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 987212859 1250 987211609 987211613
    0x30100902030f2205071206050924091006030809090c040308040504020d020c010207050f1e060406050c0f0708070b07260c0c07030b010e10061b0606090906020d0b030613 74
    0x3180e150180104400b0240810b03000031310800003c0b016214014495400034418030302141580c0028040b802e180e002410517150100160382400c60070820a0000d000584420101a00f0024040b000400340350500c100442844129801011180c40544040c6410f13503d0201941c1240102c0c0402002d110b8104000c0103c0d00e000e030040c0c500d05400c09001031903d01c071121a242280e00c10081103c15411902020150b21000d008000c0c2804034951304070341000b064035845860300e00c024001880680c1d0b403008902409404000c0c1c4607401c0c000410255521010305018100f500b061300b0032221010100e00040c1d41324800c620000c04d000d64140c282490044a0f401c52074038140c0101070341c0003241d091100c0141c1900400c550b500031402540e50540079410801448007061f4014140d031004407511000300200d0354840c901e84c1e015170881848480c0c3c2211441c0c0714002c1c00090748188803040c00c2900120610034180c0c018002e104002008012032070001082c152070f0407041352100580f044240308000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 987214109 1250 987212859 987212881
    0x50a36180516050a1e050405010303200f12070f0b010e01090b010c020a06030c02010b0a090e0f120403030c050705030105070e01022401060f0302071b0314010501030c0b30100902030f 80
    0x80350124001c2c0c5617040ca40303410109007200c800b40d0007900011411110080340c80100400f600364114401e0181141078920300245503290300c6421881e40c8100002140710078040c4007181c07510390503442050b1014650b5180000354103403100307000d4144618a40041113200f58015640c04880381d601a000b5122107141540a9005040c0c2c0d0202100795500d80b00003040558440c0c4201019019580000030b50b003d003070182c9450a03104925461240d4495034441d03ca070000c0e401514100d981c1450000b060940718584903003040306503403140303406600304011700000503000101c1c0d82e1401000e13802c441000c0107401408071b01805403400c04100110810050041034446e401c6082e24009a08000d4a81b6450b170765846030350030301c03004000980520000c007801004980d06808910000d190024031042d4103640380c0c031030b05c12940d1040c1800484006a070101d41148008404c0003420707880001c502001110480100f68041218000c0092401110120300c0b1410341c400c2e42d005195580b501103465442e004084 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 987215359 1250 987214109 987214139
    0xf21070c0311010b040c110c01030b090103120c0629091b0f0702030f060f0708040b06010c140f0604030809070612020c0c09010605040f050a36180516050a 68
    0x882c039500c80b02c401100303880d01d01983c00d09100da69103070401c40140740d600a047c45d1031340c40d00078101828052808119039803211181c0c1542d0b004030304241c1c25032620304143c56000054a000f06001e0401ca81ca000c0410110140a40d4201c0010b10310000c5007060304001c00e1315411944d6480d014205120040701c400544040c0c880c01d6082f490140c5410b600d900042c1c035000700a105d0087c5544034504008a02d0392640071540c1103801402d010700d5908050b45e540c1d00c2c100006000904002c49c40810344180940b0300c84c215015040c1e081aa08103504800040e40c840504940c00e41c041525280400d0302480c00207880340444070640da51007010003d40e240e000c065407100c080d100d554420381c1a0607540b0390ba0000d155000348580d4403050380d0303a0b24008800040e8081603201c90311610b00d1580c10400780b064511001c07144075001100c9501130b01405608285000101c00e24200c45103000448128940504828601e2a018008880304406100c0c1980710320b0440d07014660304401d00b0641003103514101d620507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 987216609 1250 987215359 987215387
    0x3020319020a0c0b0711100518030f1e0412050a141b012d0503010e0c120705130807080a1b050f06030405150a0203040219060e011103040b0f21070c03 66
    0x244154021a0b00c1c6c840c5820031030b49a0300070840c0c3c4c600a211103410fa810b0640c0814105101450900f501080c51294500440482520752400740105901c500c1d8030808072009000d07800c00302c421440140c00d100366500d0b101c01048a5041c5d104408143c900c000041c01c00c2d240100d801010218040e81c001110342c3d1541d43d1484151455041054100560210486013005003580d00e941c0c5a62504c04903400c54003001d024090341d090308010071414040c0c0441929031142544c04c101e43e4031611090000b444024540c40008180a4900003290b1004045020803100340104d4500e00b44802110364802681800d10a55030b10070042c0300c2640190a080c0091903000c0c1c010415204403400302c1d40d100c1c001c0c1000700c0d65008030302c0d40081000b04520789104444410301a4042820b0300c2c9091100207482240701e180418141b0602c0089061030820803c102e5010306500c0310b8007901d920b52030300d603a801c035045260844802c81042100030b0b044071911100700c0c03054000343d5883c183c8a6480d241a20705901100c1c0c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 987217859 1250 987216609 987216617
    0xb04090f150b191103070609051506090a0e1603050705040b0f03060a0c020a0b150117091002030606160b1008030313080d06051002061b180f010507020a030303020319020a0c0b07 78
    0x101604d181d004d001a01c0c010b030245201048116191622500380f142c0c1c0403106100c07821402c24440c06072a108002c5500c9201420006045e000c840c01452600c8400c80a046c40c11844200101c01c00001290220480d0001c1d5428060314402804101800401d0b8007170f9501a1b000343c00090503580305800c05050840c2c0c50042c0d42c00b01c0d4491302d681c81d1750740c0b040340c06800324030685e0044181964031950140720f100c05461800c40c03d0030203c9030f140c0c86d0302c41084d02c5010300d60040080f480766030700c0d0710486402c0c4089455030751155000b80360a44218800b1901081c0c481d50102002401c00c00c080110f0f031268035132450144600c02e00e0743c0e4085150f0088036140042584d80d203004200d5031105c51041001100b80d800a0030310303152001802003145641d102003201d60006106410f1803a603802d5500010700811642c500042003c080101d80341c0c0240ba1000e98003403002c100000030306425500545c09402c0c6040403802a61034400d289083c1c0c49145801c0001840704040c01d000308058648050708140e09140c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 987219109 1250 987217859 987217877
    0x30206180f0904110a06050a1e02070b120912090310051005060a05270f0d060f14010f050a03172209140f01030c18060b04090f150b19 59
    0x404900c410400b12011075020420044c000f2913460700303902c2c0d9001000306143c5146015020720000348024941c1e070420001034215280e10081c10300901091015001048490380c271180c0c840d000341500c850555484000d80034000d011a070144050040340d02d812000303402011405031484109006000041c40329030201207409000c281503032400300030302c107409599480948a910300c1032903010812991010300b5030559240b4003085191540041c450302c030041100c003610300e90604c2c01c00c02e018040c015400d4180c0f40c90846000003040a2000260580d071181d00030881c0151141c00f481703081a11404050040c00c4d204e22001030101d0084000c140c4d003503504084000c8203102d0a40e80c0417410380c503082248143d45680c814000c09440008095000c1466480301010354034544510188803071600810481490142c00035080c0340d01e60700904002c04400d084107599a40d10a050401400c207030350740340e071030504101507000e0103003000154005942c241003200d40780c41c3d8400c840400d405850b120960070304c07031f00e49 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 987220359 1250 987219109 987219139
    0x403080103140c0612061e100c021201091208070507050303130510050a0506010e0d0c060809070314060709060509010e01050c120d02030906010602071202010507061107060603120903020618 83
    0xc0040c004043c504001c021481c20444100049050f82902c501d541801e450f140106070355138408c038602803580d01d06211071210503900109040f002d002e002c1c90301301d60034a41c1e07000070000d62040351690500f6595801d0318503103440e2002c840b1482404e0024045078001c0c0f000c036070850300000010b06800e10a90031211110074484243d030507510102c0f80040159580c0d0208001c6580001078000c0e018000c44038180d07075000c1a559400703240c0c100d020700000c200122000030450360040103c44007850300100c18103d0f801500b040c60384d1340c0c24100c07a02c0c0c0c00030700070000c000742031070090041d0781a050b030503199030310103060301001151260009510106a445440185c501d421a12070080109200c032403800b6a4a01c0c4c05101d044c945001030340110219800072400300450410400c801c00c0f03095091070f00d141e1b41e07001814400040c040d4803020032020003000901e081040041d0313021000f180c0c0b00e441c03207600141000206071020b0b9034500c40a074100c402000701191111140600c01c3c42c0000c0140b910540c12100d07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 987221609 1250 987220359 987220369
    0x518060c100516050c03030f131e05010f09020d0b0c0d060f03060b060f1b01021911010b12070e0a0e2d16090c0e060a0201060e0f0403080103140c 64
    0x81103110841d559610034001094010340365210644498202180340c566601c1a03180d481c031000307140c51024011003012a2804e010407100b01c2c05107030801c04041c0b0f5582c2082a490400408503011120340d841c103c1100130000c01801a49800e07a00100007400745181c070344400540200060501c40a17420070030041000311024801c00d00074140200740da400040c21450018116040d600a05204480078000032040780e164404595002100d035106169200c0b08806480c064001c41e031a61140003615106a01c0d61540b01c03e00d50305000702c44009101d8214040240300303010140580e1030041d50006c0209208403070750010b034207412120802e000215038424500f86403c05200300c00351403155070b403c642c0142281c0100e0780007410743c0f520700c0640f02942240c10700405807000ca108a610854940702e440c100940143c0d1a030140d0706015200554510005400a000700024058000f0048054000ca4421840c1c0c0c501e151050f90300d515007055503400d50b190301d1000213415900d90308912540300410301d65252 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 987222859 1250 987221609 987221623
    0xd05010b1003060e0c0301080319170c0a080f070509010c0213061403100606020604170913050109060e06211606021b030606030d0e0103060512030301030b010b07030518060c 76
    0x540d81c0000d80e5420700c20300409244d009004641501002d0005010182003c021185d0000000703004000844a05500b900c10192034108043c9a100c2c6404005900802d50020107484e18155900100d56555030180d000004050382d42c0343c00100c05028440f0154003800404000398001812414510200301011040d265650011010395040d504e80303032520308080001000c138410050050240c1c50030401c00a41d500b8000f0005065221900105840d00c0c07044c904035010110081c145140383c1600d040100080c003002e01c80c0880715450b11500140c2c1118103a0b0642c040e00c002003071140585c070b0004c0000d84025014004490034010200005001107078501490000d0401d83c000d0100c21052082c10450010650841070080d000174080010f103039004a203e140c03109807420b0420301d44100320012001081079402540d0415000303028002681000005541203074401e4070700e503a80d80c0c5ca0b51601d21880c0266003005001c5202803001d020b84055495411480d09405003400e402d14805002540c5440c5c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 987224109 1250 987222859 987222889
    0x9010801020901021e061501031e090302070504091707020303190f03050109060612050c130605040e060d0201050d110d1107030e1507060e1905150f04110d05010b 71
    0x9400100b810701075805000c21221881c452440400700d455502d256500d95900500032a10202a082c1c0c8945503800f0340e004801e000b43c1e803400440458a10704900005100c000300030b5002d4451890009814603082c011180c51a6001c5109080d02c03015584201c1140c000c030b08100d07414001031080c042000342c0240e8030780c445c084958503007001d604030740e02c00303012240107170040704105041400510003903070010b4098241071102c000010315562007101d640d02c10b0003090313400500390040342c000003007440d80039002c1e000341c400850032078041d81c60b9101000703084165044000e02045082c403014003814a00e500c184240240014a24940510700d0341010841d80384031480090b41001159000074568004078000e0350100c04e6561500402980b010940c142c0103c0c0340080a083e113038101946e41c44420301200070b80070030b46214121208054503110781c60300b02401d0806a50100e8500041107022040422800380b03401000742d440d51041c1d40107001c00c4001c000000e48645d900c0d0055400d080c2c40303074188400d501d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 987225359 1250 987224109 987224111
    0x40020c030d05060a05100516050105070c0302010e06070e0d0c09090c080d02010605090c09010e0603070c120f050a0e010215090c0102010609050405071202150f040f120c051e09010801 80
    0x40105040c01d411542d002d0061400345580007010300090315081100000c0b104a0700300240c80d1940285a0850484201c0d8000e10950800042c0302e0010342129032106203a12a800074008480c50088080d52101d00320398502c0042d07000c4401e17015500306610a824054001c209100758141ca410042064801d13814048901e00c529184c1048012014410662081418402072000514020000e0001200079060740035006000603650b40c1a0700455100d2503030200500555140d1034124006010504061000c1d250f90030705811a13411070b441100103001c041c02a46035103043c41c1d6000c80c1102c0c0d0000c4001a039055200d4880d041c5840c0002041441c8100002001083d40c004135500090940e0350641c0140c840f181001e083c00700040000c02d03541c1c141c4010114282d81703035004c0c0c0005945904807180d1100b411384005035208094504a00400c10b58485825520342c0070358a0701c44a43c84c5600c4800a0513a254250041c030151621b0f000c214456540500f20f0418002440009000c0203400c3c1e00165040e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 987226609 1250 987225359 987225367
    0x3090d080f070501380102120c031e0309150403020a261b0d030606090e09150703091e0203060a0c05091005070611091318081801090540020c03 63
    0x1220401101c1403c80c690500c840450104580c0007030364811000c50030a8005d0008603002042c0d503010000d40b2400c00f02c2c1c0100103110b01c52f0741380c20721241d88152201e80290007024414180f07088100c148030b00581e456401040c3da50900c0d00c0d503490354108181942c19100c00540b940c2010305000c3c01400c00b904040b240703054009600300e5620320300340c43e0020341c4013410300300042040103031340080c3d1040c21078000d1407000110b44c0d00e4001d0503041040c0819007040e400c500c0014031403c40d82c560700c8901160300c203c00c0c0014010f0b40d218108141402440025410b0303001700300240c10f0f03000075009607030708541c00e007002410f000c407100020f601e02030501034140c00070f030b8003081d4602030204600030540d4600340340316001d10b40003040010501c8290300161070100143c980c009002d00d42807003994107000f290014032503038980d4a210210058000e201484600003000c1610106443c41d0200c0d10801c490070703608100d2103490224444020728400505003848004200840900c07a01440c0003c0121071123441c05541c1d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 987227859 1250 987226609 987226661
    0xe060d080d061a0904050132030c03060117010605010815010c02030c0307120317040c05120c06070f0b090607121d0f01061e0b07020103020322030806040e03090d080f070501 76
    0x4482c0c1c16485243c80038a4451120a448c00170031842c3c0c51401c209013918080602c14000c00d180800c40004680c0602c901000001c544020244c0c181c0a103003024000d1009a43c0c80c0d004584070041540c52009450303d041d00403850350300a007c0280100d101900f642c600785900740c00603082000951010640312130460305a000c055212440c030a410700c00310004111400d00c2d4690004140c0503010380d90251007190030083d010f010400c2041c0b4014401040150b881d1030710300d08141c540807000b50407103140c410500841c0c500100800e0451003485142da0340464026542924001f40c0092111a1310300c00130ba80030300e000c4807814010700f540c0e414100008143c042c64485210078889292040034100c2001190030b00102e240001101c030b1107502480c000da00c2c0d88618888100350285401400c1d299088035507402c1c10075810518007031103488102c03070411980500758900b603100d10815030006d86c0098840d5034240081c85000c00b9010030504c42c0442820103071180e803980e086540e14000c2e1004580c5440b50102c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 987229109 1250 987227859 987227861
    0xf060323060c030c0f0d0912030b0612060f0a181a06070c09150504020c0a0203011d03040504020a0513080c030c0402250201050f1c060e060d080d061a0904 68
    0x410010396000811891902101410035404040c1c841c00c0c1d020000910b9007141440141501d040e2100320808100d00305552134218980c0c2d02c00c0c50310341d0101e800c04026041e140390082c103071007072921403507098140b95407074204000d0582c40450801743e1290b1100303008a021003001134820f904007190480011030a00856404070006c01000355203100300010001c00d000075170b8010b0054110780c0c1c00440072a64201c1d4480c2c00b100700d0010782005402038130105510310b8519001070200281070080e8000c100c1c1540030025401c1c80d0f440e81e0880c92076580100700412a60070954000e101e000030b1464442d003410203036075252040049642c010305041d440001c0c005140c0c601372141c41182c8030200d80862070510001741c501c2458a40c8200d800c00360851a00380d01c150390050044481140d41d400c5980e17541d400514423210280c0300c960f00003641c1440d007140880c081c5810043c0c0b0307000744c03001040a1115055503840c2c110f1940711010003030300f55803600e10004010b0510766101d80385400101c1c0d103948130f02d403240c1840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 987230215 1106 987229109 987229163
    0x40f292d070f110109050f120102070209010f090515010c061808130812070b130c0801050712150e01150903080a0f0216081f0f0603 58
    0x41c00c01c000788680c2400240b00780d01c48541c04010100468507803055002d055042a4040012405844d014500c3c860042200c030000d403401c4040d40c0410448170003a40b240121044807001800010880d01450750301c031058694030240310072007000007803401c229070700b010301056901c103a04a4841d06181e502040c40790020301080d61140b080c00c1041403c9003a00c6400710a0040c1c2d08088203111720402201d40d0141c02400340303002501e49040e0601d00340c0b0f240d4000c43c1e140495610025202d08203024962103981103840b01c410411440103042c00755204c1c14121840a40a0a030071b00013002c0c2c07444950f0541c1c15010041d00e0322860504241c0d090002a00041c00300c6601180c91900182d002000c1c8000100dd9401d0700e1504600c80c0001c1e0259202d03000c0d01074035030840100c9915400803003607800ca4440d20280f001c6686100942d40c40700303c444a03001591710843c0011268500b0703203000106 = true := by decide +kernel

theorem cover : BRFrame.Cov 987050359 987230215 := by
  have h0 := BRFrame.cov_init 987050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 987050359 ≤ n) (h2 : n < 987230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
