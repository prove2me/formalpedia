-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3301
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:15:37.747038+00:00
-- url     : https://prove2.me/submissions/f58f0cda-7eb5-406b-8da8-598e03703fbc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 593525179 ≤ n < 593705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 593526429 1250 593525179 593525201
    0x603181709012c0a0617011503060503060a050603070e04030807180b0304030f020106050409210c02060f074808030406020f0105010602030913200a030218030705030c09040204 77
    0x403c142500e040c08020501045203210f0036140301011981e5484251015031011203505280600c10f0014064403150044d001c02c60011403602050041d5100d001c00e0901d081a141150000c0d05c1d0702c1080058102009040001d10340c8844110007868a03440080004101070300030340c04c101340050240d42c6050078101c0308000d080c0054100c4c0d680e04240c80c003c7c00d01070500d0072020141d42800000035851030039100c1c1c499229040342e402607000200707009600890600800407010300c10950350440141e00c07114054858420407a400035600d0403a8200042207000408103600651000d1075036004d52418542c2d04452003003426101210411040500d55004180760021400e91102180001d2015400246d00141d564800001c010a98071054100e031a80302c0d9015903030700148420358a1209941c6684024088004043c0b01e41c06a494645605403a074040c00c15840041d07004252115844200b141c24405003004600030a0b1076450180031a0b200c5d00f40000c0c00c0d214520100008042d500d89420040d1619 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 593527679 1250 593526429 593526467
    0xf02040605060d0509011401290c2a1909051302060a02010606081005090c220303031b030b03060c0a0c020a030b0f01090207051b0105070501060807060318170901 71
    0x70043c0d02500c000d00c070882d10b43c01075608000d500030890380800c1005050741d00311030303401d0f0000519014640318200f0400c040b40c0c00c0c1c9001c0080005141c000c0c00310000f100400c8504502d4005182c048122601030104018032646515180d26001d0840314860011a03440040104055459080d1254a020780000207500710900180c403c40389a0b041d84200305880c0c030340e00d6141a5850300c0c0703d04460503c0b41d002d032a41000f49a000301700030300c1d40403000d082c215003807021200717515241c0d8001004511803940110f011039280d9011211442ca100c02034504d4050901c2d003040001d0308100029900d00d00545200350341240018481c1e403507485011500c1015801030f00a0100f181d4a141000c44000120364103030311540c0031070011031030940900840f081a500500103003030300085112000c2d4680a490419070622604010500000b02c0c207010300401084a45c0152510a140402c0a01621480000c1d41c50a40e503034200f490010b1003000c580c100c000b04c04081d00da03c90303855070016150302c9000c0032069200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 593528929 1250 593527679 593527687
    0x90611010e1002090406060e060f091c12140309100c0201022104050d170105090709080105040b100f0501090909022107082b080c0d0c0206011a0301050d0f0204060506 73
    0xb079907a640041540e00401d840800c900ca40e694400c49a42c0304080e1400e40c010710801080d210035401030003410203810001c11621841c1200310201420b60b2440c04200c070240b0180301c00351076864000c1905200041c0b010642859450008101d0b41c4030b104900b05142072650f1907054610089c801d5065540c00f0000840074141407409036005d58446104035005c9a192095401440710684503c514200d0070440c4030510b40580d0801d000c1211142c0014030030020404c800d80b0004941800b4001c060155010700c0c0180c4043c18001c0001a01110b50b400803001c03161000700411259a00070008800c0360001c58002440503a1840050b240e10400a4480d14184034505c0741010070704046074070030071a58160304403251301c00169102000c0781e840410902e0aa000740801d1a049070043c24859172104408000c980741c0881c4888a0044032000101240141c3c4040014014403880100c14410a1000740f84542158900030004070211710490005104045e0324102c44210b449035007004002c0c1000804194035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 593530179 1250 593528929 593528953
    0x8061207050303072d030504120f02040218030d0e060d0b0f040207030f0905150301060309170c0d08060405011a07050304030506010b0d0b091b0906090901060504080d0807090611010e 80
    0x5c010f0030980d101500c1d240314442400b925070001c26010156410784901c0e090034580441c110740640c00000039a42c00d110314040381c005a032240f00900311040002210b0800040060a02d40341401c18100c2c07100f800302151107c0441e65510b0306581e20502080408181340c8006400301c0c50407548000055000781c00492014201b642110f01e0402c40b0070719030b4554101c1551a030800c44050140e01c40303001c0300302c400c00c014068640319401c0500c8843c060190640c1c0c50010f80209543d5920500702c0075441d0f08119a03003208260b01c030300400d0700b10404403400d002d03550414001d2440c00c0212002500304410004124042020078026034008607008400d1310340542e0358030441c4920394491914184060715000f4a41081d04d40311841e18042e02c00b940160700514074032120210b0a92010185643c0035105000d000c1d002d41d2600364181c0645096a12241c95515007030340c90f440c2080c2c01c1c4030007082c801391030100045aa40921860119005ca01c1e080d050385840f00c06141c0100034001c4180c29a001d01500015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 593531429 1250 593530179 593530193
    0xa1e140a06051911040308030c1b060702010605060f090d05150c040e0610020a06020306151305010f05180609010507060e0a1407050307050d0204022505010b09070806120705030307 79
    0x31050b00303101159401d50f8080a602011200039134154010b041c428081030001c186c2c0c06001c0c550026000c4c0007146401d107546d00b80d03c600c2048058480481d4801410051056428080d00b0000c01d415200d450810610100311358aa00580602038011180e1b04055000c0c80410043d8501d0700ba5980e41d8448070b402c1804510040340c1c01405088154000321001c02c685043c07d035086440001c481d40034003074460469840170046d62001e810603900c059611005034006070020001c0400f4800e04c8508034030f940c81c02c00050001484075089d82e0600c94103102491001050004040500c00c04541d03907070b5600110f40050f5414040c900010740f50515000e05140303d2007000070310504035409074401004c507030b100102080c1c2e18803290291580641001c0300420450401060020ba4144020805818801c0269412003003000031041c0e80c3c80c0c0040c20700003c09001003032142d2002e0f50000e03900c00c40c5501c0c1c9410050b01c4030380060041801032692020306592030f0800e0050002800009050701d0b540d04407810800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 593532679 1250 593531429 593531431
    0x1b0106030302010b0f060724110310140d060c05070803090c0f0303040f1e1203021b060909010605130317040e18071712070c14030a1e140a0605 63
    0x100950720b48024002e80380f4140130146a500c1c0300030310840c07420903c2e64823046034901c000076284060801030b02d0708020102e10f004000020180b940841d840c4c0c42c00381c01e0750a01c506141c1c08078044512000807030142d41c1b180511461ba50b600300001084e07250106004607005d114a00c00900700040c04024000000b1020811440079030303040f504800c8900c00c00c07003059200d01c51403180000250701c1c001c04000030300482c1c10110002c0000b0321480c042c0c5580da50b4240ca00d40415004800581265503410340036025000e03e50f40106d8265078a604000306000421503042c4180100070500001142402c580c01c902d8426402440d0701c0400646207040044a084158103c0d016241282c42030000040c0040b00e903507030040718003c80c100200030305440c181005210b00b15000d41c00840c2d000e1022001c407421680c000034849288500c0742c2c24942460030903114080080c20b01601d1190b0031038032821000c2100c810300748000850341d8040c892201402d10b810f50881324800803c5c10341707001e42d030f8020041c0034581d4015 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 593533929 1250 593532679 593532683
    0x602090414070e0d020f130501050901120203062e03060e01180506040b19140a0b040912080c1b15060108010b1218101a011b06111b010603 61
    0x50040012210240222520441c1c66800043d5482806035907440c00d80c150300800c1740054081c1d812199000003140c0d480c06c1c54800d1003000c42d2035900400c903a082819099004042800080c4510b401076030000340c490401078401e4502c000350044101c0c41c0060541c10810400c3c0d4808140e21007951303441c0240203002000940440c0703510f8440720301e0003800469002102d05500c00043c202c0ca90741c0703a9076000b000c0d001500e09101104aaa07419062208510480300403034841d00305440c851624100d00b07403d8455500b101c4d070045080514440c00210a010000c0c44400b0318108108181e880710444003080c00b8000010384401e4074484440200d60000c0384a000d0104550500b40030396407994019500d100083c420310034101010040c008248401100c1d00ba0024180c01d45040200c0c0400c0343e5905c0e10040b00c42d194010340c0c0c1e0740420180f4901e40ca00707a540c805800e080604410780a841d509542c90741020024050070740b106005552000010304548625881c0c420300f90358a174003246c2c2503008100c00c0c001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 593535179 1250 593533929 593533931
    0x1309030f03060b0909010510051201080105010302090a0207030503190e010c08010e010e01080322050405090d0f2c0f0d0b04140a02060a0e150f0c070906080703020d170706020904 78
    0x21030601c10f010100e500c030b1040a448080030b42d10345400e10440e2007401e4910b40800a0601c01107a00040b501c5a00f40203060f04000880c15504500401c2031507200581341c5c080851041100384002500301040d0380e4041610300801004a1000030803c0243c05070384000480780d443c04500300c0c80150040c1841b810399030340e4044c8030312580c0c0710240502004001c0c01469060361040c050340310302540480940c3c200400680c20310300c2440d80d44020405562050710341c22410380004130000c0595600080310680c20303038503140814401d07080401e081d0300c003100e0801942040405034516400c645900524452071280644080000c02c0103083c0444600ea090700d00b00c9110b42d40c082462045100010102151a00101440e151444640f401da80b13201000400c141c101d1051020703200071002d180082c006140c6861172840c0d450381c144c00b0041c1070074004e4101c12000d41c41e03d0750520400c407001803264140c0e0350540c1c003c50f4495207030070100710a80003903000200d803400010390002000034980207400c0484060b94 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 593536429 1250 593535179 593535191
    0x603050a23090f030c030a2006010510050403151e0b210708030d02070c0905010305060604021b06041b08010e030d02071b1409090a0209040209070e04050c0705120a1d1309030f03 78
    0x8c0d4126035214440c440a0490303002c2001809103140804124001030014103040e4940365a0b5070314500141d99070802c4000166031841410400c501100004124074010311080110380400800248590491600d8008101e032400d210080364404100c413030f010f0060306044940380d141946005011354801007040341c0382d0320039084c00180000b507409868180c80c1d00c000508a20350b01d4409000084d081450702083d0f880540610400c20303d01444074900541c000c06011001490704141160407903145d901c0002c4580c94407041045200e0007000360740d0f54148150340541d40708000c0c1803008021a0b0001c1710340c06806413400021b80e800d5640c9000440c50f8080c2c030b0940199558000071500c0d00b04000c4041d41101c2e00a0000b40186441c56050f60300c46644d0921240b0300b006c880101e000c0750000c40360b05020307050000d090401e100302000100d01c0d0608043c80c1c545400112040182000d040c49440081403c031003180e0b031810350707403500e900c15001003065003005004001d080080c80074041400340c03c0424a405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 593537679 1250 593536429 593536457
    0x307060c200d14042d0f05060d090f1209061205070f0c031b030302030a3606060e0c180103020c0c060c0312010305070603050a23090f030c030a 63
    0x60303a40a44020324030140800350b160b03810580f002030b01101c0e00480b5038410480402e20000d40c02100114007400c1a645248640e040000c41d40d4501c15080300e191600c0310b020800035079031501700702c804034103150401007009061884e00c4401005510401001b8080c1c202d2112101da600003035100440d03003140d0b24100501c00c01c040c0c040071980280c1d480350000f1118050881c245006054420440b4071901d000400034014094030701052111840c11000a174001062000309aa68000d07415880803119085840b07031800c000c40c0004150342410080c41081558051040c40709032b40c00300008011500c00c3c0e000910700100103807650347c081511141d50401034051007039107520a00c203480080010324001c000c3d0106140070090150000c0030781044502c010404180000c0c840602d480c025031060300202078580c10f0079006410740c3c0c4002d10201625140c0301007080444450348070780c1c500394a014401040e584902c04035600b40840d141040a0900c40010681c002e50070000051580c0b1400c1d5a640d61410400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 593538929 1250 593537679 593537717
    0x503011b2d0509130203130201110c0a120f20010224060d050c040903020a0c090c09090903020c040903020615030601151416050d0e06161203020c0307060c 68
    0x182000341c80d07004000104904580202d0040002d41c074001c01000d0001d400000502c1681d00458452404007903c83c072031000c558125200068903c6158058003440d94100302041c0000d40a2088100c0e106905002c0e20502042c5a03100018079000300d2003950031000c040c5182601f10f1038a99013801840b8200010f84031545040c0b0200101c0115010203140741c48450411505c117900742001c0c1c2c0c0034000d901c2d00c101d0340d5441d4826680c1c42407103038001d0311031011241800001188140c0c03201401608144080316480c0d03224040005a407500c500000b10400e540c05e04915000514007041e03002460000d02200381500018214070681d0304080724810442248103168a4003001e01c2940202a500c030010305e689401200c0c0d0040050481248a0030310410300040f41d809914088240d039240c00000c030854881e40c0c00b820703600304003200b9500c0c50b00e02051964102c1000308030080180152a60220340401240b0940495900c4142d070000c481e151840340c1000f000802164810380003145001d07100c1e010549007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 593540179 1250 593538929 593538977
    0x1030c05060c1005060a09090c051014090103020d1b110f150f0403030b151c06120204051902040b040e161b02030c0d0510111305040b04060503011b 65
    0x40d0014180f40043d034240300024240280c0469402441040003007800c80c42403240464540c003c1c071403201e00f2480c00d001d00c45d0000c206100c103810000d41c24800c0c50f41e2440310f0120366090300c003840d0041c3d4445900b0b00320b1004040b600009581d030502c09050b207a4450b401000344ea081e01c801c0c0b00781c88020582d88041a81d641c0d26171041c20040e00c8103400540035640256441d544680241400314601c0800c41c0001c40010401c1d0314004554000700300d6a00342520440400c040c0745000c4010403080b400c20044001c10450340c0b10013407141da1220001041100160085c8004003141181551036030307110081d920303658119005007960705050100256080e81303541c83c01d000580c1c980d2502d460314043e44e0712502e000e540c0e0443c243d8040c450b1a426041135242c141a442545004201601303078101030403c440b003030b40c80d0200c002500040911000e406070303000b0390090046610443c0c00055201c034400100b4090080d590156605501e042d402e100305194404482100b889255128501d0f80603a0f003c405514807 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 593541429 1250 593540179 593540197
    0x320030d09050307030605090715080f01080105040201140a12020a110c0927030702032b0206010501201c1e090f090c1206030c0f0b0c0606010f050f04060801030c0506 73
    0x201c0310318100003107206d5600542d00440188240d60071240c03034044980d0101100380c00c0100141520342002080303c3c40044003030162112130028040350500d900003d0045141000c9051030324000960070700518040c40121b0f0421401c80d0080d502d8100b040d50203052050b90944030701c1e45024500707140e41d50380ba0010920340b0529100150ba07100d10b4100f150307110161b02100b08090a484100841c4015a03020000e40d503552031010b980c00039500ca040c0040594001d0400b492055500950050040340c0e0466422204040c04034540eaa5140d1460360440c5401d40c00180a44102d00c441007401c2010703032280c074480c42588a107020f00c03084801e0250444d2085280c0c03040c811408101c26040c401042c00f40c10180a0341c01c02c0c5403c03407044000450640441d94968000c454921501500b08410f1181d1102000144840c07501030f42400c1e21100056210710005103c20b040000420701000224060001e88200c0030304031400c503403500d0312404040d250b100700780010380342c1e224000c0707000680c4c0c54105c040311040c0d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 593542679 1250 593541429 593541433
    0x30906030c140f131d151212210a0504110108012106020d05090604020a0b070809150408030d0209040605150d0b0f30060108070e0901060320030d090503 67
    0x101403d424148980c0004405500301d050441c4001101c101c90b903000444101c1d041a4000d00303081030041e641d0740e11080e03030869010f071821300301d142d14440e0b021404103070322005031111a42d00c01002c9102400b0b110b640341ca1100b0081c2d6441401002003099001512a41c0301d262081820481c010055503041e10900c20544da44013a2040a0080a0342e440071401141c8211350250500c1c04854507a410390f48111400109a4407150420017940b40803500300e001010458486071078003010b072b1503001207407081c200803c6c044d10603104001c401840420458004120380e0080c4c07903c3d48500e120b80340c080d51001e00c132544900c1c1880c4000c00c036490101c550600c4c0180f2840b405140000c220349400181400d90714465114554652a030199221b0300c06600501b003c00405100c0310304d4218840140e040e1800d4410714640c090401481241000951030054918000303000b44555a000b040d1405403400743c0000b4141c0100344a0a090394000030206c1183d400300300d00351142072000c80c20440c5c14445c3c91086076415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 593543929 1250 593542679 593542687
    0x8040c1502120301060f0905100e041d030f030709060207050d11040e010f0204081005090304030f081c0b0108060d0503090f1201090305070b01082109010e090103030906030c14 77
    0x1024506a050420003054016948604242c48441e0b510b500240d20036400b140780001c800390181e90001a04002c0c001c11141061000d1058000070180c0c00001c004074003071962202880610f88580180401c894510380c100c9035224102010f140300c5030026a25100807a000d204042840b40c000310303004058587c05003518000e4121741d142c0b00110000d203180b0315009640c030b03214070a441c1402e00030300004034034640015a0351490f01c04c00c2842c01070808410702c2c10b140b914050140c55040481100c007107030342101d562041c4500a041050307143c85811280c8828005815410300140d0558001d41c0f00c0c18802d885410300759840c0d005101c208110900c0003001504100180c42003890801107448034810060808141100008541c40c00c480b0b04880136004107001103000030810600340c007442c1c09404900701130b218003c1c29660300c4c207103040f4a0072211a0680c002c10490080c1e44241d8024003a40d44c01420480d031540c0d21b0401503e00c80c1180580400241840c510050080c0114152394904404146441c60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 593545179 1250 593543929 593543939
    0xd1d010c0c050f0111180f0a0b031816050108060a1815120f060c090b0403061a10020c0105160203030a031b05040806010308090a0b0a0206060414062d0d050102070203070608040c 78
    0x2406c0d021007942d0b44450144440f8a00da220b02c460803020b844250030a5550b424850084be900c4040c15128a9130341c0d00c0756201d44411a440060302d01220f000b820116a251282e800041010b950b94216002501c501480d030340f42203009400c5403c00c4510020008002911050310b061903101081c0c018212480043d820000030ba85a480f80d20385034258503100105646522503130741e441d4481d90007030340d2907030702c41d900040c42901c45a406d0250240490300d07401c1c80d1040c1000a03440b086011540b5040c8000071820790003000b0b5800b40c3c2d040c8554004c060300d6a40b504083c015000b000510401c00114400d20744108a050107030701103605480c0c000c07004000503881c641e01c90100e68007480840d5000451041d0008181d502100640184912074000d05424034100c000e203c11a1050a0300e0364003101c2000620140e9112116010380f034154120405201b0b08802480c048038900b0145525008505112071405008040d13019020680c422401d48202c030f60360f0a82140c10420649002e40b00c1a000a01084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 593546429 1250 593545179 593545207
    0x10b09061623010e1504020a090b030c06040e090c0a0513051e01060f080f011409041a01121a010b090607030201270b0a0e030d1d010c0c050f0111 64
    0x694248140500c60b0104400280501c1c480b50b103410001490791512403000b02610300740140c401d03401c01c61309001c034689032580000b44440c40038480e190845a40302c0f50a00e06413000d0011948640c0302414195503642e0310304140d600010100e507040094090090100e4152408150f08030032504c00510a403281a0340004540081501030060982c1e0740300d2506c6040c840c0d01c0c0c144a18020f04080e00c8144034401804130141c980d80e4000e101548024200340107203c1c2c0080b44100ca41d8050382070359a41c02903a03d5207402c144808154000c0c030900c03403581000080c82143c00101008041c451080840500c0c00002c0c0700040060a000d80300315540f003400382d21503d05011000d001050302034070012407608424a82003000500100c2d07803840c4c1000c030083d007805011a02503400c1d000343c04841d00b000070301c9800500a03124042c0400b20351078075840d1105c841c200d0300110000070b003a95810000304003d10702228080c01c4e924807040d0484003405400d402c5603640006100d00300380b182c0c4403d90a80b820421444d114 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 593547679 1250 593546429 593546467
    0x1107050411040909050616030203101527080f03070f170708030c1b03030402011e032a02010e1519020c030c010b09010807120602030a0e1014010b0906 66
    0x14501d20782032000080e048400d00882c0d0405003e1000781c06d2604001800c82881b1514030420310905d801081030040000800301180100c80b800c0441c42d403111500c0900303c0d2200d01c00c805100c0320103a45003200000741b0f888910b000459131500c003110841c59400300311580741e0140e03002c003904442c288070500000c41e1007a000c1c61460707d5140c6600345015850703990040160825140d0703484664011814001d0441c40403031603004040520019401c41c42c190b80001e02d002241e49401119251b01c50392103840a000c0e401850f0401d1500702c041c61040461a0900030001300303654110015820b00c00c4001030030801254200e80d00000d50300002c4141c5d02c3c00004c00c91010002c0032110000d50810024403500000d102400800307402e400041110741001081251101040c0c201200a4222050070440031340003c007d81d804941c000005a180e55031811504010701d041640a20503000d00c5c0700d128035030701b00760f404144044040300d42c400c040c0c0d07210050f105003400340c0c42030b090704018100161145000e10240307078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 593548929 1250 593547679 593547701
    0xf1008010b09190602030301081009020d060f0f06081f1b030b060403120201050f060a0513090203010209040c05040306060b03010522060305030f04050315040f120207030f030f0f11070504 82
    0x19a8043d0701540c4504864856480080107030400f00040c0f250040c103020070708041d0b0004c04240102c040640008282904c030450042125030785400c40d0303592078003a403c207100a942912041042690310880783c0d4848090b4034608001e0310882d01c0e6040e240b00f013442481e081c0c420307041c1c19154811956400340c00410310300c2505540300c0d00900000000804c0000c0c03d04041c50350358000f04903400d11752129410950080c00c580c1c4580c03201d000610141c3c41e040009180f511035180b0216404044d4008640280710381c5c066640c000742445248954290000014030880307210360f004004140d603a44a001190000b8040c7c47d030301c041c5507035000f0f4032104030070b004178a070024029001480c15038a54030300f491640700f107000c41d59402011404001030720703051050821070515510019010314003995240707520ba03c2d854009000e00c8088a00c0981144200318a0000c5d41d4003080c500c507101d6207410042c0a0f40e072084481e200180501c0c0e003420303842d8890381c101b01d0102c010f480140703e11070800c01001701a0200d41c00c0c0d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 593550179 1250 593548929 593548939
    0x605060625080706050412021b1311090a060c02150c0607080603160e07390c0e04030c0204050702190308090c09010b13080604030509040b01090b0c07050f1008010b09 73
    0x1a110101d204d62103401c1c080d5204202c001c0c1000020040039086c40e0501c5401d0b1203500c5030444848035074507504203c4880000020000031103115894180c0002d0055582c11030300122125008500700750040c04031140d450084840507190382100340041c400e80310f03640782c0c0c422580098021516590180f100036400440040035201c0da100c4104170000c200495034480502101c0341c406004101d500004a07690020307190007402d00c00c00040b85400c42c2190a079614011400030f5501d00800e1200c1c0400c4000a0115204442400e08050400609406075034205034452442d2001140034980001114031460b52464507801045409450039a600000104954041e0040308802c941c40d0351002c4942d0702801418240c10340320152031812124445254000c0101c0307510481c180000700f81c011081c0c81c0800340469011680380c000301c1c0101c03040103059103c40742c1c0313a0000c0303030300d6058180119040d02070b0f400c260f5440101701c0ca000204014100d4403452403020812120051014100c1e80300203003400180501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 593551429 1250 593550179 593550187
    0x1303030c031e0f0807020d0215060607050a06050103020a0e04020102100f0f1104090f021204060902040b1509120304060f0302070203120c030301030c0f03150c030b090a09060506062508 81
    0x8002001078003000502000444a1500c903004507001030015030405d80602c010441c120850324060b589100708200c05008112030400989680d40302000c0300c01140e84203050364400301240ca0850301612003030004a204046200012800a21131940c0038821134050f4010042a908100742c0b4005000190a40c0103040d01c0da91050910038250084a442e13001c03a405071551685071000c080c081700c0c0140200001c582c010061031050100800401d5041900170100141c06c40403480010000c10070001e0058022000d00c000c00e081030f03050f4001c1d00c8140c0c41503401260308a150b0648584034404c40c022400490030309400202c5251007507000d840340901c0a800c8403071a5446200801598000d004003030340d19880000140708100d41600180c0007070029440312171003a810343d5100300e14016016070101c0000c2c3c0c1ca102925103030b80f013030f04072466450014040401d141081c504100c050071600d10159400b40c24070380440c4107810200e084a80c42803001814804039100c02c00c0702c0c00d00d816842c1007039070101e9041c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 593552679 1250 593551429 593551457
    0x6090f060c07090509070f0303050a0504180c02010e0d080c09060715020901120c0807051c0c110c0108040f0f0326060906011107031212020d14010b1303030c03 70
    0xc014400d81014000600ea030302e140c0081c0c3e00c15144000c1c04006160000d0b03408020703d03201002600141c0c1e40c1400c02c07680390021004d04031380e0b80c00380c2d901c0300074106251421501c0401c095807100000e01c481d98028400b600300e1034011580e8440d9100c8003000a08224006190f9200d040003400f60718100802c1c507480d0a00310788425003050782154541111135800107608a443d82c2100896189103043c060a000150303010300d0241c611400204000103008001404800c00c241070585000004003c032020045401d6004d8020200c18462002a00921961105041d1503014107500c910a43e4440c400400000035075507003511130b41841100303c041c0805461201c10301000d4640e910141c000380303040c02c030301c9190103000c00640d048042c004505010300d614064282c040302241580540c4c0d013110401d803400410460440e2501c1402c00c880c0d0304d491000c520411070300c41e150083c0c03600c20304101c41c45000d643c03104144405442520343c2200000d010403410400030f40605520100980282021783c1850760074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 593553929 1250 593552679 593552689
    0x50f0604120c09141003020418020909070f090b150a1103160506180d201911040506010c060e0c090a0506090121020f12010207030203131e0506090f 65
    0x4030750407076070403101050030310001c245481000c21444003601d4201c22420200c00b00d086a64150001a0089480e03144403011503112a504100c1160301034444602d80c9000300c45161244103500841400b00c0c0d1204000403800c015020700840c1000040ca80080301942c8a1440040c0e0b20801d80b19090050400d0140217407801400070f0203640781c0c014100c0c0044c10b41880c006003000700041000c11300780d884011607400043d001450303440000d01c42c2002c5030707604010000401c1b082c00398040005284a03186d400003400307415400da07000d002d00c1018601c03050b251003810841643c2c0200d503010b000551040a100200d550740e040303075150480e04015985e000b0140000300d682a5001c982d0344401035124401c0c0719050801408050040c4403803041c07000d400310300044860403010b00082c040c1c0b052074603901844007030790b942c03207082c0703041501c1c0000f150b5849103481c1c041c0d1240c0042da020141c0c00c04651001900c075490751000e80782d0512924502000f01e003480b007044102e401ca40045600482014000c0c0d082d506c0d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 593555179 1250 593553929 593553959
    0x90e06150a020f16060917010615030c110609030f070809041b0f0c020603010504020d02040e0f01150f05120c3c131202010c0602030709031218050f0604 67
    0x455406001400c0c080080b407032030040000c08404ca403040c110020444541c0c0f0820b600156040030f10642c0354560011882c41c09032a4a0308003c440500c400c440c3c4020039010390107014a4202500c5403159100c0d082035081e00c8100448031031750150020051130203443c0c64207000b443e000788030781505418040308401060464001c000c81e040d0fa0300d4082c035001e849580114131250084601e242010b003143e25640032807094001072040b1030003a034010800100d041c07215010360f0040d05280e2038403445403900c403021180414081c400e402200000c464907800c03042c8200580c0103140443c0e203540c0d00c3c181028500511400d001001031540030014028080100d6600d801624021480b6000008403800088180f14121020321861261902041420350340058424031501b100c4401171500c031980e0f0305000598100054050092420303200104004c2403582140041050f82c0c02443e0708904880790700001d444032042d45c107030004401244081040903141c902e101d040400c1c0050310311424190713076103030303069107001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 593556429 1250 593555179 593555197
    0x15270706020706090b180112181b0614070813030b0702010c0305060609030c0d0c03170a0801050d020d0b180d0e030606011e030504030c0812040b16090e0615 69
    0x5040c081000d29800f00340c1303401418030a5078203490040c3c0c4600201c1d10005020a90f81480316104046a80c032101d81c1c41044a072180c0e100e50b0000161514141c00f040c3c41c039004009040c0010080880d29a00c1420803044002111203442e180095030340741c0c203c1c2ca0300403540354801c00010341c1010000500c0604014007407485500046404041004041c09031755000308102d010b1203045c84081900d582c00110740d140150240c401000300c080d1030801e0746060308180c1010301110101800d0a00f076404182c010300540141d5030703502c0340d1a45c80e00100600d6a03640380010794415860801c0c003004c0b8080341c042c26006103210080f40400d0720700031052410422620300801c04928aa111280282006d00041b607000000f480c040e034400c620088041c41c3c80000d0420074040554410000301094041c0c55129034590b040708000d5250411240301009803802110129100205807000c1050b010f2403c0010202c0b44003500c0d0901e059041c40d0b0200201c0c14010b21241e440600d260b410800c3c021480000c019004e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 593557679 1250 593556429 593556433
    0xf060e010209041107150507050a0305150d0c0f060509090a021b010c02010f1512030f03022502010e181501020c040f05061002030304030f1d031006050f031527070602 73
    0x302d103418000908000c0c07030781b490740f01400c0c981003003056a0b004c02250301074012800d000582e0f44618400302c02c3c0710704111109802c103088081000920100200d50000c469030402d04406941d120036084460340515001c0540003007032440441d40e840007a4003d0b001c1d0f003a11068509551030060340103429660002000030150f55100440b802e04c1031103010349441c14100400210125141c05032442200399900000740c1040141000b116203144640c0440e101a598a502034420301180c2825800411031140c040f404120180d4900307009080540210701c01c030380e00040710041d41e0f80b20071100c103060ba05403203110f045008403002602d07e90350341c3c810308218801d0354100003400e1502c2014800c0c0700c01d08144040955005004000001e50300c0705003c0403014061914000a0300c3c01d600306001d42c08a9600e4541c140594141174036198400d070300500c2101c80444000301c138000d501c0300303068031200789424602c00e085049000a00800078248804c190300140c090890004d00d1814a80c1d0800c045604818016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 593558929 1250 593557679 593557687
    0xe030c010f0209030705010507080304080a09030c080106170d020a12020118061a030f07050d020f040c020105070e040b01080109051e0411010806010e011b020604180b1008040f060e0102090411 84
    0x190a0405c038010181100303080c12450a0040d403104100e074000204000c02407400003840081c0e0511642e4000d0042d58044440101140c6814403140645194001c000801018000c56504000b00091001007041590040d180807070311611400f66004180f203000040d50b485010161000c0b01118030441400d005a5001410100110704400c4080c50410424401d40c800b050380d148505c0c000c40c5100480307a08440c1001c42c04500e03c003144002582014490380b0038908844110429010340019104104540d200782c0110380000811044481c0100c0782800207000d0001485103071403d82c0810f403c0400d544946d5815014002075180c941421170342110001d00302d6422404a5800000301e5030800740c2400c281104100060008052649080d0507440c00264440481c0035525180b0803074003d843d80c204080001c40804401c00c001e001c5040a0902550a0241e07201d000e41c071413452540141c0e48a5400140b05105498070000f0b07291500b85107145550030040c5210341d075118400c0c268400941c90201e41c403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 593560179 1250 593558929 593558947
    0xe010209030a030302042309010b0c0114040b0603060c133311060a1e09110310140a02040608010b0c03090d0320070e070315030b09032205090403030e030c010f02 71
    0x400ca110210b41440c088000080c0419556040300c0d1410b6400d2b000d92162614101441d00c0d01400204844400c400d454800780010b024002e0ba000784100700a60803500f25496588104041d03218030700c00001da07070400200a00040d1614600a41c2164054400780c030798800748028400140d014200316404031341440908010441e06101030380c4d00c82e040301c1e000c200792000000c2c540782241c00e4010781008603940310042810462003458411222074090210b07007000302d000078070304010503100e500c0030a0135582c440004e40b405154022078084d192180d0390040e09074030380b021b0000d00fa0408010000540410311443c48181c49482483c20218082d540e6a4500c1c1ca032aa00396802c04d410a40f126116002408144669020500043d40002c0c4034a000200420369565204185449820042c00704c081002404221040040a005800b080c4d802e000402c036840241420001014410260031040303150000300130a00035401071010b80c282e4415a0b262500280b201400c5a019410003e0700a0b070110704208 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 593561429 1250 593560179 593560199
    0x30506180f070f0e0a020903030409020a021608060106030f0e0c010f021f0c1218170f040f030204150602150c070503030a0603110d0506040807050a2108100302130e010209030a03030204 81
    0x10708050310345c10841c50000c071034010070307183d20580c011582c0c1c2580000e51482ca0506c200071100a80100311040304150381c039161000e4585c0428414000040c0c03c100c0411601c8003a8442c1c40030b03100f80100100203590a80005440d500b4007481008294016451240244500d50b0f907a409000c040050003c0d08207102071016051003003091007441c000d0b20b0300018070341011121070090412038000900e2883c0b0a44541c00c00750b148501c911103030840c0d4003c2800500500d41401c02e00a8074400c403000d0181d55120856121080e02d90700c10400143e100b0031007821000103c0f04c5140d04440c9051030f8a18100300d03522880d15650042c0c0d070b42c0d4203841d41d8a0081061221100280c601c2d814100c5000010030b4880e100e07190f4401340900040c01120000600004101040042140ca1980420320382e0005250101c0302692404c80141d2401040b0a480010b42ca50303005001c00c42030301d9006003104503c10321803040000403d108519a2110b41d820000341c0c0c6107940400c00a1401da2207a64056500d03404d00d401c0300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 593562679 1250 593561429 593561431
    0x60e040b01150c2a050a030f02030c06131505070605180d050f0405060d0f23060f01080c070c0f140301110421061506051b07030506180f070f0e 63
    0x1a00b00b18042e88940001a1003010701d51204c840c01d032031040a5440c41c09102c0800405521903075002080030400420400c001900d001d059000700d0565060214950602007188600500d445081d0240d01092100b42d08210104d40d550354130b4500349080000594034002200d00660340c0e00c411900c1006280c180340020400d0410011161400604002c1c4829203004180580d0003050b00c10f80c13010800d199420740720340c40003a4104c0003081c02c0c054104000004c0000b040c0700900d80303000c0c01c0041c00055043c02c0c04c600810070717000706a48104480e038070801c00480d981c000d01d07030446414091000000f030740301c041062030000d8440040c007031140000e59401c060131a2003031280c1010300300d01807104203e261034480c0d640d040b41180c00342e0f1307900c059058a044c1008040c05034000c107102d0340c815000300794594018080e00dd000c5413080c3c2240a44003110000d0390343c031803a220090203179004c14001040200c2000e03074150400400c108aa108000c0c154045007802031036004030b0854440b5a03000c11030360811814503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 593563929 1250 593562679 593562719
    0xf080d0509061b18120319020f0c0108010302090402010309150b030f0a0b070509010908012a0201020310091a1210140f1f0b1b0c040c090e0604060e040b01 68
    0x10407189154808103994500856108008008105a0f010320b1a00c468985e14181507607602542d942c2e032001c036064a803500e01030320010018442d622224105540009481c280743c00140c440320130b503a103982c0c2000419000100104d04042d10b5290318000a4100341880341d00203500310010444500d04014540790000034000c6c0509503014182c0c0c80046001d81c49815000015454401c0d55180c0c00340040e075420040b648130500790740ca8050724055910307201c0281c551010001e0600704c40c2c1507044104909034001601c1c406034100c1c48003000c03c0001c802d80d102d450b000d0030110700080c81c0d071040e01c0050700510458030f907400c007178114000d1403441903014442c803241c5402400511125003032058151404480c024000c05140c610450042c5814082c0c0f941c0000901403200b6659446c50b8110080342201d00c891407131259403003000000d050324070703007030081c01c0715440a40ea4000b8890318160240d440c0d024040c00d51a0843d03074070074011683c01c8005001e10700c124000d8480803002e501d4050301100c012005440b03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 593565179 1250 593563929 593563951
    0x1030b0d020d020d02030102070f120f05043203030f0d050901060605190e0405041a090c06070303180c030c0f060f050f0a02010e0712060e0321040f080d050906 70
    0x3400010303a19580707500c40e982c2d010703100c00c140d0480c80e101290082c8900322020b001104c0c618000300810001c0c50107911f5100031640e86600b03c036011002503840d8000c50060166078802d81c0220481028010541001002e0941000302c0d5010002c5c00f0a085a21800e851401e501d00002d01d00d443c041c0c02e0140580100c5280001c20503a490030000500b10b000709480e01c24200d0105911100e65032180400d407405c200014000c00050501e45070502e000c407010480c2c031268100c9003000070b140c081c01041c2000014006058146402c1c1180e5040f0003d01c1c0d041074815403100d4482105011a003408202000f0750b00c651780f501c42e0704d8100b5030071041031b102c2c41e8448010001500c0000ba043d40d4400140c40002c0c200751101c544420407080300740e014122003000c06101c1c2c4510480010301c980031107090042180202c1c4100015a842c04003d0703128403403005124041d6204a881c2c9180701341311401664413902070001200240b1392940c90140d190b1281e5921010743e0340302c1c001e1009881084c0000c81c1c1000075110 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 593566429 1250 593565179 593565199
    0xc090c0405150406080105092a0a080a0b0f0d02060d050702010204051f1d030c120c0a0f080712170703030c090803120a0c0918091b1802031008010c09030201030b 71
    0x41300401d243e205001d0940107071070100100d1102c001c01600c1203a100342d013280c04a828034a01c1039910954100342281c3c0c1c00540000c0200e41c4508151246046002028041c507000596003400d0107d0b080c14403070102c1c0c00c01c1003004000c0c02c1c01012310802c1d0103080240c0c005070351a07203040c0410a90540e900121400486940e0009031080c0d08000c205444000300901107802c0b880e4000000d06120048413026080f2103401e07414451960302045940b07034110100c1c0c05408064441d1581c1441404a016094083c4d200c180140401800299840c461078072503000e54099100041c41d034082500403440c110003003600d9008101038103030003a0b0000090642e400c0110308080d2185140d81c41c104015080504495071b070f040c0c0342e2025100f81c14203009019840480d501e00612a103c8400815a000003a901d21b500001001a000501c14024084682001300346100d600000b007500029440500700701060f0f00e1040002600715000e0207454200040d0351606120b0502d14000982521041c48029100708401e003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 593567679 1250 593566429 593566439
    0x6060a06210b0a030602130e010803040f0b07140a0b01090614030a201801031b0b0711010201150602061501020111161149030804050c090c04051504 65
    0x46409804031600300d00200d80d40e010071003c251444116040940907a0001134032003201c4143c0714680040301d001030403400041c2c0ea1401895141e0059020780203155030881d604020224031440607005c514000c40f08036100459003452107180941000701114028812030040201c085c691048038000d040d003c86800209a5401c0025200c200506008240304000341e010907180705545a0402d4008014140315a200a0300c41c5401c915142480b044455050b81d420810124880d00c3c0c0b010201d56180c8000742c24803100d5030381c48200f0403440c0300c40d504641d030307803000701c0c0d4151814114800200304035006002d060070042a52003448002ca010b0a05680c100440ba4400a01c20422030301d6001e0244012021444286400e082c40c07000000e1565209003806614201105500321518091a0444440703030b007190038400b102c1188100e1040800f26102c240d4250021a00504900f43e0151140c1c003521001d640000000c4d49101c0199920700050300082030074061810008071080707a0a602e0940039003070a03d80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 593568929 1250 593567679 593567717
    0x102041410030e2e09020d1707020a0312031d1e010219050c061e1303030e15010f0b0c0a03030c020f0d050702040609021e0f0705060906060a06 63
    0x10580380d60145070355400858a9520940c8401501214502910190340e80400c0750380c0070700c103189620002c40b0580e003c44000f0000b140300d0700000e954050b00602d8900a1a220101c0003460060701036000c5400700300310001681c60420b07000103075204036080c403810202100000d0450703407607001101c010351002000301070002000524220300b454820b09144803c40c60341c821406030141c01c1104103900082e4500a00841e000000740106c0311421084603810380d1680143c801c009407080c2e0340c006004400c2e0210758001c4203d0f000b0916a07000381808034400e020008442c0c5041075800c8401c04409a8070014051064412030300001018240b00703140c2081c200c0554140c40e035141241c01014543d5510324180e0325070017130000d130001d8100c07617080e0307070301502c141c20046e0140d4001c2400300e219034a00103000c941d01c10544281c0790101c0d40c110145203a4002007000f100319038008010310450510512400740044d0080201a01c01d822950241c031483c280203080c8103001c01c4507081442403229082e2080302d11001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 593570179 1250 593568929 593568959
    0xb09060a051e040614090c0f0901031515031a0409031d0f030303040302070f06080405030a180512100c080c071b03020907020c0109090e1504021504060908010e010204 73
    0x4211102014204080d07100201902c45600203034115042c0040040c1c094009241c0a020b01020b0390720400d41e42c0e40342d804040f40e11401c410800444018030041c007965110380d001c642d64658452944400c55213a2150912a07046118558006500c030162180152900d034504444100140d030140590a035a0307030003501001011034070400f142c1d102c0000c41c8440e27862070551150b211019080d02d0b6a800c013410b00940b500c1c0319001d081039141482800281c0b007441562000c0c441d07600440918141a4846400c0340e40841d00c1000350a0840758810110340d03a40ca021401c1280e40904c0c00800d00740c0c0d131801d20340f001c4c3c4003c41c00c058207210921040154094044081703481459114070394805540c0005844403441c0711681019420003038889c10806405d4000440252000098a410300f484d542c0348030910599000481168080d046500084080841c6080e0b194100f03100801d070010030402125540782c50b40265101c03000045120204000341070b03080c40b6549240c00080700039441c050408205030117040e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 593571429 1250 593570179 593570189
    0x2101020903010b0103051303110307080a080a050f0736060903020a0b43080c060f040c091d010c02010204030c14060703120e10052d01060e0a0e0403020307060b09060a 73
    0x14044040c0c202700a06204680303010b94404c1c031164407217510800003007041000301c9a5a40c07061502d40804e59904c600e01686e8440c864907681c44044c501e540165901404108041444024000c1c22001910220601620140003540da545003982d180d03004002d245241039000f8a001c000420860001d0784481000c803202010030540590607841c80d4040740c9149108200d5085140d400041070010841305000502c014a42d0604881050321408480005100191401081e101c0901d20030400c100c46a0881c003444000d40c89882c141c09041310a660070b4407019a00780300181d50019060080061a007889009055180c0036107642640f404081072843c4103d0350702030280180c5819180414026410015014030365005072080240d803d030002c0040c0000344c0e1030105806140003040d20001c0188441c40c0111301100060a142e4604041a110111074a0743c43c0d400c413016078400324840c40e1b0b007510703030380260301c01d9000316510406402d01d503003100c622018491182c84540b041c80b00582d02d104616003518 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 593572679 1250 593571429 593571437
    0xd11041802130807091b020c13180f0b0103030306060c08092b050607111504140c190e010f12150f0c120f05060901142101020903010b0103051303 64
    0x2040302850034002501030b0348003d030305105800c804107808980740c0010180101000f0b440e4490b0381080d101b6612099041100c41e005586403200c0c0ca60844150041480700e000800c428064514a480d003151300080321000380e0b2140c990100400415505114140007404d00d8585000040820347c1c0c0c004042c442c080000c1d105030505c1003010b00940c1d60980449032401200700550421109180294079010f040320000f000c6100412044410900400c1c0c04003e08111103090740c2580c0c4994800301e032000107100c4000c4a10a4050300103850f19090701c1c141240398082d04c050340f03562034003410240b00c00058000e030302414072507281040310a940000384c09125134003541c02c60090380ca1441d550014840203048069960400c1c004440650b00150207045404010b801400302c42c03051a2180280c800039150150800329500c010041641b075003141036007048ac01001842040f0810005040b4408040b0700300096075400540e5581c5440e0034030a201c8070a0302070a003440079103401d48070341c28600124803025084c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 593573929 1250 593572679 593572687
    0x2090a0e0a17040905070c11030106060909090510140406060501020d050301030803130503040b04030b0a06080d0c0303090206030a06050f0a03050d05070804030c0f05330a02010b090c0d11041802 85
    0x4202c0320503540a440080800c00992a0592009015014000090303949102c0d05041548608042c0203140c00e483c1140c4405000c0c0e450200014014201d411040c1c1d00c9003c0c0201c158840e2000707004807031007550a43d000044606041c10300c98101e071041d511060566200900c1140c0300c40e00319090741d0440343c00c02c1029072281e698100c800140c1030701c0c4c0d40081007030000044c0858102070fa44090000d0364010701400400340c0d40c0343d00440444900d40140d0b000c070750084410014492140040c01c01407886071501281001b010350120703034141c0050303800115a64841c01c05100c542010414250126411a1140051480e40d00c800d0348410000400c2010407100250364010300030444119401154089000845030f07507110046000385449000300307482008101380c84000009910005488404041d000000d400c000482d05c400035406000524155502d41c0c02000c140d0340e8514619100704a4a40c0042e642e600301c0303207200101e410056081d00074000500c420701c002c5d0050002c00250705000e40c030059136 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 593575179 1250 593573929 593573963
    0x40506070507031106101403060603030f0a09120f110d0b0a1802090f2e0608100504140403020d090f1208070c060c02030c06030c070b1504140402090a0e0a 68
    0x806220801800c100784142c0040c40040b030140704030f0100311649503001f604078440f94010544c8501007580c24a51581c4184105009110450000e00c5003803e581401d43c201581c0301c002c0c64000c0d8a030301c01170b14480c0c1031200200901c84410442c2800040450758002520741031303554039141540c0980b01484d480d54131900e0207103800c0c0c82c00d50717142c10540060080c03845242c8514040f1a0003001c4400c8580d052070203c644402d0502c003460840c00941810725501c16a042400c11115120020010a902524098009502d460b1403081010b00301514002800b0751800c0d04000c1e1520b01702201c0c040c1000100c81c401c02101c074547e070038170064403000c0c00e1102811034a030908002901130498003801080c400700001540a0b08100110980c0d442602900c880c0e415100c20006140801c8880c030807048010007800c0c0000782030242c0c00303078404140c03aa00e00725226804080780c12a4030349010a4010f80051080c48103500d40f200b44140d1003507070030b41d081c004441000900703911021041030040c41501d5002030f03101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 593576429 1250 593575179 593575187
    0x30f070e031203040c0506070c031704051c020a050604080706051e0c0a030e061804020714010608070302040506120705120a1703070f0801060801140612040c0302030601090504050607050703 83
    0x4150038000c04403540141d0300504811203070b005840445051150388000107090401d28281e03481990000d040314526455900e4010507104a440034284c284001c00c008942c81e07652005003036064450a02a4102449600c140b00025845402c0b19201c0c01003480f04201d00c440014488040d90400c0c075106444010a095080003840c80c082ea4110b101030200c0e81c60084640050888190780c000e07602d0f600c1c0c480810044c044144070f0080b202c0701c110f815003282003050030320f038000b041d05038422035001c590b540115035558210ba600b03070000b00c1705801010040003540342070300600da04245c0488000b01071011041c1c03110303561690740c407900d070003480c03082551305138400e083c4500065245c104034001d0381d2000700c1e1201c941580c022142030011500008295201600c0350050a040c0c540580703800c08a83d08040003008400a100183d541c410740800004058082030710565000718070441088400790304501c10142000d605130403041e601c914200402001c15030008030580c204d5201d0401c85d940d180b103424121 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 593577679 1250 593576429 593576447
    0x815240706060e1b28020a0b0106030606020c040b03030307032f03012102010f120f021902210f03041406070e0918070317090a080706080c07020105030f07 68
    0xa0880c80c42c051002488280761500b1912a40d400c408444192010880100b443d001d4028800074a04843c1c25482140b929a0784107413144120340100e401c2e03800a0395032618030310b4090b0088000691a8401000051b804222001e60100200d5083c0075000d0b4020101c1e951740001030140003059102d62140449041c00221144e1104c022141c8441c542100880c040d01580207110300d4a02400041075400c9041c1d40c0b80307401070f155070b05030b4400300310250b01101103a4042070050007010350b039510510b40e10231300700d140b00424850211004001074030403a0400070f414001300c001180c2e95140b54a5000d6540c14011040341c2492201181403900d03501c4a0a00100000c154001340b1414411030041c001c041b5041400741100f0b44084178001c000ea610305201c045408240c0841d07070041da206845c24400108050240000704406590003420501d0307000001e5048085540011000c0e0003125090061590018000317030701c0000c5038229450300e903907035000a0003480010100703080790034500007248215100d02000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 593578929 1250 593577679 593577683
    0x1415220b10090323030a030b120a03180b0408150405030913052a180310090308040605010e06010e010302070303060905240a080607110a020303030a060608152407 71
    0x221040c200200001c2d02030b102d01c2c0001e1322602080003c1d02260800c0348031400602035040051820311103401026800f9000c0064400e9000110040100c0481c03030800c41c00c0c4440b4029900d200d007429081200719501c2005030402890382004000c1030055840018520303805100042c4211465504c0307062203130440c00340d000c85a600500700010300714900c0032a00b00c0c42c020b00074074400d0500f2141003c109618500b2406001c20703485004d1004403607100c1042c0741c5074141c08000e0b0568650008007054103048620220080713020421003414003090103203c2c82402c0c00340101c1c422802c01424421f00207030040041c0d000c05030406230000b905904144c0309420081c0102071a040502090034006011820064403044c0b041e095410440e020f14140341030248001100e4403030340500000d441d518801c8039501c04102109165104448521005840c104000d5100d020214070005071107013032490061502c80c019110010810040325001e4440d91105401e0f03c1e946034910481003859184400c0016601444c980 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 593580179 1250 593578929 593578939
    0xf112a2505040203181b0f010f0c060e0607020d09120f1b06080603101505150f0705060a0e1f0c170c07061107032a0203010509011415220b 61
    0x82c89040c4414003020b44007441c00d9010341b800092903400f810b441d0b4000c1c8207a90340c408420000b0a03440c2d400b0756012010040749103031240394900c4e6500c0b486c05407441c20080c04090b601440410040c1c580c1448000300c031003424070708004400c0c80d00c024008c0b0714031420805000e4840700303c018001c00501081c1041e030040709582c1111415500c1c1d402410300c002c2103c405001e0302680d00d09420991651082c100f4110709000402c80c8982081c05002072006117000801030300e0000c0110807032511088010b41b0046100d040100114942500d1402c103031208000740304104d5110005482c10305002e4135402d500803505010000b0400b480702821503404140b03181101030104101c4c14070039080384183c000d20800d4041c1c0018032450036040d14041c41da11442c0406000503142005203003039080c0c0b01011581111a072200c4044c0024141c000900310740040c0d69079030840c2e566480b0320102e00301040c0050341c40219a80701e00c180c40c00c44404206141544801c040042d404000e8400c0c50303c0704c640c051b010700701010b08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 593581429 1250 593580179 593580181
    0xe12060103122109020312040e0c0a0504030516061e0f030e2103010302040c0801062001090b01171b010c1e08160b150604090f0f112a2505040203 64
    0x10f041030041c03040000030382c080d0180c40140b81e1028480700c100c501311444009803034015900c2c41481300311900039210b03050070010104000004200100714500d244e149030b14118076042c0c03901c54047c001800d522403010640243c015160b000d990040d840805642c4c0500300480d81540203801c01d0b0500305504010680310030f929445008150f128405181030780d1003039408000d456101c03201038980c940e0034407894000440795480b00990300d00901c0c1c80c02c0d0403c001c10003c0390003d02c658554400d035000360410160700c00c203c10021088a0b040210110700200c0d00310a0f4000200000003e000590918000c0d029410249d0078103d842d03298031141c6a03007070700301d00d0380350700d611481d088001380c9451140c040c1c94100044021504802c5840444c06151000400b56031400f840d010903000942000d2920b800060740e20389c0d84501d1205140590000d500300d040d010f030340e01c0d071411034550362076200050804468040c1e0301384032288060019507408000e6561103614024660580001070030400703504040c1d04980048 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 593582679 1250 593581429 593581487
    0x9030e030d050c0f0601030c05011101200c1e03030705090a0503010e010e10060e040b040525080f03030f04060b0d050a110405090c01170a0b030106080d0e1206010312 73
    0x7003d010b480c00c1940554851500c04ca80309a83ca0f0001e00001e000e6164a807810015503001d400003000098158002003920000c840002c2d4400c41c481900d000740b20f40009602c0041030040c4001704640410807003510b9840304001825a803408010711000501400044c0142c031603562003025001014028024403080d89881006400303048181924907040c401d41c4a02c03508001540108010340b082c440c81c1c22070356500d03a260748004080c050825030341809404149008160312240e1096144008182440c00510f40f00c009842c06a030003821840c41d800500074030086880c43c50100f900700f600312501040440c046000100602c04080c402851485020362110402013600420200000e0451742001a66a05840305840d82c130000c0c0b00c40c2c002040c407440318499260f40701100d0b401c9104c18100107002200b12000c80d003111125000000350b64842c0c000030b0300300d585c442c2082c7c903101020b6441c0a0000c2202e0302c0c5540d100c206010083c4000040b503401c1d02c0c0daa114580801d000500f5000b01c0182c41051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 593583929 1250 593582679 593582687
    0x2c0402030924070509090703020c0604050f0f010c2f1b0f0103020909160e060406030614040b01090902070314030f0621032b0203011805090c06090409030e030d 70
    0x2422102101480d0301003402c4510031a5a2141d01c50001d41c0c4400d441e00d0000e004101c2042c0c0014102c1040c1031b82809800392000341000300502c030f94403500081c410b0361071b400d01d05841d00c0d0182102428680c10094206400380e800500d90700c00c08c680c2103401b51200f10399801c80f01c510301043e500350510700c41c003a8010304101e030105900e181c40e4801e40f101c0583c60300010046050348110980c0301d0304000414040b50204625060b072800c040b54901c0d01c5100007001e5000602c1d141e0141c3c0c00b201c0041d8a4680c08d2107141007401102816090846080016844000010780202c0d09481017144440d4040ba40740b050500a015000b031081d0703000d5034150703680313814035100c04110f5040e12071b00c0c0100c2c0e2504481e181552096004d40c00404c2d21001036007030410300b01c0d2a00c007241c20b205d9584003452104102c4003a80503c0e00145020341003400303140c8030380500d180c80c00c0102c034070040c840074140d4085001202c0f1502c0b80402c441d080c840070361300401d000107141000e43d03241100e51215501342c402d5002d209105548 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 593585179 1250 593583929 593583943
    0x8090312190c0c0b0609090a0b010603270c03020d050106081609050a09200a122d02060a050f1b0d033206011418130c2c04020309 57
    0x45003010442200c2c0c8030700843d10740e0002e0354018003404240c800309050f0320341a0101390340580700c1021a070100f42d099071100300c0c45030207074000710200b030310b61034040c41019052038944008682e40c0e15400c101442c9417220041c40020307110290050408000c108203118007900200040c0140f40700300c41e40c2c1d0040c20b05d029055070340c0b4410f080b50f4520301404664100d17280d010304940d50782c1040707014a40358107000328485240d91500c0a07a9104100c0c01c0c0020701003c2c0000d1005040e030162001c0504504500da220309080211041007035082080c0b00317488016942d02c030036144406811720f4101d403030360850009079005200c1c4082550000701c020358107860303060001452101c4d80d09165000e00c100a1142e8040b40c181a4048508455510200c4903050403a0a81241e641c043d00c145401c1c001220b240d512100d159101c044c142d0032401031804807c91600385441144101c0c00032150400c02440c07000300050060b80e0031083c5014090442082c2c0d10f1020340800410106480100304650301c0c02c20000c2e907541c41c50303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 593586429 1250 593585179 593585221
    0x10030f05060601110d140c010b130f0501080a08070605040c0b07060621020a03020d0503070209150f10080a0b011e0801090b010f0801181107030804151a0108090312 72
    0x10846045460725800b20342d9040403405500c0d551590f42c0a003401b205c158210504005c42c9659480c203403803d9980c5c4802c9010b00000c080d400080320b00d10032003400306942e0305800850030390b0b20116004000441c504101c1e01060f800010010388d40e1101c3c5030492954003182c0c407107a000d010114440d07050183c2e5030300940c119100f107a010100325005080b13000e4000a4520003941c8482011010009400c10048026585104c0c406503403600105a0029280f0b030419100101d008201640c20380302d50510744690412030b68110b5007419480108400204414001001460100d480b541250140c4e4001d400d260852075140c00b021100c19850716000749850030034490391110500700200522154080c5040520711641550340c0042c507800c3c07914413144561a498840c0705035503038000d514110711042c2d001d131002034404d03500e929090030a404e0140c2c0300347e000e20f19105001d00e00303850010008481000d6080401083c00d0103070a55a900b80d00c2c60039070080003602e201c0b0154840030404d8070001d018034104005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 593587679 1250 593586429 593586437
    0x6061b060f01052704080903030a120f020304150903030902090a020c01140105060f3004060f0b030303060d02060906040f180e060c03040f0233090306060910030f05060601 75
    0x83e03652030401405014410328804400407414010380614070075069598090701403400c403494000d1140100e80f4541c032a550038000600c202240f00071456050041d40b40ca0401e426055046060940b80d1900380400a003010015669910344801094001c0e045401c0c1250014159103039854007014600c081d40c0000d81e0005554030b031004400c002100e101000d4140ea1000e010541050745032401100d075948480519044c5299010000c58071980c4000c035034903031090f8264014001d08080ca800301c2071703442c86200f010307409003803280070b4805480003c04d80703a014000b00d44180340c000443c00071881c0d40c49554500d80e00000b000a002c11003840d04081c0c07500322501119114000c0800050f0b0340122000030f20f8042c0b241c1c0080f8007048841c804040071b103801c540290050003083c0d81e60342c005440221078200d104a103004003001d007000c091420f9581c5500082c02e01d0b62a150040000010780c54010092002d44600340e50800b1a50b24030741000c0160141d90701409900c0c0140f81d40c1401c5654078811240c1600007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 593588929 1250 593587679 593587681
    0x5010b090f011b020108091906090605070e0f01050a1404030b15030a0c050d02011e09080f0a0c03060207030c0b010e091b1e031018110a03050703060506061b060f 71
    0x1c2d52040c192840c00c0709401d11000204010783d401101c3c000d07000303800e5500c14494045004294288001d5010350b1510404c00041c0041a81c50714000f070f200002c0c1048203215030f55032034003810740702c654141d1200c00d400d18206583d18940c0800303840da038004103500402d0003c04034022040003800c420460090212260b82d1112559100400d540d07850151401458140d509800308914149504140c0080388141840310f40200142d0300444402c540d0b4040e1000240d444604008032076081c400c410380c09140c034000d003205404e00c2d203c080ca984d400e07102c0100b8413540060042d05061103941007501b03842d80815060b400e542c8d207000800c02c0081c01e80e941c4c2e040c0d02681800303090604800b454a5968031000e82200c039201280010f0300d18181240c00805d40501800c5565041418180b00390100c40ca10340d82107420300c1c4044d003070004848034080c50b46409003031010010300c0402d200199240440754032030404100c541d2068089884c0e8040d4a181001d07174802240c07480d000d0080814180c0c0f0071041e1301c1d82d507500307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 593590179 1250 593588929 593588959
    0x30618160b2502060f03100b162102120904110c0304030506060405130201030b0d1203061805040803010e071809140912040909020f120d110d0f050d0f05010b09 70
    0xb00141c4510000c4d0b0140c010000d40004000050140d6400504c0c8a008914a80d4801a05589a00c500548015041c2c9166640b0802941c00040510a03405106c41785280e48090320280d40d07440c0054801d965420b000c1540c6070150340e207410280071010110011500c84101c040386603600d400500003221507024080024001d401d142c85030601c0780c0701081004810803010b8006400410001080540203491180e0403408030740900c0c0040313003800096400140e01481c01c4e0302c010003281c1e9100c020301d1581c2032071300f4071010904810a880c151004605c10301003175214a00309540c80d02d004040801120584000003940340710540c030003d0456802c6056070115035501085a03200c55202c18400355000003440f041c04514410380c48001450300c068450f450f501c0301e4000003a0f0300304c04007400302c0c41940a80c00319600c20b54008040c0110300e09690041000d51000d00014009540d40034040080000114480c072001d0400e070040250700442030810041541c41c0c0c9802501a03124450082c0641441e0002c130b44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 593591429 1250 593590179 593590237
    0x270d120807111f020d0603080301061101090803070305091915180b07031a090c040501021c091509030812040302011107030804020d0c0305031206100905030618160b 72
    0x5081001014100342403240760b10483d1119802e91212074107a09010260354030781036103e42400b550182091988a614011000f804004458800c01013030341850104800142108240e903004001418049010f03a141c504091901aa041c00c1c0640c0da545000340d542071050038240c08150034114103003842039074200450541e8901c1503400c010600415840010007291007a0f100f983d1b203d41c0182030b8424400384100064004106440380c1c17640700700004080106603010448081c4841180b15049100028050050088046880b41e12001060b00341c5040090b0312600100024513440441d503620384d01800b8030412031410441e4118099880c0010031001c000d40f090075200c401c6c0d85959903a0711583c640d401d202c400440c01c10304895000800101100007003052000d03150395103095130004040c1c0390010070441445080800c142c144216014144510345003c0b0b8145c3d80640280e1004140c03034030414031070b490246880e01514140740760010216454809034000c00c01100704c51443c2e03901d1200b0960501c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 593592679 1250 593591429 593591447
    0x1106070e06120702010609140610090308041202040b18070e0a0f05010c11060415090906211103012f04081e07030c0f080f070b270d120807 61
    0xe0361100701800990070350040d1290440e0310600350720002c070b01d0f039960b00d0441040d501e41601e450b4407210b03040c00304040350414207204400030080e4a40403211030316540702c5050500c118010100c2c00312902c00002d00f0740d11740c0d40008030080000b0b0300e64824480c41c0c3d008460360324800d45044001401c07258804a1910300701c0c0d0500d00b581c4444103062000c0380b0340001910340d03202540d801c0f03818100e401300100c1c0369035481010308001c0003403550340925006515030043c80301c00150001c2c201c0529008041c0040c015801d04204840322030303005481c0000007030900b8000003071610fa00380d030701d0b40c02c140348140b0601d08030f207000c2041d0300105141c42c1700004540c200c0c4203a002d42e0150ba41240e125505810040c89507130000c0300e01c88188020f0f2802c698503074855440e0701d1100d410110003c03c81310810443e44e0010811035088904003005403a11f107041840304070141c450348415030910f044d541c2c01c001e02009141c1500d54240c00040c485c9102600c1c44c5410781c42c600102001801203000ca000140040380110000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 593593929 1250 593592679 593592707
    0x170103111e0a050103090f0b07020f0d030e0d120b120d1218260c061e0405060105040b04020c03120907050d08030402040504060f2a05130b09040b10110607 68
    0x20b072807050803c070044009040c901c10585004c6180e50380440440d16104040380190755540c09414107250344090b040c03918094545020401d40303040f00030540e04401040c120112441450b0940c2030010325480d0a010b03102d88104c040d80034000b05480d0324003000024000090245d00e4076003070000070741060356200f1a00b03001a031090300c294661007000001c1100b1b00002140307980c2c0700d0485440442c40c1d4401c40c0c907004084148880d900c4070081c0b0610711074903041d06022010100016051740b42139669a03840300010b2046900483e15050f5611007a515901512210480e01085946030282e910307403035840d9042601d2000d01405001d001050b1828500078115403142c2080d400741c43d513102c942c00e00004001c0100207888040e56084902607a1920740202101c00e4191415481c1c5a441607c0354682140505074000500c90204401064230360105046c00440e061059a0741d01c0c0c0c950b050102d00604187c00300382d90701280890741c185c80e01d40c1000d100d40011a100c001c6840035511890144c540f00e00070941 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 593595179 1250 593593929 593593939
    0xa02090604030b09190f0b010906081c050d020a090e090105040305040e0403030f1a0301050c090d0204021c140108070906030803130204060812180d03090312170103111e 74
    0x401d001084100d000c041d041802001145d00100c070110303404a086041000407500c544854558000f440340c0ba00d01c241c050002600c0411500e4034050f00242d5400c40c240c403000541890311032644007540590306440c6440100350096645039038521000b00803100701d01564251065520105148110511030180b01d0f40d81911907919060504900d9131400300020411801c041d10f07081b011140c0c0c1c0103401740c882928845031040045071340c0041050300750340d8010480840603806010080b05907039141a8039084036010340780142c0d40c44040700d013201c00d60017403045407003103078100341404209084004100b4100d49981d802d40b6185501c801100007500e2842c80b020b8032074142400418401a201140314120707910040001070a1070f80c1d41003083c204842070101079607103030012602480d100b03440c442c3d0850704501100c8569501015960240075007500c2d000107001c0040450600c7c40041c02003030500500445000322036460360b90be01d8900010400e2865050044041d031a5400e4480140c044c0b41c00a0000100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 593596429 1250 593595179 593595187
    0x3290102150406020702060a08150f01141309050f07020709050606070201030f1b050c010c0e03060c0a020f011506090801090c03021219081e030403080714070204140601080a020906 79
    0x39190401c032400303030050300c0c030b65070030040c5070016a0741e280280106501c6444004c0980381941010188040c141c0d0810300885007040e581050b0307a800000d01d1865020300e805a500d918008020100c5074403941c10510303c80349814188502c40f102040041d10501c403507800ca0710782c103032100800c1e4141c44095440702e81040b0203202d200010340c042c0c1c0000c2c0f0840d002c40800a008203c017501403040b00160284100810b03030000741007a0001080c002e1003100300b014100401e281d0412804695560750040440c6044900030036521085032080c4500c540d407000ca0b00090010b5020f100b01e05281031713801d11481001c2243e2110020300078406024100b2a01e4101c00c280000301d01e55001c9c0008640340c8040d0400314051040b49040c5030005985064100780108180c90303c03a420400201c01c4080d2200b01410400307001e10400c00000c0d07010841642c403030386134a005145c00d01d034000c4914040c020044029403160400021102d05243d4090300c61041c0c03026604d80d16503489200c4482c040384144466150440c41c200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 593597679 1250 593596429 593596453
    0xf0102070b04290a0305071b030504050904082109010f060e0a0b3106050108060d1b0b0a030e07050a060f0c05100509060103050d1e18031203290102 65
    0x196403071440510302000d104480364028510f043e590b119400100120b50354805000c5400c0e80b080d0300e20803100c42d500a10000c03040c5514003508034010303441550321610204000408000307501c01034031f0001c1e520300d240408184500c032018a28076821503200c1d010f90b18042c410101c8184900a070030440d000300b008005070b83c1b105000c0c3c001030b00729018000c1c1c0050f00010707a000c2c00c10041c5441c0305014075030355040380c0601c010103158050700c081ea400795040102e00030521003d031b0b0b41c489020600d40d5100d503200211140401001d044404035a21041c40340a0116080c81202c0c1c154129003810394040d029170700c4040d226001c014100c2c0f07807400f6901c002506520041c9480d40104450030256020b0b41c100d4030b50707540d5000d6500c10380c0c800721030070300e80381d0803000040081160410410a0385134250400b00041840d5802c11141e5031080103840c401c01c124a001c2c1581802d4512400c00515084284211044000ca1000d000f0f0110700018002c40710902840620310480c011a50341144070507405070001101c42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 593598929 1250 593597679 593597699
    0x1020703090b0c071a07200307050634020301052410120f0b030709090201171314010524100e0111030a03052707030b181b0f0102070b04 60
    0x204580003181c810484007180b500c6014011144a04d070031170540742e0b1206145460078440300d090014550880701c50614801e59500410f46000385c032010b880d2152a01001081c0d0040115000f04030510140e100c1042d52404a141c56048030f043c0c0241c0090180da228121002c0d8041c00d07084400d029082494030b402d040c2d10702411621000003403403030103988251914121400701c5101c05c100c0d95240f595820301c010305050500c03082000740030341d01c0104000800c0341c0000c1c140752000242c11140e0740c1c401e4006080014244818030310160486410408560000402c2d8020241a030f8010381c01c400008680c502111503543c0d03049044400f410354020003007140e0341500c507041001441418001602c0c0140d144800800145c5828503481c3e030085454208451542c0d000c1690441c1001c604000d14a9000b107007400240701d601710fa0b40082c065500390388285c80304044410b0320002e00158000d401658104040c5aa0100d07a10784040329480b0748400e100c00103903502d20700c0e03102d41201d1102c00c1c0002c010560070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 593600179 1250 593598929 593598937
    0x150105011202070b0c0a090e1b090a1d01030b010b07020d060c03060308070f0303110c0a111504030b060301050603060f15030c1011010609231b04080a0302010e01020703090b 76
    0xc900805400c11a055881d103000103012940010390b417a002c1a042a0780e607011140d64000d00300201941160300b460746558601ea0380e5400003103814440060010001e4a41041140c010300c041d100158490031000442c1e120600284000d90300039078008008542c481880c4100c5010f00d500401c11400d91071b00d41c2c2c030b54018014030088803090594600c40000494201d0000b010310700c1c810750410403d2000c0f0700c1e0160441d569043c007459040001e010307054640400007014541e26810446913000b8030a0703903002075401d05520f180c04110035004100001000801d0880c3d50081c20202c009000c0c943e00c5030181561840119404404060210042500311500c01c20205480c9406810750b120300000320041480310030035000180000c1c4558804041c81b034800e1250760060a101002409281c0e80b080c80ca04005a000d4850224004200045a200301c0e45841041200e1010a12203454568032030702030303071140c1c1c1760507080e005542007502802d508041882100d0780c0b260f041c0c49002c4180c0c1005a9600e117508 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 593601429 1250 593600179 593600207
    0x60a06050f070227010815011202060403150605041b0201290907021009030822170a091208041a0301050d061d0115210804120312051905010815010501 66
    0x4c101e40c09440314064802d4014040c103009002064a520b07120350101c01c200050f0301c54480c0355040b07100140180d4405086a04894020410b2542c007150103940c54000d011540c8129807061801c0c003404502c4034040004190f0130380a4000308214101c4102414054165110707080d00c107a00d0580c0c0da249864408151fa41002c0184125202d9000d412000c9045904000082e0f0206500b20104031240c3c01310004c864050308000125004c42d01c403a034a0100c1e81c0100c0e42c0b02c00c982c10020401404007441074880100400f03c90200b044030004500b010041c0e0741c4140500c03a0310545c66150300381d940b0f00240480341240d4004e4011111103803141c41e040000c014013a0310111100d1000c10344100c1150034001d0803001d8803400400c0c0e10803403819001042080381401914007190700031803004003240d02c150035503086546c01c0384e9000050b03842d490105c60405103408015401c40c074101c140f040f0b144c6e0062040c0030b0361400960800003a40c0302d50712143c3c0c6d003801c0d03d21040404d101c2801400709500c00d03c042203e5079 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 593602679 1250 593601429 593601469
    0x806160311160c0f090c0807031802030712030e06070507090218041d2509200406081f080d2001020c011a0108010602060f1905090303060a06050f0702 66
    0x203000003001c800c0d06000b8000507110000421030030320401031070081110040040ea00104203083d0b0340100980210b50041c144002d240c0e0b903510030403408045910000d041d030f038002c0a0310070b01526000600c4240703e0b030708007d030300041d5a0b070008a02c5040c6070f400c68603083d03080801840c0084ca03085a11020b5400b0303880c0d5510182c07900140301c1e0300e501d841c00b0301d0322001c40007010400d0121b000010309107059480b040115010b03410001072162149640041da007604e001e4180828204020240c0c0320044500c000240810980020001042039200f000306000700788068074460810000300310700c03d0200043c0507107941a00050700700908203001e0208911000000700641282c400303515440e0b0b00b2a0081d207100f041c0343e51510f01d5200406100b845c08034152409003010700a40d41440402550383d0300c01020390300d0009649021460103603e0a100c01280c1d020314400380030340e19250101985075002075079124011500e0b0040860f03603d0164007510300383c11303581c032500d0709020280d0200242c0b401040380a101403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 593603929 1250 593602679 593602687
    0x1091203090e19050c0f0d05040f05030304050304090b0306061e030c1306060201060509150d11030307030c211d1212040e01080303101a0c0a03180806160311 69
    0x5581c2000720584035041c10188036000d0032840c00c4030020340b40020b11185c244401000418001450042501c00d01070318140000b030181c1d114a410440c41600b04000303001c40c40040b00300301c10040000014026a0140207007880944418820f245d81c07944142c071070303e6011000c054104001c9509510606c0c0d0094003c0844130390380e034000003085100200601c08400c81e034880c0d00501c10550240112340c002d001c180d410403007078640f09106414501d40124001d10401e81e003c24801031060720040d8aa00300401416266030350b95500e00902160500c8204031200060360410080c6559590125000003c941c0c480d5000f0000e0013082042c000306900740158400c90b100043d60802c0c02c1004540a140c03034a8401c00d55850070030501280000059001c502c1a61042080040d036100240c01142140c0a0000302c0d03d0190090340001c10301d02401403540043e05c9442003200505912040a000c84000d03003d103c002640c035448842c2d15204112104010f216034030520400180c0300b0b50100034080700c01e1120f40d0030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 593605179 1250 593603929 593603939
    0xc0402030622361407180c0801090509070e0709080303010f08010b0619050a050412120e010e0f060708070b0a02030a1b080612030f04060c05010b0102010b0109120309 73
    0x81015a250200b40301075843e6030050750100030118074958003007500785142c00e00b2202103628070180190040140481541458030f00d0340703c000c001d00e50140c403800c65000d090f881108100f0b0300404c40890210005841d040c00050f140340c4910a0300c0c040c80e00c02014001a07401c040000c070641d10094450810002508400038901100340301846c0a0b001804503950303510300c0d2201c05400d4030103000003e80b254108008441c20360400d99884e1011901d00d082550f16200188420744450045a2000b8070104450240000b00a810103407104400d20f140ca0301d00c0c2c41c1380c2c10801141c0180c00c00d8076a58000070300da0754408043c90b10f2006403070702c0c40c40754210600d840c000d6a6907c21549090341c140c490541c000c418400d0040c0e0500800316010401007602d07e228a079010020100040540300c1401280a089008811841802110a61144540c8041e41c8aa40d024000d18240c2c455030f050b00c081d4602100d204c5250b02c103014620071600c05a43c0d480f2154103002c14001c26460180c000c40a000031074800081d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 593606429 1250 593605179 593605219
    0x60608190504030e040216020909070501051b191103210a08090f0f0708061608010501030203060a09021903050a06050604150201020c06010b0a08160909090305090607080c0d03020c0c04020306 84
    0x30947d0640804100342c120b41d4418842d000e030002d41460070300e40003454144890b0f42e121051781e2805100c0d0301001104c1c9098140b0f50304000101c100f41c04901038102e100c406110322204540b4150006400b180c0b02a0000710180342428070a076070280044030100140712344548540031084d000642202500d0049003032020f154600310401d02d101101360008141006030510900a49500408625405c0d90580013103030024400441405400c2c103040d80440841c00701d49500038285c2c0903045140003155988807164840900103030780340b00b04d40064100800580b004005015507400c540f0701424141c141814040030055104a0343e0795002150341c01e02104688001c00c0200e01c1c020301d01c4860056658022540050080c1002804640c0700051560b00380c00c6a688a000d43c8119044003500056006061a007151071f8400c20442c00d0f070000b00410070405010110f40103007450840442160749079081d4200035000ea014002400c01150003029000304e40d41005d800a41d8800c8008000c10307140030450000c0c074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 593607679 1250 593606429 593606437
    0x31b06062d09020711040e0a140717030c060105010c1b0303090302040c0302190807140d06080708060721181a07140712030e060702030706060608190504030e0402 71
    0xd1950880607000d8240c81141031490003401d2002c0c419840d041003610f402c500040040340c064051503850040001c404000d0001c00c4055074400ca00c60201818111003aa450803a402492112190b080080310748040c00011a0020006d58015040c90ba20300001510030b880b12250070340b030141c1001e00050040300a0300d901c00155210351038244541d4118014001102e0101d000c0205040c810040324030b518041e6800002c10032600c0c50040440d5a07100e43c1102d044001c07010b480d0000c14081402084410203400040c180c0b0f8407401110045075580301d1007503540a0594000000c80e10941c0401410300c00a0030b24846032881440105490325441086141034014a40030b03a00d60000071444008158468045500444946006180d1020000780030140b40300c0e46030000c0c0685111340d07294bc2118003d4210542c040b001106803280e030b26021601130b440b640010700440d209071418030301160f4140030b032201500a0107641701d21403540c0282c4091100806000d0000d50511007120801c1809a6481c0020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 593608929 1250 593607679 593607719
    0x2030607212408101409060411040b060a081602214f080309040f06051002030403050d081522150f09110f03070903050313030b060409031b0606 63
    0x1c4c0752044403080c15034100c4a81500400341d0105800c1401894100002c019030041e8022440a5820454100280081c0044144e00742c00c0b10001c10407450b06500044014480c1018165141d11a104224100d0700c0340041104440d81142c5c6550241d480703600748005c0c0025a0403203070034220804240303801034078821200c00c00b04840b81241e50500c1d180c1c8449000a68060344a0340c41c02c030030500f070495558507030140c420428001c66079501c0c2c0d4075209c0b0242e0048030040502800e010b0036604604802500c1e03910501094615105040c410886144204012885028a000d1039000c03111160104542003d9410740201200300b60660200c04124600c0b40000d08c204400032001120320b066909400324040394808c04006150031150042c14098608a030312100d42c4100490b0340380e4400c001611360054a400c00740561001040300782d25056100720140c00d6901403401004180c0d40c0300704000582c1c950880080000b408551480004c00500000e1981580301d00000302d07425407204444200c0080602074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 593610179 1250 593608929 593608933
    0x7080601180e0a0b0a02091302030403020c01110d0804030509040e01062309041a1e24100f0503100b07120e030a0c030b1315050402030607212408 64
    0x50012090a4441d41e40d4421603080039260202c026102e031001d50100410408a080e000507c4404543c2c1d07504280004000d002e100b1503c1e800e2505000b5501c1ba49003e0b8036000c2100f0101480340514002881000c3c00740c25503481e10719a641d03039412225030300803852443c0c10a44402a604a400f000e0154001424a0615180f04034072085e41c500380d801c41501180d4001d41100044c0000b00d085000c2c44002020055000079040c0c840468544603540b181110b840b43c002c0520902c0901d118083c0020780e074500c81d40041400365118003c014840b482070401b2000f02e845014071a260354010780c05542e00081160004091030341c1c2c5c004000041d4844441180e170300d4600c1010340c0816030003850031840400c01360300619002209607900b4084d00d21034000a40248400b000103007945440412600c411540480640c140001c0b20090802030401a0b0b8106c1c820f001d00c60000390030602c11009002c040501c03403402d1403514054400c200c024842301620440c1803001c1c03c00e0b0f13800088815070307850060040c000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 593611429 1250 593610179 593610209
    0x1418041d010e0d0f09060905060901020c100f030f0501050904112b050f0c0a1701200c06010801021903050a0e030a1e2c032d01060503120a080907080601 67
    0xf8001c20489480c6113074410721000610920034544d1010018041d1001174688640d030722003080050340b81086c1003210a50100e20b803074519100960242907110241542e86041c440c0006040036001903e01c240640c0f50800140c0f80058046035541030713030440d03155000d80030b9507011012508a0240200141e02015510340c50314410042200030031003981401c8040700070305110490f501c0000d265200c5403050040038074980400450b600c01c00c0d071000b0b4008100d00031039503009800140d00703000b035004400d8110850141400000300400c06000316031914104550464000100f060181c000f0840a02401c1c00281d0301c2a00303409220081000700002002031b201c401d9a80288080103001c0010302010f2001c01040d0380704007070030161040f0789000c1d1400720f4581c0d07041c43c0044000b003031a002c0c54482c040020300d00d6202100c031b081901f07045402d8540411000340300494446d0300380340d6a03d101c1c040c0c28505220411001e000c4078822000903030030000002c01c0d607c05079030302c810b094900700d42a0030404942d48401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 593612679 1250 593611429 593611453
    0x15060f090e06100303020c0919020d0605130e06060114070803090f0d020d021e0f060a020a030b061e0a0903120203131e090507020a050f0601061418041d010e 69
    0x21415034481d18043d40a400c250035a81c00940b01ca44840740c1900440c0d1010200383e0800d201a0701d917003401c140f142c045494800c034441c00409081c1e03503c202405204180014045c42c84c1c00d0155008006814000300302c4c0e902c0d030100446842042c40d4103940e108400b8032682000411901c0194040c082c0b1400a010030390720511918241180400d0798003c0d0740c0540355008250b500401c106030501c018030503807444a000c03100080e00b050590303503c0a40f54058001040600f0b80c80364040d104580b4265010001a804101881950712940400400603a144c01c200440d03001c0000040c0f800f803c103481c00d04a226602c4c1d03141940340b80f0000150b00941c1000ca4144040c2c0b1f55071003404010140301154032003c4000b00035001d401c18840c060020603039103032000100750034000c01c1120907456110381101c01042460a00d1a100c4400713018170030010762004102c81001c10b01c0b80540e8040824080c0402042150104100c003c0c410300110012410b03101445c894100e6081c891404220104e0000c2c000c208a02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 593613929 1250 593612679 593612683
    0x60c04030b0108070f061d0405090d020d051204020d2603061507020f0d030e0a030b0f010e0907060e0d060e06090d0206091009020a050d0302150603030a050715060f090e 74
    0x50304445040d07408100200912a1005d01d48000ca41c22814001442d60041d122100300035040f01d0626006400d040a202c0c112030001000d0b240164641e007642e50329900c00800719140c4c4110703107201e8a160104804100945400703581c44485510a4a90240b01c600d602c0503054074100600411304d000e54040b0800802e41082549040641f9840308c2403031400005500080454042500944c0511000c1716104105401a41040b2a05a00610780080a039403842c001050b44000c55542d00901d840e14000144001080c0c41c481c000c0c1d03c4400902170030b5003480da040b01c011000d125050341c48560f90403004003081c011f210307240700d03810910040d048038946509064942000d1744440f13070455100404020491102017090a001480124081000d49403800003410540158104644c400c01d10700007001015000a107110414084400b10324013a40c1d000c0030141c0b03d0107115010404100108191400540410144424030403103110019406031580e01c400315400c1d9503040f610300030740e40e80c117034034900302003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 593615179 1250 593613929 593613931
    0x60801061503091502040b0a030b031b01180b030717130b1504142508190f02072a051207090506030a05060411090106020114180708060c04030b 63
    0x1040024032240707190180035601d00748030050203420036a403041007008006140c601d43d514124148410341d100c039151403410056501038183c58011a2a090600817035040105860401040f2002544d4003c81c802d0b0040d20040ca03d111001c400b45a11000483e17151198009035005001540d41e1a55194000111442041000e0f01003600180c0310300100001452824015901c0302035140c41103e102e52010102d80a000816400c8090310b225504104900d00e80428041c4400d00403000510484022002600c006034107442c00040720900180400a16a8680010100e014080303401803400350302d500c0341c0301440ca2076201448605946025500e9007164035584001a005c00c0b120300480f0030800021654541071403080446542d110310008440e41e80501c28405115080320540d505481c140c0b90141c00310b881070710928407840c002000410641c1c814441c0c0b003083c3c000c10525980e0340d02e807907800710940b40c071003911004030344284c00011804501c1441f4190042c020705510649560a500d048071070100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 593616429 1250 593615179 593615189
    0xb041710140f0a15090c0507050303010b180d08070f02010903080c06042f0f031908091507110d020310091b1d01031b030807030503150a05030d121b050d06 68
    0x4148200030544c400159a054115241c0042c001030203030004e00700b942c0b10300451101522900011000140461444d801805901c14107120815403a0f492402c1110070354000034060251001805501c0015094414004030140141052541c2c00d60b20341c0c0792409640540724420540d00401e080c002041a5028900380540c041b031040310304003e0304c0700140002d024655103035101d50050001076519407410b00114400003031407984c0ca51707201e4445c01c00b840950320112829028142807110281141070b400140c5102642c031201a0208511060420903561021141039070b03d8000e41c0c0c807400d003003c110311807150710301d00c1506840081135a540c4c0a45484a40d6131100c040c0ca154050460300000411f41c0139410b50754843c1e0507082041d40b0f02d140442c0314010348c01c018540400010b103030013495000307005548189203410300e07801c00300305210502c0703101001803088a0701580044c21444909000304078400c20410f104900040d02005141e1103948131000021303140109800041901d8a10114024140502 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 593617679 1250 593616429 593616431
    0x3120807030b032a100c0c060504050112091109151503060d030f26040615050f01050c0a1e0203070806010f060c0f0f05100b0a0b041710140f0a 63
    0x6500001198440c0020840800c035076003201038500104103058542800080c01170b0110701c450b05d08580c00b80c40e0f81220902555a80070001d000520342c1d2166040b50103456040e50ba840315442c080f1005400303882d804800302c0b0b1402008000e036100380c03208803001d0b200b0342c0080f00d043c3e50501c0030401d214218030000084210b8000c2001002050f46072070105a03d100d07818030302100e00c1c1d580c01b4803ca401030b1103861101c19101800100c04c12030180d500c1c08502490207a1020004c28104d003d21200003040d500ca0035401500307009920301070b58091409041c07058080c500751040f88407507a80da40c02c02e248200d5559200c10000c0c1055055040400550000d03199000044c6910350410484070124030452180e94100906000e00b2820800b40002e6910381130761000c03150094808038940710b034031444100e400402d100e01c0d0440400d5145405850b5404982c1903a0000b482c007400d1406e50201c10100c403031980c2d8544214421204100d51510802c140f042d48001c03148841c2c280600c4030100a840541590802 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 593618929 1250 593617679 593617691
    0x11120d1211040308030718080a0503130b070f080d0f050f010e01061107091109130f0b030c1e04020417030304030f1d0f01090812041703040b0f090a0308040312080703 73
    0x40b400c008032034004d00c8a040040d8107209a0320034825247c42508043d03e140206400c402c01c01c00c0c00400381020703466135041d030440e00e40c507155207010b603000c0c1e01000b6102c90718010440020410b298020154444134010200340013603480744400c1500d00959140c150000d168004000f03130182e039000f05024103200d00d00740c80210008064103540345550f002e81580b4980d00d680013401602040216041e9080141051014080c0d00905100400362011142c80c5181010036140c454900030903140c003511b80c001d0000c8000388000300c2c401030b9503070902220364101c0d6081201040d124404594520524126001580e580c5850701d0001e21150a00240b03800303216146155681145034400700c200c00b14026103444041c0407150300100c4203001c141e44002038901500b0303041d500c510910720082c000d58206440040f0916081009991f40748035030300c2416001082401440144d2280710b00401c5ca10078000c240441081d140e8590840315400741d40202d400ca55248006000700b60001c10b007a602002c281020001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 593620179 1250 593618929 593618933
    0x50111090d1103190f110111030703031d0307081c051522051503190812040314130611070501090b07030306080a030e1206060d11120d12110403 63
    0x88440d00440201544280c1102200d2030700c0411048114089048081913a450359040418524412400c103480d5490f45038560146940201c112030700800039030004510b03140030b5407421402000350803900c8071b10b1180c2c09200c0728510303010400341000c86c0c00340a0f0b0035618186004030800108400c0d40c9011907070306100c20004941c0e0038003548a45203030161208949a01c40150030340307140260100201c02070785880240038042e19004030403141031501350102d6000c030741c0510140c44007400704140200080000c00103118000d021102d4160094400d0808031080d201c034800c50f40c9035420906c120300a03c2494001040000d030700ca51103508441c90300c00034000150511000918002141c011250b003003d000070f590042511070b5000e403009204940070340390386203c1c070300d0002c0c0400e0004200324420320940c9905403c6060115104c2d018920007484c03800e01e54800c4d905d50108640114603590300c10100040040d101c0000d11401e01010380c65a520f081807811101110102c4001950001140c10140b200f880 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 593621429 1250 593620179 593620189
    0xc0501140103050102130923130f0b01050310050c09010f020304030501110a0905040e0a030e01050f0c0109050f060f01060f20070927080904020408030703080919030c021504080a030c05011109 84
    0x1034202450f6805040d49d078851052000200301c0c4c03070005002040149005061241283c545070580d00201d0954050050f41450032090741c0b802e80d1070615403107081140c4071140d03005d075520025002076801641d08040e030300d88401c0e0841d5a4001070a00c0c1d008001082e4450603400b981140251104480802c00007010042030365942c0a11a0001c00740201804000281c0e03028405880b21103d45103411640c3e08805102d41e8042d000000302103442d403045050b10161b42d14040351103880b40d00040c207140c500ea1f20740002242c104690030741c207100340002c0c000f5820142818a0500e03450361490b00081ca03003a07207090000405c40d8021004001c82c80e209004500d00c007001a0100e40c2c465401c04002b039160303c903000016000384034651211840d0303c0001610810180c000000f0741c8030300300c22800c0d24040310080c51000050b02403000b008000071800882d0800528103940c003581c812032f00c14616410680ca81040034a8008401400d9000c10300075251031381009824041d0b50350002103021041e04040c00c00c40031030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 593622679 1250 593621429 593621471
    0x21190b060a1e18090204030c0902123112020709020418020d1d06070801081c11071721090a03200910090507030911010c05011401030501021309 63
    0x10500b01c410910792920407030982c1c60303030409540c0e515403007035980b01c041d4029840780c44202c5012006000008006416200369188408981207130452a555510b0703003920350918900c010013004080040042480c400008910124070540941216500319200070346807030200c2d0300c040d0703410f40100002d00401c401c04034070a90300c41c04030310b02603207450a4030044005410043c40860380d05038140340c00020780b440080c0b694002c8141e41c1303412400e6603c60301050b4984083c3d2616007101041c003010085124443c8040300081845a02500c038240c1d101c00301d50b51032404c1045900380d194005000030309102646180724100c04800e420003031400c40f920021a059010601c07014001324090680400096454582c0482e8480020614003452401d210301c10404d842500031048400e203428001014940248a0030100d1500040a5a0150441c40c01141d010100d514101d07a203540741c4c0b01c880203140c5c5818003580694400c00003d40c0b582d026903c1d543c5d0002c1c596005480c040d061080718000001010492 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 593623929 1250 593622679 593622707
    0x1a0907060f0c0b07050a0f0e0901060e130507021b04060f0506030c0706020408010c1d03070e060d0803040605040b100f03030309030e03030318010501080d050f21190b060a 75
    0x3640c8078031a118050b2064480d0340405803059140c24200841d803a807080c01041122510b0300c3c1c2107402c1c041c0d1041200d8001081074402d4001c2d0642005000e42c0f8000d80c8080241c000c000d06901880c089032086d8002d68a056440002590084a410350607800320b00705040c1086080e2010002203142100341d80e503d120310311505015800000104240b080d000040719101c41d0070103001d55403259035004460007816969880400034101c1e03620b04d040a0001c1c004486c1c01e5a0050040c10810300300610284001c6001e0811984500b60b2110030700044e03205800b8500c22130003000001090f2030642010040c0b81030040115890f0007054005110606803100554107881d0507140000c2c2c100b4181c9810b40c0c002d50b02c0c4d510981e1505c00481041424004109100c030441c08003802485141da07030f03511056660164009400118100740040e80c20341541c0c0015010034000302072800c0701c000361003141c1d8000320b03015a07403484035400a8103400340244290149026907181030720f5982c40c1a441d5100140003101003040f03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 593625179 1250 593623929 593623937
    0x100c080306060d09050f0a05060f090d030e19030e0f030d020d0f09051507150b0105040501050d0b040c0c0b060a060e01050313021309050c030c0f090a0906090804031a090706 76
    0xa064100c921130b0f0040642c990b01c2012244404641400350344d82d00480c0404a4451148400150b02401e40c03a045d507000d020031100900003900c21140580240002140023400c502c07c241d1032541d01201040c684041c14000d0f2100401200041d09000c00ca40748a2002070081e0321400c003400c143c55002a0880c150200340c039202041000403071085401c9035840e88041d900c0481e95000da01c2c0b800040c00105500c82c860301c495401a000810201c05440403103400c140418020b000c03c103c5540910b0040000801c0000e0004846c14100c000404542c80c0d480044000303200b1892a42c03c024070005815004a01150fa8001c030b1403414500602c0440d1881030141044408000725032800000c1c0c04a543c0c680d80104001141051041c1c1000140040d0205036511b10920141c01858100440c00c2510381c81c0190610003a150403074103012048030080d000904140e80c0b1003042020558910401c0d0040b0310030641142e0761469410007501c1462003101c0007404910300000c3c070400b10700008540d4125441810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 593626429 1250 593625179 593625187
    0x90109060f0e090103080a0f03060503120901120501080303040309080703080d110c060f061e09070311131206050106170402210f0d0807080702060420060d0506100c08030606 76
    0x41c1122280d01100615070055001c0001004000c2c0500291003c481d05070355401d28111240d01c1201968901e2003541c1e05508955891102044150014a89010181418a0b030781941e01840403c0f243c1c260302140a030381000c801c0c00101030340000072100510b08640200011400e5845483e03040c03069000c85112290703501600707550580c24030283e070f0f224083d0f4000d4440ba03140c121200c0c06001e0b022244144030725105a071000208000410b403060f1540058a441c80d1640d0350701d015401890000c4c00840303080030a01014058800610550010700070000e4034655665440c54100b00ba11410703005801070281091007002050640700c45240e10039011160341003481e41541146003410f41c030b45069001400340c6039100b1710300500020f03100c1100343c01d551540320650f01ca6078129009201aa00080141c000310041404078000741a40100c00e41e003110740c115441800400106564000100440015110000c01010b4a0300e484024110f00144c02c01c280a03002d940c2ea241d03228480200001d10a4002103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 593627679 1250 593626429 593626457
    0xf050d03170402011b030921151107140d021e1009080906040e06100302070b0705210a09110301060522150e04120c020603040605060d02211209010906 66
    0x16140e00c900203601c9900b0385a88031b0400801019242c010180b00107440b80001e0814000030840c0746800d078000b0382500c40d8201e103552250261201d9607800420300340a1001c00c011071100c0c211494642c00e140700801045c848420081d040140c021306e00c9020388168012450700010101e03000500580c45078000400c24030500d4100b8060041650342508404081004642000f034002c04a0103075004540c103000c01c0c40805001c40a80c8191440104544205008290ba8030301480c00781c908240140394640e110056484901802c100c1241d01180c9251510f90302003d01203500e08200b4003800c281c0c000d200c0141414041f50406a2150004504500c401c1c2140f0350007082d80e00c101ca541282e001e001c100160790300d00c249864001650140c58030800c1c0c030006004d180c0a052103015156020b0a5a03056582d20303141c800c010030006100c56008210f201180e401640c584c903c50001040e401404400c24403110011450542c8890f041c0100c0700040007449026071300140360740100c486610341090281044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 593628929 1250 593627679 593627687
    0xb0601020a12020c0a17030f03040c0b030a020702120c030706050a020c0a1205060f040b0a02090d120504080d0203030c2a010c0e01030b1c020f0d1b0f050d0317040201 73
    0x1904020344a0014030340811403443d40802c40080707102040f07519455035511032801c80b01403800d42043c1c0c15141d0042010300e417002ca01a01960f4001c0c007645081407505c0d0788407541d60b41d03580100c500383c03546540080c0075001c624001d9109902d01d03040f20003c107428081c601c003080c0d41c0d0700c4900840341400408500c0c42c860610030004030791085030140448114a41d50241e03410310341140001280c00d80622800038104a942c103042912894102030004081e0f15405084402580480000d6070440c181c1d0f03907100082510051004424640d5543d0140e61300d01d4940468203106141c900303003045410030800e1000d82d60362241502c214076521461401c00404101d0068000250030303075064890750902020040b02d540001c210040c5000a0300d007031050200090030029a20701060000a20a43d2000d85101600b4000003401c000040130b022a5200c51450703c681c2c4d8400c400c00004500092002010f01c00d18020503500c00c000c00080e5901d160380e1040303650103072040c074403610040c0720700c65050006020341e841 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 593630179 1250 593628929 593628943
    0xf120c090b040f1a28030f0201110327040204061413050910030606060509010f1d04090c150804020612130206120a0e030405030c041806050c03090610120b060102 71
    0x41c00c04104003000314220b003400c196a00060083c4075500041000845d00640318210106a1184940410150455866110b40c200013107040e410170a03002142030841008200810181c1181220940c241d03100304c00b0041c014002c140c005011710b0041c0010040e450b00000c502c00780003401e24005484400380e425070041c0009907440580d01030610401d1001c2749416000c1c0c0400c1d00e0281d03c0038004191912400d581902c201240e130750001e403240c0929041c00e8410841d0803032100c1c10070620444607001c2d000040c1a1107010000352005078014404000220780030401c44925181070070003200c51301d090b0300059850b00170700d1504010140804c000035040648004245038207a0300409950311201011884a50300a049030500002c40c51302840081000303001064404a41c07000b0b0003800c10050360820b03c0302418010031005003000000d21481c000500c030740a46131098146880968484c6820041e00b450300c000500429507107041c0010a11030400c95030b1140000c0f0b41c1120005280340c8400004034a0505 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 593631429 1250 593630179 593630201
    0xc0e0d26040b0a020105160806060703180f0905090706090b13051504290301091109120f071e0605031f0609060f090806060409050703050a08040f120c090b04 69
    0x10018002c100741c1d2019025140c0e40307203103500070001665102210340b80b500c4441c003110046155074001616620b855401804c03170600c2031800c0035502200f09d108880300d41158105440c403038030400e0180102000c600c41e450740080e1030401070400d1b900e0a0300140c0f0f6000c0b00c0c090700e500ba400000700e00c405c0010308076104000f85030143c5900054018428100c40d140c105004092000c02c8c84c0da1030b1444241c0d901407c0d403020b000c0c0625149164a8200031000500407200d03600d031304810600c842600e5540300c810b021805c540000103040c05000d04101c0c0b5080648035000591003190260480c1c052001800c00ba50a4400c03609000d581e079142e400140c20341034035100442c01100740c10344020650701c2e030084580040307401680381c80f101d00c1d4100205882100c03940c080c206146c1d00c2103001400ca46026004080c116000d9010b40c1c03031558903915202d00344840f071001958103440008041101110b0f0050040050214003004210000141e07586100000b0900c5000307507207034441350000c60715138445e4450ba01080c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 593632679 1250 593631429 593631503
    0x4230d0c0605010801290d1a0103170301140405060a260f030f030a1508030a0e03100c0e010c170d0b04270f06060b1b010c0e0d 56
    0x4504418010040240d844040300e00a042c800006400b40301405074002c6070303640d030600d0303141819034080003140810181e240a0b80718007202284008160702c0150503c852200c411441d400d50304600301040c540e03000c2c414213401600304100400c801010004038000e00c441c1240c1c085034a884d072000142007a00980c2140e9081c0400201d80b20090000c40300d41058035801c582500c400550000525882c0d025003a10240c0e00e400400014840c0221540118101b503450a15002d01c1602c44908130700c1c0d50030110455001c01d081510808082c6401c0090020b0030084600500010b410700400501c00c4030a54865414404500c0240e020807410489003840f000084600607101c0700144050809030015455040c0110703d00480c007c88403d06004440c0c0c059400303002065401d10503500d41407044d0f51000300b990580e5030f40718040790b0400404010440000015092201503080007541803c581e400e0100e40d080c808400014030140d201c20550700d54080c0c0004458402244001c050803090901c04001d001e08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 593633929 1250 593632679 593632693
    0x61409100605071506230916090b0904020408121209121803011b0e090a050103020a050d030314010e0610022e060b040602060711060717091e250e0423 66
    0x140070800c0070908840c007200c1004882d115035101c040600c0c9400079074400274180d00320600c0440554401088804c0d409800145440d0f5184030207814000d40801c0c60050705000140780ca009004400e46a8025045102400141039008401070961182c1e840c403085030410b850046460313035420741c403480d04003400105542c6d10f0345045c00c009004820318050f480c454240000070403442802403003040c0c144c0f54007414000190b4103110400159a48140c0110308040c0c4400c0c207812042c01002a0b94001c00c030070041030a003801c180080000d03200c5028152021544100d04030040c119500003401e510350510040243c4020001c0e00d40d40141003c0c0e04080c800312800500000c3c85940081c14522495840e48c810707011492010459443e004180c41640026204003070740302440485d44c1140381c1069444003140c5040846047c0041e40340389040c007200700c0f508515502c141c1001c0c1d44090b0880011110811083c29003003101c09421400064005003921103001758004199264400c030305450381d01c000071071f600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 593635179 1250 593633929 593633969
    0x60f150902030106020d23070f0f05031b0a0b0714041d0a0c1d04050c19030b010818060f040203160e0610030b091503010f061409100605071506 63
    0x42e610038807903e00107100d81454094624462031080c90290507652040e10740b4a02050f48030700d19080b100003925000c5000c041800094001d4000903a01442500070b5503c0d43d4440c200350701c041c00300c0220303500e564010300c80340c100051115103c2036114030a410040c0c280d0100b408060801d02994000490300d079170321814030181d54004840f0610444100000b800401c0e220324044a44d8540040c02c2822880c103182503444038640364100c1039118030701051403821720031501c2403608401003038001c110109a4fe42e04060465901003450b550012403030a20340141d201c070207035299407a800200206440d001c44030204086540501c1190f00b9002a2400c0801c581e444105c208040082500c145100e000510800003c06000c1c1c02442001c0070300034030300d0b141036449034001055104803103c82685951f07035500400f0103031030a1045001511032003a540200302200c00078000001405841204022600c1c28200b2100303601c64111040c0350303070003003503800110300c040629405404c10307030000c180e40c400000034802 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 593636429 1250 593635179 593635181
    0x1b0518070e1801050906010c02010206070e0f10080906010b030115080c09030a2a0f090c030603150b010e0603010e0c0703050403050616020d0807092904060305010f0b16060f1509 78
    0x3040e1907084175186807a860702001510b0a800d06c24000307016800c002d0000f8150340c00b542c01c000e980040500680f11040c40c2000190241060014000118004030705001f80c0e80301c1084464054014428103030301c0d550401c80c15150008000d0071003010452014005400e84811000390381034418041c08031800305010346800c1603603000d1400100b500a43c5a12b00d84d0824010b032035042c08681c0315140c1561102d0815010202410800074000245615220000700140300c40130284400140802d00048404003100014040742001655a218460502c01131294200c002c0c400f42d0810040d15413240c3d140d00c0c2c0c4c581a6103038040e1b40c0c03024020f40103010401c46002d2a203100981c41301030700d13821780b0540c0b8003420040e01d06c50020f0f617100300040e00421050100c0203070180000c041081842807180c5601e0100b0030503407150b0068201c40c0020751070300010480600359909103009401a42e108506101001c07200c060224020b4402030903041e100c4c0b51210720b454290b403220035480f107074400b10081c20340c4990001d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 593637679 1250 593636429 593636431
    0x51311030c04170a03050301060e030c030f0105100501050712181205010501060f020a0b1812030112060e0d0206062707020615010908030412051501121b0518070e18 72
    0x3c810203c040c007007036560701000c542d84400d1641611210306503400d00300104c0d5900c5400300d01030340502c118000c1d02490381d020030880701c01d03080c204008195440c007050660702c50345032640081e050010501442c0002640114041da02c10f0241c40c003141810036100780a150b0826a61028442014940c04202841010740005050b10015150465088002e00c01241e40d0801c402e8040d11014032480032a6049600c90b02c0e116210500c4800c45142c55a41d0003100b6032940280e2203140d084480600740403c00045018504170001201c001d0480c4050b513002c042e480b60002042c3c180300760580c0c40c0607070490581c800d072980203441c400701000c960301d81420065601c1d803060301c80f01c442d0043c1300034205403503210302c90140175555248080c50031310b440d010080300e01001990045130180541003104110100010840703000700b000100004005803181001404125007005020b0192030400d01805652103148020318100314082c055003031959411011110340d00040750282d40410110f5403203056903c458421 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 593638929 1250 593637679 593637689
    0xe010305011205030712050903030408011a010f0215190c0c0308240105030a021b061008011a100207210b060a030201080c130e04060204080d02070807051311030c04 72
    0x420a990701e44440c07850410b0030b008018003e1340204020b200090034580407038000952400c151341455900e000080c00d54106030400c1c21a070790743c2c3c041300120804511514050480030300340502600d00c03c603030083d143c04802c880740d032244041d80003240303500010306010111115440702c00c00426400d40b0000b0105101110207400040c124408034401d07080d0141c00780c4840910300180442e400ca26001507442c2e0308001c041000d09a07007072000079400110b10031004580300c10310000d0b214038601000031b14a000d01a800c03606041c1e01d40800e1001060704040b684251200c2116212000c22240300220b141c112aa0003085005117143d42c485400a908078541c0c2c3c3c00751040e61900c0d0143e81d034109000a4601d00e2101030300050304a004107400300042001484c086184ea41c106031040d80310f100070302154500360b50846000758000703010070a080e0244408280b0b60028805440f000d45002d421030b503900380ca03005862007405814030b802100105030348a031b441c0c1d40c0c0081d415500c0389001e460a07407983e0850b11803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 593640179 1250 593638929 593638931
    0x1a09031501170c01020c19030b010b190206061c0f170406030614030304030204110c0615040c08091519060b0d06050108100b0a110604060b01030c1110020a0507120e0103 74
    0xa01d5441c80c008140d400d80f5900c183e00500107900c06104001a11080002d80c0e00101414040400860042800c250203800f45024060b518402c4208920220041902003421904003101b4080b01e996031714666600443d0a1381603000c41d1006060544070381048070030040010401404a41002114001070030465986450400c546560b44a103142d403000d8508045a0541080205000614142d800508014514003d8134108a4000545441d00400392017090b40282860038400d42450680500074610039a440c0080460801180041d6560328807604003a1001005e00000c0050f00043c500785c140d845004404c0c072030655035090b6840168008440003500500b00302011038654000c07200903000d814010704c204100f515022800d95950841c01c0050704000d8a0f11000e04030600401c800d501407401303000c0000341d015035003001608442040300342034180070640c120180c0c100700106140d80c8507003243e0300159440c42e08070300c104c5252240b42802841880c142000ca0282136000140e220440400e80f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 593641429 1250 593640179 593640209
    0x1e060b100c0b06180118110a051201090b130b0105250c090c050304171c0b090f2e030f030507060b03060402060715060f090c0221041a09031501 63
    0x42032102009000000400340304c441c500401c809100d03102d0790125a40265800900c5000c000108026039104c582c4210001da80420610100c1c18941400780c0107010044081103c4001c650110305400c401d8644052410340e620720355010f5074001d10840d5840c1c034250f1440000c01090240c008200515079500361404c0e40b82c0000403c088081d4815048000c616840b0b076402c559a507079510054a01c151820002d030102400b000200062007030001c2101080260040750360700c40d40050140740d4000820080080400e0814070000110750000080c42c084280c0e182c1740b03d40a165901c002d4800254801815000380d803090b4010300d6440703009051400d00c200c03020300083e1501010103a503110305840280d80601c1c100b2140c40055900044000ca411440201040b40f40d0b03620044003c1032159403090014545814844e0360341d43d414800a501007141c0748130310136485042c1988500c1d81c01076005246040714204007686814200f1780a454400400904480341426130b800c00101c000b40c28440c11600c07182081d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 593642679 1250 593641429 593641441
    0x111c0509010b010e06030c0d14010303020f0706231608071b030302060c031504053d05090414030a020106031109192408070302030c010c1e060b100c0b 66
    0x8041c0310742010050b540c030164180c020b0204072170b592018203007184101d400c0000010001c4540904650445a400e0090075903145040103400c01d410704100c0c030201c1c2c2200105200e41500400030005411150540103114440e5440a540d60b2058840c0c0007840e041d0200340c901001080f00040000314072132140020480010f20030785281140318007000300980c101900150415101c0c00286030700555946001e0225003441000c076003114000c0c0c6a1b104128040702c01000b040c64084880c865000400c1810410314506150700d40130030015028641c4940321000102d414400c400802500c00340c11041501d503900490344010340207007520310040f508175a075140300b142d20383340180a451003031f01075801c078400e000107003a940c80c001d0401c01034001c20030a8080200d040303024a244000301504100008122180c00c50040501d0324844a40740b81c100a8415445000664242c49003410158803a04940d81d42035285403100140240204c1950460302449154492550140c54612924020072603000980c030340d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 593643929 1250 593642679 593642681
    0x204050618120f032704150f06050c031e0f040f23011b0633050f011704060209090406140105060322052b0201110406080c0d111c050901 60
    0x292410482d001070000b8483d5000c00125410720440c1035050301745034005000010101c03500303500d101c148418224070070f1281d113807c0e40c008806000c40e41084c13400c18100c0c0c20110b03583d100c1c044921321080c201448020a010042d42940c04001004101c21307216500e6181321084842140310703000c9070100352400b0881e0701e61070121940909606a480401e89e07000907420480d16645082d0841e500c03507850303d00250000742c0500c1d002d141403a41d020415440b8104020164803401c90704581d10598103010840300907a0000c40411143c0c0d08240551400d54a50501000034000e00d003140380c003c19038904201c100500d035030040380056005014a2000c0e41c03200c003889401c2c00210380d5042c01d0b1844100c800f040d120940540032449210703400302c1d146031881010850f2042c1d61144080c0114480c505106030030740e02801070070000c84010b0312150400c3d02d0024005d01c40c0030081c103500781c4244d00094030a035003145900700c1c00408003e50b040da0758035180ca29070b080c4040300440b07240580c2c070302d0900440c0f0b80d0141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 593645179 1250 593643929 593643943
    0x319211b050c120c031215031c0203040b0304080a020d0c080f0c0a02060c06090d0f0c060f241d090c0906031507031a0d0309090f020405061812 63
    0x2125424854030360280c500741e80980c0811440307001407292010344000c40c869440184821281d54001c0c6031601460102c0d002d4041021700030f015280c400c0d0507054580d071000210581c030030220f041c2c08080340427040020b031704510513600b081110b24400810841071020880c0140302c615070960031030300c41c5014140202d40850f0405402400400100320140c11200404080c000e1088844242c03078000c60164009002540070424001035900000c0130090400c43c18450702c0d034208000e0800b0304841c04034250040c104e00414030020302d4141d441c00490003054841e0301845482c001b4a40104500140000800ba4200c040c07090b0604140c00c000741c807001000161400380504a40d00043c5258110001040341040700189103580621550740d83c6c603084044c05d00c07a90300410498900155100e100050410071811800c6502d0142850b4105640040d0340714220904075400c8280001e014809105120041c5c4034039131120364031080c081403402c07031084000418800041c0844400745078103101c40119480d001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 593646429 1250 593645179 593645201
    0x71d070c060222140319031b110d031106010602070f030206030c1201030803060a120201120e120a110601141c061509020306011202131205031921 64
    0x100c240c808000041d200d030080c051560104200b800c03042403100006003400c00380e80c850050b2a01001d80404242001e11400884013429810101d00b803072591006002006140d40c40ea4204826a80000c2032040300140880300e080000d084969410450800070301200440c401c01480d07009080001659500000e42601141c200b4000c12460314915000c0090f20b40001f011411001d800304121000203110300c507030398040c6108402568407070030498148846000d03030750060b142c2030a0803100320780940e8116080050881141c0340218a112400710310034207003014070b14164060f000c0403076041c1c210340d08110b6210b01b02c0c58190488100e0303a0b803400c560810f13000040b60303030350004503040d192001040845119844140940302c0400d102025001c4038403004040d034403d182160313011050102075a40445030300f000006111083d428000200050310025016204583c0b420b002d01c1148000c0081c24016210315040b400c0b42c90342c031402d076140040c00e0201448452003204603005420901c290483c405d0481c560 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 593647679 1250 593646429 593646437
    0x130e010c091403210412031d012f0c040c05090102010b06070b07080a0612060212100e070c0f020909010603031e02030313030e03060c090a050405040206071e060905071d07 75
    0x361002d10780b10144002000c0303601c440042040081240c20b4000300d240300891180c3d603501d1045134096030301c5084c2e0242c0303c408d5042100301c0004281e11105c1c42810b031000065540503e0290304c111045504d880038882d44035070014105990921440e0b0044098640f800007a0020f10240342014100400c0b441403000c01000f14110070041940140f01c5c80f03e4550000c000500018403c0d1103415001c0c1c44002c04908646003600010300c0c1034a182c040f5001600038030080012101c0a0030088400d01d40e810051020040040f1a00d4210070f00c1540c0e80082240b07134018107000410708040364040d02919030350000b58041074001032036901c07005601030003624103101503024606640341c100c044100401c3c026416001c104041c007140f1001c0c0d500b80222030044500215050b80d800040e420711042440d107a10a0703200b5817401c030400005d42c0301c03541103410441d441030540d1003981928100c040500102107025100e9460303d0702c20400c0100020715001501c001c0754000760a2182c03003160141c8032008072000780000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 593648929 1250 593647679 593647693
    0xd05041508091513140d030e0d0c02090c21040521180105040801290307060203120601091206020408060c180f01021f0f0c02010204061d130e010c091403 67
    0xc001e461001580200c481c0e1010603031a0525211442641c1a03040c100483e40c01820001b200305d601403080e0b08504504070060700ca05c6c4031102d0302825200503104041d0082c1010000141c0d8803540300301725001d84000b225490f40b10301140c010b500c50000c0880d400c94061080300043d00410610090309aa85440d0a0306907240403030a40d65a00480408112541400000d000214000c0401c0c040c0307200d000310f118004047d400104d01600d03124400005d4a40c0243c21500e0140b103425030100071550200c081518642050b00c44d40c00480700d2900b264441c01030007070301c1840d00d01000400c0c0c005204581c2c0110841e091034554080244c03061060000d00c00901d101a60142d140c0d0800c1c82c2c48652222050040d505e140141009440411102a008039443e0b44e6618003c60702d1115480303007a0000034103200031400c003424071002070281c0c00c08080c2c0b081c945032103074400179540d034505050180ea81e00009050201c0141c2003001400380411801100104900507004524400084002643c1090050017066a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 593650179 1250 593648929 593648953
    0x3020603011a091c030f0e0a0e1005100801080606011805040e010b031c17010f12061506050306091509070309080714071e0f05010e0d02030d0504150809 67
    0xba8520072a00307040b40c0428000081e031070744ca21300740140c40581000c0020110303a05240c0101300130800e9800b0800d02c112040c1082e090f07100c012180c015184c070300ca8000c0481d21141d00414810700607500c20703640664807104c6000b80c0340e802515503040300c1c0e0142c00c6400c5600c4074070041d100803144459154000800c0300b420030940ca084c2c0c00030200308800000000302c502c4850040f0b418950008505102c454441e4001342e0340a03842200311801540c4184041030a504201000c5038810580c442da4100c15900c0c94024140712996101e465070842100404a95a65035400a42507410403150a80306440600001c3d40c2c50040c10514241c41000404401150b139503840281e006213583c400036209072509101110000398034904000612081c10000c0582da441c110907101941c0c201203502d481d4441d004001c00c0488004204c0c0b2041d1034090034030440b00b8030b180703012500300310415802940c07510942810b401c2c0180c22400410030381d0742e4a500d0b00b65442c040341c01070303a42c810141c40900343c540c403a400903a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 593651429 1250 593650179 593650199
    0x21207030228020d050d110102093601030b070e0f090c030c0702061c0b10141e22120203060a0b12030301060f1b052a060d1b02070302060301 62
    0x2c01c04070400d0205030100d0303150007144107001d107013408460550225000c041c2807034020709046103c94220000750b25004007180400d044042541101c5e9241410315440d840425840c0d0280d08121720307102c610800d039070392410140003299040c1d502001207482110700c0e00e45800d110700251407440c00a0a0034050307031602908040d05500051096120350014810100182d0702d5070000d00c910b006654144c9040c0041c1e25654085610030b2005900c1800f0315490000826040b6000c00c0c0010700961055403681210255074454105100d016070f03650b100040e002c050364132003800749100e080030b904c5807002c3c0c8d54840e050010303261900300c8081e40c5940540c0000e0360700000754000810030b44001d0800c05510440d02c0da010701c0c60308203810036404910f030141d42d0180c07143c0c05040003480401032110600c0b07065040c0c840b941c484021071100f100461220840fa07154404403504140b4207400034180d582e4030b0040301c0444005104c41b6800f07000f8082c1511b0104c6149100095000503281c000742014a140d19141e44a9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 593652679 1250 593651429 593651473
    0xc211a09030f18181603050601020c0406032405280f060807031b03030507080901170c0a27050d060b18010e0a060b0a030b030109120f0212070302 64
    0x8a948010001c050b680c60006001d80340021510a00d540001128000c00040305046800c0081c401d00d418100701c60322040074001e4816007400d0400040c00e4640100403402c1017003804c407071a0407a003000c40c000104001c0d2270592000c0e01d0320240f801c01c10b449407251007003510825100c010300c4014144801917030440d4180044058241f4600c0001c240400300d800e4000c0d192558440000c68001020400603c0441c0c0e01602e003030056640d042c40101d0440d80c024203240100000070301818000300c0c5071180750f40640c0c08106494608450907002c0d01e0000030010555009010349000260b03800c4082c01a00740f2a0600030001400d00560081c45041100380424070340352110035282243c07a56804001600d81d22040d8222640340b081c007045035810103807079106080f00640b034040344520b0510100510ba83e2142540c401d80d100f1725010450502820010b40544482c010140c103001d15078581100441d00560016940810740c0c00f44c51481000030480c140a02415802401582000070700c10420180d4030001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 593653929 1250 593652679 593652691
    0xb01021f0b06071b0608131a04020409020924010201020405030d08072115060e012c090109020c0607020f0c0103050703020409022205030c0d0206090105160c211a 71
    0xb0b14100030464451410145022000c140703901404081406460f50200c06560300062494000d600d003d1141e962007000381c0b80d41c80b4240a030480101040440d900ca8100c190b8542c0c000f4040b54450604403180e444080070240402c00000030b9070900f1160354010b000350f0f030494034001c002d824a80b91340c6105540150005008808020320300080c101040d51400b81c884241170101e070009001c107003d5820119140013604247d061100e450641d8940e681e2010459900a0304c012151000c16591078110462803070700400158045140b4002091044d0158007901000d03200f0000c49030b143d101c1a5040c2c1e103071840e0305105491900440a85000e0794026000340350485094170300145050b0b0b54114031030407600701074403850b50300186100f804c403103040a903c0b4901510003180075061507411540000d03040341048070003c0c050080460f00e510356030300032815140b61510341130344400c04030306510b44801c100c10340e4000c584500d1030300c07103480340201d24071094024616408020110406942e40d0610300c805002445 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 593655179 1250 593653929 593653939
    0xa0c0201110d0e0709050c0a0c050c03010e0a0605060603010803070609030909180312050601050a1b050618120702010c080711060f040f150e12150c0c010b01021f0b 72
    0x99441c030384a111000b80504030a6010008041a0a1454604002099000c0d225035800c290a2000700921a0100c809926040c105110380d00c2c0540f400c0c40c200f022801a86500d035203052000c285c01000441c525203018820700c1c08201950314041003001b28082801000d400b507005020342d900042c4075a00045045001c1d050000e02c4998803aa41c1b01a5481d02c10341112031800c2c0c060781d908060f00254021213400654074140941c1c5050000245540659920a810000d2010140e0000d082d41c22036451403540000aa40d11460421071013004c440b46c09056020500c0b03280031100d0400f01800540326030b654165581403a02c101502e408056411421094550b107244151814043c0c0c0c0b000c1c028541ca048203401c0980b5103252442240518071a0740c0500310107201c04850412031640000b160007800300072248526510115220b251074090749512900c5c900d5203443c00d0003c0e1408060140c152840c400000f072004034803040c01240c590030740d021140c5aa4181103103658140b010350b007155506c142c020780 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 593656429 1250 593655179 593655191
    0x50607031e051204030c290601120e01111312120302071a090c040c1403040f150905010b0f0418111212040e060a031502030604020403060c0914010c0b0a0c0201 70
    0x91401071a00113460803404a025070f10010100010500e419503803c2c5101c0304402c0342201d030001c0e0888000c0040000d41003080801100368102d4030765010340c0e400c2c050310008000f200300e1501c2c1580c283e0300148000b14880c40e01480000e066540305c00c04184079600819030f41e075894109009601a42000e1003c035110701000d10403c160100300d0409a100d0310109008101c10701c013100c140011281007001c0348003005210000131410030401e2040300c4d085613015000e0617035030300d00b42004d00707608483d02400904181044003000c1801415006100009421210702c1100d5600c8010001110303130f110207000c0c15120000348100801c484020041c0c0c01d42d0041d01403905814071210603810401101d07464180c283d00814103122400e03000d0f0055910100582e511038495045440b10700d20846042e10142c45640c002000840300d8039150151001181d04c0300c4244452155480301400082250203001241c102079500103005610070800300206a40043c00c40d20701e80c40e005d00701c1016140320311412040d507488907 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 593657679 1250 593656429 593656447
    0x51c030207060c0822030c080d0914031519050a020306130906020c0304060504030506010f050603040809010926010509012c0307020a150e0409080909040203150c090307050607031e05 80
    0x814175188120b0f5980c03041443c03d00b54980004881d84682042c1c0443c0c0c050001c030f402141e0030951810030b903683c10988550b0203175654006481d081e0310754a841d8207061000148440c410208090310342030148144280400c1c0e454070400012808216009030340310619500b51596801e540c2e00944009002d8100540780107401440a45160310036400100001c0b000101001444018803c1901400946c40ca0074070352403a10b0300048690101030009080c1c1440040c9003446a801506048010711800451000d05580b103802605c2d0240030070450300c000d50820300001c02151061050031800884004000b000407511411016040354000c1e400341e0512003080b5420141e6203070030301200100700401d0010402c0c0300c0c600b80200705124001465004a04010351380d00003c180d00196414501c041e07030024110b0342c580c0002882d0501301290010071440300b40070700c14072294010081928600a44c11145582d90b02c1050100c14410498003034002506400c040c01c1c110511640e206043c00c0038580303182092109 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 593658929 1250 593657679 593657707
    0x150a06080403020f06150f060901081b0c0a060209010809010509061f0509010305010c1403010b0405151c05220206121f06020309010807080411062101080106051c030207060c08 77
    0x90761b111a40000300400c204e024a03160950b400208400d0b50005d00700716111001801d03001002d051100c1c0d0501500d644004c083c0c20f5003d941d030442d241400c4400e41c0c000307802d0810095004044980c0041c0c48980021108881409a140518601c0b0001c1c43e1035555100c10b00c0758125404844a51460781c034400107455960084000d010b10300880c00010441a12080030f00440d501d0100051130304028801080000c4161041d6001c488003520343c00d2100361038200e962014811101b4505129504c070100c8048140c0d1684980d204100031070303240075561100d4414005103209900300130f50003c401c0080700008c99080400980141c103203007114102c0c1c10361200c40481d400305504114010b034004a01d0000c95a0701030200c0d504510141400c0c0c0c3d65040030303241c2c0054980b41c0704266018010010701e05240c0349802d5690480e2000d052101d824551b15481200d010703280314481c040c4103242c0404c3c00c4d40c112a0f0607000101841d03158000b01001403808006607401c40314420300341e500040a0081030328507105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 593660179 1250 593658929 593658931
    0x120d06050405100906170d030c0c0b150307210f030c021f0e091504050702070f08100506100503221208061509100e060403060204150206150a06080403020f06 69
    0x40e24a04101c284c00d181480040350b40c541d004151100302d11140745000c2c0804140704c1c03490403062402150806c46110b007500c1900c500c7c034005243c250031104102d40800f0180006101c42c1084050380d801c0e40c0c7e40c10700c0d012000c080d01420101c03c3c1c6411050070002c0c90324003025641e1131182c200014400d00b59000030b400c0f0f214075510780b00500c440c52000b46245903c400200b4049404840315203d500740354481d4485036079103102e03142c00f035a0f451011910b402c1c02000100d00a1000c680a1690582c07200d100544400c174000c55006c3c4181040041881403070101800d19030b40d403143e960607040d41e540c0346442108101548066410130240103002c0042040491015103410294440303d845061805c00d10140301c80c50312070780004007024011107801e99514180312040752100d10780180c1c040751070340000d030300d6104550000b008240700190004407901c04205414401040340c00362039940c1c0e100c1e8042c505d0458600c04066100358014403e20407140501400e54005000c0d1041740c0b40f507a81100360038030b4000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 593661429 1250 593660179 593660191
    0x20f0901030f0b0f100506070302010b090711070503010501030b2a030c09010810050303030c09031f0929070507030513030615080109080d11070501020703081b030702120d06050405 79
    0x10040e4100d0b8140302c40d401c0019040510444684840d26105030a0314030305001d130090601c6440c1c0040c2007000d0602c00d40080804080080c010310307150801d1240a4074006003003d031301c0360600544900007143d25061240c117040703903000482181d030f0b90340306540400508c0e01c200c1c0072002952080b20600012400c403000c1d40c0725138001e0494070380c0c84c401100094031440004104901151402c282403003d6140401030301d40115402d002540c550101d400000e0400220a007800d0408120070404501102181c01003108103000b00c09000d02c00c1100c040ca0b0a00c046064081c841c10030400000c2131169119a0081c624640a890a47d003000d82240e92204034403c268015144ca07501e540c070340c803248a170f1043c0001c024140d88000700113a00345660b4814083c0510a54a40790741d075030348280c050b458107100071104160303444402103645902038035019080b04015030300010000314050740100c0100f00f8004680c00b44105400a29a145a09442d43c0031035012103a00c0c6041e641315400000c45403107500505008031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 593662679 1250 593661429 593661443
    0x301030f140606010c1b0503060a061e0f060503220c0918110d14070308030708130209060d03050c1603050c180f04050109120f030c110309040504020f090103 69
    0x15018205080310506108180324a034002ca000d01032943c0c0c120012410b419805101c2c60320340c191054804100c8901030f401140c0500402080004208240e8020020b45400064588600c5610b03442d4803a0111180902c4440803c90b10080c400b075400745010303550209921500580c000e2117800304030a00105801c080b40c140740c4860003800100e1650080f03440541c50706051058984140c1c9034140101e150900742400340064210a1050145011f40c40708a1000d41003180c0180d550703031415411a500440b4900001103026010803a0440d8803c0d03034044582c0c00410b8a401c0d91103030010401c0218000408078207120081201d90010a4144659603034004812106003000749941001d9050000c0030041601c02d450b101c0d49a54071001b1051007a4100b2032040c8940160f03912403908078010100094050645158000c0c9000344542c001051280c0d000e069405000c040149441940c1012041c4c0e403485d0075420900200001d41010b50040358807a00040090b030f420007070000401e0221500307810a891103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 593663929 1250 593662679 593662703
    0xd0303020d062112020c0f04020c0114041a01050d0c38040801060504060302090f07020c2e171810052a07020d030305090309041b030e03091e0102030d02030103 70
    0xf0150144c00e5400e0001d49001501034041400300244201c140d030101d80744030380d5000c120140c40c03004c254802e41031640c0c9044642e80505050600641111708810410042e04810002080707a050041400700c0f0664082800042c86041c002c590012460015100154403c0040122071000c250480107090130100c9031510390340c5003803c03401400c6d6100da41200b80514102081040140c0341c48039415840740c2a91010912625814412814241c0079031009500c219450f20704509240c0b0841c44624810344081c41c105034189030030003602c0980184c51031620030f50b50000041c801fa8155114000269020016600d0702c2c0c0916420307000b22841035901642584c081580b0100e12000146c40f40c10b0204850012400d1003041d13070001c1d0a008040000a08064035400440c0504904100303070784000034010030601c003c100030f1080e0310f152603640c0704200c0040d04100313400716140c101100300da4a5550160540c9001c03904c005c2003450f45000e03903824078118841004003801c46021480130750702951090381780c50b800d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 593665179 1250 593663929 593663933
    0x7031503120f0c0215030405030f0d140a05060102061605130e01090b1f0c08040305011802030d05041412031b0f010b0103050f041b050612040b0106020604020d0303020d0621 76
    0xa240c0320100c01c2060190000d90240982d5400f0b458030030040008445d55540d948500d0078600b180125046061a22000306190480c200740d90490322881040e034510141550b1002c00c80401e542081d0b0301140580c0108010850b071480d40314400c8011001414042d103400419034040e42c42d0b040e02c0d4003141e161150100140a1040d40e07000c1c02c1100402102c2c4840c0001c950045452440400608201440b0318520700c6000c0201010942c3c00458003e0002c210000c034070215005180c1c90484103e1183c001c0200102c11640100e05540c1602ca01c101580c2407488803100b8403100e0142d411190900e8407061261680d0000d00100005107040004042c1500e0859014810f003512042104030b1706050400707007000071020a2000240e400354100c10212056120049400117116660b003103540c002d03000051508114180580044c060351081003182d100303a9030344404a0b1619030a40d002907100f06005154004a0b00c00d130050500745c1103980c80028003a60740c08100000c40002d5044c921101c80158040003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 593666429 1250 593665179 593665187
    0x302070510020307020303122211010f090b040e0a1b0c0b130b0c090406170c01080a05040803011e15200106080309150c0d030203101d07080703150312 66
    0x14541d07405000440c100b90742035002a480340101082d026010004d0400124603e08100c4c1980070300c10074401c0e0702d18401640c204040000c1ca14001d450106416403250601e0f40e1151171010200e464503c0c2040c14030341488542c681c0302002400340c3e6070700e17625050340360351000c140b04041482e104103494000804456280884820300001c02d5030342c0da25a290141030104e4150384405034851190f030915542c407500040020014480368121034801d807204424801031540006031031100707071001d8a40c000c1540c1d4803104e0700d05450382224000e0020009200411803500e031183d504810851781c095034480c00d41c4502c2101d203184610340140000441c461070600400c000400310718409541300c0020b00c0404e051148480d07aa101e1040805e010382e4000051446046200c001c3e51300e980342d00c400b0390710f140c40d6200008000c0c0d001641c40c515203056028000800c00c007011071450b4001c948a202a1083e515404143d482200007000e40052585840c22880550340303a42c21000950320607a00e14103075070b081d107400034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 593667679 1250 593666429 593666449
    0x501140f010e13020306010302040c021c09090f060b041e08030c031b0a020102070b0d0e06100603061d0109020906160302060a050a0e0a0825030201060303021504030c06090804050d03020705 83
    0x100072440f071020143e1008900700341526010340740401d114402c184201c3ca00300e81d6252440101860341d90420340b1030382c400881c07021280c203000188140c000b500221002c48445110f006c201c103d04200400c2420034a84400300c00c0801241da80340381990341d446a5042d940181d200c00699000021a21150038400c85180e1000f00b0b8440100001d904981c0080d6590704507018001e0b207014045541a80040781d500401c1031030f800b070404e41c1c840741424506021840304d54040d0f207020038244000810510701104400c1c1f038410985a02c009140d18018040e0000c1d4007611107290082400c101d48080002100d007480c0d00329210742d00a0400c1e2400c0c02120045030405803500346800e013040c0c8400c801a03800640300403040e40050b1441d44d154150354040d840074811540b0490141e01c65a180d1003459010b51055040364081e03002d48032002e0501c10702c078800c00b10890b8000e003c100e09140c1007003c00c2069116900c01c903c29200203203466181c0c40058a580d511000c1240164410501401030341031240400e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 593668929 1250 593667679 593667691
    0x605040c0305160c08090a260105070f11100e03071b1a300106140316030911061c06050303120f070c020a06050406030e0705100302070501140f010e 65
    0x800060400d0f0001000703c07100b03004920704029084901300140302e420030031604650342c01000d000183e56140d01d0003100c040e1142c0045010844201403100c4210103000f154803a0744551f640e100e411010350401e5030b95568403440c03070a40340700e55100200d06482034482d00a040d05c030200119280c9035185801c000c40804420004240c00043d001044a00361807510400b211282486254071034080104941100811010380111071000ca0500103030032003a092070703c2c1601c143d9501c007032503100e212507401c00724401a139020110781c180c4e00000c4041c61107507210020140c4514082e020b060808400109582c0007660203500003464401002035542d0a40700308070040906a02031800c00c1c21030f21a40481c0c080042c07d1280e602ca0000000d61070b907204015401c42250300825102c400354807054002d000c1d0300039004000129207840544c441c28080011840700315840182150550038040348106e01035001200110780c1903413a00d02e00c800c60009503942d207100b01e184a150031629803601c2c40310301c0703003440151030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 593670179 1250 593668929 593668931
    0xc14040f060315022808040311010c0f12020c06010806160315050609224a010b0a0b1e040605030408070f020306070f091403060a0c110706030605040c03 67
    0x40000800071a140c031001c00d400c0c08010b8565010305210341c8405400e03441744440c103075001416100c90780c1018070b95000d00d01036070340c1030900b1803203000082c205e07140110a0408588540281304a07544100c10010441c11042009070410000b10b0310310b80f030714100303030880c0d55550840b00822640301c501800d65422110a071409208080c055184417030300c54550b00880d070281c00005100550740c0c491202c02000d107c8100e5100c1100000c080d2000028401080302000125807070110341c03014643c407644c803060410180f070b121103003003900300b62050103c0039040c155142e0354031003d02307000695400201000400000614030b9591502c0c40d003503c40c90403052003860002100303000603c50960305c00c0549a100354406c40c5d031941d514a50416034075a20351441c000798584240010050b200341d0100040c24502e0060321605110703921004000050002d644056030168000300010760b80000710741002d008885a420440207040e20003005070305000e0140c205001203501c2c0e40040000c0e007030a1140e0301181d062454 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 593671429 1250 593670179 593670191
    0x20706141611071a090d0f03230304050c01110c15120c1611060d050406150b09010c20091e060613030b0411060c0109140115050d0f0c14040f 62
    0xc3c100c00c440a0b02402c200b140e80441d000c4e21503141c6c0e0300f900c0c2a403030b0080f29003541c85206240003090491061801000c01146100c0000c4440d002000d60f8000c81d881001b070510070200d5001125501c801c43e4036245030b4854010900d15a48407500c1141c0d03441c0c0c103004100d90b6100d1201c605824030300050712822288504000b40040c0e1010170101000039030b4400d8020080d4a000c400291060050204140c0e54614103028042003051651110b102c5034400d91707039a041c0e0b96450020240f9400351b00e003045c0c00704003c4004100011004000c0658414004850141841010000c02c010580c200ca080384e0354540c200020201c140d00c100001e90000c000c0f03998500d40b080d00480c1309204100ca100003010b041d03031500464100b01041c0d998000ca01405042d0f1620350070f0080003d8003034882840c003654072080e641d40b803102182043c0645405000d08245044039285480c01303001040480c54002e40c3d140f00d01c1404034001400d40030012000305141d2501d40e054990350002c0000310f4070008003000c18580703440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 593672679 1250 593671429 593671439
    0x8030a08090d02071203050c030307030506040f0903020c014d01060803120403031805070f08060c0403020f01230a031103060d06050901060314010f06170303060402070614161107 78
    0x5444c6056490030300ea110b07403042140c5401e4605006c0c0b100c09141500000c0304001d026075055106602c11482140c050010880b01e03d500c100b15824040060016049400200002d5000d40c2112031450005c000c18690070708000e810701020703039080b0000180040d5010660f00000030910550304200180c20007003003000c0c509035080f5940c2c420050310803961f03844071001805043c040c0e4404082c241000503d010001124a0001d8482c81540914440c02d40c040c00042510040010890f00c00e2210003a07a0f8902403c5400b00303c101e007010120181008485051183c425942918240c0082090000144c035030085801c00341c10f503542d1003640003010310240100b00e10f5a503148058045542c0000c00050240c807400c2e0440d001d000c09400203810300701d01701c65042c0c2c41c11056000300242002401c04004039070320f5000341e003040000ea00d150300d0503030f10a20200300c071490f240d8014513507180302d00c100007076058003496942051101181d101c1003000d040c1c441c805049402c403a0440302010458040c01c00e09042c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 593673929 1250 593672679 593672683
    0x120a0f03030b15181c050a03020d0e010909020922020705010f0c0c060e0111120f01050a0305030703050a05070f060906061406120c13080d1b02010e0603070309080408030a08090d02 79
    0x1c1a076200341c501840800400e515242d17510b80c2005040c0d1070a100d00c2403103003005582c40d41002c400710018421202c60080103445803e50b08034030075059541e000010324081200020b03410060a640d40005d20b15250351103d08404211a43e034030708040c0241c2c032201641000c501712480200300c0c5e60045e0500394174070b8860707a1210403240915481840014100c442c0c0e22590700400388400301c10890040081c500540400c2468520300c1a80d840888840303603030f00d0340d050115104007488020b280780d105104071030000707001d01c0203011102091b2038144d0400322a51200000e0700002d40c0c0540b02c0f1541c0b01c5a51043c004203010340006001c3d06d18695011240d4800071a440b44190342410f05541c4064010074046400d9108444940702e070800780308a207584604000791508076802c012000f00da00c45034200400303101ca030806240300b030b0140c50ba180803c82903424400b0990001f4401420107a071580104005106000030700081d00202c0000c5440340600301d00038107280c1018260382c04503407112a43c02e102c2640 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 593675179 1250 593673929 593673937
    0x90406051902041d06030106290c0610081b0f21011b0f020613080901050d091202070f1809020102100e06040b06100f030209120a0f03030b15 62
    0x1006400140c25900e407546000c0341e0030503900100e005030000400151215081d80603184444040900c4805510b4110070542220418401c0c5414802c64040040030030f01542c1760700c1c071b103014000c0c206458400b410002c5030400c201110800c01c003007036011091003004000c002e007040500c041c44c0d0701841d207d03c0a0001c5c805c0100702004070300c1000c204d940400301d11506100075080030140d60083c8404601c440720b000042071003942000c0000c60048410928078800a143d42c025030b8504203100c2d84038003a448075070f4513a2000480d14117000041140d00e20510310751064140d01401602140f0740700c50744100003801c4c4602c5038010350101101200a1050b5250030302d8a0045210112002401022500c010f1f828102001c0d03408000616024000d440070300007184140c400d40c0b0440508541d5030710482080b481c1c8051170080d00005e0640d142400d0030074002d50092103445401003a00310a07600b0304403841d18290140700100c40785400fa400c08000c040c0c25015400004404643c1042d800c46801490215409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 593676429 1250 593675179 593675183
    0x30c0b03070c12090f060e2b0f2006030408091c0503030f070315050612130c0b04031104021602010c022d040f021c09031e0f1403010f030b1b0c0615010302090904 71
    0x1040e0b4280f403064288140243c1c6920f5200b020130140000c0c50400350300c1c40a0500880340304c4014219032142b24030301882140d104075440160079007400d8208041c00b00d00e0031014032008144d80f00e4103103007010420410203140700300c404020f034034041d151814004003501e6540c0079140700e50504007030500c80d40d65000b040c1c501025400c1130010b81540d441d8004c10540803441d1018180c44014031000c2503980454005100352030094018090100d261018002207106550f81070211120b01a041401513109004160807140001e089600c000b8007400034483c00304202c02407080f002c4030002c010310f080c2041d0103020b00c0304420346821402c20b03001201c18412481e170058681c05083e910b98050040600983c0c15042c90000c220030340741074080d204000380c1914801d403211000300d440d180151100c2c1c42402d003202d059641c3c00c42d001c005145555a01414007001030503021344102d45407036030001d426201025010480360392004000a06000c409103980043d02003640341050300403c40e28203913895003001c060f0003607 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 593677679 1250 593676429 593676469
    0xd020f121c0605040905030a0305130305030f04260a030e160627090204080c0a2301110609010c08010608071409030c09040b06130204030c0b03070c12090f060e 70
    0x880c4060600000d02c1e080d0041c55000345001180c03014020000050000d0f0901c82c0c41c02c20450f1100080b4007045c425500004001907010000102d20300003410550341c001e031051542075410350161500c071204620f880c3c031080540c007000c50318500390345d814042d1707100d114a00400f03880020743c025400c1e84500c406020300c0003400b544006440c0d100044641c10201814055229082c0986640519010354000c0c4100740b510302c59030300c1400c1d151400f1b451000c101c800c0c120500b00f9210b82d00205031070013401045114140103c1440c44191a60180809440b0715040d20002402c030007082c0000d0509401a0000c0b0304100c40e0310100301589070882d240b04101440d480e000c0d911403088a0000e49081821441e0542019108080c0402c01a44466003801f82ca4101c411000c074140d00d0001d2400c80c003d40c8401f511003007020208201c0b12358000c00541e000810b500d4001c0b00c1c04007944421820301450582c0c1c1e400507074510030802c0745020360442580617041c41d1408000c0c0d90744803000500500e5001403043c20310 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 593678929 1250 593677679 593677717
    0x1b1c0c0327050316021f020703030905120d0e01180f060809030c030406081b070c1a09060306060a05040503031201030b0709061e0203130608040c0e060a06050c15090d020f12 76
    0x755861202c11520a6a04100303444082c0031b40e2002912600306202c00c03408640c0040c0049481d1402d042e0b01c3d402802d004004141380d59001104a407184644024a03040c46a50004009402000404000a000244214101c1c0c2e842c000d80105800d000412003e0035800501002851580c04822102182e15600c2d00800382d0300c40a4101c5688000c081e14900420310002c1d5120030070242418003402c0310021140000e42e000741d00002c608900c541804198004001c0000501170b1900c0c4006d4601f400580ca4200d04054680d40401c0ca154041e40c4081c08154000f8010401c214080380101d6000c4003d01d085001c8902e0442c0160035680d0780c0c06032400010002c40761100841c800c00540704801041c41e2140c02e4569943d1003d00030b104d0554050358200d040c3d8001140003a01005e409000f4040544020119850241c08aa9982001c0314429841c00f03491480d1081c00708454840b8003c0e503c80020b01841413081c18047c2c81c03d40d800c100404c0700e4101c0b60110001405080c00e0b80d0241c84210064000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 593680179 1250 593678929 593678933
    0xc06090302120a1101110412080313230c1e060307121a0f060a02060106050d060320040e0c1f020307170406080702061b1c0c0327050316 60
    0x8020704522151080b0701c01003801c1210b036910068008201d031641e0300030841501001180036062107207005d0b0f40070030325624030220000703000c900c021640641d000c098a4078000055941d00350501034036400507021b04286002c810203503070510040c49403510486a280c801000c422209440c03260348100d141c03003250044002080302d07001d00c641c940501c52141c0c0c01c2014500d07101c5060b9001555660050140c00c0300c85102540f03040c40780c12200740803083d40044ca0320742e10f00001100c0e90303805195001d95558540d10000001445503001007104000c440e07003c042401404244411150702c00034801090340301c81014102a1680c6905010000214265424003000010103900e035110740c1030000c2142e14a2a003a8a1443c3d801d8041e2003030b90f91070b540d007220545a0850880c2d481409481c0805d8800711280061020300c440c10042c0f52034458610000755106a000100302110384400136140402e03120b0107400c80080644808083c0e9046000511528190640354590780303014003102203001c1507a031060301d01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 593681429 1250 593680179 593680183
    0x15030d0c02010201150f090b27090f0a050303072c010e0a1806061704030e010819020a020a02030708030a090b031008060429010b0a0f110a0c03050d05030402010c06090302 75
    0x5003129000300c49441c0b17641c0d0f5144403050200395200b429012450150003001b40c0c90091003240f400d043c1c0c4404200e03003640c09502c1e485640c40140680c80780340b140781507500901200307114005055024901035a100d10b06060080c2036201c890000045207403540007402c22100c1540f4184110801c2803070401d184d00c0c00203010620703080e03440c0c016401643c522051000c024800f5003042068401aa4030500741c0d0440b5404a80c0e500703415100100800d8600541c485030f9403107a8603440c0d001181b8501d4000d42c400d444410301c2280e02058480c00143c0007141c149040d2b040802004005280c610003c500c0c002c807400000b44941d102c0d0280130400480000814a096800d5600c2405007201c1000d48840741864a0424404403810403820a8280041240108003800306803843c1260400044a45001910007040329900181c144100500c200a01c034082e5200003081440d4120340705d0780104070303001e04505001e85030003550070f000410480100308000050b40d005d0b2040e2802c55008201003003210442ca0164 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 593682679 1250 593681429 593681441
    0x6031f060b0f03090d08040209011503020715090b09160b070206040e0c1209030f0409090606081b0117061c06020904140412080417070c1707080615030d0c02010201 72
    0xc0c1410004200c100d2001040c00083d4054410f140c102d071044000d4080c1500e140da8100c401a40c081d01c0d03000100304080090315015114404c500d801403038070342281d40741e01840000124200302c0f5507545083c1010080740c542690b07000807182006100c4184140c503419581011409800c0410034040f039954219111107081d03c0c041e1411003a9440d041c07409c5501c0300390f640c00c5052a0000110500041014600040216814070761581c564510b0b06040000200c058000312808072103d0740c0da0300c80043c1440701072000d4031801d002071311030b5040c007041040010007501c5100c540000c2d086010050000c903a80b0300209202c004d4a00070190201c031000d0401c43e0003030044040031034110342400480c230060503080c8020b6115610440d40c590802080e010308440004044800510010f001c1030034030016034411000d006018802c020104e1070395151402c01c1c07007070b51451041c94800d500c4208180002581404182d5001e190485008030881003600040d6841c03402481f01c070148000c0c001c0f00300559200f07400207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 593683929 1250 593682679 593682689
    0x31104030c0e060a060e150715050405010e1614010e12030c0309010f030c080103060510050a0314250e0c040b03070f020c01020c1e0109081002030a0b0906031f06 71
    0x803100c0c1c0d9105141042c5801c12100d040c0b00b03058080d0081601805280e000c902d90707601411041c003424103c0f00800c119408804240c604e1040910003001c042d0450003041d2045100c0c0001244480c000e10100f0301d05080b541e0340a02d48100030030144035901019010000c3c494092804951135404440403030b002a015031041c00302400009070303480001e04008001c0281c120203176214251000591002c8044132240341c9100001844100100701040564200c07640001030704000c04403080d9550300007143c01440760300c00c441101c10502e000c4880070041c00f00e1468901c20205c020800c4884554122a00d200d60192042d181407000100f00a10385d18010354020304003443c50255641005c000c0549400ba5202c100070043c840c0c0040e54400394400302e410003010700003520843c00045185048541168400340b03d9041101e00c40001428400401401e42e4103080b4070310040c2d0301d013400942c4405807040400d0342c030300807248ad805220068500291f40d5a000344884610351142c46400d04602c0580764030b41c41 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 593685179 1250 593683929 593683943
    0x930080c060a0507090f03111509060c01060326030a02030a0b0a0e06090a060609050d020f101d010207050f010302090a0b0a12050a09120503091914060f0c0a03110403 73
    0xc00010481d00d520084c00f50342c0c151101920140c1c6c98030b98128101c90b0340001415035481c41c0c2000c3c0581010748000e176003091b52800e16803d001a4601048498019240b401e03610781d111001001404000c14000c1e1100e078001c2403411485410403a041c5052101810907407001d91700100285481e003459100301d6030000c00401490909964107856000408241e406601c6452554041442c0341e01d184200030403540c1c0c0b512004009882c20003003050b401030152040c0d802000c0318040011a903500313036003c2c2c140035a40d1542400d0b150a0311f04d07260107d000b142d025056500c070304002d100c0c80c2c2d41e56010b5841082c09183c05070342c8041001c0800c0003441300e9071150f081c00745c1c00701c0c141071070340d400101e121105004503104110b159101c1d1400380582d60804000713480d0310304442086a40a110344000c55101200104441050071055007151000b82c40708025150b054140442c1510342c0c00074400b43d504503611055034809801e1819400c5e2580c407858140c4014181d503802489802c1c418002500c00445d003104c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 593686429 1250 593685179 593685181
    0x80c0c121803031c1410060c020d050106090615020f060a050402040f110d1a090c0c1204080102070b07030507090b030a2409060b130303080a020706020a0c02010930080c06 75
    0x80000b1030b000d920034013401c2a5042800e1090108480340a551150342841600f43e803282c036040081d40d06180d08070040e078000f42c081c0442e5000c42d109014590050544031800201c0a15203510710285c206250070701d80864100400117540c1900010f410b0f508120f100302c0000e0b00b81c88a1000038000c06070009983c803011f042424500106640c10b001c0c1040381c00c1c3d403100380901010042c6005140400c0300ca141d51007004ca0b008a1300b4200440082d01c1543c126404450442c51400d039408125082540003009170b81d00010780d2020001e10b141132903000030060505008a0822400c050301c0c691150080741301502d004400100c6580d07894101c42103201c0c4090721411019680d41d090080f079000c9006103140d450800340001540308444040700c50b61071444494a00c25411076808641644016141114883c0c00f07005c1c0402091803407009000c021501c2d15aa0f107040300e240300252151440f03a10900c107200e250a09002455038688100344010305504d450394414856250125443c0070300040101c3c1441008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 593687679 1250 593686429 593686447
    0x40e160314090a0201080109140a020a1701080f120c0307060c0318210c031b020a0e07110106050301020a05180a0e13110301020304111908120406080c0c12180303 71
    0xf18250510500070303600c0f401d15a80760030822060704c04801c2c000c11847d0400002440e806199070160804180030b2428080740c140840ba00c100c000c1082e080400c83c0c8d00711680303008810201b040b00c0c0c900c0d001c82c003c0990803c0f6031003d0302501e0340500d00c0007a01080d02c2c1c100e0701c59900d2003580420903041920300c003106602c120b414410704541151a0410500080a01d4071103064041c5103a158859416074404004045c004130841c0c8601d0420000ca8020804030004607032000525544d6211b540e071a581c003070340c54804116841c00d54066510a6010384d10420001007000d500c1411101d0740d0f80e150350305c03140d05254040440d80100d410344c0607100810780b400504c078071481118000500103004020941c1030511a000b00340c200d2105460091149416400081c1e1a0030f00028000007491858403800443d036680303070b4283c242019000b500c20003450016040c4032454015241603001101600c44c40d0420309807154075980e804a424189060401c00700d0306904400103400c600c5030180340901500c1c0c0b00d111072 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 593688929 1250 593687679 593687683
    0x30213090b010b0d182609061b0105130c0b0c031b0312010e27010207050f0606040c020a0b0703050612010908071e020f040f0906061202030d0203040e16031409 70
    0x48140b81c0c440d0a190405807880c00c0d00c8200030050342c00a500e0030300c040110b04000e51a008800040b20360400a003d4003040d660713804060271150403507454106010461411040c21294000c10742d48500e2524030342e002c0450700360302c910310665610305006503690158200c003525600a444007810402c800812100c2c0f016000b001402c3c50a01068800c40030340d885800111b070b030304d008a4810b075410b070850f0205450074071203410030980c00c4400000149401120b0b01c0c1c180c02e140030402c0e002c180750301101c240002810b0611644081266030b10150004040075520141241c00181c41c1504140e280c40104803260364803018480d052803824002c004400701840d00004907004a0070540f00039a440c0070705802c08902401091046074020210881903186404000040c1207021789100603d0b50741c90a00c00140c0300f845410302800d240e550000d0412081e20400d460311000004940c21900203100030030400002144242e001444400340c44050002c80320200e0040040036041e0140c01c002405200e180c03400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 593690179 1250 593688929 593688937
    0x1a070f050a0b100803090409112d01050a0804020f04060b0c01150909030507030804050705060705161205150c0f03010603021b01020c2d060429060901030213090b010b 73
    0x46059a010b40381e4914010701c9021401d0300c540100c82e0001c010040d050b20f025071100e00c4451150a4078214031400f400131460402500002c1580c040c0100395200d1888111402508060b80910f80180740500000000b4104480600001d00a2500d010540c0450b41e442d0070940c0588000d034a225207a5060320449030184c1122074569015540070340d404030300d210311070080091940d00368035003614100c0c6a0b41c084407480401001643e03e40108500407a041da1400d000b01105400751004250130b4a0301807a61408407001e41c0301a01001d01c1e80d24400001d41c4c04101c92005144000d0b000c070311030303890310205030892061442160780b10400100200b03d43d03405a000d4488942c403e4035034806100341e10b050500303c1c86030b505d14050503484040e011003800402141c0c01c40c015070525140e00c0c06150070303620303529000040c0d8045446103c5481303448940700011143c070b82c01c2a00344004028608000c00401e0040c6070600010340246004645081104126001142141d038440c03000a00c0d980d507000c180510b504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 593691429 1250 593690179 593690183
    0xb0c0a0b09030711040903050301150306080d171303090506030c0409052409040c090c120603050d080a050402100c061d011d0307050613030c050f0d17101a070f050a 72
    0xc4c0c458204d00322401e00c0c1c8140142c6a5058441c0c80c696402c10344004070001c0d0004c4041c0c201a1645c00216904109000030f045419558440010a002e001c0c49000c8460000b0b21130402588501034540c00f0139400b400010807240140d450640e40d88079141c5504041c86250401c444c070030f0800c000d001d4603070103450051954014451280d00008072507410051844002d07140a0440704502005000030002603004882e0900302d42000d01800380c8240014056030507551003a90a500283e10480b815a00415919031200e41801c04001074070b0180d001885481c06d010700201049900b06c01d00082085076408040051183c001e91500c8128584159003e85181014241d1503072015080d440301400010a960040e94030074003804e0550380f2503602100203503400344140c0400840120702000b01d40140040943d413100c4201030100e803145158003914402c0000000f100d404200b104000500d4030b4401c2e50010f480e2405d2580149240000c0e0200190042203405065090450f020380104100003c20030040c81c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 593692679 1250 593691429 593691443
    0x313060501060507030f20060c070501050726060a090207050601150c1e170d02040806010b04060c030f0e0301020a0e040f0203070206370207030e0907090b0c0a0b090307 74
    0x2a80b0b98808403041d0080d0390008020500d0b5072001764985001c0c0ca1101810a04a5400c000c0100183c0171030346000801d40d542e0030f00c038800103620320600c84203000d0380781d102281d420100000b85081451004d881c1035080101c1c5200403060101d00c8503074450564030001c20540c1001d5441e090756040c20b540310102881229000c4d460007210062a50042c07504054298000b0340c070a800c2019802082010701201800b110107665000c01d8901c1c0c00051000740070031030444400147c40d03908094001b803410506070001c2000d50418042005055400950500f60382c0d81441c00100c2c580e44680140c4281d180418019495400802c201181650114030340c0028242100c0502815100c03499140c01c921041d641000160400d600003814100c0000030740c030051010802c0600c030600842d104011400341110340301c1d14213070001005801d0652081200b242100100c441203100d04040d0005045010588210b2044400c0840c0003030240b1014407131540e8603900301d005404c403460030031840c44e200e602c1110222090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 593693929 1250 593692679 593692681
    0xf050103050c0a0f140d1a040318050901050603071101060807230607022110050a0c08091b1306120c060909021305090402030a0c0807060228141203130605 68
    0x40ca101c0b8802c02c101c91068440007030f85d000c0718041c0048680605030036500d003c08a108040340720301c00c00c0c40b0340c8100c0c00782c0e031210100e02c40068444030400e40340d07008500c201290001070000359070f20340c02c0b0781e0030100310301b071079507000e05082400ca025011507807012566028070b4000043c002c00c3c03d1128080190b607000905041e1002c8001c014190088007000ba4000c1482c5d0405221652240070303203040840c0d4141100c0d0004089007081d401c0c0c9400700c5d80b14030b682e0345845207107111079000040c0c2500a20590007030030030034a04108140210b00340b41030280c4540300582201c0c040414035884000a010b41216148000d10182042500045c0340e105290004003174034000910503c00d842918448403100500144503464427003000b01c5108060003c1e81d00d80075130551400000ea100f40f01c07100404e01c403009002100c1c940840030303041003201d484603100868440341511040000303683d08414540c2c061520004190300940d0140ba01e0606691010010400018404564414203900c04480d108140a1000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 593695179 1250 593693929 593693939
    0x904181a1801180609050304030c0b0904050705070201021b01050403081b160b03070f1106040309051c0b0408030c040308040605041e03020306060d050c06040909062313060f050103050c0a 82
    0xb2100c08030040f012030b20320810840c2c00202d0030380007100020300501c122030519440b6101c194101c0000d50050800d103134002082e5460742080e00400f64400840c6c2051401d002c3c142d00081d4850a04a00c2d031060141d00881c8000306a024600b51800343d908001095160781500003905600042d11008003e2441400e4204d4842c1c803011040100750380d08150341900f0341e1140242901c2d4980340c450448184255000c801c1ca0030300c001c11046100d24020b80c0c441e8040d5142209004c6100c0d100886d0b0210104a00c4081001c105460400384d04a036018003030760341c0c0b56070305000c000b1580242c0e08024111000050000740d6541d00c1006042903c1070840303101040001c100302d44181000034807009415801030300001c1da1074501160b02850310ba02a00a840c507549181c4009105076116404c501e0300311703642d6400041488020300c00c11400c52030b090058404000304540400d50030000600201c0959080070030101080003503013001c100035850040501c1196124940181c4a42d200c84440f070081601c5400000e07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 593696429 1250 593695179 593695181
    0x4020f19091707080708030307140c0109080c0c0f120307080c0c040501030f050f0d09090504060e010f0c140c07050d0302011b0e0301140f1512070b09190305030904181a1801 76
    0x13000344140e4a48020008511b00d602c02980c1041840c452f55550350862400030502d050010003071046d4040103020700f13100d0801004580d4074880d20060150424101c0c008004800008075065179800c428020303202d04441304520726003a0b2400c0e6058109007010000020460001041034880f0701c50380c10341d01c04010f200c056550b1a0300c4e50307820074001410302c6001c11848040d0380c86950031170f00600740812100c24101205094030308224501ba1400d94401c2c520101690109800c0b03050905807040500e000003002d03881c1d45e40c0b11076000b100e10a81709074551004050003507003c00585521510410280c00c0e0301c120152503145034000040c025401c00c8031181c015a80e0307006a900c10300142e00c4207415503e0b4000c5000380c820385c3c0d90300aa08080d282d2141d42d250070081241d0401021001e50b41540c4e00101001d103c0c5118240b4480b410841407014240300140d008070544141c40000c4c0d03000610040e4806806070711b48400c0c100070b000304001401d052103107030500c0c0509102e620038401c03160f1107204c0505094 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 593697679 1250 593696429 593696431
    0x230411030708130503030f040213060b1e040e070f051909050f010203162310050414060112060f060315050a0605031f05070509060d020c0c04020f190917070807080303 73
    0x3080d41d041040001c00f0f00040c2c04819402500180502b01c10b425060f41001c1156080e8005038a5124041022207001d03401501581d00d107150310180f641001e2a022016080060182403c414082c0c0340360505405480380d015140841e0325215104160303207840a01070059503550082c140107950f4a60064483d5000104440010116044040102d2201d850700d03280c02c4000015207820b01094002603031080010032100180088902c000125410186444664903010742c0f440e600716040303200100942101e102422850f9a0400804a17010f4010f00c648e000400440e0001014003c81080c00d680c202c40f00e502c120b00c500c24440042100b42e03120400c05a40c1c02040241c05801e00701d44490000c3d110680d04441e400c040141030223030411401c14002420341e04151040000e40b5400310301b452010030200502c1e00e05000a41303046160120f16891516103200d20f44058448038004000440403a10850086006024041c2c1034a4074801c14904140c03149040d1160f901c1c00d201d524804030394030402104803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 593698929 1250 593697679 593697683
    0x8060114070b0405030c01060f170607050a030f021b010209040f020903070303051b0f0a031205101517150306240d030e270a0c0923041103070813 64
    0xe2410007071141c0d108a00008002d00499440c00103110300c04075800b00b4000c2c10060b04d08002031040d030328200289a0174885031040010520b0b401003040c0710200d0341140450340008428680804c001140744c44c6600030b4421400010070100548480251391070042d4040d0030742074001c4409100400400100c0c4050340101044140e05400000782003000034004c10081500d041003008080f038980d44400c0807810550440e04a1a440d044401c20301c00305540101d505260300b4810700c0030040c41c10003030030070100401d5a01900780301c000c031b0050f2030130494000c491003401c605c3c4800054034585070500c840c00703200909000303040c0a4881c2d180841c03d0b03000c8100031114520303107450304840385d14482420008040b038405016000d0001000100c0e010f529600c034151402e0343c2c416421141001e44010801c010a001030203440030b0f9142c145d580061716840407078a0202ea0b000c101823412400c00304102c8000c51085540c07150b02c2480c00c044100304180b0000607600c54181e50701c428100340ea0700d1180d0031941c0300350400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 593700179 1250 593698929 593698967
    0x7051c0c08070c1e1103010f1b090e041103010e060711101a04051009180c060c05101509090c0302010201060e0f04081e3f16031506030c080601 63
    0x2080c042444184629203014003400030350440031380c108042400c480b284070701c1c0060b0030740b0703400e085270407000d054aa01064900c51420401c01e82c981301d00e1101c0d170368000c1e00040c0181408842004203030743c25000030b29994a01e1017035811500300701d44003405412440350841e100d4060b059400302040da061103a0200c0c112541541040e9804110030000107000c000c14142180d40d01c2c10340030507090401d208840843c07150000485170411302d07041240a829240d800001081300c800200c0000480101e91003072441c0103910080351041c00000841e4408030315808c01e4600501d004043c105000c0b8101e41c00c03040328001e1700200140c40e100c0c0060203e0b0b020032034540e41c00d46804c4001c200010a100300420720b40303880e504944c0d018180713035a503e580b543c0328180c00e05c0c0484108103000c0d040c50b50307600010480c90f4202c0301c1c010034074101c50200c0d8611a0050551805d00006505d10141c2402034001074441c1002d181503080254648002800400d00320140000084141001450950185030f0000c400c01010781c0f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 593701429 1250 593700179 593700203
    0x60f0b040605040e040201020f0609030703080f061305070e1203070212060c04150201020d021b0d080106020a0204090204110708040303080901020412110409080d02040306050615090907051c0c08070c 87
    0x113040e540f00014104074118803552082c4a0881d0081c02068003801c0c92201441c1d841000341001014428041c00f0310609401440c00e1200554810b0b00c005141079100c0d001041ca80e0b03d1002c240c232004040c6020641200d18646422904100030006000c00c43c82107600c0341c1c40c9010a10159034410301150510f803a040200001c2c0305c9050700c0c0944005c1c45409200151900140c258403030244d0f0001585da80c200034043c01d40307101c0b128040c84042d808100600c6d280c1d07060b45c90060000d5a6411801d00a8000d0342d94104010940d1500d4010622460040030056511005132410064550251205800280038503011420440040c02100c08964403a40c454601c0d0700f4513228040c640410444107079100703540307450100c0091800f002078106e262800000680350361442c188502618001040d55101d01e9a01d00c0c49111140d004091382e6403100c007550303070039016541e1100a072454031489041444030718581410424008d0141c21940d0700c06001d642d0305c00640c4514000351801182c5900040c401c1c40408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 593702679 1250 593701429 593701439
    0xe07030f02150c16080c010c0308061516032f03040b25110406060507200d0b0a02092806030f09060f09261602130c03060f0b04060504 59
    0xd8004a0415242e5029515010407140000e2609038125240503110700e602d142041000d405014a01800c40203003170400320700d4480d03500244000c000821162066828254000da001003a00a94540c45014080f50810004d03e0070041d0105c0f00440360a401c46c021080d0410300000e04044400107813500310001d5040c03901701181700803140c11011443d04101d2035243e41e0881c8501425080d605140644101000e0b00728003401e20054503190303008001401400c201c0180050303011000c0c1c2944503c20740c01d08a072040c6450001d81810410705002d05100720500a205500000e54020300e41c824003110740071204020400c0300d919400c142e011498501c00b104804211042c02a008840c1c404803105001074201515a039080840d001c07003415451140d51868200200b03d42d400c0c4500d4000300c5000c5240340b5109802c01040a0b1251030b8900c0407040801c0032a504544621038820103403807065105000414600200030002c11081c03040740d514150030100011a9580700080301c05843d07881c3c1d111440c0074242 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 593703929 1250 593702679 593702689
    0x4031101030b0607120801030215040b040314010e0d0306050306060a0501050703030c090f2903131b0906150e060306030a29041407050a060c200405090a02040e07030f02 74
    0x1035150180c003c0010040c80300000c40c0824888044841a200d5a01c90350450041c8070309049106031001002c0810003061203030311452426a021240e0000340080c55001d06c5814a01504a52032585807510480d401c103d0700c2500b58000f001500d00a0307080310b60315030701c00c0b0420010149034840c003808540c0400030034011078440d400c4815045443d00300000c8450b52402001e0001c04141e0044800c902c844511400001c0061034140c00c5418001c109400c504180d074580c19800000d610090070418100d08807130322802a00643c800400c1d910500b08801c40d0758540030240c1d00341021145000840f0b00000c40014501202902e000760400b82c010700e00700c0304613500c40341501e800a91b82408411003401111900c1c011258991180d44a0a02c0400708508611070500e0060b058002d5845041c0544c801e202d01c81e444045c52955030303004946c5483c030030055007203442000c901405ca0741d0003509120030802055400104000101d1003941d04004030042c10b402c1d140c441c4a00d000c0217010034000120310000d4641 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 593705035 1106 593703929 593703941
    0x706030b180f2403120d050a09032c04020703030e0717030a050d0f060f0810020301081e12070b0403110a150f0b03100204090b060403110103 62
    0x2100c80b0100c4440081000c2c5600594040c80862081c0d02c000e0786180c000c014040d01c1e00f140005010501541c44a022115014207203170100b00340008620071002182d405646500c1040031150a184c02c00c542404503012407003c1d44903c101c03c0d03440380700a2401a100340c0340021040480080c007401c000581d0701c2011100c9565180d0041c07680c010084801403159842d0483d5102c0700b240c2c01a004203039031250102a54030703140700825840c403240861b00a4412440c00c641211468002c90802c0e403200340583d451940143d01001c2800c04000c202c0300300c0c400c84c502610200300c0c0c48680c0b02500d4004a80645000281000b40030a2681008903040c0700d445000c007401c502c04e01074031940d94120328074001c41c00710381d40c50a1a144003000d40e0301109a214008040d502000781e544c501d50040c0d0040c1c000c8500300c4d031400001001074500380e000c030741c100c80e841854400807509441c010748c004c0034 = true := by decide +kernel

theorem cover : BRFrame.Cov 593525179 593705035 := by
  have h0 := BRFrame.cov_init 593525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 593525179 ≤ n) (h2 : n < 593705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
