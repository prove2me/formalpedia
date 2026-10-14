-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2395
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:35:31.715425+00:00
-- url     : https://prove2.me/submissions/9b53b541-17c0-4587-aa5b-32646a7f4d68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 430575539 ≤ n < 430755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 430576789 1250 430575539 430575547
    0xa050616030c08010e060111031c1d0d0e1905060c0304090b060a08010e07030608060405100608341e140604050934030b0f1005031f0b0423060f 63
    0x1300440c1c00503d00380c0c8d008441d100421845802c494101100340050802d1503006c591002402000c40521404c031012041981c0305500400e8000d403c981141101c07242542d401d0805100b4440388500301302c03140e0150350801400551200000004401003007660720814051107a0b04020051003a144110803da070009030142c001407088105440d03016400007510710300800c02a072108000c1d428100301303a5040750250b200010004102d42e071801410010300380540500b59440800d042c81202d00902000c4d07520700715541c80f0a41e440c0a081c810f80340039050204124880d1440340403144a20f166a000320740a521800e202112940307804030441d020380314041c000350042d8031015403980320103001c44901c004020120307500800030203415142451135215580e02244e000c10300c1c0107104441ca14104242e01440c0308010246400d03802a08481e00100b601250343e0f184180d2032026003881007260400100d6120010340003501001c507400780170b04c00040e2a200c04c10b5221141c10000144140590b400c0e601000748 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 430578039 1250 430576789 430576801
    0x19110d060605040b0f2805070506071d04050405120412050616050f0a032904061e050108041a0f0f07091404110f04080d20120c0a050616030c08010e 65
    0xf8080c0a201d60f650700341e481c0000340700d83d501b04604000300007100040c80c0814180c0620030100445034000825081030441d0810010340c007038001c124400803c0c0210748501c003080411404206512030302d190001030343d440750b449464a8a0500312401c00390323214418440400c1103440407010320725800c03099441d001d207440b4404441007080d4102c15403a0f8140344e90380b426003151910041c03401340700008408031910b9000198041200703c6d4200e400c250025a2006440c0b40c3c0da82003241c810081c0c80302420084c40c0c980d10380c504609100a0b0f8080310f071200c0030303003c07d11200c112050314850041d0303140284d00310590f440c81c804a40c91030580c46240610f0120603401c0d190b50600340e02015540c1c99180b8110326200015101c2e03201540180c1c4255001c0e441481d148034502c1e0700209100d90f000f041c01003501c4c1c0000391440117079120600d01c440505100c00103401e4800503010060120b15984c0081030303490900d00440c07a0342060300c5801482011904003404141103074802e16210741a5401500c40c030450740c54135 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 430579289 1250 430578039 430578067
    0xc0303050403180308041d0417072406030309050d0c1a16050303040b06090c030f0711010f060e0106020102120a050c09030601030c1409011d19110d060605040b 70
    0x280050b000d00401c40340502c800c0d800710700d00d0809140980c8045540d2440c3c100d09841e05200104071002074803d01080c040054544481107003a10050144903071503040c20705103007445043d062144029440d4a0a1040c55003200b030300594102d902a40700d05003100c0c0c0c0d41c814040e001000140040c48001400c01c1403054444401148c2c1e5070006510016040c0180c44444094000403a0000d0b60294004030030041001000321407298071101c1a581e076442030400b03484c44402c030300020b40583c04280c2440c0004000d103119410a8604001c140c00a000395182c20140500130402801a11800c03140c02e00040340160050088079800c500e5200c0341446695281035079001020046d00701340b1a1841003001d0310f041d6904000690180d03000c5c1c120149070b9860300800c404c4084801c605070b4080e25490004014020010014402c402c4034034548084c50b660383c0000c100082c40710300000300d0051030580c0c0000f0039010807010317080c0850350f40310810120792680802e03078250003544608843e5000801200204100c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 430580539 1250 430579289 430579291
    0x3030e101a090a0e0312010806070c021503060102030f041202040509060c0d18020303120a1505090a09060609110405130209091303090306060902071a0709140319060b0307080d0c030305 81
    0xf02803800100d60300c00c0d01015040d40d101079549101d00d9000300041c401c01d0781c20b201e802c2c1c011241d03040c8201501d030190301141410015990b00a00e0200210000c0c410303900074811107031003103072400055680e26191041c04d80e61501c400010f80c0203034904000910f000e00e00040c02806501407507803a5052244040707070385010b0322500150015010f00c140807039005840c100064080740001903204425450300090f003004030348034040c0850f040785081c081080726440c0c0790800f45d048414480301040317200c0c040c14440b01030704581d80140140351810703610603078510703090000d0419618200e0313000143c11080b001d03c101340e000705e07040d82d40e20856000101c2c01d0000c825001d035410078800e0078128440f45e501d0302c480d42160a10303440300c9169a000a403400801c07082001100400800350a007568500b00031784000c2040c01c050241c5040d02c2c05051400c801a40d081109403840d020071182c040701c4041a2420402400c80c01c2c5069002e4070800c0c502190b40c0601203000c00d80c0300c0c000e50301c009000d101a2011800740070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 430581789 1250 430580539 430580551
    0x806030a170c070b030c0306012307080c031e0310170c060304170d090c0512100c021504062304080306190302031903020f030405010e0607031b03030e101a09 69
    0x402e680340011248100780c003541c40780200180554503898108000342c00c0880c45010801c2c1e2802cac0840d0703034040b803c040c4103441905801100d080e0301d600005100518500c10100003c0d05a204010744490b800400c0000394411004c1825824803541c0e01c8441c01c801507800c44020b019a0081c4800d81910300303110028542c000e0260000c1c0c1e4542004031007002e0b260340701d15441c40403581c841c0c0002c0c0a000b10b1014050050109032041d42c101e000851186449034299042ca05aa6440d80040d0301054402c2142658031061501c84074031600b0b09242100040c801103c0a5120000303401641c01c2042190305500e1241d07401030309882c51951400c040164020040201001c015400c580c04030241e102080071103414003a4854403e02c40c0101e0034042d103020304040300004d681e88100000d03c0700b640d000242294007902a035001d1b4a43c040c614050718103142c030750070421007041001d02501c04d160741900131700c24058000c810303600282c0c0d801c03000d20b0540d182c0700c109503d031039032525903e2070310f003004114a58000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 430583039 1250 430581789 430581793
    0x180b0103020f04181a10030b030f0d110c06090a090228030b1806030d0c02030a05030a120e01060e01030f050a05100f06050a03030207050105030c040509160806030a170c 74
    0x2000200340d260a0300035820440e00040c01004ca040840308511466040c0c12540070007007010f625050025003c101c6400922081548422900410343c8040020000d04401141175130100454010014103440c0c075150b111042e0301c110f1503003e0880c00d0480450b65a0040607100071121801c12035088003950100c1c0c409412240b415501460685132071103520000416035801081c5144140100b214120714065824600609441072081076500014600f910304003130305100c2c444407401c0c00042d003058000b9102508501001a6940d180d980c000e58441d031500f55180100700e075686e0500171500300c400c035000b041c0100150400500103c0c0c440c2040e2540315100b802115410803550703032200d00340070b1032811115400b5115a144100049640a9040a0b000c15194a6056495520000c4d40c86a4038030070b1a050080020214503c01840c50499000d4213026029203507a041c01e02001060b815814032480015407a14003041ca180f2f0302291b445009500103e020303001c403280b0302c200f1002d54000c040c54031140c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 430584289 1250 430583039 430583047
    0x20f0f01091523190801050f132909070f08060d1b030b06040608060405030318071703030117030306031b01110a060209030c06191206081c020d020304180b010302 71
    0xc0228084292040350007803c02501d5288500003030002180f070000382014484008014005915081d8894450f40e0f011940c801041400c0d5505000500c501d42e00c544500e8648035201c05c682a4040c0c0d94410a00180c81c0f4a0b400e0361031040454144002c010910009901400482c11618000b8140601d2a00810190f01c04846500340d0074010704507035200f19040d106907000c01c541490144565401400010098107407072030140d0750349449200080406089400203000154604070801891015000014001007a0078840d020141d40303030007d00c20a50070101c40c000c11201c00324003000f9130b4040c00c4040c0042080c440d40d0344461000701c5c4900303c1d543c1000032405219803482810841400c58038016500143e940c1c0c3da51050605045000b0041c038060b50040012102650405481d404a640740d46010751510a80c4d0750f4000140c16554040d5410384a210000b01c0810340801c640104015280c0881358412070031001613071039000707a10541a10484443c00000e442c1000c1d0080c3c019000c051400500d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 430585539 1250 430584289 430584317
    0x120b0f040e060712060608060618060f030f06010c0f170d0c0c11100c060b0409020d0803092a0904060b030303010609080f01021213020a0b0307020109020f0f010915 72
    0x1252000e050315605a0b0249051154490f0000f40d001602c0307651103414065103003441c60107070451078090b080c10b0080c440081c464012000ca40b5620303800c0ca80c0105a543d40c0c0000c00d003246000d4000f620b0800c0c2c1000d031031010580541c0144100d03002c0343e500889860011115440d01f250b040382700c4003c04100c4008000e01402280d1a02c14030340c9400807901c5600c2c6141c01c1d400d00e0383d050072011a0082c040c000444150540e260092120290380d640188003080e880c8950000c50041c080700c1100035003164201c04000208403006003e54400c146080480d207600c0e01001d10500003c2d12041c006202e1400b18825541a0401c00e0143da8480c0c000c103400719a6010900c00300b0b2550f0310992085d0005820564140047c9000388402c0000524020095052260413942d0300e610031405811002d11400f6294103d0440d101c450a4070010440040506c1d00c07464032400103406070103c42c20403482071010b020310980714904401102d41741070040e55100720460900d21952100115007292a0a0040711480d0b045c1e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 430586789 1250 430585539 430585541
    0x2111010501080f0601090507090e090a0503030103030906110a15020c0703050706110f010e0c010c03021c05181e01030e15010807030308010801021923180906030607120b0f04 76
    0x10082c00550010544481254165401d00301c0c1a049000018144400d11800702e034000003800c203540210071086036980f51011918540301d00424010518000800000305058000000c1c0c000c42d0304507180d403034100030300400b200e0720b0700d80b4100000e140000c2d0300b94076610381d0000d602605000b10a402100c003110340340c2d140c0518165143c1d1212002030041c1c402c484040c0c406021f003000300e82d120300c0284448901d620b01a41c44400d580382480c10041c4010080041c1442017000c3c15800100f041e41c50302020007080c0c0101258094681d5040b180310040325404039003004400c00075540540103180351000100d0004401a111411900b800c51090b5442c84144011510155000b40800c000400c000c07440c502d0043c1040070164000712143c2d1040c040f04142c00707840141680710495601d00652051014800c80311130300c2030031018a0700c4010128458070446400d290002c40b09500b119810b0840c0e803000d04241d50359604075105000078860383c020300c205086c9130b000750780d10b200000c00e40d0100c0350342c03440814 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 430588039 1250 430586789 430586791
    0xd0602040e090c030313120305190c0606050a0f09020c150115090e130201140412050102091c0c1a1903050a0c09050a03030e120102120405120721110105 67
    0x5540c0410340740500c198032500704020f40601c0025800303107052295240c84040082e000b4411034003014035000022040510403402c0369061080646002c3c0c0c030305181d070f40c000c04204d5000b208542540c40c102010a043c6010170013082110965910380d2441030420700b081006e500000300d00c00c0180b250081c0e5029401e40484100e000e00784a00440c9000b40f111440104456021740c807030007a0340300e0320090040109030501c00740701c0e0301c1c1c0a00300000c0581d00c0b4140c18030103204641c05a980078030042401420031106400801b40090215105030b113170400001449a200c04000b001801c00000900030081d0180840301520200840a401c9003001e40a000d0700d0b42c2028900c03008000039075034100308440609544598031084151740f40240d4803e09100220360001b41d6400060180301c81c0424601c1c841d505d078030325030440e2200040207545920450f0034800a803202030300d04450078080c0319038554070070380c0708001c1d030324199000080e2001070009521848901c1807809151410004001c08109488000340181 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 430589289 1250 430588039 430588049
    0x71a07080c1f051609030809011e11010515030606130b040501030305040806071409011803140d02070e0615030a090f0b150603040507140a0e0f01060f02160b090d060204 74
    0x30702602c0c01c003500072508540004200303100382c825410b07000c8a25070340200000d09881d0301540e0360340d4902642006031540000c15004d170204078280c200001e0f01030360064030b160104615038020701080e202e00a001c00c0c8640712170181a019805440082e03031900d850108164115a54000092001403090209040d64000d800c10f5002c518005000c000403102006103a5103c0e0a61900c084000304c0520030303168a124200c606030410001c44103040d030300305030030402800461f0700c03240750b410036018001030503101d1080344404c1c2c0c05801080c000003080020f440005200e00c5d00284000310101d911241d0540540000d486000c102e5550403140000500700350510580c40d004d08086681c41ca4030701100f0780c01640707600d801801100180103000c0020070009901007a55100500030300b980707160602240055416a10120b12a0708040621803d051920f400303c0c1a00e0480c0c0c2d41c014041c0c00403a05980d9107030700080b044040746102004000341d0a0b032802428900c50007e29502045030303540c45100907a0865002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 430590539 1250 430589289 430589323
    0xc05040e04111f02072d1406040e1801060e01060903032303040f06110f0405060a030e160503060606041d2a0405041d0a170d050109150503071a07080c 66
    0x14442ca600c024203104004003206858032040c1441c0d01d1244041b0300b1442803000c5814414108071480c0d5882050364098142030135100d00714504083d04140d1544600100a20303075282080c040391a944c0b001e03000b4103860150300d039010082d00e580d80455484c54004000112020700b40c1d09103281d4881c0000540c002c82c0107030701c05a171200c0e40341071100488129111051081304100410a00c01900f1703029141124030803210561940c000c20001e601900110180c000d0381c0c0500d001c1c9001490a103940d40060b902c003581211519918041403100700e202d94003601ca0104040c2140713180e8403a504001c1503000c140006440c1c18441c90740301c0d00202540d03010f407591203a02e001c5024021811b251054120300c04200c40b881181e64813003240c0e07507100c202e400c0000d00040c80e41d800040c0c1d00c0200740e0460f8200010360310104802d6941c2c0342d4003402040400d040b00000220325100040c58980000c2c41400d990f91003880d40031003040f01e9a0404a680310308800c8441c03405c284000d80390303a1401e0000f0101c0c042e200300d0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 430591789 1250 430590539 430590553
    0x403050a0f0e010c08090a0b0f0d0e01020339040b070510092103140117010515091807030b041b090e060a0f0b09190c05040e04111f02 59
    0x20041d04081c054006002007100500510702107a80c0003c001c0d1415400c40103040da9150b41002040300b602e1582c01144912000060203a12240c2c80300003002c0d02280003404100d06c82c072054605085c2c1c4002c1d140070003c100406e030408004907640340d10982c040d81c2c50402210310860761001c0300b00350300726a0001000090104940083c0402030008501c001c200c5d0348200035100c800e80d9800f4100854084603131240300003503560031440e4040c2d440300c0c44140305000045401d40c0d4030159091b0007045401d041a8035420500031500111124200420081009000343c500e0307542c0201401401501e26000c5446100301c400000110b1400c142a41c015406590303a03600425850400502c003460540c09110098940031010754042c1c8041003c83d00080d0341c240100d0301c0240030320200c01070301c401e8000c20303482902c2d2003d120005010443c0340c0400400c1c05402d0041070b86031754041e02c1d2806644598041710000c4000240040c01c415020035607014020b10380c01e948000f111200f1246003400071643c0c00b50303000403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 430593039 1250 430591789 430591807
    0x11030f0d030b130902130e030c031309060621020319090506010602160b04030809150a08070905040b03060117160303260712090c1505030105130504020a06050c15040305 74
    0x1000c022401c81104000e00044c059070380030414100107091040304156503141c008680000a208860940d60384504594960b0007190981680394014030070888030030b181c20800107080b80550032040041c0100c0021180c02c1c0c1031a010b020196000410314144888000c04941d80800705110f0945003d010707100400e855810725501038036140c2140e80001050b21100c40c100543c1ca2800120341c00d4a5004e840c070750300c5591841c0420040d803051005070014100200b8840059540604000e20402c0d066032800605951241400100c440d909a103d8050b04080014400d0003200d00940000a601400300e40c800031100300c0c5a8140c580c0d47c0c10440000d0549007044000124100b0070741414a580380814103107003800701d00501b60000c0c94006503401d80e142c800003018041028920780042c02001d26007110135800d0a00181a03a1090003000c0c4101001d03800d800c100801e52103454401c5501034503505180b03007005416551038104241d40b001902c201c101000200f04041005806144261a090384a641c40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 430594289 1250 430593039 430593049
    0x309060f020a120b150d0b030a02061c0b0909190f0c0b07030206090102030606160c050a06021509010c080c1303080a0c020909010c0219080c0322080304060c11030f0d030b 75
    0xc001607407145202152030f0080174103050803103ca43e24801000200543d005000c28144074401c0310280d480400405d2108100d04003040088810382115420003c80c2c10344420001c40c480c00352120340481c0c0c045078a1181c1f0303003000044002c21500510300341808210701d80e501180000c198011407101c03007000c0340c071104244d010040d00d6003200174400298107500d010008522240103415102c80c82d007001038030007800d01201c0104003001d0480501802e000b2034403010042d42d01c0c0e12501c4028035010a100c0041d4a020045c0b003481e2040c401540d40c0070765030b101d0102304046900014450b8075092024040000040c800340000c0c1403c0f17185450b40e68018040e40104030348150000c05110250741003c004900a0340c0c00318003072180c20f20742160110280e030341341070062480c09140c0000b11213100010ba07401e024242c02c00c90011400392030351074519007070300c40d9540c0e900ca024912581d4042161500b104000500b01040442002c801404551045200401040c540019000d031600400e0f517400c8440070701c2c186 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 430595539 1250 430594289 430594301
    0x40620153909150f030406020d23010609080f0a0b0711030d0b0103060e060a0b0d1d011d0d0207050907110a0b10090606050315010309050a0c0e010e0c03070309060f020a12 75
    0x10010f00300e04040c0441000c03d0300e440001c10007005641c0c00510112000d80945c440846907107000c0c1c0380b40d5481c03003075060b09009050a000700d0300428646107001070042c60000700c2d00b000b400140c0180074404826640d030b002c0c41c0d4018200001780031520a0152107140200090700450106100c00300f46c80c804840058111540d940210340e241c410002001543d4850140b190300b01c43c61550110f0f03440320383d01c502c50f004207500d2030150345011500c0e03500b500c07c0710150440c041502010183c10030341c810700c0240581e41d2491030003010240c1c1002004120501d000320072070b540804181403000710b585603d4602801d14141810488000c0c4401301444a02c03a040061400030380040306082001c14100080a03005010040120091203054218035505074402d402c000c4000e83e0000c200c0d081c1d600e89103071241801d240d50089070a803203270f1440001203d220b541d5040c0d001d050702c1c3d00e03160b1443d203d80c5001c0700076114030b40700ad8a10300c0d210351080c14019114030080c0301d151401d9403805407501c3c22145413021707510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 430596789 1250 430595539 430595569
    0x50a0605101707090b090601020d0e040221042d0f151d01060906121712040803010602060a020405010c080919081e0102070c061101060902040620153909 67
    0x1546c20001166000a410b03016441141070a650040304400010301030301c90f0f40c81d8600c0c14030310044000180a14505014021445010304000020030003100520000401005003061040c0c0c16080010038850028021114010400500c5440803003082c0d60a0b194014a041c194410866280844510038807401000d0200c01509211191078402c0c81c8001d18401c1c10040c1000c42d0f1b0800c901e940306400000c41e40380c861030780c103d81c10602c1c3c141000409a00248100005401090002030300300180d4405c0381c0c01d0310310586401c0c90071041c0d074030340e05a1074100660f050f8001a40701100d541c00d107450b0a1140040c04420000c3c22407140c0302091125151078500c92520f5a8010700043c000a03a90550071810f44600d40ba01461000000034080d0162030f06601011003184001008a0308075030010b401420032682c040011103111408020a40d107105a10030f0401040c0e11801040140480340c2e900b00030700d00d106c00d18108510714800c0e4017481600040c800155058005880c910b42c1c01d10009480b9204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 430598039 1250 430596789 430596799
    0xe0702060709061202070c0e100e0c07030e040f0e060619081b010c080406020c040b06161106040e090f010606050315150d021204061503050a0605101707090b 69
    0x10410300300c0600010400c3c06480c09000b00056040c015003016030545013a01d4020305d1030f2040da56211040030304040c050310502031142e4840d0300822920040c0c25503501901104031800c0c42e100c09034a085502d03a0041c2d840b142c2c081c0c0c44100e840301c09840350142c00303050000207000d03140c3e03802c015040102d0000404401c5501c07081510b02080131704c5003c5500c645c0d17900180c0c466460352280c440102c44400326448018151280450082406079000807510068075013580c0403c0380340c040c2000c021030340c001c9140c410a240728400e160400104548002840598003601c01428541c5031101950405011076140515074402d11115800240034050351000301001c3c18041d20314145544240d40c040c00000249000e0380744200440036540800044400c1c61880190854a8051010000000c07005c10b843c1aa20581400c104d280580d1b011602442141e5020f0010042400c159035044080d28004040a00c01c2104e0080040e072204181c044c94642c01e02840070b810201d007000700040880b202070b5902d5001d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 430599289 1250 430598039 430598041
    0xa27051003090503070f1e112b020d141b04051635012d0617150901030b04051b060409020d0e0f03040906080606010e090a020c0105040c0e070206 64
    0x400c0c400304c11120000c0d000b45c180505001e081c140690420083d191071036803601c0043d20402403001c0389007110171100080714064940150300402d001820075144034803010741070101d5580b0040c540956007000d2680320f8441c501400f840f259005040c908030304200c940c044d44508100010b4900b61064650003540f400795005408011100101003071561041c0e00c00c440d016615081e000400c0c11440360701c0c0c003030b8942c0541e415030312401c4020558810458402e0205603000c42c5841051000c0c0c84c00040e901250f0381d00d16602c0c0c100c0402c1c50380c0e1901030450082d640308203400724540d4450921345030195000764016020741c18540303031180c42c1540c44080c500080d01802c01e404920340d20304044408460904002507201c120001030880104811100021944a1358290281501d008030180080f111010070030492160b0f80c0328819100e1204a900500183e11401106814a428900c0642040480d0001803c0501c1b6002c05404c4800c01e440030b4a4507010000104000c01c0d80c0720f40310380d00c00ba0a1000d0022 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 430600539 1250 430599289 430599293
    0x905030322050a0f051e041b020c0108090c0d020409140d080c070201080c09061b0609070b040806070c0c03050d0c021002010b0d030509150d020d05061002030a050a2705100309 77
    0x805a803500400e440307490300d071201034100c01d0040183d81040500500030424015001c8c2c0f0000d041e504100303d0790144c02014200d0b0401c7d0f0007100c0141c40346800e078000c2c0030300d03130300820801001070380c1040203da0003a46c90a20741c01003184d0003890180c1e00e643c03000078043e61040c0d00c40a46032080003003102049140c100081d80060b40d00c011031a4100c50382c210303065148e212240008425014031001003440510315151089000e800184050198408009a6032800e484943e007040364890b900071420a503020f000407841188c82045510f40040c024030540704015140e40e10a820329000c90b08550000e10a035450f0015441d00d9030b81295400c100307000070001d5118a102141c0c1c6605d09040280500101160348a441d407111300b008988051500e44007070341e130400880c28a0081d0000145454110300c3c200000d6407504048482030682d20803600194207140751100126040d44c800c5031820200801200d1007010341e000302c500316008070034680000d00c00504140a2008400410207104101810840d00f000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 430601789 1250 430600539 430600559
    0x105120a0f080d0e1009021903110d0201090308040905270a300c151e0c0e040e010902040c050901170421090815190c0905030322050a 59
    0x415990b1000c2c50b00e4556a1218034400100b04c42664490349001384a20394240c1941940309035030952080f01e00050b400395144500c0800b0885002c020b2846003250913020151511104c015203461051500301c0100d5203036a541c0c0d03440d400c0384d482121116114000e100b61340109510586444001d440c6144000490301081d541e641c913101005010f19038a811010b000001d00c028035051010b400788403100b11f002041c0c00400000c1d0f8014242e514602d54820b840b0441064050b85141b84032034801022541032010800c0e004054101851f4244408402503240341e4075940900c0d481080b502c030001542d02a103006000c240d41e01000008100001040b40030351580c0c00515000c00340625000c0d030285940c5528111900b1640c030103000300c40707507202c0340100e52550344603c408058920300c005030341d803c1c1905451148092020303074520501401d0074084005e0196994800c110306401450184009a81e9501090659010040c50300e91459894034254201000b00d485800a10007500c10310000303481c0250f0f0320 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 430603039 1250 430601789 430601813
    0x61012030e04020a14041d06040c05030f10030c030f150b06030a090302030705030414100507030c02121504050d02070b0c0312060d080d06030204110309250e010e0105120a 75
    0x141c456035010520091300752180f0320141825001c010001d03540c689500210b003c044451202201c40c400748030008115041c180501e1549072900c2c1c9a07142192100320203000300030381c010500d0520f5006104000081a801d07401c800040d40200c8003442c5405060416045100d6038081d00d40341c1c2800c084045d02135455410880358003141c00c20700042c0003821454102d040d48034200007c2e04901c004600440d4414002e8800625108101d41a6070301d4440c800307003038a03580122070b005000716401c0602e203400341c24030411b1740c400311451b002070f621403400703100c90710a41c0700b800c0c2d8046d0382581c0070000510607030303404111140203003192912007801c25100c203144668a2144260010020f400000418910b440c0e5100880740c16501511003034075003011388402d00c0140b402c1d10050b482141400303102c0710b0403020401107900030b540400207000c040b142c1c0d8030554900c1c0c1d03d03030705907214004900b0f000098406001035101d010701003d04032070030194541810418581c0602c2c4a94499400021080e40000d1f2101466 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 430604289 1250 430603039 430603067
    0xc161b030201032f09060d14061009031106030a0b030f0c0109080f100c020f0a08090307090b0d110109120c0801150609091505042f0315040f1d06101203 67
    0x816903d170081004100300f40940e4420ba00c140e0b003404022809014401e01080c4100c0c0162400d641e00c002c2804210f81e482502d120180c010821902031741207900b05070000b141c1c050b109200101c0c0001a8501207494042c400c540c00c0040d400c070030036028081d80d0003920b07080108500d1004205008884001ea40c9807580700b0300c11031043d950b80c0d55980d811402800181440c0c61f5001c00d445500c0001d0510f061140d1000150301e00c00d000740c0101045141c0e140c40b42d10254480500520400c1400359118007181a0302d4a01c136060002c1d0b028005411004000200442881076000c0000d0500e048842801e481c0a07204807030455041403c103011242d030021144045071591040411800517401044848003003682242c0c0c2c22500340034400751b60354030800d080540f08500440203411400c42014a01c514001504c40c1410041002c0460480745440d400070001104a83d4001900c0d80d080c10400112100342070200c1d001d904070404124101180994900051014000d00b1034080c1c003a9400804108030a00c42c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 430605539 1250 430604289 430604381
    0x1e0405090f1005030c2d040603050d020105010905010605090d030c060510031511071b08100e0d08090319031e050121050a12050c01050103200411030c161b03020103 72
    0x14520201d070381b128540142000f0340704118560301e030f05040b0f48805c1c007100040055030901c8000240c0b4a603510a00381204c42c290341c1c40d030a040f20710040140c0f01e1220402078003001620307904000402c0e041c2c401c0b6409010658500d0f150240f0f14600340700c81e1860350a103801c02e10b1409041d154003102050459000e10f500598000c90490740d44034480c0d4088030340d004424640f2548118130416409640080d020a075611708440c100c5013906400c498070386d0308465103c007580080c0008070154000343c410101e844400c0c10041100032000211700c80d4107010404043c2c669031240b004110700302c460416400d021041c1c0b100c10b41d9400031a01c44660741c0903450030040a0b1402c00c903200c1c0015120320b090f2156201c1354002480b50756540c2c2040e80110558140e02007000307200c045c60b40c0062400303108951038400341c20000f50841d942c1d101e0510403034111240c0400740c0c0c40d00ba018603001420b41711120001c485040304018031b0703900b1800018112001040c00300008200810840110000c07000341428140c99001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 430606789 1250 430605539 430605589
    0x3070507060302070c0e1f05030c01090b030c0c030c240106050711130e070504110a08041403090d05011e0b18070e060c0a110d081e0405090f1005030c 66
    0x3c0c1c00306450456500a1b98007001e0b420030b20000b40d5180020115141031020407404c003e07114403c0507226880a600e0901080c0096001c218042c1d00c800a140e0081d0f4603500d09080c0391103035810070b0469200c0c6a03040b4980c1c0004c02460715203400c00d41c5100e000d41900e00c039282d2543c18490003a0461107591400380106000c0902c00d112503560038800e03100000740b020240554200000e03580d03a10049406404c0c4540d0504403038500800a12007502c5000d5030075564002191910780341c2d880f41c0094518500c0460008200d181e8150f00e410110520081c406c200009008051714000220000d0b48034040c40d1080c1040b40381401550344030f402300300582d4031301081c6c11237440f840d00a480c030031082c0da64981c1003807000c1221808c008002c0f407541006801022002d0900340005d0030407e84146040c0c0007841c0d52000d02540790610045e4002500c02c0d105c910788645440e885900068045100301c0310b18414810960420481414516840001b8034090f030080003210101c2c0d002070054460342400580c2c42101d15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 430608039 1250 430606789 430606793
    0x3051e0304081f1e0f0e03190e03010b0303030c030f0112080f0a180f05041b1e050904051918080f070204150906031704030c121401050109050601110307050706030207 73
    0x1d03204140c09855031203120761341c09100010300050807840c20004085840c060001b150701754040f00f00d50700c8203007942c9050140f144014003515050b00301c03014950199031701c10070461903032420001107002d0b10500700d60035240d1400900b11003510ba0140c0100c2d8507110343d030001c140001c41c8541903e012190301400a80c481c50a624200c80d0f81a4540c042400c1721901100064a1490342964a003a03d00c2600d00b070211400c100401c0701400098080600041e440c45140e100c094803904002c0c0a01100307260291070b10107140c00080035114192000c140036894142103400300a00e030b228851007075195203c425006643c0b5140c00c1e5040c05441e800320000400000c0510456440e5800070194602c103568064919484030f05440041409010481d07100c4284481c0d00443d62040d410741e01180e52282c0c5042d04181000003400460202c0d1400310f451010303100045241060a015041c06841e90080002c0c492501000040446603502841c82d40c9410410400d0003240d404140d0000b035030800c2c140540c1d075100c64 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 430609289 1250 430608039 430608041
    0x6030703020d0c030f151a0a1b03021b010c02130b04060305070312080c040e06132a14130509070207050607050c1512070809011503051e0304081f 64
    0x240300081c00d20f401d40807010320350958041c1c0e40c0c000c180f160400084070b0007400c1c00864582c034021092960640611010714244803802820f400c8018584403006500403c022501003599174000c9026800821060103401d00302200007404d9802482c1100c0d400da05a000300302c41c0c0c000d540600c11059165041c00204c0c1e200c58100d4001940c3c440f084598059aa003050300f0340203e6030382240001003200c0089030254450000b56010340b00c42060313414041d100c5600b000b030442d003200c10031040d2603220544000c101c0030140c540d90704002c000564001c114100b40c0000e0182c0d000c1001b4084840301881180c0403c01c503142d0341c10594100b40c85406840d00e402200380d20308082c6074002039008000041c8241000000b0501b8240c0700025038505155264080130201c0034001d07800c2d008a2081d4a500054106110b910440d4000c83d0344800082c0024504502c442c1e00e00080e08143e400fa0b000c2c3e00081c0c40c130211b07459505075400300280550f090504104441f6160031400d20740095100e203058108140c1015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 430610539 1250 430609289 430609297
    0x905030a0501140603061b03060301151401080601020d050901030513330b09071b050d02071a03151302221d0411121c03022d07020603070302 62
    0x1004049481510407864964040c18a4001c00d0822007090030110b030650a0010740380d8086c01c0019107207030456000900d00c81117038000503c42d95056480e20082040c0410300c00c0408040c0c081c10654000000e5640000340c05120043c00b10ba045602c10340b11402075a070b0000a48407114000d19011070692260390910060300c5200c00040c0611103155814405090031000c00004480c4102038545e02024541400d000c8401d46019140c012003c0c070005042548a4424191002220b2111180c110304540341d0034540240907a020000d40d0020310140460381d03003a60400300b544c0d80c000c0d131246140b40134800c81300c196000340c1c910b50184461118842030800c0d1501900d42c40d984e00c842002811140d07114259803800d49110b22903801003c0307009a05607599000b407161080b90010301c00c114840e5030740b0900200b04d02920340d0a5044c020a410440c2a010b0360055100d0110b941d503000d40c4400c81c5846028024440e804c1c0c010300044450036910740202d020382503c0d22980c045840c42c1d00d03a80c62400a40291203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 430611789 1250 430610539 430610549
    0xc04111206090423010b0915090709050307030b0601110703030914040203060d110333060108090705150408161e0e0a020306060702040e0a0303050a110f0706020712030e01051012030f09 81
    0x551f0030402440004090f8842c4410500300c0b1114220389942d802076844082a01031a45c042d0006403003480441c1c03c0c0e03034029030002010f140412103020710301c081c107082c0125604100c000405048042084a1840c10868000d00c0c04840451840c18080002480d078240740c10300a004072500c008560155800b0300040380004c050041501c0740c4a0184460488414180310640c13081c040040800d886500c9103150070f00c2815013100a00da8182070104010011102d070070b826007400320402004c601d4141c10300c02485040015142c40c8061810050181e102c2014501340b003140e10814502004a80750740c944523500701c00907010050740c07911504049440c500c03a29101942240c1000e40301052610001190040310f030003540e0400c03150700c0d55844103050340e00d100c020702c0c0424020700c54104070555040040004501c07071000103140402c5903030f8100040e10010000e03c080780d951181c1d242d400b2828000c8691007100c00d04001c281c0f5052141203120604002405410014581c0c0801491070142294001401e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 430613039 1250 430611789 430611799
    0x501020a0b0a06030c08010504020411030603030706150b0a0201020d0b0d03080a05070c06110702010f030b0d03080604090605090d1e08150a0308040803070507050f0603060d050c04111206090423010b 87
    0x707441d0510b480c0640030075603040b406280b4193310759850b942800d003640d00a060040140d0304c0e01c1350039161240035250810001b1300c0d8022194001507a084a180240001681074001585131445010a42c0031140101e400c1c600413003540f4000400a82e1021505034020b008100000d010348a10f0800c888000c56810010600e9143c0340d030040c0c441d400c0b030700a07001d114801d0380e400307010010a402c110103658800307803005d4000d500c03400b0500000340285207040d0b11804c00342c400504000e0980320030094031011380318003005811601034403180c03d07440000720141e800c0051160a00da020400014840b04004103014090400c0120380000ca550f4804210020b5401140d62500c8603140e140003505c80e803025608640510403084c000515041903004c13403660880042c0311344d040da55414148940144044011102806100c0e8071102d569121302c41d48500c003940d454500c2d210b00b00e03144203a07501030016011510071281041000009107015418560500700c00100b41d440608200706640905021200c81d6482 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 430614289 1250 430613039 430613063
    0x141602031006050319050607260a1d06040308010e0c16030201060920030106080603030d0c0504050109060e090601050c010f0603060e06070503092a03061e0106090501020a0b0a0603 79
    0x54400c1d60441e4003030f15811001d480c212420fa802e10045458a000000c1c140d4005e0070000d01c0d114000c0c000807201c04030b00101141c188a401070000e401000c100d0313603803440303599401d00450300c0381804242900c00a40003000b0322442c00d094030301520b089414807500f03e040e111140000c1408501c50306944400800c1402d2000302955468082c0c06441e250103900f401615002c1407100312601075424840c0102c0c0c0340300451450342488000ca4115000420003501484204003540215145100750340108a4583d01c4940312810040010181c0000b91b100d4030400851241c46c007141c1d950700c00c005401410900741155940203440b00c4030701601e0041d0140380c0c0107203418000000d00056802c1082071245080a540d695034400f03070140c401d804207032140581c0c2e500c11100107500f4510004090007140030101c00580100106e00028034003542141c0328648540415010103100c0100008540501800d0404000d000c3c01c080001b0b40c0c1e640c2c0901e01503c100340c4c19011541c65940359001c9406590000e440650f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 430615539 1250 430614289 430614313
    0x10e1b121605040e070f0806180402060d020909070309050c040e2d030a020f2107060f060302061801090f06121a1c050d1b06050403020c12070609120314160203 70
    0x4052803e141c03580129410400091051030b006014811181a2414109c0151111340903c2000e40090703516103030655003003082564541c1c3d29140c0710300c10701f22680d021030654850b1070118140200540150300450030b010380780103030b0800460b0350803480c07609500f5460580c280c01585d00d40817075003c980c1c1d091408000340702e1041c44c0e03001c180010742c00c201c6021141000041d50706801c0441e445601e8110404c024800080060825041040055000f040200d015522500000c0c200d0340701101819080d02130908880c119600306070194002c014031030541d0100c0e8942140904000305103008049181d50f6804030700109521008403010704c020281c08012040c580440107024032884c01d1080d1154800c8140e5a06140c0c850748501e040e4090444041441804984ea100d02500000d84120152f0050000d60407054803050030410700508008020504076207441d00280c501c0010341c0003130100c818400440710200340c04c40002155540c10002c8150340d407442d551484204400180005d50500a2040a0300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 430616789 1250 430615539 430615547
    0x200c0a0c0603060608010e01030302060711010e060a1e0510140d05060903070201090906060f030c36090b0319021c05030d06080f0a020f0d0803010e1b121605040e07 72
    0x680c4d10030b495502941e40c030f84428142280e001d1000600591000001900052207080e10b00940c984200010903111209100c1c61700303000c802c8a40041c5107994445804a10b48503008240002120038400c0201e4205a201075220b8820780c011244900d8144c10a88000d403205004010803a0700542540d1107424410159070300c4e580020350607400902c003003401091001c10f61103100111001502c9003c030080c22608294042c00e0840402c0050002c110007512204220a420f00c0c0c82c265986402d84800321242c460301f4818095400c4040325514000302c0801e961400660499a00e050303600c4001801428030006502d194201e40142c00000420309040410400101600000302d1003401800210344038403107980c0c1e032000501c01c0c64065002041080241c10410341901c81120b000d021884503410548520446500a90001d03810707c087c00200250507110b401301c1c1d60704c00350742c46189103031405407085a140c000014100000488410014024150140c82120028020303203800c0a510724101c407000e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 430618039 1250 430616789 430616801
    0x309010504030e030d081f0314010504060609060e0109050c13151719150906030804050306010918170d0906020705060627060607020607050f0c04200c0a0c0603 70
    0x20b010400c039040031515841e001c21003081c3c07003138a6034070002c165440076090b90291100c401302ca155449604004804658465021b00b5494080c4001196506141c83c20104030713040e9602c010001071400d0741c28854100340440f464111f800c2a44081103544504021405a125800d0754080084005c1030005040500201c508130903192a00e68051402c51590040403401c0d04407000c000303042e01c0c07400c80860b114a50307202c0001e64000e50660400c0c1034541148804a826a030001d940245021804111602c1e04006550141803070701c0c0b041c085519a04041041e084070301d000100701d08140a1540b5509030310340b0030356400d4070350034405000410b000d0410200950140784281c03003034040d11000455034107042840c600070700040d481094030340506441800b0001005414140d01520811010b000741e55000090040c40303020f0340c081c082a0000c141c0140c40c00604550305400380f03081c48102a00c055021508490303101200030525502c6821294841c02c0c412a03520041a004600c0008104198035038000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 430619289 1250 430618039 430618043
    0x1202090415060f2601030615030501050c040314120717071b0504150b0a030b0a030515161e0507060f0615110606030307020f0310090615053a080309010504 68
    0x3000504030344c025080280107124100601c02210100104006403441c1d1000d64804440c5030701c0d98403680c036680d82a00303480007a5a0a050300350041810f00901550001c80424085040f00034000d0040210107041e440c0500c505c0034082c0d2502c4040400b0000000d021549825448020509a005404000c240b040340c0c60040701c0c01103140c030101d011a0780c05255040159030404000703606048600000710003605803742c466030020304a48002001803000c020b0030f000e1400641e0300101e0b52501c4c01c1d148064840404810f0108201d400c0d03551041291303001100f03c81d0b41d8074a025642e0b07000034140031014000c011301c0c0c1016280f4100000400d40450449140c05010a0ba1403581d071403188030ba0b40ea600c100070354031507526400c01c003c101c0061402030780303503410494080e058450000d602c507140704c216461483c0a68580341c072100c0d0a0500304035101914040d11044a0609074214130002d2003440381c00200c401070f2224202603840d130280d5204c600c0c1b50941d0780e10a060070344d00e18001c4038a034041c0c4420386003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 430620539 1250 430619289 430619297
    0x50f0f03150909060a0f0608030705010c0201050f2530060618210f05061b120f0705091518060405090a022109010c09090c1202090415060f 61
    0x120100c0d181400040707000d052900f00511054941480c000001d044010303101014a40d245800a0720b000c0a2024168890240300001014030700c4000190075240003d03c0f100d0300d000510100314a514403090685055080b40b074034401c2c0303100c0c4408140c07922008d99015503500c042c02c0c0da805588080000b918002c1807600c080501c441903403810160740040c0b0714040702c1004000c0e01c1080c014050030099140d080121120ac8204041c0c0980b03e4000c040c864050550b8180c01c082c0070400960350611408032040082220039140c80202403400d40310038400740910306550f1124020600b41841202134500c80300d80200105100c0c0132004c1034001c03d61000c5c040e0720b5000c0d1007880111685c43c06205170740c1118000740c20600303a076441c5100840207500a0340724046488900d24071041040b4a002c255100d405220000a500c0c0e502080103080e4070110740c81300034010304156002c001c0300c0c3d10032005910413a1034400940c0303a40261000070082c040081041911060100c400a1300c07540c0001026411600307526 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 430621789 1250 430620539 430620571
    0xc0d11100516030518060a0801140901050105090f010e120d0e120c060705070906030b0103050c120c122b0807020d0e1003090605040506070f0e03060610050f0f03 71
    0x503090341c46004031100150b0301d48100d019040407030700410003801d0010b00d050408004004000000700c1640294504400280b15103006000420444101100e4040100ca4504d195850400001c4c241e100b000185802040c004040e203440d039009400c40c0c90030f001d0003440c1c64210354880503090382e545c0b03030003014800080079000501650704180d0a0700c4400c046540103003072480c0c941001d000e119444104102c5044c0f10714400051218030034880c2030055441001491059459030034124030705202c9450b000c0c42200b544481520030400014648445402603407910140760101c843c0c1400c180065142c0c07070300301d803440c10801850780ba8840741c1392b4420015103e007602c0d034803010412030340d44001d01c01d420089000d102101d082031030800400410502c0e286008520f0700800d90b6480f0580d00c06583c11102d0382e019406210341c00390801c03141c07501601715243c01c00220b44c030100081e0340c9181c0901880e004120002d010101244246c0840d83c024080109075903950341c0b070007840d4a403544100c6481c0880f480800c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 430623039 1250 430621789 430621819
    0x60c0f0123060f010f3608011a10050702091303090b040b04030602030a090f03020705010e040e060f1503060114010207060309050c040c02010b03120310090c0f0507050c0d11 76
    0x69241d5000b2240540300c100c81d0300510005542811001511100b404214400040702124040403820302c0c80c0020120308140000d45000e81074004250000c13043d40c0d04000f00000c0c04401e50500040e0a1400c1301d0310f2039801f0419a00f0740b410301c6000c00c00381d00b00403242e0401101c5510b10100b6441e5510a60f0350040d45981e83e840c100c0f880c0547d02604680d01c408020420209074076401454201060140004003102c00e940e580c22051031800c4101c0c003503040024204015a082400c01c2d0342d546060718240300c42c0400c401042e0300c46500600c2c80c1104030005010440c0410108001038500d04060102d40755540c58044101440c04004010350052090307410206050313100b4001c2800141c0d00070004d003071403000f800811020f0000c00080300308540da0303028642d44940e02000303184c2440380117840c01c5a581c01c205011200052090700b01e01006803c08400380082d6034040c1800740e030042107180c01ea0300e68003907107003003400d108034030070100da100b526043c1001c00d101c04100300c8808030b0b00440341c0c0301d06c2c0d41c805 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 430624289 1250 430623039 430623101
    0x150a091508190b0c0a14030f0901050a05150603040606050402040b030901050109091a1506040b0c061b03041211010f06081b010212071b060c050f030c0d030209060c0f01 74
    0x4414000e001032903c5001c5220040b140c4044d0014035a241003400801e245c80c00280c405030011618146040446814004510700070320503141c025580840c188280e1400041d0440110914551f07070307000e40c500100143c00d10910394411405040010400d540c3c03240e5a21004020707030001d846102e0705519000002070400c0380b03440340c04007a60f0300602607100c021070560b5040c1481002001034402c500301d50340031340c259550040200084c001c1001e941d42c4840814010074900b25008100c0c160f8646014030202000718850705a9074060790001c0301503443c5ca2140030803078001c54440c1409100f9801e041c0c1c01c003a200c80710b4000b5020790780a4002c842000501121541300071814410060158002a15281c0424107920060a0040c0a400703065400b00004c0703a80d02154089a00801c006909034a081e410810244010360000100d0801541402520320800c2d0311082c502c0d1014080c9540000c00005d961140001d9039001c1e1130b400140c80d20001440003550103040d04104100c041d01140034000c14682d81 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 430625539 1250 430624289 430624333
    0x108070305040f0212010b04050a0f06060912110607080a030501030b060603060d0809040e0f010c020c09100605090109120506070e1512090715020c011214150a091508 73
    0x421114090f000c299000c1c00307a00110402440d41554a0308980401c1d43c90f54000c05001c0d0070210303400a00302c0e500c081d04104891b81e50f0443c030104041d0000401c400e41d4000c11060440e80c0180c8000905c64007600091003520450800a00400000c90030705045038243d0710485c12203005602640881d65140200150b62204540321a48140b418112602003044c510250101c18000f40c00051030f18414082c1c0c5140c0780500858002c0c0d0703910340b101c15068035414440c603070301d041003505d61051605000201115120490041c0d004010001c0340d024a1030788501100d500614040301e400d140000d503400e00d980c03102c0d0100da600c00400d010300a40031950400001c228070b017904030346145043c81000c8114501000b0050002d8826109180001c18181e1050000d0702c0a015282c0003003030441022070025141a210140424803a49000d00030b40301203043d0754299503c2140c09081c003161030541400140340318103941007109214900785032010240001078807001030360140000c540c2100c819203105080003074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 430626789 1250 430625539 430625543
    0x9060503030d0b03160e0a060605030f01060f0c0c08060f0106050a0e130905120a02010b0612040b07020a0b010603060906050301020a021e070b12040308150604060f170106030b010807030504 83
    0x700400001d22107602c0e030341c8201c40c0c8200080c16202048407010300000343d054a03401c006400d0036420184400b81d0103501c1040000c1c140b9041081c11450301924102700c1c21014030440043c4001d00100c1c03070005d4402d0003c0504039a1098034502440d482e9114556510300864140d20b4926a030400815030078000c00564507511005c0c1e03214107480401001b400014155040308607030072a190052600007803002c3c4011407401e03507401e0915465000282c80207080d101180d40c20f0340151001c004800c094540448025401600300203030300c40c0ca45441c0d004918140c9085009003102c2c84090010548540c10340011003260f549550500801d40c4840c101800c1344a128194805644915051001c0c0c54440810220a02c0b141050310342095450002c0d11096100074424948403c07404200030030941c02080d01034109480c514080d1854083c100031170034030b10460080b4003e000c01440f251203800e128441c91480c1320560141204c00d940c6d03e540240203001808151404a0210790005402c24404e02c500c51044e6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 430628039 1250 430626789 430626793
    0x1b09150302150912031803101503140a0507030b1e010b0d0c110607080a050f0708180c040608030c010621060906090803040c150203280e030a0c030c09060503 69
    0x880490b40d159481443c1142e08400d0000340d140a1420034809012583c4074164504101044441018100404440441c071001e240c851a49019003000840e0000c1e80c0d4403104c1a01d00804440c1c4891501c140c03400010864802c0f088040201301d032107040345024020040240c00c02000305903081c40f4071102401044182d41042c00201d1081c980c64101c0b6a4815103400c0c64407408501c44402800d00b401165194003181111060141d80c1c0344078450036601c030000da01381084030705062900820340c0601401034410891464003140d4443c00c140b0406400b40c600030b000700800c50361000307220384039000041d00d0072155281920014281c54013001d0440c1d440582c50600740c07204c0789581c40c071004205103070054030143d50307482c1040001410040218003c601400000602c546004c1881484c032007a840100215003080c0821881c030b548520240c0118242048009205201503c040b15580c03943d0383d550b03900d8441c07485d0420a11482c4425003007903e002e0300c2e0085c013032a143c40c02c80c0280d8109200d207903015 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 430629289 1250 430628039 430628059
    0x9170705040506030f25050a030309140d0302150604020903010f0b0f09090706080a09080a020102070c140618040906020a0c030905040618020a0207080d02010f0f1104031506031b09150302 82
    0x108050090309030103c441c1501a586c101d0f1140c000c101200750941048011440e9420b040c007181c00300d01c000c83d65201c2c0880c1c85200740c0b400c554009407036401281101101d2003412001c6610350361180c045e510000b84c050002c0000400790b665280c0548031901c03003030740a008082450302d420305121543d5031281c20701740d000303100d402e1811104940e070f03c0000704645c00f000c0e60f900d070000000700420001d1081c51010b03800580c4030100b03401c004a020b03040d0352000e148200b140b5142d80c03054860209544030840862030f445101e12980340442c0141c4104000203200d244000780c583c4140b608003150314821030196071030300e100343e48441c107000840300706008407003081031100e410b030184d920721b40c00030901c1101c03606c19075140d1a5150400d5180070100c0b4a000050703515120000091803951040c8d01d141c01d2995000d10611007800c04000c3d941c840c0d8007001d041c4110611190160300b003140c00ac20001c6a200d1860f64050000365454043c460750f038001c0c2ca58140c02c1010083d1248031088100d0300f9290020704940305 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 430630539 1250 430629289 430629313
    0x30609060b0301120f020405040b060108060117180102070209090d090b07050a020d0f0605190e2803172401020307051c02070308040f08011508030f0a09170705040506030f 75
    0x8404e00e042411140c00030540640c00040c2c445000381130045214040007501401d24900140040c1c600601c024100710b148200f014100c10440b44940d00064880242c00c0f4460700940d10b00d01a100d03048020b9040740203d02403180320500022615183d1903290346d842c40c100d03100c3c1d003804410300c1010800703080d603480380c0b01c100301514006401986d482d100701c0c1c0300700d40c25580340d4803101500c204880c920001d1012003280c550b814002d0240d00c90b240c40c5400503011044007070015000142c0031009440f171614034241316004141c0244206564503d084035403180030b1501034032000103d00c0000c48207e000b40203e0300c9060650001082d250b5955001000c0c0801c082004042c406049502689004610990500001141c00e1000420243c1071080d41c80480d5810000820b080d00c40702c20510710440800c1c101082121000b006030364890350b61002c0e050b41c40d200c0c504100c130000202e0308154000111403c80c0064404001462021114181c90500c2955180d03070802d605c1e03003c0c000e0050f1040d0040b0304500c503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 430631789 1250 430630539 430630559
    0x127051009031728090305010506030f06040b090f1207021801060f0c060b0604060503040b0619091a0603071707230d110316020708030a1707111b01030609060b0301 72
    0x140641c1c3c0302c00d5001410828181c420383c81c0781c0c040d400750219403910000d0080c0700007801030303941c858800d2f0000c1c803001004050841d0754400080019041481000c00700d110746070103225011407061100100c8546104d064103801d40c940c00500224810006442c80801041c450b02685041b07981c2c03030300c40343c800d0100740600303491a440301c6a048403416601c501540c0d5564403031010b48050940b13a40c500c0e49900e050700d810103101c1400742406110359612107a06242011024042094891001010800c1c0103205044540951405d4866170703c00350110401480c80c0d800b45505801000d20480740e4400c1e125030340152120700219280402080060303103420f220786001c4000703003001541d55100055503080c102030800b06030000e035035225211901c075040c1746c0d09682c100070b44005040d40c18044c0d8640b01010340d0140c081842c003114901c0641c10200018186401a2603c0308a440d1503801d994a014402c000503042464690446020929010000c102c00c401403140c0d005880c000303611140b450f424910241c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 430633039 1250 430631789 430631797
    0x70f03020306030a0b0a0c23040303200715080709081207021201020406030603050f0d0804060507021504050102030a060f1508040510140a0e010e0a1101270510090317 73
    0x140e00351003840c0c007003400181001169407281c080300c400005c42c0c24204000501903000025807505905950300040c00c8d2580002c1110110303a80f5040200100d11480384d203100d12000c5010410082c01010310000c0c001c18000a0b040d40000c440d5910421035581441c207880822941c0a12030f02903024a00b010641403e205c02060f03140d00090840c104900040710a0342681d209810402c00651100020410464208104031410203054060b0094802031080104015801000034003010b0311100400c0719507000344122031901c00c0104544410b0300d1301e400c001303010754800e598a40080b4904000002c4d0008012403020a0310340c818010508079580c80c01c101c0740420f0240054805000e42c911a0340141c500341700390a80c032941a02120310303920b8a080b0290840364003c00303181c40b0741d050040c2110703220030100390210480c0d4401e20210070000e6000048600000c821020020200003141c40d01101c568101014101d500498840504895800048070780000d03500c00140801c101001c48520503032200082c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 430634289 1250 430633039 430633051
    0xb1801171906090501170d0801060f140c0303040302060609060409020108040b0a020408070f0906091a1203041802070c12150c030b2e090b040611010f020301031b0e070f030203 77
    0x2c10119220740c05041121420f81c0a0b9280d00d074008001d80b00f448040c00504881a103600b0103422961411401410118400349a21b041008864117411501385080540f0351030310030801201e0301d034070b010b01e800f80d900c540541704940304481c1200007500524103400780c4898207506a44144207030f00d40e540c9010204030003900d0207a4694007440045030744d5504010610092a1119810303402c10314000c020400c0b200240c008000340b505000c0002d210000e0220311907400318003540c00319400340440744c00031b00b5030050703401c08121915040d0b14040c0b031003540e0700541540d5001c0e040141540d41d0b21405113409820064006060071664103004449051950085907107506904020031411040c5000407142400340d001c9a030081c03420031711076040007003004440401d80354a05080c01035500341103281025000d1403081d4410051030030520640d0700001c4d000352051040c4000c0035500c81d6105d181803040084040c295000005000a000449107150504d0601030003207611007052030700d00c1d0441140694030007018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 430635539 1250 430634289 430634291
    0xd0209030a06110703030e060606040b090307150309140c181b030a09031701031e06060e010e06131b080603030913020903011113060c020a09060b18011719 68
    0x401d00104145000b500700041d0381500c056510000c910300902101d01c0c1c428055107540c0f0220030401143c403040100c5043e6859046c1d02134480310080e00080c501200740c1c001a5641c0d00c8071188800803034040e001b802c15207120754810840d10036104407041d602d5100007031490b40304400502070015503001c000b03c1a0000c440c142c0455400d88425a13a03d0182e0080e121100a59074580412007131581c840e0403540b8411a032015130351994519100d11f80e14810364000390020502c07052486c41000010f82c00b9000410868000b00070395070b540c1110000c5000c003110014042c8020860380d154408072032041c2c0c00341c2c0705055078000d0f0111842c001180e2141d4000e1045030148000c0004040f00e6840b800c0946042d21050760160380d03101002c080c50309407466044004e030b0f841424014405200d07410301109060b20358519101c1203044a070700010f10341d00031030f0744042520f51811401142861008009040c0c1071110300d0010064202280115403d5100b08890200c91a0040c0800c0d42c1c0e410744078810008542d5208 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 430636789 1250 430635539 430635553
    0x20d0f0f05060112030f0e0a03320c010906020303251704060b010e01090b07060f2c010c110c090c1306080105030f0d09060c050316110a0510050d020903 67
    0xd07401d07240c00c00a070002c01c6403c4403a8950340030154410b8014940c00590325250819400d004041240d1030502d020040805030000c4a203540303401500040c2d4910382d014205041070200750b1810549444103100c080340080e015900c0407481d01d0001046034020049140702d001486e080036004100710301c03c801000200708a00181c642c0381202550000d009a001d43c4002032420300c00c000140c51074600d1140d0505101207886c0c10404003035207405590301c840e0469404900c2d4030160b200103000b0514072503280b1035442626000844a022113407940484218100200701e12841c84c081581d0201013412115001d91145040b464070303040501e130498003c001d0607241c41c1003070440468142c480c0c0090308203074001080e590040147e0715007046404074040b20000500514621000000c0c507481460061a040c0300a10280070708010042084948440c0080c9407800c804016140070782c5501d1604480a2207501c05810108480c904070b00320681040c41030712042e14125807007a8801c040d41000c542d280c0e25001d010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 430638039 1250 430636789 430636793
    0x170601060c0609172713020d140408040f050a30060e0a0302100504050325080d05250504181b0801080f03040303090501110f1006150309020d0f0f 64
    0x9000744200314500302503604c1e60b0745a0300c801014a000170000003480d00b41c400c4180380e91150720722920150b5110303801503951492040078001501003010300701b100e45080703000c0109015030180540709959246680300c001550b2402008070f15252409000002c50940700003030300c0c2c03002c02102d81801d01600301000d699500d050301d56108aa105580118907a004124600101517051008103561984050200260308140e21a19075a0140c0c80c50756a103050b22810181074400041144a5510740c00304035156240d07449444100640001d0f0b03030940c802d14003006900d0300d62078081d0f41da080845041d610982041d0ac2c1c450205140ca070f5402d45c02c0710240e911599031101f01882c94505542502c01e40310341e051b03540f4000d5090720340b11030040e0321300d0326130820b120610010354010785010407142d091170300110100c84100007a0070a004088013036054451780990030340486580d000304040b00e4a04410a610410480b81a0107407031601c84020360000070842e01c980058071518418800c2c50249a11684040e07039a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 430639289 1250 430638039 430638053
    0x1180e0109080a0e0303071707260a0f0e01081b09060c1506010c110411160b0402090907140402070c03020d050102040f12050a032025170601060c0609 66
    0x10201511a9000002c540c0d03c0c481c1c00c040481e9540c0c405400442c0b8000203500d5808a8030340114003104650400220325007030041c05440810a41701a80c03100c030842c11101c01c621303c564400f00ea06001314084900c3c11018a003e4401c04800e018103856a20482d641d140010030144940a0b60740c10054040c002a030640c0c0703905014000d000c0704070004000800030080400801000100712604200120340504000307640c001038040a03680649000c5400c03d030200090f030080c020300e110390004c21a848000c60501040c050100d000f140240c5490400e611030343d84280d19485240204044103407001040c0c002401c00382d00a0440a01880001c48082e40b03a074006421440790000603a0a0782d00803400f8031072410a40ea140d0024075100d0341c8000900501d60b07456171110315040000c0c050003d10700e85400b0441e40141c90380d1001c0044021381d00114071200b081c2003001d01880c10460003140c804400300d8599a120314000c052001c10008010076880c10000300c42c00c02c00c80c40c00b00c983e641c071110010005015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 430640539 1250 430639289 430639301
    0x10b06121602011e0905010f1b0309052e06351203090609010c0507020a0b16080a031a030c0a0302060a0306150f1704120c051f0207021e0901180e01 65
    0x18600f400301740868036003003181c00c1d42c200c4005180ca41d031400300195050030750240c10114482d034a04011800d000e15007802c0c0d0030301c00340504295a0100d031041d040f209400e07101050801249034502008400d480d5102c1d43c1c00307034804150100424084600d104401000c2104210740f4040303070004c0312450044086040041d07001030307415a440e94000b0b403d21029120070b002c1c0c41c14404261806a062080c20b40014a2141c0940b0450421038000101144448106104208601e40110a5076621051311a006000f041c520400c081c4040703924040c50b980e490003040010030b1401c01024495078074119000c21000d544200852018540d407041d000450819549004909403c10303141c104c54141501406000c0d0540034010b100c880c4080800c101c0020040d60601c00200001c1c07400081b00304941c07a00728a0f146403040108a1743c0d007181c55030f14010f031007500207080040c400e40c3c021801c203803580e040c4200d0814010a181e4030207490070044c010001c104030124100004880c02140b00f0350300a20702401c41d50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 430641789 1250 430640539 430640591
    0x415380a030209090906040203030f0d09140303100905060906060a0522060e01030507090e09070812040302181302040216020916030509030f040b070f02090117010b0612160201 77
    0x60086000d00f5a460006035082e07000f101007000e0301c154901a800213171030707100305076070206550004291a8104c0e00c0641c426031503079500c81c1e05607091019003002d1503641e03002111500c40003050080c010909800a00917207009882c068400c400c652600c0e010410310390000300b212400c1100c03d000c00070051070000308070000601c0034608190400d0504400400c0c121f090b04006050505003401d101404d0341c00b84415040320491034428081d5210460b01c82d080401d5588502c0b180c2c400c0d40802005841c100006100300d80c400c071484007214500141940c946801255080c49150b0340c3c0c40b4800c05410030340c0080c100d1030000030050035010302c0c03603002582e03407030040da5640c500c2180c40d0b0003000740e03641501c6840d4006039180015400e1500d44440400140305901810f01c01010114001c01084400c0b0050350355640c3c020311100c42c1e9030b1031345034242030a0701100c4054550340c00c1c880f0880f91418114105e82448610b84002d861075aa001c910503c19411104070100315940c4e480c42c40302c0503009440b41c041d412 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 430643039 1250 430641789 430641791
    0x302150909040c06121404020d142d01090804060f05120c0c010e061303051c020307021609112a030f09030c0a050a030209071e0e0415380a03 62
    0x5003400d82c001c004024401d40a0022031802e0a0091086c546000c1c15030300590464034444650810300d00000d002d880146029414843d094240100d09440c0c100345900300fa0144480d05103004000155080c3c6a00c00000340a40c4070803c000e000c40b610911b504400510706007403e038601040303e505041c0701501250741030407005011440b5000103100b8007406813501e0031b035801030a5504003081c4c00c8540003060340d001000d0100018a4140d03050346d84101c483d050800b403404541340e24040301c01a45a60216900b560007000000307001c50010004d200c0e083c890611200103900300382115400700c105440c0105030351008400c65060052500c001c000819101400e0780300c140e100c400f10703000d02d45400a5510110b210325a4114240702544071a18040122601141c454002da11180c0050b2420307284081d224641d04103040d85070b51002e07005003d070544c800069404100d10b640031250540c01c10100c3c01510b0300290f40c604115a14200e0405c0d0624524000040103d1030022408001455000c0c14000c004a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 430644289 1250 430643039 430643063
    0x41203050c1c111009080912010906180b01081f11091207090e061317190e09160f050f0427060f061e110307060501080706020d09030215090904 63
    0xd918240551300c0d07014924a402d1000e0742c080c1c3c1e580300150003145007540c020980c00d0340a5000400075042410307816040002080f08981031041240710441c564070030303121118003500009000034001403480e4401c003490508040008980d8400020700015003c5500544060203082d00e9030744c0d070801c2c2c0401d00c4039180c01015090310740100602503070043c1c4010199500b180c410880c00d032802d0700c500c128095001090329031a1401480327103102801000340340800342428180c10040283c10949014903100200e400e140c84d517a8512000100300708183c0300500140d0440301c00340606008002401a40b0409481d1509080e10f41551084140c0415055141c04204400c1e00720003094511811028200c6400214000d500300407003c3c001c4501030125040110155400c1280345101e001d03416022503480040d00d9851745d09003410005014207000380d145a0180c0440001c20500028156224844a03150180c0007450b40d001c11a07400c00d0b4444c01044000100710504090340d40d01886803140e4414400c001c62 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 430645539 1250 430644289 430644317
    0x10b040b0f010503041e0c0602030c060f04030c02090621011d060c0f09040204090c08180d0f0c150207050a050d0509010507060b0411032703041203050c1c 68
    0x1554088440d4074080e1003407805264a599100b011264825080880d13907091b04078001139503000c1c0c4170086001d01200510700d404503074603902000900300718140340c0031201140c852a504d02150001910010007040700c0d44112001400c05917513095000b1401003a14561030600140760041540b0240c2e4071800d41d55901c043d4655083c0740901d65800401c040040c221440e00c0d8916200c20301c201190f5880e03200012031040c03040e9541d038040714050044e002040c09142c08408014024070b00c01c0c0c400c0c0440c00078482041280b12000100f0821150a941d107002c41010808815615120b900109a442080501140303202c028140002d2807414803803001800321084d28104a408c2c12814a1400e0401c50304200380c51550f88d0003010f50714a140c025500007118212140010001e00901a4120b08140b01104120080203404400c100d0340d117240102e00400410000001d440748100d01075180710240c0d0a49880210b8410000b034080c041c00c52044a0002c14107010030000c1390140e2805000207074058801401c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 430646789 1250 430645539 430645541
    0x30201090b07031b110d03030507120504020f010e122d0708070501051804110d1515270f090b0303160605070c081b0c010c05030a080423010b04 63
    0x20040a144601c40d05203020355034014445036901c0c0f802d0300403449030102003081c44a181e40c580040c54000b840707070107404000e01d0050090031382140ca1802249440c0c4041c0e0114050b4010184281d60041c405000c5100302401925540d003000c2040b44c114007448181c0b611488100195100156000c502a540d203030032611a0500518580303c24808c1c4d048400c4c20898540e0000d102001d580003400d2032510382615901c0c501d100040b007107030560303c00d040c0136494a00111002c0100110030f5402402e1100c605040740c42c200641c0701e4462400700c441d402c46035001441c4240c2c0e04404440541d41903100201914000d400040fa0302d4110071600c1d0f2041104028070106403140024a1a040d4099400c00003204522804a18031a074003420542d103070000281603d21503624080c480d90712404c00ea8031502c2140b83d071134642014400c0c24909100c0c400c0015081e41c015108500d640340d00c00001c5240c10b403031a50495207844041e000f101c3cbd0000185400400c011161880a41c51942d0000003c3c40c541c02c0c41040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 430648039 1250 430646789 430646807
    0x108060115050705210d14010602010c020d122a0305090c040509030703080415020c0309090a0b0a090c1407051b1f08060604050d0b0f0c0415120b0301050907030201 72
    0x103000e0000801002000441c0400c1200c1d174640f44450081d24500c40d44410b8445110300c018100c0f0162502c0b055006a428040c1c04a050751111fa0082200395040c3d1000eaa03201d004001400200b929940d403000e054105401c000080c1030b9040c60b491211091818000b5409001801c00012944070405c1101d140b09c00c0041c000e113000100c40500c07903800c021900036100d20903000050100150000040c0c18046017810110500581820840d44e501c0c4101d9601d46903005a08400d00c124440800310f84a0000c1d8001d00c0b00e801802070900c2001c0e4984040754008040315281c0c1420710118440c550400d680c81d0b40500a21809040580322841c0d01c0c1a20880c090720481100707125140c0310b001c42010403841000c0a840c2203031824040d07200e440d40e90004046004960106031300c05170342c0488604000c119032aa0740216260f005000464840c4a2403580c1401903001e2500801d210981c5007030450301c01c440d50280850f0070600000c2906c600c1c0042803e5a0301120070161f5030744030203020021540e0007034083c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 430649289 1250 430648039 430648079
    0x1219051e0a060f0501051b0610031a060604150306050307030309090c0207080c0d03030b0a0909050f0303010305100c05120406020a14090307301109070c15050a110301080601 76
    0x80110a003024404010a01c03d80995410040c001c01c1c1c0585903e0500c4821a001d03050008543c483c0c0340000b188100131210f808200c9a00c04141e1030510003045404007180500001859282050b0601c40d900d01040c074581201b208140c1c5800c4001410f403030501505002d1400703640c1d8100da0a081210040c150b88112a01d0300855110030410001c503100030401048021080710341007400c104500b0200c01400c8200355142c1d101a1280c0c001079100f02e42e41c002c00e0b445119005840e900c129401905890740000d11018259812010109242c0c20365603201003011441801c00e08e040800310344c103408000504484c21119203500154040704a40c2010400b140450102740d128580000017010a4440106104084a02e4002081c42c101a590341e0140c24002c0e450404800c1c5e0b00149040c20300c0040c460389185d1380680c01d002c000c02c840d280b01d0054415859008600004840700d000082c0d030082070010a0116102c0da166000d4a008024800840c000c0c41020010010355051000c1c000900800750a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 430650539 1250 430649289 430649291
    0x601031413060e070902030f04050601050a030c1a19030c0305010801091e0f0813060e0105070305030f150a270501030b0c09041e0c0e151219051e0a 65
    0x40100c030011201010a000e68802d001188800c54000d01a00e003400e141c104c5140c0318004004c12200c0082c00000d584940d01070300485800d03076640e03428001e400c00d81c2d0001900a01c01240240840c114a0300c0f40400701c1d031440129841c100307243c1c0303540c086003d010382001c0001e1344441d1800c9800d907250152031302414182c002000406550346e00e0b42403d01440149881a441c40580310381403240f81020301c101c80e9000304005079070b000300030003581c40a03440b409000080b40c00e4030040c44080d4800c01c00d41d0505681034030355030700d15261018202045e40000380403c40b0300002d00e0074441e00707880340400356004003003640d201000f00c6004220421b040e9440d810000c00b0034070f800e004201140c1417079141500308010118043c0e41e280d5180200f0007504070089010800f0304180b803100030444c5c980e400400c1700551075680c04100c040c040b0421031003032440c0c1100d49001d0001c2c072a410750301103524450f80e042545c0d401d0900c040c04441090034142c40c0121040e0780b2982241214551504400034016400720301e40340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 430651789 1250 430650539 430650541
    0xb0a0c140607090e2e052206080601031e110a0609031707020f0d050309180105090a110307030b010915092d03080304020105090d05010e0d020c09060f0316090506010314 74
    0x4c110110b45d03440443c122106042c4001d09035102c604558100003409000d850848006014506402400305004048200c0380c0ba0010005020101040d1141600d62200f0400200a00384404003e1a50594030503904261020181151a901c90180307000400c0540c90300c1c0d00243c510f04148081a0400881001410301042440010707550024195010a822543e105101c4040d003802031035405410622034110321003803001e100030a1009440b5040740d00c1190025066900c1e2060700055402010506404ca075050000c40c0d0f0060190300210b59022040c03400c140c101e035480301d4480c00c1c5000e080d5000003146072820140040c241000030a400055400c1e50b006401c1d00c0e43c07451810034910703880094826240031010408582c030940c2101c0120310b00602004000c88141000b50080842c00291525845030030203d01c00907001040701101c07003c0c0141886800c0d0341740014010002e00403045240c4c180200e03070f0720401098450790101c02618419800254915010b4000b6007140d10902c0503041d03200e1031078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 430653039 1250 430651789 430651801
    0x60213230118060305190204090623090c0a05090d06090b0f040309060f050d0f051f120807020f06030403021507030608060a0f06090c08041106070c0b0a0c140607090e 73
    0x10841c40120f0718107140004080d0341d6041d020310b8020300c502c00b001110303000040001e14a88903030802c0c1c0684580c0d01071940c08580302c0010b00284001c0640c0e45400c5046400050500c00216025041c50030300360910524019000d000184452210304003212165643d205070003d001d40484c0d66a13104c0c0000702504d005c0d0905403400b802d83ca0742e9200360b0041001d654013103411907100300d0584036098185001031064191810484000e440216081c2080c2c05c0c0a45022a1035081d12030840e040303403041001c00e00100c4050b10307452a264000d1000766088220750402022580f101002944a14041d6001d4a002d0111903841050704a002c3e02000400d41420400d115461001c1002600301d04940c400003246004100a0703000342c20303641d01a00b412450860795040c0c55400c840a80e200e5841010008841001d003002c01034280120342001e0722034100303200188003a06102006280c01c000e08d08007040222060742c2c450000350311006032036200e50481800e0203501d0741c100d10700701d01404024245406520b401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 430654289 1250 430653039 430653077
    0x61b0f02060c09030a02060708190e10141e0a030b0316050d1406100602060a18020913051204050306071d010c02010918021c1103040b040602132301 65
    0x42c04070103441c2000186106641d80400c284100c856000c0c10183e15800341e81002035035900004800145001c0c081800b450080c420054071680340c00080c0004250882100c0880c2c2c0814440410300c4191000c001d2075038030807100103880b2000d8a900145650751140c415004041c1d4035401107090086d4402d10304900d2203004028418140c1c1c6098030551083e100c1420109152012151459128040e020900c49280c101c00703580001e403490380e000ca07189500c0341400b14007118241000c2d1400c640c2d05080348030040ca00590700d6a0006c07505010f449040981c0d84406051003410b000307010707c00c080090301f0003d9003001d000c1603511406034140780f40e10041c007c040e1000b54003a43e22450421030b0070707511001160f014881c0080030305680340c1c00134194410304429100a60004519443c5504a100100c507420070318010b00b614800440e040038150b40301d40c0c3c0c924140c1c410141046550035001c0c0200300e50301300c8561442008010304682c03560029440244d0101103d003914840e410028000c07000321112401e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 430655539 1250 430654289 430654291
    0x71a0a1b06200a080f0c07060504030504080c0f101817100b0105031006030c05070b01080f060c040b09011803080d050a0e070e0c0309010212010311010914100c02030c0a03061b0f0206 80
    0x10380c42c440c650746d500c060005486492002400140b80c80d043c003052607441030141068500c079404951005254000b04002600b030324030816404140b40c0100b1442d0f911447c14032400554200611b9880c82d1120003000e607050301207000301c442c1d0f1f000150b00940315200c1e00a03000c10040a003011480c50500100e540c5d0064240d001da0030034151a04a00b050851050085401c0a40c02c2800c1030302950b101d02e0016125107a40f20794544610420703000c1000100030808490440710800c4030907241004080040d19070071000c410b4004091245032001000c50208801030280168041c1c00146a06d00803e1072411a00301c1c01a2010940c40f01c07400b0300c203040412180030741007141401d04030340b41e03510b2100341406441100c451100c41081c40000008010790390841d0303401140245c84848907142c8960300c0c030954203003604d24954000740c40446c2c011558003a6680b41c40050018098601800140300442c003030283e103505c2160899958110382400c05910020015903924603c1d0102213041d01c1c0c54025581d41e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 430656789 1250 430655539 430655551
    0x40f02010809250311010f02070306242411030708030a0b0301180b07080403090e09010e061005010207080c0d0b1012060507030c02071a0a1b06200a08 66
    0x1c5002c40d0101c00b0821070403402940c1c142002440c4a0404400510030002d48422102418481a111030660180001600c242802e5008003850303491511008068440d0891224808980c5141e8510068042002c9030113024082042c0d01030019603003030303402107102e40400c0d501007121280030b01c48114400b0003114802a04105482e03106c2d00c0d800f90040082c98580c655560662a11400c04420ba100004000384940525000c070710340d99400e4000d0750074100441d001000250300400511001c9180040075030404880d41c0001400c64a52020602d00f03242a100030300c495007011070800841d80e041203c58050440f003070290011421140c0030030001c3c5110f0307000601c8800010f000a10361407410f03500900600c0c402c1d44086105880d0f092200007840c0030b1311420f00090600d84544411030000411100303e602c92038185000310615048902e035074202960b114200b248030704140c03e070381f62240000c0900d180680f9000030720034001d110180715110f00861000f5002410b008890100da00700141c44da00503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 430658039 1250 430656789 430656797
    0x15020601240e1305010501090b0c0a020918151503070b0d090302100c0512091f2c03131a04030201210f060f0801020c100b030a051e010f0203040f0201 66
    0x40701080080d92000d4110212980014032420050354540e03181d0002d0b41260f03c00e0303c4080e034807911004808140d200b803404506240e40242c1c481001400d00b40001036000154483c01500c10700d80c82501400c209840b200c0706a40c171060300600c102c0404642c010303642140114010030045241852808050040380440c40855954015a405142c024000141c0400b03002a04005803040c0c020040d049400c00305514003410180b000017140c48800240c0d034022003802c0003106c60003d240ca51104043d0a600b4054040d0740c1d030b41000d02982c0f444511805ca40700d401080030f16141d005061040300121460351000c00e51070401032000ca80c2100c1d40701207030150b03502803030700203d040c83c2101a00341002d00140111891860700222040240d101da1100c02940c5625a00c03000341c6e6074880c4058242c0c082c0c8400ca5240d90410002c90420004a078400001d210015050b58000030080d2600c03410b201c3c490a2142d2541007079803803d03801c12828400c5043c00305805400b1802d42c101500c4628403550700c94030080c140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 430659289 1250 430658039 430658099
    0xb10080f0a111504060503010603110f0d09060615020a020405090d0f05030a11040902091315050105070c08010e061501020706120911040203070e090105090402151602061315020601 79
    0x1d902da800300c50708441c61203c000c03562503603904c0004090b40d000744901340000b403402480c0410841e10705c0c03c903a00c08180c6080681032085a0960707c000340341c44001103a00503601d00e000101240e920444240062040e0003401d0118803a005001c240c1d2001008091941c020040f44140d5a401c880f116119581ca45000e948a507200c50600d0018072600505100c100e001241c00240c07142c0701d40051070311002c00e594403400385007400100401c1e900ea120f1914501b19050000f84825403090000c1c0803c14020f402144c15aa41e5843d81821265a000001c50a0708450100502c0307500ca4101c5d122002000e10003020003030f1620400a041c0c4a00100d0071460a0f00c0d82e14a4041c040c04000c08503072081e00400c11980da0410040c0900819040e44141c5e00515200b4000503040c170b080201d0790b1103160080d010030041c0040c3c0c1d1012000f60312640648250300401c040b80c401607190708010f8030300400c4a4440192680c1000c50481d4144900c4011070301315804540140240321981032480f0b00c0100c82e61090b42c179 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 430660539 1250 430659289 430659323
    0x6060a0f03140f2d0d0503070c061e02040f12020901050402030606270109090501050307031e050d050909010902090d0308070905090a060e070c03020312060109050d0b10080f0a 77
    0x1003068052140f10144100b190480482010084400100c0d00403a0200d20000d2000301e500d4690080d0301d0307030324003041c011b00000d0801c5000741d1001d0745080c0305500c0000d505600c07404041d8400f40b8284011980c075804501840324180301e07500400980300e0600b5444098425900240051005010300b6008580200106069445000c2599260b046d0351921013501c4603c050140c181c480584103290010b1125500007038202c000c1d00c1050305842c0041c018056080c1140c903900e914690304940b80303c1040f0f42c0680c040c0882d9044c480b60301c44012030303919160740f81014010081c1240043e00b044450038410014452103036903040107201a03580c1030500c1803096480d1082951002190b606c403640003440c1c4020000c480a0320780c400d0341619171380c030f002078196100c03048103c0303003180c10301340040241e4420484013240b4003c40c9503030b982c04001407501513002c0307407140c01180c0044071090341240c0e408000c109003c003458000030540c02600d030b18070082840c1001c80424964544c110360700038003503001003201116 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 430661789 1250 430660539 430660543
    0xc1c1109030f010e280807050f03040e1510080f1b161a010308040320061c0c020c0a0302090603030904020a09080c0901030b07050c07050a080a0506060a0f0314 70
    0x14200d0004040d20901d400142020340a0581219408160b000301c000428035030f4004a0000540140744580b0109017030144c3d80c03140c43d075026410654040c0f04807031080350f404c00100001e1020340000c07100603440342030003404130440812850200384078180c0d04c072100c0c0071154082456544042c400344020680c6d06c6000b04a41d001900d00760f8045c0a510004200316031041189190344114132441d68500015008086007c24a40a0000a0100d64200004c0000c6050308080c02c0746002c4c0003050344c0d0503c03101d50001d0100c0d4450600303081c0c2c0c0080c031030340c5c10310a00d13041c81021004c0003640060042100b2200006104101e203000003880f0310003400100c0c0c00c6d03480070000d03a8464440035104569640001e40040c0c0364807803905c6000c841d8816821a02c2080c20b003e203003941220f034080e80c111a180c40d9000152100d4202d03000c00000c601c1041400151940c0d14003414005000c0c250240c80b401005050542c24003030000d0405008400c804c0e810884549035401600840360404003107042418055402c078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 430663039 1250 430661789 430661797
    0x7120c0f06060b070209010b0901091e080a21091401030e070e040f0b0108030f09120c0315070f0201092003030d061e05090402010905091e150103050c1c11 68
    0x980402e2070540045a1005680d0081c5451070003120010007903079071400c60a940e481010040303400070381100c0c000c101039484d00e4010111304899400301c008249d1070b9040d091500e210250183c075084403c0c1c101016440755035405200001f407900c1d0600006003007180d80100da68400304038504141d03556112580c1340300140503010280c040004250018141820304107499034440b841580c041046000004c0c0b0041b002044032005403103130440c2800e000200f0308201240d01206c142c0c1825000e010502c011642d42070090301280c004043c82c80da098105144004c0850075148064810f6a141035900c00100d4420841d018071001c0f07404100c07010781980000310382180220610514180d04105020882407225060003040180d105408101c0390341d80d038200310048000343c81c080c1c0810b08114050000f8100440310070ba000e01009000d9050b00403002070115104c01c1101c01c600c80805070000d619003036174140512500040301021460619030800f500d134041041d01c0321036000e229a1461940b0711422104180c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 430664289 1250 430663039 430663043
    0x10c11031e0d020d08070c080f0c06070c1401110f0d0b0a0303030b031b09040209061203071407050114190e040915110c0c040f02090402030711070602010207120c0f 72
    0x11004944078840c41d40d8901000e1521009070003414940040b541c401c0344c02e10310890580e6290b140b084203a4503040d565034840d1856036199441049401c19041c000c01c4032902449056036503441046981c01c2285500c5048968002d041c0d05081840c1d0700c6801031401d54515010389841d4580e640c0403e11810020000b491070039400544942001080c540c00d903011072040c07a803d4065030b51401500354030400d18000d5003980340c3d00901030b41c0410301500b0400031503540860302a0441d00c84d8602030790810f2860308100030860320040900603070440d5120034840000101020309091603c0c84040d140c542c12030040c0110010400c9240380f03420070151040030703800e03848035001d0810802000c41c1d09201d6110000000040c01040c20200c5c19805600108111840890008040e0400103401000c00000d00407410811a41c55020301c0048480e40d9203100550042c00152126600827002c1e400c480e08248156110b24150791061019070b020074509078540b00003075401d04d04010740040501c3c190103010010240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 430665539 1250 430664289 430664323
    0x301060312020d020d08010e0429190b0a0e130c0b12040b090a02010504060518090f061002061012051005100816030203070603020918040c1d06010c1103 67
    0x55001d0540c0c010035000e100c907089500351220b02d8060311080d00c5843d800e01c140650300c00640c00007804505091500c120001c10f101c008003d083c540125048038900a440c3c0c1d01d00c0f9604000b03208800c0603030703100b103100c3c0f14015580c09140e5841d200c1c001c4000180100310f00721075101c00350340f44200f001c03c20200c0301070300400700c0c0c4a45603170685042e0025403104039811903501c600040800d83c44040040d444a2540d816034a1038501400d1200c100c4554000000c9103066000c40e80881e050b650700c0f5a06940b0400c00b08075001d03501d16100f4200700d1500144604034055402070001d021050394440010030680d030155022090400c024a0810b19050503600c403904000e24040034015075460b074501d01000c941c030020072501c404192428000030f904491000a61503400540200180c1b40640c002e800054001808603220142089207185002d8084804650120446c84141f000c108030206880724614100b4440c012450a0b0300041d0068000243c0900706105207400c2c150141d07410042680c90002c8911 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 430666789 1250 430665539 430665563
    0x1803040b0a0809010902030c012010021206061804090c05120c0a05010e060301091a0d0305070c0f031e050f010204030c0311010503160c06090b07050d0b06030c04090b03010603 77
    0xc461081e400c203090a40c00100d00c400468a840c0b41401139449168000f805070009010003401910020b240d9025280e98000e420304400303500304144510030380054164000340e9a44034480c00c16102100c0200003c1c81106c0600011009807a01d82102c0e100103015140007800d1801814588004007866005681c065049035051040390400b04603903801210070b581036003401d9200c0d001590b20880603d00941c0024040c40104005d45458015020b108804002448008003070004038210384080c54043e00070a50000310301e020040907028040090100c1840081c000b4291390f036406041800c2050420398089400d41c0700300780103040c08208400078245c402150780310364038a012485403149220a46912461000d2a511540110308a921496402228808082d5410015140c0204d00b1005856142e0f0321414030002441c50380b001405504552151a2100302051625098030301400ca030a01480050050141c0301c060079094070700b0380d09040700214420010002090042207540e0014280c14070001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 430668039 1250 430666789 430666799
    0xc120c0b04110f0405011a09040603050a0308180303190515040f0c0809161217030f2d0601030b01030e0d0806010f020c0306040b07121125020307030209180304 70
    0x260400140800554003600030f14210f0f000c100859000348134514203006c0301001c689000700b2000c0105040500200000b40340c5440352034042c034122143d8000c5020803a048140b141e41580e44000d841071040344402145540f50071048103581d12114030f1010300c0c480e11040850100108501c5251070314102400400442c6072038485800a0580d01c015480031035021008a1401301006c03076141e07040760000101d840c103685080c2803217851244458007030354071800031546040c03812003c00007140546444050150903060400f254052030090600c4070440040074a040301c0381c0030840000b01d6100009003030001d105204140142c003c5c12142d880e00441c0d005201d07803140e501e90806d0410f40506000c0c1c0c1d4118203a41c1501060341c0d107810f21038000303034181d22043c0041c00088900c28000d81c080c4075440c0202c8440d03d10b070038060984c1c2a58900803035803035012811001c04239009070b60001e0004600d44840b0711000f1a00403903160030386400081c1c0102101000650f0308400d640040c2c030420143c1046aa59036a58 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 430669289 1250 430668039 430668053
    0x111201021b01050f01051507240501080c03100c0309050106030c090507050c060f06062203050f0d05040b03040c0b03190b10020d2f0a0218070c120c0b04 67
    0x180c00c1c041001c0c92500c100300c500c070005101d060310400800a4100d45a401c000821040c0d1801924180808004200800001e140400403040040300f800d40c81004104241c1c010003030310b90580111406601401358102d81e07030750002e4007c078115070401002842e400580e6040300034042d41c0001401941c03c5c4403000040020089030305080f190650b208000c0e98983c15411540340c4101e010420843d8011004030300c07140510b5043d542c02c400003c014500e0002c2c00b41028419020300728071030141c0c4103010700c00c01c02d1080520400700e0a0110001400601180140241c5140607078003e00084810120005082140c0ca00282d0003178140125455100e00c0c02600495400708000c0d00100d20300d007020003007135190904410807401d4451170703001340048031000c42d02140c00701c07545922404d8440d0200582d0504a41400d8803400c1e0512500140640d9407160040c0a1a0b80c151191a101d4040c85401c000c40c940d4012207010f82154000081850040c03155000c50b030900c0024400380c1094110005d00c0104580 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 430670539 1250 430669289 430669297
    0xb010315080609060c093105010b19080c1213050a080d1a09040f17030703020403020f0907080f09120412050c0301090809060f1b0a1b03081611120102 66
    0x1200700d81c126619040501c0e024080c020700660400805001240c0c2c070500320341c045507c10850349002203a1081d2500b41001d0769000c2e40140202d160009a00700c034001d40030444403005d4840d00b890b000034200001e40c0844d1b44118003072492442c01502c0441e003045070a02e015244550040101d620305015401c0c8004207038800d11400b00d60030315000070107080040038039440480c090000d1454000380d0b110785032141001c1340300c0f000302c0d0160221206401c1c503112503009140212a265001600c0f941980f040c0318241c49084103241c484c0503424100003101b0361200106074400341c0c0c406d400105456000b138491400000000642c035044003c1804207025101d00d4083c0d10090064080f5210300100006050880f01200c6015006100800084086040c084c0042c5032800c404000c2900e040741c10816150000c0f6400ca080d20282c01c01c0c044a01032011880744046580c07c10040041030309c3c51030366000c40c641b0450025003401401c242c5504240506100c40c6007450741d000c1c04002c62441649103050003540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 430671789 1250 430670539 430670551
    0x503040801020d0e1504050d0509040e070b0c070e041223070605040b060d0c06031a09010e070e0909190804150804050d020c0105091903050a2001030c0e040b0103150806 74
    0x2045c1c111500302d640c0780c144c96030700460f00f18010f0100c0000583c401ca609611640c002c9400948541d894074100604010003002001040e01c81a180e403070022511b03003022038940c0490300346140031040c04003196a40d405070340001401d06000340007854214610140001d10844c1e410400d1010035080203104190700864400c62003075441240d207545d94002c1114420f0101005171812001d80d01c1440303914001c0c0c1c0012200e500c0310400d189085e035000d0001d91211026009041a0300b040414008a940c0000071049508402c0742e01c5030041c82c0c5540102c1e550340d61156640c4e40a0003d0042c4014441e0395002c4502400c102c107995030310b046091002425010782514116602e00c5240c07403844025101250700740c2410016966a485d26898000b008111000306d040c4900c445e84420000002580c00c22080a40740d1080c2d40c06000b05152440000c9070340c900280243c1454100400560b402d80d1160740c1100d09002128005002003819004138001c2c841c61800c689001c0620b800415140c8001811500c262 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 430673039 1250 430671789 430671793
    0x140c04050a0905251206180b040e03071209050d080712090f05010c0204020c07080a050d080f040605040c052701120816060212010b0a0221040506070503040801020d0e 73
    0x20b55448a1604481c02141c089420300304819050f1321919640b070036204018184d2400c9a50b00c1109a00702003164000d40c8840030034041110b040e80c0d81c0c0894020a01c1848003118200300511340a1900e42d103074815214020b203040c03490304400810700d0003500000c010304400b5181c2003441100d4980080ca551001c08162805101410b50700e0303800b441942c02c04185d408140042e0b60381ca18190042d504a044c1010880e8003580a1103124038180e0108a8030f4010031040c0010018118a0b042060400725109030741d904014801041208220180120300e41207036003c04002002d958030b040c41c1541c030141c3e8000c0c5500c500400110642d204501c0b8803260900a13040c5070348000e036030b1980c0004100900e054010409c01041c05000c0200559040141070680600070141c1303071240c1d041c0b04180c0c0303043c26004001c41c1300f0046246da130030030b80c10882d2050042440399509103a550a1142c200d8502983c0f092a21584c0c0000304202009010300545005041c0326000359102d5044207283e0010741030240304a0014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 430674289 1250 430673039 430673059
    0xc02010219020a050409080705161508011520060709051302071a071b0506070f030506150d02090316080f12030a051e191104081906140c0405 62
    0x1070403268186407450b41c01803d440009180ca0140000f9061021083d10414014440d54002c11424028012000c035089007a80000b820800d603464400400c40e070407420441800014040103d5101d9640a012071500b40481d4110b00d0740361410000c4040150f0340010b015103c03e01481c1b41d0403e45080a8900490b0090f801c0381e21807806108074050550040c0004000040c010318041a02010940080310b52402c030108550280080c0307641030119204407450750080c410801c030140d01c00c14034003106003030b03180902039810542c00007039060303040301c4145c99405000030381101d090300c840d81150390040014065507210105a030000903900b105105410990007125000120042c005c1140c0300080700e41c402090440e1039580d0f4070300042c00010408036640d20010201c020401012b104140300c3d090040c0b5103230144100600e580241c811007070341e41008078418002400891000310f890070958405100e45414400c2d20b04102c0c02602a80000e03011145220062200740b8040b10010310580d0000e640079450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 430675539 1250 430674289 430674313
    0x601060206070e010c0f291b040902031b0c06010812070308042319060e01020909040b0604062304060608070c0f0804090504050307170f1605010f0f090b150d1707060603030c020102 79
    0x254031000b8000d2661688c08100c02c1c41400c80c0c45d4050740d0490341d649840c00070101c028214004a0340040c84d40d01007980004010030100e4020004082951a0410804e003042d1596030080c3c41c051015100031700c100000da048080000c46080c0c50052a41080200e85ea00040000c1000c01a40b2140f07041d81c030582040c0458411200c14001c850600d00f020386100c1585c0d4903619428107400c0301400302030344280c80e050b000554905240321210603401100c0180168a0300004200c1181d1141c0d124106120300d6804100c1511707000b001c0110320039044107400d19101e031a45402102841181c2052040074036100521050180010252440511607a1209071241d444103200b591802085082040c4e06020010b14a170214040d50f401c0c4080c1c8194004a030120082801c007044d991500482c180705a503805c1c3c0c8205000030041615003111061080b040d10141441c04111101303c0710781c025066030644101240400141804c40315140e800c002c1c03c00006480349002029003401b814140d005220741c90511603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 430676789 1250 430675539 430675561
    0xd1b090e0606040305060601200303040c0e130506150102030706050702030a0f0305060307030210032913020f0901050c07080a030f0311031014010917010506030601060206070e010c0f29 81
    0x6980d00540100095940c040045038400529202d400c55400304003000f401103482000079502035480703121837008482c1040c5203806a00c00c02860480c1f04d02c41101c2420110700045001740d00311458135413450405040c100140e10710702c40c070103008103e2440c110401080c1640030015260301d42455880b4201000100411401c0d02c0e41580d2a42e0f050704280410001464074044060880056003800300310170019440340c2d0000d2011034002d510803a41003424450503c4d00300d20500394051040390441c21716082c0d030001c201c180a042c1c51541030000c0081c6145451000304083c40c01060349208a81c00b682d03240c079006100760030860700d040200b8104a43d0642090500017641e11400552110f02600744c07900c90745841d00050f09100d541407100c040e20214030000d81756482e030f0a081c0024004504d5003085000c3c50f00e8200c0c140e10030300444d0410414050300a9019410045094091030306440008490a01007001310f6001c0c0001c0807520200c09100c056070740d1500f0300440e04000403204601c0e5451781c045a03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 430678039 1250 430676789 430676797
    0x724230106080a0f0e010c182d080d02030702030c040902030d0c030e1203040f060314040803040c0b03070816020601062f0106030804032a05060d1b090e0606 69
    0x2904080104005118203481214000d601990038800401c2e03c4640076a07072011107030703040d0341c403902079440700c10302e11055800c0180c0d0b8224180b248210031400c5c0ca015603528030840e0040c148a891010180400d40b0183c004030400003400ca40d005945115503060070182d07980c0e100420490081c0902c420307540e21480e20780300d0490040d0b000b80180401c90400041107079076102480c2c0071001c1c4500341210030416181e89403244440d1103614015542c80342084d04c08204941141d001104040c20102540080d00b02352150300d0b00703d5132103050651603458515040409030541d820100c100c1102004010145a000c1d10850046000010000700c1d0300c83e50004a13110300707090040c000454a0044001c1d00354400044440d030314214554107500e9410101002425901640d205a0700004042010700500541e0307014034141c907820420600100e00c01c0c414418a420f928850140b0452011603095603208280d004801c00c00c072014010100703990303e90405400c41486000d411003515034100090010704011080b2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 430679289 1250 430678039 430678091
    0x130c0506090a060509131d010f02030c090d03030605030114041b080613062714071409090309130c020d03110301090b01020a12031a0402070b0c030604020724 69
    0x2038503449040c4a000e072043c0d441464106d4103c02000e26001100c5900d2003050303a4145c0a4800000c42a1101011820b544180d2100c2c45114410020302400501d054211004000d00380c5091040003000e081c150002c022551216805508100100340c0700c440031076000b4070a0740f00e40c8804101020409200c2d80201d4680144815030380072501190903500b000d050081d0321803084101158a44d0b40d0170040c0c0c480b010f84010b1101c0d00c070400304130700d08000c1c00d20300d15643e9540d450000c1c032106240030ba00030002011080d580d03004485034400708030a074900b40212109500040c203115100e00c0001c240c00010540b1040340001030040040304440140320b030080401e42082c414140c0c2c02c1d41d08000c122030041811810f03031410752180d11b16600006402c600c0d00c032091042c980b030000c2d518082074410312015040340705980c030481c41005a680060041d06181d0f4011034403000b603030346035501c810118000b4450614050701820310202d800c8003003603000c54601601c10342010700f800310b001980a0350400c89040040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 430680539 1250 430679289 430679299
    0x1021b060f0a1113140f0312070602250c05090a0207030504091d0d02060a060f05012c030307051c0504051809030906070609050f0d02070e0606070209130c050609 71
    0x301d20b101505030400101d500d64186101d240c043c2608500541c0c401c0c580c8000e0442c645148490101d1a00210104c40c1c0b84080e00036060602c562040d98002c1d1050010090200f40d0100e0645456450b1900c1d00300399000491004040303491509100b5419440b6100ba14400d103060800151001c11a0003036810b1240d154546905140c01d0040b80c41c0038114004003c7d208030000902c1c040b0340c000c204191a2500c44a4005c1c128a0030209042020744016400002103980300e190200440d983c0824500950303d009982c1000d1200d0040300b080c0184113604100360705110204080080c4000031a1344030031249001d2104241514110040c1d40c0b6000394450303103621440540d11424026104040f155100c0551400d480c41c0980080001700580c100e124141c4115a4825030b810420108108244801180c0d500038a011821307014020754540460240ca9020004580840c0813500c8040560781d1a0b0750041450a040c0b0307054151035202c083e400b400755110244854002040c0c00e01404941c4a0000540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 430681789 1250 430680539 430680541
    0x5041a0718061b0b0f04121b11120607090602060907030210120204051c121404061110020c060603160303020a02060307170103141509151f0801021b060f 67
    0x190549a0f04030702c1c2c06030016500707044180000100306820092249400440040b042d0a240c208000088070915010b001e00241c0d520301c000c11000c004e500c003c07881d481507a19640102102c00b18424100003044940103101d040144442d041e002800d5600380c684a500301c861540c0d4042030140d4840d03003880040c0d0410752900d0604026840784840f08105044003402500c0c20b40e03a24003180b0012420204c07846d0141802c2000f02c10054410030800449401e441c2a0400030001c612488561081d40b00c1c8100380b000c8a04501e800640034003101058009a40302151680d041c1003406440e83c10840e0081e00c24080c07922159284e005d100740d0541641d030958014002c141d03240e42841103640c409050001032000030701c5131a5a060303c1401c454041e610540420152218424034145054601e80980549401e10420801c17a5a80050f940301c90262103110002951140260031400001a0003040d0745070206820101b00a0415001843d80780c1d00e80740305e899410300f0803015a03180c000684181c0e6080072a48 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 430683039 1250 430681789 430681799
    0x1501060302070c0e0a14070201090209060f04061d160f121e0c020f01060b040e0f0a11030108012f0306090a06090e010b0f060a0c0308150405041a0718 66
    0x390107801c0711031244000f40c03035041c2c85050807a85010101c3d00702d010303e074a510385540410445034242d50002c0040c0024090001c3c0b60f40007c0c0c0e40b21000709164010a4100b0102c1401e54450b08468000e100740d512101150324401100020b42e0070071190480000d51080392101094031820150a1201d003596403c440c0885815682026100542c4013401200b0505440a02051107200348070004800740c0040c1003401013002c615080d500c0c04d60042501a606100400880203d40181035200c000e200301b80031b844c4d03260b9500c0780c0242107031a1082c1315180c0100000c103c1c101c0541c08600e404201c4408410215000d0001414844035001002290001400410140d0a00805072a00055550408240b5540b0707001e00d40304039152552010f0301c80c0e4440064500c9805e1928103800f14003429583c85140038001031000c2c01072641c10b0b40c02010071040c540000c511407a00819030b0114080240b0a110508050034050042217840303103401c44d0b102c121008246940d001d4002d0502400314404d0940c245ca1402e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 430684289 1250 430683039 430683041
    0x10e070608040f0f15020a020709060b121e0903030a0b0609011706011202130603150501090312050c060a090605060301091e05100c09082a040f0b130e0d0215010603 72
    0x8a0301201e9042010003c50001100c3c943c401d20034690017030006803540380c8050028500091580700017442031a0071020300600459004071002d11030f0101c2e601d003454848581044820000c020500841044075052262880001c00214060361007200d0901c0002404420040d8500c03e41035000d02140c1400045124040c5880510303500c0141410100300c010380c000e000505130385c0300e0b070066041a00084000c0c0045e9825115040c04c40d0000e2261148003420240040c04214003030001509000d0300c94881c1440c94441c2080314107081210341613900754180b00c21510013030082104200d43c1c10741170000154090605200c0c0c031254a80200e208a0001704c052001d0300851080041030304c8a000c0e00b224a560045140a690b803a05003a036600303030f01646403544043c140040c5403405840214104180030030b01e80b846001c0c80d03014034120b400159120048602200034100c1807040f580002030042a100150700c190301c6001601c3c4660103640004043d4042241c0700c45035104030250300c401060051201901c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 430685539 1250 430684289 430684313
    0x50109090519111c050a15050d03112b0e01111203181614010206011a09060702030f060a0b0d030c06020705010209180115171f1206020c010e07060804 66
    0x1c3c50115a00e005040101c910340b0903c98507a0001d01038503801446411601841140148020b00c0ea080d034100c0d0608001950b4480540c3c0040c0c2044100c5012150388402403003948600d85510b4000c01c0580000d03a407040380001c244940002003006080981c1555004100c1d4801d480d04800c0905003508154100c0da40a42029099a040d40c085c3c140080a8a0003040107004450020b40440b0580349054040e140748048000c132141107400c1040100960707228588030100704100798208545980106002c200e0600030312038069490312401c0c26140500708040748060058201c664140130303200101090141d02c0131424001400101d0858240000c642a9806021124880e0001524100316540040c499500003d441c65000b50424010004500c2c04136011000d00d0050030301d50321080852045c00c1c11000010701d80d20945201c5040030761a00944400c06018003001600d5910090140c01d102000350001000e84c0119841c1031030880100c200012048115501d507030315812541d40310b503101d0b455810 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 430686789 1250 430685539 430685561
    0x20907020c041107050c040b010207060806030a020a230f3618060708070905060d0608030307020706020705030c03060106110a0c090c030b0d080a0c05070506070c050109090519 77
    0xe5440d41c40110350301c60181e442045080850603071161800d092460812081044442c810f91511014012690300440c1d40801c90740c0c1030510544030341d15900420704144d400803009500030072002001c100e140b0342d00031030814140303864a84140c1c080444140154550422901c80e8003100c410043c084d1060351511229070180d03512490048011024000c512019058503d001404090380d0b130b0105591041045a034800030754900907240c0d043c84e41e00a001c400f40d900070345004403000168550a20040c1d007107480107200c000704803580c9241415000391035411074003079400180140c4000007428640050046a4680c2c02800b510059103041015544000110380381003080c040e0000c00c40101d2425442c10004244111001c100c0c0e0030500c4c0001c0031500c17850480c038410403269890b00c02082550f0241e41d03650056081c80c44e005440703814513030301d021b5003684810b83c028030006500040101444003041110303420b032104880c00ea100c6030f604060700c0e13003151804030010b100b00e109620300c00c040d00107400e011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 430688039 1250 430686789 430686793
    0xc0d0f05190c0f0f0b100506041202040b030a0b06011103130e180d0504030201090e1306020901020a06110702011403070804060c1421150d02190506130f0e040f02090702 74
    0x441e00f59214103030030b20210300139103484214843c0301e001d101010034865030051702951410010313810400018100d0180d80a00e00e04046c85031508070454a5961001c0c1200c08020210303070984106242c040d414a00031241d01b40050300b842202081a00c0000c2558032035044445084011402c10b10181001e903c001c15040a00e040020041202c030b20070b000315410902c0d96661241d5842c00d41c00003408881c1c55521001c500e4a03840108849050305422040401d41c1c06500580e4a051200c0101c0c9000d842050184c006441d10040e4950305001e0001000b189100303803100200c61040032502891800700319040b40100761080300040000302c41e60300c4402c00c1c42c001e0070500100d44074030418950382d406c0290305403001e0f100719004001408085081640c42360107070038100326502c1120045142401e1640c4002d0241e036054103140340084a42c0c090030701400000d003403643c072100a4042c50310024800d02c55540c100d00c0c010008101d21a80c4007445e4440c0c2d41140c005408584c60f5424001103c5008040400714 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 430689289 1250 430688039 430688057
    0x3180f01111b031603032703023a05040503011d0a11030109140c0f040209010f08312603190e071404150e0c03100b030c0c0d0f0519 58
    0x600d21039182105d010b5500003074854100c000e40800101d065080903510034100d0044030000e640000c5050011040141c41c0d0304100e4683c50712844100084d00c100301100000c40003201199002010b0001c980c3c040f8024405079014034519005e800750240d03e024150884005240070628010402060f034601900018140303246840d40003044000601080341c503008406506201c0c500720f104680c08210803030701145480040710018048080904100303044c403411100017811070a42e1040d0224244011049146036040798655003c103c4210f901241c3d100710346640560040d0b0b0220040402100c5400c4c002d1443d01e0702030031442e40c58840c410000f590340d02c4550385282018140f2a88008040403490410255034002c00c020035511086000a14120703d40c00c100030b5012614103664010f88944c10051f52610341d000ea18134244960381100c02d00403800828491a80758500041030303184136020544481c18001381c400c5034940394a488803400284107018004d429051080e06c10061400b5040010b54 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 430690539 1250 430689289 430689307
    0xc02030607030902010e15030a0c0507050d1809140c031302030a030905041a06041406070c060c0c09090210030c1704060c03051f03061a0603180f01111b03 68
    0x150400c100c1e10034001986800d002000c43d40c12249041c81c1c80c00c2200c040c000c103040c0c80c0e90400c0900008009040060700c7c3d00c100840940a08103c0340c01940080c03d584500b107070b506018003c80141d41000319091440315000501c0001d91241410014400840e81e43d030340c94046003104c0540001c1c141c4001031000070b19441c0180e80c100401c01e060b901c00e850b140401c0d45000208001c507010340c98100e800078544071021100b603484400329402e65502c108192011845a000300e81140113080001b071882c0e1805101154454201d90940992482003c0380101036444030030703490a4a40962000b90404102080c10768590b000342c005a0003d82145481120005185520300c2c0d070a0003514281c07100d95075241d075001d11940c10301400740d00540101c880c88080b010040042c42c440010710014103129a00c8004640d00c40310300711114904d12000b01000d460381001c10150301405c0c03281800380318622540155000f020011f008481c000d42d4182d4603541089000700114400c898038001c0e96103140410024030f84 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 430691789 1250 430690539 430690543
    0xd09140d0c0b0a230405010207121b1e05040e0a201c02030c04050105030709090318080c01122003040602040806090a0b07050f25020303040b070309090902090f070c0203 74
    0x42d10b04110b0344d0301c2420300c400141040b43e10644200b1449010010001070005980002d0800102c4180c07140103d4030104a0030903d12003c0305aa10048101180100150035044c545000d4072403900d13180c00107603480c1c2e20410032049485a8a982100d604102e0303000d0040741c604950381125600c0580090b41490303010380041d01c0c07011b0f1510403009200407000d021066007410805802d450005940c10005541807800280e03445500e40f1410f012903032039000d40340c10140700f201031464810401c242d6202a548600c207040c5c4440c10b00040500190000740700e58403401040c00f0b490685030204005043c0d044845a9000c8c003544004c0050302c0c83e1303408110025081ca810014684141150300c060440081c10b89000c980540000c2e1180e400c01c00f00b0310042024500b20070885005c006100502240303500e58103100203201034070701c1000e9414000450001a0203665800405125200390346440c00700380c403003400508868a000000c0e41016015001800103501100c940d03801001c142809800110180d00081c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 430693039 1250 430691789 430691797
    0x8090a1205120a0603080f1b160510020d0801170307050a1a07050406022a0a090c020706030e0c06090a030602030a02090f1807081003080304140d09140d0c0b 69
    0x540007400000740007054910440702d4541084100005110320f034516268011280280c182d00b100c805000500c41c000b00ba492440c49041c2c541036070650b91040c104042643c002c0c181c5200d054001c0e0100d4000c3c01c105407001c9020281c071001510b480742141d007403000002510a001e059055944020400300002c220100050b500040c4100007201c001110340006000e807440c05480e00c42845014001070102e2500410540340b43d503003402481c108642030300d5140c1640d03c0101419074100d800c401c00030a11104a401a81c0220000d408441d4040d903910011421100078039045030968100244107075003440d000703009064102006203080c200755125100c0c20202d83c0142e440240040c2d000a060125082c800484000c0050071110260900354920510402001c000c2c20141040030910000351416041d100301c0000e560009482c42e00c0c0d160501d04007807884904400c90003035209134904441c109109440f06410399103101410b4450705511014031400a0048008545160100c02cac040b90190f140c001070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 430694289 1250 430693039 430693073
    0x110301080a05070609080d23031618050603010302040e030f0f1306090b0715020c150604060503060408120603071d06041401050d03050c190b09060c0a09050108090a 72
    0x203000e8010705403424500e412a10b0f030148041c00101442000008400715143c41c19508900b8600300c02030040314072004410b24055035402408010050009515080510781078040c829195616a895089480251140705100300d540c800003c20040c00142860f0700400c000c50f080800701d03810200040b01d601480e81025114600040300810b0081044100d030303850000814560038616070440c1081d806041c28030440c04c025250008907540c010880c2c11642c11500c00425020660394800d4029004073b20f80c41094520030310403800c1c180003203403c0c5004103505003d10740c45400207140100d01440200502d000518055050040950010b9120f541e2409846d141c61010211185480c12200304421201c001c80303c00310303081400005001c507840fa0a69080200d825080c0907440d000044003851920740c40944814543c014880201c0c03c000f00e0401c401c2c0102101000d583c003503030781d9641c82c0007280203401e141c0b0300040030990200300c0742d4000c00c031303003604188a4000d07910700d04001d4590b40c049890b08410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 430695539 1250 430694289 430694293
    0x307120507090204050a12051203100801140c0318070b040603020a0f020607120b06130b04051804260705060405100605010c080a140d1112090a2001020111030108 71
    0x11504106003400380a000d005011070071400c0c1800d00e408104000000c0c010403402c800301030003c1f024410100200c0305140c1507010000d44d24507000484001903070342840354440640c01c015008441200d6000c0c0b03e8400e0003100640c40c2903a030392020700d0282400c42c4104024a000d040c4002c1181c2000c240104003038034561b14050781c1c40410b004010407402c1c404006108540211052001469008040c15022490000d000c18880d1032540003d80d94850803220011782a5076200014503401200050422614200e0f01e048004c1040100310040150440d00284034801035401c2503200e41c103400d17120001101041040c1d0401c10b081e40e400d031400c03005403001c1d540b541c094950020103001502808020346001e281c0b180100405580e840d0f07460044a001005101d070a151104805281c6020fa03151640b00c41d0041c8803581040f518072046030f004014a02624080c1d9000411691001401c44456548001142404400d445284a90606c03010311641155251590b0112a1505102440c080e00c54a80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 430696789 1250 430695539 430695569
    0x9050402090708090d0819050a0c02010b060301030c0504380f030d02073008070303050a1a010e040f29010311180301020f0f03070e030105010812090a050307 69
    0x100200201e00410400402c001c0900700b12150340c0c04a081030354203e450034019110384803001d441c2c403d00c0f004181c42140605c0d140800c0303840300081e0041d4072401c407650000c0001a51440912040c0e00c8240005000146000c01c02c0180342441c3c1c3c41400f24806890000c417004019403c2007030000d4005a150007584c2c141c0224541d00d01d0310001d96910140c04400400fa80c05038200007a448202c0c51044400743e0662008225800c11000c094800084a00351462205c3d00f0a02d4030305980d4016100c20381c0002e2400c00085c546030b1452086021960318140d01004c4181c06800444042260114103604151100058409244540140c4205100000b408850000e129502d10b41d10102c1c00010f6041600b0912910340110003401107a0034048849101c00c940703500e80c0042400ba104100080c4044140021071460710303242c80e006107002d01315655a88004100e00001c050030b990782802b5038015600043c0150081005001c0102406c40d0003a140340c000396035400002c0e041c000341d60f1042c00c0b002c131210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 430698039 1250 430696789 430696793
    0xc1709041137030e010905030c06180c130f0b120706020c06090a031b031b050f01020111030703020a0c0206040e040302060a1505010503060301290307050409080708090a0e01090504 79
    0x11614401c01142c01000400400d0400b0401091040811076010705a0f604d10140a2410a400c01c00650b904403003107960398800c2e81780d06917984404a03540c600e1041040305200e52100041003080310064010004159002c1140d040b800401804140c50304039a42c4501d651040d0301c90300a22144c92500c8405010840e252000207801c10003030840d0240304001c204483c01c059a581c001d410196904120105c8000003045118621400c040d00050a14410400026000d030b050354406001e481b000c1c0d0300640d542d00c0d071000590030f84030f00c40300320440b914092000500c1c2e24403d6000c6c103071000041c6407514113100c10340c0210302c0c0d40e44260010316901e60709200304000c0c0740e01006056001410030302d0401c6054902e504041c01c1d5400c80c0582410484c1c00404505155000d401c0364481d00c1c1800d501e0030500c4c40500d550681c1c5a03011280d01e00a0040200000c3c4503d400e200f220342042d04880366500d0054259a0286c140e40b101d084942c1c010000c54000c604500c0e00380c0032501030245540000744074107141c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 430699289 1250 430698039 430698067
    0x7030e16081b09010b0f0a05040819060b010c0510050703060b0d0506010206100e0402090411031905060a090b220c0b071104020f09090403030b030a2603070c17090411 73
    0x30b48989015000d07000041000300b15440072585001c580712221600e4450a00080310984a03d6000388c1c0c85115850404043c4602c40d80072903c03c511603c000c02543c620140151204c035085000130b0a550003004000c410004180c00c8540c7c003d00c03078500081e40ca5165514159140c00442215500c00c0daa07008004c11075804101d1107800c42042c1c030b12580014600b2580045407100100300a004040c4200032400300044e43d4858038074104018150307418480030b5041d808400403080c80036580c03480796001140c0701013a180308240c0c25035040001c500300c664440396807030880c501409101031500d004491803008100700c0c9144001038090313500c800c1d5407140181040d411000c42c0243c0300d4411841000701035a0400d402d0700b15040040c080da1021110340d514181940104864002035405000d4100340b0001c00100281c80d03c9003624040304500040c01c01c00400c140d0b408100e07000e0012840401d0040040ba242c00300c040044594450650300e4a003800d03010506403004040b400e101040d0108106004003d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 430700539 1250 430699289 430699333
    0x307030305090705030609031903060b040305010c031a030c0d050c0904080406080a0605010c0b13061506020609010504030206010b0c1f0b01021b0f0111010b0a030809120a0302030307030e1608 84
    0x8400420780b60a107100c4852300d900c00c0201907002041c8094a84804500982014009000e003940050f101d51303913420300501070140d0040383c5002038035000c0b0405920780c100c0d804040010003d00107110300405a8140455040c540006a81b507201e0303074103071b06c023507981d01c4d0691807103a4440c01c406915070749042d0b40540000c0001c0c021843c0b113424076100303000c02c0c1d07405601d00802c01d4008000e15519110401c00c0c80a42581c0c0c20054041d5003407202c9401c00c03100c1032a100707003201c138503a0865825694560307445003229000d99005005030468001017000c0038840e00030b400c1c4d01e08400156032030703285d280c922001040c030449404c0401e00e841d41c410010941c0c041c032445070703d1502d01081c0304200d21241d000525422078140308034140503044445910140342540401c0c02984007030102c50301d1030b8581c1050301007a000b4400e124443c40c08801c83d041800e8020071203020081d89500151b0650b1240c690903406040c116203880c40728418494448103500c482550703c401031071214003510700b48408000c0c40190300d030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 430701789 1250 430700539 430700549
    0x8010b040303050d050a18060c0905010c0c0504110f03011d01120b1803070f08031008070807060e0111010507170709062012130e060f0102030711040b0303070303050907 74
    0x110034002040441d07008803c840c1010b0500500244030f82d108031280e401091030a0070a1507141041e040c10080085a80c00489104455141e050540781e96000459115040d1400208010100d1b0820801c40c10300d504040e01d00b4005d00c0049042002d00c080804964000740c1c411000121035002c84001d01d08a006918054031840e4038042c0d0f4410300b40c58002110300e0180c16084010011141654a40c1d014411340320303442d900401440700e529050602c2401a0801d5076249080728404800249209001415500b101c00e844040c280312443e08500703403941380310740b9038060500014802411030320391b082c8101c500c103c22903200e444402c81c00041c2c088079070000802c4001485801c60040c0015a080743c020000d0a043d4000e0b0701e68111801e10042c00d00844410700320141c1c4020030100032800901990500362500484a100196919000c11440810401d030142c0980c00801c010000f0804000186d400040058008603410900b000441c0c5941d04c844410340001e0f540d007052004d490000d200b8580108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 430703039 1250 430701789 430701809
    0x10050c0901050306010810090c0302040513090309030605072a0b0a020c07120f120203210c0a1115150315010605040e0a0e07030c05180f1801090b09030a0801 69
    0x2100103001038500d100242901d4113000c0e039807001560350000ca00c0c066016224010040c0004e019242003d0042e412038022248100c03a800b0b6180f240350010f20030300d091650584c1d51480000d141d030701e8050003070602034880010001c901c00e2407034000965001485035444010303404000b05845003081c0c8400c207405046141e0ba14010052100c151000065050903204d810140726451115803401850440a032000241900000d0660b214510b8020000d803107410010701328031001100310742220048106c2112481e1515000b4016007840390310602081d9103426404c0204c528041600040802d5080110794007040075062a0183c6800e0070203100c81c440e0b0346030301c0510032180c0d410910701610703600803401500000b040303010011f143c4c08030304d42081800b0b90341c20080d125000e40783c0c03c00721442c02c124015503015005020324008810501e200d0288143c40501800c4025220340007440e5100181424035012592240c40e600702050005881354000e04568008560700e890700d20018200f03100c142e0040c2042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 430704289 1250 430703039 430703047
    0xc05100e0601141f170a050c0a05030c0c12030a0b0901120210050d06080606041a010906050d0f0f061a0c0d0302071406040302070305120f040504021806030910050c 72
    0x55040000c0007415a00340f00203011000c004400803c0c1d40f4021204020544807818021810641e0008858139484080f45840c2d4a159038000380354095950503140b00c1c2c580c550030400c18029a21803006103403c100310100142c138000c04c40e40514600750000c21410504840001407000005062050080c0294180c0300b018496240a100040c00c8821080183c0600b13004d0702040a0790344610110782d22042c20341400c02503162911700d500d513904401c03640306015034502184100f80081ca54045410b01e041655090074840c2095000c03909608509030102d078113600c400344500c00c5070b090b00400c1070044044000044083ca46034009500500d410740064032003a040040241d41400402c02000c12100e41c100560740d100246081e150000c0315460303040c80c42c0100f000b03200401d640401c580c002c03070b4090412290918a200144040c0d846001d0749510902c100f00000c110754101034000e081c62140c0503a80c10043e11248000c01c401d44e0007200d443c16030703030002d07501c1941100e0244251600005403134111410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 430705539 1250 430704289 430704311
    0x30b0103090209061903020a0602030304030305181e031312060f0501060f140706020c100c0219061d01020a110607080f011e0302030d260606030103150605100c0510 72
    0x8140c07004d0301c0b0038055207220f11140c1e1861410b007002e0740210fa0240685e01844d554400080d103039082590228006810440400c81d10052031551648230345841c0050702c000300c3e00d050342c50b0011040c06400c41c19800144038000401800d00d0703840380102a8050314913489a058a13206007240c5034900800d500c0791900c0014001558881d001300501c1299040a07607019220410721905d5020340d00c00100640d0001a0760140b150b0042a05c0c110003954410502269419402c01c0e44c544a480103030320000e031403608818002c1020758010303c810301ca03d000a0021b00760305d07031001c0342a40c1c0610b00010206100161401030090108881940281c440c82c080085040500710700340303424810302c40d008080c2c1c1040e40110b008444805014002c560003412111040490030018201042c508420305860030690800b2004015170038141c0d202e240c0c002c102c03e203103a0030755442d5118950380e000350384481d507a070f507402084a480e0880d9600f20b541064036201c81d80b040c2898103d02c0c0005481040910303605200702000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 430706789 1250 430705539 430705549
    0xf010917030106140c190c030b18030d0c0309050118050d0e010c020f03010f0606210b0d0b09160305031306020321090c15031b0c06060409080c0d0f030b01030902 71
    0x1074004d030074080955442d0000b544030703440e04d001c010031501500148010841040b044c01199000c60744910b552010741da4540b48408903001d80d0358444902900104a9849400030b10350240141e5002420001018411911694219050f96114032040c0301c032040c0c0d03031043c00410000c3c1c40c4090000e241205912000f00c1c00241400603001009010700011111820560b8007908180209121403108000c0c855540500030000c40c450440860ba085850181d100c4451040c041c01c00300c0d0304060290107034910a40e950a000690041141080c0d014001c4004068000100c903000114060300040d503c41020315000000c20360168014400e660041245030005d8103200200680355900d001040c2d855504e2a03640d40c02c1c14a990300c000d901108141c2c00d46840304500e0301842c09000700800480c1920310080c0d2882151082100c200c90302c0d40300000244080c039140d00041c0b080c0b071103101414180400b03205003626010083c1c85040104000800c50740c0d00c540d0521420320796aa003482c1c14000f014580e00854 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 430708039 1250 430706789 430706807
    0x3040303081f03030507060603080a090302010f02010c020613050a0f080309010b0a050102190c1a04030b06030a023a06050a0b09010f092403050706020601091406060307110f010917030106 82
    0x301800300205406c400c1c41501d0380000004c64002540d00d5079000700507c020644503541c003080380840d0a82e4841c46170144140704031034601342550001c000c40e803250070b685260680048411900c0d4440c0688110020300380e0320145d490300748691070031a00d80c14158103907829609410706050140b0040042001240e0b400551405800070030088100240c015003405c4500003c19082181c140d055001e048100300d9121004100b2640140d00210403500c640041580320056810040d50120b400c442c0d240c0608000d84d40300c0340c2d552455110041400340c4101021131013811400130388a0540d100c0801510810501880c200500100c54800c0726605212283c10122403034050010210382e07800545410f82800600c4004d030480142044101555900d03140b60b40f400c6500444d001802200c0000490b00e14900523107115400c035003040c065560b0703020180718003500004c02502c01c00c0400807c41c058100148802441c8080340400424008041d0030050340042c2c0044102c0d0275810b0410041185651044070701c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 430709289 1250 430708039 430708043
    0xf031003141608010902060d0203040614070e040e070608010b1c180b182a060d0c11030403030e040b061c2c06040201260906011404150918050f03040303081f03 70
    0x5803240c0384c2c0d040032330003007005640b2804400140703810320081c3e80c1c1004244642400483e414029510024800c036214070151085c4e10101e9103810040c05002d1941c805002000d020303007581a03200403609031010030703244252045c4604404801141083c001052003460b440112003001c03000c004144080250740d02841341030880c440000003003030b81400c8400000e82002040050600f501c5170b81c3d040c0080010207034180c0c080e000c01c5c0d04040c9651890008825a4112a0103485041c18082504140000750034400b0080e41e00180410011304024590590014840d0100e800024040b104500320050001c28a0f55128064103d9400c2c1380c8460300011410f130301682c2031802d0401195092514240b03521844010105120208100314415a000413002d04135000f5070364128464aa1006020407110f825205140040500c40c2c24030501080c4d0700800254600700003800c40c10b141640728241801c544900440f00c3c1d4200080c20402c0c0f42d80207003d90b402c0200c40d5a4a64400340c011074690081c0451300c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 430710539 1250 430709289 430709291
    0x9030210020306060c0f030c160b1e0d0903030615020a02090103080d02070b07031515120b1c0605010f060305010509070c05031306080609011a0f031003141608010902060d 75
    0x55035a460301010b40c0c04030b82c02c4000300c0b100e00140105d0031343c403038000301603400030b40c0b044a84ea00c1155403000c0027002120030324031402d803070214101d07602441c1d40d1040b0101446510100b1100705046002d12030031540900aa034002141418541803a000b10b0a03004014115400b00380041c0159032005d2909045030307400010191707903400310b88110002c1d0243e01405404000800100000e0300d4068101443d069160000650059190880c0001c441c12001c207400000c1e041004075920b0012940c00b1100c0c0150043c13034a034009520442c060a5809000412035540d51039000402030300b001e020122000d410281428400c560602c000303c0c2d1400304c0180350703404000585040e041400300c00c2c030450311030880401984031070a45500d0041d10203141079900c540258108400090032034001448514014202941240760450204540030180c00c09054165202014100000001c2e9a0701c0749030980110040600019078042982c00190704240d070011525904148078940180c3e41c080c1180d04150340144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 430711789 1250 430710539 430710541
    0x201022103090f16091e060b0d0b0321090a030519140303130b04030516080304110d030e010309030e09070e1c05060109020706021c0e010e0a11150c070f03030e04090302100203 77
    0x91b40031889110b00010440d41c0380307851408185d40140c2c000500005a8140c801e11440c11440c01341560307840300c0c08044028140075080c207142d0b40e02e40c800500e10154014480f03440c04d0b8898980904008415600c0003044202032807140c10008500250415441040c002d5415458980a4864203542c4a030000300300c83c81c107074005000c05019109130340501d00e00406440c1c9251607460300c901d150b40305490644200007652285626403402105008203a0b6156982c44050b0a0110056002e8101417904805000310000c003c00661035002c24544500426916258800c0c0303444288029003104040e51609020742e015010302262000541d9811203040031401aa071712618203044009000e1040056a200a00c051400030220650003901030300420100030014040b60865003640c0340040c1400525100b02c60058068600d0302a80368181c5c0d00e0308503007107481c1c04021507060713041c17000c1500702a82c8903801010900506910007030710f0b0b901d2a803d4808110160042d280690b070703a04295004010590000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 430713039 1250 430711789 430711811
    0xa1401080601121a07030f0605190504021c15150c05030a0807030902061b0d111009050307080c0a030e060414130605030f01021e04030b01060c0201022103090f1609 72
    0x13003643c1038250b982a1940380741d41042d03640280904046a203803071449007003500110b4107241c4022900c42c41040105202125490002400080c0d0403000112841d5409103030105103040082c01090081460450307418209810700040701580c140c030135200401c00485800b03440002e0400011521f0241c07040c10007604d541da40c000120003401a15400a4201310017081046061129003614900300750501d069847d03012414508585d00c8000f92010f443e075034408008860040c0781c5600640f651406202901d03e4082c0d561908045980f08010310442a403219240c2c409050b805145085031803000c80356107281c0707450052900f4400074000122445540d4482021032803080302c0c1d018100401c40542501d5130a11030502490003900300079101c1c42d25840c941e000a1466401e1812203050320303030107141c10b0ba0507420407804444030716030700700200d040d4860f141455401d2818040301c5a40b001020b6440c0b40e03a4507011064600309468000550019404101d00698408a108005059500115000811031242 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 430714289 1250 430713039 430713053
    0x50d05040620030906060319020d020604030b04051e0a02010503060405090c130b040e070308040e2208091002010902031b01090306020a0507021f2102070204140a140108060112 77
    0x4002e00040c0031951040d208803800c1c0c0710051440384d540f00301a03401507074500c428107484490030800d0220004040102900500d06035524a40040c000313085141841d4803030707558007110304041c1c030192013650151010350721440745045280f05802c3e4000203060342041a0340060305a010140500b032145494000107240c0300010040034040b11070007020aa007030200d541c040001002940f104900035400d0641c031400e1400001008421240c2c09003c03075150a2800d190b6401b034001c0a0440003132221700d0343c00074002c0010b103910180200d004026040d40e0309480f80030444050780c1d9900440075a41001124000b680e0f0115104000d12482411042c50010100049402091701d4000070140741c40480c560381c1040e884009000514826141c0c010317510f006a140040444840035544002140120205450246c107012400000076188026080208a0707000609130340d120000e4202d0302d102c10003002000ca840d0b000d0740038082c42050040b000c55040c14059a00c84038140070740e61150f00c40d40065000c10001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 430715539 1250 430714289 430714301
    0x20106031e06090f0308100602030306131e020a0512061c03031a060301030c0806070809030412020109091806050121060c02070e010b070c060509010806120c0a090506120c01050d050406 81
    0x1122071824013140042c900900809416508411100d115a001090980c0000f00310303405001c0c020b044001c04c0c4124000d40300a84910000c40c60381c00e2007400304079400d41a60010740000f5000e034498688a15840c0000e880801000f44518072030343c031040c2c0b411400c10585407414409905803802042520825400002c046c0d80e80107581d400400000001081c0500449000300b030311825006d8a07566280c5403030840d00c03440c090380c18564540080104014110142c05540b0215106041050b840da588082130350407610840028000402404803d5003000740b00d1241c0c03400b51000501081c16042c204c3c24440005000103c0100030b190741d00c05521a65000300480b400404003c107000489603112050716109400401088403007d48003240803403400d0096066407040f40d81a9a0b601c10b65482104010640c03c809d02c8200d0740c0d01a080740c002480d20340320006005000c0b5003001040d1401c1c814280040d65040200c0c40c8019007007131050030000d80e8410201c03581e6180c101c00106031034441d81403e0f402461 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 430716789 1250 430715539 430715543
    0xa0e010905130f0f050402011d21060702120a02150c040b03010f08120a0806130906020310030218090618070e04120e030d05040b13090204091407020106031e0609 71
    0x80b00c2c4040005072055500040c850451000040c051050452612019154103039802030110380c04401040340800846100c1100362402400481e03000048148050122110400414680c201c941040003054040050b4541b4802800096141c8405820020740b6007400e0800943c0781c000020206140c241841d00b40c5004e0880040d1007540ca581d2182c480c00c9001c19440ba20500c2e0260040c407060b921120020780e800448a911903141c50b0341d60004029003401c1000041104030b0390303800d050300494032314070180d4494007a2415403104107066004014040303010b014100c1c00109030000304040c50300c000c9445500f002600c070040445d030071001d8035a0304103082c6410030891584000c04000c284070b404007a201c1c80c0301c0d8640341c42034003080d003005064036410134441003004180100310800c54051204001d21340d9081805414014a440e1100d56003641e0241c0e100c440c81e5074176000b0002d854050341c5003140d08100d140c0000c00c00989550b40300500d464800c0308070b84d684982680d03402c0a010540c1c100c042015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 430718039 1250 430716789 430716799
    0xb0609060c0a1703010e0a1107150518030c0c0904050f0a080720090105010503060d143a030b0d3212071112030705010204150309080a0e010905 63
    0x80980c241d203030780d04034480741580e580a4007502070340d200300c1800440341070350180107003030070950382c0c0044180240c041c4001e41d4041100402100021035181e04402d09590000c00012072141001000d40c2110343c0c0400c550100d54008120072141c03030a00181c108034070481600d00c030100b56980d0801d10304042041082c1c0105014010010042101510003400d1345c501c510120341100c4442042e01400c0c02e41402842d4211500100500143d80110043d41e40048014250b40a201190341c1e4003d02c011101484950ba50000800368203000d41d0600e0252046640c11540040442610b00000800d5081c0001414076940b401f01090700c0d102d1002c409400c0750440801c43ca03050a400c20b090380094603c00000140340c42c40300450400e000400c0d51407450310000c2c1c0480c00c0c0445526248041600da6907071651041c003118190707a20f010f043c000b51841c10b000300300050312603240002840040d000c00090340304040c94500f5110000b1901030613102c81d62400c0c5400280e0201e1480166040381a64100907448 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 430719289 1250 430718039 430718047
    0xb0d140c060c0f010f09030c02130f0c03020c010506010203070f0b070c3002010b10030e0f061f050f010f03050405010e010617071203050f033402190c090b060906 71
    0x8603a000a05a10203e0040000c00184801c620000100c9101d0f500082c002024500300d4000361501420300c41070160301e001e000480740080c82109040b281510140e10100c1d401043c507100154080c451598042400e0000d1403400e038156840c4494044546001040c12840001090000d4800c0c03081c140a1a0310030381020710525100a801d6450300303040c003854208205100e20840c0b4034818040c0403c0c281014000841c50741600c441600078011812011405100701d600c210320030001046998002e0401800e4140c0d03990703c4000c0908201020b800550052500360070310500759a000c0c0303400c4144281440c00260030740316031400e01d0160020315548099582000400310b40f04590101c034199112100c81100c1c80681c0c3d650b0b521415001043c00600460018400c3c03c1804e24404001c5900410001020140d1010441c05207146281b50b144141d5482c925034480e103030302d601000580c1800c2d64090116212a00c5503450300036941302c0e402891a210b80f50541070b0415160b440035640c622000424a03a25 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 430720539 1250 430719289 430719307
    0x1810120809040c171b04050111010209060315013b010314092d03071106210a0c0e03060c0c0c03120d050f1306090206070f1101030c030b0d140c06 64
    0x560349140e030541181845580c00702e403031000710780c1745044090080c1c48060304081c074000054035895030b4072200b00d640303540070401c0303e5643c0d0b6158000c51080302c0d045040301031003c01c1301c0018240402c030302c2c031000c2900c00e10311451940701c4103e420f2604140041c0980f0003800303104e80128050441a200e401c0c0c1508440144880f0000109a030f410350308100da6001941281c110603149001c0c622071380300a10340c204000d1280420105442c00800c410003510541c90100803e1030014188021802c1d028241c1c48401480340c4c1900d41d00900325015050700d00031003043c0c8850300190321002c1c084c1c0682162100000c0c3c20f0084401030290f4010076000034140e401000d661032401c0d02035401540310154186c41c0c1070010f18180344001c100c1d0b0280c054040c1c1c0c400ea420040c0d03101c90040840100036680640c06000140000d01d02d0700381d81780c44c40c2c801c00345290400600400907007680d42040714001454100f0300300700101e0301e0316865480441e4008940710b00d41c0c800700c002c0505155084c08060742100002a00100c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 430721789 1250 430720539 430720547
    0x81507031404060506100207030f1509050d0201020403020f06032430060106170a0509030d1b030506093306160506070c023d0e1810120809040c 63
    0x1210310015111106d41c445402c6049849411601004081c0700d07204450718049541021104d01011403110006480066074035418601605c01c001440140c0d000682802142440840941100020f0303501900b50700f44100d0000524003010b0740150300d9002c00040b03503103d955042d1103800200c0441140000000d1702021800303400703844454401544503070f1000091b0141320302e0058468514240f00490b462300c40c2701d8002c2c007403c8041d00d040414441400524000511071050f10314a0031520080d02d81d800b44004041c040e540000c02d0300380f01e503001c0810010840e0000c05480030007002039018001c000c40c01e4003444c0c01140d00c0d10038103401200200b09100c2210000254104a500036070032500c058ae10000203e560050b075103402034001e29800d0300d00d04043d03c04c2c5c3d001d60030802801c4519840d000902e03800c42c45482c90300c255000241c803d15901000d400c100b140194022003201d40e0b41e2040c500f5452416081409100e12159032208021910270b104141050b1114044014401d0000d003514080041c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 430723039 1250 430721789 430721791
    0xf08123a02090f030c0d030c0809180702010f111e040b070b09060a0e0d08040f020909030a0e0a0506070305070201090314010501052b14030d091a01060203040815070314040605 77
    0x380030b00124000c6402a20300000d9400181078001c0600c6c03002011a941258038492600048038106014060301c0f901d03540d00783d0500c4844540d803840c0000c0c2e1401d240d000307085d19208182d940c290340c9070a002d41c0408240b40220394a10301d081d4031008804243c0210076480c0e210300da0108038512070204450003003040c0121f599000702c01403011241c46031501c000c000c044400080019085a100042d10440c0034011240c0c80e522034091101c030706000c0032580110307040d410111000c80e000e80002174519a000d13000302c0030745008003055410194041c1450007248a81c07007009005020b021012615504583c400c820f00c03c051540711003142100c03441c0d2400342e40a00400c1c092144180c0494603011b604c3c001d103201c5042c000980203908408400355444a07032160703440f58101841400100b095103222280c5001d4140550311075070007007a5201c8081c2c0a2221002c06030040811034100700020051030000064806d88114500c041c082030392581802070700101488204900c01400c0c0a04020030300289a00007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 430724289 1250 430723039 430723057
    0x2070507080d0504030201080a181b090b03070b030a1107140d030c0c02101115150603010e0a0c05190509040605091b0c0a0204050108070f08123a02 65
    0x1a50304645a042150311031100710200701c0050001d110030800b40d071003808001d81107400c22074002002c2a00301d10201c030f2089a28002d03515004d01261011702082c615481000030300c0c0040c0c0c100190301010300001d0f04c5406500c80c0c042e1070940880450f4403201e9982c41011040d15540a40781da40c48141350128032113802495890729030007200c81510ce440d00a01886100d04441c2c2d50300340004805a00f001440804070186400f00549030404080c1841c08200007400d00380e69840d0300015282c1100c0300300103000c600040034060b01081c030042103160145840590401d200110106400c0d905800868060084e0713503001c400c88145a225101182d0018000c1502d10000ea0301401200d032180188510103030244d9070b514800e40e00101b40c0840700c40c60b00127401c0c40f8507228281c80c3e04041c44d0b00002d00382c9000307820060140d044000c00700b002c0d5201d682d04800411b4644050700091050340c20f00d001310701840c00c020413040144041e03011114400b00030003a40c1d52030084141c0c0002840e08410000750031003081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 430725539 1250 430724289 430724293
    0x3090a030507060216140f160501030207110901140f0d05061614030a0606021c0906110c18010503100e0312180105010806090c0409050606011b0c0603090b0c090904030503100f09020705 81
    0x700c7c52480c0011800341c210444800c04141110314000044000b50301c4401c0c207884082d50791a40348925a140e03030a09000300f5919680321520540d400400c050302100b00f0b43e03503215010b50408a03000540100301c144d808044000049101c2403119402c0d240201087c1000f064100000100004e04046501c03038801c1c1d5940c1d80c2200c0d514006d81301c5401c5d80d200c1109015011920034034040048034800d40558640b008190169414205e660003c0350045024070f403034642d024a24001401a402d04118807481c0b292424014004410310154140d2688913200102001401590000d08901d503441c24129009000d03000801440d0307562030001e9220901994548000d00400d5482e100c0703071a0a01074001d62540200250800da01d41c00d00640b8504e0b549000d668140c04400040804110f4041c9001c0042016803004100c5406d00c2c6096a00268010800301c0c858405000d031980c15240c2c000055403007a13243c00c01c2130b625180c0c04000c04401c401c81c1d01131441001c0c00328000c42d00d02c91b180c0140070560b105d0303c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 430726789 1250 430725539 430725553
    0xc0307060608011a0909010b04060306020414030d210b03100903080709030201120c1b0303060e0105010309050c01230a0207050a05010203030124211406030303090a03050706021614 79
    0x1107600b80d40250316050fa48213000501d03541c1a291120b201c6410111760400082d0040a80000c038023036840303560064500680c0800c04101501002807201c920020450152030b80c100008009408910f88000f91026440305192408204580e030b03006101c40e52008084070703100080c0d1401d15020b4480c000f0b0403000155071101140c060b50213140318106a9905840340422062070b00042c40051154641a80400c26014205403450740d80c072072501100d81c0250342c0401c0e045d05191140000c16011381c0214100b51400441002041000c00c01024031882441e1141c040003ca41040310020b0403903020210380c030307000201301400d40d400050f4501141c800380c60918000741d0740c000590300c03404240324244122050040c01003082c0e42c0014000d003044121308103561043d25030809040d00458600d500d40c945660b0300d8950401d426150005540320004a00452551400b11099926026127800c000e06120700412224200607098050310340b01405402c00b249640e43da410510600988030007481a1809518 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 430728039 1250 430726789 430726799
    0x6030a0b040f020903151015050a0905032b02010902060c01061404050709031b080703080c0f0d0203042606070c14062419170c0103091a040f0501020c03070606 70
    0x4002c0d1280c81c0c4006025000d02d00300030806e0301c00f248008010510010700b4030004908080482c0c1080109075540ea1800d807124920000070300f0020040c0c000c2c5109600114005200354010022590328411403c1d8205140781c80b0708007070b8094804440000d500c00c07008141002c00040c154042801c54104000719104091284144412540c00740c1d610000144120000c1c400314030f40b1103800d40ba030320b001000041c0d00c4d655030046a08000e00b6030402c4a060100103040c00040c0401c10005140c00000005000040b0407a03102035036070b108a10662143c0c40c02c5038200465803101380820a0603e500d101a24003030b1400540080076201c1c0c80e0411174100071021404080184006040ca20550032200300ca1044600303114004681c0000780e00709a40100400032020380c005483c40754000030040780045078045a0a100000c1c14070315494640c3c1d04044c640080c801c0800e841c2c00407240e40c040e05050b804400d1302c2d00d00744080e104050400103459580001243c10054800200401d00c0394040e010400086442d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 430729289 1250 430728039 430728041
    0x706030b0109090b0603041e0803040305090901170703150f150305071707030803180313030203060c0a1e0903050a0305210408070b180114041407150c020f06030a0b040f 74
    0x2602d139107812180a000040000304d00300c440906080305054503460060b00d654036448164001c0f07a080300080c80204120400b03083c208015400f4003074150880151030140c01c07a0955640300d0780700140983c948075501040c9428203500c0402c0c4001e061905016000c404140742410325103501c011195446a0b00d00050340800e00b05a01c3d09d40c28000d00a8103030b05155889500454001900d02d03224030800051148408c01c0410090104a010801500f68540340d801014203000c030017840e91a050004002001d002607008030411403540a401840c070500642450032103928405400003000c51250080315402d240d0010090801502d02e4507a90751824100159514030038001d03030740240401c805010000c00210b0079000c1e503a102c074101043c41521000e205026003510000c108000c00c0402410a01c001c2c010b9041c18000700106020081400c0c1e807401c02c030034a0120460000c0d50070841103035030460071036a580d03200c4ad0074800010310b55900c0e4104200440003d1080b242c40b580b14a04c4c1002d507080e2701c0700d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 430730539 1250 430729289 430729301
    0x10912051c021f05070216030506040213020a0507020d05070509010b03010e0901060506250203030a03060806060604050a210611040510111908070b01061808150a090302010e0706030b010909 83
    0x925041402c110201c3c5200c00080d12026014100354000d11005e0744c602814000d0110045019100410079420603006010a0071400d000000e0000d00404c012408503401c9011a501140d06982c0c1c10100883e17401d0903400c003a0950040381d40b0294010002600388403013409113040c1c440c16920003240b6200c0d06506402c9840f2842000c0c2c001d00140459040c00c400c003821131a80c1c140d40da010101030710b00c1d036001030300310f90102c1401e5000c03e41e549018003a00004010803580850240e427414940b80c208000190344a106101f000242c101920301c04500300001140c0c44820303035200500344440c032644403c0e0145074016000d0031380121980c402c0f01012a2107200b0700c40d4801c0f00d50700074207410030003501043c040305103002054030040001c00c203000c00540b40c652227a00a00461707607002031818031107654115219160703022002a40c485584040b5008100c3c040c1500203003014400a01c13040c0034038060b40036107542109039072180540744000038041e405401403074001c00240d9034905659180e0380c01c0301c01c41e12 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 430731789 1250 430730539 430730563
    0x7020f060a110702150a1206050d11030f0105130312140a050c0c030409020d060e010308040b090f0910090f021206060702040b09010b07170405061602010912051c02 72
    0x4403080119082454540c000c00700c22440905080c50308409030040384075080c01524096442100040c0c880350341741c1c400320303100308000e05003400d000062038000052207664040901815002c7d0310701d845a401da808000006540300b2487c003d1044e4540102d4040490f1400d090a41c00b003200c0190420b4040040e01c11640544084100307820075854402a0300010034008151000240d0b082007452141c01c1c041020300000c001000340540c0c0c40741094179501c250307050b80d80800e0082c013520005100042c9090103440a85580340324443d01c0ba0014400a0607540084046540081030f45007840582407003400c5d00400e82d07082460034080e0b020354078240c004038403c0103085e2031000368140104a02c1d00e0598004d003802c500040010900009005c002003644c0070a0740100311803000060007034208480400c0b004640da00c2c1400450500d45003201007901c0b44207a441525003408080b41240c11a801007907454068010324984114840c02880c0c11580e03803003402202e03e240114240d8041003e440010030280400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 430733039 1250 430731789 430731793
    0x2040311040c051e040f080f071a0d021e040e0601030b0f0a03150f0c08100e0709120f120203090f040606210f0f140f0c031f080f0304080607020f 64
    0x300f20941501340010007030441c01c24100000240d614226601c8005032500401a2500000e18081039160441076840070001c00c03c016100035810600106a9080044d000409039503849a800707817940a1010200c4010040c10205000c03408410010103280308560070388040280780000410480445100b13070700b295000031004414400508040b94030b0694110f04440408e80440d1030800e5030580316070510030000100c040c41044222041c200030603005104261043d940c03428900c40081c442e40d01e501a20b13241400c4892540b00300410048141416501700141606600c0e0286d0300944a9009910152141c44010701191243c0346ca0b1254000310742c003d0711060f08001b03c3c1380755814001c0890a40c1210b4907a56100a40b08400030b016001c10f0903908080000e5242c990845108001e0000d000038100122050401920081c0542241c0e04141e2500c03c488001d2043d1204d002d0900c05600201064000c1c2503e861544000001401c15120182d06544450b81c800c042241c0e1406c10110b0b402c816 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 430734289 1250 430733039 430733047
    0x305010e0606070303020904020c0d020d08040521070b0c040906050f0d021005070c0b071202030c0a06020d0b031203040c08150609072609010b010e03120307020a020a0902040311040c05 81
    0x191500300000d01c010f40c402d060150030100c1c00c5000500301e0f00309110802052b040f03010082e005a90500c0b00080360559030404502500313154544550700e00d480800a0010380200c040c07461294001030035654155804401c50216141c820f000401c00d4029101c3c0344047da0418401050074505030003103490001c006002c560411a1a8003041190186c2c00c0b00d04003401020046031001c20740070b00441000c1c0c0341e00c0c00790702d6030380007589072031210b0030b0a85280c0401c40d0018000503c0541000c03500141841c1c001401607103030001303203501400400440002d244e062180c06100d041c54485400518420360141e940c51000e250740721201601d44540c0d10803d241c0640d4480014401d1034a624902d410409600d800300c0119002420b00b00218030440c05121406282c0b0f082040811090040c0c2110140c2843c10004101c0c0000c08a6a1070300c0320b640e003400844001c000903544500c200300d642c00284d0002c158168056407002c14400a61084c041911a00300d0a114440181454001c0f072070006010360304d079468 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 430735539 1250 430734289 430734301
    0x60807120b060d02190e0405061003030f0c170a0e040612080406052104050a021e060403170c0a080705070b040b040b0706140c09041b27080a030807020c010305010e 72
    0x124001c0001c1245d202c0c07031a0a6000b010f0070f400b08010060119200d5001e8281000e0500354507001c40100281c002d500318102c103000003940064008446d070380500700310030140300380c0c945843c02119500810700d01c0344001c1400d04c40550b00042c0b0f608019019241007281a4480b89036030140340c040c040c00703000c080d8104410001d6a104000030840d8600d01c0e1141441e60100740e180c588c0c210760036102941c02d03a00403608181503191040420803040b03c00102020200c5601d008600240110f1101030113450044071040c144407500000c5400c0b00c8400c006a5801001c0c51401804d140c111240944461062080100320034603000d0407502035401d0402c0507400e0900e0700c40d0202c507a41c020301d0308480036a12000c038a0b5015000a4180c1e024500c0b0071919a280e10710350007030004a404518641d101200110510402ca0b500700403207440d8a00e02c0174803610b46c80c80000102841d40c203640d00c0412584180080c42003856400781c01c4038000e04195090300c04180c0307034100440541e0020300503001c800e00f6440200761 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 430736789 1250 430735539 430735549
    0x100b0901110304030b100501110105190c020307140717030f0702060f1303060e011413020907021906050106090e04050d0302030615030f0402150a0903121b06060807120b06 75
    0x40c59699101143e2800381c50f0754904040303800c01d5900b44d0031208401e805009030741e0400b040800d01510320000300542d107008202c82501c2c0c002900c4980ca1141c0e1341d517541050901c00c5c4215565140c2284e500e25030210722000981d554120707407203000e07200d00703442c1220a201ca0000c0300321030110747c0214080c4c2c10030030300e42c081002c1c9502450442c0c0d0224820000c080c2c2c1d05044a8218000718000d6500140c20304104810741d09640c2c1d0040c070b51400201c15070400c1881100025094141901a202400c3c04d03070380d100302a45480281440f200a00029814010810401d5041241621429074407000c48907980c0801c80303092682610010650b8101a1044094611170390181d0313407018004280c3c130328829441040007525070090340d8040009010400704030950030024108940600560040e82c0391004040c0020000340c040c0c080100640003401140000d188502c14044003030f820244a290480c0140c030300320004020b1440380c0b404d5030056540019000401111298807180c0043d0103419a40c2c800041003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 430738039 1250 430736789 430736807
    0xf01062d020a0201091719080c0604050a020a050916030f110c1c0801031a0907050603190b0a05030d0302300703060504020301031a07030b0402030717100b0901 70
    0x4825005003400101902800000358000c40c003241c0250550118500004041203110f41141c00c081241020300c55102100090201c5078a1440218500382c1c2c0d81480c00320510301c1400d503410560700c130f45810f01052000101d40c9242c8540300700d03903428803a40d0326400d2124a61b41100e54030300703810104580303045280c066004a00c0f500103910700000c6504520300810850b810460341840d25612401d051480c0407080c44c5401101c50050411024661444d91200c08410744069a140714410300000320b03041c40410407040d4003402d0014441a1280307414040ba80303005c60404850340702c841c2030060f80320040c105180c0301400d80d01e0140161540d01d001c101c05a0107503000c04c1c015160501c900400c0c0c0080a040f80202001d5046912154906d080c2120000e050710a5604001c2c803a51040004000260900407580d0400e4a00b4115200b20b5480c6641603000b0f02d8842c0300c8640043c000010440c41942c068031482106011214000c425103030036246501c80140350280801c141001c01c02c0713145940c082e030455 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 430739289 1250 430738039 430738067
    0x606091203090306060b120c04080c1012060603050f0601083102060424090803070212100905070f0914060d08160b0a0f0c0c1506030203030708090114030f0106 70
    0x100702e06075243e42e024112000c81e442400b41c4007010901005184403030107410303040455801a2400c050510411680328074207002c039184503114183d610b080709400742950b01340707820150f20100910b555a210190240c202200c50307803880e4106000258096000e50f0050b80034542e210114810002d04100d00881c0342000c00202141c1103241c10707107000590f12080100050701e2112102d80001150f450a0503045e03900044107030910213803020901c903200c0f00105642e1455011903004001c401840003007420a84a00e5a10078000d0400350740c1c1c0140540052060100c44000c4500c811103640c5010010450b400300c82001c002d04000300119a2078602030726802e1900b0f024404240c9801806524121101c45801084802b14004010400707500c107640300c0c000d42d80c2c05100d41031005e4244c040300185000c1e024500180081c1c4507401305500c01120790700650141d070307003d0201c9a40d00958101030840e500f03e005120b00280130950340b0382c0c028030800e06a034000d0b01c01789220400d50b401c1c09000e490241003581c40d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 430740539 1250 430739289 430739297
    0x6070e030f06090a050106060908060c07141006050a060302040e13021810050406060c0f060518070b0c1905071815060305060109050109180f020c1203190606091203 72
    0x10051910014030035180683c00d40d9000b003891140910300142514015440301d010f200c00840100103417007010a02542c080c0714000324681c0c80401e13290400f0504403400342042d851242088090344508079070702c248240e40007140c155104960310760084040c0e104500510203d1900c08020951580f82410014800791004003220180b4000e849201501d000443e481c400013440302c1400c100b242440e00c900c0d800380103985006010201d035a106d85e5a0300c42c14510003468a0359403000a031444a043d20034860f0001302000390703004e407540c8000c40303280c0ba00114540c00c284d000d1003d10b46000720990b16103000c215400710251802c18031f04106007000101c421403411520392207035420340880c8820100ca401800707058800081c10b08200c0001011012107030410b605214a004061140e020314002a00c04144aa0360210740201c02c121084041d0180305519001d901c1500f18031038807406400040e610402d0500320711700c048086c0558034419102e082c480c034008101400d0f01409071121400c501800107000e820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 430741789 1250 430740539 430740553
    0x9011a0a20010519110a0c12030e10140f130b0403050f04090e0c0d150e0304090507171b0307050306010e12100f05010302280305010203101d04030206070e03 69
    0x50000d094680c2214038044040034402c4c403640310152446899144204185a9800c0006981010300344542d4100060810203400c440f0745107880c1304c0c1d0000c0a202d04188152456542c0e0044101c0c0580200c0106014401412001072040310044d80c14030310441200e800502c0429082d201c101001c007000c1c00607030030003008005549404803508004d100030b10807000300142d40a10300d11110704050310070200c04d101e4804200c50902080f01c4124461348011400d0001072404580da1425156104503800340e00c909090008204442d42c100704401700b01d0840c0300e40714060b980c400406c4c60550781c20108103445018103101042210384160080c40e0301c01d5060422401440c1800c000503005003e01d070790b1100c15805903011184007641070080b0b5206410040040c040b40d411540001c3c6880840d030845011182800d000300c4006c41c281514100070358020b4021580e90810184034480d03030f129800352101d01214940f071241c0540240300070a1003290194040d007030303d49900f10201c0305001c040300d2a03645845012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 430743039 1250 430741789 430741847
    0xa020f0304060903020406050603251110092105040605030c09120105010302041d061801140a0e070510051206042414031606050d0f06031109011a0a 65
    0x40104040d1145031100c0701564035520406c0705540e4150840b500510091092081c003070324142040b41c414442403900c080c8410420022104484c0d181c5ca405014031031103107081c1c209422070744400022400b44513110310a214601c25000040003500e03018001940c100b0041041a204801464100400c8400c49141007402c10005d100980b95400c00c05441e507650004004601d0300c0d1042d00100048100707001c1d00d4144c24580d0644a170001030503c4000c03000c00392140007424084d44040c841c841111340c0300505040400114000305500303c00908980b2800001041c0343c60f00151402c0702e18220350305c0354908045460300f0407141c80e001d415590020f88a22800400342c1c0005902c0132404500c2580c203000615200d0403202c003400030b6841900a0304464025202d0b0107030100d1050550b1b0460914645c0e42000c198010018a0181101f41c0c16900c0c3c52004004c00500c2542d10590b50411140749400e6629007141005002c040d2100c0050030804004112080340520107a98503550307840380442e20000e0340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 430744289 1250 430743039 430743043
    0x409020706051503030322080d1a010201060f051e0603090f0c04140a0b01020a060617160f151e0f022517070801050106030504030f080903040611030d0615021e0a0303020a020f 77
    0x41020450700580351401cad030784000091583d01400b038030244003c1c0b001c90f24108481d03a42d41c0ca103004103400380040300010080030202158005500c1700107080d4684d2842c15004607512058001c099032400d00680304065030074600b80c083c0342d000c034807010011640c03038856036404401040c440c50340c0390550084085610204d00140700b604020041d950002c0607040754001c0c182c0c141041c41685440c07103444200c01f40500d8004080781c405030b640760302c81001c7c1d14158507416150100c1e80012401c0c800186100d044003554040541035901202e5003c0310659000c500c0100200c003085204138001d45485581044040580203050110b0542c100542c1c0d40c039a00d90010030b007540c409801202c04652503505100c00c01d07501ca02c10b0500b00041d1b10704001e00d8200401e40b1a01c07403240d0320a4008124140810b400c800ca014000c03150040556101045a183e48030b040380000c100c40401d681c054041c074040303089031003018908034010f2099480039101c0f1600f07a540690094003c00c8000c000c51141128440240c201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 430745539 1250 430744289 430744297
    0xe0906090414100b102f030d0f06061b0f080306040906050109150503030a0e060307050c01050f04020f0a0303050405060c01021204050a0b24040e12040902070605150303032208 77
    0xe401d4041240c9450b0301c18420310070074150b0100c0c10019071485907401c0f0001031500c52060b2803c064115031b54811a00341070301c1d45c00b9608000380094504007030402c0210701640140304442d00c3e1b854008903041c042402c81007424007000040d0207883c0440c900e5000440c004011a40903c1c001e000090748000c0781c4071101191402d03000b60400c50303910071b80402c030b207042506100000e040450003145070100c0e1440c018001a04003007140e00070f0002001051003d4000d03015181019a40c0c00200b08618000401031000d5000341c0d0309902038000d000700c2010a0178051114000c0e04d4068a599262602c2e00003480102d51040c2c11001080d5404e006101c080c89466503072a0259008000500b41c011190400c020301c42c1c0042c0112101b41c100503801c0c1c030040c864003100540c92200325000a001605007400c2810107091900800c80c2e820b0000340800c45032041c5c0c0c017500015015600411139903959080000d10035455403100b03540b550050000070275040d00c1c0010103a1040190101c00c1030101565642c49490700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 430746789 1250 430745539 430745563
    0x6060b04090e06010b0a1704151b09090b01050a0e0402070507080a1106031014011707020f0c0d0b01030213090f030c03180e1b13031109070e0906090414 67
    0x1480b25072000c064041003200074090322540c14124541020341c0b01c05081c1001303800c0b0710404104050005002e020181070000c400c100491028000f01548136151440d041051214030b01003610000c000c901c2d1112441026070028041c1c44c0ca520b8141d1200c4d0944140b10190172040c0c0c002d80802910380094414040c07000101140d00051446031654901142e0350041402e05500521060080105044143c510072303084a440e240685043c00b00240102c0e03104804002c0d41115400d80c0041c040365641c00526110040a41416507008600580800080e03455030703000640020800c070018805450f080003130081c82040712500150288090351414282d1480c09003c1e4007140b1180361540500d40c11661407841030b003150350700b1416642008503000e6813150140c00c03a444059811041801c02e107a000c01c403001c0c0d001e40054000c080341d807807620302d0700360618000c568011021800419111405000e0046000c0d400401c8800c4039640c80b02409102d02008005440c0d618195400d880359460600044032248 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 430748039 1250 430746789 430746791
    0x60b070605040b0f04110d14010c08011e0e0a050c04090c0f17040506190207020306180106080303010b030103030f052203170a1e090e011e050f03031606060b0409 71
    0x102d401e082440700f014004000a4500206104000003d2542d5407882200e84044921b84101c034070714146072284842030312040c01d05610b0812120f0780380741c00003034540c101d400c0d40c0344070000e80718080450746040c541384c41900c03a40310401c4013003189040039030030003503110120744105405c169440c4002c0e801c1d15100f1210714081000c00340c4d02500581e00201d40c1684144120003c0c10b1814960f80342507895000034613581d10029801400700c03010312941c0403909100d80040407290340e4107084be98001c2801000c0f10208840d031822100241070303140801030b00d0488174034000315421a842e50324251824544000704904101c410005540c0407601c2c40c419000c00c0801c880d64500150035482c1201040b00c0d48883c480c0448810700111070107030ba0000f401d066902d12013044c2145c01e1042e20302074440601541262081c0501c2200200791080c403034662924843d010503050610981c0d40050ac0801003e281e041038040e0010080d4441092040c05000a80791140e240000c6896503a0000142c50b0402d0b005103c050f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 430749289 1250 430748039 430748041
    0xe0f060a020c0601060c05030304061a0436051b030102070c09021c02041a0c0106090e15100e062707030606021234020409080301060f090b0a050c01060b070605 70
    0x30340b030420180c0c0c05000c3d581807505610200c1d0f20780a90703900000f00001d0030a61180080c444072200d0290030203149a0150040c4044403880020f9002001c0711200d41498054070740d02d1091040b54201e91035a01030700b00010700008905640c100303030802a190700c180e40640d0204001000510006500002400c0103800142c48140c1c0ca08044190001d00c0d815601c0e403801840203200340c0d4900030040c0d0a543e0f060340c40c075642e000c0c044020303070160509034022009103180641a060018000c109814583c480d406a40b14591316902d28402c050b503580151444200e40030300003142030038040d038009078180e603005141e1960a072420079815038010032191180000e4071460100215901044004a81c00c006220b250510404002d180c4a074103210700c154410200701101c0021400851200c1c481e1035401400501c8101c040e801c10680d11b900a100d1280003c0e4000c13902134000348100305c0d11090724200b400407480c2c80140035085500d50000b01041e1615581c0303503000280f00e40120002c2651602c942000720345 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 430750539 1250 430749289 430749307
    0x412060b06070f0b24130f0906021216090509090a06050c0a020f03030613090c12210f0c11121f05060d17070602071a0f01060c150e0f060a02 62
    0x92400240200000b000c81d8058526210a5605c05c00540481a00e030b041c0070321a988502405420b03034800088100340380104200038800c403500200f034070f40d10741c003210301d5640c44201c401101002141042e070300080482e28140300e09d20b803040401c1d412440f00c4080300d001c07250a403204170840b1300545070400ca610000914003100b80e010b002010044c01d071080139505500c0c0040110748204d0000e007240400c1c0703603151011401c0000040c0030202801741d0b41141c0d1418810740c80c1140c0303070003004164040309100501b83c0c2a111881980101c0f064442903560118000940d0f50300d121190208a0460388500b403801600b0800008008000c016000c4106104c440301d90f489005c000c44901a0605004072404070000002c200342e000c0342c02d00c2155110020f40c0d540e0f96030400c2c5c0c009001e0010020142841d124001c0c00c032504107811035009070480b44030428541d98800301a1750101c2c0300b901c02004032582c50728602e0502503907488114901144801c0d030703051049200400d400c010301203c0c4030304056400b198400e2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 430751789 1250 430750539 430750553
    0x1e0c0a020405090d140d0213290403030c06110d020d1506020a0309120302280b0c04140f030709020a0906020c061c020901110d11061302060412060b06070f 68
    0x18101c03182801400013801841801021481da607410072501501c0043c6000100e0b40990440ea5500e2200c00c503201e0716600c0300700050031061003d540035540000c2c00d007141c00701e80e4010120380032641c2c5600c90f8908001c0701d03a40c0c100644015461220307080b0092000c1049001036000a1510711002400014028200300c0c1c42c0403000f240e900500110760112030440b00098001c2c000d8010307501c1078003942504910501c2d089141c803815020b070700c40c4001507081e18541e480d0400b2550305414410394280b001a503403100d494040d8007070384c4106105186410134454103410480243c00c00c2081c0a41502c0540c0d440f00c010000344da000d8514640060a0724504000b1180e05028400d48000d084541505d0845a19280307181060580300d1550420780c000342562942c0c0c00340c0460a02041004151801198402000f8010003100c481d040c00f24000c50700000c00b0350101050101020340c0c01024a420079060941c480d06003039640c1b204232a090759a800c5541c103a551708000e08005c9105030615251b0b030400b450101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 430753039 1250 430751789 430751791
    0x50705040911121803130b0301290a0509030a0614061003020a0c110d0230030708070b040c0b07060207020a080c03060103021c0f0506060301060f0b0d021e0c0a020405 73
    0x2c07048031030502250703000414071801c942c0c01903074000b181071405005484003030461090180103070101e0881c40001a08030070020146040b1800b080414040403141081502e11040406101a10750b070700300070314a070460103040500140c800140803980c5080c0540e90701d100b29401d840f042800051140700b048624a030205102d841112140350035820040300030800f0340b81c091114001441a001ca0782c80c18803d480c3d58000482c10f80d00180b030919103a166481d03600c0520741065031014900c094211a074000740f400800c40700203aa000540c18582038554030b60862204001d08102c42210292000043c4c00301c824001c7c080450040c040140c0d16800751041050078400d81c0d01c41d0a90b600003401c00c0310b5a40c1c020409031304494050b903c0c9500719103600a4040ca5a0b40d0100007000304030000a00b005210001900c24880d403020340c020042c0e0794a8000c090342810143c4901c0b450340404010410103000140c01800c1070b01c984c0e81c008801034a98488450554102051018160b8844006c0c902540b03081d029803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 430754289 1250 430753039 430753061
    0x1060f11150a06082a220b0a120c1e0510020c0306070f0c0213020c010e07030606050d020d06020d020708040303030f060b1e1b070e01080d020106181e0507050409 71
    0x1071106aa61954401010000340f005040e405810782e031020351a19481d1300c0d0786d0341c0c111551a401400c0c2062445900520306034070554028017456001040c0d030b003040e8a206101c0d64101c0c8600582c1403400ca400b1440481106c058026259140d03000101130710790110340e001440c2c0b5900542842007460003458601a002881c41c0300300300040003500003d0360001d5070b1a0038160140c40c985102e440b450200d00c06171207a207003001c00b958030345000c00302c1120b03002c40d0380025a445500c040c00007684e20b0b4100301c52076a80c054003030350000d9140f84613000680c0550040103902d503000b00142c10811540c480a1094004d540250003094580b03010594002c02c51143d01c01400400181c54203004041c801201e0400b00300500b09011040024110110a2a464280c0d01081d44000b08c809041d00d499240c00d01d02428460780310f0b5441010300c2006980e0040c000d80064610807054a5000c44240450201509183d41202109852540604c001043d14000c031032003003000ba20340590355480d104100084540000c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 430755395 1106 430754289 430754293
    0x901120b010b09100503070905090c030f1b090409060b0424080c0f0d02010e0d0c06120204081207080f0d090212031201060f11150a0608 60
    0x1084408900c40c00d40c01106990310200100180200383c2080d030312a03104000f0410360b520034000b40d41d01902c1440c00041039a03484001c14205582950b00410309034001081000c40204203090300d4228540400c40026446203001c40030960040d640c006200e2606c68000000703101e01c4c0d40101c800018010802c003c1c0c9940282412a00c2c4028a80b003a41510380356400501800302266280310fa010141200700c50543c540c0400c8100c0b580304004905020207044d0030f60441e1259100ca080c03271441140482111401d12002816039043d0041e1000c0301401001300307010482c0c02081e503603603813905503064035182d025600d048039817070040070301454403400045403505040c04a81c02451640d402179030b00341c015031141c0a01c1d41e01c911402841d01c0c000c2e0786202c010004030b84240c42c50201e0074200d1a0201d0310190540c40f16042c191052940c626070720300355080c03001c01086840b4241c002c0840c040 = true := by decide +kernel

theorem cover : BRFrame.Cov 430575539 430755395 := by
  have h0 := BRFrame.cov_init 430575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 430575539 ≤ n) (h2 : n < 430755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
