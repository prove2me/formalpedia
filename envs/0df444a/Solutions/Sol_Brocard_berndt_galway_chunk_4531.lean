-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4531
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:54:49.071169+00:00
-- url     : https://prove2.me/submissions/99883d62-c75d-469e-af66-c568012525da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 814748201 ≤ n < 814928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 814749451 1250 814748201 814748257
    0x915040c0b0a0815031f0b0316031b0806010608070f020106050a060e0307050409050a33020307030f0903090506090f060c06060907030c0203070605181e1603120302 72
    0x92008080450f080c40f0074403d0407040380e01d50084283d0101c000707100c1c0407504072450815858080c3d155586030707100e0581d50500e96050110312506110040f00a43c1c02d543c900302440d018500041807480001c500c0c0c000b040010000c45e541d07050f21502d071550022a261500200e945001d090328906c00c55580745000308203039072003480c080300610180d43c451100d410000d04050a001d281c2d400303a4422071a104480e00000c90220b060500c1d1504039107030008020b03028072440b8000d1421141c0b043e10360400c900d81c0705c00030a00d501550044480c0d5604015107000a110300c001c45410b8040034010480c81881040f085c504040102504030000d00001c4804242201264154100490160030341d04004104115070a006002c0d03580146030389018040010480c1d4040d41705c0c85140405083c0c0c42c1c95030001040310800c400c02c4a43c180c0c148049074002c40d80c2c81181d80c0b00003982210200d0b14021021100c0d014041c1449140a0b6600480c0702126090b4084003a00254025200ca5400e0400803c3c0c170030020030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 814750701 1250 814749451 814749457
    0x5011d10080c1c0f0b030a050d050c0a15140601020a0507090c0e0303040f0305060603060f04060b010c1a0f01050316090c030603020307030c031104180209060f040c03060302030c01080915040c0b 85
    0x120340c0c5004540f0041d0740d03048006856171003211a0280c1e1011809002040700004c00c450700380d00c0d03800d0a40d44c0d00070050b4078908080440070090640091256044511800e5034061a001115290884da103130300c942c401240c0f01d40f001d640103440c03907004100600c11144a94480406140303c2e00b850f40710b1340c0543e004a41950002d43c000e070107285007a4020024440140f00c8280c0c410f00440291246280c1403d4a200d100e00c00b404c0503000580c0d0740c090156a900949070001042e0300042001c00b492010404a000900c04946460003503d000c3d00005040c28000340380c034108a1049074603405282008132840040030401d02c50b00403d07840704000030142c3c13001c0c40708501450286c500d0282e01030850500d05070f40e0446901e03650245140460720a00c612103201c812200503412940c500c690f0300d83c480010714060140201d1607109103054070001032143c06a11040c00c0701d200344c051394141d4411400548076610100d072145180e40002d6a17204d5018401c9041d16030081c46010000380b011f40321459845250 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 814751951 1250 814750701 814750747
    0x6040e1b0f030a0f050f070509190204050d1b0503010218090402310c0c031d04091b0e01080a0c15050415032c03041214100605011d10080c 61
    0x62811450300c042c06028001c0010000c109801000005d1500c000f1549c207a800070040d000e910003c008032215200b581d01254003c041c0102015031100460801c548603000781903120a900149241c002540d040c10700a803a250b40080b10034403d513410300800d1205004004000f00c1e480301200f0302a400801401310003070021012643c900360400c140711520821142080c0740c0c2000d0105028100c0c00103944000c40d680042010036005c6040c07441c600200d000f8264021008004c0d00050400303008044d90800403200300c03009003240e00c40c2c60340ea0b68065a2200d01007035000c5c24501481d0000e100011140181038492071152910038a4150340303080c0b420031241c3c08422040040d8450302d11031104140035010a007640c0c01c154200b00e610003540d0780107036280310f148102008640c0340030b0b20400f405492041c8003034140c101003da90f00c203c80c0c90310400041940d4022a80410304482102c041070091082e06420b03404040c2448901481075642500e01a200401002400100b00402c242843c0e0940c4141409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 814753201 1250 814751951 814751963
    0x12180a0602060916260c090109020a09120b010e0c0d05040f0b06030607020a1401020c010e010b030d1137030e1014040e0a09140303060906040e1b0f030a 67
    0x541001e1603690304103080140c2a9103d00c4007144c0612840d191680030b0000b504204000d8115005450001350400d81c4050700207500850800001071b003440d20344c006040401460342d80d08121501e40400700c0040340300813400342c00c20107804014003040803290401c5411000807507070942000401e8402d030b42074030001c40c1d086800c140c1e29209502040450f060141e04180110080c00d29840c10350b10007562030b010204050302c29180400300c0c0d610312100707504440301410000300034480c644220403640d018007401503255000340300b03290440041910905000d003900592401901c01801a8a244041d00496507904510b0018064034400251003407034240251a219443d8003031009048010401141302c46498071050101070842c0742030034030401c003c0340c095581b079002d81c2c50184c0303407110418010110740070001c0040c0183c621000303800000002079481500700710741150040e5074000038402078500e8020301150a5002c41c0c0d1301c0f1540c461030401e5124490f00030788100100c0c2440300000703107840c80c29a0141e0300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 814754451 1250 814753201 814753213
    0x5100608070b030c12061203040603050108060c0306010f0c170706050a050c1c15050a060503010f0b161101171501021b010801050d03020f01110301050f1212180a0602 73
    0x54600034400400140122030400341589041c1503d03080314440c1501c940401d411400010301941d4454040071680d1f0514003c890b16961214405801050203004000c01c40c443d00340000c000485d00ca044911650040e920050030005521054a100008482c201c5501480e00b6240c4280c64525000d40640340c0101408103e074100501100202c440161009507800700803c040d41041d281c4007844039a00f078201d9000a20800c001d4415080400640c00103070744a42c032090b00007602540803001c3c5060714407450180404540d6420004204c0c8552148100c42002588103a00400c02c107050048210070181809803060001c46c0d46c20000440c03c8565555156410f2000e01c00d80d681040184a51015041c1d031031f02258440f00080e25485e01481401d201d510b0000c3e0700e80c00c0510a0152892105500c40280701040601c2030b01c0b01150024000c00e0b020311854543c16003680341400311442c20f04203180c05814005400718001d11203034000b07803c04201102d40c403080314094440d540c0c0034004040590180c26 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 814755701 1250 814754451 814754459
    0x2070504020a05071a31021906090b0301050306180c030106030506150105030f0c0309150108280c15020304030218011d040b3103120507090807031b03051006 69
    0x200d00c81158034959400010303501004951b000044460081c50391007008a1320040301545400c4a60f0740b0300800a400070440090360988481143c0e6400680b8181d4440138501e41e15400703c1c071001c2c0424810658113030b0054020070b0300708007000e030304d0003c2440001c191071038071140304046800c0d11010b60040725643d0107101000441e020501042081c2c00f42441d1282c51070500300116409030902511900660400002041d4018801c20100206185103541340046603500e840741c64a4081e08019a0040000c0e14410450601d9a004919080d44d01020b50a9041e042c40c10900d503010301c0510300030962104010100240c0d69144061202001e4441403580c1c5605041c070611a000c101c2d040892102c240e403041c8000a481c8102d41984140c060601001e03504010306d0201d6054051a00b005503207600780100e509160340244901318440c1e1440b411300c42c64540321000ca03024505841100c219402c8504180300003490b0884041d0a100d080c0c030103d6000d602c948030301c0e05001030504204480e65403401c00700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 814756951 1250 814755701 814755713
    0x51c0b070c17121501050a120e0a1709210d0c020a120501061401020c030d03050c1611210c0f03030c0f160504060b03060d050f061602062406030702070504020a0507 72
    0x4c404a401c1c80c01a0520750a40c001403c02c5080818031304c04c003500c0704a01c4403080d4040194410441d08451008021120481c402142e5840b2440c2e1600841000c1c408840d00b0016510309241c0807a18070042510f0108498211040d200c100e8089038802c0e1004000508042c0e940a03082c070302c40c054400010b20700e181c00303c6203041004e030b40e042d503043d9000301c40c0b000801da1300072500340c05600040c100400c2e03d0344d520f50b55481900c60b01c180004041480180d5405010b40c409400950f060240e5001c6c51401808180c24200381040455003000d41c4085a40d0b134542c24000d140740290304001e001c80f07080c00600e1001c1400c2c4600d0081c0d50502c3e41c01909a010403103c01c8030b5690040030180e40c1004207508010501c0f0192200808a50040800000e103100b000800c2040040704000e40050707401900b0302080b84c1844440d0b40c40824014841c80022451041e03035401d00f00d28034083d0666001c00c828222080c88000c0c2c00091201d025400780040009142e1201d0004081c124225070301d07a0f9603000070f8071b003503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 814758201 1250 814756951 814756981
    0x5091314070603051003021f1407060c0206100803030c180d0506100b0a1b1a04120e041515020f1b01030c050a1d0301180c051c0b070c1712 61
    0x80c1d400170f00b82c8004001589501c400902602c004210010340c3c065402429660f8500e00f01200f01580c100184030302c14005036620242034110300764242c601c00e4032540300941c4900c003a80a0384c2040d4104001141540352100003c003240403002000c50800c90044000403501000d078803040c2c034150403800400011901032003c20010b4806500346904100092000802101804052814000300001c0703017002d0151078800c20040c03d080304d418a410b4502450301141d0401140b003000701282c59130851042c58501406005549100d118440760030500d4100a0a00d1280d08100c0300154010844180e0034010180580358024100c03e4809450b0920140014100c1c0d421107415130410509201018081c0c1e40001c040c141c11002d080902000112200040d005283c00c0c40c810a4504640f0500c10800200601190455404031400002e17000c0054003d100c141160000400c940801e100244141e4000da45081d01d01d0301078042c0940382749842011403408d134898446690006d81090400c45001141e4030340f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 814759451 1250 814758201 814758211
    0x211b080c0a0503282406050a12021e040b0a0f050c1f0f15080705090c03130812130606080d090308071703010b04150e0a0509131407060305 61
    0x20081c64555082002046800040c0c80c0e40c3c8420b040903100d6500c001c040c0c058910080c1d0000e820003004007020482e01794030100c15207040b10400c564100284042c000c1c0207550045000341c86942c0300c2c0c0c01b8409010000c2d40547e40c921900002c25102c02c07044600c1c40c0141018007600020302d992426040405030610500800c04420030004100d000700561300801c0e0690001c24800c0c1d0009540c208910410244c2240884c488815141100c900b04400c2905204002c841101c410790b40d0860316075080c45980c002c221500c4280301800c101040c59023404001809c12907014111403400e241c1c8103401c00b040ea407401c0d41e174a00d84400380d03801d103001d1003400e2203400000e10717040004103040f91003010003910360000e510018040c20350100340b000c1801900c4001e40c8000310805e01a50b07807580c50b0b1440100903081170041ca210710a584040b074a01601542841d450003d00401000d483ea207020104181c0b098000c188650025121000c03900042001407194113844840010b840c12606000c0c0080450f0710041c0703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 814760701 1250 814759451 814759471
    0x80106090522061b020d1403090d1409090f1801060302090a0e0a0f08040303200715050c2b020a170309070b0f1201091b211b08 56
    0x144103504100c16190308007101d0041c0103007070040540c200a0f000b09840b18480b00705602103034050742c1e02c80d0302254582100003283c446110400800c003892045000441c2c2e9268554801000c28005901410b401d05982d0910403049190081900100c0d410318019a14210030700c00e140c0c00c1c8005c0e0909c00c0d096044048002c0000c00c411440d42e00022209070014080d445280e03910701d1030044102c42406042c03802c5420503041c04020b03d01d480c0c010241d5000b40b00990000d911200d1300107000980000c0803d03848000c00007440014200000c4681038a515440d0fa014440c0030000a0740f940b0341070104801c110014100d02050b180c0000c2c0294071401211103040c21500005469400940e9842c2c900c070140b01903004403622a920700e04201e01d00b42858102c0034a580d80498103100e14402440280121841400050300d140d0740c1e04500002d03100a601140566034007071913a000101c7c49005030040d0003030041083c000280c0c107020084100c1d01c800850030110000403036602610341d00302e2051600503d41710707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 814761951 1250 814760701 814760711
    0x90c0f020a0c03030e1201020f0a0f0207080c06030601030e2a0105040b03010e062b0203100c1b03050412030302040e071803080a0504090c0507020f010509030a0b0c0d0606050408010609 81
    0x1a8889010307002da400020180691490503140c4c6071101d14040f82c112002e0002107549040c14112600c0980000b602c82c40007554044040303120910114500040343c2c0c103c8010200ca001420410089800003070803036040599502900d11f001c03004001000042c2d40c0c0035141c0c442c4c4480040d4060030910000c48081c117000c402c01082010b001c0305402c407411918246680b0009403955000500b0f0752090f049034113451481c064410b040450388268034400d0510890482d0100d042546903031090325103d0050f400810741c0e032104405900a00090150418464545545000d40b034403d0082883c01d203440940002e54080f409124000c211403900390804254100803114600c8044081c0540505000040a942d0003180c01c4541a0007403041d6005440c07501402e000a04222600074030316008040240d20510480020780083d500400480320081401f50150002c002c440c0c64120136210b000d0642d12200c0701c100701c0200b0145141c401c8802030919695400c0d42c5502d003010050a540141c0c0040350868500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 814763201 1250 814761951 814761953
    0x60906050a24141203040f03081b070e01060e030a0c080307032c060a050906180f0a0303050a0c050a050a0b041202010515040b030a0c090b1014030a09021207090c0f020a 74
    0xb1643c1c620f004001220400000340103038003028154041c0e82c1c01242d01d4182038101000704441000504103a40c919501880303440320000c5920354901045c0b150446c076100e000c006120541c4140b4540208620140071100e98003810b99580380101703110350080041d9080419a07208041d4418000e240d2041c015042980303000c401c1041d03420065508118501c200c400007611300340b2501034415524034280050015896018442000150989480c191440303680900132410340341c94904401c2c0141c9815035252810403465880030360303920b0800402580c3c01c2c8030b04040100011001c20200503054401c1410300311f582000d20b080101215020503e4003564141000c2220b030450744610140e03001021240850080c1c7c500c404a070400c841410023a044540115002c203000c02c8a13008101030810541d04681c25801d403a00440c0c0d602c110345f5840f50011001c00100b0910a200d420a040080c00101181d082c1541c050403076103803070701d5548500c120790740310022980465040340313810302e06a0032800030308400c40803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 814764451 1250 814763201 814763219
    0xd0e040b03030c1c12060605280e04050a110705030a0305130b1b0412060b090705090618040b0d05061f080d0819090302010605090112050a030c060906050a24 69
    0x44140054101302a02c0c01c1d4404c4511580c00002c3d001d418507410059581c4518005046074083c0b80108188200303400c070300045406650201014001d0b43c3d94610a400703980c42000701800f4080d08034078086444080381d580340d811140007008207030310a0005540e5510a1900a025901c00400c40270707004a4003048180402c0300141d469600c078950294020602c020142281020b0041d90002d00b0311003030014001d01005043d500c0011f00e44070440701c1507800c0e0b450060841c0c5600c0b40b00040b50308540d09200d002110890f149142025000c01080031805813024404151414071124060751b0907230002c1e081c459040d4420580c030310f4520341c90410400460070160110707540c403c4d8844000c1007240e1380300029500c44080c00f810440044084080c04218100e040090191400d402802d1044601000019240420707102e0118050360010241604c0b000c162416540b07102404d10955072180c0703070b90715100007500d40e10845104102d201704c0022403c2101403100744d03d5418881c0c002404514240520074034038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 814765701 1250 814764451 814764463
    0x170618030909070e01200a051509030d0e0106080129040908030f1f0906090515010c03050d06031b08011d071e0806070906020f030f0f1b0d0e040b03030c 67
    0xb010b003400104d0b9800e40700100c030b80d6400d644461448002c01d400b1b40304506004a80c0158160240003200c040b220b05008026071440283d0741209194020050308440306655040010120400340c00001c0450707803840c8060079501030101030990542044504c4003800031610401007040c40580c0c04000c16000d50b0f40e86c840ca480050030084d0740403402e000054010400d50300307a00c8000c00c0c3d0b45004904503510b00789071018022502840140904040011b80140411202d58500560507074481f00d038007606807020348440d070101c043e00e2515a01c80801102152424a404082d10043c0e41c99003909840c200000d421184c2000240c10b502581d4030101c3c0d800f0100103800401e0b9406050100c2102d441d03030341ca441000c80e15900c6181030380244000c1101150300100044108d074015002d0390202a0518915520307480743c45180e203100c420a00c0b2254282c0c40241c0540019080c4610328000003000054251428000055000028100345111070103420b20340a20111004c044d8025030414405540c000e44a00e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 814766951 1250 814765701 814765711
    0xb030c041805150105030c07060c2a0f06091a010308040905070201050f010302060c0a060e0a06050702030705120f0d02070b07030b01050c0c0d05031204120e1e0d030504170618030909 80
    0x40340220100d01024030b1501260015039002740c003004401014480a084450024a005a11018140d001c06500803480081008941c0140120010502d683e0340038000c14021005840b5000040050700c0e91070401c1c50381b1406076002d5075183d601c41c2d1500e1445426560010114000c59042009014038001c0c04000141542ea0480e44a030721241550308640c50005044030103040203050450200300c0080120300000c41c1802040c09215a40d50390005a80e00c1c03040c16001841c50b0300011860241640240190282031048014603140c4210f00c50314030240d0b00104c80039103a05007000240315415805120b8600c1c03401c0d0a091042c241008040301035200e50743c503d59580512202d20070041000000d00444000c5100d024403a089814181400c1c00c440004031040404a5000308400000b46061003d021808202c0d400c140c6c80c0d80103c0060000070300c6040e0086091280a100c040344e120000d80c004030350088581c000b48003d1802101c0c8940700380c0018003652054104000c0041107454103486c00c0e900c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 814768201 1250 814766951 814766957
    0x90303090d05030d062405071709010c0c06120b090105060403020420040e1006021603060902031e031c1b0c11060a030203240102061f0b030c0418051501 67
    0x41c0c000c50070b000303003584144030903982d20914148001c6407032225000b101100640c904600041840b0403903003900c0d00d2103882009062510b0b5040c180d070f89800920010310702ea60303041c94031007219421039032140701700003542d08040702240a480304034101d8043d91103648004001241e071001c1035450480032418901c13039408064041d0351280f14140c06550207040601c126075918150b5642d42d07135141c10725002c0c1441134034020150017842000041c41c910008032500c4400d918001c4030595403079039907104020a007803101260140140c581160980e5404103e02c500d031201c06004c3c580d2008540400d42603010421071181c4110310305503c10340d160105020103003082070039080c10301080030b07075080607401c0210f0500300c290702c0040000c040080e2507040c0c01031805020000301c5800c0429404805100300700946c2d50850041c0d20000000b400805603030209491032100d542c2005080c0c2e100c01c0101b02503441224a1300000200142c01c000040356240c004040942401007000176040c12101031007480c105001c02410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 814769451 1250 814768201 814768219
    0x7030c02040b181f0b160c0605490510080703211b0609150902030a031b0203010504060911090f150604050915040f180b0c0c1f05010b09030309 63
    0x75035452540e03160240407800c55040d06d560343c00c1120b00c2410441c540480c1e031800a000b000400e170b8000d0041d9034a031004510003401440300c0801d182e94200060080200800040c001001081c8403402464500120200d02103258640200410b0300d0f080d89512001035948820001c02c003080c0c4461034129400c01c241c5002540800c2c080e011501c1f8019172000c0758800300015400700800c05150301465009114004402d54042d40303000302c0044592818010390107030482482140020302c210020784207045516906e0b0030241c2541c010a003103d03012101154031646d18001c2d1018001001c103650126030341224002c80f5841c0120b10f440c0d5a41e000b8102c0c80c0402d0650100c002c051b80d070101914003802c00540611030301d15040c8440e0054102e031404042c042c61800c40c8444900e07a45006241a103000d0200103a45100e1580ea0104d1440c40181551800b2100380400000d13500c3c240002d8403e0840d0090040115941c0d030306201c11588103074000400380804100b42112030f180402580d0462500722a0010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 814770701 1250 814769451 814769491
    0xc020310050a0939030302190206130e100b030c04090b0d14100f020901140304020a030606030b0a0e03040e0c1c050907030611031017010b0607030c02040b18 69
    0x4054003034004000c220003442585202a4007004c8269910903580c03860a003ca60444c18030b00c049100180400342c0181c0140c405172011140200500086500c090181c3e494080300900703440f800d0318150040b030f00050810003401030104414001e18041c041400310341d0320f14148002d05a0881c401c92141c42e155913183d60000805641da28400e101300f40e01301030444403c00000d520107844603015051540c50920740704100710f010070035200360b50200c501038440117403c0c50048121401c9400041007203902c003902080200000d4076500905004520071900d11003d820144110010744000c030340342d43c40951040c80100400f01000011310740003605d440c1c07183e03640c805c4c4c0c0e030b00c514a600c0720829016089051109010060000207251011a40110000c11036915428400e103a00e01c015039403040010151001407002d11542406001d00040880000034041c501e81d000c01c107075801c0500294003141410b0020b40950405d80244441801d04840c071103034001c1c800000c8003000700d0250000c0920050710030424 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 814771951 1250 814770701 814770721
    0x121413110d060f0e06010303050a05130b0f0915070c06050f0c010e0f122a10090303060501030b030a050703120c050f07053111120a090c060c02031005 66
    0x80d4908102420040c00403a250030311501508004203100761652902142850507900880c103541640d505544207440e1045078107007122035404c40c0001e12017002c1c039a1400510345581d84011710b00c1c13040010010707072a440310f041040b0805c584600303803254442c02040078600190104c01c1d42c030300755000e504040342c55410048070352075240260505041c545d072a0018003001201c0c001a0070089000d02d4003102e20900b60340400c0a00d074000d4000768500550b090864204c000c5074145d032a0b441c135000c0012503a0000c034030613010003551007441e0160046035540900744182d591501641d83c0740f035415030042002c0c0846a9403141c5e201c400c0d200280c82a2416148070400610581e0480d20305c607001402c84880b01c548508980c1c980e416413150381d2203510002004030300c180d4442806004003180004501c0400744038816a0b000c1c140704841c115807401c00b041006141c0d40c0c040303c001e02a00e041c50001a5802051901640c3d41400743c104030b06104806055400603500000e80004040303090f1004206a140c83c6080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 814773201 1250 814771951 814771973
    0x70203250609050601050a06030b0915030a2415030f17040504140f0a1503030e041d010905012f070213020c030a180609260304080a03121413 62
    0x10405820035100b64240880080c90606a840880740c2181007030361002c05504a072140041030360003a000e5400a05440b502e00c214024002c0080c050f20625002c55807410350100b8501c0700b8000c403686240e00310020950b14810062a024a0b55070b08040c0c03420341d154103010000d2204014008010100c001144040f010199001042e02030810302c0360b0a01e04104001e1620125808440048903030b0009900a02c58042c400010450544540d08181191812035074080c1200020303030083c0c2c594410340741b01001d18052103074450917080001188205c501e4441d007581c600102c440c91255291214444081c28408003094650030007030810f69846040c40490540c84000300014259840415540e990110200050551707400359900e111504040c110b50124010f00743c024400080c584400c1030005840d1001e504981030b10360002e802d4103e9200446600d95405608282d003140c201a041208160b00241420110469000305112105082500e44280500141105141d4000300d0b1103009005881c024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 814774451 1250 814773201 814773203
    0x607090b0d0f0f02120a11070314070f0f021011101508030f03010f0e041203050a1d03090a14030604030c0c08060a091703150907090e160207060807020325 68
    0x5002c3c440d90162150003e410601100354109010000181122610b1107610201d4201d0380c183c600b40402038804a513482e28010103006802010001c2401003000071010070f0403140301c0e1041400b2080b092050081c2c40520488110078001c0f0400c111111480119900e165101c0700c42c0c000801c24503542d5007140c46410744d0303c0043c0b1400b0000d101c03400342c07402800460503200c2901d01606040c0d0780f500d4006224904503009014800b8181443c0c00c6544030341c00080c0c00080011001c1481c00c101b0444040f0301801000c0c2402d1540005800101824040d1080c00200980d05a0794000003503080400c2d151980100002c4c1006840c13000c4030304000a104007500071740950b50442d1003d1810980c428001d0402e644143c52203030318400c03080c11038217410b0200c92048140c0705032840c524101c482171090700d0002500c036500f40590641c011800c0e07000141d416204007445030f030801c0754903500314000c7c0c00c1032101e81060003000070f08003c0051858001003100c81e040c10720340510021146100304803078460202c0034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 814775701 1250 814774451 814774481
    0x100b040b1f05040b2223090a0906021603030b010e0a0e1e07051315022116030503100911040303081015030f06062105040c24020f0607090b0d 62
    0x40b070024100403d0f00c03500e584440317054091240b544400007000e07680120348000a8401c0140d050204500341011216001505206d012030800000d513600e6044c0d0b08040e48417000d282680813020141503240c0181c21600c1c40a0a007050720a00e110041480030245000b21042c0b2a02d480c00328082119100c0000c10805900c0c1002c2601d06104200411541c0301401c881000d03840300001040e200310041150200f030a0700d8004003030300d880741c5a1042e006102c1404c42c550a410a000750281c01c2c0159001c03040076071203035462645e80d1038244210301c011f0700d02e9001180450718143c444c0c0300200d6040200c0382079a8141c24992440d5958802481ea41c0c5115000045450501d8481c00c04240d0550060222119042024005280c40e007604941d13407404103140c8014820051076201680f91241c0c40300e60031600a143c1c1d41306441e152906440c1080d8403044004a003c5038100c0e1640c000d6041c4480381002040c1c4000d030840e401c0c0440020010303e03007801402e850038000601c4032211002e940c06641c54240d0700b8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 814776951 1250 814775701 814775707
    0x102040e0103030909060e0109090f02030d0504051c0201020c120708070b040501030f1406191a07050709050103032a1502030106140702100f120e100b040b1f05040b 72
    0x240320011603440c284403c03008501d60380000301c1d900303010340246015a0003100000000d0780c0f82c60b5000c0d01410b103021003a10590800e0036501c0141c0c50a00c600c41c0340d6000e42c1c4401d550355103013106008185a00752400751030050326050700340041c3c1e400b16100d500c1040c125020890f030881c81000a0610150343c1c08800e452003602c10001e4201c5011025208030b50707090b20204119024441d500d819240420b002960301100f0b1800a40356150400103000328142c0c003c54044402e4440e2a007040d6034942222012401340041100c50810904204407006007080c40411b0159514594001d01480110100741400d481c5d51164032022052030010f2461060300b215070942000c2c2444008030003540f0038045c2c940021044030058a0503404001181c58199000c1c1098940a103141c1c0c08840d0000380c900140c0130010b91100e401002c1045008000021702d01c40041c29184052080e00c50807034841600450052f42402d10300c08c844e0380c59440c0702071182c02401e681040903002a1045809100e540c00503080c41c0004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 814778201 1250 814776951 814776959
    0x15191809050430050f1e040918030503271c090801180803090c031614040c0c1401110a0203030604180206030c1602042f031005040207080705010204 65
    0x2681086020b540244000b0185400b0069048103002c2d180b190015246228410202614400c2004110300c4481ca4078a608003c21440c00311a520000b84031100810340104081c001130041d4403e82c584100805514501e610f525500500503000c0100000060044000c01c80b100305902042c1100641c07140f010340c0c5002c034094003c005045d030034024040008800f210082007100d4140328241c003210342c142d844103c80181d59609416503100904241041c014004071a2480e10708101d600034200009800600090030100030056503154140c825106900300200b0303075400d80d088607035200c64031b401c003094074405000e007907546016240409080450400015442d05c9003039002c0041e5005490895050042100c40460b10444001107c0701030750000040000c2241c600001c001014004003204052507945007a0300050200c40b65514050b1101c60b0b40085c64400040310103440b019081d012036040c0c203500b498891440350b00c10a00915000e03643c00111a030900142e1029604940e902400a650313550715 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 814779451 1250 814778201 814778219
    0x60a15150216092741011401060c0c0503030418150503030f0a0e03030d0606020d0804150e010b0901031a0f150f0607060f0515151918 59
    0x1a02d25603140c50b99a5040490b600c08240110051800c4508004e2540050107220b4690a030548100b01c9689021021013141011140b000307068220750b440749140140d03184610ba441400f00c044001101c2d914000a540b00380e800c1003074142c1906d10510300316240b02010f142c0000403001503000725a040c400802d00040b4111507807548910034484050901824251001001e003d000c903019441c0d05800074003541a4074400e20000d000f0740901c9141c070502c0d048090b4003180c110f50180c0580701419403207800a100350f40d01006049a040b44c64035001d203080c0b43ca40c540e0000903090300c0c10310440584404e0940900c8200750001d849240c8010304201180d60b41c0c1c502402910301d51a0190700c3e620040000540380901c440403180f080114048290319400d40708100070310009013240d8203502a40078000500403568601c61200c003a9801080043c80b4240000343d00d4640500b0301109112704511005200c1981c02c0c001a84e548203d880c1003a202011411015030702d28070200842e00c41c01c000000005100c510f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 814780701 1250 814779451 814779463
    0x203101d01060504110d09080d09031d01020d02060f0c0f03011410022e060b070606091523040615080403120501050d03121b020105090c030609060a151502 68
    0xe000e402044030b03681d42d40030711040d94601c01ca84030b824001403094402c00816904241e0701644224400c40c90b1540201040b400c440b081c00d03098000507a0881c454010600002c0f01a40b0b20320240001d00442d900c050340207607104001030200c0c000f1100c0d40301103021a02401c1c243c58400c51291040c64580d83c68076100046240d075110050321554503030b000c0c91520750000c1b80d049203403184800340c05080000e844907110768010803051107092a03500d00300064a600040050b01020f4840d0f0b00118165107000407100a0761080800c030300c641c6200050800c08002d04000880b10000d0045040100703040340720000c0e00414203a44800c0d901a11501401d100c135901a10a40c410340c441e40368900440388951304981101c0d000d0044542052010030020b002c40c3c064101c13142c10740c054080116603500d411040b040c42320000c0d0007200150b034468050081d001030500140071841c1e400c0d0020141850806106543d603200070b0302107072000e43c0d80d40c1a07020100c41e004055003d840c0d005202c100300b464800e4000c3d0780c0c417 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 814781951 1250 814780701 814780751
    0xc020102091203130e220206120106120b1c02011d150a030507050f040501030f092306010e07020c150702060a120b101e030f050103030f1103070c060c020310 69
    0x1090020104141711042c0b255401480d0341c003150400103041071a0501032844807442640d1010f0144004096031094003803280c06000b0540d200d6088242d0810302100790fa00349000c807032150002d03880caa04c054504800b5804080d409103004651644d115052125103051034010320740141d0708000d400b0054904500a04044400b82c2d410032103035850f600c08441e1401032079001458584200401c110303a600ca60049401503d003d00000b401c14956039a03801700c00f001c00040c010000340c0440c03c80c4007a4003446014014850710f140c143d041c0c541100000c0d1030700001070b0341c5481004bd4250a900b210320010035100480d50251619944071034000001d41520a000e039100b04050130014401858100b5012400d040c035510744030024042908030006000301d1060514604140e9215000e004446480c0207040c000d500a8076811911310003000010121202505000d10036801040600009506120383d0801c440482c40e1001c2d21042d14030010741042180b040c100040780c200500d650000c900714480340c41074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 814783201 1250 814781951 814781977
    0x30c0105160216050d1406101703040b0304080703140d09111c0312090f060501080601060504080705010e060c01090b10050d0302100c1709100b040603080d0c020102091203 75
    0x88010410126581d00407a040703c1441e104052040015003001d01d482c06645d446501e01444e010307444d4842d285841c01c200c500a4400020742001c1158807886070300d14400d036002002551406085c203c5268280c40060401009079000040306070526124030301280407503982c051b00c140d603000b054900e080544044001950440030b006605140f0340740c03083c209100880114072216010341251401d60b17400c51600070f0420180c3c0c89403480000910106414421203108000001d0303d54100156107141c010705070060010301000b0070042c448604001001400c88009180c0504003028103c0030030540d01400255114941c20b010700b600400c040300708203500c1404018030310b0740440c0e41e40c0104001411500c9020300960010000810010b489810a00390480d950800801c0d00400254114810604903942d070260342101e204a6482c3c04c1c0d0f03001e850700303a6004407000c0c01014195180d1035614824200c01e030000d25500e454450619000790151244624020032002c88005000c007540d440303a0040101040f2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 814784451 1250 814783201 814783231
    0x3120310090b0306040b180f01090506220b040f060e0309040e1b0108090f070303020609010e0309060d02030601090f23060c070b0d1410090c140901030b04020c030c0105 74
    0x15195941c411001e02da40000e0040c101602c4544481c21140c20190028001c0308840d40752980031102003004030619620b901c00018480c0d120708125003441c2c400b0f45a1505032441070800c000c003502c40001c4400c42900300e15110300d651150f24005120000700f000040007641400c07205180c81d10080080e040d1002c0a032414010100d1010480d5103964190b903691225421504d2408800d52240341125400050801210040c086040c15985000c02d40da20440059100008004030240207006020342c12840310300650500850b0000103107503000710188a03860550110008a06030b1060765041c00a0001b002805040c5880d525001c92201d48145900e00604481881c03d0640c14410200e500701d407041c80180c00c8907400c1c40e1820103160300140203105030684076241c00c0000c1c00d140d86403d00a40c000f40c1d1400902c3d24090b1203038240c842c0c4c00000018090310300708825507800900200c500003507003480d0020319079800400040003401046d410340c03900e10012641202c08081540124010300050313a031408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 814785701 1250 814784451 814784459
    0xc0c0604060c11161e180b03070e100b090321031f050a0506030417040f050a0b0c150601020106030c0e0709080706050f0f070b040318091a130b03120310 67
    0x50340b044c910701c0c0f04540c200c001408214a001a040814000e82c0c8402c4440b82d240d41c1c1d0110300605402000b0703c0c08101da070b450000c0c0300c0d440c0401c4200010510301d60040094906050310b080005140d1017550991000002c04903d10343e014040403c440540480901e681c005541d000c203400e0308201c6030b003210182e503a01c19400615000000e04100c074001405030704031900305070611076140c0010304100c40310149410000103015503000900003801e0052002c11905151004100042d00194042c0000341c0d0300300203800881001003521211800c42e041d50410a440d1800101c1c014126940007030aa080b956201140c080080600e145c01180955910030b8039948620a994440c100d520640b030110342e04104902c601401540074201039500030b1402810040d1a49a620400408880403000150102c4804030f0b400e4175182190041e00c0b46040070440860780c80c41080d0b0443c03c60103445c2c8a00d15190841401c844517170802521140301400351070300c3c0c0c40e4400e68102243c006443c11078a644082c2400700d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 814786951 1250 814785701 814785703
    0x60f01060e030c0609190b030a02070b0f0c0d091506090204050306100f0e040201030914010902210c060306040603122001091707050f24060306060906090c0c0604060c11 74
    0x10300c03d0020421450b280c3d901040007003010030805d441068041e144000110300707000704d002c1d500c505924800581e5074050b61402e0300319010b0040c00005010007550600040304261010359011451a40c4000f48003d4513041c110040840280c84054083c02c1800c00300b0311303046c00d401a0007200d4081d0b040f60019140c80c00c03115205002800350000030303c00c1c400100942c0900240c8984c02c14011304002860b10f0080e207882c80701e181d81c0111440941e4640e00e2040460404941810500c82a0556015000241d42400c0d440310742c40c01d805c5111b08008004904181e07900d44c0a0030003150f10800e8000c03040310314000540300002550404240e81d00c200107480500c6410301074515070542c08040c4120b0303000400703400704082d0032014096a082c4070ba44030703124865604111855111050341c44411413164042400d41101380001c1180c0d00a800100c1448580e449145007581c2210085442d403507150707240e2010141c0ca0080441c01466031040308240000d01c045130344100341e500500c1d59182074020002a01d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 814788201 1250 814786951 814786963
    0xb0a061a430b090d0c2001120906050603100c08011a1b01061a040b0406032406050a03060b090f01030c05070b04060b120a030c030c0f0203060f01060e03 67
    0x25154400c0d0700a824a00e18000400c0703845a881407400744680500716811140c800c00015011520720050b081072104858080014011141251901761060300e61030b82e03800b5542c41c040064001c481d4240d44410120780c0038001030140d0310b1004208010721b054034140807024001c00d03100180a03004a000e80031400b403050140c00c4d5922420303140c030390242c2d181211384a00b00302030491280f48120144800003d080340141c03004d403000c54000000c40c4241c10001d00c1d207481050714180203642031041000b0041050628280d500301c0791107040020344502c20034100281c40900031201c120000d01ca506c0400c0e2607030000050201c01b2001d9408005440c0c4414501f040c0384150520241e11030303110300303000e2025031007a0040c920102c0070b8686542021050741e07403a00300140540f022641140c443c0c10022840c00c108108500100381c82000709100806510064540e0303540403c0901000301280d00c0c0003e12000398090f07d4140d0b8003804442003450945600d00390b0300700a0203080001100c40740d10303c0d224a800194 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 814789451 1250 814788201 814788217
    0x306180702061b0c1b0a0b04030b011a040b0a02060106411e04030204200a05031f060309030801291309020c0a38040f0b0a061a 56
    0x1000c460b1034100d048081d800f100030071420110020005550011003d00c00703c080180000050700b1401c03c820100003c1c41041d811010300c8803002d000400116803c45c162504650351a01d415441c1c02c200c0171501458032990b0054110300c02d00140c01c2a80320f0f80098200d0480c0d81c266601c01150a0310500c1404002d003224030743d4800350b468100340e1280c401009c0007402c01c0340920b0380e030fa29100709287c2c0011801d003500744c00c00d01480003090400550030203000342142c4144803c40e86a81c801c0580c1507510314000ca01001c420031401100150050152202c00d120843d9802100c0c10050f0f5503000007070240800707220403800a5182c6c40005880d40c050524094265180503006030800c1c0030f400d0a092070b801003243e8000350a94442c001448aa940c401001c2d20706001010302450070321800d119041840180d0f905648400000d0b90b84207860fa0010b0f603204c117154100201c4115107441c1484600860000e4010300741e40200024070280380d0300340d4440b038100c80c48103c803484d100c4049541d4078844c1c040d00c08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 814790701 1250 814789451 814789453
    0xf03120105010e0d11040b100c03090b0301080607110a02040f020318010b0f0f031e071509060504090902010e10090f050102030304020306040204050601020724110316020f01030605090a020306180702 87
    0xc00c140010040403005e10070502c06400040c410381c115001900e040000050303d00820000001c9805044c0d01c02e4856026107003034420b0034615450300c00102e0796580c1c000d0100041200c2c90741c80c40c5000009015020702c0d035800030001d10207485800040c1c0020351095504c0390890251100510318404180070381480702000905081d10040c5020a1000c007990181020303606008855500303041aa41d2074480907400411002406a607040c01c2d41e991343c914815414000340302c0350f080300b000643d03400b40440b0b081e101980400305e000007062006880c41058003074555441502000240c001030351018603d02269211a074a2200c44e07541c0006a80303d200940f406074258003c000098050304040d00136582044061040340c0c54241d84464101c1100c000150a000c1c48074100600c620841c4e004d400f140d0415050f9025602d04864080134030358081481200a000381100724200c449a8041e41c07103e402044054840c186610f0108481c00c001d5104844e09807058404000000303000180e401c04910681840d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 814791951 1250 814790701 814790719
    0x120105091302031218040504051b06071707020d150b030d0e030a0807050a020a0602030a0f1b35040513020301030321110f07030f050f0a030506030f0f03120105010e 72
    0x2003024602d940b1171300c0140400c021306500c50500780c842d4410749102e80d004001924118155132116001c0c140d140a020307104120601210020034142e40c2812480340841910719600c01051001c68541d03440132002601c8112031209401d9040740a800080821304224181c80c100030076428142c4028008140040e0141c2c40341c000e00001500400c01061110b0003601203c400491030360009440d410307035030070000040e000814202d0449401182c46100a0381600b400900854001a0b44099850348140a803160f00b034158150b040da0302811b03100007030440900844500306165544410254414071030a40510421100070340624918829241a030b945644d4100c1002ea13034000359210f03031810010055a490781c1c0c125852100c0c2100c0002c01204400c490080e441d000a0308000e0814610500d207001170017810800600034246110032a82e070b810340d5050004082c1c5a44010070f1500b2042c0410918510a0b542d15020154001001e0700c9400d62a80382071500e0380c0c85100440f010080034035505d4011241c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 814793201 1250 814791951 814791973
    0x1407150e04050603010f020a0504060806030a030c02010e24040e0f060904080c070816170706021c0e1801031e0201020c06071b0f06020706140a0311070812010509130203 74
    0x950811904107000400124070315041c6c0c00740f6400c070b90100d0b0780c0501080c0006402c000b50f5800039811075101c44114050b10345441c60f9140508200d5985400038100800c5060742c580a5850755501e80148200c0d2400e90890b88038002c031804980d1290003440541c289400001e00c240003c00b60441c803d040280c10b0062503219543c0d140c0c1d403500316010007071003800340840110301527000b0000264040406404404c0d000d20301418020009a40103c5242640084806003c140d800096010030ba04010b8200480c20120745811a01440c0c0343c0c20b0b81d41d001c140b5140c6034030710200b140c2116068a010340c000c1300c0312100b80e80b5034541007441500c2c000d0150704095440c124504d003070405444600d00407040d42d0000b0b01b40302d03458a00a1505e400149070400300103020b100c0d07940c0c1042001c0144c0300d5820024046201310309100200c1c006d0307280003820180c8502c01d01c4448428041a40c00c080d900c001c1658450101c80341054143d5003d00505016002010001e0721100b0808020100950007a001c1d28041d10301c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 814794451 1250 814793201 814793209
    0xb0418030e0d050f100b03060603280b24030601060c0f0305040b0d0905160302090c07020604120302010f230a0e0c0d1b060305040203060a0e191407150e 67
    0x141c01d000c42c0e00101800281d00415010b0180e51002e50824014010910310507801c441200c521303040081c044e0384150b04010450f10b0008001da40d03c4040200ea041960600486034200030a01800409554000b014800f401d010045650080000ca442a0281c1c18010007410355400007449541d001544680c20100030600050560310b1860007890241e1030142c44411442c03855000800400c00103564107418414080107020088900f801e18494040725840d40d00064448107010740384451480c4001600000c5590f208100c40c0145550340c0f40384403255007410040d00030300d803100440020740d040003003100c0004c5101021450710041c0c6101c0c28656200e1480e04c0004020303000f0350040e42d00c05c00554480a655082130394014621400742d90703048250420a103c1c100c40395501c09001d00d4105814440169400310701140e00c42c909034030020700e50000210880c9810040e00b6600521075102d207442d0140041c40584c004102000412078405540d40c013101c2080c82031611b10240014280c60540700c80d464 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 814795701 1250 814794451 814794467
    0x90b010b090a170a030801061e0e040e01061e06140d0903020a2a08010c0f050304030219081809060f0d1410050627070c030c0b0c0408010b041803 64
    0x4070103008852600c2c3c0714600e00d00309203862503d00205134405a010f00c2010f51062a03079000d41b009103080c0c1d014941d40b212928908031a00400c00c184440d100c2c220f021510b03103500025402d92440000c4c0300c0550354030705625403606003960f044060050140c1c0031480c24054030380340c2c00c07500c91600610319101d0340d8407150004084c1d50b17204608500a0140c0f51020442d2b0703400f03410411001d5031a202c0010030505030f980d24400340346d103d2690359040904403400e094110280e000c4001150a040b9540e66071881c0883c100708400c0103200e04038482220320001c0c010460083d080e2040d61940f00d500f04001d80e801c2148440080780c10070340c05400030803100340030305001e440701064a00c40e080701c84010020603007842c2400c9040c9805801d455070345080058902e030807030b02040e000d14456610540006208144500c206009191b03106001c050002801010f100d100c138414000c0d0400d540100e9801c1c03c10030204558042e12803e40c0360340c202600040345152074401c003000d064030701e040286804100d42e17054072032803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 814796951 1250 814795701 814795717
    0x610060815040507050c0d090b0d09080c01020a031a03030720180a0e07051009030308060105160605070201051e01052b0b01051c05030a1421040c0801090b010b 70
    0x41c40504101d036540381e0340140b60045105454064a40300550461440c080a06800394204102c0b604c04005042124040300c00d141429080814032400905091119101c0e00721428860f40c400281ca040c1c05902d030340402621840409202c08811080f07041503520b00860301c02400381070b03a040c2500a035100c10091410007000181c0380c01c022000103c1e181c160007104407035024006448012900e9159020700003900036000031200c18180d00c0e102c4400074000d240d2400000c05012445010500503800b4400703035030f403c0e1065541000c950540e0326001b000b9120aa80400c0590b090030081380c0001c4d0600a020b10041840d280f5500c04d03807038107003004142950808401d01e44032800c035802a5080f844030038041e90501a82620081e035140030188030782201c5100703030003840185544c030307000000b00c0100464420031a0381c503100809110200c49001c080c4140c2c08000d044107246015079900e0403013580800d10032405400c03924110341d0340c1c6455509a90108000626030700a40005111000c06600071740254 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 814798201 1250 814796951 814796971
    0xc0e030c040f2d0509030708030a0b04060f0306150509070e0609180903030108251e05030d18120b040213090b040c083a022b1106100608 60
    0x800f401e02d03c050411800180101d03160054082512000103590040c0c40c0c000c80c60000962030094503840d000094003000d000111005e441e400c203518165203540100d405440150034054580d83d40e8030b40b21004001e080c10103504800102c000003410700d404e00c0b000d4030807101621400700d40d5102a0400415070700c8210b030590f00c419591950001d03624111842441283c0140c000e6550b541803044140c5411007880c10010301b02d00d401d46a940343d050010244003141e0840325089100103a41c10201c0e00240550481d47c1c041c810494210505a840301094008540c1c0c0150b1480745500d52064242d08012040064081101c25011a0050074004c03280e20044682c8000090b9000442e65111540101a0b50545617071540c2407051010810a000c089403807920203a00303400e00115031169481d904a50b000c02114a80e105c0f81c060440c2e03009000034a91150300ca0313141d82c01141104440d800300d000900c0c0580010300314410002c081c0d84d000078441c1c056240d46a40d0100340c1d14015040b18401b50041c40300080c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 814799451 1250 814798201 814798211
    0x2060f190e0f0a060516061404050a050f01060f090c0c050d021c0903020a031719030501030b01120b160203121806090706170411060703020c19031a0a021303150c0e030c040f 76
    0xc8c5500ca549a4015441000941480c055900f445841c014140341c4241d1140d161100800003c44000c2503a411070f01040f10208440340c0002d000d880c1c00010540c080c116008504010388410f5001c0303141c4051700301d4441001c01070b14401108440401c440d001c001d402c65030f100428404180c404104814034440c03551410325140b0400710900d100c084140200300420b03114001803007048401481240035029504640201994540f15030a02c0702000e06854030001409154411583c4240704540b1000c0c04074013902010f080415215540c40705000e014019070055502017030b90004003041c150100e6296903a07c5010f0900014810001c0303101800450350411505035038040381d02c80c40c01511030b032400380d000341a54000e4502071000c0c20055154101082d20000300c24000a0346e43c4140007086038042410030983c1c0d03210380f060b00003481000d144285441e0b4800c4c0000810040c00c603001c1d07010805403402d0040c0d020b86403041d40c0e461401030800b5450380003030702107801c5801c041e80400340100105a0100e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 814800701 1250 814799451 814799471
    0x801061d060f0316180b060d09030306050402041e05031603350a030c0f0f0e0d0f0f150902090711071502010c03140c0702060f190e0f0a06051606 64
    0x4c9040c00b000061614040944000c00c20417102540b42c2c203440d000254103001e4009000d0020704c0318030500c4460841d00da80d0700c0c40041854440ea110401803e0b0140c811950703a5202e48010300720030200307203c175050b01d16002c402044505002c58491940e2000034900b14880e030455850100c040603410b41c91054802d10780381c281d8101c1e0707844807a0202c001030003086992002e403400000c09031403a1400b108140100c3c17242080c0c4065000d001ca00f40d8032210318159600d9141d0f0400078416a0004001401101810800d8000d1011155000315402d02c00e600a5941c042c040030120103888030250003a511601c05030004107000d0290148007003142600080c1c81499803130380310315030150300030440b0400142e550701c2c0c442c0341658051182880e41c0084019030f140b6481c0540390a0864401c868001b8083c18011441e054030040e9501525501c8400c0ca0041c1d03010f5080c00402042003e460002610a1240b00444a071038182401d005c070941d615940c415240c4100321002403a1620603040441e00a952031078110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 814801951 1250 814800701 814800703
    0x1030f061b05031618090e01060308040f06020d230307021f1e09050601060c05030c01020f0711060306090615090d05070f0b030f0112110405040f0209010801061d060f03 74
    0x24141d045901d40701d459080900b40c5480c210000c84c400c070140400919140c0d004100d400d0384004648a003817011802a408051306c0d4050f101a40c0300408484000c500403902101d02e40381d0000b621038a81c202d64140103c1d40d0f04403a654800300e140c450300454140102c5d1002c50800c0150784c441c1d4240125004d002d0210441c1066980802d17046040c1035550300d180030740380d510707405000002c0584001800f00651544070141c0310324041c4908810b20041d0001c0d40f0802606006a80210f0480d100854031207000d243c0e508030652000c901110701c010219006001d501d00360080c0d0740501d4003e071031480d10b543d80e44107201c408171080801c0045848140304950f074681d2000c0b0480b03071030740c8a80058003480d8a00304006e081003025030001c00c40c1000c20300c100001d01407900405811103082c0c0f1280c24011583d03040c1981e81d10950100d2540050500003080240712155900c043c8440c07080d22520480d030303a14500c0ea400c031011802142d054003450840c1d008003988410005800a02c020310016003050010300007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 814803201 1250 814801951 814801991
    0x30903020d0812040c170114010e090a0c030c1401110c090a06090e010b1e1c0303060b03010902031608010b0a0c0501021b0609010510060f261e0c040302010801030f06 73
    0x840e1902290b41086c0440780ca0444004c0e0141c41c120000d00c0041240d00d410080d5a10502640c030400d01c0343c20000e800c4580030000401101d822030b176408502a2039040c4180910342c580140715130075454008200040d4440c84101480c2c0e501d20b00038080f040000c800304140d019001d01032000c17240d207a0101180c248460f1003008602e914040002a14959480501107048451840d03030521016258070307a0015168048281500040d00840800c440b1107498140d005000d42c0e008045581c42c04800890030b02c034107900441c0900c4c0440405c00802201c150121031000702401641701c94503003440281055030041400d0036841e48204005030400e4440c203400403103041c0341c510100941d03101c1010f00c11205028460107822001b03000ca003120b0641092409080c0501d4826140c00700021a4401110115203008070070119580b141080c03d1402e0050181003090740101e40001c01c5109840441c111f043c074202205c04487c0c1c1a1940580e03680395442d1400940300b00c1001352001c903210803c00100c1d155130000707 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 814804451 1250 814803201 814803203
    0x140f27060f0703030b090603120d09052413050c0f0f030a11012007060c11030601060e10051603051b01050f010e091b061b030408071d0103030903020d081204 69
    0x39042e19240c0509004040e55000c803840c030300503800700007803043c1e0f901c011454a55581100102a607a03581c41680c010050205140240550140260368010b404a891442d00c20009038860b1103543e40300c0b602c808000381001200107203158050041000705080444050741c4c821030080042c20030840c66030205c0d09245000004581042020042c0000b940c0c000352650440d40c11a840750407034030010031090fa40ca00c0d690054400f031248003038002041021a2100030780c00c10003d8150340300d55030364039000b0b48210560b101862141480f000794005c92482441a030304031120700e280013245c103d4192010740b116448040c9203120001e02c140100a22542405101d001e0058171051633155850003265a0900c1c00180403180030344c01c0401d01c003102c8201d900041f141114101c1e0016641c030700301405140030090094007491300e400701060000d4820000303d402422501c81805c404c842c1140d03400da100590710309000c0240410001001400913040034603250f641c19100c0c0c0d0703280e403400c104a0707035100c601401110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 814805701 1250 814804451 814804477
    0x32e09020f0306011107060804020f0a05030d030902130b091305071a0903151e0c091e0405010504050702061602100f020c0705010206190b0607080a0906140f2706 71
    0x184080c5584c800030000c5c0c3c02000e9009403107111309000d00286450b001034000b074032903141c51016442c1660b81c1c4d2151f9008020040856040f034116280c058090302c80d085c4140d04c200011a1400b8101c00540112607248400425090b402e03524280060701c460400032054949218100010400e003101c002030003d01c06118079100c1c0c0f152000c104251411508409001020010100f401101d000f29440300030100d141c2e20901c801076881c8841e00d041405085032071580050782003d109860103240041d84071003102550144400e84e2a20140400e50b04e041d140c0e040180d000000062803284020070301c084408451040d030300081c900031404800e0300c050003d8660038540c0041e9001f0702c20020400030b8020718007070010b07046520388581c0310410f9400b840d07802510300d500d40c50220a07540c0c8402c1214607041c0d0004419444036400f400050001c00c941c040c60021900f214041c095403008a411f86010005500c0801d180810f07030302a0700d01e008050405181e0202e820340525843da40c450016080d0104544 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 814806951 1250 814805701 814805707
    0xf030908070503011112070c1506090b0301060501050319150f1707290d0213051011030a031d10050a14010803040e1009150f0803032e09020f 62
    0x600e049007018441e40c02144207030f1525002c03607480c04212040da5401807500b48080181c1c1d41d00202500c01444680700208213144d6030f003c4105021072640140b01b501d00d000420000c004180061508848541c0151070104106000143e0208401d043d075100b08200e102008c01c01f5000c140c2e400c06c5141c004d4004030082c50091006101010115880c00091101e10b8010305643e032401190480c00100d48600c21030f588003aa503005600003085048170201c4c0c84481d0119aa00131040450340341c00d450b40a903d104092200c6449210340c86030340d960141c604010013031403a00c3c8400c44150b008000218032101d81c0e004084022441c12801d005800010b4800c040c082081d00c2d040c4403140440c0c116607040596030071003500600004c9400429141900c40480d18100305884038003048a080301d055004100311824226000c031444207030403400b02222103441200703000302d40f100303142512808100c0d1040ea03c0e0361110f29411407803006213940c8050030800c0306100c1445844410b1074081e64401854403110b00000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 814808201 1250 814806951 814806959
    0xf0a02060403031824060807080a0516150806120618060108150a020a1110091502390d0216050d0f14010b0a0815010f0f09180f0309 58
    0x10301401c0580030020100d40100d81290381e690b41508514480c20442c4c402c00c1e00d41d048660130076802840036081d50f13030484d0f2380b0b0740e994200720303544c1c800e0354a08455034060001c0032100704081664a1081d074414010b1440b80f00200d03842211104801040640c3c42408070340d903440340c00130a00c1840d000300d089440f0300e131f5030f2440740d66002d14000c01a40324058961003a4000c1c00031890521046800a015800250b42c501c114442101c0f030240a01c00d5281358003032107003000c03600311055000c104034600c20b156142c900202d003020402280a4000340d4130509100e01180c0a00320200f04040c1031000d0301d050451030707003011400000e00d80b02c0c85112a80140c0d0061550821112003001c207040104800c903224186d54100c0d40c2d130a078a11401507c010031810801c00103000e011001e412041e0110009403025a415540d81006960340b132010f02c0c4400d81311409000810801e651284400a44002c43c10f0301d60280e1501500500074185441401e00982e108100140010f2003140d1030328595000ba0b8461420030b00f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 814809451 1250 814808201 814808207
    0x2070e040303060e0f061f0f08044101050c030105130e01020d0f06050a05031207060e1921050a0e1c0602040f0b13140f0301050a050703060611100507050f0a02060403 73
    0x201d1100180c880301107c800070544d03a4411050ba001200300c0c50310a0082e1524a461802050400912341282800b0b14402000400c6c0702d1101800b030080752192141355185800301c3d42214070940e00c145e040c1c102040103100134100030000314102c041000300018000c0d40801c4441c2241c200080c40a0007589482c0000012000b40c014840940401c0315501c203044c2c07511000954030050340b007070801108000315084060000d80e502c15601c1c40c0401c41550b0b090360920f4002c041d801c5e64040205c5035000d06103040070203082c0701100400d03046020740341c0620b000c1103400140c5181e006516502d50104401c84040f08000b14002d511600c40d106490243e02c45003055236800d512030980d00101035180044c010304074000c0c1c0600c030110894200c0340c01450800c115401248a00c510031003066050760810303003884a00c10191781f1061050406039400c200361611180211514420741c050011280d104501800e0400883d50201381c02c43c442d030070318a1410b58042401021034105085010150700a102000241a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 814810701 1250 814809451 814809469
    0x8161b090e01110d0506150c0c2b02011409030f01090b0603030a0903240504140d052b0603050703060c090608040506040f050c0303130f05060a02070e040303060e0f06 73
    0x1120500900c140c20507075002415a0040c104c0d0409080e4503500411469201c0a8100602101050f001d946d40c00458000076a100030f8041d1080c000c1c070403607421141004104201000010b51880003003002d5500360011148155900da02102d403580810240b40740b90350400c50030fa203202c0c4070b8002207001c01150500020105005003040d0082d0810044003800c00e0740003c0e100242ca9011490501d00701443c498071901c85051403003207400038504401c2c8000e001c2d001c4a802a605030401c110b13461380e280ca8500700c0e4103002d4a00651030205c1840e20a440f0465500c499440b400d0444400140450f902c1c3c580a150150aa00644580b55a210070041c8194407022010180c201070511003050304095075496910303c4003c001a000c4c0d44190900800c00405101140c1c1466004040301e0300c581c684041e64031104410311031400803001c42c10300041c007030820740241c2d000b44441d600070b804190b00c0d09900105484004004404050359001c0115484511a204078001c401e00140c8103503501c2c01009101c4000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 814811951 1250 814810701 814810721
    0x18040b0106050f22120605060f0a0b090607020f03031b101107031b150b0108060913020d030203070609080901030c020c13090816110102060c031308161b09 68
    0x2e040000360140110241103030b84007180c1d8100400883d02c00b59481c1900c0700540c0040000b5904d000144050020300d400c071038004c0301d003241c10200b52007030441042015101c03403040c10f140380c00c00e00c0003d01c9498554050030f03886002a01280c62040c0d540000b90840c0d111a0800c846841c070b00d1100400000200b104808003d48000104005261001450018000c0c1600101004220041e0074000090b40c1084074005a00203041190707042001130100252400d0313070500380000d0824001035110b180083c041c6000d020202400102452a0340a00000080452094040d84000c1191400080e5188070700354101e4000c60070701c0e454059403c00181914a080d1540c004c43d03000e1251043c10b9660711840c1c0d01900c46140d400a540f51840c60300e610240110304001d500d00c1c84501050041c8030503142c1c01c1c02618000da0a4400070303952008041054007007900d2608070340840200102c0082e00d450003e0403c00d1048071403c44070324166440c00301e00700c400c042072103199110140420943c2171600a209102c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 814813201 1250 814811951 814811957
    0x30c060a0603050a08071113290d0f03090e0a150e0601020729040b0406090e090c04020a0314180c0409081603090f0305010501050a090902030c12010b18040b0106 71
    0x1070b89152902c0c1d50303a603420359005e00001400104c82c0c0400052405405110740007a10750444542c42d2608071008141c120381c0456801c924204641c85042400000203d04030014048a0b903403e140e00c03040c059a0b400034044003070041c01c0c9000b007403007408010214072500e0030f03c2c004030703d80702c0c40524103909010640c01a51810341d43d8081c414540c0c1c01285550a886401420f03000c0302844144641000000c0b600d9140d081000040100c0d4850500b002001a20f141d07498161815a0b500441668030038101c0c1c141a55400c802d0f10720100d803070b00b0f40041100e00040e05e40828411000858034075440800d8503020040b10308110040c500c00c000348251420640c04440070041c090707254695542c1ca1085010222201003a0350031201054044c0c00f01714060300000f80c82481054a92030454002c01c001e0088600c248260303034001030210041e01031146142c0e0f0117800703091110482c03002d1001c0b4401c00c0c13420340015521010701e144103846140062181c9150740e41c265407581043d0400c3d203042001030b080b101c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 814814451 1250 814813201 814813211
    0xb1209070b04120308070201230915042003010603061d010f051905041406090f0c0f130b0f040203091b06120103080a110105070804031205010501081302030f0a0302030c060a 76
    0x18a40514003c040c10398060500c40300e15680c6d00340403030043c480700c0c0e8001c0000e0900c4406034041d0b0050a203062180d031581040740d5400da10410070080c00c03071048600820310790204005102e40c0031060565841078030054000700d403550b140c0c1e0361f600036244040301020480e0090900c05030740d10800d000359070300c40d03040050800481c1041c070f000078a11341c42c0c500810362094a07400401d04100c0501c5000100010200540d1072078280808015110500a288981c89108110048485180829024034844d0000b40800001a10303108910003911000c10320551118003002814900c0e1140d000840c03081d20980090601c9220141014002d9800c58884e14018501440009000b410702c442c028152504520145c0d00c902c541c00085807000302101c1c0340080d55007000144141d89801101c15801580310362201640b4010202110045803000d20440380082c0b200c1000c0303082c89030381c0780c140340300c1ca400030b0141c42118036210501490028040710860050740001200500414140151900401088800e101c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 814815701 1250 814814451 814814459
    0xd0905151606064a0a1a15042301020d0305090c13020a020d0804020303092404030c0501172701021215120a0f0b06010306052e021f020d02040b1209070b04 68
    0x20080e00e0040c8100b0750301e9a10110314041c0000342c2c0c019010581c00400580c000b00e2100300c0c400c7c1e01c0c0c210b48581c0f5052030752003010025101c420700740090001070690083c450000d901d00120054400903000084a000d041300c810400d4135145240c20682c0500c84002daa07907003040c50000d18026030808850308224141d014440165401310484000380c008440860211050341c1a003442c516225100e00511080001e00008000c8111140c01c1103440036299248071080041d002e03082038208451040e468170490412002d01c04440074449203151401000606151640d042d000e1220010740b007c000110400c40d403012685800c106941d25116483d0141840141350f644516074003070034060040041e20003d0015600c1d902c640e01110080c203008003150004200348020f413808014421103c0031558a1a54440e05907000180565019000c0c1d950701c1c81d41c82040c0f01000080d045032061680440c1c00300800503982d80740c00e000d040509a1840d1124050a092450501c0c0045940c40301e22885c8041c0070400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 814816951 1250 814815701 814815839
    0xf031706100e0f040b06030f091b010c14160f17070b27060403030c02040509030306010903080f0403080a120606080613022a0d090515160606 62
    0x100140580e8408035a00080f00060040c00e8241c2140b50020004010440d80d40c103910320f5107000f0341401c01903070b52106010690020346017030340003001d0110b10340089000000d0304064140a07080f03504019202000303150304156911480590004203045d5000100303010030480b40354200c2c10ba803d50002814024035010192580d800759100413600038001c00041500e5040100381d180010000425090b507941e16071402801d0b19210b24810f900503031419000030200c0c0400002c40703002d00c03816114502541e01e10b41d21000f040d40600d5030704000304003c2c0400000110800040c20ac0005a170700c90386009000c0590f07800c115000740c1e105808014110085c0441919400c1003003d6001041801680e10404600c610086050035540a01c0c0c0321300c0d00d40740c846802404030b8003203040c4100e40d5485180c9681c480402911240c180001000c004c0c04101e01544869003800e000c80141c030072a0b02040444d900d11152940078102a0a600c00304140300721a500700d030400ca00340071f0350084c00c1480400800707490300003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 814818201 1250 814816951 814816967
    0x6050d0c17070f17150402092205030409050906250e121209011112090907170903072109050105091804140606011b110406030f03170610 60
    0x8032992048500c41e10301c09400502111014003948003514010640e5801010104400c0c41c00503026400b41e1040c910841c043d8000450040b900204058096101c0e85958400080030f42408050142d5110000300081c409001400085c5509280040c0c0307880c000e11400d0410100624810000700d8240791710703840400e5550070910395031a903d084503c03001e02d8000b240d00703800c90580340c10f6544a2030010290b0500715100500c20780c40300382d031135581140760007402d980d442189140c000307000c5000307219010140c10060015540007c007841c00c81d1480321243d56280003502c081c3c0303120605400c000307001018090307040307848400361a40303501c0c2041d9200315a0740105400c0c414001c0904001c1c00182184996464018403030303100303105000152460505240140d488210300c094200da0303011700310001d2810340c0900102c6c1c16010303203c0582060307141540e5410004100d104007a40c0d11a9071101c01002080f001c101e4050060301c240c89500c4980482d030181c410756107008103140e1051001806031140c4507440f041c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 814819451 1250 814818201 814818209
    0xa0e0d050d0c02060c030310060306050f0901030204230f0106030b0a031e2111071202090705090a0f06030e0127030c081620010c0f0b040302071e030606050d0c 70
    0x18100a00c1520008604c1c0c800d46170921913610000c014004520000d0411300111100382d1001c00c11665620b0511250840c0800c41c01e600c1884100104007508098000201c0840b29117010301207840702c10500d18070b0315400d5542003c008840d0700107010680e0188525150070700122048145246941d0b190398100120000328010f0082c0e401e0b40070100000100700882c0481085100312004103c000001c00840c00421080c856100d4407000169a411090b000a95150060a029140d6030f40ca80c0c117640c0c0c0c0c0e211812054110f404040c0000350041204902009003446076408554404410925425035100c04102110b04a81c5980300301d845040c4d40080e990300740d05041004181000381007212050003801801180c0c80c0200e210764080110341d041101c15445180c84c0031002c417030a400111044c00552100500e601d108111180218000d03c180c81e6003d4820301c11030740000d403120060641084582c11030141840c50390814000c001d0207000e84005400203071a140f00d02c2d101d54030340d64007000092003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 814820701 1250 814819451 814819457
    0x7020d121206120c090e03030105010518041a041d030a0e0f0a0b0c0f030906070807050a06110306031b15070311060916060c030e060a02010906110a0e0d050d 69
    0x200c840c40c95004005440403484100001c0140c555502c030303c0c0b404508011000c5520150210001c2403200d01c601c41c0c220050484c400840c2507030300704401076580e03500c1542c0b10960741201040c0301503d5510b60140202040c0c09100c030320b00302c0e0580d00034802070b140c0b10100101801645000e2921042002040d212039030a6850407003c101e9895000c41c2c12454004045030700107010640101c0c0395011140285510711861084030441041c002c98641c5074045c0c201e45903800f40c0301304240f0020130500313005070000c14014000e841d41c402c030665a00341211030700303220ba001c0e01c5d001108101152500b805000d4502c0019285c6440a21019002aa00000c0c0c61107000384610049030003003d15220b4001c48088041000444025081000d041590789a00d00490429840d040074045801c902c90380c81c0c00026a03041c0c0300d490082d00380d501040300c0d9401c0702160078215981d0300d00e9580820081d00840092801403c400b13682c8081c1d8480040180e06a80744d5940288244803020000520005040c2c030380210f146 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 814821951 1250 814820701 814820723
    0x307170c122701060b0304110108010f05010528020d14040e01050d1109040501050a0506102f03070c0512150a020313060f020a080906100e0901060510050a0f0507020d 73
    0x42400580300c509103840b000350710b0180042030f482020b10045015034051818100c0ca00b010f2001156844030074000e038800303e00c1c041d00400c01b950295000c0c01d02508500a5890302c54103c0d0500c0030b149078240d000310300581c003040c0700c440e0040d04007000703480c0c1020b000b210310f1400e800e01522030084003041c414103010380300035050141800000a02e5405604005166494500b07060030514080d020a45501c00400d203464081a420b19128100d030760015900e46401540c43d03422640d202ca80860f403881088501c044405200602400340020010103105940c103404690070700c0c040c00781914000321107440a5008604605010300e403401450782c04141500301503901d64510f10020200c0406001c024003040c24803030b0360301d41d140c51030300540070f0596140e945940d41c0e580c1c90482d580e114010b49050002e1444c4100900c00b1800700f442c91603000c86c0700b0001082c204c5d600c5000c1880d4140c3e003c00100095808510301e501154044011030715601c4910b042410150181c00107020b544601000074080003100d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 814823201 1250 814821951 814821991
    0x271409090f03040b070b0606090907030515091e09010b3709021b012c0a0b0915010902040b12130c0305100b040203190507140307170c12 60
    0x30000c005007880120140c80d11544e0342c07410050309400c040012a00c00742910002002803e02209903100c17101d0081003e5032a496545040d001410050610340f00313002c01c5000f003c07017130302e40c034004902540481400144010303400341d04010314034020f040d16106074184a00700d000f07130b0b0340c1c2070049280001441c8074416100b0680000c3c2c032160510a070a41c404103061200164110032035004c1c1005007a44c0e15200a196080d1072560708a0313440c03286030090a100009088110b01580c0b440c403100400300d034100ca14503a11525480014407045900e040c3d90760001007480c0c404000e880c051801844007000c01d604043c01c04c0d03a615400c1c050382d40c03031081482c202d600050340f00c074004c4840850b0b581c006c02c51640c80c03074503070820940790100d0604190f1000e0030202e5a04d103034180342c82142d2084250b00c0c005081c0002101d40c8101905000d4070541c02c00c07521203241981d030a280d40055014149644030414402201c2c01c42d44243e2130010300c248100c50f0180050481074284e00c4225900c0784c1c800300034000d02c07407203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 814824451 1250 814823201 814823203
    0x4020c070621050a0f0f0e0a0b0a0609020301140a060c21120513060b0114030a050402041b021038041b05090a30081927140909 56
    0x703051264503078500f4803080c40390080d0240d010041d5682000b006101e00d0003c02200002d48a00b46095001b9600ca01031001c04640c50040482e0810f10944001c184240e03503142d04420390b00280c00c02c0b5201c85540c046464a440d018007550000c2299080c0019621403a4454107070400c42c2800d01e0340c41c00301565484041c1031081200c08424050348070100040c0c20522850b07070300122204022980989041421343c202d40c05184091203150800c4003480c5075a0310181c02002405000d80100d030071580351280880210720032032051a1010b40c580c000c1110f8080558140240e40020003882c00e840d80c4503800e2506c241e28441c0c5580300c0c20400400040c03d07624040030400902c8404080c4240005e03403100f150320030354400d00800c2072103070444085c10240d03111341244940130346100109182c90581598403181d1280d8a401405450090600030700384500004d0145940440a8184d40000c0e000300f204888130421218100700d03032200540a200260900c61011400c00620300c0d5a0b03c500b12020020b611608 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 814825701 1250 814824451 814824497
    0x71709030424030e0105090a0201030b0d080324010e06160212061f0b090102210d091a15130b0303091f02060c07030921021806030c04020c0706 63
    0xc0070544640031a88020501c804803101c0c90014000070b1301300f800c9100ea1500c140101401071200704068420100c1d01c0e80194000c000784c100ca1a00444804919008101d520000d54030403400c520320600b1000140e00016144611000c0c07041c1800b0407444440c14548414095650403c2d00400f645003811207800010a243e50420030000c4030303c208001c005036440c10250405100344500c030243c166039182c100905e03982c0108018a030050f800f2101c9072201c001101c1800c01400c20800755107292580c2d4405070707000d0790040e0009440b40f10000912910340c170074442ca2981c0c841040200c2d852143e600d80009201c4c0401d9000c260466a00c5a080751803542c0c042c0100e0701c2c0d0510081c039000303441c44c860301102890007030300d040503015021744000075900812540481741499450380d03c1c10002d0382840100c40c01a54094640042c41c00704000d82e500680355807856220580346451035066921f000340415140c50080440907015500503c03520f95030100026640d02910740b9410031031250300c01c01415400c44d0f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 814826951 1250 814825701 814825709
    0x503040306180b0103030e130501030b061513120b13020d060e070b12041202153c16030905100509010b091602150115030902030709110414090717090304 67
    0x20014000020404d904858500c141039008c0d030b00007500042610141c421164240302c050080c000140c00100d881c0f030714824865814007006490b6003840052400101e0b2001c40d42c100d001c0d59000c0113210000d22440030001a44031104005849909031168041401040c800c5c50080507162213040d205140c0c0c10520840000d060300341519030b01e50400840017418481c080d602641d6441102d140200303183e1000c640701d203040e03200a0758409241c4822600c0600078030303c10000e03c19100b03c200300344205105800c01003080003140041542c02e042c40b0030703001008404c420300507060515024807100000c0e008910068080001c0f81e00003055038170030031028050701c2441d020300e5000342c1c40401c0100c80c000a424004014000ba800c0b02c408207000c141802102c1d00130b0103050014200301c8240c681841c42508540344d9a403000d410744162a0b0b07a810b0743c109a0302403802000000001080501204215180b0702144600844881000c0d04141d60003900d239034803402c00a0441e55480e000100807030030030407c0b28010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 814828201 1250 814826951 814826963
    0x1a0403030206010e150f121f051e040312180803070807030204050f0103020d0213082b09090b0102100c021f06030c030221030301094701020a06050a0c0912050304030618 74
    0x12802c01e001002c8e8800e0201c01ca52409498a40403900d200e0030084180c91022600b081c59100342c035107480544503514201210720f6807549840807119808a1140040391880c4900d12058030703800e0010780038168440092035082007503c14081000355a0341d603074080c2c01005013800c00594840a13200028040d02c00c00150181d0b120303002000149600c0009145901c0801321030941a00000880f0740768600204001d180c40040c154803414009169654882140340d207050048442e48168100b046007078904080644015030828116031440300d001c00700107800b00140d010100074190566030b42c0180201e290101a010301d02c0c10300e045025004d1400c1641c0c0d00c000ca601101e0f201d603558015500508442c05118042400c0b42070045003201055059480405070050f001c034013010070b541d6031000c0100b1354031000d0452040c08030082c04a602845164052422501c2c0030542c4c130400c10000e41012880d90240b40c003003143c01c5407800071800c08000e45050341c0c0d0002c008a42d80700c203ca00e00c00008480c0d0b10240c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 814829451 1250 814828201 814828213
    0x615180607030c03140a050d050a020c1501140603060604213305330a0906060e030a0507140d0503030901050f06060a2001061a0403030206010e150f12 66
    0x42c0b5400000c840c084074807940c0ca0f054264120118850365004203880040460000d0082602c8a404ca1300038980c07101c4058030050030b05501c81c803241d1500b00c442c040d42c0754141c0c01030b0041c007030550740521044441005881c0c540c95424440f01081030b61040e4850380d0642524500000c8504482310010004e007034206508020524a50b406030524400e00340c4d90048038503000400c2d807200115802414424031550401c0d4001010701014440010300360710801c824403002d03018018003580d4001005000c0c128134240000d0f65820320b5405040e4034000b14225200ea400303e50400c00080c000038811040e0740c60002d00f070b400000b502c4042500010180b40c0207066010100401014010561142d0702c0f51021911402c2d640e1950024086144200c091010024000c50740b02000c417880440c01c020030300010000040d40f1903580c4200c0a060f0306880f007003440030398002020001c0c5541000042d0152000d140003c040341821007031b8055220f00101d00368010001048140410381d5184008640b9010b10000d07910 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 814830701 1250 814829451 814829453
    0xa12050a020d03091509080f04030c0504060e0907061103120f06040c052d040b0c07031505060f010f170c0a110f07170109020301090f050c090615180607 67
    0x1560304000c41400051007000b4914410340c2c402d000f220002600071817441141014604030708080e007501c000a0310401d42c204400700030725008800420003940071340c1500340341504090400041c0c4405a01a03801c0da00c81d0b1050005010380429003c08a03071441c1410701a004800d1071742415806001c1e100450706c050642080fa00e00c20392555a4842e0340121820413001e12411010b4919010301c40c0c8210444d1a412400059403070940c500070031400020095504183d81c0f00c449003042d074007408001200344c001040401c10040040340704510054004410700407858014041840c0c2003003807038180d041108200c030030308805005c0c050b0f10040c55205c4102540520b04082d020040c0c1d84542d0100002842050100705001800f203808803042143e0b2024281051801009481d000200034089050755a109050001039509125079982581300d082d684880d011982800c4e410403503404582c50040808078200910782c0d4034400903d4192010000080c1c03a18462114480d42003c585151a0404d10000d0040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 814831951 1250 814830701 814830707
    0x601090c1e1b03090b120610090e0a0b0a08070b07150603021509040912110c0a03081b070f1d09010c081902070209040834080f070b040b180309061207020a12 69
    0x42c41000c09480a0b000d010940c2c06c01c0304e000360a8070031a401a41c003a0701007442f8034102d801503801d40e9401814840407a4a03072002c9810b18030903a10441c02c0d0300d40002c0030380c10400041414940c02200301c0d010403076513240d0b402240d84c0d040401c06061040c000012809019503035a44200c07400c1d6008150004031950542c80a84103403c0c02845240b0b0b8400e06081e82901d1038072907644010b0b658003404036170820250040b80b420400c414010b00c01e11b40540c03900428034003189d0350000000c0664845000400500e240d201001040242c00c001c1c0f9641007480807042d4580100c81140c001503c0c41c6034507105065602c2000c000d00404000170740c448070740004d10092003859006010b48082c102544944034042440340d04503211280c6000c3d0806040110318400314802c4005001e494014204007031a03c4016990001103000807142116400242024040842002e1200312900ca0000c03000b0f51900c0d0440300010001d0180501d6002d01e980c41d9000214420f109015012809034003030003544090300078803000703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 814833201 1250 814831951 814831987
    0x80a06031a010911210615070309060e061215190323010902150922050702100203090c19050a0305030a111c080411030601090c1e1b03090b 61
    0x45210f03400e244150002c05918011a00840d400c0d104566958010a03003c110680000300300b40d42c401c4205031a01c16040c003c00041500034469a40c1019150a146d80a040d10114803180c40c0200414059943d0704880205825008a504641d100054031060001807245a04807154a42c5000c840400010405070444642d0001d0348011180038601c07142129a00300c0c0e1030000040d510205507001100b1280840b4000d10a0100140100e2705421401503800c82c1401f1f02d0383c020507090f94030000c102c4216410711941c44010f848280962441c20400300c86550f4800d04000303c1d21458242d110990b6050f9449100300c01800c2c060102e544407603407428007a07103a8201040c0c4c20040741c07038804040c1520201040100170038501c40340c40340055404101c2114807410080048544140c0c1d400c854049135400c01c0300d1402801c031201c010400303010125009141000e08003048000031402103541c8401034000844000c01c45010128910390545420203e580702d0301680079a10b10312002454a415041c16031070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 814834451 1250 814833201 814833209
    0xe07030b130606020f0729070302010e030301240216090f02040e070306180608190303021614010c0503010506090103020906120c190f080a0216050f03030a060b0a050a080a06031a01 79
    0x50342c400b17070f649220a8025805d00c1c090003d0b0340e64418807c9000500e00b2026151035802480002400c01d10302144910f154000e8100443d4032140390795041203107000a44800010403c0d10152540c1780740048a6038211801380107070051507440d05007a180b01c1c0c1250341a00d00911000c42141d03400e0520081c003400078802405960042038512070100100c0b0400e0140c80101c42051004180203561244010404a01c2070412000c154082101740603580160589d602d40a0041440903070050b80c2d80500c40c03c545002c40e50783c0a000d0140300400c241c4e60760006503507003401e080c05c0151f5640038071400140b241c40b801c052880004906420b00210992007805402d200600c00503074440c603605640250f440c03e02d0400340000144001c0001403503600305401034091411084000002040c26984481c02c14180360b080105c1640048200100300c09240078003002070100c5229a07140c03001500f4000c0043c89142d48407001e100842005c1541400b950b40a0301c01141c000c4050640c10301c031541320b14490318082c41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 814835701 1250 814834451 814834453
    0x30601030605100b040b030103080319090605010e090a03080606030621010c0f090803031302060d020703080a05071107090522060207110a2d05370e07030b130606020f 73
    0x80003007054114842118240c070286c88203e07065070310703596407000d20b54001850303e1800302041c1e050f2848000c0d076004000085105501c0801caa43c10503003184440d00c1c008001c100941d101c00c4520f00820b4000c0e26003a005641954015600c2e507405010625422030352030a03d20f55031440c40c20300010841035000c01c1c0c8170201c07a6214000f13040d1410f001c4415150b14000c84030290070800104240d190440007c03544548007610311410410120610012031304500c030183e002c00c80101c02c202e40c206607803103a039501071210b050905c2c181040c41007490b940c548500401550710340d248042200704132041d41e1ba0325480001c180c80c1111401900d014006500704090844550280c59800b000c0ca140c102030000c00c0d10700c000b407140d01c09045081003c0d84411940c030040da070886c80c44004505501c6900403418480500381d030340c040709401448454261107121480f122034000280050019200d0241c44c190410007a242c00b04208514200060070007913070024200d0540d01d450400240c198001ca07502001003010301c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 814836951 1250 814835701 814835731
    0x606010203030f07031d01020a12060803120106080414060103141b010219060209100818030913020d0b1003200f0405011107090608010902040501060e030c10020c030601030605 77
    0x10069a40380020340310b8110740000600082d242501c254800e8020f00c4000500c0c4070200080306d071060880e40000520400900301ca162040801e159005284c000e000100007186030503440240c09040755818026441004403a4000c5028808070b28130301c0818414900545071196034924111405905001030005517008441c051060781c00315402a070340340441a0094610403500384034000d04254403200440d2910760030300404101d81c83c1d02d6410000041c1c181c80308402800c01074900c840101d621040710203158020440c0714802d0b103808113007008a0716100c10140e103030b40140c40d540001e0140500c032150800e01100c0e070720182c2035041d084881080c401e82c4606d02c840c0c60500d0024405e101304920000040c070100820041e9510517017028200200d03850a99850f40d44a40d902d0701520101e0703010030712030b0307449031f10986c04c0d1b2810f40305d003500402a5040c5807030300f03584420100b41c807080c400b50304d2440b8002039180c284030140244000b5040500084c161000d5684910b0414000c04c4181e600b03a810080e40c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 814838201 1250 814836951 814836961
    0x40314030910110a0e01050c0a050105090f1603050304230913060606090b090d080c2a0f010e130605150301090b010503011d0a020d1803030b0f0d060b030f0d02060906 73
    0x1400315404c0034550340d900c1e03100181e140010b5803681c4c030400b81c8c2e0880c1e00c41c0701d03681002310703c080c8205401742104901514134424040751240c90030044011004d06a103916504000280f400801c89040b100c0c2902e281e003202015458584a0441d15140f15820000513000c001d0301c541d2982c01007084a1103180100240c6803610302c01c80c2c4075580380c024041007050410640780c2d50319101004003489485411498503001e43e2000c081d00709440c520030740c9410f410594225401c1c43c180640c1e030009080507200c0c020b2062030340d00001c006102903c84075000c2c00c465100c1d8007031003907240c01400c098100079003d000242460304c46180d040d4400d218503403003185040f41c3e0b0314043d84224110f904903882c10f8003807540e041c195070345601c00110203080c8442c695400c01a50740c140c0e01602940704809032414030003050f480c1600b00030301074030034001d01e040c030038006840e10000036540d500c5004200340d0450400070303200b13139000c0c0881e14090300102c1104040c4590400c50142039400100148a010380c9030640700075440d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 814839451 1250 814838201 814838231
    0x709050a12022b020103050c0c0109051e06070818011b0e1f080403050a0908070905160e0a090e010617010603050f0d0507060b0105280e0307030f020108040314030910 73
    0x148840c0c3e0b10b150144000324001d9840b9810080c6c00c003098070140d42c41c000d480c1c1611400c41d04104021105500030307400c4c01019441c0d010f02000b031400400b01400a078508280c009001c40c2c00113064076080c001d824040704400320b0943c4252804c2c02510101001300c0038224001d0306000700d440c41c0b24850f00f80c0c0c0d01900c0b100b030b108100800110a0a440b90350f550340f1640d6041c1c40681103050103500304000c903000090b64010170050300c030040610740300001d070030708102c0e2044112803064160f510a0240c0040c244480d621101040c5040b40e04180001801500b400c82e19405011190310801900c001420900c0c0d00c5281075200c5411a4441c1c03085802d0800421b036019118140c040094010542c140042e601003003280d003200ea007075841490050320b002e0540510507443d40400018141d5103400d0140c2400382500b010164401080880c0205400d83c80c56440c0340c048089000028104000e80c40410f080500481d01c8808504000c540705441c0d18143c4129a903410780b9000200c0c15a0500c41301d2855000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 814840701 1250 814839451 814839499
    0x2030121020307090e1501060818010902030705190b07080405010306050d08070204090201120f0b01204207020706050c0c01141c14010504150e0709050a1202 69
    0x5806000b40103c285440c3c0c8070b000501e8010020401401100c0368048088503184005010b010361340c40c2c0c203000e81440342c21801d8a0080041020003a03261620102c05a0380004400d01110300c00c07a8405081c9007046070f05000a2602d5201c03d8110201040c80e808008020001e4402d503071080e6410025141c0c0e48013000001c8680318000341242500f081044090708068025903122401070508100d28501810b40200301c40105205212040e6543d050803501c2da80260741e41e00701892100155804141411100e03100c000055111080c0d02d06184558920480056101c056030f40d4030741040d401040c00d080408110001b01c59100050140100204000b4007450695000c16011002004040321030320040d602004070104890004006011082c448580c260785c4546200c40c000f000304c1c0600d400d044450030000e06800440c07145040083c20520850001405421100348401c1c403030361a144e00c01c0a503040126034102c0c81c2c010845c0c1002040ca80b84c80017400800340d100382d940300908424107841e545124 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 814841951 1250 814840701 814840703
    0x1404051c0f032a050309060c180f03190b012405071e0b13050c060306031510150906120b030c0d0309051f110a02010e01082802030121 59
    0x5804007444118061082c1d0000a40d040200104000c49080d160072076144500c2480700000560004200140418184992900038a4140e2058101034090201406501c131005e4458001e20350101038800c01d07030b410020115070b410182c540d60f12100c0c0c1c43c1400741e4200707000d0085ca40486154114020240307d282c0080021541680d94181000d080350354441d903607807a09005400d000d008a418201059219030380b140283d02036140c0c034842c45820f00c0e20703506000c254207080d4032610b014020042c0036100031400710481c2d550320103030031740940e03c4c0b888a20f0840c002d030300034044001c003001e941581b00f50800c01c1d483c144d601c0342d100c0d0400003034201e4160b020f48000395071264054110100c00101428480d0900b40707024440d041507000c89444001240702c00107026440310044a01e401001011900032003100d2095080d003002e040004c00d03076000a0b0190340c80318a620304002c007c4000981003407121119000300c400629011451516070083d05001c4d4000380a4850f441c0400311003991541d02ea80c0c00d2020b25 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 814843201 1250 814841951 814841957
    0x9060c0204060f12021e01050d1a15091008010321020f1203071b0c060f2a062717071e1e0b19021c02070b060604121101121404051c 58
    0x100c000c4c0c004840151602b06003404c0302c40ea40f220090110354455008031300c1039402007980d9448600d81c0040002c0180ca0b1300c000010b00c035410006101141e18103c5081c000d6065099032241c1d080d40d40401c91030300e8401e0f8250951409035900c6541d81d01040c100840c00b414841e030b5046c0403901000c03203c0b40c80c130101160003401e4501801c000c10015008400c1a0095041810102a4075600ca98071240801040c1d075071640c807040182101d001c00600f4400e4260784400c2c01c503000e2003200c894040b8050380c8880100900703100e08040d00b00b05104045000c90f95913aa200380e9260112484111080c0c102a1074070b412154029940003402040090380301031604281c0001385174043d42c440464100351b602014440e46031280d000c10500f4100c0c454000004118080d150300144d80740d130241003a40d008072001d4104e07446030760100700420100c20080c10010030643c00c411528a007a03216001a03580d0750008078004103503410100c0e40c0c0b40065078414441d208034003030010780303420002c0da90788098800038006050000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 814844451 1250 814843201 814843207
    0x6050f01080a090606080a080304060e0a030504120c050402040e0a060e160c111908010f0b09060603060103090605090a020310200a260717040309060c0204060f12021e0105 75
    0x342c0055030004a4018000c2c18002040c036103d0480034240b84210000741e40f099000403d00c81004481d01ca03907055200100040c203090142030380c00130850312891240e207028000b4218013505000c04c0b04642c100410006008656550741c640405906a0303045640200e02031034260009820344040d00d00520412055500b48852800440d080c2c402111030350094070340b0014050480400d444106040c02003000b1240301a04180c40c1038800c0f801e5039161851400000d003004200001a200d110a0700d80112084504079100e40d40d8000480007801422006096142000c081c0012a040400c82c000418001d40a45180b4180181040180c0d13421f2200c00482c4000300034841031500c8484040d00d102c0120f80b60181e50f050101c03510b02c00504003104844003541d060700a000f03211b500030140117140420040c00325220b181a48002e80111000c1c401c00c410702a1741088a0115902e660100c8082c0460b007502c0c1780d0782030715070f00b0f110446c0481e10300482c060081c1000b811000030340b00c42210312076501692406c4c9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 814845701 1250 814844451 814844461
    0x50414160b0d020c030705060403020303040c0614030f0726060f01050910030e10060e06090901051b16080414011107030b041101030f180c1703160c1a0c0106050f0108 73
    0x8004c3d40000303200c250f5404280300c0c0400181003401002d0207180254002c41d10380c1803506200c0c3c2148055030114050000380b142c44100c202c00c42c400e680d03110505801c030b1940e603503034080c00b0b1f65100708450154040954207500c0d4203011400707200150144000f91248440d12035801c00560302882411000c9034444c0304041400340342032013a001401003040c820141e07a0704895104050040e80c01c03c0d006a221503000b030041040d103007881032490ba07000780030b90001c0c011810410001101201c919000c50b6800400107024210a40710800202005610042080c0d5480c0e0340c03208107808070350750444140005d250300c0022180368030004130030b426650000e10b051b030a500c0c2c3e41d842100304c81c11704025a06140d01ea0341068038294407441040888011038603042440a15844e1070103403049560013000c0d1034104000802c100041c0001542d01c40c21411102c106004228244030b04540c2c12359000740d441c109040104a1050f41140240c80302c03108500080c462151a0401c0103200c2007401c200ba80000c40c041c0002d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 814846951 1250 814845701 814845727
    0x5030115150203040f030f03031a100c2a0503010612031409040b100201020a08060405130f0804260706020d171906060224040201050a140d050414160b 66
    0x201400181e4011a46000c3d500c3c11012103015130359006aa02003200c664a5040c1a014068008449861074000c40c882842c1e8000a019403110840041007124012503107082005e01e680d00b2106c2040c0b80c2c548400c02e07260b08a00380030000c1c98051136010754205980010f0b248002421180800da141d150346031520324070450175550b50000200240c0c0151148032811541c0c03142540500101000d0303002503900d0035001d4010b00072545c0904001d0040b0718010400a549810340240c2c0110382c1e10880800922401782040416402130360084450303051001c07840301c00d10342c0784c1d091604034807512002e8950f91603035808140d84442413040c01401007000b80c003040c80c185500318001c660000780c424001d0101c200c014450405c40742c1c56044003002d40d0040381c8403010401c00803410048a03108038042132043c5007980c002002c0340142d601100c14802c5c400000d014902c2d50a0544d20707907050941b420801d0f4605402c0500144103042e2600c0c00600910102c80106600340080b202521040703815207243c002d180f1000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 814848201 1250 814846951 814846979
    0x6040b010b0a030906090305091905090601050703020c040501080607121e020702120d031e0b180403020a0b090d0801080114010323010501030c0312111b01031407021605030115 77
    0x42da0405590706600c03400600d542c40b6480d001c44c025550252100c54140c14000712106050100c146a0003c01003004240e440705400c50b801042880c0c1b8949403840b920b0140d142c000c081699503805800e14002089003200000c040d849424640e0343c082c000d01541071000c08276402d40c4500e445103840e03003850714411020303034008004e0540701602043d200385a02190764148403101040c01d0000c0e84510203d02c00e02c2034180c01804854115a0401a61072140c1c0010206904440100c5280303d514001909142c02486042032141d00b00c5112103952500c6078a25441e034001ca4002d40102d1950000840d0f210014444c09c021203c42d407140140903425601c9030f03072802080014800c101401600700741002c910130300449000394881c101002c5a5401e42c40c042900c075864040790010427003040080c815a1100280c218241002e4060303800c0509014001200501004c0030350080310305041c1c0030b1105036540011403454142040c0b0782d1201c401d448800f05400c1c1c1d903108502c80b11715400703203a0a01c0540d86201c80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 814849451 1250 814848201 814848217
    0x1a18070323011e09020a02010b01020606100507060c050708070c05010f0e0d391a07150207020406050d03120f0506031534020f03160f0c09020f0405030f06040b010b 72
    0xf024420360340e994a81d0260fa11000440005035152860b5103400e5070104005038001034121400c1806101138540205280200b84c40985520344451440001c035000340210740ca41c1d504000691b50790802401d0030212681244226070018458500640c6454840c1c000d26600600c020728450003410b5985440002c007a5440d494071040c00c003076042c4200c0c6110710104401d2010081800c14040d49002c2109000911204034012182001c06c00c02c0002070702c1103060f104c000380d81500180c48240034000300c1c0007080b0b02d80000741c1201ca81c020002c02c0c160460b089030850202580103006540e000d60034102554403d03540703e90140e10084a901080038000075030381d441940c04858120820058034118040540c08568800a00c149074200031002da050004d40d640040030002540b40c407410301c1e00c80300c8000c03400c0b401030040d41d03a0700c152a081200200d0158000c2180300c0c0150f480c0e0a0100f455002c9901074466540300b44103107079a5030744188010840b18807954000480049c960b10300341e43d4452543c04001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 814850701 1250 814849451 814849499
    0xa050c0f0c0f03130e1e060d0c1208090f0a080316021c0c0e01060f200c04060e0a0f1a06031f030501020d06061107091a1807032301 58
    0x691402c0810151215402e0030340c1c0d0002c4a880c1902c5050b81c0c1c03a0182400701400d144110a0003900e914035031143c5c00c44010f59410306220902c0c03e05045140664014880000b90800001e0620400c14082c01c2060f00c04c07100c024500303010404110641c0d020348242085600b0034440c0c0820030400301e00040050f40041c4c00c0745204806114034000d84155071504440e42c65800e04103100a06a072070546006d02407a0602510303d01c1441005071a680c01c244040201407600d1100c0507400c142804050404c03440900144001611060451003440e07003124200e48071803920308116001203840c000c04c44c280500d940042d000c1c0c56180180280ca0303000803e0651510400c8800207459901c280294000318040d03000140c407003040d16040d0051b41c40d154080800c00041d100340b0210003a020518a04481c0720a50009800e4000008031016002c0000f525a0042d0740c000300e481c0080846a41600c01c03e515a010006141c0e001a8420b902d11120b810a41c5018074600500c88070317141d5003c0c80307410700f4195 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 814851951 1250 814850701 814850713
    0xd0b0601050403080408030304030e03150606030709230310021c020c0307150c1b080d0f0b04020a09030b0601090b250f050a020405070203030c120c04051005070b0a050c0f0c 76
    0x3413106421036003d03500a0a0a5000004110a0550100d032543c80c100c01200070b0023054080409180c004600984424807031500000490070f0a8001d401100c000c14481045440d40c50390020002d10f0039100080d80c0e03009004d2030940c80444404c520844a205600c00c202160200744840401c1c0290004204a0082d00c02000b1601c01b10315450306440440f89030311408200074100c4030000f018502a01c1c00d0787d0032a01c4465030500003625410965580c6041d06c240050200090b01076107002e4001c2d40800754100348001190041282d1012070b40050301c0c000c00360b2050075124040110b5010201d44500640c03190184004001d201082e20b500341e0700f40241d80c00380b06a4515449910200e490320008848030340c0218007410850402c0c1c06010340c0284e03d07002035411894540502040d611988900420b091715070000515a0328032142643c0180c81c01070941050082d4125000d04a9030001c241a52007001c0c49000524117074660144a1089180140b91130030408041d4115240e0380028100080c140108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 814853201 1250 814851951 814851953
    0x100504021206101d0105010507060504020301090c29130302061c0c1d040606080c09031501080f15101403030d0f0501051003090b010311130504050c1c020d0b0601050403 74
    0x401c00c4074051180f00c0c5800c076100c0e01d0f14200c032024403204c00581d003410011400401076681c01c081501c4030142c00030404540341d84c940c0b0019004003840311008019040c010000b02d040030842c40558901c540d07201c051180300154652240c2d8501420000c3c0705045080038050005003442d5016021950a803540f500000030000448810b6a038007100c1c0c003002404100800e60303d00b07800080402c80940540f0200f0a80d0300345400240300d48801098823070b00800003d050705103510704001c02004031981c1280804c0c00e50311004066203604101240ca0142d00c907800d1044400528001c0050180768a09140407400b85088a0005046005842c05a2601007400070218544240c0108041341a012900140719814841000044c0300c45458240070580740035078040c001404a50300e035065a40042c80400c52075014000198680c284007401c620b90b50818042c00108140000c0310004901b088078001075000d030190034251500081c4070040d5100c4586020300010542d40107205802c4101854039520f080c2c2c403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 814854451 1250 814853201 814853203
    0x10603050a1412191223130203060a0b030d1806030522060b01030c0306061407020321030403030b062802031b0a060b18010605181309020f01111005040212 68
    0x1d200304501d280030000300d030011760301c5000c01c914000384034801c02a0500301e41210714001e810080a2101007411001b00780c0f00c00b80302c244200d13460380c0182101c4c5507103812034034a000b81460804c0705010f40305080d158000d13240117031052154070030404685c0000914140701180600f002a0080d42d001524004171156034070185000610103005440c0030070340364110720004003280c0035800c00d4810180790807400d02000354000404a00396843d0743c01151207080c5400080c1c10301d11a0102496103051030803021a0810307031000070311b220700d010352802c1040316080c6d41406803900c2121208510307039803c401c100442e1100031904441c0b07185144112803e101d120454480e50201050f0310031541d501001000c010841c8a00a20201d20020f8801e10f481104002c4103144258042c05490184140814000341e0680001001046844000c0200f011742c0102031b030443c01080d08142c141d0142c18003448040541d40500040390b5000304500040c0b003030649072851140200f03c0a801243e00440d010749241c40100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 814855701 1250 814854451 814854457
    0x4062a02040603050a0c06081302210109030809070b090919060b27040c0507021c02090a09030e01020a0b06010f0903050f0d0f0908060112081c0203060111010603050a1412 75
    0x4413410080c054a490342c10020480c0c000c0390305c0312003013161110030021810000c40d1000f4810743c2c10b64003c1040c14900d000080803d03019209010a907103000301c41d03810302d680030031181d0052641c10140c0d0191501d03400c1d906000c0c45882012504402c0c2000401e02641d040300b040365413207811040014420352910b07070302801c603808820301007403509007059082001550304844030f400d904222000c000c1015890800340460140b58001303881100781400305078800400e80c50380c902059005081c1107c83c40c00c0749400d001040700184c240d001980e40420700c2e03415400081c0c0d00945070b8120421101070784c0c46000460700454a0070400041188040001002038401c0055000900c00c0001600302d5a009050041000316008204e10411100410800c035036800402e090341510541c3da03800d46038030b00c58140b00425102e4580c041c0b100b0401e8690034800e070700856001d140100402d9131400c1c0d030480340703020141c2a80c03a10700000c3c04507044145180c0014004400c0307108120181d0013600d017040d1071008a0b8107150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 814856951 1250 814855701 814855703
    0x60607140f012c0a05060610210f050609060d080c0c0d08040e1f0603150803160b070309150203060103090c080a02030d031a01030e010209040603060f06090204062a02040603 76
    0xd041c10055501d4554044120340c0522110f80050030400751988500d5030b101c10281882d8042c0700e402900e010404d200310058403152295012000a1400030780350350b001002c6d0905e001030211314040c00308400c0e2401507065030003000010552549111103441d43c000036400010000c4240c801c030361a210654aa04440410080c080d03612940c96510b80100000b840000821419060400c40d26944061902e01501400c0d00e4035480c0004070510380210610302c62500d604032010900c404103042580c19945030400c207400740305141206050b101c2c0b00003079094035021107004100909040d4004010402d0b030303014607804403052401003083e410503140d811004010380c002543c1504400460015414204003640940c01c2606c0c04104903106083c04224000c12009034070b04154940e19894a8070b04250161416907000a01c20040b4070340d00c1c540880107001041014840a081c500300064845051080d00c5c129100d68480721405004402c013031f080c030800034903040c8964420149203005600d03a4070402000d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 814858201 1250 814856951 814856981
    0x106090c08091009050d031505120f0f0f250f080f070602030a0804020f301605010903020108040606080a080909130c05010c020d06180c0b03060607140f01 68
    0x281c2010070b02d240c1400503c504820003181442d845200040d00042c503c068a456450006002c00c107880c50850100072591126034000c4002e040e151440d0000b0900921151000007100c00050300f66103441e1325050308960340b0591750070112500040c40143e01425800000202c80e13503074034503225030301e840c840c5509400c1601c80c0e621460f18090300c1802000300740090112400210704082c841c120042c4840002800240544520341140c12941c88049058000600443c40c810246c980c210fa000804411038108000d10b1080140440403001c3c1c805110b81510010380d1f8200344181980c0040d2030081001e4811900c6954030500015842810300c40d68020620400059944603441c1003000300c0c480c00941501c10381c001004011001038500c841443c215a404e00b0036503051229800042c4c0c6502d501c0c2e0f4090421030402c801040d0400c010f5500c0743c450303440b0701c3c0c80c80e00d81038031800ca4601d00c1c04215000b0707130490340400001000c43c6c0c450150b504207582d440c08492030f20b200f81e0380c00c07820340e0750f1801d1152a03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 814859451 1250 814858201 814858217
    0x14060d0213060f1103030c16020d06290901030209160521040303141e090a0506010806010302180910050406020d14010f080a02010816090f060c03030f020301060f110106090c 76
    0x82e86034440340101c840304070703071340190f045003007003604031712a481480d0400103442500724850045440316680b140a840e0000010015400280c01034030380886e990304d161900380d81c1c843c042840340c81c1807243e483c1602d030040e00c002d0740b941d9031071001180d07001414400014407134140040d42405179910028036065114804484080c00c0600c1c011701914049980300300342002d01801c010322a00710384542840c0380c0c0d021030b0195068940d14402400c0034204103018146000d40350022130502000686141203a1080e990b4202080008111240449054604c4011a08060280420f065140e080f03039800c28050350006250a12402d0301c0c9040b294018220750764424590010460301d0072491039400108030300c0000e403980b616268002802140004c04c004045494600e40c050b03628811408103000d054405d1164004e10340b220006040d004828404034006810100200c080f0711403802030b00d048a140da10340302048c030048441501d91005080c04417011f0744d0384981c0082d000c0d070f403401203600010706038481c420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 814860701 1250 814859451 814859477
    0x314070504080c0405011514040512030309060901020703020a03031a0a230301020a170406020f031812040311061c061401021b210a0507140f0a14060d021306 69
    0x1c140b43c0f43c0145540b04500d03200c0104180800d41d0803646500031103150202005d240c6100c130500743d0150b604056089903c22031041807010002000f14015400041113508640e500b0042500707074403c0c1a0000c005810190a00c000203002e5000720083c0b9010051246040c900080400d1000c0300a03031003008a084290788642103a602001d00058000c4180d00a5241002c2c0d001c020301800200c82c00d141004060388009000d0180720342c103170b400311412001c4c1140e8038101b010f0903a01400040c0d6003401c0d42e005030581220360041e142e00300c0382220ba0280040d04180c42c0032040140310f0700402c90544001010b5002041c6080d01c030320039038001d0715145c0b051110454018000a01d00f103d1501e0342d0040385003004040021780e4940031000b4004050113a01140e9180103c540c50501c22107550003421840b440602140c440c80247c1599101c09084d00c03800001007000c420408916401d03c60002d460301c02100000c0e0600b400e03030040038015403c002c05450701800b640410035204041d440f03c0001510850034003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 814861951 1250 814860701 814860703
    0x10c12020307300c0305031506040312020102220f0501080606090a0303020708070509100902030405070305030703092301212903070605040b190e1810050117040b07031407050408 78
    0xd40c280d280b8134008000e0b01e500e40c1e01408911001c1d10001d284034200c100c840043c0d551008840203036a02680c18025142a020064003035041008108940c0410b440e820001a8030818114115030140709200703099072609005550070800a005a600114100a469484c2e11001c800d00c0c010341c4079500912846240c03500300b90600a0300e41245201391120350070302c101505208040400d41d404070900680d2901c0780d140442c603042607607200900502000c1050000c0c9a00007946804803542c0100508551024072520349a40b000c5008540c0445e200c001b0402d840c00c401d01c5e03918580d2001050025101c20801d0355100d1144880391800c0b40311040c61a044454203003403110f90014a410304045003030500303121801d28a8014070f0841c48100211068401103941328034185d00c40c0d50b10252202c00038007507a810038903c50301d0481b942c2000811303031100020694810100e150950301c2c2d03001482695192540e0b6821000005402e60003016114501d81100f02c52140000b800b4201e907403140c03542d82c0e290140381 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 814863201 1250 814861951 814862033
    0x30813020405280c120507020f0a0809131103070c0c3f02090c0a0c140a0c0501020c01120e151801061a0a050d0e0111040302120705010c12020307 64
    0x3c00f2490910450686070f0703801180c6201c103001966000319940d581c00f0310407403404221940041d41032080c80d014000f4821408000c1c00e43d103a090302d40b11034940c0b400d5085010307a054a01c1200c600601000020181131007150200310052082d55a83d100640c3e890042c0c40f10060144084521084112401110300c0320510038070400c0080100b00140c0329881d000200c649100400062091300300003100b100e0544201041501c4135800b1313064041a0b10050071640ea1000c18550854000404e1700300407030703950700000d0320f000740481c16940c1003500c01200b03140002404401e5480400303031003607185005044400c645d0591190821540c4c903003420f02a0803001342900c01ca40c0c072010709800c04590070301c42898035a040340c0b659501414616540e461804030034005264401c0303441e1295107080f00c603054000143c00100112802103a40010500d580130b8100d441d080c0901c43c26010a2468014200207248001850708000781401aa4107120882e182c01d035168521480d24081d0a0b4088000f4070601c0f81842d41e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 814864451 1250 814863201 814863271
    0xe1204090e190215180916082503020a030902030f0a150507050a080c120907060f031407030b03031c05061302070201080718080f01020304120c030507030813020405 72
    0x424003071042ea94020074034401107030094100d409000a2441e4089403040741403803041902030f0440c034407071400312045244c0b10711100d00c03e030000748013002040c410503504201d15844409620961100c0c40d0f0030800b1340081d0300c54142c55042c91b44401c040800341ea82401000f0100c42000c01a00c10550146044030300005403009189200e450842800040c0c0e5002080e0384541c1c640c1c0c184945a6101c802d1341c002a405281c501d284014a0301c01007004036007011076984100c50b02a144c0b22500c1c42c203403000760285e0f41e6081140c281400c95000003120184650441401102c003d4240c0b0701c0c051501d900321042c6440500b113501c0c0c950302c51042c0203960520310110780740b69525010450a0014640c0003d00340f4801400010800121450503c100c1130b9803030b100c9000308102c80441d00caa03070b14088058080d4008682c2614207441c402c000b2070000b0300030b0700207840d2198103641c2e0620317103c0c1c0d80e5001c2d0f4601802070807181000200340c90b1080161603d1080700d01881004035000001209100307403c50056419030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 814865701 1250 814864451 814864483
    0x30c18110c0d0e060705030a02071a04060e0904031e080103031d060304030c050f03070f06150506031f120615050f0a050402070203030f120a060e1003060e1204090e 72
    0x8400308840d0003080490200d215071800b03140700b80d020340024144d8040c0300805002030000080140c1c2517500011101c049801d000b0140f40a24100c0c0001042400f0750311403400402c40e89101391106180250314180e1081c441e04003000c0700c80b075851130756034408110417011000c80d40c0d982c014003d00d604020186031004100c2d0100c428803001c00040f4031036000c003038002014061414110010081e09200052408042e0012030b40c460300305050020046070104811744942d0301d0800200f28505411402500380c0d04041c1a4602d035803954405c02c1800340c01e403184820704c4140f0f4000481d000c14000900e00080c0e000e11404550704050403842c81c4030030f24542c040c0e40304403c01c41820340e0b40c0e118507408108803501200d0050321040580042411031003501c9040d4080c185c0003c00801c85460030407c6070091030108000c112090302d4000c0c42e16868005e907428080e48034900800c2000842c2508014041c02e03180c001c0e80d072a120104055000c0b90442c3d0405061107403110500c40242a04000c0100040d012003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 814866951 1250 814865701 814865707
    0x81e090a0c0503120a0503131713050406030507050108090703020a0e01080d021c11070510050c0f0a1e0318030305041503150504181a070f03020a021b0a030c1811 71
    0x40d007441c031505c666561102400340200c0002d4070002288205203105801014000d9500c15990f5444074681c01412040780d074000c4100b0114031070806204d00c0c01071301e034003070001c0c5911810300700150b503a07d0700140103201d140325411010005803038a00c130309801044d0b0701c02c41300441c2d418100c1d110b05000e03031b01c42d5050455004441c9440c48007000d2045880d01d00103400c01c81c1120068402140c1460100d03000a60004002c22900d82420b6002d07006000ca400c042c02550f20f0005002d100d10b80b10710740e62001800a004100342e003d29103000b0032000c071280340b190400a088505076a500c184050481d44140c0104001040c01c114051071280b030700c18600441d00d4104074401040c03126001c40f010310300407507010f10303500d104c00c0381c07800b1312542c2c1d10000c281c2055072001c2c20741101780c0e00700000e10b003201c0741c400040759101c00e164100c1c000d00a0700c00d1701d0304a802414141c0c0140c20800858281c000c0c1c020b5220381500301c000081081d82c08488043e05c45070b40d08248110034190348405855010070040c4403020f00b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 814868201 1250 814866951 814866973
    0x612050f06150901120216020301060e011503270510051003080d150f08030a090b0406051e09190e060109060c0602031005060f07030e1e01081e090a0c0503 68
    0xd9000c0b000394500c08003000d5241d030f56070b200403101c00c0440462202480e20019160300b41140307800001d41ca15100f18000c0c00803035210300200d101c51000781300e14201c0c40e00c46149042c20500030b820400244070600d007580c01810905060010043c6030705029509038000e80202002c552050068540c0402c81c038210000386403440d9079549a44c400d5140b1403130865501d03400c400c0c4d03005200800328000c003c20003400b81115107038074680b503da5104003850740c08141910000182002c801f810748007142c200d91601800c042c8881d000d182d101c00f0007880058691070400c05088181c0e5a00c070070082c18252170a491070301d1410861840240c24010342468144003022004100c6680c0c00300100c5003543e80035401503165296540201445480d41c0c000c25031200c0d004c640603e000000b0310182207414004d0745e030303600e80b4110103060105482810f031710700c01c9038242684099890f5020b42d0445400c8100c44211040c3c58a82d00d81c0440051001d403a065115080100004140442012003c002d45070803805048540c800e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 814869451 1250 814868201 814868209
    0x50405070509060726030a0614010f0c061103130b010504050405190321050702060a09150c0e1905010908060603100b0105120403020c132f130612050f06 67
    0x60407102e984507140001d407080410148201404d01651915038004c2205160345800400e500300702c42104800c0d1030400000f96105480409034016001070311466590004100c0895542d1400f100540b40b0a0f00c2e06001121910390764021403060b0300c96800915052900d01d00101ca109042e4080380c8a0b501740010300000c03841c081071b20b0040403020580c00c085a4028642a070f803000494800d03a13003024110301102d004a11340d4001d00d210f0a4640d003525103a0f5204800c0302c080f41d4014001900c42036040940780904049584000443c1b40c040c01e21282d19040040025803410102c0407261001600d044104000c1d40c11040b010f018108110150260345003420129540d00c5d0b0861280c08515120040074903164090011940b80c0200c81e501d4601c1c52402e41000ba50b100f001d046a02c0c05000c1134034940d5002d084d40d1140e600c2400c0004040f100c4100300a480001c16028400e40010719442082a0001ea00e41203520000600c040c0d104c10384484c1415a00700b003120002400c84148072202c904000c07085d62 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 814870701 1250 814869451 814869457
    0x124081e0705040b0a0305030a0e130903080c210c2214060d060b07031814010c23071203080f010e0a0519020d060819030215041a130c0504050705 64
    0x10181d0300050408000b50001700514800d0788003800b14040055841071182d446001703006140c070190382a2048038592911201110002440039001548420106010303d4502004080c0500010341d405118030100d10f1404080700d084e14501540c0e600000d1048107804400031507501d1208025138248a0391500e42c80e0b400c01a40c2c4002d84c0d105200000d4802e0340c1e42a00d900030409081c11807000742d1591250300d0b01070050022400310000354000c2e1840002d02d030741d0a00441b44d282e40d040c0e481402042141d03541816410b03c00b4a40a10482d003a45100090881040b8010090034807120ad0600004c903420046c107685c5000d4441107a008119005002c5010310200007908516260000100c035511034084681c8032540030155420a800094a80306250068000030251030442e402e54040007252205025403010841e001000750300030031a240040600c080000f54414060380340e8002c505c1c45000d080026003c1291034881c40c2101d45800c10502c84181179800141c041a2007c110344d00700745001400c680 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 814871951 1250 814870701 814870709
    0x2010c1b020102070e010b22050102100f20070317160e03120409090327050120032106040c0210180606030b040b0901020901200124081e07 61
    0x80540e1015008591007004003074001c1081d000c12910950b142d01201c0303d05d82c0611007200550050310f01090b14410402d47c05021107505800074001c5804641029000d4404610040c00241d658240e41107084101d8102001c01889041000c0c1d17034103081d19000d485d40ca990000c00005001350390030841324000040d81d60415810a040c4102d001c1d00c01ca00180c030300301030340580400d2000c01180024001e02940c00c1099110700c2a115100c895006111030900444041781010a0881402041206501600e20a244544050306104110300c0c1c01500070319540c4002100c003102c94481c4c0482c030345250039100454011508030703014400101140c000070340d2550f079440c04a490311f60300c04141508200d00e000420009500020900001303a80303003420b16006a003200c05451410f00a0000381101ca010b04c00c40381c0c80d031016100d02504401803400c04204114100c240b003201d40d070b2403900d0b869140c4440d50a407001c4020102e4a03840508024203039041c07094409010450500c000503a072002840418000191 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 814873201 1250 814871951 814871987
    0x3051005041b0f061704110f03070b130e091903030e01020c1603030e0901030803010320040f0506190b0906070c0b0406020d031416030b0f18060306010602010c 70
    0x15845504100580d414000c0d1944441c800040000412030070f00000303001240d50355140e03031141005500500c10440b000310340052510500304114021b0340b40c890b05010f401d0b036014084a01c01c648902018a00e640007414445500b040309004011103041018a654429510406030100c40000c0310003050003683c80b08000d040c10749540c01303480bc400c0c0c00d50540780410695400c461014142c08580180400c050005600060b400d41c421000c504100c4503540c120303940718402030f203968a1900e0707400d0301c203681c0100d15000b800e591081d00501c0d5514010384088841020000a56042c11710030881c204044440319003600400c240100148140142079484802090b00d156070788808078500200701e4072980d08040c501400101d40410f80d06c2d8009114207030862180c4007004084c00d84c000c00b507400101110b80d00c1c0d0f40d0ba4100441c10255101707030081c07256402c01a20140741541104001020b40c0c03000441140c00b02c1002c03040240701e18082120328010501070000b0401411070450007020180e29004a408ac = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 814874451 1250 814873201 814873211
    0x11030a09060b060a12050c0c0d05030601020a0b0123040b0102070302120a0c030507140118060c020d02060c0f120406080c1b01020d05060102011d0304091505090f071206030510 77
    0x340a0280c00c0010203200c002c2a140c0d03100e11201000d01460411118406003038071b0070001807070542c0303160304841e013449030b5600404004600707010480c3c0944c0002c004034114040c2d40e09907400103840a251502804001030300c8818140d82051aa02d222854450240700c1d44c1844500e101c3c50360003050603800c0d650142e581142801e00d1160492a1064004008160b080c9008000051000209090056411408441c040d0724124030045079107a0703503001c00003620700a04004002090040c5100301503c1d1016000e40c9c001a01500010f40540100000f141140c20841483e00240403e000c02c3e080240c5011300942454200800203100090080c00e402e1400d03000076044000c102c016805d8205000c200c8000d540d1204140c04420252000352149070266003024950822040c401014816041600d0011414185090510000781202c08502d159001d40054041600d48a00c90102d1040380c40703039004c030810b08100038000c2544140d08140c0d14210724101d81400064400b081c24140745107980e0000c50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 814875701 1250 814874451 814874453
    0x10b0415210f090f030c0201080f0c0d0c020a0204110c0d08010810050612010e0d08010501050c06060120073008030103080a091e0504050c130306021605060f0f070311030a09 76
    0x3e02e6955009001141003e480390b0826034452a920001e520070307a1200300b0381e10b445019070302011055034284001c4100b0f0000500b4440350380c2c090341c40c0c3c48a602c1140d4079140c07e600400d04554a054841c55002000a1001160602007141106400007403170700104949c5400081c1b600e816040465104480c0c44902040240c0d68480107286840c00c034000070041c2c2c006450709240e036092222000e40c045003201e4000100e0f9809902030303030a010f044501829103917031030000460b035132254110b80c3c4540b07448c2031010303a840707a20801800c4040c2014051005c420011007200e0301410180221809000c3d0341c10140d580003a140d402030320b0469521a1809132100c9080409a9401c1c0c091b4011002400c040d2002c0843e01d101c030095002154015101002a5100c00c4000b00c041d10540240800b03c00c11041c0070000996143d0040c403401481003100c0e14804026035a503410401c050740c3e00c0010180640610000100010380c0035042022070604000c80c0f070340e000007000d1078040100b20300c0c403c594840c0a14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 814876951 1250 814875701 814875731
    0x212090402130f0b040609090e061f09022d04061d0d0b0c030403030b060903070308070606150c12020a0b01031e06020c010c080112050312040614010b041521 69
    0x805000345003c8811515240c94107035032540c12074410003000800d41500001c0000c924441c8551002030100502580e0742c418540b00b1740a403100040d01c48640c15044c00250b00300d0b00c1e101801d5918100a100c113014211105516408401261405103401c000c0004000701c5070000041045038011920483d2200708840028034400c80c04c11300035191000040805c0602c8a11000070351040d4820b0700d0800c2840400c80038007603680105c0400c1c80e0140c0c070882d01400441c40103005004170901c10400403a986031540d41200388400441d03030071000324140000b88010846662071444070041e5601c000d01e0141c5007500d0b079044900d03041c400070b85180c4c0c41c860305070a9042c80072550740f90749800a4095640b104070100840c020030150f030084000400c3e40c0c1c00402d18010f980c091245407a0444015410056805c000340000c1002620403500ca66480400000743c8501d5031141e4003c044865030140c407245041e034000111940314541e00c0c00c00c844400c03c800d01701c005c0c0320748940d10284014001921141d82e1615 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 814878201 1250 814876951 814876987
    0x12061f0906090b03011404050318031e0c010f050f0d021b06040b070e030a0c05010323010303020a0c090b03070303030213180f140f0402010507061103180106060212090402 75
    0x8a00c8608015010030038800342d401103952080e0540080100f070303441402001000d40b00340c5004146401c00c0000e1070019101508507000301c400141541c00403024044108206103c001520240350400c0102d9000c540e0044101b40c0000003900702249803010f80d4441c0c08992184440929549502085000502e98004002c91026600d9006c0701c00b03a06160070040b242440c110b84450001d035142101404904010540e034852940c03022038100c0b90303030400c0015406002540848640700c03400055504095000c800d8070b500841c044d40281110008a0a0035014040030750481c50106080030004002d03500c000070442c045a030546801a107800c104c5002900720a050750184245000c060104070300c0c0c075069800003510f039414640410250384441c894056100044a0721800c0c9040c6e1170014000d540203400900f60a0700c203002c0000e4500c0f0030622030101e50815030341005000a11244a10341000901c503010160109000400415040280c40e11103480303001d50160046801040141981c60482d103a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 814879451 1250 814878201 814878209
    0xc081f0603091703250504062a05190209060d03020a02010c080f0414040c02071d1005100201050a150f120602093109150c090b0a03090b0612061f 64
    0x440d0303690505c40b1a5688071300000b0402807000202c98003851260740100120b038111040d903140c19810343c190342804038054031403011003123130b407502e9402840000da420300003254054130290241c0d032264031a0060000420b00102030034040c20300c48400c103012030380002d0301c48101c0d58241f814961041d00c51514003441c1c00780000d041d01000c000318022a840124118401d140b0701c0503642000032840d880c0b400c91759410148900b81169109071a0304000b4409145116489100d2029820105940740041000110000d40c9a070050350f6407001c3c041c40340e009001d881d80007882e25002a40d210f0900820900300d0b0303501e1168105c046c001d111030b5410022a5019900e14440042c1562807440750507000006074810507002d014144640d030f05015a114440c8552000560081c1110900303007940400c0500404034144507030240510000002581403080009241e1107200350780c08030f4081c03032314908945190805080c945c4034001d5203204d4141c0d42c100041c240d0b480300181c0e01c000c3c05580f500c06003500d41c07410390b00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 814880701 1250 814879451 814879493
    0x2f0c0a0203340b030f04030e03120d15030206040b0a030e070b04030311010513030c031211040f0906050d02040b180c180d02011205280c081f060309 65
    0x1007018030b001044540640c0c41c4480b000d591114001c0120750140d05840ca01031820252418808154400c40b9010a0f95100344a810302d8181611200002440d2098100307544100e84000500043c41d14014002d1791842184941c154032078508681c0010b14500941c081d00b01d0401021800c0304c5081c1c800d400101e85c00f9005400d80c1c1c400c0e40c4889940d81c0560250000343e010902c01c502c0ea40800740144900c034400ca529200c280105807203a60100d407841214141075040240c1c000600031400c1c100d104000150642d001c480307030b0340e91a10107540a2070381c16500c0b00d8030b0207180000c1006551078880241d8030b02a8100e50004040c103000001905e0b510524030098000c91107913003004000500007008180444140c0840e00341c0401c400300b041140780c1d8014000f4000344150149d01c4440d48141c000a400c6441403041180e00040d42c511a03c481c50b54020358000320b0340b0750b000c500003d90041d00e419001344641c20308161050071142884000000c43c491401015951000c00042c005038014448041c10051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 814881951 1250 814880701 814880713
    0x150612030c061b091008060105070606120b1012120c0b0f07020c061c0e121603180b091909020c010603120c03090e06030a0609050606030105071803060b120a03050d2f0c0a0203 77
    0x100c00030700e410dd400780200c0e801320142012954550700400c4050403510400800c0004640303036076031a581010354084107404d10020340a520000340c10034046510860b1007601000481c9440c030002858001900121030244400b004000b03401d44404586030072204d8490001b150703102c1c11f070700c00f1031415040e89121448040c012401a5050740204a018407541c041e80d9000c2410b444600013007880d0b2518403420400d51000c2040700c4803400c004000605004e4540140d248181e81c1c2c401c4034042e6482040c100075075135510303001441001910401d2a0300d030131907440c082c0040542030398083e021002c0382c000d18090324882c8001a044e99410040b08034000d80c400b4040c04090201d10340300e035a442003950300501c0f83d42803c00080b002d0b0b00c904030400c0700d04140c00c214140d8a04d1912920001d0040300c1000703030032449005001080c0102045244116407180d501c1070740c1e884a48403042c0c11540c0050281c407181c00014049070000c0c14400c6010a041c0c0e0095480356103000c84e40000d49014512500250140258 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 814883201 1250 814881951 814881959
    0x60518030f0105040804140609060405010f0c05070f170d08041b080a03030b030d080405060604180507060c200f040507052109011409150612030c061b091008060105070606 75
    0xd14054022130b019804007001066501d020423409019029250303400406c00d0204010f275606c01c1c40e079040409040d003012007224866450341c5080c000d468110110329000078004025000e40c0c214003540b80c00c071800280c600c0c0000000000e04280300034101806001080021184520b80c800c0280000c007561801c0790b103c699030b4078000c0c002d0041901c056109019039994415100d0181d000f2611855000014080381d949200c1000000d1580c0c1c0d00e07112110b9074040380382001517020000d40004e08002d488a840b50140c0740b5100018821641c8401c089158000c04240c244c0c648040c0c9200410b000c8802041d03a40c0e45000403a5540580b091810005480d000d2039038010080c4134149001da11268020311a050311a495800c043c6029a0300511b00d601102170140d40301802c21001e9045130005000880084c6800c1046203141c00500701101d23141c0240050014403010700420940d081466203d0505140310300c00041c11401180b234401d0103204170000000ca10368407444c02c603020198841d0013040140d8407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 814884451 1250 814883201 814883213
    0x7051c0c120b09010303110f03040b030609010812090d060f1b120212060427210c44030613051003030c02150a0c0b010f060518030f010504 61
    0x124240c4a40800c8414604141d00030442c01400c0004001401d05025030f4038641d41107446031405d9004101e94001d01c50818280701091009000501c6015841074407428698104800e90506a20691040d441600c0e0f000041c020300080d5100c81104940809028482d400c3c0130000d807101e41d07140034001d45484402900302c61103140c031840d4401296100b44880f22018292400c078416500f0113441a000100020305500d0550058071401c41d500b4815041c4c05580380140d080f480541d1811a032542038461350742c0c8401e2070310307000542030451b625001059180580b14401c07810301a00d60601082c0d00f2001005018545a02d070703403144911500703c000f105140707140002c4030350000d907102840b0305040b428440c0612a82c1c02858001c600c0304204902041ca165000c1c1d44940c82558104d030000e1015140e8005201c0c01e4000d01010384060f2240c0c6c0350310f00207241c09201194140c10446654603e8601400030a030311000766424803031905045c00401241c100068902441c030b0302c00c0d8400b9802d000400c010001c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 814885701 1250 814884451 814884461
    0x402130509031201081207080c07050409200a140603070e1003090b1308160c030c03080304030809121b031303080417190204021803060a0e161203050307051c 69
    0x1d1038050100aa6205c00106071244601649042000c40c10f00c42440803400401c01880c0142c00c0b07404803084250782d036000c501507600c040d0060720300c2c54050024045c1000c0701d04807424440c008407007120002d0300b0b0903600c80c080c500c0614224041c43e8040005482140140106c0103a1403000740080a00b580c90b500044c09400407040458104080384080b62501451010003a00c4540c050740080c01c24094400d01e550348401140d0650319002c0030720300000412400700c2d12130043c41c010700d1415035918050502412103400941864016404051610343c50981c0f881550b100c540041d40340881c5030144900d061950098400c00524801c403040c00104011001c2c2c0180300f100c807086502c10350740500b1042c40d61218190525425090100c0c5c080d40d00602d4242d009105800a2240340b0200c5210140801d2412808480481005681c0c0c4d14441c1a41802c00c03d002180c0b000440807c042030916402c4482410510001018000040b020a000c2030180d8143d0b0002a02c1038101c1011961401101c40a81 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 814886951 1250 814885701 814885717
    0x133c0f05150d020901060c03170403031b180b0a02070b19020c0a06050706020906071b0303030b04230702030903061e060103230709081902040e0312040b040213050903 73
    0x50450a818150b81424000c4207003040c3c00919030586686012001c1e1000c41080008404100e0950001c0380a900607007421402035000e90750001c0d9054455104c56a43c04e06400c1d040203200148280f0020421405800005d452441e40ca090711009020416450b0840d00e4200c0c810080000c90210303031985000c00095050300a542c21a400d455040c41400845603013802007000040041110030041001900286072411015120b0761a180c1140c5800c40301c205044142a0051504030003001450b905024404071100c045030100203131010032002c51445100482342038206014500021041402482640c640d001c000d01520ba441c58420b030030221041c6464000041e4074100000f14130b05500c01d00c6031050340340740c0e03120400141010b00c1040421703400040c5803070200700340b44001103814007090003003003504084140a268441240e1040000b603440b0030100c41074943c030074401c004e110002d4001c2241c2094101071400d229071107074000728a0381071252100541ca2810402440821340000000304108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 814888201 1250 814886951 814886971
    0xb0402040b04020304022b020a091d0105060303042705010e160c0b060f0d0507080c030f030906040e041502040f03050d0206040b0711070f090b133c0f05 67
    0x110107400c00c0103d0005840107034001703032440001c0c5d0303240c841012094840c1800c3c541080105100d940003a084030000d0300b05100e041e8607000c2d102c00d00ea210702030b8190711501d014020f1100345040e0000c00d0b0789001e513220300c00090307104020402c1da0181d050140055000700680a029660f1180e503100c0210100b643c0c1100c000049900c1c0c10070f22031242181d1130b0782c940e01c10030480b4642c84d008100500b0340c40c1c400000d64003100b401e4003800010030030040180244401c002070b041050304241090f09000c1107512540d003d410030040e418660f82c4400031036058070010344003480b03551950304007004c1086181d9401e08010388000b4011410280f8102040201e9110b0400c58000c0360b500c3c1e900300d8941c0307819500203084190030300206001c13078040c110f03080701c807200c0d0310455484940c1e038680205110031942c440c00c4811f1355102055041c1c14420f55602c40916085018440c0070300901c0c50301ca50b0407019400f200e4070440c081c0d12052401c8003505445002c00042014005007008000000080c10251020740340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 814889451 1250 814888201 814888211
    0x1119050109060e0f06030a1d0d30110409020403050705040c031503080c2d0610060f05070c0e0f07030b0409050a110d0f050f101802040b0112090b040204 67
    0x2216100c0e00e0440100c0201074205541c1211184c184042038101611030032071252914240b10a01d03c0000b4801040c407528001020300030208280500700a04024074482e110030012180803120700c0c1081d14402005a820000484e481c50800710301c400d000c0c5812500701d660001800100b401400900c41c800e881c01214100701c2410800c000364102d68010450081d0b9205012040000c14078040103002d9100416042d11141c5640280f08100d0190700200040d00315442902607188001c1000103591000c56949941241030404502405490700c02d4215820480000340c40340811083c0340740403000f0900d5542d101240c2c10010a00940400210398043c00203280094507101c52402d406581d182ca600306000d003802a40f9034603084810345007403a1854002c00e0074010940000c04655000c900d150041020f032191030302808072107040102d0001d460004505189120703900c0301c02c601c3c03003089083d030454000076105585001030743d42010201d005070701d10345020f01003014006003104591045101f1101004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 814890701 1250 814889451 814889459
    0xc0a030b0f030d0e010e040609050411090717060307050d2301061215090503071505060604050a060509011709100b060f0906130504020307050a0e09010501050f071119050109 76
    0x2452081d00030056065205a8900d40114010700d44107211083c1071600e03c041c0503041c1c2c0031400b40d9a83d64848024190346004000c280401c0340307110858100110f41600c0d150400120017043e0751f48024100307010038000d4000c200d05940420446000301809041441581000d09100038002150f070940d850707907545002d094007201e1042c402d80e000d4448400c80842c541d16191601c40030031079005054442141c0d00c080200c08502d04202801d41c15114450103440d0000c2c00800350195400a030005000c0c0b41d050205011540c3c0728050340080c4c40e46442c1c019210f83d04803004890f105001800000d104c1040740600c030040340046481000881d40321000c0c8440141a410300c0f110f03200b00354100310b08040610486160b4581a401010f6000940000d076202039102c80c0014102da0007504d0603804920700003481070003680c1180314120f08102c1100d00c001198942000640144245c5155024540000400608214a610171104c004c10090800c200c0408900754091040249014841c003091b14190001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 814891951 1250 814890701 814890709
    0x507030209010219080d0f11040b0903120708041202040f0e010c020d0212090f0a0305030a020604110306040b1f030f08040303090b03010803190c05010c0818030408280503030c0a030b 80
    0x2032403055100020a00d01111b20480780018501c40c09031000141c1c80306000300414600d030010304060401180c00c80d60320304c40320040610345203107001101ca00345000c0c8140c0e4003141110702610304540c446401c42c000720345036100003401015014a103010840c50081d00c07420501055100401140c000d0f022180710404802003a6038420702c042c40b20b204080f0410400e1058200006a07440004001e04a0b101c0141c880d070b101411500b200e80301c3c10060b4001c40c100018001f400d55030200400c000c4e40a41114103050b04d580d48040da0003003030b5190f074042c000800402000c02c03100e000300440d0844481c1c0180703002850000c3c640c0d4458403003640081c1c400700002c0303903a0b64007904032030403554488015480d00e5140503007200c0b08150240302c04148102c1110b00e901040003030280180c1c007580c980d20460300d443c001c0503039144000103550581c8564020b000502181e080040e160310340c0c010b8003050068007601440c0e00c900c111542c2000411502011051004a541020140c11071000360740f014041410030f02c081c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 814893201 1250 814891951 814891993
    0x91005070e0d0c060906110a020415081f06151b0212070303050d0e240405010207080a03021309021306080c0d0606120528020c071e0302010311071a0c0d05070302090102 74
    0x21f0b00050f00540240401071800794020b4021498030550f0020480d40d9030204c9081180b06070718000840d00542e000242009031303101342d0024240400040c20019034205009054044d1703181c00e00246154035081005555524281c002850380034001c80d0749031a240c0c40c00420903005442503040c824101003401c6882c49001c182d00008050f0703148010300800c2410052084084040c0050754075540c03c0200201040c014401040100d0583d00e016a40d641d42d40308200c0103045652182c500075106000c9500380074a40741c0f500b4200ca4940c50102d106403910070002d842403040c00390794103680e860030100080503a0092030300000301e101400200256940c842c0400c416180d40307120754250034100a181c03102e00c28650301420401402c007049403c00381c1ca8012600141140751032000c50301140c408100110342e0305010b01c0800d140351100943c00c02045586055107600a1814141103a845000040100d4540c01c00c0e56801d81401400f44150704045401900942c8021a0784d8014000e08001c5c0310f10413070f94101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 814894451 1250 814893201 814893227
    0x13080c1f050114100314160e1807050f0c0706020105180106030f0201110a0f050c1002010b0d081b032206050901121a12071706091005070e0d0c060906 66
    0xb08202c074a02c43da08014100c414001a0001d040c0e850b48000d92241c8410003451203850080703146818040320f204040d2a404040000e50700c07595122080d000d080c002101c04540180c007900b042078490708101c1200f2058000c146000307038581300d203841c0000c4140d41508154010304480c0c10350840031106018a500741d0320180806449004056021801940304500c80d041c1c00c00f03650107483e0703154050380d0b991a40070080e200959440c0d2041407001350510b800c003803e000f000341500081003402c1c0c101d0080b5444031400c4d04090309482c07020a02c1040d0210380000c1d451501500d50a1b60b9544116641e607104c0c803120005003800040780c91a02144207809a021500034501c1612035409440c200340701d590281645d41a00000605c07403a10078152520b80010700640481000007034640750f800e007482c2800c04c0e40c1165800c0d0050703000e4002d100149002113119008030100314808503040c2d68096081c0c0d500c5501c451041d40105014032100b0601000e6100d15050f146c16940350700c9d44581d14081114080b6120003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 814895701 1250 814894451 814894469
    0x9010b0916050406050a030912021b0307030c14040e030c011b03111210051509030f010b371404050703060501140d0e150702070f0b030109020313080c1f0501 69
    0x3c030034041c1c00e001d44060807240d0b400d40ba010640308016a6240c100903180f11610f0090b034010030064a5500844044d812040016801480e4003461504c9040e9401d138244030f1050300800b900030303001c001d8446030000c5403503008410407240d852075042e0280e4000c00c010051108505401c40c1c2c221041d5202e8020003808201d0701300c116050100c010700e1101000006040c44120010003440000e458850000f0a202c1000c0802020740301d0741e904d020b01d0300b4210303c0707807808225034900985048a903480c0022464080411403610b040000b410200803640050900c03201d804041420300064a0b40d00c0c02c074003c140d43c6041c1e409101d103444d001000d80690b0758034026180440d04c0030020b043c60307840303800203403000b08052039010030001c2e13642018905144d041032440030b410b00c4820400c0344c01ca40401040000b0b02d00040206260383c5018028905e0340018040d804800e5000004240610708001c200c400003038000911b26070320078543c000540d83d9207560303400e000d05007040b220b081d00c00d1500344540e9041751407001d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 814896951 1250 814895701 814895707
    0x307031202090a1a090f03012c0f010504080405040c1110020c0309090a0501050319110609190b030a110315010c020105040e0f010515092d0909010b091605 68
    0x10224400394014446883d000303006807400084825000800e0413000b510000d50980c1e99800600b070024110328824014001c0e0304142011064243c100454400950400921001d03840382986441c20310303601c0c042284d01c960070311062000b40481e000082080341d200b190204820b100803102690780b00340300c210411154104010245140509400501c0d01482c0c03c01078920746400300000444a002c1558480516a512001031010f401c04000c2c4000540e211201080c11480301e6407440c0c90b0b403600d920602d004070404550682d01d0303220024115500ca139007040c812216602c9289a02c0203070011250400c01600703040f4484400c2d2106402c990040019004c405083c0000e440103446c01180032804038100304040100256060305000303083d004105000010420794501420070074003000280d11302c194010200400c2903203a884070003804030718812000e111400c0c885280300645d0f0026018074a5004540181003092001065010304960b00c0203c920443e942c0303d13a00c074000e02d0340f280f41916000c68010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 814898201 1250 814896951 814896977
    0xb01031803080f0a06090203010f050f1c08090f0301053c0a0903110303070216050603071b0201030b1009031703010b03010e1005040e0309010e12030a080a02070f050d08060102030703 80
    0x3034400d1513404190b5140100303d071913460500c5ca0480e4000d0b8010781c11401c40034014025454802a806808601140d00080f04040080e807591100420340340206411000a1806e0054a400360030f0204007400a008001515006d100040900002a00c80f191015100303452580700c080c0c0c41c1c5014040e1659010903245030b9031440482d000b44038103107064040c013202d4812094040e8041000b1441122103901a1904040c100c40310a446c2d140d94200d1031046106200f084103499120342400b8920b844401c42185005803400144d004200208180e600504295502c4071555000076026089070310a60351000070002842e803640f8140420702a4044c1c0703409c200010005070f81e00181064018201405031174a043d95000001c0483d0022401c0381881e80012401070007a40c0c109000310154036040e50070301d140061014425850b0322408030000c0922030b140b008220340c1e54555050f90801d0b42d02689141c0030f2001c0e41085035842800004a40005a800c40003c200d5480407040d02c0401703a05455035004a900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 814899451 1250 814898201 814898221
    0x1e0c03250927231501050a0318050304061701050f180919062703050406050c0c130e06010b091e0f0907031d1908130e0a0b0103180308 59
    0x8440710311440c080110300b40e01c0c0d005890b8410052103114860180d0b0501c28510603c00e1501c200804030340006000c62000581070341c004040b41c407500c4d4185400550000002020307507c9480554010b09644008680824070326000750002803d0040d000785c00c41e40da83c0c1e65040010f040c150380401034200d61428070040c141030400e00340f039400504030001c1c0d414035206d29031010040314000105680c900c0d218103001100855100c0907003041c25030015110803149145d10090010710481c030a950812500288108003810305111542201a0040c421030304c602c1030b8000000079160240008000303000301c000010715003035034000701e0f04c0d00b800c00f405004c0080807910103100d60500112145070404654500111255610705480c0e1091203d41c0740010403200d48415a0090b0701070381c444a41c00e0b0b109200c009240d48003522420501548080c05030fa8500c0b18000d031540102e595400841203490340c1c803d0041c080b07001e4022010208013a40c00300300d01888915004240304000d14054082450341c7c010400340d9074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 814900701 1250 814899451 814899479
    0x2107060c080c10090303050601080f012715060e09040f02040902120a060e07150c060c0302070f050303040510110315041e0e07080d090e1e0c032509 65
    0xc000c00403203080080315102ca60a01100f07040341d10340389644010800401da0180700300b58125400b0300c1e040c0001d00c0c0a003a07103035030303140107000d10710084804900e490011440c4d0010000e030001020001c0c400380101c1003103000c02040d180608400305107405481959400d0418006210316001100755550544907002d0000500d6650f0090707802202108010b410748204010054078030380302d81d00000d0940344008280303007051142d400c0702c00c0080c0c40d0328400c16010f6010007449280b07600210001409905107009070700a125856008260003152081c4078280040400a10301c1140905e0036200d14014503507030001100c0d4040c00c2510321800c2403011a044007200c00e480303041c41c1d42c00780c00025001c0b01c01480c442502c40d05000c0324501501c4800e13500542d4005d0100c4002400078500419400560301c1c0c0140c4207800d540143c40003150520006040c1c0070f03207070301004552403102c81010218140054407002c2c80c0c0c82118451b80c5542003800c4c0800b00031ba00303908460341c41d03c00c0d40d4402c0164100304055800c19 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 814901951 1250 814900701 814900703
    0x50414010909051510080c093006040b0f130b0406061707030c051e1c0812091b0303030118060902130e0a050f04110102031e04052107060c 61
    0x318040c1c0001c02d00b455944a254004e502d420b5807204c04c8041c200410500051440120f81048119000d100300d652422090f0b550f200d00032202481d4134005807240d034440780c09030380c489041c0270142d0b404a8500d64002c5841401a80036905d1450300da541c00420503044641130f03e803070080d032402c200121701043c040c0401c19003052240c0030105415640f10310031081c40e001c900b412245908421001c0040140c078808180080c0002c0d00e148201c5441c080c00c045103060fa84810301c1c021166509000c80d15419404001e841c1a40720007400c5c0c542809201c10707400f56070f04861102c03103131041d10882d90083c0301d550b9207010300d1003000300214a103030300b4840d410841100394502d00c406551550400f007001c0c4058006030001c80c00e40310b01191a2840c0806200b00510081c1801a034549000144154009696980c0385c1c0503030803000400d000717401040101d1441c0300d4440f0050041d44800c40503520030b1140002002203450840c0c0c035218000e64840c211004c0d000a2a101d5441e40c4070143c00c120301e501440d1810211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 814903201 1250 814901951 814901957
    0x200319060b040b07110d03030b01020f0703020906040923160803070506071218080c0c0d0c0302100c05100b030c10210204030c0603060f0b030f0601120f06180c080705041401 76
    0x2c080440e0110741b10341c850f000d040300402d031510941021940d0401c4801038055010000f41245482c6801040c41c42c20b0180c5010b00942d19410010240701d084444500a0000c190380e00300c0c2c40780c00100c941e850320f41821003c2c034410240c941c0012540341c00401c0d151125041005480c03a030325460b4040d5920b0000da4194192a07032500e0740c58003110301c501c00c000403d601580e031407659060310000c007a0901c242c0034030080c42560f9645080c070103c2d00b89010360050380d5058815003884070b80d18500381d039a081010300090140c8910009484118602d401c00408454140c04492011101c01c08010a0500c00b0881030f0004441562981c0c10001a60031810764018090006142a850340c03500014800c4680003800440d849140c05c220f002c91100d20352000305031b481026400c5003030400d115044400054030041c100b00250700b003102140740300d50000ea004400b0001c02c0040c0c6940320a0085603000440e807654507035240119110740c0750f0245d000720744251400d80d5002d103000d09000281d0248182c1400503410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 814904451 1250 814903201 814903223
    0xb1603090512150a0501060210020918190e0c061215030d08010807080102040f0b0d1d070614130b0a03021314030c0d030e0d06200319060b040b07 64
    0xc103841c2c0034a801110902c440181c01c0da60041c407a0009031000c080e007561a0b4a103410010814a5030105070840c42c000d20030300142e070743e50310340340081c5c02c00e50b010625203202c045507010310456480000814503042d20300203081c403800001c5250b00d611511000303851504030004008149910307509000a0b90b014182e50800000030010402207440c0c900444015404288200010303c0224801c00c113200003000707144e00952606c1d0816404c940c22030514841c45650100110305c2c0b1000d2841c9801c0038050404503d10407601d070443c60f40c01642c03001d0511a0a012451913625500316a0291085402c0c807100c0d01a890300640c904808809164098210034040540c240312a28240c00c241060038001c00350305000f803e43c01502c00402d810300f85145080d91241d0b011580702d500094200d001d200310810304440d00001d0300c0b0b0905111001d803017001e880000d1120750000ea03825030f000707400c051070240520441c40a40ea25590340c0d214202c03507940c0124800b8440500080104c0303071000b03000340405841610302181c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 814905701 1250 814904451 814904459
    0x1e01090b0a03020310140307030b06040912081017060c03131e0c0b0a020d120e010e06220804090b0f1206240a142b06060f0b160309 58
    0x500d4000769089000640c00006002007080d4142c58000a0600b40741c0c1407510382c2045001a51318850f510005043c8030081d400a079030b0307a843d54010503155800c80c03507004120400441c0140003e1086505440c05c02034980b020400f1550000d9056850b00414001c00031a181c00698000640000f0040100c11480030524000100007001c82a01044811a04480001146402d040584041d00b01005084082c4420160030342d00040c05401607010342800380d44c0c0300e00310310f80c10003034107039211411880c0d0300346aa046008480020b210b44510315642c406103862032071001450442809800141141006210900000d403036070340840c0300503c2c01840e4103403007008030010803608104c4c000c05032183c1d00324104011407604000c21840350f00c48503501240e00707000c04100041c503a9066028004220b924845034070110b0f10345402c6107103080450302483c440c210b03018017240400d41303000100b118200d0505000080b2480700d0340100003594070054681c0e003080b464452602c021a40da81d000c0d804c02100c284005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 814906951 1250 814905701 814905719
    0xb04110a030507150305070e010804050f070e0114010212070312060306051302011e0212090303040e010b0c0c010914010e0406050a0605131203090b1309021b010e0c1e0109 75
    0xd002184501c2c040c101d440c0c64210090a07451090a406050504010400140c3c80d03114403070303404040302420004256112418458900b045810381e240b60352080c0080410303103807000c0480904079004203003001501d51078080126200e40703118070028600c5106022071000a4015031003405818445500041e00503629211101503c005540300851541289171000c00d55078800c0088403002442c8441c020348108140000307580d0501f0201503529000c0c0031580c48440d0f0340c144125402400c08401c60603071940c54640180c00c6600002824080c2c2c03203440598103882d401110520204c0d410201c90b041034004080045d10451444030400f68010342d81d9001042581d1814582e0016205940d141c507101c520750700041100008640101d0050410030042c03e001030740c800c0d460803e40b8652900107807141c0001d103401e0381d100084e0308550052070010921441003036132410204070051000009121242400e90074907101c0c03100464060300131002990510704815041c08000000c031043c50000c220039a504250 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 814908201 1250 814906951 814906969
    0x5250f110102120406050604051501030b061303110a0f0803040b07031b051e1b1c06050c0712050a0915020c0a0b090a23011209020303030a0c08090a0f0b0411 69
    0x501c83c0b82c9182000e100a10000340319003a0b2010003074404001c00d040190f06038540810080300241003640b500401d90945c0c451505840411030030117804490140c82c0d20304040206400c0c00c0e954018071000000041c41001e0041660460b680c10001d986024142403001010f030740005802c1e401d0001c8403100c1c84003030009100e61090741d40540017401c6004080003001030b0b8080300e59400791880d407291b800c8054492031620320740d450b104100c880c40f06a1003110b403001e02c0c0d00740740703100604050f00d040100803e481e0b9890040441c90b1080d0503103096400481d4003500c0078010050050001f0b6040c11040c0100c80e0803541d01c0c0310b081e12900485090396141c0d400101640c245030400c810740c0901040040650401610302400f45c406031401ca03100d140c0d03010001068940f4000c03414100184411400c0301c031242c40d4019103043d43c018098903502c1c504200d1682c041c0c80840c5241c00003400346000150145008605c0e616051303448045a400115251030750b81ca41000900195a071440340f405400e000d0b500c030001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 814909451 1250 814908201 814908217
    0xd08040506120a150e0f040611030702030331230304060c120f210209060403030518091b0c0313030c03030e030105010501080c1c0507021005250f110102 67
    0x12210349009618201a0b505154404144c401c00c08800d0090341062a00558031440c1200c00d08541c2c0e40c2e40c200030001d032411070502d51070103000009200e241540400114440c20041402803441a01e0110003094184c01003001c0030181003552110001070402c00310b501020b0000c00f200d120a10322000c0c1c440c1141c0c0598040008101e004034040308101c06144242a200000d0502c40058000110f001d000c42c10440c20700c040e03c0445203e40b0510018542c1621191a80a80b4254449850b031034090440e41c8407682030300c80704404000703a00a41c0ba0400f0101e02c2940401e590320504d080d401c203041010b8219040518043c042404802c030341102c0c0c900e01a0055009401410130b003450b608000e0103140b031105841d4041e904140040c03109980150340d464000080c0c0500c907680b01c2000669400741020351030f40e205040e08013402d00501d264000740c203002d030750001e40b402c00290710748201d0024402003404074100001d40d840e4980d40844d0088280201e841c49c1c60800701c010311502c00301c00e030891b40b014070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 814910701 1250 814909451 814909477
    0xe0d0f02040c2a11060403081e0409060f051305070e06070f06090305031905090304170a020904061505040b0f06030702251d06010c02040209060418050103050d08040c050d08040506 79
    0xc00501c0303000165500c0c001c0c3c00351010307491b180c15034035000300038401d074580c2d0800310300040040404c0344050021078005000040040083c9038642c071211445503500e00c68544954003400c580c00c0c0d07501d00c1e0311915008001130703264404203007054800e110032500000030944080107c00c1d0480d01290641c00b480311198401d40d51140e40e843c0040205a04401c0c040c5605a8039203042c00f0003080c050000111010340c1c0000401c2c3c1c07110310588120a10741800c481d0025048080001800100406504140c0c110120380098159040c2c494042c04126182c0a001c1680031100280c506100d08050008680000300b0b0b1040e116641401028001c0c03844540e030241550fa40400b408210b40200e481460075414207050101046081c031100007000e000c00001d01030f1040e6400604940e4070b0303907401c2c200c500418568900c0e80c8464107180c1410b000b040244005c0e21a8042c170801a401e50744070394001c5100320307844240300403404d05203414021000d09503c0d0071641000100070105055807000701034135401c12105 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 814911951 1250 814910701 814910777
    0x10905130203010e070203031012140f1e010e3a0f0810060807030f0b03102715020309030403080d090c05030d09090519110a0e0d0f02040c 61
    0x74041c1e40b212030300902c1c5c50704640091040c1b040b0001da40346503600b00d0790124440040a031890074044c945034030902c0d0003181d9101c0e61740314100300000072801d100d60702006000300814846250856099801c0c0110094640d00003200803940c41c0352800390b11407612500b20310110400954a242040960401c454001282481304202d004541c401c400940c011403110592034400c1c540751f8080c001c144040e20600505494559900c01c0032001e034050070410100808640200401c600e00100524a07102d5410114203000c80e40d600111281c04403101b42c5a00074151001ca1043ca10440f000b908060000e5000d40405c100000105102c94007600c82c802000d000021300301a50300c5c2070f40c00e006255101500030382040c240c4615040d0070001c034004a61403480701050a980740e0111035200101d80e4081c0f800c0929001c15421140c3c3e450700034041300c2986450780700207403c1103001c00c9a142c0d46150020040d11703904000e0401801c045e003220460003410f040540442c0b075000088802280e00c002003908140d001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 814913201 1250 814911951 814911959
    0x20d09060e150c1c0b03030c07141909090510060f060306090203061c030306051005251106090d0b040b041709030d050c0c09190f090b06040b0112051f090b09011401090513020301 78
    0x2c0010154ac214100d52107803c1c14550841c0540740c401521170061400d6441c8040c5050090520081b15004182d5100f048515110464800c46200b20b0103644002890940045a500a144203c90103400001c066440c4c1044902c182e000c0e500c1129400c404054450340c0009013034039064100410582140c4529496103911040d1134030b092070010011000f403045251100204803400c40080c0d0700340741903c410b50354a140d00b011409107041120700030300c01c0c4912820081403014560000d40180c1c0315050b580381d541c49040110f9a1030150484050380750300204190b420050081009000d1010f119041d00d0582d10940001102001c08907a01c1800c0016503c600c000010b843c45440c01400c8102d00410080071543c0360409001002081540103a546211015690780101c259410801c55140144a03911300340030300c90041d160307842514880a00c0788001082d10450b80c05007420b501c0c2c004d000c270f414030b81c41e04030000703540180403410905104240c400400c050321411500d291200002034013695075454 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 814914451 1250 814913201 814913219
    0x902030114010f200a0b0103060e060f04081912181202070b07200d030e1008041214090a060306081902100806010201020d09060e150c1c0b03030c07 65
    0x9080c180381040501142c06414641211900301c0000c062101c540c030310013000703c540b45003860016000d0100d008400000040141c180c110000e00700910041d1000c903159000200c1c8062000d40e00205040783c05c0c040c941526035030382480342a461092030058090550307030b07034008101c481400d25500c407030000d2012041407022124200c8039a0138a07200a0645510f0082c11025071700840500410041e0085040b44c140288014a03458a64004008454103599031501820040303038001c040d0b01400d004494008144d00903400303c4d114540203030b040d140c10101c402d01281e0442d46c1c122030081402042c007100645840b484803500c05032000c0e0f01d00041042c00d18008620b46006507000d00b00740503c1151800050b2124007505014650070704100c0303019212400141d01a024000c2038514a1346003024540902c022a044040c0309d028036000d40c1d0124041c501002e0607481c0c201c81114881c501040081c0199052003410a0301c0310083d14005035100765080080d0460741f240e0441082c583c4406030074805414 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 814915701 1250 814914451 814914479
    0x170919150f050901091a070b010b0705010c080c09040c02070312050703080c1603110a0206190806030c1c08190314090c180403050903070e180c21030c030409020301 72
    0x721401c149007091900c030700082c5080c3c0e2078006c0c400100c41c141c0c180c58014500400341d40010758040b20406666841f120365030301941004100761825820181c00c04600b5014041c141d0180e64800f0b04949405003400c00d0001070405103000c40700f148254140000801c80c03100008402c03021540d140383c0d55a440703041c002c01c1160080c1c425104800c2c00c0151000a04060036010b5000d136041c10106414030074000960b00f8146100806508050005507407102656443c04042010143d0780783e45115031030341d1003030568071640940340c4d070741080c0d20300007108541c0c4e4006c1235400c40e07501c194002441c3c44150040c2c140c00217030491740e10f0003007a1189000b00003030b441a840594840c03d0f401c02000d103d440000000c1b800604040c08000320030a46011509161240c021a004a640542103510445d59650074008d501401c840000254141038140f007000b6402081c00212800d0040c00d2441c920000340c040c80c007901d0419190700c41880200312851901d40d045c40075000804403454016101d6250411441140c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 814916951 1250 814915701 814915727
    0x606010207080c09160513030302031312240207061a010f0c0f0b06150c06060102060a1e020a051210080d05120a0c1101020c0304090f050417091915 65
    0x7400454564041c2c2d100d4003130090307105d00d682404112101070194142c41c42d1042103800307012140c031444080181034000004061450b000c48035440c001c2d50b110408d40d143d45d0481c070000d0000644800342c040d00000d0718100e03440c202141d80c0c014588070136541d800c001c035104101d1804044000408001441d03810455009181c0510304020303407250b02543d40c1070540821450010a20100324001c02c8107500c0d002048400c91318002030b007650301e200c8a180145e441350700311502401031090200080301040035024038031482150040002096500140850103508880030745000c201c0706109070f181c280c102c180780a018840349030044400d90304202006061a501051500c1440001c000c1c00c0c040075400c6140c00d82c0705001e0140003c0e14030442c0011500103441720f495160340d41c008500e2015900c40400188200d401d407a0042003210000002202a11411900505000d22a1032080c04c4452188020094640b0041000406081f2030245072540105904109400000b6100356454682c005c41965000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 814918201 1250 814916951 814916953
    0x2a131413030c080d061214010e030a020a0201080a0b0a0f06020c0405040803040f030c080a091e0605031f030b07082d010b0705070b0c01091b06020604060e0f0f060601020708 76
    0x580100e4078041c022500d2228001c001c440001400d4040507400d9001002904407803a6580c0b051680b414011a030250090021202c0d52821042c0500ca071800000c4540a46590300036000d042d0654006440300c2c00010070403001d139a02c038a2685219642e06010f40050090089160812810492300030702c0c10610600d200d008501c1c14092002240c619015281c2c07080d80080541c000c9081840e0440310808c40f4040204000c2d00882c01319803050b004030f00803017034803480c1441c0100900c0f01c0e0040c10307482d0030360711406020450800103c0c0c0f83c1000c5100044030300f905165546c00c0a5a2980c1e004000d550031605c043c006490401884807145100b00c003080011001c0d8503141006800220025607080c06208079a1480c2d00000c980081000c02d21054005040c10352195841d500c19484c414040d051041c021190720800d29880c90802e0380381703005a401e96100b50300502080c0c1c0e40e07030382d0540100601c0d82140160f128002d06c01d5004041000f1904400903010090521801d00e0b0002919000c84d45e000203c075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 814919451 1250 814918201 814918231
    0xe160f02010506090a0914060f0610050304170c0a05030c0307060f020c070501030f0e03130e0106110d03021b060a0c1409090c0f040302180103050d08092a1314 70
    0x20561360a0109600083c440d40000b44180003407901017280c4000c680e80559034080d8504122000740360781c0c03903075100348402e64a80c20842d50068003100c0a20003190000c0584e04a0200580d0031003012002e0480f41d210302088807000c803040e4640b02c0c51900320518469842d840014000e0801c0464050b9030710180c3e031020b041d410640c0400a6035103c070360707a0054604041c0c0d6078a150007100a5a0000b60140000300305581d9608502c150001946013140104140e205c103c000004107944546d459004000307038130020b02090307043c003507040f400303980300d03406a400c0c54000e04410f4400803800e014160181e82c0301c19000076010101e140150601c50005180c410400e420302c0800c03082c1e110f912031554461038228200396613100074220184039010b59040650050142d136940000031200d0f070030450680c6e000304200d40c03641d0f89402c000c81d000b110848044041e504004090350744d0340d16080c00d54201021040c0e030903480d481d0708404196505410198180040d40741d03411504c026040f0006a03402022150795516 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 814920701 1250 814919451 814919461
    0x90709020711150d09060b0a1d040618200f1203042615010e0f04110d020a0312050702042328060b0a021c02070603150e160f020105 58
    0x1c2c052086014003842000c0d0301407092224103c1d0360b6019040340c20004224a0300b080d0004044988016000e5000d4031404115224020600b044242030101000300b0f0341c0e02c544e11b1700007030843c0d480341041e600c200e20100400118201c1d09027014414a40c2d80460003860b02080007580044d4240103030094a00c1e414091071040c0201c116400d459040002c4000401d9005429804c00920f12070550b1a0045403003808601ca41a05001d040b2030b0104c0585000f5250310803804810300d002d5030b0044c1001076503007181d07000b03084c002071000741240014011703042580d4a07121f89058a982210420000300001015011403901d80720300c418000341b03461000c1d45015100c0004082503030250460403c4502300800d880c0119082140b40000f60240c1401c2c440c50f83c1c0c480c1182c07165000200c400300940200043c918159036071401e15001c0840314bc0c000c2180d03a207040001c0e001085450782c280d0000c14891400b00e0b41c1101c0e9807005004810382c24205011142e900401049540034011030030440e414902440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 814921951 1250 814920701 814920713
    0x90601051806130f0515031e0a0212011e08061e1b07030504031403030f04060b0a0302370602060601030b0a08150402120109020102151308120907090207 67
    0x60414056650755989070040000086150081c1103219103c2030300540c0210b025056000300c0c80c1183c1080e110302c09044036080403003005000c2101d10050200c012a079108251550341e40840d00511310850050ad0200e101415000b06c5100360071041d03070400d00003081d1404102e0020303c00003e0001744050700490070725240e1017100148d1140c01d00b40c8901c2d501c01080c2d4800031580456241040c50030f01d55920150f52802130410742051106075501c03aa40c15200349459408011a032041d080e07440b8040c116545ca80d1140c00800c00d40c5a00e940108034641c01100580b00c41885c522004040c648019100740c0c03034068080c401c0d0300001900b6003600000b00805c002d0f80c00148c087c0e0007050908000c26202580310100702e03441c0203644003618501c201c800050380d0142c0340e01a14003403030007900c000504c00309078201a03090305d10310b00000740145c1c0020747c8090750f0808415501c0e040300890b1158104000f81d0784540d011500051220b134204048403003070100c0001c2c104112801484118401d5041c07000c1c5844003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 814923201 1250 814921951 814921957
    0x1009090c0504090c0b0a020c03060601030204080607200106030c03060e010204080703080a031b03020d06080304290d02030c0d060503150a0207051005090c0301150e042d2009060105 79
    0x42c0a140c070388840808024002d030851020344482c040e003a854a82c120002583c030380200d20031901074041c9001080c000c0d40709000301e5040c0d079807101c020600750300c80c48001c484051005002c80d0079080c001e00600c40c40721080c081c04000303600a000d40c60200c2c0c11420850300301c9404003484192a841004100505040491102d040340e41010000b80c881d240030009070081d0102d40c00070003500804404480c2540e4043d4050400c484d90303110104032940d00c40c07205554a20450180414841c0426403202008106880c10040078030744440c890706220b20304440b00241d810a0307031500311210f00801c81c505070f00342c640318150007040d0440c0140741620692450000e241c201818048490b500001e510090104c100440e110754610181700700282e29001c40a075456100c0d100f08540301e5400c020704c040b03c0c8900c100c99142625041500d265841d1140d94800ca40c4080080182d040e407810020070304010210a581144102d024034500c0141a01200c0e0a030880d101d801d01c114810042c100511210766448070039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 814924451 1250 814923201 814923209
    0x3f030b0102161224050709061e051e0c010212040b090a03091406160503190e0a142206090606020109050c06090f0d050d020c010f0c080304060207060f051009090c 71
    0x190020398807501c64500c00541c09a1180044604010903c20202e501c540c0c507c084408668030120300007803104103440c8000c100d40e01003002660500c0400c0056400010070201e413540c40340950700d4040341c4004a030aa810003e90064645240c00070081070101e400c00a6503c0b05204019080c00e89465402500c0045a8015a4007001101110b4540b540b03079141200d080c405080d41c5040802240d14196035258408003410b62417407003800514030035500908991002800042260340c40a0600140c20701d603860743c0e004180e1100e618031000d5501c0e48444045a0340d0b541c2c800c0040748850402d40c0780e100b5941d4642c411021a8034041b80d81021032404680c054041500b201d071103a40c0e054580c00580d07081c1c00c1c50380e0750341c0c00341d03280ea00320080110011350550b004042d6020380d025445c0800043d10fa0141c030002440c0800d141c0318005000a4080004641c0144940001070401086485600880d40d81c8035040a8035036449050264034031102074420000c090015040c030280c04076603109060407042d845 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 814925701 1250 814924451 814924463
    0x7090506040902030a0b1b13120206040b0a0903060b01080621210c070e04020310021c0203040312050609071403060409061b0f05073f030b01021612 65
    0x1080d45591180c100c41d0203941c0040481d170110302d0508000d812100140c407150051000b04c44800440c00f4040180c2d0b441001c02034041d0a901e103484000e05198081c02412030340300c0c10400010480078001e01c0a004a0794250303461071401f070300b1460098104c4603469210303070602c4070324400c1059564a002c091040300c0903481c48040d0018040c1070081c5060488002c070792040703030000000041c075246d80010f040c183d14560122400596a5105007502c00e006840c040e4040e00142c0790b030700c1080e540d50010001a10941c0070b80105030062070b0b0038070890700240d80840001749600000241203001d40940e603044030741103c00b26902e042004026041440750701000100e100040000703022503540d944580440740d0004028041030040c540c002c090714904c0203c4202084840c94101e180383d100d00242d40d805948903c030811546a0300c0d01804d1004144000c0040b01420089900d0303401e5080c0c5c0c2544030740b2800b910003044894181001a0a2a500f140d080ca4424641c1c40c04209443c0b40708070260006070010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 814926951 1250 814925701 814925711
    0x20d050d080f010e220503032d0c12130f0b0702010e060105100c0203071e150e0607082a0d020f0f1e1e06060f0105030907051e130c200709 61
    0x11203170812139031581c80c0c0a407190002100700b01c00c1c4071000980c14010080791400810700d4001c1040481c8601060b550050340103001d0101d8142542c9005a0ba60400064400c0d11403000d11507131034290500c2040b4044071500c40c11000d010105170240101360040340980050709056050a000c11524102d008940d001c01031880c1c82982503440501240340545000c0701c0310032541002c14200c1c80100700318400d008440401580c0c02030a41c0c412001440a8440184074610740b00c12a1283c28040d0070203c000d40c6200e42c650f0449100c05d0b800e0b0100741540da0707180c1c050407450341119806410000810b404150f241c00c03a41c0c940d0070103500492503582c4c4140303104401d001c14007001c591918241d440e280c5401000610a0000c1100c0300004080e417091108441c0c0384080400603004491500003078400190720f600c40c0d00103002a18000040c41c442801c1002072903a07054040c80007800082c107080300045080d5075031115008480c0e10402100d8100084100c02d26912070360760760241d44105c2481141c9034180d480c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 814928057 1106 814926951 814926991
    0xa0225081020160201030504020604091d0601090e0303011a0f0c0f3304030e1302070506010501050306130b190602030316090b04060503060d020d050d080f010e 70
    0x3060801d1503c2c0d0300d6401500602005802207a006106000c0400c880d0854410301d1072440600080b03032082654042100e06081040c1c000030051030620071000181e200000403241110a0306281e400001302c181e00307108a41c090980340249286000030840c1d000800041c4404078410300009850b616078032400c1d40b500440010081008d5400c0c4152000603c0f0406401694014000e04003070b4000c14101001a0ba4840207076000000306501080020a00c00c04026007405454203013005803079414510002042d000751900102c2800340c660b48042d640307454159a01a00807030301105410f500b9100c0780041c3d280d42048032040b2070a882d007080740c10020700c10642e100880d11280405031a00341410400c1b0f40b6a400100060b40044505a45074016220980c5692400f8054400703040d203644480d50003803084001030700c072a402544010050200000d0311880d03076005115000102d1441d440 = true := by decide +kernel

theorem cover : BRFrame.Cov 814748201 814928057 := by
  have h0 := BRFrame.cov_init 814748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 814748201 ≤ n) (h2 : n < 814928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
