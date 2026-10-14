-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0674
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:04:22.522923+00:00
-- url     : https://prove2.me/submissions/0cbe6732-a335-48fe-9d26-b22571f9747d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 121043165 ≤ n < 121223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 121044415 1250 121043165 121043191
    0x303010f08010b042d0e010f0b010305071706061605070e190204060e04090807060903030c0306060908070501050705070b04060e040606051c02031504050408030103113c18 75
    0x105143c50b2901608500c1170303100c04603e0070b0121180c00a5003040046880c409800d8030382c040c0001c820b40030702c60400b40840112000c03402d952070318001402c03200b00400b040300307004035091900310300c0c5044e03002030341d0186013901d60307507034030b40b84804802c400305001200140248507400c030100d291003092450b5800349080c0f110050140d0040d030203e0040c0c2c042da00800c0e0020710801c4d111002031a141d0010f4100b613001d1140ca40c500482d0380c55034800d03075000c3c100c180c0100f03840f240c2800b80d26906110f860300400d214a80007a04505244016841c0d44892068504110010543c0c506100e000c0c01a14010002c400d11980c0d150364440c405880084044411803007945803540c0000e09074010800c0f6882e001e941c00c4541602803800091400940000d061001300440c0c1c031420304450b844da40f048600450041c44400e0302c075851868000c1c072112403860741c02d001302411f03170040c1880340040059969415024070f43c100681c01c03100342c54042901707a49100380d04c07030a17036085203810740d40380600c450080e81d542d1808 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 121045665 1250 121044415 121044431
    0x7052407050115060801180c050c010c020105101208120403020c0a0602160f120210050408010603080c010c0221180a03030f1101021306030e10020f030106090501080f060904020d050303010f0801 85
    0x1d4802150900c940c101f0315080c14408840f05020341c0c06074130200420700b000b500b0201220361042c210b940030890200503039035840a01c00b000c622606110010280380c00b5045402c480c0382c1d511046800344548420565a00c0c4022230200343c0240901c2c0b84c5080013904801c00c8990b070300c1c0025a21581e010318681c2480010304007241000a200d030107400d481907031f02043e2a0304504c1d03007801040c050010011042040c01c0c0b0012808080a00401740254007903240b01c1e41310030440100c07070708460704003c80e5400d55000c0e110407103100c1d81080e842220021030f10819911415006000181c101080000a43c4058000004800c2541000b440100401a41d4562180a0068400d64200e2003100c3c2095180ea2001c0304c20401644260440a060206e007815140e055035070508040030703070b0807540d5801010381c4044014000c40394000021030041c9000d10706034038141440c1c59101082d100141c2150b01078010a0300040640d152460034407001940241220307641e40e03541c80c01204503020b07805209040d50828040d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 121046915 1250 121045665 121045667
    0xd0515070503040c03080a0201090b0a0c0908010213050d0f12030e010f11030c0a1209140622060b0409050d18080610060e0d0f1b050603090705240705011506 69
    0x1e80784907583c841160111326040d5260840140c0002d541c89045640301c074030740800a080c400d401400b4074400070700400c103501c07103d070301811102c00b03030b00f2050b821380c410b110801e68100300e04000070032101c0c10f40d0018050881c42c202284040389050014012240070100e205815034160f03c24911000103034020003070783d079210031403c050b1000403c04104403103060010a1030a10b03102e000b00386e044420b0416003881d14a100c07520080e10610002500c402410000001ca40745003802050341c00440100706400d40c6041d54181d4046511001020304419030791100050107445940c04101ca083e00181110850008044000c03c061071201002d10082c2d0000d800180300ca0780010440d004e07a481c008107422890400d102200c0000c0e00076444c903804003032401c015001c201c1c4a040100442d00421002c20145000c2900c000c4c8200c055020b240110420070400c10303070003404500d0300d06450017126520303504401c8100441c490480c00c0504050744a0005865003040015440040da0401d580c451b0301c40182c0d9114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 121048165 1250 121046915 121046917
    0xc080411120604150e06040803010509010f0b040902071707210e0114031f06170615070b04022709010b0409020108071110090b06010801170a030c080403020d05150705 73
    0x401e100300e03070081c03003c900000c00c1140c21610800101c00005000310b5403800c1246004000e0f10261041c0100100500c081c0c01c0c602001c1d80541003805426180c68a84074043e8a1071150b8428400e905501141400401045440c1219621601d62105445400500b000c8216850502c000c106480700070b010400258007500345041c00aa05864403403890300129a400030340d5000505010942703695a00206043d41140741d214003505050303413203500020041c800741c000d4100241010b03201d10307840c0040c0c01c074081042c0c0c100d446156004112118a031500e1012071501c40c0f074601d03081000718003441c8030b40d104180b00040c944907084900090010100600070f02c41150700031500607000a800c1c100141c42c2c60301500d540b0b101315601e502112280b04114404c40300721202050308440303000c0c100040c00742e03541c0c1c011059405081200780c94000c480c3c02040013581d0f40c52288004040c0300560030b584007441181400c0c3d034000c6070080d00884e0350250301d10340b03a03403901c2d6801ca0020b81c1200f03200118002e6031240b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 121049415 1250 121048165 121048189
    0x10c020c01020d05070204022107022b0c050c1003090c050904031707050c0307141c020615060705010e150f09070504020f07020d03030c0909020f0d0507120c080411 72
    0x30b0081d03d0701c40d09800040310554840c481c142d8001707400b0841e14000800c43d50104050710000f51840100b41002003000b414280c0140c0b0464501c101d0301800912544080c805208564807410b04000f03402031480e01904119904543c2544035510080344005580c06401405502d8030511010000715142c1d02000080103041c3e0b40503001502004180d0400b40c005030000703070440708034142141401e9010b40c0035461907000d140c007160031290311000c4110f142010441841419a501c1c80d09881421405000f90b6450b4001d00c0e4092620660101040c0d54440f2000c0752440790300b020090121481c03d0201940d00c442820920100e5070361100001c64040180a06a0007007840d04007810007103160070b08200181d00000c8554042c2c50041110a005998070340d51809a0b6119490102e074911140d5070181400209a00042200e4010050031100702c86080859542c184100800192030301c81c0502180d040500150303442c400c600c1c7c281e02000441e088039000d44a144034000810721034280c1d00070b10201310044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 121050665 1250 121049415 121049417
    0xb031f0c090b0f07020604032009060102060402010e130917030106111c08190504110102060601020f0312040f050d030b0906010e01020607031a0303040603092a120602072003010c020c01 81
    0x30b100403144a4600f00007456803500007048503091071380f0b075100d140340c80f620012812500505419070b0443da007080302c000ca6024600340050102440c3c80d40001c0c1810341d0900f00c0e24460701c0c42d42c94800029285078407045030302c0e400441c400ea510b104c00000002950084c0690400300310035203022441294000380da9201001121000c2c650300070707182e0054a11034009020030a45e581d1035000000303a180c45201d82c2d442203005680186030001001d0019041000161085c1d04541102004c81e00c2b441000086803035a050751020301a030f81d0740700c0c2440341000900400091090148183d1206102e525400940540070100d030000b41d50f032207031001561400751100d4500d0151704a4000111124044d81c041845130203068030385070810180380d00080c1141d101d80c014502095840c10100e0900c642c1c51603030200125189400041e610003040404000000b0381304009400e6007140821081150715015196030940c00a01e0003290b43e450445aa600341c0401003450203907281c14510301a82e84001000c50b41c031081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 121051915 1250 121050665 121050667
    0x70305031209071526130206030a090807031d0109050109140a15030f050a022505010e01050114010e03010c1b03091706100b07170a030b031f0c090b 65
    0x140110a018000740106400e96a014458000600c0e4000390181d400390070f1550390b1500000301a9841008001c1078041d0840e120740d000301040440c0d4403a01020284640444131680c580d44d509042a001c0c101c11107009200e520082288010141c00c265240140140c8210380d682d00501c48004481b4034510748291400518003010810002d005058030240400016042c4c095039915420001109481e1000c01c0c00040d0b9909461082024544605504509001019480c04d02e29003418040500550340440b088541000741408000d02588000c01c0c4a220b90000d1003d90303035a2211041c6100c003600c2050200b4192902d0540500e810700c5121160306003034031610b08401820440104604607854100d0511928840100d80c1103208000c901d4401c603c2d00040c00c192900c40b400d50900c401940c000da110303e00034040c51002980d500015410340540d0310460b5107511807001c1c04c4020746580e00010b501401411100e6100d2200841c0c0710400c2a10044240048070100400300c3c0d0104684c400ca0080d400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 121053165 1250 121051915 121051927
    0x12050a0206070501150e1608010803040311060d0614040c050306030a031b060905071e0b070807030e0d030201050411101d0a030b09030d140405031c02042d0807030503 73
    0x28008028180c403e0042000145035800e2015103101c0910340d40144015130501e0041090000045c41c0c00d200074466490503594952410354181d17a00d01860000900056441100c10490789850301135990070744440d00240850360703940100048015520003021300980c280f0041c06202d40c051800c5034007802018000f8414280c49171800c892124540c01c0d001c0d0400f000310718140104800d0b010b00307511903004401400c40985040a4060020414440284000c0464070200f100c10b1019040c0c0700e0380c0f0f0700030198a65039110303850700711484130701401001c0c1c0c030100d1661488107045e4154849885144900c0c0007400d16075122081200051410b03100c3c50000d4038078101d040d1a10300401c51002903c5010b000344081507100d9550915081d01141c807200d0340d910200c1c0008031082e0361b01901a1000c2d1000381140340e401c01d62a030640f00e1040e1403c03501030341b80d04141030300b00f05105c2c0d048030700030072003030700d602e20b041c2c4c0303000fa00c5210a0004c00031204110080c17130010681c5138005c102c55040fa54031100452800b9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 121054415 1250 121053165 121053169
    0x30606050a1b05010209030d08010518010e0417040f15090905010b0403021302070209090a0b010f060e01390204060504060806061207091802041a01120b0d021003050103050712050a02 80
    0x4800b0020449465400740030a01054a08010211034280b03140c03550555581030105000018960059021a440c01e0701d004000c00c40702c0302e103c01c2d0019084110070a40700e42420700f820b9a84120b0788004a8548030728000680401041c2807901600001c0c0da5450107980d4039848481131710401e01506000000c2040108010702d4000c5a060390360f080000050308200326500001d10300c980c07c0f034171110035411989120040010b0304040e5405016002440c004003400c0c4140144001c0650303011078140400b802d0a44240c10202e40c0d000c000c1000c03103024030780103c3e00030099130782040380354412030182d82407500c0030690740b034540100400c0c1c0b00018000c0c813240d5138050400c0314080300068035600a0154000100e10b484680c010b02c0703614049880700788076402540c8184001c03a01003580d242d405040c040c0c0c01140980c3e00016081d02c0c01803421010501454060004501e01c4080500039403228507081f090300301d2a050f8020324102c0f8010400c0d150040e41e15444212040301c001c100031b14a4005888220040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 121055665 1250 121054415 121054457
    0x9020f0105070512030f01050a09090b01090c0203070f03050a110a0b0a0c180b0316050306010c02010e0111030c0706031503080403020d0c120b040b06010e03060109050a200703030606050a 82
    0x240d0f0081c01120810181c48100c04100c3e80b0a80300d240350524110010300c041e00780359610300010600c80b0000c02940c43c407925030480405040c014408559100c08554003114400c00c151041c1640065001440100500d4040c003594800d020300008245115400c0c8200c02011030050841a003010b0090034079500c20042c1c100900c08960030764140200c1001081498000c190340c10080c1c28980c03441c40d42c1e400e040c03010b0b6019007034540384002082030410420909036403001811480960a00300b030301d01c4100f4000141e91190010b0554902480042841c0c46544070008994040f540161410004417161060400c80100340e4040a0710011302040104014204042810f610070b00406401d444251102d40d41043c1140001d41502c8072011a0240424008803520b229041402400c2c841c01030840e100c0403a40710501445003847e515a181c0000d409220036030842140394650317400392040e0f8400d032400c0d06055080f014081d00068035000f80411041c1c00b50044900c80100c5464081689408400300740b11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 121056915 1250 121055665 121055677
    0x20709020313080703020703150e0a0b18030a1d0108011a070302030d060801020306010905060406020c060306040e011103071722020a030c0f0302030f0111030f07020a020307030b01060807020109020f0105 89
    0x3141102d07000c03080200d600e0001a0000030301c00e5014041062a5040904903d0300307501c5404071003454080e00c050034801c0000c0310018560301c5402c96505075281190f5440e0300364000e070011494000090042075a590045030100300300400300c09030194103510001118141000d0142c3d005131244000040c0d103807403042000d0304490748a8411240b03044081d000c680150707000342d882407a0030380d000320621206680102641d009010103031501802c00b450440002d548496000515000d5100040481c3c030130345942e005004107010310f80c002c1c018101040c000810907407044460200085200e05011031000034540010301039039003200780c0e40e034a600c402c649102c0d44d08110801c80c0e000032188000000280b0000c1284000c0c07280919034004a40785005142c202030b9416040c44803070f45000300f003007852400d50b005d07641c02c80c074582610744240d40c0c2c0c10030991070a20118001307541840f03030413400810810910507850507140c21340e40d480c1951b22603030303400d909030b80004200941c0a99420303100c0c0e002c3d503c240301030301e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 121058165 1250 121056915 121056931
    0xf060408160f080f0c010c0f0207051e03121c0204081f0e070e0106030c02010501032a0e0a1a03010b03060f0c041205030417031e090409050f100501050a05010207090203 74
    0x20100c1803950383d5000650061102c2d11190b0008185910982001e100341c4083e2201410241900b01c0311040094407880c0038000c0c5071180880c080c0b60390182c415007110031940c20020341215070030010a4401c54a07a00484c0313495401904048121024440a00a480450700400020705180b0081090054000b400e060082c0106135a101c0c401d140800820104c0d00030402c1c402815841e5050507001000c1d60a69040c4006581c100401080001d00b10301c1541e0380200f04107102c4c4101841940428602d540a9022000360840c49003805200b04540c1d014481c104003910b407055a428540c014903080e1404200c046616810090014524900300c00400fa400700080c0725582c5400d40b1004035903442c403003184081d1000d47c00480c0910060000d05040150611810001c4d8105920b44111043d402035250030082c042c0c0e400326071141c09807141c1d0400a0b44940c00000e4400e4030011140043e91001080303080700c04581400d0000840707082448410090b5041030b03026103002d030300708070105000c1d502c0600181 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 121059415 1250 121058165 121058183
    0x60d05060c160f03090326041406090603010303090e130312050a0e150405060a0e060c0a051201120203010c09051804051501061701080d1b030e040f0b030f06040816 72
    0x5000310f001800700ca00c6a107488481d542141020608000121000203050422141050501007100c1c165012541d00314181c0d403641c0510030200e40c190091882590b005580130002100700354210341110180d4078458035620350340d540c0c0700c0d540403010030803030003d40462200703500301c0b6003051103070003590784006004800300d00301540d15102071500d0307041c6129856804544007403100f0807d052202540260700c0450a10a040c800740c40d894840501500312100000c0000d54111018055400d40741484105810b51555680d2101c1a0300c0811175154106d120b94030305240d0f40f2a082c000d103541c0042d244007a08018024600307a426450501c0d01800540c1e142c0302c2d0030710044601468a141a01800b06591107a40c6110010031f8681c81501c1a0001c0415400111442004541c04103c203000300120280340d6031a410303681004d80f1127480c1000d840d500b00782003800c0d038001141e4640100000300c0007a404c07248490b000b41101c03038072400203a030000c19020040084600900c032022082600301d004564030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 121060665 1250 121059415 121059457
    0x1b0803060f0303030109061a03070f0c050f030301170d14090d050703080d15060305060d02010323010308130608060f04020c120a0914060702010c030f03020408030d050f060d05060c 79
    0x2e407854100340d00142e50039403201410f000740ca0301d51082d0fa03002040700b8842400c5040c2904040e10000340a00384c40c0801c83e45a2405041c03103810880304110464002c10340c0da907961101c00c110395098800409420910901c0700804d500d45c1301e104040b0301c20058948050900703100c00101700030040011003d5a20340310f140c0c004000310701000010143e030610750400040303e2000d451240b080c400190b0000c4189483e20041048a07100c81004000e1150709103030020368021080c01c078249014443c107030141959640d01c004401c1242c3c160082000603021482807a1460b03803000100c540d414203e84264000d80811219511410140c0190007080e001d082a5003403280c400108660f81c1c1c01c0484020700158488000700500c90b05a05070aa102000750707511480e003045070f00003030130f0111600c4008040104800380d483e4003e100ba41620301030101001502d503140c0404200002902c4d090721495a160200004282149880e1441c6211150302c4000b0702401d0b80d8203820440039401183c01c0140700b06400d00d44c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 121061915 1250 121060665 121060669
    0xe121c39030e09090303040b0408040e040b07030e0304050604180905060705070b0f0c031503070f0902040e01050102030c0d120b091905150102071a0c0f0f0105071b0803060f 76
    0x5856803488555100590303184090400500380742c641e01400b0700800e260020f1003034020b000300881e030b03009800a05280076a00c43e031404081c540305607446805292442d4042c042081441c4080c43c0c06205265000e0085800350600c0319120312982c030a5030f034401c10400c82005545940c02400380340f20544003000603c1300003615002d00f083c108031010310020f0000960340741000024000945c000d03c3c442041269450010780c842c04911028080e0002c0b503110325401c0400b41d070100034040140c820305403c0e050944c0c2e19840840650002d0141c10a500c804000225140d44000190b50480000d50010b150309540500280c0e11440031129141e00c094a862a114907528bd242e442c9020b4007a880b01150204039050a280c11148040c00c098401100051900f280340c0c1c0c001000d2040d01c2700c420719508100a203808030700040c0300d10348481c0c101d80140c0c0c0302d140010001040c80250540044001c0c00542e1701d268003156024210614651301d01c2140c00a800400c5407003000d598441c4020704a80451540000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 121063165 1250 121061915 121061987
    0x6150a0303181d040507060f0905040203060a0317071e0209070c05030d020313060b041104090e010221070206011a0403120c02040908090f0a120f02130501060e121c 72
    0x101c1c490f031580d1608203100400070100b1076a00100820319242c40c4090b040343e401811568244141403149070040082503641d03031180d07a000c0046500030b01c40c0718110740055039021141c103c1402910000c902d084a81c0000008d502444803440d80100202115900e48400f5180c02040c0305050f290b604c1f06200c42e507107003100da10046002c0c94400079020a10300380d0f89401c40c140c0788050300c1940940d007880303d01c2e080e2000035016141514071918000c54505811b003c41e50090203802e07208540184030196250b103607542411124010403149d801d8484582e03c4240d00030059100402c640b03001c10013007208001240c4140136aa0f580c02840c0b034240d00d1805c0759000a0180c40f9007040c10b80f0289000210b044e1036103401e10103101d0044041d00e405022501e0310b600703040c051150341c00152040702a40e044204543d00e40302c410300b503c0034000c81004a56140c07040103154014560b103a90044c07003640c0031b0003070714000081c0d0030314100f6603500380c2650320603c460125140e0b01e011806010a01d42d031a81222076060140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 121064415 1250 121063165 121063199
    0x5040312091701150320030307080d0510060507030305060a0312080106030c0e010e0405100b19020d1b020d080904020a080a050c2503050f0301080604030206150a030318 74
    0x260762880c0c0141006504200e2a1940c480d4803540c1c0e00d40092544201420440e100c122030300700c5240074445a211035440000940754a0f1540c4c180000142030003080102c401401449041e40020009581e600c2215400d206841c025075011910500c82040024465005954010320103000c0354801c65484c0d94502486c07400c0100040483c800c000140b200592500c16035054074114600b01950f282d840c0700180c90384140da140c49001e030740ca40e000101c416420109000081012440b103a0382c2c5c1c1074042000b050700d80a5000100180039660305080d500d8840e00000326100300c40c42c4071700900c40d941d0307080150301c0283d4803007107a4160041c042c0c1c002e0b90365984041c3c4a80744003521156070920340328211808440c40200b8000904a0905c0700200b95013110901590210b4100711400001c2d500341001c0e0381600900d00c2001d42a0301c0040045410000803038400e008507ca03400311105500c400c142441080c0007640e0a030740000f1516001c0021070b02c1000201e41c1c4110503465001c0807038a5a40b10100c0310114 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 121065665 1250 121064415 121064417
    0x3080c0c040c020705062a032124040213030602130816031a1003020406140906040e0309040209060c030403050d140a080105040b27070311040302091605040312 70
    0x1100300100d141000c1c0110804550184040d0090a042000003503440c0038051200b441001e05003100005004160301e04101c001c03402d41225128440810200c0505801814446919518038003040084da1200c5071200c600d000b0700b402c0d00362140c10b041408004c0d0010600d40054480c08880003011507804d1000341117940b1034820a10411703061040d03007482d10264881c149c082d01d040207410004110740309942948090058403e400c9c2d41c030381110701d651140382c030381001e5030152903c1d000040501002402201d181c074243c40e24001c503941c0204110440d05e000c800f030700f4147c00800246009281c2a07004180741d01005040b2807c0441000d815482d40d0400c0c0c104840e40e03402510092003d50f00000c0d0344400750451059245001c54411000b014400103204680c040c9840307000d02440c50b44c40089030909001c0650b0344d10070400c0d030b042c4405202003065680d1400309281000d6100c01845e43e5048506a82c0c01a01d03040300c64540500d06107828980200c941c0810000784000310001c0d10b4010810803040345 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 121066915 1250 121065665 121065673
    0x2e0b071a01030303020c071a070813080f07030c09020c0c060a180801020714060c07030813150515030a03080627090102040503060708070e0d02122e050105030601030b09010603080c 79
    0x10f01030040c1c42d087d00382d001800e84580840244511191a108a40310580d0181000e81c075100145d00b20028501140c1007070700e26010744043c1e000010400613950f01100d002e40c4242034040d5031000031004a114022200507250813296105103607080002c01130060312a14941b081407641d0300101d2000c4407881d82c00c802c8450f500004c00710207000741c03030000c14440380700340028000c5420032202030b00b220321444400a041c410041d000403240c4021543d41030300e10350051400e4100801d1044260000e100c1203403e1141d4900c8180f0382d0b0000c8c1800241c0c8800c0f150b0503142c2440039101d40781040303003800100c0603540d00c01c42003035411640d4045110030240965202400980c0313a504010400d4107180c402081d0008011035581005a415070007085550130080940b032420b40030303400d4000f00d0184014108010101d01c40c4910040707504d0400341e0910a5041c514860001040c600d051240680340e080c8120f6030315030b0000d001031000c0740714011650740052044000107503403552039a409074a604034190355508c80d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 121068165 1250 121066915 121066927
    0x3120403060501140604090b01020114130c08030f071509020a0611060c13060302030406090b16080105030d0f050c0307020d030801060e0427020105040801090b2e0b071a0103030302 79
    0x1185002d0305024015601510310786441c2c0b200840d029001354414600620f880d800340011590007984444456a14005200006d241c0b628424420303420581c41154518404800024060070110a840e14084c0503103510b0300e0000c0d80c0e11409815800d419041c4091039413403080c039006a0f130707000d20480203106035110b1948440103c100282801e0000300460308a01e010040004240700702c190f003c060720440e00700141c590b2100c0c104072009081000b801803001e00103c1c05c2c01020364101e0008419102550b844440381d80c1c80d981416283c0e55407010f0710f000f04104118440c9aa805000500540704d00344040700e05011898001442800071082d040d008505640014000c5d158040207100c050081960240698000705080c281c030801414a031081e01c0001c0c0d03210104583c41381c402c40c0c0062220b900240f01e0b10400e424030100864058520a0700c5d0f100c220044900c8116103600e000210350303c400c030425031a1600ba01c0362000d51010303070100c8039401c140c191042e0003469103103903c4c041c50003a0780050300c5038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 121069415 1250 121068165 121068173
    0x60e070216060c17070501021608030a0e0102070b071b05121c090507031112070e07030b0901030b0f040f05010c0804140f0613050102070818242703120403 68
    0x6800182c1044055000c903404280d00c0c9203560030aa0403402e000790303035001da42001402030080b000711103016a8440010414882c0c044091070040101c0350f070070031110036190109802c07882099001803201e1807010002c1c034030501445c031402c1c1c13000410388105004882030b0382d0300c0e091074103280400070007a0001c194503848591030b4185040d030508118080002c0c07105510b6031580c5d203001e4400180070b81560351007807803503450304080c0c0400a204c0310116448261251030702c45282030300303d8082d070000c2e19040c04400d4a25007040308038101ea4008031a480e0581756010350200a1000501c1a84c40d40081500034001540034801c100919603943e450070560304041ca45000c8511b890800b4228580c020703000c00e041c3c01c801251154001c030400c6405001c02c8400d1400c2ca001e4010b080780034250f1080444e900c03040c0c0b4001d0014020140d41100c2100c02c123500038055000c00d5180313170707844185041c1c103215a0709405030414190302000c0c04603680103201c00300d81000034500340c0c1c05102008803240101c0c0800400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 121070665 1250 121069415 121069453
    0x15130504110d0b1603020c071205011103011a03040512040602010c090b0c070e04020a05040c020d110102070809040b0d0209191a0306070f0314040f230607030f060e0702 74
    0x14240071101440d4010b010b840d0000f800402030702003040803406140710540c690081c0d0481d40d000e0304040c1901e89159035a07444035001142807000381c0f029401c1c100090030030900d003400c503810386004901e00e940c620740314014800355400081044500748104c0b034401d490f4821910182000b800940d001190007a000c04000781120402d9010041d0742c0014048140c040001040c04025160f454103202690b0340d1b5400000c0340c1d8030341c940c06590014a0440345607103455000c074001c00c1071091a15204100d08203120700034201d119824000e003a110b001d01c108038080c6403d030418050044007c00040f2103c041d50005000c1d95002d544d04c0a954081e11485000a4840c4c01203105045501c5485590001c200c00402c2d10b400c030050006041090601c10358bd07060780294440f080c80c00351000c9102c0646442d10340790070658aa0042a183c80400e41405d190f911104144100c1c0c11203054060030503600c3d20381095010b03004103c22806155120500440c0000c0301c0c0401c584545841c0c0d0084c48151601400c1407a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 121071915 1250 121070665 121070693
    0x804060f020105060604170a1a01060801060c020913020d0501110406030c052503021e0a06110a020a110a08241305070506030a0b0907110706050a090b0315130504 71
    0x7964184001c1105035038448003500c04031000d150030000b0303003c1008101410260741d14401814840c104c4800c00c412445444428166503940d19522240e03600c56505030340740305080600942c414502400119000c40210700089143c2c4054100c01203c64203594180c02d5802503400c0c94100300d00410200561540744c0552040c05450b41040341c0340c003141407800c04d000c4d10f020040106008449010404040c030801142d0101c545072880325007a41000f581041d00c40c1e960303030001d503110382c1007010030381207401d4110071214000c655400030188005a9038441846513046048a94024200c0c00300103482d4030240315000000c910002c01c41c1030303d140f07006017511000002d4522204844c0c842d44c039500003034000904606454003261480d8590f40e03001c12840251400b991800c1d044031114050008c0c541e0041c4412205c0c3c40d0990075205100d0300e0300d20880740c50044078021130025076400700400110203864015508400700800b0b880141030550049543e2034850440d18514075592802c1200784001d055030020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 121073165 1250 121071915 121071917
    0xe09070311090d02060708040306060e07210e12070b190908311d1b0405150d05040309080c010201050c0306040f06030506100602011a010c12030f02070804060f 70
    0x141e4480c50301c2190300d4010010302c64082c02c00340d0340c036205640d2002d00340c3d040564456503c50341d0745d4580ca445409040b0a105407180c901c6c010000c100450f000350402c8050b0f8280c1e46c14080340402d00c220f0300e000350103032410070040e5003da01c11000f400c05000c0003c00049002d850300d00d050b8148140c03509001096400310404280c035040b070780c20000303020744200d812103401c8414204229405800d10180203100c0c114802c1c4000320300b04002404200400c00b0f5401190702004655103665004000d00c0c0d21024021800012008000501c11440c010040052127186803d00a040c6010700200300200c68080e182900417031102ca5003084210b404100b100039282c001c0c4024041e90500610710f1120380406010144140d80b1804840c01c28582c5501010003141c02108440725410140400540340000d070054000650038060440c10030744280800d03a84a2300103039211a00b10240e41c0719080e410f04482d10f64400c15403942400c842018140c000303880341c1030041110654552500b01c2c064911038103054000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 121074415 1250 121073165 121073171
    0x41a01020c030c010e011d090112020f0108090d110a0503030c1b03070309090902030316110a0608090606010f050c0a1a0619030213090213020408240403050a140a0e090703 75
    0x91280d82c01061000940d0080c00c01d030001f500a513003411441400b4400080e04000c4901c000210550080c2c8802e0740d5a000f40c0303c4100360010800110380c40102202c42d9540c070780c49401c080444074800d00c480c02d036101506041d07030350741941c9541c0c440c1160700585906044803008210f40101503d000410400b82a510380158601012a5006000e40d406846500103907a030721103a0f0700c00e64a041c0708a034600001d9240d0094010680e04d007188440e003542d801a80076001c0341c400071441c140070b0520079008803025401400543c3c0c81c000115180300c0c02228038010048244207200c43c80c602040510608c501c10a0b04c00018a101c1d5210340d4403081c002c052a2148000041e4005010001c1d14424203a9030159201e03000810000d4800c0c000d48200300e00203400500e041163305003510964040c2c0103541c002d40c1035980d8600003080020744d0390390301160710109103901c1c80401e0020380240003e0031261010704004400f1902c0c0050f01015801121803400410041207440402d4580342c0318140e07000c50310342010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 121075665 1250 121074415 121074433
    0xc01020615060708040506030a091502090102060112110306010b121b07020d0203030903150f01060e1008060a0e01030312060602010e03070809061b100c02150f04030905041a01020c03 80
    0x188540c0d15910301060194000043c48030600c20407504880240a000c0c02c2c103a42c0c1c7c00c1100c105002088046000d1720030b5509602c103502d80e0861402100c901c034505a00400650b400c4c00c40400303600c509040308560926441140c854591400c0c05900e009142e80042d0540b15a032203460824140c00c010140c0305040711041c40f0100501c40c0388103603040c036030301032f10a40c101648510101c0e02c0c610900141d02d41c14421405c55410400c44c0d41310744c902c9802180b400a4883e6a07c034801d40e0000c1c002600e03039034088085060300f40720500c100002d0742c2c4028000c01208030070369110720b144000f200a0300f040c1c0000300042d41e17440851400303000b820003d00135072001b04410444071b60904d03145d000b00c03200148a03410000303d01b074140e030301c1c0010740d44c0031205072008103801001d040010356180104640002c40508000c1d40c411420300108000b0310210503240141855038a54004d02161440204100c0a1111a50b03011a840e00c0d0b80c0700d1540c0e280c0381c3c00541c4090740b071544006443c1405480300c1512903130080c255 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 121076915 1250 121075665 121075681
    0x7050c0c060a1e0903150614040605090402090c0d05010608040b15060301090903020709020c071a0f16050f150702070506031b0f0d0c020a020f0d020f10021e0f0c010206 74
    0x10a003000755078100488840f40c219204441d5251240e1018080c1100c2d4a03003400c8000b0154007100c1103074040103880352082d6880f02484141c40b254466203904c2005400003502600305658215809003180e803440b803510400385c00100844000f80c02c070100003282c1e202040100304010071130303c0c0c01005028100c18540e81d03560000d40a48414003444030b44649502110382014000c00501002d085a26070070b5444401c8031484a5a0300c45a11643c10741a44486c240e418480d11841100e10146213001340910b0403c60b0503100e841200310100841307507403107400c219030036101e800c0c003038050086240410000b203400d0100c00240341102170f420441c450700c4100103204415000c030005906000c4260009919000707040313203012050044043c485541406d10411039107184c0e000c149550710500c212259a1400c45030014000c90101c0c0c20f1009411940d41641e404180c40c01c2135500507001c0d0f861040f035068010390105024405a0102240160352000d07135180c03000c0d4020b00c1f8400030301c3c40a1000342103034504a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 121078165 1250 121076915 121076927
    0x501080f0603250905151f05070f0809060a0305060f030706021504050c130609050f04021804060f0e070503060702062505090a150212040602070b0904021207050c0c060a 74
    0x380703d440d4508820030003440c00070106a07036000303003c1c0f1442000546040340000a41c5003810140711320480091b6060703030348590b03085000020b88146680d5903003081d089035030302d42e03282e44c00c650269500c1030203115003801981c03600020102d2903155540803500b4204041400002c040c41c9055511a4020081c2070112a9001800e1008144241110541502c41d41001030a190b82e0320245a00400c0030000201303500c00540100e4102da04a6008022550700c54403100050102520000e502100b03100c0900066100444429040340c087e03000000d14180c40405c0c0c504988031303404201e210390400d010030405e502d1f050109a902c02d0050000c0c0c243c40c030f03080308800480c82008200c01d010698610741540014403d10039521100c501400400c02c4984490810507044c00004100d001449412041c0c0811100d80080d10300311401c2e44c0003403502c0c03400e00a20704015004040aa508158284440003591900c00b60150251200703440701956217203c0007840c0d007400e580e1040d682c007955040165113403403075200c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 121079415 1250 121078165 121078183
    0x1203020a0f1b0605010b03070912030503040204020a09092d0209090115050403061416020d0f0e030307050a0605100603060302060a030b01020a05010c0e0f04060e0a0b03030c03030405070501080f0603 87
    0x71601600d0001c91509210b22118004009448545400004905119044006d5024101a07101c4d02001507075401140c0c4200c01001005001402c1400801c005040a40241c003041e5003034108600c0d06074030b42101c03c4c101c0c0c040b120103492078510030840750700c581d000c2d0404416a00c00c07800150308e03040c1b0440202d1411541846a088800744500810703048078410416600a154402014020384410171407003c1d94107025106000848043c04142030920300003e40142c484003a91543c0a00344044001641c401030b12040441e09408208101c2d0000344080c8040001a03110f0f0f6000265400c00208110150286800400c14545403010a00250340e400094410034092460045251220800101d08120030418024025800d1880e80016142c00c04404001c1160a0b0b5060003030b00c4440c0b04000a50f1500c0c0b05941003e4201c42c08160415043e40080420380c0d809011640741901210046103198000c0350269280d8004040c2031190307603030140c91550070074030070703e007100d8103040c99000a52500820 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 121080665 1250 121079415 121079417
    0x105010c0c03170304210c0312061e030c08120403060203040611070501140a0207081206030708060403020607090605210a0e030708030a0f05070c1104060911071203020a0f 75
    0xa5500349040251204549000d942d008181c01140d045088111201e500706480c1140c082001461050306480d01c42680144004503551308241d0034410789083c2d9908d00503609006e040d07521031401060000c1500110b00964042c00c505164003071441c107003030082e14026048195290401440e81c040071400b24242d8003925000b010050340c941300d518040004144121002520381d10200d110b5080c0a0103504c501a44084282203d00c95035582450034202e12802c81d00801c020000d0000c064003e1030020741c145c0c490009412211035035190022246050022981140180d00c01410001210350020201d4001c1c00700342406820410071a00e5032300c80201d80080c440c00a4030110000b401e140700c9800105961203003030140d90b550451420714032142d60045481354001401c114421080e100c4e41c3c480c0900c40d010f1640c0e01081c089542c1d5520f00403440e0b800080741c0c426165003001c40c00185070710841544c0c440ea000e0856a0702d1152038004401203a8094807014140b0501c034201d03040d5041070700c3c0741c111025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 121081915 1250 121080665 121080677
    0x6060503010506210c0904050d0e0910122a030606060804080a1206050a0b0901030b0f090c0307021609050405061e060613030501020409060509010e0705040506030705071a0714030906010501 83
    0x803c413507052800309007281d03585c1c0c001240350a1005001e804103640529001c0c035030f2444030181402041c49450802501c2c4840e5070000084108108000d1410f140c003207d20882e90000c108495081c6142440118111101820400d01d020010400e0302d01c2504000c141ca41070111403480c003070301c4040c201e000743c808000038894244c9888441803200d0b07128002815000b4028058552200c2e02525150010140b45012900d400342070000c500c0d04000b2441000401480c100c05690360700c040c5a43e940010b0190b0056101c4c190044025460301038200b07001d41503688001540d40340c035041542c5807550161001c400a03180c4044480e10b03404808400d5844181500c0031681d03042c21440130200180617038000f9015520110f0007040f460b2030382d000700c2c1c00c07201c04642d20252641c0310b00703010411437000d503440404501e081200300458201040038603807081c603506000f420401c540d226684083c0c07054440d500070389903120800080981285099024201c3c543c5840c3c00c40c6003840f0255580c0c1d106001d15814401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 121083165 1250 121081915 121081969
    0xa020306030708011a0d140609030a0905010201020708041a0d06080d0305130b0a1a030a080307110706021f091a160203071a06041b030b030d08040209180f01061206060503010506 78
    0x203800c141e0921fa00000c002c60b0174500e0864046501d036040550b40030009001c0c0c040005046d80b050094940c0107400c60300c800c0c9440d2901a0f404510361441c4000c41c8400b1060001c0403245889108501c0240388960281c00c0c01d4801800040c1112801062081c25041c0e000341c9401103010000f006602903071101d00000c520f80301c9620b1301c5101010038240c0364140719220004ac100655200654020201d035116101ca0381e049148503500c2d20705900541c00140d0006e00c0c2081248680340b82141c95030302107400040e04540f5501c844807607002400411401c03032400c10600210401004580e41070883e144082c3d42031064039a910000300c1c000d6068459000c1c07010020036001da0300c03a8021840c0c01c0d021001111000c5494401402174100c14102c6403080c090003040c4800c403806a0020342c41141d00801542c0d17280e4800380c807030605e5401808c142101e4880c040c42d0140c510803d214001c0030746040e080f01e005500040c94040251a440d802c00c42c000d03410901881030b1501c500c3d0081c4c80c031600d04000810002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 121084415 1250 121083165 121083173
    0x40209070908012a080609040305090406051e010e0f1e031002070b010806280513080d02090a050d020307030308070203090d0b0a0c0207061e0e06030a020306030708011a0d 75
    0x40701a0020107507540390240000345510480c407244500070b911085103110041d0b080c2c003912000012200d0f2030300f000c0c8110000f40000e11075001080e007000d00820010361503464a01041c0d10031f0703a8140e034500d0a64002c0150b80c1030740c1c0028a20111041c1220030400d500b642c0c82c0854004010b0389541c24621106044440041d03405025002191050100440d120000760410f0b125a800a21801009018130b0010440d4645003000d016800f00e05010405081082020020700410b4000d02036481c2e461000c05910000355510300401c04000e80c40c00241c0c0701c80d503034020881035480341d0340114030800d0508000801030701d000c99400d0442c3c0d09410064802d50b13035540242e04601c150b2882c55802035551130741d0b4080040b00140a0701034508880200030440d5a90300c00c0e65141d485004040c01705050040b00c42441640001d00c02060310039181201e00d807040f07400801c030160400c0c0e0300945007030b4022080041e6420100603400040c10030300024000b484d03c030b0154800c2c400303040d0322060040d211007010030240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 121085665 1250 121084415 121084427
    0x3140a0203040b131e03210603020a080309030a0b070c02090702060108010606030b031b0a0e01030b01090e01150b0306060f03010e091513230d020105092103010905101203051201150804020907 84
    0x187d080302d01041200441f035020b0b58000c10760790100700d11803026903401045040d00082940c3c1000e0000d0020402c5400c10746a000101c040280480e007000300402105c0e0040e201c0e0014280074401c00c1d0000c002c2541031519807405c0d0b0b02c0a4004404040c075025074280196400110001040100e8140845407101d18020680d0505e8070340083c82c2d1181e00038000004c0050b0400010f04888200bc001c111010500403030600b614207400b6448031083d1021428400248030500440d08200014866860010018240311a6400903400250403500310402c111000c2d41c14058044030283c0402c2c041d00500d07014540e41440e17103144101910000200801c212000c15000d02c0f4080d2044403400c4036004c000c00000240a81750880d4070300705900400f500f2107140501c0c0300c0c2a4603511a1a03041500f56802c0c180c000c0028403008051007203024084000103030880018884403080f40c02660b88607503a14146030010b10001040e4000c910380c0304043c202c07011241c0c1c031110150700309904641500e16502c40030411181c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 121086915 1250 121085665 121085687
    0xb04060611060c0d0e0a03020a061406220f060905010503100c02070e0c12010b0d0f060b0a05090609090907030b0705040b040311120303070c06060b07080a080703140a0203040b131e03 80
    0x185e4842d010140080c1a000941300703281c58401c0c07900740074240310100e41219140b01503c0d9203802000c551608101282012118a40c44071248000500030a04030741036000e0703a135035501c40f1044542c0c40c0018081405c2c04c1c00446045007400500b8050f41c160004000d50782e2160f445044c44039481c440c003040344944003a04543c8208000801441e841d61509071a0269038490048203220034605910900314a403039005040448241d07868240c148500c1400988065200300c0c4015030180041105001c16510203076040d005840600003092002d007107140200b4006005000c420038018140700400014070b10360101c1d01070703907440603c2c2890440540c001c00c8040406843c0c282c69400007004006c3d0f415030002006000310b005020522019a548103540f804d0310030000301400c000740401121703020600039188160490308515001404640d20603801800c214251000d40c2c1658000050005016a81c446180c1010755101b040f03104a03000da84520030b61a07450200f40c000c510403000042494010101081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 121088165 1250 121086915 121086941
    0x4030c06092004060f050f1c0308070219050c1210060e10090204051008190c0302120604150303080c1308010b15070803060f0f0d060b04060611060c0d 66
    0xc010945445001c041242ca0081c0015420100d2082c29150034020042252600001402c03800c1c284414840e00c02444062950050200c0d083d0340d04c983c640300384490000303010780c1d1800054145190000d041080304810f40c5840c0c2610880c680219101180ca081d00b1a0112075104030981745000e1603050000300c0e4070389070589241100c0003034208400e44016218030000d8010210454945000d00100d00507070191a030001d5001d05d44411140c06000e090b608424000134100d205000c0744040002c2c3d840c1241c0710710000f40c0200f00700054039654407945030064000c5030148207083c00c8030300d0031444011034070020f81080150300104032440b191004880241106000d40c984c1c0c5903c81078001c3c041c242504286000761807003651540f03949400025100103a034071042d810300c1c64a940302005008002901540c1d0b10800000704c221482e540c071600001c2061007082c000c55800c41c42800c2004482603540b2580030301c608010710740032000000c1883e0b0340c0300a43c00020380d143c6580030011401411104010b40c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 121089415 1250 121088165 121088171
    0x1030513080c0d020c0d1e11191406030702030313061811030d02060c0f090f090f06030c03010c0c030320030106050408060106020703020d03050307020c0405130512120f04030c06 78
    0x980240b020400421200341c3d038089500424004080c00b112802001001d010340c040c81140c90240600c0c114608201c0c0c6c002e6660794084514000026003c403403041c40880c44113842c100401040010045c881024841101e01c1802d625040c40042e442c5d04c001080d684140080101090410400c1d0b80111950401c0903042e42c047c1c501440d114541c0d401002640d40b00b441810782c0041114800200b4600c910000d110315410011948002100342e04807114095201d0303401d0900004075258134036150b11600c401008200720b410200145403d104000c11740c00e00a13414000c03605050340e004040c0001c40c42c0e25250000e080d50850303500d14400340c9a005d92609015000000080c1c55a00c034010303009560403c42518003903681c1c3d80d0300380c1c0c2d250210711009400c1014001c90402090007840070316409069401510101000c16000034112901261411010000c0210190902100300044a4052000d0b09030501e880700c14054840c035902c3c028030412031038458000043c2090b104002c20348003294000b4081c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 121090665 1250 121089415 121089427
    0x50d0318080309091f06120e0111030711070609051302040f030b0718030506130618030207140603010e040605070215040f0605160c03030e0c060d090506100e060103051308 75
    0x1e291264803200f40540710324480b90100d209006004800e006a4407028850165503207003202c1a40d0b130f1404070751f2510005070384249003075003000d0030701030440405203503030071030f556403500503030160807100a800302d103080390b020b1042449259002006e1070305072102100c14000c11032224880c1e8010340308540040d8000d490b5204004100115005074500980b4a5150f95040881103013103030081c00c03c20700c0003802a51000010038004640880903095881c0a404080391707202110803540e03041d02841e10114010b0780040010440c9040c8140841c004440440d9602d146501d0811441c050a41c064405865550b0b00c2d0041035659000b040544400722242c500d02d04249464201429401c0f014903042d58180e0270000000c111060009035500c0e603100c192540f81d042d4020380c81c00c80003444410082d08840c41a42048003603696684040d2402c40c588110201761860240342071400c000c40034203082040841c0700030502840702c001449580c840028a40045e10760b851400145146120101c01743c2120800500e07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 121091915 1250 121090665 121090679
    0x307050d030e03160f0206160b09010609020c0a080c030702090403050d150806040308150d05030c1002070203030409111b030a080f150409080f030702060a06090b010801050d0318 78
    0x200c0030688030a4404104070055040c0280e2030744030700d00b500c24180d002c9150800c00500c031643e995000070300113044241000c808040d20801910b030b025080e110301e031004040260544007406644068003400c1c03070035418400e40c04902940c40500c0340340103003070321400b080d46509540100191504281c0081194484d030400d818013620962010240d030b81224200801001d04001410b00d1a003240c003601c000300315564468070202c3d0810009414219000c00c602c8202c2403559880250604d090300680186603582c064541091070480d00d204007400e954014000b00e400760b40c2c01700a45080b25804a0046180c0401c52000000762142d40051400d200c00840240c000101c000080d10b0094056220007081d0b486283c2c005011034422035581403c500c10480e603002c2d50030143c21402c5603c0c40350b803010b0704110402d4502c07102900100c403ca00103900072010040f96819500408005003141d42041202603039590000704803985c14080d0070300480e6840c03514020107200f4594941c42d03548040c0e1444040c1d0321106 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 121093165 1250 121091915 121091923
    0x15030f0117070b030402120a2004060e06030d05130e01090b010f020c0604090c02010209030a050a05060106170a0b012303060a0501052a10090c030b0c13090506060705030705 76
    0x542000000701541005460400142440035078070321080141c216a20780c1e080100c60032049226001500039690408000703000c00b140001381c1e800701c0645580602140301400103c4502e0342c0141d050010380020b000842d01c0104001c2400761842c41c02c26540d0b10840c0d10303180e030b6924a600540c0e00e010300100002da07090059025020301d440036a01d0840ca041d00e0b25007241d4450071002641d500250811040018011603800003091907000c7c0000b60500c1c410400007410095880400c4d80c070f90b0405d998100c10407000380300313803400b511090038400000d00801c42d00c0540d5400051220800710741c0d03900030803550b070b00071408011950055000301a01e0114510b0201413500103030341c010700510401c20046481d40c0030724107485070a8102d02280c0490060017600100005003408000607600030080c80034800311a901801918902840503500c0203032441c6045044030b00010f1007100c61400500c08216071100000076101250360b1800089142c2d115000051858440d16500502e1803000103595020804049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 121094415 1250 121093165 121093169
    0x15020a1a040c06170601110a020d1407060809190c05060307030905102708070c030501150b0a0e01030917071a060d08030703020a03060b0d0f1b020a1115030f01 70
    0x41c40b00d003003540d5500c0c1516007030440180c030a00007a01030300103100740d4410034240d0032100d0300900f02d40840113240c004c5140c00d0100d080540d140d01c07548650454400d010001d080003441145403058003483e114a09039143c11550b2034a099604100000c0014050141000707409050020310083c4d881c280900c02170001c1100c010103c6030350003290180350101c6020722a44603162a41a0302c05406849020b0003a150801800d0880c1c400c6020b000010105860000d02d0000d14880c2000140c08070102200a00a00c0c4a60120503080380030807130428070980c08140c61210640038240451201c0107450a100c90204104c9030805058000c61260144455481042c0c80d0020710100c1b42c0082e1900001d10081e00400c01024004039410000b28020781d00c030342d0042800d1001351800140c4c1c41c0d1138809601030742c0c0c00280f50341407a03612070f00c08540800182c03240b440c2600743c00074610020080102c0294070780d01850342c0a00030400c20380320207890740c0b21440003910b001c0c940c561090352890540180f4515807400c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 121095665 1250 121094415 121094423
    0x30910031a120a03030504060e0d11070e010518130203030a17010f030c0303050c0708120a03050a2706020904020a020a1401020708030a0b0d05010e031c1515020a1a04 73
    0x58014005800c1041040100b980c1100181034461040d4400b64058407000d40100e807444d56034602a81c501c0750502c8469188a13403070b030340e0b10b10060035036203150300d4484150809151030702500010091551180481c2d03110840b0f8160f40b1659a1750405030366100e8516031000ba406000c0000c0866110781e20100c00c0350282d00a844c80c4510f81d0700c90b1004001d0840c580001840c24155400c24000304e0b0241c4040d21341d00304081e040305d641c2c0351180c04e2141000d003040500c00f20f00c2070204513000429094010180d0200307425000f002039088060480c0d01c541c0012100358280010840c0102c00d01140350100c0c0e551040c09042955101d001c102c00039a140075585080e69080c040c02d804441c1e00f45c040c001c84050700c2c0c11814150847e2500510540103003005141070354040003407000d950004d1402e00a8104828012000d1a11810b0084000c00c910060010441c8014a0f29141e030010400307107000705080c0c4080c1c160381203412f00c0703c060070b03441c105260101030509034440041c0d0030403d0480404504c01c501c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 121096915 1250 121095665 121095701
    0x31101090b0a0c05041436070f03020a090603150b190318050c010f1106090106050102070501050405030303010b0306010912060b0f010806180603160f17031e0304020303091003 77
    0x3243c90111990f000c0c0e8000c940640307840c100d0f40700756803400c001c1040e4070b100f0f019401c085e07040180180812440c4003c100940d4621a08200300c0419040b80c00c900102c4000d0030254500700b600303080100702041d203014080a055642803207404901209541030003505c010f100459485c1440c1c942c00c2400c242c000407030b0001900b0880f00d11100b501540c080312a26510200174444401081c00554034040078801d620100824014020340040e4200b00182c016124000005003240c10100024203003400344e00007a06012041004025980f400000c8a04407000c5068107500d90301d030b00e00101c4e88501c441c2c3c0700413059444e03410144223200c0c940e4040e845602d01101c0d240700ad03049840064494040803203900b68070104000b66200006030101c80190300640080130303283c100205009091407103a140d00070081d0076455000c1401540010700c060759002c420100112300b048232098070000030003c1b1380c8210120080200200d811034501700161200960700400e00111241581c000a0003418202c0d1403900f4031007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 121098165 1250 121096915 121096931
    0x20403020906040b011b060b040c0512060913060e030706020f0d06091a0d05010e1b09060a140d030c0b010905040614010506030c0c0a06141801060b070f031101090b0a 73
    0x5004d2183d1a08814180c40b40007002e4074699407074100f03c1c41060207403142521081f032042c84c0d94441c0f064090039000c580359a078691030219100d1074500c500520007401a022042031100d1414013032801540958003101c086a20411824204c1c01c4d4052804020251400407881000880901c009001c0d4810800010001140e41d40c00c894191b40c05041200607030710407100c01d544a4101800701004442c000c400110740c0c04004140940b905055900340c0d500003041004509041c500300c8422500b02c0d404990134224603041c1001d41c041c00c100b41200f0b5214060103041001094002d901ea00d181c1504410344400c0c540e519520080a0320080f201142c07507910349016828110680c8950505039038014040700e0455441e404d600c0c207250f00111920400d40704424141c1c002a0440c0100c0c2c81e040d1100480028030f0901040c19081c1c04045144504a40d050920a0054400700810b640b90103400902c11280440755003003c0d280c8000000000d8203550800c03c00c0818004906000c0d40a03010700701003000790700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 121099415 1250 121098165 121098169
    0x50316030203071d0315010b130519050d0201021603030f1101020a09091107050304080a030f080417070f0b0906010513060e0105090a0204051206071d01080403030e0f0d03020403020906 81
    0x12100715641000b04903465410a2103464011300702a44070700c060122459403641100942414100360700017889024001902d0740d4009d2139201c030700002e1005840c034040500300e440000fa01c2440c103000d40750142c034000d540501960300c2000059604211031407841d50854680c100103000c64080350310007020400b81c1c1c007505461780307051003213400020080d952500e030b139818542681e0140850041c1c0c001040ca080c400640440c6041c0003c20041403100300502c045202803a0180404400c00e401c802445192030401004c80d40700f00204001c03030320800c1c28039a649414a880424030038031420207400c80f40b42004100c884400001c01a042c0c420480743c10700007041d440e00d940700303441090040c41034880d55070004006500b04911650b0700800740a00160030651100e0106d020f10090500501c010382c4001c0c24081184e400c00c070803003010503501c00100394000b0014006022110701800080c00c00d40c0e508540c40041c00c0c14070a03030b044826003605840c04194446001070207900180802e0740f051410341f010403458 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 121100665 1250 121099415 121099417
    0x7020a0b040c090506090c0706050703020c010f020d06050a05060d020c010207060f1a030304080718060e070507060609060506030402060a0908010c020c130203061f030e150a05060d030228050a030503160302 90
    0x240941f400e81a29208807039072600050000500030303006164007405203901c2c1550038014024003140b036800050301c902c840000401654400c0d404940100c0403040c0501140e204c040c11908058030342c68026a582c0d400c800c2082c0240715140000d07103000d2500b81c1c503800003103e43e00100d003603014510a0042c41c00d119810103451384101e1160681641c00507104205807040102d076403402140301c1400142d55542c13500c2048140100300d4090001890026441d01001824810640074003680d0404102c01814040419028403014001034031800d0f0200340f91088500c00c0d1021406450740c40002c0c40035006000010b95190074041c50705208030103d00040580307224038800d4a21a400c0100120000b480c0052000b09100c400e001103010141c541d259042142d004000d100d56003511040c1c021014540302c8402000c60b200a81503d11030015140d940c40802d40c0051001c001e062588440d607030f514030060b1014030581d5600d0000b0198021070328403806054000740514807854440c0d030710801c150a81e040c11012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 121101915 1250 121100665 121100671
    0xd02280509040602042d1502030706060b130f12081602101e080412050304020111011109040606020109120e0d15020306030706090807030b04062403020307080c011707020a0b040c09050609 82
    0x10351040c440304001ca6100c4c0c100c1d100e01c1d507e240c01661b240a21640b52130090768910f4000015002c0c00141030419013402d00d520400800c3c20050010070142003182409440c0b0704d04a0180502c20702040c814000001c80c8980c0c049103a00518601d02000101006000d40006c00481b015441c0011080c601503802094910711980c1e200130780400400000c0e4044d1265080a00107070704200d442841c08201d41024400c0b01400459403081e40c1e102c030641c4d410001600c03801c0d00042c0859052507281000501c440b510040300300c03001e0030554441601c0300003160181c2c3c000c400c00b80507111904407500219841e07500a40c020581030381960051034842a041d00e0050a40c400c0c083c15500043d4101301265503844040c0e0003a01c00c0c0d0340803c80700c404125041c603580c1a0140400741d90600002002145004c200d03110041011401a040c5a0182000070740000049041c001e4031140000010b01658401e016040400c0d034403150140841c03e0604103840864014002d1a08240c81c00012400601d00220381a01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 121103165 1250 121101915 121101989
    0xb0109180f0501020c0303010905090c10021f110406050301030b01120f080f070204110901030e120405040b0402040515030906070215072024060d0228050904060204 72
    0x254030009035600e448080e68141c0a603050356081c880d0503050301c0c00f4001503001b456500e038003007000d040c1648c4250600c1086005030b4801e5000c0c2c0010841c8a40100714420283c44043c0c0c2610350360200030000026014401442c0c2c000240040c0214003642c000e0042e5041c2ca0013000c00364031076a2214080d40c9155001e010150161400181c000002101134005200000d060b400160800003180d011409031103c82c04021000340c00410404502c2d6814800c1240c00c1e045200240000040d401c040c01e0305206a000d068000c6884580c21035190710380d60100c0700146405412000c0b52001c8205405041c0c1003921011481e004040208003060320001303100d6044056400c2d0314415499a403415503140001c0c41341c1c052800c1c920701303240c10240703828446600e004100039a03110403480f1227600800880d00050015205000e07011506015850300b01d520f5083c000f1030b07201c1e403070141120251401c081106504c896030114090040204001f11900504201e4070151200d90440317800110021000721010b80c050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 121104415 1250 121103165 121103201
    0x9080304080606190503070303050a120506010e0d0611181806010906030b040f050906090c1c0212070b07050d03380d05060c120606030c2a0a0606030b0109 68
    0x250781858920500c07040d4134980c04406903603035075a8010034100000c6030f10a80c00701e01c02203031001916411401000e42215191410803061138100d0001c0c2c1001404071589015400304c3c1204030812503117502064880d1485203445c3d480d106e02000e08403007600c01c1a0141c4c0940414085850001c609003500790207000305031038280419007020b600b10000c00c07580460390391098480042d80d40c000704500c00e45010712840c101030001854a4a4018900655200700301d0007034002c0704640803401d41130f1191883c1c490703040b2140c4124402481c80c5901d40585d40e000308015400c0020410100000000c10120442007902d00b4001c00140750007448040e500700041080100240d9407042c248200c640340e0800211009003100241c1245031140d900c1c0070402c50701c1806055001642e05000002c10740d0295004104640d031500d94a811660b0040500403104080a00180c1c210f101c600f04540500c0603003002c0000341110307000c0a441c20710078060702941c8000e07100012014000704e01c00143d801180c0c641850201c0301 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 121105665 1250 121104415 121104421
    0xc0f050a02030319060e09010c0305011e0302060a02070807060c0c06080708060d020402040f0e0a11030106020a03050a090b0708030a14060a05120a0c0e0f341403010b0406090803040806 81
    0x300540d0500c0c4c00f9420074083e0340b07490200781603034600f09882c000c100c0540001080c1c0c581000260840b401030704803540100c11070404111480140221009803a0306584082d11028444010fa28005a9400a616602840c4008620140e0001001446034003a6101c810500d03520a8161103656060320341000081c10003002030720a00740000c08880952010b00010320301580c5441c50b401c1e00002c0d0700048000400b45080c000005400d0085802001d40f1510144c07031945424800f030b5a503180c10400805104d40800d44115203400745520b61b005248009405544915519003103501794412166165028540782c2c0c04d4807030718030104605100d9140980304802c05810075041242c19075401201c007a40c2c1c802d0340c1d43e0000085821654500410204241003c5030034500400004030703400905418042501c8040550182001c6000c0406c0e0b4028008207203d894031104110740b008120524044142d1002000117a03401640e070040c01100c3c1c00c1d98520b2090b9441313250750758413031003280719034419640300d4008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 121106915 1250 121105665 121105681
    0xc130b031b0309010e070e100302011b02030307060e010f06050a0911040909050c0307080c0a180b040c0e0a0f0e04061d07060504060305130b010614070c090c0f050a020303 75
    0x35034020315614481c007020741c07101000c54496481210b0000c6140d4507104182544641044445c01500c1400400c02c001e141c81c00c0d003031607551400c1c407020307040155048002c0890f00501480840d50354010303013070320380d50030f2581442030142c0110700c3d10341104d61a111228018007080d00c01d420a40b10020a004951032900040c1d1020b030103150700071f8060740e100b0040001d655202d88201c400c880d100341c014017880d9040004143c244441c4e98032030100303900075201030040d80da40c1d94000380907102750054481d41c0503d43c48551001b03000000007650003038600324082100507007120303040c41d501c0d00881ea032003949911884500c581c3c001c80e10a01c0c0c0e10003e1100480c0c00280941c0040615041c0d02074661b01074041c0d040880e00d080c00940c440e00100d00b0005051100310b505000b4107512101c0004005001101c996a402c03003840148501410030060f404485021208113045591007038100c00c014029036200c00c2c8090003040030641e000042072400c00c050b041c41d40991705035480000f550300610309503901d10724 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 121108165 1250 121106915 121106917
    0x1f020606040b0109051e190e07050d0603050105040b0a05010b16080702031f23090d0e01030209060f18031212040f0209040602030609090f0304050d06060e040311060c130b 75
    0x520f030520000e4140400c0645604840c0e450004800045801d074105e600d0501c40381100c02c4080c042002d00c1d000090044101c0c001006401004c10308d05030361364420046944000b800240c10080075942044c0a21050003000304065014103116081000a41d0783d6040940a07486106d204904014103190004080703031001e0b010701607403400a01561700569250419130715044c1000e4421541c00d03074524184404030301d8050781004088604000540c14100020b4069403400311000003004c118441d00703929000c0c3d100c0d4044e84c0010202420765038984031107840c40107298010f449030400c030200c400301c0c08a8500e00082c541e0852211170320103034901500900003092a4078010720542c2c5079003504841c240180c5450754414840c40c014040103842e420941c00700032009001400050140e440148121241a0040b08980440d10112002d8240c510a4504040600700c541e105402e2080740d6030402082c1354102076403580e410104010740304950b85550b0410f0183c05001c0c0604c08051602c941880040c8100c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 121109415 1250 121108165 121108181
    0xd1e1e0b03030702030f0a030201050709030f0206070c0b03010801060e0c0a05120c0408060a02030906090601030c170c03010f14070c110405060315070f0906090308090910150e1f02060604 82
    0x29081d20b20300021500446e141500c0d01c1000720b00e590200c00c02d0418568207220380d9030000c8980c6403152240f8616192402e51451a2030041d204410001c3c2c074100304181e100d4504c0c02011090600c544969455481a009044a11408075002c103030034001900c402030903046400c03010b1141c0b00c5904007c0400b00f80b000e20381f401040303001a0307a42048003142681c0100001440380b01c102d4405a40d03403600004c07803406d045001d04000074a91040c001800003800301030003801600d0100000c2c02c81d01d001640001d281803e040e00d000e415500e0840e40c50b41c0e0480c182c200000d0035040f55450130590319500c204449000c001003016001c01030804690250b03144c00c2d040345800c0a0000d0072520508900045440c84d0341e0141d5003c408940300c200b40c00084c3ea00903003010300410203030a1032000c983c50360326900b20344d21449444510903682800051030b07102c441751512019041124100317060481c070a0b0043c2c00110001d4040d8859102c590320a1a120130115450f6508800d90b806803810f40c540000340300191620b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 121110665 1250 121109415 121109419
    0xa0c0207030f0c1a0c0d03020306030a020a090c0f0503041106070204091509050d0507020a0515272b0209070e0d080324101407080d1e1e0b 61
    0xc81000400300e910340d100010034034010301e060660329250505600c000c4249a914182080041c03100010007038000c95101d000d41540d080c050b03500d50700d41000a041124200b0025449101c1241c0890114801d034080d502e502410b480d050b9038201c04000513030303246c04103d40080c1500b495801c001038070f003801c1015150700d500c09040418400082c0d40c40303800080010322109106a90380b00070100340101009844d040b84d466081140c600070441c0c000c584241c03100e0050900038000109400102c140382c00441d5002507501084244104070310601b001050740b00440940f01c0d000b1403101c524100c894080b44030340c110004081c0313032002e0100da081c0044084001d296105001844e8200300c1191100c0760322121240c4250865a900d01d083c000c00004207072425140e08080086100c0d072040c0c0c0e269881840718034251820003107110046035500031014840d044000700003c1d40402c100010401a8104161507070141100105581c4030080c10011038030800da00049114240300740d600e10708803a5119500c81180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 121111915 1250 121110665 121110673
    0xa06180b07050c13060b0f03040c0b0a0818031201210206040f050103060f05030a170c01060e1510050a0309051507080f0901020306010504090b120607021c0801050303030a0c02 77
    0xe5420159180c0e0403120060b12680c002000c04402d034a4040346000032141206420401d079810f0000c90f1800e4000c40c01c0e158000e1900001017070500c640e60440d01c0c000e041c52100ea036075416021000070035004094a01c42205c1101c0010b000d031149001c82510150388502e0805903440c2c1c80c040718041603007440c1c207051a40b050340c80d0b0150302503184c039070003003010300201010300121030701c0c2100060454a06500030b40b0401d14085051009a4000c2141550380390030003040b110b050501c04a4095030710509044074a150b10f0800000342d425849907502c3e100d11040d000400152080c0c3c2c05204848507200440c200050b0100319149005010341d100030b9040d07002d1021100154a01807840041c100256200c03004141800c08200c195080f80d2071403a480b0444000a5084d424980d0002c1c0440c0101e02030700035840d8540c154242c880d194106800300d581c1c4064121180c60600c294041c0d210782510304880c805000c0108041c42050240c0343c40c2e812030300050011469980c403460000b00401120a0350011401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 121113165 1250 121111915 121111919
    0x1060905120c010c0201050304021c030906090504022502061204051b1c1407091505030d0f020a03030216060f0501060806190b0c010908030a0203091e030a031508010207030203130608060a0618 84
    0x80f1410452f116610940f0344000e01c0e8284200644010300350740c8481d100b0b0b80100020554282181d8155800740303c90340b246c450b0a0b80c2c5100160303090183d00300032032291000c24100801d0000c00a0700128040c8501030522804140d042131181c2c407c2c0d4501c510040d02c041d50301c44030002d071107088900c2000e0203080640d0300c03607600d545210301600e42d442111290740c55020410300070f500c0c0c02d10034240e04807c241040003107070060041c040e46400b207481c406414180d02080094110f29104842e5031802d0303122030304000c80410310f2407000082c68207009080000300c5d140004ad695041803510341102c015107180720006103240160181e00d55000c100890201e540b5525880c0005035032001440c0500ea016502507103904d86400c08900c0c00035060300003100c4100a0910780603442001c41128030390080743c034002c00d24244070120101401203071340c41001d8640c0300080359014564040301403c1c0c1d401c0e10002c4482d5080c2d1f01c01c0110b51480d02910401c3d4404500881009050302a070071005006040310031090304e0365 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 121114415 1250 121113165 121113199
    0x9031a0711010f020d050105010207030c0b0c0a0f0f0507050a120f110306010824160c02040e07090c080c090a0605070515011511070806010501030e0307020901060905120c010c020105030402 83
    0xd03088401280f0041d8001c2070451400e07003580071310b502400080c4000d004031859526800322441151140042c101e8001a00c480006818001b5039003032500300030a1403070012030b8500344002030b01141d81501d0502410101007070b41d00d0910080c0044940380704492081c0605070304d0360000440014412901d00700e9640b01512140c4051101c28024185400500038102e00803011140000000c2c08141800c176480c0e0070000001c9140e2072213001e0043c14605410810000e10200f0024805c41502c3c43c814411003a0025450031180c000c11001180f1b940c4d03a440c681c4070090441610f000d079400540d07205407a04803e101039032052002c0c0101c240104203d03051400c143c3c05511041b103081c2c000c03106440c484200350350099000420700ca030b0100c0500080445c01e1500c541c01d6103030003060203803030304154507039104640c18002042905c82c91600144809400d59403030030090301c861920302c180c5002e24002d0b10021103407800454206402c3d103047e11164041107181d401102c0581c001403040380c1c04402061020060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 121115665 1250 121114415 121114421
    0x1e01021f0203160203070309170c03120a03060501090e0f0615030703050402010e0303030702060117030c0613050c01020d05030604050c04080109050a150603020a0b07080909090106030606050109031a071101 90
    0x2403111680060341c0f400d1020412100366110340d00d040c1590b00c10464003001a0f40056500c0c11103125030b50541d150350507040118240b00618150079070610840c05242841d4140c040140501c90880d02c040004540c6d0310019146501548100c486841d11070b800103904503080c1c40c0490380802c3c010140701503520100d400b044203070400e44030308000a589000300f204550300048240141181100103609600d045280255070320014065240d6900310052a69030300e1070104207941402d209201500c0076441d103044003007140a04030030251154400c010640c04d43e54008102c2949041140d07a5440c596070b500c46c2440b01502001e041914020400c2200041c1480d0a200e1103030300303a01c2407026101516190810511124255a24030451468003004000696030f08810408458126060903103d0034182049007203409a42c83c0940c2100c504402c000d1140010b6201d203003600e20989081201e95100c000460b4442580e000040c05d142804100c1480c240d00558000e9100e03149150803560080f94003d01829 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 121116915 1250 121115665 121115713
    0xa030e0a0c0302030105100b07030e030c03030d0b1c230c04050910110906040501030f09140f0f010c09050105090a08121201151403040c0e0c0d0c030b1e0102 69
    0x20721000a0018021441d0038010320b070b0801620b440003042a803d055028007a8402e00c0030040a110005001440540f424022441018002416280c4030b40c988507685004d030030340f00d8a061242d0440c5102039000113401a807000308542103d01040c0a0307448810748055402441e4002c0401c0c85004040300c4555941d0259510400108000c0c00d0171401280400c41581d142000700e030611a0240810100c2d502d400e8140c401700c0d2000d01e0003141c0c40350100103c10060616200c00b60a10002d401c01c01d1880200107100c1203807107a2001250304018200002900321106010603d0024002440400c015840344000d400d1601d0b0050410400565a11000b40741001144411980e00c1d40882c1040103c0800d2540900420859848a600d0044054000d01181d070800b01310b00c03081c1011021405124a01e168100a0115004248070324145090704040300d8200000c05001380781003804072080b4078440c2c0186541400040d002d80c091211120040d4124034448074194114400c10700485014410b1044000f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 121118165 1250 121116915 121116923
    0x4081006150906020615040905030c030702010f05120402090a0e010510180501050303070605090f1504110f0d02120f03030c12070219020d0303021605070504050702070303140a030e0a 80
    0x100a480c00c1440c0568225285504092102d0031004001054010403296402280240b101c9180d030f24081c0020700411711a140035082e03120218191101040003c01048014000d89810340524a404400c94680c89010309281c1e082e9010740c0410018100454070380c3d0009212000402d0841c02c002006086800403216002e51044241d0100440034081081e6500c8a401c00b000784020b40c14030012a66030f224a2000030811a81c95002441012040c01400c4801016000303407003207900c89081d5560703078950036107003a0b03048c8550782102040c515003140320400b140009816054400c8054081043c605420340e13110003030740160550b81140c21000c0c801940305000c800d081940b0380744000810b100740d4070003e084e5001e552100320a500d02030070390002403142640c110f42c0300c1c1c2006202d103411006401006101d0b110640e0040440c0c0c20084080380a4040d0703501a01c04014565403000100d07554800c1d4032014000c100790428081c04651100020184849107080204809c008003114600c2c04c400d00e0f005031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 121119415 1250 121118165 121118171
    0x1030c1b0317060607170a0e0303040305060105090c07120c0606090c020610170a1203060506070b090f010507050f0c1921030b010e06070201020703020418020103050a021204030c030203040810 84
    0x421924000c2c000e10360800003d451941c00d02d00180e44010500060120100c0488030118020404520032940c40c008120301500f500d4032207a5038540315076a04800c0c0034081c0706003004030018401803080401d441d25141c003c202e1207180400c2e0b41040c0ea0882c0351580544000c0e8503881c0c0414070803403034010032001e0003c580c0100000d240400b0300d0740e2b0344103164200d19006144002c0c1014500000142c100b032080d00401500c60303101d00400c065000340a40e5025580044002c42c10f4030070311001201551141c083c02081d030701c500c40b02c908490308a980c22120300303001c51010b1180d5021050f0600180c01c1440c0032004455184600d02c00720381300740070721940454801da44001c8500e2141900c241c0d008132110135003020701107c194075002a2840c07400e046600d001d01c20208015042d68400c014000007541c0240c001c1011194403081c109013002d8820303099010900348400710780209072910884500d580806420407860301c81c1e42d011604403218110980444c8000e21010900800c00c1c4600c000f643d00e245000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 121120665 1250 121119415 121119437
    0x13021e1308010b0906010e0909100c0c1109010b0d09021512040c0f0b040b0304050c040e0102180d0b010905100905070e0907020c0102060f07031d01022104050a0201030c1b03 76
    0x5030030b40d07250103100b9000304c0c2500240900759822000c0400141000caa00c616595030b10b84210340f41606032100d0a070b9640c240940303955080e40004030400124003c0034840d8800300d600d001d20088030028414040314040c100150041106c955000e40b0303034584020300702d1031480c02c2c46407000c0e4150000d419100f4810300e004144000c0100411148008002801c00380003514548a40e01400340698890440e0b1030030000b00103410841c0501c1304034040c480c0103000700221205480d031039000b508128150424010303d40103640041c070b807280780c000103940d0142c107408444e0f0070f1803c07600182902078a090000c52545401003a5100c032401000c0c41445907903641c0380c5000000f403c0200c84000070b00f910003550025808a01240d80c0171035600e601c0145040c4140598076aa807049008003c98580030805203000d02d0305800c4050107400602c044907507454070340c3e8500220039001f18004416a802030050380318100b5080194044e801007421080c0c00d0919418407042040b0702503200100c017070100d00240f251002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 121121915 1250 121120665 121120679
    0xd02130e0f040c030f0206250c14060301031203090f11040f02120f06030c060f0c0c090106020307060504020613080f28110a260601120213021e13 64
    0xc09980000c0c0c58044040d542040d4551101c100303802d01010b42814807808a81c01076441d0001103902c00305100c82007402c03484d0004910007980408035000c481d41c0c10866000118078401940404030030f44018240d610b142d2941c2d445a00d61500700c80381505041d00c803082400451603003601c800b00741d405220250302c01030b1000100411201445460102d10388103000c502551010302e80160b074070030041d9031070100caa01ca00001a04e400c050000f941d0b8440d00014025207003c0b1001c0140504445450032a9210305590303042254a010074040c4800690040c041e4078041030313098110a401c5400501014501102c021082d1203105440d080014158490041c0c20400001088000090107512540f000000a1007121880c8030002403805414841183c1491009030b0711031484500a007241c1814214503000800720780c1038600034010b84005401144000030b07044000460149135250300400719030b46511121402c8000b500f21440d440c2c200240031001d00018040c0c50028000140d0446622201130302d0658 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 121123165 1250 121121915 121121939
    0x90b120c03120c100612031e0903020103020c0c03010507030e0c09040201050f07030311070614071718010e0307050c1011280606030312060b070c2601140610110d03020d020d0213 78
    0x1800500700703040c005286c0d27000341c000b0140c1b64240380c003503524106601c02c51310780030b10407450300d500d54684810310202c0d50701980b0040502c07403042c041e0b0b048240408204080e02c0740c102c070003a000c100304100e0841362084120080001a2003400c0008103800c8220041465804c420022a1120f84d510b2110a000000303c001680c440380901c0d042d074142c1100481000c0921002d0b12010310a1303680e000d40780c007914080d040100e411615030100c035156841414840c2e80d944035660461f020341c00c080455211706118508500b0096020340040084c240046080040041000900341c2d120138840c0203038000035214012180114041d40d5101070b450203101c05c800465510368010f030b900d48400c0102800180341c1da0411720032035140c0039a4050168040600a108654010300d804d1254a4580c100d041c0300c401d803418034015031064900300a103011aa40688040120780d5011300c10ba4044a4164100707446500200404042c440016007028088007000c6c00b0703600414200c11918002200a010100507a5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 121124415 1250 121123165 121123187
    0x80c0409050118271202070b030a021315020d050306010c021c051b010e100306030c0312020d03050403020c090402030f0709050115050a1b0219090b120c03120c10061203 74
    0x12007098140400c075843c284c5070801014000f03002549000f03020341d902d4000d1046500820380d44030300750f6892034004001402944089401002c00615200100e030310001040007080d0180e60350024402a410301070b060300d95070001001241085500011200140c50700302d8120800726001c555015140d45910340320b81000510741c03c1c610030511011a110340c0f680d000b048101201000d40b0401c0030b062072080f0450181202c1d40024000e038101000000410812034400248500160309032280c40401c3c44088042e100107407809001640000c0b12a046840d1403200103170000c0c4010100c40c90000040d030450304040036503005d07401742d991f560010001450030300e060003510049450240d00d8446010005000c00d8420b403400785103554903143c000c0464660348070028101d030b07000c008035882540d60703103215011b1b1030100310b070602a40c01c4c0405200101d6000400307200e54000240903080011030309070a54042d41000c1540f0180348a2030745603040b50718440c4500009031a550206c0b02003a01f0754100640500014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 121125665 1250 121124415 121124441
    0x1171c020c101d0607050708250e10030809010309060c02010207110901030803220221010b18010b09041409070302030d11030d0216050f0106170616080c0409050118 72
    0x107202c88903010400e1083d0b0301c02c2108111001c50722070034203003041407500c1da4a41120f03056102e083c1000650070901160455810f210b01c0e0001c2d110340c1c43e00c0c646448440191519101144010010300000d005440500610781040c50000380700082c07500e030303001070b0f400e032003140e40150b540018000207100702d20072030b007500c0c00301501c50131815459591444104e00c0003e01c10010103181c41a04e003050103035407a0b00d40340d440c2c0040071040e99208a101c0880032010f007020403030041d0f28014940303600b42041c121030f10200700c010700290300b940e29044103240d4a50280b8901c03030380182d44080c41000d00c0010110035000b00d6580000f0710080381540305041c94800c1801070401449102000100c50142c00421500e28190044000d17032214848600702402c1194103034010518000d40180407401081540a07400300e484100410b44040800c202cac250301ca51040d10740c0140e2044d04569200707942e0260791801e8029000c4180c07a45000c0d03560008104941d020381000e0008003050050001e811518003411181c0110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 121126915 1250 121125665 121125677
    0xd15050a080c06090108340807030509071a0409060e06090c180409020109030609060b0102060106091a03070c020306041a06042d1e0b0319020102030301171c020c10 72
    0x1101c0d00080040c0101c1e08424104000351002640a01280040f5660020524100c7d030040d86008a0505200000c006180c0007e0f1020000744069120340101809040118013034107540303050040c2c603640da071601e0580d01c3d12298200030024058102e4401e00c0010495200d81105030305000c000c1210310b102c05020490a800c0600283c18240211f03400940ca28004440004110070750340700588150240364405000940341107014401c1c400c954112001c030302c000f43d0036906a42c0c1c90b0602910003c0340d80c042d00100c10301c0315a180f001401560300650b04800d440c00c2c114410350881d800a4582042110210344420291000e4040f40301000c1c2030541001c821602840000a81c201411b8817141004210003900302209000c603010100f039014123144a513486464a40551406042015240c1e5a4409001e845400415010544c3e040005441981e0507400303949107903c4d00b011041c0788511000c0501c0c25005026280c03555440c05441035500b059141c010300145040d14041054a542d010b241c041130041c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 121128165 1250 121126915 121126933
    0x5010605030a140d08100909020a0e040f030905120d030f0e03040605070605130209040204020d1e0b010e040507081602030c0304060305010509060901061e05130f230105040b070501020d15050a08 85
    0xc5101e02c003040e02c0040c0c2002a40340c5ca00e000158032501c155000171040d00c1558144403d000743c2e074281c643c00ca806601c0f5060f441e9438410a114001e16400d1700360b0b0a0b50055092440030a1080d00700d00305808998030081541140081c001c1c1c1940d0040d404140822030010310042000100d01400d81d000340103d00007826042d05801003021031000500007440f503503002401540307001c40c82d440480802e480030200c00c00c8203098400e003001440d145031018003040c00e0003440b2100749401c2c081e4a11640c510340c2ea50301c1580314028110081c2c05e42003500029800b091206402c2014104043c2c0000c2c0f489680100c7e40d54540000c4c010302d4107014000c14029092180140308030717038100b1400f40800490000c5004903441300c0c00101c070316004040c0d0302c002c540580c0c000040d41131030001c0d240c0d0075a80c0034551000c040da15480321407080e4419020391404201c0c10301040250298041c007600315103001c0c800240c60a11510043c01c00c81c2c218101110150509007018480e5051440040c8042c0079040000c0c44203003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 121129415 1250 121128165 121128181
    0x10c14040b0a030504060914030306010210090206161712060f010c03080114060903030f030a051320130c020708100b06041406040b0307030903021b130905010605030a140d08 76
    0xc0300351282c610905888001044c00c00032207910031000d5540107041d07508400c0c40c01180c6522644152465401882204603628100d441403203102e00b07156004003100d1418802c00c00414200c80054016103a60100c042c0500c0b0303a01c90070000b0030300340348005500480f40c41c11004114190404804207410404141d401200007a003201c50581502c00c1c90082c40d402d0341c0c680001403503e201d01121150180800710b42c4040c172604500295000b18103a0405104968a0440c00381314585441c2c0041d017072a0f500c0c800c4001001c3c030100010a0260082d0629034002d0618243d02c0a9505140407140141d00130841000050410f10484c0c588464000d07007403084000c5400002e94602880c000e14003d1914843c0e103505a9540008407001060741405240d101d10789074a014000309683d07103064015024011440caa92030042407010104031000345100000070700040d1682c003c00c0000b00c1202e072503580d40c0c00402c40e65010052201007a01c901e080b104000511168241403102000d00c920611426105021880e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 121130665 1250 121129415 121129417
    0x702070602210714031c0906050106050702100f050706051e010f0b04050909160308120c070b01030f2a050406090e072310030f050906060105250c08010c14040b 70
    0x39084401050111321075103080707085115031110350085890080d644140078405811980d1b01d50b01030241003120b6030365104155024800e038140250702480402c0d4000505024010f42c0c09014074619140d07080000f182c1c0c1d4401150790079105421401000e0010492613400406514007504099030320304c95041c944040009940a0341c003d444c815801e000c00180001c5041109035407107015203650101c00c641d6410315010691112483c500000c15580000f41004101c20407250215400240303402d05a20359100e0090400703041008482ba14502490559495004000a01d003000e190300d501400c64604402c020032243c955106104845c2403a940d01008035020803204200d40c0b043e070300452441c1d4040200882d00c400400c0c159800200301c031440c0a15036065011810b401d0104204001c6500c40d0650f8503903601c002c0740c02a0014200f041161107040329519030701108046518000782d10b083c2070795038000ca42e40d10740150919030354075501e564080758045400304c1e00604c0ea180d4a494641031000b07003412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 121131915 1250 121130665 121130677
    0x180105150901141207060e0108090109050703080702010509150c1005040f030818010c0509040b0d0f03031d010203011d010e161409040e0a1115030a0c0c0506070207060221 75
    0x2800d000e43c41001191520b0030b404001001190541e40c1403034a40901814440d40c01c0000d600180c6808000b8020a00510030a00342d5130700f00c4010f015040ca10f660324002c99100c4d000407810014180400302c8192600794000068814240c0440c3e200c4031480503061402e41810200d1700198100028040032808410041da02503800d80380c4200a40d40d03015559440325403451001c107032503103048070001b05603038400c1c080c00703281000300d8050004100600030480d45034256030b405040a5804280140061300035400081c08103207002101300a21003801400b03089802c00d2348180140c08008420030307012000d552406000d4810110443c40c0c5003801d5140700c241081d807030106020300001e444410992240c3c18103035190208010810300448083c140d00c69160700891a084502e111a80d00e01887c0c1d26060324103480f101e4402800030b007190740e019a55405010700381c100e581440203e0207a5004583c06024080c8500140d40040448519001e0000e24110460740e41107003541008410307400e942186412200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 121133165 1250 121131915 121131929
    0x20d030b060906030a090b0a061a0a0203090108040c05060f0301030c08030703050a03020d1d0a060f0b012703051e06060d0317070905060d0e070e011518030605180105150901 76
    0x1d2617980700810607000300607690001d07001c0d1244d08100b056208d0f89030006016604d141104000228824502906c0c41c020000010b0158009201034000c0e0b501c1141e1003603026024424042c0c03820381c2c400110f10940c1c007c1c209500c0d19400040148244902d8400c10002000350200841c540740c0ea5460061107400340800620400d500016200e0b43d4001517045501d00340031480c0c0721400304099140c3d41c0d40c0d4400d2a0000c031601c5050070400120a0070390b100c2c40c00c0083c03043c2c4500b07485442c140320941d0b480c142c000d060714405aa511010000c11030800040076035901d4003003240b0843c1040444246880d2000300b02a1040b1081036181c00060f03845012214030402d95510400f03962580101501c003501c0c0b640006402810228200c08070034411b4014031001550002910700c811348800d821030407010240104d500c441050176003030f01c500d8031601c0c40d0f1060080900e0340c140090b0300d80d03a9200c1520001d030b8443e1200105d013646400e20304020312880342c204441100520401410b400807030203150052194038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 121134415 1250 121133165 121133167
    0x1509010f09090c031a0103050f0c0f040306060e0603070f0b04060503181c09080601050d02010f02030d051302040c0e130e0f12030a181a0a090501020c0d020d030b060906 74
    0x1110341d000d030720302102a00807800d040c8014a281d2000038001c05205490f0840b50310030b00814011035000b03114481c020f01101a16400c0f59854030b400420741d50ac0001d5800d00785104100c0080420380728030898000c1d02c5610080c0c0242d0038a14101441d204594000002060003414200301c1501d964003200c08503035076428182e03180d40c0c401d600c00d1006400340264134110f004800e20030001159001c103d02411680340c4400010b5a200c2400e20740c2c0c0d08013409999080403000d140e81d00950700417113085116400904c100c9290070380000020050b95400c0d12800310b580c414030b40240452400303024a41c40100c1b149440009000c074040051125040420142c00d500c2d96024011a80b0805002280b440604001110021802c410070036840e0303071044032501d084520344030044450400c1510b0001a25802c070800250402c0d9040e40c0341254040500044240f65039101c1140001c0c1003800a803041c12591782c080d129161070b18102a09051581c1021000c1502d405c410706043d540e8030003a19440343c3c06407445 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 121135665 1250 121134415 121134437
    0x2120907051203120705041e0504061d01030b06040608070e07080c25031b08041d010b0d15050907020d031d0a0b04110a0f0303030e0c010e0111100f060501020c150901 73
    0x40d105440340e43c21849940e2000e110041c54518030740b08c0d410845200b55410401aa51150020203098100d9550001c080c616801040440e0000b1070040e08242c0041000030360603079482e403c0e883c00344181d0003e040100850200b102c025009039600b98801c821612043c6802181c0032000644030314890804140200703403069405041c810381d070305060000009030b1104445105d040c58003240d0002d00c03500c103030141c0100d81450f20000508045040315a0010304609000040c2100c00103818030941482c3c10340028000000c690741c80e00d503e107000752150340140004000354200201039030b0440e0521600c008298850f1104541c0c0011020881074004040b000d241d1140c1c584030031035080503050103074088540320020501240365401801105e00caa141081249580c54849884086040c1c45d54041402000c03940740300d5028018002d103035884201560381641c0a05032032070440b030b42c881c4041c030059075500c0140103550301040f8469001c8411500301c00b0382c84030281d81d04c00d64403034801d000381003020340d8002d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 121136915 1250 121135665 121135667
    0xa0c1e0305100e1c020304030215090a0303030f0c0c05061f121b080d05030c0304021c060c110309090103081c0219030f090209040303110d021209070512031207 70
    0x1119014550010075074400128848407080501046001c4410034000c5035901c00e45203075002ca0101e01c0c0d074101d801031818285960208002c0d45540780001e00780e0002000054003965403192044081c41c825100001e684403032010305002c46800e142031109000d543c0d082500450000560a035008840b02404660001c10a122040e8005a64011002c41d01c0c0d03140b92034200240c012880e401e81e040000c400100ba540c2d0260300d65100c6401d4207200100310100081040709000400a5603c14009083c4441ca59104402c1100d4030b810207101f90707082641c42e4000e05465602c000d003c1c00001008004501f000f002c500010760b20307a01884000d01d2070b03c000582c1e1040303180710300c0943e070161a81c0808640b1100c5c000c0a000b510f030130300041c10000030b00d000d620581240080c0b01e040503481c0c003d00201d11607629507070309a000f098418800c403011282880303403199026041c00202004103001c44058140d04007041d01c1441c00f1800d030403483c4901c02c0c0150030303258120000151004a8204442c0790655101e81744 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 121138165 1250 121136915 121136969
    0x90105070e09270706080c0f0a0309020609130603050c030a03020309040506031608031206060406051207050f16050601080a020618010e040c031a010f02031606020919170a0c 76
    0x9441c8001c10740324518070f4007416001c102c09046a4079900e401c0400e55a184001c840740c80303031000403030145105000f1404002d100e603100415551001d0a03291a10301043d00041180e400e0407405504030f51200700a004015050101e5071000070280c0082031070308000d80d070203522801074280145c040c03566a00000d01c1c5640410690010307042c262503450b00c09071641303841505c0c2e601200c1ca40101c40707101d60116107203083c10310489044621540d074a070304000100c4456005528050860400c00a0a01c030940046e0340000040110308036041c401e150b039035003a290003401e0450590002d11150070810080001d40c54200884a01c03502003141c041e00344202c20016541440030303410840e086403410340303622502a05903001720f41c1540705040012200484100458160034074011500040c1c10500030600300990200ca4900c07110710442000d0309004217900403564002c800c02070064401604503003007005114601c40350490b44c041001504500c1c4407900c0314034203030a07940f003040d00d46000200320700d0301450343d65 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 121139415 1250 121138165 121138201
    0xf0302011209061d06100e1810020309010e0609060f0412091e0806090a2103020904090606030b0a1803210510060e01090e2d04080d05090105070e09 65
    0xd18104446600740d00c11145800c0713204402c02c0301780302c2e003004545040320f60100743c1c1c21540d184c500d042c0385a81d01e21425501044c0d070811122a44100c01c20341d42604602d0015510421b09140002150240410a14549600901000c643e9004041071000f000c0354040a1984141c01040d0308504440c40d5400312400034540c2c1c80303d001d01501e81450941e00065500c1e410881e031007281124074940b59106081d440b2120700750028150648462580d400e68154031000c1191070b41410014203156902000c101074034031000d000c40302c0350b5540c02c0a00030000140511900b01070345403001c1000003444221842a0852984041c007485405a40031259090300d1040c0b010302c0d81c14410501841c00c3c21400400540f40b513005490101b804c0500c19061540300d80b8100c0210307051500745180903202c071004401000c0d212902c19910342200c00281c0e000055610700ea50060344681401c3d036179011111054030032124083c19001c526410042485403c903800718a07400011300442d0925103607262840c0e1240c10401c20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 121140665 1250 121139415 121139423
    0x51f0903150f0f0b0d110102150405060a05010605070f1e08070b09010b040c080f100305030f130501031107020f0a1d0a0c030b0306040809041d0609070b040f0302011209 74
    0x190000c031400071240c0040b4030320780304260180b1040e11404901c41c103503040030030f10075045620f80440300046038020b01c03c4400490f0600598006009219111250610403102944c041d804442800615002840340f28010111850702a08114845c0e640e03036500048103401070400c10b0000d44181c0348103850350942080940c021305486e07444d012890301542100c401c6480341c980317500e050042c0465080500460700850b1096584640b40da642206400100c4000b82c0300412460041001000180303080005100d0066081d00b003d4450520b001c41d001c400d4520b0700014100750a140d680000b442c00c060507100020782c1129080b800f1840720303004c94624600382e8081070a84100904520304440710000c914010200c552041c400701c0d0307070154160150741c8a0000785800da44080c0005001c1800d01000d051004c0740101302007051103850000708105041441014125080801404500c1c03c1c200a2100108900c94205040c20f207091200d03004040c003407001070b040c0065070b803515510102d141d000708070281d40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 121141915 1250 121140665 121140683
    0x3040809040c031505100905040e10022715030711160b1e0414090406020f0d0606020d170c091908010b01110f0303041401090b0106020c04110301051f0903 68
    0x410400601800d014a02c1110513200194046002d052980040018100a03154804403038a880c0c00e02000b01680d0708404014080e03241006010701081c0010241d5620041c44440d022007880c1c52426400c01d108012031186c3c2d24104580644804e910940354402d000d41400c2d81c011580340130702410180a1110b0400811100c040810711035494000b904628065040080c80c9036060202680c0d903100744d00070a0000360b0680b4081107940380501c1e0442d0b200303208540c00b40c01c02c7d06001b44040b183d044140302903a00c85d2030710021b03c03107907070304000c0d4500c040900c0c40d01d0804007441000081142002901c8991042800640415144c440340003d603604021a400f03c041c2c0b0f951044400d00030020103980d2400920000c8000101e1440051444030960707040c0e010f5850340d110380e51303a41c0001c0c01c580305801840d521030078910f021a07401b081c180e0003010f0039006414440303000c80c100000c840d892001d420043c0d41c1440140496143d42c450080c1c0044511001e4500400f4100180c581e03070800d5000070030080e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 121143165 1250 121141915 121141931
    0x406020a110f01061805060d0215040902030a0504021c0c05010813020a170d05190807030905150108120a020c12030c060a0e010b0d0305090d020a0f0e16170c0304080904 74
    0x40b0552001d800c42d11142c00400311200c02c0748546094940a549650f80b03c4016120325000d4036141c00c0280c0c10321603610b01e8507c0e099582200d40c2c01d980003251b020244503581c008010035401c007201c1020801c070000e50890203441640e40c5003c403001c09030248070304104101d0005060042c0781003990b030310582c005200c410400d0790b403031200071904c5104900801d6801021500c50700c0c03a00070b400ba54030301e408051503024014580c100448440e040240b41504041d2035407180b0000c28402e0009045c03102044188400350760421511350b1038455031041c40843c2440070043d000d10a64007268070a090041241c60b6203111500300c151341d103140203c640c1e19130076004902c18001144034030341c07004184a1500e4001d101d090703410400c00c0311011001d030703015000c1441044814007603d440070a001c10b15200401112042e900c501c6e0780385422940360003a05005610b54240040b02e00310b501104410016451704402c100400002c2110b0090080c007215455030700800031070104401c2c1d4091f503d12001c00b900410040b6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 121144415 1250 121143165 121143193
    0xf02070602250308040b0601030213090209191202010e0f060a0c0c050a061d181003060f05040201020715030902030115180507021f0b0405040b06090f040201080406020a11 75
    0x9405040344040b0002101c194040e12210441100b0b561501a22241e50583d11501c40740c1c50010010102ea040507401c00c20700542e03011110303c94001c4c00c542e910050f110b000d10030900005640620307030b00e08900d10901c0f08010900708503500800c8a58203280003e0030400c60743c0800c01c0141040e0407654004c4003c1004c0c15650b500c1110700c503c3c0e6028035102140306503688240400a01c06010b41000203030240401002010078402c5881c01b0f10020b800400324004905000e400440242d81d00b0001c0d541c184c0d010418010346004610b5014a054000c01180c245076002079650001d0344605c100000b654002038007868060740c881c01000b900600203001c0342e4441d0400c0300804070540928418024030580300128a141071060a2280c8101c0c0c00070301d4030352000d4919540b00c210903408418600e855013024042601c80d03001d664040d510904103201903060503400c00040e290000d0000c80c0c40c141d40010040580e9100b0041c1d900325421080c0141e0794111a1421250642020340c1582c89108402e00e01c1d10074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 121145665 1250 121144415 121144417
    0x100e0a0b0a1e0905010f020307020d0c05030f070b120c13090203040201110604170327060a1b0c1e02060a0804020a08012c01270302190305160201030f02070602 70
    0x4907210b81c0d607030146511200c10b01803800c40c01d00e6102c0c00a920140103203c11350049411540020075070040700d081c122a90f0003d0081390155000719140841c0c10382c10070280c281000080962100a00904610390800b01e83c81000d004000f50640140341100115041d40320503401c07120892a88c2c50080602600c6588140c060b61058038100c1c001003140c0e002012420f008541c8a00941c2e000b103486601c40c65400100f4000e80000d0701e403070300390341c0e5030300b00d0404800c1ca00d640342c038045103014043c200c0d900d0300c11100c408440d00542d08614010030300c0c0e20352103001d80c001d088203041a0b115440d800200c0311021900310481551800a4121100040f84640150000d220620840c400c680700050282c4888516080e214940440049031a04508140082d80342907010143d44201c0c40c000550f80d645640103049003860024104c80030b250b122a150145641485840e01d0001c004c075041070302c3c1c002c0b80e070020a5441900c030550040004809074104580c40f9070003924007034211500943d181c850b103091210007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 121146915 1250 121145665 121145677
    0x11040f0b04050a060518010e011101060801090506011a03070c1a0a0207060e07050f06070203030d060612050106050306090c07060b03030a030e0708060403020d081510090e06030a050309100e0a0b 85
    0x810030307404034002900c030711982c12034811b00140a82c40c07014860820040d075070490001405070520040c40d85030500c996003485030760010008000085101025400c2c0f040c00e200c010b03040308102440d8204c81d1041d142c259070031690403241e2803800160902180c1041c4650700140d016015044807080184144c441c00c4e500900021400f81004000031554030201031742d10344042c82495040805002c5c0c7c400c40c1d18110303000d410014009010f803850203070709070310b804212031068203c000460b580150313403c6485c01c0340c414035000d0300107424801c0c035508240c000603540446c01440e0104585000a02c442080b00300e4100d42400e03500502141d4503007400c1d400c060090024070f10920004d200b0003a000070790380070000d151030045030180c01902d8000714503d000c840d000001840740141341d10b124520005a25148408069010166240314519084c6661781840c00c9014040520903481123910802050307020040324100c0c0300c200c440500c00240001c0c103450035544e00400341d510540c0d000c00091011250401007170 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 121148165 1250 121146915 121146919
    0xc03320301060e0307080d0e0a0b0304030804050d0302091c020103090c060e1e0a051207033c1a150301090f03030b010c0c0e0705040e1905060307030b0a11040f0b0405 73
    0x1075500c1c0310004d00d5621240d5100c1c0d5015980102e204030344290158200170821900903110076610760f207810603c0541d60081c2d0b021030010708060300700402d1003414460b80400328100e180a51821240c0800541d01072580420f00400426901d040d10441e030095008401441d445007030340e882d03030395200005050b00f07400b403090368015030140f4170341840d06566451090300340c13800070b10b04540c45061000b400200c01080d45143e10b1132048407404008124000c002300841c80f00c000403804145507840c0701c0e03c4006040314801c807840c00900000800954040b41420306120490080102c0c1d40d00d100d443ca85403120756055507059481d110b900e5040c0420441401d0900d4000c0e20103001030b4040301c00450b001d59401d04040c18000000c00305220a0000d8a203150700141e0900c1c2081c2450788032454055000c0059075561600c0708005181192820103005072607200c40c040b4050b01045295854080f1001c80040c0542d07400c1d556004604600d420540c20758015108240040c20300c2610f4848120880e40b190040358 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 121149415 1250 121148165 121148177
    0x9031b01080106051c05040203010e031801170103030c0f0602091e09010e0f070c0f02060f030a060501020f030d23010e04030206060405150f0a05060316030513030c0332030106 77
    0x3c9641c50142040b280014401070014800d84c40c070900c00c50013082c001e4412640355403500b0650342d0001c07080028000501303034580d09080c0c6070005030008d040600103124010b6985c000c0b200400109810581074100640c0002101c0400c00c00c61170928001d104000c140744c0d001624003440da0360002031609107030b0403440699101d46640d0721000741c1e1040120480e50300c40c040ba400070024044030301c2841064940d500c070f071106415240d190341c006006a003280d118540d11340030110030029140c116001d041c1c0208000c0c00a010340440701d8010b15207d104100c00300001c0350302c41814018003005145604280a04007100103100c1d611544500e609440541c0d007500188910f0340891060310f401d00c02c190040310b140351081d1511071220184203c03000001c001c00e900c1046200d0000702911034200652052203200c0350084103c4011310003034121440030b4031142c0842c4c01c240c84e10380007c1c0c1002c4071041d0190142045040d001c1d00803920680c2e0840207900d0182101d01c2c034064080141d0900c05503041e141355031581 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 121150665 1250 121149415 121149419
    0x15120e0f0f0c0f06070f1a0a0f0903050a0c240203040c0f0609050904030302120a1d010501050a0b0903030706090302010b0a08060f0118020702030304030f031b0b01031709031b010801 80
    0xc0e82c031456411901c2e030000e4110042d40d0f03580f6054004101141c8900b00320206141302e901c4400308208450803080d00401603404001c4060442d100700002e4a018480030011150240c034000c1150180203a100240b00480500d03805001202e44030708101c00a0680c640c4580348445900b8020350070607a01125902c1c1e9401012441d0204420010141e079403c2e80c540010901c2c01341004411a00603000381c05240d4200101e0820b1169585418400d42c40c200e80030a80003590041c2c0246080c05a840c618280d02d4400103003c3c0340c4d80c4c0d141c20b40403542d0500c081d5840d4541100001e0a42c440c0d60001400b151034280c10f0f00c06c1603010b40011511080407a610542d17581e80307014041c2c0b5110100c0313140c10b00680000051061004004071003e290710503000060a0400c0e03076006c42c0c5541d0203900282c40c60400003480004040e400900c2108280c5520a000c52410b20b50703407903440b80c16041c08010088225092002000e8161078282c0300842402011248021007a80b00b1440141100c004140050200703400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 121151915 1250 121150665 121150693
    0x20a050a060203030705031806040f031e050414030304080a060b0306060103090b3c0a0606020304060c0305030702100906020c0c0f030709150f080d02010c0c08030115120e0f 76
    0x4030040320400d801039440c40c2e072410310898456100400c00d113095081c2c22001c40154604010681c80b640c440d81508050103010700b00600607280a044080c070301101c8080342e0041c0e5a1144c151412600c0f00f02c01034101c00745401c0000c0c11802280c01140140c8210940721080c810907802c100da01504c1a002d607902c03038903071000460503a009004042c1c04812230101040c004161040d040420100c519010014400c002c01c1c0036182e8070702c19001346024000c0f40d0070310400046074881c0d1002008180011440d041c41c016025241c40300a080140922070003000044d007440c024400305c0e207615816182000b544510303141010080d0804148544c052041103194846400c0002c0c1d2410102c90041c01070813310715080b66500a420710100d078074421481908005500724999600740080d1120601070324040c401050001e01715002c5a404104001c5c07210b420501050111048905540c800703240c80d00c0c41c012240c001e0340d07000070200000349030600c0d20341c0b4446800404100101d0b60790411041e180c842c1e002d0301d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 121153165 1250 121151915 121151929
    0x50a0b0306031507210b061602040605040c0e031006060e2107121109190e0a051507080916030303020309011d1605120706080402010c0b070c030e030f0c1e0d0c03020a05 74
    0xc21b03140c201d0401c1124000c0c000b0f0401c05200c1c1180300600c007240044c1c0f0742000c00c0503109028160000314000600209181c40c0610001080101d42c01341081024a040fa0040c10000d0400c2494012003c490816601c0c1d0140d541c03004049949030101c401840c0d4031400e60108031440c22051702c107410b884185120701d1400d0310a15000e90030f19440081d406820b0003181c030050044c6104200248100340c0b61100080090040040c41c0c504108690800c1c41d02d1640a00b2070031000340310503095008402403124461140c801c0d01c0c10341e43c06190042e02c036a100e8500300e00500007a1000e00d80c0c1c2c000c1943d1031450640004001803440d422032441000c0c55911001d1207202d07201c048036548150800d06e420300043d0f01c1540c01e50781c0180145400f0251f1685511003401514007603a4110001705000a250141034002c1e1b0740e0030f0882c0043d4010030311031085a000903114400c90541600c99807100028442e021169003156000b61402800c02d68000321394035080e81d4244092000b00d019402003c2d0015651030080303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 121154415 1250 121153165 121153181
    0x1608031611060a0f02070b0c070b09030f0f0310030b0f240105070204020706020f030a021305011704060e0309060a121107020d0611070c080d02010b0a050a0b030603150721 75
    0x3100422181c1c0743e8504030001340c0140c418400e181e0744e0038010900400d85a118990140300a0659280d6880c4a418164880e2500a1000321140c0c01000500384800190044910504200e0b2040d41c403a107801006805100f1594405021610703480d061200071441620349502850020540200321841040e030810516262036580307000c62400d011850260519070010001d040c41407900515000c44090100e9040d001138403003091013039011030302a50440810143c00c02421007420100312210440800455041c001403004000719150b03100c1045001040040d02c94009004010b070307440d240d020100505850202e0340f651005800e103c0080c1c0610464400c54021607005884c5401030121a185c1d100034001140150351007502c01c00030540801d250301400c0d0098003904000c3c02c205001312200a00351403007450b690340309000d90710080010b55141d003050400c6481c1c114445460780e44800000b400c003403003452144001c1804804101c6030a42c441d200712240d145405215010318207007140003086903080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 121155665 1250 121154415 121154447
    0xf020d1b12080a0b12030d0207110423091603060c090b03160207050904020a06110c031603021801081c1b03170702030c060105090406091502030615070b0a0203040816080316 76
    0x2c001605000307c2c4e64000b80790903401179542c22030300d0f08e01d00301003000c59580000c082480d05014011b002c004050030450b80c0c00000ca50024802914604501000c2c55082c0c48000d0489503140d10402555014280300030090240015464492400300c819a0014100088003030050141c80000f25052400050150107640c005d4010040f032070401c4400e0b100800035030340000f800d20030140c3c000c0503550f0801171440b200d840c0310b000380c44152461043c8540040c0194501c0111121b000040c407a644000406007043e035000000c1480860b203804007a00e030002d400e04800e6682814041807002e154022803540b10a1294a004100641e00c10000b281c40b4011240082040e4010b41c0c010020381ca0b00300c81c101c0c0c00a008500010300c2d6081c40da140526401400f004039a02e0b5008810400c1610f020314003d0100c0701d9040d400c500d0200103503210914040c0c0103008000b42e82c5c0c00700c0820180308840060300c40da21603040424a00050904009411381c0007190b03401c540310f400092082d4404d10540c5d00d60009014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 121156915 1250 121155665 121155667
    0x80d0e010e060f040f0b0a1401170c0f010e0a030b060f010c0809012f0105070206070c0506040f0807020d06060315020405010c1211150402040605010f020d1b12080a0b1203 75
    0x1803000f15000c028020380f0a6510003000c82ca00344c081040c280d0120b009111015002500030f810030503407211010f05a124010581401d005201803d03008189030600803000c44955080102620051300c0104202580d281c11007990071011040142c0c5460083c0203c60131901340f004011654011610240e65003401084003000313010007032565010f4148194410355039800c0c04503072032008810141c1c1c5403409036291000ea44400501c02035039010b20003c4e4109425142c103009060b0f094031410f941d00c8010f84010414107000c2100e009100b00c1c0d009940400390300806401c00c401072270400e20090f2034540000e4a090a0700d518100904d002c51007103404980381038440fa00c424520341c851414040c200c1f60351300d0610041e00d8101c12404020300c4400d20f03400c101e80c41079038541498014801100d095400040c1401a040c91b006034031a00010100c880b440d061602e0040203c8032450b508441c500c200c0028000b030010040c103070a85800c00c024a00c65411502c041180d41540000c010f018440c045c046013191300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 121158165 1250 121156915 121156921
    0xa0501050901020406210b060c06150603060102150901020c01180c0e191d0601080a03120c050f07080708040f030b09011a010c020301020417030405090106090b090f01030b0409080d0e010e06 83
    0xb00708001c580003440b80500004035545047e01051080c2d0045800c924941c00c40400c10042d0a1042c11755000c21401b61115401e5290090000c0c0d55044c005055030906514000002c8001e1400d404540d00e1940c40d4000307100b0880c55070380e503549022000604840074544401c001c00c1a00001021038440e80d40d12a0002c21042c030b00403240010b120501e007244502d205000903090603d01000200e0007014028000c040784945410b00920003108600c402c102c10b420102e80380301e1981e00c02c0945111042084c41b0b80d503207009528100441d4418034a000b005440041000038030540c40000f0320040ba801401c084000da903a400c5d526080b2071508981c244480e800c3c0718002c140d0f5100d800740040903440135000501e40798403480321040400c0c25060510150b80001400c0c003607420b080300154010030860030700f01110b030b05141443d0740600030440356a0003440c0001140900d81c1c443d4206210b46138000d04200034201c1c403410006800e5011448060400381491800c5594600512a60300c01524800140626403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 121159415 1250 121158165 121158197
    0x50c0103090224030106200d11160305010204061103070203071802120103051e0a0f080a031407030b040614010207030611040305030c0610060903080909270a0501050901020406 77
    0x20507088801d0b41c01c80000b600c0c02802d2000300c0a545140e80403d2000ca0704c0e036251000042c00303460490000b681003102e0181c0c141258600084c0d0088240030f03414a401f18003004d101940c6041c00308001e800d034240d1703445000800c0c00010f41c020416210319039580b04031000c070b00039400c2d5a0310444c00025050740c018041040b04601100828101950400015245c22846103040708481070a0300141c5103070304525003a000c001050070005e41504500005007890341900e4541144040700c40354064404900000e082c81640c3c800d6018070109842007180e04500d00703006000400400b08280114021490040c001c40d54902040042c004001d050b40200343d85401d694402e00980000c0320031019405044c4400300c002001070000d0a10181c040008101507c4c04140744100c2d02a140e02440520008031007c2c00440c02040850711410001c0da080413194941c0e009903c0020005090003022040d20304060706040c0012a1480050f402080203000d981c55680265080b8031481c030032507000c2081948200c1c03443d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 121160665 1250 121159415 121159421
    0xa0e0c0a0f02030d060305010e01050601030608030a0f02010b0a080d091a0904020f0d14040303060b1c020c0f010c02070305150f0610020316080301030204150b180a08030a03061d04050c0103 83
    0x180d074461040d241018151070301c00302520002d4104480d180d454135000200100248500340e4030003001d1a050000e6440c0412003510b0f0321504294108114194408107a054000d40100d000389001501c03032642e8550342e10010b901c985804203204009440c0e0301c40010000c03846d8000005040915601d5032400ca20042000025407040c40f40101e01c41040c045102c16040328810070084c1c45a04410710141d00c0c0a1030003c040f034090381c05c01c2213155414010100c901d03411842440000318a400016510480035203014500490700700f40c0c3c80598240024100a142d000c514a02282d01c108115400701c1b07a0344000c1b1310200c00031103580404280d80700020700d007440c000030801815a40d03401030364034100040000040c0390015200a44e6a410000f0041045060511405844218000e0040b1800c0e003001040d2456204060303c60b440c1e0649045010743ca0b0381c1d904000e100910144007107a0b61000c81c1d8201801401403840348619416044070340c40e070503d00e0710441c00c1c42181c0c0709025141c1d54610303070019401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 121161915 1250 121160665 121160687
    0x71d0a051905040905250b0d11190509100c0203120310030506240103022b021b010c0809060106081603110307120b0312030609040f0b04080301050a0e0c0a 68
    0x101840540000b115107452154600c102e0003440640b9600507030502c00090014903909600350301035100750411074a10028203440008103103490200d40f80701e02602c4480c441c040c07038240c00409154401d011200325003000080ca48000142e03803054802100700401d550071034454a010350581c120000303032004070505200640c0d028040d445001412030300ea032074040c0741000071100100121103040520100001070410402042c00c240782c19032500116010800e11618420341380b502d181014501641c40301500d4044e903506801c01040002c078441100402c0380640550321040c0041440c1c03202203440010301040a5040e548661100f00f6603465484040b040441d5121081d400c1540d01c642d0440b81080d070300002d501070203003556a04004001445401c040300d08402c036140c0b081e0b11420f000540c4403200001e032680654200c600614954032810445601d030695100102040d40b00d00800040040320b501641c1a110262281106540c0310000031403000b000342c0d44100882800c0c041034889503c102c140c0c140d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 121163165 1250 121161915 121161949
    0xa150e040201020a1208040209010504020304030e0f0f120c0909121c0204050d030503040b10060e060904090b0f0411010c080906070f050d03090501050a020906040302060a020304120b071d0a05 84
    0x4954103058848026170101a092880021154001c0c04250f10308801c03890302500d0120740440c030314142590080c000c65501d10a90303001d00c1c803a03000407005503190080c52900480260100ca00210310031045070700e501c8007000182c40b6640300400300e18002c60010304d2031f0012500300c558070f250004008c0b1005061084088040103d5000c000100343e60300d900450700c0141d4031a845050b12401c0510f401c00110100404022034443c46030810040903a0112803903504007000d44145640764401400708010b4018000050100585241840813010713500006034412402071403100c0b8041200c030011160b0070704120000c2e24400090040003c10300d80b080c0100380700e078842c0d01240191801d69403001e050050079a204030110342c2d46c01109003817201c00c0c081e4942c4480d62078070845c40c1070304020008010703010318000a4042d000119104030094000c00864007c0d00e80040948800000c61030000c08225080b990030001038991050444000540902e03c140d403135000702640400c80c01c1c030b4180200c0c54190780702c81e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 121164415 1250 121163165 121163173
    0x2f03030115120b090403210908070b06090603060c13030503042c070f030506180708070e040b090109110c011a0a08190b06041d030d0c0c330213050103050a150e04020102 74
    0x1800e46210300c589068213200f0301144e40c44ad9043e040010302c201c00140100e00078000241040b8803558003180c0c055001030700c0091079844003030460a1307076070011058100900070312001801103050040c8030464411070036003181c40440480041c17600003440005a0340c201c003040c00103520300e0b207041c043d030011a4401c5001d01000010207010b100480309d104140c034080041000070b424008102c1c0d000300f000c510780c50260b9043c04000d84210108808003414454030540c50380d1100480c50382072032641102c00b102c0303d1000900205e0750000f409020545858a2a81300c2d00c94071500246007000411107441d0720710204071007240b0180686442000a80042c103855100f60b0b01c000364103d2400301c1e19510390640c0c1d075400840d100da41000000c0b08842080e0139101c01c5c0044074200d41c00151842e0602107245e070b0300c21080c2a2180d0070701c461001c1e18030000c03a0494843c0c0089113218185407a480031000700c0d0001d9805100075151a80a68220b4040f540c91f0429241c02050910140c8044d11031aa005032040c4112 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 121165665 1250 121164415 121164467
    0x40f02070515061c0b040803100f060807090905010509040609110406060306050f0102010e06070c1703070203120604290312040b03252f03030115120b090403 69
    0xb4108460704190b9a000c1d20600c090100e641803a00185070841a4a040900d5001e06030b100d88690240007000203020b010300000003100d582410500500030641c0d5213054000e540c65040103045107104841e030314001480c4c0000051000c0250150a04846019011107596241d41d1035035000f6100300720703040d41c1e10a00c14500140170b0703c072440349800400d00c55030001012170a120402c070400030f0301c204250441e818503100380041a408624650803103200d0512006000142c40c040406488000101d400d501d80842002074103030300032008040b80252030f980701c030f6140d4540382040200e4042e121010750550038480c412010150100c0c1660080b08010304452522440c3c0c440030751140e009801c4030f800c2c1d82c8003006100b60740b90328600445810355024440380d056110f41030b000308030041d144075103205100c0080341c0009600d046000d0320644414075045d44d94079a1690520350400322010801c20028400359042c201180503481031840343c80340241008003603191174400b241d42004000c600181e00c005c00c664 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 121166915 1250 121165665 121165673
    0x31a040b012c0a09050f0604020a060810030203070608040510060b0301060f090806090706020f010c08060d1e0303150f031709060d0e072310030e0c04020711030c0604080705040f0207 80
    0x503610500540c840481c0d00c941c0d9141007400c11841214a086d1540a0405d1000596075270303000d90140c60062901d0107440d0740e805440c0e0884a0254406034042c0914600420381e6640500198800d0b07024008407611042010284c0c404c80740a84684600114140014801300c2d1041040454000580c035144680540781c108250408c00c06030b910943c140c3c8a000c2c100302c125010b02141e03c101040a000700042030480c10042c0c14000300408044c0f00c6c5003460455010000580b82d4990154045013204142d4030032458060000c020b00340094045528000c0001001c0d088155181c0503680e000194152038608050111142d4006840c12548544240b002012948241c030505900d0000000241500e034076000880f91400d00944103400d001d011002045195218071080d11105021340c540003842d250882c82260070a840b100c01c59911600006582003444820030613018400b00860070380343c4400308042000302a02c914402c08030341d600510b004014902d016440304425140b908005131a090300e940d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 121168165 1250 121166915 121166999
    0x7080103080a02031b07062006060f150d060302090c0705030f1e07030f031428022208010e0604050a1709060703030c030c090f0b0711040c0207031a040b01 68
    0x172042d4081d800701008200c00c0307034405040e11002121340f507c3c00d803005a268581d5142c9400410450003400000c50101407600c075442900100d600710400144c4a812400c101c5c009000107100503032180300c10300c0c003181c988081c1c0c20468440c10b1b07000000710b20f8400040001031164010028000310110070800b900d20340041c0c1c600070b051441c804d999041581c10281005811114100c1449443d51882d404114107850301100f0108881003403c1c1541c1028440342940b000ba1080c8075021305038038501c549104410481580900c01e43d06580024495400c0d4240110740ea10300860703001c0d0007984050309803004504c0d02c443c106d0000255040440c5401d4000c1d0106c1d02c5c0c0c0d4480076040780082d643e03045541c180390b8140300f40710a800003490301d040d450380340268510018116000e11002040000f80d011308104468040400694001d0001d1100049909001e525030034030b8803095070340080b01c001d020a9101070100a92055a016040034256420451201e881007222924198a01d040c900758a0942c14006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 121169415 1250 121168165 121168207
    0xb04061d0a06080f0114090c03180f0106060305010e0c03040212070308072306010303020721120302030115050c100c020a02120f0c0402040e07052101030c0303080f07080103080a0203 80
    0x14030340c0c04441c10601081810390300c0581c1b1920005100f004125220b980d0303602e00f00c0c3c00031500c12020b0349a8541e00d26450a145e2603000400b4079111300340b581c0001d00c0c419001101143d445480c20085603a1700c004801d044e08044521003141002040002c006190825040440209660442d80c18948a903249401680000d0b82900c1381d200382c0c1100c14824418040f80780040c030504028104a514669000c1c9d5070700058000c0000b4044038140380e5076102020240c0d804203e400a5411900c0300660b2005402075000703018070a6038001800715800b01d580100115020700000600910b110204410800d00507c100c034070075030450050401c0040540e444954078402e454403000980301d00b50030000b066190904500d13500c0c4c01a401804108081100419403503801750690406131b030f4a29102e2400e010241014540b51014280c940011090201e00d04c805400c0c1e03407007900c410000c7d40f01c181c814900c0010031507010000900b0100180001607079100a000048500d00450742040b0500000c001c4296000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 121170665 1250 121169415 121169417
    0xd0f050d021c060b09011202090f0306010314061003080415030f0e06090c1c020f011107080d0f0527060d090302010911040204050d14030706050109090c0e010b04061d0a06 75
    0x121500344491200f445080d005150b40070949141c071711341070006092580210b02810040b0342c0030882e50800c0c0c480c14428000c400d0000c090b6422036851b0714080c0000d80e00045030043c0c502c82c60001410510607000e090781a0703508a2402c0f41000e2602400d54800003801f203086c020035480b060400076002c0d080c05658400786c04440600340c185000700102d40f0f481700c030b840d0b82e61040d000003654240d80c40120309448030290b01520840c0302c54400c440180c40003010381c03810202d507114082002580a070013080f04042040f06d5135611000a202e00012a964003846036503601a407039004410444a047d03248007003041c040980514240b144100058088603d0780905801503516029841c1c00c000c2000000315400c01e049800314101030921021a4007038100c0d410003400a10180034828101c4420030a170390006600840a01c82e070368540c50008050180c0c060b00b1946034204a202084400c5203211040c182d0b00c51103026400c1c0351629804580c030900765204c10340c03512001d40714041c603503c075115010050701003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 121171915 1250 121170665 121170697
    0x11030c09010e0103051306180b1f050904080d18080a020c0a0b07050d080a0f0513050d090b16020609061306080c090d021302130e0106120e0d0f050d02 66
    0x16030300090403450321080e00504040c9400100065074810900700c958441c0c00c40d0001030006000311540c142c41c50240070140810919a0401944516045a0031071900503032218500e03003036580051007002c58040e0340003040000180001c8440c01c0c8103174001e20504c150441d04624040041d05c0f000d4035580146070b150700580251038442d00c04e040c5180113600410035814568900402511043d40324a0500c1c07010003005207032000314910107803a81100a00042c245020041d50804840c02c00840079031304c0007107519001b17121249041c02c0c00b622380001100e01600d03003a444d00b40ca00e00060078005031b11804a91002e02072060343e1a540740e000141c900c5401020b00b560381141084809095154010700850110504002a8480d0b031a6030034960380b4654180d40c2402d925601e900e07450060300070040e1481e0074019a810014440001c800c005040742e5882d254851450000d004400c10b80d442c0413580d002d9648180410050341c3c3c440d000051240c02e042c0303020b50400c45100a00c4d8140c4e0701c10400510240301c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 121173165 1250 121171915 121171927
    0x12080718080615030f0d05030c0f030901060e0105040903080f070c0b0a02090406080f030919031203050a1803020a0206030612070f060f05040501020c04091509030507060b03060f16020111030c 84
    0x34119183c0c2820280407401045410030821641c2e03510041c14442904000e00800401c4200c0c0b00c240a072450680b910a50680700d10b40865018003d100da44540002000d403a000002d840c2885c0c41400c2d1401d8065486e200241d413054040b0b103400101819003802c00003144400c00c0464190314a0b18081ca90100c00540c5d80d07a0607108004c1591030b00d82280744660040da0308003035600030001c11100003030b01c1907500355070303c0d802408045000c15035070740094003e583d002203142e40c465241d44664070412050208010b45040c818482510220b4503030000c000d64002e400e04000361074464042e50f4080c00040c03e6003009541802910b080c079805910044900c1401c5c0028800d0903000710041f06840d03114a8a0380c00c00b4503180000350f550106070001400b46681e00c0f0400c0600140510401003991455000d2203894000c0c9001411a4403055042d80c07000e00e8421814510b2501142c00c41c00b5030b0000100c850b0a4480f402c1e07002100e242141c4110075076503500a005c0c0e034641080040c612909580c044161548 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 121174415 1250 121173165 121173181
    0x402010c0636061a0109090b030c130219090f0b03130203160e060303030f0a09260405040506060f0405010f0c051203041b0f06050d021303061509020403120807180806 73
    0x20003068611a002440409001301643c0c40f010040031034001290215504034000b000c40d05142c00402c19540203d1043c0c0058450b034011b40080913000318900650504e00402d6000712003641d514011810101c008110400003100316001a40e0410b10400c02004c0d08200e581c000b91600d0490401c0001c080d603042c4d01040007049010b2000da06c004158060343c91407804001160b4103c0d0000e0800d1003c0341d07140021000c0c0202d142c525100e8140742c1e41000d070f1010105884054640141c4501d0340304508041c0018550700f0004140c0d00000000e1800a003018203201c01555246107040c02c40302042007050880303010441c20804082c034031121035031066880c00c2c03030b05080c104581030101c0400710140340c8800300720341c108860044007106e50ba03182054407582c888106202a101c0c801500805017820100403007400007942c0301030150a40401d454045c26034500c1c01c43d09034003480c8405801c6c1d10600e1125980c2c14007a0708000da00c041289080c605190820044c4800514071f500002da0692104003041982c0e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 121175665 1250 121174415 121174421
    0x20c1926030c070210110106080705040b0406080c01030b01110d1d010806010c1101090803030a02090f09010b09040f0f0f0f0f0e070b0708040b030a20030402010c063606 74
    0x8001081900786503280a0700c0e585030b03c0c4104180240101c4800100b010460f20070505540c001840600a1007550f0755030072810342d00e0b46c860007400d00c1280b4003290110507240c10f03c0703003004803a1040301415046014000650042920490381c0303046c0400314494a0601000b80300c003011082d810f444040754040000004007020940d02141c1d0305000081049c09090b80c0c024000003005540320116090820700a001214203d4040e80540c161380300200600a048060303401518084409940c2d108144caa40e00811440050038864401740b001c08025085050174503800c5084141410b9601180d00040c1546c0142110710030400050315039929500751040c00d40a0150b9a40122244400e2048000340b0141e2030701c0b43c7c0c1c1d51140e03a5214000003000c03410000c0100580707004100c02102e4541720314003003120708040c01c10001c2070101f0442825025a1002005003503031b005035010b0f035a0100403110b030b41e1500010000f41058082580940b03004444100380a80da041d0464201414180c0240c0c107480c0c92000d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 121176915 1250 121175665 121175723
    0x903120403030f0f0912020f04020d06030f0515100603050703090812190b0a0e0907050301090503030a0501060f0509010c0f0503030c07150b09160306051003270c09020c19 75
    0xc00410540400203249030116070141c00760101d4072a5100c2d074423040020000c0c4642078548404500f0104000b00340420000c41028680c080c0701594106070307006c0e0505000785401c440409549401c81420b01c0b2692080e0300a80d400034250600103008500342c0c030b07008450340042891904445046040042c0d00c0c4804a002000d280484d400f44220660710000604502c614001d81c462040340c08001605540104a0100103010240081290080505041e80c40c0c2c3d0046500205407400e0200024107103209030003825000240b0b03603c05040528040045490446810040d91401d4148840c00003041017032004601880110344682d5a840d10307450800341c0c1810300d03d20032044514020104000380c5400860ba90311111038101902042c1d4071450607002400aa004182c00909102c0b8600d500c9803d1f501039003c0080c01160140708401c8800644246602020700800c2540914010080204660054059040e688094034a900030030000940742d1280c0e9081640c284281303048421107ea951030b008a1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 121178165 1250 121176915 121176917
    0x4030924020120040614040302040203070507050f0a1709060c010c0f021e060105040b0d05060103050a03030513020109031704050310022101030c050607020d0501150302010e0102210903120403030f0f 87
    0x100c0102c088246410b0b501807440b924060110910603078046400200451f0060740e4010411904ca0800b104002d00d81e070000da4003224036205500741900c0394400010500e241d5640002c0c0c0c20990908050f0034080b6402c40215680c200205000e901ca04c10400c1c0a16400c0740b0f40707540c4007140c807598840c0081c07030102c0180440c0c00c0192400040c10700c034000807072141d040d42c20a44001c0740c5525140042451070000a4015103c0d005141c004410840042024070040740241d85c00e0103203803525404405d0700301030104001d01246102c402003001641d440001c00c00b24016040c0c3c641425540c0e000319061041410b0140304d110780c0042c0c520301c1caa40d88a45c0607043c80d22036400b405290f0542d0344494031514203028442c4504800b0504d0011540c486d0815488213600c08024050b9050707950fa0141d00403418042207000c564615442e5070703035520006410040070544d5131503420440d070114602201e9400b003850982c05002d0302c3c030820f1042e84030800410095109a0300ca981c0302d80301410042034031000f031910300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 121179415 1250 121178165 121178201
    0x140102071b062a17040b0a031d0312040c050409050717030c030d0908040b16050f120d05060a081507021203060f040203090a061d0708030a05030f040309240201 70
    0x1201c05000c20402048006818840031048183e60418010b0308003490070b943c1580000081c08540c05141c1e50241494040707513101489480046444104c2c0300d06030000e13078030580d4424004202031103100e60a03640c102e4061440c4180ea140c9400c04182a6400820151b98603445802c041025003d1550814138503000c0002850074840403402d05034403071003480e4070184d070799842d5021a8180002c0e182154024043c00310082d995405400c1c044074004401002540c80d400b52024820381c021003ca41201569105c0840c42d26241110200400405002c0d05c901d420800540340404c601c42c08200c1d000f0750f1142c2189001092400e41002460f0041c07201c140404110240306021494882c040c5c02642d007a4200e0f40945c491b56440704d85442e102c40320401800c250b00f81103070b0301210404601024001080c0505441480c0c0d02c500055650303100356800070001810402c00210f045a13151001600903102e03190054000c0e42d587d407032030f14155141103041c000250b1408400002902407207000042800440320b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 121180665 1250 121179415 121179437
    0xc0301050702070501050d020d02040f140f060f16060606031527050403050d060603150b0f0706090f0501021c0c0c03080c2a0609010b01110a060207140102071b06 71
    0x94580314140320b464140540451a074580c551fa1b901580d82c5403002240854071243d5508080a19071024800e0305c8104001e121051018100208804c0d41d80d0303800740c110382ca884402d6180e4555a440350110b0000120001103482c001041c2e40104030007004540d42c0031400c0201c4889449440044c0d910501c2c0c2c981c1c00b4585600d0f81e80741c520300b0042c40510703e50000354640d1181000e9480d4443d00301c0c5480081e03d0280c01141423500b540c03003c2ea500f0640c045000881361603031a02000303440707800c0070425080021f200d07a80005411703800914459105000c6a50084490358829003681c1120150001c0000342510082805003980b0550594404038903064050200340e45000d0000d18018040920150000800d01c071071480603401180ca02c0c0e01c0c0310380b80f900e40c01d00411450f2030740815103034030001d5400c0080b048240d600c242c01e45003081c5040b0000d0141843c2c1c6948110081d40044021201042e014880281401081c4080d001c5280500340c1c44120364030850311162441c001d0f41004043c03007015008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 121181915 1250 121180665 121180667
    0x60106080703050c3c0a09050f1c0602030a0c09051f02070b040b030f0906040203100c020a15090203062203030b1f110c01020106120318090c020f0c03010507 69
    0x11864222419090000e241e4a40c1e6450004c144502004042c51084440b50010020f1000c25010112189185c1c1c0591a0302d2074805141c2d030303204141c0d24000140081e03c040c0082d01d00758100703200d016801401003041c0201814a0034014403512002d07030f40d40c0e9010040008140b2240200042d003075a52030501c003850f040400041c1802707800b260342000607400948540c0380b036000f0031221015007450107030340e0386890342c840c90665136a20031200c0e110a00d000314045222110001601c5000342e50040250400c092081d18540040628400c80d0301103100d0400144081080c43c2450b182106030300d1004281c418403070042c10301c2c000000c2d05002d12902d0003941c00564801228504025591518000c2018100040044c0d160881e01c01318944400e07030815140c03001a000095a408031454500b070300e0a621400b00164200c905a1058805d400032031511600080d100d500040c032032100c61407050b001c46407500032203001c5070982004040583d2040801200c040c004000703d07100740300300b20b00034407582c90510b00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 121183165 1250 121181915 121181927
    0x30a0f0902010903110f0a0b180f0a05010c1b03140d0f120207030509030114040c0807050303070809030a0611040f0b0c0c0904080c0118110613050108070201060503060405010c0908060106 82
    0x300141c400a20b569445c1c03e40e0340c81e5054403e0f60340780141082103890300c401001c00030303074050f400e0318201c01d803104d4138503215007482c1d02c0c09e03e50042d0041008035035a151500544144c0c0403910704070f407a4802e58080882c0c81480060325000340d40110100800d02c000d100d4410303d4003504001c00414410505101c01e8a142d00c0401610200620580581c98421a207010b69075802a6200f0340e6155003416407141100072109681c80c42540500120740144d941c03219000c2d1680d405000340364150708204141d80c003096aa100801d01e0f0507029007190104030041d01c03407004450381d241070251a070300000303000c0102c01201c40404002d0a50405800c2c80c02c1c40030326850b1f5031a03c6008016028429040004051254500960782c1d143c02c004003d1040c9510040d4112803040450021200d6010411030810320b81081d20554a5400301e11000b0100c441c24200191141e040041ca4401150341302d006c0802d4680303007030088038026845900046441d01202c50094031108554000150f5540700d10010003029501507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 121184415 1250 121183165 121183169
    0x81e06040c06050f0415091d0f18190b04050d05040b09010513030f0303060602010b010509061920060105010206010e060904022b03050405090105040b01021002030604060302060408030307030507021c18030b0c030a0f09020109 98
    0x204611202c10b1001c007003541006500c8bc0c0b500d4040514082520503c8072000303c1611440c85031040e43c1e4000401e800c00d40d60740c092801000f15441003803000308100e5000744000d00442c44015012178003507660340e4544100380081002200040d031100c2040141c0c0350240074090307011000b403e0441c184003040000c60482c1c020b2074800c042201101c02d103c00c80c94003942c982e658010045003041d20707000c0d00b03040c26544d80c0c00a100705401803044800008560711240844c9000e190000e04c800c14540321502041195014402400e5100d110844a40b8100380292443c002162103501c980b41c0701d07440c22080004200050740860b01807801d0203071022550703a02013452181c1e48084c040058032a01c0704070101d03009044a40000b50400380009000c120030310000040e6120344401e54081c04660340d0b002d022601c402410341954000d6840d5510869564000c48082e021079240800100c0020b54030b840b509402c03035050300c0c01d0050810000a11030b92003564060000c84050320002800354074502da0008102000318 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 121185665 1250 121184415 121184431
    0xf030706050a02120421030209011418220506030f0d0503070c02040c0e030c0f03031602040b0d030f1e0801060804110307081e06040c06050f0415091d0f 67
    0xd03400114035010320ba05070350441107078240c030540030300c5c2900d000070840d059032004490381003d52484000c020b219008441107108103950301602081c1025254000da0414020144202d1015220f4012a140c014034450064041c001e040c0240150301014011580c015100e00d0094000d10365005450300001025803a00103249230255581c1d0311280110366003001c00781c1c02540075041040e966041a80086801c060720821010b640c0504030345410844c24040d4030322003a816800500084414030086040e80c82e90034000b43c00410f400c58110005150840c41c003c0840c040340c1d90041c50081503601028080c041203122080012071801540c0251204005108803030400281c000014200700e2a401c0014070f551000d400c0354940703500c903440646c658091064403040c148001605162031000000c80703502035038009050480950408404440d0f0754405004504058400c20000580c0300c020802e502802c1c100795594103010341014421408080302216101d8075920310000e020490700f04101c001d40083c11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 121186915 1250 121185665 121185671
    0x1205070201140409020307080106020a0302100b01030f0f060914150d080403051b10050403150c1106010b07030305060402030105090712150602010e0d0203070803071809020703021606020f030706 85
    0x18920048400d81c55100a002c003409001c1400110a6400e4015600503907007615810784903078950314101e90b41c400d02c61026005a210001d103941c410480c0e802081758100604d00403603403826543d80b06c0c060320103400c4000c4045a40e590700704071001883c800d005000c2d9401c41e41c0c0b0060305101c0124103d10600000c6644160103140c02c1a040003c0e84013120020356103d410348203480c5041e40304070000c10030160510b010f846a4001c42c0b5459104004035030a80740e01c2005035202070300c046503481c014142c0352001e200f48030001c44404400030007001401d009100b095821581d031401d41ca00142950340c0541818000e60044c801413240c1d07503030303a803a00d640b08080f0700e403800b10402a100000040c0c140030818403200420030b500800c0040c0d06420034082c5c60f51080498110904a04040b6640c0c89000000ba11070a020b0000c104401c0c411120160b02032042c50711121a681c89601c90401c0f68405403048001d640011b0070405015a40403803903004003070f10b0002e0300e00003110540d1140c0300d1188000080c0401e503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 121188165 1250 121186915 121186927
    0xb030d0c0b19090803061008100b0c07051804050d0302041a0c0114070225031a090f030a030209012007050402071406181b06040b1809040605011707031205 68
    0x18080380355000340b924035028050b00d140e0b418078030825441a0f940034081d4082c4590103105600070302030306000b01000d02002d61402d00d0802400243d420035011400b29014214000400783d45400c0ea61003000c5255a949a0504042c68010316014034800b912040c5030061000b00b1101e00102841500c0d29a2040c50035981d0496815250040030245c2801219280c0b00d414001159400140780c403c121030450404000b01000f114500300c0b0a03640700040004002001191031401c210b032046400c8082038040300c00400d0000000f134215041a11389000003540422103403165a4048100030312200044080359140000302c900e203441d942c0e0f900506000d80d4000501600708012035500d102d00800b40c1007038400347d04216425a2010004408900d000d01c951581e5450741406004501207a140081516180030314103140140c45030000400030340f0910914088120544a040c50f0f203110b184070b500c00007010360520040c2c3e504051196100c0c03486512100e010f0000070401240028200c030b1504000f900d0b55 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 121189415 1250 121188165 121188181
    0x304060c030201140c0c010f02030405071a0c030409290d06241701110307020601050d0305040b0a08040c06020d090302040506030708030a0c021008040b070807020c03030403030207090b030d0c0b 85
    0x50a151307000401142c0b601008104043d1101a010744121035000307000c19000000140e060f80401d45000d00f481e007100004202d60000606411002c1c4008492141003003581014030781541c025610000c1041d0300c40703454403040c0c000c2084054106020301c000098040ca0301022403422003408000610307842d43e6101e40c051b0482d401d013440318803a20842c0c0c1300e14182d4980ba044078203040494000741483d03081c090703401108040101901e02c01c007103981c0148166803a0204008200c03444070340035420700c8010031002c201e95843c00010800303020107443c0c06d000307401c0a251505540385240d20410864000d00d00404032258050b28000c2102d40480300440e168541c44001b90409120360311840c2944000500505640e0300290b154170341c42d0003294141d1140e1180709042e0380c0c00404039001451205500005000b050046400c603801480d030b03104903504d003c186004030f0300e9a0b003e50030a801507070003250708001300030141c09500091003043d0050443c0e803107540005130100701d01c0c0500401c1da907451400a0025 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 121190665 1250 121189415 121189421
    0x50309300f04150302030112080703120e1605041e0b04020405040531020105040501210c090f08010c05070212011107150f090203060604091b0e16030e0304060c030201 73
    0x50054140036555200700500340c001d02d601c5840749403490358458040030b5460b4064030035030b03040301d6005800d000d0485140d03482042c0365101a4044040c0a4114281080034034144108003860902c0c0c00108884aa14500c1e0440d449441d80054861820501481e0503090b5690b21000480c2c0e2404011905c2d450340400540640115003000e604645000704029442003201c20050b00b076802c00d80807200e030000659664600301d06001c00640491010441007100d94840c10290b0f03034490302e009018030300f407440c070010b8410b40b0041026200001d40d000e10030302004044d402d0400c000c0080c0b1000300559200180080d01a00901d10080d02c644400c08c82901c0303544003900f1003400b08191018155030340b6424600118070070089141c60740003500e0000080c000d440e0078812006850380090061080b030f66004c0410004e40f1005008603a041105224000c8051490800c078001d080484401001c0b450302001c1c1e804411094212042050f05102c1020f401c04c002000b2541076521500d40310320003480a060a9000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 121191915 1250 121190665 121190743
    0xf0303030906071806050301050d02060d14060f0a0806010302060a1808031e070209010905091005041202010e0706141b0f0d081302130f060b0705010e0d050309 70
    0x14000002046450701d800b0070120310035019512169000c900721075110b81d1114942c0500c3d070114004000500581c64802c81c0009031600c02499a8078000c1c030946140291a03010300d0401e514542101804000c1c0b030315a4101500b21030541d40150241d203003c0e126030362110184000b0307000300c000003140894184900b500700c2d1104042c1803180f0020340d441d20015507940c00905129000c4c01e1261710540000d0940c000c40c1d0645800429030300069007400f00c40e20003400058009525032145201742d0a40010303d000d220b20460007240340d6154840b44078400703801d45160400644181d0040c8005216442e08010071400d01103081044031b48801c00c039440d650b0740144011022049104105c01c41c590701c080000c0c060921039060381d41102e40c0c0c603051001003c00b414140020b500500401584000066681c0800759002c1c8c0910003040250f503480c0d05c82c2e00381d40403201c107a8043e51070340400007001c182002007600d840c00d9490041d16615000792520307210740d4400c5030850f020802d17204c6242800c4880821070a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 121193165 1250 121191915 121191919
    0x10306180b070c0506010e0705030f070905100c0c0509010e04080705010b0a0b0d0e0d1d0a120f0b0915040b060d050303010f030605150a030b07031103010e092e0b0f 72
    0x1d40d050000b40584400d5080204580d10301c201e10003c40c03880303ca071110034020f0701292036403800c5441d580105d80003084024000820044213100008180d5900305038a50300701040c0d1140041e00d100d6052203000108070750441c034040c8112000422014001d040c00c030341d0194004191795141d01180c0782142c09420f4104003039520094105010841d60301c0e402c000c20030395092078010000c400482d04840c0c0c603045560310490200c4c2d00c103610f110301482c0d0a400f410480200814807030030b0765160090050803250b005007d44c3c4140007800100c0402080044032504a440c0100529104000c49842c2000c2417006100070104625240880c90780c0d15089050401c19600074250780c6c8030b41e120340c0f02e07401c041928481030321243e0410f80802c0d2806074241c400105020050a18140d580c110b481d107440c8804058252420990341c0e8049540944499001d035020300100e0100591506140c0c00b140d02d09445214031500c12445400305a00c0b401e4101e0070920159030f0b2460114a21010f000052103ca5101041ea9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 121194415 1250 121193165 121193183
    0x609050a080d0506010f08070e0d0c0603020c0708060411010c021206010305030a020d18050603041a01080c0f0303030f0612030d090b010317040803120a0623010e0d050601030618 78
    0x41003204100107890501c07442e5404000c10750f2094011120b610740c4039058400703e0312084c0030601d26031244200490030035024041c0941d09800d95120442c100c420f42c84980080d80c041400c03007100005101a20003054120001d202d942030588450140d1103a20040d40d060100c0c2c0103010b0b04645514000c900114550000e9034007070340c0c1d242003c41d107030b90001442034014000c09407515011130141049100340989148012111401c0c0810300903107610103072043d05d440e40710701c03000d0920300d01c0c0d1552107000c1d00108016140c12a00c0c1d20a10880140c50300883d8401d0b0814000c100380c20202585441c1d120100b02c901c040040c030505425400c510a038050b81c0c00580c100303107402c1d0500c60f4020806048070303c201e9000020340300e10700d0a030001c0d0041e80142840c41d003080015103110028540b1700e07038202c050818001051030f580d46890302d0450f852518006070b0180d82a102c0000d6800c80b040741005031040d50b0445103400b00d030b0764143d142d14050000800d60f035078614509003e080990005072410f5440b001e14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 121195665 1250 121194415 121194433
    0x120d020d080108030c1203060303070212030408060a1a130f0f0506090c0307080a090c050a0e04031206120303020c0102090406030503040812070c050f010c05120901080a18030c060905 80
    0x252200e8128126001150901000003200000082150381548440010b0610404545542c2d14140d02c064401da505201c28032904003d0b03035a280040d0041b112a00081d542c1364505203c403130903c41e00800142c00d4518050b00c3c018603078825008421401c0d400c036040b0a02c0301652038074400806259004603d00303440c007446020304005643c001d9024040c1160030f240355954007151a4218481112003400040000d004500d044100342c100d07030080d910440500502a4550b070108000e54050380c00352a040d0100c0c1c05000c18103412409481c00601150403d010003810f0590711460260300c54001410140d00003050b0401c0d0900f03605940750301e00000e000b40180b0340d036420f00d2aa40d4000340903041190140c0c05007c43c1d050a541c044400365680700310400d0001c0e15240c100003d0442d40c1000505004000344c4407400240d062000700c0c003083c0c0b21a5200d46480d036090005010080c010585a1b20600c0c1600071101c0c4010351045407105641481c010f283c58106190101c0a8901e04c00002e08900c102ca0300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 121196915 1250 121195665 121195667
    0x602040b0405180c0405150403080d1a010c020102070527130201080a060f0306020f12040302012f0d05061c0b0115030b0f0103051302090a0506011e020705060702120d 73
    0x70030031a141150450143c000700c14044580c004181c40b10300c0d418400304800c1115041c07000000c00c850a000941d1410540d0725220346031142e1081c071107604040e54583c2d46070f2080c1900d180c88519500e003031a04511442242e80041e60303d50150182a20640341e40e0a0303a14080b541400c130448026000d4165a850700340a4458007003001c54140032030101d04100c00080d1440082c1c403079241203900030b0062200181ca186c86220003548200744040710010100480d5118013090303005075019500c65800081d544c144040c40700c0044040071040907800089000f140c0c041080320003035407800b6116140c0018503803035540005021040a102900314920058003013418000d0115540b4121402222848151103800340101d0440e0540b020a0ba80014844450740c5176500c20340c0035560040045c0c006451440300341d000113607a520101d0341c0c00d21080d11001000950b5078812000c1c060b445009035101030400303000704081c3d2100304a00501c4d0041302c3c041070700c4040d543d0b41c81c2091000c60031441620004816280 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 121198165 1250 121196915 121196917
    0x706090506072a03030213030602131401050a02060c0d0b130e06010e010312120b04020f031801090206030a050403050418020a0e0102030c030a030906110a08090c0f090f04030c0602040b 81
    0x1451102184200c00c00c4034040580000c20f07001e4030500e00301c810500c0e50641d4290025002007804001c08124164040700142c5184001c03c00c42c40103203080e42d0740504d0507828184c0b480f4405025810040700348410041650005440780d04400d9515a1030703281c045a40d40800145428004564003600c20404a0441000c40c0d2101c9203266504003602c0b51030fa02c640b030030031780e4010a100040c4055418042003950510519050503110b2071401c0202d603101920300002c040c0e800038800d00515175000400e1100480c52172a40c00c00c42c1540c200244401d03606900042d44a01006105031034050b2103030000780401d813103442100d000e4624102c00000102c038442221009401085290300410b42c41c400504803913000105840e40802c42400a51a000c02e00c0380840240120407801c5942a03140e80481c04118240307006004011007595480d0550b140c5080b10502c2c290703030700120902502c841b0f44009060b880c0c0c0803074168081d41822120845403158074007102c1000705100003605503840440c01180866002d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 121199415 1250 121198165 121198171
    0x13090602040b2203030c02061c050a02090901050d0f08030c2502010315030c170c06071a0f09070603110d060801051801050c0d0506150c03040501031b080c0904020706090506 76
    0x74070415480c0c1c24034112403c200202d0b0102801080071548080c1c01460310400401c1c01c803072040c190030000c0403000d600c00103481c4280d942ca000b80b50040703903650190400c90b1825004010440f04007950520030345590003d101808809415040e00000107058a0031200466071074440c0540c040c1c41d00b0101e524a401c4070084024102e002a00302094802519411200e000c143c07600300c1d05000341d10745451401f500880c212106881d55000d0001441d1750350703807400b0151401d83d001c1c111906840c0482c20b030300c03e00d612001349440c0b07800c2440710600c04440c0001a450040d03d00c03c0c1400640603000d041040703024010481c0601303586080c120301041c1c891064201e980941d00c110505005520b0303420490382600c06c100c0308602c544005004103a030007811074001d180c000101030201c24030030010803d4424241e0200c00c1078186684002000c00065906114110750145031000003405072040d0300c07005110b070303201410041d004c04000c034008d4100c1e55994121a101030380420100700802051078116101c807411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 121200665 1250 121199415 121199437
    0x130302040c0203031b130b0d050a0b0d03020307020f0d0206190f170f060f06030906070f030b090f0a06080a0303061401050c120f070c0e04060c020c0a030213090602040b 74
    0x41071600e02140000152405908040c081c4a660441080d0810540c4c001014034403108165510008000b840b01d0000c1103485620301001c0307418604103200d50251142c41040318046e4042d041e011010a6010064852050b412940f2501d00914480050110305007a000a03602000c009006e1001c0f084101d03820080b0606070700e8442d200b600f1680259005415820110002c00130712000404000141190703d0744040000e0181c6074440c806804119150400c85030749003a91b0040c0e0900480b10b8103e0400a1030384040d10303060090714141f40200b100b404001d0662a0022018004252800c0d584c3d00304a002d400e560046507403810030303820010050a018810b01032044103405240c00c981d4414411140741c40c817010020502603803440c5500009500007100c2420000c0c0900005000078610050350b00101140c054007216420541810703412104904404015548007000d0350320036441701d03c40c2408407901100e66a62058040780050702920b0081c6005007801d10005021400c84490400b0741f4400c000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 121201915 1250 121200665 121200671
    0x30f171209030714160b0f040b03131b050105180103110c0109020f040513080a020a050a0c170105040b01060c03110d05210714030a020706110a030f050f0c0a050f13030204 75
    0x4c442c030b4803078480e064540c00340c4c80685403000c01c3c0001c4840400030940d03000318a0f500762a0a80d91001e0035400d40060356803031200408009000180201a000c040000840d584545401c034030b450000b030500c1c411000d884050001e54584240c5980c040e40c441d220f00f6500d01e08441c0d03100901c100c0e090081910300c0b030882c45142582810141400c2c9489914070a03000850884140c40240d181c07504a504180d40c12001c41c03142d02c402c0381c0081c4041c0300c200381da01d00c540704040241d8101030342109042c0b4484107070107450f0f141400304800315400c0040d09045410701d0609114110441c2030480b05c2807000c6103142c410f032090808112040381d10030001c00c1c4003403445214030048038402c080f0048021b015518040050f0b1005404c00740d60040400450b08003440100061810b80b090313450905a44a00e06542d10800b0040f0b809030300c0c03170b4050103403143c40c2111407001c1040b450104003412480b04050b110009038800400d01140702e5018004603a525640a007503940c0f00c403e07250020800300001d000132409031342 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 121203165 1250 121201915 121201943
    0x14d010f1104030303020913021c050a020a0e2106190e03070b010302150c0d080a05090313120201020708030c01060302041119030b0f04060603140f01030f1712090307 73
    0x10300e600c262802500010090380c98180781d900e04074080d40042c02130310b40c401c901d040728000c1c80301d8a100400d001c3d03900b5032442000840d1001c0b10000c56900402800246004000c01204c0c1d40d0320440c0c400501c40100c4050410f1040d00d0b600b10300608218401014512900083c014501180700e103884c24a90401000c3c013404501072500340c0c1302c0c043c00c10020310b03204240303005000504d44070b40d0090f000070a0781e041a00f4818848a803e290002c1038070741d140414401c8061040c00d04042c05a40c0e402803210006501c0c1c41900a401c05440d9068030a04800d6540004500f0071a8400e1049400404928044a480e1458103603524003c10321803004910803031400c91100811f41428050340c1c186913440148464a01c01400194007410394000b480d50300c040c090030055580d0340e40c3e100f101e0140030650390001e1514440030130a842c04102603e250842c951003001003000540950316082111b5000c00101100e09000c04407640b1801040e0310481740340d860b0010441e10541c00000f500100b1301070501c00180356 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 121204415 1250 121203165 121203191
    0x302030f030c03030106080703180b1501080603030f0c010905030c061009051603090309090c0f08010e28021204080306040c030624110d030608070801020405014d01 72
    0xc442d048080700c0c1c940040c4010007445006140b8243d000159080210705d000c1480d0071008a0490b112045981c0405082881410341e030701c03c0182d104440a081c18511424090b00007540c1e800f401c0401c03010400c1c0040c501c95000400e40240402e0741d403000450782c03901490b691081d2116006c031403550644040c60000250044180030b054000c3c521141d1040c0c4a000c0d1400840291100a0080d01407120901000851a04502c0744176108001c541c0c3d40710b00d01c2d007220b1008243c8841a44034003180c1c0207000034000d828184a020303105c221007049400040f41ca440068101a0160540399120a2501801c01091100c400003d5105480031182001501399031102502100c40d14000c0710103115181c110b299440c0700340801140c0000e51414059001c4c0751030b00c002468108101d5041d4002521030600300240072081000c800a844200c00035400c050400000801c00c0090203540240c003502c0704062026803a07240100c4514820225580d079031202520812112a00d640c100c4c104203620f0000c140e801350b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 121205665 1250 121204415 121204417
    0x31509140d09030b130b010303020c01090b0708040e2701020426070608060102010204090f02180904030f0c080d09030e01020f07080a020904060b0a0603090203070902161220070302030f03 82
    0x300c44140c80b01000a8115200c2004154004054000a40c5007406030004180c0615546000398440d82c02000400d0180c2c000401710b104076442403020202c00d1180e40c000032078010603102584c0c0494640903550352140380022000e0074207400100a501003c0400f9030340101074000303009071210403001c040420040e82c84940c01084c10308001c100b6820106d0240715081c4070760049a0441030510001d41403940710003158045507502006217288560019400503400ea40c006519200c42040385e40c00311307500d0251406031505003080031100410a09140c0c01e020405050282d81c28250b5145080048180c01d01d40905103109801c02c95001d0310481c1008410301000141c0002030300c0300f140103084020450360911501b964080c1007100c61903100c400011040c0c8502008600a2050b0307680840e03506144e0040c10b0910780560884200079004206c010039541a0300076200c00710340c0c888041200c50310640d200320748a08500002c5088202c4255030299a010009400819030307001701c040d686958245040c0c0e0740e803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 121206915 1250 121205665 121205683
    0x60a1505040f170604030e0609030d080105100201090b0703021c0207030c140303240a050910060f0512010611160b0d0e01020901140309010605030d03091103010903050405040e030403150914 83
    0x200f58080000217000912078040820758800140c24641094981c00020f41000310407103d20340001c0c1030400411003444d219840ea50000c101c0d0008002030310b400c0d2655500401c0007080c146c14540c00040000c008011404403e10b000c41110782191104c000340f034000d100b0341100c0000d0311109041156000d15200100c1100c2c000d000b00094801d854011900040c4400801010298051000440041c00e51100f04500e803245144171551000c0d58203000c1f0180c980000c0c3c25545013003100c18400300700e00311001c400c210706503501400c110244c040c240384000d1402c03184680c80a6115401607000640c014003d028214000041c6400e1200340e0111250508030700429a6982c00100f041401c003501e005078500550f080080b03480041011520380300804d25120340709040e000040d40c1c52101200348080c5088000500208500034410201e154070010000d00540c01001d11459440300094030007681042214003e5501007125412080c403090070b00d00800701500305075000b003001701c80a0703943c00300420400c4d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 121208165 1250 121206915 121206959
    0xf022a06060d06020c030403030903021003020c0606010c150c05032202060306010507020319050c0a0603050403020c12010f0e100c090608010e04030507020315071b020a030605060a1505040f 83
    0x400c1d503100301c108200103003441403d94580703500308000700b0310079001d10040c0702031030290f15104112417441c81444004084194048101403040c400d0078400b03800402c030360307410140034a803d000360080360800c0c0396144500c8145600c4249000750032181140c005010391310801515503811b4984c00034499615004a202c8002940140c5c1000010700380c3d030144000d005024005002c032500800c410652000c4002c0d8841c1c103903541d0348500c0c1d4101c8903282c000000b00c060f000c6841c3c180160304003a0350295448008410107440303035200780913410881400758451b07050407142c0c500600044a52140729a1030303032005044c201400d810b00e40c00d13800c658041d8424000300c0d1190395800c20715a1a19620b4176403540003400403405c22801300002000b507501000204d610041c8100c6110440c1031000b03025000810680c1c11071040f9900e50342800159465400000480b608400c000c075207651a100064a0481c0c590404408440c18010000c02d080c0c2c8403000d0710030390b1140119401c0c81600c5440c082d24901d40c07140310007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 121209415 1250 121208165 121208173
    0x801050109031104020a09030b01090506040b060405030a110f1008041511190203040902040e060a05090705070b041b0806040c09062313020c0d1d0d240f022a 69
    0x19404d055008204461151601203403654407603466030000002070744940c9045d03850f0024460390745050303c0303982c0700c00c03100b1640b4510f4689801c2c04640c942d008036402a15a1800300010320f000c0c1c903070300008559480e00614191100707203070309800340c9056010396080c1d484404500c50700419442521501211a01074903071281006201500c1d10003882c4503414400460006205c0050014140e0010b40302402130a8a003040c18a80801070041c140c103242c0c4502d1160b0b101c00140b12104ae086021100e04642001d040d10b01c654a50401040c80c4480704030140500072000000550300c84046885400ac03031254003914122642c840e2440c0950b5000c0c014400080d078086200e03803921280c464400310940010b8a85c56051050806000403a001480782c14929040140d113144190f50084200c0058040451044007013804c0c080410448030380d0420007480388410340c0030906c00b40800102e00081c0d020340602031004c540356407002c6010f50051038042035142041e08158050303141c09501800c139040084024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 121210665 1250 121209415 121209443
    0x6030f040813090216150b010912020f0a0e093003090f010c26100b030714070609110603040209040308062206030506280c030b060703020a03080105010903 68
    0x707036607a68806003400d80404040103001a03064041c2c009070002c40d0402d44d096480038464146603007149414104040014988148091141e13080984a0151258140070001104540c4082040110b00782142a4800d042e00000105103c0e000780b0036110f908200c0c01d0366903540c102044849081a4400001860205548a001800d054101031a0300c42030400c102c0e00008058130460342121134001d041c0c00016241004c98505a105802c030004054100550032814605100000314a1f00140640304500c1d60010104120fa0310407910210703001094810195181c45620b000390081040000c2210240800c1607411080d142c0901075a21440e0007808070b4000b0358031a5412121010010500e90f0300034010301a409a669a1241642d021981f50500140190950900c18900000140840b914548612185850b0082100e280140100a14002c44e1003030000401751b0151503503203c100d41220020861901340b65000508084040c0261554242640c94500441d18400e49000180000b1100500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 121211915 1250 121210665 121210673
    0x90b18010f1214040201021b03070302060a0c0803010b070c0506032e080313080f030c1902010c0602031302150c19020d0602210108161e05040c091406030f04 69
    0xc0080341d200d1804442c0c400691101c60222910701d00310701d01e4003652004010441d60100103440900344100301d01d980d44201c140000351f81d070110307000003809003201080340c0765118000c2c0d9110001c01d41c404400358407580c580d003002c0d203030703412000040d18811602c3d44000f5150510354100da0041c680340422040b200d581401c6903070600f00d400b03441140340882520000c3c10a0341400905860b56441c0f2200c3d00703080c44c02040502d0300c42c0d45a041c4040350800c004141d194400000c00f908034112942c03c0040b9175071140016a503480c55001c028084500000c1001b10a214800c0b45450051003101e02400c1c15285100041240c0501251090160f201664000720740f0101800110782c107100034a00c40240307401d6503841c4141d030401d908441e00b44140d1441000c010f01d000d80c03135074003500707101c0000d024000104500d442e4602c0940b0a414000c940110302c1c9c80c4c0344800182240240401420503c102030000c20002c2180945115030384020203146d5002400703140803c21203000f0042450003802944a03529 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 121213165 1250 121211915 121211927
    0x6050906010c1121010501090515120c0a120515010614090307050415150216060e0103020c07080c18040b0601030c120e160e040510020c0304091b090b1801 68
    0x700c1a41d20000c0c411005a1a07035a401800050200204c180c0c18003c004160b2142904c8040e0440800e076410042003100c00750700e403410800e445500711560700801603010740b06800c201902d664a50030a00f0720602144544000074a01c480921035070859840e40540e94000da41c540c4207000b107500003a000c3d5200381e0996011000341c0300302d10000b0261129640e40348001402c84105d9110411174040d0740c1d10030408007513074a0001010130b260380068415400856130301c00c0241c1c85409600107204080e554901180d200c3c2d4150b4000d240220704a40300191100c116aa03a042502100d40c4100c444081c0300c6009118000c04c940510703400018510315032600780042d409081107500034000c1102c5034040d0f004c00d180c1c500a42c0c203002e22000c0589601005003856031180d028a40000c59804801d0301400001000011200c80e51071803441d0040e04c800401c40c0b035500f140315590003405690304240480701c010500050000b40c3c5560303034031102c00160b80c442850860307004100486800c61a500c0c00e0800550141d6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 121214415 1250 121213165 121213187
    0xd0e0301230a0b180a0203150904200105041a070f0b130c0902070201080a05150d03120506010219200402030103051005090c0a03020120060702030a030f0605090601 72
    0x100046803145500c0c545107080da9a9000d8903000114000c20711120800c14811204042015a2030400d8404900c801070030048004d80100c1c0c80320350010015071198406000744ca00c241c4002c044c524541418101711020706207041004000c0305901c0c140d482a503005000f100c2c100e41901c5480e01040d04100380741405504140c0050b02c0301090661102c2c0060350b003000c014030402011040d0f0b950300000382032078580511903070070140c3c1d590f2040002d0720142c2c2e004403e040d4840d04180c40450aa0b480c0040403614860240089401c030310003003045030030903800000e24001201c00700b80030400d903a204401280d4405100c1c07038998040d6070261802c000300729a100521070340c0e01d00035910011100d40354081022640240e10039a95074100a461070290b14aa002e06500580504010300b90400b03028002110706182c1d1100034140030f010301c280441030300c08000d41380c1200c00290541d0310034a0500406512648003000c6040024585200140200064030441c0306890001d022401260303070b08001500d020041c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 121215665 1250 121214415 121214419
    0x14010f0302010c0c09020301030309061103030103030806090402030f01020c0c0906030d4802040b0406080607050c0c0604151403010b030c0904021e090a051806040908040807080a120f020d0e 83
    0x40c04d00429058035500080d4004c500c26500c80f040986060801800c1c08044200e141c00c50300108010000b007a0f01c00d5840707402402c1101d00d543c4a40700c61001a18140c0d2610196003154008195815031310804941408000000d5900700c18075500d1104150711103080e000c100300031a00b504914460354600303415200c03c2e200e0014400e01d0058181342c0300120010f508170403600d24000075041c2c001f14117260140048d2a001914144402d034248400261951802070031941001004a00d0080f032120070010401071000c083d06d40b980d145c0d219880c501c8444407064401c40414450303004108861b0100040300c0c100c0d482c0420a03811501c5600001900d03510900007941d1040d000d000c40c02007002140c8020a28035103120710650384403c00c80c18070030041e0b5203074481c520901400403800f2004049145c403644c0000200d60020780702e0344070b141a81c0d07a4065a0020b03150361090035000b040001c00000d0300c1f103440d80660040881810f401004541e94100005210300603009814450040d500400041088500c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 121216915 1250 121215665 121215683
    0x2405090a0b031e070315091a1306020705070503011103040c0e0c0c010c02010614010c0206040504020304080403170403030e060a0e091b16020f010f02030a05091518030114010f0302010c 81
    0x304501001210301c1c3c540280031079003003000104100403040a26091917181c0d4082449503001031f8232002019258803e035030460019140028525110220004801d260300620854031806103042c034540d6090303140100e5010703629004c2603045031640d00742035a01c5150700c4101440e01c07500384404203110070405085600078980500502c009001d0a00400080140e00d0b400014118548809800350140704040d2505015140c9140c10158403110122019150241d030056503a0b02d4a240203030040c070680d03001030041180c078890300150403007600040048070302a03514510b00c09460b00030002144101c40010001c1071180c0c3c2200c10324109a110940d0001a1036400813407105185ca401d20170f40e000c10000068003251701803200451612440c031016081080c42c00c455043c074981c2c4041d65030300c0342e2012141072044c0482ca41c285691460311003810103140002c41901c900340203099a50715607250b82164465400c180b080320f440040864054100c51444242c101800d15507001590030000c0341d1002d0340c43c804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 121218165 1250 121216915 121216933
    0x70e150f150703020115260f0109051c090f0e130213150e01080d1202071a0f0a140105040e010603120503060306010902042301030e010f2405090a0b03 66
    0x1d512004080c80380c0c04505080e030b03110041d280003421543d210a40c42c004034240704040c00340310341c00180442d20702c48070301c510541207607400380680c84c201c0d035206a074075150300380b009450802c1008111441d00302442401c2400b1501e0024050311082c0690041c100d40c0703000e100042082c002d40250854100ca0008250307002d0a4050300400c4001e580541c09089140d100c99040d88844030103c0c4940060110b40c2840c0b005505040d00c588e01c4211400d00d030010000901e103c03505400b9543e04035580385500a40009480c0d1480d0085000050f044807a500c43c000c04100094008980f40a00080004a03111800d901e0b07003800f04010041c2100340c40d5004a40d03171410f0210002d80740c3c6152003074904194a0343c40c0c4914280040625100c8140c2105d04801d006100c10020181c402111a00d80c20500340b46400c9180c031400120020012104c40310b00ca5030030112015515052680009200200b00c5c7d901018480c02c0350691107030380f01c1840b81540040d4420000303000b1003142c1d880b8880703013a0000c0070b44003140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 121219415 1250 121218165 121218169
    0x2061518060f0415140d020d060e10060f300b071403010801050a050903040e340801050102210d1104080d11060a0c080406090804050a0308040e09070e150f 68
    0xd055168204c00c00314031a600340079011402c1218108100100c4040c04c4504842d0302080581c4100174000b0025622022030854848042c024501503408041c01005241d03901c60103102d06940d1846141540309040c0748880b4426542e84003401e103054003201e10145040701e43c2c1e032010640b000901c06020030030340310421040540c0d20030003103009009081c00804c070340c01c10219450403200050300b0203040d980100701c02c10030f646080903119400800290800a2803a00c01200014442c0a815405401600d94043d0001981052100d4141e54080e402c40b0303101341081c081070b40106c8410070008003142040c8258036a01109400c952001e032081e44d1054107140e80c8588172403510202c4030b04600854514900f10040c4403003080700c5980040c0c000d409004402c081c910207482c160018002030149078807440c0300c0c4144942c0d1800c40b001000c0107066282403940d42c0c1031a090542150140d5140c0055102c046042c20345c000070101c040c0c4010392001c80c440d4803112100f00c0c00c80d05401d00702c0e0308000e038440c41524035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 121220665 1250 121219415 121219421
    0x10b0604030309050f120a03030203070e09010305010e060603160909050307020d0f060b03030403030f0503100e09030901030e2d07030605040c090b121b1c03020d02061518060f04 78
    0x2548282c80d100e4406060104201d500540095014020200072889500d1b5030303c0083c40b203101907014100140e6035100e1400031900881100c218bc0e810009582c000800c0020550203141c3d0101c4503802d50b07400f030725010201034544440601201100740e0030355040c8030180855008114942c49241100c2c07608900754040741d0030002e00b02043c0c801c0e07004003000d0b00510203140106e42545c042100950f2600c1d0440e9000b42a15000e07a120710200800231002503145a0700c0c04a02028040245c1449228075000d05066625846115000d0000381080480c0b10b5000d00010400102600441c0d806941001c40000c2402610030914014191248100000109020740724450045019141e01a801d509000c074200c180c404510a05000389800004d00c10100400f10740c4034001a50030228070f00607040d0f0300002d480b41c402e103103840000c0c01c40100440c0800da000600c400e1404015000e68089544160b000c04144141030040c2e600101d03803010f40a2001800d264403075100800070110044100710f48045012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 121221915 1250 121220665 121220669
    0xf0e13060905060a0603060b07031409031f0c0305040507150c060c0206040c1710111b1507090e010303200d0f0201050105030a0f0b130f030302180a06051209010b0604 73
    0xe642d42c8105000742414203400c0d02020308100d090512855140410f40c1c0d0070352196031801790400084018010040b60104d00f2111080001001c0301e0b50088440a0204a2807030008030200c0c03280340001e003000d031500038000c02c1c0c803071900280038100161038030000710f0420841d070f01e403901041402c0c009280022158030880e030807e01d0f42c0d0b004161a141515182242260b1504800403400c036820901c15180c8002680041c04c0d915160007060590304a400340409002d080c40c4103c0403103404d0201c0c8209000095944407100c1d031680701300300315110704a00b84c401b002039000c2c81240424820051011038040d41c08001013070003210081340c00c08500308409040041c010606000030708a00c286060440d030902800e805020300324042c0080407425980e90180032403070300008103d000c1c3c800000703069803480c00c0c1c07107281c103600b02c1c80200d506c041c1440e00a0003580041d408607003643c1c140e40c040c134250800c4030001d02030320196101d1a21b40003c01e409000c0e1460000c0c00071440f99218114002c035a11081c0203400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 121223021 1106 121221915 121221929
    0xf110615010509042409090201090605180a03080a0212190c0614190e010207031202090a0b0d1d0a0816030c0605041101030b0904030f0e1306 62
    0x8283c0100810070781c0c0300d4a000c45038030380c401e5140d895090900e03901c808031210946480412003215084030340a40000d800c0e45048c80a280590b004000107a0301003c0f4285c00c0880800140c1100640d0b0022148440081040b044098042201c00c8103a5400d05459060215849034034200000d1070018404001401d80c841c0180040c0798001d5141820709070810b011803407c0201004010a01c070200010180b408020082c903200601c29100300c80c3d0b2681c0c1d6042d00704146055040031f50001884660b019100620000d210a00745c001840194400c80e00461001c4c1d268003000c605159030402d600c42034000307101500000d4001011584480341c3c9036805842055a420b003261848003001c0002c20941c505403d00080c46020320b03801d400040242d03000c2c0f01c0d0410b81d0003407005c040740c190b40085c0030944410f00b030f00c0c910b800f890090300c1c00d210160400b641240c040f08018152403095104070 = true := by decide +kernel

theorem cover : BRFrame.Cov 121043165 121223021 := by
  have h0 := BRFrame.cov_init 121043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 121043165 ≤ n) (h2 : n < 121223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
