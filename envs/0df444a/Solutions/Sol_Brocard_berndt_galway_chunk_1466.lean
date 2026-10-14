-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1466
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:07:23.864362+00:00
-- url     : https://prove2.me/submissions/1e23a79f-5b6b-46a2-8b3b-9af2e6ab80b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 263489208 ≤ n < 263669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 263490458 1250 263489208 263489231
    0x6040b04080f0a0503061201110d0c030f02030421051801121508010b27040201051e0313060b0f0a0e100e0c0a0305091204141203030412020c030c01050409 68
    0x4601079021042c2c20722100081c00c54409500c08040c600580d016503004880d04100e48549098035107841190f41414000c0c000300314a8500c9030003101980809080014640c0d00030410f034810703a4000c54064403440300e00c0c0d42d1100510244807035450b845e180c51800d14180b129064801c140701c02c06040341c034104014604503821052242d801804100364451014040503918003a803030291440001e0303280304036485a0b10a050071250140005840355462420000d80d41e150300645964000740c0d0b220303516083e00780130f459050105c100114010031644141c50750ba44000d19184080d10800704659018403201d00614005071240d84000003524000075001c2c2060755000c4107010340340c9441e0311096580705031000f804400e5014200070300300350006541c00e111036910300d500180c1d01d04000b200c0003585541040200440c140c1241d032110349000052041c4840881c0380f08552440d00241c4040d607490100e8000318980d41d80400000002020503005810b80c1c02e1a00e00180441c026031284081e025110f40081d00c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 263491708 1250 263490458 263490473
    0x212060315010f0b03180d090305060702150615090a0608040606051c0303050a0e0d08091015090b0d200307151407021f0f0f030204051e01031518050a090506040b04 72
    0x11000300e01b01220150140c0c210000c0201015100030741d45401008041195144085580d0b5141c0090400400c0f0a803030700414404949505802d000e80280184001c0c00c41c2c0c0d4604e050000206040e42e41d03450f403400c060800f0001c0795050740c00207100d0b0300c143c007022890307d0a408a02e107016405003000125592005c1849000e45140e000b854800e000b18005e0ba2007403034102c03500710b000309028811101498401c003071400444000f542c84640c5100c011030b0070070440e10f80da00503001e1620054592400000d00e692600c0c0190348034113030800d00c0303100707040800240e0a0402000000b0034501d42c1c4510340c00820700d006445007510040006800301d0015a885c25510303845500e0484440310414011000240d0f00c00070503409070002080c0008802c2110303816020320900995007580c01c02818241800700d44801403c1007140100c441d8141501d8100c0c0c0300d8941e2107140400020324190100003064102d442015048039001401c20760784030300c1c0000a4011603000036550798031541c01046896180c5843c01c04a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 263492958 1250 263491708 263491741
    0x102071220070b0715140c0717030a05010303030b010c1716150203060913020f06030702010b09040309050a0506130302090903190306030b16140a050c010212060315010f0b03 76
    0x4801d0b2190040c001001c58038080180b0780301d4004d0100306003070410212030f00f0503180da1541103070b8810007110100301c1006007040109480ca01c140215001c1c0040707894014450382080f514071501c16620380c010024541c0502400d00d6643d000d1030001d1141583e81e41d0840845c03000c0304050617081c004161244058207017142c600e0056082004500342000685079400070358000c0311454000d0540c003001c50380001042000300001640105440386074011001030203903d40004206004544d2940100030054840c86071aa0199001e80e440310201c50a03c0148651220540d000500401341001030b81040d02c000d284403010340c0d504440184258403080b9002e4514041c50806441800f2011030100c9180e0f01644032000700ca1081c00110042d540d40e10884035810750306188030022035004070814500f040e06c50010030b0210b0f0b50b0704000d801c10100c420f60038226000501404028260601031210724a0200000c02402000c004086400c2d070400c4c0040601c440f0f5403140c0200564040041807008101c60a101d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 263494208 1250 263492958 263493017
    0xa031e0207050418020f060a0c02100306030b070801050a1a030c07111c06050c040e0628030f11030304360f0207170306060a11030409050c040e06010201020712 70
    0x740280360742d0710300e09032000440745401c901c2081d11b4001900036040c1102610800300d02900c4020b20006641c00713002414000401c0d800415a030340c8004000544611050340c040d521640d01d10301c40d507040c42d05100001c505600708403803d000b103030384450f1201c130944100d96101d59040c49181d00c46000f49041c000c1801c0201e203055100c03074512036a041004820202d0f40300d043c00740d8802e000507102d612849a1521841c058403582144103000a901410301c0207212980b4488c030110003120a510b101020051030140d00129844801c140020080c8420001591b40e24081280610320300341c9010302c11100c200c2c03104400121506c08443d910074184407010402000407007010240600181d41c00404000d40c440721080710400c1112403aaa2001d0400040d82e100300b00c040c1501d031412108403000c5e504c19150120540481c2310400000c902c0182c00d000d1180900e0707030440510f44542c18008100085a03009101504580c030501c41080484e400f0300100b2540303841401d003d00d6440c0700341645002142200d41e038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 263495458 1250 263494208 263494211
    0x6131703070515041a1303050903100c030207021e0d020909161401020d02070509010b13081006060f020d12020309010209030703141207120302030c0c0106031101110a031e02070504 79
    0x10400380240c0b800100d02c15440b070a07110000c14000e0040a882c55419105161b59100c02c0841c60b001a0141f00103011400c0014219801e5911002060301079680c1c0240c88400603401042080440c140445a07095441405010000031000c03100444c0c880400854040e01c51a0704402155800105212040803441c0304420355115503243c2064601051134020781314014400c05054000c61880030640c032003510340050690031030380d1801301c005200350008481b000d044200c51a00244140c010848068401802580803c040c0d1030b040000c1d000d089d410541c42d040d034000d030461040c0260300c10380440041c8440000140c590712070b070a50764024090380b18111742510941d900403081c00400e04648103400001c00445954501d40c0500c07903428002c02ca8000c002c100702c0030000102c140030341c004d182c3c001002d03459142442500040c680c2956680d500a407403c04c5002d20007115540d106068550311009140140780304003079a030300100311400d540c607144c410150103002c102e52184240300030402004000e10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 263496708 1250 263495458 263495473
    0x1403010b0a14043506091f02270a050108090a03050d0b10120c02010c0905060703140d0209040501090207030203071211010608060109050610140a0512011211061317030705 75
    0x12224202e40c00c0d0300140c1a0146030600614040f41d0000308148a8804000a4001c0c0060314285c0001c0305600c1d80060710485d02401491160121100b27400c1c82041005107120342d45110005208030b8034400d07000281040880400c2010301d100c0020081c070400d5052915554641c41e80540100408840007060307405280800960000c50340030740000003000e01140f0400001b0031449060703089038640c840c10343c003048502ca001c100d41d140850290079502d000c0c2c1411524047c0803804160103510081003444250b601003500301540c20180309a40c050310b507403401145403881d1a200030f5038900034504001c165164000c0551403841c421203812010341c001e50003c1c0a02034031120f8540d15003209014950b181e42c5800e0000d0035510f00340c440109030b109a5120310134042c80d00388001c0d00c1a40300000200c1400420483c4000c081d035042e24660090241c2c0341042e072000c05514140d20020f22241c0c3d0f89100b400280714109010190080c0503045900140b440d21841d90780340c2c802401d40c0030b40500600079000d44030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 263497958 1250 263496708 263496749
    0x60a03080c1e0105090c1318080706050619090c03060e1302030f06062b0f110120060a020711090108010b120105090303070309060906110a1403010b0a1404 68
    0x10b0b03051240e003400e1511204044a10550790b088803800c8450341c0656001810008441c10300c0d00c40c0716080c0c902a2004913040085c6815032400c914450400c40c6c00400028414042c8503c071b21490b500804200d4403a4120444c25032190000f00c02405801541580c56402e40100c90013640a18010210000c0e00142890190301c2100d0341c92100006038060302850f611886111b8022502d1403107410b004200c152603500031404402d114130411080c0041640349010740c40882d40d05028442542d100f03c8040f100e41c910100010054042e02c4c009802d01111216850300440000c03924580c882508040143c1f50645424041d00e4150400a03080d0049510340c004902681d041d0019507641ca8161340c02081000d403c00315900f207410850f4030a070309800510114010728405e03001030780068051240800d201c0103546941c003c6410000384840405000180c0750400d58101c003840701c0c09401858014119858629003a60341e1040030904020071150781c3c0c1c600b091040f145c080c2c0d4041c10000402403202400c91 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 263499208 1250 263497958 263497963
    0x120917041d010515030907080f07030611070f0206131701060e060d05060718051f12020406020601032a060302040806150d12030204170307020a15020a0b060a03080c 72
    0x1801031150640140c1114070312818501d1410781260f6010f8a602d9074800307251804403041d00050b01070706550048074030005d01910100b2201402c030351071a000c0e041c51899444c00c081290700c0500e9842050300140700420200e01685400d0400b99010f1710032a40d500c101a00c10b25820045401c818900d0360803590540018005502c04010b072001c88444018039243c000800c211640d881d400100b0381d0380020000380029205207130303041c00707804610b4560100c03276203400005507040080394448001a100f4079500340c405520140b81c019030b0381c02090851030315080410003503c400f014000502084065102421070102143d0590322510a000408542c2905d03440b008011354846d109880b910b1240802090f0b94092559425242100040114603402c201c0c0e0b540d041188038001590080c164240000655442e01e024000b04a6900d000619510001481000005c07611604003602c00a540400105559000588211401d400003404100c9580364800207990400a8000a010b2040403034801c0450100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 263500458 1250 263499208 263499217
    0xe0304090606170601170a0e01060e0703020a0207050603100e09030706090f050c011b030e030a050303070c050f010c0e011206030204020d020307030e0a050c010309020301060504051006111606120917 87
    0x888003450f803548400004541d01030141ea0b0740403915400001064900440d50f100c101794038458000803825942d1400350402404080710080003280d000502c440c42c07a50305000d150060b15086440a046081c241c60090344129a4029408070201d002c011944440040069442541d405482408000c2a40c42c10481c06000001e044581d4891030904010301c0d070298100391161580f8003410b00543e405510304680c0d00d01c4c040c20b000d4041c02000700c4100820403d000641c425102500c54201d0081c003840c0c11762400348400442c503160303454200c10303c1e08036a00403600c0703121560034a00203c030504c5c0310145200a114650000354030910002d00c0e51030342c2006402840c07161810703840c1004000d0400c0b60035521451903650007030041d004440b00fa17445600030740c4003d01260000d00000b0b090354981000c141110303c02d481c40481c20342451010400365038002900415180c070340024012070645a21403036401c1e6018044c280c2440031881b401101454031358011181c00c0d80000520494040c0c8864460540e8030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 263501708 1250 263500458 263500487
    0x100e0709060501051c021204141005061c02150315010e010c0302280605040c090b1806091e15010e03070305030d09061404050c0a1211040e0304090606 66
    0x64104002911511441003100325101a1611031510031400c0070a45600242c0c4400059141e00341b204074034103a981351165204620403810f9030240307500e150480e4649000da011a140d51402d043c2000500c1d112008803044045003100c0e04141d10700c862001070031800c2401c030401120030b008410030541c6d41021039000c000310b80c2030b21100200d40d548001100c04180150020b800761707001030403c00072240004001e8092a002e4001050a074595540c0d0405070b900c107840c02da07144032001c8400d0004a80c40d1084812201084503045486000500c800a000d08000c1045208140c1d03000012801c00016400c092403c0709074499800034949034007140c140074500c081c04ca0018440603540d00341400c0005644003a282c0000c0194240780040070706d60301170005010b0444026403915042040c61101c8441103000d00d1150010304600300e40001072103840c0a040e0302c025816009101004003113100c26131b40701004001a20003044000c0ac0d03800080c07440c441c60b805041d48078078150340040c005030b215100812105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 263502958 1250 263501708 263501713
    0x12100303030606111e030903070e0a18230a0602040e04030807050f0d0203040812040b0403080f01030c090f140c07060e0c150a0306030501060924030503030703090c08100e 75
    0xa0701c407a03046032088006001c2c406507078030031741220808011211400030307201c8505e001ca82c50002c495010a09140311580080c100c00c1130b08081c0038148000b401091402850180d41024200580c2c690400c1504000c80000c0069820300a15080e1603003070091010894110606640e01c0350713503810034060280708941c1580000c4841c004183e1082c454011200c0140700408024103010300ca1301a0320084d03001400c02c41d0b642d10b08005481100840c820360512072802107991403000e00c7c06003405800903000070f0003240403119540040c030001d07482c00201c10547d034170880b00160441c04086004010714400e0500362202003820204111541188001d11160348500c1301030000015000d21030340e9680148100303550140440309071000c0b40c2e8406d800b91503a510a0318000c00c0441e0740f034540c20308440d0142c0103c100c607529110300c03030911502940324000340030000081e401840e113582c85603a1680000b60484003015200c03040141031144014900c005420f4480640b03406808181c44000146520314141e0101d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 263504208 1250 263502958 263502971
    0x140d0b1317250b06010e030f01050106110f190b0c070203100c030f02030906040b040503191d010e090a0b040902060d0515031f020a0306090c120f0605150a03021210030303 75
    0x2c041e00c994800c40e55900c039044102a480e10300054940c20340d0900915014442c05002c0b100c070300001d000b11802000d60342c65001003007040e100401d04003071400c44101800d0784030b5000910380c04a480546030600b9000210350a460700c400f10055a0340c07181d040c003c0d5152160092404500078a0b074044130401074917860230041c0315142174102c0141d00045808079100c0c3c00c40b00c001400718500c1040f13a640284100240c034645441070162400780c0f10071a1041000804600004c845a40580041e541411007400e01c3e025042c520342c00207201e02d80080c4034540407500c1d407500300a541c4494008005a982c002c25140e103481e0b124801d200208005c440c01e10070050000012510340c10089001c01c1d10a04a8a03016082e11030020410083c1d88000d841034101555040c001074440c0c520711134408aa9170b143e5605082d102c2280c624816200f031702c4003100d0704615055003042580c0d00d100c04c1341402e40000c12010307152040c202d8190004d02822610144181c505403c001c00b0010300749150080d82c0c4262801c0011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 263505458 1250 263504208 263504257
    0x5060916030f0f050c03030a020f0606010c120309020f03010e032106010906080402011713020a08070503070302132d0e2d01150f03030306140d0b1317 66
    0x119456440701400c0030040c00044000300f020b9440e00340085000710100c403424100c001c0400e18660040c1420340c01030300006410320304020103119464101324240307402084800300351104221072007400200710905540c1c207241d504644951492108556000740200219036003007503015102e0b8041818400c145441a001000142e150f03000d050103540181d44050328142406c40c152140c010103402030303051005403892007024120751801c0c14411117842a9041106031180305010051a96030070844494110940500035030310005000c0f01101e0b0102d680142c09c09042190300e0040c0307945c0c0a15400e09160a00d81d01e00341e100c60480b108111091a400c00614020401150b01c5264008e00c100201c04400306007880107245074260142d4181d0040002080e43d4039000d042c09042495110220074078441d0300400c2415050711402c8001c041d520800d014040e00140051041c41005400a0800e40c2c100c000c20141076403000b10340040e9921002c3d000242c48101031162158002c0c41d5035140031600000740051 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 263506708 1250 263505458 263505493
    0xa17010510020c010c1e0c03030224130201180807050102070b030709060302181008090c011d0d0c0807091b0318150b090c0403020a05121b010309050a050609 69
    0x1c1c40c5000d41d010b0312101c1d0300000111204140c0745400c0d500406900c13a0b24004440d1604060380d5a40700e4603a02c1840c034911300c0c000e4109022419200d00c161428121070007000b2950720a01c1d0300c0b00001200ca66403c180d4030059601c0b03884a12000360394001c1600100c0c078071030001100d2096130005d0702207a20480e52075203602c0e5103110449500c00000d803c180100003440c002d4002d09604203414076000224031002d804184148e14004980e0b00041c13243c801d018510750700303010400504c80c080c81c1501003501d242418041c654840782c2c02d00e009030b0004081a043c0011080d40c1d201411505041e181d40541e900d410001504001010340790502e0401000310905001e0711030f5642e6018140c05840700140180c4900210250100e5401d1496031144007444060340c500814074400c81002010742c2c0c03200d00b1801440041c203a107401c10750160b5416420300e482904009604820002482c0c18280c0e004604c000403000b404103070a00800b580f003058000020440e011a00e103210703061420480d03003c603014800c03115 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 263507958 1250 263506708 263506729
    0xb0f07020309060310081024030206031b040f120303060609060c03180b0d02030a0f270618050a06140601171e01180b06090603010e09070801020a170105 67
    0x2015900c10001e45166040c40d0000e1603000d60024000741c00542e13641d6410741040001d110720500103544a079081300110450382c0f410030200074125a0624182561b011550600c009090300420350038003c104414000902d0445000d031280d04000c5804035501e40c1b03c9070301030101120480100c1c0c100303040407031141c0c0b0070400c942c04c80d11580c0c1d0708080c1c990191002e46640c1341c031014090b40200300050118004907108000d00c1d201e000c40d4401685e07407500306440021260030200301d43d2620b0500e4920030b41c104650440e400c444070500c110f210340b5585c500d000f80050401030800b000c841d48d2072072644244003004c03500c171100f54010703e000c4c864150700345011102018100d581d680490b0b965a5800304800d000071030180e0003811a1198108214164071050780d03200709a02040144446a000c0400106203020344280510150360882c285201c900000307900e40014010311803482818400180c0c82001008100000c02548001315a01c01413040c008004910744000c04942d411410b0002405082940104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 263509208 1250 263507958 263507971
    0x901020901080402061c0c020f21031b160312050a140106120612081308030f0f03090a24060f033306090207060b01053c070f0b0f 57
    0x120b080e6966420441c4681096603092210680d600b01c3e0200b15040c0d1050013590a45034000748244280002d0091600d1400d50000211030b542e00b9002051044140a41e900b01100030043c00d0158481c4800d420b07640640e0a8458801584102e15824075410007407903402c600d04d01805001d159558600b036401e680700391a001d0084030442004001e0284038a4a031030003a07000d400003144890340c0f501400e180307c16464055404480c00516038404004990f400001414a1000ba506000c0e80d01e00011860280300364801d01300344000300160410b002848030250040d0320034103485298090306424024032031524141c00d0308a20b46440460400c0c1c0c002000c0040302d50040c43d110003071080b030f0002070840001904440314805810011014107200d8010311003d45100c440040e00e4220b9801c1c100c081d901040c91040c1440010044202d0592404416000c000ca10341202e104203180c01c42000d0040081c188010400040800d1050070005d4028072000e0341d030b0050701560001e4660070340020010310140e480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 263510458 1250 263509208 263509217
    0x108011502070b090d020a0b1b0610090c11010c11060106022b110a03020109061803052b0e1605030313060807051314190609030303051003021807080901020901 70
    0x80007083e82c0c010042c26000d502410b2440410303001e0b030210700301a0150704440710f03216010035520700100a80c6203003060200128000d00741400c00c4801804001c44500400304030035111203a08048034040d04130488101c07840d03402041a110140001802e00c940300e04c180300b03140140000081d02c030340700040da003840300700500a0349116101c180b60f400c06022818806800d210200c0545008140203108024a0500139000411080c003180303000d10448a1401c034207480414020310b041d000ca40c0c0482924041d0f00440040e58103880c0010410341040c50700201002801d0070507910701000c01010030301000100380000c11010340b40d2680d00f0140c4a002c0c04003000100749000c0c0c03040203c00c0c41945540d030000142e0070003514021250401c0400605d464100380c02036404d82c0c105c8852410030f410804c20781240101c2480e189820800000d0030901c00c0e1002078101030704c0c0d41c080758680302e405000700000d540c003d002480420388000b0300d8001440440704d1501041001c0700142035020107000302e5200300c030141c1d203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 263511708 1250 263510458 263510473
    0xc010e130905010b0a03080d0c080106080406090521071505010b070f113c01021c02030d02070c03030206010603110706020304060b0d140708011401060e01141204020108011502 77
    0x404500400c030850301030b100e42d900e40c07032055210748918510602450140d01c41581d100020403040098512002e804c0c820020800010080d05e5404140140c0055100c0408122541c040c1022882d185210f0410300403540f109000c400c2c600c98100c01000e2643c843e110307d0f42e0500c05803002c1e0084800074821000b411104000c0038001440c5101e090507000d100340b0103001d1545640000c030f1030014038458507909a90045019a204141c00c080da0450702100802d41138007003840b40c000035110000d22100f0b8403045601c0c108110224002d0064411841510504640f00c2c880b0341406081661184029405400b5050000c2007030780c420b004154100c0c0c02013546078544059541c814009500c0100151003007a5500c0004e40d00d950f401c6017204003180203407107007006179040301000c3e41000c14a520101a0b603240034569a11003107034240550441e00c5506000404902e54801079403180769a40d19000b07a1807000580c40c01403411208442d008a000303980d0000c0c81c4c0e80380c505e14015031b0030140c4100d01603480180f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 263512958 1250 263511708 263511739
    0x92a0405030d030e1204060503100909050c060d060b070507170f0c010f030204090f0501030203010c03090506060d02030c060a02070e0a0e2a1003051501020307020d330b030c010e 78
    0x403c500401044c0104941c0d5180c00c0307a103045081d4005820643c0000d0000041c446943d2910906c94007501d04400100a29400b0b1351319207607074030121030080c0c0c002c40006c41c13500030010482e40924000c06406010aaa902c42c510f41035480380d0450161040c441c50040c08101903550000e082040100d00e40000e10600c0408801515540070454823002016020000803c0e04503890050382c0b0003400324803010407203504610400d03080d200802d561004144c640660540402e1000410f5038010713200352103140d1001240c0c0042030514001d510142c2d001840005c0303441c20030768000303016000c9504003000211580c44400140c81510310113088a80c2541c010403060032107400d881e040c0300c04030b10111030075660185258089a0790700d42c440454004079030345d10204800400b03001c51220303910f6400d201451504d0703a90b43c0001c034190005031000c2d0802807404e900104c001c40040300100d0340340701300204074000280c007480305018000260030a400780c001c80118054035402840504100341c13005040102030000362 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 263514208 1250 263512958 263512961
    0x81902040f27081b010b0306010905060d0f020612070504030c08060103170904060f0f03020a05240a02030d050f040323040501050f040f030c0e0108060c07060911092a0405030d03 78
    0x80c42c05444074001004110700100132003da0800d000600c00010540020b401c0c10541000c0d016802030302c046044c03204104941e5615004490031960003028485202c005002250250281d4480c2c5451a0200001c0c0300d00503030407001a0044a1259545009550712100c03c4c1792900e4083c40020310030003483c2022054440140b02910545c807002e000041c445075100000c0019000d01d80c00200b045640905c10f20940c00d10300c044001901c01903640d100c03010b00c8500d03603c1181d48000c5004c100514045070703100c0700a2003442240c5141500302010b02250914203a005465202070354101e020411201c500c181008000daa50f4280740300403c12241060314120054810303034020003143c079030102c04100108400031028807010246000e01030482e030f454100035800350480e00c1a0442c00041d0b0042d801c008506006c0c07000c84622582c0444003041514a07840c003000703501c0c1032581c500c0e4004518410405a410790700720200d202410105100881000940d0724801c5106034000c01c0e8264110110046c503283c0607 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 263515458 1250 263514208 263514281
    0x408030a0e060403030606030f110d05190e03130504090b0610020f150a05010b120c07230f060a020909040b09070b1206010e01140a0c020a081902040f 66
    0xc180011a100d154444101d080040c1102d0890129544501c24000d05074144144048441e10120420031844440c042041ca03001d004901000642c80750009482c0c190340d07480700301c420603070403034140482e0249646c880d80381e4108a00b40910414082000079940c6440d019138182560002448401521810305021a00c2d80c00c03a503100c05e41c40f86155103404031008208030903202c09807821a0580f400c00800752415514103038096150400c0c1400744050851302800d00c0c1c2e030040b40203112580d440e41c6901d404003106c4400f10706040c0c070741a4140c00751910000410140003280d07285d42500c405a403090f50752402ca001c3d0401c090382007131507000020001440144015005010740040340ca032196034090543c60ba9203c0c030003c83c44000f164007030082d40e50700074610015000d82400e18034226400c60f850300e40c3e036018038104d4008101a007140403081d900c0f100b00d46006000103500fa5000b411100e20341108501c6c004078100c0c025464114906154a1340e40f241190480b01c070b40b034007440c1c92000e06848500307009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 263516708 1250 263515458 263515471
    0x200c01080a060e0f041e06270b0a020904060b0c060603160810021c0e1c0c1a150901080102041a040302010207150504080706210c0206070c0f0816140c030303040803 72
    0x745400c5d500c81000c0b515403c80b46d513104041c0456004243c16549800d511946229804070340410300e010000b4101480030356000e000c0f0800161601d00d03540005001d448542e100108090300090039003129140070920074803403041582101d2680220403c0306c480121188100815a002001c5081d092651a001880c0c843d03030b84481a98400b40500c00382040761a60127440e00240c0c0498a0188480210300740d01c4180800780c05c00c220060019116141d0900c11003100458054900002a0030303100e0140350302100010103400c030021503031182c5505000394024010b80007215058828201d045160604450a407039040c4e0141c48021715052000c15082c415886020030302c4000c0c03101207004038081010000030019075072810030400451601d01600711804004401450500728006921600000c440f6005603562414606101450400b81415999803c000709a40000220600c011104808200407140101d0300f41e41c04003c24480c5503540c8036150350180d0190814000100402c03031082c040d40c0d2140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 263517958 1250 263516708 263516723
    0x4021f03020d05010b0c0f06060102100902060c060f0a0b1504060e011110051501020303070e09060112020c0c0a06180501080a0e0607021018080910200c01080a060e0f04 74
    0x8051103085003d860098015002070140452243e118040401101c00c6078525200600b0280c1800c000003901e41c540780c12501c050ba0307200c1e10ba810854851400f211030501d850400c2e41d0b80d81c01c007001084840c5a00b0389003814840d0403d80301e11500d184c040d00b101821400c0c0580c40785410f02d002800d49400c0c4403040468148002c0300360b500d80452040c4000444070b01d09510018191030103500f801c1003c1402e40d079241c11980184201301c005900b100402058940450301290b01d540c0b00030040744c50054030f007500c00c421780c0003041078079000800007103044d401e1104941c2004c006071107060407281c0122501603114070f00b26500080000b0350280e80304a030040120b000105550350005141468040159101030042c0d0183d03a142d00da400691082458001402c004642c0c17118094844202d5800b80c60301c241e10844241e441c060190b801694440901c08400740c0741807904480310340e0750383c480c402010001c0c0822000030008104d89854801e0400b40c1d4010703044130381359440740c1280e0301020400a00031160311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 263519208 1250 263517958 263517967
    0x10f0f05190c050f010506010f080112020f060d0213080c0303070b010b16021e090f280b15030109050106080105010c030f090503010618060e040f020111210a0e0904021f0302 76
    0x601c0601001d60707102c9130a00045411308101c1c000402d29002c0100c00000c10813500b0050110303460010b103103000c190301203c8400300c1c0484400042c0760b138400c0300c40d8551000e100190074906400b40c3c004200c2182c90f1003064078000034420060545030300c20590028000540b000050207040c4015000c3c6c92200c0c44040b401c8140c0040e980860105007000e00038580700b02001d5800d006500d40445025071140c44891100c495091000204081c6c60750202c910f1210b81d0005401e40d14038000380d000300240103000b40002c46100d00d500fa09403090740280140b010b40790411001007212800703810b10324100c420607900c000003010652400c5039581c1d0140c1d200e03403c001104030001640d0340d09020301305c041e0808190607641040711800324000c0b100264060b1442032036a808100c00319030140811010f1680a08102c042d1014a110060404000170010ba046100e5016401507580700b03440a480c803c000c41c0c840840c01005501000513022040340c009600034010003110040034144035034050003055504001d82003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 263520458 1250 263519208 263519213
    0xf18130c03150b13060305030a0e01050d050103030e010f05073f05130512120c0307080403061a030c030601030303020c10020705011b09060504030206090f0303030403020c010f0f05190c 81
    0x41c40c816951100c080d6441d902802568600103130141181c0d80408000c02880b0f1550741c030b69450303008120f240d00910112031400c0d40c0c0380e4003c0c0c04962114526840070000c6603107034034340580301c03080c044040ea00040a285000c0c5a1902074001c031200f0302e401031050f82024014131a001c0441c200da07001d11081042004868842c107062000040350806203450b8103465884d00661114140485d5014600c581001c0e03c80e40f540e0700c004200c40012010007800303e640c410740400076520714810780400070011100000d000090101b15440b5090091804102c5d2810080c0031007010343d5014498403c5600d90060001000001c0c041d5000b40780581d07416003502d20707015440b10004126088103005a500341d44603412201c4007554004502402c20300303814107a50041c00e00c01d00402d58022400024010354000409042d556106038064104a0307000301144e50364542858000e4440e801901300501003500c034500d4420303d9001d21401107440c0f51580e101d90501040d004500e00c442a11071500e0103110050941801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 263521708 1250 263520458 263520473
    0xe07050f03040b070212041a0a111213050907120c091211180c0313021309062004050f01080406140f162a030e0613050f18130c03 57
    0xc02d5003d058000c8191030600c2010b4202046d400d440310300294100000e00000030340003a200000a91141c2140d121078215a003912803a010749000c4409100340001440800b00c1e004c024420540d448034a030405035911401d2003040301307041c1ca00da000714800d18159518008203500401c7c15101621349101c1c0240d40d461f1100310307800b10038815250295440405585400c0450b030800081c040d0403048442ca14040809a103603010240600140003101401c1034155a11045412401041035008000003140703403070700300000c142c002c0c2e17582680086d81144924000c1d03004181d608840014121004514184004654100e4000c20444046c1d550700b80c03a41c0341102c1c80307250b07520489640e03040903101c0c240501141e42c203152070560b4030b04011110704005c00303500c810124418601c48944820b51452250f150075140d207048142e14680082c40441e000101e1003162901c6011218261004500c8801c02028403d00845140c0405401d41d9940c0205070749503059640c1514150003681004000d5850fa541c500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 263522958 1250 263521708 263521711
    0x3060915020a05090918070e070306240e010207050a0b13080a0602031e19020a2c040b0f090c0702150c03070b060d150f0902031c091205070e07050f03 66
    0x1a0f408601c1c11000d040075540d07076401410000b449800900c0c0c0241260f5581d20300d0107035150340b02804010441c46c13030003604260041c081d123201401c0c025041d170255540000c01c4014250000d414241d00303103620f5001103001d1095500c05021345040905008034072142d640410303640c000e00e100c08580018403080074810750359658403400002d65241010301507007901901c0c0070074240340c01c0101e4041c81000c1d0300580444008040c50b01c009615032802c503009595100441c003803003001d99011005910104005c003242c2c010120300310703010020b98207100b00740042240048d0100341c000d40c0060124046000400141c01d180c0e20091418407086030307000d009215900014005c0280e5840800e40f0020840180c86090380000b0a880c3e509110303415031150091400607084500265550b81c030006800c0c81150001580950013a081340e80016001d4410034000700114909400200d20a00204100ca8407942c0c800b0100d4010700103100c428200300c0c1d0100403000c090001c500303000081180700303160b01100c000355 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 263524208 1250 263522958 263522977
    0x60f1f05031911070303140c07020f0105091008010e091b120a0c030c090506060901021e01110f040e0c091f090e010305011b030524150304141b0108010306091502 71
    0x1551140341314078014007501c1403410344036969138400d801c00204c19001000e950005404a0307040b881c8018010050344d05100b074510b200c1c1c00041c1c5480505500d508007800e64100c403142446071085039200072400d0b890300314800503080c00c034004071840358061905c20b1340740e103030301407030344140e0f12145c0d01ca43d5140f01e840c4541d0310880f581d0404540800c030f40c0d54584541da601034020f545e00b03480c000716040000d4503186041c0c80c01c607107a14901003030702000500354400c82900b440d10b1460b50b5104035a00b85462250868481c03070490a200c00b00045481c107509055458158010b00220003c1c07001c1c4c40c401900403502c0380d80c0c0040003c02c120000e0084903201c241d500860040000180404a59110801070a07095000e842403504010510180802900000810814080704101200d001c00d001850b5041d54080c011080c0300040280300502490b800a10f001c0201d04003140c5074011070031041c004903641e15802034049400301c401080070500c960040c1074000d204000c40401c044050070501d0498004419a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 263525458 1250 263524208 263524241
    0x62d08070608160207060504060809070302120a020f04150608040809060301090905010c020106180903050f03040c150c0201080a18020d03050a0e04020304110111030d060806060f1f050319 82
    0x40c0300480e02844000c01110f001807016100c0941800800303000b600c110320404c802c01c00e513240010720b080000c0c010710010356801000090305081e500001e0b559032801103400d03480742c6008140c88006103024403c1000302c0140150b410b00e441e00d00722094400341d40082c0141c404900c10070038592155203200007035020340182800040c0c1c0e5031041c200035084400b55000d02c001c2da8540342c0e092100b2000d00a000c02d98240346a800305140d10249811a540d020b02c4d036142d01140004018401041380303c2c1082002e84407074596607139100c461039000b01c6000260007006400300f070421001c1501c0042c19004861a6101c680740452003845943c081750b0140c0c2902410b070005080801d2608026901a4505a800000b101c0542c2181042d0b140d040041108110080c14007000314045000034078107006499464540b00c9007002025a9140450348075201200d5243c45024100120300382407a11075060706540f0f40c0046510207600407958191080d9002806100700c0c120614020600c12900380500d0240c98490603c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 263526708 1250 263525458 263525461
    0x60910030c080304090c051602060a02010e07090209040507050412110109050603040b04030e12030d0221040c06020c010c110d03110a050c03010c0519030207060b04050a0203070f03062d08070608 85
    0x2174100407a4081e014400400c0300410500203504450180240c00381c3c0c040320101c0c0d031116020001e0380100340b990a0340000c5e0040d41000138034113010382c0c003410300100255070500080c2c0d0758800031989441580079260f26620b00122040100d2914894004d04103410306200f0141034580d0f00082c9035400c215006c0750b10480104c00c00c82050fa0044291508032000d940540e81c502d011403045441c0e02032880910b0700f4981c08504801185410000031407458540361103221541000d0410158804080c0541000352096404209940d48640020220385030801c0f0f40c0c0e40d941e60098100079010003003420603810010440c1c414551743c10148201100b03107214100500c8503802d10002c0c1401c1d00c50958452040c480c062003c1003815882d0514a03483d14258078005948042c2c62030a0001401c0420100c1d17040703071a0204100d0340751070310360045014540d6602c40134211100c142e0100c045d5500d80c041d40d40c5d40c41070f8082c482e68194804089043c0c0c614009400c0403200c1d118030300f4925207c40c585c00840000c2d01d040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 263527958 1250 263526708 263526719
    0x30f021c0807061a0114031f08070806060a05182a0a0e0303040b0301031e05010c0c02013207020f09070804022d0f031c08010f09060e060910030c080304 67
    0x40380414070403015062103011184c4000281c2100c040c0700250034038600000025081198216801c201801074050441103030b91640781241c5c0c2d0303500c503004046440c402c0b100440c9103413402e114001e0484e4401808104040b19054030102c1803000600b0240f81c0420421400090b001c2c0c0791024100b1100c00d501d42510f84150020007004e00340d1118466002c2d030801c00041c003130880704004a905407504800c04800d100c9289001c018110345210380540f403035107400b44508030260301c1203813980014004d07a9120310308a000c03145c200c04441e814100200040d800c44401c88118600c0c0c1c00f6100283c0010580c40582d4642d80110300c2c0c0e48002c461a40c00654030002300821071400454003880000b0f40c1001484075150300c0c041c1e0104503420000c0900c40e000781d100010f4180d90411481c80d0354400003542c8914032017100405000d080081c001e41300c86001da54000b0079844d59900c2140201d511801c94420344d9203c3c10180500d242015001702c810340c1030708901101040030841601c0040030340c1c81c020740d61946000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 263529208 1250 263527958 263527961
    0x15190b090f0a140d141212060405060a05011211030901060303090605031515040314070e1e04080d0902100801081902010e0112021909080c0118030f021c080706 70
    0x40004034401c0902c8401404031a2441c00e05a401c640191035050002d01141000401904c14101c020101d11a03050080b500c02e00000140c444000c40d80f1003c4502d4403960300300320640c2c508032441713900180c2410041010358401c00404000f003000303c0e00060541c1c4401c00c000c2e4664402c481d01740c02a13446050401c10158420703054001014a40750490035414003083c00340c03407984124956882a0150000c0c214003140d031400305c400556200703101d550400601180e09490704078900c40d0044240c0604001254000720600c40171491030700941d90840c41e6119618250207400410804005c03981e5030302c601005840303c0d4842803e41039261540c5c2c1075589030921032403412440300d2080c0a81c4a50045050050341c100140f9104034009080c00000012030320b4a0000900600c010003460840700360580f15016000042101550880026140c0c260440c1c00151110465003500c2201c51a02e10f00800c080f41c100b01d103101c0142d10060454101c607089600c0f0110031200d4441c1510706800c00a400e004004070b9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 263530458 1250 263529208 263529229
    0x90a0609060335041202130f050406051f09020c030405061321020904081b0105070f090e0103030509090709032001110a020109062703080703020d0302040e15190b09 72
    0xf2000359580000e421418500d070307004e1445001c0c811045510450215550500708602050b201c1804020407091045800d02420044e41c090f116645081c0201d400381065012140b050341154004250403883c0803048002036001406000544c0014080460150380380d0703004050a400555040c4000c03802c00c1101391103261a05800c4950a044240240040e00c42c00c15181d801900801225120014440020b6590f020100142c8440d480e020421031655000144121281001d41e80c0016140d102c00c0c00b07010f102e400f03010180110340d043c0650b290500d440b20041d0703401399041c0b50115500d0340e00d55030b1641003250860080080164a00e4070465941e0011080b00d924011400400d00c49020740c0010301813030181d000b24820403410464603028581c401110b08a003c92810303a080071603980e030800b06841d8104010460040c086c0c40c04003c220b80c400e009a906483c0ca1021200c465100c07810311a1074008110740d4150043c041c03240014400b9000d5074081c004000c031401845c1e030340364a4002c100c240c1c2c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 263531708 1250 263530458 263530523
    0xe120f1507120c020703021e0409060c110f0a12020a0807030e010e040c0c0305030a0902030f070e070c05070b0313050f100b030307030c020409080702061801020c040c020c090a06090603 81
    0x5050f9031007030003030f9002469004072a016513070300445902800c1d21000083d101408140c000d4200440380d010006264010513000c03195a4410b12281d00c92072b051a02d40e0303000c0903460500c1d8441c81080010a601c0740603407031212907034011910048a2a921f203813a41d0800c900503004070318006200340140d60004e48003050120102c030700300154001404060200780d410000502000b4010001a0000e0940e600481c0c15a4005049030104200d500740b40ea80c4400300c1c096122125200030104821a01442c5c2962030140e011001e0300e0141e0070802100107035000280550f080c2c0c03107445d090001042d401d00400741424000d0300902580c06109407840159551208910701a40c003c116003408a0b500c40c3c030010703100750b0403140880e6010b240e04054115005020300603500150000b203108244e0030400480503010020713000d035401407120a040204544c080540000544c020384003400442c40c000300020344c003600607100047c42648502c0c1c0da42c00ca07402e07a00100e440514410210b000e01000f140301c40384510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 263532958 1250 263531708 263531711
    0x25120203091008091e030d110301050f090f190908030115021e0c010309020a050603190b0d0b0601030b31050c030903040312030e19060509010c0e120f150712 69
    0xa001e800e0642c0e422060498140018425030208084017050040b07480c7c1d07842c0c0728030030b11a050039880c0a1a45a10030310a041c0300311508542d00502c3e003005514148910302051a00b00c25949030030035130081180917460b00e09426582d84181c0000340d403442c040c42c047e290021640c80580400100640b600c0084181c90f0a284114403054901e0100021000301240c8286400301c0c0750708003803002c01c0728031010740c0116501030000f004110304058484030048001c001c00b10280030001c5104140321160a8603e4003070101c070700342000503103035501030341101c5891100a0003800b490361100083c21404e0100c58181020352429840d03850f10030350103010301900091440103443c99401c6c200400d640d01d1095200003082031612189000c2414001d51008c00c20703034044c905680c4040d048521614036414490003c58140d4035140108141d01414820006601c0094481d516500381000c01c0041102d45401140114490030000d5503012006020458158a88004010f0303e800c00300700180401c61401070b20400c05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 263534208 1250 263532958 263532961
    0xa03060e100e031e0412030201050603071509091d0105010801061805160c03172802120f1819111903020d061103072c010525120203091008 61
    0x81d00c000c0111a40c130101c081d068a151210005400d07000d002e580c4c0048010716030000300405058041d00140d00c6007004400f80d0340b00d03075242d0701c54081000281c2684c40000d004118184080d40040d03000c2c00c2000040614242102e42000d446400d44030260030a81c0c60341d454600400800104100541e6410000c0c0d000f0302c400e140c8000c2c04800c040c043c108900400480341341010500d03000300c0e0051003440455031340b1303200f600d17009840f8540000002c8560f481c840f041c1e19080c01502c03503132080d40d007150269a0800341d1510303011145114404050030414049140c440f124001440c20040e580304100106000326810200e030070486580490b07241d88a0041079540119214032622002c00c070b064075811511080400c1d010b04049000308060440007100038000810303c0072464100001d0804181ca001046900e15080303900310a142c2001c030358140c00700b6024840c105594440060086060302c0c007282c010a1006282c46408448910fa14084096000001c0c482c189061412a501c070308a41420100181d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 263535458 1250 263534208 263534231
    0x6060206010b0c100203060103020f070620030114040518010903080105040510060906111006080a02120d0905040f0b0a0303090e0108150708090a021f030b030f030421020a03060e10 79
    0x1121150844c03a001194000006042a0300039410344d07065142244070302c0e444403080d00d0840010000c0c00c042020034548089960380300ea0f200d0303049034181c600b00d0b21f00c01d28000c0c00209000140c00082d060103405c420510a13090a01c40900c9480d901d03900075590380e046075141900784030841d68090541d10044149800600507280c10400c2d0b04101d031054504160101e0400103064202000d01c01c1c883c250f1420a04001250a00000e1036600301c0c0c02120100c4018580e0388000f035540600c3e00000010841b0030f5010001442c1a6201050342d44012602013110301c11710b000180585010741045010070a005028010803000c5411140508000310080040a54110f004501030400409610410040300001607214009000203006c041d030240c58840c00c0303424120504507a01c400400000001e00d006002169898001090521403076000040c51a090404070203d0030350400504503191030301030001003001030f180d05001c100214001c8000251600c55004500c1c24010b04401c031013401800d054803081d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 263536708 1250 263535458 263535463
    0x16030b0d020a15090f0e070f0c170f040308030f0403090e01030b04080d0f05010806090c0d0b0f0c0412030207030b0606030402130506040609020c07050102240a05131506060206010b0c 80
    0x80e222010f00400390f11468400c03c880072040c03a00200880003001c600022000d0000704458015907140d10342440b03a003c400022503031f0744031211000d418a20810b1401c00c0b2100b280e4001c0c0003000f840c40700c203842c143e04c036140d1002d2544152010128815446d04100034907901c483c0e51070150400d025494400e51642e16088071a850190014000000c00212020312a046030301c40405888071a03000d001302d681d9500c40030348880044481d0b040078000c608250307480d03140034400d590140342d0000f0320804584401040c6110f445005003e03d1001e90100404035050940900c800d800900c00c0c2d00034120203040d0301e450301106102508050048000f4414031005035a01e02d070000340000c074a40002951741e50600007070084c3c82194400407000e07100084a40a450300420820107862003a000ca6004070325030b40b02c00c030000c85921240c04c400112003020919040c2c060b00416004004040c00085441091300d075184603201c20254680a1035461508100f00c9406205060041442c080124100b13140d80e400c464 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 263537958 1250 263536708 263536729
    0x10f1805060d060332010e030706020c150405071806080309010c0203011808070c050105031303080a0b090708160302090303090111121b0106090b0a03061805010516030b0d02 76
    0x2407003081e0202c2c904000128a50003d00115045841081403020361000ca01007100100e02d03200c09441c82010300440390070140280d0029021000017107240c0345103900ca62000790400311503c98a8000e004e100c424040700302020318021070040b80940001e91805124035202c5414907503014504c0c1c10000c0400c074091011040e6100d105003800c002d80b40c0c07121440003e0040c1074111860a0300b52107103149070f00b405007800c05002c800d0701c40c100b010749a43c0c40c2c0703006552500044039400c00c09a071782c0a0440c00644641e030f841c1c1d004200040c01007815038100c00064100f180032150500028001d90802400111018160a180300c0c113060440c5090301c0c41c00420303102d22446c0c8019040c008138201102c1c40d07410030045030310008a0140e443ea121868001010811211142c0000d01036092003c0840c4024452144031003010005203020030040c51a0b8481028000312205584600340c0e0b000b00b01e0100c1c3e001c1c003420340304696440402c0c2d640521100054100d801d400302032409000003e0203500140c4543c401d21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 263539208 1250 263537958 263537969
    0x307051b09061e0102070b0a090f0509060a030f1412070501150f05040903020304170f06010b040501090e0a020d0507080108010e06040c061107090207080a12020c061803120f0402010f18 81
    0xd00c0c120303c0000143e2504001d648802c40340440040c0b02410345030b01000500c10b035040d4101e15068503541e0300c200840c06005a5480350700102000c41000000ca0182d45010428801c0c40741300c0c4540310380310322582000c845010440c2620b00000d0340108200080c45071034031500d03588045001290426084c40039014503805824050740e13441c0040700905000f00b003690018050800344040d0b40b82e520545584460704a00b091f00584103001c00460003102400560b0140c50301039554014540c034144c1d201e1041714014003000b040d01d908000f10351049a183c000c2e540b080c0d91031b8540b901d05501d4000f82c0d900316001104010055040102400000740d5801d00d4502292494645a0306c60540c1d0b4408500b800701a40c04015414400500d240410454a0142800504030b44450380900103050080c0e0503445541c5149100d41c01c5040011112039915440400c200000303070440b428101140486004440152249021524403108002c11503a00101d06403918004c0e1508007030350003445148144020890040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 263540458 1250 263539208 263539249
    0x50606040b0d021e0307150f0309080403060c0804121d0f010e06070c030606090528020d020c060a0e12030a050c07020409030f030c02030f1602120307051b0906 70
    0x101e88481d9101c4402100181d0002d010741642d00744c1850b11540840340c041802c1c024002c0a90000b1031458100c9103480e40d40c8a038684c240b010080b100200c008200317104007162801d4007440003001148003445055441401611030350001c5c14a81000c0c1807441c4440d8844040026418800741407c000d142c22800c140d0054500d80d14010340280141d802c52408001990440030105911003803001c1028000f0469006020400200d07480356640826914102c420070030a403109030b00d00200050841a03c414008004da00504002d1410001001d80c4c0c400790310107900e035203d6824080000240e104040c801c0f00500020003104000740094492800000d048003c0310743e5501c001070784800140203d45c5c0e81a80100304000c41103944c5000b502407880184420300291500706010042800001110004a4900150342c02d00007180200c08455040b0001242c000d0141c40903042c0300201000588030691180e406068038080600d4001c6900424041642c17280c0491410b02c800c64461081428010814608 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 263541708 1250 263540458 263540471
    0xa0312050720070e0f0f090111090d0c050a0b1206032b14070605240307091508030409020c1204030b0103031d03070e19020f041712030c03040309080a05060604 70
    0x3020741843c075540d00c8014402280c40411502c44101c0e4929032040c0789030062601030b5291000c02d41c2c201d402c0a08003402c0144c04110925842c6000b00300903e02c03e00c030f02e041400c82602d0700e01042030401d20380e100071100322002c65100b030108a903840040c0d101ca801c0e8020f03c400c0900b60355000340c00f8580c44026610b424003001a041e05441303001c021a80400d142e080742d41e00c80d110b00c1c00b0030080204840c2d030300c0301c289030b81c8980c0e0b00c1d0b0502e0301c40900c184138010010004503081c0b4141e48020f242d89250701100510440001448110600180c03000304001c6000580f03a418120100781041444160204103540812080c00010030f900003080c1941c1d0507142451801c042080180105c0c020100f1140d032501c41d4190020701100c04801c09440740d180001c0605548400a0881c01a40204c040f01d43d0002d4091106000d10700d50704c0000c1d26030042a008030749035124501660401980165202200303c41c00104000a16410026020003000312000900c0d1803030442e25040c0d286c01c030141c0040c1c8501e0300e608 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 263542958 1250 263541708 263541767
    0x30702040b0a030501090f0b01060f1d04090203071d010501050304030225050409060c030c0f12110906031501021c08060d030e04110405030f0a020a03030c06021b0a03120507 76
    0x540c2c0020b1503011000b08003000c070500b0405001400000100c8021071020b00103d0307a00c0c451512850a000706071540411b405190050050307c90358000342c5a0040e64401120015075020012203000f004138003644403031008202c1e0f2880020300140c100c681405002c2041c80001fa41c0041c140302c0d50b40f004400503d80174500107103c00b1040c160750083c1c1d0300034185080c07076080c806254040e14142d65652030400005040040965400d844a540000401d80c0d85034a01c03d0421180c00181200c400daa10681c5003101d02400036030281c00503164002030f00182240c21b2083d5030104860084448080c41d60f0361080c041c00e0f0020b00c294002044203004803031101d411000c040c0541e09411900000800c184210f1140300e080c100749811901c1294824407911070350140b10107020a01c1e5407040d40190064580d1411a00c0907a10556108002c80d40c4030707400c108207030803950b03000145000c441c8030001800240c8194103008007026480c07603480146070700d01300501c413009030407103812092030360f20000b013440040000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 263544208 1250 263542958 263542969
    0x1110318100c030218011404180e06091e03040b04270c0c0302060f0906040b090c0a030b0f06030f0c040915020a030204061107141309120503061011030702040b 70
    0x5a594240e541c2480303502c1d03101680680151440c6804010b400c1040e201c00001128010380f201240a18504100000d0101d04c00d800c002c0c041d210300701c88012510106c02c8124600e0450121010042c0340c10904076580491805020316110706443c01c000c40c00e107800c09072141120700c51885003140364140c0901c0244400c183c1203980740350b070300417981c2080452071102000d400505450341c114010b0085a00150351040c041c04d40380e003d49001c200501080da5142e07a0440400c1020f407110540d4452001c0018480d0f0303498a200b4041c41c0f040749007541604107108461070245010f001d45208ac1c2040901c4590b64130700160300e04490004a9010a41c05c101d428941000c01c0d00c200e504005600006903690a160550001c1080b2001ea551b182e103081411640903032119507a018a980011108550340d07500c0c9002c1c417181221070389040000460601030340e20000b0145400034502c2c04076801100300301c0380e840c1681c40e07040d40079058204500d0113019041a80c3c0c0300d2160390708c0203108503900d810181140d00c59 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 263545458 1250 263544208 263544223
    0x51b01091202010f0e0303010f03142109010e01080411190504050408120702031206040b12030a030b130603020108040803070201090b0703020405040605040b030307170d0609020c01050901110318 85
    0xe000441d2841080000901800c4981090308840341400d07450040000b0020841e070403150019500340145045946a452650a0641e41c48c0184155105440c1444031881c00b440c0c55005142203550328a9920005004a9070310014035060117003807010800032a880341601142808116190300c5a0410020000e100e0300c003a030041da40003442d0008200400841c01c008041b100c03462441043c10707948000e002c0760380e4030941d940c00080e20fa503070021a0302811f041d01b03c0391b02c1520051248014800b50003c40307295401007100c5500103500c540a07c8040e00301005000326180c2e2a10080c8010390454001910800c40900f004001d000700100107845e0034400e601ca101560384c03100d000c4600d42020762004001e500580101c0d4461072600344c00080a04d490701c95480340c4003000c5d0281d03081c403160303845442007101d901d250000a82c50411511085020790300c280340c0504010440161107400300c1400c1801c64500400299850303240280c540481311000040c0d96010008a442c296040c150200d0641030424 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 263546708 1250 263545458 263545463
    0x10302120a090501111804060519030803071218030e010908030a0e120618070b18060702010306050603010f1d0606040b030415061409100e01090902010309081615020a051b0109 77
    0x140414940e083d14000e40d1b00b045054804c40d402c1c41074584900800400d4018064000203a072052803040001542c1c0038051540044141824005420807440035010b9803a9544c9211042160100740c00400d9003080f449601e0160a20700650703410306041d0310903038903c12610000103200420009400c181e841c3d0000465544013141568400d0811025000f501281d600b201095401088004161031448001740e410510b208500301c28072580c882e091110340c0d4840c10b4140d04160f01c851000c1002c0e01e0740c8004600a0480c50359401c41c0030300d82210030010314103081d9240c00113141c80f020f201c40340da164019a010b84503a802d40780d580ea122443c2104031002c0c2e90080319030007400c2140000f11700f80194010101c030081542c0c01d00c0c1a035148440d50301c04081d0760144009501203c40103100c05506907120422051040c10001401c40940e151030342590080d07003404a00343c8403110b9503020846918003030740001c1d610b05002d50400d010000302500c07d00402c08060364910501806054458094000a80464 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 263547958 1250 263546708 263546741
    0x10150e060f0f090307060c031d01020c042a020f03040306110408010f0f0e030a090611030408011109040c1112070c09020c060406050105010f0507060e030f0301061706010302120a090501 81
    0x482c807258125904800354441c442d001321540045c3c2c9600410041c0c01580d03066940c40900e0141242c050b0103010746c9100d00381144204910a40c40743c403103124103072902c2c200840341c0c021081e280001001d90304403565040f04541282005041104001066500360b1b5401100840e24151100031500c6901442d80030034819824001c561001684c0c5600115031000a03100c148011075034800499924441c00f01183c00080042c03000f00180303841900308a02c18010102520b10b4107684c1c0224a0a64150300b900c03c55540b4005280625450180f0404000c00c40e01d0621060308101007020a1322a5840120031001c4c11001848004102418648501400030140119101d04400c044181e545208840480702c0320300d0700c0e00111326036024260f18071980281ba9107084c80e001041e070f40c80001e00303903107a00c0c1c0803544014441c013124142c0500285000c4c2081e5512810243e07031090041c12141c4014107130b5418148100702c44680c14607400d10a541c0503109900101d1200c0841c50302500520448080b2809076 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 263549208 1250 263547958 263547967
    0x10f0914010c080a03090201090b0909040f060e030c01060e090715030e0a0c081b09220618050312010603110306101403070323270a02190e10150e060f 66
    0x2150198029506d0b0750003030741e642c180301e030311903410704400d10800d6001c40d881690300d000900001c4030380e01300400952107a0b01c082491440240064910b8100911020b1283d44515041c084c00114505540e0b00c08103441c0141149460305402c1119200100729110405d80c84607e40241c5000402c51010074580c0800e402c0402590381c0c00440d01c0d0082c1664250355000300c440b07454100c0c50080d05444c06032990304158505440c4002c803181e803411220408071350440d20340c511003124800c13007044110075a00a5014595902c8403010186040405800c607005152805035284500070010301034030391008064075062600f4013100740030384d0351010144100c84140c40010401050940c15000601d82d100000001d10031000c424903405c151600440386200101c11b8500540a034066441d075525410301040244d44071701042d50080741904820040c80b00c0c0d001242c24081180c2c1017074501c059484611071034911300543c00d00e00c00c02d680307001d40e401000800504801e050707490398441e021a42c0740004000303042d03602d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 263550458 1250 263549208 263549227
    0x2210d03020d0e0a02131d0a050a0b100806190f060602010204150e0616021203030403030b0112090b010e07050408071206051b09130b0d0f0b06010f0914010c08 70
    0x40d500090107107610a00b40f4407801180800050382c084400e50080103000490700c8446441c0c010001c6104044510180300c09041100600b4041e40c00360030300640140152840d00d04104107a240c01400000c0304030b0140104018442020501c50b0704007880c41c94481c2d60880d9144140094000c42e0b82c0b010340d00b1301c0d18a000901940550040040f00d664012000c11140e0700304050724404000c20003550840d0007000700382811034407000e010380e410388014001e10802e00c055000b00d165400c00c44088001c40e1390b0710f2984d001580c000245d40c8235040c0481d010302401e1031a0760380c141c0628046c4543c03000c485034013000c05c00145c01102074401400140d821141c140e541c840203540c840076022002d4030031904d4000030400c100d0b1040c004c0002600d03c07580181c40c1528000906c01d00f04103842000300f880d551000082c0d0f9640c1c0f090520f514a50085907840d00410203400c2180790104042c14041c10300c8007103409481101d03089500720089a48884000c140230000400580f40b0b000100001401c01000264042c503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 263551708 1250 263550458 263550461
    0x110307110d150605030d050c03030f0403020114040b0f0f01152d02030d110c03040b0d2304061a010f0302030405070308030117010e0a020609060c1006090f0b0306070c02210d03 77
    0x2225001c074111b81c400b080200d01a0781174030400d4030031030301a0020400030f09a423030218101c6422600c28400040c8280c0c0c1030850b9035041c04152070071210b60450030309200d07001600c904a41d800a80c1c1c01c1004045516207a243c00b001054100040180f040040a6002000e001c8409a140800000c101242180902d600075140ea10000301180741c03d190031000009542c410040e90a00103109004602d080d08060404913140c02010500c07100f80d840b04200c04410140039458015090175403078400c100e00700b07440c2070800e0704c0107550201c140450090002c42280ea00010060300e003c550b05005030340392201e0803c182080d00e1034001600c0030000000000e030b8404113055040c01c0e5140c0348002c2110900000610313489284e041800b81d0300040511280d0000d00d0b107640101b81d5507901100319000300812640c11010788465622a4103440d07590700b0f22000e5113105010303001507004d044000c2c14203454461000ba0540c411408080d004041c1c07481d00e040810310103442101c0c0b8806100849500d108903c00060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 263552958 1250 263551708 263551721
    0x6020106031a0f040f081306030903110109020907140c071203020708071503020a02211c051b130e0906180a050703140115080105060907110307110d15 66
    0x3a070949488507408000400514010700070b4010322402c00725a00c4c0c1e9115040703041c8442c41c0a6403040401c21140d0503c0c0c0d061380307120b00102525200440e4044c281c1c200504890903840660020341d044c07404100c0140d54080301c0d5a4031000b40c2c208024403c40061a07045a03015803260545503100e5070b80041000e030a44803401c41007504ca50f00310380703503a03403900012a141c0c0b05611604102000d158801500302e80a42c024000d00d407080e01c121418189420a40745000d40301d100e1070981950300240340d82100b0b50140c0c14001d042d0a800301444141020b4040034401c1e076090005400d016408030745004010303852140400104801009645036003840b100041c0c8584066850503210803900c130324082c400c0c0e80419003510650300900644000d03440c41d03d8124a074184040f04c3c1d50303295a200105800c60310f60202c45400307082c80c24000181c84c5001c40610070180d10143c507507002d0100825031a181280008110755149500c0001e54415034011808615440303036000d4014a03048d284560403620f00d201c0d60000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 263554208 1250 263552958 263552963
    0x90a0305070f050a0f060c0303020d14071d090a0f020c12091314072307241b0f0207030c1203080a0c051b0c100801060809030a05070201030b1302040602010603 70
    0x102c100715910070130089035155600c82c0c2c4e41c01031201d10040140c1405030390f0001100c0d021313040140c41d040d500700100c1c0881700010741c9503102c0e010010910910541c8465141c607801000010303135800702220070024031100e4008254910345c98881c2d4184800a200c1c0d010b841000310100100d40d0701070b007408040c10180c0c102c014001d00500c0165441c001c0c980300d5009940100c070a00e0040708003519030400807070320500300e4580035826101c644040e011000529004056150103480000c0e4100c0c92402d44e42004414070f0304103030402d82040d07024882c20701d640001e020240b4650400445911140304240c1c00c0c1205940041c0802594410000b56903a0500e65440100d100c4d54030a01031750f40b0030b61408210b82d00d01640f5400a0824050350200c81c112071040c40440c2240c10480b400340c854000020f01041441005070009010314004110380c9800c154410781103086900603500704207011100a00c5801040c101904040e200c2d040015162a158100400e81c103800300295903498449034081d01030419480308 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 263555458 1250 263554208 263554229
    0x3040b030115020d050d1d0304090b03011a400c0f030c0e12010603050f0a1b0302180606541017070e0906010302030910020f090a030507 60
    0x1d202c0d864804982d48107400883e817602401c1211302c5144100404141c0c840644d891180c41d2024559001080640b0051a55000c003140300c0c0c40c644241429551400115002008821300350341c4540da5441c0341000502e20004020311030031040401030900c034060200c00c1d143c01e00c40711580400d52400e0b0084881c0384115181d07a40c00d107030b2048c005c07011114243e2003900004d05d03402c3c0001603803603c0c00d06060b4000c4100300106003252680c03070303603818400d004d080754100f54001d41d1180e080010002c441150004800380c51580030f17156402061081c205604980d80c41c1070a480000c00b90b50700c07841600d006400c00341d603201400304c00e411102c0c3c190740ca01d40c0d04480480f5aa00c840480e2500d0b0248080c8250b0720b410f160307038041c0d401040c0a84410054490001c1c4000d001001a66000c0d407200c1c1885079078035980d10101d00e002e060501211490140c40d0504042c010001c120900e0780005007241d01103503540c4016914402c140d45c0c010780f4007030030001d9540001b034050b002080c018002003403001d80c2d01c0c5051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 263556708 1250 263555458 263555489
    0x180e010e092b02121803160819230d0306080705010e1201060b0c010902011202070503070b06030709060308030f07020703051203060604030807030305160302090d08031803040b0301 79
    0x1022a964000028001018040c950140303044007840788000180007543d004a0700100c809030084130f010307080460b101d40e411511190100103032400f00075420381e401d0148000e80c01c0700d0409440a4854020a405804408010017000304100d0606042d072086007003035a04504a01a40140310f450f03404c8100d101c1c0002e400c008020901400121380e042c21038034140c4030204910004418002000103c0c58910115503803200005082d0418900130000040980700000b4541000c0c800540000390712444600164414002040003940c008100c5080304d8000595415550782c0d0700c0024680b120542240450fa8200308000040200702c001a40c0645090940704070340741c1d107500e4101d0b600c0304107100180031036003d1440d41c0551280c01c8029508103001800083c5440e8a035240c1d190154069001103000940c0e500402c00c130325a5059507100b642e051860150701e00340c0b4200c00900002e581d4207000c0d12070f42000000c540203c6290500300c20141c1c1d50800d480d00e4507920050b4a109400034401c0a4450400c42d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 263557958 1250 263556708 263556721
    0x3030a0f0c020a0312020c1c090e06011407051e0703030201050c0a02061902070210051c050f180a0c141206010602030307260405100605060711040c180e010e 69
    0x2225907900559000340340c180881c0c2c80481d1210f0500c9228500309908000002034000244014480d1060074201d201c0c4c41c004c1510024040005a400380e070b407c10607070051010700d1780c0c0044440719015030802560340701c50040c03d00500300300195001c200c0d092012840c4149060000c81d1107001c890182d00208201c1da204d03c10000c45101c0c1138803000060f0400d0000817007a020400c2c01215151510f00018200200ca5000c583c1542a00300d03500301241011514011034094013641424004c854102131205081c502c40f125050440034000b0400c0380c01380707140882003030780c01c0140c0900107410076451b10b030003540d03903514000083e48100f5136070140b18410311520711000002500d41c121080f59000718075682d6001001c540340703044002c89905216556413030040407500707004054022400303000071700f0189000d02c0d00d49013115055403001d4000c44e802c0c083d4a020968a880707284000750f05940208842c108520210746400030743c07144628a4560315808038215a400e861281601c0f00440d8041c80d580303802 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 263559208 1250 263557958 263557961
    0xa0309050c0406090516210c0917010501141c03030b010302071b0306200301090506061621020a0b01050603181e0d05090306130309090e1f06080709020c15040503030a0f 74
    0x515116903000b084c4640030380b4251f29940f0220860000d4035101d04274546942106031424210300e60520113a444400510510341d500d81c407648c100004481c00102c0e100968624220300308a0071002d4103056039085050714590103501110341882e4009120111504150520550403805003c2074403803070b29124100c641842a0409240195681d02a041c00c6030b181800c82d402415004103003541064050044d903200701c0e01d10f100b240b182403207150302c03185440d011581c0402c0407032000118421940445076203000310308281902c0341500d030141c03425a920b5568051142c40342055940000341e43c49404140d208138142c010303c14402d6000c04081d41d040f0937800c031085416015488903035a040e080600464030740041500c06c3c0c00e4242c4030303060030304015581c0c0c400141150014441c842c0c0e0343c2c0200e5007000065000c01404180039040000c02c0003010304100919a680c0d078036009110100d0307130024003040d144104228904010010420002203403400d840d006440c0d1300b060700c416070258149512402c89401d01e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 263560458 1250 263559208 263559227
    0x303170c2106010302120a0902030d020606010f120b0d0302030711091b070f15060e09010203100605030912130e0906010303050f0a0905030d05031611030a0309050c0406090516 77
    0x24446919034044001d0750080110070042d060506050f4200905043d05034100c194a00c2407041180009100c3d8043c018582011a0740304000d0454200400700710550380c10424007032250380146460b01110111200d40401000480e1119502228003040e050406038000020b2000611400180005202c0302040c000202c005460200c400081e101c4510303101001071020300a00760080081c0c2032000742540300c1c0384940d0704012103c0c2e20a03460341010b2241840300401c0c26003000c0b00c0b4000310300d03510b8a04050207001103580608002c003e000000700306a62002c021040203402218107465a89074580052880c1d116a4810b0101e080c00d10780026180b80c201040303031412641c254a81500d8206124459400342e80120b003420306211000c200840c04d52810442d20800340a0381c4c448070b5490800c01c03010501280c1000b1400100001c04109090055010068a40310811400c0120310002245802e0b81440d210408080d001481c2100010784081560456400344450303403200c05d003049400380c0440f90703141c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 263561708 1250 263560458 263560477
    0xd14030403090603052a0309010614030c09041406010b0d050114090601120204080f03071e0c0e04020d12020706090b070809090c090603091f0e0a0b0a020906040303170c 74
    0x400801200b406908110351002c910001038a40fa11b01400c0d088000a09000000c0349030008070070840528070901c00d40c40600600103100003005141c80029070758048035258580140250300114040141d04000203c00345040e2060780da01c3d68588456a402c0d8221015026034241018000989116100702d48038040c2409407a00c030b03043e1348030001920131002c0c82d202e20034020740c20840050204001e100c0d55246821103c05580e440b50103050002c42c00d90503007141c0340f26003518101440054201d004a10440340c0300754170502169600d00003e0014012031038080d1500b09100d42c07041000d9408a07000d01521059100d16140c00d4507040c11b82020300030104004e140043c100001180380c03030401d560356400340c0034038000740c90150040086022030b0403d9031142495800503810719440b03051144007440c00207818608200c504c0325410760319660f00c0001005011201100081a41441140c04840b06038070091301032070365680e403440e00038440c50035280b21420520001c00418001c01c5070300700301c500050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 263562958 1250 263561708 263561717
    0x20a0216050637090e150d2d030323010f05040e010f060b1804020901090603021b06090c09100f180605100c110909120d060b04080d14030403 62
    0x26070114a0311415080704041034081088003101199000800c03c1d91550400ba40c40c001281c4c90034006074840140a48900c50a505030080321000b0703140c1030303010309840350801011f480340c10424808016a021407020740c44100040e100e80700034190180c00c0034007020103490780c250b8410703480c0469018481d82809032643c000400d800800240c91705402212120144000002c0c0c880305458034241120752a034000c40d82c0034800700e1445004a0500c002000068007640d00f50300e028001c1000811070043d07401150203143d800301d441ca000c1c0800c002d5a4460003880c004441140c20000050341e501c80440101e14420f0b060600020a5070508002440485400c035603c03011150901e40c1c4804101600495480c02701d0b03682c2d20002d919a01c03450f168900203044e03290001410b540342025114121008045405800c00c07000f400001c040c009041c0c440e00c0300100145490310780c8441100007421312540244840c444c041404550348002141240030518a511110311800c00908040c6203800105c033f0240c04035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 263564208 1250 263562958 263562967
    0x9111c0c092c0d0c08040f060305070f02030c03031b0d11190507020d03050a11010606080412020a05060103020f06120f0f0f1003020904032f07061704020d0f050a0501020a02160506 79
    0x1039014a03400c41c0741300e10a03d0f10701e007026154105101d0910b240da000e0300019032210103009115030441940111103c203032025503e0304003080c004030350301e200141078000c8021880c100d41c40c0500002080e520544940503041c460900c240c03512103450341004075200d40344020f4500300d999680c001c2080f2a07440358042c001c84c00100c80d82d103050b9200e400070a0360a050008407000031405480038403800002d041c250321030410034101400c0404007069500c00400c295800210340e0004a50002421070440b54121950200d40d00350401040e424054800003825400d0402d0620012603c0b00c1410752043c0d020001d4941c00d40d86000009045403c00e85444100c080e00035028800341c1029000c00e07601501a0800401c1c1c98503d000740c200c00349070b5884400800d5043c000507a281c074424000e1100074101032500f0081c100c456280c8865800e80500020b10514a4001c4001080b091400c0d2a01841d0088141d40c11004182010b501075440030401c1e01c0180a0415143e00c070b50380100714503094810180403c1d080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 263565458 1250 263564208 263564233
    0x6060607030309050703030320040e13030302043b07050a050c01061a22181d0d0c0b0a02070308070309032708060a09111c0c092c 57
    0xa560203203000754101921060070030f0100ba004c2007504029031099500003114a941c02c0da0402c441c0a8984a0b01a40d000308010040d00d6000100c031500000d04614044c0000701074a402c0d8001c0c400c036408091800c030f0003020360901008a0381c1074100003100800401d1015030304001910000b20895444001c41d00174800000140c0c4a40050480c40c8070600c00003401580f2240e841c0c00700c15140710b41400191b0001009801d12900340400d003003113491a015201110b0502c6030707150b004402e010071500360301d81e5026074802000482c0c5520310006440380988141c02c4072200c0c0201562819401942c884403118042505004c0620071180c5040c1c050361020266100d404045003e800d031150190b0801603000d11b01d81a000300c5001a080f09103035500c401d41e01314030f03005616050450080c540c0001510345036186003c61016810401010000c1380c603038424458010b0400061000341c0d40241050140c001c001c030f0180d07615803104403401c40038072928101d00348980e000040000001c0c8080a01d80008280c0d056 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 263566708 1250 263565458 263565469
    0x60606020f1002070c1e05030109060b040b0f09060d020411030f1f080601031e0c150e0a0b0a030915020708070605012102040c03060b0c0c040c080f041101030603140a20030606 77
    0x8240000307111211a503924002270a4444403501605c0c504c1c0c0da9803004001e80b90510a4401d005015216240782c5048a0009020200028510350183d51031550f04070855403261b0001e1215141d0111183c0c032401d00f2a941c44c128901280c1c0c044c0700f03085c030145001c0000c0039241e550040380c0040005024507821680c40e84141c55800c420200105203042d400c200186e80d05861030080e1a12052621128001040c01402c0c000c40b01400b50162516060610902d40e2540c100c50a008150901049201180c0b6110071003111a660544000e0300c04036440c02004507403002014113500034001840f490f41c0b9000e10180c2035910b022407841d400003804101d001400c040e041084d2040141c00e00040159507051405010340c0000304505154000400750200d1380351601c10700000307180d58603109882e0b15080c844150844405400030384200060800c6441d142e12981005d00a9640482d00407030504024918543d0340306504070843c0c65007900b140d2500100c807090003480b0404d0009004050f140c460500b07006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 263567958 1250 263566708 263566739
    0x101401030b030d031505040c0c06020f22051e031009060f060303050301080d111e0c060703020d030b09060f0402031308161709010f08090a060606020f1002070c 70
    0x606140e00c80c864010760b540d00b4880c0080c0c12035207840100c1e0b50a20310601914511103900518880c61800c0d003603d80d415803241c0d00040baa80d0010006903144180e400c21307012030007480140106100f444490202e502c0090203030904585003511300001d1114450442c0d00b01c041060300f0300ea019400041c0390101e400303c1c2e0300032400032800b4050002d1009002d481304829102141c2050303000c01d00c0040100302c007150070481c1e031401e1600c03032503c0c510300b12041c01082e40300c2c0020301c03142031000304031114580c3c141d50510a403040320300001e084696600311441c02a44405402e00c1c07040200f8500380b841c03001e0341003100313896116100040603228800c008404100007904040d01c0480517408003d17041d070000d001480180040c000486100e01c40042c5880c1c181c064030000d103c010b807889414070007120940d810107040c29180980d82840046a5100c0441a2800d890600042e05490a02c40000f07682078000ca00c60903219042c1007618029802d9103284410381c461003400401402c508101045502c50740d07119034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 263569208 1250 263567958 263567999
    0x15070c200a030b013b010e0a0b0402070609060b030c1c1b0f0f06020102070803060907020a0f060f0b0a1208090a09020a0801150c0f061a060c06010e010e10 68
    0x4080355125155940618401d8010117103513800d0343c1e02e95804900d041d140c610b90500c00c5618607204962481550301c2c02e4410b02c0b900440314400d50105100da001034001034050440034004545449a90400324040d200200003541c2e0a46001400c09880c00d011070300709001c1801910140601c926035103c080c0d005030445060703d501003840c458210050041c104000145001405292000d050040c846884480c2c1e5005405682c410001880050408001d9941c030000454421600c0c1e6508501070307003040d0210000411903440d0002980030003400358440d6100c0c07140c07240300b003100c44403038003d00c910345202e8003404072a4001c3c1c0740b4040c00503803d03030300801c0700c9600070380b90000b41030341d605c400e500ba60410300701000803400f14001404881610000d0744098030261409284440964030382d414101100800076010b60313240c1540203ca0960341c2c0800b50141c1000d8480c556902041100d103031501402c0c050500980b000c01c2c00000d140c2c0c102c000c0c9901840109660700107041c9441c04114100c20b180344103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 263570458 1250 263569208 263569219
    0x5090402040302041b080f240109091d120f07020d1a040c0306180840031a04021c030c06110d0506190b030a020c010e15070c20 56
    0x4030043c4c90381c2c042c2c0d13160703c00240c8518080031700c4140f024186520080803900b20a0401042080715070810148000c08088540b00c01c10700307042440125118202a008034940c0e13824004170228007000c544040503039031841801d07a2503400d040001c0d4109441440408080103078148085000361528a401401852140c2d00c018442c20b0322082a96440d07500300d0303081e01e0320490840c08005002150261810861148000e40700360003070b6940303986031402080310340710301c4042c01d00011000e1040c6005158114035008178451110140704000001c40801d400708035000507443d14000c08140405141c5030159a0007000c1d141519144012682e107032964440c16400c11440d180c0d200003051507481211034001259082690f10718490200701c0c02c0d07402c0604424050030414048000700840030315050242c5003541103e5603251507014a00b40030307000701162003040e5403074505000d4900d4800940a07801940b04010304000e59107114065a80c0a28180c000d8980c5a10071320703141404038030700132603a00c01400514 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 263571708 1250 263570458 263570467
    0x10207090513120c03020d2a0303060e090706180509011208070b04140d0f050f0901020708012406030204031109090316110312030405122d040509131205090402 70
    0x642c1c032501c410703c1c2601408a03c1c403070b044405050381800814040030442c240b0740d080d003611240365581400b20003902d151141a410262007098844d4110034014001051854001c1c20300503060398541d01c2500c1500c0200e0a440c80d103c0c10070f0320b0003500c101210700091960041c0d0f86011045180d8800c0c80508407800700c010040310b00010007100d181c0c2d003ea4058500590710b0503514070420300d071a2001261109002c0010134401116a210044454070411500c50603169806640141e1038800c0e10f0300500901d50a00180c40341c00c030700480102034480c145c141c44c0840c0c80d0ba43c0400fa41244214003000e409010038652078510380c1001218540c0220810302200e1600881c00900b892014044034100ca01c0d00250304442542d1800300550fa01200348510030910b1410076680300c070341e10701802c0200200b000c0080b0780c3c0b01d4110000e90182c1104510910010a0340d9020000c066407540f241c018144149400004a5024810b0f1402c81d040d4a03807050740581c6491b442c141c03ea80341d40200300040c0d4403540812 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 263572958 1250 263571708 263571713
    0x90403140c06191406090412030b03060c031515090d030c0803090109031101111b1608062a0d2706091514070509030102041716080c010207090513 64
    0x80d540b2421071000c548541486503001181a039404640840b0525000c3d0288202e950b510403006401603800303481101582c7e00c5880a400ad80240e00f000d60b45401250304224030f6a0356480214400c04e091110541d80c40030300c208101030a003040c0d8122408610620400009045c40301c1c01d0b0704d220340603061000b22001c03281d0f5504071542c400ca41c00c42c4c03641d4640070041c08041d00b001c41d60802600347c40080c030840c030b00d1480c440401c1c011850450200c1040360741c0760225007000d2208046443c00d0020002c5410f88851646030303200801c0e91100102000040412092000a0545801d428041020f940340c41c84151b584005020851000f10a00907a1a54001c00049050410036550311a410110b00f030b4149003010190f00f40f900c4141c19280d414507a4102c0202d221088080d40030540c4d0500584078149200441e009010396001200030301302e1001140c3c0542030010307125080500f03603401000e406840340080394076034800440d07960150340001c50502050b0026002540e002d1802d0881c00c40089154 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 263574208 1250 263572958 263572963
    0x1d06090d0809120304050309040b042d0204150c170310142107031a06060405060c01180c170d0f0f050d0c0c1a01050108010e06030307050138090403140c 67
    0x176181101c0d16440011180c1035420700e4000c05411070002c4904104000344e0901641c40c4079207101c4a010070071414500725171103190396410790b00070700002c0e05c0c0340c47c02c001c4122002c1d000403181ca20540380040c445100040601d10318044030b2050728240342e000036451030926a20a60710f60001600d41c005400da60445803050b02c1d0901e90000340000004200702c51a504041009500b00041d03410301070320000800440d5142e4908450448100341c40c002e640380e800400c564014000800070390080e00340601d402041c800091021030968429400c1c1d04801c420b0360081d65950007039240801d010079100300b601702109002d070509034604035541c2011840c10486a051f5403c84555030360840c0420719901c0d100090024881e21030b5900a40349400083d0740d41820006407405905124650f503002d0508001031782502c1c18400e880d1017942c4240288242c0c007030740c961a1501142c0381440703c291802c04000301e80005080c00c282d07445000c098015541c5403516103007120714075031a1011000d91a001c100c62051740504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 263575458 1250 263574208 263574211
    0x3090d030221040906050307140909030715051b0c0c01030c12021b010b01051303170412030e010206060103020a08060d081c060501030c08090d0e1504091d06090d08091203 75
    0x1203000c2c965441c00c01c0c0038082141d095803c028001e500100c004d01103107500399401d80210100300c8111441d035071000749151443c07244510003400c00750010b4840030140001c8d0060390140c540411500303043d10543c0c40c404054000c4420000950384442c4084440754003a40c80100c1c006d00074900030b10040c0150085d401a68070001556221801040301401c0180080c4256480c444091825601d022184c00341607203085183d00024108007810511080c0c12046407086038000c1564021083ca001140d043c06003040002910b098094040c810001d02107610074421568143e00c2c40e211011981c8411040c00300081c00386000b128211800c100041d040e00c82509400c1c49020054004920307141804001001d03901e04211800920403c4802d0107104040403a0081c516040f43c0f82c203005040e21607002031410b80300d00348041811200040c1c0880c040d1040c1d00460107420b0914a6005400401c0d40c416940c0c4008441180c5160400340f03044140b80c0c41b6101e0f8940114854040340c00d090307210300c5000100e030b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 263576708 1250 263575458 263575513
    0x804030c0f111005071211030d050a060f0602060618010b180423091006140906240d110307020309010516120e040e06090c060c03040306021321020303090d0302 70
    0x1020891700100004088a8011000f262401d6400c14504010340d13582c034041c01c00d4860407207480e0400240031071401e1b408078009000c800341000d03100340e030340341c0180d04d8141c295001130103022060014200150440102812249601542464160010048000c0381d90700b5000f15841911400d080b0030262442c0412807641f0f42110664140c0d0401c0781005217800303010020141c0040c240001006820035054421850b1031058030100348036581c2100103041801032408880c0b14441c000d05408a0360165405020b001c040d11404112100c0842c10046850104641200041c0e10801c1038000651190000d8054034001800c004a441d8043d55899042600030704440c0008101c000342c00b14900d450301448003660040405400c1a00701480b580c1e8450000c0460070780902c4001031036070310300802081280d0056400250440d22114420100c2030700050310b1194660795502c01008a4140d08030502000545074000c0065107008224401c0c0150b8204250065055010b0343e11421400c40044090300364004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 263577958 1250 263576708 263576717
    0x1060f150809061005010e010c0510020a032702010309140304080607030516023c0303040620030114131b0f0c0201090512120a090e01060804030c0f1110 67
    0xe203910801040314000500c0601d80e0390240c02401904050210100140e8200b80703002d00d03542e000fa0006988455081c0f000502910039091340610440306907000d401096199030741404501500c0582031650581c42090315a00d290220300c3c0e100560195200b03d40042c424124010010002041d550071500301ea8404000f0f0b8005800708600540d15203e042d0f40200703403003240d05030ba0344030b4400259284021b07009000c09482c1078002da50000620141c2ea00180090301801003c20040c02c5001d40302d400943d0211502c0f07040c001e002d40da4510294410b0780080a081c05642141e19010b001e0b9448a10075031a1034010428940c07044079050340b400b964200784400b000c1e0780c0034051017102c0200b55981c00c0000c4d0040203448c0c54280b0050380e000c429481241c60450344030354441c00b5206200d080c071045a0141896802c0003640101e640d4119040f0001c0303640500086420380c0c0d8980c81030300c007140d089400400041050100d180040c203140c0d50800a139004400000c00300582001282d030805c1c00c030345e0650209 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 263579208 1250 263577958 263577989
    0xf07020f010306150c11060a021506120d0813120203030615090d110604090603121101020301060804390f090209010c1e02130203040b0f101701060f 65
    0x103003811105041160020310702002264940b202c00d81d80f160a2602080401c100f10100e4024400e41c0b40394414041d500810b40e681d618068800a962042546044108814048000744140c640071809500d00384510f8090954003d00ca481140c41e50002002c401c144040e0760350540100754050241c141c820950340040da03490400204000220704c3c1d2540c41e0303e2081c400c020300c01581c2c4401d000e5542296022a188480d0f80168000070740600840d00501c64107840d042c030010234019007454810541035942c44294030641c103004100c2c203130f00c0f00f401150046400440402e000800051501510398041e17030540807540c0c20b90942480507009002c07400e04525202206010000002d50450000c03c41140214940091003001801c041d10500d00a000d1006880c00e5000b104080301c1c8030031415034001c0020307251780b0380d0107a40c40c02500140e40690318102000b0025143c81d056116150007a03894400d14580c003850503084022940c480480f5800d207548070600050074852031500980075010100381c01004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 263580458 1250 263579208 263579213
    0xc090209010e0d020303040510050d020d050f220f0204090b2509140d05160306050a051503150c09030102160519080910030605031606030c020c090a0203060103060503030f07 76
    0x9010b0000e0301c1c41030400350203010060b40d00208032802c844082d00e40759001d0004150540301e9000e034080200700b2078000215010401600e84c80ba9100d5004102c1c8542544c03110040c060301c580011180c0c1c10b68001003070025020800c03085540c1840c5100410100d0164596034600707802480a44401d030b07100308203030070b040a010086000440a406a45468502c0c81d14140d8110134074160505154000c0044a44d6903003803140a011240941c003107a01d10010f080d03540d28200300209412100441e289141601003000b0030f9049404801070007001740101250b100c00200380e055540701410700760346990208540c0156031000e001420541c1c038404d540002401842c20700031700700f014803882c80c0a0a80b254040400140c086420b9901c4004180c42806200e04502d4095004080340d400c042c1d858031a1451000380e00244810440664866540501608510703440c1640d0f540d6064150652182d9140c0020b60a80a07503400f035030b40600c1c1450b01054050340c83d004281951302c05e280304002d0281c005035a10070b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 263581708 1250 263580458 263580467
    0xc010329090a0b130507020706110c04020c01020f040e0f060d050616111506150f0d0c18030605091204140402090a0509012909010e090603120c150108010b0a0317070c09020901 77
    0x10546820300500c244490000c8ad070f00e41c80000f080d144915808641c4100402c42581554921502c0c241541e0350f841d101d00707003080302e200219070300303165541a4070000e038240c18150300b5403c07510f5115000704540e840302c10410701345100c3c1030801000c0002507109240648003c200e6464003408060141429040003004d0141400c1080e140810b0302ca0204004580e0030314100803250025801540000e00c03514002003102c601070300011003074180c403419402200b03101c055272203140201000070032181042842021000213015034800d00410742d0207100707072407564140364000b084100f10090403070b101c03d5200c10000307492100a81101c10202c2c4400c0501515040c1c640e10301150045141c280d600748400b4400003000d10710404846801102e04102051060310100040301103481490f9809480d2442a1519035641c0c0191210300d5510000f50000550144103100d2150300c5100500b900310103904688942c0c00c00300388103d0f081c58102c8208070900c0800e90790707101c48000e000d00810150766035131311000050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 263582958 1250 263581708 263581723
    0x1b0611040311090402090403050a03090b190b04060503060a2c0102030f01141011030d09030509010e04111e040305010e01020a09080c03250b07050c010329090a0b13050702 75
    0xe0085190f00140005070760b0340c9410740d5100368549003540e90b07002c1d1020114080c0082d01d00c0200a00d071030209001880140031043c105c1d0a10100041000a03040c00404c010341c1d20620542c0c2c0c050300000c1c0440d50b141c00e140c001480a01c205280072003000101626980c403c54810b040c1d00c0d583e5030210601001c501400e0282d03005082c89004000c08205007000103ca600300e0035407480600a80e6030030480c10074000e00982c3d11043c0303940c0b403c2242007041d04000d0443d0340700314000c070b0024142581d040d00c81d14192084040c1c2001102150341400514101c00c2c078603100c3c1d10078100c0c441c2018480040060300900400094501c0030380096207848412601400c0b07001580c2041e005d64202000341d11064070001100c2813031400000f03a10111503400600d407903407200c29800030400000d00156150234040001100108040281e03410003000c3d40c02e54614a81c2041d160755145520395280c004401480c000d020307e074015221030300000381e86060341d000481071082d010b450f0919513181c208010040341c041c0301d4070303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 263584208 1250 263582958 263582993
    0x30901091e1101030221070216150912110324070c050312060103110a08160c02030d050a0201141305010501060513031b09060e090709020f0a1b06110403 67
    0x10a0901d5560399054200265080d00c1e04041d4040780440030090300c615080310701155810082c00c03d04003d400203444080410742082c8030103070800000340c07510081780410304a0203075645801246040c0b42003410041d440306020344004d800e03a030405090303a90920034081504039207002c83c6110300400c1c25010900700020703c01c0c814000d55010702000704d4400320446540d08078600c03012086030781f05e00059001b004501d1001301c05000c04152840303a240c001080701e001e000000184500c166143c4c804803030044042c2002034258000b0400c0000403402030001c0c0601ca02c00e80004120700203a00020140341c070080b00e1010044086207c00c0e81442020700c20940500550325110b454000583c040b10480c00c030520005080104a12540c0102d44860f40074074007525082e8800c0c00100e41d40c0444103020360b03055a4000c41d80c0035071a000522180148200c46203d50040b9a4a04049484406951240210071001c1c400707402c007140200010041c1c40383c412080d9039207881c40e4850f0700750305249400b00a4a02034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 263585458 1250 263584208 263584253
    0x10030c0602011419062402070f0302011e030b030d0c1208010509181903050901080c270d0210050a0e0a080a0605070c0b0f0105011b0c090b03011103090109 68
    0x310742c01c0403104844541d0061202d010042c20400000ca1300d001448140d001c41400c25441d503007000c04140c283c000d841c4801e40da80c200c0d0b045903159240140095000d01c0001e0100d0a40005040d20003800708140148801d141000100c0004040c040b81c1000e4095007d440061420880641000940f5000101401082c5414000b40d07040c10040380c2c031903401514000000661110f040e41c40c000402111518042050343c03407051040c607140240c210b40000382e0301800b094031072001410b1010403e003034841d4607108681e05011084000c240a0788160302075080c40d0002001d0b00054056140d42a803404a2604c1e651030907a47c02e601d0000030030711088401d403240324030302c242000c201c0400c00060a40d05590040c400041c103844610095410a02c003850050906100c1810000c110220600d4517041f6002a00c2e114198040301d240485440001d1000502d4142d05950034441400e50380c1c003003030082001030000079a1078a520079110f02d50700300304d0344082240e444000020411112034441c150116000a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 263586708 1250 263585458 263585471
    0xe06040c06110c130b0604030c140108070c0f020d0b0f011502011104210c08030d0506040506011d0a05030313050a0618091505060412120228140610030c060201 70
    0xc20b43e110b840207140300f4400e100c1c0b0201d0b80d03950722055200400e012801014255540c0c3d4071719000b00d60b481240310305c6038003400000b1200400d500032240584145c40360364911420200d69a00d100701d03031714260002e0780c002800e0307514840011074048000703002e0a80315150305042c1d0302d080c00e2003a294503603186402c01c69040800d448031400e0100c09903001c0d520300d8241e00f81600e030385c40041080324500d0300c2d0181c0050b00b4008002408207010001388041d00590360180440d580c2d10307090000b07480c4180e640074006100b8151151452030f0320030421111050081c0740c2c004c0d03c0d554500080c0303560024805800240c0c5419400c22071841e10042801c0101142d0a212154004004020b1000c451600c14290b00e01c0e19406070f50501aa01030b000400b85c8001000152030300d440d600391512550a584085580001036182d41d5980e500010303aa8039060354000081000c0c039290111518a4071400e10304640d901e4109090107038684d01803000900c1810851800d55200f441d604040c1802d5026a000c4015a49401d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 263587958 1250 263586708 263586737
    0x8060402030f0118021210020a05120108030708190201090615060e0307030b0403080703061505120601090e07140702090f0603070603020a020d050309151914010b090d02130e06040c06 80
    0x140d01380c55090301201c0c0d1142c40e82d000c5000d241081003d80c02030040c03910011f80070101c01d070030501820440300f540f00c0c0b10700280c0e03c0740c004a07a640315401c0c01512084082c041ca800030f40d01c1078004a252a6944008540e11900da44c65406a802c80c0d040a401204114001c0c088a503100002c032607900d03011401041c1440c910307290300d0074000000c0e202904220803000001d5840c0d0082d08910002c1c2019034400f175040d804400020415048a030b601403102c882400492602d6220380c01b410180c5045d090840343c5511151400d49590302400c543e241c1d481d0080c003580c4003599495100b42d07c9405503403030311900303071600408240c1022515044030007454418440c840c40c540c1d0000381c6c0c020b0390485081850303698950340d4001e440d005c02003012507031150010041007003a00741c1d4400c0482140300c404080c844403600200c26030f8510401d0160204680040c06050301514001c03189548290000e0400c0702d030007a400c460300301690b90882e4246204c3d40318005100c10070142000030001031107a860035601400824 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 263589208 1250 263587958 263587991
    0xc05060c09030c040506060d0b15040f03120804050c0913170408010c080709030b06180403170c0412122606270621031606060806010617040804030c08060402030f01 72
    0x1101c1910815686985400785034036100039004cad801003080a026100d903a02d20700841004c01e00e000480385c10503100c14004c421805809000d00482d4401d02030520030080700c00340080c100b402071150380c4201c488145940840c03010041d842416010100c1d043d51581450788590a42e10030038070280401482030100694030340d10640000549034844101021a1280d80014a0001a00204210305201941404105500724255105070b084006a00340240d4a092071003c59000d54072400c055905500119000907049a640d00510881400c0410000303140300b0a00a07503030fa0002810580041c0030080c42840e241402c04528404403030a0a4080b554400340c19118022000d0305850040910b43c0c18000044001004e0700c1440c00381c4000c5070784507883e0381e00003040c001c0d15403402e0781c50702d02c3e203040401c06003004681300b07050302c0c1c3c9502c811104020244000391041002407059841410500000c40041e11191001e0002d10380c02000301260b06144c0109420900504002022a0b00d011074508071200038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 263590458 1250 263589208 263589217
    0x5042903240c071505040210090b04061107091e0b0d110120011506110307030503010605070f06050c0403031106010e0a090201030e16030b0703110315010c05060c09030c04050606 78
    0x4101050103919101140c85450107440d10040048130300491030030400c8441e900981c410b0b070003121090310060583d4002c3c1c811a00c0e50003041c0c0b02c101d04000900c039150060142c1e940002d41c40c821240b015039a03c4c040c0003120071501d030b00c0c82e40508160000f828004e080c0200414107004a8245040c10510755820000b080c6030902c0c9814064440c900340c0481e103030301c5090b80c4811402d100034090740710050040230b03880045004000104801d441d000c0b035003007070000c01d462859a2503144e0310714690070540300342c0c1c0c1600088405c4690f40009580c1d00d00080c3c450007014001d0040440340c0e030f140c45c114607001e04520040300346003000e6405140100010001c224100e50130a18103000041e82d5034450004078050f14034175040241a2003507140341090001052201030880c3d00400112565441e00390046054402180d00d801d1051014800309880700d407042100902402c0504100c2c000481d1995240e06251048960211802001c41d20b002c0d141402c3c80072420304441140c08000e0741c901742e800079255006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 263591708 1250 263590458 263590513
    0x801020c100c1b0c0513050f04020118030c03050303070e060c0a1e080c0714240d0608010f05150f0d0f06140412030c0c080702091005042903 62
    0x100e58410b094000e0141c160280014401c000240112140e400c0419902d1044e218aa0040e290010313441440c19031442a1409482520400d061540300d94004448804003254031420007030300d1000010014600e450058003c1d481100034503128903250401402425145c040e2501070f240811140222020200300907400d641d1050a411018840001488810b0940240103086000000d0180142c00000540304100d0f002e24414200340c8410b28203014040c41546000608800c501103082d0040034404c0c05444006130700600014195603a119040c00c0d60076604440c004075540f581442180303240900483c1c240c000940b500b1384000a03640c081050b68540060160207141e0501c00c11040198940011141040003410a0058205410070299608840f003105000c240ba1400c019406809208000883c07a04002c10604128181c3c0920950820050603540b8800b47c023032002c2006e03516845402d44142c40e0300c00103228081e2055050400c282004801e505c40e6000d8500305c640e04982c2c4140419041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 263592958 1250 263591708 263591711
    0x8090307061509060803070b0106090e07030c020a0c1d09010e070b070c030203032704050105150a030e1b0405010f0e130503070803010b121b03070c020a0b0a020601030c0801020c10 79
    0x2084100b801081400c40c1c02c01483e0900f0100001178071440040070380f41090282800f000d441e40d0b2035070103480340342c060310910160744244000075a290380a40d016080400c01c03801903a0801c10650f42e09100021030b03070040c402400d07a4080e003040d030301155010721740c0c8102d00000801002a0b401e61050391002c041c0306040a082002400c0c40c100500700441c2e900860303010b03007101e0300c50204119429000c0c00090010800301100c00c155281d624250041c00d04941c8050322023030500700d41c400554641e601c0050350005168544480354040c010411403c02c0741401940d119082c0c1d44410100825038030103038400b54005e0b0000500703111a005a00c0c03405d400450742199420140c2042c0740240c10b600814102802103c404400092040d40207001003118094070b00d4100ca03960b40e0710425504030102d0381e02c4140340140900004d0724103400780c1e003500c00315030008002200d440c3d61100c0f4490141d01c20190100141c0003c801082040128081c10b4060316100f0020740c00c000250b04c140c1ea494000c161030a140a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 263594208 1250 263592958 263592971
    0x90c020a020109170f07090b0310090308130812090102041a1213030c050d0816021504030e0a03060f020d05072a06020c06090d18120204090201110607110d0809030706 73
    0x1544d04204802e105514082a254000c1d03a5061480050200c005910b0003801340c4207c2c07030b00400d4540b054081143d490f8441071001e03103420700956203e002414088035032200402c00c0c074044000c131b1140300b0b1041089030300159589082044048120704000340022410b4800d1041c1c0c11030f0003090700c115900185410032588001c0140c04c044894410224003c1d000e4002d000782014100d91014810740300d0708403010103000780e070a6030b10b00b00d07076914080310781e580c0350600f6001140010744030f60303641c24141d5401001d0104040d09c07a02c518040382c001c004a40d600981c0020980000b410368010315034002600d040503000c5019041c00c80441e140c0911442000e50304080c501c208005251781618501c001c008121204d0b4540348482507a2142c2044104011a40c051001c03c000c8000c801c00700700b44c44588100300030800380c039420300020b0100040201e040c01460b07803145251610800081c0d106104603500d030340f80031081031801400e04110b443c2d035000b0085514100100300000108139aa86603011400190300c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 263595458 1250 263594208 263594249
    0x1527020d1211070e0103051024080703061506120906060905130201091a0901031112040c0e0604050c180103110a020f060a0501050f060a030f1104090c020a020109 71
    0x108000001808034541804403003080b640000115505000c0034100d40ca032545075042c55000c543d007480014031341e0307000b00800c9808000540103c0c05102000121100c1400c112651502c0352046400402969208e1141001480000c0c0180c40840c120ba143d43c142803810114020300d403030464000f507601b9507122504041007040c039900c0880100061350003003010341040e1a8241100307064003020b0380001c2c004207010441d03049141340e801100c204140040c1c9440d94002c010740c09054282032104030309906101c05d10494a00920082c80b940c40703030000030740707175400c1a40c40c05189030003a1000340541d15180401c5504d856072000c40d80b4000c80c8612140344031019900480142800c04446030961002003018145243c00154108480042900b0381e10656207480c3c5580403a00d00340b140d80e41c0030a4031421005582064001801c502e2010300c1c01180045040d076417041038640c820800c01550034002410001c07407000744501420260a807010b482c2021182d00004c0a03404030740109a60a504114803040c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 263596708 1250 263595458 263595469
    0xf0f0e03070b04080702040f05060f0a0e13061104080106050307060305060a0902090f13050702150f0412091a070b01150c080a260901050c04060c1725152702 69
    0x40170769000b0800e0001080401102014260a54143d401034003241c40304070700e603d060000c50094a182c0030801440d60740b09003451010031013884055840c0c0c2d68aa421030a0fa5290b1380080c00074045240c00813030458a4001854908001980f06501b0545003405201c0144d450304064401c403065040c0160b101c00b043c40018180d0382540050350342c8a40141401629a880742e00300c5480b51016409445d40680140d680211203d01160a0991090850700240014880703c841c900c4161107460217030740494440c54024200480d002d1621004100840d07940100041c50107001d014201e0705d41280159058100c016103030500c0c01100522020021840c5400c05200740140c07001c10f10071181084940b1010a410740d02403400b42d580045a50802001a50300c9111100325000c41c0c2d450340e078503001c00302640c5800f0031017a00040c200250724810000d11a03006804500a07003515881c2950803841d02d983d150148101d006840b11402982c180307a40000d1200d60354003038903a0100c50780c142640301074442c80080d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 263597958 1250 263596708 263596717
    0x5070905041704060912210201140c0c0606190f0806100b0405130f0e07030b0a0b060405150d0b09041a0a0513030320121602030f0306011805040608010f0f0e03070b0408 74
    0x18020051040802c40e1f603035054103c8400c04500a001c2b0745180c44103514414144102000100300e0b1340003e010030000c0c1410b03402d00f50b500e0f15004504c842207494402e5080d0545480d4060341da2940140207202007658084200e0b8001c1107024411441c0c949040e01151840c0702c48016981c815903a01c1045040040355002006504030b010260f5080e1510380c900780301d20030016105940400c2c42c200011200d8101101140d081da44005c201d203608502c0e030703a00c21010390f000244404140e41c46441900c0c103601c43c01180c601032803040081c49034840013510f26090040000b8901082c1c14144070520001418060302004d00542528000c40c1000441c0e145500c0a152000c0d400159200091142d11580d011491140262000442c442114102500c1241e807401521320440c4811002c1001c200198007615107a581d1601c580006031a09540b04000b81c1100e09903806440f050351180c9030344400043c0d500c01c103070558807955130401c100d0201d83c4c1220b80d00e005049005101c1c0d4910f44c0070070f050050180c00d66 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 263599208 1250 263597958 263597993
    0x80702120d050c0106050301050105090c0c01110f0901023703090807030503070b070503060105090402070519060501140a030b01060e1903080a2604030509060705070905041704060912 80
    0x265a0302541d01d400502c40c0c0d0202c0c4080c2080c2d4a00240400e0344e24040c05018101d56009288083c5501d42c2420f44016a02c003180c6103800f5981c0c0c8401000c490600030152a03124406240c158036114030703500180c209050400820340b20115025800001010a010018450403080500d8040115407405890501300c5130000300e1503105202d400010407800000030801c40f84612183d000341e8075031940680306404103944150219809110030980d07400c082d406020301034056000c40d041c0451030600146003030600d60042e281d440d11440144100e003550505002d80a405551900c90649180c40d0390000c0a01809800208004115848880d5484008c03241c1c81e0901070011544607566482d00c019154820305001021074281c003000c1189003840d511f0416844280c100c410040c1c1d0355540c04039070a512601c40107a001c04240412004690104054000f92440310000940d03401d06007084801c000300007099031a40441003209200855000500d58115180710b441404122610300d050720100e01030b0244c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 263600458 1250 263599208 263599213
    0x2040302030f0604050d080f0103020d1a0732030c09040b0a060306030501360503040b0c01050a050105060c0d030c09050405041a151008060a0e010303110d020607090308070212 77
    0xc2c01120980402d00754010740c4504100c407640d0f8104070080e240141c045501d2144c044844004101606103951001100382c42045c01c0c2c4080d9401103003042d0701410550f074a8000401d0410181901d00400d0008121b4810202420407085498400820548030003000840500c0000c03c004101d900d46070010803402c01c0003001c0300701c01521100020000d05a5100580306503080012040950050709030360410070640090010748180e05101e14081c8010300c1d10125840e100800c0f00160b010003100151a041a102c4000304503810b04180310f50a41e4810381009200c0d038400c11044a0303002c4c0001e01d085141100e8140810403000701c1000b41c41e2002e1541c0304637005800e24042008103c0d03001040b1008400000c134480e0282c03503d8141e50550600b85030f003e50030144c1240c0400c940c0c1d00440d07001e903108400920b045d090b42d4496004c1d0304030240a03407080300402c0340050f003030222020601c144102d00d0322500c018001031600c0d40e0010517015482c0700192182d034001a051065484900e0309150030b1205108 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 263601708 1250 263600458 263600473
    0xc0409180506130b0a050c0306300c1e0612150913120807050d020f07050109030905010f0507080301180228110604210c05010e0304050915030607050d0204030203 71
    0x221001039103d08001141d8840c0075000156069140b0b100b218024156074852600f59030b100001d001c04444c68140f220f9483c0e0900d113603812281e07201d00c2015821450303c805408a03450715403c0c000c032a036001d84808034112002e510b0540d2500daa0041d0f5940d0365080c03410070001e4848410700c24400040900d0700390411448000c201c440008880c50104052252000e5010080d0003e001ca441c0d8006030740303100000d00f040000c802144459000751061480e001e01c500e1030800e40341d5070745007124220341048010a245070400c0100c0c0d03030861b03140841d00b0400e040091400c04d0b599615440c51105006242d85014803030380160380250654141ca0b4843c8500c0c000e070450216641c0040814540c8282200000702a5142603032075030000705005026a81c004c1d15580c04820210848560299007a0320740100300c102000100465400d001d841d0150044e20050b42e6034608080a00c40d0303104000b04890112404142582201e460010741240d02216a15206444c2d03150b4084030700182c407442e0300103581741c8500030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 263602958 1250 263601708 263601721
    0xb0a0309140d0509091302010f0e041d0a031416060903030908070b100b07110d260903060a0b060d05151002030405091006020a111f0e010906080c0409180506 69
    0x240286000340307080700d03503d610ba610942104042c9000310301c000c0c0027408480c3c8110905003e542e9600080000407c007054440b0318030f151180d86000012085800d600c9038481c2c0061640001e0444150b07006003020390b240c2608042300920085000400030000313943d41300a0b0050501c00e0384400c4040760302c10402607030f0b1200f07828410382c9003d00350317a0000c59072900796000541622043c00c44030b501d50b11072103840910800c1c0c0100060300f04a96801c1d100003528a0746c1400c4041c20f50492060041031500321500e81e50118207251510000400d2620079604c3c05449441c2aa600c4082d16210304417850301003003654031540d203007101900c004c076169005442025130420301500031000c0c00540340c003a110101030b60f5500c0c5c0ca03001000d1142c0f00e41d0340560003200240c00440c82600740740003544009060b110b41d901c3c1240540342e048240d800c01c0400030303206401e018544c1d130740480e103000103108030b1501c4c0010341045205031007903125074800d802e100c907901c04008001814006003100c0d21904801510000d14008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 263604208 1250 263602958 263602967
    0x303120a0636051909061103090f0105010806131e060c0e040506060301030c170c1903030f0807080106050d09050f0d080c07050a0b1f0609090c0203040b0a0309140d 72
    0x42036400002d511401a240c542080e108681c85110742d400d11000c0c0c2030004031900c009020f081d42c244e0744179448040941c1c1c81640c0c1c40c0214040c1c0c1812005105140403903078100d08445040c1c009002c2034008100b88001044040040c054543e00034440c01c07540a000700d00400040d16100c002410203082c40e5200e45036507040103d0b00c1c1a0a0b0681c2d0034409551400c007003014510090100030b102d0380c001d180a0140030f1174000011001c4041e142241c2a00100d0b00009180d0203102ca081c0c0c0321000c40041c24420590b100c07444d0300c1544418201401c49003080070000c0c1080c8d1050040307800300b0001082c0c990b80344680360000004280c1041c08e5940c8034000408071034640c0e4812081c1c40c04501c0da42c01103515a00060704070b0740181d4002028004014495481120741100544458a02e10700418024840e40c3d140851500802c03040d21521a402d00d03100c038a1098480888400040d50000c0c401004540c07040380c21031704244010705d00094405007d141803803580d0300170340e81c2d01c0451140d44550703840c5e03d811 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 263605458 1250 263604208 263604269
    0x702210c2104060c0f06050c0d0b0906180603100509010e07150504140a051c0201020d030207021e040e060a0c1d031908160b06120604020303120a06 65
    0x405803960081040000e0006094020a10300140c90401040100302c0c0310701384124003070384220305e8442a40e20319101d0b94140d85040d40c1c0c4101c0c00a0001d010001e480c1c0134407904001080544002c0e942e45041400141103920380201204021081d1000030a03070381c0c052100028181a4000410450400d0040d46009041491038001d181c8928500030404401c41c0c4900c0700141401e598551402d4140000803c11001d024116504409800c8021400380c0d101c1c0003580bc802d204001407102903a260000a16110030b0301d1030301e4181342c410000e140240e141c04206020941c1074006480148400d00c3c0814000c1100c00030103103039409504144049800d4542050881c0381040d5a02892440342c1007405141e0500c083c04a5410f600c0008007170000f880c19410b0082280c000c10b032a9080000031140c2010f26031011004480c0099041c0400105203468800885040080801000720b4034040e03010965a1003108161464401102d000404d0010709420820241c0760750700401c1d50440240f002030103461170 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 263606708 1250 263605458 263605477
    0x40503010c090302150c0c06071115040503070e150303041211151603140d06060306080f060103080c031303110108180c010c0c09091410020f0d0203070221 68
    0x280707400744080324400c000d80000d9a80081c00c511100030201020045a800300300164802e025140040c049540c03894003900c43c00d4000d0107244001c03041c00c01001814070b034a034001c018010303061000b4080c41d1000600d1805403816502030f00c406454196110011280700e0303020b2a0b051100250101d4a000c6090000c13510a1140060103000024103003017258800c80d000b0441c0c1545002e00101d504205c50814418030140a400c1c140600080c51803200032580c00344503444821916135074100803881d032512070a0010000e0320090240c44401c2d40c8400d483c0d01701880080c00c1844045400c11644100b80200e030001e913299503640c844942d517840e00f0b500303600302d41c440701d4086079001d00012020311910500d19910001a40070701000c034281c07001034841a290f5813080d15034100400022071144960311411804a0007001c2c408008401107404074600318007071180820309401030040c80714103402d407019191038142c1b4480258a95070342e607000300c0c500902c995040c00c0411980080c0d2610b00c0001004049070703074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 263607958 1250 263606708 263606711
    0x405040c050108131e02060c0106091a0a12082b06030303050f0702061b0c1002040915030c0306050c12040f0201030b0a0f090203150907030b09220b0705190504050301 73
    0x81d10402c000400005012001d42505c001d003024048080e2400008210948014041c504110010019608403104c0e0341050110710ba9860a0000c04d40d04179200171840d940803103003480d6103402c00b0803003150410140b000030203000f004900c031111003500494240585490b0180b0401c00110056500040c206610041d0042442c004c082843c1581400c1c101c5d10410340364006000644850030744d0001d6401414813210704280c01d109218101c0710500c1403611082061201507107aa00b08031b40035040b20f00000c028003e91152540410005a40c0c82c81901220f810880c00140380d40c400e9041e201600c0382100b4129070341d507104204020000c24002c100c0300103000781d804100e840d40e50824089010074ae8000c40c0300004d00c0d24030800c085039103a00290f0f80000fa00390012a4001c508001c10307200c0301c06441010229488502c0080e80d407c0c050149a03200c6001195007400c43c04034140c0e14028040b5850161102d5200c0f400118103900032004c40b21130102c1c010300714002440c0400d0080c010b4010f0f009413407095 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 263609208 1250 263607958 263607961
    0x3020d0305030a0605150702010e01050f0706061502060f01060815060a0c0c0f0f2102031c032004120317070e09060d050c060a0903080d0207031205042a050405040c050108 75
    0x24101b0300c020040904006107224a0308041350015540b031032182603103a0400c20704010710202050301d403000d4107803a441584041007240c00c00354941020741c068140042190301400412924040c004d507424110762540c10280107a031143e60f10701c03044810000d0b0f00d6820a1000600c12640713640800703420b1a01c1d010341800d500440d00c0f8500659500307568403800408040445041c003203040500c00c2c0741000b0012420a0340003003980c0c1c0c0844c0c02c00126176090148140016106503c8036014021401c100c1e141413000c0c07450800d2071076444428040c1d4007039049a401d20308080380415000384071000c4000001031844a151800c81c3d001015190710101c100d000e03407170740e0010658508000b10384480703440d4028041c0c489207805c003051048035046101c806040004042c0004040703200c000007048004031007040540e41c0d81490402510784541480c2ca078401c170703140c03404200206880c178003000c0d06c2d01c0034074140e400210032011f0a080c00d00400c0d048030794007620b80010b200030010916052001c03500d0170788501c03105 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 263610458 1250 263609208 263609219
    0xa06090e0703140c0d06080a0c0317041a07080c1e0f031e0c031c1a0d1101050d0f0e07030201080705070c09050c04080109060f0b060a0212030a0603020d0305030a06 72
    0x640716100030401d03404076502c0205141504d04406811045048800010700c15a47e030050b600d008070b40c0e0401d0301c001700459414010b0101078080304504145001c4814603161a000ca0070740307038800040c10450b9001d401b0584608122001c02110701342c9204500315208030510b01802d20000b080740900f40043e1060303489000070450080280c65801c00c02c81c80d044468a103102c502c0c00720340e101d000c0c8a48240001c0040d4401520070094001040e0b608041c002030b0404612000c03a4a000c0014000e445600b1204110300010481c550041404a083c42c00b9a19400310380e10a4010302046090200d009040c038034450712009000034a801200e000740e90720201134079251403d554074810110b000d00100d01021050001c074602e0341101c0e402c017814000c02c9150a54409e0b100c2d003103510a9001b00c5006480c1c3c18440500180da000300ca40b400720854a0629004603080043c3d555900b4140310030b1851800f00020704070f80b5040e8003a4005603006455000c042400e468018002d40c021298154928900203000c543c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 263611708 1250 263610458 263610461
    0x302010e0c1905090702070b07030c020108100305060402040b12390105071403120a051608010501020c010c210210180825080f09031b010507120c020a06090e0703 71
    0xc01d018100409006040c0418040f9400313000b000b010644c45848400900070b140040144240780c020f640300b00c2101ca640c8001410040c020b40000640c985d500018404128007040254006a0440340001d50054203408582d00c2c1c40690800c1e081400785060700070020400c0700c81d0b85941c00c42e102e401100c07540b0b05c41c1a401c1c841900911a800580148425000a000303090301c120032112000440b403d101011501d210f0704141141c80030121a00c540a10455200e00c6103141804020703814200703e039604141c0004d503510181c1c0b040700c0c100034542d9505424084181d000e00301104442213403049520440700e0103075641d40900c0306030020b9032516042800070707404d1410041f02d071984150b0700c928244412051541c95070b805041480c240241c440c2e0140015410401000c200074009403040c0c5800705542007500300b5442c805c44034903c6040d4a04005507070b81c04001c40310342c59444000540c4681c45040b084801da0036181000350420194280494060b400c2140481111194485802d496407850700880 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 263612958 1250 263611708 263611729
    0x203010602060c0c03070605010609060216140f060c030d0209010f0903020f010804030e03072403090b13080f0f091e180702010902150a0314100b250302010e0c 70
    0x40040e003200003c1220322209038010054000d0003c1203900300b00c41911a1411100d082e809131021990546003080311039010701c940003551040003441e642040c500b0240b190510b10120100d8490308d0f046c944005a1b541e02c0050f80c01ca800c040c0d0480341c484a40300480002984000c2803140461300c040c8035440d00a204001030070507603901501005100102d40010340d191400500103e05100016044105580301002844010403841421541d100b0300408440807100554080c40e0805040207241000720700c010072140d0301f00110072041d0450f01e0307403402c05000d42d0160360090201c1950000d0480306510909010745480300003143c40700c4051803440301d516020b54043d5402600942c0d005003200c02110340131034043c0c0c4814103000100b5003480303560002d070341c0018103c911080310601003041c03170110b5410300c15503895102c00e000000c0c4c9800e05c0358030080b8060b00c034031610b220482c00240d8a011121111500c0850b04061107101d031800301d042c0b034080d0203003000c403249480902c07503070080c01d00a240245002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 263614208 1250 263612958 263612969
    0x8070807030f031e020706030e0d090b0c010b031e010c0c030e0910050604090501080706080603070306020306061b0d020c030127080415020f0105010504020a05030601050702190605040612020301 85
    0x14890a0701d140e503541003a6410319030076401c2c4030441c0401d00641043c00e1a014002e240f0354007030101c05060800103003c64400c0380765990741d9030290610109154102503018255010304000b40d8903030101030052405415040c92451b05802640c0644925a40017601681203ea18074001d1244008140048031112250f42001e40054011890700300c1a0800c0e26005400150120f5900b03c00c44e142d10204000da40268400c0e2501580c0e07100400c40c003002401103c014003840d180c80703011800c1c144006a51892a0302001d80400d60000101e8150340c0c40108543c2d8031142d030091941c0c200c8640c8821501c400d0b50300f01d000050b000e0101e0380b9000e40303010b00c2000c288141c55000a0002d110480c100c20f49070085140440340031204100c0424020b10500b00344a206100390300401081074600311444c29900103900080c003580c018465800c40315001001d80b54031660038a00707151903503254000102d801401c03114809051040b6240444c1c0281e10000420a44400b07480700205a51010350300400c0303104c01d1048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 263615458 1250 263614208 263614213
    0xe0c0105090405100503010204060c060b030d051b01021608040305010c082502011805010203160503040c1503230106030c0810030605072007060807030212071101020c1605010306080708 81
    0x1c5500c61800d544040e4100758195640c0315800e4850000c2401c90740550130071004a01051640070801001c1c0c001e1140c2e4042c02d4011349070303000308040050614028504021030343c688403a0b401141820940c1680c02c42010303c1d030110385502403801c01c2010f541c40340c041581c095080000c03807103201e8080e030041d86c01504001d038080b070021410925014502054980e4200315501c507021940c1215000032000707812405400016640c0c140400082907500c9080c40000500c03c041c02000040303aa199201000c44540f200481041808084114020424801401007030705070905020b03c0500280c4829043e500640c07401c02160721600340c00d540d8603d0071150344e40003074940b0000f8800100642c200941000c03050503c01000012111103200c0200030485804c3c596201c40002c0040a41c00001690090405d0504628009c500610300716140001070030001440011140341e41035000940c115802a20014140c1d401c0e0b800d000c10000c400700d07051040500003401c00c00045071400d00440c00c901100c800f00300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 263616708 1250 263615458 263615467
    0x1206090703020f0102030c070308190c110409061407030c12090c0513061d06010905090601050901111608010212010b1303030e1302030411090f01050a0308031314100e0c0105 76
    0x800c011440b0180f003490450100f44000d580014081016001651040e200d6030345a4002c401520881c81140320041d0402000c0c1c20f00c50041503a24a40441c42d01094401044115140c1007090213072082028007a40c00e040c00d4204000380d507240e071100003c0c4030700c0d40e25200c00c000445100300a42e5041440a8080702404004103c00d240005c40c018040c1c6000b03001003185580c0c0c2c600e0701700c0001c0c42c10502d800032018204110007580d0042180700a05000c4035800740c00e00304040001c143c2c1c014015440c1c140300f00d5030306030760426008000d60312044a1404503090655110101e00303010f500050390591130b1000d00030000c178400c2c80c0c0070141d460780100307001d07240c0346185152400c448403a03035012015000050710152034000c1c2850300080d48641e01665002190343c104801740b01d0b0140000b4070802ca01c480741801031001d559602d40003000c03250480741841d203030388400390000c500302c0301c01400900c03412107500780132030711070000c10006018810316070708006a6059445240e20b0703d120504150000d00100b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 263617958 1250 263616708 263616713
    0xc18092a04020d0e010207080c071d0c0d0e06090c121504080f130b030708061212090102011b031b170c0304050a0f03020c150403020f040902131104051206090703 71
    0x5002d402e514070b5240f80498a04810070b5401e08980c414401036032517100000d00d808010300100007682c01030190140f010805803988050412454014143d109200000181d10034911440d411400b0051020002d0794481d04100d801155a0000800c0349030244080c600c01c4025014049422100c3c0c040800e602451680d90b035032400d04503805590350f940c2d00e000502500d441c1e54414032098004e445070f00c03129a40d0317040c20003015100c5a4000c20203441400100c074142d1440601003030907415140d8141010340c441a500c00180d01400740c410356003040180c0e00a022a107143d2580103070311103000012204207071403000325080b6800f03c01180d248180d0036001011903200702e030b15030003142c1c001d0041095a011404a540394007581040c1e0b0b0050740140e1003241c41c07451502d050400e2901001100c1d51a030701e40307031850740821014001c001b45103114030350b652450015511640903014040c0d883c00340030400c0602c11aa92030305074000b8011280202c172500071148500d1341c0001d1780e900804071200201003580c95603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 263619208 1250 263617958 263617961
    0x3020306040b040c03050a0b040c140112050a090b19060608040305090d030c0605091b040204031505072007060f0905011b15020d05090c090f07030e0c18092a04 70
    0x6001180c81451444001021586c1805031039055031017601000142d00301800c0c80e9074810307490740004e409005c0c61042509140e800c558020400c165000e000300d555a14042c2040c01400b0a40b0301510018000f4100040d15030048401d0300561034a0744108405601c806084845c0f2004403001004180100009885450801161800d0504ca86030451a80c034042d502c030000e4480c00e0302e1003400b55110182d003022071407000100310005041514114100b515503165044030004200500200c2941c410124102e00d100d1802c000c041d90440004100c035140c01158170381d40c1d012511420000a5034855900b00e0540709501d00b00444105945800d02c009008020501d064071080d01101d500303050300540d4404500a00240210b0703034074044005114035128403010304002c801507003944100318107410003240e0066800601d800c04840e18000503400c038410703c05407404100c00600e030380c001c030008118000300844140643c031580f021826110035560b8807118265003d0120200240c20054082c040b0f0503080c82d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 263620458 1250 263619208 263619211
    0xf0209090c060f130312050306120f03121801060803030f0f010b0a1b0c121401060e0f09030f030f01030213060b04091e0c11061b09010e04021e04081603020306040b 72
    0xc1d60641113070507070b50365102481c184580302c854000c540040200051844d00d95040c060034000400907101802c102030f0313041d4030f0b80719170207416009284103401704030807043e030088944482c60044005c01c60603858040c110341d240c00c1120400790314003229000620a00784002d41c2412184c4200301d05050110f000000d6418483c4042e41032024054644003001190903045d90000800c100200354149105034240320050340304500d05404185e040c0101080101d49105203242c3c049209e04010070307070751a0080b5003401d6100b8035401a80070100801440740754036a800d52241201e100312042c10000050b803451200b500d80340c0c450f40c0720400090000f0810040744c0c1e04400d41c4114018194070503011898102c0007101d0702c1152450008040b0a1840078051040000541208208a0000c800c245003000181144074200115040050704178011095031695010796544480000004030f40c880580082d4040350082d100304d112038810481d40b004078140c000001c1c010b480c0c010303002d064560f82c3c44e101d50080000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 263621708 1250 263620458 263620477
    0x30902060702040915050412030c02010e03090103050c1204061a030f2107020d0605040b091501051908012f040b040b090f0a120309060e0d060c020115030f0209090c060f 74
    0x5c180e00103800c5442c46100d118800c601c191591121241d030550300604448400001c0f0041da03140503140300715904000281d0300c0059007442c002c141c540c0c035212485064000c500080203902d002d9018031003000101d4219010306c04807640c0b02c050b843c02480800d60784118200620056070005c0101c42d0b5940b40340d00c48100743e00392400095180030840d03400305801c9401030000351185035440f01484208400c207400682c000d00d0700c5000341801050108130703442c40301041c440d05208080311580c5d4000140005044001007540d40001c0140304195166004817280d44c22510460006d20715607440c84079041426101600c52035100c041c240303070030249130454541c40340060580c084941030b0051450f0380c03a4504100500000c1c45540ca00c170f900c628000d400120260000c800b40548401d6064494546000c4d20004542201c0003041a103280d41045c0e0041c140100baa01d54000c130740300d0102c18800c0300007249554038401e07540036100c0d988004c4411380b0b40d030340304040d1980301408010a1580d8050100074044120 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 263622958 1250 263621708 263621723
    0xc0b09010b030a0507090f090b0f061503160f020d1209080708040b04091b080712061e0321050f0705030c01021206091302010e040c0908070e04120309020607020409 72
    0xc4512000070301e48050940700b15400c0e40250401d0109286c54060203012108069003800040e903103944503910160014407000303440340b2a1740010322035660400c030f039140d80d0020030a20f5034906142a0030808852210089400b06e1120401c010b802e07132000800141c11880c80c5e440e80e50701020301407000701a010700102134860b00760a0010304082403010000b04003c018241100317a58038580356200c0150760340403500443d80210b04030010669a040030130980d200701c4500e07050800c020180c182000410182d00301403181d62000e0101000d04e0000020030003980e004240c182c60030a0070030603001c04405620034030700c0020020f10102c52500c000b9800b51841c188a103040e00d090844c51240030f0b00b2078001031081d08403450900c080c045c1d2410200080e60f0060380090b58070301400010b800181c09803c0500089006a9507200000305e0701e4454140c49000e00505801d84803000e58404191013096415141522800302e0256603060543c0a44640c92030944e0150080c0c0c1041c0c41074080000a0606040940d40039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 263624208 1250 263622958 263622971
    0x210030c050f03010603050f15010c0201140d1a13020c0c010f0c0b0c07120c03170907091802041b1e17040f0309140a0905090102091503061503070c0b0901 68
    0x40c40b28400f40d8081c1100d5980020f5618100d1000c01800001801181c00552500001c145699100c001e1100300c0760282400321142c41700045682c2c7e00e01c1344a0300807000518051420100d250320f0320030034420010441b038205002c41d40080c00c100f244200380c54080ca0342d0243c1d16110180d402000d04081190041c10181c0f070501040c0c90f0a13501c240e01316190b040340d02c80003540c00c08000d450100a0b103460a10b181c040e035018415070300980b08424a0f0b9600800503a10000100c001e5802c10941d13014048920040c050b11982a40034151072100a00880c0f0581c10803181d0681910361800781000004243c0d0f5050207118481406050802c00040b25002c018042d0f00d400344003000c0c03030709290150b40300c1d905180002c04142001089070314642c10494100040108068095544084450960381d484600213407640f9281c05641c024414501030075085001266001680c0c1c1d03040c03000d5441243d0503200c4000818469030104114482200c0c0440802c901e030795074801003820b86a0250f4080710001c0002800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 263625458 1250 263624208 263624227
    0x8010b2a0a140703050d0311030604050621010510050409020d0308040201020307060e0d02070f0f140303190908010b01080402011b3306050306100e071701240206040210030c05 77
    0x2040d11282c8445070aa0003150b00300304011040040b100c1c0400746140410030088035a01c8506a44000ba2800b44207039115004186550b450710310307060b441d0740d0301c0c0c544540f0540d14200305070103001d01316680318250400840004003400e107809a488440e60003807101980c0d07801030b6020b03607814901500507411803005201c03000008116220310810100300d08014a4980740c6040004c0ca000c07640c1d041a031340c140807150100710f101656051202511048000202512440c0022030b19500440b41806014202c2a41c80000da60b0407a40907011780701c42400900c4245901401503412003420307a002400207220481209c00c140000609800d80b521500a602d0089806010075180c0c0250700c19a10b110540c0b0100b03100103684d10f1040d40001c0c81c0640c0075201900d400d0b0101b908159151250320040030302640000d403100e10840c2c420b858940c056500c1c00041d41c580c00e40520f11040c050280c40881c0c405180394021a0000449a111b140d00500781e03107150440d40000c40180c80303c0071810003441014070001a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 263626708 1250 263625458 263625473
    0x201140c120705010f0e071401051306030605030f160b09030109060501031b06020a050709090305190201020417031e18041b0206070816030c050f07110108010b2a0a 72
    0x82070301e10742e200d41060415500b115840308040840c1c40c034068100d9106400420302c01c00701d40028561045500a8500603120361180c5e1002e04405008208041401509a4402e1054540543c01c480d02041c92590142d41c3d0701480c403100943c2d00c100f641c00c00c12481014018800003c000c0c00210382d4010660791501640c0c001c0c2c20480781040030300d00c9401b016030079210206c02440648001c02c4648016200d480e00c9140500407422000d440c3c030910790502d4018800c440701c4165410042800b1066884028001c5d04503008198102032107a5075400740302c000100307480ca170564030040c60115101054020116074040703800c0e00e60003801600e1190260781d50380300d08962805020001005641000c41c001c3c02c090700108041d0900c00c842c406d00c12040c06119821047d820030b030600240600000c4c1050311b280c00f800039a50500400050000b0800003610300303010010400ba201c0300300703590700d07900280c20324003907000a017140c980240f03040c0200f84d021080200d00c0901d80307000d407803e00500703490381107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 263627958 1250 263626708 263626723
    0x50901061d01031b0f08132001181e090605011d04060b0a09091103070804060506010e09040f031d03030909060d020604030b0106111501152d090f0608040201140c 71
    0x11a045c1c0b41480902074018480340d41c003c0c0c2c41056604c41581940e20b101c5085502800d282c122940320b461004964000d03c00c40030a19410010420803d0382e406070f1300501a81d80307a5800c80c994490000103440c00c1c03d80102e60a03550161200f481c5115072040030780c022540b0350f01942c0d00c10348907140081c0c29000c250080101140360f64a0116090600b40e001042c1c0356011009008000c1c10010085000d50218610303401c55442342d00410176803180801200c40c0006044016400600202404104050a51128a00d510071b4480d001401e400b0600103a14402410009030190810450040286804007189620030402403512003040e0b556004103403141c006800c11500000c1010051000c2d940014203a810340c0b24030001845484480400d05802440607c00d00d124001d4480082c0411402088034151101040d1104541c440c1300010101c8442c5071070b0700741400700e2400140442c03801608980501910039940324a07120740c95031390044030b00352903941d101c903000a42032008012541c0207000c00e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 263629208 1250 263627958 263628011
    0x1020115081e0610120f080f070506060d02010801121e0323071e02130509030405040e030f03010b1b070e01030303060e06090402010e0301140a09050601050901061d0103 74
    0x20801ca01e681c9440d4420780600c00d0705440c160f0b0101c03040065901409603c1000c0d2482c0c0035203a0030034030040c036000095403201040100000d6007c02d1012040c00d01c10040c01c0140c0c099400c480c1d0a448003005e002d9010102e02c0080d000424510040c800001d40d0302440750b6462141140341c89916080030184010044404100d0000707440911a0381131180743d8501108032044041030340d15014099a5070602403040440c0007540441188441d01559210101d941e05142d080c4002d10051030b00d40d5030ba40d100d9005024452181d46800c1c0c03076221a00d0008280c43c1190305074154a85503074240320004110341c2016840c10164145014035000500d000c1c06110000c01400d10300741003139410751502505075203094005041d41c0010804104071a55810640b5800980a00740700c0d102010840c0400c1c05400044001488103091030144094040c5650041c401c142c001d805882185e40c80301c0410041031000c3c4201000201800d80c1030303000c0194482e14142c080414100090652150141c091900d40501c620 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 263630458 1250 263629208 263629213
    0x409091109010f1818020d0c050901061407081602060a020d0206010b090319050705040218040605100c2904150e0f15130602120108010f1a0d020102011508 68
    0xc0360a20700302418140d016000350019040203500303080504103080040e41030700001d1912214980e10403218035082c01960790700500260780035951420000315960309482038a000703011140c00005c0c018070808001e030b4150380380300007540b5100c02900c6510964115140d007a1030781c42110039810040c0c0e540ca000348040f440b0340e00904044820404042e0900308168445043c4000070840c01707107150b0300030a500d405689400c2c0400c0b103620190902c2890078220ba007000f40c0180c0b00042e804c0303400c4102080d860345248100c90a1201584503400d001c42d4199110302d20000c1400385081c080041d1601502061001100c050f0b00040954000d100191100940301580c21411201ca8044117010354028042e6424219000f03000010006000d55501d0000c1c2e8548070b80e0f40144404516402d00d00328842c0e030882e80085c020354440c0606612000c1c0c042080c03244401070b600c3c0c5941000010f00d1402590354900d6110311402c8810003030001e2200c845103401c800c038115541c80d0703da4034444050f420a0b40c0070301145d000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 263631708 1250 263630458 263630483
    0xc16050312040f120c020609120c10020f120703170408090603160e090402010909020a0e18011511060103060203040f0b0420060f161703091005150f090606040909 71
    0x140082c0300034444c0c1e41074040141022031000580c86a600b261603115080d102d2203013800c80c0160326814940e046039001d42c44032241072034240311540084c041540608041c207a41c0c41d95201c420b201e01a125011000380800d8506101200d000c03507070210141d10a020343c0c40d06141100120010b095580111104280f4080c4c0014a0245652080381301e40351a44c203840e803605500b003580018000700142c0c841c3c1c0b4421900003441e58001c901c01c4441481c506d00c0a400ea040d441c40450003446161000d000c1c604040344242c04044074948504401036400e102e0344090300c01c51b421034440394040d5000801c141c5800140505580005401e40070b018811806145108015076100341307081049a842d2008921890007031007000708540c0780070211100714032050480366180b40b41d481c040c1c010801d5241040c126084c044204a15081c1c04104400c0010a081080142e81d03284690b0200c0303c41d488500c0b40c0c101c040d11072400d2130790404030201034020100400c8507080c19a2044107000b500d45459044805854a60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 263632958 1250 263631708 263631713
    0xc0a0e251107120b07031404080306030f0a0c032a090c03020912011a1e1014030709080c010c0b070e04060506040b07300507031709061e0c16050312040f 67
    0x4030a81c05c08910b140600c0803019007070000206030b20142001d420000c1c0040841c1081c0d030104165486002e541d0141c800c41c034a40c0c14003200aa14500c030686000914281003255810440a01081500d50460300c100035401c3c01409070091209003603e40031315a0030052400b441e038035541d0318164000c00380c2c0089035403401c40c0040c00c18489001c907814015901804050310901101b4444d03050113100380c035201003c0c4030700401115242e81043d90600f0580c40003003070001c12a48100b001e0b0540d112074045990369160b03100111051040b810700a41070b500241c000c40c4929118803041e22a08800801c00300e6501d84401c000f42041d80150b00101048100144c0d00b001c00c1000e9140710404075150205090000300313030810006003441c40c13404034204400010804100750051416070801411101c5403030942c90080b01d45591480305480e0070200800c0c02c13080d0b445042e1990031461040ca244011541004820700b0a40b14001c29904d0032202800180aa43d0440d141409600e01c03450003100c5802c840304050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 263634208 1250 263632958 263632973
    0xf140a0b13030b2502030403412e05060f0a062106141206150d060e0a0b060a090b03060f070302070b04050c0a0e25110712 54
    0x1540580a455014085070001c441681401d00460750006602c008039566042020324844401c2000b1040f000380f032250b0482c00340d0000141040c0c900c03819054140000341e40d0211a2220300842d014070016070010020f1844074403512100101780b4080445502404192040f000b0240e46a4258030320300a22081a01420050040982060054441440f26881407000c00c82160284c0a00c0050104480d40c500b04541700110703004152080d0340d0200826501c3e403041450440d400c4140b10320451161420f982501c1003c00c0b46801080528000400c05101c401070020601c500402900e0895461402404003a0240003503243c1901c01c1103054180e19101d810030508000c1358100035109440d001e04160151000103c8580010b80b0003005120782c0d5803204114064415940000c3c03e2000f54003c0c84100700000501707241c4020304840c0641d480c1d40b203130302c41c40340803001722880035210140240200504156969401c004560344c9001000100c441d6042803511301e07035911000c0303c108207024500922902c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 263635458 1250 263634208 263634229
    0xb07080c0118121d060d02031003060203010e0a1b12050c0c01020304050f16140418050307030e0f0f0a0e040f140c040f2c030910030e0c0f0a031403040f14 68
    0xf04400c4d031148100800c0484d0060041200440c0d500f42c0c0000444c54141100e8100d10080d07a00c56800c1d503803583c5a24000e46d49080a4400400e21402c1951540d51940c1c100c0c40005100455034480300c840510f031707013014041c14000e000515007040801161401c01007e0000350302c02e078010700042c00c82c40d401c210b041749800c2550000350410a40074200707009180b0059140000c404049801207250045000f800c691400f00e4a0024100d220000b040003c2680020041d80380082c111854081c0b01c442c00c0900801c088a80d002503400602c121051000d46d1440301480e4202d40507501310201c902490380d40d92540241540030720303102c1e844450041640c1c6007074001c800c00802000f42c188885966900e004807000010340600320040c0e902440000b5800f000c0092301c1000c0320082c071044801c0c0070300e60054000c3c0a90701c800125400b41e04000b868505100ca031140d102d0b04c01400e0b50b03c8092641d00c895140c40101d802d00c80d00c0c0e0004100c0001e000d80e949101c1e0000d0714001003203070490072944080114103801c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 263636708 1250 263635458 263635487
    0x10110c0105030f18120a170a020c031c090209091e1506010c060b03060a150911091309021005040603050f090c06090d020303040306090b090105010b07080c011812 71
    0x70001c00c4a480d0f841210301c1d402002ca0f00d4102801c03407902020f14240590002ca0452060020034400c0c4280d40c40301d9030843d0318441e000100c3d001e8940b19000000d038400d140c020107440d40100300128043c2494521000f4035008001d0000348104994001029100c0a41d80c541b180d91040c808020305041c400070401ca01c0d1083e4000380410591a1514030b1042070041619040c024040100000d1240350f4010002d8010014241c84581c500110010000e0540f003046440480c00660701103480c0889110303074401e13a406480ca2600303281c901002c001c2058540400f100c4590340701c041410050322250700841903840b45032070341904c442c1000d100a04131a00240350090039441032007801500040482c409410b6641540c005039200049000316407114142d0000175010f01c40001e0000070702440398007100410b44283e001090300d84503c01c915080e80d07803c0c02040c944620400510300052400002003101202c3c1f6800402c0b40ca49090320344180c007640e0b0f5400d43c1d180e25460b1880d4003640e80040084180407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 263637958 1250 263636708 263636717
    0xc090f0603061f030611370509060316090305070305030702010807020d140307090807090203090c060403080a030207020409061b0206011e0510030e060c0c070b12040204150510110c01 80
    0x3e4504000d440e180d400c0e1201900762543c40300c40303189106c00d84c01240d01142c001030000f1a00d0003004245488902c1c3d544003420f4a00340d40d02c800b007003684100e040b43e0241c800241960700b141c843d501d81450b1074030040307920014800d441d85c0000001c1d1080c04040004d40c09000070707640b1171486000140000c840202003200b150070900e003080303e0396001000944c46000610b9481d80700d54803c0401d03100400c00340c10148003445a20307000500c0d22800d80040d4462401481690840c81104051042600071800014640c0c0030a00032880c805100740c2c0903000b01c0780000c0020643c004c17251241c40484038160115070030710a0805d103582c0b000340c040103080d0050007010510321b0400580d55083c42c1500440c098079200740681e2509030501031090f0481a40071038250309580302810051142c0209501c00c0d07685135200d00604900050600f090790940b49034102c00400201c80355030742d03400c100050005414400c0c039007050607000704850701d54200c0c1c50b0740d80d500341e261080121a01128249030107800b220700360410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 263639208 1250 263637958 263637991
    0x607020a0203100b01110f03040329070f031d0f121e030402040f0c0305070306050a08030904020906040816030605010e190b0102010912050903010e0316020603040302210315031204170c090f060306 86
    0x5520004410b0ba0002650dc1d044c007500c04c02107003c501070300c0401d19900380800c0520380801100c0c4041801e13680518075408403508400f190b0340c00541c40c01001c600e05400014103e02c010000760000085601c40d100810004440b46800e03e21001c94a40ca003542001995940c100031040d5090b204900c0504821906400828941014590b5903c581101e1601841c0c001c114048551201015240a80009402d0320101d054466003840c808035140b0042e5005420480002010b0101c122280d0203850b42c0701003071100404600700d0502070101d9402241c115907890560202181003c25501361000b4a590ba2a969070041d40030142510300c40e1030a1805900200b01e94030031410b00c0c0c2203458443d80e040e100340e9229980d6090070313814522031110800b400e6524207103281d40244080d001f107210b5030010035800351500c208002c1c56aa0030303845903a500c101804200c10700031280c502c80030140440c4000304440031a400030011070f02d5250141d8180010126040a003c4245418440300c1d5000c040180340d065070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 263640458 1250 263639208 263639273
    0x30e0f030a0213110708030f040201021501050a05010507051c090623070b041a0a1b020609070303110c040f061409131112030c0c030607020a0203100b01110f030403 72
    0x30f00110303200070f03a400c40e60b401e1812012408101650005174111200355280c1c9801c0c000900000000c40e004ca00502400f848007404141c3d04c01980c3c143c0d0405032101043c14100700040da00c55101050a44031481040f070002d84880c01403135014800381503541c6034a4001e14007103000d40304840c182200c04004282000f012a44805081994a5990010910000c50f19a81090003098200002403c19400d60302c040001041254200ca84c0000038059200c000010460089072250800d0321009510342080c1c0c801c1020a101d40321910300408540103840c0001801c0e0001070444e010459101140c03500d0761420042d54580c0120b0241d822015146030405181042e8101040091541300404545424509003903580f035000c0f124050781da0b0942120358848100c13460994940d003c901144c464428040015509407001c5101c88505034094002d14000301041038003000740c0800d00045040001c5c1c041179420302c1400b00525201402500c000d03582d900d085051021a5030403088150601241c480112040d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 263641708 1250 263640458 263640469
    0x1801150522080c060715050606041d011e0b070f1104060f0305060c0a0203041a0d060b03091b0d02060706090c030b010312090b0f0c12030a1d0a050c121504030e0f030a02 74
    0x6d800404040005441d9111000583c03d4020340d08840f800d4400c00340e14044000203007034000d041e90503030186028501c5041403258a560007a0040f041e107050203101e001700140140c609500e070144698020a21003004901150485201740e21000d441104e100003082070000520050ba0090381c07601703216242a01c01c513000307540e82c0f1880c40707007591201d1034101d8030041d0a451000c0da51100e030444824001d00340e0382c0c02d00404503041640e1051041c010303282102440e0070219000c0c0343c152400b40160f917004181d03800b0025590001e400c1554519207591b40e880008016165100c080c1d44241c0407401654110309245a251030180e1600b018800100300c188090389292059502c005281005a59a078080c181c0441c240a005022031421040120030720030390901c0c64016607202e030f1600580500c00303002200b9080d6141403941d005000740d08404540d1080c0c0c02c1c40403c200609071940b0031a81c0802d441c1030f0100c2491000c0781c043d00082c08810201c03000f0701e00070761107030000380c405c400034010542c19800084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 263642958 1250 263641708 263641733
    0x50a030201050a030608100c17090d05090303040b1216023009040609020c12032728020a121502031b071101030b1801150522080c0607 59
    0x905022011402600d103c4c842c0c0c204601500b41c403401e54900744170008000002e044401994004503a000e940d10f11002c00c1c142d00280309505402c018a1310075288002607800c1d030302c9440d120341c050004200209136964100d0041c500046401503003480e52400845007006d103080c6e04200380c03c42d0000d1000000e0342c034008c3c1c1041094421004803036900101044985140c0c411440c225400c01d08109002441c00c10359809002da032056a000e50791075240320074a8006521080755aa0305180c80404c0040d280e036030385c4a08451a1343c2c030320126040710b440d480f41030084124407004d0002c1e042d0340300300c03070b10450a000214400400100941d0b80b45e01000b079680702d11040298280841546c4d005c800103000c4050341c05041d5049108096290360750310142031003805500c1950000c0d010906041c102000c40c01c00ba0354610b01103801010400343c0e0b03403c02070100350401c0c142e6601800c11406010351581803c000d0b03866814003500a00b8a90150f00d000c1e0b10301e04281074019020f108840600501011940d146070781c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 263644208 1250 263642958 263642963
    0x503030a140c180d020405090d030606031415060f03130516081c09120b0915160e060d02040e150f06161a070206010f0b07020d0f030c0519140106050a03 67
    0x30b10000403500041070804c5113200c4040d501501300000c0c000e40000214005051407803a0b42d003400310a458034410741c1a0b900a0700c82070380c1e807100c2d60000364454000c0c1c2d6081148010040c0024500502c0d0100300c1c00680065461400950202c802e03c410800100703c0c0800b84a1030f008007907009440c110146880302501e1801d81004580d03a0000d205083c4501100c4d0040c201c0310325001c20b001c00074202060a06030444000415120704408480600200c1c8600780c032408041c1c4d12000101c0790418102c4101c03115040c9503401c49801d104240000d00c142c005070014200d07074605000c05107031007003040c5201c4170400300307031400f0f040c812114000f1500d8600440c1c04130550503030020f030380349124505040c580001c4190080c41d001040240904103501140050403210ba600b06030080703640f54010f001700da00c50031200070740c0920401c8580000655540000c00020700a082000627411180c40d118148803c4042d07204071130290344009410401c42541543e03002c40b0460080103044d041c03502091891400d808003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 263645458 1250 263644208 263644237
    0x30c0f010f151e0306020d27080301151704060b013905100f020a1805090a0b03010e0a061506030501030209060f0d12030b1807021513050304030503030a140c 69
    0x3c00c00d80b100d044110f60001c5074021001c554038122510f00100800705008072418a69203545869103100d1a1440c9030480b5800c9081d5034650307442e1015180922028604584c10702a50180d201c42100c1010380280c403545c014a00440d4149800c400181840d1100c445a0241d50100411000e11826070070200034046a641140000c5007050420f240707003400c500e4405412500b00740941d41c2c000102d030017074046210103850f0411591061800102420814060603401402030400103410007402c0d0000d42c81c105018000003100d0550540380c50070254400c109640650316100c500d15048404880c000051095140401880d4119400500c480f0b0010304028410688a0544140c940d02c20008900c120346c401d628800c000311030800503000c3d004000010340700d80294141004400903069019205802ca03074007510710040806103080800f50040d04007004420128140e50009100b040144080c600484c003d548034a0400b1900081c4d42d00d52209094044400c000e10015510107015540c00c400300144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 263646708 1250 263645458 263645489
    0x50a090501120603061509180f080d110a030e0706050c07090203100b040e040302070b0a080f0c04050607030503010905010503030406022a211b030a030c02060705030c0f010f15 77
    0x102d040190046420203443e0b146089900b10041950009010031101d59030700c14003c68603807800c4840d10700740303040380035240d54a030b5004100001c644e40010422044d00400000c0c44ae54000b6140100e90401c421500c0440e42d51102c6012200040101a000709818034106281254216140391034900520a42500f5500400810000745004450901500d002c0d41c441d51503039038544e81c0c40a500320070b45090300540160400891030305490001c8401480aa850f42100d070740fa07040350100c4010f0f00800091510b40207000200300d90703a0b070b44020805180a681c1c1c09890794100b03c0da980850300c0c183d0000b13100354170410003085520340104030541e0110503105010007040180c0c110b10490703a01c1c412420f500c400705101500690b03650101d0907000607020741c21190300c03070320b421080c0c10f100900d20032040e0305910240401001034840ca88251741c0c1440503125a04010303c4e42e030f90f01d1564010072007001198201c40e02031054070500348a40680b042c1c0c068014060680380c101101803501040c080c19104000090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 263647958 1250 263646708 263646737
    0x7150c0305031b0708130902070305070f0609060507021e030412080a0c230d0309020f100509060c0d0809060c092701030b01170106050306150a030501051003030f050a090501 76
    0x10322082803d0b900600e056030f1070510780361812a5511042008040c0c444004020480e10101c1c400d6405596040d00c5052a082542d16271004120345401308640c0d6079120800c1c0000220903001f811b0103a9540d40061001d00c6044602d0001e134415890100d0701580705000800c503003032000040501042e000201540c1c0c0c2c0d9003200b4111201c2c0030b080ca0290200000305020110b005038121041d20640078401a50012004090100c050750030303d01020390311200d00807004009192801501c8500303100f40c00c240340360003801804545190005192170101e0340000d50390861480d00b100105612024110240c0041d1a0180d100385245c010040760f1800f400809002c0142601d1004000642c0d1f0b02c0000140020b41c2e6924056052039024000d103c030440d09039102c000e403c44140525402e03294020090704c00c50361040c0502054540001486620a00b1030300300001069080c46a2805500710380f5000c0f070000d08505020b4204080004c1c002c0c1007040400440c8501d5500c0135102c4240d400910b08000c0e40003000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 263649208 1250 263647958 263647981
    0x111f06050f030f19140604030833010810050418020f1203031506120a06090b0402040806040609170703090603112b02040f0e06030c03070b03040305031312020f07150c030503 76
    0x1070305c00c03005e00c1c41240107020a040e00481c401d840381e0810030328840010000042c59050440144201410342400300c1c01b1f100e05e601880d80c06510600b100515011207940c3c4001030305544e100c81c10f1448684003030600100754140758a5040e0055801c0c2c03010504d01008903440b540d03900c0002c3c00c0400350588030700b540e410b69030364400300c07401d040000b0107039121400c00003e410010810380c41104a481d02d0416212150308050003510304403020100505030f0340c0c0e01d94686601500d44408119041c500c0b80942224400044018010303060107a07545c03400c018100302c03019046400f5244c0034440a80148009515850010b00503002800007100c0701c4a5046c00d20305100c040e01940c0c20503a40d21400b100007151032900e40c11203502c5000101e00300e8800940f00414103481c3c01d1320340030b0b91000010410005010900800007103821222680c400b2100c070100f901c80d20169240c012030180181c0044103d41f0501e0000c100c0200a80082085084224810000030380789180c00a0000d0500ca400300010313907000c0302d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 263650458 1250 263649208 263649233
    0xb190e0105030c0d1e020309010b10120e070b1306120203011206090201020a020406080c03060604060602030a18050901061d100203032d01030803040506090102040510111f06050f030f19 81
    0x100550b4100c90392144005c0d50180d08110386000d195071800c1c241492740d10340200c0180f10782545849800d1111801c0c0c1d0800c0c00780c0416400c0c02460320907008001407880f80c503c01850303192214150b80b6941d50a1540c02007040205c450a451500d00610043c02807112640d040d081c2d099008400041480c0d0610041c0e06140100d500694001e1030007800107600d607008107149072038840131015030711159103042c1040202c4000d402190016401070185030102e9000e4400d81da05114514608c248455841c3c1c0001c0650000b600318200007103500401c02c95662000101034407a900c1214501c031203252002c0b00035964040100894112210b02000c0004010360202e503544048415001c040c203981c49007030000c0e180c0c2c016181100c091040c03c001032400c1c02c040c401c0d18203680c0000c20300a603541100b07800b03c540000c1014030f0410b034024408124040c10602c0c004020001d076019011a002d407034081005138503900108810b000e03800c00001400d0003600030881c1808040c00ca4940c4511030042c1c101040480380 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 263651708 1250 263650458 263650481
    0x703120e01120f061a03100501030506060c01051018020901080705160206030f0f0f0f0c03041a0a060602010606050405060f07060b030d08060406091e0e10060b190e0105030c0d 77
    0x141070228040d8480c60740045050750500380310035010340002100e035203080c4421107032038049800c47c1d01c05000c2036209410094024100070b26480c10080d4400b0241d003154000c2d01c2d491640c41c04003804022042180410050400d0036040460500c0d00d03050029051000050109042107400035038860380140301400c2e2106981c025210355101c0c98050507100d6801d0040e100c45464010100025002613034031990b240c401c03903181400601c02c1c0c03551805900b0942010b0000c65980300a40034410490f00804c220034816008020003081c12440c00202074219a26a003004c020080200014080d94664508480130111301d8061aa590006410500c0080c0100418580c1c103010b111002040700c0d81c8900c0d15402072004940405c012a03039501444100c41445100e081d07000c3c26070105504c02c00955000104007409801a103075007000b83c81c8032004440e10380d000505a0503001c42c06600040c00c003d40300180c6c801c503050074084a0200000640a400010703e0341c004404c001491300f48403441c940082d22100c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 263652958 1250 263651708 263651711
    0xf03110d1409060f01081906110d0c08060402030705090d0224120c0415110a0b0711100e03030117010f060e0a0e0a020906011b150606020f0703120e0112 67
    0x803540d0820401c400241c40303001081c8100404070300c0ba041843c071803d040f111a800108a00592007502000d01001200b081c1c5072240d0742d0814030345090a4a004140c1015407041c0000d013002d0003440500000f80140c02c640c01603105204000c00140c0100072203805200442d14502100803a10004105985040340004404000b018601810301230402806007010f0301082c1d100d856503052990409030140c1e101d9114042c1c421000c041c00c0034017801c0c030f414030034a030402607413242c40b590707290b043da408802d8905c0c00c001403002240c50301c613600521084806082110041c442d6080781c402003aa46c0c041030089103102003185106014918095110034210000e0040900589594145005000600f103d500f04110700b8420403070ac02c580042611983c0d5580107040c040c064662600448050380e54403420001c0c150350321204030215440030141c0411a005503008100d041c105500241440491b141d00d480781c2d0700c019810720014448078081120140760345440411040d07503100413181040001d42c03145486 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 263654208 1250 263652958 263652971
    0xf0c0f0c0f0c0306050106110d0c0f031205101a030123010207080d02010903030c0302090d060b0402090333010812030403051c0f06060c021c0203030403051504020415060f03110d 78
    0x2000f0354205c14100c3c0d0301c070b4450803498105407403829100d4540c44a60320000315605c9000001481021601c00e14034001d00e4145119082800381c8400c0301c0096451a28500c141d03581006010512000101e050040d4608203040d5407404002001c0c0c1606020001c05000111207031a50130b920800480700142100c400f11101080038200c080d000b040c4165040d40000d00f40110410b41500070300844403120790152065040d51500e0720303144001d180240e200c41d03005800300030405084c0c1e010072840c1100c500076000d1760f07485101d5074248020781400d405501e80a41c1c00c0401080710900200b591040659204a601d0742daa13a80d103000c07962880740c0081030301420b0507840c0302050b496041c0c0c44010550b822207410800c9544442040d524102404c100950000d602c43c0c243d0520506501c4003000c1c0780c13016003101d0801d9141d035503141c00c01503e031490f001d46c03070300010404c415440c0a010b0101011514490490700e1420041c00910040e02c10b00750200745600c40c84240080c0f0802d404545107603106031000c1151 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 263655458 1250 263654208 263654213
    0x20705070b0c0102070f03090e0f010b031503030f071b0e0103030801060302090604150f020d031109011d06070f05070603021216090f0b04090b04020414090406060b18040f0c0f0c0f0c03 81
    0x92400d402009c10f9041c4100000700c41e5194400000d05852040b00742074195910f240b81d406000d000041c8140d050301003030141e01007086080001e480858032134051000700ca54450391444011500341d0200002540e840c004001094210022505540941c64050380d140500f50110340d1502c12035001081007141d0b02c3c0000006580a410301c10040050341c02e6410b1019502f13422001e031054940e082e8107000c02000350045d258010b01d64a80500c0058040b840c45801d1000000e0940d000204140c40c040c030340844e61410010305105000141805083c02c6040c00c0241d40a10b030074072030003419a9840402010800c0146002d0400c07200145290f010180d15203803070742e6046403150414031908040703a0030503422031300ba45424025035041d0351055008200c4010604100000040090302c00c2d910a0765441d00803c9005000008008030100220700c0d175142100101800219109600c0f0303011114905942a0111680f24030703504003270703400c42c40c0000030400b030b41c00d20b540e20698002d001040b440020000004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 263656708 1250 263655458 263655467
    0x3010b15130e0c12060f221401082112040602030406021201090b030f06060d0f15060b090a050306042a090e070608130f51020705070b0c0102070f03 65
    0x850b200c4c0300210030251907010600415512405450760700884441080325446007800581d024651214400314008100800c070310220903082c1c0011069401440891000959901c20320592180310110289480381110040300c2c81e603000741000380100e4001004c1018030929405642e500b82003501032514a503520b41a01000300b01c141e000754042d0044e10710980c1c40b18004110b8612805000d0708810511807c0d40d15650b04404100e007c0316040c0c074410050f0000042449000090140d00c04a2903561520204000c3c00f006c0c10351080d44246e00c05030402000800c1851100304040c0c40401e11070150b4110840c0b41c0c5400c6058020340b191034501400300340c884400142c00000c65115445c0e00302e2a07220860b11642c100c05684018000c400281303c0200020800400c0c040d460901821017818214007034040080e03400007214002c440940034030440b0113419214823004a615840404505c0e1080580c2c546807140b40c07920030520500d03408108900840c40a4044a001d1030744002e107242e68072228075001d403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 263657958 1250 263656708 263656717
    0x311070b130209010b07021f03150b03040201140306030c010309080405040f14010b0316080405010902120d0311041805090c040e1c020c06120601090503030c1b03010b15130e0c 77
    0x248503058450001489190031700032108410740290180080c040c40140c04c52a07098005610020990b8405c4d40c040c40320100915200640310380c6281c2ca80e242407600006103001c540c280c7d03e408042d0b040092242550b400203029103021030030309010906800500b0180824000c5901c001d0f08542800084424900a603101c1200710740e000c0d0344401030384d883e880711a0aa010840f20640c41d601550140c9103018040d190070790b445441100041212022a0301080c1410100c045549080c1d00c1407981401244c0c260268200c603000e000151402c151501d81c1a20152880c20518030041d9034600201c3c510382801d1000064002020740280502c1401c0301400341d41d100220340121050b0035289010800903c04152500c0d6540300600803070402450b02d00f00c0352465809070540781400403034407001030251020310103812000d05040c0903185003c200b115200540807034103d01c0b8401d924001811020359184229001040300c243e01481d00d980c0750342e03000c40030500d041e0001c0c1c0f01d262035241040304000c801c00050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 263659208 1250 263657958 263657963
    0xf230a0c0b070201051213080d09020f03010c020c011d090c0403020307090902130c120507050c0d08010515162423040803070c060203010f0329070311070b13 69
    0x6080d5540d071145000000d01078500000d002541c10040c180d50125141c4896801801d40c4203242e1075020703190b5511103194440002400c0990307c401100041d860103d80d100032646040d0005e00c44190817010080d201c120100c8064140b01001814150b540703c0c07440d92500c00d0300090440d10140c141400300000c01d410038801207200344a00d00300451503000d107006403d106940034000c20003100301c000380c14014000d0048000c08208200851480e405c0040c0925405190962606a80d4030001d03200a030420100600d20b205219544004001c2d603110403031880e04080300d030818103071590a104800290740034000b03c0606040b04040003c621040e0b9a0550031404e000c60324104030503244506280706104414801480c1600482d000601040b42e800041d0380c00045454004060030066071400c040340c1003038000402c15088890b05000304a10f403000c2c80911600c0c0100e001c01103d00070b2100d0355446000f0050020180c071003050b005420003800039120000c1d885080d003a80d80c900074111550402640909 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 263660458 1250 263659208 263659223
    0xb0f06040c050c0606010f03110307031508031804020c1c08070f0c050a0b0603011112040506011a04031403090411180402040b04030201031a0d0b0a050a05060d0f230a 73
    0x781c58000b4000d004864602071041c0181c038065690000540d5160001500302d4107040c0c1301c4004003801e00580005600c02c200b240c0300050310f49114406c00d50841c405400070a00c0e64410003a413458180085204040003004450240e92111400c0300b00d800e107410320f102a01c0d405821407002100c036821507001d80c0710b04074660700d4040d001030f2014112a0380741540070280c00c541008129401207141c20500c254815030180001c40e484018221240390f540c03001c15901d14810a42d01404104a0180a031500601410039400f014404a0030401c0780c1f403003648401046e102901c0c0440340144401d0040d01c44140e4001c10802000300e040e01041e62a501000c11150a034400307a81410840c905482500c00380c4403d401d000d810141541e00540c01030200c10850214841008511182584c1d00141d45e1243c512890852030a801c0040c01750b801d444002d0441c03503640c0c2c1001e04100d01610707148040f601d1250070841c00004460f081c24440c100d00c50b10f00406c0c17071117a1528100d030641480002d09000b001d1007000c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 263661708 1250 263660458 263660471
    0xb09040506041110082a030c04081506150307020106081603210f0e040207120201150609031113020d0510080c06030c04062d030902040e0613060f090b0f0604 69
    0x30040042c04e20000d000204280001068150b80002d581c0c10300100810544c1d4010314814484403c01d800c2200e14800c02d40c4000303418030806000380400c0c401d42001107030314035450900300c0004598000424801c00d882d02c1c0400050071062003504180003c1440d001035030b44003421001107040e1209540802d5907614040d40744100c1c8144040c0c2000c003480c4075035480003264094040100e840600b21001c181d8072980030700542c0045511246510070b486d0752074000040021103045284840c080690080c0305000f400941040443c070380030318074003000c0411104032428112225013180240507403201400da81d40f40204000c140000c013010042a58401022518a584c0756810000d40388002c80303160a00c11000d120400607280680f102d800a103245020028980341103100744c2084c500d050366580002a04c40015100b035007001d02c01c0b8103000f02101f001c0d2140d4a800314205038443d00f885d000501c82030f0348118120103005294003880c10190b10035404400750405940a80390503500340c9100b84900d01d01324 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 263662958 1250 263661708 263661743
    0x20301170d08040b0a0b060f1e040315020a0c0f0506040507120309031202240a05070e0306060906040e0a030e03061807031113050106050d06052d040b0904050604 71
    0x14203000c10900d10303525030020f59540c0e900d600c4070b4036028003403003d400d03180c8082e04030396900c074070240041c150380b1502036446200c10400000e4004076007503a060b4000c0b003004203001040004a42580c1c1080f044005a0303900c3d204c0400b00da88080e1080b0240c0301107d0425034904000c40851031f240914055012103410a48030240d400c200b01d00d40c50001c0100d05181e0301000000c0740640000040d801c5401501c0030362000800c2c58502c0025400c0d1503042c004218100f080004841c0301d001e0700120285008100da001520100341d1311140542344500c5004404001030300c03a9101d8200c2c100302d481c1c200c15515614180e15001d0300344203107000001d00c030740544400111620300c012902c696240c000d4009001081c0f458680b4224503040c12589904004081c1310440346c441d0500890380281b00f01c1d0303101c9030744107825820700003200c559420841c81a0003481718020704900290b82800d101401802c0c40140c1201d0382d0009004003682c00d080c1d41c008200f41d04100600c100443d0940c411401001c51048440004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 263664208 1250 263662958 263662963
    0x180803030613050a020c06100602010c210510090c170a0203040812090c19030b0f15010e030a0506040b04021e01050a0305090c0307080708070614090d02190902030117 73
    0x4580e01500050706404010701042070f50070254120200d0318005281240005485091903002c4a0580081c0300b690b01c1005a5070b1b0912907610000d0302c520303107119445124406c05802d4280b4692020a050f201e0f40420844030002d40168020011400f0401296003044800f13804c0c0611410088202c0001c0750019100542d9802120b10540c2d110850710328083c2a170b600540d008030058400721040c85600d20207c5151034150b04040d05140c0c02426407040e51441c03401c1c241c1c1940040c0800b2500855006200c02d401e80c01100d9490780100f420b0801001084a011a01c1d10032071403400340003071160314180814003544110250040303000f526400002d420502050340420150009036000520402c5601b02d010710a038066500900f5081c2601c8140580c0b60010745410300e540c0144210f43c00000c0200041101007220b00003e00103810040030300d010340a0300071240d019190a01d070250701519012821980c0e4a500ca84036075601c40075040600d80c07030b0070090009402c00d021300702c04d10160480c50107540000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 263665458 1250 263664208 263664211
    0x100f1505030a02090718090b0a0519061b0501060b090a0b1801081306020c06180a050615030a051f06051c200d050a0c0e0402030303040305030916030318080303 70
    0x1d00100115403040e424040c0c2810005c1c0004108000001103060406402501000038410b0f0000401e007954080104018403806506c611701c180c0d4000004100d081c00b003d00e081c01c030349050400e400590111541e84001d080c250030014865480d001e0040341115102001d00001c00c0d05032a04148c4a4603842e200401e0720401401c40e0744003001080850003584591a070b2540010750f40104060711455999400c107a80002212408541084042150440e111001001a603220100404203000c064031215161700000e0034101c0a102c441c56551001d45082060051f21036100084403030105020f01810490b2140d4500f0303008550420b0800206c501c1c1894041c504c1004a9000b4130030002507a40b2000080707454800c3c001c180c022100f040d8016035a04110000450207500034202d1840a440c00800f610407030b41140d0380c0f030b00400707040c8009608c0000179a94041d6050030b00c03503503070b850b00c0c0a281d03d0503e40d05c0f01d91181d40b010040204c00c05500102d000d0346885000707085006140c80320041034a0303020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 263666708 1250 263665458 263665469
    0x503030a060e1b03090a0c0305031806041206200403141002040e0105010807140f04061b08030c030718060e180f070c0c0503100516080402060f070212100f15 69
    0x1c1c140c0031a5003c0a0060003180c00600d4402110420002550780c00c50405140d481555982c102041040070a00450007039022510210350b20303484c01d0300740507044000d9015288054412a61003121480352205084030303240710541a407003030752125661310f003000709081146071080c080c1c041c1c03020036412075541c0d00071388054900c100520b00d1240c0c200401185e0551008044004009441a4030454084038000a100b4401903103c240c0c2c1c2c6506004024101401d20304210b00b031001100c44640c0441d8901098a411207505440380756240c6611500f01c840d00c41ca00c0100e0706800038214006115034101161489440c000da481010b020541d0400203e2460103d03140348aa00361030001525851090040f5100c03e07209404290701c43c2c0c0c40b840860f02d050b03040d5150070016a81d0f08240080e8650482e9891040b602500d010700c1103142c2540826214010303a400d10401a10100e001c104669541c000c1800e00941030b400c440d81100f02d4030101c800752000c58444c0c00c5840c80c01d402e03100c60a5007080e81c4401ea42c7c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 263667958 1250 263666708 263666731
    0x110111030a0504030c06060303020d180f0e06010903050f0705041107030915050d0516110a03020706080a020c030c0d0806030c01090b0c15011205011112040b07110a0503030a060e 78
    0x1074a1040c04400340600030022010444e02160601c0042c019125410107140254000d1100303403251000540401890014281059202081008450f1400700d1002c103403202504507114076115200107840113041604010308038050040b490041c1c66002803144216003044034140050094965110740310301c20382c1800340004107400300600c074900d1905d0181c001301c1d01e24545545401a91038588084980036540c0b43c04d00508010410041075001101550501040c40500014003407a64060f503a060706208040510a8400008480c001154181c5104007005410b42e42d0380c0d00680000380e00d40c440c14000101190908000c140e6a040c0020000214901030312100c03042e42c20480c1c0030340d0303075000080a0324191182d00c0c1c4c0354101110b80149540280b0003084404003058003480d20750300b95091105207941d408030920200d03460700103142209070400d0704202c0f000302e20b86404008403903d172009481da030028400c0c10290740030000c0010045105201070242000f98588400c2240045603080d1040d00520 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 263669064 1106 263667958 263667961
    0x1a1011100b0a0902040605220902030403050a090b040821090a03230d080601031a03060c1206090106020607050a0c0c0f0603051305030a0c0f060f0b0111011103 70
    0x100010f200079030900b414604020464040e5505803560050701c502c0a42004604c852444040d2006500941d900c1c603050a0181c86680500c08410005d50000702c000391503081e1300180c0d400c0d910840003404541c035403040602581181c2d8516089110801c01c0951710316501d8840100003507100d44050354455021424140342405500d4a402c082e0b00202c098500080c0e2024140307074002e00901340010588180315072400c540c150311050075014424041880790400d4447c01400c0d100384000d41034086035031a0300c1800520742c400c0c450240541c1c480c0c000314680038000c1015000090140c07030040c5001c2019191070720007850035406640404610b0030107000d001e901d40500d5600c441c0c3e8850106c501902e964400703550703116804800040004008440d0200111403507404102504030b0310a00034070440c580c00358010a2440c081c140407540d4545015240c40701030043e003100149040c100d07800c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 263489208 263669064 := by
  have h0 := BRFrame.cov_init 263489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 263489208 ≤ n) (h2 : n < 263669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
