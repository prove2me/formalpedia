-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0888
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:28:18.126697+00:00
-- url     : https://prove2.me/submissions/e3658228-b87c-410e-a09f-38fa9840100d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 159532374 ≤ n < 159712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 159533624 1250 159532374 159532397
    0x70e030705060f0403300c020108070c05030d1802130617010504080904050603010f0515012a02150712080402010f020607020c120102120c040e06220c030902031606 72
    0x102d58090410702d800100d5040c00240300049a15540704003040d840207018800c40300c501301304208220404804008a041c45682c00300f956442100380d64040765504000504010680da81603513880b03400c14a40100740ea811405038035600300c079140048247c000340207404140d90102143c0003805184513403c0ea41e0788240407104d1940c41802800d11460300b103000c2e00c3c00e140c006000d00002d4100107160ba072f8955a00c034500d18451060b80b00c1ea501624442c042c1c0000c8983d00340000d0700301c80c2c2c0700e041d00024660b00305503c4100403884010440055043c0c45905035407c8409410b901c0e806880710040c41c2480f00480c005145500801c02481070b8000d82e00d404122100302d9042c0e0700c809041d04c0030401a0800300400c1383c00e060404562030440743e000e00051528034901010170025405513121820000002402c0001c403051a10b210b420a50884004059510038001078212546103c1e00c08600c68440028036444d034066484000c64980103002e880f40b00521001e00140e044450081c50007182d8000c050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 159534874 1250 159533624 159533629
    0x10806041203091103031206010e011701030206070206040305060702030c240f07091d01230108010e090705100c0201030f11090d14010e07030b1302090103020409051203070e030705 79
    0x2400d0155030003000c14500c45032044421000340c50b03a0042500c100c4902c030b03004005074804100510f40302080e50030f04503007420320b800014407811442001504005100d80300c040004209810241120380c104d0300541d03200c81074404100e440c0107a0b4000fa01c0f5004403010411299004030080a5001454040d030b29900280e00c1c903000d5235000c0414005007403101000041503541030303100481d0003070068100401c400d5615103c40308201c40c0700500c1d0203228104401005040c01c81081940b401509414011f5070800c203400092107940c0512916102421081c04101050b005015500107088081d06131001000b449102800e103480b02c00d02280001e02d808021518440d035481a042c6900f41d11600340c0c035000b265401c00c00355002e084c0040d10304800b020421004044244110840109400041c251440c51414a803d803218018400c1d01011062407400340184c0e620a01941503030740c1103600041c20744e81c60901d1071626000e107901c8030340b002d4004148240035422000714002d62404030100d50300d00d41c48406 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 159536124 1250 159534874 159534883
    0x703020301020708071a1e090c090108010c0207080f12070c09020d050402091006020c10030204170703020a09060803030a09050307170912010207050a230601030f03030c0201021921050f09060108 85
    0x269400c0320080345241d247c243c0100c0306144d800020316800c50313041c64030700e90000b45500d500382d01908040e1b5407007007100b00c5160107125400c02440000c01400c54448102511a10707000720510201c2c01d0310300002d00300d00704a400c0701410040d060301d0004548031041c0016801c010401036906030700c2092018001600091105143c000346c800c154040c0040d003400708148140780292030411001d01d0b400703100200d4030310086041c91400e0003800c402812080d01e140140b129400701904070084803030070180300748050100041104d070020031055001541d5080c41c03c0446c254043c07070394010070b07204616005014607032440c40900346640c0c007215403a4610b205102c8140c200d12486a00401c1d94119544020118041c2c2c0b01c8500e110021114051244a50000042c2410300c260800c60700388480c5105682071592500c90004c401010780021840d080f40034030a02201c030301c0e003031902e01000340644d82d001058003d164030043e1074007030b4a02070016042000d4000241c81e41280c410b01d1a209040001920410004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 159537374 1250 159536124 159536131
    0x6200f030d1a0a06080c071a040b0c18011404031a0103060606030606122d0504030e04060b070209270c03010f0902010507060b0a15080403020c0a15110703020301020708071a 76
    0x2c2c45880380504d40841038980000042050114900510424000c241d4404504131084554803000042d49824504000419030144c0314601d658020310182c800190f00c0c0e00034500e19002401c101b003403800104c8800100e4840d40d0070007020307155803164000c3c0c607941d0a100c06043c0c80c450f4505100e41074684000310308403080c512504001405400481d03024031400e5111006008800541c0303042070750321484000354031800552803c0003640e164100024103601c02100b80c0c3d0b00c40111001e000c11490825480740c280507000010344264114004160100820654401002442880f21510003415201d882c0c403540848003da0084d42415284414500144102c02010380e05850342070818409894100003082c585103640e8100d00c01910216081508100c1fa0008940f0350744e0f14107451506240c000d04103100342e03d80c01d0081c1003200c800d010baa5601c0040300c004103018608002059821030610703140280c01e034000b80d09540700051400503c000f80008240d158090098546800c1d09200612030061045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 159538624 1250 159537374 159537379
    0x609070504050415030b270a020904020913060e030a081f060f03090b0a020705011a10050702180f04030809030a0207030312151e05061306200f030d1a 66
    0x800040c00b06107484c1d405006100d440c0911454400d803030343d03103005a80c0360540c2c600b600ca41803640201107001c42082d103021512140760203400c400d0101c1d40030509805011303100900c1a9144000201c1310b0034011482803080340c000c0e009001c541854000d10340c036503201c0c03150840051401c1002139840e43c040d0501030039101110380c1d40c071440e500d001e03011200b80e0304445805040540307a00e455008500d101d0b0101c2c0c080c00c85c0d00e500603a00c0310145841401c441d5043d00d1051000d075444951240743d40c603c440c41520032540d050466440c02d042c40001d1396100250302400004400d401400002c0341d01c011414442d41c86a203685030540c842c00c04003640d0b405411801c0c0c00590050005100191148a1541c02a8441c000c041148a500b0b907255290781d0042d080901040140c003400008a989021094001c10068480e103203451140f12550126000c280100340c2807041c542c002c0f512000702c8038500c020224010054610842051640b20344a41c841d860143d0308a003000308108401d4002d524400720007000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 159539874 1250 159538624 159538627
    0xe0901030b07020f010c030b040f1505060309030706020c0607081317132705010f0e0103020f01110d0302090a061707180807080c03190203030d020d0b04020705011406090705 76
    0x31581c8008203041c0040140d001c5002e06070201c000e0140034000d100c0d120f02141c4002c074541c0c030007409100441d01c2101d980c000f60b03400e240500446031a040440d00035a1f009480084e0b42c0e41d60320303040900d1880780c0c00380100781c1440022906042140450307043d02030501e5a49003a855100e001d81d0341001d203084200580303a19a01c00e0140030220b114401810b000405a00710411650307100d01c01c90b0082c0c00a44148080c2d2068a0705241e5160300d48519405010a21140507055060402d00c8654403c140802805090a04d10241a980c022014500906403100403105a14044400100a5000075103424001d010351840400d500b80078510b810040100801e0744815991404c10455209545201000d17a81c0358421000c940d0010a00080010341100c4000340601c1c2d80041c00c2c1460112420801010380c405542e400c1c005a401200704c82c14000c0c220f1015844240e00c0340e8601c001d05180e02450b0b4490700c001020b10820006401500d032a0704600075290300c90b941d074011300600900403600c0c1d0001510 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 159541124 1250 159539874 159539879
    0x121305031204020406090e032107140c19150b04020f030613060b0a020a05070e070f080c270108060103050609010501180e011d0919170705010c08160e0901 68
    0x502074203440e03205000400c0414030a9454130f14000301c4020783c03128043c5400000700c0552010f880f600402203d151607029480307503e070140001f003c02c090786003007600c00d20700020103000c0540308116101c0e81000354500811800031900d450300041c402015a5800c00b41003000c00a0b00c0d24061080e600d40c2c10303000c4900d03031550355a4400c2245050850000e40d04143d914900411001c1e0210b0180507017075030a0300185181c81440c00c1283c42c00c8002d5001000c800c40c1c500401051980c010508a089440c42c10204240d407100081d440c024003415400e00e4070901d01038001c05038095402c040d815900000e807254821900d0721001101908d10031180c0c0382c0c100f402d12004104551042d840c03c40e0410030700c406401c4544e215050340c140814203a101d035a000e180e0400c85850011a490100e0b000f619400c0100018440c0c200404448040044044d040e5100da81141c2c645501c000e0031610724070382c000004c01590403421005040c80c3c405989010018000385440c9034003a01030380001c1030b41c060080a104840e803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 159542374 1250 159541124 159541147
    0x1020a0206070804150e0115240c030921031b0209040209060d021503010e0906010e0f1003022205060604050d0f0302030c030304030306030b1b0306090c1303030512130503 75
    0x500141003241d41070f174817800b00c031004402032241382e0346034a602c800495003010203c81945180c031341d90000d0310352001800e401e8103241e1959080014000c0203040443e0000544e0805035555149913106208116486404000c241c85039150740040f20f100e5242c01e0750707003001000c041d44001c0c8114002900304400e14046005442c7c900720941c2c0c840002803000d40c0e501c41542c0410349408206485400b80305c1c0220061000800c1412107590094083d801010705602d0080e11301d070b682d280644503904504101000c100c10180c0311190501950f00549000000c0022007020203003010030003100308030145842e004c51560700d007074004c035411508010004410b0601c5034842104c002c01e0410b044040d4441008034030f00140091000d544507600070b840000b41d03180345080607020054014009042a403030701d0380540b04003a200b004d0720f81240007990360002d40e50b1408000b8030203111350790021980c002959000001c040e8401c005000580e00310b8058101d64440300710304001c0c40d0180e40028680e41051204d07102c0c18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 159543624 1250 159542374 159542387
    0x906090605041202150c19050601060f1205090c06071a06061606020306030c19090c020604080304030e01090801020309010b0f0d03050301050d0c0513020a0f08070f0c0311010c09080d0201020a020607 87
    0x10740e81d010443e1b280403240d0803000d01d01000b042e1b0195003103002490390001e01009002c081d00425142c100181e0300e2440c0c4c40000c4c26011140301c10340f001e640d80c2010440c000d81c100001449410040c00d800e94542d11414a0bc001ca04031032402c50b04540414001a0300741440e10583d1442c55a056810312007040300c5e5210006504002c2c100c03600761141180c518140d940d600e0042c040d0035850510b001441c0d092152640aa9094140810070f40d40302805000c0003d007500102d82c1d000d90036240200c1481c1064004039040710ba030fa44103a68540c00402405620207042d0302c0340c911080220303044c4800304411010700c604812181e00c0a40422000e000401c0903040021000007490300c03c0f00054240d03a04c2e503002541000902d13880e2584982c1c00704102d00e100b44c01c0756646541d8205824051524900001c00034003203128405c010042101200b03d09081601400c00082c800a0717100c001d01a003592241c0040c014812882191800e00c604440301030014018400c450350b135201a4007400b0959103c43d0192184c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 159544874 1250 159543624 159543649
    0x201090510230c04170a3c05011b080603150c0706020a020604150219030c0c0c170c0d08161103010f050a0b0303160209090106150906090605041202 65
    0x500b036034070341014024070141081e0b10980318200d20940756810260458012400221208981c1d40020000c40200d0210320905112404082c0300c0d01c0b01d1044484c0050002010001d014030703a203444e0999904100041d001104402c02803814400884519030003282c0d015170640b072050b01600301c003015a0316002d20000035903202176492202c4d442d101103540c13402c041343e00c03400b44200141c0007c42400104560300c044c555591032074907025814803044801c54045015800406d1007816503030008481c8403401043c06010f40d40e0071900240e0965602c8150440d1320702c1e00500c1007454000d8040e542801c0c03a100034501840307900b005170281805c4c15400c8500d00801400400d9440c00c0010312166030030b030340901641e0800300c105640402e890601c07111078001c0d242c006040d50706c1ba420a005030441450139204074071849404580280c11a21b80240c10360040035a504544c504004034408142e0f11a0030496071021030f206981e8112031140c1e07900c001c45044c0164040c42580b480180b15010241ca059038a9651 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 159546124 1250 159544874 159544901
    0x403200310091505090f0a1401060e041a1f030501090c1a042306040603021206060405010f08060d0602120106110a020d0b040c0b0c010b03010f0608070303080901060503030d0e010b010201090510 85
    0x4080d940e092500e10340078841c00c0848d0041c291a050807403413942030007124014031440358524450705250359007071079401680b40340450307042031180042c130601000d9400800c00410069821209612801d02c540a4903001c40244c5441a56080000c1d064441c0750003001c02011080390a0304040c2020040103501c2d81c04613006544070803029404019641380ca00400007840d00f07441c01691049020b125001c00c0c00028411407180c0c005102c208544d90700300014041e083c0c2103240100d03a9075610b000103080459158400380081c1c0c804200b118164800070b40b103605a60035611004a020b0004803483e56501d003a60009400030b804100a80000e9002c03c1020381003841418210322680e01c0b8010540c640c0c10030121140d1980d107a6601c00e6540c1400c2c030803506500c143c03003414030009051462080ea910750304d1000900300844500005da4514082d4003c8001d00402016243d407900743c2d102c1c80c400381202184c1103c80754640390452200750300510034070315030961000c094148150f084c1d888070b0041101480c8000b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 159547374 1250 159546124 159546133
    0xf09040809090411150c0c030a03080c090a030f1101081f0e070507060c020c191406070515101a1603120f0603140f070609050f06040320031009150509 66
    0x42c180d07141c15001c20301030b071172450b5140c4510462031420300c0e1407000c8107824044d40080c0d03100000b00b584000600d9000554405091f0348000400108d00b070001e281c1c0c4050903000106d15003208100d0042c03000340c6000c800b640c1c0c40e95140c4480704555045860360f15003142d0540600c034200180f41c140c920040c0d00c46258240541440702c1c585403070381540c208524080050304001e0729103a0b5803a0070f05075041340c00042480c02c800c00381000c031080d42d2822108981440365502003120b004005040040340a80500b004941400f070030164880c588292244c0142d103c45040a444118100902400e603844000c500c01c1c20008584640c03401e48014044098008800c0e80b10f190359030080d5130500641c4000c41c40340380d01402c80d060208445051041500a203051a00a0f0310200310403070380019500d0a80d0021260741d0120200c0900148091266a00007002e0450200400b0000725000c54007000d030312010340c280da08440c0400f040d07404650400c040240400441454550400a15882103600c2442e40040b075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 159548624 1250 159547374 159547403
    0x90d021c050f0c010605040f1e0509190b01061b021804030e120703060e06040c03030509030a141608011107110a08030f070c09180f210504050f090408090904 69
    0x5a400d60100c2e05502440c5e444036800c101d0350600d4401c2c03064031a1402c3c010040180014040c012000301c02c0f459141d007503111400300b020b0000500c0b40e000c90014505400188428a10345506441c4092180202085a242d03890112400001800c120039600402503000e40300710381c1c0e407000883c401900c01d80401c15021120540754850f828102c411000030301c000e1414510b5440e015060300c0901d03658540c41c2d0404802d000005280700700c407030182ea5260500e140c440078840f0110786058444200542120020328899010601c081906040700590035a549003058550034800e00340d45051400f06002d243c10064600419100d0000c011080f0b001014844401e0303072400c90700c0c075541080800c41d5040c00d00140381401c002034481c05400810400c1070510112810080c8210f040e03c0b0102c000d030178202804200002c00170406442c01090720000282140000d0009000b800794105000312401208992140c030468038082c5d02c0188200d601406040c501610b903800d11100700405001100e83c0210940f00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 159549874 1250 159548624 159548647
    0x2040204080c13020705120d0209060412140715032d050106120c08160507050d0f091d0112020d080a08102301050a02070506070812090d021c05 63
    0x2000148044801801e602c0c4180c01000801c50010f43d4100c440c42c81001804001071000c164a0a01044100200e450745600510700d000f80c410440b028ad4881d000040100d811306041026490480c0110070004100008204165071126140103104420000310b20030307000180300390064181c00103a030000b103505030100c4001c2d840c038620b6905000355440d03c4030014058154040c001078440700c408a82803040086d5070710080c10740200686040102d41d41c00d030150030b515000d00216010380390b00a0449512258582c001042800b02020400010b614104002143c04030201d04d0b800702001144c1906580e481d0500c042000d544100003207800001e180d1512022441c0741002e003550146c0c5840d04000341c903046111644c4480550090a980500700c01a205901540141107212030707801c1c2011a1b50305180c140c00d81ca041440d610141c0c0c860000102e680c200300d4403401404200300061101803c41c0c5642108545802009400342c00680c442c1d0000c0c94031000c0f210f0052500740190408500e441d080301113 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 159551124 1250 159549874 159549877
    0x9050c0c1002090405060d0c090504020a030f0c03030809010b031213170304150c1e0c0b0721030908030f0a0f1b08090c1c06060503150708010e011a0313020402 70
    0x3001c01d240c0d50105032405541441e005907644090704951200411442c0e50358030804501a00403800a00d0b52600013504645134440c40c5c401a41d08487c4160141c0300524000100c090389000440000d42c0c410045444500140501c06905100402520078808a00d024000d203400261003040c402c5101040001c0340640c200004141c100c0c85c1c40a1030781e840c14403900c0900c01d50155200c204100f4100315800125a044000f0002d1450070103c042d804900c60130f00c1c140a41964008605900c800503046041005d00113205400725214541840c0c40f481c00320b402e508661110502506000007000040c1e15008812559613210400d50400605125041c0c0003004481c0316140604014680b4030341554002d80089813030f0761008000c0020581202040c01058140d0386900c4108010504565010108801c40e0010b0014043c00384c100e41c0300042030740c555100d01c0300550358580468014400030407104824811203050360b01e2041c8801c0070070360b200c604d0011580002c0036040020046000200103a86600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 159552374 1250 159551124 159551143
    0xa0206040305071e0f0b030405010b030601060c06050c070201050702060a0201020705070e0402040e07060906030b0f03030f0405100801060f0804030c0507170f0307021807021204030b07030b04140109050c0c 90
    0x700b00a604013040c45401144c0d0004502d0240000481000540c80c0c04000006842c90604a981c40791500e1a00c1030140140b002d6007a4507011b00d100101e1443d500c014003100c660700941c028005074850030310003041e070703c245080640020010040e180240c01c16400420301c0200601c00103141c210184c642e0390416000703070462100240f200d405d00007540307002e004855002c80c0480243c40308524050016040c03d1482c030a050034540c613001d0301081e90741e424002d91100c11000d0103480d40e0300e0b0000021107090340035018892040300c100c40141c514a05c130f4810700b410f8a5594a86941d58110700b0020380b65148020300440400481a4252002890030b0000380c00030720381d803414044c080c8070503007910b03041c8001241e901140d90310070310810000d60340303911034902410203d40222515485104080342030440741080903035040c4001038000200481003907064840d041c640d60400c4100e840380100000e03a12543e030410840d0308003500500c1040a607902036a00a2034486030240f8000c044104141840c4060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 159553624 1250 159552374 159552383
    0x606030402120a05010b100206070e090a0e0601080307170a02060105041d190209180a080703140f040f06032904021b0610050604060c030e010c020d11030111090307050609030a02060403 81
    0x7900b0a00140c20603a540d14030a20440c0080c05551400c600022f1081c1003500d81684500d84400200e00742400c1c65204119203011001502c01d5580c403200d1180c2d40781c0c8590380c216050041080f103502481c0b401410740e04010300e00e9001e84900d900e01400c000240807181c540032445e1811300306804000d481080300302c0c107052141490156a109d0f500401c140c2107030040072445002e061010b1108152400308004c074265031b024008988420142c00d0482d0340021802c200c1c40703101c0700000c0b0448001c0140d0081c0c000c603403405402030070b101c0c0c03551800c03000d85e04250850342c2080c40d010449072a271030803000c40e0004c1141c0904014200b030b00102d0500445558030f0080a404c1c2c0100302440b05545100b1506406010705443c56881c0c14500200101f0b2801c45542c040c0c104a113111600469a2046400ba552550010204441d024075800d200b10b109a1901449100e5880d142c0c1d12031034400820195030f00304800502030700d03100d4501010f10403140c1c00350b20038075414000c0d42003c90059480d00d0160010b10f018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 159554874 1250 159553624 159553631
    0x30a050910240b040803070201031a0a0b0c010e030a09050402070f0204020a0e03060903070201020303070818070905162115030b0405060f07141e19020616050f030606030402120a0501 80
    0x56680c1c150b8070140d9a0400650714030200010301811300008220b800f416820328001442c44200c560038440741740c0840c08590701c01740f0003000207072030440030000d0240145c2c204020020b02081c04083c55403032207000400000b040d13030100c08103d14a46503014040013802000060107040d815400541241c1c01124240301092880300d1a03501420108a4264044881e000070740c50890641c00127036590100402910070041c0d00c07400a000070f1710765003045605110741c10460f164207880f01240005030400312603840000c5000e0900c03202042c4100001403410b4000c00d812008800380c0807101028102c81c4450100e0f854411100000041c07284881500c200d020303c01500c2681403800009080c00000340059081051002214a100070307150110f407610300744510742071250741140c80ca61519024540c41d12000500315050001415004244a0320910640307000b816500811141a20305010702c00014014820910015000d410684011608035000a00d50304400070080744240ca4403560f40011140780c1d45 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 159556124 1250 159554874 159554921
    0x507030608011103040c030605060d060603030203070204140f010603330f060c0c090c0903080a0c21050d0507050f180118150309030e04020a0e09060301060308030a050910 75
    0x40a2050f006500f007240d0000b031550606481d005484216400040d040c10355820204080f50b03550044400150303070000c0144a0360fa030320f04010b900ea070080707501079004504214248600400078100144034282a2410302856403c0039400c8005042030440480100d00740d08980c3d014800d011101c0d011440781c00100303a40141440c4030040c801c0fa0961202c401d12100d0718401c4001504a501039050b90f040040000e14540501001c90382d212060348003500e11640040c10101c0c3c079070f10003000c046450241d22880d44201c030902500448405d44800301001400500091116068a400c501d42101052600d80c0c02c21260388201440707a80108284280242826070050495800512070a03001c0130119801011030300d4488103610b0300c2420b00c2c9040415aa45105d41c0416000b0340c000c071441000a0070031511510254009806107032410b0703117030384280301040014156241c1402402c090b03d510021450540d00d45901280c098240500410098000e0756800115170f40d00f803042c2d07610700d040350180541249 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 159557374 1250 159556124 159556139
    0x40b0c0d11130b090a03120e0d03030b0906010e031f06080d020601060e03010506060a08090723090612032502041128050910050705010f0e190b04140307050105070306 73
    0x10b60542c40100162002d0100c20310960b03031051800101c0340c104c01300da40d00407541101282d60300c0c0320362120742e4000340c00c444040515505034051103a513802030701c60800315118003005450000e040384050f0390545c40011130303184100343c9020000c1403d51002d00801c0f004c1d141c800d8141005001028400140c0c040700041010700e03800714007102000d805800030800b6045c22f0001c0b42c228400e10502c0018400760001080c141c0d10100580c000070000035080c01816132103100b034101d1041c0f070629054440c2d0318010205070340b40b80048480c512100e10038003e45c81d000c848440041a9210240400c802600900f42400942c03030398083d8400c0f0744a400d06182c4d603003a0048284035440940c00c0b00f80007200070300c42031044003900b0070105c076403811084500d41311204c211041113680344514403008180c3e50804403030910802e07117901b00024031003001098495a080d00c9585410603030300c8007000b5041050f014042000701319000c80c070070848003400c03095a10305022501c03850309541c0b06032000b0002030f41e81c110420812 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 159558624 1250 159557374 159557407
    0x40e010b031506180609010b1c090c05040c0302040b04030605070909110322020901062703060c03060b070b040b07030f0509070e1602061f0e070e090a050103030206040b0c0d11 77
    0x84c1134820750510707034100760004c2501c90303205000b1100d01907000594000490b0002c004e2061032110102c3c00d0090300c80307914141503092903a11680340110300f0103025040301030181c001d8800ba1645040d2550410746140c44110260102408000c2888003580c0086a441058011413100c0b03d140e00100c1d9903411309080740c444001e10b03880c016041304d1090500f600182d581c0e8900390b04403000c80c582100350034100c3c000b003001400074648070226280c481c0800000c00c880303900b0001d8400031644041148079032707540c409089442502001000c20940760300090010b00486440b0750030490b18500003440002c0603920b00110343c020358950840f5440350a0030401e031040500080c0c1d000300d49050060044100c4840650b881002508010f5000c2841c048203107001541250140203101c418103007200c9050202c8050801503074110000e0203900d481c0c001034400000d07130117070a0403640e055000f006c43d6915601c0e01d501c4007602138160324820340c080111b01200010b0707004010032000e0400300309503038034540000d40654 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 159559874 1250 159558624 159558649
    0x60f0405100b010806010e0120010608010609020c1002072d21050409090f0203030406080a050a02130306050403030b03100c030b03060402010f051308060f010603140103020906040e010b031506 84
    0x110303400d203091000681d9008010640065007820200c0036443d07001f0040e602085600c01400400505a00c1280c3c180c005401800480711040000c100c290b07110703800c8409034481c03249058000d521200320301c41040302e1a401040c3c0d06024004402ca80040d0082e55003840025580311511280c80c46045410700810744500c4c071488120694000540012800103012801240b02d02c0303224a5641c1945030034000c0d80ca10707200b8425801429659100d84608014103421820740b04114103a1038032000941c16021071007203c820912003950340300c0c1c0b9480c1da51110041c0000600880c1095107030f40d00011b25440c10401c030250a407403002c01092480350724400504031590641c045107e03910007030030700001d80d0700601c0044402c4424030344582c0d1101c41c02b5201600c58082e90000c441c5100b404204913034030004c0b07440a070503654265030620040c1454525210311001c2800f02030b611081410208081e807806600000a52902e000086a10310701200020308003102c44141080300b545900c1040b0b460f180c030b0880c2590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 159561124 1250 159559874 159559903
    0x306030b0f0f06040c020106090f0e0f0a08030c030718170c15033d14100215070908010207050a0303051303120504020a120c032603060d0201090305060f0405 69
    0x12514000489110742035016207581c2c041d650b60205c25442c14800c2d040b00340a807210348814010442003080141c014044c04110300483c1c001c0d01705400300044d000c50540c0509030014000ca0450b143d101c04c0703002e03503400985070105121503101458003244ca020b10100003030855000b2840580c3c80c40c0c03529410f00781512503452142c5041c0d13850304141d04051080c2c2c0c2c0c018185260484010f80e042894001d09907400c00c02c94401c0c01e41c02035000055501c10840c0080d180403005004110b80d40500744210400c0807065040036802c00d4400340881d41615010030361102e424940164400d40d501c0b0ba4500320f070320540064a05400403144002890b82601030160424507547e80909002c00c207840007410b91000300c110300d0307203140c68002003415580d81e8001c48020b40300d500c09440302e045044c42c091650400620041307032025043d40050119005801840d00d544d03e0040c42030f0301d147d603030300c2c01c000d0811140c0a04a040c0100303002c0c0480846d10130004d842c8507242e4148900d1780e070709290a0040c5020800c1c440c0c3c10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 159562374 1250 159561124 159561151
    0x503070e1e4809010c1421070507230904020f0a030503030610141e040f080f100e0d050903011b0906030f06061205190f0207020901090608031204050705030d0306030b 73
    0xf9403a680640f4071640f650300074104070101c0d81031200160801c02d07044800c0341e1a11101000d60442c1074514018902180f15a0444180c0742e40c5a03102960404054580d54034000c900c8050409428500403403984144010600000044d40000142500d103154005607502d80c0b02008100300c6061007480880e076654503080011035400701007900b0035a84902680c201310040e40b02110480d504081d000e031000b4100c04418404483c0e00c4000095648001d0701803198503201e00f0085190ba000184605400e00a42030098414812803800030303140d80d030114a101e9010742da05d0120180348403128400c4030b808561951008441450250020160780d80280402040e44c07500c0c0301040741c02c0d0021020350084030f03000380200c0d05584007118400c0400017400701d00c2110381001704505c080034030b950040c500c51b44221924500b50f6201d1150000f11601405101d40c036510400c0006900d92500710390990143c480c3d02200d51258071000441d05100e0360480542c0440d840c0e20040c0f041100c040382c010380c40980842d808 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 159563624 1250 159562374 159562387
    0x203031606140f180f07061e031103010512031c05010510090f05010f031b050d06290309071203021501080f060a150f0b040503070e1e48 60
    0x1000d0841c0f001d071407180440004903980b00c4d061000c0c080030342411040707002c2e140d0ba0782c0d0319040a412400ba401524a04500c501e4402c0c51041c0079108501c298181449810b045a080c20705000041c82507421910a030311050007042c0c82000c0c4002d00d40c0b13a03914050340120305545040240101ea89020410905000e01e1400a2015007001c07810002200c2d401d01c1c21040300c08840f0020340051007242ca00141c031112190300c00c0652a0417800500c02c0f6400d420381080490356601002c0700700c81400ca01402e40c00752403123008821165400186070031951200c107894515540e504680209000d11100b1000350300145005a0030020f4018150700610b50700001d071500d44492101c0c66100c801c000c1c0401011a6545080910101100c0102015028181d0102d90040d01c40c04850002d030000d1141510070b1285850214001e28180b5849000703140c4c03205141e07900b100c05030241d88841c4004150303218144107050000c00100c2d0070382440c00d02003207250342c403002d40d4003c0c001e51111000c0c8a41784112031400f00440c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 159564874 1250 159563624 159563641
    0x10905030d05070b04020a330f020307020603040602041203020708100605031e0f0312180f030f090612010909050f0706140d0209031f060f0506030a0b010c020303160614 74
    0x440303c0701580100300744081c0d611840061141d0480390032140d03044001d03484c00d9605601c400d41d88401c081e04420500c20318040c003001100c0c506618001d82c1c0060304140300380c00c014200ba0001e1900300707114102c00340c20240c654030341c80b40e810006641a40164411281000990028407040700d074001c0c2507600b0b000c22414140400d50701c0c510844805405840c0740c90704094240c0500452400841840940b42e883e01c0070313805c4c41e0300c0315015180f007031111500705980c3c01e11007000034650b6001c9650740041d508018080031a518503810504400390040b40400c011010080c01480650280c1026800010b401c0c280d07080c500e252490726104542e943d0300c55801441025006415886841c210101c0300350740d0740d45018800080e0195852030b64142c0b10f420303201d07607000380503c059000480d0780d100304001103942e81c400091500c4040c03081c48e81020f400c0000c42c441c0040c0f5004041100c906040c8040c13504202d6010a00c1c40e0b01c00c2030070b100b016000f14400c03010400305014000320020012204141c03420507615 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 159566124 1250 159564874 159564877
    0xb010b0415050a1205070c05070806010e06010c0f060204030303140f22150c020703021003060b180f0a030b180604150203040c0b040f1406070f110d080c010b010905030d05 75
    0x540000d00002040841c400341c42541084d8001c401241c00b0300c40c60400c08170240c0f01c108114401c68190041d0f40000c50700754030010340c0301e0480364400d5604019803181c000546031140068000d549145d01e000502c008600c050004000031486658002009600c0d8911024a03410183c00200115050000d001d408650350744101c007424081301411000c12142d1411091140c0350814020b031003403c24540c54003064011540358200c038004e0303031030007819448500c04808580d4a03000c0c2d000788035414010000a41d81d88402e450700088040e04640020100d000001e00a0711942e000b140c0c110742e8241048180c0b0800301d2100c802e504544014441c1b4100b43d5035843c03419810546945a00343e0220005040c4102400c20500924840703280c1d030303582c0d912070820701c0084005010f04080034400c41c680e4001402c1820485203000e403c02e051868800d51503445068100a281c50b660340520a90200b102165180004140303044072203000013108008200007414810941c0d10091094114408010f0641c1d080310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 159567374 1250 159566124 159566159
    0x10c020606040b0f0409050d0f0f08010605070204060305010f0501030c1202010c0f020f0916080117030d0c0203132c192a020105101a0f1303050a0f0b010b04 69
    0xc80c0828003c0190010800001c1da0102c0e041d8400c1c10540e4543c14428017180c0342c485e204907030760b401d40b108120b00380548980700703250a503030009110b000c010030195100ea805004001c2c1f00501c0403e0a940d02c1e101e280c255a02c1120203981503a450b001001003080c1c00110000030705084242c00441030302c50300046d04041130f140000e0310441c0f89841c07a0086540d04040001c00c8040248115540c3c2004111155840520011480801c1040001081c02c07840d40c1074100c000320f04034000b1481d2030b517205044c00140801245450662006000074240c4001c605103820142c10070340003d52148004440760500f401200000d00d00804d4000f0500030b81c03265030760182e407030030081e0100032512a07050b20a607004400e80700343c201c6107502c1c0c45c60940a5143d041d0402030240f0511191340d00c1442e110594207a801480c0070f040c01b004102000141c500300b646401a1071180441d4048031030065580e1611424640100000c0320382042c40401c44003000100c1614901520342c0b801c0c0c2d0303030420b42020343c1c1c4080342500c40c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 159568624 1250 159567374 159567379
    0x717011e1403010e0706090f0e1501050a020a0221160e06011413030c1d09061617070503040c09060f0522110c0706030203160f0507081206090702010c020606 69
    0x341c0030001161004d401594110b0011402c40d0b144075a6410300808458480c06071078180c1201040010741c1c2c0e2401100d09000c1d9607060500782c8443c12040040d200c5500203030741101540104920032000da0340b460391460015070510890180d11700e00c660714905054044d85100e0300703201101d0040c80481c20608265500000c02e08044003554405d107001c0d40d203402000b14241140c15051008401c20a803a0840310403103028143c04140300700c42204900d48410f049440100720360202c40041c80c5030f207542d24000018241e0741414000b420041001d4500ca6000700c99240c085040002408104800100d41400808503908200561410036103035105803a814802c20303100e1a0a00c00d140403a65250410000d840d048107402c0000302d4400c81c100a031030300803101d1540d00d4010107000091590107402128840c100c4001020303072140120354140c450300c28201b610000c1000c04c2c461040081c440c103008241066044007000083c4c03400604129503000300401c1001164106070410f0b281e2500040e0540d08403108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 159569874 1250 159568624 159568649
    0x2c0c04230712050a021b03070f08030c040905011d0105010206010f03020405180a0614060301060501051e040503150402040501060c0b04060506190f030b1b0a0e0d0b0717011e 76
    0x101c040803900e51600c4000507200600e00b1050100c0c00806900500a1504500b4240410042413454984a01803404042c0190a520900c41c000a000c00c00079984051310119141c102604c415a2000b00c4500f41c10006904420030075040c91170280030304140c012300d402d2006040560400b00da01c09071030302520000b030143d501c880c00b0404100c03003003c4102000c2e00070b0702220a10000d40c280440076101c0803001c0c84117030789400b020448a04044c010131b030a4900607110f4070301c0c01c1c0c201c824107080400030642ea00c111000030b000104aa6409001d9a1041c3d120f5010f0740807a0b0400e4010001201d1040c0e00c07103418007010210401c0040c01408d2080c0d131281c1c000d0310009040c1c0d64003012603d4039240454ac9000811481d401041c003400c2d00c011030081d070f800340d80340b039500c2d40d1004000c5120101680600d50001e205000c00c030f04a0780700b005503420355017016087c0100d800490765090022402501c049002c60a0750f80792401c1100308600c454014803441440a000d01903503046003008803814041d11002095 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 159571124 1250 159569874 159569881
    0xc15020309040c1e0207060c030c1103150a0f0c0c0206070204060e0a02040e06191505090405040803090f01290a03151407090501050a05030a2c0c0423 66
    0xd1060703454030900640b00b80301d101d02d10400107000c0700042c500d41c1e1102c80e0010b8400e0200740700149000c1070340e001d51685582044192816602c421030480200d035a0341d01d0003c21901a1070600955940c0301c501c009540b640c6c24094840000d440c840e45020080c0740c50005143c02c2c051f8003c960042154040c0d4195550310201d001180140c40e140d00000c048c20981000e0182c03030a1240c1c0104210f6800116440701da885100c10000d2403400003013800020741d8401c8092107421100e071341d052a04491800d0940c9002505004501aa0411101912001400720400405900521900b104c025580000f080103280c201000c101c261000c0302c01100040701c0442c040301c151280d01d600d02c0a160054a502d040d10b00100f01e403000340102800c0150a210b04102281c0024010400d010a481050b12040e0505001403800c56803900002c0c407407900f0644407042091000106001c084000d00c109009440b0303c002d2005491030300e801c040706103000d01c3c80c1010b10010709200007445610010050b41800060b00d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 159572374 1250 159571124 159571127
    0x7110303070606060e040e010603080702061c060b04030c06020d120b040914030903010c090e0103060507210f0c09080309210607020604050c0d031205070302040b070602090f0901030c15 81
    0x5480070042c005840c00c00d011481c0f9400c9201058080c0d42224140b04d144408111603081e80c1d034520000749003580520a030700042c6031160180c41c60392225904059a902d049200d50182c8040d984080d1515900080074404e200d192200d2070301070005400203000d041800d1000801c141c4159403804138003582c401c0004501c0d41c96800c144111500301e02d001007803085034071089803245e1000402034860740c0381c148003120650003800c807401111050904800f19a196403600c6024110081010042002e80e02030b2005000b2401d14601c091807054000140c07000c0490314502c201c80d50304050106010f1801000c015075100041110040c0c6429545405406550324120004502c40b03580c49100d40148000c05c80d0181c1e0005007184240e00900494451080340d509006007041f20b0400500080c00d404015460120303070b0781115401c0340032850010702d032940d125103880103074002c103004642d00c60300041c20b2181c9240400388951407840444a180310740d451507584a4007410148260980c042184802e00d5006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 159573624 1250 159572374 159572377
    0x3021503010806040f02150703090e0a0516081b121603110f0c070b0f0703080c07150b01020c12030405010207050a060c0b0403091203030b270c07210c021e010507110303 74
    0x101c07d8026925103a0140d450b000c2c00c4522070380620500e0155907070005000800500801d80500004d05090310321170740700702003240c1652000300841ca02c210313400510030000c2a21001030441c8004882c009695007000520300c1071075401d8804c624105418201c51030305410042e4210b0702003400c605a00d80d0703210f1040c018039003860850b42c03040c3c100c02004580e015031080d04a000301407041c403d035103908990ba6441c00c0030b042d81c00382640c090a010b0310018004017403d280c0d40710005012050044880c104142400110001c102181d881c030590008074080003135580400a10016100072203007254a68140503004156030209900984401803072000f01c0c05141c050b00a1a02802001c0002a8424141d0401801030400089182e00601e005040d0004d900d40a016864640c21a40c000700e02584403041044200e400151084d1400e64601400400312030b130070301e4540c108411f00e85411071361042a0041140007850341090801d540641c44507401c41c1d80e8010121404154003640703002c0180c00304e0000ca49107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 159574874 1250 159573624 159573649
    0x6180106081f05100e010207080102131701020d0e0304061b080a030213030c140a0e150111012a020606011106070c0606050d1b05040b06040312170103080403021503010806040f02 78
    0x121421a08260103503501000b600017500e402e80844007a141c0d0783c40700d03d00300c1c4034891804803050707407039a01031052800e240030000b10050140e0001d81030888201109040b5400c555603080c450344000360400c00f00390041c0c2c00101e04040130070f03c0d6540b01da05449481d2180300e003000440400d90b0020b528026480c181a90002131500040c1c2d012400307488400303546503070303031868034042c8541d05010300040d8040107950310910032a50104500c4041d00c0f0000103607009412201d0031b800d070313548858001143d0001d0801c0b00100f907410b107280401084c2c00c09806400c5c1100901054100801c5202d01540114001001504003a451801c0c0307201400d28108100100708070b410941d8007600d040f00400034440c0010315a10182c0040c0c0007030505940d9403080000300c0302c1603501d0310303080602404204045030703900c4414011102c4c0c900b040c0300d48580840b4100d0300e10310240c0003100c01140108040c07065082424070041148600c926261a5506000007a65075490082c0000d082c00007854800e4210f4a800343e49614 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 159576124 1250 159574874 159574879
    0x80307110a060501030302190206070212100218040b04020a02031801090e0c03060307090b010212070c080106080307050d0504050f240c01020c010e0106050a05010516020901060806180106081f05 85
    0x54090300e40103003e41020710059005220780b40110642c6204045103446075a401480b50f032500350340ea42405004291118540014020650b4a240c202c0403400100380c15801e51440b41c0c942c00800041004403000d900025005510620801e44401e40000c00c42c0e0300514110b24074541c000074200125030948650308a181c1c00740010f130600c5111607491002d1400303405d04405840020f83c8406c105002c680b12076002c80d0059004600c10015010541c00410354503008440341d070091030303d4641d0182034031307001d0380500103503400015500c052100c03d00c4085002c6201c0d00d4600c0ca13151900001641009000000b94410303c40005002500400300c00c0661010642d40801529401c104d500396000b0740044194580759400c0c80c040320310443c010b05c144015220300a020016440c10301c0011102d0750000000c002c000c0b091201c11201680e00c0302c0038a4003d24299656035800c2c503018003032000c0f00d59202d98503070350230100d880181303c2c0ca070300b02c61040d60105a5511120b070030507403003564107010007681c1d00c1680c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 159577374 1250 159576124 159576133
    0x2041d0405101509050601020610171c0903030f050304110f030307060606030c12110f030c16060b2e1101090209010b070528020103150b0a0c06050702070b0708030711 73
    0x1c0d1554000c500c20004c9a480b8a8100300c995240d00c01680c80316070448581d2000e81c0d400ca000d002d0920325205180900207904122190f04181c0d00c040e030f5203004100e441c1804182081c50800405600100015104400d4504207065040c10340c4c5000000340700001c0303144501c07442d45002c0842d4030200141d95542d508004240940c1e03540d0700c0c000c0c00a203901041400040c0c1c0c100c106000e80007050140443c80e41e560207240d45400190750180390641c00c0030341000ca51010411103124480c007450700c8017008a001b00780004440000d5010071250b404262403408288a040000183c07604d14000a114003411b54107000ca901d114100c442401881a0b480c0258050309580020409042010207030039000e106a04441410700c1048036104c2c00c2144581340c00d541400c40c1c1c483c2006503c01d411465625800c07000d039031045502c49141c0c05807071b000b90350702c440094440059601480110302480750849420f0000d40761050a04120780858441d5030303001783c68507200002040126120382c0c00d501d006091001a05c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 159578624 1250 159577374 159577391
    0x7150e030f07410609030708121503060f0a06060903082a0313050907090509070e0103021308010b040b010801060903030e0a050a0b03040b160e01080a0b060f0a08010902041d040510 79
    0x1020000200d96584005104c0c1c44009441114004101c0c0c0110f90050b90745170034403c1da6420487c0444004194102c182c02c4505da510702a00c08000307982c0585442c194131116807800b0b9046a048070b159074488000c100841c0030030404136152b542101c0329007000c0071040e1418914000b0307000940c518000c094420344400034481c1c0d44080c1c0300d03114006980084640045648991100301e516512500450b0b501c04031304404101036502a1614040180040c1009400e0003280362b042c218103d05a803003500303965152040d107940d0b032410388500c681511003400e015400e9410a00001c184449500005042c030100b0340c16025103654084c95078ac01810010458400300341c1b00c10104119420540701160942c003900040343c14125100004072045801b555515150b00900e001151a100040c00b034250165598001c00e44a842d610000c00f220201c1c051b5450f620381c2912401040f408059104a400c5403040c8424055607080b035030b00703840400a29100c0c0035552120f0402e01c0c18440c1ca11402003040d403400400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 159579874 1250 159578624 159578723
    0x806180f06220618050108031603110a1103100c050405150d0c0203070215040303080a0507200c13050609040809130212060901060c0b040308180307150e030f07 70
    0x800384c5000c2c401c1d0703100c900103100d50a41a11028000e0394440d81061080c600074840c50382480090030b009143c02d14040d000c41d04503a040c0a0058000c2c0c0b5010a0f41800c224039040030040c078210441c0800301000044c60046000303240380214003c80d0300c50003040500c0d041200d0814140c8501da030021008020f100c800000c040e640e0740c00048201d014a40544508003c030007000c050394202c981503121a40a0399400300d084006200c0140b900c8148141d4104940740ac6140441c50941030960000902640402000700090140440614040039080c002081419203c40300f0081c3c0145d40044001c0d00e403012040014403a0005001003840e4520104007036030000d00711001c1038001c0d641030303a0303110080c0d881d40c400701c440c00c00c8030502400c5040d1080200e40003911540d07801c0da1148104150341800a00030900c00d08682c800b410641b20398200350340412042d0b24520464120210010013580f0b0300402c10b00000e1103003c0c036000900040785a40360300301920f807a21020400e6075404d00c002030401c2e100841 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 159581124 1250 159579874 159579881
    0x3030a0203010608010503030c0307060f020f0318060a0e1c2a110d050d0c080c01020a05030402040b0121020c120a0f08220807060207020315070806180f0622 69
    0x3c0ca00010300c1a100015031801c020003101c04402c1702c280614076101250721303100050020381400c0140304ad400c1200100f40c8002001950090708828061444544c0880809103044400303008040e1140c03030003554442150000506146501c011664160804180350382581c2184507591400c24441e2078007440c0394100111002a02c1c0c1d54480e240700300020301035000740940901c1c6a01d0043c80b0703500100b141083d10340111407150100c0d108400c0640b420900545450aa81000c04a28042040402070004500d841d0186804c00402840d202840001545071001000501c903004c044556000454200c02841404420038002c0c0030a80301c0d903511501d01c130013002c1c2c618145583d80012002400300b41c2020158010552034151601400303400d21003074850780b03450b6218540455181da802c01500e40141c900380400c009070765200514001307502d02800060310104e0001e103060b1240e69141d00c06d0325070340c0d501501c4e5038000c03100000d0b4140c5a0b440002194560f40940200c210a020b481c80207008c0180540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 159582374 1250 159581124 159581129
    0x13080607090603020a080105010804050708030f070b010911031b04030203011406010f020601050a1e0305070e01030218090d05071a0108010f0c0e130e16080d0816090905100803030a020301 82
    0x35604000c15980b404120124060300e010507002403400b2004011030f610034001150440e00034000d4032140f9035182015851603000348403c0280000c0071560b00300384000f0703901c06801080da20005010804641c00702c8801d80c44024a0a0500c0c020b03030006180315901d10b130959000d182e01030b0082010003d50305100e00d003120102c03440380c00548001d010780203061000c50681d041350006030500116904005000760b0302c4816015a0680314140c800000205030204090802084100400c840c3c55045006101003150101c2043d841c0c1d00303c64051003082840000c101d1f00d161000d1801d103407101036501d04082168200400105001c140d4400800c0488040d800242161411942000800c0b0120402e0b00c10260700780300c2e140d01035142501c5130321031020b903005030015503038803420b07582184041038504884000b681c000409a03484085040d041d150064802508500c80e030400d40031030900024000c01c442260701903180c40075150400300d0400194503402c0d1002d400c05d041500e45a02c0d101000c08020b40017403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 159583624 1250 159582374 159582377
    0x307020307060b040b0901180221060109050d0f02060708090d05012a1b050111041707050a05281208070203070f080d14040909050a0605010506030618060613080607 72
    0x1d11480d0030f510382486410318500024003ca0780340da1074004c080801c00c200c001803e44640c0c080000076000884040c880509400242c201042402e225000410261305c1d030300301c5402a1200a18400030412549110342c200d5070490f20540d136200c1714503055031140508506243c1213400301122004008041d0070505107483c16183c980c000e0b654a28032152420b01d00b500007400314604c0c1d500d06800041011144420034059800452a242a0742c0001065405130388580b072600e40c500403007a017100081c4841c1d0010542101c500d00708909010019200c0031002082e680024038035405041d01c869031048040081c0750542c070018101003076081404885e4000c1804034030a004828000c102070540e90031500988948030002c0c00d40d000c00000a8592182e003000c0880070500038132000070034551341c5c01040c0d0300501c9100070b03000c071050791b1410b40156501a000035200e8003080c0104a0b264840400c000c8801d030210141000036100c00d03020440e50312810f400c809102e940c410011a440b00c0005038503002c1c0c440c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 159584874 1250 159583624 159583631
    0xa150911071a01050d110a0e070203031b0415120b03010c090305070f081e07031203090b0603011a04180b0c0a0f0804020f1011060f10061b1214030702030706 69
    0x12892031503440024040c083d03101c2c00795110300700481d600480c07a0446c60000f40c801c000942d01d03100c01680c40c0c00c003154400c0041e40004100401d024a44c212500d464060f05106803c0504100b54100c130002d040c0b040e10100241443c2a048004031030b003090f161120302400030081807802c1403000303209060a000a40340c900c620700000030304840c16050103040361010b6024000f90034626a030103200d948040da03544510b11521102101085080d90040d0145a0701d48000801781058580301e249500010300c05031090345060034800d000d04403080690500c0d041260f0004d44016420b500c441140010240501881c0c224010809002c184c1001400102495240c1c0c8075040f48800d0121150395040350000e4100c111902c12030303218185540503000c001e0542c14051125401c03606a0703464224101c0f40d08100001d130000340302d08510032003501d8014084030f20f4206111003400350050104a401540100128a07000c200d500041c0b00301e17021a90f200749034144c0f95803030030204402541e0f500058401c2d80c0b214079 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 159586124 1250 159584874 159584903
    0x609020d061a0f130905070302030f0f06010804121101061409240904060b040c020c0a0605040506040e1f0b0712030504020d021003110403050604140a0b0a15091107 72
    0x2540600552400c82c500312561400792012000c0910f41c003e0b501000740c1540d441d6001c100b00d9894002d90303104d0300a5a0300141c0320f180000d43e82d18030200140c01080850700440500ca4640d0303111f025203600580080c18410070b0030000070220f504030710303409240c40035519014022800c02c60607010b001c0d84000c111351481407a2180d4034107905140314408810805080207211201c00d00303100c04542c0c0e22601440d4001460795402000c01d040d03d0440482d00016000701420301103504e004500b180162090349409070a103414013012130f0b010b100754000c0316030211196000543e00004a040300003851544c22001d400159110608403042e00807140403a00506014420490b042c0b06e44116031142e50008c1204045031080e800303000e009101424407000305030302d0711503c86600b180e1000a03c000c40c4a00018080c034503150402e084500421409602e09401100303600000c6411010302d141c006a003410000340440080081c03135514115980010111802c10b02401020a581c078060711585000c1c00c00c00300b03803c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 159587374 1250 159586124 159586139
    0x90c051909060804060b01180e0a050c0301051309020a120b0403030c032307090f1502010b0607030905120705090f06011d01090b0d020c0604050319030501080c010c080d0609020d06 79
    0x100a00a010000f0080c200080104156401802a059042c1000b40621440149070342510740d04e9003020201504e007009010380c00b6160b1142ca1750100401c400b0a0175941402c00040da9841028003072582d654851030b4070303015582d50000340402000010824804440c141c94184a000d40c1250300ba00801d241695540d481d5000f4024881404554040000c61103224090264001c00c0a4506010424250408a00d61041c00001c07805811841199036002694200090940303850400742c50190406001d00310010303420888050a03108210744038a0344450020b00d82d441c129480e030140d580b0090b054144141c003030182c003015005180a82e92107509034000d501810718511070541d201e00142a0340010000035007910050107a85034020005441d0001010280b07141c0300007070760250781c56000000c9041d045c1261120015181c02d0364142804250f00d40a000d98460400c41d10450500c840d800d020390422601c81c0845400b50f041c1e9404018150303c854000009401c000c13044140a031400c00d000c9145e6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 159588624 1250 159587374 159587387
    0x6030109050f1f06050703020c12030c07120206090906030f100506090906040f0803150d1401061a03040b04080c0f0703020f2b0507080d081b07020d110a090c0519 71
    0x41c1c48000f0305019140090444066002084c1a403c5000b00d1414036030310341c5e86103007001820407918025616105403040c143e007000c4156021200d0030451007182c1006031121016900c100c041114085c00176920040447c0c14424240c41c1c4050ba03004d42c41c42c8944000d0f8a5000c039014090588083c400ca98405c13900c1c680d00c0c201030381d0190641c1e951920b100d0000c2c913028010759102800e84107140003641d600001c00c0b5207106a0204aa041c1102c421420f940d0f11300f40f05100003483c220390a0003520a0041000c003141c4000b80000c0c0007084640c00043c01e2242c01411546440428421200400c40c10b41c038041d1503004d1400202d10070089a601c05130035191035550b680e900781017820511a50ba4000c04c1400301c4d040d10741d50840d0709000356030b400030302e92005201151701a0031a4560346c1e25071520030042c00713582c0d0620085558680040c0b2000001d6284c00740a0001250700602940141e003c040c00106084a581d200314442800d00c000d898280364464050001e03444e0720040c03194080400c41e01074030003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 159589874 1250 159588624 159588661
    0x60306030b0f060a1505040816150c0204110c0d1709070e1803030f10150e060a031d0c030111120601270b07030f020a0b0601030f020906030109050f 65
    0x707640c0d030880410803050b81d41d02e40d030ba00304000900d514a03140d40d40e166600c00031992803498020030b00100d42001002002d000e443d500401120940d4030031810310010324000d000120620b8100079000c007a2108544582e4414202c054003c0d0040d602c500078948a2a0b4400d64080080001100040304444418001d0409030140404002900500e42406505440d035240103200143e21070200c40c5422110314140000c6008450502d2040c549103440c15000003420135030f0348000c01424082c21180e003d540e22141d8001c1459007140e0305a584d500110089003e0000c8618101404880e03980329030b007101000070702400d9170400b40c00a1191030344008002500380a200410b402020341c4d000040d0496226150b03d40300c900d00b01030082090300600c4098001c18010390040302a11318001254000e05812411011905103540300800a03400b080c1d4400b2145403002c2c21603410725440701140844030310030390151122498080d11071a26580c0d500c43d100c025103800d55200954050802c089440350300d0198040e0300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 159591124 1250 159589874 159589883
    0x20403080d0c03061a0c0c04020d0501030c06080f04060b0f19080c0a05060d0207021909140105040219050307090302090907090e0604050a0201050d29010906030209012102040e1f06030603 82
    0xa56034080c918540c1c0d84545520304580c06000c102c511f142e42c640c40a4540c4092104000585604524207160282247d40042c400e00408004100ca5490049031a6901c9a172000700490881410400300d503408036899580b5521400742c951380b54015085071071000883e84464110313110303184150107001010b680c900909420840400c8801d25200080d0020322580d03202800700540c400d0a0a10b03c42c03448401c0e003240035419140e0021205040c51140e0807405400100c800f103241045160300e0070511961702943c881800f10100006050310f01444d8068000c54015080100034902a40141d44074a5540154100c051402c06c10165041001078054451a1b000c1c004100c1008240c0040d1407540103010744c1c03080c03241c64548102400c0700c0014010306604c80b009110100c4910580050505049074000c90704151042c84801c04581c1e00c03243c20310940c903944154240d4038a4010b2008085c0c429a0030004c005400c920501076002010441d80c206444171241d101e00583d180e01c0210151a0184000b51 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 159592374 1250 159591124 159591149
    0x30b060d020306010212030a2306030307032d120509030a0807031515051b0303150f0d0506091f05010f060509031515030f0c15030c0d020403080d0c0306 67
    0x9a5140d800d0380115041007050048814560100d80079109560080f01c002d100702c0c1d03c500c540c040c01501d50611002a002c21807030883c061800c41d010a80d00d000358000601040ac0034134003440c80e170041e000c040001c1c100082c0c035442d242c000d03108003403c44a0703000400a915481c000014950600200507203590326503641c0ca01c000c0e038845040c06c4003d0049240b0741c102100309540b0021741e40c0205104a0041070302d54580b181c80d05014030300a00708031016054100705401c20420400780401e4030700303400042d103402c03501d0302c41e55450200441e000d06040072008015215540a000b0240400201c8245007044148038054030b28191200405480084c4106520342900c41c030107201c000e0290000d00081c52010341102d20070038080401c0d001c101300030745035110410390f0740320302c40410700f4148421105800c11b44000d16410f410358010601c2051720b082c2c0440c2d003a10100100340c0011410301103500f401d903900c80c20b5444548034104400554402e140c2d2030101417a0041c8080c000f4064001e04084603103520300381 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 159593624 1250 159592374 159592387
    0x1e070309061101110a0903050607031506030f0b03030a2106060219141b01201e150106020c12010e060619030c0314010b01020a0b1f03290106030b06 65
    0x26144010b050805140a54890f142c0c18414201c0c403000c0c03d0204841c0d03842d581c681c0d156041681c24990080d004c50101801d0102440e4031401c1550240100c603200d2500099a064004e440300050082907030880c0d00d800000f48008203c2c3e8081015102640800a400094142007011400301c58181c4140030140c0c109001803140c08203c1d80300703101620701038240340340414000300c03410f8200700301d9a0b03800541e40d0000c9044202d55910071411095202c020071904210091440030035501d55180b19545075103110001c03031151b0084207100001c452031ba0014000e0641d44c486c00701a4441c0503001e480c40c05101201c054071102e00c01400f072981e140c2c1030f09020f0502c52302c1c1c034028448507421150001e0101c21a4002c00030004100c1e002c85402140981000145510300c00782c46420b44403c0808103045500000b544004500010342d0150401030100305040003480100e552140c0000982c406001e010490a45900c1e00000084042c500c000d0188101400da880340340590850f1041301e00e141d00640c0a0020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 159594874 1250 159593624 159593627
    0x209013f0204020a08090f011109061803070305030a0311070b041218060203040503010608060f01090b0310060e06010305010503072913030302031206010203090d0609060b12031e07030906 82
    0x150203800c0c502006400a1084a401040c140c1e0301c800c110b8400a94442c040001140c07080c4042c00182e44000000c2c41681e07480d07003034101a806211255032003400c00082d000100f040e04bd90306050b503c0081d00b607952013903803820240c0d00e942050f0801004603080c5104042300743c503a2011180103a60000c00311040e500e40752180e104800382c000003401489400300031602e102c50000729460050215034011691070341854241802c1d14400d6120303144950010701440300c006800015581924000000000e0442d203403400a450010810400160a850a0030200310300e011890700074031881003a00c0034007040e42e84006150350f03041c5030301c030b0201c41c3c904000111141251104a002c0b0004070703c1d00c2d40d400d01d071102040740c40d0801c45904c203c015a00c0026415000c1d20035403415640300d40709001460a000b081c00c013180300034800c01801030940d5503c0078900200807155000342c81881002e00581c09506810384900c1c0d0b84d0740140c400d0440b86180c1001001c8080d440021a21f003c1d506944200b0b141d80ba0100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 159596124 1250 159594874 159594959
    0x903053a0c0203010e1b03060f060108071202030a09020f030c010f1b0b0f0108060c09030c1c060c050d060e0903070206071713090606030506030a15020906070c03020901 74
    0x4a000c020780e491102001d60341c240070b0a41c034043c0743e0001d8265502c0800d4004c0644442c1070706035000781c1110003044410045410a103078003060a0800c80c50f1650b89600450b21080303035805400d4094804801d00c030a402569100c40c0529100b80c03901400f040c030079010555a440c10700501030024010420039070344a44600d0020140f44090f40414903164040c0d6210080034008a03203881c0d40d0144c080040100c02400c02000b40c1040b0805e044500c0c086946010a845502a00c801800785d04503520031040d0300d40220344000c8850300994208038100c0c00001c000d00c03d40c40600c072000328034248003000c41c0205543c60b00e2400343c86a080150f10b001e0299080c13020940145406440015240052a84282e880d00003007800034440074807621514207000381729045803000e811007030400d464882040016140001c900213031b59044013410001c1941714600101901c2202c0140390405d50125942003001103005045007a00d00c00c5507c4184c3e682c031520000d003000041c02048203200d024403000b1000d00320604 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 159597374 1250 159596124 159596233
    0x30a03032705100b0d0302060705030c0f130602070611070905090c130b040501060e1003090c150203130b031e0901090614060906030d0c06110c010c090305 68
    0x215014000c12601800000180410030a42d556081460344440380f04084c412a680c0070030480c1e00d82140030f240d03100290f07500c000800705018004000040783e0a60300c20401c1d20250a4181c4d031040da40d00000700606c400140701c0c801c820240c42640c0e00460081e0242c0280410300004200400101789421800d01c040c040242051080e405100399418058648422643c900d04030840003040b00600c800500088820507030000e01007080803d0448035940c0e0390b05640c10800041d10707000c62089603604196588003416404400c58019146a080c0f600f0b8001c4080c0c0400c0e285d0310501c08c0e51550310403030b4014030f1000321094000d81160400035070341d00601c5110b45400038254000003074500443da4500048485040d02200c1005144041020901c0c10b03042d03482d404401a0040c0030010f80c00c0d1800303819640070800003030905448942c3d102641820b8419640c15100500c001c1c0005603540d030300a004408280003c1d12a170041d880c015421074400d4860604610b4001504010050003000c1e8004400584 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 159598624 1250 159597374 159597401
    0x40c0f0e0a0e010f03032a0f020a2105010509010203070f14090a0b09030616020c040e010e070b0307020610050a030f020118030501050105101d04050402180a0c0815030a0303 76
    0x4840810801e000e544414040d20754884e1400300d003819401c0282103001c0c1c444e000200e00c001c1807114022200d4040a00c0c0c074096014801c00c125640510003d119034440760840520740e081100880601110010400364880c001c40c001c11050b00e4a00c203103801c0c0c0c841140c0c61404510111081888107200e0b2455041841e0300026260520101d80d002580020141d400302540c0b41c0c0100d1521500e107405e001c42a00a4806400c080080c0700b1030750065203411a940704140700d9943c40c12441808842900481d9510103c00180c44021f91100c1404007140c01c19240709005100f11000100044011010745080d550000d001e186624a507550b048184142c900007241000300000c1907001c3d80c088032405002940c4280c002140c0f41d07043c2810320002082c0c028030f10041110103075001106a1124441c07100700780099074040b37480d035618008281ca4140781d00901541007665420170042c0991544000c0300703e00c40d0f9407282c3c8592135495010200101d2171200c168140c100b50070340c10002c0c3c025842a03190380b414 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 159599874 1250 159598624 159598639
    0x206031009060e04031205090c01050c0a0602160303050601090e0c03070302040b03100e0a0b0d0809040e0d030c02010c0825030e030f04050a0504020304050a030e0d0803090c0f040c0f0e 81
    0xc511030401641e100758400008000340f90207120030144c102506100c2d145002c0400c000d40c0c0341c591500da5641c0352500c1c50505000b40042c0c0182c02c100144040c091103500500107651310405c09a045007041c06d0400c00b0b40029241c100814803662140e200070781107a80000340c00c0e040c0d44540c1d020540a40c000b4010005140c0c1c20000064403204501c0594410f12041d448088958504128141d180340010440382d1320070300d01590300c21030b6600e01030041042c41e0004020b9407a0a20074010030b00400340000c14000502c10030001a071031940c503400010150700716a00910054503080b030207954204056448000c00070000c01c0440032004160005030f0303007408034503000c00c0780280d00c4a003d0850344000d85031280c8240000d8140050705111110400620042d5021840c40c940b90312207507200c04840d04010b080001400507019a1b85c1c80000b00200203401c2480990b40342444c4540640c0c0d008101a224003480040c66007180600d040e00c03c8038400d80075a1950400813545a208036007c03000a00d070558040309 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 159601124 1250 159599874 159599879
    0xc0403021008070f08060303071e02040618061a181504060c05071e0b070303060e130209180c100903050115061808030405130f050906150f090402060310 67
    0x2120005110300441d1500c1e140071074200400028101811a991481806000010310083d0303100041124059500901104403071a8001c80c0300000031174410000e540541041e4000c04d1481c40000c4003c901c00802a0030003006d6643c00c2c91a51201c0c0a691003209850f0074050225407007506002c0c00701c2ca80000340407080c1e0b20640c02428100350041d401c0a40011080d107008010458108074030005402e49111062070380240c0483d40440070320900440d00748170300201d400301c10075000b500b200e8080c1c205901300484034a00b24217400c181440020042c0e11620f46880414109520345202282c10380780840a040140152402d20145027500d145002c104216254000003203102846140200004480b81a0703805280160007001c01d50001c49032405441e8010041102e14000011602165020b582e054661203020741501d00811500949507042800d2600704070720810702140d0796204645c0d620418144000c03e1041c040c42d0750f00300c084d854001008102040c09450840c0183d6401000c06400300308242c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 159602374 1250 159601124 159601129
    0x9040b1513020a020f070810020703111014070507021f050903060a0b010305090303010605190509040c030507180e0c0c2d0c090f13080918010509010e100605030c040302 74
    0x240c5010319001c44580c041402100c0940c1070100c80c0000e401480105005410708076410b13250140302c02c558419aa001603000300b0140908441c5e404038a001055070341e0880488640c5015220714440b01c0c110b60b8140000840c0180500e040d60341c000e030060421500c42c0c0300d11601d41e9049654043c01402d204080c0503245c0140e41c00c1200d01c0c0b007062000c0700411a03a00321000541500c4000d0840081ca404c1800140301c40c591080685034420803801048240c49500001642e5600c50f0f8201140c029040061501082d5015000180180c038980e448003100428180c0542e9400d00b85d002d0401c00c694880041840d07135400c0c07805800d0314034214040c0e45a40d030400301c1c3d400307443d8120789407146084c402c414a290341c2d24052000140a02c0c00340c3c5c5141152a10340f01c801c082c060000e200e00355490301c030090241072100c5c0c1401d450324040054440f0300c4440710b0300320044003000300b4410284100350210000c1000603000c944075016074404c029002e091810040b007641c442d0001040d0440c039074010701c0b0020159 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 159603624 1250 159602374 159602389
    0xb03070c020103111803061b0d150e010308071b060509060706151805010b18120708060c040f0f0608010b0a110102040b07050610080c0d0212030a02010c0f020a0209040b15 75
    0x70b201701c641c99000c201c2c0c9424142049002071440c4001b4103000000400c104020089484504540b4070008010b040c00664034160092500303c1d41410b031600c4008010000d1003001021080d000c4d1070110003000c40000e07031a401d1051400382c0d02c002582840083c45508007500a414110701c5200302040020344102120320b9a40150b000b181032004400449103a52100d101d16405424040480c034a41612112415060116900064040d4110314002c01d1410700501030003000d4203904041e2401401d0000d400c1c01c09030480e004004074441181d0b00043d9000c0d149540d0400c6036903d468205250307181403003401179034014280d20028400a002001c126000a100500c041c08100b54010703103540050600f01d2034000c00404102e840b10a05205010113000080c58019861040741c007401001038500c080b8100340320502032981a0306c004551404159019081a01d00d03020302d59510102240c0450101e079034200a02c80a5040510380021030b004c42c02d410031055010980010f03d07e0300c04120fa0108902 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 159604874 1250 159603624 159603637
    0xa090f0204150f18030f08030405150c04080d0503130b0c0d06030305032202030a0803060607061a010807020a120e0607050f010f051f050f0409050a05030a120203010b03070c02010311 80
    0x343c4806040100300380c001c1c00c55124a0320801ca8005014256610805410412000030306840307400f0000508111082100340d42000c44018103105504003d800c1d00c25a8106002c1c002d5176006007407004a51038400d43c140d034421080441c2c607201c81c003a01d44403220100f070090032a01c01e404081202c10796402d050300404000754480e648440d0350b0f140040126140d486d0700c552080d1800d00880a5401680d40068403152070b90304000300c41c3c1e0300c0c2c032404c0c001002440740f42c038001c10b500d0400c00c1340220141c603d030001c1076500e420b80b0f513000995542c102c100c0e120010030b94020302a40d041c0b05d071400b043e84a010112443e04001d4481450101183c44141c41c1c1ba43c00300c899aa585c1d1203a0501c5242c0d10580107258102d21701c08000030b10800380c0c84070b5a00c9031066001c0c080c0030f000141150469070751140c10591100d908034080da807030a1500c0c28065143c1c7e100080b45000300f00d040070701c5035003101300344202ca04803014401c460f13083d03444100089a4200c4100380613030402d80c40e02c40c0c200e02032591800a119 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 159606124 1250 159604874 159604877
    0x20d05150406050627070203300606090a14210d0e10091e030804240504030c03020909150c0d0605060910050706180803040203010e0a020a090f020415 66
    0xe41d14140c41c01c00b050707940007803520b8000c1420510784c100351a0180f007261440c814080461030203039038075141207165005420150441091528200c041c0072410700b07040b4061807803120384522030341d5001c09001180c421000c00c40c2c0c02600c444020041d2008009440c00ea40a00030a40401c00040200d401d004401242d07030380226400c4880ca08522039001440c10030340c4103056999446000300803002402d00c003100e1045640c90b2049180400904003000c00440c081e50340114003907202c4da00c425400b58884010281007901c1c07035556891040d600c0c040c1c03040c1c0701201e0b4000c0b81007441074150780c02d02c01e802c00301500900007842a40c0c0040c042d1704a0485113071080c001140100d840b00352510b441c005584007644600c1c0282c0e8108141d01ca281c2f42c004139200348500303d050031680c540d06031500130020324695030103569981c0150034100400002100950040380201c000707110b20204600310365100c1a80752002035121403617420401501c0daa03604146089403104800509096844030503c00002e8010300510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 159607374 1250 159606124 159606163
    0x5040b07030905100e030304140102010615030e070b0403050705151611030d0305040519031b030203030a0b10020a020f01090e0907030303110c0601120c090f06030c060f02030d0504020d05 82
    0x11071400c00d480942074010892800c81201d0316817002003500ca2280d40034180c0303c0034000d120101164001d4120000900c51950210810400410010024a1040d1032541306024801c00010b050a1010a66007070b40d8010025000c407a14000c00c110b0b140c5c0c116880c1c82c2003c41c00303104010040f140c14604040e07540c0110008400d04185508260070f05d843c0c04800f20502d490030080c07001007a40024030400d54107150341110481601c6007420795100c66248240405004403e04000c2019408000b0b1806002848800e208842c814001c000700c0700008085100141e000d1203075500585054501021100c0041c10980a05622441e410000e040111070303000c0c45038898842003040607031500c5108260010151030b00d04005142d40820b07280c50042c840c043c030200d03800c0d9004042c03041ca5600c80c0300030083c5550400c0400030307429010b009051148001e617002407001d07000054590007424400888801980a9440c00c801100c00c40c000345000740041e60003c406d11071881c0080c80800001801014184006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 159608624 1250 159607374 159607379
    0xf0513050601120f0b06120a030210050c0a051206011e0e100503010f03030e04021209060907141003180501021210050a0b0403020607061b05180f0105070f0305040b070309 75
    0x40d071030841c06070f111446061000c0180e50210700c0b4002d412440701da2143c40851103803600e0000509105104480c0d80e858003803010031400b05900001c120851441d4800305205030341c1c40865480e80c034011503d859021500410072403c6444442c8641035008034141004c848007030741124600181c1c20400c000d00d000c5410845101800d02c0c01c20700d0603820b07400c1e03031806038030315030400e000143c0b041c202c0c0c84000c0c18081c4070b941300e282503580da805036000401200041a480d02d81a2055a07450720181c1d04645640107412000c1a0765100d511440d5450802800a140700d1120304006c40003070401441700520000003074950f100150003800100807070034007002000c2190929204040c04d900c0f150384845c1c441d1001d000204a081440d006650480781c044582c1900e801890504401400c030000b903002d8400420303000d05030030b19080300c05003101c42d90049545070781c0b003021010303c606003008292103400704006019040028003603034801040315100c0e14005041c165180c004c07032425044904120042407203003209 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 159609874 1250 159608624 159608633
    0x13240b0c1204030f0f0305090d06090b07020604050705060d0204050d05150a06080d1b0210020607170f0105041d03040b0301031103031e0a0e15040801050f01031703040201030f0513 79
    0xc11501d6905220307245064599615450040c111420080240c01c4907520b01c002c0c103000388280d0b41c104c0740103004603168600a1030300c403000b00760b088405c0b40d100b81f5001c089608030348001821403051f80d00900810a5504007030403c803441d0804140e60101540070480415030352207a034403469a00c0c0c400d500810440349440c00c99182c00b20003d0105000d02e141583c1080b2781807002820a0101f165804c00c0c0b5102140308110307040c00d007400c0700081d4005aa10007528001940040d000703204118540c0c91004d60070712138031244000340c4142c0340d005e44d949056005008610301035000c5409800b032a9200c0f0519000e1070569400e580299024114001020004009000081003510201ea42c22006140b80c148040d0714a2842440c0c040e0f04001202d004ca0910b4240740070b48425014558014041510100e9641d0100505d62141c00390308215400d00c008644204185001e0720f0603241e100100d02450045042940341c10380004006030304042d214402c1542e00182c0b0f11485004400080e4804d048207000d050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 159611124 1250 159609874 159609883
    0x60f0207140d0516050a060c050d0e0105070506071709010b010206041b1a09040f0908030411040609020412140a0308070f030605060406020a0201030509071404020d0605030f0d110c13240b0c 83
    0x20014407a804052300700081c0f01152000c05030059041c0b402c0c0409190004980d0b80c05407100c0100581304034000d018580c0d401003803030030340c0814000f40c0001c6035a45510341070030f0341c1c000008103001d0380c0070501003070000c4c000412039400c8480501d41071800700c0d81c6024145484c019020759100701c1c3c03000208400141018096815010402201400043c419075555640d0388001000605849200c3d091000c0c241c1c0e03aa00210028042c1943c10754803607403105485000d10b0317007031042103908641d070700420b40b2040350100d61002a950981c403070240c0c6903170b92442690070b0707030550209034205a0745001c081090360320040644040c00c4554010a0500094400503040b50405048811643c1c06240c08001007601601c628440040603100542c507a080d50845030003924031a04010340c5030041c50549a590300d4000f0329012440300700c0c0d0f101543e00c2100c0407a00c0c2c4610b4182c071026042300101c043e002c14010b081c1c000e0544540d050007440d04400707070280084200007058001e441d4050f400078503c900c00b1000c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 159612374 1250 159611124 159611129
    0x310091a0105030303011d1801051e1e0103030f050d1509050f011404020702030f010f0504260306010c1a07050d0c030b0639060f01060f0207140d0516050a 68
    0x6008520310750415195914400000c0d2440440c2a82c000c001190500341c032103108d28410300c4800900844c200b0040d41844880750460b440703009140d4400240c4242403001020303050300080410850f050b421a141242d01c14039480709801400010090240680060301c9510143c14070080201d00c51414a03000c0030550700081d2215000003030b8400180b0610b0503d6907183c0119108840059483c0c070349201090038038051031441c003555403030820041358040b10754001611462080c2c00211140d0748043c6901e03007420380001705003901e080500000340b10354022002040003600030508203c0b4604000d00705600c403d021035502c80058408a00c0500c88401030140403e58189030405000301c58160307000c00d00e68082c0c200700e80e000e902c04201c480406184a41110110b840141810f1568000c004c3c446d03039980c0b010345080c03184158410000561034891070700d04001203510f6019040252034034041c0d440d215441845c0541c03008110014000051080006000c5c0756034170030700b0307011582c40c0c50b04200c8041c440c0e9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 159613624 1250 159612374 159612379
    0x340201140705070b0d060905011e060906090e34030f0605060712050912070e0105092503020c24070c050604060e0a020d030e090105060f180310091a0105 67
    0x1e01031000000c8003c00c50400b55480c2d2140152620941e900e240041c01580e40300c00d2010f45414004540c04c44c42c0b440c54525215443c4805090329a1864100c0700710a01d403040900280191009000395080041e101d5004800c84c5a44000c000d121014030103103203c50040d10500303440c200c10014a940d090702132401c2040109004001c3c013886c041c04a0a24030403a100203004d0b040700206029127a029009403001040064402d0841ca090100c81c541d690300c1341d005110f608a00e405c00010b080c94000049441003404400c7da0061191400160f249010076804c9541031640031700030100703400400c0124089481f000101649005200d52500404407000ba16070420080c5140035400402c200240f0b03143c00c16030180f07002840d10044104582410812080203610400301c016900c10705a006207000d0042d801154114100c1e661402000603e02ca271900c07801d4620301c140078402c035003132043d8070341c00e1074543c094140c4040303540e9180b254048130740110f01240e811740142200009a40d441c4003150240206 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 159614874 1250 159613624 159613627
    0x80f0f0907030807020303071a0a0614010f03021e0d0209121506011b0209010308031603061802070c0504020301120510020c0303130813080c03010b0406180234020114 73
    0x1042440c0d44400d401d0101810b042e2002a6000464800f00211030096800c4038a01c1104164404d0121100c0c006840c19120207040c4900412a40440481042c404030f058444404051710240143c1c00ba41142c6d400c1070010541005401c2004180d40003403807505c9000400580c0d901002c6d00708046143c02e030740118501d80c07006900b5100700340041ca8164001000342005000005008600181c8815408000b500468142c00000411158001850007800c4882c1c40c40400144c80004508840e0b042c400c2e44c17000c0510340604a01001694003e00c401c6004142002c003a5403202c1c0400c05030ba0080c1c1c4820840107804095205201041c4403100b481903c424007517140c031080171b094580e00e0001030003114204000c964414104003034181260141c0008074103466a0682d034021480e19216541c580b50302a508041c0843e1951034035210721010b40b290281c4c41d05090000c0b0701030318000d40054200d010310b6581601d4040d4804480202064078030b52402c109051049a840014103180502c1100d8441000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 159616124 1250 159614874 159614881
    0x4506040515061512040b1303091502011401120201090b0406050409270c140d08040b0a180e0a0c0503040506060904060f06091b020f121e0a080f0f 64
    0x100490254401d680d03085500c10541c80ba24005541c02e10b07514840800460001054080c60340910291381c812800790000964a5039086502c1e450304440003002030000b4401401404a019600381c0c11103401c544d4400020a0311120500c00707607000080e040030400b592182800c504669100751044084d00440035080d040610707151000d82207004a010b20310406840340611440590084c00c800c100c127200c0802d09520b0302c054180703458a004607004140e074403000300840c900d03241420103000e00da0703940c843d03c4030f031030b1503e411001c40450300040040d00421a801401040345441400440c01400c000c54201c0444e0410500400071995408848014400c2c1841007101003440030502c20b5021009441d00000c0d566285459001003000310100004949814408900148150b00c0308121000d00d050f9800c106500c00d0040e07a4400c40b1500480e040e5000004645940359514054000c1f001d1100d40c004072025001c02d4000103420240c0303050b0024440c1800c01074060030410f244c6070010500d44021402c0e04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 159617374 1250 159616124 159616133
    0x50c120c21010b060f130e090d11070e070801090e010b0a0302090a1d030403150b030c01181203120f15061b020d0515070e0f09450604 59
    0x41001c0e1100c4a048060642441c942500390492441c00000400440d0782e0300682400d100941c1004964102c0119129400316210310708060860184100e900140603070119640d046580e50303209015078009014003013002032200000d07807880c0d001d014580c90300149981891a9501100c141d07044031a81030781843e1246142da100d4110382015250191840c0d00980e88400c4400e010703020301074031014245580900c020304010084003a0098912a120011042421340da00c8401e84808a00f4641c1c99004401c0c018100e6000f6020308120201c6450300305001662402c903440004146032041c2e001c206d00909040f151030040c452850b28410150b004c0090580000d298041c007009030180c4024486404074010440034880451545207600034081040e02006140854962180d4200080b20b01403450104800034015118901d0011000c1c105020414200f400c020a03040007824401c111500446a00092941180001d040086084c1000d00b03600c01a02d00d17481a1020203e415815000b41c0140300008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 159618624 1250 159617374 159617389
    0x30809010b01051e2a0706021b0d0c08030703051306050307080a05060103090f110301051803090108070c02030f1c030911040207020f0307032004020304020f12010209040603050c120c 80
    0x48060071012110304010310200b02903c05c0300d9411510000759141001045140b090001200070f40b4000d0340d64803a5070b00400c2c3d90302d2106140d4144164400a040e410a0810000341d0160701e00603070442080a41e6540290301b903920502d4250300040d0001410800008036800c048020002c0b8504580b031071078100c84c010300c0035038003030910b80c40c5030303200c10100e074071603201c1d8005003510360f0098502d01c41810a03113007220340c1018031601d89019500f41000a54510407000741421005d50500c0074600e071600041c01101c0c5c41000a000b1000d0220178140304002d40c5041008404c0146008010300394100c041410010148114007103004241c00d24005c1c0300040c48500811600c50425140948c41d5800d030720024020b1452102c9040e054814181300000b40100c200381d409841c985000c80455003000b1805100591000b142d02035003100103080950900e09002601c884c049141c03a0005003007519020000b010341303c251303100f5103040d400f074000140075142c14101d40d038583c1c1d103080092481d100c10300b001c65000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 159619874 1250 159618624 159618637
    0x807020606010309170a08090d0509100f0219060504031403070e01260c0a0908121c0b040f2c151801050f24030601140d0f0609030809010b0105 63
    0x403d0b4803102800d0800690380c020004454041442c180c4030710f14804000c040d180104c489401340d10500317540b0008a4007500c1116000764001d0030a1081072401e44040d101c40383c1042c0741208601c02d44d5595602120304411200010344030303d1001c501420171341030007040700c142444e13a480c40150070001c0c072544642142840321036400030301b440703181009110801d142200c0d418264a140700c03010010031425078003100c020702c0182103a4841806107500c8002c01e9945000e200d9080b050200100305c3c0a0765484103403220f46c9481c905250115889c40600c0104054030f45040100104139200ca4003100300e801c8a0b210030200703401d1509010b0709a800542c8036030b0340709400080c8052002190740031440c51031440c01e00008504442d80280a681804482c101c0c100e50110307076000340c9407032450031410b001607600090180c018001300207041c940d00306401504d20806000d8550b90006a81c0100790009114021403e400303406070100080002c00707030901420714000113150751100e91500c11070b85c0c016a00075040e00c01303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 159621124 1250 159619874 159619877
    0x10060336060615110d080f04030509121b0f0d0b0601030207080d02031003030e030a050c09070207030609080301050414090307060203060409061b110c0102031c090c06031407080702060601 82
    0x40c24106414500300602c6150080c00c403050ba011800c005564020f500c443c0c0c5080c1308400c0b1088055061011541100c00355800264545c41a000c600448e01c1007025142d00c5e00d005116581d04141c0e00340c414038080c51140d24041c10344031901d004049180c040d0700300280c1882520300940142082e40c918a900c2002403a8038141a0b020480d41300703100c64039054070300c4400b010302d0440d81d0781400c15049131801c0462108030000f45541b0740d0000e05050120340240c0443d40040107141c40d031910020015060f000810303110071407107402e4000020800c2402880c1481e4014000b965aa504150600c020b68102041c5501030029200070b00603884400030488800301d0300108010b80340e4a40c20000360241c44410f101410300c0e0b00306004912000c221140644210aa41e2206900152441c1030513885640da200b9031805078000303014584640e185006294600c000480000450f801103507501400200141c00040000c1da5030748025032495000c5c00081d03084401e50406682921f007a05009650f0400104450b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 159622374 1250 159621124 159621221
    0x1020a170a06030212150a020a02060f09030d0f1406010c0b01090906090204060b0c06100f0b091f0810080304030b0403110a051903021605010905091e100603 69
    0x40c107208280d40404041c3d54020801854080c5142d03882c0c0d0360301101010310020000550114400c0040c610848001d07284c160090501551046c040c1600b0010007007139803d03180000c024192200030b55110704072603501240030009a101c14081c8a4840c910018070150520800020707220205465094003411200007220115401015161920207001c40ea00000d4010b42400c4011801001040c040d0611b5103042d4201d540d5940c424410100e104000d05c590106182c1d201d40038465606e1050007000c8482c0c0140541c1c0301c20b210044095003441c440345003207001800721000e004030340f11743d104450001c045120007182030904649502c03580d120090300c0202400070806000e940b40c8001c0c002d4410341504402501c080f0310340c01691900c40c00003414100d005001d80804550b2411010103508151601a920075120782e092000707201c00d9901c060040413000140308070b4540c0c00114020410b12816000359030514140ca01140a800c4e02c00342c0c0d1012170427903e604600c409100a5129090b10044c03007640d0707070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 159623624 1250 159622374 159622381
    0x303031109063406090203060622020d0e15011a0f040510030b040f02130b07050c04090305070606030c0e15090403050f0405030a06060314150a1a090a0e0c0301020a17 73
    0x400103030b2101900c82e8401d5520407034140c02d00044d5400a20102d0082d0140c580d1990b90300c0401401c0c100c00140d600d042c0d8031444501c44102e10320744c080d101140300d400d00004c1c0740031864000f5103400e40500c0a4402001c03541c0052007003111414004120740d8080e4261400c051620003069001d005a0181d180189402100b030072139148650030042c0300c05000b5000b040071840c1c40164802a50000c0c03c03201e0151410b04001a659944004903035210303811001030118005c4d01010040605403070310042d003c1007428403071603011511a00c18440110700c01d03581790704090318020540c03102480c000c1103600703018044003020f0072946400c0000f1350b000b6070500c2d011b607884901c0340104206c5e0180b508016094031417024800708204590b408031090300d0244000c40ca80c0301504590554a00d805c0c05800d00c59100d00020680101c1540c02540b40004880e00b1340100c0d0341c00c0004211800d03412240300f55000d440c0e404404520740180f00d09850040300307400a500c4c0104030080644064458031207a2041040035000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 159624874 1250 159623624 159623677
    0x15150f0d081806120a0f0b15032d010b0c060a02040323030f13030c0b041a2107030c1701050604062d02030d0608070e0a0902040e060c04030303110906 66
    0x481380c1100b003500c50700d041170905403a510000e040031390002c25940d2420006007130502c0d20a44004194400c10600c41c0796655281145400305c56610401c030800805603020318500c0c802c40c8000c0e0107008002c1da650b44072140800c1c428549000a0581e000c0c02e44100401d00c0822807100e882c400110300d030712900c0d0300c8440000303241d032441c494103007044234003600407500e07412018003100e01c4011640545000644562030f001100042e100b18452088410007210000480c1144000600f0500042c02d900c00c032240c0410100e440480700440e50140080e643c0d05610b4445c0344c12a4403400311305200c0d1480c2201d581040d003c240c10303116030b0003441d00340030719007000022001d92181124050920f8003003210f00b00d94500c6000c0d41d01e801004510785040d00780840412000c0300000c141044803103605018a207512401c84001c01050703511020303a001502d40c0842c1d00d1070300d02000558011050a9422996103107182001022a2000201d04001c20000c01580080e552482c095420b405882d400b0600070540113030b403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 159626124 1250 159624874 159624877
    0x5010b0d09141618020c06070804080d0f0f0f060609050f060c0a0c0302030d030b0907110a0c06180906120b07020a0b0702100501060305090a1415150f0d081806 70
    0x541c107140328004449005164030b25440003168050000c101c0002c684c81031141c00c0e8018136940a00b164010301c0003544d401d11507458550040c2c020825a80760180780104c030380c05d45043c1075a03454401c0e220b400000344040c41303226000c3d0580d031001c8108240f81c20228000c00a540c03a1099500c5a803011808400c2580c42100303e603441c070424011075185d06500d150210000115200580c0300c0c0c003d020180840500038065405450303c010002041c0e40e80701d641c1900c98010524404501d4428902c4a90000d40440d601d04e01a0501f5190b4001c05440001d00c1c1c80751000ca5004540410705103170003000902031034000c52051950208a80242ea23481c085c1c1286406090f201c003a140035449014020b40c15000b0030340700c0340807101d0036003070085a8843c00d0036026100c4c282c902e42da44e688800241c0740410200d81c0385c1c0c2448840f1005841010080d0320203c01c488000303440d12600302c0d03041d68112886180424442c41031850540e42050004101d07100c003c030a029501034116030a0880d0f5200e80f0985d503810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 159627374 1250 159626124 159626153
    0x10e0a091d070f08010b19030803040f200f04090f0803060f0901090e010506011e08071101020703271212021c0302030711061315060305070303080403030f05010b0d09 73
    0x101201c2c1e4850351084400e18002d1030384214403065191042191942c1040b551a0f92400d482d120326035142441d41d910580036610040064818010a0070410006503070640360320f900b00050303505200c61811500810500d0031008403c54801d40c41c000c1924001b0703c544120200781c40c1c0102015450356920070218914040c001469980040c007080042030030f6000340e20130380c41611000001c000c40d9030b8020040d11070000304070300f0924807517469680541840c03013080d044d80d0111182c5002c006080d9500506826a045103400700c012680030310700444207c5400da0020040c00c1d4001042d24100d2604005a951401009000c0c00080c02900132025880c0200103100d0701c00101d544035010308890fa10010000c3d00160341083c00640b0a02503044500000281940160740700355840d02e0321412503880713510b2014058007146000d5243c800c004003103202401500300030341c0291a4030906250078034000b02100d01c00c0100d44540c03850b010060100c01042800c0e10780c940306038100041c0083c02420000c6c00031b04101c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 159628624 1250 159627374 159627431
    0x20d140309070b07030507030806061819081f0e06070905120106030507120209071403060d020d0203060901020a09060503040305040b0a030212010f06020d080f07230706060e06010e0a09 81
    0x6421403c046d0312400804041d800303642d9804c80ea480780e004004c09445101c000c0c01d1668080d00c4d9418040c40c0030342c1400b005003100000c049600340d894102c141000110601fa0440740340b81d000c144146003440c003440c20030145030b20150100c1c2c90003010107440340086000b031901601c410003210214510035072200e80917640001c221203c0e240e60344000940041800d0b030403402010104046115507028084412a03080f2013201c0030306666680c001e200d0b41c2003c509041c0c0e8403049180340b4002581b403d0040c9800f030003e550008d41c1c4c2d00d140d0a4090711501c026400403003045010030410020a80c4a400c0e5400d596510f0802d507aa03403418401240a40034802d0000b4050411340000110555004241d0044039825006e968000c00c4059090780c01000841d007494000c41a50001090984138107074080301744084e1000d5800040c0d0003003003048160030450f0b0880d207696030345605000e65074012000c40d900c001d0900c0c00078000040400850a00041c3c0c1c4240180251158801080100c25448412040703241 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 159629874 1250 159628624 159628627
    0x509031f02090414040b010608090c1f0f09030b0c03100e100501020601150e040b0d080a02010b0901050a080a0b27060f06040b0303030f1330020d140309070b 69
    0x31822800035440000750354807882c81d080000d0070001c10100d11030b100c0c03508480302142036883d0040076074003004004c000b0241e50060081a2003990346c0c0d09480c00803041c0002d0a0882d80480302030140803501940a0f900c20b001803c0350400010b0562803e155118032000c0c0c080c2e4807600c8010100c04610f05a4024103002ca40701810030004e0a540801407003200c00c00d034219003c50b660341043d48813260000c098500094010700c0b210140b42015001035109110281041e018041c0c0d54845281c0b9070050148400142d450f035081c3d180340c0c90035100c4030340500011906406000d282610081e40c03002d0b103036401070030352450800003541000c42808500300c4034400d03800c54104e000c085810715101c51041b00d0068080c10080b01244003400c00703104881d841080503004518603218501003a1840340001e00c005a6101c0a41a400014000c11018086070003441e1100c0e086140302c0000103202031a014141e004c40d441408041079180c0c0c040040407442c44e8400315103540751250006a81020601d42044025800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 159631124 1250 159629874 159629923
    0xe0105060d1a100503063c030c1908060901050c19140409060303020f0a0503071506090603150e010e07090b0105160804061b050d030c0e040501170c030a020907050903 73
    0x10884011481486c0032035580c0c01500c0c4148141242550201821302c9800b0082003000304205181107208513801c008003101c24400e4200000303034034400c41e10128100c403009400c0802240d02c1c100100d07130b002144070009100038a03100c0840320039400341c2c094908001c1e65040400c404103000b8162054150424250203507580d4450240c100074140c1e920048005105122280c4210b0002107032411010303510a0107186170140319100c52100201007a0703100600395035808006080d00d01032203201c0045101e001a41c5c41004c0c0c4603040c42c00c4510202c004981641048806461078001258507002e036041c640000031104c80210040360325014a030a00c4070031101e11114401800850000303041120056961581200310403462a040780400d1500200260300c00103103150141c0c02a0000000c8950600d0920101c40000740081c094620a92002150629075000c030460300c2c6003030048440030181600181922401d55000c10801c0c03c1c000e0100040010110b4801c08641d0140081203a01484240c5d5290411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 159632374 1250 159631124 159631127
    0xc1401060e100f08032a010c02100b0907140f0403080304050105090d0504030510020a0302090618031b060f2a010506010e0109031212021306020a0b010e0105060d1a10 73
    0x100c00e80d50120062484a00001c0241802e8010415905280059403c081240304c02d6400040c0412030f1b41440b107503101c842c2d40d11850134440d00d0b0154400c2e900410031040409444c10854443c03014032409121040200120682c004c0c40d0500b007190880582962100c194514540c1805503401c01042000008107100034000150030030303801101180203903112414522801c1d00c99209901c0001d096401c981d9013600720401d5a8003600c00e0b20054100546060700040003c0c02e5580080422200060300300385c0115142010440c00003440404000111b0040c40a4000f0f2114042c1041c81e42010200141001c0c619402c0200340203110b100303400c0d95820051000c0303494041c08049502c2d500151101c10740304510341c820301800e4101c0382c2001c50240c0361542410300301c03040e00011100d203c805808004044000d0388401d42240106440d5000d003648862901e86980d0b0310030103078000e0100d411010300502180d52220101c903041100140000b451035000c8a1066015001c3c1518550010070700c1d09007507030b25 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 159633624 1250 159632374 159632399
    0xc0201020c04150f0f06210b0a0902130506160f02030a020d0f1a040b070c0512040602011a0d020619030f110705060a0501210305120709050a1203050a0c140106 70
    0x4503c0c803040004030917120341c901d1620080c103104010000d0820054502072105141d442000c2100c881e10100311208198046201055185e01c010001c03503000648064076000103103d070b00585021100546081010b014000281d03911100160000f000004804110f5804000c85812a41e018042c01115040b905020107602c1c10a032040da081800400f40c3d02c26801da0b5441184102d601104060054440300b600310303081c061112080314181b2a40c034a401500e000c2401505c000c12959001040c081e00407040d203a0010301c0002e10364040c14081081a0060350b442c2c1c15035118070110904c0309000252280308801502e809928088503503d02003224008114540c002c0c8842400b031400c540d06034856039003030805c0390001d1041e1161800200c0c224940c043c40e00e910210003d01070700d01907080010442000c4800742007540c3d4003005c207244101c204414103000a03c14014004075035000742c464459103028125108a10180081080f6402c040041040503000070294205400c003c000c42e42d191009030580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 159634874 1250 159633624 159633629
    0x20307061808101407050306011d010c050604050601090605061c021c0219081f0608070c0c120c0b0f0a05030a0e01020304060507140a140702030f0a0b100e01050f010c0201020c0415 79
    0x280c1c40440001c5c0d80c0c54040c0702200e0060384180e40f0754005d06a040001a011418103158504120440c0c440d04007042041004600035806030014010552500a0850454940340e02c1a0701500092210400c4400008606c61010384e14800c05070341c3d040300600081e00035080f50b0f0b0030110140f02050a9021405140e440c82d80700e4196141c02c075031034403500030b2201c504108040902c2282c410b0f01d020b0103103902c903080d16604100e0341e052a00c8015200c0e5550202c006982e00110300c0c0c44031185501050080c002d01c0b003c020700180c0480761a1444c1201d4000ca144035400c041400e02000001203201e203202c59004500c140c5051000b15202e042ca881c0c40005402d044d500301001590707806070742c2081c12a420840d440921a510340141c1c245400101141e207800c0300605a0307250145c3c00043c000740c44103204501d5094407035001d4010703518140c00d00b444040d08030f400000c40403007503400500c801e40318010f0380c415500007400c2c003c10810070b070302c0102d2901c100007030450f40142c11f02c603000c2c2020301307141d054405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 159636124 1250 159634874 159634901
    0xa03050609060601091412070b0408010f050f09071707270c0509011b0c050d080a1e0806060c010906020a0207090b0f1c08090402040312030b0a0302030706180810 71
    0x2260f2110001128800514010349826a13050352044003240b038400d002d00702210601080d0341155513100ca8076031694020781d000c3d24491f5150310042e199000c4902c100e80c2e100c40300100403040e030305080078103da4410b024001e4140d040550450301100c00c004100c0c1c0c00c010000c0c015224103104800c106980c910382080d94440c00d00e820035087c803c90341d000340144c1e0310182e41a5125070241241e007c03100f010241345001074514a40d403101c08101611a082c00400b09402840345030742d100200071008269408c800300c4200b10301120f00c5084a040c0d407101101c4d4000004172200e64a07840d01803030030390052580b00300052500307100250241e6041d401003403180844005903410007500000d071061106440c0300c54603943d408603106e040c22108102c6032492a1344103014a00c40d03814103240310081000c0f80c0c066003084d904c0100c0c00e11a0030000340d050042251030002038a440004d1440c1d507010980d42c1015001d0b000a11000140c201071540b440000c02340140040303011a02c00184569041d001131113200100b41c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 159637374 1250 159636124 159636133
    0x110d151506110a150b0f0a09021201120b01052b060605190f0e070908060c04091b080a020d1401030b0a060b04060f050a050d0c0806090a0902010c020f0409020a03050609 74
    0xc445000c041001e800141c0c001d1559038400c01da129913400200f0f1106102e40e80040840c41c2071002e502c0d01003281d4003605c46248016030700d01003e50303d040c000905078000301d0031071850394101001520100001e41143da040d14041d90300702050b141d03074913000021401440940c111004013801d1100c87e802a03004c65a0590716001c1c000c0725410365080301101ca005200086031450300810112a03043c007925400940761070900c040644859045003011400d46680e0000300000c03a00b4400c245440c4248501504542089181921014800751084000610700442c095000c103260311401c00f180c01c218000d00710551044120741e1245081d145081c0c05481100c0e827280f4150011412105a0041760151120b075205c040c204807030b003503084400758022400c0c2400c210061143ca035440380c1d2030041c2048100c407900d5004c07803480c001043c0300155000070711065080c2c1c20495003c0242c2d81000000c7c40c07c540543c0e00003004010640400d010300031380d04009400031180382002091107008207603240520fa001003540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 159638624 1250 159637374 159637397
    0x6091212020c030403170405031c120209100c031e021c0203030f0f070903080c0f0d02070b0f0304050a0b01080f0c030606090f0a0b0405011e050904110d151506 70
    0x120b014044466a5980c020841400401c1c843c0c01502ca0900c0030364031044c605500d401c00710341005a0140104400c1c1c0d40402586286a003080d030740700c10803101e04411400c00c4103290000d0880304281c0302041c2400500c408007424944a0120741244e00890080003945a0407400000c2d9284015130703510300700f10003e4a100400c0c91000c0200ca00528414120035525103402401c490305100141c00c400500c1281d0100000141000000c0c00e581d100000140807030006661409060047e00c140c3c00e005c44d000444140103041410080e902900001580303103407030782c2e10b61414500d810b0a0b104090181e0070900c000107140200003c05c43c44194580080d14807049504060560347c0e0029920b03161310400a000080101c1111580c1c44d1b4000a014004a900d8080750041f40440c0c0e002c0c0c204102c000e41d10208001d1005580c10000d00070142603c00e240146898bc49000031200c404446501c503801301141c0500340601196800980d9003214420030101c085d1002e54205141c0e644220b102261400312803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 159639874 1250 159638624 159638657
    0x10e0d020f250b0a1b061e110301090c1b050303010f0f0302010e011115040308060a080601080316080705010c050d060504090b060621100602070f08120f0403060912 72
    0x12000300b511502c002460b06818901c94103030382d400c401e0780c00040003641282034110180c40031240d24a0750091a001629a09820106120103c910310484c0a00e0901c6007049515507030104580c1140c1d8100c400140b180e413000412220104520881d9054899001c10b4034184800840118101c031010303105410b56070359500032144440203510010707010803441000b40da0194000c080b0301e00c5100d60346c0c0a86103604103224190341c0000c410303101035001070a05000c104040c202600710502600205d070051843e903242c004034a0f56841805050788a8030f2082c00600208021038003668002d40c1c0c000000c0c0950303110000014007981040525010103400e24000044a08042c804e11341056001581003030240e80e800c040c0507207a808030f00c0d24403411025000746501c00c011411400c1c0199074500e8840d08042c5003020081c9410440c2d000b0303d00d603140c2042d042100c0d1000040c801070404003801c00c16120aa00d600c510300300e000b40d43c0081c00707007070508052000b000701d00001c4914080f04c0381c80392030b00710504803903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 159641124 1250 159639874 159639913
    0x4060e070305071809020a0e030f0a140304030c05060904110409050603150403050a1d060a020c040b100c0b071803064109030403060212010603180305030406020a02010e0d020f 77
    0x44e800d101e01c00842e000d0000448a07002802620300600700001c1002035000883e00d03040300703e00c113604140c2044940800f003003802e0407441c9400750040011350400c1d04588440310441c19a110300c9100724000078445a40b07441e160000c0b6101079900b0181500c1e1996500301c4d1000d000c04840380780c481e0003410391221080c0003402d0f0041c010b540543e501420a8001c0344140e80c0c9034076200100c00003000b841c101e07007116540c07400140304c111fa283d400341c0445a040020700c001d541c044010300b48a01801b90020f084140c0c000421000d0b04e0708481c503100c1688502005860260540002115829a240000c0140111a08414121a01e920f01304c802c42494036507840d00804159010b1b07080031090300000c80400b8200803c130307411901c88420340345407540d660741c1c0c08200d92041040d01c0640c00030000401c10140c061050500c0703c21007d591140039001d0780c2c1d004216210040000b4032480e0b021400c9400c03030703100b58003000340320314098200c401c1001e000f14040e46d98807504100788901d2003180000c805840d00283c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 159642374 1250 159641124 159641147
    0x2150c0901031a060c0c0910050d030c0809090f0117010b0303160206090907030b0315010b030c1b060403030e0d03020f070f050328030507080907031101050904060e07030507 76
    0x4429905215414004501420b20501403055401c0c0c5030590303401590b6100001e2108495203001095584215000d000014000400c040515400c88034100416101c0454601d8100d62501c0d0450040e8050300d071150150007020322240d0440341c030004100f00724130b600340c8880c10fa0f880b00c600940d84034241420b1030300781ca120701d5100c0d80680003030203c1400048505c01c1040820b10061209050401d00300100380e20400403100c28001940f108080c440702d003014080c080340c42c081c2d04103060040d0b04190194246100240040e06c145600040b103130441780c88960721101d031803404400c0d41d080e07040c5030800401038030507062086841d0054040600300c581c001c2c07003102c40b03085402c03c200c1d003060116103860700e0f041c1c5e0a1406403241d0008020202c1160382119075406a852810543c070b59030b0500100050880e0700007000082480400c07818070a101200241c508104c0354402801017000b43c0c0200102d03000e00404658070741150038444041944071000340c0051007190340782d4040040b640c4916084415a4080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 159643624 1250 159642374 159642391
    0x30e030903070308131a0a1e020303060609040207061427060a020c0705060703090801050c03060108130c08010218041503020d1124030a0f0b0307050607050f0114070215 74
    0x4030b1040000481c10300c040c00e0310308001e46100440940c0d0343d4103205401c81d4010141c0064100050000400e900200020300000002c0400559030380f108201940d01e10004c0d200c91b02c2440301195140107a925501110100c40d4064400c1c003024884070907464561009450f01b0420300c01058225401e8007090302034030a014508402001142c560210050082d07000410180081c0607154022405446000c014a4010710036920800c03024074040f0a1821200090051080340324208180805c60ba4414a0150030042a40c829040c0000381d01e00031001c48001da010444550011034140e0741d40120b102034451246080d03c00b400491044280130340b0035001ea0100940c4809803075020400710340b48481d04280c0d400050220b0741d001c0000c064003503401c20214808200581c0000802010310210302410421700c00c80c003428407140d0040300009882d0501c07401098022400824030f1070178008100040302e69021124020010b185014002c01c504100444000000d80300d010f00500d50b04809112452003000e95 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 159644874 1250 159643624 159643633
    0x40b03120403110d05060112051b0f060a03060f06090f0b03040f080c15040b01080f12091e06070f210903110d0c09051b04030206040308160c06080403030e030903 71
    0xa40c0e45035030203d0154401141c000920f180b000c1c00040c0c0810199002e405685001c1400603d54505030f071506225403603000d0586007107540201c07140c0302c0b00303203000c0042c80844010351184c910181c101c0c028000daa01c28460a904070000103540c0350001d00750811780b030892545515181d280d100c28501d51005580c02010340702070b0600e00003ca03440c00041d00c2500111000c0c6c620f14801103415180f5039906682c01c2d11600c000f00010003881c2d80800000030710006a4010380788010252054441a00030002b9050280c0b0039038141034640c52001600c030072441e0004103179940307a05107414149a545c00d60041110062000f01e018000312811034038800c6508215640c0080d650704654405d456010345001ca190403200c6000a440040d540f0320b00f000280c40301643c00940e0b032034003050861100d01c4544100d0340d060001c110620168032004c1c100c0f81035940004030b13103640e002058102c407000c15040030702410703003000c41802146c40b0754400e60f1580184d000b1f035801e0146c1d40c4e1164456485e8071a8005460340342c0e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 159646124 1250 159644874 159644879
    0x1020f15010b031e0c03160f0e060c010e0f150c04030b0c090a08030a020d0f0f090314030f0a020312011a0d0b04020d020c01060312030c05040e04050309120c040b031204 74
    0xb0418010b5901694600504040a090300855600003509440c0c2d00e035628808000c0000c18507011280c0c0300700c441245421a10400a441e01610425003050002d02550b400500d941e42c0c14002d40080300c4a2200b9021285d1140704000840e0b16002d403204209107109404010030b8604180300c0540b41a07a80107400440031b81c44100300180e86034040201070350482c011810000d02154144050102c0c5086500589074844114030010444000c0000c401c0c00e22408038802c800c0c1c59070000c410000d0303a0380b101e1038466220400015524500a940140800000028401d072401ea40480508403128110b0000384e1140d880342c4810300031b40c65003a07030a1a841c0b401e010b032901c00c2c4c40c07542141c005201c0c0544014506940075417a071080ea0310982c26a03e240c0c1d1106010004c10604441f06c0f2000e141905e42003100310038591001780a4480ca04c649041840500d02003024040107000b02c50000c8030041450b040c45020340c0c0c0035911076031840b0006e44503914184070301d505414080342150807808041003040c5003a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 159647374 1250 159646124 159646139
    0x7290a0209040f050c031504020a12020306030a08040602071403010b0d020910090f0905100b0d1202030d1407450801020315030d02030a09050d0201052701020f1501 72
    0x400080107982d00c26107a00400c2500400f921466016a09080030b0990324a8100e100300d610700b40e0039805030302843c81004495882c0b584001e009800000203140541c3c1ca0325a500040c1c0380901d10440644200c10000f0002021a00040c00000300d82424240311751500c04c68040600725181d0811050300300008003c0c490040c540706607142d601030b248460400200b0740b500150001c889480303101601840d510010b131701c180202003000c403042e40d020403820311400300c0c07050100d1100902902c00900442a81d03084000a900a000751610821410003c0104502c0709100b0030030703580d0545803040822000d0314503204040c21091011f000170302c0c0f40d11004251221906034501802515002c525182242c90003140178003007800103601800e6964042d00c0b0300e01400b4101820702251280b04c101750f5104000c810707055500f184881084030b00407100002d2010440c001610f0b20b2068003084840c1054a94411642c09546002a078000d4000e07800c98045096550074a5138600c4210461051040c0a0b0300400000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 159648624 1250 159647374 159647377
    0x11060f070f030906021315021216020904080c01020304210c05070605030603010605270c03010f030b040206071a040c0f0b030f130f0c03060f0507050a03090c170307290a02 75
    0xe100700001481c0845030201b08980d8101c80d00000c1c21454614001300c0b9142d41003198400000380e02014a291100781c1810b42641044140002c0c000d0f140940018248038041c4c0c181d507040c00144009640c2e0b0b180c0b078a0803881c1550301d1a00540e0340c0d864021495440b44c070a0701c02e81c0a20b070b4414007d108040c107004080c0c0c0e03145c10040106a0540d2521004169a01c5480c4942c0c5003000360040f10095003a076070021282c2150061040d20601010f100402040518240303d5040700d4014580f100d4649036400811828403d51201524030110340c50304001c202c01140e840c030302c25401503400c40d44031500c039078110f6091031141c0310325103d405092001c15102c007103441c1c6075a0001d040b000074500c090001ea0301d0209084002c030042e41e207040b110794104103003c164000d1360790840d0030700010032003841e12810140c1903029078036501c0201039458a41c2d10400c40d04440701c10240c140f4410f519100000e46100540da03500040742103503009441100c0e107455007081d0054003003242c2c654168681c1d564072580302c071009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 159649874 1250 159648624 159648641
    0xb190c0903110d212319050a0309060e0607020705060906071407032405090a080301060c0201180906061106310b0a0b0102160b0d09081911060f070f03 66
    0x5954440300c841d00c0a40400403440f03d161a1284503421105c0d1030152855064004101c43d4000c0812802e000440c01c2d1074130003580c001900b0100c0d02c03001313021012402401d201c00024110b030325142d44c5800f9040009091440350b05140e08903035030030b901c680c140030342070049114454102100340300781d8000540008101c030074110500c0031558000c1d5261980c8961400344200740d9580d5004200c0d040d841542400386650014151008064a540650b0b50108602c41446140c0c10001004440d404580c030400e400c11604409041849003d52500300d2400100003521411002c24504000c441d685d12021070702521407060b100c0b0414003114500ae00b00f04a928900c240050041c0035010341000070058001240240710035032000a00e01d898400282c0b62240001035107a03800b0110340d007088101001c20890384d14603004500801c0a041c0d51034100d005000d0703018041c4180b038100b01d0105440b0340c007102040c181656002100c91680310f8000c0000c402109598200019000720070900d4241e001ba00f11188 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 159651124 1250 159649874 159649883
    0x140a0209060c0a030e09090c150d09060c05031f0506040303200307050a151b0e03010b0603010311041118040507120e070602010c03020901021b01020a0b190c0903110d 73
    0x14007402c840080303052284201c070440c0801c448044004484c1004581d10380d000300c080c001494000d140c1d000194080140420044140c88000b40c0c80c1d402d5034030f075007018040d503520007824451703008117080250098104844604500004c10070800c401d040900030007040360000790101745890b096441c00c03544a0010080c8090151100c51101d0321040100014130340703240200040c01c6180403a1a010002c00e1040d901d14410a040804588100d044254000d42840150808040003605000801c0c090100711041550008001c400001400031602c241311904004131400c0003104201c020540c401d020b80d160600c03403035800c040094400d0806600c4070f40c0107401810701d8086940c10900d000265a6109a1040290400c600c100001502400340e044110074a003000d50600f048000000d680e10400009044025054440c42c5000d90017444a610f015401c201c40e1982c81c64001d0740e800b503c95441c410b41d03210721721340b40c880c020603807144103240c090700c2d40180c000d401c100688041002d004804e0300b0944 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 159652374 1250 159651124 159651127
    0xc0c050d0501060e01090f050c03070f030c02070b0d0e100e070909030306150507060506091501050715060e0106090e01060e01080a1b0c0c09111909080706090e060301140a020906 78
    0x10401e203c00b81c40360080001186c08500b0342d010b01141003c0e180003403c82d160b0400180244214581c00c8582c0c458141480d00e4001501704110008900c0c0c40000d901241130b400c00042c00c014020140d030001d803040940281100e84120b0030f00a9901215610700c681411900211001e02401d5403e412841480c2c1c003d2901107103150301c52000900001d803c00c081c0000c140c2c0000d5039801c022450003480c0e8007130002c5647d80301a150140d10a240e80020001c41c5040101c002200420407510403025075003000036010801c203068a07401e00000ca21000e00813540861b051407000204090240c030480d060b0342c1995103c8498102e0a00191550040035101c0c10f00d46896125080812060007680c0092165176071342c0010011150034aa8403029454210f00d03029802e003407400c88400b80700c00807121306252490000d802c0100c10b500450303603401a600403025134056a100002e1079a8001040070503034010400d407020540303070501050b00302c1d0010f0f854051511050000030b1442c807001d50227002200720280415 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 159653624 1250 159652374 159652379
    0x150905010212071b02090109180605040311071e050d1103160906090e030f0f040e09030d0e010216170702130f05010512030306040506010c150603120c0c050d050106 72
    0x1401c0ea041428414006510202046035560340710074540401d410a4006034018100c1d034020544d814014001d100185445901c0d800c0070a41444404442c0c503040031040000307081900c0c00519001c2115018200e03032081c107201095030b00c40140300d042c5000011100102040c07408090101080c001d070801c1d070300c8015101190a03251400d0241c0e600114020504031500c50a00001d175084400c141c22101201d440e102100703920704d0000044600034040389807015140c403e291000f0006120769000314190b249450b0600a40c800c0c004058610f03d200070405200f680354520400c0e00300c0c082e44a404181d0407840c048213000c0355039000c0070161501440421454082c581d0085144000350640740340c1401c0d5669800103000076680728150240101b210500031400760000d002d9980e0002a100b41d100d207640e81e0201381079038002c96042000d10307030142c120301d90a000c4d0082131005110520040c2c6000380300f8100c403080280304101412440da0300240710644581000309010b1845e0210004984030341d640c0202 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 159654874 1250 159653624 159653633
    0x9042904180609141e0721050708030a02011802030c010e0a1e050a080c03070b0f12281b08041109010b2d090409020a2d0e060d1509 58
    0x203c198a60064004409440e84500321300d10b0a0706201000480c07550741c0100c5010503c0100f2100101c0d0300140c21503400c0010308114107030b000000d020050592040c0c01c0005070549020029000120554000f04418000500c42c0c50040466240007981604105440d0081d5806507030b6018020b440600383d2a42c0d1038031104514003103c5068410a02c40f88004420801803409410030409000714101504121100c0008260307101b919010b44c400d5480c0c041401c8404105c190155414210780310302285540c202040604541916200005032280001d0100c074000115401380b06802101c5136103031036000d064031500300c54004002e842102ca16100d0411520a82d0702c3c40b00c200d010300400c2c40c50580e04e602c20281141d002000050f03c1d40300d9512514005940d00018041d100030480548022034941440d10000300110754941110403082c1145000c801c4548600002d483d003c03035010310750164180c54140f00c0e01c080204031007403079004904011034000a04d2842c01448000c4400402007464802550b6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 159656124 1250 159654874 159654881
    0x807030e0607031406120607050703030b0d032006060303030a0f0207050706020c1206060108010501030c020c032a04020c0a02010f1b0503190503070c080a020a17090429041806 77
    0xd1070800240c0303c2c8940c07060302c03001141d62a04407500b06d07a00180000601549a21010020b011a003400800700b944d50505000350450070109030010301411040d805842c01030015010341401080b9041c0d8858007002c180000948280102030080c000c0d421030703a8200c082c3c0060030940703c04110250f0240030010001c0c204010f01000352400340c0141a0188079030044c400440d024a030a40303490349c0080107000a99800040860540310203107004140c20b40000c4090745070000880c10f242e003510610842c0e00c020185220041c071500515400b9485000c00b041c1000705900078041d02c00e4483e006131030603000660091034803000070740c020b04002920b11005850341001d4203010300203459a1300001402d59034003649110260450403542095030850821001c000d042e000d4842000301070000008100a03241d0082054880d9141d120114048541500ca2200401c0d041410003030300603030402050804c130306600b55408010401c000e1304200c020410740d00308005000070750050590400d507010b142020458900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 159657374 1250 159656124 159656131
    0x203311518060e0c1005040303090302090414030c0a020406090603030e1905090103050a1209031a0a1d100501050d030c1e02040207050105071403070507080c120c06041101030612030807030e06 84
    0x24043c0801d860003404040c40c0042130017400c00504203c18000030b60400b05c00c0d019a901a100c034181a0365500e481498241c00440a04552001164092484c1400228000e50030300c26a41030050540e05d84c2a42c2c1a142e82d80130003404603500322001002c03410100d007207007442a045640e1500f52680c0d4408618200c10a07001a5000d030481038040060000b00010303846c418446190819189240d5250305549000381c584c682460618180810011119500142c0200c1c2c24041c18620b1b24010030b5103543d8501c0c031038102540050414000046c60b01d011146000c085030141ca4050161450b40c0d00c0c00f1820410414101d41d2130000b603610030160f00c552000c2c2181c2441a00005058101060050b00d141c00540703181c00e07420700420400c20025800021f5556942d070060000b602d90f450002220b040a00300007541d54480e00103c1c2c0007203040700024400d13010794044c52003003d0100b81d400045040c0c4055000720700c200762840740f100700084d1240b0b8074150b0000f03091030001015910703901036605100094 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 159658624 1250 159657374 159657401
    0x90807020d03050a110a080d0911040614010207080105090303060d08040f0f031509050309060c070b13030b010602010204300b0a0b1c0f060c12020331151806 69
    0x8619042d00b2508003070000d1002c40024006c0072000b04a90302e60845100b080354410155443d0f03241e21042050304000804031840040007070118a44a03c1441801d00120041c0b5006126104001030040010310a4500a00941000e03510350344e100c0c0140b0101d030521940485038040100310000d036401d07403d40c5d2140600100b46011aa83d45541010041008419510403000b440d144030580000d100100b16104c1d281d054903044c0d01c84d25908401307810300096074840e905900380092180c4418400f0600c082c16a44107080c207807500d0741c80c0c41d012403c07402140a0000d6400d1504504801c2c20915502c00003200f40408a1800e1800c0070750302d9080340f01003a0340c880d143c1c0707807543e00c403009a1501040b400300cad01d02c0700071828442840d02c1d100c020300d000c118403014000039603d21174207407420b00c101101b800c108041c0a0a6550b4103000b40d11b2240368413101e00a03203040300030f4100c18100030340e401c00b0451100e4010744600310008901641c03070010200c2d218020413840721200b80400080c01c9008000411808 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 159659874 1250 159658624 159658627
    0xf03010608042901050111120c030306270402010327150b01140d020a05040e040f050105010b210601030b0409060510050109030512090301111b0d080118090807020d0305 74
    0x1903e0b0064034003902c501c4980f81d10740e5181d514815069a442c4640c11a002480c040310b10940c049001350806010101c2c04201810007d03596407407100002c01580904003c1d1040c2c04844040c5505c01e080e89284c04943d080f0100800200380958801d42003014400e446489082045850340003901e02900c0da00320842ea00c0d02800d0b907032119100c291040c51500e01d4203080101c03408084010301e0244c2d00c03030010840d044550110764580c0441c812400d41300584080481c5152a06041c101050a002119002c944540c02c10b0004115100750782c043d249441000e5805400301c1c2103820030700c4804040205414100355850306000030300d03074030341c09170810321070284400261905000d000030025000d80d410040c14025000d20410020300002032001e112802a003c00c5e0321002c079440000d01510620f07003031840c0b40d9000b0070090002e440803d103c0000149600c11149045540706090316403000910034008210f21401c0c0303044020340c10390811903046106403c03075480c022041d4000b520b4180070b0300d01239000030320 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 159661124 1250 159659874 159659881
    0x6030c0a180f050903041e0308030c13141f031b030c03180206070f06140a052208090111031306200109020d081b060a0506180621030f03010608 63
    0x35200e15181c04900b0b10041c801c600d00300e01c04036540d12651041b85418581e818604140662504c3d060000e1903124444917035900b0300109040c0320750403003440d2001c0241c58440001d040c0820800030781e15002c026080308503414a40749180808000b40c84481c0c249900c417845c120f03032180440302000160a4039103000a0300e0303910040080403a00d84020440b0034500c045110030251f0344160540f84090750003140b01030303480390a02e446009408555a01c56540f8805400d100d03050605410552080140c00e0310400d4840c248014441140b29001018041400c10440240346510031110b501d01d101e46c00040364900f644c041c04120002003694803400001c0c1c0031040c00d8469005114112000340d01042c020b006142c13154000501c5130784490760040c81802c00040f001d00c2c05080e1040703500303d000000155040ca02e041c0c54503d024020071104a81b04094070602e401e04c080074820ba00740030340f40107000940c0702201140410035100b56100c9588480c441844401c1665134104c0c015806006169141826802c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 159662374 1250 159661124 159661169
    0x10e0109050f0d020c0f06030712020307120e030702091b0906210601050f031f03020d06090506070320030406020909010602011517030901140c010e0109110a0602060106030506030c0a 80
    0x969441c4102150400c070645c00b12a82c880d08900c120f1801140c01ca5035941750300c44181c90044d461356000d200f0500100420a541d90425010540304136801018015810140e0303800f45c40388501c80000358028101000300d06058581c2825018131804115030a141610b041300041c029003047c040b080c0f032035160049902022944801003500b0000a00b0000d0030450422138180407404010060400d2044400d500c0041e8481170400e5030045401a10044030030b111410064090464a0420784580c4101e00104031032034403901c960303105c0140481c21100c440c054948820b0050b4000391040c1c41440d000d010040d8035589044807203008050a400010741041503034414881d0300c21301e51001100c0e07122138807182501d200100c00c5610300c0e0300034a0201c031203422141506440340214142000301d50310703001c0f400203401c81c1540102070aa000d00c104480c02d190180030810911118040d5100581184004100d224081c0d00150713000a0000e0584d680740d00d81901207031104d41181d11805c0b0580004003450340303a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 159663624 1250 159662374 159662383
    0xb0d0804090b060a0203180a0b03070c0506070e030c04051306050c0409061e05040b210102091906021906061e26060114030a0506070f180602070302060c010e0109050f 73
    0x2c07820340c1d0b05401d2501c1118069100d0040c90400c440300b800810072140b2039a60306811101030100a0346560302c904000d24002c00f2955843c4044541e8454140443c0301c0c107005114950250324014014008076080100303100103080b0203441000c40b19001c103061000036500d801039034403601141d5041900c0f1803a000b2a0007c0d0b803681d0307101003140b1040c0302c41d01e503110022004045c19200c060b100480c2c8034600c200480c5100c2075020700b64584c0402002140d104800640041c004040c0c1111800c2c4452198819030321003007030030701c41e490150b808500c003006803110b001c0106894034007900d0005402039613a040240c40303418411311011003443c43c44060201e0740c0c8210213620001641c0c140d07070140d00c01c03186102d031b03840e4011b0107054240b034045043c1c5605aa800c104800c8400e500a013134a000342440b800181c80b1003000c0e400321006c90008580c1640b030005103403460044031001ea0090841d24559028403a1030351140d5030b05003180d5240c441c24008600c0c240180e20307405100310010841140c04000c0c030b03800c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 159664874 1250 159663624 159663641
    0x302070203070e0f0a090809040e01020301051e09041103100608030306090f040507030305090f0a03111002031e0306040209040905060406110f120901061215110c030a0e01030b0d080409 81
    0x244080410302c15100c0300305102e1680450305d440c00245180c45030070040c0039070003241000c40d8014204090914000019005503040716021b5800300b206103000e040c01048103840840e0b05403c80000000980465002140095008800743c01d581d0111560458230307055075800e400a410a13480042401111705080c0c1090354081040d080100081c1020741d030701500c40030184000323010130a010800008a94801481c0301d6905001002d0b0258281d83e45805421000304400c180d10a4440c3c8410400090011007203640028090644c1c581400d29180d040074160400b803c0c25811603401d020081081d141c5214054080b40078500620062a05252110640c0e40c800340100382d000060100c2c0044829040540303404501d40922111107903600782c01c0034010030b403a42c00940040e003244070560a0181401211a1043c0010001d018000c0a040303402510f01c262420b4680f254007c11054034894422411541c0e00b010500d40030681000d4080060001044500c041c0c0350f1110000d001c0000c403250f0f02c2045903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 159666124 1250 159664874 159664889
    0xd0908100605010e01030e030405040608010506030607050c0601170309040c03150f120206030a110a39020906180907060e040603050d14090402070b04020112061a0a09080706030207020307 82
    0x701d6424031000034078603031603920701e581456101c08440d100b91034140262409040d0203041003002c10341c0d83c04458003070041914200c1c040c2c024040801c405d103101d4011075050414060003484a6480e001030040c1c00580210301c45441d00007880242015501d41c028100004200d40c0c020445220742003c401e00e4000ca640040c01809000350200046c6d101440908079083d0101c0d241502c0395690850040907026256208600940000307580c400603801c0942c075000345011140e9190104582201a800c203c024109981c01c0c20300340c01090010300d0011500759000c00301511800380d000c803003c0040e4010105640c135070f405400461060000c40e500c99480082da1360300302d07814415140340da03d65540311007000034080c0c10401001b0640c01c24541da641140c5007208060001c65546030641040107540b03a06942c12400100360342502402422540280070a603002e012045124080703000c07138074259501c00e0490b03a0502c4104000028480003d0068000601098502507503801c3c491042500b85030303440e0042007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 159667374 1250 159666124 159666131
    0x1050708010e07050924040f0f08031c0213090e0f1b01030e12130e06030309031506030c09010803070c0807150e1804031d0d03050904020d09050d090810 67
    0x3188040410009821002909183c1d0b84c1d61700000c04188841404034103210407070300c810020b11029403490018800c07180804529103442c1e4950300e6200e5482014450000c040c2e0050283d101040d0702035000402c038a00c1000010b10b403d0808402d4002444d440d17010900c1c04d5079407480320042250500c64488085100b102030840d117000340361400d0030000c00c2d1034503904056a032038400120400c10000c5440800d68a1060360302c501496459260001150040814140b4a800419100c5c1030020aaa00d01d01008000d0910700780c2c800300720020054002c16169052050744c0c013418080d100d055070706000e0000f490141d0b5607482d09040231081c55115030b00010b06580304980070004444200140c5468081b9450840000402e1f0380020f241a00424001d0340004c48003000d100c101070300300244c000c682041d1420003844c0a028000c00982c0015a8800381c0801c4c0304002071a40d80ca4281d0003080111807800000540c60b00d00d44135586400750045040c800f04400d6281805400005c004500c00e0301c1d6428002d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 159668624 1250 159667374 159667379
    0x90c03011b08041205070b04080a0e0a12020108040204060510030506031e0a0305030703110406030b01020f010b180406060b0318010e061510141909080c151b01020f03090105070801 79
    0x10403821004101624101010b80c110001310302c184101c41003242c0110244004d03042c80c0c2003040b050360001d146900400c4081180102c2400c104503544102c40c400d102104105800c2c0d001903c4258006000302d034041d80c0c400c0c1c00b003003c1d9101e000d81200792903a940c00240d28034003101414941919101c40000c4055000142c0c0e45002e00042c007203242a6042c508035031203444518041e0040c10f007a05c0301c4d014150740071801040c40b036416404076407040000d03422079920f088203000403800c071880e507100c3d250850b052405220100d09031848060700309201c3c000c001042565000c0500a0344c00c247c817141100358954a20301e02290f030074002c8006450020010345110b0400701c2284900b144507041040c000c1d200d2840c00d140071400f40300100588041421800c0d81c90880e01c20902e01d00480d00c0c58007010030041200070030440c0d400124003204450203031145021104030183d038206a04a40c078010b005810408480b005903000f03001802d192034040d4452038517428814801400c0d031b00001d003c8420412000f004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 159669874 1250 159668624 159668627
    0x30303061703161109150913120f020f010609020714030c060a0e0f0f10061406040603090f0c030308060a06020102071208070c0203070806010602010e030c07031712090c03011b 77
    0x125440f00491940e20700c455071441ca00600402d0180341142e03400406041007040355404411069140b100c205c2c1d10007002c2e5600b01001ca1a82007810020344000c906810090f04a4010340864517190100d00498100010b001e002601f51102908800d0016802142d480200001039100340c5400c28008080c44c00c00c41c1080d01c00e50740750002488211116110740c2080050b010520075201011040801c2e2041c0c200317141034007a0341c0c40c4032a158080d000c0c82c2c0f540c0000c070903090003d105c260340301c000c01c1ca510b00380c81c0c00402c8000c0c200c0203100781c41c80c5122818260000f001c40003c180158401c0e107900501e1316102c0104003100020b68442c9055900400c0a14002031b0501c440000c0758589040c056001d072180041100c00281403040290548500320020401c40000181c0741c1c12120698000c0c001d141200c42680c1d100c1c0038004000360281c1c4501d80500003c1c440681490340c444298540f1409d149103201c01860061064407020400e07040754403a010181020301509031885040c0700020712022051070b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 159671124 1250 159669874 159669877
    0x50103180519060207021e0f03010204120f0206040b18100302091311040f090e101103131a130506091f0b1f0908010c080c0316020a02030313030303061703 68
    0x40042d0392015050001041002960545a0581d00541461130f40c41c6801042c4038141140c44040d8800c038424240452507140c14004c80e4140c03101c45070b1000c5999800d90b508a41c0c8040d902041b64040c0b0180000300342c02d0391140c00380049089000343c0c0d81c10928654244005401880142c0c4101070041100b0301c62a01d8124001201042c0407100244049050003021194040d07034110300f80040300414005480c2c4800e401414083e031880d07056501036403003500903104076440301c16004c61099051001400150103040f10a002c7c0340101c1b42d520401000003451500b010080300e14041c0c80426000400502004011040d80401440020460410084004100710300ca443c3c292000e1625001246001e850706900060b9181e024400b10124603010034000d004038440e8042e09940d50300c2e0840240383c0900c203e001e51300a080074184185143c444980d442c0208003901c038980150300c07542c3c841500589080009001d000ca403008240003d42c11450020141c0750541d01111050034042c0300d68151540100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 159672374 1250 159671124 159671143
    0x60406060f05030a1104081b041505060f040f060801030506091204050607051f0e1615030c030905120a0f03050c0a180902030415060909030e0f0a0f08070501031805 72
    0x30a0754491340c8144030360b0040d0034500e46502d074070b4601150004007a0000103d1500d5407a1128601c0315403501039046c00f00301c2d49000c12255550103204403c101c18245800100340400014613000c0c0342945071410011244002c0d4000d0001921080041050280901c41540c01ca00035002078050000304800c0b014090096006107840b685000594604000341001213020415000d82601c84401111404c00d000b000c50f030b20101402d0003518400c0440d45040444030050381c000b0409600e8100b0049022801814603030003040c01d241d6036402079804075408000a100b40c0c8582d00c00715654582c0010010112041d09812800b410b0902091041c02a002015118030744941e24002c6000102082401c18021071948180803080c030000c00c1c0001d1024902031351404071031105052007210f5664079a04125080040301800043e00c10000f00e08602e02040002004000104240902a10341049000d04613171903004031010350040000700029600350048650002c0300f44185e1192304c0241d110300c0c0d01c035240c84 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 159673624 1250 159672374 159672377
    0xa08010e0a02070c0905150102030c030301120f06021902010b030d0203120403021f02040302010f1b0209070e03030c070816050604180207060c030209032e05090309090915060406060f 80
    0x10001291220264151800c3c550021a641050b65490b40d000b070080005884c0882501c0481e08034141d2540000b013254105010030000b14a540c0c0ba0011800402c0003103081182d0304101840703000003081060015000c00f0f44140e2018000540e4050080d084561300e80c00355001c0d82116042e541b01a0f00401641ca03c20030140c0c0750542a80c541c501203041107594508a080c4051095176844001030560141040c0e038400c2e225501d01420460050f20051400b0656034182d143e860300d03400041c10224407a5400c11280d04000c154070118100180c21500000c0620844d0b52103c1070821240208008202005103160f0300f44446508000100c1ea080c0303c3c40c0110340c0c002e010300b44481034143c02c903411101150b030042400c01003103080d0240180650f02c240d94070361003842050810600b101c4400358113040840c2c65030300c1031300c654008262503011f04401046100701c2d010a01c14200651070340f02e2654400e040f14000b6005d0301c48800141c200350440900958003d42c5001001d100c1550415041300c6800c015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 159674874 1250 159673624 159673649
    0x10f0f0b0d0905060c0c010f0204180c09091109040605100804330504200a060e0a17030307110f0d1103070f0803060111030c0d0311040f030302030a0f02030a0801 71
    0x454548070180c00124002415441013104101e4600d1403500075141c89910349000f0300c10149801c46882c280d001d81d0045100c45080c088e070510b040c0d10035500051802006091424885030b0790318510040f186440101c13408120001184a50b5141510411010b00300c1224540062000100c008083c00d0f40103100030710860f203d004403400d0581a1103a07405111040c11095204800c42ca01c02000e0a01500d049903039041c1c0866a1030890310700580c450610300c000e007221a20700d00c1e2080c115484a02d2801c1d1356082000c0c1180030a000758407030014114004050003c540e00c0c10482002400b45400014800c03142e0000103141d8845e04001c035080000542c1441d116140c00c050070145030461107810350090050941c4d914003c10000c011015510428017600d981c1d400007803041c00162a44030300d4040800c5508420349030f8140301d0180d03000c0291071103c6250b0742d003401e03103800407683d94500c1c5400c20717070141c0d0012031002042030307124034602014002840030f9410f0880c186e001400b003d0042c0141504c2010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 159676124 1250 159674874 159674887
    0x501180314100504050a0320060606030a11070c0e090a03090302040c260402120712140f030d060302040507030b0607020405040302190309050a0902040308190c2108010f0f0b 76
    0x10000314261070a203140030822400d0505d4050340d40c0d4842c207130031000300345e00c01506050058220110500c442030306000e040350f9030780c1c0010094035501c010118000300d640c94002c42c2141e280d500c054148280f05d50007045a4070b06284c408010002c000b40070501d554001d034400b10000b5800031583c022254140d80104414252a4095034078032518004403140c4100c4c02c003e200110090903002d40114000c0e5002210200f8501c81c071030726441c0d03070f0113841c0c050816402d81e80e00040e070f24800c0d0100c1020000a550088030040c6901e42035034030000142104c01e03120399050007907240038440c1c1ca1300030502d400c082100e8155980807a082c0e024444010b0710440d43e950020b0185030007886100101074000c5681c2c103e0090500d0060041e80003070084034051013031902d0205a4201074400c65059071740082c42e46084c00300f280c00a641003040901c0206c20408140302840c001240f20101c5d03d08090207000c1d2480580388030a0050078140143c1c800e107059600c50408202419502c290041030ba01200c29140d500d20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 159677374 1250 159676124 159676163
    0xb092b11010603020409030e040c0503060319020d0206070b010603050601020102090a1701090b0a020c19111504050a0b030105120703020f1003021c0c080c04060f050919081605011803 80
    0xc2e06500c0607402a062600340c1e01019404026a4000c6000301c1d0f0401003910201c408a0f024003048407503540543c45403940380d08203034000700d02c02d43d41031005111810045041e0b02150198108003002c80b000b040403001480303a02e40500036698043e0080c8021410200381d0070005038903009910618507076000201c00c040b4140320039003082907415008030380482d10781000340350280207500c603840200c030350300a0155078207030410450300110a4a8007ca54001e0203e180d4003008005441501c0e0164000703010000026152950b041d010020115201c0150b184c0d031504041c000c0e611a04008807a554100c0401807005070b40e0700790581c0d1584001d0f64030380041e000d1001c0c250001e20a0100c50007881c0701b200003200c00e44445403c040809440c0b581c1d50900d03921100040400f0380903074011107011800f802c0f10010107911501c05000002401040209aa0180140342c1c0002d0700e507030444a0603070400e48030f004910a1170850703180201401e01e00924442c0005909100d00c0311103000090161030b0351000300c915038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 159678624 1250 159677374 159677381
    0xa0f0921200d050d090e01051e13050702070f12030801090c09172103090613080d23060a03030206010504020705010207210e090c070209070306080a0b092b1101 70
    0x24400544200d9680d030b090f050855075110b00e1603490001590100e804680040702034091412601c000d00350510752802e556080305050754001c2555040010f210f455a6640901d014441c080c07038298014000817800c0c0041c142d45a43e20740c211500344e01c16031802400107584454100e0441e5030500d80058040000b080032204800c0b43d41c050840c165800c0c104144088c0d011076071902ca411489042d0703401018410b0212064002190300780c0d41504040005240481017041c2e465140d4400c42c091480c01468610395000c03140c00b80c441c050020280a188070b0300943c84036990360000c42c1100d11801c0e0b0703803a607a0000d5a410b01401400d00032900880c9450401c0025016104010340c01100e246c200a5404210b00c0d510b940505d81400003003200c4240203d5041c03142e00725000d0500b112317041c2e00d005030039003c4c00314946001e00140209075803828000741071a828803806142500c52000c281050400d001018500344c40782013064000008003104100414640d101001400003505000d00524621040035004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 159679874 1250 159678624 159678683
    0x6051b0408030c0105130c030605040f021c0201030c1407110307090c08091006030b15190f051906021903020106091409011422060906020a0f0921 64
    0x158502080104a1a60200c05040d1a000e207400030020381c0da5a40c550b42c100f070782d42c2c1c0e00607085050462042c000304000b900295401406445241c4101180750301140200480c42c046083d402c0e107180c11a821581d050290701d504004526140d04204040b44101c0300520620000400704003540c09040c1030364a007800401c0c000d10801004000c89007601001919800003220010407074082c00141d40c40003032031441640d0959030000303801551750355901000d5640a1030001b8140d403000756202d070003204513a00645d160141640c0307680c0031159841c050500c60072440d60305960680a00c0c2e01c0e4180105540080d80001510001083ca240302c941c50605900400950b08145010f03800e020401305012605241c0d40d0184464100030402c414000d84640781c034403026160000e03c124000301d4665542003901d100b0340e0450040d038000400220981c0c952003241e02c007441d503001040d2040000d80d00756800862070402042c014803070425050b0340300c110034041114410700400f40b10603541c3e032410010001e41803101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 159681124 1250 159679874 159679921
    0xf1306090204051608101505030901020c0f07050103151818080d09031214150a050406030606030209010f0602120a0302190c02041d0703062004030609020f04020a08040605 75
    0x510b080850100042130500310b0300c0c0000c41e104001089001c0c0010f1600c404850000e00c42c00b8549801010441d250b900c00f80243d00c0d6503400f0300604500d840c00f4480d104c00640004e00520803186000300140680310105850882602103e4007048500a01c4d820a96172110b603078000038039121920900c10952600c1c05018010000c08280004108001e910070002c29000f42c442401a913380001d000c141c81010075a55801c006090201c0c100402840503000206c20061541000f00c2d116004541100c00d01d07801511900c0e01c800d000c0080d81060f1100f54090182e42d48454461800c002010750b65401030515000760600c00142a40500c1c03080d4140c1d00c02e88000e80c000d4400024030319000f03185544507002a441549001c00c03c0007040980c145e003100c4005d240f8042c003241861900e5035001084031072844c04100710806034025040c1113490080018510809000401b9401ca0043c0b00e0305400281a00740039510400102c3d00058011003007070380c043d03800500031540c0d80e900603c13903195901f9401c0855 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 159682374 1250 159681124 159681131
    0x190306180209090a0209010507030818010e010b1c020d0809010509060f071202070812070503070606230609010507060f0915020702090a060506300109060612050f1306090204 76
    0x660340159001050701c0d4200b100c03500019120096008200e100c0c4204090100d04100041c20019026a4003a603015441c140610001c40714403403001d0a48600d00003c8465035511504805285080f81d48240700300c0c05003080d440164001d60114507200e038510320252607458046030706583d5a201d141201d6a800b070242c4029210400c0c689844059040088100c3e007255001102d01c0c1c1c82407000445200301c5800400030400501100b80c210103684c464201a925400108421000700751107003d003400401c003c016000c0d40705034460314030840f11000000184602030400005200740e0f84107095559158202c4000208a14003c5480005100078000101001800a07408060412660180190900a40300c01c40965a152860030481e00d05001e2b03d680040184031818803c40d444e02c450003000301140601200000c203d07000170315000c00340d010400094480900780013680e03100701c4078000b10075486000c0c4050b0801280e40140084010b08400300150140200024084540c014001982d000342080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 159683624 1250 159682374 159682409
    0x1e020a05070c0b1201060813050d0309051b0f0112180309240f030507051603020606040e0102030f01090b03190b0712020a09050609240306120715050a090b0309010603061a06190306 79
    0x74000d4942c464cc140c1e02805601c4e9080207114407254080d803001c070001d200c1d510104c4480c2c019903201d10b1521070032243c40da4072048180e405141540004403103009441d42030456150030b261074090003885880c101e80340702c00c0f2000b5005a4100300c1549a00c42c00c1d0401040c113035101c0c1022240da009204403168002603c501140078581c020a880b4002c641c25138040c000150101d5201c0e007030f44015504244c03920842d40040146000d50360007070f44500c200a0988250006140c1d403198908545071041d40c10350b42c20740602502d65040260a804c20b26105400d40c1030001d0160042c02044407442064000c01000440d20210303900c1009148421078182800c9208402d01c812155954104803005801282000c0017041512000603001c1c04440100303001c2903200c0d03904035086860f900010100c60070f000d100000407504404da00040e62084004100000301d591550411406403080c3c0458004044d2410740e015400c0c1d242c12003220300c3d83d0f4050007030b03140382d1902c85021002000d0707a078803032031020314180f011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 159684874 1250 159683624 159683627
    0x409170307090e01090e03030406110c06151003060e060111070b0d1508120a05090303070f0303090c0501080603030a1d030601060c061104050d061e020a05070c0b1201060813050d 78
    0x40d809035401401c140103d40e0304c0d2901c0c403007181c09602c0c84c04010341c402d000280c0001c4064100a5034030080e440c04500b00a1250101c0749400400e031550040740a91003510f8885052020740484041110325082c42014078000360540c10032000fa207814104078440c500201e0b900070802c80300d00240300c40c0103040d1f5038012505a010040100229120410411450002d580c0c0d038001042c400c9201203184192401e09046410b490507400074091507003602090003e14041203110100c00c400c0c50081e240804c2c0e4030214903040e2521507054120070306009858040c061552400030030b449a41c0c070281081c0f005515080511244040c0c14012164140720300c070004144036504c4003090701f80c02e100b01c0013480b03a80b0203880c98250500403405180e4200f07334541c0a80c00410f0319038010074454440000c2110038440e03a040d502c0d0682e07000c03026a50114100041040c10011020026070080c02000036060034070302c01d000c01c41d0500b181846400e04000001003c1000d8031040049292141e912000301c803800c01d000c250 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 159686124 1250 159684874 159684887
    0x503040603060f0905010f26120901080a060807060c050f0109081e1c02090d05010c030e0d0905060306212409010506010e04110d020f070b060d0807020409170307 71
    0x181d40d43d0300f6210700d80052070644900800341a2404d40030b036900341c64202080c4201104442c8040c6148540750b5040310800c40381848850100400020810340d2103a0000000d03000c400f01800b01072042e868031104000b01840440d117031040d510140b83c50080c0c10110b05109107080000341e2040029441e1401d02000c01141000a000d802c03100c0100c00d0381b4442035440768925029805840e031042072040445141c04a1640c002e160103540181550031461080d120942100d1181c01070202003513030f5900b1240103020070014030881880d5441c00b010f40c00c3c20301d00441d00c68080070740350074041e00d208070016040740c043c48046020182e80344119107180382c11105078008074420b84000c00d40c01301e400b0013041c1040418081c0500c1468103840b001c071486640810b000040450001c9000c1d038903401c2c4484d0303034101920b0000700340710060303507007215110040e9040841a40c007026000c02d02c503810820804001440843c10b80b18181e4040700c0000b000d42007420310100c0122424100100c0c2e510010402480b01c0d041017 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 159687374 1250 159686124 159686129
    0x1110f0309010315080d0f12051006020c0a050a030b040804050619080f011202120c03190203150f0406050907030204020304030c030206010f08030717210403020c0f100318050304060306 81
    0xc2c0c1c00d01c004c0c0c505204655040c400c1e03000e00b00e255000780c4032200100b4040d801e00340803800c00380b500300c110041e28034070341f41116170646808086608a0500f001410f48c100486192000202d528001d85858540000c3c000c20980c44018040c4413a50005428003140100f45c800500d030250a00da5980601165444851158220300c008110390344003041c43e2405205019061340e01c1505607503d500959000c018141807074072011074a51242200b400e0b01920306104040c0f4445180c0f1315080002254410542007415034000a07a1544808040020b000c07051020f0b10340040d000320f030000c1d940e10f4401c2441c1c04c04545400103034001e40000203010400d540481d40c0f11582c0d000b5030070341e05140d03201d060441c040d055a01c119481c0b139000340704c4000822043c022178420300588051103840c080c02030407108409180c000510880c034152000700b000b81901844800d00ca00b03c03c60703c1c0582000d88100090b21850341400c003800f0181e603a204403108005201e240a030117131b00002203d4949546001c014054001170 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 159688624 1250 159687374 159687377
    0x3010e011809030c11030c100203040612140112140102070b010e090a110402130509010906030b0906131e0209160e0603161103070c06050901030e030a0e060901110f030901 75
    0x120803644091400c2c41241626640342d03580d42e01d00102511440103450345841541d500d40030b0b4104042d01c65503041900301141020fa00035541b140d1400301c0180034000310031002d90065040a60164040e01c10700c2c0340354103403a4581d45900800302203081c601503d65140076a030030507600c001810381c1403000150065040380d401c5d80200c0072a640705c11040f51203803490100140100070410900c00703141b1706074000d000c94030140c0c0074945100b030341c42d07001500c0c0c4030303081e8000641c03141d0700d00c02072082c026040242a03014860300028a080e08118940300011408070101a040086500c004840751070501c90104020b5001003651801c0c0c01e044080b01c00d031071810303490b08000c20340f200c11030805818020140c0384190006804c2d048801ca440d103094a2440b5040b104401030301041080c94000f4000549002c068840f99541c25280c4141130009011202e01903440c0035541d0060000b00e11003940907030b11b00c21115050740c0c4242c86006d03141c0165a1040040442d9425003d81140c0c1c0d94460320001c007804003000d09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 159689874 1250 159688624 159688649
    0x705030c06160f020706030203060609040603140d0906080609100902071a090a110609150a020102071e0f060b0f120610090b150a0203091c020a090218120106050603010e01 75
    0x84003d0390700341000301c10302000d0b8010800822400b0b0090340550741c080e502a1480d4940318084000030125412030b04211001d44140c1040005104100400c004541042c10b0004e6100d043c04c3e0b002d04030309401403c1c039104228042c000341c1c403e194401602c00814500c0001c0d511600b5914105103000003005090106030000c4001a034091000100e5241c15a0400b001550f1500703807030148041580940e00da90742040c41308000445241c405e900910f03410400d6800180c44141626040c0d0740c4503245094120b40e40d16441444020481d10500421482c0c5c1c804000a0a071809102003034450b450450001c0c4c0c4011165140c05059201069052041502018403550380d5114108142110f030748070072150700303d1041140038511400e14001480e01c143c040c01186d041c02010342c000741c40c0c160010b1504038a460070f100e120f000c5040004400f809402102400d604000481c0084e90798010484031301d9210740c4094030440d075100001e610082c041c101c0544042e55968440070f04600500c028403407a00b09240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 159691124 1250 159689874 159689911
    0x304020427060b030102040b040b0415080f0a020d090203030313031b080f16060603060614040e060619050405010312020d02010207020d0602091903050c1201060305060103021002030705030c06 84
    0x8520341606140c001e64a01c001114020752150760081000c0c02205070159030130000400c00e80302c03803406040280019880181d50b1820f06000b84082c1307542c01c0f0118240081c40050101ca0038027001039560001110b0401600c90b0403841c01d8402400c161503010350180000414130040603070080214400c2400707902c035055501c080c41c0b01054002c0d904000031303100803000d100042e0300c804190004c01c4000c800c4010310081c0e5560342c0341d001c2290100d034012110302c1c0e41c400041080110b0040d00754a4030004a0301040300c00f94031082141c481c070b001890603101e4804a50548240d84800d00c01c0c1d0301a02020788200310300c0d81c591408080e41c01c1441c80b54009032082010002015105008842c4820b501600010340241d2070b40d280c038041e400002003039038840e0f50400c02c0301018618600c000c1c01507003d04000d1070516109018403003d0106085d12502a9050140034800f14000040850440354150388203000300040386002c030b0560140d070343d0041c9540800160b040b1004c40004806025041030030f86040880c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 159692374 1250 159691124 159691151
    0x30206160207080606061b011a04060e28110c06070315080706030c09050607030201050109111e21040318090204210c080d020a060605060a080c0a02012003040204 71
    0x46511510f0032550100b00014040c0c1018000303041e81c5070000f00d002c44000030008402d0700b07488040141c80c0045c44003013008040c501d05406404d0007010010700018031404d01500606400304060929410030703020200301e21817002a51700c20b607480204001e502e9100c09541e100d094a03181c054070300300d0006c0e080404514150b503040321002d003229a84801072500c0c40c034005041e0087c0031904407040503c007001c1070005493b12140000c100840c400d03800010340e50704080c03200040340d074880043d28a807101404480807441c00c030322114004455846150392119104520b10030b1712004c690364482c51070110020300c0304264000c00c40f0506504c2030080012510f440d641c0003000c81c0902d100d0b00b580380d0340040c4c090300300302d8510843c0c034901c40c090b854801c88940ca90111794034007200c0c1141180145c0c0b02006070302c2400110310030400a00701c2100d0240c82e00350b20400042202002070800c0300300e580005090084c45000358840180c1c0301040f034460ba406514480c11002c503800458041c0d00031410302c4000c90300c09 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 159693624 1250 159692374 159692383
    0x20093a05060c090d03110a0b01030b09070f050102030403060f200c01050f070c03030e0f0102040b120a021608360102010c17010b070317090105040302070609052d0901030302061602 79
    0x40014100480a00641e03c080302c11450a2401b005a4001c00c280388000c90000d0707030728134041c3d4060b0440e8500c5040102010389042c100764840c9404500307001c1c041c04544e03030110466045a4024002141031307849021004002d00802030908280c40d03220119444144004014106902d49100200315942c1d90080c8207101303640c211241d10020306d48165180c0000e01a0303002013100d802400480da064104c05c1852805ca0b40076400400c9005400705a407131346682030382c0300c060b23100780380e0041036040661032011942038800c4140010b080c040c020030846003d03514a000920a02003d840045021030f83d19040080081504100c1b8015407c0c40e03440203601340540b401281580348003e020305c0720703840c01800311072941103240220b00704102c524440a03260200310902c0e000d82c041c040009018100341c50080d00c0c2c5560b42d4048000d0045524080080b40c3c0e0b0592032a40c1c8141700c1c242c070781400c01c030003101b4101015a8092240d00840d5540040309240c1c2c002a04c3e807040c94100803081c5819001082642c1e80d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 159694874 1250 159693624 159693637
    0x30501060509070201021c090305090306040303050901060b0c030406080702031c06050103050c070507060509120303100e1f0902090d0206070615080708030304020d03170c03090120093a05060c 84
    0x51151f0460340c500300000a6100c02041d82c00791a0081c1040c0a01d00000c0c1000000e6500340e000986950a00101c2c1c032080c4a010002c10150410515146180000c0398403401144070359401d10080c400020142ca00034401ca0350540f260200c040b2410401162880081006020b002d0000c2c3c07511000a406e00c07000700c100c800f490f8100f0001d004040c50600212603550181d0501c1e900060001502d2503480410805917009920011111425074104064682d038001e0003400d4407418401c90007284101c0d0b0a4000d01c1056481f03141003d81e4400741d00d4003080840c910708030020340000e0700150040034840c0550000c2c03040d04444070340000182c0c0c0d82e4045583c58405014460681e007080000c500140b5000c0d108144c058881d0402c035103c41007019692017240d504980e0a0f284100000c1040b1031800c2c01e104130079900381c3c0302c1043c0e041766103410210a842c2c0940010140610309031a0052402e06404034100140005c82ca0704411151013603c0e424071000400d0000c40301881f4202c049030305446010142e641 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 159696124 1250 159694874 159694897
    0x1091706100e040203150703060b1c050c030402011e02030714030a0305070f090b0d0912110d030212060d0341070f02010c0813060e12070f090f0e0703050106050907020102 75
    0x145008006d52044107080080c2c0710070300b4035a64aa002401c20550000740c404903007014160015001040b9090b01915002802e00b06480c03400c10170480140e1300402440840003401550280642124105074591703ca540801303801820502e4444030f4a14002004020014803a9005d2110303445148040e150207200300e200002007400c1242c28400181c41802420344040c900300045200c02c041d4440c011000c0d002144080007d00e11031032008a082e0400c05020000e0040c5000c42c5008036500e4200310900010b080c151082d440f6905410a0512a4141c0c8401a591000324011b03107803282081380594501540103906840e41c00303540c50721070740302c0c10540310056040101080740c00c2d260b82c01194903c00300141203652000610039070b402c0400e030115202c00b515003a200c585501000d0403c00c00f2050310010003006da9802802c003404840c4001c2d40b000101c0345007440100f800302d5000e2490020b01559000407a0509c00d4900c008103001c01500728404543e4140c51303c1005803103403c0100d09034454101d1010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 159697374 1250 159696124 159696133
    0x8221d18160b0f0f04080f06150a0510020f0607080118060f050108100f0f1406031303050c01020c0f060609090d0e10170a0b040518061501091706100e040203 69
    0x1c1032801d005001110f9510070251800c000703140035135034681064001c100d00c0c1d4000328058a050108001040e08005004a008420255a000100c0302c0c00c090007001c0c0a5054140101c0e0054000c000b01d00c07103813404209803991880c1042000748150070921901444100c1c219582c0d599010b54031030f01e400c1d40e50100c4100040b500f090b0040d135800c50301030a5010028900f0788006000c01c100031a01c0d0182c0b4000091945a91800054094003464500c0241c0b05440c1003050240d20b9001429101000e58541042d948411104840a0090080750f200003c50300a07a10400044031700411921310600d0122951401911040c58482e6129135542204000c00e02c641002c4500385000040340803c900c40f45041c000c40e0440c107451303240341d100540b090704410b62204800400c1e450075016541d27000803500802e004113004210f1296031050081d1055070740c0510250365038196481602d40c00094010360034446100c61203191907a9840350200d4034400341c1c0c055480085100080c890b00c090007550005c4c000c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 159698624 1250 159697374 159697379
    0x16060c020d26061c06050105090105060c19031112070203061305070b1e0c030c12090a030b180a0b0702010e0109150c09090c030209030609030708221d1816 68
    0xa00110140490b13a218281c81c0409407541d4602d0326403115a44648000f04180d45400c042c410041010b8004c5d5102d00f000340140d2500920000d100130007101e00c006a003298281c039050669240141c2100f8182e940a0920210602c1388500000d1030010f1080c0c0440740c00d540c0e403201442c0d080c848d40000503c4c54200920411002d02090068008030140319504c1030500a051103401d000c0e8840c9020b40e046420211b24403040038001d200d81110040b0404101c4c0c9000d042c1000103159a50f00c7c0401040049000c020508005201011001030b213003100440b801051302d820607030040f4000700c2c0c0420042d0300b00896100a082e0601079428140c0d8801803440c5802c0f49440044003801d00181c40d0000c1244030040003031a00740718065140c0011745a14010703902d40f4944241401d20100801c1038283e580100400f000140307480c41226200800040c280030342400d42c80200445c2040d036404401420200c15074151840540300e40e41e4007840028080300e2500100d651400d8070790010b05a2035100300300b5103908 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 159699874 1250 159698624 159698687
    0x32090408030c07030e1c030f0c03050912030c06010311130204120809040b041b03060902160f03050403060203010605040e06100e041d150115110d120216060c020d 71
    0x30f0003ea80c424200402c0304000b01000c110019005c0c80407011525000215000b81070304009064920b09540c07406550015440c1c034040c00750310401085500501ca400040c80264a060003030711401f24840041d100903503942d09041519140ca000301920624900e513a608100e55544200c608495100e01c210310f20380c4e00c541322260340e90041d04981c0e40154582c1c0c040011941d079881038100c4c0088154108190000e4484014112105a000384104038410401c44000040845450040d02c2c0d10400d4298403016030b25048809002d15403000346120700200020842c0c503008000b41c810f495482051100b1907480340100304030001191049804100c010f100c10241d810700b41c02042210700013030002040303249880605490300244064030012a00304200600442e00b00c0620350780a204145031204551400b680350075120301145521000703000c41c000c1e12501440b115010f940340b0302c00500c0d082c0140001d0742040340207007031401e070b440700140120408110014003c3c03100010658403c2445882d00702684030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 159701124 1250 159699874 159699877
    0x806010203040e070c1a0906011703070201020a08070c0e07050301090b0f09060405090111040603020702091003051c021002030106020a05160b04170106090504050709060f03120e010932090408030c 86
    0x40c1602c400c0000300ea146c0f03621405030000380c09005000005e00b0258500080034a02e0200c081030b085440d0410800040540e0340002c4045003d500507403080d5541c560382c0340c035250052050380514048242c1c1d408022800b80c104020794100c0c0c152681c05c1c0802a00c100401c144041c001003201d074020040c8000c52118100f40d80f01640c011115800021189014030a00340140c100b603020b0000603800048401c218240036400d42c0d00604010050381010b03083d580c41c107458038030046c0c000c40001391055504a040d4801c100081200701c81d03440c119036070358446400a440c1d251031101503400d481003410341c0196103014003080c4211050005c0b440e06040c18001e480c034a1841c4014801400d648810010541c94454030031280514443c0000740162858182e0010a44545038441e4040d204000c10810100340b0400f88c0031008030040c03510090840d1050010b8440802035082032a40480303c00326004010042107050b044184c59007010b800007920700c0100f004085045034028a001d100b8004184591039100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 159702374 1250 159701124 159701147
    0x20010e03030412110303121f030b070903050d080f0105040207020a0803042402030f09010302091c3f05030415021204020f040b09042307080309010806010203040e07 72
    0x54048488209000040e1464000360450034108803460441d40410069010b42448401c1c1580030314140410070781c40317512800c8000c3c0300210360803008600184400c15100c560000e554490348500060411480c0204840d44501044455202d0111040c10540c05603042c548124501540a070050b03083c0b900307100280d0049042260000b445190208107280207001500c0074105010001c080010121520201407210101c0320b415500304000d4214401e004c5007c5440c584021700700540e5507000c607004240004810a9007142c5100f01d002da030800c015800b8141d0329414084000200d0368541c104003840c0c1c40700c100514000c80c1484504a50b4400d0184000e5540240280e500b4440313901080008805c0e680010b143c5001c90f4415001c000c01c500e4950b0404540b0304064034100403044803007010481c40a40500040d04003400c4010b0982c800421a000c008208400d10036684015070303802c01190340c0c0e0440101c050100d401480020081c1d44008207440031076101d1422880c4548408030140c40504010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 159703624 1250 159702374 159702377
    0xe01050405280f0c0509222007030207270519050403030b0f040e0312040503040b0c0709060603060605070b0a1127030303040201020d030f060504180b0105041b0e1c05060f0105030102072001 83
    0x3000d1036450031805440d0308e840c541c141c1e4852542d441c1246402402c09420b90007100c0010f400c1412622070404824210884c0b144a45000860307449200c0c7c2443d4071020540c18889040c1000f00b00010194550001001c0d0380c4203585c000d8854042c0c20070001920398400178420507500c103000c1e0b00e040300030203100706800a0007034040d603142070b0315604a01482e03803080c0c682c0401d40c0c0c04000108445800c4d440380400400750361074100002814100300621621407071030702824032140c07100410904003150380084d01e03c6031040701d402da5500d170040c000e01d8013291140300c8030700400c0c039007204190030308020041301e1080d54141c0c082e1600f40390041c002e800030010100c1040b081c1d503440c880880e044c1c94038802d101005400c00c2d80307880c03690014604100c07a400140c1205014904000c00079241140b02d406000c404035250070714450559001010034014400110620000c1c8458680d030410700c0300100c0c003130b4051500b509803079840c0c0e0b880d801810300341e10a00500500050700002c0a6000c0400403410300ca008405 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 159704874 1250 159703624 159703631
    0xf0b0307140112330e01120210170a0603050c040b10230406030501031401091205160602070f020a06030903020c0f0f030d020619060e01050405280f0c050922 69
    0xc24094010760b0400901c0c41140a190002d06410704050342800c04c003c20405255492560510036032569008007240000c2c00b480c0781140300700c52180110307850508007a024002140d02d1604400700b40240a4510003560309000d0124000344d203040c140038002d020400500201d150b014503490843d8000c0c481e00c4c80c00c50701490321405010b880c100100900c014030203560045900d50540c10680400c030348141c05e10340d10fa80340c2480f610024403500704240c91070348a0709080752030344003032242c42c1240c07010342c070000b04200c0c80091404100242940e040d0402c60003030311480d0189803034890a41c00c5807400b440190142e0301c005500030301d5103007150300c0451491014011100c00004080440d181290307185030a000341e0044005c02c0b804183e200e00c081c0c00744503015800d018041c83c1c1701904119070010300030103000c1c544500c006483d200e46100000d2500c0c12800b1950360000d400b0700248000c189a0f024144940c0c18801c000d045d051188044d200341e010018084130504011519041c0c50030780381161606100c0c0c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 159706124 1250 159704874 159704891
    0x6010e060c0316030908010b030703060e0c1c05010b0a06050d050a0608060f221713080a0807150b1c1106071112030c1005060301090212010f0b0307140112 68
    0x41c00d00c05072108050f1045100320b03050721032034042c0040c1d405803c420402c0e071601241150a60300000c074402105d4029500080c5281060300b0981070000030140d540e00b054040302000c2e0008522152001d0040c0070304000c21840490030304214013040c0c684541d000140c005d0100410400b801d90010380c1007001040c0c0000c0d965a114441400c00c1021914442c1c0d500254007040820743d2031198400200b901c00b480c078690708180d599a245880c812000e5815001804a032a80115080001c5003004d000840c08a5624401c0e0b45071410041d4469042103500d40c0c0300844000c424074482c001c403d40d600340203146c1500441030b02c03c582140b40724580155640744450400c2d60980c4c030303070000a21500d8000c00d41c5c103100043d0b207801d0005e803041104c0340b05080d80c810048401d58a01c0030800320400701941d44007242903151400028003415212401030742c0011403805200d02001c055101598034030081d0300034015070804400701a2100524414104480d0441c00048442d61050105000c402e0b240100040d0900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 159707374 1250 159706124 159706147
    0x10201060302150c1018080318060f041403040303050d0207230304090608030a0807080903040b21090a0209072304090506090906040c050111011b03020d0f02030f06010e06 75
    0x10302000581d42200015101e150300c04c051081c1c1c121070110260074040c5400480d80082d41000030740c1e0203460a0008004a01c0044195880040c1c0c00307060001c80c0c1513800d2031100c09945040554045412916000300f070301280401200b0303281100c3c1c040d00c689090100c800328010296001100807035070580e09864010041140e17801e5051042d404000440d291820440701404513a4079410610b520b62003404003480c60f0744e000b14990f602c103000b4540800140c54544c682c61071030203160448141e85102107203c501181d1a106d801c00c6003c4201101206034988481e03041d1520502c001c040e410180c44d60005a1441c018183c0c0350007401032008405448601960030070f0160003a40190328002d80700c50910906190014a06810411200240290307040c10fa0ba4544078082c0c0f44102414400141c0a00340f02c1042944608440f03808540403100700001001d00030003e501c10034034885c5052034a802d0f21440d0b50a8426171744075580b02c0380300c0061502c840b40152801c03020070746290340c0080308009144019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 159708624 1250 159707374 159707389
    0xe10050c011b030c030f14060613170a1a0906041e050a0f0506060910031509060e011d070311090c070c08010c0914060307080702010609090c180507050406030b010201060302 76
    0x182c0060380c3c005600340703540314020191a615041082d1245c1002100d50b44d6200740c0000a4100e0340845100f40e407070168907504002c0c0186940601a642420038121181501c0426034a42c0e080c802c2085015802800440070f9241205641480080e40707c0300000300004c20340c95024036143e110300d103100c020341100d642c0c903807500c00d480e00201c980c0803441c2445010010108141070304980100d65240c410303c1c098a0194800d20144800751104480101c80d5400c4c0c00d140e44800d08103074100390180300c41c1d141905498083c000c0003001c3c1009035240c05224900c0900441d0442c1500d80c4a2103002420510b4010011a50700281c0900307070f42841005913000242c50070a0b9100144020000483c10121f000c101130070b5542c840c0c0c8803040d03841118a0a01d100d948100c1125400740e001c1c20030980e95210038404074014900d541040c05a02d10b00300b080b41c18412481d0460084998850740005040c0e00702042000391142039415402046042c8014841540260004100e000061000146003540c0350001240e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 159709874 1250 159708624 159708671
    0x2100207080316060b030d12050703090b0a020c0c0105090d0201140c031b0c0a180510080607090302042304021003090b010605030a0b04110a0c05010209030303040302010e0d0e10050c01 81
    0x11802c000505008004041c002c6100e45d0f08202c01811803030340040c8014046150000c05010b039030795a0000a8199402503014661305604600004042d02d00203a41c240290301c0011000114801d45000032255807140302241c00b0410003500306d004080c2030768010b6514030040202d09100b00401d0004c2c1c0f5410404001078402c51100744540d80c42407140c5c8040c181051000100c040c09044032500610070340070606003040f500007000e40e00007150760b070b80030580b03401301c85ca03801801841c003598041c008266486003c0780c007500d0003120f08008141180c2c2100c1119210020380f902040b40c070b0000500503141c824041c000120340c7d400d01142d05001580e40e0107010100760440404100007105114040d0000c3c0b04007000004183d40801180010a10000090052180407002c000440804031300708102901a1082c80401600301c035182c3c102464007901900c407c000015145c4540c42061660038416192202d10340c001400b180c001c210b41c1c1c45c00715840c0d400110943e1740340d900d40080c050ba50800d40c51a000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 159711124 1250 159709874 159709897
    0x20d020304030e19060512130c090c14040e070e13091b060309151e06080d0e030312070302070606051c05070911031302041e050402042304021002070803 67
    0x5180c1110100140791182ea10f005074111001c04e024800b984e0408202e039848101d0588102a075a03580c41c000d166031a0100000f044c21049150010740c0450b19006684200d466442e041041c0c04002c103845103c0c00750380310b40ca0106c6000c2001c901d46502a4841081d2203902801040e80501c07800c0d000006d4a100700783c100c48003c000c0c00303402514140c007050900648085d18007848810b2054540621609215020b040101c1d0764180202e00640005000c40c0408000349003405420b90f80c140c0d064881c5035400900c00860581c2c076038083c01c0d14000c82124504d1020b04105000d544a259084009402c140c50442d81035070340d1140842c1c5641c03a5100c41242c041c09a81891203a5203c0c0b414900f0554580e124003001c60601080141100c00b440683e030740700070000f00d20300207481c00d80009005040c00035550441a003d1140303820318000c05422481c400d034003e403014030410200b6410300e07000a0798100b2480a940c9050046030040ca01854000c0203900c5601c1110542d640381da2145003990301c400140c0c107 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 159712230 1106 159711124 159711137
    0x6050108090624040608010e0705030307080427092102010507020a02090421050301031101020c0105030a091703070e010914030a141207080405130b060913020d02030403 74
    0x3d0405001001807206a90b2180800d0081044500031007081c003414001103800e040010880e505503511007035942c0350518100b440a810009007800c82c6440201510b816040000c0d401303400040c80c02a215100200007280460002c05070001e440750031b5904280401001540118100c20b8458040e10a0035056490b4908ac001140801130141d410704a02d1061a00c1c1c107a001000c1d605981c440c8041e0790000141c1c078016681c5044900b500387c0003900800010f0303680103050b0081c00300740c0d104004d51800300c0446050045640c0049406400080c03209260080940e8000c900c3c40c0241019210700d0180b05452010903100c4200c54009001c5000150103075060744010450101041007001020391107817090320f404117007940540f145d107200c0c940030000e02034030385640d10551515400041c856440e151080d024080c0d06461403051582c41c036400c0c010418000c6190004500c2517101c1d40da62f4 = true := by decide +kernel

theorem cover : BRFrame.Cov 159532374 159712230 := by
  have h0 := BRFrame.cov_init 159532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 159532374 ≤ n) (h2 : n < 159712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
