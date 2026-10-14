-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3371
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:28:23.078294+00:00
-- url     : https://prove2.me/submissions/d224d123-259c-4ea9-af73-91cacfb14cbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 606115107 ≤ n < 606294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 606116357 1250 606115107 606115117
    0x141905040807032f06030105060f091003020c010b090921130e06010306080a020a171e010515100f200307050708010605060708090f0d02090a29090703050606 69
    0x16182c0100390340001400740244c03542c0010b440103d030182c41da581c880f41503144010080d0f0f1031908a00c007400140b00504000780144643c1d81d80c403890a00b03200260001500c0c0038030410004000030340109003444240b0702401a03003511001103800510078500000101d0795500310210340c42078070400c0d60103d2a6260020102e41060302c090084202c0d080c1c60b20440c07814010250b400c207000901e046e000145515000c5401c1e803440b80d008040c14070981c541000340300d10085822280c0303c03600901d09032078581032850074000810070b0094000319691421101103038400c0c01d043c407081d000e010800d5060240e1603201c110300c07801c0259410081064465961100c030500c4441003000020303c4005000c5050245c0040d180040718501e000034030440361114144203640c056100000e08901e4240400358a61910708100001e001b005098070b0102212500002ca400b07009851800fa0107940351400c90460401da103000310340ca10000c402d141c81c10a40e00201f5004400180300c0c60815a9910102da62a03468a040319 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 606117607 1250 606116357 606116369
    0x170c0d1b03060503070501030504050c120106050307030b01030209061005070b100f03050a120201020c0309010509060f040b0d0e19020d020f221401140d030e040f020a02060714190504 80
    0x1040203100640281031038000d2500c40c2c0320381d003030028040d0b209003c1c6500c550303800320103800b0303015441090102000d0700041c001c0d0155256200441c040d10204000d40c015401085006025490b6005000c10b80002828082c040c140d01140400c0d540e4000044424441c1d1028482049a940500c48540720000e500701007258000504004140714001416258550003083c2081003010354000a170700702d00c40d102403c22590414040080e842d070041c009000c8094010313181501d8030340081c0c407102160f4005d80107240b20880c08580a80113030304030311450301480040f400502400610400d0450107644030003000f03104103040b60b034000031034450407480d040b900d2014000008203001051000420b0701100e0811201600d0f05c0070440403012150041412114925010480408600d052000c000c5da405400d8040c419840e4450815072942d12400c0455081844016100c0042650007814200c01070000d07410000d07280e85071a442d0800108860000280005041e6100203864040d00c1c24022a8010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 606118857 1250 606117607 606117641
    0xc0705060c030f0f070e0f061902070303200309221b0f080f0a0e0f0a150b061c0f11070c0806090a08030c16020418030f170c0d 56
    0xc05001180400039502520780342499a01e10b40d41e440769080e0040084400e40c002842c0c0c110300940078104801c2c0c1e40c11031f5901130202413030b00d011076003508005d0746041e88800041e03000b00300030018194411a11010b0480314a450001c602080411907542e02500711110f108081d50346e0b80648141c160482c1c0c0304001d082c19000e015840b105024071520403580c15119010481c09440407003c0c0d0f01c03483c40548a0f8505002452060f12644c00402c01000c00140c01c8903544110312000c0760b10101001002e60461140b00e01d10303031407510468003c064841888046014440c1480380c1e02440700091400d000321020224001031025940340c00401825140c8107000188074001030420600010120000907a0071000455415803684104940e6500080c900601a04802d001180006001c0c50042c800068401c846481000c10703900001c00300c0303031040385401905a1841c0c04004054110b030024500d8030b007600b0103001c244500304070076071420030040c02c1d0a803035400000c604a040042d0b070f0212410110348040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 606120107 1250 606118857 606118861
    0x80312010b0d06150e0f1912030e090f06042a0309031202070c0e010e040203100b010e06030718150210110706020c060f0a1a040504030c0501330b120c070506 69
    0x6010303444403001780380c000c0138518140a910f04007280112280302d000c5a2944005160a00a406801705074004034200500c04e00381e09041e50b10048642e0013802c40300c0400030f050502c0c8080104071260740c020540780f1107102000035840d001203000309442240a00700031601c3c2070107180171a801030000c0344020b080d03440824000140304541c1010815034082d25007201241e41c8440385000c07402e504444c025456440602c100801008070740000b03401c0541814889002e4001d200019459081201c01c0b00004111200381071b01e000c0c0c1c07080d60500400245804003001c10485400945840720204150000360301d4460141c03101c02000c0488402580000c000c641340c4484d81c142c0b944502040d074001d01e102c2510404680c000c2143d10034020034501306142071841e0103000c01400013411009009906202020340035030045903003800350100c5441c10503825050881214100a503417244070720307650b0a084802000740000a41d80c01290401c140000101840d0307600c07143c400515110f0360030010030384d00034001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 606121357 1250 606120107 606120149
    0x3080f0717090c150405150d110a0c03180302010210020a05091504030b010f05060d0b01051e0901090e1603200c070f0e090c0f0103111909080312010b0d06 68
    0x14a000400c5821213165410341400304184082c1d00070f9005040c0d2200b81165070307080f5207001b1402042c04800080012658030590940103405410050180c8041410b522a0b0360030503034050f107a901480c071000c41c44111035007141c0000796519911030112072f000303070300280115645001d4400e690314044000c0a2443c2c0c41d5104090740100e4106100c00c8421901045c004a002d1540e920700301c06580016102c0703818201c0160901c1c000d4500240104d0600c81c003080403441030082c40c0607031103180384098100d82c0e498161500041c1142d08950004c070804540c0800c0c091060342c503022964100040f40b5010403000c0c00c0840180b8804c51990703055294040c0014061100074010035940119800007101c118941e5940088494200c022541c08040d0341089079503803454a0030441c01451020103240026000c0d1204003481c0c800d50100c001034200440400c028150f81c0c1e0310001000207082d071600910b0030200c64121603041000b060150012840d80031440d2031900107568099401850800d01a41d07016540b46 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 606122607 1250 606121357 606121363
    0x150509090f01110c15070f030b0f030a060e0609010207021c051203010f0906091109010305101a030121021c0510060e0a0501150f080a09020904140f070303080f071709 73
    0x441516000f01da4084413034168085c1c11a200305200d40f14482802c104020440060019841c015441441d641c2c0f942401d403800c001182000c7d215040000704000e007908942e29050000308104150380c0100244801603c2d00c1e486082c1c0340346240507040360800b0a180507810480c0007040c01c042018040000248602d101102c402141c0226404100494803582500c066411021006103122020070190206500c170b6031040c0d42c811040360346d8008194440c0d60315450007d070060980c80300d40c4003100500c04039074440c2403103407058851001d0800c1d8500550205041004d50340c00c4161003000981c2d140c0c2440800e21900c0000a4491401c00c80146ca4080d080d07000541503c000c40118600750000c0742c00b03451000c00c071001404d0703501e0b040000e00c0908811100880001d10417021152242119001a00d880121034021171050208940001280c16240d1802d80c071601c2d41c1d00a584111000c00220b81c00216864201c1580047c0d15429070700d5a00641d10501c8505031520080c00400030003030184404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 606123857 1250 606122607 606122617
    0x1062102040503011b1d0d030f090e0901060305060609071e0509091602010b01111f0e0102040e091501051e0301020909010305010c0f05070b060f0d06050106050901030f150509090f0111 81
    0x2030b840c0c00b00d02118400606000c81c00d42c10038030740c100700c2c07c2c0b083c038001c01d0150a918040300510b262140d80c147d2210380443c8550b40951310092103039110346040c03040003400c0c012554044005d4503a00d6551500c618000d0440d50400340b0002d030040106030b1410100c1c032032402c507518800080c000108500b814081c014055030020101d8005519128800f6043d40c4191400f8105008403402420060078848200084075450b040800006581c0d041070145100d083c00600000d2803d10315504403440c0c41080d0608025481c0c141c0d51000041e0401400380c6d5071403070420982940b28000648030b1000010100b40240b1850f0710f01580f042e4042c00020410030150407000785040720355a100c005085049040e00c00c2d00800200925912021001904a052166a003d8030301c0008121498135866030722103000311070082c0c00017030010b600050340082075601406100003042d901c0c41d041103003c141c0034401100d0041030240394820749000021541c4d251041000c180e400c0c004030020000540c02142d03201050b031107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 606125107 1250 606123857 606123911
    0x82703130e16052a0708060a0f0e030c03040b090d060e060a0b01030e15090a0803090c0f010903050a030f11161406040602120706090c06080703060e0106210204050301 73
    0x3410010603080c42101500d036061101c1c07612400c01c64070821360540200201d8404852842144000140c1090410806004140d2590000303060f0340c0c1032141c482624910381040e03043d03500c10081e51440280020495040315080c80d030171603e4862180000b407107000c0030700015204500b00700030100400400b007101d6000b000102c40c1001480418801501900c40c17030600323440590004098603140d85846106c15501070000000c0d40c05242e0141e031258040d4200340e4100103542c7c0800d00f100514200150118110310382402d154070101e01d16901c4a13900e100300d0600404201034161400801409028a00911810082556000c4000400600d9003034102d204100004500701304201042c180501241d0596803194050b2110f00400c0d2000862075100b4481202c0d01e035a5a03401d20041003c050445c0060030090f0303074000076414800f00c01402d17644a60030821003410900c0c0100800381c0c00290b411900040f8035290518030400e0051500240555804650154207054941e1050083c400150951140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 606126357 1250 606125107 606125131
    0xc0f070809010e090c04090506030a44030115090317072609120a081204030e0109060e0112110703030b010801080d170901090501060807050a06082703130e 68
    0x404808216000c481a903100e490548200411f00c030000c42504615800000902220f002c03c03955030b200c0c020010845d8400d40b0440407202c4480c420070150b000400318250022911103506c01400307016401344810301c6080c5c8039000c0b003d90544021300440e2904015500582980e1000d01628a00045d5500c08282211801e03401d4054407005030740c186150b2000340342c0d00c401a003407584400501c00000800201400175101e070b442d025000034400c00c0100030380c1c100035801701c1c903e081914028011507a034009150500c0b200c803406100480d40b054881d400c1170f9091030007038651201644a000101045200c1d601016000a22501816019042003500080a90f0307400c40582e41c480381191100300221040001543d503070f42c0701c0e40030940c68009030b4022500b01e0001480ba4039030744e1800e003140c3c2c0607404584290054902003000740b82c1244104000d140c40e06000c0c070380c0d1500b50030300200289544545403100c080d0030150400410204141c40c447d05002e002c201425403222144241d80c80102c074040740320301c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 606127607 1250 606126357 606126377
    0x1050d0c0c2a0f030809010c020102100e0d080a020c0606151204050d090b190305180604050a0203100207051c0c0b1306150312030b0f0406170606090f0109050c0f07080901 75
    0x403051514030202c03908a0f0b1341c5814550304000441d940348e180c84060303045200708840343e503c01d04584910145800408020303d031000e4414000f5100000003031a12200c41e01c10b100d003100f51200802c0d090340c444000c460031208085040d0820a55019142006210300500d008210070081c0000c2d011711801c0b1161100315040303640ea08142d0003403084049006a600200c598044540d001c2d40200d1b4010b840d40102d00d1400503542c0ca42c03890084102d0342541e095009c44002819400d06000010381c203400004c1c203515103083c0f516150743d9540110485100960170491000601e4450280c4e81240c40e4062400c4041d070406d1900c4000c1c1130b40c0c0800548090380340280c032104049502e00b41c1c20840380e0100d1551401c4203c01c0095000340510341c203403074000341d8500019807603958622071000900301408801e20304800c03c802042c0f90040c000c00c43c0b80944d003a9002d01204915000e121411681e01d00404122652450001c1259000d180c1e0380590b080000300c1c581c0704120350240501a801c001307984400c005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 606128857 1250 606127607 606127619
    0x1107060501140f21031c0c090906050d03052a1c030207152c0706030f02040b12040807020301060b090111010525090b030f1806040201050d0c0c2a 64
    0x72441880c0b4150301c000c1c0401202c0008288868000d51310004c074040ea4141194400040104080b40d041510328550360300c203442105401c07060321009041c903a14200426800c150200e40c042840c1c01d809028060046a01080c0034882e00c010150801020700310306446070040801d9a442c900328480244c1864042e5284900f01d119100340c620741900500d0241c949084440c007a07000740462001c0141e1820b42c8282c45000924441c204468150b00340c0c001c0c02c2c0d85150003001421250709214451420380100810000e5000c070000b9100300c038480d8004800c45d074403246400c250522480600a405500702600017400c4020750010384a00803080e00d6400300d25040c200d20908070340b400c4580501a02184c41d0100b20600002e04156400449003491419103890b150404c27110380045414200e804480005c0004144402030003086c0c905030304000b01540d0a140d40007034001d001d0340c03000d0030656680b410501515807042c101c41da1860303080800c43e21403440103400d112402c4600b404440701001215800030b22 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 606130107 1250 606128857 606128869
    0x9140a0b0703091a01030507060201061e030201030b0d0c0603020301050f1c0b0c0409060f05040b0603090303040f020a0312110d02070f03060e01020f0a0309021e010503130303110706050114 83
    0x51035408810400396544001d801d9008285054013038590707000300380b8001040d00c09925401c0c0610f000b14000c206003458084000e00392192a00032520b5507510b40101143d074010300000105030b0354242000303e51703280c041020071041c0380c0480001c0d114806042d0000340a503010390096042c2e410954004114490a801340703d18014004044140c0c07049451881000c81c0100c0081904071b101d03902c3c07607460709540d45502d005440c000d0300181c40902006600304070328602803165030b506030710075603455003145001584103807a800002c2c00070b003c1401c102180341c00c43d1340e81c2c1804000b41d9407150346038400c40620030006107890068030071050144108be414a80d0390f80000746100486440400c1042d5a41c11652048080c08406017040c41e01d640038051102c034200f1250181903082119070300000c401556004101100f184a00381000f042d0403041003454999202c130450b58850150028410343c4640e9140031001040b045800c20110300e4003190000803c10a600014125906162010100426003080001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 606131357 1250 606130107 606130123
    0x10f05070206070f030509060d06291b070e04060f0b0f060405010c0627200d030f020718141501020a0f1b032f030304091113090914 58
    0x98810810710414000903800b2104c5601c00f4407a180c06800c0802c005c01050300342c0c011009081d8580d4544105001c070301d6500c0d00c0ea2102440b060304080340b413581c81e034040740244918240706010414024502e510400e0030481c0c03800400d11181071001a14150811100500e02401e00584003424141c50082038502811505801107000b40f04270306e000d26040041d101170b0350072441203643c2c0d0f031180c10000c2c8101c0c3c0b140f80b03844086004030b00440001c003540342c1a009550104030032548241041016616902c560822031310682e0b1504085100500300682a031600f03405901020f41e100001540e4041d221941c0c02403c1884c1103004008060f03129902002007000d09404c01e140181c0c411301e14000460b0304903a10021041c05200422044c18040101d00001001d80d0026644481c02080164034401c140701050740d14010503011480c203600840000ea07e80c45680b089515064541e00081c400b02e0100d8211a4a92039072100c981c5e9080d130325140a0b0142650800a45014100000d40c45042c0e2001c60300e04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 606132607 1250 606131357 606131359
    0x115030606050406050702040f09050319030e062d01060e0a06020303043306030516060206061f1b060906150f121104050712051b0304120513030b0402010f050702 71
    0x1400c00b0b00b01101190311b9003000b541030307921540324004506071440038850354800500032000f65a450260598110400040d01c901c038080500d08500041d80b8100400c0301504900320300c0030021020310720391075400c461003240720048a043e20749000003a42c1d90081580d0b00c289006441c8003003255900c85080c0e0711303400211400707854007903801858050101c0d031416501240d0005611030701c0c0d0303000c1d800c5400d003198030319001110580d00c221214003072a400c51321002c0003000188010a6035180105c0071443d80c90803040326002c07402c050100010000e001e03c41d07821004160b02e03606c1d0340c032170000d00b4411b0140c480250251a40c03480c110007500f988002c1d99118058801e400540f500d07181c81c10309450056400c464042c3d804c0c13008001040c1c03060b6943c0c01042d000d00e1081d074035107020040d0140501c04690300a8041401c805444a1015480042c0001e89a10075048003121287c003540300015120ba200344681030b400d6141041d4040f081018802116014600030b0340c030b043c06044481e00c1a9400d01c942c02c406 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 606133857 1250 606132607 606132617
    0xc010212040902070302030c070602030d1d1906022101290708090f150c010c020601180b0319121d15070c030c0803040603230417041d0115030606 64
    0x18400424240c008104c0c1c90700c24070440e841d080e03121086a04019880c0c01c0303030006800003d41080c109006006644000114890303030351030344a4108a4903582c8503e810340308210038205d5595024400b840d4113803040740c40c4c1400d0600d4180031030051020381c42024007c4031031001e44054400101c0000c000700750702e0f080081000d00e181002c80e1319803040541045105a6000d44003810401c026200d00b036025042c80a8901055100c12030760000754251280c0805420840d801640100502d07018105000c2403060070100010703008901802080c10441095859105080c48610450400541003c036403001c1c84555180c03040300380e610110b0003400c0c0700e02d190035030303ca03404044103401240000000d001080c03041100700b410940d80e50700e180b04d145aa42c403101160b040810100005501406032100301044a01881c1c0c504420040403095407101a1007e003211a03840c03100c0c440b442c000005c03600640507040003290103600c1d2200b0b4148011003400b4507052403c0ca0100498518080c0c010003040d1149030701c407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 606135107 1250 606133857 606133859
    0x31415090c0c010f020d0e0c01050d0b0a050a0b19140d0e100e03090118120623090a0c1d070806010c0c0807150c08030a091103060f0402030c01021204 66
    0x10003501140240014440020800500e10075410034414040e0500009101585803076818200b14103c1c0e100350300d03100085e0000c0501d081c0e5030781e001c012920800c0c0208030010b040e01140d4040340800c4000d401468000003c4074011601c0401200608600b4004500355400c2c412601001c590f0100c141d1050391480000780b140c030100d035165401003048d4a01049c111404c00c01a5801c07501916502105122150800074401c94103591021a01103c2814114407041580c9003403a4443c502070b9000016005540ea2803a0451a03812804001540c02c02e542141d0014140542c10948840e4040c83c200d0700c01200010005807034041c4002501c2000010205003842d550b40300c0c06403200c80009042a04008400d486440000e61050780f03e0b02034080e4100504096041a5040c1495420151540c05002100e410072001507041803c4a80c0301c17a4404010419a4091801c9020981c20060306545400790a042004210417055254891070013103080f03400105003000103a032580750183c603604050f0701c1004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 606136357 1250 606135107 606135109
    0x604030b040308131208012405031308070f030806040c0305040302100c02010605031e070f1208070507030b011d010b0c1b120607020d0207081209011b060c05040303031415 75
    0x360041d888140c0039212015402c481e964040040002d0485c00d0200b9804030040c01840c2d250054540884200038030b418103110f4a2002404602005040700b010500803110001040401d0f01944c4105030b0000200c12034202034900584414812540d090249251501803041d007031003401024091030b0950050020201d50800140c050000050301c01d00303644d01c62900103040c0d07d003003141101c01814480c0056411070210300c0c65040540d41e0780081d850b10900c0c401842014503140c044070721301c0c0d0b1250046a40b2880380c03515505042c400d0740082c1c500c0c00d06070000070742c1449040302404c0b52102449801c01503038841c12400313428060035041404c3ca5018518520030f4240d51a400aca4064005190303111443d003c600d0a46481001c40d05900103811900d40d01d80c11640411201020305440c034082e020fa1071228a15110700e0041c1d908490401c000c4912000910850154004085030800c038248008043d1100240c401d07030142c0300c00c40000740f03091200038203080039a01150140254400c1d014210280074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 606137607 1250 606136357 606136367
    0x5100c0c0b150604090209120706090e190203011214060103030e061e0d06030215041d0a0e070e161b0b091006060f0e0414010603150b070516050604030b0403 69
    0x14454420700100a001c0c10a0741d50b0720f409803008001c0f0290140c1e07141820710512043d220369103522442648640310503c80150801420b0058030b40604c00040d40d9520100380a07007601d9691002545144000000304e181e04031103400071304031401000b804180324400840299250f000f484060700041031201c12401c00e00d0160001c02c07501291f00828a69001c0035240f04403980d010b140118001596a1010000c40c01d08942500314201c0c085607690a040c81c1c58030b4824910400344018009170031080000b01080c0d1035038440010f01200108480b000c81d1240d10300550050f040d81c8004070702d0091482455824880c1c64284c4034180360914845003030392a41e6405407102c8026044120324059401c2682e940d155520690307005040540d0794612080c0c80c004003412606c00d424403580158245020340641c0300310740c82c00c51304403040742c0b6001071009800c40c91450b1142d19500b04a000650004522050200c00900300e84c01050800700b400c2d030541d1720010805180b00303610004000c801d4510004011a010b1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 606138857 1250 606137607 606137611
    0x60b0d111207031805060c0c0f03040311040917070507060e030703050703080c0a1401060e070f0e150f0a020c090109020408070920070320071a03040804170a05100c0c0b 74
    0x7002501c6104ea01035407024140203048800b142ca21030049620f44400d001000000c41d24410705c4051881c240c1107440c3c00500c805202c080c580942c2d02d50700c200301004468003404483c4a0302815240e140c0300b031841d150343c40e00c103640309460014108611a61092901192040880b0f910200800b0a24a5039460440941112402c1a400e025455282e00810b41c098011503e0200600000600c28181039550000d684043c0a1a0820072040702703180e1029000302200741c07003100865111840048040d0700e0070301c91040e8040c42d450350b00046403410f444d50f0000f40d141140802100c0345001aa01e070b0f18a04128040c6100f0b48400303900100c000c0180418079404012400075060b601559105500601051607010020860015908403a1040948072205025484411342d401030050305141000740c00803940b40c41408540204000003080400008104603002040b02030540040d405407420143d03224141101c090301c503802440d00413220410307144a1049100703400d03104c4000f408825101c0010a03040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 606140107 1250 606138857 606138881
    0x20705090a0f090503040905150d0b06041b09050a0e160f09150e0414270c040e07060207080307030203040b0a1107140415181509060b0d11120703 64
    0x10320402d18082c5081402440400e40c0200021076949141144000843e6001005006070b071203455405426551519814009a500001c004800c0d403144400603000b09880c0c0c6820100981c130012280e00c80360800e0f00302085802c21074482e040c650391341500c030305000c0b82102e418415807a1000780c462f119000b20031440a00f80145400b001752522082e10000340c0f0203c21454010415015802440303140c24051204c000d20307000301000c01400c084400da609202c4400341110000c0d0051290400b01a04001d00300300364200a10500902e0b040c00b00450b12600140904001401010404181038400100301da80c0780b68554025450285056200d00042c4c000c00c90200810100e0f6810155124042014001403ca030501c0e0184440400c000c000448450350101c2d15110000c810070803202a804208880350780c034500d400304540803040c07154511280e0a03000301c4882c0f850041c011424083c8034021301f540382200f810402400c0c100c6141900701c1d009202e80008000c003080d001411b5148660401a07810079 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 606141357 1250 606140107 606140111
    0x9090c080c121015021f0b010e0f03120d09051504050c0904020a0b030a0510060c021509192c010e04020d020a1d090706182714090d020607020705090a 66
    0x345822000100074103000707410005901152402c81b0002041c0450802050301140810a145044001905103440c0f85c0707082c0d10481c881c0c0c04460342605c003400a002c00c0412011502d0380e4041d1069140014a00c444003625217214480d416020340600341c8406015030b81120040c00d04200500c20040c034914001c0080f82c00120300840080c1c0601400050350240b02590070219161402d01c681158a0449912070360070411001c5054000d0f80310900a18203c00181c5060359659410101084804540b071041d52110b00e207544002801804aa501513502070790030000b10b0640d04c2910400c80380e440c00380109030015000002180c01450324580c041e0b1400c1c0b0180100c244c41c1d650784915038030001a1202c6084a6451070204444000b0901c5900c010300480e05000d01d02e03095030b610118403203007203000e0352100d04034408a0b45250000701c4099000380005001c05e0200d0000028640c09600094891010300d106030120003000a00202e6954401c040c69401400e6240c40c1600b000156503001c4d0100e03000b15 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 606142607 1250 606141357 606141359
    0x8040f020103180503030411030d141e0c0a03020d05040e0601080601020a02041517060912070305090603010906090e0c131d120a080a050c090402070201020c040501030309090c080c1210 81
    0x8056030500c03d803a405030000d0340c2c40340780900b40b4a07807182c6000050340c401d40082030312002058000d24440c04041100f1364180d102c1c421310843c0342408081c02c0140e000c1e12400328012841400009046c00c0c031610075070a84240000b0104151480e014501074000340c00e25000018100354810f24050b50f100105104403406424030384c012800701d50114403948200e400b440c0041c80210040d000c210120000080242118900101402d480d146206102c00d004000040c284060600c50b0b020fa03240075500610f860f03135a581d41d8405800400c410710440d50064100044200c80c1c1c1d01c00320b10700d00c40312009010039404590714032020703005010845484021114009013460056003c100e1034606002c2d00445580c3e036680c1c0c104c09422800c00421200703415040104001c60b9000d00780c02d46800c0c21080c0d40c0523840750503900c0141d081c202c2c4092203d8003d4504400002810f40c418040c3d000c54070040010020f4148950b0201e602407400c4405110701c2400308204092101c0c11003a0a40c0038940001620030b103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 606143857 1250 606142607 606142631
    0x10c030e180601030c050903030d0b03030f0d020306090105040b030a12090e0a020403020906120c150c0114011a0405180603010605030a14062d04030905130905070e01030308040f020103 81
    0x12500480711148060040100440c40d42c042c400d05034981060704009040164101c0001d40d613110340c24004845507101c082e945040d8400300700f40c65240051000850300c698240c9181e00081d0022141944600300002c000a042d017454428440c005002038042d07d07400ca0503454900000446044280800c001c1110020b100f58040940c02e005013034008000da0b1b10307441c50040001320b020113841103100c0c141402428800140008014000f00401d4650140807004108030b82428001c60500540341d500f4043c3e1036002402c0803112a042c0d410400a0a4003c1c0740700603101010300481c0905a080241d110801c050601d00d5101d9642c0004000c001085054441c0c0c0460300708010481708450481d030341b40b2003c08920050101c1a44000304451080d503603403085030400c8080c078520310104400180200880c083c03601c140d503180098030011381004100301c039509020300100308030101910680219907000c0341c546034103403900b070403240c06580d0040251202e46545c0e20462203150308906045e99140b0103170301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 606145107 1250 606143857 606143869
    0xf060c0a030e1207031a10151d12011b0203030912031519170d0e060306010e030105090a02012a080d091a0103060f05010b03160c051203090f0604030905010c030e 71
    0x30718840d4194400c0c4800c01c4100a44155007d0840050300c0703002c110500854a0001c4141070301642c0e0315040040b54616021141004441803030140c101c1c3d00014401071150054001405000c2030f1554044c00d00e0341c4050498603401b054407080090b81081c0714400102a05001864100a1444a2200c08803807500000d001c413080f51100d0000d03440703010003081035040103950b000e084010a1b015007071010360031070b0040840304100c240c00e00c500d001101043c2c05074410588140b003003c021f0000c0009080130746850303a131a40104000c80c005030300c0308450340e04c00c854007810b02d2540d50041403850213181103680b88182c50300280945010243e0301c80c4007001144028103003040769948a80d00201e0b55056042040550b0030290304c80d03005508080040000501c0541200e03405900030501100701c0300c0c4181c08542c00c00654101038030602c0740c85007406402034441c00450041e041c1c0001ca40340340b0300e08842e0782d44a05003168045e000c2018884100429405220f01181a5200e0302e003007500140c0d41800200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 606146357 1250 606145107 606145109
    0x20303011e05210d0201060308070b191e1a0913030203071e14010207050a03050c070b0309160510020a02041a061603020c01020114060f060c060403020102090f060c0a030e1207 77
    0xa112500301c40c3c00d074403200d0a000306103010405100a0010318250340b9a40018490343d0b0004055200310800604062112080c2c0400203011010a003c00c0710103e091501e43c50244142c8d5140c03503e01004203100d85000400a00d141c0009420080199583c40081040d41801e031000d5080d03020812940e80056800a0712504000140300a40000e001e5030a00528205015031425516031041010134042a80007400359036156261909650302d05c8103000690420149900c48545035801000b0f201860310041007010803a0b0b41480d90410003613a031010004084084007034540540c00994140000d0b00701900700311030850b1101171000442d80210082143c42c0d0081c200080d000c09000018010181d05026001450400344002d1004c60054041d8550031400074180500c03480d100c40c00820701d6212101aa40d0900440301a40c110303140c03500b0701034040c0d030100010a100c1c04184450780400d151290030b840d0b640807414014503005a00f5070f4280c50308050640480d5000e158800c40348420102008054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 606147607 1250 606146357 606146389
    0x5061c05060f01171b0303040f0f030b0906040210080429040c06050c031b150f0108060106090e060405103b1b0d060e10150807020303011e05 62
    0x215142c1041c40040344801a0000c81390031a8070050031414600018841a901c408030b80e100250f1014040028510301c29980001e90848950400146840101c298201140d016407400d410b2641da840d42103842d000d080f50020760003034200c500c07100c1040c42a211250300c103126429101c0d00000d500034507030303000e40000f500359004044102080300704480d8800d0710000f0115424403a00348000320b0728094aa00490300c80701843d804c0240c01c450070100030001080c0068450076410102d05020565a1000809018224031445030000000d03e0b540700d00514411110f2280f0041d41c50703212602084080c1c10041c110201c810345041000c5044074a82141e60204450451615480005160360071480110303020078100c01c0710080c0820040303154a091300c400e45040ea040b450350351a100b6016100030081504603407484100b4104008000001c00309003400d95081d0b0f00c501505e440c840710f040f070344180c0c01c40783d140068105000400c01d10710080c4181c4c084044c1840c40489450f180c0c40030503800d01c540d042e0b030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 606148857 1250 606147607 606147613
    0x10020304030e030f06063001060609060212160f1202010b0103060e0c0f0a1205150405013606091103070e06070b0408030a090501090c0e010f050a030605061c05 70
    0x44020140c10080d540c01005083d005040f01041d2000c1182d10707490004c11160152140302040b9101c006074038174074482039030b0300107403444500e1442441ca4024201c2d4080e0101081e135200d40070034a02c1c000501300c075649021903002c0f440d00200184211008045100171181d0082c00f4072244001082c003520760380002d50790780c00054003402c1c01c0001010380d21254081101c2140c25001c2c45001c10000d4201d8402d0f002c0780e501d40f030b6100042d81003146e0248012200c0b112117880c007024002c1001e145000c103500a03500b22024010340e600d400b041e181494455a030300c020f640c0800c642181c1540c1d40400c00784d28050f1042c000990f80d41c3c80d103508059500c5903580b440c8190300001080805c54210700c1150725180d064035021305050050380c42418001020304003600c4c28001000040d0b0182c0103070022486554080000e001602291034698401642c600500c265001c60f600003040080004c109a41203c1008140720100c0c1e14584880d40100005800d00d50005580d5881c0c1004010800c400306c0100c0c810402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 606150107 1250 606148857 606148861
    0x1c0914030a02012711060307170c030f07090803091509030706120e0d0f180b040e090d111b03030706060f0306050702060c09120c09010f06080a020901020a0f03030608100203 76
    0x203604c1c00150800d0b41e880b002e104402000c0380c0300244a03100014281c4000c0e81c1d039155000300b618030706047d40404c24000d024204114611000d0300145010b40341e00c0e00448126240e0840a5030007900714001e00ca40c0c2c1d407017480481500d00d480c1041c0e000d003030740603000d40d1300d424841004242010a2608500e0100740c02c03406004c01c1c411b5501c0b98810000400c4041c0410900020004040c80182c40c404410007495001851141504241c00b100801070b102c3c6840c1d4035a42e800e114981d82c1030466010000d4001c10050110850003440c00035803101c240005004d11084410552240504504803160107100c1404550001030301c41c45208003074400c140b18848030510f14a0480141d55005140034219040002440362500e0000700740c0b03200c981c04480d01054490b94000301840d100300200080d920019400002901c4454140d1140503645995a4136007569904c5440000340d100d5210154016440240c1000110f4514520422200d10a00c0d000c00c5883d0b48850261800000d944207001d01d60340001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 606151357 1250 606150107 606150131
    0x70203070201110a03080f0408040810091406040804120503122a0403030e040509030d0c0806030f03041a03060d0606090c0801060e0d1e0204090c030b0601051c0914030a0201 76
    0x890240c0400c443d801040006a15500140445005040d0383e034400107171000314082103032403000c0d10060036600c4202c078981c40741c1080b40800f070405000e007640d00c03108240da80c18002c1030100740244560f800c050300b240380c1468111541307032840f0003140c00d5030f66000a10944034480902d00400d400b41d030250000801c2c0100e030903079605904880da02c000308014020082040000c2c0c0184c0800c8041e0011075000442e50350319010a41584141d800001e10b00b0f242c00c201a85c143d400540450240d841507045480320b005100007103540344914000c0e040d8196040a074a2981e50250f0000c3d03138443c40140c4601080d46180c1c0c0e4080681c0c20a4002081345034940740104d0556904c40b10682c0180f5403454098801100000411006c10104030041c0008248154159404110001310059154050000c104e1940c2c107013013800301840070380011a04d0701803540c08034450351310940c00c6d10307895807540c1d02542480c00c40030700400090202078801c4480200e4102d09022081044c005003c03c0c280740c0e00040f6403285100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 606152607 1250 606151357 606151367
    0x50c0d060e10090b0f040c03050f130203060606160506041a1b122e0503010b01180e04021306140f1c0b0408220611032817070203070201 60
    0x14124000080c0321000b04006030703540e2100042129000f03c030004003004803402080d100c90203181440c4c0c0184c1000381480056a2507403203580b04451030030303440c03401e45c44896101940c9451000080d40c1a4081d001050540c60700900034040c80619035207100d18085503a46083c20306e041200c00741d404141051189003800049800c3c640e101d00180822450300d80c01c02103102840c01070340400300903011000c0004a0030005040c58803d00320104410052030140807d03042880e450720300820b80030f5428149501c850394060408000001c40032041c0c14842401d00f01c01c0c3d41030f40340041040c0d0b8040400c8140921640c03030f601c2128040d0044140c06400c03242c03544248110380c169a070000e8081c10103088001e920b0400d02880100e21903122500c10206d855a05205c000c50050741c8d494031150000c1c1c240280f0b410650085003044851548407000504009000103031a1700410054840d160695800c0e05807003030301901c40983d40b4203142044d40e580f41010907880248442210b42002584c00002d15078155a004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 606153857 1250 606152607 606152609
    0x408030906060a0b0a080a110408010c021624170c0c3f0d0c03060f060816032c0705010e04050114010503040812090304090513031e02030c01050c0d06 66
    0x150395403c2c0541c41d00c3c00d641c3c400d01c00c801e42c80d030401140d10086001c0800540014145104e103000003501e0350388400345030340280031105d194005482800704c100041d40710440103404440ca1800701003007540441d50074044400c0250800e000f044169402070180f2410389030254012440840c1c0176489251960120785040b9400850102c08840c0010b0a51070302e00c00821070741c110784490f000e00d22421404c1950ba8107800341e100360158070750804aa51808a905500c1803003100e94901c1c07400c1d1099a00c08048e44c407060141c8403030300e0690040920f00c40260198101d40b07000c0e803266903001e440c803500c0c465040e020080c3c07410303003001d80d04290700402c031941e400300351030184100880d0308020551402c07101b10300035080c000c2c0250502030040001014001800140c034040c41c0d445504a01a00d40030301c0840d1241e1043c00b807040341c070f0300e000085816801e01201d21480c05605844103450354450490b03c5614000c183e0306e180c1148010044d8030780701c120a0185030302400ca0410260b07251941ca229800642c1d103d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 606155107 1250 606153857 606153859
    0x20301090e2b0201140f0405010b0d2d0f0b0609160509120f0a030906180b0d05060a090606030204090c0e0d0312020d060e060112062607030209040803090606 69
    0x42e50305841a241085161401c02c2c5480c809246000d1034802c00340d01520648048014040401040080c81041e1006087c45030b84950003c0011702d50100130880d403001c0d088030140403241850121015843c03502d0030680d41102075070010a24094550300c0c91110788040e4400c40d101e0a17510f00380006810400b46468000504800000c40c1a0380c0380001030490103105070b051702c515500900e0030b64490041c002800401716aa00f030711100d5000c0d06018100c0c400a2044000240d019603291511200e0234204030142d0b10203902c010702d4103c40d1100c2402801e0040d10340d9a01c910111400a68501c1d0b41c41841e0080038140c8008d41c4461400c41c0343c8048400a520007000d200030a612280e0f155600d01511031060fa150422008019060200304001e000d41030b800148149006d00c00300e040f0290408281c441c4500340e803141201f02c4000d44000907a10140f0801d0a17006102d0703000d04a00c81500c200946c0400500129a0207560701d40000d01343c00c100b95005e803003800d000001c0c40106c082c1448401d0b44064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 606156357 1250 606155107 606155113
    0x6091e0b2407060212090304030c12150c020f01020a110601090e0a0f11031603021014040b0a020c03060a0c0801150212070303020c120306040e161a0f0409020301090e 73
    0x4900d5280c01d40d00e110003a01586554030000e41c0300d0410080794140c40d03c8003a00076101c6080c2c03900106c0c41c2c0d51307a4060300050744ca00b0904100080d64000840c0a005810340c030070002040a00300d8155500a0021504140298044d103181d180c0514400d00c050045000340d5500c4807480c15658401d1802c020040c0c0084e2041c40c105201e01380c005a0000300100b200c0e5000900032101d141c03600340101400880e0b18040d5050060756819174800009414107800d4900844541501d0020041c0955a90320300b003400480030b40d01440200424500f04000c0d0044400a0041c0c503034500ea0000042d082850448009070351960b104450079200703902486042c0504205480300d140150b5031a0069910340c101e00142d0750401700007440000f0580b09806540981c03150008640d4015444210b00030250001c643c0a40164905444400781c480c0028108900e000f5130411a40e015060454141d26440c5a469265074100100305e40200002600d0003000200002100161a9410003071400c068507101c1117403081343c0d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 606157607 1250 606156357 606156379
    0xe01030f03080705041e030c0510080106082802040e0c07170306040902100f0f0912020d0305120c0a02121c1a03030703020609010608012a0306091e0b 66
    0x912008420000e26806080c0a515561a0901190380b40b0494002000e203599190007003104001411180007501d00c02c0c1c002c4c08810f40c45000b804290b1103070440d074400241c3c0031001080605d002d1009207402401c2044920600100458202d803918021090308400070f90000c3c0c108121030b070b00040640c01580101d00c1500d803403950744400085410992208442c3c0300d0000202d1441d41d1182d1254000a50280482c0d020350a5074a01a01da0008000000c0115080701c2480018502c200d031154107540c1d6960001074070560300d400703001e10700c07210340012810300808106104801c000400c5441c41289205002b0390f507110304010007420609040c03003040c440b580030310810211130002d20411070411084000001c0195000d42001ca10460b01d26210380c15000020b15802415408a02c180c4502012402844007640d21441e0702c3c01c07134584a200301d42010301d91018412641217a01c5c000310100d00c0303150102e840c944800d01c0900712200b080403121150711030900c3c9015144135006801d026101151107040030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 606158857 1250 606157607 606157613
    0x105100212120601021006090e070b190e040f02070506010305070f141c140a061401080c10050909010e0406050901060f06120204180212010902070809131b020102130e0103 75
    0x40c01907810746021002c960707000030b106900c00c0001c4055812031100c1403100c01e50340c0301c0707240c000e149000f4280054083c000c008a6104100d00490304c10f4500e00c99400001c0c07031044002c80700c4014803800d243c1e20646600b2440d03401411400175291480c05030019000035459454503500e40500d56110f4010041c46990400c9240780c0b4100090408609580c0e02281d428450301c00c01072400c084600812000c6a51170307140c3e490400080440000d880f41d0000c1103c0c1d24420f0b48002d03003200c01d01c140b80f0a580005201c4196040c00c584e482c2c684912424042c0c02c0000d402c00103146000241c02554140b51040104014402c89014107900302e11000004c02c02d00342005c1005205052501804090144441900c4900c0516074120b4005143c20300b2003081005000011802a5006420050703100700715100110f40000030340700302c6880e10390105182d403609056900b8444030b0501d002100702565556804c5125040420f04d440d12100606c0d400160b807011034660307403208604d02c1c1c3c00550080f40218014800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 606160107 1250 606158857 606158893
    0x50f0609010b0d2d050303060109090b03060606090a0801020406120c2f07080f060403020c0913110f090a0b1002010b012102091003090b0a0504020612040606050d0b01051002 76
    0x2083d50000140c000e0300c1e604000d02c1c080107403200c40402c03e003c401104a824040040040c5001e81d0782640c3c0c016030641d907039400b40290b591700c810300f980c142c100d100454031130b19015005001c0d40d0b1002d031188010b17664074040f079822030300300c0c1c0d0180c000728044602203484481580b06104000043d42804501018001c20030f2040d850b950000401040c8804000b15861804111800060254100700c40078103282c8111607071908415101200988500f100c5040c030703031514070b014502c121080c1d120501400101d40325071446d540c0000380c140d00016405d04082c110f44440f65114840d00a01001107881048601400510449030012400b107924000e148000e07030b80e1082c007078942c043c149c1e82044000c1610303580c000002d00c122a41e89501ca0040e450300f1a2050305034004094803400b41810341c805580700419402900c0c42100c0c0254089010040300e08141d44800c5c031300343c00c140640400207115841d071000c2490201d40000941d00045d040c001013100b80740c024810014454240f0140850210081080b01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 606161357 1250 606160107 606160129
    0x2060c041401081b040f031209030302031e190e1306050d06050603010e06040b100e1501050c0703020a0b18030f060f131a07020d030506010e060706110403050f0609010b 74
    0xb0402000380d000c500e8042c100000c0c2d6001e8030100c9242595141d8030f5540b09040d040070f2100726032000813004241080b502400040c6c1c1101d0300358029501d0040075610700ea0000c0c01c280c17400740320400184400d009400005044468170702160315540c03095100c090070080010407616100003010b0520070240855100c076106120a941c1c804004103040d150350380080d0152010007200842c510508042100b882038820a56001d480340c058600400703526121240741c90003048400302500c4600d14100782c19544901e000b0140102a0010b9900740c0d5166030010b04010030940c00b5924510001c11201c0a2400c40f0f242c1000551b070460003018420060031340c02d504c1e00c80c010615180880440000340c000c0701e4001c1800b01d00365201507a5880d001c0003078140d440c0702c032003540e00c1801441080004001c0c94080d00c14240104016194812000030a0082124640c4022800c442141d15410904001e05155020380003841c45980588000c001c0c64014030320700740008000e200c403a8188045a0400d46071014150 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 606162607 1250 606161357 606161359
    0x2030a2a0b06030c101d010c0b0a021209010204050a180e010c03061401020a0506131a0a0218040b01140c0f07080a0203190b150d12032a05030c0904061701060602060c0414 75
    0x102d07002c031b00c00142c0d18156180b90107014103600c0020850f10320b110303034020708484001807503200700c0d9210350004900302d008500820381c201c40992030600803100900c400300c103034054581010540c260302a540030b094814280000c03001c25101d4009000f0030003015805075074001c1c03e1004012001080e103540750b0300c20002d00313103000010b0a0032a900071320007071401401c0b811005110020250a001c01030b18000d51201240c44003004503034003001451b01d080d0048050080c416561800c103131618903845041c1e07a03c2802e50301820710a03225440640700085c0143c00c02490940c01829030031a86005050424110341380f9084c99544200580d400918491511a0860b0421030320500307034402900801d106000070380002e0301a00180400f40000c6a060304062035510110280294003c0d9861601070982c0c03031840c0c0701022850901c00540301c20380d500042c1c80880c10041c00402c2e46030782d131032a14040c15405110100c9030b9454038024046141c040002070f8200c148045071526052070154403181907204c0300042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 606163857 1250 606162607 606162647
    0x32003040503071e03301104050a031a091203010b0a03020409020d0509070e192003040302210415030b0a05060c070314010c02030a2a0b06030c10 64
    0x2140a0080410558461940c050341c0380e0240f68402030b2880c1002d140b640304a0018564040b50f01b14200500c0e48030940c2c0360b5181d100703818885000c01c840c000d0803106c072408139881340a010000e9255224104480158040c044241001006c088003c841c4034004107071041c80e80c070416241c4403403c92007044a04544566904a40b01c0403840300c1107020f8030640d404100351500100f12540303c034109034080350141c11101d0848850a5070b603001c0d144420f600701e80b0040560b070641b0740d0000044032500300d040410804019101000c0d8103080040868100752400d070f0041c1c2c0002c40d0f4040505074042c940c000200c032003401c0c90801e0314102480c2042c03081341070840101500c845040c26141c803500c4c030368005010001d0056489812111202e5541c1d4202e10094603400d2201e40d40600c50003040c819880f180c19182d01640c50a1681e06d003c0d10107408500c000709400124545081c6600c0c107108500c3c0319103106020358002d900f0074404140c681305002c4c03c0d0304e10450003051f80e5410310b80c2201c0b581401c4210b840b21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 606165107 1250 606163857 606163861
    0x61f030b0c22090f0b010207091e110a020601080712060f0b03010903050d1a060405120a050a05010506100806180702010914033103020d0f080a110706032003 69
    0x1d001d44a004480c00c0982c034100709007000314001c9222100005441682c0700030403402c480ca40e025425100b0850380240980c01901e024415103180743c00881490030000c15000700700c000c40b0b04540c102c42003041070b00c550300b4002c80c820300c6403641405a98010540000280310a60408840f4400c1ca14005001024180e4601c5202d9181781c00d50411040c20f00020f00810469409090140180e80180f10004145241811a0b00804041041140305600280c0380a0030136040000f0300440a080c6178101740e051140141000002c1c80c00c11100d80c250344140004141c60070f100050284502000c0349407414000c51508004032a2101c1c0e01c0400f0001d84103500349102c0d241d01d00103900502c28100003403c1d585c0030101c51510f000c0004000d00300020300000851145c0d0031400c1d84903102040231400850820360150400140c54012000d601c1680100b6a43c4c030840403950301c11006510610040340440c0c00041006841038003405104001c1c41c1c1824140980c3c010300008181740e01c491101c02500f2840400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 606166357 1250 606165107 606165121
    0x60109090204060509090a02010305010801020a0813080f040b0d05010605041212180306050f071e05030a0f050a290d032a030206010f050406060903030818120c061f030b 74
    0x210041c0304c007811101290130125007080e207600d0125001c3e800710742001d00004580344140308507941c0701c0703159440b2100ca4036270b003030303c81c84c00365542c10b0075210010709024442425590754010002031400440d500e40e138602605100f002c1d0b410582c04141808810300c010451031a4074501c1e9000d580e4031a4409a416101040c16102128101c3d222118104010404010040300d940f01c18069815040010240e0303982090448600d07044920789805d00741089070201c0c540d80110059500448220703404250b001000000c0e0044842c100c0311010b05684504d00c49060003035003010584221000002c54140c4990100490190216000010700300904046c5404014010b010104028071841c5807147d02403100e4100203650310420b000f01c1e040f004940f900040c0901c2d00d8030888040340c00d107803a00e04003d803454070296041034000349003507104584100e80030f0980d0001c2c00071030721381e80d6005a41030b00e6200308000d031450310070300604101c8605240a0108907030f9610a42110440740c0c0401c500d126030752006 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 606167607 1250 606166357 606166361
    0x70f180b220b04080a0203011a0303190e151b0c011b020f0910030b010e0106020a120509120120041d061206090d171005011b17070b01080609060109090204 68
    0x9071001e10b010a01143c04102c580f8003080290410b40200c009128003401201c1c80c1030403010301c815465040e07100304400e08200c48049140740700d1290a08121015683c640e01180c6951414541140f0b40e10000070304030038a40038075820035145e40445000345030b90700300304001808907100345207546442501c0800540c1113688100070000c088402074500c11950424104041e1340780341c103010466007494800008202006d1001206048401e02d07401070607507880036100c040010215052290070804100140d948c652107032010009405000000018400c0035980812080e100305004c9800c5504108020012103410300d241300f68404800d4410015074071030100040042c01103102da081240903400c00c2051030100491040301c401c04a0f1622002c1e1480072002da070f2400d000b2103c8a0502c503800c103060256510550400802c409507440e1041d4604179500d8000100100ca44081000e200000301c020411044409060050940340d0040045080c200c0c94103131504c1050140841b030f02da4940102055607116 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 606168857 1250 606167607 606167609
    0xb0303071b080609030f0906030423060103150204080304030b07200a020901090504080d0e100212060f04090506011e090903080703050c090d0b0603070e070f180b22 72
    0x40e20424400c0031809071800d030403214030408105000b2140050a04003000c0121406003505182c0e0501e40a012030030000b0903000600144d444445000620720001140080d841441c4501002030a0b158550b01d03000d14803040c107040d200070032030042c4810041d001000041d1070603240c0c418071000d846d03564884202c0c0c0c24001030507030104004250b103074103004420100e9001c08050080d45c2c2400541c1e22084001d060314029500117106507006c01000f242000385600c48504030700382c00240d40e0008201c07102d0000b88d0b00400e40c06140c5107010700a0003902c0c5860700710780c54030745000e4400380b10035103081c6c45941d242c0005120b0700003105004020b21a007500044c0c0f005001d090b50351307410080083e5a0500800c460000c80e94880400c0c90300020a84001030202601d4622100600302d045219140c2d84a400d0108003404080e090311611502040c80745510040f144141100c0e903c0c44280802d1080007045603101c0d00c5895143c05032842d05100300741071142140d2605034155030b0740705500758080c40d4110f400d180d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 606170107 1250 606168857 606168863
    0x4080c031c0e03040f12060902091008060117031207021f020426100c0302160b0603061303141602030a050709140c18010903051915140105040b030307 66
    0x1002401c0038408080c402035400d04103502000304040401e060750b0541e244030342d01171030644a10700b0208103c034490514110b03012910a0202064000d030395030201c0c1094800b40c1d503401c031032031501c0320034011107000b0000c20380101a48401c8900300c2c3e03988501c2503140c5c4100320a542d0000f079424001940309008200484881e0504540800c41145001c824030080d0464081c2160414010b030b01c150300d100c1c0c0c0003022842c81403514054150b0020b00c0f001e020051458420a40c1030540900c9103d8400d59800201c00700d5a0003450000c8991034070307408040c00c0403401000507018131700404072040401c1e8009000c9141d281e80da9401541c0380d441800a00209000550081d8940700c1e0b0701b034083c10404d020854808507041c40c04203010081101d00b6032664907c00312000c0b00c00d62428414a450100d008196200600041c107140746941c0c0c0b25101e0307034240700c1d4150462441c8030a0140e10020003030101c58050030074280c0c0000700190014141c0f20321140d081841400d01c2143c82c0d50302c905803a541801107906183d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 606171357 1250 606170107 606170113
    0x910180224040816050103090c09020a1b060903110a031e0e0607050f060a0603020609040903112a0103020a1b02220501140303040b0403150902060706091b0b09040504080c 75
    0x603850f848141d0b611007050400b082011000c3c00020107501038000d008101d548969420185070510500c20002e4200030107180030400c400c10300381350241098104c156600e00902e80811b00041900340903150030781603c014034142c1c0c010580000401e0344041d150700245181d020381091400302840031a00081d90601040c0e12650005040c02001800111200e001d04810241d80f800d90f504801c40044804130702c4060340004040040c1c2e151490554041c06d4198032a040c2401e4181c0f142582074a0116003400c07140c1010780404414100e05504c402881c001402442c0a40c60320041c4640100340c46040c44e001500c921060711214115039440038607000b58800030005a081c40525003c00d0054070082c89615180328602200c2c58090602000726070a4480d10b40d00103141a16558640500042c1c07841489455541c501c034400060392414000c00d0620b00902d00861507040600382400c0d2104002d0003118034450490080041090030000c0c1d03818a0400c5a002805a4890418001a10880e0f84900141c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 606172607 1250 606171357 606171359
    0x4020c010b15030907030809030f0f060406050c03130f05250f05040e070b0a0302211509090d0e04091a0103170a120c0e0a0608091018022404 62
    0x4105600055070450201c5508001c0b0182e10000d000c144000e46081406801030001440420f11110050103030180c06011103031500d803036400035828080d40090154072500030409120a00820340162908107819492552860408110004042c42c0e00200100070322080c2d10300e10103014050109610702d001c403140b8480c40f18064139000c142d00606002c0e1901d01600c1a4002c42c25040500c02c44c0c0d8207180c204001c0c09020300700700d210403864019100d207404146d000c00040054600c20302501c4000030900b140d0400340e0a125103d0104407850b01c014501400e144010405c1ca810002603406a8042d00c1c01d11000541100021601901c00b8035006080c0310600507000715025180402c9074101d034001c1d16900c15040d00c00c2e00384c000505c074010190001a410000d100221240c9a000d03c1503642d6506001c401c0c0003080000c68407440050b40032801144041c0c0801600c040c080c0401e12658404007810040550505542d8100c410480c0010707008480c2c1101c10001c006607010f58421596815109135215 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 606173857 1250 606172607 606172627
    0xd02010305280b010221120c0705010c09090e0d0c11061b0606090c160b061305100906050102010b0a032006120a15080a170d020406110712200409020402 67
    0x2920000c20f80340d00520541c40301106101503c0c03000ba0401400942c03007444c0c001068035001c000000942100400340c01084001c001903001d1041d040044c40139150825824030345091f80003103c9100c50400b0190f048450040002980155807000250b44988000c0010f44407801185a90040800818200c031104090f02207607400040c540d486800d00f15041052961402c409480c94021071200b4003040100d1601980003818520031541d2210000d0201014400043c1d40319050710015140103030100c201c1101409140c01303c0c010180035103800e0009119a080c04404101c944100e0320000d00784419006401c03414060b250103075161034130010041500c4a428884000005506492258940f441c0c02d0106601c001049207000c1150048009400310b100544c40e40301c0600c1d080c42003d07203a070108102d04000c0006910243c0081c0001c3c0e0f4862040d07289103440a440d00304140c10440c0d981e1410301c170344000140d0500340881181c9640c81e410348411840c41c081000b0b8500d002c0c00030351040c0041404201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 606175107 1250 606173857 606173861
    0xd03020c03072112030f05040605091e0c0d020604030c0816050d021513050a08070302091e040f08040308030c0d0506010c0203030d0c020f0706050307090906050d0201030528 76
    0x4a28040342a14001d99654042c10b08407000f00026030b4480c10100e4030600482c6810640c50705405440c1000300700c000c52400e445048500849040382c000b80c4e2407085c02884041042400030b1108015000506244c51201d020ba848010701000c91040c04101881c01c11525941c0c29034000719402030420070b54a4550150f203441d43c004119500745103964000c0050b0a18101144805c0315801505014910094044c0a0340f42d5112a0740d5a00c030700800140040c0301d0302d486913030340014058100540000340c00c51042041c0300c0c00140410720900800d800192032000b5aa030041d0b00103900505000020009180c00002d50103143d00250506202108100008007100000c1c81c900000340e1040140750f07110b030019240c01054540194156000703004000390b8101c03540c40f0030034407113403401100c030303060865544140740c0324141d0401400524003000303200c0410b40280449014207a014800d0017860b0612010800d03100361001c0c0070f8101901c80c0086030801c010002c001c0da60f0080c082c2d6140d50201d111a400f40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 606176357 1250 606175107 606175123
    0xf0f07050409150e01050f1b040e060607140c01320c1609270b0f060a1a0c070f030312050c0408030a030c020c04090209010311040b060a11071a22050d0302 68
    0x400040c07c00c00100e5010740d0052010055154200b50740c04c0504024410600000c010149600102c0c00c000b0350b0003151303003042a00000c0c42c03800014581f83c0d4130301c8001070040c6024007400b465550900314640e41225250300d0301c14480c81e40c1514a44648088030410b2030b2075240d8240f412284911200410715007904e130031803107140c120107103802030003042e811400800c4020580301030548100742e0040351255100c98070550b0040d4000700007001150300c484c1d1503400110080c0d0b1003107001800061092150300e0511180004110b41c00c2d03c03554061550302c000e89102081040000203594450000e14881e0450040d5000f0348072190031281c803901c10100140090204210440c05882809407100312071074640542c03014260302600a00303e40e461603648003400c9c070305042240d5009440e5104058140c9901001e024500120b50710b1031200c00d032138100f0303e0500f0b681e0742184500900004005000c0c3c900103080703030203039404106008482c000c217500c0c01c14216540d0300900d41c4145090b4500c000d060780014071903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 606177607 1250 606176357 606176371
    0x201020109140d0906111506041d06041703040803010e0601030920130e0a080d0b030a0f210507020108040318060306061b0c0513110301170f0f07050409150e0105 71
    0x141c1400d803114010361b1005060340040074103a00c00c111210b05580100d40703582d04504017800c00314285c890447d0404008840840314601e81c1d00103000c100c2441126a41140211680c112403461810145c403118a40d2205002e1b083c1c0d000041030102c0c500382d101c1d510040407180c1080604824034544c8020390450324800104510811000d1034010b010321451181c241450075100060040e40e510f85e0b40c0c805240c0195000900d480e6075201c00c040641c03070034861401400d02c284106e0a08800c145030a28004103c40c00c059881e00c500140008800c1d04001201c10302502400e03c07900c82e1f915480c080b10f03c44901c110803007030001070090002d49150503805c240240d9440340c8500c803020b041d01d8501444404520f801404801551404200d203080c070144401c4c80007602d01021403410401001040036900c2039220b03001002d480e1002409007103040c484041c10150207030152014082201c0c0c400e60b240d03d10301406104690758041030041101c00032a502204c514010709002e03181905000d54000c142c21200f01c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 606178857 1250 606177607 606177617
    0x30c03020f0f030712060f06092f04050f040b0a080606010e01020109050a062c0a020411030f01090f0f090b040c060507052503020315010609050105040308160201020109140d 76
    0x822082c0c54041c100d40140c82d409401402d002e441c1c00907002101c1801d000c140e80c8a0360340c0c1568400c1420f28001c25000d004104808101c1e0740c031011240822941a420003840c0400c01614100c10384071b8141220101c030811102480c2000c1c042c0b0001d4000c04071441d5a980c8401c0c0444002101c00c00800c60320300c50031003621b0304000000400016800d0302c03945000140b05400c414550300010b000c560103c0024400c04117101d0081444c00d03424000c54401c401521015445542044210f1405000d00795035913006000c000d0450410060b00e255030031040c09040070301074486149510780341680e44400300440031307100705101440e901c1c140b4400564050707070280c8800e00c0c07440740460800d0080c4202e4660a500c40020260120310342181ca482c10508100d2141d00146c00c01e001001d80e4040010088065048842c900b10f035140440c0900401035030b600c031a050050600c410408100d884068607000c1031035540c03000c20318005200407801810031000007004003a220942540d000c1c000100703441e0504090b152 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 606180107 1250 606178857 606178879
    0xe040b010915060e09220b010e010f2115060b0705070515031501200303150a050607110402040e040b070305010801090b06011b120203121803030705160c030c0302 71
    0x141c0c0c01100e081c0d000b6480850300803403400320241030000191b94400c5c1c5959503030702141000d61000d04505403548064503410001001440b251100b10b510500424004041480b2940b81142c60448180911191928007e0305480070003400961803085007034800c4841c04212a544515414030039401c846d60a8513180f0541e84080b4890401000541800440c18081c0b81190740b8680400c00780d001c18070400381003007092821081d010300b0340e003020580d803200440903640300d140034025242104003041c0d02074442c004c41f080c20081a05c075101240c21264000240d8800801440301280282c82240d03c0441c003031204000304010300003400c2080c0d001d40f02c942d9040c0181c2c1da0740d482c1c040c241e5009942c060040002d26000c01c21941c00303950705d40c176160200301040c0003015a545600144a43d0b0070285e40258000240202203a00050105a0711140c0d5503505092201900452a07680c000100884107009000a80c0c407040034003042130320700d4a03a001c819240c005859140c0204626080d1000300e00907900346007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 606181357 1250 606180107 606180131
    0xc03071a03070215190b12031c0603150f0b0409210207051207150e1f0c121d01141209071509180506090411010c0618020114040b091005040e040b0109 66
    0x14a2080e0310b0454001503082c0b16510b2000c1c580655406274071418159102c00000c00600322041c00688880000000a000720a554451060b00e03011000700d4411490500e4020014401c1200f81c1010b030b030304540d000c000c481308031001d03480c1c402950400759001c400007150f100214000506003064410b120b00503002a048820309581c401e030900e40b02c1b580b040f03807020f41f0404c044e2910540d240d51002440c01c0300d0382d007040f40c450701c072034104040c00000010403111058007550307aa0380b490410504d0130300c0c0180e4126049102e41c0380e00c0c00f8111107030451244520100c1c3d0b42c070314100600d0001c1c0505140d9a030409600040141c040b01040c0300781d00c0c5150051488074150f48036407258a11880010f016000b26582d1540d07903100802c0b048071058140320030b411024012803180c2c41414802c40584070100d2007840c2b5400054040081e5100d40302181008200034043d4080e054291095120295503c607110458480203072131071b0040f42c0000b810f0302846400c0006000c424041c95040340d0300c1150802112031a02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 606182607 1250 606181357 606181369
    0xf050c01090e1513061e0e0c0406020a0f021f03060603060f0302010219051e0a06110304021807170708060f01090f0501080406020c06010602030c0c03071a03070215190b 74
    0x203c2054440c250200002400c2c140700d00310110454041c00000f4403035440345000a00780344110b01c10600140c2a40303080c00510411015a90003114140007a403c2c54a1f103000259500c010701c40080c14090408510001c40d02c8200c180c440300c800041801e80d220700c580300001c0017081c0d1882020000b03804c0200c0090701d804286c0305541070700d806a0142c051101100e1100d0700480c018501141c02d071042854010010856a1200d10070726508000703010861090704059065a50400c0003003c0d8104c10818003005994076108001c800100c42d800081e40c4c0e540030820b8840a840344c0c8441107030283c0c9420817a55691055100d4820041150b00c80321991100c2c004483c1125240030b01d003034500c0c80ba54107014640c0140001507001c0c1c424200949400680c1c540346090690a0f0b0260300541c1c00420208403074201030046104c9800d0540083c03041c5494844040d0100900780c07140300c1845070000100304e00b24800c0c00000c85890006100900900740030b145040d2803400002016807040c50807400d102540345c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 606183857 1250 606182607 606182611
    0x1c0f0318140d0f052107020103150f030f0503070803040606050108090604170f0c030d050603060708040c06080c0c150711010e0c1219050c01091203090b0904090f050c01090e 76
    0xe40b24a6020085a48805103540124400c1d2070034495101450b56000d2110004824a02030690050700c8000d14400902600c403510002240c1044501c828803035000600c3c0310100b02d940051490990200600780030f4258454400090f10000b400020001484015007090301180d0081e44d40c4129a568209450b8070764100740d40040c64806a0720381c28038280d4410001c0c160f141c0880c09510720700104c1c19101403540d4000200358039400e80310010024a4601031003a00e03440b81c41428510300c03929003035030388603030405840c06240e05020016000c161600007032030944004005407011648481024904070540f500c044a054000400c058403120760f0900600a207030a0300d0700312000340b4410243c02e08100c5910040090744880384a0444440448541c90036002109030040c00a00050403000d40010940300c1c00e904401003004940720a2030009906c600c10703d00320b9040304049070b20303021181c0000d00584100b10000c1d1024001f01120f0303051040200382034503d000d00742c0703840222550701c1e82d51210013802 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 606185107 1250 606183857 606183859
    0x70c081f050615030f070311180616080d0f051f0302100c05060c0d0b120d0c0c05060a1716020d0c2102060403030b040b030c1c0f031814 60
    0x5240e050368600303030007907600302400800118040241d80e09424003a0821560b9504003a00c00c014052030b550144aa04c0e140300c1e0b41c800c8280740484091242e038510304025816402034a001543ca090079414085400401d0b03402206a60344002c01c040d030102900141519450052034034011030031001d000c140407400f1040c0d1411072410b1138516001c104040301400f80380c40510000808a40c0000c1d000e01400f03104a407080314207615140010010411190301c9aa120300545070007100281c0e100000488050784001840c203440d45280350714142e00740c610168000c0e0307044100842c40c2e07240d07a40c1000565182803070b0b4811405082c0c1c0d42a2019281c40c25603d1a503000d0707000000d05981542c4200c1c1d04240c0c8600030380604400d01070301c16441002820010305080144c1205091100b055890b004481c02c009048405016559500c00000e0310391604001c494440e1490490305042c0980202c41c480c2d80c07542062440031242000d09015081c0b8485c030342075044030f21103240e000c1140b140c001c0c201d10744120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 606186357 1250 606185107 606185143
    0x303130b0c010912050414031501092a0507020f0405220615090e0609010501140d050c030f01140f22031e020705011106091c050f040b070c08 62
    0x440d2100c240d019910820406a203552910080b0001c9100070641c501d003124541d0390b0603511468400151a664110140d82d40f080e0080341040000003038012149040d81e05032070340002c0300c4411180c540543c980079240320540e042c11f0041c1c4000e030354005c80034000140c026036407402d1446009040200f260401c03148a00d43c2c0620301030003000401103017012071490380b01340700000316040c10a44800d184140d66011280b445c3d118841d05500c2d003802d20902d500100b00600912880d410044069202d180b42c2e0001400342e04810701311801e200007041242200d900240070b0700d1007040085401070103014180c10b00d90760415260082400c0c2d10015030924880c01541e100700340001c03961030200522306201c080580030413a000010700900388142d40c680018119640040400710300c1d203c0090081494080c442003260042001c100d11f1950102e0100c1c4008503a1400307001d250410b500c203a0321400b880068010110300410007040c0710316480e006110980c011080a0b81c515900d503906680c900340300701002d00b040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 606187607 1250 606186357 606186359
    0x10905100b091305090304180204090e01150302011103040b0730020c0609040924151d06031204080102070c0f080c01081008010e100b0301050f041506050405070309020a05030313 78
    0x3c18a6000641081150080d01e180c107640da800400c59409006951038419800030f400c000c1180544110b0f07a10f11001170082c001000002403081407100341c0e12029040c031400310407000802301c081c070860303001c0c01d10840401d4881c811414010808111210340e017840c900310180040074005200c8200d03032480203550092444d010041c7c1402956001442c0b510380280d1900344200008400103211803170781c64080700c403104d00002445401c05403034250417454541e00b0030544c2448603080d0941c0c014518201c1d44208012521103801203840e184696031498501c003000304005c106e040c8190002e01600d806000c0c00c81200d6120000340114000c140700751411039000405c4011103502400ca0a640009a07281e40c0100c3e03541c7d00380c001d00b52550030310b0740303c440d400c50280f98050b52018454051030720010750080000b480d080b038150203d48000b070000342119002440340346104e5101d0700039401801d00648203100b00d080c12200a401b500310014101d10443c01c021011a8a04001041e01c00c2070958480f0f2000e42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 606188857 1250 606187607 606187639
    0xc010905090c0a091a030412050903030d02070206070b1003170f04060f020f010507050a080c0c07210f120f14190c0f290115050d14010905100b09 64
    0xa5405400000c0602c068040c00254a41000000030005d0349075140b01542c0e454180fa03c03407421040703400300a02748601407019016680300001610503042d44100f006170745400c9800080d00707501038a48028442d000c0901042a103415241d030713160849100c0c420b06d06070310001e03400ca40c034139028500002d0b141403001e0000300300084c41190550703129152401901d0082e82e48050a40c00d58000319150008a000066104072040c1d000b80e0700c9500010107941c0074106220146225110351040c403e48100c4581d0014406038107600d09141d20016502c00c0303400b442c5040c585401500b004040c514800413801c2e2285440540e401390003070a89107089100f81500d03100044000c00c6078490071201c80010000b04028400000d86070300c403584141400342c0a4510030694540307004034030b00c01c0c11200b000c0c4c45902d4001004074843d801c050403d00c4449052071703a1214000990f5000425540c44a1250700c0701090000030360300d01c1a4840360044454004024040d92141100c9501c2e2040c820495001424038950600c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 606190107 1250 606188857 606188881
    0x31e0302060f0c0d050f1902120a150f1409070e03060115050c01060e01052706060304080706021b070906060203030606070303140108010e070504050105181909060b030c01090509 78
    0x11000000b85480c4c00d0960f4030891000311017007103c21005030049107040c0008480500c0440c00c841c031015009600c4d000f1410800e00903407070060110201c107902d90400c12001a130b407005c110050310421b080d4a44407544d44807002c1c664400480d10500510301d001c00314038614884c0307844401074400900103007440d07441c1000c1c50b0110048000d8201c100a02071200c0d00e40c015083c028000149240c003519100765050000f0003000340341c031414500107100f01e080109a4a1030324080b180d4882c2085a02c1901d9999508241c0070074407514100900a07131000a9104c5458003d0344096110002c910032140e15a450700c0c070540491741180284000f43e4000e000113070380341c0360a10040903418440d10340428020b0503071a01c0011440207811000e866515111081c9404000b08401c03c01414115001c0c406035140c0000300d0b01035802c0b8450b01c040515110001600044008605813403030401e100c04011140303180c1054002842c80c0c6114502c20f002d180b02d08006588a200c41c1701c1503400081c41ea4150362034411030303501 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 606191357 1250 606190107 606190111
    0xa060b0405060d2a0801060e01170d14070204020a0503040c080c0102030d0f15030b070f050a0915230c07090501060e10020109080406050a080f19110706090606031e0302060f 76
    0xf541410801d44e9003450801d130710081006005580010901a0400ca40403244035816048001140103001c0414400c5100080c083c51440c61801c20f1020448100c007400d85510031010301940050002480c4145642c0c071000442c0b0030360281c4a00d2610070b86a1403035a450300d2003030186a00680c800e0103c400c044245030300261420b10301900c0042c0400494001024100c0d90784c1c02902c1594841c000c008410b034000b800515010032502e805407402d442c07403d001e08034154074001e81d000f40e28202201c1020b42d02800c10040140c400c071403400351540003c01c00c19001c0e480031214843c14010808002030620706400b4142c1610215141c250180c02c440d02484803080b05800e00e001190340f50880703140803c10150050005e010710740d642c00da031001e5101c005040031344042d040e42400750081c41001001c081d50592030452061750b101c08034410f4a0405000e2181c01038060107800f1a103001030250400009611410450748030702d40c505a19840e1680d1401d00002551000d000341c0c10000019032000b00010040d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 606192607 1250 606191357 606191393
    0x206070905220f110901021209091821031f03080304031812110a0509100b0d06090f02120708010e0f060d0503070f110607081b120703020a060b0405060d 67
    0x104820f0701c00000c1c09841c3c1c0030069812007080050401e5503564144a4910103007045c171103543c0340030f401d8404101c1c02e10f002007aa59244041107002c4c1007024040c898412402d00c600f42d0405009400c62801e0b003254003c5d2003650f00c014800314140442100101000c041329004a112030450b0b036661000d682c00332401d010001c207185960800304126440600640d55980607002c070310400e940f03039001d100500341c4c02e0300400e125880c580304001e103581d100305c82d4030195101c508005840300d0008800d0805002a600100340ca00c0c1021400e041201c8554083c0c5403000300000039150603250700e0b409556a000030f00403040088020700020b0302e0365541c040c4140d00114081c010348450b80403600c4160a64105c05811550080140341400c1032151044901c090010106c0d0078500d404034039502c4078518401c448c000c607460900e081d918005100e00f4892110041141d480940c0e0f26601807034020f44601c4c0719881221881d190070031800042c141072140c94814840900703085101070041e114950300c950402100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 606193857 1250 606192607 606192611
    0x6010201061d040c0824060405190e10060b090307060905010221040e0708060a050109120209060a0b0c21040302010f051602041b021b0a1514040312020607090522 71
    0x62481344c100400c101c2640703d522540e9081405803981d10b246c040150040344600d041c60180080c041e021011050721038040000003548016a41405041010a01c076803850139190220005011241100030715100904030309558060751900000e603103228072805080e0061b40b101c00c035034004d0504a2520706007185014100742c1080d5440d100b000201808541c202c0000791460248081420300820003030103031400f400d1051429040420f002d00c50a107072030b806481200040d01041d11510303000c0c074200240c0030302c0d90b09654031400c3c40c48140e602d030322006401007045603654800f2110170b000400d03102500d50503503490340c40380c0100108403016006070a61151b1500540780400050350749120b0040170101600d10b01049074042000681410803e81c0051415406e541c04000b8070341e291491042540c540803814a002c0040c84012035108511900309a544000000e000c414840e9501d011181850641d00300da10640d52240212003100080c81519040b05032408006080307a601c08072440101004200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 606195107 1250 606193857 606193859
    0x30f0606030a27030323070c020a030507031a2d090f1b04060603090f02040207210507120513030332070605060d080301031101050c16060806010201061d040c 69
    0xc0c1c1c5420009110780f41c410414035003405040680601444010180705260304201900120410034508001400a010003030410b4100c4215070b41d900c1000040e5802604441620f612440c0c0306941d80e5646600303d40d1061018005450f00d5486400c010700030712000c0f01c0301841400d590840300000c5000d0300d80ea03500d00804d00071a02c984410840d0740741039610100114014003421091000300c9555422220805051068001c0421000d03c20144110303810740d4010b070b844446080514030722a110b805403120406100105200315840005002080d000d15016140307480000020380c4d0a1054011002844d1118041000400c0c024080e0240c1d4885110102c50314510708030752154030003001c110782040110013223182d604dc041079200b1254070071010b6925000e42a10381d15464803038041488020400d4428035260030311640300f20280c83d59540780d01d040310290011000c01c1011010030f40240c0d03000400c0c640001e005c6603c140507280c1159141803840c580e81410141030605c400000344207031800603900d04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 606196357 1250 606195107 606195131
    0x503040201120c080a2003010b09010306080307030504090c0528020c03120c010e190609020f090c18091009110c070e090601120b06010c03090b031005090606030f0606030a 75
    0x1428401c10195907444c1481c50914420300c2140c2c240001d9071044158000117009600d00401201d040d1006414440c0e2501008c0b0012006803440760012800b070b00000c2190000c15070885c0203001600e8824105006e00c07140000c0031600f5004096042006074980b40044001c120743c03821410301040648182d506140095001c82e14000c8001000382da000e0340003c4290343c0a0b0288100d132410159070002c1c2902000b02140c484424080c41800f6141c550303160a40303021940c592204440205011f0b03c8410280b5209640c90343c26000144184c03101083d0b8050b038003e605c1c1564445200758130810290b40302074107024170140141000c15007a40e07a450200201c0e9103841080003030310700400030700f441d07200d00e4500000c80600305081a4480a000050110b418000034500b9031010350009081c40c084080c441c850500311450b49440d4080c4482900c00002e00881c0d894509840c820340d0f01c04d9907181010b445003010301c4a1440101da049121a081c80045505498003800550300002e41358030125000140075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 606197607 1250 606196357 606196361
    0xf150e0604060f080c030105130b04032604081b06071b0602120c0c120a1d0112090303062c131b080120071104021b01050906062b0201050304020112 65
    0x40c200344420341c041c5c1c2d40f1240900e001d004040c0d00c041484004c40a03000d407030759400ca00d0307200030340000c0a020056000701c403600f4001d0758031a40500005d0b1401040c0c1803a0524550b180e1003194480105000f248540e11180340002d480c07030240c080340d620b00420106108075200e03007801c15801180c80301d400301b142078062860045614000e101e44010315a460244003051403900481c0540a00290310510180c1c0d005500468411b031010030400c906640043c00d0350040311908042202180a07514094100f030601d86c3c141e0168040e40c090801c459241402c00811400b0025441141c07031500e40828000b844801003520324900c0309124110380e2403110303002c8051040491050300922441d039075031101408410311060b100210114414040352810401e9110000000c40c01d29455008a400040640c4c251440c014042090900300d0000c0000d81003451107180c58400584406100d443c08a40b80c804501c1c050300c60014400114280840307a910f90350042d1000d0b0401001641444148203110001807018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 606198857 1250 606197607 606197609
    0xf020c090a0501050f010c15051e130302010507031107110a0b040e040c0e07051204020616030302090301060812070b0712090302060601140c0a0f0602190809010f150e0604060f 77
    0xc1c4000c119581020207000c130141c4444039840c1045025000e02020901550380d1040259010401003050f0b500d5514482c0360035589418130210316203000400100303101058108802c00d00c2540240a10345600c10300b1002e95600588440c3c044130104440781c00a0040009030700000303c060008002a6910300b03180505801540c00040105481401c00c81000700303200000c40a00018492940c090030448001400780c014800d0004040508002240941d55001c0546220005540c00001c000146148c020041d4203e036101501960a280e400700f039801c40415240821f829900c0b40900f0040b01d600c0307600e40aa0081d1480c800c0c0490a00642442e2015009450760303c0e009800a0015007481d2000401001c0340826842c2001030501240c5c02a500100f40003210a42007458100c0c0c415803414904001e1240c0b4910820a061028019180941040c002403052401c640200810300f07588030301300c060303d141c03881710081d00001e03403000c1c03000b00c0a011402c0d41160016100203600394032607900b40603003001c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 606200107 1250 606198857 606198871
    0x18030912071205032104030c021306090c03150e13080a030204030c15170405031b030f030f061309030e0607060e070e01090b0d020a0b0708250c080c090105010f020c09 73
    0x5da8440b072014025401084410503078981e075440e01d000e84004001074041c11009200d0115500410a0b04ca0540c0240300500004002040f8405400c1e0019005041000d11088a0050300c1000105215581c44280c0703c1c2d55800c550041c030550035a10580d00368810202074060513424440400418403200e0300c0c8015103c000300101405980d40e501030240607090b2264201c04c252042004000b60011040d121581000054092490032005415040d4041d08034501140f00000c820400314400000140d0701628081c0d40f006424100c104a1809550b0641b0000e40441c484015212039801e00500409500e4041c80c0b00240c09220704824a00b040c5180d0f100c0c0da1000b0700031006000030b8045200320701c003112040b1142c148101d00303907010401038100740c03103410070341c0b013001c80d800044c005042e080302c0b8550075502c0c00b4a2410300074140e8503452181e8500a445811401c980492580710010301443d605000408620301ea03841d1000440c1d103180300481c04400c600a481e07411503036843d4aa681402030340e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 606201357 1250 606200107 606200113
    0x140301030b1b0315010813060908090a05010c030f0f1b110411120109090204060b040806010317070b0f09030d0c080411090f22080d090b18030912071205 67
    0x4007404048810b280320700012403520810014000c0d52901034481400e944020b0030b251010341d5500342452042c43d00c0e050042d01c850f00307000c01001000b8880000742114241122032403803540c0c80c1e00044410302d00c0c07100d000300401d0700c0b460079101c018040d40d940741e0450a10314048074a02c2c60086071013a0b04c90107840880300400c00c4d49203650145490301a06400313070400b503605420000064100d841403041842039030196542c0306028410764550350802e5028200484a241e59241c0d6030405c566a54004d21050300c40d081415010610548250221020aa04104541c0c60381d21040c202c0341b08001c0c082d040340010710007041b8016a01c8aa030007030300081e0500d61600812850b050902c500c0411106d40e44c140f00321041403c01992204903d00d00d90046c800ca484200300c02c0c01054507525414a0034000360410b00c011490280c10801e90300810880e031b00c500200155920740c1030f0114070408040c1e1030036a5507002401100080d080026007502c0d090050800c4034603099980c1746004641250041c1610290 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 606202607 1250 606201357 606201361
    0x150b090c0c0a170c0c010e060706150302030102191205010b0306060306040b031608060906010e1614031006030b0f03030a11210301060f0914041e0510080d0903021f140301030b 77
    0x140701a904c100340030300302101f4210004000604ea4861101e00031304c01941c7c3c0400200d03204402121801556000d0001c542d42d905000860f030940802d8113030500014540341c0e404068203054000d4504030348408414904540703c19040200d0303500000e002c1a000766944400000c241d404200801c01e00c00301c04042c09900342404522420845d006040800e5940040010407403104440c1445620020000040583c20440c440868022203611490089410302200340088400c00040c1e66080342e0554400708000c171101024445422050084294540c105211031000f6501480e14881034111590a035107a80309555401140c0781101000c0303c581040210051101d643c004001002e00310a83c2441d00c3c04524000300ca0054891103031516001e16100c0c407000031002e103200d031080000d80d07040006002a2810142e2403181030300c64800c0d10355030300c5200050034065004850b03a900b502e40184c4800b031000c0b801c03440c03180b10580d1f500020702080300d1007007000c001428501c00345000e180329a003411035074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 606203857 1250 606202607 606202627
    0x3120906020414011b030f020f03040303050901030e15010b090a080a052d190c0b031612020909011a0910020d0f080f1305070f03050307150b090c0c0a17 67
    0x200340c00740b43c100e0610100e46083c498034402440a140d05a505143c800c604d0501c81c1c4049003040941c0300c04140c1403001203400f101701900040500b0240100381d0f01081072040c4c100d81c075035a6800700f6407040110302c0074400500c40000100300030001c20101070014100f441d56606980e01c2c0000c01203042c0e9944e0401a4966440541620907108603d00c2001c0b500c6401032041206e40c5a500001d03e50b0b803072a004a280004101c1500090030041c00c021480d66164036212a00804102a150071400001c5070980e030b43c440c4440754804d9466000000e050130702d02d03a080c0305042d0842203182c140103084a8080c4803d034241d40c0c650201c504500b4659026140c0382442101c041c0014499603124814814518204500300142c40382c0c6d01d41c004a884000710100c1141d00341682004d0890300040c4032610014404014864000002e0080500c2100441040002031f5035100446040d000d100ba8491400310100d84069070319405001d101707038000140d580041081d9248c622050a0322940281920081088440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 606205107 1250 606203857 606203879
    0x5060c030d060e09280c0e04110306010b040506090402040302060a0c11180a020912010e0708121201120507210b070f0e190b0a050304122604031209060204 68
    0x5000d80c1480c40c055003411004c00d074407051249401c80c81c000c0012520032000e004a080012580c2d0040046408a0b44030400c803030000104650035115206180380e91804c0e030400060150482e0f1a4200303550800b4104820403000d5403142403074560003038081c0004000340e070300e9100410320940700c5e85500e05008078038039212a07050035142d04e1511a450804030107449503c48044250300c804030030310060b5102c1d98500007070754a0080c2c0340307943c85541c41d100090311005c2c000100750041d03e0101080342e880401e51009007045222f00e001c03002220074804010003c04195a02050703c0c6880780003030715151900c070340e00540703542c01d4603101032502a120340240342070000341a4019007242c2c4600e8100100e0700110006044101c200030b000e4011020481d10a100c3c16842c4117800149c0b0100c8205603680802a50040c0f07150001c0d0b4095440342d25903212450b00c80d02500fa140c2c41e2440a802c450f054800e088503a800b085001407040c0c040c850a5004510000b10311f1003601d80031481480010780303c038140030340c00c90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 606206357 1250 606205107 606205109
    0x30109022805030c070206070b0106030c02011107120c03170a06030c0806270f0703050309030d0206190908041e03030e0409020117070e061201090b0901060c150605060c030d06 77
    0x8505060414070265150b0100450f58000a01c0690650700c911034070114840340300c1d00b003001c3c3c5448503600c00803c3c1e4644c19080304840f980c0a034002c0c0120075880550010764803c0d107030003d210105d850041e103091405007441c00102ca00074105242400035900705c618420004603180c01c440c980c0c5840074400c120711201042c015048100c000c04961500d88002c0d851a000301ea260162821803000c5150060b8041001e2040a10b00100b0f070340b0f1499807440d1069494202106240c031a000c0c5035403800d20342d40700003140c40c412520070709180ca9042425a401e0000c0c4210f00042e82e4480040002044501c410401c0b40520a4200b004000d00352441c100100300130154482584640e007000d070480c000d40ea204050003000d0f501c2e12518150f070b840d03100d8143c840000c000c3c415900080d000c2000c0030541e4845110302c0c120f0304075500030300602c000711040085400c002d005170340212f0740381050000410083c0111040310300a410002520315100c1d40010015040989031803600d03400024080e0856540f4003138a8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 606207607 1250 606206357 606206407
    0x102060106141b0c030a110f040c1d031011090a081207150e06070503100b04030f0b061207120507080f070506030c27010f0c020f010e01020a060203010902 68
    0x4a0b401c0c44902d00c00320610a0400c20204001c80d041043c41c01d190511001644c3c5a00400722448a2010300c1c0c9885035180d140e051a12038071084840200038101780c054a080c0c242c1c43d81e64115118171040641c61031100f40c84400f40c0500c59400070311071140c00d40c440c415400c41000300458030f90341c00d10204a03000c200d6070031404d019042590100c011486032000c0da10069400a6442c1040040c103a1101c000e01180c407c0c7c40043c4680300500c9142d030b40200c000c50050750000303a01d80c2d50715200d41c1c804801d4465440010802c0034a92400e2010500d03a803450f45e00024020104502d00801081310f03490158240c00030340e04907080f07407481c2042020802000c1c000340a15005081d071454050b4240b500d800e050312940c0e020f5200000010a0203002804448210000c00c0e802c001303401501d540b840e60340d0a0000740c140415041c00f84450054060044060425401404c8101c08802d02004549042225151a0552080c4001040068568000345001e1b0103065401070b101c041000854074540d41d214510 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 606208857 1250 606207607 606207617
    0x20a02010912032f190f0609080702090103030f0210150302220c0c060b0618060f0d110c010b0a08032b0f0c1413090c0216030b04020102060106 63
    0x1040141d03004a007200c2100c81000c821101041242019219941680401c8002c440c0001d001d0120300d01100464941c1c1d80740f002240c030b01d0030541d000c1d0b014414041c1e0014184800c00c409600c00102e00d508a82001c0e44aa1855030402d0825800300d1181e4400707820450120b2008481340d920254100104400c08082140911036485034008882c124950742c0400380c051642d80102d48001411180114a007286d8902d00b00510810400000c00600b1402070444140c2d05003250400c280c9010415150b0b0520480390300c006c0c0d40f00d04c008000a0381d0040c8544014034605010100039041503200305025100c3e600c640d1944c542d5803051f2a42111409500c0912980007181d040c8841c0c0000010745400c2514a001d4000c84c0c1e85900b43d401a000c0540083c0b080300d030406488408881c101d0700050010b080580b180c032050280441c10f490a03000c0d0302c00040402d11614820007420013540c01c041003600d464010760301c1040000340c4100660079190000d03110f54000409000c21540d041103500e00518280c944 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 606210107 1250 606208857 606208873
    0x6020c060702250605180f030f030d361103030409020304060f06080a0f111c060b0906240f0c1c03141305120c0f100207080a0f2a110102 60
    0x3014060340913480c450070070391416824021b030303546400005c0540048014120703142d059014089036a65800403110000701400c0201c3c01030441086002004c1d030740150607050142d4040c41000d0b207610740c81c2d200e080e282601000d216645030303141171005102401c03045001583d0303440e05080400645400401d0000c6007458140204140b42d0301159045ca40f03a44412152030b0306044e4280314402c401031500d984e901042012300c5020355615211010503040c810352081c060140302a00700100c0c1d400840d05a40c01141204020036040d200f00062004640b5040f200760510040e001c1605241e041881011311030307402440c284240c0c0c42814200c8600300d86626040c0410680c5030b8508004400151992072514030001e04081000800c2c0a0803c000d001c14038007076140c00f10058034960313a0760f4020901c0e16500550740c1d0030040c80c0c01d5008482c4025045019245402c412900846003180e00c815800104080000800071651080062407000740072000201c0140d07210303003002d096006049881a0566002c004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 606211357 1250 606210107 606210119
    0x2102010b0a0506090112060b030a0914060f07140c030301060302040302130614040e012912030906030c03060a080a0302060a05010e1e1305070905010602160f050d06020c06070225 78
    0x1080300c040385000c0c6001d40c0c0400a802d0b10902902958100208c02030b008803c2040d44500ca030320940781c0500484600e1582c4901049103501c4a00558a804103440810300081d0183d0040a051050500154280d40b5092001c02d2a501b103030002e80080380002c0c0c000404000b0b505c0c180c102641c6d0500149000c00641c0e20f000741c4d100b00400ec0089181c041c40d110010301c03131a01000c0d03100c01c03c00380c80307500440b10510306501c003401125100120703039119908030b11010790150700c00425580c4607900544528079548a5140010440d0001480350f98000d0211101048a1005000301d00039588290001c0c6070500b0540e18034010340c0c1050b0051302083c00240200400d800e160400c4400509070a4160911501c88090a1405070040d000c050a50302c0b40d007100080880980e4481412250070707a0944889010000000020310850b114401d03540c0d0000105012a1800f48158007040d403240500500d03110404940b45e090141c219629405a08910220400c0b4051000d002c0c3c07003003610800d02519135040c56 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 606212607 1250 606211357 606211369
    0x20609030c0607030903120203070306180209060706090618080403060b100e0f01032004090e1504170d0603080310081c030203060a050d0f060f0c090e060d2102010b0a05 74
    0x10703d0201056181c1c2044030502d80108000c6542d584910000c1d0340e2458000000b40181145200d0b000e108940e038082c198060301d040c8240c403103400c001400e191514155440d80c0c006403220403c10fa032440c0d13032202400d0bc220380385408100014410f42c0b6454556180d810b00c01c0440340b40030642070042d0040c0001c0c00807294003100540c001d030421910348a2000304030004800400780070700d464000d400544030000500c04844060421110349490510031a50001807050f100d02c0b0302da60b40d030381e08410b050100300011101880c2d40c2444c0e0518100c00d0403c02400c0d010030079200fa651084c1c400480020030320a000140030031002c083c2c200c0200400138054000d07640c0f00711a4902c400d0b0000c00d42c0c0880030441555604080d58010710000340503084000f018100b80089451050b002c5481d20f29141071452030880c030b8041c814510b142519000807071403806d0000100b004d001804660300c031507803d40010014000a001138106074414180d040d4686c030240c000390031a101240701c0c91090081c41010490740d680d078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 606213857 1250 606212607 606212611
    0xf15010c03051c0e0303151203071a0414100501031202060105010f0e03100f0e060f040f030e21010510060203031b13030804080a06050a020a090e060a081507020609030c06 75
    0x540103400f5082441e071800108108000c0f1007150000105101c800060907205a50041003255042901c40040b420340c0d68074810b204c0010401844d0039410750810032400b8845038482e0140410412030b45902020508180c0c00f01c80003540507130360b44010302c1170181458004c0c40411081c00205595410322001a08480c4022200c01c2005440c6440c960300b138a00703028042c0c86a00d850418000c42e0008007803100602840f021551719841641c00081e01d004c00025140d001c2d07a008908041b0408690320b0840d03840422050454120b070060188288401d81160f00100c46030040c1d000049a0409003400110003013240d01880c1154402d00030b2040f50241884102d6907580701d040d42c140c2d10f0f96842a940c00d6109258001360030301d0400b10b0002030301d01c004501c2c12204c1d84140c8c4d0410080d603c14010400320301a0280010000b100e1000034003c031100040341c01e4100c1320081c8004030b500d135a007a000340f5000c00400e500307042013861824850015010440c154101681c00043c40c149040b81181340d90718540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 606215107 1250 606213857 606213877
    0xb0f0a0e0c0f0d0206030103120807020a1205030a060e0f10060e0f041505090f0a0c050412020405071803112e0e18010603150801050702072306030f15010c0305 70
    0x8484000e8043e5940300880c0c0459a0180c25282c6a40c6e40c3d04103041c1d520300701011080403400500004a42c1c504c0130032a60889640070511001c22303045440201c44540004000d0f03444599207071004101807080440d490b01c510280c1048400b6850003c45102c51000503502000500c040c01e0714206180da40c0d044821240d107020b490018240b4000c440b0203403255441e80c00350b0b801c59006030a000b80001c40c0b41c542d9100f07000e564400c0c01500c4503020215128411440342e90540902864a0801460650131640d0050304070320301a00f04010f0030400e044000400c0d030089030b200c00e00c080088490304008800800340b0b1159103900f03844883c000d03282940c0c0c00c03906001208200c00120520002e0382c5017880001d800d95140396100c52036840c0c0c100a4010304040211b503113024603510000650b800d05000c2d0783c0c4550382507800303000d180c3d00d000d041141d420050152461a1203c4c0b0030760290319100d1101440c840c1c9000d003080c00340ca08004010500004480302c1c040d0411111014003400700b5046402c4807080302c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 606216357 1250 606215107 606215119
    0xa090605041d060a0b1215090705030f07030f1d060f0615030a0f0c0815030d1d01020102070506041b0b070209010e04110a0f08240105010f1b0b0f0a0e0c 67
    0x903d2200007210703050b00f50402c2d40101c102007094290914015003240c800c0035034440e10743ca0f0074420030822601d64801c0f114640041c0040001541c0781c00003441d001d4014900b41000700d0541c40380e1a80c5020b480589411240d40782404400e803005110410050350400c0c80c00103070705140e00340707030001ca0f501407070101c20108030100020105402c2e169030f0748100241c2001d18400c202c1680c0313404009045100c00e44000c8602003c01007039100704d01d00450b807c401c92045444040303504000a00c42451070313101d450101e05555090140102165051001c4c603c19032183c0c41044280d0312400030300b20b286110b42c0009072131000510624005031101150181501c101d00b200ca0020759547c030b043d8543c20000c0315034681240302c210000030608680c0d002c1005840402040d5541c1d5024000540d180b8802e486406070850f12040040110b940500080c0464407458a824001c1c61640304001e01c0703a1010140c2100e0340443c0d00208080a0790241c02160800000001440041d241c081c1142d80c5a40369601d4500c690f03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 606217607 1250 606216357 606216361
    0x6071806081b03190e06040201091508071407081c05010609030803070c080708120a050702030a02070315060e090f10090201050a030f1e1a240a17010b0a090605041d 72
    0x110000195a00d00c0c4131800c060000318001118a6210b0030706442c100d0100762050300105160300c88030100100b01c85a5a41c01001c0c1e40d40601c12642c144400b0703012042041d0070040500424039081c020111002c0401641800c0c044c5e1721108000c071b5405900c03090400030307034180c18400205d608044980240c0e40307191021003100542001c00c1c0343e01c00d0300c0c4c0003803003c2400503901d811354000030021446030400e010100110744c0d81013010781e04d91050003061001600701602c203000040c0504190380203d039440e580011030320348809420b200712200341d55050540d44005070340d1502000030000c07448041d6402c41c0604c540801640042d00a0281103000018907480d44104e650b1a815540200d6002c51001004201001c032851030400420688019010140075446d00d021582420742d003030580400244140c040305415165075203602d400c218580400c1084c0c81d0810241c1c03041a10b031890103003002c12a10703540c030788100501614406895115400380314080c0000c00c040c2c40440c42015038420a2080c3d80d0640d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 606218857 1250 606217607 606217621
    0x8120c03010b0d24090b010806040b0f0607150e210a14030613180c05040510030f060e010c0522081b130c05040e010801020c03270306071806081b03 65
    0x15003061041d81c01c031104150303400179510005410488426600382ca84144a803038038130030b00c402c2d030306820b200542103a00408034072024240000106041030050407158084486500ca01c0290380c0320b000c2c004a25030020710301880070854405e0302e07003004480f920b10510340803804c0c43c00f9082c1101600034038050752010000400039203034021840301503143e5900800980c00e41c00a101e902d1003844400351140030b100d850114850070540308043c0207484400b4001d044c4c170306e940e494030014190703500c0803981c1d180c5940206002e10003d0280000161642d116651940c2186803030460b030840e0a1041205000e0081041003a000d000c01c14035802ca0000102680324107412000c20500307114542c6141040b0324045512400c194044c0c0648160348503140c0c7c3d0402ea1b40c3c0c9010303c0b804c1c4c0c003401200740358079017040114170440e5400c000300c803100c107200380b0700030040c4480080000d013058002c44040000c60f035004c00040701c114590380304401900740340c20500301a05083d500c00f501600014481d060400e80040410b0301 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 606220107 1250 606218857 606218891
    0x11071805010e150307120206160c0f06210c0504120b07080f070c0308060406210203010b0a0617041106070b07030b030d0207051e090106020c010206010e04080d0b0105041208120c03010b0d 82
    0x600d6403074180811014a8624103060030480a101d504030030150b05202145080c41040d42d1180310710301c0e101c0d6007201040100e00b0370080c48214151001d0100070800052070142401004c001c0078020000b410781440c0c4942c02514401e4010310681d044151401004041d0750002d1901000c41e4051038991010354030342d008140100116000703d04070030034003c0c0c0c080210745100b66440010b0b209400074401151020244150f40485004900c007264048240520f44103071b503a400c3c0c1d409800b42668843c0a104000400c555610882c815203d0088a00c10803410b250035005041c0c0c01e541c141c000340071821f62038074000c1d1520310074000c0a1268008180f0044100c0c034489201c001c00d080244420060b503551031020756940442c00105001d8050040002045160040c10b203110b0343e0408942d9181c44040c1320b90000505848050f203051103000d00001c5841803000100c0c01006200700d484598401d03005105080440f0001c020b400044010001030117540030074801e54507442100600070070400074034001aa0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 606221357 1250 606220107 606220117
    0x230a0c0201180806100b0f0313030e0607050a06060e060f1e19030318050f010302070c080115030b09030a020307035301051011071805010e150307120206 67
    0x482d00c0b141c254041202540800e28500810400b0304004402e40e440742d90f8030300c0d401182540c0041200500008e05010321800541058600c01d02d03002400e112480d00103519504414010360700c60b07002c43d10305401c20000740704060207004001a03a0080d40f800c040011a0a03800220789800741d4070000d04250300c1ca030709042c15182c07004010185161400146003103501014903100540002c0c40301f04001e1410020030b01c00e0300a54001400305441413802d440107401a50040504964a0000c82400204680c0a01c9414010640101ea604030745140d800c0140301c54030060708600c400c0d00b0400c900c0c010182c0000880303010039410b041c0415420b44903041805108072012841074058500c094003e00c2d000683c07188451a01410024070f407980c9204207514200100b4045d01c2e401c6004201103408650082c6004603114288104681006407650341c10145400074001d500360329601c0308018842101446102588100403d0441864030f4010001966603441740c8103001c4004501000b42c000d40d04e407602112 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 606222607 1250 606221357 606221387
    0xb070e0a0f0311030d080f0411010c06060603020301060f02030c06042a081c020d200120130522150b030405060609070504050a090e0309030d050307230a0c0201 70
    0x301c2515030301d061640c03418981c43e60540c400d0241c4110390340d0150090001c1c1c0d029450613022252641d5456440c0b50140519a488505100f11184200c1c0080d01c20701800b0050301c6c0c10740c6c0158403545809406807500215030403107020b540084c480941016030014406610641040d2244070003451005850320740015010300c0d1001014160f004510380c3c5002950f00c0c42c00b01d542e0150000c4003443c10007245c4440400200c08001155014000d000010041050f0001d050745400010344a940304002d00b440d614085141da109080821181e0030030580c1103101c002007d05641000b5041792040c802c0e041e01003d071080c030104698807460b51164403010000c80021b060031401480c1d80e81400d00706039654040c103e6aa41c0f0038080c10000600c0c15200c1c0b0306032411144040d00741c0c266681003c584001520f42400712100701d100600c20a81541d0b002c0000c400c103135549807a219034a080800300107100100040c80c10b8071062a004d4682d40080e21081214203051003460025004a034030710040b15550b0002105c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 606223857 1250 606222607 606222629
    0x803040608132a1805011202090705091c05010e0606030304330c060b0609030c040e01111b010c03020306060a03050618150913020307030f0807020406030624030b070e0a 74
    0x62070000fa100c481c0d82d826118107500d089406a410700c600c0e802d07210709008030303000d080c00201c000c3d0050901c03544413034210040c0e05100e030070a406134012940008000980420b0346503d440c2400038440288501c1c280c1d0750385500a44424a03103000440c0d602d01c03d07445140d003609441d00c421164051600c007210f004040c0310480d1481c487c26100c0090100f80744070001c0d20060705d8110703800160301e80501201c0840302c014008d0801001458200001000c0c58030500b5459500c0f810360b0300c801a9078400070b12001c1e1882c05040c0710a0050303007d4608588044080005061041061201d981c2d00c400503503101c0c3d03450385804982c0d540c441002c1000f1000c04498603007000400d00a000b80843da00314908004107050360115651303a201d04080011014110020f501501300340300500100340140d110107840c81c002c5992624020b00340e80400d0841c1e6240e0310a84016607100104400e540744041c612030141400c0c00700ba45c5490444d100ca04103424054040005d01c600310540712091b403a40e43d4510001c00060101d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 606225107 1250 606223857 606223913
    0x4080d060803030a1e0c0f18090c27030507230405040804150c110603040c1d100602030c0615010903140106050a051504030303020d090506090f07080304060813 70
    0x4400601106540c000001601212440120184d40700c0d0761024106551802c800001c9101c1c2551191100041e6035012031000c1000b150411090042046400440e6032f00d10007101a5080548100150403c1c0000317544849402c201203000003600c03a041e224010001d114000a070b54160345900303040c0c0501703a00642003008006c18001513070060011292125070010003007503c40c0c421607402c581c0d25001031800700341c04400c8505080400140d94064852103403a820251603c4264211002c80100c00ca1080800b4040003403000101d400c40c001824140019810801451030301d50f01c0d020020038a00e0400e4402543c0700980c1c0c4a444650001c5400140070440b1800a1894901038031031030150701d0044102d031500103028240b410140c040c024204070703030350305140c00c6960440c0a90f00022415040780c0c1ca800501002c20b00502a4a0103904a80002c5c01c0101620054908104255014840f1500180002c0007201c1c3c201c21010340c80900c1000e051640e0800745040301d8984003001c400f903070702e40b03030010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 606226357 1250 606225107 606225121
    0x516050d0c02010801080c090414030903191b0b03040308072015090c0d08030405120327030f04030605090a06150f050301230601091823010e04080d06080303 69
    0x7150080c0305000303030f0f2918020b0f078850181996540c2501c00d50b5400c43e01e010f0004011581e405286503c042c01802035907d0001c12200180c5040042404000f82c0308600400200b0072803001920b001c100e410500412641d03243c80d044010311300004201400b406000400940400c1c4141040d1080000610030941c1c00c11002c10300e160307582d5021780d8091000c20044086440340c000000d01c0c0580002c002c00501d0b8861071941c0c0c1c1030054002801c1154144252424400c100002c2d0015503c11004100c1950407200c540c540d10400080d4001c01d00760350340081066100c408548021075080e81e41001c030108107070716401d01445c91300403500405000c0074a8811400c00300d0045107100021203494116a030403854a0720201401c03101c03014070300d24602c0804800c008041d0007120740c0560041d4141442d07a4039950340d103c4510400905801c00203001d83e15a01480c104010702c0c000b889490024040421540c106402a100c048000d0130142281c1c0c00420400c0701401c691b08400c2c0600141c0d000c4c1c0703880e81010302d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 606227607 1250 606226357 606226367
    0xe0c16020a06050a090f082109040207030c03030b2b0309050d030e03070608131203020c30270d05242802031512030702180411010516050d 61
    0x1c0c1c05100080c0700c1031001400146c8402c0b22400d07262554003411126481c0310a80641c20a035258407403c00900b400400301640c0c8500c0030340251400383d180c081c80002c813458020105d42d4422803070b0780301e94241c000d6803000280181501040c1107502d45003150b580b4190509035103560041d40702903030003070b000200001011752000b416026a54240d08403003c0d01d4648030140c3c0c03c44821154900341d550174404190115060500c809282d0100d401c00601d4014821849424150301c81e0342c94032411031024003281c1c5480c095461107107401c84911800e08001030032040a40000100c071200a0b1903206c0d40007529203079034900103000060303449800c03140d01004001020480c19110b07501c500101c1c005400141c6c83c10312030420103582101358084901003441c0020030708020342020300040244028183c00d0303001904d0b0a000d9160404c1038500a60b01e80c0300a104102c003060f080111210301406400074040003030a58400035180702424201582c854100043c465036411041401820a104084400d16581e03004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 606228857 1250 606227607 606227617
    0x90f0706030c020109051b190806070318121106070c020f06070302011503051b01030509030d15080a0501050a0b012a03031503080306041a0f09060307030813090b04060e0c16020a0605 80
    0x555a1100500d00c640000201c540c00c9d206d070400782d0300580f0010740300314801d60040358604210300551101c0015915241000300e58008200c010524450030014030709000c0240950116941c40c0c0801500c109502141030b5011490605020f4080403c2d250200340c001e4001400040042c23100418450341c0e4104580d0303601c81c45c4460102651f46071400d480c0da5120f40500703840351010100a614142c00100b00c03200815001d402c00702c1101030076001044161060200004031401040003080340e09140300310b4012100408043c03814171803040d41c450500415601121403444443c2c0c0c2c80a1149100d042c190040d2211800940140841c10f102004115075840a14001c240a440412044a0180070344032603e604180041d031018204040440c24039010350310640c042c8010b4180c90207159030b5030700d1721855041030f0f035a2510464a000180010b4010740f03c0c05070801340803031f000c1c081d9510b46802254010000b03084c0c00c401c09800076103030b95403052030000ca000e02c95001d000c5a50311544d49a0050564000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 606230107 1250 606228857 606228859
    0x30915060a092703021e15061c02090702010603061503170a02030c0a060603060b010c05030f0a0c021003060303080a050c0904020d090f0c0501030b03010603171605010c080609090f0706030c020109051b 88
    0x900003036951406c0040c003d09803146000c040c50441d214501001320034920150288810300080b09080b0050b11840182e501804158001080c0c2904618101c3e0983d65003480306088032030155010070101c0c0e490341c0c245e41c003504001112669040354040490440c812010030b16624480c0080c804200b0416601007000c0300d00503102044607095040044803003400403900601070b0351003404525480201e5800030002d0b554141000d515002e6581e01007012000481e41e1500440e564210420a25400c02070095224071582400c2040e858070300300c90760303450007030452180c080e42d40810342c4d00200324554008c41ba5690008003625240e942c81c82c1001042443d80a07a500007802c054403450725040500820781683d5208205450002c4400204107268001c03103500024016084541d2003c03520a215640c01010290b4940a462410300e05200200401500303540701e690000b400310200c1e01000c0744210544100c0d1501044844140500303d02600740d0030005000c0c1d0040f0064000c401c003020620a02201c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 606231357 1250 606230107 606230143
    0x41103191a06061c0f0209040f0204030501050717010e040206040308030a0e01060803181512040818010e030607301a01030209010804060b04061a030915060a09270302 73
    0xc2c0d41d505100c11801500b440e01108283c03481c2e110100d03103103074029540d4450600b20040c10240658005010703114000b5620203925070010f81802440003c0c000c6c0c075030084081c10288080d06105402c2076101105100326007064445401081c115a40d14048800554001c0d041e035031a82000012a00140203200007a2815840e0140015840c0d0011003501c40e0009552200142d00300c400b028060103025032030f104622084108000020101190032507030050340030340581a100c00e0500700401c03621070134a001c6414800c418049031503d40d40060000d51102461501c4104000191950b121802c0c0282064119280b4901c6840c85002c5030f611031503c00076212003801d464021600154101e101d0b0907086030019442000180100d1640d03041180c074010003a02c00569543d070340c07a0301e01d150790200000b08107241002060182850040003ca00500701034503185169040590000b00381c044680302e142c041c1500c2f401c070704944180d501e0001c4011085000d0b83c4040070b020b460000d455441484007090416 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 606232607 1250 606231357 606231361
    0xb1207020a230c0901120303020f0c0a051b0114090d050109080a030c12090b0c0310090603240c0509041d010c02030a11010b01020d050d0f09210302030f041103191a 72
    0x41340184980e41251040c5c0200b0500030800c2c0c6085004e9480078200f904c01003010041c00301d40342d4042188988580c01031001c0c14158071859010030182284451075410480180c9520a41503041421280916070460368080c16900c546040d0703025041c0d001d40540450740201c1d030340010b00c0e0160041e41d886072069850510300c2c0e610b00d0309502105d01d903600203000320403650002501d000c180002560402214540c0c3c1650503038405640c001d6841d9908203d960003400c0701d080e50741c640c0801c4440202c0c0355040040c000a4040c050042980c0580f8071800d00c550744030384540588044c0700c402407418440d844028469888900d202a5496001e0040705c40080c445001489221a061051800c0340c82c059010b0074061803a541c1c100c13429040500310002041d80c488000090b2607243c858141d410344603850907a2042c0c10a114045040700c42c49000f414180108200042031200c0c04210380d2042c2d01c43c0744180603e4910001c44c1c0340000c00c10003040c0e20f4031360051480a2202000030b1100b01412903000081c96 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 606233857 1250 606232607 606232609
    0x3080d1103091905070e0403090f050607050c09061201020d020304050606031b060d0f020c070503070b0c060c030408040e070512060a05010e24070f1103070b1207020a230c 75
    0xc0c4000c4420078100e800c010f690140409410448522640c00341c0e040b10b141d01d03100c202e8040c200030251821070110300c20800410013200b09401c91070040c641101c1700c0f802d04c0c0580d100d264540c00070701c248034810b04510001a01c81e42ea22915012401019002192907480e090400b000940c8251001d81d020b214000000d01d403441c0009030000301c00d00301011050340c0316a00040c0304683d0001610100465220422440c1e1155188090079003004108014648a0304d000181030521101da088030448000401c00005010701c00542075400075044107907103940b03640360f081c544618000c5401c0700e40e000e21008107000a065000001d4100100c000329910001d4880c00108910b00540380315081c040b41114981d1602c2d0f181c000000c884040c80000d40816054408010380070a510503502169011418091201840640324100c0c1141d40d0a030010006182095148282402950724503000403800c4800150112300c00d00100c0a0242d00004a101098092640d4070124150312480800c2d40301d540342e0300c0f2007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 606235107 1250 606233857 606233891
    0x60336060a181703071b12140a140f090306160e04150e1306050702030c01060f0b03010b0c010f02040b040e090d14160b0a1512110d03021603080d 64
    0x1406501c0303e9000b800c040340c0c90303540d59560401041c010034082100d0341c00504c4403000b020602020f01c11050404004040c40f00036051404110114140c128180841103441e500040110074000310000310a4a43c200310410360400d10420100c550035000b80c3c1d007402034100a04283c001c0c40780041d102ea02032064402c080c4012a103a407070300110061642082007101d40780c110303036050300082006100440300582d07031a02010b42e0001d481c5100140e10014541124080a21826000d07041d407082c010401031a16540394801c0c001809640d076100d000040c8568031020035800482204d4107500195129079841000c80f01c1d0f500203109042c03c640d101c4001410200000c24543c4140c11640c0311210364108100042c4c0403a00521403010791601e84552082c00710b0344103040c0d2442640d05210200f40d0780c0701064a0540220140e026034080107280c40004c0000e044000079500b8030381d007529084c2c00c044950800324a0425451400c01e120260440301000b800240d50090989441c14601800500d81d1040f496034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 606236357 1250 606235107 606235151
    0x20303071d0a090c0c050607110c040b09040210090806070203030406060e070914150c1c11060105012307030e0114040f211202030a03150302060336060a 67
    0x250003038402c03000f4482c844403030307100f01c48800040c500300b800142aa40e40324074081056a0240c007262a01400464121040140d81b0782d41c80195828172a8204800110740b00395000b4000030700c140648130149810a100e003480ca0024418030088132401d042c80040030b0f4403035005590a442c41c0d400d11402144801e070224442d40600c100c0e6032807a0403a482c0c01d80300014aa1094102d45c2d00995094070b60003020385250160885070f004c50050b040350f0a2100e0002c1910310079610b400c007404408090909440d0010510700d04540082c20000381d0031980740040f44048036941a00140540042658001d06030b00102c0480c0008082e26075584605030007107001494003451140e5541d6200440303003401010342a60382d521000d8444000c20400540580d24012650610b00101340140d1000c100ca00c1d90315894001c0c2c60fda0f0310b090400c01546411034010138101d11004040c01441050340c003144c4444140d0814001001c4e0b02403400811600b8242600c684455080d135103040e00c0b90a1041c1030034400c44a40c8480 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 606237607 1250 606236357 606236359
    0x617070c05151b040e1f0305030a030504031205010b191b020607020303070204022b09021e01110f01140901020301080a0f0804050405010f0603140c0306150d020406020303071d 77
    0xb029035841100e28500041021002400c3c0ca142c200c02d0300d5100300504080c1402240031442890a42c541da40d4041103250095004a6410010808030320040100c031041d6002c0e01e804200c0307503994101943c0c04514020841c030b50398540000011843d1b000c2003d4660310b4804940c14020845040c1e04403405d4081600401002540360f404400515140300100415840541900d050020310303000038080f0303000080b5800150f00300706407401421a1000412041d100300c0c1d10108294030454010030803c0202d4141e686540034541100c00b51a80909084140c21015008651a0386211603030715010b411182840c4d200800e00c0e50104030784440600a80f4160f40c5460700510420303007591a06003410741e610006890380c090030003000c54a900c9500406011341300d042815030505160480007405c85114480650495060700240310b051410f490880340c21200440300d0902d8201d05040c10300e103a2180080111003a0f100140c0020543c1c0c010024500c81c0065480310300e0000c3e04010010f4074a52416040c2d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 606238857 1250 606237607 606237613
    0x30a0c031a120f060108060711030a0f0503060301022710080c030601030c120501090c0f052b0b030610081e031e09030102070c0e07030608070b03090f070617070c05 72
    0x4841c450612507141600001c002d0308484100d4124443c0a003000403c1e004081d85800840c100048190800205050803025600461401d412240018464809122080f040020000c0401e400d990f0940554010210854400c00c15207010302d02c07080b0600c00361103001c1c029004a40340b0440b20b40140300c8035204d41e00707000e0420700d11b64690004400411038050a4000d00030070098081c010412403080e140038044e070400000e00346082e10806400c40c0035002d0580204581004200380740000300b81000043c144906042e03020355015a0008007901709030140da9011720400003005111001d1945245c00ca40c405001d551a121712442c1a00d070440400000c1d1020394010004030200d00181400310740044443c00400d41886031a000090aa0b03004100648a00d9641002030000000e01580c083d040102400c0402210b407a000301d2a80b9002c492003003030400f81d4003000140170004140040d4511040b01d0060f0744000c2c0c0c031180080d11240501d100003800700c03600d02c00911350600440c16003035030355002002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 606240107 1250 606238857 606238901
    0x32007061206051809070f0b030601090b0c1e010e15060f10020616090b21070f0c080930100b010914120d0f0318020105090d03030204030503040902030a0c03 69
    0x41640054005c1d150405520035000c0020b404070300002454054081d0400c0c0c251369080c0b000004158816a82144003c100304000e82c2c051050002000c00c820000b4400210603900d440f50014010b101c820344900a60154240d1200340140520f0380510852007110340036502c4450100703021851003403900440141c2d101802041c428040d54449004001081c5001d0760f42179103078049240c0942180000b45c11001205220000030700216415039806805480d040818402d500c00003450052904006808a0750008608075251110440b580031240000c0c10b0321006045e000b0128658080800414082e0150300400c0c0c40440c0940501c0f09154016036a05440c4c5080a522826500043c0b2603a40d00600810000d91050020f010ba034800c0c0404e512114140d094200300901a0742e81000a10440340007001c00d040181c0e0858107441d01041c05071103074600d0b04141d240540091007550800342a82c0b00106000605010640041d403160351880e42c00e0161030520a4280c0654204591401d064503a0100e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 606241357 1250 606240107 606240139
    0x709050a1d0d0c0816021f02190b010611010209030106030c050a061b020909190605090d020604050601091d0a151a0901030312020d090609050d08100b0703200706120605 74
    0x201074051009800400310084405e80d00045101c0710200040041c0459480050aa203405001510880d00c4615503616003140719501c111014005000d014140080d010031103800d000c02350f05982002d003000d4000c01c14a41c0300d0070040004900e41c0700f034900c51100c0480c0030801900c40c4070764200401c090760007400e540300ea541c02c101023004003c186402500c20210303880001074000c2d000241050143c1c000080e50308151000ea401e0800904010080d0750008041c800001e03000120b01c1e0458080d000001890071102d000c1c403045030094203221201d442281352507000e01c0480b00b408844540755035410000c00b41100c0c502400c003030000c044240d0094510340100086809080005200751100c400189001d8940c0d510404607042031505407106035071402c0c40d10130000c08200442c41d06045042a02d4140791405040080403210300405060703801c0400c0705030815004c1c00d265032414800564599480c4520071546641e1700c0d0a105d10000118855407002d000090392040a0554001628012288440f05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 606242607 1250 606241357 606241373
    0x12040504020d0207060504032001060302090c070309030807030816030902060d05060301020412150e030903030315150d0f0b061305010c0f081306020c010509090112050709050a1d0d0c 80
    0x15502c0000d8903020809200040c0322840b603c3e11444c485e45030003c280039600c0c00c00000700c90a00075050315a140c224148050381c0e4061005600088011106a07106a545412500c8136010351005202200202c0c0d00010150080ca01c1c512030009803005801c0c803517030807100b10281e0b0100c50001c2e4220f08104020080800e0300c0e000b06600c00c1010740003529103943c1e002c2c10581e0034020b080c00e40316201040d07a800422100d80c0150f0042d440d2a500440c1011892000a0348030710028010132610300b41c035411084079440359002401d00c641c0714094642ca0f0008407108038060301f1a000d8244c034007440c065004402d0f1030102c05442d841040300109103030182c00c0100540d60031009070010303101c40a8001900e030000e015400140601481e0780f40d26108603160a5000c0c1c50114510b584e14140074043c03200712815299803440c2e50444500035503000b002c50050400c2402e040854001808940c108010095007280707e40103c5200d188a00c040000704006000542d140c95241420340001400481290080344102d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 606243857 1250 606242607 606242617
    0x601020a17071112030a02060627090a0f0819090602030301090b030a06020408150a0603121d04050f090c120c040903050d0615080108030c0a12110a0f0b091204050402 73
    0x403031001c6160f0069400081c501240720041326660303800080c80302e14203039040c001c041c1c1204c001d0b01c1182030400310242d00c0300e10900e495002d0205040002c000307611030108008107010150002c2c1f40154561983c20030010591050240c800b020310402d030340c580d00a22803c4040704407042030b40614256400c0c46094805044001090355140c442c00c500c0da00401c54620040c40101a500300410000005a41c0752441a500801c8240c1e05c2c2e11b001c1042002c04e44a801600610300d540ca00743c014501c1d03400440c40591900d03614280c000385090100071825061200290080e07100d0000c41d140e0a80c0042000440c03034080d6089541c7c1d402620b00c0340f0b800e051a403c40c5080c0c62003420450b0900c05143d001c0b50454459510030700d01ca01609855402103900040ea540c09403280070050343c9815a003541490b522402c0c000d00a200054a48082208078400c4840440c0b040e032031820341d02e01c007146040c98484001000310a603043d404050108104035000034640c2400b02da115035840c2498944400c0100a404c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 606245107 1250 606243857 606243863
    0x1e0b04080a140f040f15050a0806150705010c080901020a0e1e0306041506050d08181207080a05120301060f0c051e1f05060a030809031c0809060601020a1707 69
    0x71104809514030748190152410004020f2480d40741d0f0300c1c0c0030b200014800f00340e01c04180800710a12001800368000301301d0b004031290f4146610b041d210407011422589110802c0002510003145690400006420503003400209036121f00f13450300c9882c1190300301e1089110301030204c2c2600680c50300301c0c1041003415080c6150320780a134152a103840b0129003480000c507801c44000301d0054000740710215521820016090030380d01001404140e984000c1079104030101903804080039007250516503910a80525481448030507540550b41d5207460380d03a0f0300c900c0311003181c1900811070b41440703652507882a64101c0340569120104c00300c2d04035003900c00c90282502942e250040114009032020100c0224860300c0603180103140710b4144201843c18401046003521a013810303c028000c1650b540c5415500380e070b801000d00d543d923a65000002e4500041680c1d15841b810b4140300b01c00c2103030380041d6150706c2500a034059500c0d03a5251401281c45a509140041c042c003480d0300d10369080d00706a0003400c40948 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 606246357 1250 606245107 606245117
    0xc0a08011409030301050a21061422020112020d0902031606140315010c050c06030f011806060e13090f0b0402180c070f0218010e0915010e16090902030c03041e0b04080a 74
    0xa289e48407d8150344100840c148010301220911400e81c2581c0741106014081c0114204126074031b60000380125914180301c00d0041d00071401005111050740880b2103d640242121704025440e8010601401644200e2021a0131041032960140040040300e1158620016010242c2d6040c401074500049043e01901c0600c00e504940ca01900c50a00450040a890020a0312980341c000980202c0ca10304a02400c020308050040040e1a00261900c4840004440036080741c119404450000e040140014240140720b00c00c00301031040442441e400741d070080c1d40e01d180300d0304002c19914031010181e07640389129808100322400318030381e02ca9400106100510a62004034081000450aa0b003a04135100d401c04d801c00f8004d5003070003046051110034a041241c1c103e585401d00c00c09601100400450f500140e1f504c50404991040200c2c034090000030204540b40e007040f03000b4010755041164203e89038034484244a8188910b200300b5508241c1c010300048041d91655515001c5800001c40c80c0c1c2804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 606247607 1250 606246357 606246419
    0xc09020307211409030c0601140609031203061c080a2a060509010e010b09061504030c0e042006070f05100e030c070504140106030c020c0a08011409030301050a 70
    0x6a03405201080b201e41100010840340c1d940390b5280c032041000782600302c065008010014006801042036030440b1348070302c0f400040e08140c1011030258032840e03070101c0c0e05000c1e8420f90200f0110440103580034080a454400c040c51a0a8004a03458210307400544130401c02e1094010043c03207026038030040c00343c002c4401c0c0491a01c00388042c4c40380081000b260401c0d21203041004841091081d12000d420303043c002d21200b201c0390041110324901812a03400f8448407620550841c111804450003183d0001c1c40c4048541d035090755004402095408841d204024000c00e120400c0c1a08080c0001c4401450b0600e485080e54410303125000021003210540101250070701c00358114800d5540b404000b0000d0f6a40710600d04650381811403503004203200300e1900c2540100c0d6920141200c1c15502d01d42800107a003044083c09a15001c1000c0c81580d215040300070216102c0019001264080b0403907206030007a031603941c2840d40300e00090250380d4200500070010131014540580765100031040091400c110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 606248857 1250 606247607 606247637
    0x16090e07210204051014010c020411030414150709060302030406090818040e06090a03050d0e010510090f2013231906020604141f0f0e06040c09020307 66
    0x390800a050840c041c1c0e00c90845800e5080c54040c080d404034840d0b0440c1d02207810403030191074050441d500241000405078540085440e10b51090542000440c0c506460303242c02e103051a42c1c00034401000310540110403524140c1510250707503e02030708150326a800040c0c182481100203400c020002c0c1d91660305c4001c0c4c000131590080003448190312801c0c1c0103041501075010701c01a101d81c07111601d960741c80b080400a070040003248000207207078186030880da00c0c2310050000c0701501030311004d00350f1395103044c040c8440e44001024400858020a809100941e00d650600f8125000e0070050040d040f280c2e144145c2188481000742480c8511400d00c0f41d1164445070142841c4101001c001c4500114502d00c3c02e40349850a080005802e5030038804510780d081480082d20f41c078025200901d802826100c0170700d500818041050108018a001503444070a403655202500d8580f1040b40d0b15890301e02c80401034030700818400d00c03480d0000c481505443c42c1840440080d80000c16020030001c04da1078030424 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 606250107 1250 606248857 606248879
    0x30309091521010c110a03080712060b18031b10200a051e0d120225060b120a0b070201140a090b06011704140c04020d020706060816090e07 61
    0xc011404607070a0802e180701c500c060031150340f22580c0040c0f0820031501603213020001020074070a80d0610b001121521540c6c0169505001c0c926001e415600740f043c046101004040500402010128001190820072083c143c80311405404010390441241031b4078881d080c64020f995800e0410303e0440311035411400c88100f140030311a0041300725005981c0031820310804020908501000c80306a0045117180c0150964030b1a900c240e24081c00350f89803188641840780d0b4140e441c090040303401800b02c05000d5103420034503020542d0803599240f40405420381414444510341480031104000c3c0700101c0716171569100001d00405034011507480313900c2095032065020303180d406107583c0040880c1455491a10620604008001604024150035003204141ea6800070311b4105420500c19030800c1c0d109240c00b81401d02d02c0d03880581050001440004a0500780d0003883d6281c0264004c020301512001030326180d00e40c07030001c00144014004140505807066010b5900244104100d500c5a0384c0c455407041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 606251357 1250 606250107 606250129
    0x13030b0906151807020f1911061207030c03062427030201200f0708061b16020406090203010b0705010b061813090c030b07111606050f0405040e0309031b0303090915 72
    0x103c05601910040308109240100c8c510b4002c0440b912030030141c58019030400880010400c074100f54030342c0c1c1c92500f4240698001c034098041000e8070301f04c0608034540c62600c81509241e5000180400c6407041036102c5500c3c910b56030b1000d1440006826146400454000c440604840308a164510780d903084410100940c45581e01802d001e0700703141c3d207000c1001d03046c280001e292000300c04140c84c0f840004403240040b00e0f01d00003050380c2d00381c0140c814008200101000d03007015080b20310010020815401c0030b0003802400c4d01c00d030024004004030f80e06001140c001c04019140034070b10103402c52414602000b01c401c02c0e072581c103400991456162900020f01d902a44180c1302c1109880038490100c0c0e110754000c40000440000f030030141d6801c00703c00300b6140648110000c004d000302d25001c01c585c204085500504004005121548181c451503407039603c081c502c01c1c841c3c0714507429480c00200c50a09201040f40086c042e50a010b080d80510214103001047e0000c0705c81107613031002032603480500840c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 606252607 1250 606251357 606251383
    0x21206070234050108041401050901020c0d090b03010b16170a120516110111192c060d060302030a0c0503070519140613030b0906151807020f 62
    0xb070452401d481c1814255040368011803541041010703680c8a8441842074002c4400a28043c012540d840c18104d441401e43d075032000d401d508001c280f18403903c05401402113091102d0030b13510708906480341560005190702c00c54270100d4061004224111602001c0c04a0040868501609040701c5d40c64101c0545d607181c21180c034100101d440b41c2072031303030000f565800c07490054020040341c01e22001100c2280b4804500000300403192101002001003908a00004204c410310261500c0b0b26030108140003581d00c4841c0001500292001600c0d40800707100070001904d2114800c1c180c0b1410b00784005988045918450181c4030540000161002c1107144d0445c0d000300360200f03210342802d04243c107007036180d80102e100d40c0a1050305d03060004031070800c5045400514078102a074880c2e0010400300d01401c01420801740c1804c10000500050b028528070a000410a4a03220340e2854000d0032020351100440390041e150344440d43d5101d190300f40098020f00e10380110b071503403242c580c10a4a0921a20600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 606253857 1250 606252607 606252613
    0x15040606091406130c05040f240e15130e0c190e0612130212060103120c03050405010503130c0b0909060f010c120c0501051510020c01050a0302070212060702 69
    0x10044a00c01d8810a041100000b0501d149824a070000481d500251000000d4855079215811405405034048400810000440641c0325070303030f4143d100280e10b5110030300c14000c00340d03c103c02c5440e10031545c00c08800742c01443d1001d4900000a40c0e03031903401078070300351b8803040d904072012403400b800c0e003017142c8250048200035540780345941000d5410350000409800303002c0004e600c15059610f40c1d05a42d500926203403030000542e03c2440b0002040b510202c040e4120019110242444a010481c83c2c10390740524155817444010180458440c00069000380002d1424071050000d036118800440e00b0402c10030078107505200b6a200c00340e003002d156001156002e0002201011424070000d6503500110496142c2410364003c400a403442c13001d80c000602243c1c030202090096030052031181c1481d82c0260082200345080700c1c030002484800301440b4824104121b0352100c2030300c0000c5a820011069462900384945d00300117038040c2d004540103d07400321907041c9152101d0307410000180714085603402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 606255107 1250 606253857 606253859
    0x1a07081c0e0f0d021b0402070204060312170705070b0705091e01020106080a0c0909080c060901020d0506030a0c0611030f0c0615011b020f121603020307090608150402010215040606 79
    0x11803401c02c03030120b0030080c0e80003503c50841c0c1c030350041414641c15042c0b038100c012024852000074020f2081c10030003940549029400b00500120368001d1a02000760340360418404140010044640d60031124040041e80400c9880d000501c6c101800d40c1001e075a0070642d041540c8000007540002004010070f50032500580301c1042da6070309004550080a0100c050100144a0746032880c49007014056a03801c0743d00d400406080019040840d42504988400c0c0e94190134468110b5000c0d6002241c00610141454003040c19890b020502c0462294065400c1c24000c0ca0090240e9822240706074000b003500003842004805c0c04450000e1010414080c058440c51419070f070f074000c4405081c0303041030401030400342142803144041e562801040d0100e400080e82000300300019140b04040303003035108502404000d540b44124814104050301c0c400c906881945858610240c116150761051185a034071548085003d401c3c00303001d45400c07030300601c1501c2c451031080c0d040034070078641038404555103661050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 606256357 1250 606255107 606255131
    0xb04060c17280b010203070f26030f010501031a100318050f011104080a060e16080d02070602030a0207090e03071a090d0f09090203071206060f080604061a07081c 71
    0x26640003181d14002c2e0401c6805180c0b40003e58038066003000400800d910041e80b810301030261030981e15161001031803c4c032440c1118110903590421303074402a0345542d0380000304a5602a002c0c032941209510302036994200d8000410880d200c2c034000310380c14160395450b805001c010b0036510600d114060002082440c03004442e0900b19917211005102c2c8400a11080c4181200450440303507040e044003010810380c500751042403c1c609040140c0610781303050700e40020049404201e0340c0300124035030240c61010343e503420166100e101d80440400181c0241c1401e1041004036401a107403051000c0440382003041039591180c24032080c0006034481d03d070700c00c10014165800c00075140e40303c0f40351034000d51000d840714014014601d40d0140c03a80d95600803001400e224820048008243c240b46018000070380d46010140540d54403001110000e0300420026040d030502d801440204c40c0202401810302c13100d04422140394000d1002141c420608002c1002e01c0c203802c02c80145c0f50720140301c0000f10618014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 606257607 1250 606256357 606256411
    0x102030717130e070c0212060103170c07050a0f030213060b090d0602090918060c0f190239010e030c09060d1407050f091905070c2108060603040b04060c17 68
    0x140051f00a584000014000903490300c04c406941c1140014031902c8003000580c0500740461340d00915000100504c0001d020900000480226802074807804505034810401009860007030040001a0604008404c0c00d030500c1140c03400f01d01d020710001803c100c1d0b44000982c0220096074450b4070300d144210108000d0a00380600c98201c848608101c0c0783c000e0040c54100e4074000d01002000001d440c10b83d0340540380c002c0c000d5030520040c8a0300d50781c00c2084049007409001249200c003116a0804651071110b50280035410345d6500020000c2084214210400107001e000811031600311021140640000300303514200c42c0308080070409032882ca0700f8001400780364a480c1000307520903074600d01400054150940300300480500680c0201c0c00365540c2d03000399514945104d00404c004800d83e07628289190890011011480f255117400e000e1300c0e038100f01301083c0802d0310050303c4110b24501240006006034004030740400581130805031485055540c01c40401d085601c0020f5002440706050904008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 606258857 1250 606257607 606257629
    0x519020901062a03030b030a15290402090402070b0a09061a010f03150b070309290f13171e0f0c010804061104120c050102030717130e070c02 62
    0x380c0340070003d018000c1c2c407140740340b001e20540c420344982c52190344003414803942042d10140d0380502101d10610062820007503050441000d0400d19103025803d178017181c06c0c1420407140d656200c81c45410120141e0402009500220140c2c0d8429801c001030000154940401d074410f19034800c000a0b0140182011400e4521001d410194030144119820143c0e030010210100c0309141e28000800701014400e21525000035040782d081d400000c02c0b008100340d0b1003007568098624000d00981003615010795400040b410040c43c0260400030302c0403040d0b60480e600540b92460340140c001d168650340b807583c5040c03880d0091a4844039000b481030f403040320307003540c106940c65a40741300103103000402500a99190707800c1c1d090103410450745002040030302056800a4070800c9688d40c80c0d9a0301e584d541d04051100700507600488250259060014071340d03002009850041c0d41080c4000c00e0f44ad0322401c0154940d104000c1c03a000f0034100707030000c68008460302c241c078480e60a90301c500000c40514010003031843c0c40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 606260107 1250 606258857 606258869
    0x18030908060c030c07151413140705091b04030204060e0f07090f060309030507120f090b070b0720120904150f1502030c1b18070e0f0105070519020901 66
    0x4106100c0600c4182c81155807a0b074000e614241206c0303908040d48042c2a1940f40c0700e42140d400c0341030150010000c0040303600b80703101c0e00c040c1005400410100740c680c4490b1041c0395000e40d0040028001e0030462001c44001e008494204e4074080d12940060f044800d1500601c60300c184c1e980410100f00c1c0e520160707075040041e40c02d04015103803810321803080308662030041c8820551a10464001c1601a20135940e090780d0040d040c1c0c4d40c80d07282c40001885c4140c4082d001c8001900c0e2040000d12010000454002c0c41c0c001a4106c525078801700103075281101c0c0780e10303505910744907054000c40c40781c14410180c880c41e100004030b644442210412051703c1d6980107150920ba807a40081000041c912030860880d690410582003140c0c017400283d0641c082c089124540b405aa00ba20807010110fa00102c0c0341001241d01d6003d840d0540340240806001b2910000032a681c604c1c403038454642400c8022013600145000303454903c145c1d41759401e10050b000301c00c01c000307680314048085207000515035000d403034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 606261357 1250 606260107 606260131
    0xd08040e01060f0c17090d29220f0827030606040b0117060d05060910140402210f2a01051c0f090204090305030402030c01180e09011803090806 63
    0x3c181d03240d09045e4020030030405820840081c0300801074a83c4403400b15240c1d0024901041074800000000038811110f5902543c010b40000040120401440004c204e4002c07000e481e00c420000c3d5624800b01001d00400d560080b014080004094101801c002000b034101034001071801c031102c01c1c076107401e40103030040c2c0c496400c10f510201d5030303640214460011001348000702d869466034804100c2c41c00c0360000c040c04030f0245074104120030f6800500d500070b0f04000103041048000007880c40400302070a440080d8800b0001c0403150446030303104022400600c0c600b06a5040500300c4503d0380c0f03042c809480032800c084003204401c044804400241d01104d100382441840c1031402d40c2d10086803d903081c46074803125a20f812404995030141d11840c0140d6000d0800c100804003420090003540088a04074841c3c4034100240c40b455204aa41c101c2e02c90161480c0b510503820b00c040004a0070300140b030300310950b6803046800091989a80300d00b40d218020784499858508108000d41071420042203210700301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 606262607 1250 606261357 606261377
    0x9060f0908040806100e01092304120816170c07020d0807170403020f060304020f031b03150103030905061b03040f03141b040f2310170604020402070f0b042108150f0d08040e01060f 79
    0x284d0000951a5040f40e044074280300e503030754058a080540501074340a50000d0040d14a03c04114800000341441400750f03800d400c03090b40d1047e08200740d00c17890000035044500c2c0101f518843c20048003a540052005280740c00200302c6a000c245800300c2800042c3d17000d040041d0035201c40c1000e10401245800e2a0342d4444658155113000d840c43c80e05110340b5009140000310301280402c485001d40c0e8000380714003640d94031076071055103028130710041c0001d403001c40c1481803020b01d0003c0050081e16507003a00712a2003180006404000041c44010740300f9849030348484040ea91506148078a81107908502d500c0384036030401c15031b418800d800c0b0342c10036509206011140342d800c160014040354041d90450340980d0b03680b0503150848025010213401003040b80904140010424811420a00c031506a00600c2c0c440c41201d80c200c8044900b9144200b0301c0c039218044271664184510280d01c0c900000d81001c4000840e551201e0703281c4d00c141e0290164a0842c401440300c644e0100c808402d0300d1451030041504 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 606263857 1250 606262607 606262651
    0x1201006050105180d0503070f080306010801090c020c13150e01090c0c050601290a090303110a0c29190e010309110409060f0908040806100e010923041208 68
    0x1c0a000c98452081c4005c1c58540c0800004008464415500c544464001141450700c0402ca40003a41c1d0780307003c0303002400085803880d080d00c501307100c07000c41381e0080440d00b0684041c41201640e8803100e02c1001c3d1194030350040481120343c504006c0c286260034400703541c500400c20003118003800d5144200034441d1070f0742e804142c0026415041d0350807103440003d4003400f4014690300901e6054040e00060b03011405182c00c6411082080440340280c50303155000b118065101c2d1241450300004240610420007803141079142441c8503918500b01c01c84010b41900f485a00b10140c02003084040d00003002c11900b14120752252803298040420b080070f20030925655561007518030320a44d0b0600466a070b45410040c000550402c2e000e413100700c0d0013003110624908140b00300c0c0d4454041c2881342d2140c4000305115040c05803548048940420002c0e1499003022086406403014a88922006c404d5014201c011120744c510380380140c0c4951088115010039041c003800c0100010200d20740108400444000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 606265107 1250 606263857 606263887
    0x2040b06041d060d141c1107142b11041a010507050a14030424020703080a090302060a0801090f0b09071107150c05071a040e040201201006050105 64
    0x1258040b20304942a0b6540d01c01007540c1d11035215010384660031085000300c00f6040428070303d4100000d0600c41c4c103400d5201c2002c1d00c5010184070400c50035800301c101000454043c0300034403690f1000401400d0070b16420280740040c03081e0a451046e017000318000803000c0101c0c0b200180341c801419541401000341210003008080c01007003800c0c1c10300c180002c0400800c0014801415510341c000721895402296841c606d603242c0043c051070401c80c0c41d81c21554038491481036505080b2500d54010214a81107589454858028000000500000c0280800144d076030748060817900b51640d80c1c0984d83c7d894244600c0a4031103034050f48403254580b4844600030307250503440d05d501c4001350070010680c4c012804500e191440d1907001c00d5a503402c5071005645140d110b2507000300c490050301106c0e080d9444880d0011200126010000128030402c0108103100090048652050050515840382d1900003038241800200400841003500483c44000004e480d07031140c000030304020300e49142411405068845 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 606266357 1250 606265107 606265139
    0x4060b0111070e270d0e122a18011e06030504020d020108090f07080102070b0702060f0a050a0b1f020106080304030816080405180627070806031c050702040b0604 71
    0x341e0031040c02c8440c01c41c0610100307205407000c044c4c0898404002d00c2000601c1940308600040c4240342100341d0800d54a400550b43d84c8090440304250313040c030000c4101010103034813400002c0c0c200070042680d00105108007256402404001d0342496107440c40c1c5c00840e50074034690094003e05d8607001c01d00c00940c8a02e078522461950a080070780f000d40310070302c0780c0d854800070000d42c0380b40b4424503201055031031064003d09071061007058520f030542c031058016078440744119420003078041400006000325a854008582200d02c500b000210b050000300482c140d5124110403042c081d40d00d001c8041e019909204031402010f1031b1000c1e60900b41582e5440c20719115421001400d010f104140d002809030207002c8400808000b410901501d14608030642100d8040b5001c43c0701c3c04a0014071200103200c8800c0066401e40355003907021580e1148416104010f0140030306801d4862010500c5621421540042d01c512443d03c4640e140e8147c0e2041105890710704101c14001c2c1e030240000c0140d4001054060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 606267607 1250 606266357 606266371
    0xe10110c012d03020405060f070212120d051f0303020a020a0b1905070c09061d0610120c03060e07090305060c040303020715170f180c03070603090c050904060b0111070e 74
    0x42c01d2420007402c101c02070301403900b04560085000a004400c103194000508401b4425501d0355130443c080b80030144c5441840c141c1d501c02e07540c20844c801100c403142d48107030741c065a103028000d107183d10b50f0452048001c05401c00c40c09a80040a9182036162100c2104003c09241202c1ca1070410303444000100e145104186200340700c40030800e2800c1150480c0d80d207000d0a1444000c2201c4c650303c124240300303003404180c018042090000410158100392104030700380703100e0362107019021404104240080003440c8403001019680c45000c42e400d1280085140501910750750010b29034290304089050140207404100400401c01041000a03008102007007200c0001180c4504034010b04403d64900c14600d00550350f0404081c10400c044182c055407034066403401040308100c00b4066065680c440045c140203515512194040120310311a0b08400080c52040086684980d5218040b85411070b007039808541854036411010400e5034000e002d030305500c089400401d41180740505a11090801a000d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 606268857 1250 606267607 606267677
    0x403080d05041a07300e0606011d0a0b0d091a07030e07031a0714031015030c090326073005040e060a03050319020d111b010e10110c01 59
    0x403000000c50303c88170003100c240403401485069078050003075880d00411200c250100709103229040c145454130f9489880c5183c098900a4403e0030b00303250300c0d099040060303140d640c541c075481e02e0340007c2c08409603e0500c00c250250400d09040820380902611000c00c0300600c5a40305842c104045480401201c1d00c80508240340d142d640c64005081f039040c10b201007542d012150003c02d00c48a1220560790800322040001c00c91155105604110300355030000f0400d10000c0d00c010303801d10200700d891610940b26030011543c1c2c0b81c072401c90000e250b41354001041c00e44001041d041029200c1842004040070710b0301c460140c09800c22100d001070001c0c06107002e80c40c510018000060015101c02548501441d00001101d460740030652007c0545002c03810b04000500550148603202070080d11940c41c1101400080d0908181018030010b4107001801220b04001c00b80d010f500071030702c0e615100748414480c0d6a40101171091004180e2074814004004c44c1000100c1c2030010700030003075440048800e0054008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 606270107 1250 606268857 606268907
    0x40518060a120c0e04021c11030d05090603310303060312020c03190c12080c07060e0a050d061508060f01121109271e030414150403080d05041a07 64
    0x1203072981207561030440d0701502c03041947d400e00580950682c0069811421207844040700036080700c0320b0055184c6140c0105050001c140d102103c1d003078508140c0b51015103500100c81c440f4007016601c0c203210040e80460b50703c030300c24014407000104840501e480e5000030705d00c0000e00408a5950004481c00e0005903da110b003440410000c0c440b60320050403c580e08410072081d43c10704c0f131155802001c038242648550040002c04500a10305003a81c03100c0201301a00070f80c80c08082c4005005010001c032400d40c1c0d0344811a696000c504512030240c11340800504151400000080e440700d01a0000d491000c400b0751010001004011680341d10032060f20a11295100e0102c200180000d00c00150144407500140f030026070400280704c0001c03014804402c1c3c540c2411401c2503103038800d6001d00c400b00ca44030710240d40203080401ca803c4150f803183d14076901d4143d50f0307102c0103255007012186021960b103840c18042440601001000101c030b81048039900c500301613030702401c0c02960103144040a030080103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 606271357 1250 606270107 606270109
    0x209130e03071b080102070b07020c09090709020717030a0207030f05030f130303140906160813081c18031d09061005211e010e1506040518060a120c0e0402 68
    0xf128200801302c00f0300070354a038150781c501012111800c0f038550005110302d110310006031404903c0c8a003d168400040d02d0070320308104c00300c00a980501c0301034804030034000b8403414280c13241000354400e020500c80161184801d1500802ca541814040703004c100041c020b12407546540802160003c59110b51035a48004602d0164050300500302400c40d240c3c0c04000b080300001003c01c03a5481039800803103036540e00804c40c4090724100ca0a407400d01203080107078207030400548401c00418032941c800e02101c8042c40951010826644c0b5030b4180e484a19103d04c80c08201500302c19488800480605095a06107154000c00c075000d20083c18240300300b8024516202250094040302c003044041111124045041049080208000d03564003010001401c101d03a01259003034005416034845d071402c40420346a841c1c101c00280c91a01d44946c6c032913420407002a465031a100003000d80714030080010043c0ca001020080300000d1507101d54405810055036400007440d52400f41d00b5908104080c08054071030340 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 606272607 1250 606271357 606271403
    0x50a0507021f082a030a09053f0a020d230708070203120910081f030327050604050d08070f0302100c0e090c070f06050a0209130e0307 59
    0x12004007909428441c040b02c1c2c40341d02c4000700c0d100c1c82e8401d090340407125a00b400341c503010403021841c0d00303014020301c0400c0c0340413400c3c0c10001070716005004651000058000154103540942c4078800c04040b401c2c6d01c0214075a40e13000d0440e510a40c0d01105080c40503c4101035140d50a980540301009103004d82402c40206000b4001030094103102c03501d403203407041d2174108425031121005900c41c0c451621400c001c058050100c0c5c0c080d940103400c101c07182481c141c9c1510b055402600e501c0290702ca0849031408944000040d600541c001e0307940c42409042801c09901510345008118201c11501005001540b19403048904036003060300c010300110918101100c09000781c1100070400702c08005240c041c140d00003401041c2c091b0480041100a138045010b07241e0b854035202e0a50061480740010380326843c0d180113001d1aa005010440c01403869079a00000ca560454200ba1225800305880000d400c0034040702c01c410300e01d4001000406980141c01d55240544580100b05018400340f07200c1000c002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 606273857 1250 606272607 606272629
    0x40f060e061003060509061003020603071403192307120905031b071202030c3d1202070c050d02060c0105040804090b030c0a0b0a020115030b01061e050a050702 70
    0x1441510607504240426442035840ba10041c3d800a003020040f6824440c049030302402000390581c50b15102d45160300788010350300300425050500c01c440740c07180007911a001c02035100d400f9034044d0500f2180c5a0302120200d61a482005941c1c900c40610200e00c0101c1c000703030307907001074184c18080c0f901214030f800140071b081c1d0408014541c0c040070480d0045560b0600d5402e0652140405840c0e0040d100e04541800400555003c2c0d03041e40003c05458017801c100c485901455150307484000420102d1030350811a1402d24040e03020041a0550940030b2076204400d42400300d080c41d4154581141d507101c03000b0800481c000c00d4400c0f08904e283d8011559040e04407103010048200a21140ca4542070684103600180304060b000307401c1c403c20301c5003481d000c2000103c100009001010083c04e25082400e10f400c081d844900b590750382c1000c0c0807a565110462401107100b90118941136040500080c5640c40b020030032a00d500c441b00301141d141c0d80010079240e0841c19458025150805400003504000c0d603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 606275107 1250 606273857 606273881
    0x150b042f0d06050d0b010e0f0c220909050c0111030a0c17090a0905010503010f020424032003060f0103020301051503040f0c0e061005090d031b080c030c06011508040f06 74
    0x8060410805c111845005a04841c0c40d15844800c40d03a0b806018500104e04503080c80c80914108810407a10142d103003440d040d064449048020151035544032801c807441020240d03020360100305182d0241da404038156176400040c0c80950300300040214054620303401450014110b003528290342881c40342107415100c01850051000003c0c4d51f589030400010300c001c1c01424040e50a0038103c0f80c1d40400c60080360304951502c07030003425050200b080158260449140b01007010784411460644900342c80c000f0f03100511700702c190399480c1004c03000c00950b81100044c080c18136005000401096a82781100f805e4081801c0507540e1340e58075488d00104140989100900d5101446e901059016203450070034401c940c1540c0f005100303900403106407445c1c002d41002030f521002c103002c20800284210b400c1800b1419500512060303450035901e80d00290004c00c1144a075a01c08149140c605a04212150040021949010f2032009114000300013040c0100041d00c140c1c004498a020000141e01026001c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 606276357 1250 606275107 606275119
    0x62718020409030903202b05030a1106010927080c0d090e0604091502180607050312010b0a0f03050c28020f0105090a12020a150b042f0d0605 62
    0x1881ca0068003210240c00151013401166a850481400b046201040c851000f01542d100020f17050035220f4a5030761545260041f10001582d400061040025010404154030b40140c0050041c3c442403030144164020b00485081c5000d02485510654003054000e04018441110840609262800f441071240c0700c0c400c6d100340c5540c0060a64406c8042d0240d440443c1e203480a92100c5c8200070070b40c3d100d00000381002060150b0f250340c0c501d81ea8000c100058092140324014a81e00340000d550b50801001603880b030300f00017030b181c40120f10048050b0150202c0d09d405800c00040d808001d210f220f039147d2410030b1503900e0001c1740000048405803a40c0125401308001700c14603020f20b601c0003001c8208084050700c140702a941e13074001c046c09140d210740c400e800145241845500c0d0500a4401000c3e00019400342a1640c000325104600c0c040141c12141400308801980380240022940450100b035002208285a0302d40b42d0100082c10818011016200740c848402c1460315004010592040754800c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 606277607 1250 606276357 606276371
    0xc060e19260f0703111e1506040b0a0510020a020301050a020d051008030f0913020a02070504050a330806090106050f09070c061508031b10050103051207061104030609060627180204 79
    0x800065044a051f1030141e5401e29403565030500003a00c080b00e490b1070b40400802c0c0305000300d040103442032140031403610403203909600075000309003142c2c42610080226500058a142402018042c80d50005502240911a00d00d464410b5031640950340312000c00320000199880d45a5400981507542e010301c107011036403040c4200d0013956541c02c1d4810680103e05200004075194118820110806021a0035086402444d412400c1e188103c01d80050b040c1c8403448082421141000424070409c41803000190f000e0038102045180f402e08039019110303d031000104810991f003d24a00c084981c88680440d00d20345c0185860035450150304001c011384008034204a0114420900300840803803030307069603070100154075210155002400064076a610015100d03007281c0b03001000b480401c0c090f0300d0000d060040c4030040c404e9540940c1c02541c01588500b86642402120301c17484005001c080d504403284c2c8040d011050020300d181040c6401595a000c9452040c0c0d110080104c070707140d000f00100814 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 606278857 1250 606277607 606277663
    0x9020a0e09060f01120807020d060e0f071a0906090111010c0e0901050a1a1c0501140315060f130b06040f030c0906060c060e19260f070311 61
    0x1000d001c0790302241034810301c80401c4281d004040168140d40c0440580f4600300e21a84414070142e02040003240c12003500c20314034020400500c070380e02889131040d015224001c081040589800e2254000105104540b002c100760b0030001403c480b0a0301084c0e0711546c4030700d20440103944e026108000300001d075003000c40300325205034401841a00034900b2103000302e950342c0311360a1245045050003942c0d2041c0424414407600d200c0d1002401002d030b1400705183c0845003094036401a10400e0b4000d01903074610780d120209918041c030142002d904843c20101d41d0781382c00340003d8803500c40403010b80c0c0201c400060b0708000c4604d039003040e0f95200002d004180d866a8600102c2602d030182c1c84240c1e4076051901e00400d1158441c0a880121134095031460340050b050380326003008000000361a10b0901c030716422001c0f091040c61004806a000da03060541001c1c80e40c0c06c068a00a80000b581d4a4a01c2000302040d10691078003035903407450300761802c0c0310240d20720580685480005801e680b1a480c0c5259907080c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 606280107 1250 606278857 606278879
    0x30010509010209100c110108041401150302040e03031b090102030409020408031b03120604110702030a20030703031b05030405120a0512181302040b07050102071a04030906030f09020a 80
    0xf164029202058251000034003192001d03005003000b402d42c2a29140390510358030454149800c02c0c00341d120003510101090015007180c040d004030000b100c0303107040c0800561406108001e000d030319040c0a5461440c01d1081040343c80c1d9036504004892a011880002591080082e100a080c8100e4110b43d03c4e80c8410019680e60042c10407000000401d02e400c4003824804416618030b00c0c41031000a5142d1a41d9003000040d00c40a01c4941500100340004c1015030390402c4110016809000e1880902e0300d002282100000c800e92154000d42c0300f0b542c10400a40d000b10040c0a0040e07100c0d1032002c070200341c5041800c52003680c0c4002c0d8030000d00c201c903001c0c99201040010040340320b1022a120200c500300200b081d030103203880c4010030415812581c07049007020310304005841d0800000624081d00c4d04005000c94210340401d8070207a501059000422a2110840c030003c0c030040f96481c544c0c6403e590042003451240141030405460311019007801c492600a003080039402055808001d80300c400100d9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 606281357 1250 606280107 606280117
    0xc05030606030402091924080a050d1110230f24030304031202150a060b18030a05060a0e100e06040f05160e09150601091e12080714010209300105090102 67
    0x6007c611500c3c0c0046e45c4600058107085490b4084041c0103214200d10003170300c1380300c41d0403021041c0d0302a0384051001184a40300b1301007961042140d401c20180200c25016403100002d0148000b4244101442100c4c620040e0516840304554030031550180700300301090643c040d6034001001300c41078610030300f02142c01181903c80408814003414865965002c607801382c51840c440c5d401055403c000c020000c0c00100710844411201508131800010786039109450224101c44000500c0d540d1884454211401c0c01844e80070360308082d0900c014030200059586030003001e440100262440003810007001020302c8546848118010250f14480c0d68180841403044c0c1150458030a004107640e4004d10307115207011901501040c1e4504079850f0802e1441d400d40d104400002c200d03940d901000080801481c48180602c40c40307810b180ea120783c9149082c044035080104e0007a03103a4010310031000301da141d40c101540100d0401c0822800da40b05500d05501d50700c40d48aea45d1030954203080800094040c1500145 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 606282607 1250 606281357 606281411
    0x306050402120d140c0a14030904060e040b06242803090c1707090504080a030506100c020d0f0203030304050c190e0f070513030c090c050306060304020919 68
    0x40007034a048428a0721080c00403c1c2c400030501c2810307000d0300e003080000509404020042142c4100507103032140e0340301240a50748a0010b6000089810301400d003400b40200802001a81c40300307904141e9160301c01404000e01c4240241c009501030b14074070038810900f5090400c01000540d0b41c200c0c01c110071f0244c2420000b00340340e05041d1140d411480380b017803081030760b001d4004c1c50400d0b0650401d20340b460000406c40d4451303200e10078910080307414071042c89558081c51145035055502e1b0390903c0c000d41600c100070081403285614141c190f42c990780080b004181c050741100c04242e01101e501c0c08002100319035002a400d84004020001000000107a00400000844501049214a00c0000d081a07001d0140320590718454000c8ad06e0489030040031034000c442820540e00309241e40e408060345c40042d82c000d85039494195410888401148113000d5032400710310f015440c503e00000450303410f10003e070000f4010b004000020300107540e40140e249402010400900c0100c0c00204400014800d03401d4507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 606283857 1250 606282607 606282619
    0x708010506040b1903021b070509070503060d03050a1b060504060605030102031902130b070b041b14011107180c11012304081909090e01090c09240306050402 69
    0x1140d24074041c02030724103c0d1400000c10b46041032030200540c0d2101c400244105040c1c090145696102c45862400c03e044a080001c2030307590f04c0c020800c508404060803450034000308005028040c0c5454800315a51601030030480d54642c0c200d4000c4640004882d17a40030380300703503103540107003040481c2d00b05c28021405100280100c0342c0301c004043c200c7c403056443e40d0701c0005405034082c8006186e000382c80402c0d40d801050940640da089500c40940c00850112403800e01101004104440e02000d014007400f4803140115217401d050811100200d0b1540b5141441054803080c021700d03904001300005030000c0b020360101040300f420054050110221050080750007091000c0400c8014031031383d0000e0b1440b0200001d5003640002c08600c03100c024006481403881005000e0540125554102c040d0b100f540d0382d60709561601129000b241c40c40190001b041e4140740c80309000c1035a40c64030304290740e09d0000000b03404000b00206c03400d403052a24a0200e8281c5100000140012603001c030344107600035104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 606285107 1250 606283857 606283859
    0x170403140a0e01030e060c180310020301030501050f0a060621020c1006060e01031103040611040308120123090f070905120304030c1a0322080d0c23040902090307030f0803070801 78
    0xa080d03140e40c2c040b030740c1f4031000d50144040200c14200d803021011500700a4103441e050382e1044074030300981c2d009030000d8480e69103031000d00419940700d60390701d43c0c042c44042c0200206814140b000300030183d40b6640c90f02d02e1b0340443c9803550460325030307044403030605000c000c6950710b08204075010301030311540c070411000c50150400040a54042d00403800d000711000e190a2a55499941e03000040954003400c12540c10244030200000c0c180c0c60040510701216000c00180c0d6141c00810742485074920103600000e007140b088500316484080190b60440080da000c01c3c0c0c00d50b104142114000e4060780b219606c441ca034501034480302c0002c4000e000741d0380220384884d8401e442d1004c1c40c5005002c1080041c1280c0c3c00c00000d825501c400340316510010340d500b1004060146911341d24110b030403030b600c0c00312a00d55445481795250742200c000200400a0740e001b00143c800c004500105004a20034880748940004a01001e07940600c0540043c50b407040c03440901840d03504000034179400c12282800442d0001c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 606286357 1250 606285107 606285131
    0xd150c0f141e0703080411010e0f0405060301321b0a0c0201031e0506090906090a0308040512030702101811060702041d0a03120c170403140a0e0103 65
    0x60800c0385144680c4a000d0515586000e001d0103500038401c807244081c0380300d418015050004000e0076042d000369180d148505250078040b40075940103c40702d040c0046214010895220042071740c615140031500025699a4200440d02614030100b94428001c03103076254800c1c40761041000210440c0704850511690348180803441d207044122018007580d03005001100d140d91082d68600078962042c540800c280c1c2441020b20311a0300c402101d505e6954950f0100310a500b01102615440711000c03005007541c1c00c220380350315241c5510b4000903041050841c00682441400c204200c151070442d000c05a9a1401030740c025100c10040d2518116681007000002d240a9403517910040d05401c8180505450900301c100403640d808520101d0b03f103900c45030044100c100c0c0c445182c0c048200200a0300040a0300d2400400f0450b07518241031000340340950b02c0e0341080c2e02500c4140000b0202701d11040383e4403181401e13a042000c601c88040700950008885c0b4000d544100c0384140b0046c2a20203000c2510020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 606287607 1250 606286357 606286367
    0x2010506040e07260d030b01020606032a0a0b07030305100e04051c030b03010e06152b08070807060915020a02060609190603050604030e031606050702040b0d150c 71
    0x24903001c42d60340700040a11001480038a0002c1c2966104d80805406024501c040c1c00d0003011410310740400c1c0e9900000b074481d6014459260f0003030040300609062041550015582009040143c1421105928100c1d00d03031129003281c40540314000e90f461b11901246030060107410121840c1c110450b51860004504004405c40c80c005e56111028241410f940e4403004504040c6503944070805448132400f00c0c03952420f116403000c1c2101c0e41d010703151514000a020a03200d154602940c007d8010304c1c0014644450817400207105120701e4210a0217030003609088100303024440c00a000340303a00107101400c001d0154000c5905c640b09141d2001c1200c1412000c4c0100d000315003144000d0303084000010704515103035010590040c0e44001079144000458120b4080392140c0e0003c641c9980038100740828140c1001000380900e80c101d00600c1c0107500c207042c1c0307500c0030020310841091010200f44c0000310364803900103402010700076252000325942d03820820036a07640e0f2545445254a82914400070901c25 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 606288857 1250 606287607 606287621
    0xf040b0412060e072709081606180206091207031e0c14010f0e120304090f0b0402090303041404060302060d0b101b0f0206070c060f0314071704050115080d0201050604 73
    0x41108400035241c030b004c42d403614020b1076601d40d500d179903a004e10800060580d0041d04a612002e00c58000d43d41c0d99281c800c2c1124800c3c0c1284a46408000001005076103890407140007a5003a0340c040e8140d4202a9910b183c4291030b04004c0c00000456101138814400f400e04c5c0d00c0c03c038000e10b14000d07000d941da00300080141e8071160b44d81c0021110441100701c1e41c000d041c0451940406040788094030380240c5441e0031038200707030050b904564803401d511a034003240740111a210b2804803401c40c9842c1e88280042e9807403245229070001820003c618540356920343d44420300a60700940800c0d40d48018030340401c01022020a1244207540b40310302110b80600c10740784610041c1d8032200c54007007284192220f80000741d021500f03c0e40f2403001c0100c40005603905d07240c100180541d0b1035555554801e920043c2c00d03155415140ca600c22000020030000c00e500520f0049088602510865561143e0804501514400d02d16009080151400056120b40082c040032030368502d9008005544a0781d0400c01134402d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 606290107 1250 606288857 606288869
    0xe2103060904060e1507030b04054611030402012c0105180a090b10050f090904080d150501110c030d0e010c0b1501082a0f040b0412060e07 61
    0x10400040c0024034554071a69130a08103000310b0b40c4900b240d0300075050002c2e04407950b00000340c9407800c444c42410240620b54001200c04044603841f81003501e80144d144c0c02081c040e186003c03801d102001203028082032069040c00980602c540000e4201c00702041d801138030101e001444601854410f8012640c0ca01c0e69846014159072031143c04000460303558114049480748804540240c2c980340da901c1d10004001e01c06040080b450041d00c2c2c0400c40c506050700d081800740a01085155290170190046414483c800c45240d0016160390405001300d00541440482d940c0c50700400c040803051008900e004c40758243d85410400030503070b9141e03803201c1c8016200c941643c014608100031901440d12480300081c10b150244085007242c585544010707042d0b9617420740c0303e8058842c0c0801d5078020b40d0a45d0002c0c0d0001e8501d40d18207061205161460b4000107841d00704404920303040c07080c1070780341100d0080c0b8000c21225150350b1200e03813421440e8108070007110300358074284040e0300071071011402c6030481d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 606291357 1250 606290107 606290119
    0x3081b0c030709110906220503190f0c080a0c0f05060c100b0f090a060602190f0b07020322050a08121c09200406050301050c16150e210306 61
    0xf207061030b070314058903901c142082c1d4010188000039180d101c2d00301800482c510742505408100f80d51210002085540d04058081d8020300341c1c3e8000703098041612186036078850590140c0350358505160f0359210709608a05072900416883c6018400182411030036529001000c505075941c42040103010311610be180c17103443d00700b0315080c001003040740c4c4130a200c4c020241142070407140c0800050300c2174508552a00409599500c24000e142d41000006d09006120500114030a4141ca450310714680c54540180008154400680540e10a009a604440084000141e0b98042d007211410204803402514000d0700c1e44000020380d103000040c03400d405a0041121443c0c5010b18103140158542c821400613a1512444140d000901d20a001d00c050b890b684000101100500700300401c1d151103a20031442a81000241b0030101221802c5036054960071030205503001081c984015511659090221044d00e40147c05610210229034902c984031000300907110324000380a011543c0c001540c400d42c1280c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 606292607 1250 606291357 606291359
    0x3030613052e0609050f06120a1b09050102150c0a080403091206020d0b120c0103020a020a0b091608030301080601090b030a020d0c0f05060301051005031e0103081b0c0307 75
    0x40305540066000090703602c92622040010680080601c90b1a462000002c2c889408000c101d502071000005000101e940281c0034429000040c0c20303006000c611081c102c0c4040100e9124085039000c0700d80b4920003890351211015009001c1d040022074414507015010348031550400c0a02c506190740305481e4100605d05080c80054101c174400f0780100308400707210304000041995040004030340c498520501c1c01599070010b001200003510030948007240a4031341e82c02e2021000d90701042410722540301b80380045e140c16410f0710491600b910100040d06000508050000c02c001c0451032003251107080030754803442d55488076020b6403403000f403082502c00e411000040c00381d21800d8004134220708005080300c3c102411a00001c180c060144c804a4840805120810040c080b1060318001404c04590b160705561600b000b042a0491804140042100000c0040d59a00c004040c100c06840b1a090f03440456840303162003030b121f5200b40b529410102c0b983e07009803158100003690741408080540500001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 606293857 1250 606292607 606292639
    0xf0c05030712051e18040c0206040b1b0705030c06060a0e0c0a091e0f06030b010c0b060a1502010509281704080a06060f0605030c0f031e090d0e03030306 67
    0x102072a12000411100308982104120000c2580300e515a403070310f4075070352802c6255800c0743c400485c624490140303083c02040b521180e000700f513081e803090700070170b404031195503000d0b00400c01103100c944031103440c0c0c021406806000b0000003900d00c560040003100c0030b6495180401c40c0c00c004d2403140740018801d02d00010201181c17803000c0d00c4200072078144111511b07110140ba10000c0044113401d1146030022000308203d1202e0710b4980c000700404c0c14204040c0c1030071400240954010300c4090411600c03800810416107984102c1030042041484500800510384802406040e040d07401c03503c180b14464a56117105840d000c0800c1d40083c01000c084401c40c1a580e80d400d1031624401d0814000342400001401c240600521004c0ca01c80c2d800003581600340406210241c07003035081101002000c0c003c0080700354403201110030070924218480e489540b11803411a07040030600c03072101507000302014400c84a400040004d0780701c1c0d064480a40c1484840103041d903074081103034980c0d802440c004000b00c00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 606294964 1107 606293857 606293873
    0x90709090206091c020a1505162a0e01090b0105030712090204060f06122c0106120807060506031b0607060b0316170a031706061b0d0f0c050307 63
    0x92280040401070844c080e031101145401001a040381c103011800d001042100c042141c02b840e515000059400d140036144035001c89521030100104213101c0c14065018680b07811f82d102c904643c0e0b00f090484484005140303180281d991907601030056280c1e03014141c05030000c905144881c5281117002001c800b00c0e04032039450b4900e4000c211143c100d01c0140014019440c00e400301c8214040341c240d0380140055800300350560340c811406c4d0b04114011010303085107401080d08200c1541c40300c050540f102c03070398081c0c02c40c0d12030070040082c03240c13504001410343c4d94043c503000214000c80c4000700340740030310b0392000d0aa142d08203081000082d281103c0340920355a080e014050461362076502814944409a00c0d440b0004a04006102500e0301c506031241403c41c2580052001d07141828943c440780c2d1184482c00041c0c00d1102000203078002e086920720031b9403040055145c02d906031540c80d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 606115107 606294964 := by
  have h0 := BRFrame.cov_init 606115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 606115107 ≤ n) (h2 : n < 606294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
