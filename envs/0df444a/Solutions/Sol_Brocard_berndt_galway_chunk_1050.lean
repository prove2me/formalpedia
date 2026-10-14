-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1050
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:00:38.228813+00:00
-- url     : https://prove2.me/submissions/5810c0f5-f516-4645-96d7-9c145448cec0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 188669064 ≤ n < 188848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 188670314 1250 188669064 188669087
    0x130b12010b1503010303080a1a0a060c030f02010b0102034e01090204060f030c11160305100216030804030e04110a030e1612020102070f08010b281202060712 69
    0x204140d03207402d03448981d12000c0b241a01e605945074006501c0b070407109000b070100b5142104031a0002202d811309622000d13031101c020110b6942c1c40a800d107003070901401001c07010306084116418043e6001c5c84c0d0760000125100358044101e105a1200d50013580c180c0341c80203408080313003030705003d40d544403544290040e207501040306001d100003640ea480f0140104e10a034402c04020030140c1e1540c0b00d886009500042c010406403e14484084040d4041818031010907001c0215900c07140d41070040c00f204220300c035490002c030700d0b0840c58030502050541c6400d8081400400b08490140010101807180c10814803250010340240040b06030841501c0d0b1075001340210100103031030310300e5a003805580041c8036001c511800039030340940f5017032404c0c081c50000030307680980c10b5118910000852250345003141c40101512000002c0394100082048000c0e04005150807004030021001c0e441c1da42081400011100386080340014203620380b01103a85406600c0c0301401c034000c88050402025004040e0600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 188671564 1250 188670314 188670319
    0x90303070510051b1c1107060501091a01140904020a18080109140d08190e0f0f010b0a0810020901030e01020a0305010e0109020708030402091e091c080702030306130b12010b 76
    0x4100d501d08020484d4000c0c3c2c0d441e03901c840d0f00004a100c842405502160080d004a041545024016100c5c001600c90a134082180642d442c54040c04882c02030288694001092900307a00d402e0704940701301c04900411440310f1069078000341c48071069000364021166090804840c000d29991201800e009100074101070b11101e00c2100311f50f4443c880440c0e03103c205802074803440405c1d107400b0a0007524400d00c2d200741511130355905001c648000104001094003060600609a00b0440b03003201d42915103c044060244080741e8007407080800201e10a0880c981901c401a10b650390000100c014124a4401a070f8951000503040b140e036505410880c140d030030840d942c1f03681e0703640d50703c00ea012442205400b030311490050001ca00140380c010120340e0490f110a08400910080c02007000745038a06540c0803801d0303482401c044007580c403400180d60104c1c9003410051010720748080041d49078400185494810780d000e0f102d6075501001ca80c0107400328180500180d0f44040030105090090100d15101807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 188672814 1250 188671564 188671591
    0xa03090305101413080f04090b04060503030c06040f03021204090203040605180a15060f0b0310060513030b0910050109140a06060c021003020708070303020d0e012009030307051005 79
    0x2821081038024520480303042c6010303c0d10369461106081c038040c044941103402d0701003001500754072070941d000340c8040c2004003000100101d0346420401101c14950109020f82c00600030625030410204800703a0094200f000340390300e4401460304074244040d02c130300c0e080d20100104000c520300070554091481580300b0b0400304126200c500b000010304211004100c4141e100180c4640040c5216480504000303200901140903030312101040d0314041503402803281c52201204200106601040321030061609051051601102035a00c0c038003800b650101a001c1d5802c00003180e84130340104040c084180756204104103c0d6140c560070b402415468102071150700032000402c40c00201c0b44941e20849556840f951950f03560350b404d00208000b41010041415401d200c0e07200420b001800605c076070340c82a5001a55905100f0085c000c841e990348048090380c0c580705100c01401c2c41a141060140948000d440e00c4034603c90000c1d29500c10014010124020f0b03030b401d4050b0b1b41c0030b0303084540911003249809 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 188674064 1250 188672814 188672833
    0x10f1802031608070b07030e150a09450903091d0c0d15090e0304210c09020c0c03070e04050606010f2304030f15061a03060f0607050a03090305 63
    0x710030540b50301916600c1d0304030010803c0302a040c01c00401031075100b8109a40e00100403c0025072128502c2000c6c3c0f510500012047e0449900c4680000a4982420303050300203482107039811510300080e40158540b908851400803142c008441c10203d40098050030300900c0898940100f60103524480c0c0c000c1c00b0400c65105080d904843d500c00d208404001c4580c0c01d1500e960021001b600102e041c5855071200d8a0b00030600c00c0741400394a0201004100075039a451900e404402222050b8203d01440560941e0b854005100602d680c01121401540941ca0701441e851090402201c181b29aa041c440d01c440080c0383c614400c0064400c9014400380d501c2d65039841c0c01550000ba04400b00700014054002c6016165800c07460240c0c541d04810015082980741d81d254010200d80010036543d002584c4100d001007119401403001819001d404000340d118042030000013800090180c503c20344040c00d03104515120f050583d009079070424201c544040060070040c08014140c082a200740c090304106 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 188675314 1250 188674064 188674093
    0x210090503210d272001050901050a03050919240b062203080a0810060318020105030a0e030703050c0606090709150c17220e010b0309010f180203 64
    0x105a40ca1500100701d207003a6403000030200402da41d0101c1c003a0794581648540a811000350b9a4030005d21810110380b070201084100030b00422541416810810b0400c60741969903441416111481e5072414041001c0d00c03850445410410b02c280c0c6070100804c110030103414000c0020400c9544026081840c600785416141d000a6680691040d60040c2c4100a0b078485840f03a4229001e2004d0000e1041c500b440d240e5403003a441c0ea02150700880001d00c180180906072086c00b1401c0014801c84c1804c201075412107100c001c0289004a01a0502c1400700008040341002d801c90500c1c0030307180055903983c44142c03802411503000703080c800a56210f0700c030018001c0d091010400c0d008214989804d400a443c0140080d00c00681c0104030f0100942c481080000030542d642035501c15074034038429612a444801301182085101c4945504c46282810070000d82800990540c1540c0e0b0031010140c1e00e5456010071805880c0701d001d2513940a02d0102c4a440d04413074400c401c0385543c400c4003580e0b861144800b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 188676564 1250 188675314 188675353
    0x91a120c0a0e0a0209040504030c060b0901151d06120702070b0702060f0706020c1006150c081b03190c06060503030307090506090d1403130b03010b040b0a0c0210090503 74
    0x85a9001094071400784400046040500d900280028001d0310f0580007a012405881c01660100c1c04141162221400c018050142041c0c004041e5200c5507950b140c00035100350150b142120200b07021480e41e10901301c040030f0714605c081203009030080c1da036900c14034954041400110740850050140040118456110404071000e85400820346418500200e08160265100e4441101e14a40c00c221503010000c081c40305000c820808040094400e14154540103215503000c034103003c2100c2d0080202c000f440c10380a54100004911403044124024003c0a20714400c0c541048020054402c50500981c0d0120310a00418803817282400b6980c1d0310720030300d5038a0200741c03840e0002c504204c07024030841c00c2110252544450042c030f0082c81902c0c64403130011607503031103545485907000081c6560149141c0f0102070010040d40305054a5985846080c5403540074900a00030503600000d08801c5451160001d0824103400030107045c543c4603001130180900c0d209201d442e009000780c0034007001c0c903000c00340d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 188677814 1250 188676564 188676583
    0x30a05090607020a020f0418060b03010b220b010c020a08071a040b0316050d06030b010e07090302030d0807021005010e070e010201020a090b07050109050d110c0901121407091a12 78
    0x10000c4c504920641e003048480981e852000750481d50b503500e0540d10072038400030b0305031030303402004001042040c0b507080c903013501c13050403155004807115140d0140c980907400c00111a255021000a20740d03041c41c00483d05001c401c0006503020022607408501c0d604086030301d0703084451030740c000900c0e403407888200c061601851182c4084801d040c40081c3c4c018900054081d8103c4003894218501400280f40c6411101950800c0d141e000c0304031300500101d60803a1045810078100e0030a130044903c0d650000303903161140d0000d2410803010704040340c0c0c0c0e1802000301d40c5403803401180500c0b80b50303103880200303038001011101c1d01c000a0301d000842c0d0341940188225084040c6a40e01c06c00c1c1a418020108020307803040c203084502d0340d0307141c035000007240d0700344440c28540c04141d0720702c0640b01101d03416900d001041401c0604c0741e14210010803420b07807410215507989034001c0030070b000300300755071420742c10500e565004078203660070b001c0120140304404408001420084071843c00040c0c84ca1045680c0729141e9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 188679064 1250 188677814 188677817
    0xa12140a0312061202010804060519020a0224220f02100c0209060103140a091509050307021905010e1309050a03020c0a06030e060103110a0308070602030f07030902150306010c021203030a05090607 86
    0x2207001c10003254043d0442540200d0080d4401408208bdaa940080342d00000401005070040e8981a9050104001e10040e19000e50343c28a158240940303c2610740002d1601c090844202032501d9041050402c510740300c031900145101c1402c14201c10203010304600c254200c4c405d0f0003100004105602900c01c00c0c880c0c42d000fa114003a580d48041d0344800404100d403080d03450500e0b0241c02000d02000e4016205103034441c8020356114506032051152161010840c065616071000d010703c03469912549043c070810341110b608446a41c0b500d0032200134401031a010740765000d4400c01b101403640026500284007010b43d1846011136665a00f02d007200d05100540340103402c00c200400c04190f00310301030032080d04003d0100d05041c0d46c0b6079a03410b403a40f21a100b107610030340100400140700e55207240d02d907001c440c070704003885940c855600241200407005075201d22020080081083c80c0d11170f440c00240d0381d60103080c22010b210742d502c04965a80046620710417407810a4001000880040741c01030041515 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 188680314 1250 188679064 188679077
    0x30e030d02060403030c0e030f0c010908070308030a0b010905030102032e0812090303120106020105060a050108090309010c0501020d09030c05190302030a140f07060b0102010b0f0a12140a031206120201 88
    0x2113640032009440301c20b1107001089009800c80400340d40070700c20600120454402444080202c1d00090948242d640c03051f622504140020400702c0d80c240222030b4429951240000e440c900000141e4621880344c0000d40c040d803010003002404201a405028914100d644010101d44002c0e003040c203c5a040c081c4112507000207840311080720500015080c0c504001741600e013418401030741e50b0240c110981c440001030f03450ba030034401141001400031025100a203031442040c90140c09144d074038452210910304001106080c0e8013404029030580e0128842d00b031060005503030382e00300241141c840f01d40c166094091504000604145501484425603154000e141440d4420303030705503050425905032070f400c00d40800c031000e520881500281503603032150000240722040e11000900b10ba480440e03076401600c1c2c04d90601c0e86640c1e00002c070021650224803014010026141c010300e0094101c0c10303040c040c4160480031040541040e180255442500c808104680c1c1e00c940145071000c15002c0603020500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 188681564 1250 188680314 188680321
    0x905070506091302180603040506160206100b0d0b060c030703110106031106030406060503011b0320031308250213091203020c0a0b0c18060705030d240909030e030d0206 74
    0x244c0c01130311003020000e24881402070311a021944d2544100c0d0110744c1500714800300142504c54907003004521409100910f1145801a072071b10b400c1c4c0c102d00460000f07035000710391181c02c096590403541218038060007840e2550a040031599480d00071340303011000b1440c458450820800c1c148190390441e504124140b54040303001d4207102c0ca9503c0900188c4181c0d44a507800709054074240541da095421a100280c000f50340008004c044420009004144211400c1483d40402d0482d00b9a40c020303c5580c0407980c41d01542c605a1074911031241034600e800c1d18143e6041c004900f52400c05081c5000b515030700c1035204210105411192030240081c802100742000241d400d1299000d002d25074130b00c204a811380401510761004c00e04003103a45c03481c1500c00081c0124000c1d400d001c041080481503401c0741c14210b088d0388043d100e01a2010907150940e4071400b02c00c6003051005441650180701c8413171040c1585841d0301801520201c0300540101e60070520002450500080880ea607040c0c03607008d0301d060744 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 188682814 1250 188681564 188681599
    0x306060108040212011b0e091005010809070f0e0108070501050a020304091505220e07030c050405090c090408070b10030f1202100f05010e2811041503090507050609 72
    0x49002d030040e07070042410486050803807024451005c565502400d01c070a9000300c1c0c00c1c02004c16a003504414058505101402041d540c4990b42000b81c0380242005d503040e0b541d00120604c1c001d41d40d4401000c8096003100060100d0800c541d050580c0c251100b581e50441d16034006480e0751081364400c1c4c1c0140c7c002c00c010481c0541c20341c0a00349425254510008156807000002c015504003859032141d1803084950303d00301d035007030300c40c8002642554020f02050351660300c80c42144800d6128081c0210348840005041030402d210f46180c45200429015032404c00303060007c40f03074200803011200c81540b0303804520001d1280000004882d0301ca0344c0b0f55412012540d9042121071445100420740c81000400c0019800500a406039044640e80c00149036141960318088100701030840174025210745050f40c1d03040d0703410702101502a01e8503008035841e0344500345580c9501c5a035201784800c0b624070340c065030741640c1500b00c21002c9024000b10390011b5150b60400c101480f5901149a0100048040740d0501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 188684064 1250 188682814 188682827
    0x27020309120d091208070e030105161b0204090302030309010606020316030c0c080102040b1309020301060c2a030f120e01121e02030c0705070803070203030703030924060906080c03060601 82
    0x240d8140d02e002c925182c1941d03806148104450280c2c0105050b6000c00c824968403d0400003900405c80082c40345007001d400d05024116413010790804c000c89049465404410308104000780d560140080010b0b00b4582402501c1c1d410940b00c0a4455080c50380c000f50081c400420b0350300c0302d81200780700c00c4d2119203541c05484d00701004004484215070120005a00c44003032015100910310520b034543e171040030302500d585e00310041e04a540828414401400810b0340701da071446240f0390008000c10b158140c0003c554503024840d00700320103401e00304404820091865101c07906207104440c408540c80d45001c0c2a45d000c22a034100c2c500154a000000c190450340303800401c44034000e90819444420101c1484c001c0e0b034001c0318030b80103e000000306a8200a010060780000b0f264000107036041086039800291280701c3e40706c001d410141c440c0380b50303000d10401d099032400c1001465010f0030600c021200c0c16001d044140705400906241c5030340054208030224666000740d0008003d80060b545500054610 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 188685314 1250 188684064 188684077
    0x1050d0201111b0a0b04180504050a0f03030b040609053303011b1b0c030602090a05031b01090b0c070e07051b15010504020903030d0c02030f042702030912 68
    0x41150152500b40031500922500d0f4910700e40600c426040d6074180284104140264424480b11a0400c400c0168540510240640c0316a8641c00705a030f0301e4504225103401c89624002c0d04400c0c0388001c1008041c0c059100e003004800544003882102c2d03030392905004450003103034400c07210b4102d50380b401e072501d0b841c5081c007a01110030240c80c07482030811000309007144c03404001842c100e60052210140340350008002440074150b600700c140c2c4403055a5807000c00d8182c512004101c0ca8022600072850764405403c5009840041d0454240c2c108103480800611881401703c1c3c045810580c001c030750b1940d00f008407030340c0031031140050107401d20700020003848001c02880c40080060500140303035005e0142a03000d001014401c0203048000b2140c100246c07144061b0300c031910441c4100003125044c3c60201c142d074040312490300c00181518001800380d0451162281010032806c1c005804a859528400360306100070b40b0b81c109100c00c00c61341d500c10f0120b100039500408a5846081c2c0d000c4070051840c000d052 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 188686564 1250 188685314 188685317
    0x112030f09090e0a1b0807120501020906270405011a071103070b0d0b0a06120506030a0b16030509030901020304050d080904020f280e06160503130305160e01050d0201 73
    0x403035079451042c1e4003264040030b4401002d8000010078014040e80454030810b5070368103006004064580f00702c3c40c3d42ca003194401e12a441400724504000e200d02981511044400580b11654a90982d1500c61064844803200b65070150756145d10a800c0c2802d109090584a208250911080700401c840c491a041500100c41c0f00382114000c410989052101c540223107031030402507803159803000c590b106403041c06071a64090641801e081010305e900029030b032040d0300012030011b666110400803a0038282059006491065900b040c1710420b14a0704800d40050640da1301044503403141c1705e800340c907446900c24650059005000c103201e2480d15825082c9070a01c20403065140010380d1022901341d81140c030300e600d0512004103025565800d00304006994044c08045114102504c0c44050110640c0c42410b0340106004203c0030744600094a002e00443d420904407034484280c04c0e002441da01d0749000032100c60007008242034120700010204002c0d100700d0710b50344881d6070034881407004c180c0340000160f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 188687814 1250 188686564 188686577
    0x111504020919061205030901090801090b180c040507110709150e19090c090e0c0a0303141308070305070e160503041a0702060103170c0c0d05070302031005060103060e0112030f 77
    0x50ba000d082c4411100300e5115101564468087c800050326020803070780424010f904140b4030000150182d030401e5800103007907231820050301c040380803140f62240d4180c10541142c5808140b2000ca42c201e0501600b10007100111080991034004410540d41c1101e01c150000d20700b50001d00a4103064004d0710b41c04401d5a80b0000324040b421103250603504503e605807880000550240050ba40f240601d4104141940040c02801441d01c003007a1000c1207440007404100704404e060040f10078a0302200c81600c5145d040100454442c0a51900c61541d48821541d520602c82c00003a07103400c0060252049020340781d48040040d0b008820b5580e680020030403281c3d40b9088056483c0202c4040300345c0d004a0940e0b00806d0251b045280c82e0001c80b1b40c510b5015003220b400c4c401080010f200103000070700c5803420303075040a0328051881e06c076142c801603800082d458019525000310143c01303580304620070902660305005444d07070b42c050b4071203401c03081c010142c2c01040d152541020a002c0c3e904042c10b0f407410301d0041c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 188689064 1250 188687814 188687819
    0x6210c0c1709030c010f080411031603050f070e010302060a050d090f050c0a06020f03090d21021005010614160f050303090a050c190e04050a06050711150402091906 72
    0x400e9504401e05206400c09020038036003050b09080000e0a01044207084c806131720542c50034058000317040200010316052181e8459501901c1c1400240031480c2050841110140c607071030025101c150044c0c04400310b20450340005084000e01e200a4122a000703403040303140058412088a941e4400c0811210f12a1103421000c002003100b803081d045c0501030005007600e1140001044224a0107034002c0d0304544c00b182440050480120840e250314031708440f400040040351078025200602e0156502e035100c220450066182d4001c0341e005441c03a50f5a10400444e81c991209803103000c403007805007d0b2020284480b02e210307252055460aa05d0240381581e51800d0642d039070b80d140d648120780e444403035081403c41c00d0410804112905155404880c520199200004032a49017180c0e44600385c0440b844c58017060511509001c1d810865400030303000c5c0803510303200c0740c054480c41e41040f80381c42c01c1c030564010007142010b0a01d10341c081c5034001c02d2009541c4502d200380d00080700d043e201c1c0c0500b070341d07840e0b00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 188690314 1250 188689064 188689073
    0xa0317090a03030512090601030c05062b0501050a060f02060a02030603030c0f03091314070f1404090902010f03140610090503010e0a020111120a031e2406210c0c 71
    0x1c40005600c6030b554035995409894a4100c01c20020f030180f05e01e40d001400603c0026015140c03001034600a81e4032680b5198001c80c2403103007180d4100e114442498003407034040c0c41101508400c0c141c0324252047c1d01c28581d5130350101c0d40150289040d10068001c00c01080b0000d00c1a0011600110020304990034048008500c0b424880c2c0c520000204d903000140201d2541404401003c0c00c1d540d59100f0020a0702d030340c081c0e051044008101e5402c11513801c854413220350241c00311400d503e8075072441580f680c1e02e0340c10312001440e0342581030740420b42d210f126501c20344c46030160440d2040703880c0c14500c3ca0345030402440f8800400811250a01c800100c011846072401d03c00c0da01c8607041103000b02000883c0d03000141c84010041d044194a41007031181891030704200701101c401e60840d20b000100030100d8450034100c2c01140140040307150501000003802c22504910200d920030344003814001c0303a90343d4029108c0b144100500201440030350901081b6804c10360040c00600035074101550784411581d01d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 188691564 1250 188690314 188690329
    0x6042a08031209010e010902010507062c07050414060120070519091b050313020103090f080d0b09090a1509060c0f02120a0801030813031e021c020a031709 68
    0x4450a9141280c0304003c0c54040902800d0358410201000700458890b54000928070311401ca8007600c0e40c0d84072811201c08007910b0404a4081000c0c0c001400c1704c060101c110f94542c411482200c1c8210308200d0f504900c80c010541c054011541619000c00c990b5001902c0c4503103d5126078968154026840c0010f060344403101c4403800c040318500c1301b42c1200e042403004000c5600019444c0c01d0f181c0c4a045662441d1f40040450341c00c00845861418481440c0c40103c6c054015040010600850b160600c010080072002a152030100202c09000d0070f41c0700e90a00c25a444100d809100b0b81d4440d17800140801e803030300e1400a050b1600d0001040c00c1905803510801d44041c000840c0020b4100f1080340d180c681d0602c031001080d00d840710750038500746c2030240090085506000280000400180b00c0990038498840c8134004c543c04010001010007200644615070350701c00d0268010026100d0801e88a00100103008076258010083c031042820760f26004e004072040304081030068003c000c55400340c0d44c9c580 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 188692814 1250 188691564 188691577
    0xc0412050a0213200c031c0e0a080702010f0e0603011203110303040c1d0907060807050909070305060117010b070b040c0305010612060c030b031015030f0f02030c0306042a0803 77
    0x6034085a40141d4090404032800b994007201c014072410301805c00c20130070200c2100d501502002d0400350b60046041414002c003c4010f11030000d2149040d42070400c528040981100e078000d80311502175045000054a149036144842e90340316800f00011701204d264141001c8120b03000e45440703054480900c00492031540107031415950000541c800b0850282300503e20200c206c40d08604821500344020200e6503050b43d4026601800310210001d5215441242a03403a100c1c80204000ea4600308400040c00a00007130740e03858002116001c200c20b402890900282c100d49200ea005445c2210a03103408030303142e0001c4c000700c4102ca08000c00001088007406100c01030460350310a44128002450b05204544a102e660418141006035801c0a9036000c224130142043c14040030544903001003040c0700b04503481d08001c141d40817050507501406414030aa001c01442941101c0d2207200240c10940c5d1988100c2e001008032a074420244c01c0301c1148080e00d151181415142c540341d949407a0714900719002032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 188694064 1250 188692814 188692849
    0x2040e0a060e1612050c090301020315150702030a08070206090a03060605011b0201020a0f15180501060801060506040303031107080c0a0c05010f0f2105010b0a08070203030c0412050a02 81
    0x10001400701d002008503050300100c0d81401ca1407500c031211406003802c00b6468181d00c8484c5e8500000c1c105c00c051782c08580c03150400030f0085540380b078109040420005801d0302c85001d0000d0044200d80481c43e40b0480f20440d0f0024020301c9070340b84941c0c4003880c0c3e901210089030000f60601810526407910000321000c0d500c00c51001c100242407100040404640a05020003004600030290250741c020449841454000c1e410240c3c0404505203182d0048510364901042c0b46010b4034413441480304080001001d05c035900900080ea40d0f05842ca0a84295024491740828200070400c0000e0280c0d0151840c440b00d001300301c0c204412901c4119042d040030322a0041900200c5159007003242100c02c1201801090a0236401d40320f440100500021440c0040024000e0506c40382201400c900c02030701e07083e01341d072000344070542c4c49003590f0183d80c100a5003400402e90344404954114004010340f407058404074001030601e0300d400312404011501d55000e44450240100c0790000d40c58100500f103040426 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 188695314 1250 188694064 188694071
    0x3030206071403040b13060b0a080a0506060607050d0804031103040902030a0b090106091401020a0605090307120f0804232b02060105030a06020c0f0d120e010b150d02040e0a 76
    0x86101400b4212100c1400d45040c10800412000418a8800e00c3c0c04c440710450208600405240ca00b0041901c652044da010f034201b031000524810005684000754071643c10b455850b240c01040c0001801002c500401c150000003580354458802c4645660280c000d107040000d05001d54401420740c0d0060300000340c01da80000c1080301c1c660403806000c01c100e40035260603c40358981103004041036864020320415000f10011145a07a100f04500461f95401810411941c207100c0d00a0799a0703803003c00110b0340c903a080b5640c40e01e91401510080006c074a9500c4440b800e50741c0d1344d54400f001c1d001402001c215407000501e0a4076a8042001c032074500810200d80743d800151031010b500c920b41c524030010841d0721400c0107020986000c190f0502c020740c003050168030b41c0d034001d19290030300c80680340d00c4d204d920030602401038180d0f10089803004108031050070041c414500803403074242e90f52394600c56005104250150402c600020042c00a44080d810050a007602e450040c420303403c4c29103400c4201078070b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 188696564 1250 188695314 188695321
    0x14150411150a09050f060702120601060e0315220b10061805060d0902060c03120f0604060302010203030613020405040f0e070e041e03030605090f0f1008070b0d1503030206 75
    0x140040c2200d500d440356046103082c207000c0785000b045100d0b680112801402d580c83d00540e9a164203080d03544042c1c0c000c3c94404104c00d03503068185d0f0791409100f05000500320032208100d80c1404a02078600072209403200b06140d0b01c001c05012600105120400c105c1c120001031004101e41c0e020f06800f4801040e1066203940c60640300070210802c40c00e01d80c1000b1b082050411059032100200c03504ca6201810204a030740d001d000044c41030259184801c102c0c000080c0e03411000140c8101244601340e64401502c51b521642e00f0b2004a4a9a001c02405070340100080f55051800982d5000003440041025150984400c041020794980c522240f070801c0e11120740902001b42070000001510314031152820b20b241079190801148022800520301409224040017454401c0d080400074007406000e03044642420340000d130034100200c4200355004040004a001d000c506104101192300e01402040c0d41d031708065610b2070b81e90100106003486507441c121b081d140074040e41505d000f94025000f522013484d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 188697814 1250 188696564 188696569
    0x150906030709091b17060f010602030d0f02090604060906030609090305090f0f0a0b07021f0903031404090504200d0201080a0b0d0f0305031b03040804090c02160b030106020c0301021614150411 84
    0x51b0040c0c00300c00c000f04883d005000322a400019103140ca101b40001140364040c04140400038410120740c0f5401000001780850301e282c20901c4c2e0f0741107c1d842d07607040107555911140d81084548401008000030010440d5a0841c54881008400640000c2045200000c0e803000140d4403100c83c0d000100001c07000c510403040d4501001c5207810000b0a89403000b00d016082001810b1140c240030050a01242c11144190701e061101541d000d010040c508003c3d5061a00303201100f0300c120041c0e481e007480303d00c4180751603090a00071425002d9060b12000e00c9510341590171406040361441540d0000c48440d002000f14480e0000105401e01948400faaa0b0600000d60b1175007940f0b0302c94031040341504006000c001030200044808a0780350100008030800c0c00e140c101e04201155500a004100c40400412500301540c0214122545034003100c0c0521000800d15081c0c0c06900401d9540c0c24000509101150754543c00e080f410725500156044a1001c2405d0f0002100558042d21101c518200709071460 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 188699064 1250 188697814 188697823
    0x60f06061e18030b040c030c060903060605040c0807120e01020711040b010c03050d0903090b0304150b0118150509031c0201051509150103061d150906030709091b17 72
    0x30740091600c81c0c0c2104603040c500c10520344510004250350b00d420001014400351058407806182c2c01a003401d5803075a1414000c200d01011300040ea0710b5854040c00042c0c0b45414858680644c0080d01e68083c941d841000c19980c1515280d54103000c2c80c2c0780d1402e004454000e20040c2040317407240920211001c5160140030071100136226940c1072040c81d02c014030119401c40261841c003403c082c5d000c503825201d0b242c11550007040e640014500b500c0401407008210703901c00d4108451a030340504002d46c0d07801400455190301840400c9078100d00302c04040c4011084440507031103c02041c10554581800032002c0b82c07906181e000007103540000015400d40142d8280211a08540001a01300002040100140d0b284001825124104040c200d030811564000c0c2c1002008001d2000110001180c58405222103501115007182401101c1031002d210300e49010304074000e50703000d0001c01e402810110380c000109a0403605480c405ca80c03480380304202e07402c42c10007070183c46402e0100701145440c80809160 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 188700314 1250 188699064 188699117
    0x140a05180402030c030408030705040e040819080c07060f091a041104090206031503071e17011803050a03182d111507050601030c0515070f030c060f0606 67
    0x181c0e00420a00c0201450403040c0d03a00310b6040044907903646c4421206841c035100700d602090305400d02004010600140c00041c0544074041c4050000c00b1082c07007411140032800701c0e484048102c0034002c150214100e54469564007074021000146003540341c840c604802040c3c02e02e00884007c10b401c100c04c00095024403503101006440a005421195000a80e18000203002e1003940003031f5515040e09650801045c0c00400d0070a1801001144030100c02640140300d01446d501003003d045c50980c442ca05200d501044180030500c5501c020641e40c049603103074020300301d48041585039014954038136101100601d045124650903450008400340280c9032600c0058405800720072801d0301030105444800d01c50070950203ca03c0c0f000a82a9280c054190148610241861250f14004401c10110866480940300204ca040343d080c104240b4042c090710585030010000801d008501e00003a00400070608410301c201e1001c40c010306043d400710200c0b6010b61240c400184200b044000b141c0140301c03038160 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 188701564 1250 188700314 188700319
    0x903020d0203031302130f050a0b01030c020705030339010b01090915140a0305060c0c01060e130b062d1c0f02060c0309060d09030e04022701140a0518 66
    0x11844c2015020580515045010340035034020b04070001031881c0ca5101c021449020306040015091154000005060f0b4060040c0070900e01100c5018450000a1520480d08018010340c40d248580340103507889482d2170418031310b60100d401140342d010032110b040210085c903c400043d000304c0c94000104060410352003c81514034200c44078502620f031400c1401a201ca81e440d0601036240d10002c00c6064580c1c0d40003800b54041d00c414000d00014400c01001c0174030041c03000b80a1a40c884883c2070342003009450824003016015038100009210320121940043d0040070001c6600000d60307041034440c03100b00b164400d140040b000a04514100180c030101d040040040c0a030300842d560380ba0300600700c0c44000307481040045501d40d0544000c1080b180b81044c05000c55485a080c1082c58024010840085022445d026180c00e01ca003080c3c801e0f1074501489103022074000ca00c0d10704100710b6103060030415040103120042201030b00e55a400516908640380d0b500e980c0c0740e9103104c41e4074030070f640111021b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 188702814 1250 188701564 188701567
    0xd02010c08090c0111070503010c0e04110405010507060507090b03040807140606030c150d02040e0108060a052512051504060b09090720070605040e0609160c020310020d0903020d0203 80
    0x30000d4000505000001c3d080c2800b20104c5010150140303099100ea000e540d040d03007031520052503107a1141c5181d41032401a101800504550b0420901c2402640111400581c1c1130100344040782d280d400a41d04030025090941d5526100d010a40c0c09a2081b03c3c00c4e0f0b0900c40c002107000c100302990303895021402d004005011607081035000651118540c201c0c82c0d1040c001480d02008940c0c400c01115860810350780119a51a51501140407400742407040b8026400781200040c646d107481d010301071142e07806894140c0f0320004142c040342c1c4070040c071a501040000a44410905035007600c80c0b54001d8034207155285241400208000680b0b0964008070381841c400d10102442c2d80710035410035008000c41c02e101000c0c88254840b00070341d11180804056910907080c000484a0b0081c1c0244195254501c51840640d2607c041c04811700c4240d42c1e1124000b074502058400911030901400e07200e03c000c040e0f80c03900c2c501100e03901c02e0781c0000038000c01c582d03901d00c030000805404006109101c0a54005507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 188704064 1250 188702814 188702821
    0xc0304030303142404021803031303030807020a0305070206070503120907090b010915230a050d0b040e0c04020318070e091c020303010504110409020d1401170303040210050403020d03020d02010c08 86
    0x8000741303000d1050600a80e0085944c0808500440e007490110350068107d03070310f603044008105210186444243d0206003007070007040e4a40d10104541c0f10f05a05900c4640c54007015509210a56100c05401c0d070b2140801c0c030112030b1001440c3c0707030940a00c4d814801044007038202580c0740300b1108550081d50601c580100100308002c5100401100f00b041800d01011076460102c803e0001e82072481b00f6208280d00041c40c64607217800001800c07940078143c50404c681c0c03034150b00344400c070b80403a0300422081c0d00c4030506c07044914054000b5031380690b542c1900c0404420402503d45000c0d075a07002402484c0c0c401c7c0401455100410440c0000c100541914a08154280002c3d40300e210600400b4010350722072580031504551030084500030010f8070310131942ca9003079200071301c010300c4540707441c1040b00d4002000103511040194640701c01200c58003d1403031030700d50f5403c1042440d002499102486428403002000d40c1d02c020300c05c2802400380d0090400c440e00c01c07800901710782d00b1400c54400d1208440c2070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 188705314 1250 188704064 188704111
    0x90e1513030c02061603022a090709090e01021b0c0109060c1b0303020d09062109020f1903030201050601020303070e010e120105010609090e0c01020c090c0c030403030314 75
    0x28540140000340821519842420100e44062214402079042000010f1808048a0603070040360045e00940c04c1d103074060944441c0300303041c10402508070a00540c191440c0e40354500a0710301904071045003040e01791280d031552000c040d142c20348603858043e5408070705020002203003d05020f44c40620400b403c2c10884240019000745040d00032841005102c441000400030410803080c0c55080300350003d4225940c03860021b44e106014004440014003e20001680900410310f10340c4035410064403074505684c2810800c000c20200e0010381c1c1c4080c2071544500306803940310320000d01c041041002c13003856065042c06030a454010b02502d045600820400c507000380e1055001a00a0b004d28050581c00300d4040041c2c440c4403001d41004865181c100001641a00912400f0840d0001d04090016040c15107100e82c030780048603070103030260700541d141c00404e1400d500501e61000c440c8840e1428101d40c6c010103461604690001c4000c260345003007510089015860b2140d20042c004040300c1e0290600b0a03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 188706564 1250 188705314 188705353
    0x70203120403171606090c051c17091c0303021201121106070201031b030b15071a1308030412091203020a0809060c0a0c03031e140a1116090e 62
    0x44001c00300010512403044d40310349261816a6070040000d0100180908111760f03c07024501c581d600c41d595003c40010498103540b5401c0c5041d4016448505040c14040c4002059000048050b4003134100380422080c48061080215541d0081e07038010b132280d959502a8801c0001a005511071070460f20302e01c030009071a403c009400035019a035031034903000c1e1740c03006a0240a5618034000801461710221600580c035034032040c1d1001c4102c80110a080316400d00044510407910040c010244100d050102490541d4036141c00c44a0000c1b51020813103540c07100d0710070350400d030b50403181c480f881d070884070900344e01c80c02c07010103040c1c038100d5182042c00070365020350b0303d462014000703003001c41c04135400150381e450300c2c281da048400500c1551091503640ca000110700800f404202c020a1100c0440c00b1901a0ae0000c4016202e482d114840c09074044c100305641604541060001c0254250f181210441d040c41008a07161b0171000e01c0c404642810080d40659082030416080e5900005821703c0310011282d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 188707814 1250 188706564 188706593
    0x40b06090112151d0a061b0e150921010f0e030d05070e030109032001020415080a0609061206060503030901020a1704030605010b071103010c050406180e0903070203120403 75
    0x240d4000b41010046048809020220300c41103110004100aa13101071000c11a422494851a020040c1d0062240120141180c000365200003403a83d2820001038200707104400c4074071100008180c00c09201c80001407461001c5c502c004046000310056800444003402410403184c2c1c482e00a000a0038040c8020b55607000e1708410380085601e46010400180c06011a04210200134009014040c11418042d00b91121f44000d00b00c081c3c400d1002e071801c0304061095070250b5100690080447c582c00d8012904044090201c242441d9501000a10300fa014828a4002d180418400d0785c85e0000c1c1c1041b40031121036501403400b9400030406900c03240c0c1d000c03680c0d003c11684940c9820817031490905134401030007650001010103182c040040b403d03180300c03800341641e14444d41c000c8524015500a0501f0388081294500c0820400d00080c080c0d0390040c120f5011000182541c0e140050f41d648000280740310549000801e5000094414154101444a6070f810300c0e207850700c90304c1d0924584e00d46040c500d000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 188709064 1250 188707814 188707823
    0xa080c1c1805070902131410080c0903061018090503030601140702060d14100f14060702090f01050a0801020c0c0111160303180608061e01200303040b06090112 70
    0x2440500314405402490152a503080000c0301c0c03030507071144c1d8410029403000d035943c07110b188400400a007c581d402040000d440c4c02074459150340783c3d00e070303801e440200000e014a41000d00038841681d1a48003041080d100d00c002055120405140c038202d030710380f41021089010b140e03050071b0308500410800800c0386e801038000e04e4150a40f4408070001d003118010b0301c000940c050000034110054946c20f4201440c08042c44080c20000d880d0007115528400d550300c0b980000003400360703082007403e10042004880680240c000340c40c000455000501440c8222000e03003800702d0660042c812402c040944c4000707808103c2c003c5103000413102c100f9668141d003815840c1000801c0d250000c41550500c1013410b0040d080d01c54036140350b10380c82d02906108506558040600422100040441c422140503004101c064603101905190111030711041065202c5141403010b040f54441030050100807400144840e00c024545a080500e07207803080c0d80c0090b108610540c0c186005100e50b200c0c005501e104e050b4031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 188710314 1250 188709064 188709071
    0x1e03021b06160b06190e040204090807051609050901020901020a0f0507230f090c0d1104080f0309100804080f1810020d0909230a090203030f0a080c1c 66
    0x102400210103215084800d40c009500001050402902d54401405604d0807502c151a040103604200349000071172040c400304070301c420042409800c16910101c6032500900311180782072615140c00d03141c11200c0310740310317051406c1003c00c0103892100c0c403d030b0ba00f05000c0c0000354908112440008c3d95101c060340058542400641d0744010000e08001c188010400038113100c171030a81042921500e40014031405015010040208405241c03060406103d81121200d03142013050303c030810310061100e07510807000b0180420001c02c0d00d01e0100800c0d840e20150b080113583d544680400c0c807400341e0000540005011300304080c000000e0120050b00c0203443d40350003064a03520b94a040c1e0505901d0409204d0300b14002ca881d0301c081c140e005c00d203c100c460b0b0a844000e0780c42c2e50703041e10608841e0510394220074003d06204480c01c100c04481039a4028129038030104e80a006900081c1c1180c2c4002c0c4140340b12070001490b10941030704181d0281d8000100a50301e408c00300c00040c0381c1043c600324a118091190b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 188711564 1250 188710314 188710363
    0x411060c0c270112050606030a0c060f0c0b01120611070206040e100f171501060207060c02031c050304050d02030c030f21090609010f020f040b092701031e0302 70
    0x58803007120b85403a0300075241143d5a403409603981c3c5180d00102903401d0300910000900d1802c00245080500780d1056a4060301da240c5a400c5070100c500c1010201082146200e50001c41c1e0400315044c00303440c0150050340002601e02e852000c60304800807482c2c036920140800750141c0e5841068074111504042c00d0300b016034030011210b21185c0c440c2c104842c02e030014000440c43c00b80360b91940001683c0142218128024800c024069181c00d02c07459005901800c81840124480e8a805118a20203000c07112400e24034071030012612081c00d0980f002070004001c020a003e810064070720b0500d22400a540b4040307a40d01d8080d103034071601d11011101c07100018031181120b030310440e810801800d8540c10500303040500c500da0b00c60b18140c549000135030030241d941319000400c0c422500401d55055019203810310b8000c915030643c11181c0a030354400343d044181c01e10051104840c500c1e184400044170450741c118070303110000020301c040c40403405e850f50b06a440002d0700050380d00b0a10001d200c00620401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 188712814 1250 188711564 188711599
    0x406090908031f1e230f01050904110c0102180105030c1206060d09030215071b0b100e0a0905070905060d1502040b1c18050a1e1a0411060c0c 62
    0x3d046a000d99070b5406040c3c0c02d85880d100303c036074440648a0f2441034440380714103410403080d6041108600d95100b10b010700a0030866001d5001081150310250001c40e626200c0240514030340c000ca11203c001d40d40000710440801020a03c0000031842401c02604500302524140c1d07881c010300341c101800d20360708004240d2556920f03081d1107031940d03840700a01041100e403400a441e41400e00018006c031301164046031000f8000c3e54501002c4202d072103840000c504541701c0740000a006403908142440180d80403500282c024002842801502d4002c00c0c0d10f01c2a282c064900305441d84820540c1c0e18060900080e666016840d007961500050351810200c034241c00307d0001d00c226401a1810140082d5860740c2200c0060380110603600c1c64401c00c00d0300c0801510207441140420700138101e070003698480c0006502c001c0342c45030716002c0f91050f012003425542c4400c2181e007081c0740114a4041d04040000304800f550605403107902c160b8105003803141111400d0783d03139660686440d1042e604582d047c5031b0b08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 188714064 1250 188712814 188712871
    0x80106030b031203040305070b0f130305090a0302151c0216060903030b210105010b0909041e05070605030f09010b030309060d090f060207020a14010e1c060c0806040609090803 77
    0x2640e83c00180e541e0341024900030302a81d0010004407060601c040018480841030036086100d0f5810400f540c00103200e994048800b0380c080d9850030342c4160701420120150703c8507503a01c0030069480136095a10901e65000360285035031010344040d03482c0100000328080346011107030a00198040c1d400704a0543c5864180d0203040c0055803039800501219100404041c0441c81516030001d200080101d80d80354214540300d8072070420b415070040c80c1880850005440700c50701e0560780d4900103007040019840d0761410308140b403a0707004000081c4040700f40914402401c007155040b00a40008001e0501440042926030041e4080035100f8540030a030360341a4140c6400c1126403a40c848503c0c450020b00346806d1009402c0340f003081e40189410400890041207003062401e9241050310b03800040d002c1329003041541c0c0850f03410f040010074a8001c0f00700003215030289881c00015511000718500e084014001114115400f06001c0ca0800b00b2840104020b00216030300320108800a8030648807800055400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 188715314 1250 188714064 188714083
    0x13050603130b25030e19150c030504030f020a030e01080a0e010504080c071a070809040e010e01051501090b0304061805070f080d09181a0604030c08070b0a080106030b03 74
    0x2d4400360010440c1000b18404100d103d065589603040a40d0041d6030101e040340d84101c100310140d0300c03a0307108051040b014940603100c98451601c90500440024240065844626800c00400e403034406000405420045101c0b840c04907100410b60010552001040407400032201c5040c003850002081e141d01c0103070090040c0080c203400034442410f06113444c52903548080c0000c3c813503003d0401c0102d911a003500c2598265488000800d041600c80d0b100c1c194698005a0f038680d0040ea0342e00050000e45080c00b500c0d1006020500014141ca44072644020908011040504000c0005011b00010200c081629001030f0042c0c0c000a1440003881404241c10820501400c0d51050300310004a0a070318010725010b403800380064590582c424141901d840c541c501960883c88031403140443d0003034481e4404420340e074545100312400070650001ca10300398000c0c0c005488240030050301f0f21211404025903801403024400c0b04e85041400c1c0b070000d115138418000c0c60100750300c40900d048140e40030841c0c1c002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 188716564 1250 188715314 188715323
    0x14130236040e10051f0f0312020303072015010e06041416110a02060f0403031103040506070f061103100f05090609160905090a1a010306080718061e0302090c1305060313 74
    0x1400c545814003100440c5047c4000c850801000300c1c1085520710100079280220030b180c5500d07503e80c0300e074401d11410031400e035074440080c8a0304102260b80501e00011a00820403076481000b5820b05c9810b01c01a141d440d02c2c0f0495034503008c014031003445c83c0c2548003801d144c010316010700c0080c41411100e082c4240840040d40c8514080340300150403200200420840780b094442000304208144410380f00d000e10301c15075a1004050200c2c401081001410310724083c800d16002035210a030030181d000980085e00d2402040c0742089040c0b200d24820b402c031001030242200d0206d0359180c00e4001510800700102413207108918803800c0d00000b0b00401c041c2c03024010083c50003155240a82408000740143c0460420944210071102c0465000707100305c1c0309a54428001c2e0407000e06016041e460080c40340309072000d007030759008000350743c0740704006004141300c1c0c140d1908085482c0d401000000302c000f4040b24806a0104001104c1320590030081c030072200107881c0b0989070340d0741d0782c07040c0d00f407102100c070190 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 188717814 1250 188716564 188716621
    0x1909170309060601020f120415110706110c0301050402150f0708030415110304150507050c011a01090605180d030309140105060909010614130236040e1005 68
    0x4000c0481d000f445903034207900f1245580c03a00030000390356140605842d10a82d070f041105000c0c00710141d000c40d80e0740321325080251802c190041e8661400d1640d6122100148607220744000c6d1800911144100a004038028061810141c00080800580c10018804a0400104c69581001d0030b0103598005400220703294591400b810589504134003114981441d614144a00315030601c81401e8900450b00071010041c1c1d00c0b000e2240c04020400035101806000d002d1080302e000d003000f4011350200e1030302207064404c0c03460800000341c0a08001d400c40000d000c0280001e101171507001f03404991007a4101e039052501c01c100d0405034014207000380040d000090039105024500c00542119000304000d4074060501e5840c2d00c1c86038202c0d45680681d0742aa401c00c0d00200e03182c949016181031500c030280005142141207030080401168031007840002049000c035050a200203001c0c0141200010f071400d0003050408041c0399190344e4107190340004940e942e40419001c3c61303120076070041c40c1c1241c01e018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 188719064 1250 188717814 188717821
    0xa0f0b03150406060b070b06130608070f14040605010f050304030e060c0c0a05010e0a03030c080d0c0f03050a0c081f030212030903010b060403051207150f0617010519091703 76
    0x1d6204581100e050302c407103003001c0d000a052400c400488500907088464424036455100c10011840100511054041c3d120000810500401d000c400c0003070041c1c0e40b00200759072900001e03040803819183c2461260f854003030204400c2c2d070001c0c0c2d00b4001022074505136981e69901d10741a5085003160750a60f4000c0400300c1c00e0521800001100545c80310110380d61000d40f5900c400456152030010a041c0d000030380c140d020000a4002c0d00d650249901ca01520b40c141500860003400704d4175840080300004808200d0300e10700301d0301b41c82400e42001e100350082c80003624045016003c8280502540a0321820104031092114054140e80103564010300b1000c11050348807400342c2d00c4d0064a0003503c203528061032101549003040440701144d070302c400a4240217002c02e00500482c4c010b000c0c29124010010300703000c2034640c203124410b8504001240020a0b604101005e03410180032044402641c0c50078040c03221400f81c05038810701284c60604085040011464840d14110107001424002c50010051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 188720314 1250 188719064 188719093
    0x3020d0b0a0e0319121a150909070203040e0c090907050c1006080106092906070201050f0c010c14070c050f010908010e06040204050f1306020a0309020d0c03030206090708060a0f0b03 80
    0x120f5520607070541d9185c14461000b151081100c641240352000080000140c07401d50030185807032500702504103042c41c144101038011601c01c10045805000580000800748170503490f0101007900111050307030716400e04d5503a10114000801c05013080c6d042c01008100c0103000304080003001104180e6039000d00055542e445600d001c2c080a014005800381480c00f8008041030201c120800388900c003103032904030480003080c0400c0d03038003074041641005130400c4650f4002c1c010a004000c8052100e00006104850303034001024401d2100901100110400404021418011094003075441c11203104420810410042e02d12003099440101c0950904161890560000c107159101d05e000381c0b028446d03645c444503100380c070620440b03090008000001c41400400d60617400740c00902c0c00ca08000030206403540004031524000c90302200c85c06e20040c020700130150705100b81d58102610b4001450880e0070702c42b05549031708005000f0f083c02641d50b1024402d40301d01d81c100800410011301603a41501c4003004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 188721564 1250 188720314 188720347
    0x5091f03061401050f1602040b09010e010602010c2c0307080111090a06020c090a05061305180c0109050a060804050a080309032113021908061e0105030703020d0b0a0e03 74
    0x1c986800d072a411603081d840d401042111074100036011704614120700440c01c02022110702070705a13040307580c0307116505040d2110f1055078060006200e0003034075507161200c002c3c00d548400c0825010042c20041184a642a80340e0b801c0440e112220440300b0155441c01003883d00b02c041e03008210541c20701850741e0208038010001e02040800b540c68007070150712541c1c2a80d0350f01500000c1070300444a04d0001d848041c21354032a135007240c0020140703145100d01c040c0400907550b0a07100d1002802d0074070410481082c0402181104910a0070045401440c0c400043c42207607a80c031503072061045140c009000c1000900000c1c1754140c3c0010450f40700d0070300548142d640d0b0811b040604c81002d40200046518001c0c0c414540304003040c00c0c50b811604c00079424003120404d04100f9010b812203141d40840c1112042c014030344070342e1088181e81d0035150102500c10783ca500687c8294081d4100010600c0561100c2020650040e00080000500d84503802e8880041c003500d0005202400f0210b81102107058261 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 188722814 1250 188721564 188721569
    0x405070e040605120a080a021914060f220201020102160f03020f012703050c120a140c07141201060f050103140f0a151802070c0b071205091f0306 64
    0x101c04100603a00e0343c0c14014100b40107451a201548141c80041c0000c3e07107800140b12070010751061b03420f441c800d0050320201c01c1500c0300469001c0300c2c0001580240404000c001e41c4500c0800c0ca04425050030054074668403d28801c296484440003482c80942e4000d4040313400708a0301d20f290002100e16820000719640e25508114018043c100055a10040500410794104e84401641c000b91303405000404d00000025000c40501c1010320442142580502c1304180225018401300ea036106098001001c01da01d40f00ba00f03921041c1440001c240c044006480016600601351101c02c503e0341d840000d0005444082e1031609600b40382003c51111a00d4480d030703040314000e0300c05021321482048075400c00102200c0c10a95054250f000a440c01f400350001c80750484040c0041403001d49885076040d022203001014814140c00103508001c0111000340c0200030040c04219900b482c0b044d41e25042500418207489082000c0404d43d09019907810b0748003d00d01583e00001030102201c01c4010780030742501e2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 188724064 1250 188722814 188722819
    0x53c0405010b09060904200f03030315010207060f12020f041203091a0307170a1508061501111f0605090a0e0c04050c0d0509030f07050f0c010c080306040f0b0405070e 73
    0x11000c84c0c0d05062106609009950080800c240512900444500340500006c0c40d0350003204040c141590344c40c18030007180164404100c80320394016220001e071a044c0e2541c440b00400c503190b59003801d90f9078055550001502c1000c000b50351a22025810ac0311401a50403000317000035502024004c0542196148089440450700700b01240c000346c01c10843c0c1e0104465000c04602c521058501c2205c136084440c0e407000c3c902038001a5030300b4ad818000001c1c0c1c02038000021075480202402000784803200c03813500c0c0235002d01e4032800c4901054042070720b0f0124201405064071031210036032075440d255000400540340151024a180c038000000c0c4001d0100d01c0c961103078500800241c60703141c1c01c02d400303180e100c1d0002e1521146000c9103071880e00014240145901941e02050240b040d00740f84020080424a01410007041c1194400c52247e083ca02d8081032a4103002842c4003500014040c0d0003a40d5212030708503400a2440341c0d00d80c041c03000e809150700080e072051900040101c1e45400540320781c02018103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 188725314 1250 188724064 188724079
    0x30501050708130b13050708150606190804050a060c051b1506060a020a14030403020a080c0102060402060714010c18050f0303090927030a030f053c0405010b 69
    0xd445003554200c2c0c040c0c0303442000c12000504000862044083d0b1a000000291035890180040e241d190504405800002041c4c2100d08801500c070300400e2220b411220445011345030091400400d000e01440400310030522402d100028103000c018041244a0ba4000809002c4212001c030020b0160340033544d50f50480441c2c2115845101c000a045645000b000714021380303949604040040a4009010700b0003107115150301e1000103a100090340a1380094a0000c40d151400d51041001000302a000007801780c2c40002c000d83c00382c0c3c0c001407407504a074042e01e046540c0c3d03516041265022501c05040452513090204145c1c80c150300030045030030840c003212084182030711070042005500d9044ca84a03819441072140c0c10380d5180901c0b6958101a0008440303800050104000b01d1803100505205603039040458102101500b600036614005d481c100c04005603e0400300360790041e003840a5880b00000050300044c0e0300c0d0b9000c0204098074111088000040c0b41501d0901c1c0601704200c003031030082d40e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 188726564 1250 188725314 188725321
    0x7050901121404020103050c04080703050307050606030d08040f0c1e06020f030703090311030a021f02071202061b0f0307060209120705010801140f130c09050619052d0403050105 78
    0x181e511500c603a0005001211466842d00c2c0c0044003c1c19000d40f00c1114101d0402002410341c400b00700344001548680007541d01d4500f2410217904108004080c1c034003c2d082a01c0c403c9415070b00c0076181c1c0d0b000758000c1c242c0c01496030904103441c091b2960303080868107040c4100c00c010031504841405084604d19400c4460720401740c0001d68503400782d80f000801003882c07804240006040480071501c010409001c03500c1c43c85041c2c00007043c40710440c02500f01c45c0e505400c4d20758441ea0500c81e02d0043d006210300d88960080b1755020516902c100310080c9035440302e0101c0403050070001d00c50351f0040d1110300116a200d01d030300d003030100081d070001001d2407003a600380511010072a0081503a41c12550305844440c41a840e0514198103840ca900d4201d50140d15440e4491842ea9030401020681071500703c0003c854480d0b01d0041d29400181d0423031032043c0700500501d829540001e42c428035050442c074100fa1103a0712500300c80710f500c2044001501c4200300384c903d0306d134030043c180242046a0042c4000d01075500c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 188727814 1250 188726564 188726597
    0x50319180603051f2102190e0f0604050103080415030605030706050405122b0207030602030f0a290402070c030203060408120709150522090c030c030209030a0b19020307050901 77
    0x1c60344a0810100b00a20014400c0d1515800400c51907002030040100708207044003200c4481f1140d0042c8140c800410f0130710100c3c01e42d020040394402c1054408010320b5055032501c6485028500c50209640303412a0002401c0d8840d410150040c807000e011125401d4841d140038010740c209003d00c40c01400349103025a1003880009450500c20fa1504161054036000700005014404070000c000c00c2d84908800040010000d00c01148a0902ea072320160450600d600e164090368400103503c0300075410040c00c8180380541c040700904000040340e005a54507602c1c40e10003110015540f002e541800f402d8100024040301d44018111031240000c00f0815039114401030f202d44210703000f000c100d02003070102500e003107000790b0040c40d004a0040321080c00b590013044500d1040032607004401c00765102d44468ac40075805008200c428500c6080035420f01c40c00601083e035910f150b0502500d82416803010844c0601c45d01e10395010021406405d41d6a40341109025001e0b52000c0d942500156a4003402e0700240f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 188729064 1250 188727814 188727871
    0xf0c0301060e060d02030a15050601030605010c1505090c0301090b070f02121608040e090a020a050105040506091302070b1608060f10031a0d0312050f0405031918060305 74
    0x840030381c80381460360740f600f4042c0240d6800071034007244c140c030510b52240301180c9040300e0744103000c074a0000403c3d54603102000506640c501e078041070502190400d01c2000400459120f0f003107045120380003425030f0380c50398002c1c031b4460798010071a095440c2c00002000e00451a110070b205554589901c1a0260382d000c040783c0d1403120b10b250482d011000c0c054010119118010005003034026842c8034201506c031081c01031002029100c014055024815200440c180442048020402402d01900707007840d08010070114481c1000d66486926090546160102c2690581d02c0c1301c0e40101c02c8450783e01d07110026112040c240c0a01c00c020400b6580007510511f4a480c1981c0000b0f0058070007030040541c2c07801034000e230440b020171100400c0d03050345c803905a488400c2203510081c0240daa01c2000108905d08004550307020700301c2d0f11810b641804120118000004079143c66100005484020071034034400c07100701c148900d0001480c0c41599000401e9580368206900618007424003002190080c008070104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 188730314 1250 188729064 188729069
    0xb0906030414030d0c02060a0501140d020f120a0305040f0f060f030c0207031e06060506090609060a030204050a0902030906070206063a03030204261203070516050f0c030106 76
    0xa000300001000182c12408402500740c0010449080040040a40d826500149249401a0b1092041080107417040c020340f8014500d003413082070924035440c0482d03654030700c0f440041d000760380520000100d40c4a00072054000c210340703003c1d10b504e85a545802005640700b0711644409043d411004213410904540e40c0c0c08417031840d103510080c0c120441082c2c005c2c0c03070070764114001c1d801021000408240f07061094048091208220f281041d10352806074102d035140c2e0002801040c2c140304824454581a04960301700104075292519105c01c01c004601a1080e90442a004080c0c000700150341e80c01600038501600d40c410039031345169181c10089a5441045038030981c0b08441610b4050b100a101c803414465130f06e80005801100d03e00d10404080500e01d5400300d0000c3c1d40002e0410680207049a40d04500b0b0014a094801080003200142e560291840302e40c044c070000000700780824014011190288a4014900c84980e030a003065a102d0405d01c401c0303403007401100300703200745854180b213507409 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 188731564 1250 188730314 188730319
    0x51507020309010c060b030609030d0c020a05300403031d0d0308011802071b0906080d02120a050c0a15060911190e0909010c12060b091302130f0f0b09 66
    0x40076101401161881403a4805444091b9180600ba8490b1014840c05116240640007507581c0e52101d000309040b40d50450030343d011900250202800520045000510f404090300910040e007071803040d02c00d044a05d04034200180b813000500104040c1c0281c0b50700d22444c90000c2404100396101c3c2407000284070400001c000491400061200821580505801c00b01e0601d005003448043c8c0d50300188880028211001003409440421842e001c600074100a02889000760150038030280000c3c0d55540102240001c0c080041118981d41d48540e0035202c02e440c4c103c0840b04106020706000d1030715189400e0349070641d820a1808501090107019600e00c841290b8121880c081e1450303c5610043d0800c0c007118100408511044207a0340e826401c0c43c0202002c000006e207542e005100607190945100d000f40c0e20a0400300308100c5403011a0036640904030585442400d05d031840c41510083c410100c0305a07400781866408501c00703c104106106848030746110034049a100d0885002d9070080e0100a603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 188732814 1250 188731564 188731567
    0x7081b03010620280c09140c070f0f0305070311070f06031116120f540e090106030b0615040905010e060f010309030807050a021c0203070515070203 65
    0x2201d500c0d02d010b00902d200c040080d911440a654125001c1241c0e0384c6081c0041c1030004005001c0c04802c0102c14010070b140b201c00c1200300c104190740071810800414000c40ca80021541134140700f0054000c1c003003180c0c00014011a20280d16019000b84c00484060303000484034290940d1181000035160213a6241c1d003a025600d500d000b07003c40180c106241112402d030010b00003108209440d0203201c02c2140300c0c029030811284110360041014001d1406402005640504000042c0a800808216103010312244d05101c0300301c00603c0380140c80300c0a5500786401200c0004440c020824210240e4066003000156034580100140c2660f00e1400b01401713192146000c1165842c004426120256030848090700b0240d6804444084880981c01303990281809000c00c060741ca025042c1c5d090000003424100150180d6840091008200a200d10300380080003d007211000c2c02004880306c14070000b0a01003060b801090000d4a941115104840c030744180754240030203074000e10340584109819401503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 188734064 1250 188732814 188732837
    0x210e0d170c01140106091802070c090e1c0504060201230a15090f06030c050103051303030f18111f0212030403090b160b0109021e03061807081b030106 66
    0xa0155911500d450340da030b90b5031a180c0900d2080c0c1c42c20b100d8001d220301d8464003d080d00c0c1500e2000b046c42c00c1c80224109a104118203000581d08020410984040c9500003403800c010a24140c50301d0644100485082078a201e5550f90941c40801031062f1415503000744160303100c2d0a042c900c04115101d800251300b500e03d000809031a096840845184500c10105625079500c207400e404441c05024411143c60300e43e04140700344034070060400010312084c0303000c00151502068a01d070342ca6500034014105500c4200031621503402e50009902a40390031100c2ca10340c24185060307203146500305c5685000c2c06038041e001c0c1446070301a0b032440070301842e9000b0303114801001d40c8100c41680010070403024070865040c0480c40b0040360003d4010302c50b200290b005003045e139041101100005034032001c94240100310b448405803200702e07000707104036400003400e4580d116800059180000c000031000000d0521080241c02940546c005000790750860800401031740507080c40609200034060310700410359020f00b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 188735314 1250 188734064 188734103
    0x3180f07060e060a022d01050c07030e0d03021f050f070804050601210c0e070e0316090f0608060709060f0806011b03020a0501060b0a021002181903210e0d 68
    0x1130030a15150b105650140a1000746606415030260420340d1440461081a031445030034450035400500e200c0c095820320516a400403c3d03481e4012095028010f06084041094020020307008159101400140c00100e03c448000c000d0104644c0040d4002c1c0c0c03600400d501502820f6080d010341c0d004400781055070b00300701c0488014403004143d400c04800005c5400080303070346540d0b1080501298900c454450038456401410341541004140c8280c100d04080c010445401810400700c840b0110040740d680b00502040006121aa10400d50343c02180c00300041c0940c4000c0040c151012030300c80714051040204102c1e09d0413001c82d40d103400300d0808074000c41c02d2000440349242042c03203071044810350700705a60b80a003902e09039403100030715035804070b030000c01d0300e406001560417060003400c1103050441069600a2020742c01102ca0700030f86420b54005d88220503600d121f0090358011134640d8507503a10f1070404d0903260514003584002070320a21105800d20380404005c100a4000d0702d03600d5424a007018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 188736564 1250 188735314 188735317
    0x90606050f1803060703020901030e060105032a03010204060201150b0301030b0403050304110d0b092401050402070f050610061205090d05030a060306090c091512120302040b03180f07060e06 83
    0x2e422000c0d20b20303032031803031603034003040b0580c85a60a6500580c444004c44005815114500350320720703203034104200502c0340f038400090004c009100d0b04000030000817483c04005100c485000915015400003602103103003038054000ba0b2804030300b4900e03410301d96900c1001d0001d41c0020b001c000c048880702d0020a0100b0311074009075404c01c2c05000007480c0c60701389800040566020100841e42441c500080205c40041071002514007088040308081042c4071f03801d0320581c6401401103d01c6580e0100d0b00d4400d0000001000c10300345c2d03100c400c80d11a42040b050203c142032440c442d04c400500c110800e040e607500340f0f004007801074a11900901c07a44402010503203041d04014201c0000c182e0781c0c0780000c0400d00c1406100c6107180a1661030000c9410a004802070310f4400c80741200f0f5410759002004200d40544098100300d402c40000300b003840740204200c010344a15030051034841400720a20030f1641d186001100407060a1041f182441e210070040c549843c803911540c0d0205405400c09550f07400c0000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 188737814 1250 188736564 188736577
    0x70518010909090b0103021c08031303110706030509060711060f04110402070b01091103041a06060706020301090e0c01030e100f02090306070c05101803051305091609090606050f 78
    0x421401c942e850344004400c0755034164040d504102864010410740c10800c3e000f400340040485103014003107494603580424072010302100b40ca101503603109800e040c481c0c11002c294001c50030560b101c096482000801418040d183c58805004010110320400d0081d1801003510301410040c11042c0c1c0c62034000d0f0003c42c00108141d8401c62500c8005030281e54500c0100b19152281ca4207481d11350600340725400301e4a03d80040300111400b0814403000c213002802c00940c0654034085200940e0f60365002c1001d5001d225001403035140048000718030700d9801d40024244110410484000d6007a40c030044090341c0c000341d4480915001b001c4030031184400c9400040340b90200704c80143c5802c2c0c4840c00701e842e2040031200751002030840ca6110080140500003c0d0800c02c1e201c400380208032049002e00032414013440010207002002800c1c0c00c0640c1181e50710b100405006020424500d001110303043e0b66101c4a40280001c0e60a800c04a28103425206036002e42d0950303910141083c7c0401c00320740c1da40c1d0111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 188739064 1250 188737814 188737817
    0xa052209050a03181503020a110f0703030206060a12021302070813080c09010e0610090506130e0c120118090507060f122702011103070c180509251a0a0905030607051801 74
    0xc0100000344104448206d070f800300070040020307510311700b37000b814100054040c62003241c4040040241402491078028003a404580c1c400f1101040c1c00768900a11550388014403c140c041a40a4010b800321406000c03126110b0035244001403034810001e40450034002c83c0c2e0a4041400490214100f03d02c101240d1540b0341415401d898403200004d01a420048601c070101c47e88260074001c01140b1011030703400a40b0b40124500f000c1f50b80e000591a448140036064598040003c0844070038183e420041c08190090150b84005440b014001c2c06060364040940218401c60400d2404c1d0310a403082d22562401e11801450301c0d5241c8bc0b80055006080405038100094205600ea814200780004c05c0300c01d1040c504070741c0041c03610445d0300c0d45400180c002090070b0700d0303c020001d502c040031507450116207101c10b103032070200c0901c0ca10010030001900440140c01d403456035144103422107001081100d04d9622030041156a82d000c0559440301215102e000032410b1220350348146200702000c2c1d540405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 188740314 1250 188739064 188739077
    0x17011a013b0915040c1b0204020f090d0609030305060d021e15040807080c0a0b03180304090c050702030c0910030807080d09060f1a0a052209050a03181503020a 70
    0x140010b0849102a14080d05491074070011001d50310b41031041c104500c8141c00c0001880b8079501046d90b2240081078041c1c0620340014503050280309000459400c21401828002800e41a04150000f00341c8044110080791403d80880d045180440500b01d10650040c0140b006503c0075800c031103414002c1c018584c2042c520000c4104105008000e4000307081d8040007042410302d00110980b40c400c240714054080c00100c1000c1c04180c00700d000322035100310045841080444024201851032040d0351058000c0361030820899003450f4080c0c002e00030a1b001320121000840214104101070405859501c04180781000410020742c0034009071568501801849060400030005002a210b4228088400d581d0361040d034800e00019101700d00319004074540c000b14829010f0081703800442c81d409a18454003018203048107100d0112032115101003912000d101c21b0107180b40240c3e840060210031000305100d94001c0e016400120b980e002150b541c07a0b58807064252801042d07000790f1003281c0e00c0041011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 188741564 1250 188740314 188740427
    0x7060b0402070b19020304030518010c05030309030a0311040b030103020d08040504060e010305061501050406030b030316061e0b060304081b0a050d170903070303021317011a01 77
    0x221071016000b07481c05000b01c0c2c003051801507000340b4490307003803001e40140d40d1040c07051101103503000096402e40810138484c036100059400041e203104010340f10080041c403001007000207030b24020000d003807540d80a49040c00122a0240c01220303070300882c0140040e8050500040000d4605014281011030080d605203140c00e4440c0301107020f03201150008150794090f8001002048010003245500c182c0490740c0c1c044454020000a00511032840707640100b58645600c05c0f003035034091044038400c60782035600341100d50503494002c0207802070741c1900c00c401114064428001d038180c040d014481000406461450303403580c0e650142c5400040c8d030100e10100049140712500402c01104020b00d00071307001005216040e510003001c00c013010b9030b17900903602c501d020f20911043c00416951b210f41e0500b400f50715100402c0c050b00410109500860540b226071408901441044d84031440240c0f540d01d000b240c510b210001501d078403680d038010300001440d99540d00824aa05113003c8422441d10040004004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 188742814 1250 188741564 188741569
    0x30402060d05091c020309010206070513090e071d01060c1b080607022802010512040501182603061809071805090c1009031709041424030d0507060b 65
    0x304100d0300c43c545640480c00084503004184428540524140300461408100100003922107402034002414004041585c84012086c0b00080c1c020f0315070300e07074100501e16809040e0743c0c1e601c00911408400700b440b07103800341c001c201020030503050f02c1c0d40e51680e00c1111519960075040e201c520a010002100461001c110307190180141401041241d00504d50031040c1e0007403144005002601c09080c40002d1202c40042c0d0b08001942c1d4089103503504106c065a460600e11301403e030f82c41c030000c1e50320440103000c01041500b603415200b01001112480001c081d0000054041c402605c1050f07110110f02c5600d071800e002d2000440c1c1c00b20580c015540283d40c0c8401500e0a107001411600140e41c8842c200110444100140c0798103a8003258806245501c500c8060001d00e0305020282c0070312110080c0302080030704a800c45412810152080001510120400c523451b01c040e501150444000e01840c081d03034807940d580e410501c400601400e0801c00d00c00e0282c81a5000c503104403000d5403110446501903 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 188744064 1250 188742814 188742821
    0x70807051c14060f0a05010804080c01060608010f082805010609021b012a080a1503030302120609042301060504021303120203070308131a0108011a180606030402060d 73
    0x90240c04010076602d180c61442080001c00420050090700c80b40254503e5507180601142143c1d02820441c21580700c41c18509450702c503005c1a05e9040d802c0c580005052603010840c3d038101e61440c03007541041c030f40300d034030840d00d803601c0000311381460a641c2e0706a1a260980c21848221134460343c000520181e0b2048820241d8001c0d900310307020241c0704803580089540a004036080c50003045000d07080210085075025640e010240d10000704402000090610446a0300052403510290440e070001d65882c5001130107940301d469248041390150000c15000d003401005035004d1a489591000603940c0c0007801e0307001c1160007145280d5592070f0400003ca544030381c0f0080c4901d9060844d59021242141400d00f01c91003585c0051085500401540380400c0c0d00401054001a410440c5614400a420140300725401001c816001c1400c2200004074514154400b096034200e51b660000c0905100081210a80303080110348400f860010004a5501e002c90041d50301a100401d00d90402e05500c8100d41203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 188745314 1250 188744064 188744107
    0xa1d03060c090607061a03010606050909011208040b0301121101020f0c0405270102070b0c1206130906050708040b0903070302070e18030a030b0a050922050c06071a07020708030307080705 82
    0x10000d8480e050400c87c02c00b030042130080c040c9030410a103004000000708401030814401ca22489580020078030403c40c1c441c0841e80100402405142c0f17958582c1202c0200441354042200d00c0031315060801d825500100b01050300702070120141000e5003028050202414008011551080403464804840d45106580282051100d4001038854000389009100b84d407002d03000045414041c400c0c03d042c550f811942c1c1c0d900c580203903441d038480348010200001400c400791f0020841410501000019540260030a00c00c40c020b007608469511a440c07030945920903964043c0068000c8107042c418000717540300d8503402402040c00950b0710350541d2442070854000c801c1e91800240c441c024840d1a01d000760895014000884615040b030821904240ca01d18103030001d000c85a44020803a0306020050050a00000c40982566070b00c4e010361800381e1102141340c0c00c01e2014030746d420208d41a03a20018404080c1c41070903001b54603503100c90382d00381c5901000070103443c02c22104010019005170350060000f82c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 188746564 1250 188745314 188745341
    0xb07020f12150105040c0e100c0503070803040807050106050f01050f1e0a17010602061501081306051008100903080f0c0f0706020406080a0b01080115030e010c050a1d03060c09060706 80
    0x41c694145401c000035a1606c401e5202000880c0c280c0704420365408908560220a906081808482d0f42c501641540108039018012100120130841404000b000070702841e441600200141602c6004221820010181c000d000034018041e02800030516002440d0550200300c00ca9030140d00c0102000241c0d0201035541c00040c4068012046000d200c114640545400e0010340018580301d0542510000c282007100d041100800104031610384003040c2d000c8c01a000001401185000c0880d101d00728660b00c40d040551042c41c1000e00304020b144a481d0f551a4580d0703c2c04040d0300d0707a01055410400103860404480020800d041002d180300c7d004000c0380344904e10140e11585004000f034501d9030028940d640302800d110344070a85a03030040d4501d054a5201d0507440f80399080020072002010652089886507190140d02100107401c40090a20b11000c3e81d41e40c285042c60030024821000c0b4a090035805030302000200d00c19540c05c1c80030b88504500642541d0824881e40c40d101d00742d8a10540e0142c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 188747814 1250 188746564 188746603
    0x60e130c180801061802030c090a03110f06070b010b07020a08100504061802010c06050a1508010902030607180509060105090301051611070f0b0c120409240b07020f12 73
    0x8030190741d891050300c01042218020816549840b409a01030011801e03100d10803503000002482e442042025100d5010014101001090300e900e0b1880310700406119851140c04038146605c200c0c58120210b0328016807042d10001a41d18080304440c058004910803684452210404a99104104849848001030781c01c0071031503042c14100070f01111030b191004001c2c00754400c00d800150744c11140f8202685d9010b000020300b40ea6003001040200490100d801943c07130160301c0020a01c01c1504991100780c002c070181c40304c0740c80f04141a5690800c14106842c00c841a1208000c0e902e80101c050340c0c09441810114980300c0140c002178210303401142c0440b110711003510030404240e4803021514006240320f0090a140f4100402c81c1030002171485100e094600c00907040e10306000c01d0108210002010f01c4c01d58459403500d80003030203404862606140c0d4005896040030014000c1c2040e400c680c4080711092404c0307295009e00c20807504420349030760440b8844e28494841503080100c41d65182c03502c400e85 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 188749064 1250 188747814 188747837
    0x5010219060b1e1e030c1318060e0d0806180a06030c0b0309120a020a060509070308030907060e18040201030b04090b161b020102150a141305010c1404060e130c 70
    0x2104135484001d80c1c43c14454031403403001c0592400100304c40300100403500c50180d41221032441c0c01400d119a00d031316030324907000041703001c2004a400c42031108400900f0341e110441c0d94901102c0d04030301210038075400b0170540811151113100e1320019400c49050705004c9105601c07500c58076441551540a00f054413800420004248020f001c3d150010086004e00d03450200600c800070b55500b01d10704007806e15581e035404503008080030002100195400030640d61280317803690003251161520b109a8000c40c080501705545442e00411580c10b21028015840464485030011070080c00352100030f076013099880480740c0c007040e10b1400a0b84039020030015000d0b08619204001c00150000c0c02104a03a11f502d00d51200603a004101c11740c005416a10b00006a550410f0440150060000c0400078581c0314080c0071581c0c160014818645010380024810b150300c2050449038119111000c0b00e01000134003040c011180708d501801c0c522040100118807240c143d401c800d040307501a0151001255602818 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 188750314 1250 188749064 188749069
    0x3111908100b0433021c020a0302120d09060609020d0f02070b0705090d06090308041a070801090e010b040501092307020c09040c03050f061f05010219060b1e 69
    0x1d50000d01071004254051900c0c6042296000d14003504142c0e007111146491100810405040c0000d0942a1481c1c011810702019403510b17139081008142c0490300d002c1864081c0005001a046541903005142403414070b003000540b0740110203800e0303499841c0d42d140c00c0802c103140107480c0642080c510050b034541c40300d01c428044a40080d0b82d0ba40c0d40340140300d030f42c02040c0300300f07962a405a6182407060350b498103500010300f002a001d100910987c0741480f01401c1c180d111005612480c8210240442c681140c0203103101a1001c9500400003092100107220781b254507000032450480003c000300390720662800040c00e49009810502c81c41d41c0e00c130b080c0601c24140c01555500300c400b04012801e51f0078400ca009444150100c40742c0e001e05503000224007003142ca81410001103803c0701c166400750140d641e020b074072003c043d5152483c240184000001a01c01c110312a811590142c00030041c3c5013000400304491100078000307032a175694030946192152a400d4040c03680c92281c0303150100c0030544030f08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 188751564 1250 188750314 188750327
    0x3080703060915140303040f17010c110a032f01142d100f090e06070206160809030c0f06090708031603080406110c1609050408041203031119 62
    0x3081d1640e08000e803045030149250650410754013240040e07891800c06002091a52085520a051451690390700241c103034030908170301290b1002c036002800540c01e01c070802ca406254145074a045c40d0407a0750100c0010340512111a4003e4078070801d012000c2d036448190254804c10441e00703a040e511042a040c11860740900c2a5110044104640c0414121040c5249460140d10001304044403840811303402040880311400a0420a192070030b419160050f4001800c0c07408a55111480f458000c42c4016002154251249400344c0041ca81445003400072200010040d1000301c41d400100001c034184030b01440700310182402540205498105404010b14002d440d034000c541a81007400040c290340045201d414500790189400e6181c0d4446040850007040443e45240b0056800aa10310b10484045041c03001a0640100400c030980c0e604c2d01042a0765044030000c009290811007482200356041c000c3d078200b13019240c0050000002815922107510520082c00907030400729070703801e00a52205 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 188752814 1250 188751564 188751569
    0x5011b0306080d050f0c0109060603141605030c0f040f05090703150603050601060305071b0c170c03030901180305160e09011a061e03130b0105150307030c14070308070306 75
    0x50040038203484030200101280680d401845e100c0e40c1c0003502e003981440c01d4209100464200204121050b500d1801291110171150419501d01a05200c1d85a1124001034101211000f42c054140240d1140c200640e03885d00a10b0b17503074856501d256446001c90280b0455101d1240400200906801e60501d04008024900c0401102c0c0c01e001c0c06000141c0041040b504407549030030082484d407980042964818001c4201e00f140100f07503040c91050084000340c103c04c031005a00d0810003051450716160301c4080141481d134059004000c01d4206500c248201c0a2003480c030164010303c5601d07503aa89043c2a0b0000540304000c80c1d80030184003070179032512420307004200ca50003008a40b040960136801c000d00003294a205480110384141490181415030001c2240004d205542e4074185207646d01c84802c00c02c0c01c0d0703400540880081002d08018500c9640707201420455030941d50784110880c0a802c5814184007007104d00311500e491010700c0409802024800d855850f95031030420001002c0360001d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 188754064 1250 188752814 188752829
    0x1401090803130501080c04120b0a0608010204030c031b031a09010f09110f03070f08060a0e01020c060c160b010e091006050a0308070c050a24091410020a05011b0306 72
    0x104460b0003a6201c24038280c048601c2800d1400c503e58030341c1402d4203617014951240c540d20188800740c00810100b5514103204d02d00300074040206075200c420203400c0780038501000784030210f03980050012aaa9251211528001c440c0500c0310940329a00c113941c15403020001d950403d6184107002c1c4120081c0552140a0f136500000c0014003c1030b01c560510400000c20a4000e0303a03140303da0503580d2001c1c415040908101c078803140c02d490703544035080e03a0703008226901c110051038414100221030044c001c540e94142541c1c01071483c0d455040f040d20b240d0740600074002848180c188540d0004501040080c020140c051a40f401850904140c60074490000e1050a1140c50b02205000380e580d0400c00c00c080da90090b00d400c1e00c540c01881c21380015015500180d0b408240c2c07000008031180801445e603a004208003440c140c2850011060b074501006009801c0408807141204c05a804e20180708482c003502807044481185654540f00e08685a400402c0b2004016040070f80b81c46400d40035410041100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 188755314 1250 188754064 188754067
    0x3020411030a0b0f1305070c050615030c030102040e0f1503070b07062f09060408060906010302030f030c030f07050a060f0e01061202060a0f02071d04030f0516020603060d06061401090803 82
    0x111000031a903180e100345c1c8110701030303442c03010912082c03260281300000f0380d0100c1110205d041685c080b950300c40109156620a1085c4086800282818020384040302c402e036101100303035181c282d40c05808401c010503500c007640503400000719980d402c000060082042e0055595a0942424071009550b80395421401a0703400c5884c6d0310307040c81d420b084084945007052606032500a254001101e40c41103034005020751058005100c0c0c4c40384040340060480b4400c4040715609401c6c051050f45038041c99000c03d803203410a200c5c1100103031700c0c1e03802000040e1190303041d00d8044c01c0f2699180e0445001c00211000140e40702414106440f007480b0319405030010302041c4001030015070020787c140c81491050402c0000c241d5980e20b0341c074020408940606002d150703009400e81d9503451050104c40c11101600011000202d04a01030f01800803106001c461000f04202800141c0911555a00142400390002d80c0006e0358000b1881c1071140f28041d0103a00320261600030a80e0006000c200d098119a41030f400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 188756564 1250 188755314 188755339
    0x5100b090f060d09053a0801060f032304020112060506220803040b1305011115040c0b040f080d021203190603021c062007081303020411030a0b 63
    0x5a000e10140c071490704030740031540c0c0c49524401001804080c2d000905a10a240c84640740080640c0b000403110804014010000b039480b4110100310582c8904201051590f40107010302441482c122b40307018080e04011404a07000c0204900c40380c40c81c1c2d015009110fa070024802103682c81401c00b5002034600c0c005001c514241400124148107080100000c4280c94144010119526008600070040e00d02901c0c0c442ea540e40c0c40c00807952026012080a1200c45804159580110203e14a09400d20b0041c10454210140007088503409081500c020a81c0c50000800301d1103a0b00410141ca03009201000da0f51070030058034502403070141703200259046035887c1e2000d95201d4003030701d6010f00107480c0b80700c1d1520340c0442e400044c4060341001e03400c801c1c015880c07120000802400030902e031165004000c0b0314048100041c0c0e00f0444040d40d002110108030103408142840085c003041c0040c0104410350580c2c0c0d50018044503c11075504018000110821a4844080c494901c20040c25190840d5000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 188757814 1250 188756564 188756569
    0x609011712180406081509030a090b0a030b0a17060109110304021e09180d0806060a030b04150e01081009080a03022a0606120a0c05040b0607051005100b09 68
    0x203a09540814512202280810104882e80e412110310303400900100310494440ca80a521000840c41b580300d0b0a400201240741040b000040b00c03a911000c0da0b40088450801d0402103159001b0240700007059107440e01c4000c0c9544180c7c40070001d00800b09a15290080200b210381003c0c0140c0c051001c0364600f0518282d81040300048036449941180c0080c00348001c40c40281070011011409500688140100000e00c80c0c20030319102c42054000c22520f442045440031201c03504100c0300f140d08a82c041c8841207600c0e000780c1010031401802000403810026007042c410710080641e011a01004d4000d00401c0f0046007440f0150031080005030a000814444e11001e00500c1100c0012041590008064225101015000c0b1090340c502e200c4207040c507410300c0203568801c000c0e9042c070700ca4500c09007000f0340908005016408107a0000030b0304525440c103400c100060003154415600650708000080c001601403211190800580782e00040b9400e0070088405100309503044050140410001c44810340d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 188759064 1250 188757814 188757823
    0x5030108071505040b0309010c09170703030305060f040906020304140609070e040c050d0c0807050406050112020c01090f0302150c090607060f0209042d0207120302071a040b06090117 80
    0x200c0800c0310070300c400c442c210340481d01032082d540243c034000000700901c0510300d810b402c0540201406e68401c414661a5000061102100e2000b403006500030303881080080d01a81109a000b40300800080e81900d803400401c0030340b64003444c12524203500000304010042d406243d006003807541c80c000d02c03103460000d0f40566621228080d10b1f000440c80b034000340411000c134a000c80a0a0050b040301d8404403a4031f8982024030030ba009021645c020590041036504007031103400d08940b8140d40e02401c04541840b0f0400030744c4260781224180d503c901109011990032908480584d100740d0050000d40511094906002809800c00150340020010004160394035015246581d400560014041c000c81000d9802031182c24410f64101d41032401c10169000d143c610440351030000c01e41040d0740c0c0042d6061100700d2240f03450003404801480b8640964038466130181c02e50603c45c0e1118543e440000141c0525000c1c00c540c00c4840c2d2026404008580c2851004140101040c018504449180740ba00319240c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 188760314 1250 188759064 188759069
    0x210c0703030b040f2301060e01020705120115062c060a0f030b2101060504060b12130218150114160f08040e10150f1407020a0e0106030c0503010807 65
    0x42544400c5442d615980e07650101e450395a0040b01084210300d115103414985103410001c0300d00504071000000c200c0d002d0200003a0300300059021b403c2ca1400c0c0320402c03e402070080070310440c544d84e510b052b10407200d1042d1a000a4160342c0ca5205111400c4002107884d10310919003840c8980031a4101c1c14992902c0302500c01f4110303142004500c00703485400c110f005000710b424199002507a0388944005000702600076980c074200000a200c0651603e0500058134014412071511110800c0440c10802c000c0b00860f410590004001802c3c0d10305070001030390750365100d1001920313512080500141c9980c103038141c1c001000030300303086172107901d2040020158010300605050010440403080204100809560280d81d40550700d41c2e00c40b078954613a044a044116280c1d1803040c500d4002142c241e00c6009007428a0456070f40b07444a00b103084c201220300c482400e9041000c14002d0040f013006a40b006044800b800c01d070000300c4c41c3c0398940f00b0010140c41c280c01c806010b1090401c01800b480b41c01140000a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 188761564 1250 188760314 188760317
    0x30a1e06150e06120a05090708060610030504080c0303070f03050108011a04020904020c010e030309070b0c070b090d0f030f03180f060209031204030b1b1c0b030102041505210c0703 79
    0x30b80300b61010100b14a4030844042182070a42c80303041250300d82c0e0359400680200c0a20f070880700b20035142c0201582d0340000759400c951000c1900b16501c1d103140b198012650161180610b07038245400a540300c0c2c519002910518041405940c01540042d850300c50786005000740301c000c0c4006200d01c0c2c0c0102051444101007401135400040c080c0e095100c0d60112510501080020080314003110341583d282d8000b40c07414034490050303002c0064400f0500c026200155030718005083c01e14a000c4d0100042d501c503940144c1c01060320000b1030701152401500507000d0340243c41d482412098044002c044800160511315240900500c0707501280041c0388040c515a4028401a0f40311060710000340762a401c90048140709200080c04010004200301d0303c0d0203400b1180c0c06540d40d013944004540e19010303440904c01e0b040c3c0e2149880d002800e9a800c41144200060300051401d03481d040000c090301d61510700180800c03000143c0b8198515510012140c1201b240d0254000d400c266541c8030961090050140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 188762814 1250 188761564 188761577
    0xc030105091503030913202b0605060325050a1b0c090912080702030306060304020d0f020a06020106080610052d0a060806040e0c0319080708030a1e0615 67
    0x1000d07620b08004a403035080c801401780180801b140010009060a00f81032984a160024900001c040850079244000c00c0258005050403c40000504150341c9041c00e030460780e10340d100001c0548540c0025070080404110f65500c0b078242c2908030400303103810790f200810000700700f0540e1a803980c441e440000360f442c451300e105145085400c0204403101143c00030040386142104907000c204c0160314034119400d6584449071503984100080c0e860303000440310150040e004100040041c9400302000301e0f428800c601c0000b4100c007a4011900c803900b517811180140c0c0d55aa02032282d4031003042030b1903002c000c00c03070640301e0703941040c011030001200ca82c001220020100918200001482107400e50580301a008400c2981e03030710001065400280c90544c01113103424034201c14132801048c5114070200c0500100840019840048400784041400740c8114406202e11000200090001c6002f80d50740340d40411b9103400310718903240d891410710540038034510344801004440c451f4554520048841e00300398 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 188764064 1250 188762814 188762851
    0x3080904020c010608070603090317040206090d0203030c010f02030a0b0f150309030724050c072d050304030f0c080a03091e09090b0411030705031504030c0b0103050d02060c03010509 80
    0xba030141200b50040f5076503011758030000c52825810391150030054001e03039481d0343d481c03030b00b8092402c150405c1d100650041c1040002155508020345003250140c809811a0714001c2292444c0382164030482003581c2540e0008244526440c29011f006808503040303030903500d040010000581e80110045860300c03c540044000b509922081c82a01d910300d80200042e09a02d020203c1c81c582101070625000c403062420700410000000c01042e03a45480d40144022154050409010380c030200940040c004000070030000c8000038814000341005600c100c101c02e01e1680c031407902109400c5103400c001402e60040003101c011aa114510b0340440d100001075001844c210000b800c5031144d1500000e22490405280344204031000c3c1e9040c1c0f0507402040c182c9220356460007055102c10707540c422550300d544004003a91000c1200300d44260010302c281840001e0790300d070340e9031443d000c4000d0f030042c0c2e1941c000c95038120b00d0b29014000b19a04c01d1510380498039640c10500001c03100b0381d014001c140700c2d00500300701 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 188765314 1250 188764064 188764087
    0x909040309050603040f260702190b1803010e0d1d0f150913060612110c1203070f0306030308040308060d0b151e010206040212190602030402040509070308090402 71
    0x1c078014000c050b008641c0ea24040c20441c00c400039400c0e04407016042c468242030707440e003000c04e8444460f88601c041032411006400f00000707414071a245400010f000480020036900c07120040c520a00640002c0c031070340507880b080500b100d500452003581a0880c10a000d40702d5841405000003c00c10045480c1b0100d000e40403681040d2141602600b02e400815011b81c04100b01c0045c0004d040d00b150154404081d0903200029611144602e801141000d16003e01e416020b8104002d00002d98040e5410026941c0c0d840307291040c41d507001020f210000080c8070b50140d218030351071000d05c0c040c10300340401441d40e90018500f1000401c05030411040002042c030594500c005560100c1c1c10400150301400d03c1141c12100070f881510741442a44201d1004041c40c001c1050420b82c900141c02604290b40c07141c003403001040300c042c0e4001890184075660501d10054015003a00c060282d540140c50f440d243c03040c003080b507001600b50300c80c40c0e001c00c904000003144c08044464018050381c0c00360701c8001c000075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 188766564 1250 188765314 188765327
    0x50f0d0c080613110a05010503070e03032512031808370908010603050705120304030525080a05061b09042f0408070b1803030a03050615090609090403 66
    0x100d16014000d803000d21502d03030514544800e0050250012160000c1101304101603201548a801e001c00c4040c4001410b56020360707480d00c5c68490180c1628580f07006d00c02030803903441c00031110b00001404081d0080030b105130809501007218450908100c0c035544d070242d0101250004400500301000041e07070f0494551075080b900052400e902503205c10b5103992071212010501859880c1c000f5a2445000800030014003401045a4201010700706441c1403d0520a04031600d4441c420244001c00c00040000c03410402d1503052025001940d002946440270041c64420507800350300694800d040b501c002c44e00100b885c03a001500310b024640700c07010302c040c0242907005503880162b210703150510300c4a0380502072024003119850940128440245051243c00c203018078020f041060380040340602c0300005444c010803444030b590200c0780e026644140003d207075600090b2440c00185d1650140078060600c20020260000b0318000c25081c500d0130004075542c1c2c01003859075403158040e00081802d1500500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 188767814 1250 188766564 188766569
    0x3060609090a060302030606180a0c050f0301080d0e042901120e01020d1104080706050a03090b1501030e0c010c0305030402130513110306010e040f060e07090c020c030601050f0d0c 79
    0xc0160500346408802c8500a00491006a009002d050001405c9280c5400240c1d624503403210980b0351602d4050407400200417560422080c400108071000c0c848008902442c0223202c010010300c5513175500480205a9842c03068110300550604800c00c0009402c0c1004c01c02e4004501c034259014030621004a8940320304010716105189003800705003a0f0300040d00200092002030b2001c2c8007120200614007011b1146101e130b0a1150044081400514410001820750100ca440c0c00300b80d102d51030702ca01e600c030203080d10000c000d880b100075075401c6540c00d4000c908000001c0070103865568a000000303040c03035140500041c100000007001400b10b541e4903950f24020000c2441c10891407801c0c4044a0f4030000c4c110041e10000382e1f100030b0780920b103000200d1a06a8403410340c1601e00d52501d5440c13400d80384100b801290555115031216113200e208008203002450030903000b2907400e0506e40060b041c034030b031072170158042d400450040c03159464410b0382d519500c0041d600d1030007014050404142100054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 188769064 1250 188767814 188767819
    0x50f0f150f1b21130804060c05010b0901060f02100501060e0f01051309051b0403030e04091104090c05042a0f02030705010609060302090112051c0e030a06090317090a020603060609 79
    0x4610307100e0b03040c081111410440b43c0910b64035690784583c3c4180c2d1100c4418040284001c2c01000280866071003205500c2c01503100c2c03000071030042500c40000e940c545098101078001109107603400c102c0303507040120308003040303503140100215414480000c00801481c110540141070a4031440034691146084030b488118007004124420740b1440008040c110541c6d400598000d400c408111a102d1a001c8070f01700c0350325803210402082c468050001500c1c50420a44007140c1d401c040c190b040c1c03a240035040e807a030712812003440140d0600c003c00040318010b04c070000d034506000d4914902c01c0c40c0c480f030244080d460380c1030004c1044010b0108074558451604020010750903c0320000b912042600203000342da100301c40380780182c1e88801e40052117112a4101404a502200036048034800402403030f9003808952030300d030f0f41c0c400340c0e80c002c6468020715080403603109644043c40000d15034002d6401e269030010090702611780c1000204645c1e20040d804e0040c0c070441c8004086403180d40e0794000c990454101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 188770314 1250 188769064 188769067
    0x506120105010b030601110d050d0504060204090c080603010e15041124041a070203101109041805070e010f06120b04050702010207060606020303102709050f0f150f1b 73
    0x110b0920f4249500f0a9442602040441003200f05400d40030400891401095072601e04007100c4450701c20203808003a00a44500c4d80c00c01000c640400300c0e00401a15400784e4444408600380780e401d00d4210760448004a00d5a003110000e60610305800070200d41040e080200492154218070000300a5807203011107401c1890000b0003010b11043d4500584105d6081099480c10b10603400e1024a051082820007503154100c0c2e036184c00300405513440804088442940607041205c01408901141c854a480340c400000d205045c404002d01085a000500701002000555503d1b01c00e0f051074042c0710b03002c0d00080c4003050000a04050f8681c1c024100b62800400510081c10108401b038001e6004a80684645003001c03404141a400002224040d04800192550315071a148120340e40703034502280e541c0b2138a5060b80d8040c03645c54501916101e40c3c0281d010b00074240365078924034640451165882c3c8544c100e4211602c0b2a00c2c1d07100760560100c90a01051240c0c0d4600840200c4030340e4030b4a1500401c40c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 188771564 1250 188770314 188770319
    0x9211b030b010305100203010605030c0c070504050a02130b090a0323010603030f1106010f0b09030a02030303042f0312160c03050609070608010f0b0c0a081611060703090504050612010501 82
    0x1c0d192201c5040741e001d60251a01039042034540320aa110901420000c0b8408202144003268404010018005d030710040d14081c5840d4800581520010707100c040000d42c021a20210300000d81e150407005120100e1000e1401c0241404105840c91912003d05025074030200040c0c19444000c0280d0002060340003040b51644900d40584000034108a101c0006c1000b9505904180001802410381381201d82d010b640601c0c00c650321120342e0103002c030f03650540594244440103071000c00c0a940200d00c180c0074442906030090020207003028604100c1e242200c400450065910003003140d02a8505203210159200804444560b91105103070307005040c031500b0080041403000201e0240d00800c10101607030103007076031030384119030070b40c406c0c0644484159004001c001243d0110006e000c0095100150340b00c00c01c45031900d100c903070444450788100e522a0b500c2c0760f08200303000913418601c03141110040c0c28100399480003008859103000c1c041c0500c1c1d6440c045001c503699401e0110b490303580c00c4c00038840c568 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 188772814 1250 188771564 188771573
    0x8060612011508060303090d0b07050c031204020f09100e04020a0302060a0c0c050102010b21011503060f060b03130609030e0d0312060f0b0703080601120c0201090c050109211b03 78
    0x600142c0c1d80000600c01c00d002c0780c2e00303240100c111940c0c1e10300102083c03041666a1500100360701e000d4908024840200205440500b00748040c2200004555031400340d03240900610a41c0006203a09a02c00e035800001c200503080b00140c0c0303c00303031007000d00640316903130301d6101143ea00d692581000c2d5000c0e1011034403903011540241c2030720700c0d14400da450098950396400164281c566001c581680700c803078541035112100b00e08040d5113288003801c0c004901c40021034400c0c5000d42142c0c006941c2540c50301c0e4801250102409000014400412250f00d1841c220503c05101a82c0040c0100600d0b1107040034801e2511608554032840ca004004c00e0f0030f10b9007440c0140409058400329040c05040c03420000391307040e14182c042d00701c4001c540d00380d1410340d46a40071180c100008100905200d0000d040409210244c42090740c00521500000b40400d940d081c511076008107940405d042005032101800a5010a10b001c2510000460704400a610301e150540b5180c5110301c0c6010801c005500020a01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 188774064 1250 188772814 188772839
    0x2060c0d1403072304050405040803090708060f13030e04050c0711060322030315031a060f01050d090614090105070906050901020a02010f050c1002031012120806061201 74
    0x89546403a0310028100a01120100380021100180803c00300d0042d11804c1101e1501d0350340a04540b40b800c1d1425442e000020b04036107064905642842d0040200f10051600700642409030407000000c083c60304d424055400c0e60040100055000041c40c400481010302442d00c0c402c01c608003c0041c06941b800034440e41c83c1c3c4d0403860040e00c200398021203070192800c19000b101e021b6a041d2084030314080324048900105103003440300700c082590310781c00f000800d03244a01c1e00300914843c0200810f85100c031040c60f401d50602511041c0f00702c840303207000c24103030f82c001c022943d001d00b42010204209585041c603030020192039480c456511a104200807190700c044d805107104000d107444000d202078403210111894099105418050303404000c1060244d80100e010400ca5085450401d240050444c5002d044c950500c041300205034000c414800c4840e40c01c240500900032000411380e2140c030300d4882802d03285d180b10020081c000f140c2e0205041e0f48648081b07595000001131041c0d040c0d6503d04080302d50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 188775314 1250 188774064 188774083
    0x120e010c0510051b03040f030e19090507031a010e01141201031208010f0e0a02030a020c01090f120f0801031202010b0312040302030105070512071421090708030c1207020301060302060c 81
    0x44111404d02d01e02d500c0c401c0c03002c1d280902c1c0c1110114400c1e000c1d1350303070a81d0000d0b10703801d0003980100c912005203080f00d00030424070041d1204403004209800c04100280a440005140911a424103040c501c2c85990007a0480e104010901c1c1c81001d40d43c055244c020103110700741c800d851000c0120004814022254840c0c000d800e942d5880d507a407a03036039481c484c10440740c1d4012015040510404600c1c2c0c90384c207070090354000315503c5c4018070700341c44004070508403181003004030381401506418105101c1c2c002c08040e159174103070801031640702da81c1000419400050000600940d810b0f0b40900b0100e00c01d5100480c804e074041c0403107440c1c40344a070701c1075019007051104900c02c0d030815000464692044c4141e4200e180c0c1c0c2115030381151a4004141c4020940c4002906098018022158084440c0c0c198040080e001c81c60003965090114566041140303d400ca032443e64000c101d80c0c40342220000b511401450800729503900c88a4500c0001e01401c6150300183d440301006c1080040161f011074003045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 188776564 1250 188775314 188775331
    0xf010804033609060b03011e0906061206052704060b0604030f0c060302070c09240906031509020d031d04020f220e13030309080403030f12050103120e010c051005 71
    0x40d10b07660b88441c1c0094540501482105407802e1004220007605110180d41c90b42c00240010b000b90384401d0103c2c1115099032110703001404030f40c103c440000c00b40c443d400207040180c4010014910150010507100a4220382a40c2004101c000030180241c41d4490b82c03070b441c4010721803941d541d80c9080072101d58061000070f0310b61450341d00d400503400c1c2c041d100b240c0203070350b104500c000043c0c034041260000317184190642925901c0c0801d800b00d441c1c444010540a4100c1c881b000a0b40b60560a00300c9015140c0d000c0d03100300d946400001405a034a0b50003001d511a450314202144003010803000801e01c071145002a001400440d0800340c89404101411200f0070f20340040c2c0403282c8102e04112804024800d40d085d4280c800003240403140c0c07104140403505e0107810041903804141d5030301440e55200c1d6100f680003903000c030943c41141d940102e6014091803884000c1c031155055445117040d02c0d071124034210034003c111503402c0d1540d008a801c030904079000f0f0f095800c1c16414140ea017000e0f003000c4481ea41e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 188777814 1250 188776564 188776667
    0x603070603060f0608071707050c0c0603010b0f0f0d111e090108010b0a031d0303070305071412060114030a090b0603010e030f09010309051c0318020f01080403 70
    0x1610500c24442c1c4070440e4010001e142c050351a000040d519903401804000c100000004a40301100b101c00300381d8007a1404e6665180d48483c049201418040d1004201c4d105642c03c000410014401c83c040c1c508030304910082c0c6642e02c0e0382e50307440e00b5076208100031428054107003940104203040043c05001c4065200304d409140342c641c00c0c42d6280c03920406c400c5502090188006000054004015100d8a0007034100044c0c5c030f4000d001c0c02200c050300c01c904607605d030f84000704000303410f40c0c903000d42904440241440003030110010f400c030480740504181c62249040c0038001130300c80d03840b400d20320300304030340241c40b8a0760307410011117032000340040c80030907190040d4090100b642070905208840300700743c03603e000c0e45c00c0070000c1c0b6685c60254480217105042507141c01041002ca1001c0c410400c8480e00c2e034030180301507074a407080a03051366003101c0b6100c0c0390f982c0310300d4031009070701e80310000315000c103007464152480e944074941501c401c01d01c95590440c5080400070070b41041c12040c0306c0600483e00b000c040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 188779064 1250 188777814 188777819
    0x10f0504050a0c0f030902030f07080115050d03120c090e09100c080705090906030a1202150606090d030813061b0206220206030405010f0f0b130c020d050c0f030304060203060307 78
    0x400d64070500c0f08180021900581c00540510961041d0100c3c0d2004041c0c8030b80c160140032061804815401405159640341c4404010345100c00080700106810b81d40440c4924540d02c0181010f05c1c1441c0c00040c864981c0740b0a00d02030310900403100904840c4807095203c1c1051500380d0342e2000300075031800080386418600222507005060582c03003034035503550301441c1c484801c090005141007d842c0c203400d07200792520840000d16101c2d0950301646c10b64002c21040105030482c01c0c000e00013030302c000e00405080054102a48032074200302c03600c64060401d019551202410784001c161003881c0904888d142034804104a1002c1781f424000203070716400c40300309444241c40c6070814076203507032180700e8071700d0000d03919006091000207076a01c180036a00001b07190410074040019102c00d6442d05885655a1100100501e01901040301180005a003040384c1da11084000e50341b0300c5500c0302101885000725048241e0401000109035925212007903948a0070b080c580400650010f03200a4828091100302 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 188780314 1250 188779064 188779081
    0x12171318060e150301090503120f010b040503070303050a051306020c0f061314010c12020a03080a0c020d0e030a02040f0606080906041a0a18050a0204060f1a1b06010f050405 76
    0x18502510640041d001c86510f40b400d007115041201451603801d9501ca03203c900100e50103002900010004041154192518904440c40c00304142c1010318216001c0c0720900c0700f81c0f40090b50380c0030750380d050604a50f94072120406403154000c264000032031217071545010030030a6003c90001600a400e44242d241210301908018543c0584140c4411604c003043401041201b0711041402000e110605142c0b1018079640c03030740703003c11594121250250380722404c1107003019844020035a111405a00c10000410003040003910354401d2000d07a01004000042c02c00c01d680c0900c00f4003506640100304100501d9004415406806e03035205401c00f003414040000c080c80b0000c959144038592000110a03188030312482c42080c0600a044220540d07902c02a4600c0c03074019441d005005801130b0010f0030001003510411054400641182c0a403075a0b0150410903190103810282c40308000f428034549500580055103850001c030301e500c0700c0d40c3c071409000103040411402c40c00243c4000b41e4003807000b035840c04030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 188781564 1250 188780314 188780321
    0xa031b081e10021e040f061e05030f1008030414121f0510050a0e0603101a0111010e01050c0703110304050f090417040b0a1205010303080112171318 65
    0x35012880c1c02c8080c80d0104034950340d00502c041c0d000040c0744003402d840d254070000203030005d4121a285840e22101405515041000c003064128601710b2075403c03184214004100f0b0001a0140748140c3c88180030130004260040601e01070004001204e0302c031076a8512641d0711941035604503014000324101030744800404140801c415900c6681c2c180ca40b001140034000902c80105020410b2000c100080384a64480b010030b00141000320031b420701b40c00e12504050a0201d821005006a85052141c4445602c501ca0142c0446806d08082c2420300c140881c0301e01400190100d290103500c2c00041010285080002d440030078001d58070b820300c071180400ba543c3d69114500505a21803400501405d0324076101540036400340c030440d0b0492050690401407107094000c0e40100c84251404a10488050780c40000052584441c0c130082c0501c4d499610080d10660041c0168034005c81510343c20014030515142005030030189914007076960f0300010070020740c40c066001d0456000751125880305114404d01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 188782814 1250 188781564 188781613
    0x131502060420060703050403110a180e0109060903260915130b070e01111b04111902030301050901140312160f0c0305070e16030b0a031b08 61
    0x80003000380da1502e480e05001c03900e40c0180903000b40c2000c0140324007510b608000c0e15900c1e110340c660f1070b1a5429458003010321025031121038012450180d08000040d2110001e101d000c4100e140003074100e1480040f01e02410b40184d0103019036082041c00c608040d400414201c0300704424005488400180ca617101c141d213010307201501a139000b503096072242c030710f07003041c040d004503c1825038601100310fa69624400d0700304603910b1011500109882c160741d40c100c00c0580307030030029030302820341509414a4900d0b8405c10441d411b00555541890761300c0e254200301100c500c806034514010002040d840000c0d900d910074014540035507440d000018241402042d000600403004000c0d1000da8004140d0029940204500e4000c10040b00700d00c03030100e0541102109814052800500d1050442c28658a4000345500c403c04c1352001e007042080e210511203500342d0070001840c0100700304840d08005070180a80d60000392010804135030b2105030b4071861002008546075001951180c12404c007030b83c1034490551 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 188784064 1250 188782814 188782817
    0x5060601080c0a27030b0a0c12090816020103091509120e09040201080705041a070c05090f040816080d0e010f0e0c060c01020f03010f03050c240306150a051315 70
    0x1141195203080e0303d01d20040207494a444d168100350f83c0d80b41d484081405488803845696101c8242d4000ca900c040110341c948408003041c00041201d6a920301c41e44a4104200804c13143d40460108680c82600203c000d44e800001c40c4500081044000005000c003500807103a0711400701d8106c407264010711005a00d001300600d0a415035907140c006540081c2300034290000c0200c09c000c0800c1a42c6510300109120013081c640c1600c0307203100c1c586401041540d40050744034400d000204003040d11000c101c9607025500a0701c803038940801d501c0228200103c0b550092861f04c0204152068200340d03800360344410070150091000014003600281180c1c02c90440e0181900f080196010a007844801000140440000145072500c2c000711002113800c2070304001545980c00e031007001400b1080107085590380040b41c801c548d4024296680840707010140300b2440d22580400014401d68079940200c140402a0300403e9641c00400c0c001003040e8003101100d054140e8010010403445110155000d426026 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 188785314 1250 188784064 188784077
    0x80129010e09040308040609200a090204080607050a03090602031501030513080412020f10020c0310020a090909031e030b0a080a1713210c0902190f020c0402030405060601080c0a 78
    0x584c0c0781112030150051054640c540c0718004200003580c401d10740e840e040402241e4003c01d030302080030000341c0d94040e4005a2001d005000038000654080f40d21604200c80f818000d0380c03862412070a03400f600d03203500050a113900c003004014407558950a820140711090341e0410241c1ea520013501e032a0030300141d02800c941c0041c03200703004010000301c0c01c0c80414002000c2d103041480c41d80005140b40d00d82100700c3c0058000c090a082181000c010703425000d1038881c800e508000c84888002d01c0107403107229514031183c6850312035041c1800383c140754070703204050b4507800c1180c0941c2001070050044d03a030341c01340294109900040c1800012406000c040d0303014a5100000008008101031a00140380024031014804800585150480c0e40110340c1c0c3e01101c126080304007281004a5131058a9004921040c0100318400c042c0c000e0310780711000e0740590f0601c010030780a138003012480c200c2c401c000c980e04188000180024410002a4548074200907a500381e8107a50718420396501c2e00a807a04040803c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 188786564 1250 188785314 188785321
    0x2090424050103020306040612060903080f13020d0212010203070807020705030a080d09081c0506030601090912030510050307140909030a120207050c040f090b1602030a1404080129010e09 82
    0x7180c4c000b9900b000b00104046100ea4a4015005103125111001c07074125942d03a40c003001301a00451a0356002e04506801802c5107481c16414824100090009100f40c0000802c0001c40d9100d410102d0707080581c01c000c54891403d07010140040c0000c0d1100e0016109240000825140000755892030b681d000d01254202145c1c0d0465038080d00f2841412510204103100706144615460504940c040c1e03165404104d0307041410505080c5601a003280368614184100900810030b280881c55600c60145070014281d0350300c0d80300384c01b23003406604950703410b00841c00001401c0e18241d191038921502184c00b0005034681c2e030403440d83c80c8200340d0514081100e50103040c9560045502600d01035025a0503140c1d0307034090100090880f1505041400d075541e540c0c0e50101403182c0703d11520f60007108a0703590340070f4901c0c05da0080d5407801010381100c100310b0300e5481c00c13201d20720031001d40c2e0007440100c00912041d00e410b110300c0c402d514a08a01e8510134809016290990b218100c0c0800c034107000303421001c141d00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 188787814 1250 188786564 188786567
    0x309030a05181c0b06041b0e04060f0602031b03031501110703020306040b041101030e0c1306050a060f1101061a070602070b0a230c03070f140409020904240501 70
    0x4100411000c920b10b9102d5164000c2d44484848511030204000300e440e0907000d501e400b030742c080c2003e00f0f2a0b000e1450681d44002d005061404c680020541d4100600034408d40c80009010304829006200248001c5800069441d0000302401a10145850086c0f2500000c22020f503280400c5810400e80e0040e4040400c2c03950203541c20300201261001a40c1d03100741c484d00400d01e03140c07080e0742c111081c5440200700028041e440e103090300e20210910b03041c0901012807510b50b50f5100040300c807070b216011081d2601045200d40d8404030081001030400c03040103070b494802800145045000c9400b0a55816011100e508180300b1802a500c0e03880041a07107003440454541c0e030390000c01c411244541d0801c080b03804158520402849080f10700c40104100042a00800000c0000d40e289410b41ca112010f01400203000402c0d203030300c9405850b024240241902044410f80e034164181d00c02c00d01c1c0081c1c040f032000c0b0b8507001840e002500344c1e4180140711240b00d00050006196403d2400c44403030400a01480d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 188789064 1250 188787814 188787817
    0x50a0201050a02031b0714010e090c0313050f061608010612051909061509150509060d0b04051c050a020319050c01060609090f0608060a050403020a0f051b060309030a05 74
    0xc2441100d05000d4840103600181d0b4039505c488556a008a104100801c80e18002ca00080720a1904c07450002070300000c0760b0340d18800303414501e10003004000940c102031240141e42d50300380c12808a400040032060100d0f2038100035101c40848440500780111040c2c006c0030038a049800c0f96840f140e150841d0341509000b4071006d8038041e90045880c144040305442406000344050003183c002803510300e41e05c1e4410002800d0b9000c0e002c0c0e6400c10000680d00d501c820b21800880b1016510210f8640e02c2e02d0000b40c3c403855a12000b8045860705060006021000170b2031005d1100880001c03446079150794041d184c81c0501c00750480140e00401c804480703451105a80e28032441c55080c114203062072810560f09546481e04080c7c0051101802004403150600550445c0c1076040002c0001a08024546846400050144100c141c0341d001150405208014500c40b103500481030348942d11340ca00e030064a915030b0403912003460040043d03580c0f00f40b03803100459025002001c0154900202c60009444a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 188790314 1250 188789064 188789077
    0xc17091809032b0c090b0702130e030f0d0e0c090703020a02120f0703030b06031608070504030f08040305060a0e031e0c0105040506160318060902040f15170307050a020105 75
    0x11030000380b02c441103800d4000c3e185005200500c0940d243d480546a0f207000f15400405280704000f6801810041e82030030702d00f103404907034042c1c2c1c2d500307440c14100c13420502070110140c04200512001a141190480c20b001400c00e2100403a0300b40100100b11223001d82d00c00928503604c0e4405940d002165580d13000794001e0005a05038010303200564078981722444160480c1b030800d0701c204000190402095818424920011012034280d400e504100c105c41c8071016100a0003c140310300d0f1000700c0da105004105580c015030740112403140140c003e10f45807030181c01c80d200840350b6200701c9001c05d108020391b0140b10702da80d8940c001036040c001c0c006c059040c51162014681e40e03c071000c000803160540f0a0081c42d01c12405040200500e0410085108650030203001c9602054a010620034031140c00389003400c3c400d5003104000c0380e800300500020300104622405820982d1a110441041564205030002181d80801502c0304241500412a4407031059030f400130600d0304103500400041d030041c03015110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 188791564 1250 188790314 188790331
    0x3040906060906031a0d05011d0c01020f06010803070201140409090501090b010803031b090a05090f090d14030115200607030b060c030f03090c060a030603122604021f0c170918 77
    0x645280141046180c02440d08502c28076400c2b0f5074604000d0f5030104011039074030840074001c0800b50302d059040354481c007a0040003030400c00c00000c18240b4030740e0082910013a00d4000801c02541d451351a01d075000b00503800b0f046071083c4024000180140c0040280c038130543d01c1c8103098030b2130702e6816500d0329140d1182c031040364080301041000c1950b44800304c1d45d602c194540b400c0d800e01c50505a00007031829501c40740c0d2200b00002c02c900e02042040c0a0244e03070441e07100d80c0340c621095034101c009030360901c4980d400031402c1450721041c2034044800034a440c0540030503102000816034030003d00003184100701d03440106900402c100c0c902382c2c0348500155400205d500c1074480c2c0340100800942c083d031114075910006901d596050003070050790741d2104401c848500308415050118441100e461103c03640440c0303641d03161030015040d502c801d00040e07038403409180341080c010f65032000079101e04050401528040d1022600c0d48190341c6050444e030103294010289030541010144940181000030300045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 188792814 1250 188791564 188791571
    0x1e05010503151f030203100b1608090102070b0a05030f090d0c030e0d170409050c03070c111305070201020d0e010603081c0b0307060f0f08010e060d031103040906060906031a0d0501 79
    0x40c669900640c442c0000b440e50790056a203047c0a111003010614507086461248010040010003000c40c901c4401c9413075019032240e07101c00048005034200607156100c18501d10001400c030a4007a4004001c600c41c1c1800c164042003500d9860b001c0c2d0b0303108000c210b400081000f00342c07005c020a0040c10101d240030402070030340c100c0028035510700e5a1090000107003914150040b50501154085001d500da00030550201903085150001d401001d00e560a0030180044a800a2007032703a40d00e605440c0403203020012014006820000e100a0003584202d640c90302491402d09210920641030040404480d00010001e00349024003500c400d1511540d848680c400740e4a1a003900d8980b024003a90b00100760719122461805103441020b0300545003140c0c10010040040014005032a01d4000250003000695621b0b0301c03100c0d10700e8250b4043e07590f40a18103c502c0701040c00074117140f13a6041002070714425513a00e014591b41d24016801e0350801e1406c0858800303c400541c0700c80c10080f0074503440d10300500011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 188794064 1250 188792814 188792839
    0x10f1a0906040305071a03060a0b07050a0203010903050a020c010915030203070207170105040201031d060a020901030f0938010509060a1d061203070f020402030405030705060c041e0501050315 84
    0x80c100d510543c0200c3e19a0055034080000c8241c205a1100c142c81c2802c0c0e451031854044000384822406000351980d41d60040b81e000280141000f555001d5035004d0003c2040e011241030144c001c0d0803840c154401032003221008862540b280d90b584003180c40c2c220481d613469842d01001c0c3e019401c000d0080003184100740700082d9030b5083c40e582c246035880e00b90000403541014000141610698806520201c1031300ba9454521180010543e6028145680060315502c280c4d004a010f00f40c540c49198815080ca01c0260a00c01c841d0304001114503108541a442280c1071b403080c03c503116807415544005c02e6080104100c1c10004c1c2055849500180032880c0603881e0524012405541e0109018041004080041c1d030b0801d0049116120202070046081541e5903407190701007088281d000340116004008202081810400c2d15040c40e4420140c8003640b82140051085422610400b4051040c18108071003402251700504251101a580d280c030303560340c07040605070300c603034070300301982c20810b030021a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 188795314 1250 188794064 188794069
    0x9020604060c05011a01050d0e01020d020c1b090c0307030507050405090f0a06050609151e0406020f0d0302030708010e060a08010507020f0c040b030717210d050f010f1a09 75
    0x3400030748240d4480007140700d2181002404c58072860564041c4507032900303d00c081030380c1040c1a100c416100d5440030134045801803100d40680190002c03075003514000324030600002404607403860b003242400c4010b5114000c4c1c40410603860419540b04440900030404100300034840e4007d25800008c9040c13080c5000d030741310003041c4c002000b100d1441040302c8120600c074400c1a540520401040c04032a644d0909000718005158110804910a10500001808041c080b4000d82c48011f1028900d00c450312103a0b00c600103910f8143c0200310003090700038450b014980600a200707403801500595a000702607805c4c80c500764503079000580110b034440b51614001a401c1024003415114098580c044d0400080003030040d4688039590a20610881c10000760402c00c2d01c001424100f29141c0704031503600d900750560403c0c02c1c81a6002d09001d04000c11000004a03202107005014140760301104100700e94404141c40b40e40f82080c0542c0031844200d100410121105140340c104407084008912300c2c14410400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 188796564 1250 188795314 188795317
    0x5010b031305070e041109070c0506071803080705150106050403050307060509010f063011240a020304030c05040e060114032b02011401080c0d0303110703030f0609020f071104090206 80
    0x80413902960002e04d2004181060701f03103103070800175608049000e07103403541d181500d54800510310410403440c0507483c1c00044443c42da0400070744c1c0109009545481070306000d926880d0481c2ca0030009060000001003c2d4803440494040300d800034040c50070090140da8410107030401415000c00c5640f1501c454512150300d1243c80001c06034030f49040d40e5980c0b03070010498030610144610111400f80e00760b41c404034681062440800400711801074030f030540740b44007140040c03540391480c070042400314604140d690000024400c0d02d000b507c107102c006070340310104425600d207108910b1044c0c00c440010052100c2e46401c641c1c4c8808010140d400c014815241141c04000340402034031401c28403440b0048803071b0284245000306855103400700840d81070034403242d81c41ca000c04032607004d915103481440615102e0f520036070046041344429540d91180c5d00f401000341c400e80c141c4030102481c01100182d82500c5100300d91100484400c03031800c01c8055110310042486c501c0310340350040c2c4c4440903440107070754480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 188797814 1250 188796564 188796571
    0x30a02131d06190231060f0f08010909050f06010305070807050f01020a03030f0b030307080702091302030a0305070602041d070324091e110703020c0d08160c051c030305060405010b031305070e 84
    0x109205903140b8080000381408034940b0001f090001d11071550500036800a07480313040d00c2d40c2801c0401c2000040c9005854108103603c6850540600380000c802c2000c01b00340d40003140c0309441140d10705501c40003003203080c420003520035001da4014034003078001a01070b40107101c0d40070210400060f02c680c2140803a046034040402181c100400203825800c510345140e4054021000c0c2202c649110503550100307a07030310171640300901804008034011003084901d4040704c003c0e29841c407980c9002c952000104100680983d143e20110f828000c0d0a2042c044c0040c1c100340c441e42d1006200642c1c4c0c035021003a40200301c900e282904103058940a4410f84041c0d0203400036210f0214840c41c2d48080c58140281014441c0071035920030381e580c04800010803aa0810f5400d42d13802c124005641054501c0c1503c4119040c0d0710160b040380c148c4064002407200419000105402501c00f80201c0e90340c1000c0008940b401d006104401d02c0c140f0128108032900505a1041882003007201e42c11602e608605200c00002c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 188799064 1250 188797814 188797897
    0x14100f090501050f0105030604150e0d110d020d0e210d05070309090c0806060c010e0a0b1e090a060c050c01063506060906030a02131d061902 62
    0x1880e101041020900c00e070340e03020300510990b1200f5410040041d44030500544041d000308150820a00d401c01a0b80c00071103051b0b07030b100881e030b8070256401c0007505000180c143c1b19264054018065415400818000a5500c0a6840c80740081000d008c001855108002c04c2e410000050900022820200000320408985031192900e400040c60000d010000c140c0102580e14184586c4222030754000c0c01715070304241c0485a003502d8124204016006090440e6071843d10300c00e003648101480aa481c0090082130203170303425048010580041d900940c42640e18070780d1540945403800100740c807680180202d841c61310b00545442c41d02c020700d90a48545800501010b50000307a0104070000300c4503c2c3c1c1c1c1c01d0f250010622121080399000315203c0400900c19409030040c0d6000401c682e03014481080500e500400003aa407485c41d5103980f0052030062800c044100305054010390700b2000060f128490105148500e1090507009118400384d0003c464400184842d04c030350890700c0d840310000f0b100810f0310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 188800314 1250 188799064 188799071
    0x501020c160e04030e0117130318030506010b1318020a0e0f060d0f06090c1806020f060a0c0e040501030f050106231509041113080303100314100f 64
    0x3103803a05424200181416403420300001d0040003240001038600303a00c15010b050038255104c800c001600c101403000142c07032403000f00501300500c80c008401c94900f024040c2e581c039030210071420540d0000c2c21050001401c10380c80b60004020f5440c0080040c80074040304151013482664030340c12281510400c0541804039600481c0720802141d0014405000e01402c491030103039a15801c020902922500607802e03403003922a00c004072080601d030031800c000d00c000041006041600d0b10010304e04e154040192a40304901400026440d01c00036460905220320b03000342480ba210f04c80088010001d1030703400300c1440190214001c8560303540c80f0f124003d60195030362010840240c6800c23402c40381a5001461505520a07a0010f048a55071002d0407039001a203100162030b091072840401801070070809680b0608020315091b23101c0005010b00040c0c0e44c40c0c8011003005880742d40103601c0380030031103203400c002107021400c201064940d5525554402c2e8034081e120b0001c4502e030010280d415041d00f03034500036103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 188801564 1250 188800314 188800327
    0x403060e0a0f0b040b09060c040603020c010605030d030b13050702070605161209030b09060c04120311070f0509070c0302120d0b1f020c010203090f090c0f030103060b0a05030109151503020607050102 87
    0x1002172942d0050000014011030300e441c00011009008034000c41081641c04181c2c860b4140c0254001c0c005020024100e0300818450b8400030050310307020741001d000300340341281088001d55501440d8003a40035900034103016400c1510403180b90704264114002c0d030660b090305d40003064070708192a11041c0c00f40d40350100300307056041c0f0340101040070313190701c0da503a1040040003001252042a00e0548802c1003281d40c4101131402c048070040164040d404190140c0900003480014000d0480115030064a03c40b68655840c0d1003951022031520002d405604089112039400005000400d0740b2144030340c000903140300500204500d4054001c90790700da0442c0c504101c00c0540c04015075a080740c4244000c6140c003440e00042544660a0146203004a00c0702c0d02081c0030031101c40940c0c00d50a80049030720b49969403402c15402034186107900714081c10740d1801c049801d08040c0510130310650002c000400480c502c140e100003c020120001c8489010303007601000582c2c0701c4c030003800c145020307800168503100d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 188802814 1250 188801564 188801573
    0x12020a021e0303090a15090c0e1027020d2901091403100e070b03040f2f0f04020c01090501050604050105010912170904020a030203160e060403060e0a0f0b04 69
    0x888916510040c2e60042c41008809440001c2c041d8003103070702400e14034201170401000c8000d130451800c001d1100c49603090102e107841c1159841d500c5240c41c40040481250780300300e908100b03d07000b1681c0c101030030314114544d841409a0002d09403804150340008002d0f4052754407440442c1290950160070000681c10f00b207560740a8500c101800c601942c00c0e0000018400081c5c0d250350300d15183e1a0503480c1c0c401c600c6225814004080144500400030359030303140c18070340b0603440d107160003088403110300c556441030400820181079800d4405507014400170764120030401c544101c02c0d41d00b07564025000c1020141d814828010621180d00c01c10010445003092000c1000742c0d44160022410445262000c00140c443d502001b4869508a8204010103070b050030ba0304d0136441100c1110740c000c0d000144849040340d060f40158400c0300144844078540e0300310309003181c00014101c02035603c0101844103001103000c0c5d9000c803541034120021104021695940c141c102076103030400340d64003c00d080030842880b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 188804064 1250 188802814 188802853
    0xc04020c0303070e03391c03030c0801150333080c040e0303070507060b060a09031b1526010f05030d02010c050403030809030705101b05070506010501030c12020a02 72
    0x2100604904101aa401c07240310008201c6c440d28240203c01600c3c03401204007114442ca03402500311207140c8a03901d40c030703100c0c148078410840020b8580040c2e10449031040c21154144d03600008010440585401c08801130952b545402c602008041100c5c145a80700c8100c0340c0034880c50140ca00212850925494241811107010f5070284d810038106140c0b10901004480c0e0190b080d0030200d80f00c035143c0c10908000c00800c0e203001c1d00514009090001c480c1c120f66100110f0348229410a0607424200c1c00941081030f500c5007403505061004005070300c500810000424490080007014810b02401900484e00006c2c0d125800f840c0c5640024406410305000c08844907086000078844117400c43c000130014405d40c44081e0400c010000800e24030322041c0115013240350854116440c00700441c2c83c19004002c80e1524902c44010380074600d40d114080c0302a511384503007200250800781c0c81c040042d80540b421050b0341041240c03d0703a200300313103040d01d01c050b1a482d20b4940c001c007a807100742443c0200c0fa = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 188805314 1250 188804064 188804087
    0x507020f0111040618120f0c080f06070f0219081815030c0d0204180f0e0c0105040e2a0406081302060912010b0a080f0c06071e050c04020c030307 64
    0x307904168030303808403070300e007008450480d141454110030160b1043c103003406058003074004c0039103403040e8520381702404040c0c03071000705850003031070460795441c1d85e1041c41e84e4404001e224850a504000002000c2030f008403443c0d261801a801030b00d4141321704120020b42c019551404036003030480454008440b2000c40054059003205680110b80c1051107015180180002000840310308000114843d4040d0103406a500a082c0c44c2c0c0019401d1910b18010b078060700011488604003407601841850070303180000c0483c10044103840310351a150501603045921240108401d8200c00d100c642d05078800b035222114103960703204560481d140d906028000303000203006000d12040fa030b00c1e416080050783c0c80310101c07101110201c4a500003401c90a600e24094080010155480007a03440005485000031a88030030264254045d40d2151100302c04000b50b034020740b40e01400c1c0701641000851080483c1c1c48504421b400782048541c406e1803440050284d0307000c502036510039000402444245030300401c10620 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 188806564 1250 188805314 188805343
    0x6060305071b030201090803040305030a0507230714030a1106010b0a050909040c052d19050909120304080c06060d030f0c0c05040e0106031a01080a032d03050702 71
    0x100d0901d000000c105402100d101c070b8108074014080d50403d8000d41c45040340381da01411081d20380c41c00b0309010703095410454003405410304080c00605000d1190000052030f0f4a150410140b0084440303095009800c90082116030740c0829001e075000034810000382100e17951580d01c042d0807004465a50381403180603445204103020038041c41c1000d0750003005442d040c21094130790007161703030f00c1c0c0c280074007180516445150010a441d2009124004585500d220803010440d1440700c00d00c408140310f89040342e0000f41940d211044814400749c0ba0034a42203801c0310f111f0003114090004840300341400d44c025103080702c1c2c0d640c00040c90003c508007070141a92150040320b062500260307544024000140300820007082024860101003001802e00d071074030241c0320241c410044050240641402000b00e07000546030760807030100503c11140b8408040d41a103140c08094501c0060070f03a42a220201c84211000c0d8008040c1840444450105600c8104a1942d0341c0454182044031001e0b041c403800318041c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 188807814 1250 188806564 188806571
    0x90227060904081c06050f031f0905030f18102d02030403061505091f03060b04140a1406010203070c180603080301030b0709140f040c110d02030706060603 68
    0x85125806002660102050360080140d030764900d8103007100d104d800006800910009040d0a408a050f400b001c2518400e451041503550804201039031400784051190080541101801107021143c0040949034031803801c8a0811404492141841e080001c41c5002400000c0c6010450f140c10040120080c0190410032241c00180c0f1400a0813420648158140183c0b4005d103550039108104890046030842020041405c3c0a002c003a501407503071140310f01c03400c09840446c000f52841081a1903001e60f190640403c6461b5a030340501070704244d079030075502c1941c07800c400340f1010031091003603c122008880041d84118007a000458a400541700504552060280381c00154240a91a080d02c0d2a5401003040c0c2a41500030310241c615600000c1141c03101100010410200c2d40344580540c3c095204e200b03501e034903185c01980c50710208140c240d00c4504808488458100359000c003500e84482c3c40c0c0401d041042c00041032400c800400c0c400c00581c80060100148200d51080380054001c0d0b20382407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 188809064 1250 188807814 188807869
    0x1905010206040f02010905060c07090606050a1709070302150304020102060f0c04030f05030706020403080c0d05120403030209040b0303041d150f13090b0708011508040302030a18080a060902 83
    0x3565207600030801031a60038241e003904107582c060301c890340041400400441d070320300209504a8032141d50344940a881424090040b8150b80907000342c034034118082e43d800035200d8101708400d6105101800c141d0350b6000b580d802001684512203940074280310022020b03624285480028501400101a820040070400c103020a104030030044070200ca4004450b52100c0140cce0070080d0451290003001000c00340b001500008110010f0050102108814291110170314040d40c00d8400707100e82c0f14244001c404800005000034007d5000d04003207034010344006501e808420100346103a0140c0c00c00c002c50100c0c100305440c49150f0450307059000a106c5195554000400042010203030030714102032251424010408611900e940441d440e06c0c1c220f071079603025040051000d4880030302030092000d01d850380308034980c816005421244c00340c0e42c546d005500c0d0005501c011034096101e05901d4140c3c102c41e000004020904000126100340200c10004003200310303104001030400c104010345804060502072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 188810314 1250 188809064 188809067
    0x90c030203150c1804021b160605030702070b03091903030e0d03090f0809011b03030506100203030702120901090e01081608150a2a0f020f0c030a1509050a060902190501 74
    0x42c0d6108042d000080c40c1a24403c4c00081c001e406150707800002501c40d80d120100d1154005000b0208032015014031454640722801194688005c84104016a00c40d500406c50049000e00039075221203140261a1f15040008420000c051680c106030000fa49620364008466010301412184102c00d080c10001002180c1d555060382820050140007900d010a021500b80d01910011285a0001d0750b03109811305075243c0600100410758400740a8449041250011800081100d00860440c0c00800b0005034031409901d95a01041c6507504111042c44006045032100c00d00c00d0107070810b88060b1041a01c804860314051120754000c01d401d5020b80100710342c0220503d0155007008010170046850f1b50315921102c040301c1c000244040a444603005448040d0384420516005800d81e400d841e804c1c0012900c0c42c2d95400403501055260b00914a054000344d4a580c44440d1030580803008510420251100390808039141c2060751101e4a9101403000c5262407001801f4465000d107901c4074581c1803500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 188811564 1250 188810314 188810317
    0x16030e0c04050405031c0e120a0c02120c03030f0301090e0d050d150f090519020c0d0503040f12080121030507020f0a030210030f0615020607050a030609090c030203150c 74
    0x1a03050007595a40082818030505200710b030211150604c0d0403221185003802000105414190b052250103460900003240c06210207d421400265030340488881583e000c00890300d10f0303032800b80c0103440380844a81c060745040c005407200d040001506a129890000d0100540301440c880c0040794215000c011a566004401d0741c15030300c000800018a01c12500c0a64040b00e002d40085c100751401c0d00340050360620a800c010301c503180c1440b0b080050856071444809034047c00b900040e8941001c4440d049a43c4100007550b0300c14003520400a443c03100d501c40600000b070b40004040050041c00042c048129055440c3c660070440c030321960802c4c1680e0300c00414900407410001c1c0304210400b8902015034a0b20114006190002c0000c01041d00e5030902400420b805416085103600f003c0b0009806a1000f0340030343c00d41c2c1c2e46c1d0090300681d9161481110980d0161a0100926681d4240440e800042d441141038080c0b0820040f11210f013140100340c500340d40c402d0b0203201404007000b0420784160010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 188812814 1250 188811564 188811583
    0x7080a08090106180504060b150318010b28080d090504050a0e0615010315050d060c020f0105100e090d0c06020a02030913060e070215041b0510030516030e 68
    0x340401040d255804010b024154a6000c944400b148491064007a0101c1d40070720300035407160208000b00080310040c041740f0314028a498550107420b100080c4507002941400d0301464110000003003001c441400074480c2680303a03402000d00040c08200210341080381d2440700241022600402030519481001480b00c050b5008590159403980c01203441d882682d0040e11041c1c028034169503852920007a040c000c8041000e510340020305201da000c1d200c10a442c03200c1e05a03140070302500007440d0700380c54030005441079520341d07001c51055130088150a08203204090003016103011294110745045221400107401521a8405030031568540040c5604084800d00d000e40c00440903172100b110400985c111b0107200550b94001c0581c1c0311703102c0d030140298031010039603140d502414020748951100700c3c0d4461115100040f15400d99021401041c0e100048030384000c41250030103840d5485001048650f0504164503010036155424400c02091016034004959003a00d0100034004141420b1940c5e002c615 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 188814064 1250 188812814 188812817
    0x30c010215060f130f0b0109061110050c04030804091b0f0206130c0816080f0610030f0507152d0c06051b0c0a0c0608041a15030f0708070b07080a 64
    0x40710b5400d81504c03a04d0134408a004c83c1c440410840301c2c0c812841c00600200007049000400510010460f1030003200c0e850054042040140303400103071854500014040600445500103052100000191141004001902c0e00200115080c0030460200011050aa5140c403d0040c03941c6034000b510390004000360301120701e42d541c220035285030604400f55030781e0360080d0817207014a800d881401c14003540a5021a65400220341c3c0d008007102d400c984035507094070003885241c0043e100300046040c0e056004038142c0658141c6881540e41c5d40c20705000303c8108003d02c00b0888032109000540c1c2e1003000c034680c81522403400101c403008100c0040804014800051040e55240e01250204a180c01446072000c1081d0700a5a19842c030208966540031503d000c035407400f60f010020810610600a050245d03a0100c0540c451500080100008500082880b178183e1410f412080a681d02001176074103d100f01800381c90301c541001d151a003800d4040d08030114104d42005a800024400400c40301c00030285e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 188815314 1250 188814064 188814079
    0x3090e0703360501020a0905030c0303040f1716140f09040203060105100c0b0405030c1b0603040f110a09061a12070e01301b0e121006080c030c01021506 67
    0x14441c0050501c5034001c4083c02c0380d0f10108070520314035001a0294241c420450032140305a050000305a542d20850061205025450fa001c1200c111200300344610003a000c020355131621480a0010a103200c01c0d40104600c0310341c80c051f1982404c1c00c0c14000d080d05001d48420800e807820350042591a5010311649004443c2411080400d6100d003030501c60307140d0b0080980085040a040040d81e82c0c000414840329802858580d071010000c50142c0c2c19041005481d6905582d80d6889414500b644440160f81c01280c1800b088811365a1103141e0025150a210025096041141510360858481c00d60020300200b0004d2074030002e0030070526580807100781b401d8182041c1e07038001200c140310313454401c0d0028000c00d11508844854148202c581c4920740d5002c1040c102c004a0010305204450b1101012a001580115260800e078003a0300618202500f1900c00c000d003c44020300b280c44540c040c85580e041075110019919041c01100e000c00c002f48000c0c8051a05000041404100504581d114180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 188816564 1250 188815314 188815391
    0x1006180519030818210c0105030406020f0c1c0c05100902060c07060f08070e0904060c1e120b0301060e0109020d09080a05221805060a03020d03090e0703 67
    0x5044074031501950f4400d01d0283c482c00031103010000003c54440030703880761202030111034040203900f05c0100705118820052039560048001900e803540003400035100d40c0e4003002202c0c00541c0c103034001e042c20030b000402012444030400c0c0802031000c20040b5401000880d00c40303803002c03400020340c11070006481140011891040e1000800902c940e0100e50024001c0500001d01260849070b04141941c09844400301a0b80380001160380319208070304541d0152200740801c0115050b58400c00720365545091271048510303084290602041543d0700d1100041070316400044403032a45c0180410420705034001c0c8411400e2a0803a01c824205018480a465000c00e1440c5500b000750001001d4640252030503980d181259401415544100214068501c8400b0316031801c0b00003540010850b5030202a000290b1300c05410303c40540000b4202c40c0d400030810b5400301c0503076244040d0b6048284a511403243c01c0e49070101c1074611040c01000c200c141403030300b00800768a005100400c200d000001114610050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 188817814 1250 188816564 188816599
    0xe06010215242806030501080d0c2a0b07031701060e060c03040e0c120f040b070c0212030d14010801020403020d110102100e060a06090221100e04080310061805 70
    0xa9011010343c0500340400900c48026129281003a10101d070707014020342c5c2c0ca07420741c19520700b140034007072001520130b81050021034128545a00035015a1050340800780c00001141411365440e045554011000160070301015004002000c0b0300110301c1d00c0b00c14940c54180050a482910b4040500403000041c0c0c0038040803041c0120f40c003510240100c04120309240070810250f800403480654036400701030100341c0341411601c01501c00da5124100c00790350740d981c5a040303500c1c6511701400c80e001b130941401c03040c0c849001c1c40500314030000f0240000740000f0300d14100b076081c5010f9220755001c0c0d20402092003d8dc4566440700c82240e0070100030182c100100c1c00403842c10106150b030b02152481c0040d05156803401142585c0210100d0400b44112034072078a1038000c9201e004009070303403400010342e0468085003908200e94404c62110084120998410200820440440c4c00b118071020002c2013011038011420703214050005407910780f80856104007000d0304564540100ca1003224145860740010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 188819064 1250 188817814 188817829
    0x80a030e030f070603050601030b0102030c07061202070206040e0a050601110705220e1b030c0109030b04111005041a0405060d150f080708010f11031b0904060e0601021524 75
    0xc2520b004075001d07541c1d9004c0060050000390750a5000904004204035158800800c0e140c0c42840385000d061010b281c0801a500031132505d1400e50640d800f032040401607910400134000800c0e6135500c5100038540800b4a8003100c000400d11414026002a10300001c01c000a11100f0350382d00b50f0b62550b040310f084900341e222160511141c02990b0505841c44080d46001c1810440d001c00c50350a42d200140c41c3e4105a26000c2d240c1105000404114003040411240003040da0000e02501c45007440c903040c00040380300305245000850200d00002020040c1001e01c40c0340c2c80d0400e129511250070641410000b4440d0711900c41c070008102c0e100d1408100d00c055401d90342d0000c040f40c10007888c0b11303580d51800e40d0b1503015a1054189a5190100d408980c2d030141c0942c2c22251920820305181d1394071008403194002c07880d01030003858141808407100c0c03501d540c812040508144030039007949290072800240313850201803040000d00d0b2050144060b603003505851811082d001c0020f00c501c0c82e600800b280a5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 188820314 1250 188819064 188819083
    0x61b070209090d030c030204211a040317010803090f04020304030311030a0f150803040303110115170c04090203030d090f02150c0d1d090402010509030d0e040b030601080a030e03 78
    0x20a81800502c00038503400540c210066142d600c0600c188600c40209a040f0700981c0720b0b00d00c400c102244060319000c0007030030740c0e06964030661041b080f2010080d00e011100c402110120701240d0841854400400d814040c070b801020104000c42c82c1c4035442c40400d0360098142141805960044003003000c15010340c01c0003400d030103105501522403902d800c0e180050807480d042100c2051901040c281c0e2820001d003580180d401e0070000f940341a01e1503504650030140c0d5900800c455603200031401d4040c1d00c0310030f1180145003521008600200b901141c90401a1a20889101c1c6107041e40c0400142ca0200944034074800820000170025110b06219194010685000354002c407003400c89880c000c8550040c1c199074000d10103c441c4000245011350704c0050414401001421051108a40d07240240340164030501c1894482d042c94850b00c0880d107000f40c0c032401ea6010803421201d0007580d0410744904070850303504400601301545013500d010f8441140781c1000d0200016911031080701c1e1020820b41c4103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 188821564 1250 188820314 188820319
    0x9150e0d210e102703140d0c050702040e0a030c0809060c1615180e0c040b07050601080c06120604020711100305160807050910120e060609010b040602061b0702 70
    0x9002d00c00b849194440c0e403501e25500310140f07480300720341c0610f040d0020825429056102899400090f4809845810080f003c2d00c801c20001c00920000c0c00300c5000d21010300b00a0303100c5540f00c0c500381c410031007980c0300c0d042e65070700c691301c0841c0c00d03030120b540301440000c021340040c0d81c41d64801e42c03000800e0301841824034460381ca1045e03c6422441c44c04032482170048424030410324100204681c41280c1d0002c50b420020066a1111310510120000d26010350b001251107280c503240c01d641d80310f5008070750031803081034500d500903000420400b20280520490501c0c00c82d00e1a20340140700105803040d42d00a400c41e03001d181d0204020080012030743c0c1c001c0442ea002000a054081c280340c000303010b04002c480c0c050b402c00a4085180d09030307004200081c0034880544945050035070b5042800a0b010b070701d1105008005114102d28981c00d0144560058889010302500f098903080060080c081c1c0d040c1e0047c0b200d680104410000541c0c08100c2c43d4005192501e00c0d2854a091b0406190030f000c0c0d4040a50f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 188822814 1250 188821564 188821571
    0xc02040b040903091d0c0a0302090102011512050c0102030f0a03050624030405120733050711010b0303130b03040602090301060b1b06071d01050c010f09150e0d21 71
    0x1010326400c010503804a51803845050f1400c0350217040045401c0c42a10308100704030050181690607402038000d40034107407040c400001c4145402c04007000c2040290301071043e52103a0111001031000900102c000000203000841ca4070001c031310034061601c02c03040c0c188101980d90020803150303a40e05410300e61240c0e40045043c0404219031b104c10142d030094604603420300ca40c0c008221340d41800402c4d514550340000b140580c1318003146000500099070712051403601075151009281162500c40c0b54040d0040303540b010200c000b40c0003450300b10384800c2c14451081c4e009200001418289040038006c0d10401e0048948079151231a040019000c0c000c0c03240d51650078480b0118841c014070740074150000707000380c2d0010380700c020b01c0b659a103a480c240c0d65100082c01c50300921700140e4000991920031740061621514201100200030308440451494044241d210089841844140200703c800c2c850b076a2002c11070491251f4601d695800d104030a9000d021003241845030700d0040d403412900e00b032041030061 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 188824064 1250 188822814 188822831
    0xf05100e0915090f010605070b040f0b0f060f01111e101406100e0d030e0114030a1401060807020601330206010e0a020403050c0f060705190611120402010c02040b04 72
    0x84000245040c2d51401040c5007000a0010a001e01c2c0960403070320161945450310a158980652341d0f0b00040054071001401c3d80301f4000225440c10207807040c40000c240041d0341c2881030402c1208504500001d04102540021100d180c3c80841c4c05465011110045101209480d01490900f0075090780b10310020f14191081e2200020001c0c02485004100c402500300d2092041c1503510b0294060030680014103880b9002c0003e00810148007000300506224840340f0501d038030784a8542c400c1310031005943d1180300281590700c00c010003a000d0586402e00d040c1310b01c1d085000950314201442500000c001024101001d400001d000501e00ca00034600e01c540b6a104400c0a0755070300084c40380c41c1410181c540062002140391007502c082d02d9000c0050041c1c400041c0400c601560341e644d106500003003c1000300300140c0100100e41005880c0c500460b6000c0680c00c242c07040321011502880124030411980744034a881d40d001030392050342400c15024002c107c1c000304004040382e040103a04a850800708 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 188825314 1250 188824064 188824081
    0x604060c060609091203051906080102040e0901090209150d1401050906070f0909021b06130311070608160201090501020a05090310020403080304020d0609060c0302120a05010f05100e09 81
    0x3010418018141803140d180e48251050884140c90405800a0074041034003140603c0398100582000d04581009001500711140d802194034a5200010580d80001c080242d558a004450f41c8808440e00822843d001c54001c24058038004150b0381c8020200500b0260f40e90701c8036000341c03055802c806519211440c44030114020407003920300440d203109410000d55000c0c403482075004145290703030380c940600c1e00d00030170071019400c40700003c03552030300c203000b0365042036004c1040c0b83c45400c0c000419010050142000f50801441c0c036085003440e013011b40140841c903080300c00545c00c0403040c088400814010b010880c01030507071410051165000140400d22141d01601804042c03038100d06490305129803c101d1001c034400d604c0001c03c00a01800020302614240c84c502000500074840031950b019180c6c4d030a8201d91130307025184046a80400c800303540107984141c155001c1a0b0074030410195051218940c440e42d06440354910034005050000c180901c112076140c0d10202c050b0810704281010242c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 188826564 1250 188825314 188825327
    0x3050a030305090c0a08070b0a09050303070305090907090503070e04050f062a0c19080c0102040f36050612120702030124031217100905060f060f09030c060406 70
    0x400f440c0a00ca10140c000041c03910720440d03412240f210009115042c680b400c00001d40d0049401070041c04503203040014607450500003403503040e00c241d0364240d442104404104800e0300c0544448108204a1020301160310001145403c0e81c108040b13122840d07486140003481c2403280429a4214020b81c030a1000c84100368100b03805131101e103c0b15a4200004181c4000c00e4000c5080004155102101c00300c5042040c3c80f480120307130b0013501d0301480e28100b11640d40c00d907802588a10110748400c007080240512080b0000d0f00300442100380951003640c22044980c41e900c0c2c801c009000d55032600414196a100d00d041c03080c00f0084000e4420001044a0020140d044900164025401e040041886080c000c000103200a0301e0f1010b1603a0a00756111042005031641000d42400710184031503a03030b512030491a81c401c000d81503131020303117905052051080c0d4901820003070007003012403d889550354071042941c503115807603e0020345840c403a4000030328000d140d058440e040380d800200810143d60120 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 188827814 1250 188826564 188826571
    0xe04022b0e070801020702091f0b12060118060c020f060d0920010201052a040f0e0402100801151d040207050d0e030604080d021e0d020a08060d0222020403050a030305 73
    0x20280c0d40c0aa41d0380c441c0751300343e00c5000802540444120006030151000c0c0b529201010010520400c0c20f0b901c5d4010071455610082d00c07460b10052110402800d0b6a1002070340360450022005c1d801c4091900340082c15061020702c000f8401c2021001003070241c0c40300000d5500c03110b05200c042c41108440d0815600c404000c042d40740301911300824411107540140120303409030100d07442c3c014105241203c3e1072000f03c00d0040301808410100000a2201d601030483c5015000180c1e24134034a04040c810010001442c0352040c040c0101440104080e0f00d2211030020001c4c003d041441c1c080740c440c0300c60394000905805199201e4400700740c1d541841000111a00100d00ca0384454540d0310381c1c44200750741c5800496004013082130401408200c0449074000e4002c010744002d4082080c0900702000e00c40d0382040c03980d420303c240d020420802580d84550000c0d0444419207841c11042c0d120f402069692080c5d452204050000b807030110103000440d8101c500031604402526001022841d0007130103003e0a4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 188829064 1250 188827814 188827841
    0xf040f020c0712080304030c030e062701110705010e0a0e04030509090901020f0a050702240a0f09050303030612030d11090a050108090a060c030b0d06050a0501060804030e04022b 78
    0x42d0002c542c90b420300781d0014000e90071030b20260450381c90741e4046602c984000000ca04004441c0c1e40140141c03030f103102400c811418034040844101c403030042104000e100080041c10085400141c030b82000d404105102500e0003841d14640e1240c605000c1171003001580c1c0203c0d10104803808000c280365014000e00342841d0121000c0281d44c41e180d041c01c0c2030b40510342d1a0815950300300903460085010380c00610741144081c1c23200800b031601ea2581080c1081040c82e40041031000911002d03041d5000340c002819840d54200710074864100380201e0383d68000200b0750750107002191495235401d14100240c0c0c098010100041c421054020f5007840c6580004503218025511940081801d42c0030321380c441d01c40d0046034005d100503801900c401c0c001d000960001c2c4180743c4ea50344541c40640b05c4485101da91401100042030500b8072002000407504146e02c03100c20025400280400a98410324010055404580c0980c0f00c000898564000700c1d0091940f2281a020b00c418011400280e0042600810f05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 188830314 1250 188829064 188829073
    0x60309031812071503090b040b010602060a331509060e040204060f0806040e0a0f0c050d0b040308041b090c02060a050106140c010209060307050403060b060a090905060f040f020c 78
    0x3401440400d10b118440c02c0d000350422201030145107058007210014030510f1401140e00100c91701c3d4000039200c180e0701135440070512001803005c00d40400045801c102002c0c8204200c603130380107400c643c400d600d01e00303041d50a98a11003011880700080320300000e8501c40c0001007408000c4400645801840c0c0314007004980442017410f0a0300d094402c0e501214a10784400740d080300750300c80842e110800104030320b620654624a400c00c40004000090201c0e2280300301c0202c2c080641003850180501c0c0d40464410500c2881500009a402c11800d422a41c5818070510a4803149003480306210010760740840c43c142e800c400101d40d00f59421000d480d0b016a005d036030a68540b05508410ba440074001c039004112076131440c2c41034030008001849105940b00005091102c40b000050256200b80c0300340c80002c0000c1410300038091544600802d0300350484c1e10303038a8140c2c500d0010305168880d108120b07899949200042c110707101c00f0700000104000801c201701001e4442a500001e4100c1c202e1090780b80304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 188831564 1250 188830314 188830357
    0xf1404120f082704091211160f092a050c0a05010c080402040e01050603250e01030b010305120315101e111b130b01050f0304080a032301061d06030903 66
    0x401c5e10501107001d401c540e10100454015206480c070542102c1c1003051845030013411035407600d49061442c040c106502881c2c03000c6107030102000c29680c1003261a5070178000c0150403a15040445407042d00c00510381840f54541281441c0c05041c0507001c80302908075400c00c4820400c0560000105120300d108071410804150b18a071024202c400854441d03030158030010215244c80640e00584210520170304000c244d658544c00d40d0b10040f0340aa1040f10482003d40050040000c240009801c40f15590500b030700390314040307002c45040151441414099000041507115040c407511a4028071070341c2c0240705e0903045020700010a000010300c0b141c4d0080c09001c1d007010b04519800f0356262020001003280700b03802d55050040c801001c21205050601c88200220310081f44000060343c4914050803007140c4540b4010030240c02d07680d02c000501c2041c881804200c2054020003086410344485103080d81480c1ca10303c40c02801d0b800d0081019a005201004225071070344008018100280c5042c0c1c0100000c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 188832814 1250 188831564 188831569
    0xf1101150e2401140c10020307030b030318010507080702040c08090705010306080307140c0310140c071a190e060a06050307080601090c0302040f0305030a0f1404120f0827 75
    0x2403007206024001120302608018542c81004441225401342481c1e030701d0000700c0030440d440e144524000444d0b0507008420444c0082d010710410341c05020640103580381450043c1c01205180a10b590740c1d0500101058000034040c1c07141c103130b42c4000d9014104000840f2601406032000c88201d5034282c280c420300e503011849503c00d004170710442d5074041c0190b0518401d0f0343c52550420048020700020700c105000b40b10295030400400e003200800540000b100306034201c0d490b400200c01003400c62515801c10022000815294034458145513a91103003000d610764105048005101c10440c2d0076940c01c119404402c180c021402074060541c41c0c0c420030440707540310203160b1651802e200e40050f5401c880b00400031140d440c0c02c00081443c0c5071030018602130329030303254921242c1c1941058500c0c3d400030840d89030182c1c1105844852030b100f1b0904030181c0d840000c0034501482203025600ba0f58214419140401407118a034202c120340c012500c6440b14169082e007842d4880d841c4c203041c1c0450550b01010300a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 188834064 1250 188832814 188832841
    0xe0604061e050d0f05240c120a0e010f0f1a09010308121e0c0d14010503030409020a0311030405011509050c090f010e0a03030509010f0302041202010f1101150e 70
    0x5400c0e036010009076840d10003080440c007101030094842c40d00003a080c40c0060414840e0040000d0040e280e0319403410172002c030a4038428020404030100104200c0c00c0081c410602d00305030f1114887c5008541d00e41c44040d81c5014084100c01050703107504046084911a680e41c000b50040c110b000010010344100c00200104801c6c06e01c4060140715003040024441009405101c0d4080111242c81c0307414404008200c0248000305d030400e0041c070b008140410492130700d000d4050314003050242c00e140c2c0d504040001c2e45910a80c03044141d03859001031040702c9070340681c11500d401e01655000301e4503460182001b9010f4660000f03802c405079803010300443d050000d4401c4a0043d503004003002e0034040c1d28070a2010400d0f180c45c8035414003004403c2c0d946507550b03e03c40c1c2001b4610a980d66511820f03544005060a0b4012074550305240c0140010320100040030b00e102083c1d80c092034504065032040348103850512550480209035400e00c80702036166080104803e0803510207901c24440c0d503503640c00c1d0f44880c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 188835314 1250 188834064 188834099
    0x6020d091202010e0d0f06052502070b18060408070501030c0f1704030306050d050a140a080d020a0c080a0e01090b030115031e020726030705250c0e060406 68
    0xd10603801c080805540b25001241c038444020f13203034103071400190303c41028456070160100c42c0f09880d030003000032200c1c12103003020000c40080c0d5980880d844d1100c001c2d444094500030b200101d038010541015001c8243d45016094070041c103010340d01c54882c410305840e84024010280802d0610740224066445200d03600d54080c1646e403140200703016111566204007004c0e0081c1c042503203408021646a98805c1d80504591040d0010611152145420b108482003140b02d4981d07500480d0103100400e000208031038072031203000030041e078a8050708800d0ba14080760a402401801001c03d1042c038003904811100c040310b000345ca500c04150b0f40c07101c1c3e41328503100902a6503a520840100c0380703142402030700a06c00e4646402061400303003002e412050106e03001140c1c04c1c3e9801e800f5030f441c6803180140071002e601c50705980c0c41d89842d5282c494800780480c81409d1255a8540ca50307030100705001c0b0b40c401c44591241c0d000c40456005139644510184191081c3c1c0d4041c0705500e41440002d454090700c040600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 188836564 1250 188835314 188835329
    0xc1204061d04020f030a09051203090c040b0411030103050a05010b0901060e0904170d0204050414040305070311032701110705090a02070c0504020d02070308090a020904080a170703050106020d09 85
    0x10941540c0400c0d81040d101002402d030801d40900c80b1000740e40f162805984129200c00000440c1c0d001e80c140b039494403841e10707a070078402d80c020800d21421960120320340d50740e91420f84002ca0700802c1c1c2d201003001454041124040148040004000c0020224240d540c040c000c2009011211030b040411441040078407500340450b6445480d010039040c90780000c1d5029003c1c030502900855544500129075020046490050390b0005e400c0c000c1e4030307040c4120f0399400001c2c00007103024605a41d014040740700307088018060010403a1142040c01d0100116452000040d51958500c203514a5190b00007170001092804680c480320700030099480001c1d0b0504944c001002108030761505019036000f50300000c030907144691101004103142d1264002404e0440441c01c0040e9a81101e0400802880340581603500d9500305401d1000941d40d0400c6464005030050031041d80c3d450380005c140e40d2608444200980c010b80082080012501540720750704980242c3c080d654140d00d090012a15038200c2d0189a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 188837814 1250 188836564 188836577
    0x9010b010e010c110d210c020603011e03080a092c04030e030c03011104090b06030c030601080604020c0f0a02151309020f040e0112030e06071104091b0b0c120406 71
    0xc89542c403543c0c1d0099581d0080210f055104800c102003070b640c83e0164002d440e40a09245d0307056074030050350300d0401e41594a00e0040040140e41e40000c000d44410b2280e80c0b00c1c0354036001d840401e10b9440040000944d130002c41941e85010040e000303000c80147d40f14034111700443d501b0024050385404e0010340da00c0d102d04080b0b401c69440366415100c2d0034201242c0d40c0c040c030400c2c8603680643c4091046090021040b04080d0725240791800d010251080100118024401401481480103070300f415645c00c50400d0810080c50360301c04011600900641c0c080d60b6180c030507202405040c0c4000320782c0c62a102e0080d0b0341540000a1001c07030407120700c01c00c041c5c98403034620900100101a070a41c00b0344804001e980405141550740c24805021042c284c103c0c2c0c49003040350210000705500700560032116401a03444c18200161615140c0160464405290086485100d0042080b070f10305019a51240340c0140700d81e0017507c960f0029800c0d044804519968424030400c0c4000d5240d0005540440d0aa80c1c8d500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 188839064 1250 188837814 188837837
    0x909010e33102a0b0a06030f03030c0201020909040b0a050c0c0703020108060a0306050103030504092306011803080a0e03120c0a02060d06090c0f020d0e03101d070608090609010b01 79
    0x1d5141e0031000c018041004500b1000ca1195107240f1a0403110105401164003900f0350402d01c4207054060510403a44c0d140010400004500c10407445009405040014190a00c0340e000d9019101e4101d005500c120103a040004003c030302c2a2141c06038480d4a01003007650382e00e4108009034071410200300a031754890407040006601c240d0b15180d120501500d9440b54030b0396642c8040c162002a001140425030104003070200041c0c5224010201e044a03c8800e61814600c800002d40c05010780b0090400020803a030300c80540000e40c0420086500405081e61440c1503072000389840c0c80204414464040c00c411400c502d84410300341c0b440c0e4466000034000100c0d456007000940ea2000018103a401d841b00c100281d40c01052250a2a148858440c601e810003e420000c0c18030112049100a225178a030510000e03440000b64440340403000540042c080c0d0301c46401c018648940c882c485140d2080340800b0815951003e00140500d0f61001200e5598441c440c90380d0a95aa5103001ea0028203040c0781c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 188840314 1250 188839064 188839069
    0x9070c20010509120a060906091b2301051603030203010603140609181e0d120207170307091a090f100e0d02010905180609070302040b070807080909010e33 68
    0x441c40844c6580c01140c81003001c6039118020703180e030307a481a141c45548100c0601440700245400c02e60317010b02d448810404e404c0442c110004482c1861050207200e40c80708142c5240d0141c01181e6003010340f44100460703800d02c0e1400230041d510902030800080d050241660034901c5402085002c0c24005200d01c00503903405081c102900c1d20116580580d1281d85240750007c580101380503880b0b04944003602030320b48041c0307026080140d4034002080380b510420040010880c003907035101140e110b603030f2030076500d0301e0b15032048589222680103c030380044100050b07128000440000d0403c3e900c00e03240d84440e2000743d020040d440b4128000d0201103241814116228544100b140c11154414102101215200e0004c101081d079101400c000c2e0300d6200c41030003030601d0b060b8012940007a90703150651034282031640c002d10341c2c000c02078020803120020404404011041d015070318000d00c090b1105445607510b14004d04c4801003582c10440d40e5010042481e100b4940070010100100c0391008688040b408109 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 188841564 1250 188840314 188840329
    0x60b12061906080d1b081204050d031b0206040609020a080f031902010b1003020d091203141501090e06060408010e0304031401060b16050f0106080a030e1c14030909070c20010509 78
    0x44914010801110301c40120710407c1d40d020310f00401c0100710140440d04090111030310b94400c0025440a40303d0004001c1e40007a80c030343d109a000d60007252481703180c80400d4903a5010b81003081140102104400b04030300c00000b800000903a00d800d14585101e01300c05078200d5110004203034000441c05d9081e1034032030003a0000c04c0a1580c0d0040003a0700c0b5483d880d2001121a100300c4030380040e8441c8091074500025189080e00305244040ea142230030324210028000140030700c501e200340700b07505002499554a09050310000c1c48890001d10403c2c0740000b1951b1641d02900045442c2c07002c015030120100c40501c0b038002a07070010b60302e440c9840400394514404c0d5418a8040341c940c0300d074002200382c2007000c2c06210010400100104a4600d43d40760140c44242102c07036660245410500341c0c1006004d1003100d0501d04d030820705440f01024094651070962080103089a000b06051040c070580942c4100140a4140240d00e9030046a00c125136600056450b01c5d5401d000036028804140c00c0d16200302c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 188842814 1250 188841564 188841617
    0x12030b0102062a0f130e01030501230a0f0f060608100e070206060609030a060e0304090b040b0303030a0b0604030c1e140a17010e0a1103070b03070804060b12061906080d 74
    0x4d69081c240580040a0082500b0541001021000c11801042000000d000f56071520070150300d1301410701000049283c030b00e180200040c10f215160b10f040b040310041907021070039403407a1181c10b00c00c035030715140041c20482c0c0075900890094136100000aa145c4410002070140e0103c2e400740c000c50302d0340b401700100c0343c020703071503c561502a945060b4002000c40c41040c18110060b80074503101c0f032528150100f10b80c000c2c00e505024078148094a64181d8021003200e0b8444420344002039800303024800320740140146c2d000201801c41e64000400e030402064104010300e500c034000d40103415100d90310810b0b035180e44243d80341c00c1080c03040144101ca18030500303c1d119051000c00000e40c2d2416500b0b0301d01c1c0ad0340b0b000059508107644030070344145003000d10001000e00211388002c1d00c0c508002c0760007444a82c0040029042503520049802142d80c0c00700d40c20b00c00e10001003120290b0030300c4025039144c01000d5901001c2c10b403900e80005070813400800c92002200c0b4130b0301c84007a0f078800e0300c650689808808 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 188844064 1250 188842814 188842837
    0x9051c0b0601200706030e03070f0b040317100e2413021c0b04150614030a0f020a03020a080603060c0a050c070b130e0601140403140a12030b0102062a 66
    0x10241e0120f82c100b02d1034030350700351a803030000d01c1e5040c90042c003c1e081b1620b2102c030040d01e0f00f0070442d140100b03035050855405640c0c0090729800c13a54407414203c070b441040c284e6000100c5081800c0c05280c0c1071a1662034169070035414600c01940300c02c1c1800581541c511784444a10940c0d05602900d445c0c00b4811220700480024007620b81080c41800c407041c00403c510740c808559a40c040c1010074100380c1b090060744051000300c808454204240030b00110720000201c4118800040003c404010a400ca039080d090161301c00e645400e0005d401030043d4103e032524000158640f030019005140024100e0300402611003424500012004119000d60103810781c6c814510035014001281c030613100041074541000111551218208150f060380c0c030801600007410008180300000c00200010300b16011264007404900420501180c11401c0c003080071400350803103010390030210020750150001034080001743d0aa0b00c035a03039441034801e4021618095003845c260607900294540707660000810000000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 188845314 1250 188844064 188844077
    0x3150d02040f022a150c0a1b030f0314071b050127030f050a14070f150f0b011b03030528090c05030613060b0a0e0405010603020109051c0b0601 63
    0x24a0b0318003040c1d901022000c80c0071004842c031441c420140410340030420480801500400714031488a100604010308410f10700200000e81400040c0030321a0024000750022000304100020300b4090122007010070200082800c1901c15461410000b000c00d205103040e4503081101e52882c00c000701c07581d071a01f90440b419980c582603a01c0c0e14075402c840c0d0b032001c001c82211450202c6c1e2407038028005080500400107016007480b21034062500501c01c1040000c1100485441e401c450074020440c180c0c2403c081e00a464818842100c00c0440d0410510101d1003c014444422400c0046402c1d8503003040307500f4410046141000003034402d03080396404c208503246d00300d5041c400120207100300801900101605660b02116410044d21018440003060201d014007414504500c100003200401000184140ea9601c00011035a1380c20703800801804071106540d04038a01481c1485c02071010b40000d9000c92041c2070005036926028105140c4107104440c2d002c0c194100c0d6565041501e07000d458a41480130 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 188846564 1250 188845314 188845331
    0x14010c0203010615020114090601180914010603020a050a03030c060f020f0a050307020c0d02030a1211010c0306080c04090c03080702010302041203051314031510090204031a0105040203150d0204 85
    0x5090003610050703c0e03d10342951395400041c20203400c584000c6044040c0140180800c080000c000c6a0036045969810b42142448984a5007034000d0500c141c005016501003e180c04068030305511403415a442275494074807042c3c8417010420343c54007500c40180000c0d1350550711400100513400014065002160141c146142114078541c01e400c2030680b6070004070040108076980758100324212454600756500c00c054055034001c00c0c0c98a06000b0f0251114000d0030123451401c3c40303010840ca1103d8041e008000700d500c02d140003005000304e0b10500849114120010560346405e03c545516a03501c0840680d2032481d42d61400c5d80c5401891050303040c075500340300000758100c0700052000b40c0b038802c1e039a0302d03034850301610f0807002500d20381c0001c03c0c0c1151400304910682c40c00518414610007100000c00d169a61240c8100e500107030781c0004c400385c0e0010400004222000c0d400001204440c1000308642e80c0b5103040c0012400b084840400c507403c24280c80e8100e040410200c40086d0018001090300c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 188847814 1250 188846564 188846569
    0x30c03030103051005010b030610030506010e1c020a0e070519090b07230105071d040e0703030507140a030f050307030902040504050708190b0a0b010507060f020406030e0d080114010c02 81
    0x8000341e2003550290070000700c0f100d61940d20f200301d1b0b0151426504d010700b1801c0c940c0108000c40d50642c544005c6c5940d500c0410305681c0070301d0021546e000c00800c00c0c41101d10303a202d41c1d00c112406481c01ca00810302000041100910340300d4451003120036565581c10051048030304505030f5a144040e9007481070080b00410901e400100400c0024020484c0c11003841c14042100804221b4068101e9503915210a014001c4d41c0300104000c019400c0720800d040400e070000143c004d2403140350301902481520000001c00d508407000e07090290040b154210310841042520f43c681c3c3e041e50300140014242103544035014003850145800030700510340040c622a041d07010a0440f0410748086e500c0350b21086040040070390400c184034100c095407243c1c1d054441159980f280394030010301403503172450720340c50884081c0e40300300c080d203c805802500a00403420008200002940203008102c0002c0c1000e146500701040000c500801500c01e0307460034250782c40d1151813034541c040e11940c10304204003031201e240540e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 188848920 1106 188847814 188847817
    0xc0206030c040e130c060f020706120e01090f060f020703050702061602031207020a05010c0807030e0301020c10020c060a0506030307030806060f1612141b030c03 71
    0x944840d1a4001e050180da0000c00502030a602000b0f149502a00607020440c02042070810507901c948040762004c94580b0003c0c0542e03c440c0041200700e100da281c0361075443c0d00c0302d000122134207050885801e503900140b05443c00b80c1004690302c180320143c40390420300500301070300310b01e04999558080e05a0040a102900c100300220301d000b58004038100b98072103143c1c014107481d554200c85043c80d0035034000c01c0040e0f000e0412803002107015401400d0400c0b8903a0846102810882e2550302141c110604a00b220f416540030301050700c14800801506030a2410031f1800f60f107801003e25400e1a0400003054070682c64181000d20085403404007c85141c1b03905450519455a143c1021038244d00c50804503c00c1420000740000b403003405240050740c1c9500c1502d02c1c048001c5038142c1124400304040582200c90400c11030006110420300494540c150300708140c0e4100f0401030003144c02c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 188669064 188848920 := by
  have h0 := BRFrame.cov_init 188669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 188669064 ≤ n) (h2 : n < 188848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
