-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5280
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:20:53.00633+00:00
-- url     : https://prove2.me/submissions/37bb31bc-152c-4ab3-bf8b-1d111137fe74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 949460431 ≤ n < 949640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 949461681 1250 949460431 949460453
    0x6020f0d0606080610030905030702060c0a030207090204210203010f151e1d10050a030c0801050a2a0908070b030412030b0d0201080601021f0e0c030604050d050a1803 73
    0x4589440d0910110b0400d000d040c1550041c00701400c00020444001d00541c02008840e000ba107103448140882d030010b036121002090340c00d503000e001c0d1210005074a000fa18240726a0820140c0d2030040c0010300c5601c2140e004144003a0700800b2200c4c0f081c16034004a030040241003030521480c1e040400140c0c7c4500e00c16460000c413024040c40c121030310000e42d103501c940302c000e0007079407803418030134401d03840c10262490000d40141d0aa4815403c5640d11000075110240503802242e50140703100040140c51003c0c400c4d40e510450303841c0f061080d00d407914140d440d1462900c014084060140660300c0281380310300c2c0a1409841035001b294089626400307100f110340c00848048858184882100b100d0610a01880701c2c1000041c00744100e05400741d005481550b0014003603411403003411150841c0d44605644a440e00b00c0350a000210080500e94030f44c10070f00e0482c0d4050080c4d000c142400b000680004009400a0301450150b488150192040b82c400c200316080f696039031b042010100900c1004506 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 949462931 1250 949461681 949461697
    0x907090515090d170d02070c05150c120a0207030804240f210207051c020709060605040e070203040f060e100314061905040f0f06060206040b190906020f 67
    0x181c01080111101c05403039031064850b0940c00c01c0c0d14003000c100140d4099040e9007041c0b800c500ca2410008040503060880e00b0042d81500c148100501c101f10900300948000d082002610400345090b031040b01e45036641c1b4082c100d030b403691880000c1d04080588240242c1c8050b692002e440c07641d460317a4103031116031003001c003050304114500d44aa110b981801940513201e40100342d202d2802a601c1c134400110707580c4403140e49140f482e40030040e0300c00141041c02455000f8090044003e0782c44880c5400030315200fa660400c492143c60a070082c8140741d00a81610121142420500d0080e6035001d02242103000c0c65004010240f0803490104606402c0710400b22104d40584502e10201c03e600412006c0c7c54210107109904100351012a44504100e04401d110780380c1501d40906295560011404841c80d0b01e40d400c41182c2e454140050984030345c01044001c0c001c43c4000c0001d82481d0b20340000c045405480ea003810040702d01c01c201b45102d06d80199141541140c003c64460000044042d550f5000c644 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 949464181 1250 949462931 949462939
    0xe0703060b120304081e1903020d032904050604060306060f1e06080a151a0c01050901090317040609020a0b04180c051b160305010b0319020f0103110909070905 70
    0x2d0052801c0d48004183c5040364000401007030f6000391262503c1c40c24442e00100b00903400343c14088811242c1c00e01309818140d10a074010301e80340c07002000040031030f141010100d05000c4808110304420155a02c5101c003020200c800054a840f1b010003e0024802613100820761400c11b00001440e10341603038104201c0c0d03c56a030b80504991054001540c01c05035005100105030110082400ea035a554880c43c40c0c010051841281d03c0c0c0c0300c0b010383d540d1a040d0085c0c000041c0b030018400c1e984030310a01500307030010407040080c480c0c00c40f40e5034054210016802240c0c41d0515260000e801c0c045540c109071070383c0d43c001e0030320300d00c150b00e46111820560043c000c0c40000c580c1e0b1140e285842e2814418502801c40d26501e50342842d80f50407120000c0207030700180304441d1040180100c00b80d02d8180d1039800a40c0702d8000081c030026400b01341402c145406a031004100314000c4c5540158070b0300062100360080905e0002010041c1081504582c00707134805164005c00104104900c0d0b0390005a080203542c4203c1d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 949465431 1250 949464181 949464199
    0xf0902120c180f010605070213060906080c1c1113020703021b1804031805060c0f0c03060106091401030e0303090f0606151e041212032a120e0703060b 66
    0x1080c02a000b100503120320390400b210703500401c0342e1845040503100280c4002d1000034180415401013068130101e81183d28603903543d178406c02c0704500411001e02190b205803000a04042c1900382ca0030f0b0a20f4241c0094240d84d229550072096550300e017901013205209000440d00c0c0c1e02c490900035521f1402610048001c0d203001c50051080c0341084c0d0703040d02204c00307100511450340d0301c0d50221507101002070451200000100c000c1102d50b90780b005412071980500060002120944086140440144005007e500161700611603164020400300075500350301402241402001d004034000e0622282840c002e000200c00d0110201c40456040040e12512080f41e40548441081043c0000ca02a10002c820005c01141c41050b0340321403018007851420072264280390b40d0b003500d036120301c0d000941110108201c2040310012a054440c60050b0520f010718842d0303ca003802402d01c8800e058180520503c50885494210b000c0c0076000351400145035020780e04a541d0324035200004d002003100061080b0494 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 949466681 1250 949465431 949465459
    0x13050f0c01080a0902030a0210020708151906150c020303040f030b1006020106050105091c080f280e091306020d0f0609020a0f1d0402070b0f07030e0606040f0902120c 73
    0x1809131036521a0001d0260007056810f90804c031461050517480340642c024014005503801040c041c2c070114400801d02003405281c48240780f011480d0005861505500c0e0003400e2084141c1901ca4074041c0101e411316010b4890b0710300000346940259400360f07501400070780c008010801010b000900a1901c8500440381c0c58680c00142d01303803400c2e03000b4140041e8040c071040b240c07450a0200206256914151861200919229094243e1142c4100035003503c1c005101c1d600f0000c000e051001210740d418003130345030040301140180031240c0100824454412107010910511985035070803040b6500000c21540d4810042504020340555a4003103a030b0751030300300c00248005040c001c4804c80d880e1a41c603844407900120342542c10360001040e41005066950030301c041a2240c2c8000c102070343c0216034000280c40c00d02740d2502c034668014810020142441005503860000060310f40d0031040c00c480c082207081d958101c110040080c1900654050030300b1000600c1c010001c20100c3c038484050b1a280d20071072003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 949467931 1250 949466681 949466701
    0xc0a0f09050f040906060815040b070c0512030702100c030b01030b06040311060f0d0f1a011701150c06060b030406050c030c030105060f190801060e03150f13050f0c0108 74
    0x8580300306600070b440031a00da065072500d0b40c001514140b04600009005445081840c9080007100c0c1055aa0440030244014080101043e0340d008046103001c84250049a40d2952a600960b507225403003000480460503060003804464000104a04c08002c03001814000070054581030207450b010070701d01481040d41c1e00304070040b502503c0d0841403075280d602c100300500080d6071040c00040508541031101040c40303078650080e9001c1120488010600904000906011035030701d680031810f11000030310007204850009681411601d10f000001012403034104103030740f040480d44c0d000b0000c078a41040072410903d4000598092809480708000d0f6076245000c0c00801e2206580042c89180c041c030042150380b504c00000c0c1034160020300703440d080c4803042d10050003001d00203003d01d02042e0340b41e005014142d4840c4c954205071104a0040c020601c10500b0100c810502400924054800400040307c1100d40109210410760100132502000c0c00c6030600f64a800700c003000d0600150368600800d401c48a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 949469181 1250 949467931 949467947
    0xd05070c200901141e03190f0b0106050a0f0c0201032c070806060a14010e180702100b0609010305090a210f0203090a060f03060b0c07080c1f0c0f08030c0a0f 69
    0x20f0044c01d4170045216110039984031002540400c0e90521500d842d00c015003041c0811001440c0c880c1c000102041001c1c904103074502c0058105a04028061010307401c7e0640c001c1d2209112200ca0610710209031950004030050080011b000031042c203101010601c00c01106566003c41070340f4004c0d984201c0e2a01509a1203c03410707034100d0f5004400c2c02c0140304003c20000e40d0f00710204c0c14101542c0c45080880400d10417407080b2072000e074240f203007010403940039018440300160b440d1070039080100400030000502e09000300c6102c1410141c3c2e50b000507000000400410155541143c0c0701c15101c1c0880f1028025000302154400000340c000c0700d4002020700003c2030b605411f60081c03136980c2941c08c1800884541407103501c540d0801d41ca5043c009060780d1150010280c4864403030180020303609100e40b4920381074909840d00d00482506c00c5000040c621010356400108007417900d00442803d509101c1003a8240801c09050124004140b04d05805007034010704045c0074546035070707403407615440d400d40e0011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 949470431 1250 949469181 949469219
    0x26010501080d1709010e06040614070f1b170c030306190305101a12030a090e04020d020f0120011d06070e040f1d0705011b05030d05070c200901 63
    0x6498982d10040c03000b6a012850348080e0460000a46d040030111726450a0310988050b5100ea58481319405e410503520b00300303940428941428040d1602c6054014180864a107c044c041414091a00704112801050500781e00000344038503200c42082800c540c42ea4401c0d07a04c24072455800fa0121200f4000b448188100c3c0d4106003e040020306106128000e41010b80042030444030303151480300280d80701e21490010074800c100464507840d04050251481c11160030005611542808010041e82c0e0070925203c0745a05407280408001c8480050b542d002050b1003c00c0200c001820030800c940c4154840d66415500d070000c100e50000010a070754461a0554495000501c000c80550b03e605040c1c02400030b4000d80400054400f92800c1155001042d29040911741c1e04485c20070000380da441840300074100509440f400c03016601c0d1307948650f2031244c428141c1059032108009101d541c00b640c0707000f60301c9400c02c568820f90700820300c0310440c039800841c0d402d100392a00000803d00c2d02c24650030306148 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 949471681 1250 949470431 949470437
    0x3024005030a0b0f060a0b121609050a14040216140d05160b0903090a0e011404060b0304030e060d0f0e10290d060606020604050d21090c26010501080d 66
    0xf94440203001240c5400007003071140c02c0090803500141413407001d0010080740420b14400400d030304040c4e070000814801c4401040802c41d007980240450741c1c13a50100000c503008000c802c0b0b040500c074000305d0003900907000507400c4045107120030400d20070818006003800020400b9510511040c240070345440c098143c641d5605800c08070488002504140d615810051020459007098031180000340315040a40080c0d108640b007400400204a0042c0c10b0702c03800c0c108640620855040200191181c0002080501000304038070014540313441d2a004c85092400c05041400322802e240400c4002e00303240048111144201401141c044045105c1c81c20054100104810b603804410000600b000c0001c0600740d00040d096414400a07140d80b041d500140f800d038000d80743c2d078600380c2001e0341040400d01c500d2081c0400c4c3c3c5900360811507061000c50110782c14110020344150903090800c1640740d03d1b0003c8035807020003440d020040b0500303032081c200c0c034500200070b0105a88809a99803219203807000030001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 949472931 1250 949471681 949471703
    0x4150203030f180f01020c03070605060a03170f1606290a0b07020402120f01031a0c1c021204080405040e0f030415020a050a030f03050a0c0f03024005030a 68
    0x1c1c035000c9645280f409141e904681c0c40d0b41d07502c000f4a089900803005005554000981c041c2046000d0190342c0c3c2c0180e00319401108030f881c603140c20520411124440c0010580014051080c40007441a1138540041e2610300313904c18003034501840100f8042c41e128070b070500f07401e00f0b85002840018108014280c040e140506c000d00d08a410318a54014810890f4080d400780011400c011844907514822005424400007035495811f14903001007481c0c0c218412400048100300c1e080a0190807580745034105800d01c4500181101c06070001c2c055407104c110700410a0062205115200003d401623480440b4104159a080d500b004c0c0d0342c00b018401541240c2062104020000c12003455440708451401a0344400c1c0300c7e99038030f6013400740032541180440c1c001203401e0a880c0c0d1520030706030700424072142086081c50b4844050310150800c0506001c141e00081d02500e4141c40719061b0003058120007000e000136a121703158044071580a6a0070001e034600c44000900c5103000a60a0cd0b41504880d203121 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 949474181 1250 949472931 949472941
    0xc0e01030f141b120102040b0d0203060109061e1404080a03031a030a0c140d020a0b071b0509061026090f010603200a15080405010f05090c2206060504150203030f 71
    0x40071211101c224084c2d55030074030001524024100007000d503000d029000680e6890900d0014002c0c0c1c1203034200c8800c000000d480c003007180500007481c0513596074609201e40c0e801507886200e41a4860f83c1c014103100d000721001035007015010303040144100d590035042e940c48080740303090681c0c4248460028050102d105002c0109814400040e44403013030141c21002c0994031038000c03404202c00c9074046680345000143c100e00740020785080c155030740d04200c0c6918040e03103484006001c0040141c0038a02c80d003100f01c420f80f140b40c059007003074019040d00749600340c410b00b44074046c41c001602203440d032055000b003143d00c0351202010f114000035603504c0301103540703125030148460006141d40b84103a40c00800c405800b0512110910b04400a2801565280d07440d107001c4c03511509440d212040d100b4058101818040340c250003060001203000240c90220b5040c9948840c24428500202c1000c050303443c2c0350303000c6852640700c030041c02a03952281c4c0510745098010000c07a6240700413280810078a2852021070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 949475431 1250 949474181 949474189
    0xa020703060b03010e0d0903050606010e06030408030601020a0c060c030206090601030302030a200102130914070807030f09020405010b030f0912180f031e010e07150503040c0e01030f141b 82
    0x40009203001d400007510300380a01c07505160261b0220843c01140481d030f810800c00c003042240b80e500072401e02e0110721020314000410180e00000d08001c0c01c4e0000440081d00076442040000708181d08241468465642c03550b003e07200480354041580180145800980b118000041d40ca049a5160307005614243c2c1071241258005019035410941c60b88004218126040c240080c00c940c03c11004046e2495150030180d4044480001800e100f40004070b0410990325048001141c7c08190342c280420f8403a03801300301d10300074245100002e5001c0e01d00000800c808221401952140005900221160312182400c0303540d00401200c22604200c2005000441c4c29405012000e00402410f1501e1043c803200000b420310f0a580540000c03418550300102850f034007401070644840c00c21014148482c204001c1505a600110320502803210000c081001c000c0250585030040020048804465031680381c0100880250b180030348503004111181c0d002d8640100300a0030414800401da00c10071000d03c248 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 949476681 1250 949475431 949475441
    0x1003090809041e06092a0207090518150103060c0503280207051903030615022a03030f0c010b0913060c031b0c0c0e0f0a1a040c02031902030a02070306 66
    0x141508495110f078a6922195010328005001d038102c01160701440d1080480248040d16580d1004220102041e40b1440c1c001c030f000c000f5201c0c02c0d071011490b640ea2001001c002d1201c0510030342648036502e41042003142e00d4078194162440f50b6824840083c00c0001110b6500094074801c0c940c0d5089007101d840c0ca03500d09000780d0742a1081c0350141c18440c0c140c4034541480c0c42c66400001084400115104065040c8140e001401e142e400c5540d40c0020031000955030700c20b18400e20200d02071441c8091710001080001803206500a00300d980d00c0700500e40c1040300d6003004e40c00300c40a60070052000040e10300060442e01c104034944a03809400c03000c0d1034040244c0071b030815a600345aa901d1282142c00510300000d44491240c0d1907446040e03019141c5041105081d520042e68407544c003003030001c01c8048942c526041110640007107040f9603100110360480140031640347d405440e02d505683c1042c4c000c80a080401d40c805511001e0070768000b010303604c03446854841c5005811080c001d0000440d0f035404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 949477931 1250 949476681 949476701
    0x302090f041a010e09071d0609090108151e04032024220201140409060603090218150d0c030209041b0b0711090a090b0411100309080904 60
    0x803508405150045800c64034026081010b000000d09800b1031035030860101c00310260300b83c3d0f01058078a0003090043c1200711608541071885503181c550303032640d69110180d1742400002400c41003696901d00f022966010001010140107a88200140c101e020b89681030000072607000b03c89a607917a5655044501403400712000e016001505030490750803404000c41c042e4603030343c0507585150f5200070a03070b54041c1c0c90003072500b1402c52802080382d210840050150018070307070a090150800e020311261404c1070140d9042401294940364002610f1a419000110520300a031141c45103001d4400820710f12a404456408108001c00c10034411804d240403114803031070081d0b6600e15031984030740c00030700d1515040e00c5c190b8240ca6241e2094459180d5004c1080080030200031040c5040c0300c42c0c0d19120725100c03440e02c0300c1c400d40350b000c00039840f501c04e60081c00800c1da028505852034542482c100d04d010090054a07402186011070b9078401318000d11640c01b0743c41d000b65115007480c01c20010070010f0005008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 949479181 1250 949477931 949477939
    0x2120a051f0603060512011b0e03030f18010e0319170d0f020a0809070f05100905090a060e010f1a0f091e18160f14040609052e030209 59
    0x140115000c42840300d070101918250358045426031400003044241c0e0b80ba2824144a64502103898103100340c0e0004406181e2101c0c01c0c403012400300000000e0860080703000001c82d00e85c0c00203050281c2400c2104040d0755040c01d0303c3c1e5440100c96031017032540d101c00b840e80202200c56038000d50340201da88902030f510f5499051844a140c070a4401908040d942c46400c00c80d6010340108043c2e00080c0c1181256520038400001030207410302e40324482000c601107210f642e00504001b8400d960451240c0ca803e8050031002d801090755050a2001d41c0040c00c5030321820401000c00380000c54403c40d110040e0003280c1001e4005403103c00340303040502a83d0300c5031800005041c0c04204420454682c0010002c4d00400000c1e03081c010301c1040107101d00700e0900000341c41d5001d0702c20100a8640b40400d07501c0c414400c0d0307151000c1c104400c50402d5a1540d0b00320b0602c51042c0e000b140014001e0351003400481038030820340340d51208500e15051580c24045c0303003548281a0411002c9045007070302c694050400340300010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 949480431 1250 949479181 949479211
    0x5040b091207121a011e12030e04110a0207081b040f061a04030b010f06080a150e0c0a030b060c0316052104080607020a0b160203120a0203070807020102120a05 70
    0x1d03481980c1c04003e0442112081301d8000c020b02190a10f0040c0750051100f910450710b003c08800e100b20003046240541d90036a0f020100b00801d040c421618907040c8000030300100150640f4074902503041d006908030784010700c10600003003034030140400d080740410600000c500501e600401080301070812001b410070b100d41e9403400042c544162070008044540040080d42e80d442c1103042101e007450050300034510003124a03200300080c036805400c251f804544030301c00050a5010400110100205130310010a03100d002050042031250903005001c65845d5450402070002c212042c4840d6004541d4003429582042c8140d42400010085d4010558032800603600154901400741c011800030072601c50000101040520040000300030f46500300d07500380010002c071441944c9268001d6801013802111601c0e2041c41c1c42c13654001c0040d1b1720800d14050f0f00d8042450000380840082d00704a80c3c0c580060340b043d0101d0a81c50061003210389480440c5c064181940e0f60b0031241c006008017401c0d803d0101021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 949481681 1250 949480431 949480439
    0xe010201110f03070f0504030f0201050c03090916020d030501080a08071a0a06050405090a1104020d021c0207020f0d260705030a030506040501090605031c02010e06071e05040b091207 80
    0x3080051441242e000d074182d44900f0010300007019660854500c100f84002004140046a080c04503210140d50900c0c1c00ea654400b54113545045008078120b50b50000540d4044c800036002c80a00b6000c80c40140c2d0884a000d00b81400c01c5003a200e0a116500140e004a944807012a0b401401400054001c0c0d001103480944d42c5030300882072400300c400c100d500d07a0f154414411494a4002c20f50000c0315030000707280311951a00e9030200c880503034814030b1240d07034000703a00440b03031b41c00e5016a0a0480482c181c4005e004900286102951042c0c800300e103c0c1140000d001254030b8000384144586030047c0b108a00c8007001c10750300d0710b4012281009c840c000000c0c071912000072400c1004040b017007001d580111701030400800340001d41d001030300450302290071300300b00b400b05403000640e0201690792004000341a0002e108164010801003443c42518000e50f0308002e0300a03003284010000781c03102c0f41010100d82c00004200d6a0340228000c080d0482e0042100015610340300c0b030001c0c04800d010060341e5505540f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 949482931 1250 949481681 949481711
    0xe061504031104180f172b0b0411091203030712020c15011e08030c0d03150f03120206011a090906011205011d10124205130b01060e010201 61
    0x20f225401c581410b51400b81008000140d071001080015401006040118400010341c55540d018034681c2202c0500d22114211403a6030807401d07008c10007a0040120103d807540d030110a41c81810154012051170340300741626040003007164492030031580c820030450004002c250196100b056561064840c0e07a181d03001d00004102c80f81e0007400444410301200000503041610a5495800340c10141c00070310005810380c0d004611000e0207412458001411581c0c102e2586840300c4540100e0420408020080200658500300e4503030880716400300c400582c0e81e0401c6100700040415207038047e200600800180741410304516070030000504000f10f014450030b080e082155000d07031140000c480000003141203040d0551007640c201850840900b082d908044000603072400b6600001e085070f003032000c042810782880d803851030703581c00804141900301c4405440302040070b070742e0400c07125981c94800810580414000704150703603580310351514216071034114151a60040c028090313055540f13820780e104025071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 949484181 1250 949482931 949482971
    0xe07020304060c260d140c04260f1609061d0c070f08030109060e010b22080f10050606180918060f16020307031d0604031505010e061504031104 63
    0x1550108079034417156030344a14015604071324090308181c0e040c0020300601c5004038007198107803610412600c52800c039118504003010b0b5801d0040105d0b000741d100c2040b4814002ca140e640c100401003103209005e807105414011200c941c410008200303c12000071500d00c00b41490140d00007035000701203007400c08c507031102c103070310b07640c07141e08031200540000188070910140c1b1075440642a021003210440d81001d201403207510840d00743c0761551074500119142d00c01d902034840043c001c0b9406845640305100e203441d070b0311407252020701e00203801e100004001d410b11000361081c081000b089500c0f140e4404c81441020301c00500408010017140e9060012038200300321030ba01809285200c1c100078544608084000c545d81030940c0c085400800c05800800e60004544260b40a642c400c2d0202c0311401c80056001c0c8566407008181e0350070a6807906d80e40c00b403503100720b0485000010a0f03026540e55030801410105084105401c6002400117002040200300360780c0c2104000380000408010040740b9020b010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 949485431 1250 949484181 949484243
    0x5040c0c050318031002040506030402120a1205120601030c02030702040506131e05131226010305010b0306011a0a030b040e0a050a11030109110f13150801060e07020304060c 76
    0x8020b120f0b0551590408000071001034082100841c01c217420440011542d00c0058030183c82141403c40d064181c5000f44480700b9900e0f808001050300c40b84024001d02203030045181065400c512200149030340d40a8080c803400c5040a6024618200300e03035003080010400038043c40e81154403e01c0d40e24007424548500364669082411405000c01000160b100707481004240025800c6d031100301e41d002451040c1c1650007001d007401c150070565001c0c418003e070031386025208018021828000800e0200640c40450b09080c16804c2e80c070a0381c0c841c0c44881806c00208405c080c5064100034000e521031195000a51200d801000416003002c4d0101e003a05d004901c2000303030f8040d00401c02030402c201840c1542000d9500c29002405415079541b100c04075402100206070080100072580c2100b0380e1400c40d01540b8200c20340040280c443d4805112004002600601c41c03190b203022804200b540000782d04070f200e11640d500941c6860705101041b6582d240f8554212003450480f046400722228907500c1304084 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 949486681 1250 949485431 949485457
    0x606090a2a050d36140a060902010f1e050c03041203030b2e050304030216060801050f1906031104030b0705090a090c1e0512190608061005040c0c0503 66
    0x20300a20070a08003111504000e18080c000c1c140c04900b00b074400020562a1912400d402140302c0703015083c004000e84081c085e10015001d0010f003041007005503400600c8940c000c1e40c5803007404e0507042e429980c2c503017084410940d003100d0b401c9481c00c052095000304100c581c2942070324100391340c60460441590b0165800c502007512084039100b28148091041545440c00310402d20052881451050601c0000000310400c0000400507003410b000300092204134101c0d129048406a540c0f1b0700402c644402e0083c2d621840450190400710301c0c003a59005202241c4045c1c1d07080091800700b00360000c0501010061174850f09200020101b5803034182c1d644914807a481e4180e0794081402000a100e0160704019007040ca800518404240e000c0346080d8012000c8000d446003591001090361140103111885500c0c03032100d41017040090041c802180c0c00710208800348140d40d200c0d1221512008100e54181c0b001ba903c2c2010405864640c20484030700c51a030402c8804034115488550035580300c00a4503a403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 949487931 1250 949486681 949486687
    0x412020c0303212802070c1706010f1203020304120f122f060406150f0609150201060812070c1a07031709100207020310021c0b030606090a2a05 63
    0x1061901107081684556034441500710b00c5844143e0301040d900729440d4902045c0e01080704010062003607094005030011f0315217051035001c4c1c125a0380d60b0341b100340580d4500c1e10f04510001043e6041c0000a1449607041d00650f0400703007002c060b40e481c5070030020b054452541c10031140c40440c03c0a8001c80b020f82036a500c0c3c209480119807101c9481c0001c400140c8105082c00d035480c403c100210b00260802c0e401040400c4840008a1055244495410098492400000c005400360708003500ba03080310b44a000343c1701480c4520006900b22403a038443e900068020901c245910300e00306000701036051041c40b020700c0a076164041d40c08416506120081c0000c1c0000316402031640010180440182512040c40e243c90b00784060b54803403620b03076a004449500414140110342c0d0521032003089203142030045440f407090f40e00c880650f1000074403550200386070030040d52960402060b403602c1004013030301c1e2001580b0b4003030300700b8002d110820404c00010301e0120364403803561882d42800360324084da80d80d541d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 949489181 1250 949487931 949487977
    0xf04110325090510030b010e0a1202090c040e07080c070c0905180d1e05040e0a050105090a0203041109221203060b1c02091906031b0e090412020c0303 66
    0x211502100c60003041c4142510308020f541e90300c03444a40c403a801440e0102c0c280c0d66800051743d80010340190070394400c2d0300380e5000c1400441c10340d103103500d03e008444040c604c0c0c407400340b05046803185005840460800000081d4114002d010580e081140d05525620b4100603444409072840190000003040d5140c1c0103201d00f40500500e01d038101303001400030707098031416105c019048034080301c0c070030301440b12216601d00001d00070400e80340108103004012420346485000b9000500c4240550346c0f0412000000c541032020500c00c1d02d119561020312000c018030303900300300030f40c3c03400081445807240d43c00450a51601d0341c1095074903c0c1841544c0c01c82d00e03e840e815000c1c0980c2d055401456691a0510244103d60f2514000b0300300c4101042d401603444c01c01d100401d03e010940d254000300341403400d20006074560705603c00f0080c080249500448501203560464611498a001c60350108006004c1030102c1c1c81d5094002c3c05806c60f0045030526100080130070b0550b003080001d8165802d0190001e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 949490431 1250 949489181 949489231
    0x40203070b070501020409380d06060e0703111206010e040f020c070303111b090a0905030a020f010f05190e01021b15090d0210111611010e0307140f041103 68
    0x5950340ca1202310284c0b030b01082c03806a00e40510502c0c0d100829081c1000303200071640b0740c1c0e0070f0f151010b50031800500041c1d8031f40b08603400e00c0f40c00350780300320001c1c0c5087c0c0700c50701c14901401910401c0110046110f100d031903183c01181c41584a2480e01d900540e10341184800050601c0140a0040c030100a800018610708020300500b0800b441da40e8590051001e00c42e401d503001041359015042252004140d483d0a80d81000802c0f00c004000c041d888009455405580c0015414140c8187d0000900090704500c0020341500e1066564550f00e030320721080102c0045580e045040d01710f0a5030001404d2280442d4810210074083c4040c240e0390b00000c2000d0385400c1919021070b800b00a0100514801080c1d010003503650707140d0781c03031a65070710340d01c0c40c9007006404980704071404104104a00d007110056401d002e1058480340600601281032180c22003924100460403500f12280400000d425449060a0088208051030305582c05540c03407241d85500181d610145000340c60b0540501c01c402400e0b401a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 949491681 1250 949490431 949490441
    0x506060103060f050405040f08040e2203090e1e1512010e120c070509010303081e0105130902010908010213030c09200d150602030307090909051005040203070b070501020409 76
    0x1a410582042e005010020780140040704541d07050300d00050555940c01c0000308101c0c10358000380f5050001400150820b07035910747c40c3c0100601950724002000a06900500c060941c0300107010581c0182e08009005400c420550320103026001f040010307080d2081c40d04003181c00c4995180620072803203a4041800d003501d12403404288030380200152003004401660310030703401c004081c1100c000101d100c03d16006000b00401440702030134490003035031645400740c407105045030340031800c900c030b2000d0031441036420050b01e04035170001e80f4045410001200c458041e000308082641172161030000001c2202c2c0034801400e5819804111100340c0e0305500c1c19a8800302d540d07102d9450a81480e4101c0700d06502d4a400d1844126120646603131200501520b0010741014940c10b80d4507000c2400c0000c01c80d8020000314070500e504e80e20070205903205e40c120340844d01003442c09485c6611040d904c65054510760f100c01c0d00203000030308540786556502c404c402c680c2c0c41440119066500803800704050410b174024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 949492931 1250 949491681 949491691
    0x80a0506030a12050c010609090c140a080307060504060b06070309051c0803090105041109040b150f0d0f1202071202061305030616030b01080f0f0a110d09021504060503040303360506 80
    0x11301046402b61501c0d008105103000e008004404100c00413869a01d104040008010381030980741c8482990808900034282101d003610705500700030306074480e0b140240460301d6041e4141c54080d0018103140a005803207611141c00e41f52000821018000311305c04802461041201d0400490300b40b03000c1c50210340e442c440c05030303c82c00760b003084062100007004000001e82c007040100400d0310701415800000c40b203940600c1180e400086115042040c0704034042440c00dc54010a50b2031201804400101e0342c0b01101d2103020086066558640010300c0c08800800c03510000d011072064482d04c0d100001c0c00e001c0c05942800c0290074915148012a4241c011402d409600342468a214508400401950320b00108801c0c2c0030305840b4002150701e446a1302c0348981101c0182e0080d219140303400c0f200002c0c070241d50182d105800c1107175880b104050b6481200c042c1c03075490703542300d0440e142c1d950160040c048d0085191500f40c4000030840003030903080f10603800007c107442d00b8000f4640c0d40c00e02034142180545 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 949494181 1250 949492931 949492949
    0x121410080a03120b0103140103060b090105030303070914040b100507030206160c030c0501090602031302090f04050312090f0d1d0301051b07021503010f081c080a0506030a12050c0106 80
    0x2510020980001d4402020f6080d04030128a04d10f228004800902203500044070125482d80040144607140e07005084a040a6403105150f0343c07a07000301a076901040301c031400090f200c260b041c008e00800050019900c08060710120321004410006a0b900900d80d044100090000c00e00d80140760781080080e401604102c60850b5040804000030142c078548200542844041c0300618100b103000d5200e0104c6a800a0f4115240d003070003088810800c3c1c251074264821020070001c030f048442407680c4540150741c8100218600080d0007428000700341e0007818440f050040440c140d490220034800c030408109642e41e13100070491441c3c4516508030500101d80e000fa0f261504028035042521800b002d60f100301880345403510714504c0000c640001c0880e051410f1113011000140c14601e060b80300e0240c410040c10396582d1400c041460030000300d540c03550700005002c540800e140d8503040c0c1c03007e038100708043d040c1e070303441a140c0e250203107005282080403001420001d00404090001c6c812038002d807002c84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 949495431 1250 949494181 949494193
    0x15071103120910081e0a0507021005090312040c030b0114090a050f0601121104080c24040e04060609020c060a0e070f0308030a06050d060209010e0a0506030f040312141008 75
    0xc003c0f4426152864001091107102c401280c0a8060480c6001d1500c401c08419207052400741d15910103000103850510162185400a94035450280076242c07254642c07600031400c00c12121a108601e01010380199800c20f03d011011001c100301106460103001051117115070f903200501817003002c100c01445201d6891405c0b050000514201241940024003441d181c034a5270392160f00000184019401c123941c0e090001000282c000b00881d8140001c00c00300e6003030780c2c09400a40308907502c418050000794000404c11084c40403040c0401865007040c002e00740000d00703030307103601100381241e00c035440409155024800b0031958110900801d03144100c3c91001c0d00c012460050f80745c440681900008010391400310000e4020545544200c00406000303101403510865802c0c240c0003075101443c103600081c8040c291a05e20300700a445281240c82c00792050303246640c2ea0949007100100070f002202007204002c0580c6410b10300f8082c3c0c45c080441d0b024840181d0070480f00324030b154100b0b944040007640160f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 949496681 1250 949495431 949495447
    0x616200d1505150406181b1209030e060f030a0501060f0e061e04030305070c05030610030b1506190e0409050d0f020a0b0403050309010b01020c06090f1507110312 71
    0x41d81c995041c032036803494042807a4840075404103185074200502c40c0c025240000010702e00d06410f00350304460402c54001c01c1301c0e9000c40100a44669004a404003240408410581d80d0590b07a211598a6000c0c0c45c2a11210f1283ca00003280355220240205c14190080184040401140324a0380182020f0902303d00f25000b2103809031041c12060b00d8075100c0c01001c24001c8104400104010b44c910600103441e5a5980300d00e8090726a80040f82c0695076403203201c40108143c03c4c00680540242035452803842c81501d1551a01117460300180740712400a042c4410440648401018019038054004119220580f190005050f090290740040c8540c0c108070380000403039000300d0b0001d40c89040d0300e403204058507a20030a924240e00c1e650028001c4500f10100001d05601c41c01850144d10003000034406d10151000499980c201035103815071142081204e4251850302c1e045da01040d0030040d0250f091140f40000f10402d542100100361007030f05a808010302503140500c60b0900c2c0650702c50a450810105e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 949497931 1250 949496681 949496693
    0x100905060705070809090702150106140d0504030e090a0c03140c03010b070305040e1608011707090b21010c08131e110d0c080601171b0616200d 63
    0x4007070000d00c20320000140d4182840007440494a1101c40034000c40380c5801c110b0402590380c0416440500d4204400c80003040c030512400d51444482d40c00701d030743d50130512720181e202c0081c100036000310144100a641d4050301d4884140003440f617404120b0002e01010034080c064299900b0030504505101c03000c1c1007141910360f03c0290380c1580c044802107500c801a914040d07070184103680103000441c0300081085081060051818603600c1107907030700701241c1d90302c1070f6400c00060182c0c1d0910072600011800d01a10145034465801c04400a110440400300e41ca10400f00d180c0141d4000d6071079464610311907480d90410440f54200074103141c502c801c10740c43d40b01c03100c1c08156400c0807070350b40112038426400c0c400380108201d4241401404a10850a58503009075a601c052250000c20300480c0000a07900030000c50360240c0101080182100564119054001120b224101540f120042c4001840401c00c038402c4a0203d104c3c030b800b5a03801d100a15115130f041080d54540c0e00c103a00e120b20207400211 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 949499181 1250 949497931 949497943
    0x1080a0b0a12020f1809012a111207060e0712150c0c2901170a0b0c04030b010b0408070f0b0f0304060615020a0605100f1215050c0903100905 62
    0x940721000700044881c0d10000b03186514131a22030b64070603424038040b68940581c00460b40150410320081140c5407042ca41003011043c240d45141e14070f6554101d06100324000c0717441c0710b00301c60151b06541c41c1240c8030554501c00c0d0810300b015203080703a0300c1d00b0aa10100f82008040003814100c00302400c5e44c48556550110591001c4040e0613035a00c956030f00e60340d10300814100d050f8a9100009844018420742c010104056110084a650300f985d00000740100032192a080020360715406805505940d440d01300f10960046d00e040609501003000101003132404800501805142120950790392420341d00070728110701c40e000070f6045a64031804001c4c2c0003400003214004008020303801d441e0707030301d60074036500920701079011010005a034601d900c03041d540445c0b0701d170440d8481c484c01c02040e00c071820f15441d82945801501924080414140580701c0d100d01c01d1003410780b2584500303800a40700554001030f14419141024000c201260702e503180d10342404100c21815890608000240f556121203076208 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 949500431 1250 949499181 949499189
    0x603090a02030304090b0f1f0f0e0307060f0f0e01090512030d0c05071a0c04090506010e101e050c070b092b17071a06040608011109010314070e010509010908011a01080a0b0a 76
    0x200000240042c0d801000d0394101280700504cd50005581d445003e8950700600e65104000f80b450002036426a020300d05191b10355a069494155042c1000300384005181000c07058403143c03105000d040401d00c441d00581403000d2071662070a884031030514164809841c0c04034850b203140052401c0040300f8203141c3c1660308171801d502e0045010b482d40700c010b07555500b400a406401045040c2c6000310250408401c01c40300840354900c503074100d00140101c50381e028004070350006422101c803c000800034440901065100213007120315442d000303000e10030744904824100710072a1140c00d840c000d00c420885502c06100410070361a2070002aa81d4195800c45224018111010384ca00802e2054a6035448031010b44030103002001b83c00340d00201b80060760016142030380000d0409030b48080715407415410790f0241c00542c803001703010780e22180150f41c2030700600d00c414100040c0b80340004214a00340600c41143c015180e00a0400c1d00440c00107104290003000044858100080b2840035160489018116 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 949501681 1250 949500431 949500437
    0x5090d020a021c020603040308010f0501021b12011d061509040206090d0c0801110301150e090c070f02060d050702100507090512030c030f0d06080106140603090a02030304090b0f1f 79
    0x2a43c0e48084180d030701002c0001a4020b200407040004050304281010b0580343e0110021f24030301d82d00d000499940c58180380c1d23036070b64078000d001019540c1403110608104c141c0b80c80001c14440b001d00c54007203208132041844015980024140060510501080c80c50b03400281ca00d01c0041c078180e0041171591290459a50007450800182c80500c80404005000317000203900a0125015070343e4440c007150000e001d211052050f0702082e1103001e01030303601c006201001410689076651030303c4001031a40c03c41c1200340e6030801001c0000d8010b0352000e0040145804001d80040c076410102c1000380741001c0075014554003441c0a00b8000050b400803103090449108031000888007000290032401c0d40a00c40160185210100300c0316140c030442006800c0d0392070040c0741001020390301c404003401d0320001e02ca0310484840c0384000300c00b141002c800650340100200126121300340c1c2c0741d001c01d1840d0b00603480300d4207440d50380600340740fa85131100055200d00001c648003239213131301482c8009a104528034414018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 949502931 1250 949501681 949501699
    0x13061b0f0f111005040905160f080a020d0204171b0a09020906071e0308070c0809010c0618051b04060f060c030215010e070807030c080103080c0a06051905090d020a02 73
    0x420031a241c2800d00b5460240c048582103a1200c0080c11a820a00034184103504060000d00351103180100380301035540c0c41c1d465500c000050304040d1802c02d40909074842e4071340c01f0081b6210103074481c0001c0001304000c0d00002000c00d00d481125081120400c074003640c00d03d40801401d000c1d52060310311410b64071500c80c010307510003150000400c00c0c0b0903c41c0c01003258402d1100e003c00c980101411201c414040d485404840e40d682d8021581c0d0540350000501c1403c09201042c906d5115011a00c1e007940320f000b00186101100c0040c005000da80c00341100c3c3d035400130500150802c20040e060112120a8500740103860900031100da41d0b90240c000c040c100214444c00c481410700c01c00c5040755044040300c070b22006503182c4420040d6034104030707101300205d00240c0c007090144d03110303101d1540016142d50303940172a40d00b143d6440030b04e07510040d18104503101d049181008031307106202c0c150282c5075241c0114a03141040c004031003a9800100002581c1d0407080401c000241c012815240b000d60407a017040d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 949504181 1250 949502931 949502933
    0x4120e0102010906050a0905070611060a230f1b09150a05160b06041104031e080c030a020f16081209150403060507081006140714010213061b0f0f 64
    0x80105800c60002d80118242070174400c030a0700f154131600c0498012000da601e41602c903d822f941ca4211501d0760051544107000041d486140d950080c2180521034440516061030a60b1054814406648000d641304400050040001074511409461140b0740c6401e420001c048001440198071001d913202c1944001642048507482a01280c1034040104100750a029850415003212002100d41c103005c0d43c9080b44918503030710802d055900301c95002d040b0f0548810085c14450b10f00417202c8045401c4e40c010301c10400d0806044c805003410052503401044c10f10f164040d807a203010f130264100a02c01e0f1880034240314503900492604901c214020445688a15000c0803404980c190304011a07410741c0840d01104000140d000140100000da540400c2c540324409156042022407290202103060b5410300519040d0200c05030035014011b40f100596100e45820703040c00e91340085503000300280c041d0310621006401440d903240740c420b101017404071000540c2d9060b12403a00450043c2c04030111408482c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 949505431 1250 949504181 949504183
    0x212100518150307030803070801120b01030f11030304060f120e120c10150311120d110a0606082514060c0a060f061a0f03040f0f1703010e060904120e0102 68
    0x101104000340403100181d551b4100342d51242c00070780d40e40000030380042c00042c4030741542050302502908101c100c0026440c55a5038003d0159012007110044600402410780340e500340f01031f200601031612030450a403420803004040c5c00c0f0884401c5003141c90148909200e910004100090900d21171240b90359110a4814030700e020410310000b0485810a00d0140841c0310000c001e07411640721f00c2003e049401030130100561900106401002c1c1c1d0710118107282d045100e00c5480307861142d005c0a641e801302040c2c4644054440c141c010800e01d90102c4403412a101505207080300c416542035220420905060000b04602d650005403845080081039800003020140030340c0000940c8558100800030343c00b07201340702610030792040090840d00300704090020010b2808a07015400c018008604d140c2c1c460340c1c3c1081d80d05401d0b8082e103100502489242c0000c000340d0740e5840311030250000ba500ea42c94240c0b00c990450b00100080e0140d071640081c000065008450f080503039581f410a101110340a070300403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 949506681 1250 949505431 949505461
    0x31906050c04080a0c05040e011b0806010c0606030501052e05011202211b040b07060e011407030504051b0d24021b060a09030519050d0507030212100518 67
    0x80e003003a0140354280d4042100c42c000a0b0100c406c00e41b41408400042c2e106c4500720380802d801004c0000011040c5100c0c0303841b0391030701744c4e000105041400154406031960812100e254008880b140c0d911000d00c000f0301210f00586841c0f0010201e9002ca454a1540752210310b80e240c0718540c10b01c0080001c9080d4072189806a41c01040034000d60220054460403030340052406541c0a81c0b00105a0180224007900600719000d696894065602c1c00429644440080c56100842407480d5a6500c01907803050301ca0740d0300360241546540c00b00741420a0b05001b030400d420214100c850510b01889030a841e00c1c0c115290b4000380e004650304052810251500110050040b896030525100041000310076403d00060041b4071440002c4440c0703503070340e0000a01103619101e8040c1c04958148048005208042c000711480c50040c40c1580c1001210341240c000c0c3c4900743d490030007094010407041040c1e40c2c141c544a034001243d0004044441c0b030100803610580a214029140040b6840010781d400100410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 949507931 1250 949506681 949506689
    0xa06030f0908070b1b182209151104180c020f0f16091503020d0305040305030409050f06010e010f0e0118121b061209030e090103110f031906050c04 65
    0x7150365007207070314124403900c40172605598804e81c5203c01a02c001928170507164103c2d0150f0320450030103005d20030062081d0b8041781c6d9010151001000803040e005900480a1241c4a80303000700c1c000120b6000e0b4070075181811541e056115051200700702d40140e411181c41c7c2c000c42d484c800a660f24041008a0500080c210501c40910900000355500314002070300d852003001403001e028902e40c50340c002c4030548031039801e0207000403000c1c04140090310b40780100c410320501c40c0c18124a4959070f9520a415038002c3e40c40f4540ea59600c804100d052034600308040e900410900e41640c18030301890000e0081c040c031101c0b1000b0405401c0385004240d00840008808680c8400c4070851942d94182082a00c0131960003180c0c148136001e000071041c94184400301c241e44440e101d8110142e40c000341c24004200103401902041900e140003510307510b51140a9010318041c60806d440846000d081c00b0700c0900525045000394800140da00e00c906920004840c3c166000c440426140c55840c00d90140c0d000d0380d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 949509181 1250 949507931 949507943
    0x513120204152d031a0717070216060201021201140604050a03050606030f3009040203100302010e0d030c080a020c031f1802030a170d020a091d01050a06030f09 70
    0x807410007800c402500c0c8a800c0c0365141905080406900c0445036643c4c072008003582c5a20300841000070130103850a41c040503e1921403103002428044000200c400e07122a03015130851903204c40c1c4000b16004041c0908079600081d4548001450140c85401c0e0502c82e8541440300742041000668070030007220020080148481d054a85074180207848800698001d4030910444150300c00945000c00c080d59003e84c0b03130103d42146840404680540d400710051040c0c039000822007920300c1c0e652440030f0340c010099810341c128064258030016264010140074240701e02680050740000030b42c48203115901c958890b000d56215805040700364940b600c0701407165818001c2c60529030300c0601e800704001d0381d01d41005003800914440c503c80c0c0781c842c44030784000e501900081d420401242c0c00c0b0b810280c210645900131841e240c2e0400c1c0903404c0781c005108032000250012010000f040401841800a08140d2110083c9502d0040094a03089084c815041810344421103038a40c010194442026190081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 949510431 1250 949509181 949509221
    0x10f0c051905010e241e07030504051606021005091f090c090c0c261b1507090305071505122e05090702060601051e09100302090306070513120204 64
    0x10040340110301c030518080c0c42807641d0100064030b40401b0500e0700c0c01d40340c0300003100d0816203c408044000e840014416900d500c140c480180c0130701c4080303030010000c10340e583c098100b01c584000004151032001e01030b480e0580c00120b540c1c14140070004800d8110000740c000107081041c500c1c0084011607103504c40002c0c940ba15030b00d8480741d03412010190b4041d102e0800d4880d4040a1841c2d5809001e80ba418401c010300180310450882c14070405c65186406030104440a41283c2c0c10a81c1d8160701c00c60380c020009203914000c00c10407004104400c00350203980c410407041d6500e11001400c9005600583d45d20341d00c0c0201152010542c0400d00c0f420f07101341d805212811b104080704550b8100540303d018040c503040400900403920210305140500c1e41655110702d80101300c076101040c00000240b10072000d0040004008a81c1c2d03031441090342d03009545015031552200381c00c05007880402489201809004c1000079003c0f2b4407884100159441c0d54140245500c09001040050040d95000510881e0301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 949511681 1250 949510431 949510453
    0x1009080f030408070801050c0711060721030b090412051b0a060b09060609090412140304050c1c080304170904021803190c0320130b010f0c051905010e 66
    0x1c402001a205000111000c0c03e07590548282210001c8580741180d02c0181321000000d992000d5107003c03e90018803150819105846001381c3c158420032310b82c00b522440040e03d48080c0c05004030741b0500000c0b6890200f1780b0b81915440064016003410a04014001840e100442c610b50150041c0442d8082103441d481d5103890854014108400842c0c41507983d10000b9a1618004080764990750010f0181082c0344ca407a038803440c080d911001082c0a00c401c41c02c1001140300400c001d984224060001000121441420703c0010320481c400c800c13610160207283d00125076035804030b0b44c0159000141c1e480e440e035421961200c4d80200404d440c4e02c64000a0a006502c0d000e0921080045007242503504c500e0b02c240c4803a0044040506c02040b03505031003030400100300c0d024011500d510304101088007440716940015a51400250401781103903613840e400d6000d59010b18035800c0e20005092640d040382980e103039280e80e448e06007050321502100e5000b5404004003034000044001f00c0d0307400c8409401a03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 949512931 1250 949511681 949511683
    0x21060e0106050706060b180d0501180b010e010b0a1e02070f0909050c0f2d060f130605070c0504090c03060203090c0112020a0f0516021e040c0305060f1009080f 70
    0xb040c0c0c41910001c2c2444d9020880da40008121824819408800794511f68000c042c040011040c0c0e9058800303541e1003483d400e5100451401480c0c107445250b9060456040014030381d51038006030000c80e13203454140300d010030450300010040b11422184818031407080b82040100c0c40c3c10901d03040f0b003e001d400004002584901a002507102c0c0b486841500c54844a4030244012450b6001500d5400300c2c0140c218698901721480c0c034041e130000c01d501c1206604040300400c2e115844048040c1c8032840000b096407110200851140c094002031511030310342802a1075404600481d4051144165502d024207820001c0300c0702490004d59110806540303a152041805131200c110440048c0842c460a280040a501d640301701c0302c42c01516110072002e081200b10854040e00006c03105801b0f2402c1d10304070300243c2d503000300c808600307040805404903210002c801e02055070b14500c1c00c24141420700041c0a1503079100070f10140c0c107110a44840050512801c41200d8550040d0f0011407580030351788482c7c0700385034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 949514181 1250 949512931 949512937
    0x1110f12030406050708071b0311160f090b13020d0e0f0705030c030a08030f09160308071e050d030f021b0d020d050f0a080a020408010f0507091521060e010605 70
    0x10080c54208456640c1441c1503403141003c0343d4090000320048c14180444400712007071b4814030701901d04041b0b282d41401000749000c01d0000f584846c03406140040019400c03840c0382002509140d6810f00460100c0d5002c00d4000420461081c815900407a00104e1018144c1c0102e08000303c3ccc0044032882d034518402591503155a0082e20302074010050901c005003000a158609035502503038603895544d5000148600482c041c0c110781181c00380c1c0130005011020010142c019501440d01d00341d58500c07a1034003502420f23030b501c2003842040d8161b40d8407000c80e0010036401c1b00500345040c0402d8240e0030781341c001300a05c503d02800000c02c0c1c0b0b03440e0414075404009036051401c0c8050f02155400e10748040706840318050300300132824050040140040b113238800c1c1000750f040004d0000150805885122250940d40a0540f150b03259584c0c50800400b6907101d01c1c604001c10b078192441804441c0408000c104a01b0700c030400c4100d1190402002001d14594845402800800c40b9400f05507120302e80201254 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 949515431 1250 949514181 949514183
    0x2030312010519061e0e090a0f0605040506100309080f0d0212010509040c03030e180114010305150312070212030c0a06050901050708070c0c0803040f031e05070501110f120304 77
    0x2040410303d480102c260ba00c40c500949040d41c4500c42034203802c0741c01c0001900c00d5440c1034104044400200d403180c55540325140130310503101c000300b01c1c10b140f2541c1d1001c6401d641d2140d80700d00d040100303100e126140c40400d44003094480c980454180c6103400c100c242c43c441e4100c150300c0c1d9000041e8046210301e460b406040b405210900080182c0d0780c6004001044c4070035900070304040c8500d041040043d000c0d000d48130700c08001601c3e09000c11031309078021071510426884100d0071b00d81da0480d0170142d030b4584902c1d0381c00380c0100c0025150070745207004031fa034503280d1444a002090000442e44c0c19940d600d00039076045140c90381126520340221084d6a22840d0340e001c2102c002e420040403072460401801901d124111680e14140d0580d40e02c04111214014150305803450f004400020600a0045c4000e0018010340032444484030300c3c0d441c00310500030b1844c04203581c20fa400d5107510006500420301c0c9080b244240782511b810100342c0d411a0420f891920001880e1045080e000c421302009000f451080b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 949516681 1250 949515431 949515439
    0x1050d110f130e0c040e1801020a0c0203010c0923030703020607031718030a0509040f0f0b130e0709090309091a130b150a0c0618020909030c0a020609010c020303120105 74
    0x5a5400f80b0b8944083c041d618001c428106000c1406035101941c801c6500c4000319903d210110340c1a480b00d0308aa02903100480014160387c87c000650509001e100b034064070a2030260401c40c0b40044404c200d075881c240107245400d040340b20082d295020080d00c0b0103150000c28141c1d60341e02c0391601800c902003211700390581d0510840050391201e0b0440c0c5054142c2c00780c44c051403400340542070840e07443e40300e151030a61003503032460034003e101c03418415802d02c8018044002846001c0200300040d100c101d455a46056003042d011010803c0040b41034001c0301d4039998041040700040c0740c240c03542c00194002640c00c81c039103100d04528888684000707200d0402619010641c0c010700113200e0a41e502d006c46581c200d0700002d01b4460205026006100c00d1940e8545111070508595402d42902e141e000700c0d41004510406410030b6282200d905600301c00c03540c0045180982140c0c040c0d86501d2454806480b5a0300420f04120a90081e11080d107001d5000b0181c81d0f03100030a01040c000390030207000c0d607402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 949517931 1250 949516681 949516717
    0xb13021e0301361a030f030a120b061204080d06051503131b030c05030606010302160b06180703091a0714090607082a01060303050901050d110f 63
    0xd44460001260705803081c2c011603105500c125945402e9941d0762101c1540c50040721003c203608030000d48140e0000703240c2d40e4100b03c4044071050805107080d810b000c512030103400410001080d1900301c10740004001e80c1c41c40100341c044145000139624025100c0c00020540c13818100410030080c07500415086a40e040100280d80e01c03502800031070b403e204040400c061041011440400d007110034200324920071900682c440602200d05122400558411901c194040c203060000e8541030101d254071130004e10301117080c11034000110038440f50301940584030158a02c04281d1944a00307400d00100004914401c1c0c060a1543c4000c006086010080d1054680e800c01e40d020005820030250142c3d000380d80f07841c2a4007546400781c016034030582026038000b4041007401c000408201c01f50030034036178400380c04d03200c2424030750202080d4810200840c01c81c0d26162007840000c0d00401a42c1d1102e41c00e04c0c055450707040542417440107041c42d18000b0b4000c440410220301c08101d031802400244902c2d001800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 949519181 1250 949517931 949517977
    0xc0a030c080f0403030203181002040306060905090a03050c101d0609060c032415040f0e0123030f07080309040608031c020f0403122a1203020a030b1302 67
    0x201d00600b0b803502c03540309590070042408203100381c000e1354000d1031501900200443c00e1203007d250101140f50030903419004a410800d2005030f100e040010640c03100144007500d090f440c8143c0701c2c00c4001c80281031040102c0c04038005202041450300c078071842d16040040c03841d442d0203010000003040e0189003d100300c0001540410010681c103024528440c041c0c1e0070b644500210061103111140c003294180c20701504014191340d0850300c040c014034a803554554940c2094480004a180e03500080201d00c034030710040003c41c500d10340140d910554101c00804050608000a0a15580c402c4042d1588110070010800031008001002006004c55013000031598402603d601da01501c01e61a104c03038196022588a03018503001040b459085c18200da180036203030364030b1180c075a1080c110a40000d035080c002d103c17004210901d03690511480b281d081c0300c401c526501c03004642c1064004004041d00031441c0786425009400005803800300404074400f00f121074001d50b009400c203a00e480e2151800319a094 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 949520431 1250 949519181 949519187
    0xf0409050907150c020a032306010b12070903030815040e06040311010f180809040615020d02160b0306010c060e0a08030a0506090405060f041704060203130501081504051005090c0a030c 81
    0x12404c99010308540e84907842c0d41c591180410000c288002510083c140302d0505003020b1011300d01a00800101342e072036140e007955403d44003c000307200701c080c012010300c1400030170303000807005602100301d020781201904840080703006803100c100350141921600080c001016045000e1501600880f8001c20449140305001010344950340b0040da035422154554001050708600102448007018201007803c960701c3c81c0c0113805240c101040b00c01078200d02c0f141c0740d45590500812041d06440d0029084013410004420194800645420b0501202105100403c40c084c0c03c000350b072116a900f621070701c003410700702000c681e0b000f107460b58660361074040090000d15020038001e0240b500715005010603030b40e801c500000340c1c4000c0c0040d60f000310041d10b80d620a0a4603001000035000ca81d001e142c88645209140c40d1410a40d0409030503c44c0b203c042282030741c1c5608044034806800c4501203116243c843d10141c402640b03030001a0802c2101003000a02c0b07201400134440d44559603002c10035071110207021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 949521681 1250 949520431 949520447
    0x20c011202160303091b0608010e060102030310150e0306100f0e1b03090102090901270b06030601030207080906040e09073318030c1401030902060d020f040905090715 73
    0x44201900c40c02c10480200344603074491001a88284600082014142809a0681000d501c29000190944018400d03603070407040711600a102800114103505004981d1400717070910340a006c50440c00c1c0300c80c01c0044c1d0310615041c80c0c000030150544e0041e0410503520000a1500d00a038030322103180440c0003a84d002a1b0700464840d561014040306040c1c1c4000c84034003142c1c800b8101d944599003d0011a04a99403c200c5600070140811644042e04562121701c03488014002c405501c2440c0a1000320b003520b400080700e510060034a0010b0f5907a44503d810405d60151000032504100d021502013000c902454086000e98480d9040b1f426465a851440c603440110842050716008a25484619000e104181903c0c2c801c40782002e05141522030002c407041c0c0c015500a0314642e0f6a0241040018142c40308007414180a182c1807001800640104007a8464000031070303007481d4001210701101c0c4000c400d480250510385004e00c1582000700040d0354546440c00340c90005595645241c030640d00031489 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 949522931 1250 949521681 949521697
    0xc3c0403080405190b040b07030305071e1b0512130803180103150506030a090b161b1a0403021005010e0402131d03070f0b070807170a02040f06020c011202 68
    0x1071850a41041c0c240b258180c1d0003801002020b90034a03012507059400d50241014041c0440125240d140c0341c00d000b01551006010041031201021801c2c800030311519100392104003a0400d00061100038140ca86418040000504180100704110030001100401010704000d0130310007102e02512441d42584a01c035002241030031003100b5164104950190704059901c241c1007036240101340d560300201c0d20643c0101c5829050b15600d001074800c2082295001c0d80040c05d0300c0724000e400386540800360001030700e00e08429400402c0002c20302040040c44043d4401d000706914058507062528002c3e544a02d2865080203407420240082104103607030030744512035900200319002440411207054010028480860f81091001e042c0320b001e500100001c004d064882d20f91400b4448035400c0c040c21801c800b42500c401c0140240c28032400c6035024242c80320000c1d8142c121040d5840c1c4c0d0300944000d10a0341d1240d901c0004841c00052215004211008480b04c280c039620b800d5402101d0200807485003541c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 949524181 1250 949522931 949522943
    0xe070203030c0315041b030c0908011104030816210215070804020d03090f1d1b07080c0c03120301080f010b1f09091803090e130b0c3c0403 61
    0x3d485110741000300244c3d5100a40000b802004800c071009035000221b40100109840303a4003403030f085a02501c854010f08441008201001451000030100d20071440050908940132590804800c1001900904980d21266060750f03410b8044034a0405000d800300b4401500906501700896503000c42c23064070070a216542e400042da21a405c21224200081055003040303250500480c0040140001402400340601030244090880c09001c4003564028041e0032000100068035a42c10960b1094440300396000c0502c0e51140d40c00d103601031800a6510a43c1e925128440311044d0b120003600040d811780e00100140d070f00107070690a8180c261203940ca00d00750003030050596034049070030703451003c05200b54619000c0e01c019900c01d060420b40340252840f1480c064010b0301c2400701a0003000c1c10380204001800b01c400da00c0c0c000215280303610391900240100ca81c0c8400103040643d0130f012174000b00c0c0802c113014001d100001e40c0710a403441d0641d41000000203c6480580c401001060380d00b2681c0c400c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 949525431 1250 949524181 949524187
    0x3240418171303080a032310061407060b060c0d080a050115020a030305070306091b09210210141305040513020d080901020102090307060c110a03330608070e070203030c 74
    0x1549a9110383d05c01000e540c10142e03552691412144a05c80d02c240042d012000940e02d800c1c03054012408071302580c090b205000984810742c040c000940145e408040c3c1004000600785071305400302d00188190f003402c60742c41c0034000903610450b03000028240264040390742000b5680c0c0720081e1140555840e0810350160b1301c500003841c0044c4c42500111791000312445d021031559510103180050300d611040340d15440c0c0b417803c1d448030308a40c003c00f0203000f04402c81c60081d90603080000c1d41c0f0b50312160342003c0e00880000e44101c00035802030158611020040030b01c2c682d102516001410525414007d051207607081c075020440d0900200391212196400404500d1320b030300781d42d6440b00799034404102c080c1595001c1c05a801c9940d82407100800a0100e902c030040001140d103404010454840000c901c600000c000078030100c0c0c1e10b03960b10003444610f030050300340803511010744202c0e40e1035003100414002d05040d4003080c064400304101c0c003191407040b4201c00903141d40307100340e890b800f044400100d411014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 949526681 1250 949525431 949525433
    0xb010206060d02120a050c040c09061e0302130b030f06040209031005151203031b190302090a0306050907080c370506030c04080d0905030303240418171303 68
    0x7030b1070081603540b004041d00384d1181001480307414042501e5059440750401246a1645d0505010342c00000000e45402c4002c0c90400101904040058407603100ca4180302d40c80b4040c0c54002d80c1259440204016615009a0f581c01c0d0040240e100f280c0c000c001e000c042e0b0124466050034000c0d603c10001c01030140c032210340c0700c10400c0c0003424000d101d40b00c0c0d0420501d80d04102d07102c1c0c220000340e0204c200080d56403850812031091600b50301c100c83c0a8082d42c01c011004030130010a00c2034055980520f00580c1c6c40c03440030001b0f002840541c0014100c4d510700018001c2030342001481900316007000d42981d41e40c0c4010000c02802d038008041c904002c07101813243c8840c4807040034082c8404c02489444018054541022880603041162448031801c0c0001c0c0c03c5c00350752000c1103410440c102510b8545d400f41c5c201401300f40c40340000342204c41e880301841c0403148900d800022300800c0040c082c00404c80303031410058019040e2102802524030340e11a44003030320182540f000700c40c1d481802e120560f000c1d07491 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 949527931 1250 949526681 949526689
    0x60801090b0a030b09030306012a080c1e0c0123041509090207030810080a0201090e060f031b15070c0311061903270302060610022803120b01020606 65
    0x2001016070341c800b901800200004850f40c102c6401004105d009640301d18005001501a080681d034501c1d070f5108150f010791402040042007604140d2003650b0a44414144070024601208250f0b8003030489170b14011982c14241c0002d0702070b42080c0990380e200081e44c4800304207500110441c40105685e0040206016003018503130184a9840d0a14000090070f50303e07141d035000c03038218200442c00a506032003071002a0b0303080c4c007981c0b01400081c4041c03c0a401d055001030070001642c031954424400c102c00240303d07551980380c031403030510000d41a1400c4401c100f0710052000c40001d00b032481040d00c002042101720300c9a090b500c58540c080e2080c2782030750860304d0f5450751900311960180d00050030040b0b0a4a00c00340e078110840c560040c0c8020a50f444d074000d2081d80c3c0348821143c95001118502030802099000414540140094410344802000f0480403414030300800888240c03002e07040345060b10402211300d1303406098000d55800c10722042038030004c010f5511440007180180c0c00040810503d00d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 949529181 1250 949527931 949527941
    0xa21050f16050a08040f030b0106082815030507030c062a0501020d0906020309010608010b01020c190803040303110d05040302010f030b040b03070b04081204051503070513150f0906080109 82
    0xc0104111402104503031354074001c0381c3c065041107035801d40142c820010040482141d5015041c14200307000585003462004610461000030462a45030b5404640345c0c40c58168401040100d1958404550a8803410840c1e0744a070030b41b00440d00f20745850400156140302c1d051040c4c40140500711054214186100d00202c2603d82000b95115503007040401c0604589101d5a00c0306c030b01c200f602585078640b42041ca0300b140c0d0298088025a41440d100c2340160780c0c0880c0b0690841411254a1400c107805c1c0540411041283c1107a0518400000d000c0280354020074ac5c2040b02000c01d003154503901980d10700301d8440c000e41c0f10003400701e45801c840c0c5e8881c9009401840d91001d000c1d000190540c4240c0000c1d103032400580c00131801440000f0140b068030380a000c44c44088403c5e0783e0442c54246481c0200d40039480503103076042901008030104071060700c19070840341400f0303181e0728041440d0345505940008d50b040c0c103030f080007050b1720307000c0d690300c1c5800303810344000700d40701d42d1204030060b0f00e44130f09a80540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 949530431 1250 949529181 949529183
    0xd0c2c090303041b09020412020f0d02010816170711160513110d1a030705010309050d03091e110126010612020714010510120507061805030a21050f16 66
    0x441e8156000c05d440c6190f1000d88001e20304881c1ca112a54240c0c01400030801c0240c1e016401103403e418001c0140c1d030000b2a20380c02410058454200501064044620504003016230420013000c400384a204e0340d0011444020421603016141c40c4110344c01c0210a81c01244220b9402c1444000815038030002640300c4030036100c00c50081032170894014140b004483d041d154060183c0315903039610280e81420801c18018220a003010400840182c854527658400360341048100740d00d4440d0f03242080315940103802c2a00e0001d0500500600b20702d000581034030300000f00e500244420030800c00c0c140002c1c07001e02d080340f50000003e81590a001c8208e80c1940c103130f001c0000580d0200072030300010300d01c078441381c81101c01030f40001039604110350152510301d243e502140140007200b03043d40100b0b80104100e0100e603000c0c200550a1045204444214845540040d9150040030340072010f120705a210072041040c181c4030000b140702207034019185405030801440c800c10084c01007400c000c01806080c1003017 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 949531681 1250 949530431 949530473
    0x5060924040615232106010c1506210b0f0c0f0406080603060604060807090b0d080a030506030c10020a080d14010b0409060e060913020d0c2c09030304 66
    0x109844200c040032003a00200700b1400180c02c0c2584034040300020b00d40144041c4113091451900d611040c55100e880101c42c000d90494980b9000300b802a8001c0282074002640f100340c18110540103c02c0b40001c2211b072180003011030703001691a40080c1d0300403401407060b5009039001c07100d07201c84440100498000307108002940081221801000445020b1301c02480725070b40d50303042450402c0905041c00e00190809000d20300f021010b000195001c680041659a1031038006080d00c41c0e500003400701496241e021301418030000d00302800580c1600020b22030324041d02200c1e044507010303040c02007910b000b01c041c000507000400c9000006402e400104904040b0f01c1e80403605400c00c804009e081c06c07088c1c0c001c080c2c80c14001010083c014071402031100070212465005034501d45034001c01d00e5220010318409a108410300100119950132000e40c4140b074205c0748081e40b4503181e08000407030862400d00f0308a0715078003040f594102240000780c01e12966924000e94215215551191070442c0002a19000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 949532931 1250 949531681 949531691
    0x21f030f020d0608070512061801020405060703050712080603120d1b08160c1203020c10060b04060912050709050907080f06061509010e0f01020f031204060506092404 73
    0x605003550001e05084140d072040000c0240c0350071085403030031015074000c40c003d49142c84008007002c0081480303a400700006280d5404413900c001058020300c11900241d0b8080c0001c21034405250b0300101a22104e445455441194444403100b520303003c00c04c0318030300e505a10110b8078050594180c80136007200001000d0108584010040c0815a104801d24074400128544108841c058506c203039840481d205040030f4240c03038142d03150918000c544500c0d07242071540000d0038130240380c0100f00f0f40041450071882001080e03110080c2070340700c0c2d01600c14031002844803500490340300700c00f40707503c202154800300900a1030b00d00003009015280050a454150055100004044e0001c2c00080703044101080074103103900c2c14008001240f200c038403041140100c24401c03100c00740d82001d000781142c0e004566006501d44980c0040b850003102c41078500c02800b020941440740380e08581014040da20449050201c0c1d52031100b40303d85904101e0f030a1114459210086200064407a0b600c07a01420242011803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 949534181 1250 949532931 949532951
    0x1c0c090504050a1b141204021507030305060f1002030301030f020d052b0302040302010f1112040e0a201606020906041202040501080f0705060d0b030f1b03010603021f03 74
    0x104031842110840155610b41007000406400400e61400c2010217080c55510030100c0c036607040090140c500390701c19541002022406550341c804405082255000b12203503104840d15004000d030006407040743c0500c02905403180710b498100304049940e16140d0080d42140e1840d1201883c00b030300c1400c242d0308a0551805000400e00501c4141c017065806c4c40c01c4248100e16008000c0032119482032038081520500c02880182e90040c0c405103003124602d820300e00c860080c24940d09298050410444030400040e0024000c440b003c0ca05104541c030403001c00007180014000046050128084020030704c00304034400380000122000c0803403e0146400505155403400883e8407a80140c011f840b0440e441001032085142a01842d4090402000506604081d81ca50542c0c0d9200c60f0064500c81d00000c40c000781d00702010340c4040010b50004088070b4810904809903502c03185140d0001d01984a60796102d0728908050040c103003180c2d405081c243c0b400c254000340d29080e07242d42103030303c04158881e20040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 949535431 1250 949534181 949534189
    0x200f0c12191e0c200315070215130b0414100902030c0406060906050307120501030b01030b1b0405010c0602120f040c140307090209010516080c0706030603020d0204020a09030b0a140a021c0c0905 85
    0x6c03040c2c0080300203450b12820310001c06882d107070300c064030000380039034a1007003103480e0910780044600c19a006003012302640b1645860381244450462614461103036011415699400d13070824140781c1c0c020340660303082201600501003a90168040c0a0114091602c00c22180f4030501c02998421070520307200d948941075030040da003642c40a0780240c8191135114018814024280c00140d0020b060404483c500382c00c244020304a8000c40c0710740c1d810320030100780b590188425501143e0352841d400c8901d00319482c00500050a0750001e45060b214003145401c04200780b1408060325466240050003461454607003004030700690f0203881c5e250304101082c0600031044c2188102c200d003203489440703000e84410601e08407600d46078061b4070410415081490400240c0c0358880c2e0140400d40540d00036940d01e82040054070014415403008228401c03590800643e01c0c034962211b9a186500c00d035a100035100c64114074164080e582d031007600c1c2c10340c2a4034160411000e81c080c00d0728003164188642d103503655000103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 949536681 1250 949535431 949535443
    0x20d0501020424031a131418060606120105060906220602012d0e070806040b070906030b030c1012021804200f0c12191e0c2003 56
    0x764100300e0304074086107880241d40e16803031606000d44c40c04200300802ea0243c03042504c298900d040c00303083c6402d89482c00c5021508030780c03201c44110300d0900017401c0034120340c442c58224180030801c500442c004105a442c04a0841e2402034116084403c141d09110401641d540106400703a400102045a142e00d00d14100800d81ea4000b840d031000d0101e8a455000b03402c0d501d1090802042592600c2c10f02501403c07800000c00d00ea510a000140e520103e6085501d80301d00398104140c1881240304020811040100c01ca00c12402640e030311040569846041d001d65440300802c9038150015000b014050510704065032800c0d041d07240c0400074201208901c0100e901c003402e1441a09810030041c801800c041c01166603200c155000003080c0d05403002042041d0046410503a482d0b20005000c40b80744604000d50f40d01c00074991003456a894101d1010f03050800348412405c04900a032202c03200c549121004401c144001d42c41c2d4021000c465550900040e0200d0380303444160f55503125002c0641c801f0002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 949537931 1250 949536681 949536689
    0x20161e05100c05043b1621061706060402030c0a030504020d0f080423010503070c2d0309170c270106030204090b0108011a0a0306030c08030a02161211180f06010905091012020d05010204 81
    0xb0a2100c0701c100510640ac1040c01449140924010800c0c4400000313881c04560350035226281c00034003030720380d440010004c101503480034044814400da1041441000070041084603240032291310407080818a10070f03000c200280305800300d0002d100081d600c6011b50000d02e01c06108481031308510040c401c5c081c50047d02c446401c031410b041402c2c1881010f0304095000c0207882074044089c1c402072088a115502c01c90a080c45000d00f0300794901204036900400045191200140f079070200350384800004009400074452150243d007400b50f0140154000e550850581d810842030490402c035030310200109510085008080642e02d45002003c43c0340714510101402120015540ea03200602d0001d2520580d4441d02041e4803801e4010099030840010102000382c0c8018484154006100041e180b0001031014a4070350b501e440411043e4003452107a07621420090f00d400034040d4803003043c00712541d0b04541a01da284602e03c000d0041000700a080b11880d0b100420700006149145d41307050998215901c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 949539181 1250 949537931 949537949
    0xf0d0818010203090913080d0c211a2202040e0708090d0f0c150504121b0206040920161e05100c05043b162106 49
    0x298406003211008210501050240b004505080d000d03000200070100c054501000c142c3c02c5095102008049001d85040b02e440034401c00810807000000380440110500d800d5510031481c7c07001000014620490011581400c000101d4010302001d21a4440300f82d0741c2a410450901e40242000581d4001000034144440c0b01d950507091100d001307804601c018041c041c1c1c1e41c110800c50b0030700b00c2d40080d007c8240007041c03520100d45400f6041100c1100c20300b2030586040e50070281044244220040803c24207a950356905a0020903084003858003000598021751042d01040b08101241c0b403900141c0299082030b074140a1484803507501039450f1302540840d5800d0f41aa425503081c49281c41008110f070310110440700760503040b0383d00d0300c0d2600d42c6010075100543c0e41e45910034229204100303960150000b200319018030f003e8110120100c1d0201c0d03a01c0810015503111040d09001e030b8040d600e0140071100c0b034081003002c55034415a508031141c60703c0801c071428140802d548400324002e06008010a00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 949540431 1250 949539181 949539187
    0xc171c1b20030a030503130f0606060507140f0c0f0a1e1502030405130203040f0510023c0a0203070c0f15020f060126070303090513060f090b0f0d08 65
    0x49040d01040004200d03080c465040f0828150202c4c0c5c000080341d6000c503580c1c15050300a846460f00d10501c0d40d52601c081c00f482e18110011070702d60342020003842c0300340c091500c0ca04c41d492078010042c1d4409000d080c450942c1c114100300c00960070544920071442030001e01d030341855515034000107480222040e480300d064103480000c0000c502d00c02c0e0310442c00601da101941ca0b06041030301080d0309100b03290f03004112544c000002028000004506c9400e10342c4201030320741c0ca44000c25804065041803640a10307640004450080d001c4603410910700d0121480003000c0000c1000644208680055001d0025400204044000500380c4040c01e8090000c1c0d504584041c1c0c203016901002c0a0400511025540052407401560300001201d6044501c1e244501907803100103404150f40c110b034070101303803901c0c403031900c1c04001c140d042200c12003510415501c00e14030264100e400c40640701039200700d05101070100018015003074150042c5c0b0b100b01e0082d12182c00e030b0030480086600710805035030031f58103544c003c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 949541681 1250 949540431 949540463
    0xf061803080c24010b07030c020d0204052e05030a0b04212a021503090a14060f0f0f0c0d0209060712021204083003130c171c1b 56
    0x20045003104004600460f45598180302c0001080d115204001c3d061104082000f4110345d203d4407254091903000d8010b02642c14160800c0d00c0c401d40a401321003810103031840d031201d0120800c41020840b480100140440800341c0c4803030748103000143c002d40c0c80100980074140c02840002c001e40300202e4590300c202990000c2d1080c03501203017103982284613140f003946030080540d446800024603042c90000070b0b0b90b03070344664ac0590b1030500da80e07400501c0384420784007201803070b43c0100311030344109210031012880b07070b503044001d01c4c0654045034103821031501c01c0041891502d031403000c2c010b1150040340c01490f0405250010b00a03030010700d4200e80300311720605c01446007a8107002d29401c683c90300c0c21b043d00b000d0074580350f141c44a044c0d41c2d9862803403200b8044600c4c80074429211861110364041081c0e0780303041c50041c0c40c00e00c040341c100a440300c0135690700003c2c41c43d250364000c51500c402840900051006543d64400c0c00340301c0c90055082000c501240c40d03800c00360000d10110346109481c0c3c12113802d24 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 949542931 1250 949541681 949541713
    0x8040303021e1b060c1e0106060f02060f04021813031713020d1502160501061d130201090e0108011d010209060405060f0409020a05090f03070f061803080c 68
    0x28030040c84184500702010644040e00c009003865045031003e0054080e051003101141c158000d0b864856042d2182040802e00783c210580e08106854044000344a115103524080c0d030703111080440403005a1082000610040000080d00e07080f0b4801007550004100000c0e444e400c4050130b80d0385020b5940d4281d010410150400e2001740040840b0505904a00d00100811560196400068014100001444100140020244030326603280c101152581d50010141748001000c0e00216241e43c0f900c0d90100d51090205010806101003401e44030311030741d810b88a8032442c2c3c04003000700c1c1032105d0340e000803d1a018240010f40a0900d040001556801c01e2076061104841e07035400000b02d920401146009441d02d1080f6000c0c0c9405a8071655221788a10b21495648240d9010100183c80401c030941c045a00900500401c202141d40f4042108081c1c02c041d1102c2c9284107245103054400804c100c198080e481c8100e07020011200c480a081d070780e4443e59001c2d40f00f070503c401d05802c200208090405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 949544181 1250 949542931 949542943
    0x91023210f011404020a020c091005010f021b0d0311060f16050906030708070c1406041505060d060507053007050a09060c0204091b030212010c020604081b0a0804030302 74
    0x40500714a0321103500d4000039445142c80c030b0301c01d10b00a41d00000c0d080d2a81707000b0080149040d40c0941005c42c9450070313604031107408515004041c001164118031500a1384000381c0603102420780c21a038040c40401c0d2040080316030481900301e0600122504203d4180c2c818068140b18100390314a4040a281041881c0c441c42194080d42c42030010502100116171100c00070349038014000d061100d180e8032000016501a1940c400041425044100d40302c1184408502940154071480c01107491800c00342c540f4060302c00454080790400d22400c2807501007038403500801d8000c912418801d203440c000303a08503008010140c1c0c180403605401109903c581d501404010360250712440d0250414510b0000100743c180c980c45204200243c3d0400541556255030000c01c100d948004000401600988100d0601103980f0050340711345040848685000818012902c61046980c060304c42a82d8964440c8001e4014101610420304121407440c3c000400700b0011510502030908651598a1031074028030f054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 949545431 1250 949544181 949544191
    0x10063c170601020a08091207120c1e0b09131d0f0c0d03050d0b06040b030a0509010501170c01120b040212040b07050a1d12100c0e03010209102321 64
    0x141c0015141c40c086030b82030040da15400030848907c40d40c00c003c02c1d00607160000e1500180041c038103940354601000200c2c0c5210702100c0c1480703c0403000c00c2d1003000b142c03005a154407403440001000c0106240614080e001c0c1e4003046850080040c1c0c802d8081038801c46503489150901040e0700c128640705942030200461180d0100c216940c8c01c016000307580c000c12502441c01e00000c4e01e0785403040c05141c7c1c0d503000240c40c00740c82c01c0b00380c84dd103928041202801070003080e10318546552078040045a10030b158502134040740c100328000d2030b060385d40500440c0c1d41c142d401401c01c50b10b642e4074280342d10341e503c500080090000031103a40455040c1814441101c801c0608400d052010420a005807180c22600b026091042c0c080d2400c008500c005c04a05660240192407140b800b0b0080c0c030810489070b944c42140d210040d503448405040c1c986040c9405c074425120700540c010070340e9a0003540548144c1c007500c180c900c2c0b40805440303110b45650607c604d8100800d0790042c6141800c00300030000d1454100d582c46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 949546681 1250 949545431 949545433
    0x703141803010b0409030e091b07060204060f0e010f050c0309030a0803010e150f0f0111070e09070801022a0703050a05070501082202010e0f150a020610063c17060102 73
    0x5e80c00da5401502c1f410781030011500035124400002c5000c441d240804010110a02e0407654990a03898860000d50003400303484041030840c405061105c2c402c400f0005045010707140c08100700d4440d001070b42d46030801d1548602c2440200000002501d041c0b1881515610803100e003520395060001c500144d80c401058810342c419a0032404100f0360324880d0640c0640c400340d0b44082c09101180040311044a040600051792041c1c4500040003840c1800c036611580c40b020a4490312a2111031003802e030b100b451240151051640e01d0000c411001d8150b0b2503910080344c0c05c03102126640e070f6401d0305195003d0420340341c03600103038010481c40d600134200f194040700a500440c044902a005251054810680031b070401070103c8141e000d51702d420781c0f4400704039002018040c148481c112080f12503800f10f020380d0014002d08001c035a1000030403a650041c1c0b10103417030707840303003900110004207a54101c7d40b41c404440242400d0345450200141e40400c0c41c868607941c070300b010003020082c2d00200e18003511072411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 949547931 1250 949546681 949546691
    0x303040606270917030f152e02150f06010f0e0108150406050604091d0703030207150c0602030a0b180c1611100f0905040b060706020703141803010b04 66
    0x2c40a40b02074425280000a4070005204200b402e090151541c441d1100034408400000c1c0500e074589140310300c1c03060300304020026219050300f0500402e4030b64480d001304101c5291402c1d1114980a1540740071720502c4d403040380d2040001d170341403a440003c00e0b10a40002c01c46d60040c002956441032020401c04c4460400920681095000800c500401810612140400400d04070950f89035040b240c01001d00602258031036440f079003580e0007450070460346070012460244111060901048480440c2d4150f000340010303503d048149a41c8099040c441010800c1a05103038001641510146000745c402141c001448600c1d08288000c161411000c40c15029100e0308000170040c5135000c0343d2858140c0c40c1c0d09241c040203458517441440941c9102588140b02c020a42c0315540c0c441c610400c801e04a598198516613108240022900200000358000b5020428900800ca0070b0b0000c00030a446441c04490510402210074901d403c00c08250701a009202003409161500740610054200103d804000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 949549181 1250 949547931 949547969
    0x2180d261b0a0c0b0c070308130e130210050d0f140916081c12020d0b090a090201050405060c1009050c01030e031213020a08010f2c06270f0303040606 66
    0x240c804501c2c804c0044004000900300d40c8640c00303000d401e00641d44900842d0301c60303030b11142e0003602c444140955000c41c3c4207500000c2042e1000101c00012075000381003c0b86108d01100106c90aa010140e180501038a440640202d180c241c85041c03503a4034810712181c07107400c01d41125805e10301a1901c03000300e0100690148204500414545002525154484902d00c1c81400c1030701c1080d80c3c00c0e07441c0303d0944003007141c000130407561700a00d4170b820040b40e095102d0350311000c03024101e82124001900040b4103010500c4a41016002081c01c01d25070403c40e119800403005400a03515a24404c507501e400404000d070ba0307560503000c0e0640c0300e055100030b9400e1110034000d10303841401c010714210780200e0399100c29095448101107a0040e025480080c09401d01c3d0000b1100901110541c0400c0c0f01210f00c04001e11403040052584c01842c0e907000b4080c0f946941d4070b2803050442c00712400225400651100804d003e00b00441c0b0b64880781714019544920f400d08004080740c01d12b0b40600452a60043e0040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 949550431 1250 949549181 949549193
    0x10b03060703051e0a050106020606010215150d021309050f0703030e15040e010b030114010801031211010e01181b0308030a09050c040e03090405060402180d261b0a 72
    0x40c1d8403060302d240009042e95082e2402e9800b480074560100c90503800c10500050a5980d0002c80c180e500c2d9400b10303644d1740c841d0001240c1d9075594140c816001c0d825003002c100030020800882d0102940100790303603601e01c00ca80024803103032039201c1a03810440e6241d030030300b040180600c1098ae5040d82140901429072940d10058221a00715040611518410701440025940361080d10007070000c2d5030540c2070540c1c4440c0c001000b43d000f03024034480d04031010094185984190b444d40e050300ea0048980c6000360801c0c106a4460720f0b110944000740d500c41007100c2c01c07d0340c2403141c0702810401f0302401c0d07184511820880b038210345998030803001044403c0180040390310101100e80060400000091909080c1407040c14101d0380550035902908040605803801e00c00009406605811641013110f510390104010880c4601c04110300022885000042203247c0007541384103e501503140402c591181c80e0b185100c05001c82d03d21080c80c1004204041040e4080301c0b8851190806c40044c90301c2451a1155 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 949551681 1250 949550431 949550443
    0x306050109050a0b0d020c070f061403071b0c050622050405010608070f03140c030103061a030601091a0405010915270c020f0d1214192d0903030608010b03 68
    0x1400640e0340055100700c061100d504545d60031090030b052314500b035107030030308084951420f210300000541012074840d00280c070b900c2261300403010b5499091110f8003c2c551046172a0a50909907013060072902c1c005146e4950400400620840c611070305001c490550f0003690744142c6422040c0158070700001404035980000714541c005c0301c1801c00c0b5071341c200300c01400c401401000e40d2031500a2200c20511403809010070140d4141c0b0b104030401e004000c4a0310307046108003684644140c0c950300980041010340a80e0384819080034200803214444144c0c00b010505540007a4031880c0c01d10384d14003c801d10341c2c44048450b400303080074141c04200b02c19100e4904000b9080145000040ea6450b0503441d1814003c01c150b0000340b0409003030b1402008840d03000b07492116103610300d0342041d080c0000380556040d0141061701c500d54960350407900300e1986a01c100101222140800100007540d40c3d0141c0694244a54040042d4802e01040c1003003145402800d4034500c0d44008603e030304000c400b400c0342e500842c030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 949552931 1250 949551681 949551689
    0x105010f140d02360108090109030c020f06130e04051207030225030f0f0b06031612030912050106360f110705061806091e0c060d05070306050109050a 66
    0x8003584401120a1115001d00c00d5000054240c01c00700101d0f0130043c014001d001141001d80304c1c020982c2c0d03031950340340c280c441446004000078007040c8140014034200e141c0a001c5035015200608005c5260090700c0036405940102400b011827a040000304941000210004000f1403071807401c01082d9940659646401e0486102e00180a408500c074030000c805520000c5401c501e60074000350441c1003000300c150100e07e0075a542011480003c2d600e007000109000307880c1c034066a17400341916003025142590f0302c1600c22020001005000a070000c880c05000e60903d00480c0002486480c01c0c1940f10010010355814107110307090301501d066203a00807205105942030000104900c00000b00c644001e140c1443c119840c8003000c66000284000007810f144947c000303551040300350b2072101c4c015968460450318030b005540002024564546130381980002c0806070001c454009060800040c0f40c0d800c06901c45202c80d0b070341c1b01081200c0b58036000301001048207081c50042241410003140403040140a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 949554181 1250 949552931 949552957
    0x70c060804020f0a091d01051e06041515091a0301210b070504051c020d021017011d160e01110c060d05010e15060421050706080105010f14 61
    0x4006400e64070303851001c41d25804000c4c40300e0042c9844040485c010b140720340031000b0340810f00d41c9144e44850305200700d82c01400c41e44004600e112100c005003020810080120360400d88074070151455081c242224009000c50b00b20347c0038004a0118002c11001075980f0488206101c0310346103082c18030982c1140d06484d4003034440c0b641d0554080140e00821b8543c00300400c8000c0f4030080090142c0e109001c0d10590304226428000a403121000c02c803011040c100c0030398810ba600764981e00614082444030500f200508010b24940351840c851142e50a09900141c50008402d986039100007a0f004040d902c090302d140b0105000c030f01500010440002c101250b4140718068682d100648010001c103519107030000c1c1311555030120784403400003428083c40303030102000034400070444944c00707244220078040c0054125418245030014a40300218101180d444a108490302070012460602c2004040c0c0324a0b00c1da145154584030004000307085006c41da104100f110103100000e68aa00300319000508284 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 949555431 1250 949554181 949554197
    0x1020d08150616050f0f123103081611090405100c120908040801050108030301060e0d080c0114040209160c121107080a06060e011511010f09050106080c0303070c06 72
    0x2001001124103201c02134150b110740d4100300404d4100262071614a8884400d880541d02d181c0c482c20140d000d44d00c194942d042a00d000401d0030400806183c04202c2480380e6072076002d40c1e0340c407078101903800950200c00401c0900c2d058014802000800f407001603040d40ca0620174542900e5030380d05c904a1179400c011050700c0744241940d051064100c4503811108840c10400c82c09140b0b003401840c0e0241c4588415075080c10000075003200c0203c1580d040b1101760311400c1a4058000c10801c03140280a000c0703a03120014004015845000d10441a0001440c0d0301c02c00c560520f0f0041200340c2d01c00809400c0f4089440f201700701c40d80c0e0b1100e0b6900c441c50b8408050f0030403d00620040d01d1000b05c04095420900c2040300004e18503400260744020940105010420745880d6200314003204001d0042e08650100502160201c40c8580c080c500300400d030100000c3d076042c00b0600c0005551042d901074905a444200a120303e82007804a20042d29045008502d0a1841e9403080c8080645100b480c061000b45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 949556681 1250 949555431 949555447
    0xb04020406080f03030a061a0406050a02031603030b030c060301050d0f06061706010f0f0501052203061104050a0905060108010302010f12020706060e0a11030606130b030c040501020d081506 83
    0xe600664040c06081003030300c0a03000c104011950b250400c840210100341002000500900c3d0144100c11108885040c0f81c942410480f0a035582d0744603d45410451100f0400414480c1c9034030162030001c2c0c07007664003051104001c8105840d20410070483c0b440b5603010001005691b1381e28540c078020700e5102d04205900302940c20000001c0c5065030012846010000381002e03a40c0f070210b0075506030b42ca008180303070440d80c440300f5000c640401d5002c0c1c43d0229500b00841640c01643c044141e0380706410040d0205082e881f0b682d01d00c140c40c0854201d82007200c012806000d649004607804000e004089020000c51510100003400e081c01888080c0c14042051500c0703c1240c413594001c558001a020159650301451601000501d0f0520500c001a15183c2c0840c000210703e0003917020064403100c1c1c3c0346c2540c503000c2c10050b00e64405001c1d80a00c44076600002041110030001e10710490100104948443c81c00002a00b0100b064007104c08202d000c1c01040901005a0661618070000f9100c9903110121 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 949557931 1250 949556681 949556689
    0x50105090d050109080c0d02070f0b07020105070602091302090a050105030c04090e0319020a03080f06012c0d061a120a080a0e0405090a12110c0d0203010b180601030b1008040b0402 79
    0x4000c07000d402c1c4000040e0800c1c0365000001c0003400440d440e030271203107110b5949610302641c155500624080300410007528001d9031181c0301601c102d900038030700145440304400024a801c04000842d84500303030007088008403490541c12110081100382801132030752614410300c41c3c02c0d126074028612815a02e10b2190f00f031440c10405c1e80c0102a0350f900007510007103081400b0f55110b0410504170f000803e20800500e107180b030448503901800c0180c541d0301c02c0b2503c50250542d440b8515142079400141d908504245035580051074402c18003540b400125050462401c0c1001612183c00d01e0180303905090707269041000045051a00350060800d580324000c1c02e4084580086640711141e00030300304024441d4440e00404c070549150712a4000c440070481d8094183e40000c08107840351219001840d03404060300307145104161580c4028000985800080c0000700d1030307000c0c040b81d003200403840010888156014841c2d195030003000c98420307c2000040c880240138040c0180024001003025012030f00b1034407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 949559181 1250 949557931 949557941
    0x150e1314030d02030109050a090f0b04030e100c17040b1c18060b010909050c22080102040b04090e070e04110114160b1e012c012c01050105090d0501 65
    0x3441003640c1ea01c2c0344985207800a50003c0c000c076003245107000f010400c1100d01c0c1c455440b001d07074400314100145500e0f482d454266070000b8010b40c280f102c0c1c41d036482900e50b00c8000c10145822251244000840a820115802a81d02d4000e0b9181c0c00208028001e05c0040300c1a01c4508a00313113201e8401c01030f40401400680130b002c1d28a52603110403240d8200300321003504035104020017a070326031b0210ba640d9800f00055400c165110082103c1c2000140c1c2030344241c600300020000c007200b507031280507a0740b070b48642280e00c03550002c84070105c0031a05010f920024001c82051501540040c80c10505290980221410150004081600903004994a070b40a80740030405591195442620713074941d10b10004003203407005021549100d00c0b81c00039000d079448910070300c141c980d000030f0000c1e2030313081a0008418441c0704840d039070304403840300c008801d80d0685005103001e04003103804003850240b008040c6440022181700805500207901c010710290740d010041d02c425100460b82d10b0100011400d0050041c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 949560431 1250 949559181 949559213
    0x7050c070306090228120f02060a03022a030f03061c060608010b041107060506030a1407150c0302060a02030c07050303091612050c060f09180604150e13 67
    0x8003603620008240002a030100038154001d07114051980076142c14400440a00b02030b090712404400340600881580412113a0070350f1041058581d06001ca4000a00641141d10380303000003500010180c281c409601c4902d1a0f0349202041340e0f542e5484c41513041e840380980c2c942141c04860200014416a072010804030226208101207002420142003c81c0900380d58015045107608040104c001420180701d02c9480c04001c1101d28201081070782c62501a00001d89260381c50b104109021010409402000f880041c00070700815441d4030300011064600c460681c4607040c00f40d050480e00100340c001c20080d50049410b840140d42e903840c000a00c0b024081c40c0009842c42c8008410481803440006810981034043c8600b08140c503503408500c41603400001000b0032a030400107074020241003601c09081d40d000c541c0c0049080000f4070000c50f13407400f06426000b1000741c00806000e000d040900c102855062100c00d84d044403814054520308a48000c2c0800107191100c15503c400d21400c12a0b01c8070b90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 949561681 1250 949560431 949560433
    0x1051906050a0e0a1e0603060503121602030a1b030308071409091b0406030b0a0b0c0a0809010507240f0c0c110d060507050d0b030303040309060c05010e07121112070e07050c 76
    0x941d00c208480c000072041743c003e4030301291403c24046003602d00060042004141d009080b0303d00310794180042e40325801e0f818203c0c0c140c441c14003614001070540800c9000884c0b05080f48120a1460400600c280740c007820000c244a4180709500300015188203e03900042c0c26504c40d942616100e12500c4603070021901050034500c003150109807154590007012842c28101c51010041c0c1d144c64030049140b044420303500320f0303038031050415000955440240c4004841418464200856070f1284c0003003040c140d9074030840200c42c0c10461000c0859200b641c10102240b10100303c0b9144919014011f40c0303071583d000d480d54100b10582c503100da8034280500301d03183e4008018441c5050044c009441500030750303131407207190341000c40c000d6045c1000005d4038451609995080d12092400100365825480c0d2002955a5501c410312040310700e80400c081402000090743e10509800c542c02e2009000d800c040d915031155407540803503c05104001080010394980f06001b805985a9110550311485030080304006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 949562931 1250 949561681 949561709
    0x12071b0e0a0203270313140d120e1807080f090c1c0f0506070f2d0302130305030301051c0507050114040e0106080f0c0a0807050a090b070b01051906050a0e0a 69
    0x5001000c00602020203036007100880d815150510800c1e0241c031f4980f03282e0090040d1600c0300c003084c4503240300a40c40400c1e040c4110594071410200d0420381110300328103081040c44041c0321556500118140d802840c1c0c4204d011079040c5079031190b40303564020890310b100754071070342052010140c0d44c01070449980e40990342101c440e49514006442c1d100032250740020036564104540320a00426403400c0c0045031000210000144500d44291035007041030030030030141d092001980881050103801c0103140620010750f225071400c0200240207554030005022020803401c0303c400588009044003e4031001d0030043e8100b071051206003800d01595012100c441200b800002d0496004081070b4059000010201c00f039640e554543c01881c8170784200c6600103490400002c120340c0c42000602400021071610050455440c0001e05654010003002d031040d10b070f004010410380c900655a0311849a10740c81c420402c51a144000e08903020702c00e83c80003802210003018005985004210020f000e54410b0030761 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 949564181 1250 949562931 949563001
    0xc3e0a231903030e010216060309080706050a0501091521030c0203030d02250308040f050f010608031b0606090a02070602071205090a230411040812071b0e0a0203 71
    0x2031119414401030b000300344d4030400e5542c41c4d4800f203000d40d02c0034941c5840c006241c0c50142c0c101d0080c90b16440561310010144603050000340c050081764010321000c10042500d5040070410070843e4402032510180c80c11000c000c000c100e4000001d118441c84000c0481c1007001c40e41425124002c1c110700095043c000002c241141c01070642c06450000301200f45e40c0313214070b0703201c50341c0744100c2400d02c01601240548000030000ba107400d02c00b01c01d0a1107041a81c20100f2140303001405c3d43c4803504003a526810100c1c170240320b102080d110414488401000304807034201000400e407100006042040c4447d0000303920310500490341c04030741e54140d008800c1281d09031395081c02003d980160101e0b61080414030030020f0420301c03c04003400024207421601d074110514404202c02002d11034445902e9110601002840d503a00380003000ea405842c0c9042c2c2d0703940d4032501c0c10400c6032615113800c420310701400005000300c011043c00f0703d40c841010480140c0c0d940324452107442c424540c4040038000c03000818045d0f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 949565431 1250 949564181 949564219
    0xf0f3e0301020702042a050412060f0b0603010807030506060612220b0f150d0b0a0e0a06050705040501020706050c0304060f0216061d040504050a120c3e0a23 69
    0x3c1011584916804c6c6000c5a0900c05ca5141c1304500c14514081d40d10107803440801d60340c0d400400244000c0000042c44591700c00401c41c0c640090780b119106401100040041c44405c2c000c050780002d08480711807a000e81300342402c18114024104880d000512101d890024000181a103812504121044400d140c1000300f07d0800c401100c1d8204032114258078085641403209811604642c041a152500d42d5103001c0c100c0284990750241c000c3d88501c244000c0460800d204140c0280744541e00d0799903ea09080000e072030721540d54401c00402208010700c0c0c1c951030000c82a141541c0c024500407006103030800d4120b140010064115202c4442e03210b00041c50b5070030804036800212451220380c007000300c3d04100300c21140100c1d005009904000c00341c0001451018a101451200d418040400003c40e21849046c11134603003e034081644072880c1400290703584288000344c80407602500111580007002c508503882ca44107100c080d44220680c001203111711514007408810180012514095a01000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 949566681 1250 949565431 949565471
    0x161b080a110c0d02010302090d1a010905100812090a030501020d1d010917030604140103060507030f0921050f22050402040501080c070f0f0f3e030102070204 69
    0x444081188090680c407024000304000d011034000038202042c0b00c001e0b400550203588210300700d980c010001500341000603969070070000c111510002d40540b80d81014400350403140090719500f00818207041c1005005800256406003000160080703441d80f276280080b4404502e036800007400e9500128010b40804c43d0b640c04401c0d10100302241500044440b0700180c2240c482150240a1006156024201000c8180110b070010b001034400146000341400700300041000707802c226035043c4c0300c8050040c91035150080d5085030181c0f00301000012143d0792040141c01c00320aa00d80c000845000001d012801031054505c408900e240c00c07030390b928a648050410b6a608d030a107041d075101404011500b41890720030349050740d8042e111010107485012941d00190043c200c122034040c68035a90000240c44110705040e10b83c480ea00c0f500c100206445c0c10078522245030304d000c0742e0315005000440c80d121155840050b2001c00b8802c1e5600d41c1e0218007081c0640320f034182c041d410501380300f81080d032a1410390710 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 949567931 1250 949566681 949566697
    0x3f08160606031b1e05041d010c17100509060405070c05010c020a0c090506010822021011010b0904030f2015041205070c03080f09210123161b08 63
    0x1100341e02d04d8071028101e40418034000c189110f132807440070901035828507500401c1e45c9408160503117071025407205110309407807187c8015000600c0ba58242c1c2608200d078594203400c00403016442020783c1c240f9011600b0319078020a0303c0d200e1900c940204441c1c0e4040d413180c40c0c00c590050001d01c4403180c2843c01a65036410341c80c0807190100181c80000d55280c403803003540d0040f172059641208a0320344000d034611003000c80d8120100b900f0600003880050752070901c030504100698940c0a0214083c00c4150b0071100a0b400301800740c101401003000003a48600320705000180c604019201c800b4003900440f6415003417190039420300c1004086444030100402d058070840c82a03076515001040480f08845500400000a08082002c1c209000049013000501940001004c0c01d03802c006031100060302103500c05101032045458040d1105251a0a0140c0f1242c1401c05403888040b6003a40c59a2140740001020a418804c042034500c0c1d0151248101e01d00341c1f01c0960704032008039007505120400b5030010070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 949569181 1250 949567931 949567973
    0x28030c05010e010203190507171620091f0905090303091c0c171c090507060323060f130c0314010602060f1f3f0816060603 54
    0x45002c115601c00411942c601000c1804080c1214038000180d03910f07000f207a0b00b10f0326410169903c200d48000c05020b00000640c1d141c120602d11024103000c80840c001c10000d080010090803104480d483e07481900303812401c01750103254545010b0010b081480c05d1a0425103180d803c082c144081180000061801141d210007a07401c0101e46401300b103215601e0002440124010656442c00b03d00210500d0520f040d0182d102490858502c04120245000c4803590310065911035030101804400c10200001d46601d080400c056540020f1840180078010303550807601a00c20000350098030b0f41c0c601d004c0d045a001e404241e0b040100c0382140094001020500002450000703400000695005070714101d03001ea0300a4403240e26440c2007a44034840003005c00c10f9204480076180c008892009500b0010600000c0c692644c10304d107401780780035949800c3c0f076a0702c203080c44003924041d000c44150007a1103584000b035160b640401d4564103e508a80c07a102030712484c6428400800e012400c080285500301c0c02c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 949570431 1250 949569181 949569197
    0x60305040c080102040f0902030601090f0803120a061a07020301180308090c01030b0f09040201021501060f1101060f0e040c0e1e060d200609040f0b12030a050928030c0501 75
    0x482c9080b030060b0710a5980303582c0b07011000c001081c034560041d90440810315155030f0103615810b0f04600300203540c1c82005580d000040d00740b00d07499009802030f000941400d0501c15140b4054520903143d0000c1d1800c1e0901800050120465509610030502e0000311040052108a0342c10054111041103c034810b9902030b403103982d83d82358800e1227004240d00001f4651205040013030140300c02e05100510803415032096009c002e409400001001c0e000b000b0655a0307076001c14100d800100000225116800e1030381c18000c06001503104a0b0051040c0c4a50004484096860703003040311070352132141d201480c40d000c0366090000c89551400d083d0b048154022007000d4940764202800300c41403007084058846e084610b02404040382c003189003110710400500007030034a0065800541241c0000840000c0035965150141390f1341444409541181c0200d40a14149a0803841c05440740c0301e8a80303105e00c66581d00641d40c2d1664400913040d07600210401c003107180d090301c1e07280c007000700d103014050240422003079 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 949571681 1250 949570431 949570439
    0xf01140c1c08190516080a090c27060302030307020909100c03060504110702011e0e040539040308032203020a060501090207050709020f0c1b0f091e0a15060305040c 72
    0x3d80030701d0740600a4140d081e000c045a0580c1220850130141c40000c50a031100711b031201060001c14094044d21502c40c001348183c0ca100400d6902030111350f941032460f82030110400141e603005c400c0d1148581c0580e0030a01c142e680c007502d181081c0c150803903010103901e0134140d09852a03159101509942e01500e0400030344c4c2e20600b4056160060010080c00150728400d030b2a040c00242d01d007500c2d140900c0c20040c284074242d4001030190303401201c0700d4a40c01940341d94083e0300c40858240805141c07a9000a11226942c81d900f08a148903038080034003d41400000700f03c504080031401c001c1010201c0b000d40c001d02051030001c2d11002400425981203050900105920400d44200d034803580d4403100802d00c131071424188a020750850740e0903c82c1d01d07400740b000c661400c406020f45d0344240c43c1c0d07074452148201210300b08a0040e000d107000d0b6000b00807910422000491450170305558144404090310300396030b00f0301008094a03c2006a1040301601200045c1142e010340040340110f2190084903400f0b511 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 949572931 1250 949571681 949571731
    0x10c030605090a0911041d010b01030504030503041202070e01030b150a0503030a03180b0f010e090c06030a050603070302030f03040e01080f0c100509100504080c0f01140c1c08 77
    0x514001d6a0384481030101044007998207a205500c2d05200d060319035440c40d82c1030002021140113129880c001c5000c03c03044221200203208203c40940242010003203400c0c161401841c600009000a1131004070301c14040d0300a00802c030721001001764100318002981c4078500361030003020980724800140c0e8820790810383c40c6400c41d402c105407100940110700b08907402c50203c0207021041800243d2100058000d004104040c0300944030b960581c1e40240103500d13141d40704001311380003040b1010b5030f005280342041e5662210300f22504144180d801090944610b40043e05060950307200950610910640030814080403000c1c004844420200030712503170380c4040c03c948681018085c0881c5030000000548240781c043d642c0b800550551515900344403041010480e244d40b007040003804507501140810007014100840740c1d6405040c0c4400c3c103014401c030b0010f0209452081010186080442c20020307d0a00704080080190700407002e0600c4c0c080a02c0141081c0c105075082d81c4c44001150307418844401c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 949574181 1250 949572931 949572941
    0x1121b0608060112021b15010807050f04050c0c0d02160e010f06081b04061701050609090a1802130b1002070e0c0d061206050a0612170a0e03060f0603010c03 69
    0xc16500c8080c26640d49000444003030003403c1d614800c056080c000c0b03007510050700c850050503905402c000c00455460307c01240007208164445141613000400900042e140c40101c2e00120704182d6010800d81c0705c1103a0380e01140a5206a149548541040030b030040c5c0d40017980c000c04101c00450b0403a00d544449080984010034081d20341030b84807540d0b00b0440305200b02252648402c0c140d404580303150241c3d103046105e4ac4558403c500081100b00c0a0b0801c0c100603110720300405040741c09a2900004d4008a800900c0090030b00d20641d81d02d030024490b400e0301d51b49554039164001c052039a003810180c5440000d00125503500d002d028101740a1061a00004610b4141c441460801103150b9640350038410640c0a810107480390358860b000000c0141402c5001c1c070741c1c14450000800c0d60325114282d1021620160b001c881c2d04000c25447c54007061168800382c0081c03428802c465600c4600c10404c0c5c40c000c0480c4003843e090b20620341007102d440c000003142d41c041c8108030028448008040001c80c00d0f10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 949575431 1250 949574181 949574189
    0x506010320071403041e050103050411010c0602130b120604020f1215040504031d03160605090619050406080f060f01050304020d0c060c022706010c0f050601121b 71
    0x6105114072140040d8010050201e0364812024003a00c1c203840707054207085030030644c0050303885010801a80503040d1000c4042e0080c02e000c4c42c00b040249025203c0100c103901a54000741804480382c0980c0a01042c0d0701240c1844440f110b0024686a4034100e03404184d201307e0304d6102072441800071030000c2c0f80c507000319661104c1c0d03443c00780c0c101541088584429070016144c43d41100c902c0003070700341503261b50107264032450090701ca45541d0b200078800116100310340110607200341c202d5032000101991244c6100140d401503e0883d807284c000c100403c96030700c02c00500100d110500c481040800380e10900800c26114141c0d0307200f41c41e48030104400d1003408143d41840c1d0064244020108a51040014580c490b0004252030b41c240c14a0f210000c585100c0c0c1c000400203003008445078254140b40c04103041440402405048084c001e901c1000d2104001c0c00480c10450300300324070b00c1884000349100604d0b40d04a001c1d68055651122000c1c1640c1003064126180c44031408030201c0d880240348008110703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 949576681 1250 949575431 949575461
    0xb07060f050f010522050a0e0c01020c0102030a03111303050d3e16081e0a08091002030708030703020a09080f0705041806110a171b090105040806100905060103 70
    0xa64240020041060110440c1c000550f0517401910b500300258051a4011820880d000420540058589050030319400d04070b410740d40801071580169a0000c00c03195862014940003440400701e4210130064450321071102442000000d012088c040049950441511584c403490084100c03104040101d80c1800c8081e40c80b0501010742002440505840c0d145c03606e048015142d04550409103026004c017a45c00c40d0107181c0c4004224220101064003290308100040010103540f0010350795110f41388240d034100b5005481030801c480d900e500170016a40540c2e40300b65084d480c2d14001c40010001d40000c0355010005003440c0002600e900081a814211701940703015010160800040c00f000e0001d0400f59082c0101c2c1e410b414000c01c04130303c40e00c88014130303002401e82d6490703c01c0001050a280d5004040c3c02c2c81400c0d081c0300003c23048583c41920340c2a4619040d403980b20031001682d20b030040794080121030050404120307036402c110910705c090780c05250341001152580c500440031900f5000c00e4900f2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 949577931 1250 949576681 949576711
    0x20c21190f1e021801080c030c0d17070b01081c091d07050c0d0e1f020d08040f230d050f120a022812090209070f14040b07060f05 57
    0x200d440d81d41118102c1d11040c2100200010740e038089095800e070b68040004850090300180f01c0603005001c0d1244000085008000c0b68900e400022100341c94181c0052034418507403a6504500d41c0304013903510306a00520342440c9517039195940794603044010803840c40380c1c004031110701409000b0404a829a0300070741e151003000402074190303e2064009005c2000b40a014001009610410028450560520382e108441d42c1c11440912610031400490081c0042c80901019001076000030b25040300030302807401210301d0301c3c1d90401a180c03c104d0341024003100c0d545010200600c000040200c854821141141d0600403846000c4880d40038118219003a01c404000040d0b1484800f40500d8020100c40c40051410516101d44210400001c600c0200c82058508180510b40c0080d61510740c0c041602041c403a00c11654000344c21800b0080280060241d103402d001c01151213840c40007620480c28140e19a0f5a46402d49110715800c100000c64082d030510b074015038108500d000341405030780f034401c0c3c0100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 949579181 1250 949577931 949577933
    0xa050606130303081302131e02030c0a1d0d11010e090f13060212010303090f0909050703032a0b09160f0627180e03070201170601020c21190f 62
    0x304801301070030051417a5111000d07000960b4503981c01a600d0002c0e01d4000803142084017101d144801c101c0300c6500001c3c4140208140388600c00d04503a000ba0003458550700c5411400071250940300c014400580100b80d14001c0d0082003050210000c462100340c031004521034100b0104205410119120018000000d0200e0140550199080800d40c400c0d4000f5081500111028030070b04000d80c8140d002800d8280100104c100c110345d04d401030700200d013051103400b02a84480b40d0b11030072480300608009050321355000081c90b0440754034100c4808815007901071803034200342050306415642c000c043d0041045081d601d424800e01d0000f243d0181061401e8a0300d071000c29a0343e4000030504007020540106410101d41c168182e10f070250044c540402d50785c2d550b404030601180c070740c110140c42942c820000030b40547e03000305015a41c07031135581c0c031174145a58080040342801041c1e11590b80044105190303002140c107540280021700d298130211a002540440750301b03822010008058a15418020701d84 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 949580431 1250 949579181 949579187
    0x11090d030e010903020d120e030307081c020735210714040b070302010f020306010c14010b0d050307060c09120303150f081b09010b180d06020705060a050606130303 72
    0x21540d00c070505001e80c20039a6034000c103030078820001c0c00312405500510000446508108240e51910050340114105281503907010a94840e1000500c3c01402a00350521005104d0701107070031048c0d00003001d1080328903580303001107501006805801c440c83c4041e19207040d0307180101038501d001c0700d9400411454a62a60001c42140c0140c612030800c8840c0011030841031041c030081000b0701140c07040300d0f2ba80005003002400c50f01c000501c0d040090041051060a030b81c00200c1460702c9800c08880d0b06e00c02000c0c190180101851081a40c0003203002610400b40100407024000b0180114402d1018502c44a803c641d12101030060402c0345e10140c0d0100007091090380500750450f40f074410940c04e9904c40d10317041c2040221398448032081d48403007414460103a00d4081042080c0b1b090b211407517254102411580b45010781c0e010992042c0ca415a4820642e032081280c414498006000710350b01c0d407250a0803616440d088819008075800d0501007207103814600202c1d103c1d00e000a014110311404d5981c11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 949581681 1250 949580431 949580447
    0x307051906030b1201091412030403050301260d0306030201031802090408071e140d030b0609041e051f0614030403052802070927030e0a090501030b0a11090d03 70
    0x265130030044426018040b00070900c508016540034003010000062110001480c0510300824114034400034024003000a410100b92410740e100c0020204819141d02480302c85031b0f0010080d1076452044400c2c0710b082c5a010750144c03042c2c03030003030341c051040400d241070300c1000245c4010029044000700d800100401e8800c405800d9a511407501e10154501615400e2040300d401c1409070360f82c0841202480801d50100300490780e800d12428244480e0b504e040003c0c6150049560040c051510b81c0c10705201d02801a0b104607483c6400b440030006410b083d0000b205000d071592030b161030303003a03640d01c00b051840c01980804441112031029602e1070765955411610342d000410009480c40000000000d004030350000025080141d6009212041c039010311001036800401515803644014070700180101d02d0010b110800c540c05040c461fa480501c1d40200340803002a6101800c0349282000100070004106007450180000d51018042c41e442050300c3c0c102445007a0b03c150f84030b110360749146c2c0000c0c010160 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 949582931 1250 949581681 949581701
    0x301090b151206040606090b03060609011403010f020301090c090b120103080702040b0d050a2003070b1308160f14010527030a030503040b0705070f06020d0b0d11030705190603 77
    0x10441c9811080b90000346000c20070b81301140d0300c9488410510080050b4803601051000c00c5004100070308085002c5076080d0010f00611030369049182d10150306840c250481c07410301d0440c1c9001c42da20340e0340f40c40030801404d07142d100740d0000b00c0c1c4100000d0841ca00e4004c4d00d4250001c002c000ca07040e441c550b50002158004a03007241c1003030300e900c010880b50750782c04014816070b40108080d115244091500d020861a00920b200c045240d1420345003154034009000700a80741000c2c2042e681e00401e00e281504a4035940c40205a4824a850b40c112400c0140e0980e00715003034150a45107103a203910002507560340c4043c07603d00050302400f1540e200600c60004800103000d030b505039801c10710703501e0109040541215003a07000c00c0e00001400100101001c2055103d103040c603025003071040d0340e61009411112940b0180c0411740225200404a03032981c015400c2c010002c1c03940040c6c842600e8180d160707184050016100c0d0007000c40c00901400c001c0040044850040c130000310041c00c21205400034a10809 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 949584181 1250 949582931 949582939
    0x27071203120c030c17160809010902040603050d020714150a0c080a030e12030c1606061212020d2d12060308120a0e07230a0b0c0c0301090b15 62
    0x4800704040440d104240d04100c5964020607650421400502540318400860318080395070f13400c2000661407840012102001442e282c0c0d101e484190b000d80c0540305513030740658481c3c6041c40c008100100000d04003807262440c1c082d64143d0385d980b49501000300c00b0490b40c41d00f0a5030b01101c03022805800c030081c102e24029083c00f400221807a1202e120940049036540d0100c2d41d00e810003c011325040107000039400c2503090561071841c191b862280907006039148028080003c020001c00c0140b1034110402905231090f6884084e001800e00c090305182d4165404054080c01400110f25480307850325500e094100741705900c20308080c046100c181e1103807661b010104280300d0b03607203420129203010300740003940a90701840e22400c0380c4e002c0d01400403000c0e000307031138280c500000c0c4074440802103060411200d41c0000c400d00800c110740612072111480c603030954880112140400c4e07000190001d0143c0c500c1943c21200e88403040400d25088994907000035100c102c0325000500e00c054282c10300780340c5910240c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 949585431 1250 949584181 949584197
    0x6110a0e09150f0d3306090213060c080f160210080f01051e030f01020c0c01090e06090a0b0d0b0108010e0a080f030612102306180705090a0e27071203 66
    0x31920192204e10403545c01140c8249841c040e006000b20700500d00a06205c1c0c4046140030014000c4010642c0341f80b00b020305204e940900c40d018080b0000c01d4681000c222841c0c1942c6080d800c0030705601102c0300c001244074401802400044030711400d07100b80300b6086c1c9440080329900380000c1140644170000d13815408200002c041c04180c0301400070458a40c071100000d80c4540c0c96540150801a40204150403c02c1c120400c202d003403840d81c0041e41008040c2c80c110016291100b40501a01e045402c094015050f50041010000c040180b03904844c147c40003045054141c094031500c0700308504002c0d2401c0c10510410075110302c0c8000850304440c00400d5a000051280c809600700000041c114414950358000c45d0944070046010008041885019507075500e0507100244007500f03000c0c01000c02d0400800000c000318024012141203010003081c01544554ad4282030710351107401c85920841440c1c0603041c1424200520342c04c8410f40c880c0b40600482818102c8080801c0c40c0000260104031942c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 949586681 1250 949585431 949585463
    0x3150b0310060b0705011406011e091a03180705130e0c150d0606140d0c0306170d02150708040f170a080106020c01020c1c06110a0e09150f0d 62
    0x40c2c4240c0340104a491140b40d210512420100d0840300b42c1b950801d40c5407880300c2041540c1ea4070913443c00003541001c0318002c00050340401140c441c000c0350026251210042010103a1011a202851155180441d000003000d051802c2d5900c410329413060715000314801641148034640d98111640c0240400200c440c44500c0f940052030105000802044080c1c000070811175550300c5024000c098040c50408100d0b5007a0795640d030500f44a9461030300001640e52092039a801e03ca0f0308401d0007050201d590b0154541000100c40d10350180400f03013805480b9910150030043e00c81c0d20118882e0140c2d4489000c695a40c0d160045000780283d01122030790140038205400031911400390103042d14503a1254207960519401910f400c0c41200000e0556004450714602951010712503401e00380c3c004480c01c80b008903407400c00090000301c5042142401701040c9400303c0341e4800354400c5110303011202c7c08081d4940c030551312100981500c641c1d8001065200000781c0341413122003e1b0742544138040c5010340c4040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 949587931 1250 949586681 949586713
    0x7050d110315030d11120307030b03011a0112050f15031c1e080402030a060209040204090e0606031e1507052a160b18060403020a090b090c0403150b03 66
    0x48588002c1d07104200048540d0303007003c0091041059031400c00e22980a1080c21031a550003902c103d18102c0030300000041c01380c5100b41c1003000103c0003e002030000d091043d2101e0401d41e418072100d40016504440c3c00c0002500f0b02600e806070401c50075010040c0c4491060202c0300140c01d0107960180711718100300481040417483c0302042c000b140c0c0d803a4088604004200601301c000d41c80d038000c10144000b4800075a902007040310382650f11044c010b070b561151802140190140341e2040791440e06c0c0040c500e00156001c102d8911922003101903600b0006407075820610012480480c3d5403590008070070841042d02c00e0300341a0045040d08089061600000500145940422200b42030441c9600d500807060000c2103034840d04402000c3d020481c6080248414543c081c6101403003203a0300b11081c030384c22512000106d030050741e00074280d080c0c001c6c1c0b600c105201600c0c201c08601e0107101060001900850701c1d80554055903808901c0c901e02cbc1c43c0340416040607148090145506000c2c0d0311100380b140030b03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 949589181 1250 949587931 949587937
    0x60506040603140c03061e030c1008040507090915020d1814010b01051603140903121209070605070308101e0905090d08010605030a24140d0b07050d11 66
    0x1072190340119410100e0310ba03481c1c00c0d0700098031841c43c0329800d00a2045950307a80100960803007607551040c015425081c006440c03c404004000d40040d40b08650101d41355115076400d208901400032207008641e2000d80c0d504489450700040c102c1400d800d40fa4500c40550b4000302000e15030080c000c0f03030508940840140481030b00d48203c0b0440c94864175940c5e405001c0c0110900040c00342005424850039400715440e0000801c07009041000701c041a4490702c540c8000d6504000015044503030300180720038210b0899110307810301605400c4207800035401d003000250030001d442d89035403660b040683c03603502602c2c03011000d0100b40000d010103502280e1200c05806403015020f401482c8862985480f0030781c1c040300c50240c10418590420603028207899003149840741120308a00c0c2c095620744da04035030a802409222a41d107552020051284039429807580c1500a0310281e04010013051900020800c440c041c1040082205d49a41c0c00101c2e4030340142c0151006c035880d9400480e40c040220f00403001d0354 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 949590431 1250 949589181 949589189
    0x30a08042f180c04050d05030d02160c1a19050c0a0b0712020f0a0c050a080304060903080603060f0f0c09060409091103060405190227061f09031506050604 68
    0x18000d40420300d0a490111802c0040e142181d54070340c100e0910f814058440d00c01d6016590013211030614890401504100301c80f09409141002c54840c4500150641c050120540640d083c01d982030000c43d0032071040701460804481740400318034040101d103e40181d40c40b500c0c21003041c81418495042010800d02594482d00d115021504031850445806480600b0205860303010601c1400080211154401240c203400d4441c00c000f1281141c1e494211718006103414010700c143c101100b48001c014141c1c10803071020740b02e51244080f558620040c90754807001150b980c042041d041c1c02048001d002c0303d6405130840c10120b01a4a052180c1c404941140d0007603000c4c5600d10303646c2e0085000d015000741d03481c41210b02140501400d08250304c400c3e03554258030000c000103c90302e20b03d00e41159610784502c0c80c0000b0750010905011140b41c103920b0114001c40d55940500d0301120145009a0700004450290010741c0300c00040c0b070b00710f45564803c5285501380000c0c441d03540a01003502d90319140500028 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 949591681 1250 949590431 949590503
    0xa0f081905040e07360e2a0f13030b0f180303060409020609030706200309030d0807030f061706220803040206130f230609061c110904050612030a0804 66
    0x3030f510f0b00c039204006210007407908043c1b03848082c4205e0f0002c19071a05640c08452404410b172149646230122041d48a0b400fa6445020a003010000400c50804003440c49240021124502c65650301c0381402070108802c1681e0701034100700001581e9141c1503000443c42400600b926090040003c0464a0810240c100e0300c0841c95040c1c8034801c1034a90842802070001030030185080007125004295100350090003007040c070401da000542414443da11000240310f00803424408199544454500c00c2c581685840e4140240d0002a04541d101d4001022081c1ca80d100c683d8100c01940780c0c0d03e419000604100e074030800c1001641c00350508410407401604a40f1204500c0d5450b1035407056001c1c1400a6103500000714800e050110b9503120169400c094040d00c20a503101e85000f800b0241000c0e41e610125003034500805800710701552005040b44c0072027a6010015515902c0401088081000715404aa070003004881c80091141c0b14103a001486180c40b05252403455405d0500380c50422081c480c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 949592931 1250 949591681 949591787
    0x70e100905010807080312070210020f03040b1f17030c070305070807081218040b0409050606180f061207090c05031608070c060e0a0f081905040e07 65
    0x1400c21403103998010000c6100616505140503003031500e038025124050140300218002030321300c2e8020320400c0f03002d65103600215941c032041848072485800946080d225189200006840e07107500d481840700704104540d05140c414585060101022098030048003d230109000a6020311010003541010718030420240408905001c505403410499034031140d0309500c442c0001c03d03051214030854090950003c01c0c98100034542c4040340103030156520b0650800c0c82d1024a805010b0041070040c0640e404030748442a0341c107880544117000e102515011002000840031907a01d103450340c04540103100540030b0300c04a13582ea60a001c2200d81d0220001c0c0070620000400050106d00b00f035030204000740e824040c445c0d06020000400c510a082c20040c1010303038903080c1d250b50b50303020031100c414507900c00910300c4041c52500d8681030382d800c00c0c045021511241d203d16030b2424000c03800c0e030b0150f40e0703034400046c0d03e5640c144049600104551a0310040c02401252090b0b00502814480043c6803c0e006416 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 949594181 1250 949592931 949592939
    0xa08070504051b0a08040f02030f1501080c0109290d09051e061f090e0c0f031f05060f040203150109051005300106020d09050409020918070e10 63
    0x420340c0e9000b0300f840060b80c85030441240400c45401501c49102c0749280450b015038861521100f03448910b00065818461340c0201a00281d0003d2814030740c801b031030358030805666a6140c1e150359800850355035000c0350500724188aa540d0941c1c2e010704060300780d20f000c4030441002c42c0300d00060780066001c0b9903454541c940c1d0000d2010420428007016201300a0300d089080b544800380d100c00c0050005000400c06105420609804294250107407000000400100409040d0565581020020b4074080c0150285401c560b21380030507060b400c800b802e042c10140ca940310b241140100001805180e100b01c90400100640d101c030f1028510880c201e0f56200d0758240d80c000098013503141540010b00c150707861410381000c4c6a109041d1003901680c0174444950f40c00903800b140707c100707031044424a071521710400040c01d02e90009400039000f4554071a41441a1242d081c081a07038004140a50010900000b0601c08502e1402c01111403100200b924096501e600309007030580c900361900d800d03c15200c00184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 949595431 1250 949594181 949594189
    0x90b0a030f03171018020d0905100605010e1e0d0804030503032e210309080109030f14040806061e09240d050c06070309080609010606120b011e020109020a080705 71
    0x41d130000c804048a001151503e00e9881404050942145a2503000b02e4040100c0c055504680001d40d072103001d0311040d040041d40e00000b8041e138030130030740001e40803081c8140505007200085120f03154905180311300302d200000c0c00300b840107640e81100c9002003000300001054092002d18059548881c1400804d0110741100c0210010000c6441c91000071460800040d02340c0c5c018444854618910f80400c04e00c141070980d44444030f503028440365400d00307a01400301540040400c00180035621581d40d504864030f00701100c2e02490094015a6008001095817403403c0c1d461902d00318030301c0d41c070320015074000f00104965080a03140c1440001c0c5071603480b4a032401858109440920542d0715522545e82902ca96544204d865006030040c1000a250300c240742c411124a40681003c01c219405401c00c950118024100c0340b04c4c02c0002044050001c0340300b074641c0105181000d05a450f00302c010f4480f20b4a81d5482e01d0015801d05540d0b803002641c0051700c81c100280000d04100c00606242882e0034144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 949596681 1250 949595431 949595477
    0x5010506190e010e030102070c08010c023c0f0c100e030c09040f0f1b050d0f03140405150726030c03070207051324050604090b0a030f03 60
    0x29510900041c080c11039502852a407468264005107011041e819072100142c03284072000c0c01090b0154000642c0380284462000003c0c100c403907a8008002c4141c000380304a07220580c540c00f0700c2802230300e00f1411000441103c09002201d01070110b04840020642070385280654007240c07000e69810466200c00c2c0ca18213411040d110003405e0401c82c1000102900080c0c5800c942c901440c8201400004281401003260403114103580c030400c0007140b10340c50b0406050002a10201000f000e201d03404c013281b00d041c008036121880b0751180210a4000540e5401d5580002558542d9a1100140400116940d0b51510700c00340710104036400c3c0c0d0380e94030f50402e030f40700f0882c06030001c805400e821300403075048102d4011258450809074249450b0b031201c4004a0030101141c0c40254041e0303a01180069003855940402d44850600d2001c86003d4960100e40e62a2150340c4200ea600c00c40a00c4100500c0d07030182c02100c21050b00814640c5100e40380c2e5a41106103405100c141c0000340c3c024850180c600c40e1150b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 949597931 1250 949596681 949596689
    0x5040213110901210c09030b090703030f1b0501051f08010e21070203070609091401150c0303180305040e0a0e07050105090607170c100e060f0720060a0501 68
    0x4144881880704404003400e20034024164104034110244050400040c2e03108404902c844409115140c0580b50051001207180000e940c0d00c50360801113445d030760000444100320781e41516180300c446030608040d11411014080503001c0d81046074000c3c0010020301c5001c0c82902d6000041c16684440ae0249614681e03c1d0003441d0300b03a02d81030054101042c00560031183c17070122995855105050101070780c09000d01800250584240781002c154240c00c080c1c0708003900ca44410070001e01c60000b20f044000c8100780308103901d0a07050803060340360310710a80c420030015000707040200313400000340c111880d900700001098000038000300d01440f801d07000300011600165540000d002c25854500016201e49007032050074144032000800103903c0c0c0b83d0f5016141c00c00d800081d10220704945540c9100726a1101030000c10502844130300c000050f4907071080d5001c40054100910055807081c00e403618898016140b1b000b80158800c05e00000b201c030004159145d45044040c10060400000070000d407141030304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 949599181 1250 949597931 949597969
    0xa0c0911071a09030f030106080105040c170705030c070c03050f06060d0c0521060405070f0617010905100302030a050c031501080303191805010b0907030204030515040204021903050402 81
    0x1201d0118600c0c0244440e03034044002440c8803602d540f1070031807452144441e2501e001d1408400040e826800c00c031581d04035042601e040c8000342038008200d6410505214000800d145240070a40992040028650109180d0b0096281c0a070341d8030341004140040c0e108036495800a088025003a0050184940141081d61098a1401c0c280d4a0340564646401480d0003040340c103180001c0310000e0007007108451290b2040d0b0f032040c10300e070800d0307516100140900340d801c0f62400c00008900344a041030b826400c091025040c02c507402c0819007005008040e21110320840c0035200130000d40d506000c040300e1103201c0d000400c9100c000c0c00c141030401200c400380544020b0400300404c4881c002200712a40030ba10981d401811403030401440d801484041000300116052030780c50b20400c6015488910f00392000c417008942c6680d0090120140e10907800020b020380c00100e2503c010301051306403030390094030040000d82400c1c85102c91088000c1005c0720704000036114010700095090038101c2c92400c0c80410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 949600431 1250 949599181 949599187
    0xa0503160b030709030b07080a1a010504060c020415060c050105070c080904050414060a061a1602060c19111f08060114070c0f060917060103080315030a0c0911 70
    0x903203a940011414800c48104140c00000251054030411410001c1d40e44014024000d003801c3c8401021800e084940b10700c1c039890204240c0c1c070842d0310f4403826441e103016503a49140c5170425004985036181000102e030859151003481d00c0448088200398081c141c0c0b6a00c081d80a12107040483c04c2d5640074100000380040c0210800220b040307081110011310059401207081d45642c605a50b01d04020226541c0c640910002d1000703032410358000a04546041907031411a040c003152250491180000441c116680003c5078001818204c0161404041c02000d07500301e0001e01e1402048404c0d403980c119504100c0205a210324940229001e00310041040301e183d020300c0826014040602c0a040d41341441500d0042085241c103007004c5480d0154003c0b002d80901d40c1e202540f280518039400740c900880d80840c4049080149002d0038040310304000300928060f427842d1a9030100740e101030b00c0b03050072409070945461716440402900c07400b1485103e09a011900d00b0711941e0032900c4494134074421075010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 949601681 1250 949600431 949600453
    0x6030c02070b090d0b090309040c02150a0e120708090406060305040f170f070602030109050705031003082802060a050a0e03070b070314070306030213020f1605071802090a0503 77
    0x4554040d181c0d103a001c83d5607002402c002985400c60035a004000c2e5445c03100b006501c8a0110161070250000c1d80c3c2400101900300c001c0e078845025044003003102031804000f400035100b030382014600124000c2580c074050700307400e04070055500c0f00006880400e070001e03c071000c605062090070020055031604000700c2c20309655100c01c1981c041805045640544c01c8140d103440e10008036007a41446006072592900340f864020069002403250800a514100008403014040d004480c400e9454040308101c3c581565a03000040d0051b281200c07c41d0360100c4900c810380f503900c9482c01003c100350020459480c15030180c10503240000e0040303840d581081c0003095021400003c4d108000c1d4003442c08a034959440c0f400b1001417103003011407103c0712089018852415010307030002041e01e0027941c03403417984110021200140c0c4542508083c01c50001c000d1481003c07131100f01c24181902c0f0340c042e90440c0e90785510f1803160181d65101c5c0741002d6400114011203141c48010a0001c04040d0098500c00e000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 949602931 1250 949601681 949601683
    0x13030c06050307081e13020a120c03050c1008131a0405160501390b040b07110c090a09320c0a08070e0705070b0421090f060f09030602030f04020a06030c02 68
    0x2c0030340b80c2c05071b180c0841c59080031541c902c1451005405a44054042145242080407115105120942d401e0007503c4501c103e5090229075510901640e031100c61190b152644401240b40340400141c0310f080e04850800050344460110a0040b4000c0000703090700c200c1003100544e50240c0754049814031408071484912110802d403000098440204a40000786d01c40c44100c9400060f150001c1082041c0c004220405c002d4070b124134010260f0b0703550700349041800f04407941d89040240c1c903039500983c90310005409581640040d81c10038070410003c420313864002802500c0c402c814042008100103401c0c2d1415405042007007101d0460300711000400c0514111505444500d03a00400c1c030300c1e4407494001401d05d8019001c0340c0c1042d603c9440c0c220315191506002d10154003a41081003040822000b030300030341d0300ca054490269403000d91689452403070654103541890300711078200c007404000000040498490300c081c61281c4004025110980761910400485d00c1203900301d50306261a04400405041d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 949604181 1250 949602931 949602991
    0x30b09010603020f130801142805150d0309060e090c0406030b0102071a09181005040c261501020f060c030a1d07050108060607020108040813030c0605030708 69
    0x400c5040059a0700c01d10613000c94035114003002442c1c0c1c1c0389080030004d046141507000d69608441020039400d0340d2640140400541d401e030311160761440c5180d0040f820403001e0784c80143c20150305403c1c8244903c003000400d0b00b0301d2160100350302103500f55104004030354100100981107602255003145514050b907010100c0c1c003460044000701a5510b0a80210303074000c01800c0c0183c42c00041d0031204400380000410154000398a030350242c0e20b007018040140d40c480c12050f01401c0c41d2003056220034140b0301440000c0045038850310130403180c1c0c030b01c1103840c501040340548410700081400009241c503031204081104d0306641c150465104180b4190b00c01d101184294118014031040c0b0380d2a100d00c0e0242002d80019090308071160160310000c1c40040b400140c2d1001c448003038131000259a03032003003000410f00070b04002a02055414002400044000009041c2020040c150403810b82c0c482e1205091000c040e08254042400001400040e80d08855031903803003001c6840998007540000e402c510a06 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 949605431 1250 949604181 949604189
    0xb07051f0905030f1c0204061710170606030c0315070804030e1e0103050a110d11040b0c03250f0f0f0b0a0f1107030906231c0c030b0901 60
    0x866215850155014150441c1d803101c1c0c0c02030201d07911074041c800240b04030345c4200f041c2c414a41c85800e1120b541d084038001d40d4211003c0351079036611102160061604039000920b0aa59481600008215015110180c503031140d600390040001c0c0c0f4100c020b0614245001981d284244d0100602c40c0070020340c4500c0e140e21201528114036251100d190964581450070085031b440741c41c2c011603078a084201d8003941142072090b41c09001c0d5448034400e50007100d5410b030801c040d808042103201c04c03411480d08401a00101502080d02d010395500e20180140c0040417031182c2030b0000200704002507150792802c0c0c8000c41018041c01e100d50180c0e00c2021440d001d19009000900c00443d10007801812240d0154254201c015000c0f180f40c0724446e80014816881c42000a502e003502001ba51032425080d6410303a40e042d261140b48900f010015a03003171031414590040b030b44868045260328802000a0941071031111144242810382c000241c0944202c445880105403401800060b96a50450424112 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 949606681 1250 949605431 949605463
    0x50f09060a180e0a11010807080f071b0c06091806080c0f0f0409060507090b0f04060e06070c14120a0b060f0a09060806041703010f0603020f040e150306010b0705 71
    0x4101c111881c0d005065150641060340c0140000031003400751021458404a20917030b56a81d403035a503010227071440e040c15940300e40340038034407800180300a00070011300e184e0301407030a0440c0210300301e5611000201d4883e0080d00000c3d2860302c0c100709140c4200003000105880c00030a100781405c3c00000c594134008444a144502070741d14455900b6101c40b4810038400101400c18011050f0500f003500141c071043e40d4290024020010000d099035041013540c554020700c0b284240740c0352070900300700c6030f10010039038060f0300000401421001a01c42d0703c2d074070005c0c0a5644c131011a030001c5010840d45e16400b01e40034546401000070b83c0005124400d105a1108081b104107005000d0003000ca04120341c2c640020034401c0c542080480e20b5100080c1c2d4a100700d10a5101c40c030140ba541158010b50300007886502c43e0003141000074000076019401400c076803080c180312903041c0799440349070f501007040503500c04140c002002d95614503820180700c140c3c090800e058103e843c0c69136035550079a85014015a105030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 949607931 1250 949606681 949606709
    0x908070803070b0705160615061b060e1e010e070b0901021c03060f0303020601140102010209010c0f0201021614130b150304050f010203160f020607171801050a06050f09060a 76
    0x2825005d00241e814414804450745081c03010b51038001c00402d40c08003a01e409000e140c3c8009590b03845488918218000011000310310742041d0785007005001c00401900071801103011032062500d500100e404810507000000c01c1d54000d50b1149400d120344c4e40c0114406a0b1b0820170041d060741c000070f69030b000640c0354030396950b01d900746602180206400c0d0084c1c12000742145c8000240f59002420b070341072700c00c5250307160b00d11180d0b1001a0308070310413884118040f45c124501403001c03505040300b2142c0640180141e4503c8841e940a400401e1042c0c1c1091503100342841442000781070541891050007a03101e400c004020303252001a6280d20b00b8885000e48180010010701080010312241c82c01452000095491782032074200310600031901502c81001901c0d6644c04142c46100050881c019212625002c80407544000c22203a54000104841b1440c60248155481f200c4240309040c03281e0400c6c02c0024039107040408122407608110f001c07510646030b40051210a607108181101150712003895500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 949609181 1250 949607931 949607941
    0x6060905100f0c0c17160321111c0e030601060516020d020a06030b13020316080702150907050a060203340501020d090b090607020c060c01091b060908070803070b 71
    0xf400303441042000704481340700c80c4c0014130115241c100c40041803200081c2d95000140810b581ea1400c210310001e840c907904002036100d484a496813a007500c1c1040d24000086041116102c1e00e00215003849082d61040303401c4928500b070384102c420b007081800714064010340d45045001031680c090030303251610300311200c2503410842d902d4100310411942d01400f101c00c940d640d030201500505910b62500d00819422460b844514210710861340b00f850300e030b14840088810f81400326074100c0000e01420961240b94100c1120941041c0814459850040100003007402c160510490f400a2703400001591300c244070f811890402118800381d91210248035481183c1040242004043d1400c3c016201e5440080c0032580d20903250415030055018450700450b544170703050011341c2c80904442e0307140141c0001032070320301c00d03c0c001004017004041c3c10000714003c810354496103001400e07420105115881064204070a9400140c400014201c140c00b078203042d07207040c00c166101c3c4500c032030061401032000000f0b8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 949610431 1250 949609181 949609187
    0x213090c080f041106130b1e0a0801030f020a05120d030e0102180907020a0b0f0403020c1e090406061a03060a0603060b0f130905070c0201020609060105010504050405090c040c1206060905100f 84
    0xd0020720305049959141c1f0340c0ca111038905a444006050922400e40c032509040b81c00c2c031000c5801c95001c541ea002c81d03aa01e592140c50b501200d60308200d0380084020310000d400d0303484843e126010f00444002d0045d504140304007904480d149854040782c0e0340103008221ba0000325044188002c441620003c41a42d141c1004178240009020b0050203003048034144540c81d4800021030384180d2280c0c00721848080207400700310340210120500c005035031101c6060916801c00e0b8440b142c10500c20100800c0301074581032440c0590b00c2c1a01000d0003441c01004022003031070107880c3c0c0f50040c221401e040100d24281411447c0d584240c00741003881580010310700035401c81c1110084021326910104101720300b0300c100000e090002d001420780c014480d2001207400c051000c11198100c400c1612120719003880e16061001800380100141c140b40200d03240708100c2e484d98003800006444a03598054021401e003042c800310b500c030390400b004000074031001f408107480d1406402c070b20b90664217000c40e0131711200c0c07822 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 949611681 1250 949610431 949610437
    0x1150318050105160e0910050d05010e03030c0703080f0c09060f070f11090906010501020d030b03011107260a020a140a120306080c0301020f1902030d0213090c080f041106 75
    0x4003a03610f440e04100100c0943d00c41c00907220065968403900304054401c200103e10282c2c2c1504c00040b2001042059117040c00c10000090b00c550000304214281c000c0040c25038008550060354210001021002c040c0d020b00183e60014901c0d142d004681400403070075045001c0c611102d03004100001c0c2940319400b0030002d40d11b07000e600042c50090180c240c0750165038122100e40c05070040101a02080c0c1210340440e10a05854069000b0f081e00c01c80e0000403005066000000c54055507174003640c500350074164008054081c0650880740306050358005181c00036a400e092540201418800d0303940c07042d0701043c0340d11860741060005052846803207810f030511400f00c2c0c0003059222280400c20003a03800d5000602142d2181064a80c80410b0000381802c0c0d1184000100030140100440d40d0f4250b00340d00e465081440a1040302d081c044469100c9049a1001e807140409a441402c02c0016440d0f90007a01846162460503040c24140481942100900600010b02200d0b0b640036040040d01d4038001e07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 949612931 1250 949611681 949611683
    0x120d0c1103041202040f1b050904021c060f0f0e0402010e0a080f1005091f0f0209060d091104020a05031602030d02070c09060b0304020102060c0f1309051e01150318 72
    0x507a42d507036945649420080202c5a01203008605007100d030411940b062143c1409100c00c107203d4402d4859140b000c0390760b0740c8455030f10b503881582400740c0303580c0a039090000d41d00d10900e0040001c0c100d0600000c4034100200358004840c00c1c4140805118600312540d016401540c2800c003078800036144000945900c50940100340300e40706056140a40e8440002c92841d180030607001000180c440102090700d4001c4013112041c10007603000e242c0f6500c0042c0d4010307002a021420010700300005100055a298485141c8000c0c440d06c0300460000e200030041c60210707a040c02c0b6421440c0c6802050050a10700004040c1c0003036035805541500414000d2085681100758510308560b81c411524191200b9140c030301a0240c018584900400d680c141c2008903402240c0580080c032117a9034000a0b00d50a500004044070b00070420322280702d0b13211b280000e20000d00040d19000c64036107031040d0415400c0d0380061824145a100c1001040200e02031034000d40d80400601d80030072408010140b81d203d40088100c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 949614181 1250 949612931 949612933
    0x10501030515100e040503120105062a010209030706020303041a061c0201140f1305120604080c0f0703120206060a030201091205030717130602030a080f1f08031803120d0c11 76
    0x700410006c0100052a00e11300101060b607080e603d581c24040c05002d20300b10030480c03041c10180d20301941c4c50403141002101c1d00070005071805a801d004a401c04546074080c10140e070000c01840200264840441d00307004189c1150a194a004000203510288451513100140c0d94180002d055902c54070081c1c00c0741d07048451541d170316111081d88c402298803241800020078004880491743d03292418040d201340e0780300401004076440315121368645510404801406e0f00c0b40b000e0300d04090605224410046001d50340108603143c264030060b040c90b100030301840c400c6110004c14401030303800c11254016501c0b1a12410007180c201d00d0b029140d440303840400b0305140c401030a18803c000b0301c10001c0c01040d6800120580035541c808080c1c0e6a806000c0000000c64811000200b60887c0746051543c003c1c60b0030300b22001000b6a03050340714190708641104032150000202c000c100000d0085061300c2548c00e8004025650402c410180240070301c180e0345a105854402d140c1d0524401c2e0900351224481c40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 949615431 1250 949614181 949614209
    0x30e040e1b190503070b09060403060f0f06080f06010303030c0314040f020126040f03120e0f0601050a180e0106180609060504110313031e0c0c0801050103051510 71
    0x703401c1003001200d1404240c03141070149209500c0181e01c19080d4116a07024008100e510305014407160a50000f00d00560000e809200000200b4003a000c0d982480c003040000207410107401c00c5090a0b40c0142d0094010360340854150070059400181243c112070305454001a2002c4100e0101c02620302c0c5981c6203400c180c031000780001c2c0301d84081104801d0740300b62507495000f500d040000040c0c415000c080320030203060500040104a000c6e1210380200c1c031038074010400b50724002501046900e00d030390501d07441d0702890f0f10703100c180010409140904011120342e191300c0d240c00c00b15040310500e111031444003a200e034982c000000c0309400060160081156500541d01c003c0d5140000380018812490b146007002c4002a42d4141413003401408007654a0180c0380d0340d1084001c50b02d0283d9184201e04114010000100141c154454540d03c1030300c80d914840007869a040c4080d508003250480d01003645418010030019000050511a4810210402d15a1350760080c00d5100c045956000001010300c007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 949616681 1250 949615431 949615453
    0x120c02160b040e010611030708070501060b030406201905090a0f17100501031a04030207030212160e0601080f1503070f05041508030904200c0609120702030a030e040e 73
    0x201020b4003d6403441c4410034040d80e60f41600b20350309080c0910b0400b03690810040710011401160040000d203010f4000071504558a00000c2c90701c0d442200c0549041c0d0303a07848407005803103007600d14084400040407820b041100b0207000240c04000401c0300000d0050000311001e00d03031203030a040d40040441ca00100122591011078071203001000748900f1f02030050701c0458407210303440d11455068a0300400e5036000362086440d4100c4141e030180c01982984500000000107a55185010400e48420b501078005d600703140c0c4510b100c00c1400d410a0701200365090810a01c0d0b648a051b41c1e6001600342e000d0001902c0b00c49082d07144e80d000c3d0701202d805000d00200031030b805500074480021030341c040e07404002d0300c2080d24204001074401c1c0250a415001001210075030301d803540120314800403849400f03125400b0425030702d4603540a44440200b58000c0d41c03c1180303213401800311503640000c2c0d0154915220303040c0d0003e40c0301c800400e001400d00008040c1804640c8940e4048400c1c0314407032084030410301e40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 949617931 1250 949616681 949616699
    0xc150a020a320f0c07030318050a0e13080d09080a090b0a0c0b090c040623010908060604050c120901061a040e1519090213050a06120c0216 61
    0x40c614080100707007050500810b410503004903880075104400320742d21607403480d00c50310760b076600107003041250003c01e00824011060a009103001107210740c80e0b041d44030760303100c003034501203201c0b50b1040c0d1080451100c1009201c20380c18101c0d500c50100c1a00c01402115850012458000ca0307203c1445680303450410300400c507495006041d004041c6e20b8540003180d036016004010301c25000781c440041d1501440340001901c0050080d00019100b003074070b42d0199000080f404913134a60b03111f654041d1284902c1000600c0782106825002e0007071a2080401d402d0402080c6d036440007800003809517a8550000b0340501b850815120b04c0c14001e09000c0107800d0841807135001e8812030040c0c0e03078001a040b804115000c0150304990489a450030340c1c00e882e540d1080f0b810ba00c1103030360710303400d4000301010107040c45e01e01d07100c000702c016040c22800141c44039458410200d80500ea030300014016030320341c401848400d070490030b80018403001d200c010902c910104d4080781069165116028811800040400d0f030b001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 949619181 1250 949617931 949617937
    0x31d070b0f16080408120405180721050a0f0504020604032004060e15040b0a1406090d030906030e0c060301050d021f0e1302030115140c07231f050c150a02 68
    0x30a03008440320700d404035524218502c1f643c42404e602201c201514001c0f018801c100360741c0180c0c5030401d10702001240000c1d000e043c51075140403600325507540c20810000b41520071203440700358001080041d0325141d400303c1c041384103500000d044008034000380307042c21142950300149150042c105000c825558104c50307903d8807068031841011244405050424209441501082c16008003520186460009076010f02d4100114140d0041c6082280c08800d031a500c0c1c2e1000d0300340c441e42e0b40b400d40300c0c60020010f0440e0518006402e5a0300b06000c50000365865001b5a41034031001c81c0c010030000020300c00501410960202284514490301b951500160410701c50018000140c1d03d0034809840c0f002050304a03c404d00880220070720704080d0784407603849034600c404142c4000a42524100f2032050b9030303203082516800b0ba040850344241032180106407481441c17001c0130070390710000b140302401d00d01010404c820300d00504011010541a04001c010800c1030203104010b000c41c4010b050284410b00a54 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 949620431 1250 949619181 949619189
    0xf020a03090203060a0b011d0312030412110c100318050111040f12050615060c01020c3307050a0909050c09012304050f010903061506031d070b0f160804 67
    0x401134800140310301c803440c00340324416901695038086200718002a50840a00d0008072901031141c4c5150900f6075505030000e42c000c078080d0444030401c48002000401c42140b24242c906643c000700003060540c0c50343c02c031806403080361b400c006c2483c03282003034404440300390101c003c0c20070360a01995150701c00500000748140e42940c02c003402c585445421840102070755840040169212000050340f1305402e1800d0b030032008006115034580451089503600f03907040a4140c0c0040c1e006441c4001c1207182803034540003244554030900c2030a00c8000084065240010005010300c01f0001d44200c80d24841c1c119080a004100c0e41000281400100000c00382c0045031510b0224180c0b80903010002e1984104101003a1949006440c4c60309141c1440b81d45030407540703502d041c041082408000103a441c042d44101610f08074546001c0307450003100a041c0c4041d540700b400d101003000400c030300d030f90404242981551b01141155680d0901c15408810900c201c5003284001d4140070075640411004800400030bc07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 949621681 1250 949620431 949620433
    0x50f0703080604090213050910020a12020d0b090c0a080f0601020a0b1f090213120c1208190e010206151810080f0d09090c080f04020f130207061803210f020a03090203 73
    0x48980d09c1d404404034420000350384045503000c01b0380c44100b201600140f5102460560224207a100a0f010a00581d000d8070040c000000100c1d4000b0b4440d8407070380c881d50205807004030700e003641001c0b00043e403601070307481c40600b907a03405a000500c4414100405d04c17241c9514407409402d150b403408071000a402500044000850607070700007803002d10460b100024150890781440096140c0310110b90fa440d4140c1b401c407100441400301c0484240702d047d841407015256103400d04908488d80c0028117000008100c0000040d4900401e515500e9084029407902450405100e00d910f59121035600052280d00c0050300c0c0c030407094254402c000100d0761140c2d100e4503444803030440f03840704801400e480449445000240b4880d001541c0100c080f40c40395002400a0700700b1402c224400c002c604c40c90f002c0d41900300890740006805003040160f119842809280c11003170004201d440e60014854043e00038100c41841c040d207000c100350380b031031b40c00050440c103184000c5640d40f0305504084c1c042c10240d1303420391107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 949622931 1250 949621681 949621693
    0x7080114150a0c03140f0a110a06060b0901031401081e120442050906070213051909020a14131503030f053405010f0207050d050f07030806040902130509 67
    0x10181c8407201b42c884504284601030700381404c2c40c0701100c48082d0101c0c1a812407141071004030124607c0d00c80c4074003403e4a03080640d87c80b0b100174005000d4500a000100d680d29104004002020780421145110002d41e6804003540f100009031500d000d005545c5240c04035000500020400240c1d0840f15494414182e001402c0d540c001d03145400c1c4809240f5a00b818001e11b01945251b44610000c0100d0b610041005040c03840d69004501d0700091840740d01f04450340c46050003180381d0036803a200100242e0b46003d03c1003000c5c43d400300f07007629000d20624245480b41c1160a101e1303503880c800c403d2040141a02009034203002350380d44120900c14842500480c659202d414440c13413090040b1351442c0c0d00d040c100020f070701c990300001c4250540d041039502802078080807040002c0f401e0251040b40080d005000d03855181508080d400d0588000380c03801403083c200078145c00321801400b5600d18036003506146185549180c01316000e8030302d443c002580710300745440034409045a540440d01070446002180c807 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 949624181 1250 949622931 949622957
    0x10c020a0302061506040306240503070602152505030105131a0d060608162c0a2a200712080c070906170c040507080114150a0c03 57
    0x18031419440405001a04024005400100340003600d01c20400301404151406d5521b0f15003500f07c4481c26541c0002c002d8158201c2c0c00003007003981c0d0303801401c001c402600c06035203484c001959a003c80401950b0b51100100000d4031078400c0036444e045d42d002150001c083c024030401c0144a80e0003400b40c5c40c450700d901010340801e40f48038420041410a1a065a4183c00801c410801440c0b1600b104840c0b068840c40045941c201c240004010a642c80c1240c014260400204100d100b5146c0c40720354032049080c0002c03510383c0f581021940c010700a0380340012050a420241480452080791382c681c80d0451445250322194070542041001ca403162158046402c0038a041e034540700b0900c6030418400420150138007040501c0010185640d1035000c075141d10341e13600744240a48045610802c0309041c4c01091019401c1c0c10301582540303c0c01120100320918094801400f0341106004e40c0c1e14000140c0701d45000c648035841c451200030304118070161501041302d03004220b101411b01c100e00041e40d00c1d0b5050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 949625431 1250 949624181 949624183
    0x70b0c070f030c06270609140d030914120405060a1b0f020414160e010905040e0309030d020708100903020c090f060f03011407270b040f0e070207150504170d02010c02 73
    0x5120107030517000061029a480d211070001c2d150805066800c60140e10f18a44c1c425010071007030409014070f1310041054141420b000495800c80d80d80c1e04000e4202001c04002c03200788070211001d50307000311803258031214140011030350f45041d030100d0480c04203080c2c0d2038001d02060004190102c0d01c03c81d0140030b08032350f408801c3c21111090b01c40d14401c0d164020a114864029603500c405d1017010302d88402855581e1000034280d845400300c400d0542c0000980500c0340c00c0c18420043c0040c040e000501c0d0091a10b49090b6540340d000c01c0300030f45680d8a05014040500c00d0140c881c2400c0000c081c4070560408035802908403a041d51018072810095041e42881d00341030040c003511200c00181c1c110580c1e01d00c00242c40079002000d011902c016940b5001741e00040c202e41c5040a441e00504440d2150304040c00002e000b44540c21a95143d00107504100e203940e070014942042d00e40e41c0c0464a44c4075000c0c0d80596803802240c00c0320004009104412032500d00004071f10a940342160700178810413400202c16 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 949626681 1250 949625431 949625471
    0xa0b090c12011401050432040302010b0603040c1503090803090f1608060613020903060103120f0914010309030e0307170706090612050403140c161a070b0c070f030c06 73
    0x3400b40550040010817091501d940581c005074400d0482e80c0300801209200381c41481e10700681680b1162000900060560900c5031162221054030300c0391850030117403a0590b0003095445046482c0b20800c0380030406612a400413850313242e10800aa8503400e00c080655191541814258500c1c800c0c041041030803551003200608507140040035000c07030b456040c01c0c01100c80d541c40101c01d032540c0030003500806440c03c00515000f540945030010500c903400780c0042081d6498045a41041000c8409000d0050710a03003142082400742000200b201075441d06450000c82038000c0342c0c0c58019810005020844203215030030740d007402d10079a12129103a2000b514100d6450140c44002141000d058011030140e0f84402e80140c081d040040019005082d40d48195020310500d86241e0030070b104410603411201d4503a030142950b070b0580c62003258910011132240c09880c20280000c03c0d600c0c00b04039901c00401c01c0300d2000b500305d1752200096401e402e000d0582a8002d40031074542e46881c2c01d0300701c803518503101c4d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 949627931 1250 949626681 949626701
    0x114070308040b251803020306090304140603010b030106110c19240816030e010501060e130c02060606090a0b070506010e01090603120804110a0f080f0105041a090a0b090c1201 77
    0x5881d45504510008a580c03501491749801c0301d180c8050080090317501005298400c9005a00561359581000090640300602c4502030740122814070050109400c0e2000b0f880c10f440040c58800e200b14010107905140c82017445d0000d03004040031010307202c03561080a419083e04c0039108940c0040741c2c00007840e0748522400f4070404c00a078a94000c241c490303803003607040001a4658030700403507454030305150103007124000e921500102d0f10700d05051049051254810204410714001003011900b071000c003a4a0b003c000303104a200340300020f9400c00032f41e80c0300002000342c100035140e00c1d02d030000c9181c080ea80c0e6a00703007d2940585140c0000143c030200c54040ea005403230707020404003080c10302c030701081e90179480c013610488a2010b41e581041c400d40303d8907900401401003103040c00f8010703e8000b580303080646002420016034180410400130451455000c0c50610b5525108140f540d0780342480d40c2010861400280300608400034000403080010705200e1503502141c0203004c0140304501142203a18043d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 949629181 1250 949627931 949627981
    0x405040c0843021c03021201030803090307050303090d0206180a0602030a0204320d0f0209060a18050901110301080a24020403060e0c0603240114070308040b 69
    0x100c0714001810002c05004010040ca49800e0074070a80c2840c103001245015140005a100e604580080001060068550420350030110f04d05141d17000010450b07501404094003510300080403c010352010401c48224a40110589450f810005145900c50001140c120300510814011840f051070604c004008940b5481c001d110a03160342e81c03482e010703400003400c4020300c6130700380800900d01d4030180000202c4070040c1500032103074100f4000e000f02d00ca006400d1138001d4500e003407044000b5091803410404550102c1c1c8008895650200140448040d60048011500004000e011420541c0c002c140a2002034000f444510b18040759250140000d01c542c80c0580d00c9940102d01080031500ca10648012580b03204012600315600700080e41e0040d4012203501350b071351380d00c400028802c0c400b00c0182c7c00b0840e003181c90742c20300301023030580500c4c60088490001c1c20f188284107070380e010705965079040d540c0e03003505501d640203420080d02003c2c3c1154203640500818001074030f842051011089000782e004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 949630431 1250 949629181 949629211
    0x91103010f051b09030d1803020a030305031008060c0405210304030b01080d0509090c1b071503060506070206070305030910061517040213230a0c0f020f0c100c1401020405040c08 78
    0x340c81250341000c003407c1c8030b0071008411070120158a41c0480d00d070285000b030721038580c0c9041912101d41c0008546c1d0043c1e50345e070070001c00c0c88a003442703200c1280c1c1210320455214601c402c1c00c3c1e40142c1509891501c840c2d0a200015000080040c02c0310114125040503040d00c0c036503110b070442550f441c80307140d0207982e004800c03900060103021000e002e0108404071a102044400a503007000b45811040d802c481c80348a03c5031707800040247d040c0524800f03040c003614840d0909000b60f010a8a50082c41d400806000001c0006842c0b03100c208510001508245014085540d45403140002403401c26003060000302c80562a0001c17038030f0382c540607000302e40c00381c03985054607040c0790340000411030811401c015110700b280303007186052030000c182d0041c0c0301e4900c0014640d030038160280c10013154401901c2550018907620b02c01400c00b2481c2010008142c0301c2e202d40c0d48844504a030030500441000f8070305242d20000d80040041503000d44117039407003034804104074030300c21100307940b103c0c0d0403550602804490 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 949631681 1250 949630431 949630453
    0x140601060801034d120a1212180b071706190302040f020c191a0703020705100e0d0e0603040f0512040602061b0a02060a091103010f051b0903 62
    0xb86401c44c2c1321240e120b1074102d40100340c42c03618100e2900911000c8815404002c103c00302640003034001c2d6545004c0381d4000408224500c02c6880d01003240b409401941d045480d804400d00503011a14100c030ba940f41080f1040030078241007055030030440280d070102070600004d03440b18081c0880b2502028130b61213034401130380c80c1c1d0204881c1c40b4040c0c200c40081c0601100000068070b0301e01400d41001d824103400360f06d600d0a5611140b9000411440600c11142450b90704013040a07108a01c5420b901c0c01c041695a41d11844158043d2085400091041c896840101303100c0a180e800040f0501d8031000369007a803103a40c03204440400303400900035401001080440c0000c0c00101c002c0503170034800c1e400d071034454120591955042d0499403148015800c81d50070040000f06a954200302809400310003403d00c410018002d54560380280b25204003951000b40100b80041a2010f0100c03a03002070082c0b0889810010402c042d0000743c4001e8200c503408042c4004616800d4190b500c00030015004003017180f25 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 949632931 1250 949631681 949631693
    0x708070914150f01140f0702030c03120a030218060403050a0c050307060f180506070c0e06040218091f15020f030a14030c041206020a081302031c030f02041214060106080103 76
    0x503c4101505000425102c80d540c01e40794405080140200701003d5103e24040c018035042c00008042a44641c1081c0004c800050340030301503c6400505141c01030720303184500d406102e80b200910348168440b601040001c10090009232110380f0900c282840300070704d81da40c014907a98040502271407011848403100c0c0507040e4403c0f200b804a0460034100240c4083d95136011940030b601c12031054801d004050b800b030250030030f4a80300582148051f1000c6240c0b00d24540410840e1000d00100c0c0c1c0b10b10188800300f5043c100d203410a2040781c804d0501218502d9660384442c1d01d0a09100d407080150044002c807601e50400401a59940d00746922030307000740405191624034542c00206011030003c414040411810604215208081d10a040044c0e8540822801600e90440101016881410b60045500684003c0760f0240751103041c2c00082c06c00070104000760003030101c50620885140c40843c00141c03400807044820045800307854120f60800c40440b17226240c2401340540c102050201e001000040c071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 949634181 1250 949632931 949632949
    0x211e030306220e0106050a150801051011010509010b030d0819020f19030218040b0f09130615031103030705150402060705060a06050f0d020a030f050708070807091415 73
    0x9102e00400100642031050300444a010101070a0b0782c0d9158402d104038102428008060000400c40c0c40c40340c03007108402071030000705002c0e00d8003448040b070590507202c4c01150400f500d070380329000031711451400703c04d29802064000c800c544288115072508402c180540e100e14007901520040f000e10003108045907004e9070001250401c1948204500c0c0040d1025210001c4d25400079540035a4803800c00c0300c02068000000d5015204514104881400365140d0121144501c416154013149594003201c401e16103000e240007804907420107850fa250340c1c2810303201c0b2040da03104015a03007403460141c040c940e0707900036460000c10030380c00b6102c20110541c43c030002a81c41880100181d11780603260b41c2d202d040c03840c00c2c1d465014142d12043d00b804540342c99039201c41c901c04266221140101c10b600010201c003032600c00541060b211250803002d019080c08280e001e0611801116592a924044a50385140034421280076901e0140c01c000d0740c4555110f02401185c42000c071601c0c200165040001d102 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 949635431 1250 949634181 949634209
    0x30105160e1c1a04061401240504050a090e070b12131e1203050a0e0a0305030c0904140114190303120f0c0c03020c090403090e04060605211e030306 65
    0x140d229080d200002e0183c0c4101d04507241038015a11041c10309141c0f100c1903984041108010050210052102c040026081b0100301206440d04d02c0422800700244c41500c10381c0c00207500b1413684c5c0d8002c00c4e0404203400c00280c80c10003d0440b000a80eaa06078006a8020b60031462038009103807010135850046c552061022900481200f40280141800d0040120401c14200c540700c4901c00040551609442010740c09405c0c2c603c140300c0e8800100065071580002d4900809020307010000c5042107580005894402078040d0080061a0404240c16030f5203009100f04c0052a4604842100310704003095084040c403d000d800000d01c5045613419100c1c02140d21890040c280e4482c083c8140164034020f0034030415164964951030081c50600904020098241c240110242d4042c0310009610401ca0b03822130700c1c005000040c0c2e841d82d1601e0006840190711032940000c0302c99401c1000c0c2c074040c465108200030942247c110b81d800c0a07644204184880640e99960400d0000684500309005004015 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 949636681 1250 949635431 949635469
    0xa0509040809220f0e010c11031b031e0c0d1b080f07050a0c082b23041d010e040b0708060a0e0f16020f100f0e0615030105160e 56
    0x70002003076100202c2d203130450070000d520b48850114100c40d43c00e1041c03840b810158507080c115030b0784081e17820741d903481580020348441c0c2c0940418039250307905205030380c0d5046101c50200880038001c4801c940d1600252201500da014155100079400d02802482540f2034413104407180c49070751912403201d142c00c04030705c80c810309104100110020b0004c0c003243c0c020381e1040e050b960f1041e080900301450140300d050001840e40c3e0381040c49140c0e4050603c01d25030300b002c0345080400070321100d00d034130300f0f00d07519401003c01c1400101c0c0100341c030641411400c003800c03503000800d1800da0703990990030380103902510013030800034246010404452240c0c0c01160300103006008140500d985806801041e1001c46014044001c140140410030342200004904070646c0c3c8000e01c0c400c00c50080b8583c4400030a9090340c9881c1e50f806404c10030524641007911f43c2040359041d5055072404110030010740011400c22031080d4030b1703c0c0026508003411620622100229960798107080d50482c18400e07408a100501030302d07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 949637931 1250 949636681 949636729
    0x5010503070318060f0b060f04090504030c0807030905130605330403081e040806131703090604060f0c020c090a020c0a030c121b03120b0303030a06050a0509040809 72
    0xa801183c030626000d462141100064a1440d440b840c000c44208019107446001e0800554480000b4038055400b40c41640c1c40c00246a2210320b4165003150000f08c0050424802151178020b042e0001c415908075001900c422015085485525084404078058150f000103402e8148801250f9400205c20800842020140000740103051134000d41203540112500f1070300181d91381044009504640e841c0085441450510f4200351015407100e00040c03094616600000401c4103020060802c1c1060300842e04031182d59081c25458030780c441100f214156110703810507001e2000b2202d01e01c100c05c2160300d42d0b0b01034090b40442000f0404500c002030900b500403a007d000b070500f914014800128003078400c0d15542c4000244d0310741081020601d0200c403041c002801000b070059404080003041480c1d248c41e1940c0010300240e480d2004080300102c8540500c00403040008586081e070205082c1d80e011680800d55a640750104201c4003412075000b441c2040c148660f1800c1c1c02c00501101070f8403464810440307 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 949639181 1250 949637931 949637951
    0x20a0306090213140603090d1409060d05040203150709350105010e180604300203030105030f0316080f070b0403050702120109020f010f1803050a030e030f07050105030703 75
    0x1c01d81c2c00080841e164083d10310300803c10598100c14002e0720400566407141107180c685c03d6992902d007014250010b0003c04d0365848049000d0030100c42c1000f00003407083d034172813502c0306008d401008120f404a00920494500c441c0e10078911540501c203841a40d505080740d030900c4003444100820000b074480c2032445440000007250120110045c403506d0398000501c83d807404111018452014194801c80b80305020941075200c1c01080c101c1d44603030010202004c40d01c260865034000b07628001d80c82c00c03413054510b04004141d8007000460403900100c003112040035840c001c0c0c0351248603000003000b400340100452000500502e02030801e419041042d06d00b0201c84e901c6c3c40e00120b10440e13080b400200009840303801c61030070603c25111786449074005c00c00204203034003007001860b100b4a100d040c0401b00d003181d007400d0702c281c004110142000e4402e1007950b80e2403400c599108444401100894840001c00342a03045c001500c5540300c480b4802490f80780d20348401134501d640b018100f1000c05844a050360 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 949640287 1106 949639181 949639199
    0xf03061a130501151b0b040503190c0c0b040305030a0818010c0c02130e06010b251101020c06090f0418120503090c1909020a0306 57
    0x188a800c822444251400000025540701258441410980c04107401c024101c40e8082c00801c2502c01c010740507241480019460a4100750a84154002c0b50700452100d800c140130b40305070382c6002d41200205088010046100c00444c01c0d13003201e03104128000031084000c0c030b01079010900301820b5546140e164426072020200301728245010469105207460098500106100204a01c00d43d006019240841800c016481800b2a00c030200780b5490a02440004200401c09010f80d0781c20700c0c88080ca07039007080010388001e400480b071400c0c550264815a0380004e00406550b465084a00002490420380d12a014000e00c0148544011525044c0350300c5000b038000ca4011507850740c050941080180c00c484042c2c4151100c81d04260f455400030003d501841245003503031200e000395018030919002104d654461100d6046040066022aa010348404071282c9004200b2a0342e0300405 = true := by decide +kernel

theorem cover : BRFrame.Cov 949460431 949640287 := by
  have h0 := BRFrame.cov_init 949460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 949460431 ≤ n) (h2 : n < 949640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
