-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4834
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:53:28.275418+00:00
-- url     : https://prove2.me/submissions/ad33ba95-477d-430b-94b2-15d2f61959d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 869244604 ≤ n < 869424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 869245854 1250 869244604 869244643
    0x303050912120c0304051c0914060f0a11030705010c030f0f0504020d03030203150405010305100c0f0e0114041206090c0906121202070503060705030f10120f02131a030706020d0203030f0402190602 86
    0x13050346031070130488100d00c0c002c0d061a03041020710320080d1420137848009400e140000c110320710000b14203100c1d20100c0620b0f41c80000d00c400d02900b41c0003c840c9400d0205c89150b1401e0180000740c3c0d140717202440204c0c0d05180150740c0c1d0f600c031b180b0500f001841340720b00340e006400d08001101f00600880d01103200d0000703010801c6403c0540c5e000b158000f10110001d0007090024502100303a500c00d00c5010000850a500c10346416030320300401a020341182c20a550301c550305c0c03403541c040004110440d001403404070810302c1214100081c1c1b4402031036120b4010141c40c140304e0210203440c020301c4410000c00e001001d403010381c501248043c280354403c5035001c3d000140300e400641c0d20a07004480c6015031b200300c404070362056015640c488240c0c501f4107090781c1c000e4400003809c409403034030302a151018041e00031000400c034450301450b10701923541c0c101c3d83c00d54111580501425038000b058030b90240e007004811000e51682d0000ca0b225201c40420584031a03800540803800640009091141900f15403149 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 869247104 1250 869245854 869245889
    0xd0503030402130204150c081309020712091508090f07060c060c020a120305071e09050310180807210c0b090c3a0303050912120c0304051c09 62
    0x1d400c0b0300c1103004e224070072446c045080340014801d80ca005034452050b0443c070300c1c2c00e280c10b000241c4404980c0c800382c411600011014100445004041c0042165081020310b00e810141c4252000020103229000c0104030340006404160030820280751184660554003003d407176110041100d0b009032002e6881906207900203c00510005103c9060341d00881d6101c3e51024090040b0041c003005806802044441e2001d05e81507010481281d01040554803401a07017440d100905043c07080c40308021a00511b4152200300d10300e4010412204150703c0f00e0003590310915032400041c00703800803803854090411565806190303900100c0c82980e260203211000c003d60340303901c501d0766507110b02126250418030310804200744444199110b0031440300c81d40c1c1070401901c803c15440410900690550001c0d86800901140420a00c0b02c07034078400c03a149506103002041d09580740c20440180ca00030440400000040030310506110318044403140c0140030884070300303a8900925200c180e010305090310b032895101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 869248354 1250 869247104 869247139
    0x5040812010e04050303150d12080603120c060c2508071106030403140a17090319050c0c06031504020d0506040b060703120b0307180e0d0302070f0f0201030204050d0503030402 77
    0x12840f4552120003940703180d03100300e040240300f820801388542150080d405c9400040f42e0501011b10b00c000c6645130021407611070101464049000c81545903600204031006e404031000c2041ea600c41500d0320103030782d03d42c24805082d09103401a0209245804041500000c00850000406645000b03c0041c0007087c005401c2001501c001e990003404940d2040c41c400028001d500900411541810700703040030000340a45000076401140c80100c9034000185000d80b03480c0b1070558100b09666803400d1030a284410804960f1024442d11983c800e1802000040d405851018030468000d130207030003551540b200c0c00c0c00e50b01806080d10f8840c032890501c2d49145607030515105803405135405039110350914205c803c00d00d00030444809902e805000743d00c0040b9541240c41c1d40111305c54242440010701d4000030580b00e0a1010b440c85001c1094010040c850204526072211828a0340100140ca800c98051006a009124903409190868110301050003441808400b9611030342c02515245440019a100d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 869249604 1250 869248354 869248379
    0xf1206010923061806062b1b0504120c090608010915020319020d060306051e010f050108070813140a11040b03030417100906060518091c030f0504081201 67
    0x81d00e5401002110601c00c1341800f5100f0190000c0c0058885490481d580402800c15091002d8104d6000c2d015040c0b10340361240b40c0b041c108a9103034210082c00900700c800c0b0003400307032096209540310991005602c070240507020481800402e900303002004860750390440140602000d00040d11255001081380780c02d8102070088034820020062401c0601d0403800d4050000d41009041c0c00e14103645150100c002032952142c0c5004162030b0030faa5007942d62003004141d040358140c20200c0031000c0c0a01c20400c81c0d8105c030348540c01007094101042640c2c3e502d50080d076480c415070701c050100b040d82201e0404d1464007050501400d400303082c0080c0c010b02c0c40c07000d20059a001c0f60b0b0a540542c0204810003940c0000b00c00d040900190005a480c0300d814180e1600039115010016070316a42e942c0d204003c80d2030302248080650444072400c0540e4034082e0181f0b074807440c59003034144d4641072184071102aa40b0a6201d403c400c0406981049181080d040010907034128a24140900428600210300c1038035804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 869250854 1250 869249604 869249611
    0x513140c010519030f24082b1b1b0f080a0305030705120a1a04050618071b110a0605130302010c030e09190c0c0201020703020f1206010923 61
    0x8403801e00d0840002c4036143c2c910761140000d0201591420310104450b0503005050342807070710845c41d110b10a090f03680f040006103254842550395100d8103541003180c43c0802404000400a8511043c24045240039100d03c2c200103000b948000c1c80081d0082008250152101c840000030603c902c1c90380c03603070421180e60b00c0e00c0c09220b0a60b03101340780400c00648180e0085501180900c0d00c0360401d0110004154205010f8130030004107a12104130070035021040000c45112a400c82d000d00ca1030400b440071418460020040181d480e124034000740c560f44c066080348584c000f075080f011081907a14103150304818075800c401ca214101c00000042c02c1485081981e006001540f5175034292441c0d82d005454101c1c0d620000c80a2003000140700300d003541e403100704138400c82e9691207058081007081160812111410325910601c0214544140507036030000d4001c1c2529030542c1c00791040c514550005406000407801e11120b40f0503800040b84c01a016000780d11203018454070690f81200380e840c48501d224044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 869252104 1250 869250854 869250857
    0x6040b19060e0423100e0111030402010c020904020f28060527010e0414060a1a090409060f061716031709040905061e010f050604030f14010513140c01 66
    0x114010130400d11100da400754000e0040c0004041da1a60b8500f0600061981e41145595440480000400703001e11102605081c60040c030314a41540042d147c2101c410380603002e069000009404c41d1289000580c0010f0001c2191840c3d19109108110514040020000c1d41c01190303000550240a10140c0701c0c9400072000d1500d55441800c00c803c01c410250312031324100107141040c0e0381d15484038403444450700000311118055140110603c24100b507039500211800b8100c2d609400c03251008001e40381e20190899010076800602d0400401803c50380e401d03150403616100d0f0018501d10524010f55400521f40291800300f4400c8010500c0200d551001901d03d41c40f0741140d5284800c444000e2140c0c6000420006403880c10b030b126949440c1e800c55035400d010641c5460380c0203c6440314107980c01445001a0102e03c1400c0402046442c000ca01c401401e501481c8200410002803490307200c0070140240080200d46405010007000084030001914000034070b01003e04491004a41c003038940360103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 869253354 1250 869252104 869252129
    0x1e0302100c030315030c1403072601061d1009020703020a0f14010c0206060f040b0325030819030b010e0a140a18091a0106090b03040f0506040b1906 65
    0x14800c05071a00700480a0450400d6995900301820301d01c4507068802641c02804854016410407016020000144601c1c600c01d9004c480e042222560345002c0002c100740b0203440390349036841e0b2142c1074090035094200f41401b11748445441c41c2c40c5044540c16105508014040511a0b50b90030700d10203c2c482c1c0300010300141c10454a60000c1942d40480740c00040c42035040300024460b04030043d0031034400072a044016003042003440014074000c0c20f095000481102d04010801ca030a0000c0e40e0b5450503940c50705440c00c140000000c01c420030100e8002584c00000d1a60780b0000070100982500c2c0d9801c00c007021a10781035680c1001e500c030f0402c14a52041c054031031801c1900748031801c2c400e6056040f070075920207032120011a043c04c800c4052a003811682c030f40030481d2800d80c5020040c03076810b81c03842811042620300400c1150351020504003190801c800c807aa0360344603420103000eaa0030010000c0c14910071007003440204001664550303c1290450309410754544101040810f5400501c10502000304 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 869254604 1250 869253354 869253379
    0x606080c030c0a0504080f01050108010621060b0301110a02031c050906040b1b1803100e060c03040c0f062001020309030f09040209030a031709121602030c040203010b041e0302 77
    0x41801400c9100f03150034001c0c18183c0d1484001d00c0c2c00801c8100840d41d9440b40e00401840b102409800d0240c4040c1c641050452440001c0c80b0b10003081100c080c00d5643c5404680a1301d072400e503c01187c00701000090f541c0e0b5202e0f520065600d520040c02c3c0309000c115205000c0c0380100500c06c0e00c0c01b5054003409400b107915552609900044007030004104282421030b02c14101c2c54010080100c0700e048030307030b0aa410b41140200350821110200158007507041c095141c0c03445201140065120401055441c2c4035141c500b050840041d04c0e81040d42e6410401d40301007107168004044041c207008008180c0c1a000da50040d41e4240d01041d90094103550007070002c010107644540281084c400043d00060501c040c1500003031a00711915019008202051303a028200c1c00c0e040310301d580c401031040c000c00341401901c2c034010030351280194403171690411703610a00440d94103111403e41d54400a0056403256110342040c0e1859000f4070038105100340c154080c072500784042d2103140807030340c0003043c59071240c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 869255854 1250 869254604 869254621
    0xb042d02040203062b05060a0c09121a0c091002010b09070c1401050a09120203090d2909010507230901050318061501091d0a1a0402030112060606080c03 67
    0x40000d401d0b5644115841202a088402807941c2190b00031844d020817030400c5c0e282420741c2031030006000840e5039410802d0106e07084d500030b000c0c00300300c4003c500b5940d42100203003081c2080d40700036210103800056040601551450340c001829400ca0110f451a1381090050420b82c01c8840100d400358122004600180c03036a4000c8101d000c1ca5400343c4000b0b184100c0910250b8212082126001c00440d520000715090085100700f0700394243c0580003c510f4031220305d0010300c01c80e0b04010300610058211500c200390181c4540c541e000f410900c3d00081d90b0341041258107010703000c11181c600024947e40000c103007050325000c0040c40200c0b0516000e1410780300c04011101503000400c1030b182402c9210304800010020848544220207031815420f445240200040c01c4403c164091091425a0726082846140800c40c075038100c110148002646210108504210b0f4140801280d00034070100001907110030200b031042c0010700c034000420403280c460105072140e55090303804000b07070340d07080c0001207000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 869257104 1250 869255854 869255857
    0xa090e0601020d050901020721030201060f030c1503090b0702060f061014070206130906051503041e03020c040606050702100305012303030412141c1d0a120b042d020402 74
    0x17840180f06840002e82c81e044a030784031001d441517802d00c0000100201062540c2841814081c14003a40511800c510b1030700c8100c000103d0b80500d044041000c2900c000d2140290b220344041c81d0310243c8a071103850440c5010f525424112043e140c0585603800040c40351521440d4140100903648401400355212070100c085508001c070120f0300180308010302c00024000741801002400703030203000b140440c2410240503003295010340340400240181b041c440007501da241e240c08c482420b0b00f00d00c54080c145041c101e140ca8200c5061035049464040041410747d80b2000405030341e802a0380381c200307030000c6c00011003c8860900c0b840d406000c2102c28a000d00c8511600300103503000c020304680c109511459400886203048404641410607130f41405200c2e4000e020080b1b805c802980c18120300c3c44040006071000c0005c100c40c0a280c07224480524941d5a8500280040d014443c0769804030364640c43d0a501540d01034400341d407142120303010180101c071600d00030780d0140f101c004100a0210300e5428003029 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 869258354 1250 869257104 869257117
    0x50a11030f0307110d0b01230a0e150a0506030c1b0304030c15030f020f0903011a030c0f0406080604050f0f0f030703030c031410210b0112020105070b0406020a090e0601020d05 77
    0x460784c402c0d048004038085a003554041c21102d0501e2303081203010721240001410301b1048600400e01281c00f0802c80000503400b2390300c60240e801d111454180e450003d6070f40800c640040754000700c080f0900070b0007881d01d07019013121050030344d046140700700b0541e102c2d6880c000ea03c0018001454a00c00f03001c030f00030400b541002ca541c1030502080c40c030031041c2c8500503a004800881c8440c000814450214070f024011032503401502203542c071000700c8101c0440c0d00e85032603074840c1d802480505001038403a00d65511480080c22400c0c00d440c0c10381003900e040341d02c0d15503441e10403115204001c44008501c1001c10740e8188410714000440c5003844954082d4060906480300300d09166954207110059819004c41ea0301c901e404100d8541424200344036400781c081202502e0f1100e805994440002680c0000740d103055540311540c14100c01032510048a0782c2c403400c1c000410300800a401e000030040e058024004c6544030351074041d501520341048280702c5808035049401070f8418241201420301a00c01441c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 869259604 1250 869258354 869258359
    0x1009080702011128290a05090c0307030615050a0612110409091a070207050102070b0c0127020f010e06030a0b041d03030a0f02030727050904050a11030f030711 70
    0x2c03408034000d08844d0300c104081d03561010303541100f030340400000b0304c000c032071000c032074660481034072100c1c0c4403004410002842c0006640c2d07030b440803c040d020200510308495100134100ca429613107030710700710000d00703c0390032001038442000344042050301e48a1203400680300a95101c400390400d004111000d49080c803002d5007000e800300030215411560380500344e0b10070301980341066150b100a004600ba02d0000384201d0454000c1c2c0740a110f1685d010601804589000c042c540d100c1011501c0c081c01007002041d0f441c1103505810342c42c940c01c0c0c207160100d0351860003101c13009500e0a2042c0156000070f082e0300c031281d00200410008040d12030540c4010200f44018200140d0780d2440ca2a28588101c1c640040c0b48580c0b020003007050b0104540191161426081025811820718803406060706041030300c122025020310300040c0d0480c07014008180140401000041581080e003081030300c900c800300d42620401c15200c605151400c0c001002913110036048020f500c0c2100d03a461b0341c15440c2d80c980c003096 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 869260854 1250 869259604 869259613
    0x6091413020d17071101030b0f06030a0f0608060a0b060306090402060d09080406030f0615090b1e040f0305060a050106120903110d0f1d0d2d0503090310090807020111 73
    0x24080750000f55401e51041440000582da00014108166010743c0182c890f030400d41412a1003c164590005107404100242c80e250345a0b1142c00c0f60380060420042d000c04618908440041d000d10001a10f5001e840c041c0300400c440e1210740144105484116051900720000c0c401080040c01c0c1500140601c9a00b0040014504480e40c0e8851050b03215502801c0000d8966250003812902441854000c0100120b03000c8c0704602901d02070582c1c0c007a8441c46400040216148090b643c001c00201c001c1383c2c1103031040d43c2d150b40380d0f40b0800d110703482400305403810300c81c00000544c00c10180c403406046e030310b860310b45901068040030400054441400d04a040041e41300c105501c012041082100d804126100c003c01e0240d042801809001107d443ca6200034a184000080e41c45082e41c0315401d80d00b080441030004170f0341001a000b01030700b907001c403450703c03003a80030f1424000c1c080040c21040c0ca0880654140300d5205003860306440c44403001502d110810000c1310300640c0504040800c007069542502c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 869262104 1250 869260854 869260879
    0x2d02040905030a0e060403050c09130f081b0303070e060c010906020319110f090103050a06050612040b1305070b0c01110f090a1502031602010e0d150609141302 70
    0x50036035160140407103081c0c0c004202031030580d4008018850406050325058242032654643d165107401c0140d149026280e02408a0041e2508400c0c0300c100c0d581062031090611020715010085500c0600710400080710180c0645107003001104032405543c060351500b4a400d40d810411050368060340d0480c20541d610760704500000c0700350005e1842040714405010784c0c4c1c0b100035030343d0091701c801710703001ca40d201b1081141c1e14a4051840a0303684007c002e19001485699171690500240350f29003000354850300200b00001101d051b189002e100d03c0c0b24240b1040b6903102e00518090f8000e06800007000da42080d4001d002c1081944003500801c4001c200202c1c0195040c040400507038011b44183d12a400005803a90741c60410b403808000030420781d1480940710f01c800400075264020107910140c45013408403400107684c0f00300c4070b0b60b032412401099011640b005113420805c2402601403404860f00384480015074403032034460650203038a00e8400000035a100070310001c0704482c03c50201c0e070100c07100900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 869263354 1250 869262104 869262109
    0x1c17092409010606030605130e030f0d020c0f0c01051e04151e0e010e0f030a0b07232a010603051c12060f0513110c0c0a0f032d02 57
    0x11002000184a80340050821241660940e011a00040c082c141041001c00560f218842c2c0c00ca89450709040c0001c2c102c2851000c103003180b1036602c240842280c046045500d65009500401e2403190783d000f100d1107858030f90042600c0f5000c071030300c1034080780341402520310090444101c400c0152000e114203180a41710109440107030894040f2000281a2120001d0440c0d2802964110b40c000c43c140320309000e2440340024000481c030345406008038844044540c050714208000b03440703113030b022440818a00d041e031002081a102400c0c20f0343c0000010060100050864080341e00c003502d04008500c071105101e1840f8083c0f060361001002c2d0b50350391040000803840074400304480100400401038a201c503440010012041c40c000401d189180000c10800c101ca83c0c03a401c801c44005071403082d0f80c8104403070042c00404864050200d0000700088a1102640118a4030320080382254000000e17603c400241e91203600e940001001a05a104005412401d19a540b50750700800008000764500c0703a4003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 869264604 1250 869263354 869263393
    0x510170c0a06180617160c020a140310020403051005041704090603141b010e010203090d35070b040c05030a0302010c121a0f061e030402031c1709 64
    0x20120015564800382e180110f80c1c000302400600c041d24098000010448003448209406060444092944540b81c030031103000d2140046c03c5d98008001c2c0c02076a0340d6080e04c050403041030103824804c0c014000700c92244d100e03c4c420784055a07000030084c00c100e1101043c0e540203081c040c106642c044610b801e4641c050440f0030042c0040d00c40083c2c08144c0314550f2030550701f0b00c00c0c0300381e2940f515040020940102105046012410602440c1c461991403510f40141c1c21849035140311600039540500c19014004450240004c40818070074003150032140b14181c85102031042902440d01000f0003440300481e03d030380b084c07640081c05812400440c5640790002460243c04c9081180540d46906c8400c000740c0d00000c011600c20100082030000c80d498850f100c0100c0d2200180605c02d816010744001e0589981c0103891100b100b20034030103c80d42d0312400c20401a082150100e00c203100340d00080c49a046901802255080d498451003000c10400c41490518180100380040500c120342208d514202000d0303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 869265854 1250 869264604 869264609
    0x61204052506020c1302040807031406060105040b03130201020709090b04111f21140a0614060316030b131e050405150403030612030f11010510170c0a 66
    0x34010600070210a030741124040c01e070400280304140d410030800020f90007140d2030f004084100c940380c100c50a02c1c500d00c1c0c0280515040b800244c86610000f000300012042c480750780c0c941e45d4045880c15620f05004581710b1245000e84c040d40d06040c00032810750203480b81959041441401605c5180351940010811100300d000165100003607542408107200d900c4912071201c02c000c0d0740d084004004241071030302204a901481c0b0400c48500011105400170040c08a80301001072414044104a124071425104081c1e034051021031425078001a00060034040700510032014110608513a510b003986514099079078480d07000e06841d050281042d9942030503000d01040741c0e64000420060b03049101c035854240c80300c3c0c40a241d18000602c004910700085401c0c8210043e5501501d40d510307454114043e040f070741d1200f030b11001628035000c20907400100000c0c41d0545945c50320755650400d440c00e42038039403e644540c1030b0200b0040074400340000b5000e01d10170070790010403104000d040030049448080c159 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 869267104 1250 869265854 869265863
    0xd0f020733170a091a040201020c0f040612060e0609010605180601030207140615040e0304031712420f041d071d04030f050306040603080c16090c1d061204 68
    0x9011350820400d0070004810807440c0210040ca135031400b98000303580c401182500074884c00141c10b41e50015569600003070050720303501c501484c0d006854900700c030180504030031100031070049070005005540144541002c44100604500d07800282103281c2c45140302c01707421241050b800300301c0100071030304011100102211100040420f841c0200034686c0602101490510407420a4818454044000280c0b01071381e8002c5c4122000000201c000c01d81d074031540c0d0f240888588401f00b00008142d00d1031040100100c0c40e2120101041091382500c4061142d40d40f07010392118420b2803004904081000880295014100041050000443d407031884800c017002c0d51958450781051000d01070045a03001114500c4080c1070a0b07017410794003e04841050207040c01040700120002d14190b54031340062008540058070f45039919550a00030b41c075085140754050000790f2030800018454030510a91001c0706030755032041c0010401c45007444881d817840e8844c07076200c0c00c140001103d2038800c92515020728800c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 869268354 1250 869267104 869267111
    0x23010c0c060615050316050403140a11060a051e09060d050103020a1a070b0402130203150901060f230f030f0a1a060a0e0109080d0f020733170a 63
    0x900d440020b59419400000c1510401140010103d800c402940c3d0040c1c400101007408520064089406005079400504140707401440f0f4441520049506050503000310020203414002c041404141d03c521400e01000440c10400d8000c10010114003d2110300405621446c06e240c0d140011901c1d08003803072a03460035540314010401c6282424841005005c0000e920750a40442d45114500d40288c0030702815480c044800642190f4851800c815072441c044c404540768200b00c00640300d283c0d107040c009400b54280000209800707000b04582d020412113a80c03503144240e03116401000350402d00d18070728291082880300d00302d45e044c100c01942c89072001414440c01d44c586030136810169840d0104030b034407040311500f01038041e0311143d0848045007154100111240c901c0d80c0121400401c5134000d6031240a51403510781210380c00301e580b00d402d9100c1d40c215003003070780c66061000c1c19a640b050a144401c65030040c01c40d000c103280d1027500401900d03041043c500111a018141803c40440cbc2d0207000715079 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 869269604 1250 869268354 869268377
    0x1806010c05060a290d080715110307020d020a2607080a0f09091803031a0414060f0906031c021e060438090304090f020a0f020a0b0423010c 61
    0x204c0f0301c00c5881440c05250401800c4503074041010210404006000c100001842c002804510b034060205112451030421180d0546952051745820680d80c0c0d8005018248070465103500c000b0b0f0710203419800c0030841840f1407480800d00303160300c13241c00c00c40c1c800d550601010001c0b980b0203016203100384041e114500215191000100a24026040034035087c0c03500c07210714810702500104c00686a4035007800200e094401c800c094050010700826030303010382411460249100c2c9940c1d0703503000384015544a50400858001c00100290450b0910381540c002e01114140b01d42580b20180018000d005460b049403041d14018441c0c4081e0f4160502548284180020170144901c1e82501019694044c0c0444181c1d195405441250700004010041324001081d80c0f01820b00803a4001c0006007800c218a0201c0740144010303401000252001c1000301c5504502e25001003200c0e455103078861008074044e0b0711644da0011120542240611003060300c4007a14141c08240301d0340c41c44040644581d0084803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 869270854 1250 869269604 869269631
    0x31d0301180507060e27070c050f100b010c0809240a090e0124030e03040801150f090b010f0302030705070204050405100c030e0304050105090f28090b1806010c05060a 73
    0x1400301c040540113a2140900c07110f5400308201940503c400341002801c141c03550b1f401110b03241b0310810b01810300c0c010340b4044001000001000e29007400130714000e0100750003400c010f4518600c4030301c024000c04d00030010b40b20f0780e261904407103841c03c0000c201c0046589800030020096000403680c080410301c3e1800500c14076928840f0b2600504010201d010400c544541d10078105121200e140d09154880a80304054203007882903c01901c500130080045207844d000c5696208018030a40220034100030011440501d42d0003007014440041c0c552004180c03c0c02e174114000d5200600e200200507050081800503600e5008181c081d9002e000100031301014406ca040446580000d144141860316036402c411040c040f0a590449100342082c40d100c4003000081072800f009210015400030050345070041c812442c0c4400c0e030710801100040f000e000c0c1c640e80880200c07210b000d0404c0e0303c1441d6076070810580e20118590341d8045010f1401d448521707840d9072614034090050341c3e10008103443c0c1c00343c9500c0c070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 869272104 1250 869270854 869270867
    0x702010e030304021e010e13060905090d0503071407020307150f0305040209060d0302100212010305070902071709030c0306090f150f0a05041a0408040e01080a031d030118050706 78
    0x24503094051491030a00c0c1d4000750782007181e420501810080f08441c20380b01c1c1c0c041c0fa0409070080f0090140d0700c564180110b0720006103658050008441d142001181400500054400081c003440e240c07640b55850303540301658800b00207480403061100c00c0006000585040c00f5503402461545103000d0814190640a05180e6100f003900302007500d4502000096510300980c5074021106a81c581000152814201e0510040e06200c4071141c0c000501001200310f0810b003503048a0046040d0342205031620501410313841199400350007035900121020b50307400403100410464000400300c0703038080340d007801090502030200c40b190301a402c02d5030340702d01c003400c1488031410f4562030582c3d9000030700e482c020341100018041c240c0b03000d4a9440c030004d0208a4150005a00303600034521200e0b00e8a41407405c2a03d561060040c04104001a00002001800001c4040003e607054503090070044100503420889221552110b42c15901d0300318640342c4041e501e04040394603020701d0181c5079140c141507019014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 869273354 1250 869272104 869272121
    0xd0209030a06020a0306091a0a0b250b0709050a0806060f04090516030318180905012306150a0e101803111e030a0f0c15080a06060f05120c041d070201 66
    0x5c0700401d00c1030232060f9100d25407071042c1c40f00907c082d5291a2001d003d040c0e4008458607103054510140100000d004540c082c26202d8481c658030440107c2c0c07154240100d4069500c10168158000390200b00d06280c96003400741030b1080503000080032089601d80754507190800c000c05245d114280428018140d02c40c3c1c8103200480c400d6110038050345050260f2010300b0f02d226040000c0f682d200400001c0200a410070340b44420139182480300541040801c80c030320070302030300c80303c1c070074450054907004009945080e210024a03644440b02d140703102d1014004010410007907581041101445100710341e00040fa0000a940038002d682050340000c0b0912020110030042d6400f079160324010b50000d80c2e000507400300b459901c10344055032181c40b403500390b1030070010b500036101103180240c404101c9548074104611505231b8140610030641e0b225010750300d800c803031500c1c000011070070408030180700342c00d2100980002c1d00c03080c114540ba54640c2a2908005a5000f955002508405111400b503090061811 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 869274604 1250 869273354 869273381
    0x315090603030910032f1206011707081e0106121805060402060c03040506030415151a0f160f120e010e09090a050109051c05040b0d0209030a06020a030609 68
    0x1a081c1e43d907000683c0140c5200100d410140c440c03064041d5002144140d2024210205019001c0403854040000c030b1740100c1c180755a04900f01000503915031140e822403420381c2c2c14030341c441c400e030700ca8601c200c40f400c8004208013196110b162a10f400d1402480707080d8020074841c1da415445031101070f201c074280c80307158a10704d10329401c0c0030304100460b901041741071b041a81102c150341d403500654002411340c00ba6500082d03009101108103c28041c9810110860122074981004100702c084445030010304280911a00c203a0981400805840300c0c9005200381c4000000d07540c05c2560000c030380051032001040807558000b03007d19000802c20f105404034040d19090410050001c9000002030000c0c03003007140c00e48140b56400100b0020607062140350351541d0800024800c1c0a40781c203101c2c0c1e40396100204503950710345091003410882d108505841c00e545495024a00d4650342d071803180040d402c05019164903014400140000800341d20081540d0400c50b1004600140f818102c40e0407600401030106 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 869275854 1250 869274604 869274607
    0xc1006060f0c1a0403091806031e0515061914030706021c030c030902031902120d2c060a0f0207050f1011190501020403061d1e12031509060303 63
    0x2c00250390b00402c1070349640c240c554008a6a21400d04a0f045002c030352010400721050800b90442480940000c81030301e0140c0001400f10000803980000100c160b10081c0580c3c100b4a03419804c1c1400b001c8a0b600908020324038040c00495010f0a408501554040d010f01c4100302d44000c2c00d81401e04c405002400c2074005410f00406540040900c030110703052440070103681d1000154154001d60007005c41c143c000c2c040350050400c0e484010504040d600e03040e44503c1031000511484100080d0f80e821007501a40c070400060084c001c05c1e0000b031203921017640180340c5d08105089a0301c0780009014140d000382d80d015a0b91300c03039070f0b406030038020341d0b0308940c1c024070508409561580701c2800003114003400340380581d0b4940d85071825a05210102002080f01d00400303011601380281500544196030080b50f0401200c2038180ca01e650740351414038810243e42041843c0624110404030207041035180030140e544188a111100040d9031003125101040d50110150210340d05043c9495940200d05030001c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 869277104 1250 869275854 869275877
    0x11503020c06070f03061a0306181e060a08120a030b09060a0e18100b0415061407211205060d0206030c0a050c070305010605181b0901050c1006060f 65
    0x8980b0b0b51002000c110a0104c02c008002c2d0040c46607210100a1801ca1220601c02214550115441c0c2c01a5902449514465070382014480f1a8480c180940d1001e00c1c0100f004460b030300402e00386000240f80380d900682600300042e035601d0500903007600003141c07810a5a5404a404050102e0b1488020305008899190810000d80c881945800c02c3c0ca0780300465811503501c07130444048410000381074401c28014054a2600000290080600d5440c2103c060000000601ca003858040ca07620451000036002030300c0084030b619840c018802070380a8502e4184a43c0165041d100d4a010b050351040020045507005d400031101d032242a4101a08a036910074600c0d281c1c0010310319000242c9160081c3d600020880d203554041c1c4c0451f10180ea003c400d803011a9070301e04140d80203202c80d202c0c1728058540244152101164066060303c0754090020b44100908805000c602c40d401c03407803c00d8140701081004404441c0f040020140a002c0818082034050030814010012907441d1502c02c1403000025a1b07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 869278354 1250 869277104 869277127
    0x11b050712050a02030114010f09110a270b120105091b0309070f03060e0c0102070305070603051306090c06020f03090609040e03120103050303090d0c020102030a08100b0406030501150302 82
    0xc080c221a1014448200320141d824400c0c01e10000200c002e40c99031030102c8041c822048031400c00d0482c0c040d07035090500c0750782d150144c0040d200703a09207000088a00f040130300d401d03d000705d510551700b4105500b980c8141c65008101741500c1d155411212024030041135078070000403144002405400c041e503444603181841064209000b512034025002c0c0c04020000480e20a070420403180104038111240000a6580c00c0600003440e100801c9401800748211082095000041c0e0350100c80e400402400d4642ca0404228001c02000e407448811052648032040810ba850084d000741304e008010103200b0360b1404001a10340307220200c9000e1150814001d0050760741d90403041c1e5064500503200400d40d02d209014450441c460b07400702e0204042703c00004401c0c41000400342d403140000c5800c5a181043c4210203031102c03040c1c00c9000340168010440c085506114080c00ca0304011806547e0801c644c0303816410520f83c016410440010303568200402000c144002c01c1d45101103c0e0030b045141c42486c0c0780 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 869279604 1250 869278354 869278363
    0x503031918050a110f0307171b060a030e1c030b120c0f06030c070209070512070512010918080408010b01200d0f050c030304060b01080708090705010f0203040f0f05011b05 75
    0x140901942c861303029422180c0c403108110302c400f0100400780c81c07115031196800d14128582805032801d43c840c050f1f44988542c40b201041c000c0c0c03407006206030306110200d82d0880192071552014800c60081d80062142218030705091581201c40d81c0340400e141c0c9101c010711000d034080c2213603040b02c8d0f800f5542c0030480d5182d1a4101314007103000d84000e40e482d554046c5442c858031503908002c2d0010951070401c070049034000040c10010807907100200d101c2d2101d801c1144c40c2d00840482e04070308500701c3e004009805007684a186007011110000030001c496440302040b0b03801c1a40082516511000c0c00861507900400e03138840e04c003503e5000c22200240341551540c079500320b150403090101119464000900690075940900e10180440ea03480c5440d15028010700f2241c40210b000c10b4000010501b420300942496204580420050140500e031000440b01220014442e00640c0001c100200340111480030000141c09101790046109103000001090300408410b255004203004900c43c000801c0800e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 869280854 1250 869279604 869279623
    0x101a0432040e070b0301060905100503060102030316030b1810120c14031204030f1101021504061107020402040b04080c0d030504051014030f0f070f0e09040609050303191805 76
    0x1c81c00100805a50102c0e4500300341c1e41c0104c202d490010000042d01c0d5803100305030b025154143c0b0b1099081c1e44111040ea0300b07000036a6441e0142c0c00920004035001d041451440e000681450040342100c1d444000caa58459114100b40c0f9000000e810000a1181c0803003190082c07540c0c0c41046c1d000c041d1611090000070007030094080b604280050100c60b40c0d410440320304001c424100b032566807503483c60080c21003901d00e04100c444a200440d140090760010410500e481da00543d210441d659540d00c00004224801c400514404140145c00160300e80d84040c00103400c403a200359036a03908200069180104030740b00d45109102020801380045d900806a40c1203501c107469120b41140a10320507180020203640d06c0b043c00300d02000700459100407400c0d260007581c0c46100801c00341c90701d02c8101c5800f5600e2002c18041a40c646640e5100e00b40102c0041c0d01501824001628240c0c55480c24119403085c0c03046141780b01c0800080c40060705510844482244103400c4500d038000365614561244c2224 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 869282104 1250 869280854 869280859
    0x309040e01022808011d28090803060a0b030c0d0b0d140c09100807060c0f1a04050c010c03090603021303080c0d0e0f0d0209101a0432 59
    0x18205054030580035010b60b5510004196240140c51008840b0307861074152002e04000a6400070002031000b64207a07408130084035104003c0520b40e1090701d905000c81a024050022031340342e420590010690b0300c80c014801d0301c1041081d41d2414440c0030032040201503002104003010420620141207100001c861106903040000b0406040303101c001030110410350800340c0b0180c1102341c0e014221001040040039001c0c110341055040e100d009401c200500503000308440c035400f40a050103554004c0c40c1c00013056100e4050145c0c00c02e0b541d603d4201d0614020140e00d0100b01c51800e1104100c3c041c003500b80b03001400e10348400011200e890062084515100b458281580019408251a03400c08884081c1d90005070391640c42004000003139940c0814000400010b0b440700701c40070685821010b00480c842c000303000c510382260640030812042e801601680124066540000f428080321100c0100409a148a50f0720f40e8a400395511422540d500706460030004190000c4016020003805000c00c90107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 869283354 1250 869282104 869282111
    0x215011206151d07090f2d050f0f030a080c01050403020f010b090f091507120b010219170c011505100206070c17071a010501110a1a0604090b130201030b010e03030904 73
    0x1c0c00781c240d070003c5c2da64000107005042e403200451f410307104801141a545c004240c1241102046011765a68000390003850b42c485c4901c0c1c40380585103050301c41246801d10003400d07a000740400740d44915550303105400714038899446204002c1415014040c1c03000f0007890600a01000f00410001504c01d80010306040d00f410382070340450004a030130001c000c60303050b0000881e541400d19440103400c04050b418402029414032032100d0442d40b0108030250740210160f01c0100070500365480007105091940c04048040b014449480808404d0140c150380031034441014010700d0800d001c0c41b504500400d440c10555209500740000305602c03c808aa034507803c04144800c8030061140142d803440307146005003030b240c0e011030342c0b1007400c03a2406454100c030001d8980a00d0000e55580c1c054489000340c50152803200c003543d4071125192489003890740680e0040000452400c2951966410101546c0a40c01003409450540455800d889840f8030703040d00742010b80c2091744100010303035284520303940140280c2d00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 869284604 1250 869283354 869283361
    0x5060d11040c111510060f080103120507230705060903060a05090f010207050106180615052b050a14190f18050f2a100215011206151d 59
    0x10400060f02ca88015600b40c80301100c0650394580070790710540d00c40905010701031001800798018484000200c4054031620f100e68a961203004c485804105508240042000b031140003407060b15018400c104290500c80381c0c0c00000c480b103464094180c00090103804100b01b200c506580004030a980100300201c0842d803550b40c403000f6828100c0c50000d00d0001d6001055070820000190040016903172141050719500822200c0360b804e4510034454100103910040d6015880340c07151005100c0304010a687c00300d10b50200b2a15a00c180d41c00440c00b81d82503945091200302e1055005400d1801d811081c18001810704500020704840c55071120554650341d0800303c0c14088007a0010544040f25221420080c0e015023059074030b455020148114a0080d5002c030400e0340285601501041c0c007001d0340120300b0501d4002d102162901d02c0000e81035115880204480e01e003c00001ea018010405501c0c10310306240c40c000080c0c40c140036110113400c0040009000644071582c001c001e103015101802050384 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 869285854 1250 869284604 869284607
    0x10020a090510030b0a0b0403020916050403120509100e1f1b0f02090109062d030b040f0c060905030706080c030609060d060c05070209060111101e02180405060d11040c 73
    0x88104c1141c0c0c1207840d5020004c0d030001440090b0003124020780d80b008503603860f01010b8060802030552900403a90500007480071070300d0482c90072040c038501d0400501d000400000a481a1a010300100c0010f0038900c280ca0b40d800d180d0030101ca8208010010000300c0c0d50b04030050070f510300d1000506810810042d80318180302510f0702c841406070300070f0a07060742d950f150400c000242c4058065120081c125021040040080d000444038518100c84403071455401c43c0e42d0340202100c060030039109407441c8001c0b040440c4401400d4402002c003601c0e0595070514003014582810602c2d44410207220000e01000018103105081703d0388050116103004455480400054164841c408050402d0380b03440d6800b11181d40240040940c0d6008a84032801903941a004461071030740c0e03454150040c5c03c2401070420800058110805141401001c407400d0400d00e40407808030380000c0b0008501048402140d80e04d0b04040c490320ba008601982c4100f084c908584421410818562082d8000c5a60f05d18000129 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 869287104 1250 869285854 869285861
    0x106050a0504120b060306220b0a090506130b0901091e1b06030203070305100302010f1101020c0d0519020303063316020301050105010e01021506041b0c030210020a09051003 76
    0x8103001c03e50329024440a00346220300043c2140d10a01a124840c080340754412070381e017007031071144c1e810743d8000c035060482d42c0b011a2910050106402580c46007100e0000038403c0c49603e100d42ca004806002e20b00311401c00035401030026003551800d925000b0800c0c086505c3c3d6515510003101cac000402030754106840e000c48980d058001000c03021220000c00300f0001d62580003036028901c070355014001a111040e81144140c400c5c40001e000c61000304806080c2d6020f2151111800094000141000700e224100e41c00e0144000d43e410000703000058000c12481c1c030384403a03500000948011811407030080080380000c0c03e441e500802202d292142980341e00070034643c411100170184242038580341c4840b5220305120800b00700320310035424940041000c1d40f0400520b0520310b0142d000b4444101e00a44014000c0e00c0071380815045500c0d500603200102490a80580c8042e803a80c03801c1141071a0b040007410041030103000c10126004100c54011564401909415540304a422407000b50310071009030000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 869288354 1250 869287104 869287109
    0x1f0806030a1b06110c09040318150302040303110f0613060f0f020705210406050f0702040504030f0909060f05090a0f09050d09050a1a090a0909050604020a1d0106050a0504 75
    0x1d002904200514101045031a00c08844039910384848000361403c0c0d617516540a401340f40e4008a02100007404280f0950341843c8404101c0480b080064881802406586804060101003500001d0400170542e000300c071501142e0001c000b42c140c55050040503500e41402511002604102d40d014a007031201364dc0c000e080ca11a0050204145001109040060740189400b03451703600621600078620f090018a098145c5d41d40a070051905042c4001039425800003d0341c6450b04005102c00c0c40142c644e071065034010360180d00c034988402280e800080c0301c0d41003904072014040c1404001c200e5000c03d092000c09075a81201e03210a1030f598403d00c039000780600045101040d040c401620709002c0c0104401051704e00550358042000c2d1501c1c00c0c000701c442c1c00d1090350510728201042e085503076507150207480181e000402000601fa625840c210585620b031105035501d801217400d1004510f008240c0c80001e0203140d01e1808404070003c070041051030140b02d05828080002180d81d240c900c9070085502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 869289604 1250 869288354 869288363
    0xd0b0117011d0a0e0606271e06030d051602040e01090c090e0313090902030a1514150f010c06060f2309090322030213020306010e1f0806030a 62
    0x680350b94031950603284030b1150380806248000740c0040703810404140a61024030412100810300c5890b1170050182800d0003103512041000803604030b10581608042840c018900f03241c0c2c4074049440001840c8071500041d020a1180d40203034045407150350070a0a460481754041d00810a000550020402410043c048900d10354130b00b040441c1040501680a8281d51107040b040104140a0008a55910820140751003414010504000d5051150086100b1610140c195050845255114403480c00200c00028031103803562500c0c003409040e848060341c400b540c0d4070400c0c03070804c1032404034100840c20f124590400000941c000c0512101e60010f034010040001e1041400d41d42d07019080101e5041600c130105512031025030a0f442c07500d1507006000741032840246250460154002090711040003a480c000c003100c20303000025a0729040e40c0c8003d020a60805070b80c9140200004003105100c50802d0f02ca0000421000101c03011059070000a000c14207048507242c07038030310000b0b14100c035001d8000d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 869290854 1250 869289604 869289647
    0x80d060e0403030912020303010819051e031e09010804020616141006140609062b1407080c030a0b010e0d03030902011b0b270723040605060d0b01 64
    0x402da40740d444403a580d8021200c44e40d06440700c020413a180c0c40288259945580f14440c04000b8810b0700d80200c00382c500c40c2d001c4502d5150800ba568401e010501d8960559410120307e03880701c0525020a01080400c0e2940c40d41b403d181c10001800482c0e002d08040d01580b40400c2000b00740095081032848184c20003603030141041a80e010a95030000c0ca1480c20b9034500b00600001d01c5d0b9080d8401d000300d540003d09445c00d02d4600c00034010b0503007207404800608669410071034001180c690b0080c1203502e0450001c1800207a05a08200301e4801074483d00401c0044420440b00080543c1a42c0d042441603c0100302404070000480d404085510a541e200c1c1c08001501c0801d5010b50000b0b4001c2d200703072180042d05039044d0406d0011807030310350041c080121043c0024843e41f00e6844944030150b00700d1a00d001050340d110402d282041e690010440d009407403400078850240380c10710840702c1400302c8060180038100300103d8414010450030300800ca445100300c41c1107078040c01c081c00c102441c000340035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 869292104 1250 869290854 869290861
    0xd0b0d1a06040e03090607110a0905011203110d02070504110f0d051617130201140c2107030e040203060607150209010f0507030e09040519061a030a0b0103080d060e 72
    0x35030144805441ea54440e91503c0b40599100c0c0000c41501d080715001083c003400d20720300c3d0b00d4058005c502492029408a1855808a85a086480344a010f4040703c0b40205502070240b6016250f407803c030030700c0407550344001c42101045500040306c805441d03060350080740c008403c0c59100d404e4011007405662a00d40410702a8020005600c454454080283d038460091100310b010344584400500300d082c00c80c1c1d8100012040382030000c034010040c0c4103240100300c80904540c0100c45402c100d08210b802d411132006644c08240200301d0301c040b503a540301040d10f040000e5402802201500700700c01d00454001c00060200d507140320070f0b2124142c0223640452004d80c01c1429400035400ba0310900c0c0420b028102034822144603206403510946d05849007084980b0a0f1b08004011000500c100c0300c030701c240000451948034400d18005c4482c0b19100c0407807103d03c140c40180182051110b0b040c000c0d800800c008010a0403000c659044a800803082d03640d500d00c00c0c001d40040e00490f005201c01061076400e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 869293354 1250 869292104 869292143
    0x10204060201090c06081e100b1b0d140714070b070c08070618140a1a0703080c07030801151b0309060206060405042105091315090903050d0b0d 63
    0x4a020b252240401034070b010b032220f00a0790040c109490311006000c1c5d1f04d0307404592910300000c55030803a80740e83d00d1404840ea40da0760000710380d12004480e0484829400062841601000120000e9982d810f00c40501b900c00f09980030580030b5810060700450394024212014002032001c1009065066503450796158035003424004003083c1c1c41001d0301ca10401c080081c0484c441c505016400c1700703d4802104151038007c4054410104150781548030400103000101c407a5000f4030002d00e00c1e00100001e480358860306001d481c5d00741c02001c0000b0300c14100a0b0400080c0e0064034181542c0c4000b00000c010788201404480c03841500c4000040c0e1180b0000740000c0c560880082da048030481e03400c450507680e17103201740301c2a50420f8400500c00c0800c1a01d001d80c08046d204c001c1448143d0340b41280c100340d1880700142e20840100810703041180e03a84210a0080d2031482000083d0203064418002d1035081d58000704076100b94100340240c580d0b901c01407515651203502e01c48040f500001d80c449440c151000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 869294604 1250 869293354 869293361
    0xd0510060e1315060c021003050106080105060a170a0b0a05010903021003090507080610092a050307030b090123030a050d1d12010f0f09020a031b0302060313121b1211010204060201 79
    0x60344681c200343e47d10000340b031003402001e0507a805c940d1210441d9180c0401d01c06603070026161442031000489642e414202c2d00c1705418451040074101081002c100700c02d0014400301604480c0c10440ba003c81030000d602d800f2031480c4036103407918000560007124103003113040207100d400c5029039004240a010481400c2e000d4001980c0320810100024202e80107a0200341c043c60302d038107501c2035800508500403802100690341c048498100407601d401c0e607000181031094240c200d0030010808400547c40c0740f5007602164000c82c13081c0c00074108400d9503100c803035448a49001d00c5080005859503501040c0c01a82e8800c80d485d0054000c080340420385841c0c40c060131240004101480c41d00c0c030aca10041100b8080e0784240341d0058424156141140c41742e80e81c0070905c3c20803900c40203440f00300100503283c281c019441207690540e003240403030041c54922001178003400d81500f003003034104d680080b41840724200b000f41584510f08210070303169200c0944001c001c078540400c0a51000c0390008600f6010341 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 869295854 1250 869294604 869294627
    0x6110a0e01121404060911121c09031a042d1b060918061a07110d08090906013b0612070c050a0b0406020d0510060e131506 54
    0x2c07224001c25060030210401c41e40c0aa00d046502c04000c0701040110b807040d0310114009000308034040302d4905072030202e0b50703116506c2d001c20041da00046a00080740426106850035031014948400c0e9140340d0344542101c0300302050354000d0784020001003020001c41e0f01e4a440d40072183d100d201c0b0142c0801c0350b0392200789996102500d0081c40304003000f010311a13442c4240103580046d2102c0c0e00407030901202962544490496940c100c0d90707800b000c41c1595040311680b0b0040c103140c4000390741d81c405107008464140c0400d0141d000744900518040055443d10030394000c3c50040d158035041e66142c0780100c9004e4a003421120031034103030001c40d44170319084003041600c611000f20701c1103000b1401c40501a440c8203466100d802018a03c021442661140c5c0007240410300034402c4444000c140c0c4c0b079a42e2407117000e072021600c05d0382c0061807202c02a110701a081c1d001580b01d50803c462803406201505100c05618036911030107080b403480702015074036442000f0751196219012002c03500c52501401c0019030f007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 869297104 1250 869295854 869295857
    0x130e0613150b09150406120c150302090a060e0d0f0c081e0a021210150f050303160809060c06040b0a11070332180a08030a05090d06110a0e01 62
    0x104400111a02180101040b0b020003810000e0b255840001d401c07900b00341c84030344940c07181c2c84410029400340c41c030350f00703240b4607010303000c4805021701d0005400c254070342c0c0030340c09014035005201140c02c2c1d40e21058403104541c1d050030204000350407000003034a5440d00c0d41c1d004015601e07802d10a4184110f5060700b200b51001d42085480040c0e501e01104c00c1064030070031031501c0381c0c05a120070300141130520120092400304812a401d15007001134040c240c45060007100c2191088050401810348401c5d81e1400421003500a180b80040340f400114140c10401d101030002c090002d0450615120102214070620001c029284141494a000c0801e030b001500c0c501078072030a003000c1440c40a0800211900184d26403210040d500d40c0840c66440c89111401c00302005c05180000042240342c0340c001e00d030090b440d642c2c0d240003117555000c0081a034442c3d004802954020320001344c695410108989000104544109001e000c51420380c000c1c24801c2c0109aa0540101d440700883e03400c4024101c1c0040e09 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 869298354 1250 869297104 869297123
    0x180d110907030204051f020a050d0e0a050a0b3403020105041104151502031b0c0a080616110c1c03031107020d02060d061e0914010f05130e0613 63
    0x1c6031000c60590040d40601e5501c103070507004a0040d076110944403131700800701d4010349192400584600b402d00d82a800003101152000110ba01645030804100006c0c0c081194208225070620480b44540d01400110300030760090f1000d92420584c04417000044054000302103000403510340340080c040d00c001d035800c940074035007001407069920b424014500100d05901e0200c1c01c0900d404880450050140c102000b035002c208803a090088d40004400d2915212a00600c00c624030754081c0200000d46a02c03110722600b2400c288800c140a00c446207802840c42e18040c004100500507050a1454822100e075111051929551501a0402041440a0090703c0403c480c0070010142c440901c10000025841040170040c0c0b070041c6441d0b001f03810703038072502c04001030940d4454074011420004110405003540d500401000150582c2c081c1c81074150062003440c00d0f65240c801e070080f40030228001c451141d4905025440d640a2a40c80803c056400000700c1f480ba0901040c017400400743e995080e26032088 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 869299604 1250 869298354 869298361
    0x6021812031b0d0c0b131e0b06011e1d0414071101110313080702120f0d030603020f010e030a0503031f06030c0206010e0c0904060801020909071d06180d1109 69
    0x80114043d0080d5005460b07a5581d402c259440800508008110301300c90b0301003024890100741c429450f1103d082a1101a0480da40d03141000c03040500c004185038108401706c2c0d801103144940341e0402c40304c290141001c078515604407041d0b0001420725942345412925005044280744000b00886001d44402c0d1a0392500c40c41c1841403500b40c0c1c5d87c56070103405503c410000700e40644200c1c0c4003082982e0250010740e0400100741d00150710409028462442580311002c40700c4035903418807844421700300070f060801c90355146601258104c41d000381414103100802060340901e860902c21800002e5100341503d6591801c0c2c44121040102c3c0302000c000030510010100f80035000f407003a5101c4030300d260001c107003da1810032084004c94009103035682c886805d0140300182d40b102e0094501411807a0009608c410a0006008105000800354000c100c095252800d0110b801798042c0c40d006800c0c2c514654a8084a01c1c0c040703a058200090798001c5040c40c1c40c44240186a1440d0108481c101e81c200302f540c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 869300854 1250 869299604 869299657
    0x61504021615140f071e2d0206060406031505150604080736090606120f111903080a05090901060804020102121e07020f060304031709030a0c0602181203 67
    0x4801c4540c680490492540c45105c441d81540760300d8100a41d20f0440000c48102482107c8081c6141194540f11a10445458040d40500484e60b001d001620108046031450301d904a403500e0b40c888c00e180e403558903070100b5040c411031482000800c0e405021070307a41c1c503034407190716540c1d42940c40780c001c2c82e1601a0600411450071228200e01d00c14a1814044400d01c4580410040030b441c0000c0700c45941e901000a03042e103400400f4120f240c0030b81d415490722099818a206218002c180c000e00c035035240300382d0448014040000d00c040d01e801488540d12043c4010098500348140002544e122240c4070000650690020500303100301e100303030f0a0f00e6120307049071001d0101c0c0c0100075a81c0841d5a81c0c90020418054800107071480b5800288044000c3d041003000c51307990342c0140e5044e00000c981e040f04150341c6946071005500300340101e0040d40307014a0b800009180008c4103030014002600020501e9802e00c03c1c202e40c82c1c1602c80144030701040c0c801222065980e0344101e041e843c8001c410290040e048 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 869302104 1250 869300854 869300881
    0xa060509040b160e10110616080103030503041106040909051c021209060f1303121e03020c0309040e030a0e120a14100f0605010e0306150402161514 65
    0x41d580310341400340d0380d11041c0c0300941615041c10640704001d1840003a151650f140c581d50701c2c400203140c407000c000b00248031b189418108001c00c5401001b0003a0f4145241c036500800c0e80381100d070103260441d101e481da40380c0102c0c54410451002c0e48180c0204001c1405c00056000315080c92003401124036420001c018208890300c40f1500101603003000b0102c0310070010b848020700f203881c0b0003410709140030035801600280b500040348140c82d042101c0d100348204601900000c241d038500b41485610072800e40200c402070000890010209074000c220155628000c000395030001030020002d00c41884400d8219959410020a540010300d61550209403801e2298110392200c42c020042d009000880e1100802c1d9414140c40d2400d61251912141504041d0700c00c0001460302d03401d010804918000004054411844501c1d10a421603000d020407000180e000c5031404005440242c1c8617210980ca03040d44043c940c030301a2801e05d030f100901400c0303045603001c245001c5902030105110303110700041c0c4405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 869303354 1250 869302104 869302111
    0xe070c050d0e13051317030c0904020a120f09030816090b03060d050d0e04110a020c0d021c08030412050c0a060203091c08070206010504111c06050a0e0a060509 70
    0x4541044211082062041c020b88900d588043d03d148540c000c200340803821038070700703d510f801400c410060724402c004942d4118010b0340604c0d14058254207007007090784000e104401440380302d01c2d03000803080b40481c00f820300000940702c4041d040000200ca80c8030311002d0410380d041180019810400200320220741800309104020a90740c5030089410207805150302c2d40064842e0b580a0544103581c00000c0d401c0000c030000646c1a9101403d03a90b040050000341d1b0094807010b022007078144447c42100e5030016082c003694404480d000308011907400401e03d480c0f00c0b480c1e50104910342e10751200901940c2002940518403940b1170140070400d1820441e80d41c0190010410540c000002e2a00810309540103150000a03080c25900c030080300d000501002411080b64401044829042200c401d406000031070045c601a103091008000c0806841d40c42e1250201240d10166280c03c01d170b0b0314603902c0d0301c08405440041c081c02011a16014004a101030496144030320500700a4041010704103d03004501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 869304604 1250 869303354 869303363
    0x140f010914040b0d0501021908060109050f0906010c060c0e2404060c11040920090105030d051b0703060e06090d17070c050a06062108121801090c0e070c 67
    0x1c003800d01004120251100c4100d440d4401d6500000a011800030f10040401d407802c03264400100007030a070003412258000308643d060014801003040f00707071150110490305c11070444540080c0d9490000503a0b160003984000307840303e4641286520001d4000c000d5405840c011140790f1019841c12824440119040c241091903060031720003000307002c1c0074048209101741304502001550341da1201260865000c000d056401c0340d9041c00501a6407034194881c148108107841e03030500b960521003c40c1d40c800b00015000204080059072003603501300000181c0442d94a80180e8040716aa401c05d000680800201803609000d04000300340c3c01480041e290280d2090764131102c40c1d4050b031000070000f8100007804001808031442c0307100b00091041c004400380b64414003000400f40d080c104c03a03140d0625201450f00d480e507092100d580101d44604196003076050311544000c100e0340c0e001540c00320045142c0e071201c407a41c2003219540130007240e10303c2d0005070ba058250010644d40c482c0c108a490705402c200151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 869305854 1250 869304604 869304629
    0x90506030c15090f0d0807080310050f1f03060503070806070f18060c060f0c030905060702071802030a0603020d050703150203010518040323070b0a020c060a09030c0b01140f0109 78
    0x18031410810f00c20811020300500d820031914083c0c40b46c001a500c402801c0301c40030f07000010041800781c540d40c200040c020a8802c844403540c010301045c006021203103202d90340301c4142101501948281c0000018100150940769001d079a1001c82c1d81e6800700703640c42c00100b02d00300f481100e110301c11030300b1008a600316220105050300e00075065038954801002030b50825180c50a9404030340c2c036401901c04210196074005540d2299003007841c20028044c00601c01c5400512041020400402513083c02203000d11005940b5100c4003c004000c01165000a40010894545c081845000304044003128080c5000105080402c0648022407201b4040d0503840181203840c0140480041d0f0400e038071078400d0900c3c1a01003408100f4035050b401d4000302013040e81e00018424200505007202d5074002d12a1101135003030280e030f00076040d16048020007004001d6549d04160023494400c2569405541e0040803084043d61504010051820300031400381c010a00c44110034030951140008e10f040307840c2c80b00c04a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 869307104 1250 869305854 869305867
    0xc0c02150a03020d020a08040525170f01110a0206010f060c12120204080705012c0603091f06030203010506010206060a140f15070323030a0203061801090506030c15 72
    0x1507002508200d0415a080c482419441c1c02031004140d144010b481d403007807924141c9821450046c00c0082220440c104410310072501003d21419400e9505801c030890349003c0700c66036186088840020f0400c01c1d82001140311f4030100f000010444511180d00341d404607038035500d05802d10f0400380f00e40c00004908080030004600312080310308071004240303031012892400100c031406a8115803c844146d4001d0081000301e0368100789084045a030f1072884120701c4401c04592007032040d61f0400c1c1d9005040000c001805210300780540ea00c11084401c001151407152040c141c000d25050004034020340c40c180c0414142c1d0b000062441c030826005103040d243d44d04080c0d039040c0082c0e038078680300d8004481d04071080c1c02c0c2e0b40e0041d0214000d003400f00032a44490041c14020442c00e44c1c03000d400002c2100c03584201c02515850222944100713448005a940d4036504080340700b11814000c4402d183c21000004924201c03181c000074090001102140d6110007600200300b00141030b00901680c5000030010b2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 869308354 1250 869307104 869307139
    0x6080c01052203081b15160c080d05100801052502071d07080c360d060b0909030901080103120225052418310c0c02 51
    0xa007000d03148000000b44450401001407601a41a007044500c0180030484055030350440300b03400a0040704a000b071895411907100c4e080c0d0b800019002a56032920080302c4035105000f40e041d10400d50f4440501c9580e108180da228005020a41740e00040807210240010803420501500b40603481d00c007001c16a54401030075480c0c80d801401c8070981540148a80003698941182c200208043c1c4031840c0180ca00d02441c00800c409002070921002e0768003848030555241c05074903100c50503089241c01520b03070726014220081d96014031080d0340d4000c1e11041084104003070f40c4c0003020310794000c3d41e2058031600e50203070064903070042010715400a0341e985c0041010641820304040d00070400e0060b1203038640441604040000c08180d10001080d40d0582044a0300300350510721034a644050b03036800031403030b80315004001e48610381c910b00c0c1d0100c007604601e0151796681c40c044541d40c10302c85815481d0180c81440e03656014054441440c1920f0408a0f0700103078090410a1803585e40205003580e000b105515 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 869309604 1250 869308354 869308357
    0x6060e030d1206080304091406030a080f2503050c0705100c02040b04020c010219090e06100f0e060a020f010f050906010323010501061d03070e0105040c0e030d0906080a06080c0105 79
    0x94038164141c840d00002203003a0240001c1001e000044004034412120700608c04803503901402d2540250b01103500c46021840c8141907070300741005c4140881e5508000b444943e8258900300d00702a80346039101a682c10107400400810054445c81c0680344016660000c00c82c1c524900391400f804184900542d10041c23820740d0080c420110010401401e051385010300780d007240c02040c900c041141d000c450203c1c0c1c0c076030040c4142000341b40000324052a487d0401c04100c001c1c0c4030500200500019408040d40c290081c03202c03103c0c5040180c14540c1b1084e07101070017556510404588030b12940303404000590012a8091948124030741c9009018507480c5540701c40e401c10301380948141901c26991a459524406e010700b034000c0c0882d40e290540a280780411a41e120102c044191295000040410058400ba4a014111003084400003052444440e00341c6000b004141440e0703240c001c0c1c85c0d46000c002d80040103581a40c000b42d90340002c694440030700f1001c0320014054010a075000c4500030059620074030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 869310854 1250 869309604 869309627
    0x10c02070605280e0901120f02010c031b0c06090501050301081e19050606120c0a03030e030c0a0902030f070f050d181a01030308070c03080c030417030903070606060e030d 75
    0x10078011444000c480ca03100c01041266400002500c507058044d09280c440b806501410580d00307010060a440d03528101d401c030859a0090610041c680c6013001e06004504000044464000303002da000303801e18004100203404e002d002c0100f2030200700455954420300c140e0381601c4402c001406003011440e8003905150302c4000c80f90951283c0c131406171a80204900c90300500b407054004000c2c605040c0c0402094503c55a00200e465100b040443d030f0319621080807000320394260902454106003040881e0a15844c07401c100d400800524001031058071950003180700300300c041001031562b151980e0842e007006000703545900142052042e02d010760019030041e0411181199201c1403007040f991000881d441d54400c11003c0d55646004005041d0000f4901e030384031005150004000d0b00b01d9602405c189c0014101549182c00840010100310b1100424009807a020b0151922071070030110081d600d0303001c05000c0b103c00341040e000050aa01491510b8411600140500250003050508603400c000b0407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 869312104 1250 869310854 869310877
    0x16030201170c0423010215060d060c0e120303010510110601090c1e08040501051b04030f080708031003171801030f0906050703290a0b070305040f0e0612010c02070605 73
    0x1040b00085130a403c071000460040111071003c00407078420006424542c070303801c00165a460550070041c0640e01c008003010f40c2e503400400080c904458560480d510b14a07440450381200100f280c000082e0000009141207038001c4a209605600310981104c0110f20708200907215401a001441800c405421202d6401d40604d002c500b0700514003c840041c0505131310410204400100380810300c02d0a009965201c00c015000c01c1d802100c80310415414400d41c800a4001d5150385080800c10800d601140c0d001034000000c141c690130b00415a0170a05400c2c40304032100b0012046460740e1503034440c00d88202118103249160006e02c404010b4005e4001291a90f0002da0345280040001b9070512400d801418650780008203d024007030f00c0d02403451200c0320355843d250385048449960391945d00010984401d2003640d178460107a032500781d4003801960402c01007424400c10202c0d11081505c442403240a04072440008060b03000c408074200c81c40c2c2441100140c11244050041c24000e1008269404a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 869313354 1250 869312104 869312107
    0xb0406031e050a08030a0603031e09061407060e031315081612050c09040605060906040302060702060c030c030a030f0b010212160c0e060a051c022e1116030201170c 72
    0x140d54403400503a201b107031310030100c0f5600c240c14418035030310000c940c03000028001351001d440442400a8600d500c0e91140c482048014070155441001032010389030220743c401821304c004e012802e00c00b0f03160b4200340b401a13050210340c0c80028000300c0182ca0400c01190035200e040654881240c0c000d00ea8a02003c54030030b2100d1a503403201c1c018003d1050510852000342c1251b2a510b03000200300c00c1d02c000341c0c0f1052003510284002c081e10b6655000303c0d4120799046800d95580e05d614800b0074014010345036030440c94040480d448120050110060122544039907007004804a4241d062044400b403006082c01a03004545903007218402d2001030080030200341009070b1101c02c65548607059075281c0c100f10307113143c04a418000c041c01c00000b951f0240804640502c10400c179403040021003d64014003034071078181040507100d0100c400c11101e14910000c01500703a00020b00d03001429040817041200903074030658600d400c802e48000042016698141d40c1d8009d640c81107204a04603010140001100590 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 869314604 1250 869313354 869313373
    0xc120703110309160605120a0e0a05150402030c0406030f060506060906040609080f0604030815130e031308060115050c0f1e0609030315060a0921060b0406031e05 71
    0x8400000d14401d43d02c2000800b00c501801425000c903540540c86041400f00611404500712010041c0c030b07501004034080010903501c5528058903020009002a01900901e4003002c206003882a00300d20440c000c0d0b0880c3d0700b800d0107105100885a80b0b04c400341545018100e0300000a42d160000e9401540003841c060408191500180080d405948a903011030b100d4482040100001e02c044404900c0d030401401e103521309620003a00b68140104103112400040f00d50045650f500341c0d9201e000100b10f4410400f030003042c90702036660f5200e2041000b00e541440c1e400a00a500000c40c03505a448088050243c103621a90a5499802c07821548400c0d000740c1171a802240e2080000c000780052184803011100703e8080d5190415502405250b01900200200b20706c12014004000c0105400d41d500c41d40d4003c0401d040743d403810990484104000e41100c240c03402c5800707499075100c8900820303080210f50154010441240c141c1e00c4000c041c151800b40c0c1480214034040400d46a9000d44165080d240e03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 869315854 1250 869314604 869314631
    0x80a0306170a0212030a0509011b0c06080f18030a0c0804082d0c0a12080d1b02100204050918150c030f01060305091011090901080714090c120703 64
    0x40661160055a02c01c641000a61800c4118010a003036060080c601d4507000b80c400a180744503050007181880214014007105d80c401101e100c50698000502444160f118140113118200a0751494040c03e01140480d0710200c0c011150b4198401410040d49481c3c42d81c02c0a40d14070300394820694484001340030004201100b80060403c0340380c4070f4545003001f0344850044517101009030307400225601c010007040c2103448982054081c2d400e8044030700306034880c51030b04000d42d11030082c0b14001039040403400d400c031010000e07030401c1e0700c50f00703070241c0d041c82960303c17000022405244510755001080c85c0110317140031160103101d068801e4820603035803000d00d03442c0403802650081d42d6034414024000b0402c40a030b03050b00c0015001d41590b18003400a4280080925912440325050020017541c41d1290301c20350302103804031200100080d10750442980d59540f10303030f2621001d10035601461100c19521503d49003103200e0380e03c56204440f9250900d40c460a40300050f00f0014227810500d5a01c03800c0b024000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 869317104 1250 869315854 869315879
    0x4050409151d0601030305090f06181c0c09050702070308040608010612060501170a1d07050a06090f090e16030b1f0503030a1b231902010c080a0306 65
    0xc0c0919660341280088544690480d041c01c940b070340000751000808400e0b68000304601d0b044a07050f10f44240c4480207000060300c011070792500d841e40078900284042007413840b09050060b99074200c40d0300707070b500f41200103c10741d4120b00c9000600c000c5001c0002c0c0100c11040c1e1206402040510480d41515100d0791000d20720750081d0400d5012078040d40040080316441100c00104000344842031151a28140019101c0503a042c0b200030030304c180000242002c11a503220700b0034490303403e03000303003580d01003050641d182e050500035940601c2e454000420366a0003800e440084940c068013184101d413400717901d680200700000214003030f4010a01c00218440b148908000034502450600381d443c1040c03400380e048000e0400117402c1844059508201c1a5008816035103d4151418502c5900c003183c801402c1c0065091401040380b040003400341842c4481450504c06118003600b110519044d0070b0301507110748614080240010315401c010400540550b028017484000d909011954540352411003a10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 869318354 1250 869317104 869317121
    0xd20060403051005100b190315060908010f0b0904080304080d050709090b01030e210d020703020c0315040f02060a05160302010c02010b040204030803010510050c0a0803181609050c040504 82
    0x70b80c1e0120a81200f007608501c42d0a400100c1201040082881c0c03580b100c543e4000c03498501c1d101d011134010140554040c0e0000279075070300e8101001603903a440e0031000c0d0507540f941c01110160361900703201c50004441c6100320320f00f00400400702e8441d80d4a039600e510180d8030043c070440722180103104105012901d4040d9a005620903180d04449a0034198003408035400c2581d6903042505140e40c1c0c40381a007000c90070700080400000300300101d0030381c0003405105106208070101c00d02e10000c1e000b001d255010038012400c000440c140c1d0040e0700b60350300300d1003a1101070303502520560b0318003495030062070810009c007480c10345e60800030304002940e100b450506810210960250351550941c08140d642031142102c80c00781100c08504060540d1a1102c0c64001402a01d002c0d0700b080221a81c40d80c0940d042e6907000100108440d1201c42900c3c2c5030406400a541e10814102c16204018a1250128410015040d049100050149040c103228080c00000d02100840c4508000c0403400780c0365400341044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 869319604 1250 869318354 869318363
    0x2030c10111b090c031b030604060e0a0f06080d12051e1504050108010218040e070b0f042405030411280e0601030504020a1206020d180209150d20060403 67
    0x6040302d58818410307100340040c05551030100410401402401440707045604c0f03214851041d48030381d100b5000c07a00514894002d641d46080020810180ca40c90390048800d916004400384a031302d0791010450f9446035034000d00b070042005603440019000040d0311059000e1200f4804d1445a00000a1413030700e48030503951201e180031101941c4c0c66a003024020f00e801000030100840c40c0c564082c8104a0303140c1401070032481142c0700c2e031401c10701d00000c000d050041c00042c0ca9455840d4491581003806030b01c58441d803c15020549622142e801e03104c0c40d1031070045c0321030b11803901d0340c1e030307695602d2821000709040658411143d0406180210403c02c148612030034614803200c910341003401004d00301c10000c014504040c03c1608000060301c03a00700c0702d0b00700c81041e108100e1000071454108042c0c0207084100c40031a2401d00c403000c1c002103070404140074a00956070707504c0c551240c2c0307a080501a041c5283c03903000803684913002c0002c0c007980006c1e007a01c1c10340d210300c2e191018100e000801c186e0040e8070649 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 869320854 1250 869319604 869319643
    0x6050a061a0c01050c041217220311030c0f0d02150f0c1b010c021908010c0306030b0604060f26060f06190e0406110c010e070603140402030c1011 64
    0x81d08800074828180c200200750134490529181c40c0b01d0075044107c0c0140201030740d140004015101d5401d80540c0e424991181c140c016000810511448600d0140300582c0d00010b4565500300c681008100c0142e20007020b44105840200d40d4180400c1d683c02010480c1c020540070020b040790300103440504500a8280c030510390394400107424500c0c1c01c1001540c11542424400d82403c030b81c5e0040202e40b107855050301c0000e19101a100340100c81c00e0301d6031141007a9420840d00e041001c0d810f9000c4019248504e40280003500e13071714240002c6641b40d02640684000ba01c3d418440a010594846140fa201e100140c514400c28044141050020f950041c1030440c40c400b4004140f5040c3c441a40d400300e4441224000341c07a00c0340314001c00002403c0903001c00d540c2e01a1850b840a12022641c4419080d0001c0c00b0031030450340b07290f5544c0c006105030400249051001c80702c02172038955080c01150001c000301503010490040100788090109804140410080240f4821809001469181710319940c0003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 869322104 1250 869320854 869320867
    0x4050c100815040513020909032503080106110703030e1c0c031a070e060a170f190e030f1836040209041205090d08090301240306050a061a 61
    0xc9014000015001d10544c10302d4108518080b1551130034804540450b6455201e84501144a055100c0c2d0081090030500c0c4014540d08208a01078444030f071032103030341c880d501a80d8802044036602c191180540c400c3d0804401000480d1091503105503107034000303141440030610000c004034071540c5020b048510b115a0401003060202c074405842450604403501d179282d01e4041c5000b040f0000100c0c0b198032070700001c52504000c13442a071444503020742c80c2030030340b6030750070304090f544058001291090310001810984a40f28107190155a400400600045003001c960f40520200ca812071203a24120004c0e8640250301591130800b00103641c1d5180030001c8071420301b6450840c0c00c4546511b0b5a210602c400c0c00d100040c0c803100c40c231580c081e4000c0d200c08d4079800115130848041c402c2e4502c080e8881c400211a40c140040e0030010300540108800810515038042519100d183c00c0c0c0300300140c1c0c0f030079660041000c00c426800c030561191001030001034440d20b411031040000b068a40c030803150200452030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 869323354 1250 869322104 869322121
    0xe18030f0c0f0d230c160909060510120f14060c1315080112050c1906080f01050607150906020409320a111908040312110a0804050c1008 60
    0x100d83d0f0402c600c2d0140809801c80a9030b4001c0825808880d907550001502a1041c841808141c03051081914109030181e994000344e0041d089811050303c00501d840c011030007810f0001c105400b11a54150403815100d62a00c070000c03d2004624240c80010200301d080c00302080c140a00c92154400580c010f4840840c0c0030381555601c1c0c0c0d60011045550302c45080b0350590340085045044030641c400200350503003245091420181300c0780034503401000395100841810b640780f030084199101b0380c0d500b0115903520722702486441001c0c4901500040104000c0000c200d0344810741103105104030000c103030445c0c00d03681c01c000c07648a584000156035640070940c52007116860304d00440e42c419940340d401c100014801b01154100585010070307030b40e915042e00c000c0030361750402c2c0c4040c1c1d036400c94100300260044401900148e0101d40407800540d1400001c903801405128040008000111042c00c1400119060301c0714100904151610f00c281d28003104180e96a80004243c4909a0343c3c1c14a1424034030703e03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 869324604 1250 869323354 869323363
    0x30702070b03010608060607060f1e0f051b0c07030f0b19090317090c120a140f06010302010e13020a170702150c070f2310060e18030f0c0f 61
    0x201c4010362070100010003489510800341c42d04008211039141d558541807605000919030b828162001c1c0d42800842d45200040c2d0078442c0030140f444400f8402040d4000403a421558100d51030b409000203500025004088880601005100300c0c040301e0400707492361074031240c41e804001c0403038120100c041081050480d4401e01c55403079404e02c80c144042103641d0b8001e00800e9040b9000c0b4024841c00d030005800c440c0c1040301040d04403002c1c0c410420454600e0802d82c48500c0c290003a140c140480361000c641d07450008940c01055400c074050300030381e421540115036418002d0003d41e400325a030480050a41e80c14070017001610855160312100101e54400e40c030b20800300a02142c15500f000030303a008010000101c0580c0801030402403a80e0701c1592030103d03075881203800054000815500b444030241c0c04240e401c5161418201154800840070a4020a9032000e004d204240131111011402040c0f42100030440340030000282c904142e50f54110300b1403600700e09540d01c205d501010342c222005a0500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 869325854 1250 869324604 869324609
    0x60209060423010f0516080d02070c0e010f0b0714010f1d0c01050306010c06050a0e0f070311190501032a0903022e05031b0d091a04050705040c02010905070b03070207 73
    0x3800656101e4410b8082e08901428040314914114202c03011b042010742c00840b8000c0c10740b003504549485460600e82c1c080355280c084c0c0143c0803000702c0041040680c0a440748100c8580d080e8480c44c100d0195146514a41e01d000c03040c03000d40d250700ca0351182c0c9207d406038500164170100302c04141c8c40d200c6825880c2142c0801d0303d41c1400030400038402141d07071000d00964100d070049004a840d484402c0f004000341504100d4100030b0103100c41d0303004c119201058040440f03000c5c00c2c106058400b29010002c00c1e00344414000c005281d0240100300f076502075044101b0a015640480f8295103160080300f0b0310007481c200c49070001d0700c05c01c814411454402d15004040422031038000d40c0c46144d045d50307290781c0d0172035844030305004010001078030f20b0100841840e90418802d0303d25442d000c00d500c145001e00a6140c0440c0c000d041e085001e4103940c12108420320541c0c1240c000c2106a1604040c44000e04024598100319502e844070800840d904004100c000c02e9100c540300e1750392a01c0c0700300904000309038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 869327104 1250 869325854 869325857
    0x204050406141023090f0604152304230909030a032904050c0c0a0b0601090801090b0118020405060c030a0f091a0a03091a04150c05070f06020906042301 67
    0x50400c005081a4100c65100141400c001d190f0311200300c400580c101c603486d488258403041c005004508540d40c64800c6111510540780d8001e5050058052031582168802455081d4000c1c07000f00200c0d4006103400d441410341d100d08034498690900403d02c030f203804942c490303100d900002d100894168944101e889a0046400504140342c100154107088840f076010607100d82e03241d90100703030030303c801d1421103070440740b1041110f0440c006071502d51564002218214040780c07140740009204031040c0039420f4070a91010310030406a003404e00c0100302e060044040a00b2503402d20010030315455260007401d00d41410002035488008215004000241002c1f42c18100189030108120741e00241c145029041c480c02e0940703031140b403042c004600819507040060001d807078042070501c019030400109400b4034016241c001c401542a407680058079941e84000d000a001000803902190b411034064500300d00c034000c09850703d0345610020307010b5009900079040d40808500300c2c03a40c0580a524406617180c0a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 869328354 1250 869327104 869327117
    0x40906020d1b1409330a03090606120f0b0702031605061005040e0303040611120117100e15100e0702030a091e09020901030905060c07030207081b120102040504061410 73
    0x300c40c08036000c000161201c40908801e041100c0c111750b2034202400428040003c3d903501c5102c500300c0200079104003075042e20709524200300802e42c004250100380d1440d03001420527001c50324990310200030940c020041800c60100f8021b801d241d0640c003c0c00b22501d07005c1d1009165505003454090902115076204521071440c00c1c007910a0180003109403075105400010005500c840300504107920710501081c20545d403141c0e40003044888601d290324084848100803604a00701314210882100c4440d1030380c40080c1c0c00641044550391a56080d15803210114180000315542e403280480240800d45440d03015030408105090200c1c0d02010340c00003000d0048070904d4080c1104210181c0528600072014000d4000400c004140d0080d0008810130350301904480e8145040030241009030051030301180103010340c8600040c3c0d60400940c00c020058000d50f404070162085041060a140800845002c0d540034440000d0341d07074640c8120002810202c0c40e05814590500030061349502e000a90414002d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 869329604 1250 869328354 869328367
    0x40204030c03141f050106080708060108060f0f060d200f090603040204140c0c0c030303011d062206060f03090f060e070308031906060206070c02040906020d1b14 71
    0xa000c410440e500814441c80049103820321504251414504d0650b400b8101e6002c141c0440d00e030f2000781201c500f60fa0394149611400c03c222241c82c002c0c1d491500250790600411824a0310822045a840e00200894140301e025030124101c0d40001c500d00361140c0d82c0f003c0d4044084403120222201e60086540d00e803400344644109040750203070900c0c00b409094084001001c540b9642d010014800a044124480c0d240c4420664925484200c0e807000074090b441e805040c5d410b000081c0e0b07040c0c451000c000302c1480351060b11100d03000c200421203503200351000c10009529020017441003c207056100082415814120050554026070340241e04062604c171642c00070030300182081c01e244c0d07406140408c045020070000c40c40c0c1807098202070300030341c0004140030004039420500c100004070040c003800703403e40c1d07030009903280d807001c60780c00d004240707414008001440e20f5444807917407900c601001800d03c165442503804843c0e40300391041101810322034185a0075000b1041004440f00301c01524503001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 869330854 1250 869329604 869329613
    0x9030801080d0c0318170a061503051c0309020a060807080c07052a1323040203033f06030106090501060f050c0309190e0f01030f1e1e0b010504020403 66
    0x10203c440103070400981500741d044410b10350305070320000e080d03800c940c017180011100c80e19215801404112103640c980050195400c0b0325418a8048a8002000c3d00350032184800101044056800213400c26646042000044c1d48882c1008060902540d60484ca40b03003245025000000283c070ba0b14040f48103000200024200090981a0301c02003c2c0e5201000300c40360601e0101c20042e004254002c2c542d1003482c82d03c4403c2e0303100e0103255166144050741541d05000100d0010010389019405402c00c0011510003003610300d40f400301c0d10129141e02d0304180d0340c1e210b1054101269002c1c0d4015860f01c410301540d85024001d00b0040c1c0740f10003040250303524010f4007810b5490008050001c0c01808a0215a413100a10980d50300c004042c0008081c20030142480c8862071203406002611a01200840d0040480c200d040d416070340d02841007009521a501c41030b6002640f5501012002c40b00002000040c040140301e4401d00341c118080000181c44c3e2410f000004016000340d40100c0c414001040400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 869332104 1250 869330854 869330867
    0x60703050c04121505092505030a02010507140106030b01082413060f0f020c12070c05040216020a090218120d2706020a0b07031401090b030102070b0a09030801080d 72
    0x840600d00b10f035894050300e242c06540e4a00e0b0000309010645804104403090030f000c19568a51030001c0c3e02c00d441864107502c003404103001c0d8010380344c1542c01010401d0042d4082c500400c5001e0054540e4841e45641644190a445280d04111030b2445044010440e080f810407016082000c5100c02d46114441c02c0310354494441c2c02014254813106070144601802156889410541b102080901c40da412803400c41000e035015482030a201d119039003d1440d06240281501c5134140d22040c841d40591400c4100030186d0001e10480e421414610716410042c1d50b00d110050080288100240c2c8408111f02d42c2102031104065060050003181c1000c01400c8020a5080c50320106040808901c0c490405926204000c803182142c08101c106006c500c9540028204071007510560303040002d0f40d940c44048040c2c840c1c42000600d031410700001804460303181d81120312404005030005040021030389407144c1080b03082d00d030300c01c0d4180d48884450078140e20400035805403a07607200030003180c0e500d000000c061 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 869333354 1250 869332104 869332109
    0x11707030c030b09090d0f0807020c01052107020714030106120219080604030809010f0e062a1c0b0604060203070f0302010b120d0801211b120b0405060703050c04 71
    0x8141e501c1d003401d11124000c1d40003401d0303203070301030202c03441032a125850f6544c600401521001081082191111a48c0b10f0740c1e41d0761262121f540501140340e010001902c807504a641c46c2c42d000843d025402600e0b100111946220303c036254000d006040c030b0b010315a1403070a40c01080902903414007905000961740610130391502a41034072000300041480340082003506454011814500401083c801032541c410701d3b030b5000e80350840080008007000c0780c0040840d104520744d403540d070f04940c1c00256011519004140c003850551120a01241080c42c1441c85500c90034583d200b180e8900740002605c4407074440c1203889801510410300d0320b0704190000c0c1d42c0c2d0042900040080b0f94490070380c0101071003904126403030900603040c01c0104c032410003040d07101c0171a9030183e00080c54110001400d40c0c0b485608442c0c00700e481800c1c8900c0b46241d00c0c4c005801100340c100300c2d415030341007400083c41c0c540071045001490252130007108508103460070500301a00a0544d0080508080502c0311319a01c1c0d0040301e08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 869334604 1250 869333354 869333357
    0x12041212110a0819020f04172b11031605100b2202040e0717070311030601232b0504030509131d1b010c32070320011707 53
    0x265070712901490550291642c03010222400070641046c42555080500191401d076009001001c154400c2d85541d118403808191a21401d03a85a500540c1d4415980b0504400e0b49004550648881c2e00c20340786a0020007400d414500303203050f550902009004060009040c214103110b0222020000b880d1400e0b840b21802a90340c00f0303841030304811016812140141130072240c00c0d10910700618050b182d0140700342251120240c840000b404141301340b203600701c50030741c5414103410760304e99400443e5251001a4802a80b00780f00e8422848a20081b0242a140e00070411564103a00c1c0c400079018181328140d801d0302050700342000d01000940104c25241c82d0417061310b004100501640c040d42c05004240d14000100d0740141194041600102c1c0940000c1c2c00070007100d45100d44400116200d8101281c068521004040d450f200c844105021010190ba1744444000394080c3c100c0040c00c200d041d6008880c0304a130324a01b84041050101c621000207402d00b0080e0050f801d12007000c0300c400009120b9070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 869335854 1250 869334604 869334617
    0x160501050f0d060308040320030a03030518061503120a020c0d03052b050c090f041d07090c020118200a090f060e150307090504050312041212110a 64
    0x340c101d038010050b40e500395a407020603c00c1a907a030030040144d910138042610f407a484210918000e4030301d03100c40307200418003070000c00c141013050324101d004150103448031400c1011481c041d01504400c00010f0700690040c44110491b011710000c152400e0640d00f00e034492503c007404a52130250700030031182d81c604002d45561144954038a400c0b246031160121009240f4180c3c1c3c1d0881c0b002e1484110081c421000c00c00030805a1207860a017045809240c2c2120341c04610800420b10303500b01504803607090011403002c8002c140c9203071442800e0a01c0c98000c51886a0f8139803200112a909014465000f03100c800c8040f00034040e620740009965198000c031003078072004a000c4070300307881d4100a0002040250030800c40c48805004d110060503151003201095200c070f90209400059084605038201d01c000c000705899441c200116015040041c41941c0900081c4050328403009014150343c840c91040c0c00340455400708641c0540740800c10420142c0301840c0c40f6000c08210102030840c3c400100c241402c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 869337104 1250 869335854 869335867
    0xc0809010c08040b1303050f041202010f090b091e04110307080f0103021320040b040611010203010608040b0406020c0d0801150e1003110405100507050d1701060c020111060103120e0316050105 84
    0x1d47d00c030f00c02c07020003070f40d44100002c00041842c01d05804241e09ea100340d0300c22440303210614040b039042d07202d03002e070b00c604000c2040155a5132901e8180b840c21400b42c0d880e006c404010010004045400c8904200a036000000404c0a06984500b40350ba000c0c50011181d43c095040d0340100d6620000c45002e1103400d41d0790203100074291401c0c8100585007150203034940d6116115964420140c203d0312442010880121681440d55010300949050390740300d81e00d1302802c0c1c1d103e48a1040c00140500250f4860b41d0801001054820a01c6401d65140098650350015450b200a102480013030700011004c1025001d10382c0740c241e45441140e41080352501d0007061800c20314080061501c2030303074005980090f08402d50f00380241c0140c0a483c03120f000e5000da564011020b0420341c0c103101501e1a22598542182c0107005c154091000300c1e10050040c07511510682035008804e2800708284c005545d581c001000001540340d10005560341c0341e0040d030103132107075620111514040a4860050605000010904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 869338354 1250 869337104 869337107
    0x90307030507032703050304050a1a0316051e03040c12050c040506031f090c0b030112081c020c070521070302091b030703050a11070b0609060f040c0809010c08040b1303 74
    0x10b441c044550813898900a031340c0f072608650726445849518001e1650a50009480c40001881c0e502d10f030400203420728541c1d482140540c88060142c0d0f43d01400000d22807102114040c074101520000c074079003996500e0a103030804003408810750b440a203101c0c903a98018400a600400d030910407401c151070100780d9484042c0000c0c10444040300300c0340300082021b1303079105034070a0743c03c02d0300143d00a00c0310400c0b0a440d0005248148404d00030541003840c950003680008503190006c0000c2a52084503800075801e5a10042c00c5e640940c1c1918010f9008103002c0c4a5842c1c48841c0f10303c04030303401c0307012140d640d0740d030a0650f1030315803a100103031041156074002203a4844401d44100130010148039196030307190801c0040c00802059403c1600d16103080500d0740301030039580444000f00d802541e4505d45076201820090324030001003405411140401d985495511180121031007090b0649410180f40741c1030700b0035821103d02c4080702d02004450028000802d0034808101d0f0000c02030701042c1001c1100342030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 869339604 1250 869338354 869338397
    0x180c0a0c080910080f09010903081305010b0d0807020102010f06050f060c030c0f060a0b0306040309092a02070e060d1e0809270609220f05150f09030703050703 70
    0x1d0380fa00480d11010011105a01805007840340c9440701c00500c80d502d43c5c0ca2800d0807a20400750040201c0c2c1110040341549940b07411402e0708511500011400035903040118000f50701c0f1000403903a0050105c4c500d4215a020b000d1606000003c070030801c05145800c000801036000d2080309030007030000080c1d10040010500c2140c00c1d40c10000100c07400f0900421a4981c0c83d84110350743d04440f80b805404454518020456502654040d680e6614250410140a00900c2c0e07138404e4007042c0100c41020340a030345446440d036040000700d4001c1c0c40d20f04e01d02141e00b0101040100710501c10810b811114001645801c01c45c1250450000c5041c0340070310500d45220b0f02d02c14159096881a001c019030f1140000d001d5270001d030120691078610440e12840b007407140022064034181d44140a0648080380315094151460681c0d00403070741000841455100c03203082c800e00340c58040502092004204034010115601034010299200452034030004d84c4005113030380500c40c0c2c02010420029400482c0400941 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 869340854 1250 869339604 869339617
    0xd0f0b030606221a100e010215180f06070e0402042108040308070507051c030e1c0b0c1803030a02070e100308030901050703111810090e09010b180c0a0c08 68
    0x103c100078140000d40c1c01d640c0510031406191040703040510424250b4840d0b020710348241c0042e002420000d43c041c00c1d0b1000703a103009001e008407240290115031000ca04000700700794076035008040d1145083c894801082186c43c1d20a071401240100810084444150044103502c1c600c11007882c16841c0a241c450514407c590002e043d220303012444405011003c9003034021207404036800301082d90f6041600c040401c0d411409004102e1030900c80c4440e04103803000180c0036000e515560070004031562402200d01013610006c0c8900300101e01202200140005c40d850080218015401d2100600000b9510011750103240034603a9000d0114100341c103802f100740040d42d400580c8a13287d1500320603aa00a080846002d40000e0801c540d140703031b00300c1c140115010070b01e1141104203c00c8109081c081d18862a811520411008840000710503072480d4105005a580c90300101d2a03180d000208200d106003000c1c20107050b01c0c14428003541d1000a012203035410118140700610b00c000d814040700d540144e9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 869342104 1250 869340854 869340919
    0x1807050307060f0f090620071d0103020306100b030127020c0105090c01140d05090a0204020c0f0d050a051b0f030406030f0e07060807180f0b0d0f0b030606 68
    0x501c0208482d40c100780c0d01040c2c0e401a41c0d6075003a181484008681c2030903680714032000300f034000448001034501000b21406002c511411500002c0c3e072188040316a019205a5010744c4c080200140214501801010b8201030007150f40e40045083c02110031040c401841004103054032404100b041c41c0800048842d00245103c046458814401c3d00c14040c2030100c9021006010b2110f2511856020301003090740d000c0742c410341e507003030440c0044094001c110107407025042d42300d003031403100050f6a2800208101d01449020380b20152030ba01741030f450038010381882018400280030010740ca035845007c0d1b814400c450118090032010642d002d80c10b01502201d40b070002e001c001030220b00550503800c0034400310342480080100810940c00c59803105824002c5400141211020450703a901c501c2c50090312843c4030f0070041c2c04583c0c41a000d00704211351b6001c103040340d9003c00c0c0c4420141a0388150203ca0481110512800c1d0b48400069107602c0f005081c00d224041c944682d5004c00c0c0e502c11040b108a510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 869343354 1250 869342104 869342113
    0x81c02010e1c0e01020d021f02131401080703090b0f13020d030306170309100804020a08010906090624170a0c0b0912070e131707030309121718070503 66
    0x21a102c0386503141c81d1000410128014603804800c6500c001102d62541c0340c00c5d4003500015000d008000c1c12044031a222201c0a030b02400018009561154180014014400c0a040e11056800013400304000101840305041c64403e41310081b40d4441e0703a6941c17003020b02124942c00c3c0c1e1101d00542446121641c0a900072495403241401c15816a00c4441682c604000c0c80c14400e10048100e5528070405268a81084018910090450085200340c1d0040d10040c4880011a200c2d240c007421903c0302602520403d4a80510000340072a43c4643da40350070071202c5008252402044203400716005224655402c40d5039000c0d114082c03014401030700110f522001d0f1015855441c6140c20550304843e601510441c401c1c1008544001d000582c1c404680e190136400300107075251800a2501040840c0c280c1d0000303288080e000d141e20100c402130070070b14442c0d10000342420a500340902a10010080601030100c01240600300444000e0610390185801295960404a1120351803d01820790b0019415208 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 869344604 1250 869343354 869343373
    0x3020913140a0209011e090f0b06070503040f0e04050d1112180306070804171305150d050109020405030c0d060b0907020f1b0a061b02150c0f07081c02010e 68
    0x3042c000c08041c001c0b218448182d80303609900108034a200e0f0700c0301201070454810800410325070098030310300f02c105600080d01080400480c016a01c86103003140c09410000e003d04c440300304c480080000d000c448052000629182d40c3d40395440004035000317418402c005d0492500c00e4401c101132212000b0804402e500e90048032401050080c0300c5403814800c3c00b0319000a400c91740b081074054840d9401c20355008030070811082e004426407203000c4004800079031100104030380d150300291903050701c0400c415995900c1c00d1030003402201c070103802c41c6c03402078010807040080399400100c9003030490742125280001c41161070113170000c18040e00c10795000ba40400410001640214050f070004039601c00341d48100901000b0614070030312271002c041d0f0002c0c140a0900096110b03910b000d05424450b040700344884416000201c000d98040d00b00708a194000072128220b210600541c40703608400c000030b0540b00d0900040030b885099442c114003000780c103c0d8004200600c00d410030b40c5c81d169083c058907542d20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 869345854 1250 869344604 869344643
    0x1b0e190b07020307090c0818240a0c0207030c06050f04030209070c0b0a0b0a060503060103020d150f05030c09010b090a1809121e050a11030c0c0307061803020913 71
    0x200a1081640b0030b01404000140b003817114007580d40e1078101551024665901d108641400100f400c0203030049203d03256030141e54420169140303500c0030300b050280702e0900c6c04641c034909071008d844429045405c00b0100700005400301a0b803009440c071038104262110b1300819410814059070344041d6018030020f0500940d43d070880782c0a0901409007100440c0c554a05513910b066a10b500e00d41d5400444451302040080e214030091604007030145005490280d0147e000001d0b102c4141d24120242841c010400200319801a030301c0c010403041e00038210740b41c0b41c400020f084039414440c1562083c4006030300602039039900702d08005840207035400401103101000d00740003000c804e241225010000034581512600402498104c2c08805003100c140d120101c4044880350407007a106030601c4010030b44041c0c2100c0034000b80034200c00e054010701e08041c0000403d4a04141640010103111000d94119444010b40c040c050a80790151041007040c1c940c41482d060000c14440041e01c07a004858818044c071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 869347104 1250 869345854 869345857
    0x1c020c011d0321090f180109090201050d09030201240b03011206090b01080c090c030c0702010f26040615120807051920120a140f0303130309091b0e190b 67
    0x20f82d0b06448203142d0107620400e01510901b0b1800040c1804802401040140480d402c070760740891040c50440d0a00ca004450310040c0c032446036080303015035118003091881e801200e0b4000b14503200d61000341062445d120f041006484180280f01c0907070345581c603000502c0003a401054900340d00c80c046441561391003000b562551240d4800074442c0d10b2940116054001e6042586e024240000300f01d03181c4002d541c0152103140201c8a0001400b9081f00b00190322840c2d1b10281c0065402c03e5080a043e10f0503140102c1182c00281000303091401482c024001400d5414842800950003920541d46403528100245410100043e41405403031146100040140d07900c5800d0429001c0c1004243c0c043c2d00e4010030103048130a01986070198464100b030400700700200b03442413480340d800040c0d403005031465003281c0c1154012100840e1450845c45640c04041c0e01142e54002400c074100200325040480020034940340d0091141c50400480d4280ca11060b87c4400b104200e080030900002ca08a07900d40240300c05 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 869348354 1250 869347104 869347117
    0x60d0e0705031203160e0f01050d060302061c05090105072a0c090b0f030c03030d090c05090403020307140606060d02030720010c0f031406040c090e091c020c011d0321 73
    0x80ca0920585c402c14500908400610030302c0100131000a0074520011a2260008101190480d880740d8001000d40c4a01005000d9072810000d1980303036003408070307602c016550013605958142c1e140c6001c2000e03d9a0050540d05800b403078158828080c00380d2150440d80c80f40000c030203402803054000010b0141c640d07030302c24115035000740c801803100b040c450101911050110308441d090b0b0810424441481030603444222494452034042c2115a102e101050701ba0008540c202d003d41d100040100502c601055202d01c42001d441c0240403074500700004c40c3c91801081c0e02c2c3c0d041c1c19008030204004500861041081801c07100d6500038060540b00604e010f04400a000c0c1c0102e00d4010000e882988680101031140340001400009603c0e0001030100070521225010304001940001241101d02494602d0041040c1d100900003000960000d400e0300761114043c1c41550f0002c0c1000c03080d660040131201a800180c3c19440440085c01d01007410054815919058071401000400e501c036141000b8040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 869349604 1250 869348354 869348371
    0x110609070314060403090b090118290c120a120e07091a0f0f0414012405040e060f0a080f03071109060a03080306060412151a060d0e0705031203 63
    0x500c5480b5090a44601d02510084d00050b80c402090204080c420018800030106142012002408103510140100070760420018000c112a681c1ca50003042a1501d44245451408070314210201c0341d03140ea203652000030203481c080c0104111522900901004200d0300c68400300317206c21000050030b40d072200a0303401488126440e04641800c8000440c0d4464030091010740b00c0c0708000100e10821008079981007040f07902549a2800ba000524110f00031402400048070428014004980414082c44129001c1007004001c0c8010030481c0202c0d581260008001e983c0100303000c04d40001f103945c2182940012000744200058040610030020007081d0181c0142044034441418008010b1268001d40d50654402c2c001c1200744045941c010046402c40c038000c25540c5000d664464000c0b075001ea1090640b01da541c05c444050010341c0034010000440450420384070016070005c00980c95001da01d0400344200c1c0c1da103d003950601010042000503000040488452210800c0c0c02c1d0b5480d40100d84105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 869350854 1250 869349604 869349623
    0x40c0f0807090510080604020d02190f0804020607060e0c03030313020909121e0c07090b030c090c0d02090a03083412080a0f1d0c01050310060507031106090703 70
    0x500803403003054680b060341c2c401000c0752078914035000210f40c0760002030115640701d5402c001489110145100070800107484494144468041380c0e8080d002c00d144c24562070a00041004120040c0e847da0112907400f80e01000c001003500000031a64030380070000300e01a803d4072000041c413244038203811011084602c01c58800550b9075a00ea01c8d1515200840b00c1d01c44240400d0083c608080c01c82414080804464044241050f980945492801c516a40115442c1c3d90302ca486400780d08042c003d038941e0301c00c2540d40071641c0c1420b4601c0103580c030503c8040c3c1461580804ca070300c442d56805440d80011504540304980710000303072140c520441112400034901d004041c2c260500f425604640d94005500103d805c005110315843c1030f98581802010410959074982d4010507540207481420b004003400d00d4407d54000d294901c0a03d0b200c01d901407a8148a8240b0400241f0f030094030000f815540c240ca006621880d0901d4103944114010202003201d000b4042081082040001d100044030301a10050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 869352104 1250 869350854 869350861
    0x280f09081e070c0905070c0501110d0e060f010501200703110901300c030b070804053a1b0f06050c0a05180a080106080105060901080c011d040b040c0f08 67
    0x32181c0e101d507000043c2040d04103d0300700260b080540c0040c1e0b2003042c0c0d0418818400c2c1684d2180e08580c02c3d84e60441c0340c03010105030b00440500502c1120080e010301001880507007005030502051010511403c1d04001d00c0c03a4120f040b814a01e003500c0d10007113481c412108880e403a4a00f8561549550004d140100c0000c00000f600240c5601d45084843c010340c0240217062140792418200b0007026400c0c0d8144640010001c00100102500f1388a4865a0b4501300142000d15015041205059034408103003000c0058030550315441800c018005c6030012446821210701c1c0013556010103d000c280388441d020324200040c8011811003002c00d91045004000da5070341c501500e04075000701d51290000036010300c242400656018801440544010103450409a40303030304c003900390341c020307003020056944031014044e2a05000c5065409409080081c040f0f40c1400b40000304084041c10b00a11b4115890074004009d8580b43e0018410032030141060040d112814000740c02480204100c0340040c1540c00003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 869353354 1250 869352104 869352157
    0x70f06031d0a03080a1109060409090309050a1406030a06080a03020d0906031e0b0d05010c090302010201050c03040f081c061202130e03181f090617280f0908 69
    0x42c030001ca64951654540d40d00c50800300341c02000c00882c0d1010914080200380003a559541c00b50005026060001c1900c038494500100019410743c03209010b0390700c1c400300748405194911861503802d02998000d85030760310100844003406150f031010b101c81c064020540140345c0c0c0407840344002038645d207801c40b6250384e4035400c40c11201c40740b20918141c5828a200f40c05148550441c10902c0c400502d5400880320541b1202c0c2102c2c688c032210008903400b410308208550702800382170f0f401007030342407014194602034960242c082c00c00392008000d0070001030348001081c0e90110300050920300c007504010541d2a00090307203004101304011b900c2103900031511250141607015a00358400c0d007102544c184000b101c9200413a4040f440b215900070002e00c88070714407030142c030f01d4100c440d0b14030703520102a10b2410700042c0c8102814441408101050300c1045480002125607019102c6603402c1825503c801b612088010481c441d442c1300201c1c01e000310134061108080c080c4c005600354401240f00c1803d0f0440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 869354604 1250 869353354 869353363
    0x60a0f0605150a110c03030a0309060912051305061c09051203041511031b0a02120c160602060f04030f051908060f0105120402150c1509100204081c02070f06031d 71
    0x5a16411f500420611850358480d030000e0104a2084101145070303085641c0d001c80d100358011080c400580085625400b801c41d0304198030003443c040d2613030780c90f0818540d88410441030303551043e0b03030480d12035801d40100241006100501046031100b40d440381440d241184030710301044940c0e0134143c104854040e2100c0d880e13080f00c3c0101005145244c1e100b00801c4109140e40101c4140020350052510004000b550400200708010314240680000810040320050f004803541220045602c105c042180c14411040400d82107a014201080c0040102000307d61314403503407da40940d00000c075114441c0f6030308100c010703010300d000700e660301c40158a02c3c0044803e8082e40c02c0c072130000400c41000c98094200100d00030340c024810710030b0501d40411100d6091610409000c040c012a100d8001c001e9804018441010942041c0e042940b426251980e000e1f42e0785c0d20030650444100150106218140c000c2010300b00805071902000006581c1b03035000307030040c40001d40d03140314131596500d1802100d03400725 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 869355854 1250 869354604 869354623
    0x1f0507090e01060e0409080c070305030c01050a0908030a021602180601090e09031213082805071716020307090c09051f0c0f0f08030103200102060a0f0605150a11 71
    0xe4500f084404c1c428200800741100741015180c00c5420424003040c5c05080c07000c0c4d005140550021940c3d441c14180d446e0171a13000038a05e03040d481c83c1503c40c0f00062310340801c0300c0e0804541d260150f1981d41825403480c1a040f5600c001358445100d9094541e00003011807494440c4000762141e000199a8403c00d00044c141294000e9040d0003c000498001003082101500b1081440c000100a041c50f569511990300880d1505000b120000034428a020000702d070300009034440c42d00c582400003d1382c2d00c0c0749000d4815400e100191001c66803002d60b50400004850490b0010122200386035903d00d400024580e41c007102e0002044040d0118071402c1150f820019602c503e110000c0c01041d6075010ac0e043c2003901400c840f8102400101000f081061070842c07005800352024070ba4951651038507614800745180840e600340e11101c5190b401e03a8000c2510756101c4595100814860090701400004201e03035080319501450703a1201042d03c1c44418041c00c0c40901e180c440c200513040782907100d42d80b09406c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 869357104 1250 869355854 869355857
    0x9030206190e060409090c0f050d020103050a0b2d09130201080702030403081315030e060a0b1201090507090c0804050c06131d0907170a060e1f0507090e0106 69
    0x30482450040008072030300e07010203154a00034490402200000d50190b1069102c0c20403251039003030640074018102c425400400100e00e030fa4080a1600c00031a05080c4c803003002074107240d43c13803001502d403100982180700c14410080c140c408441400021500b0310709400c00b441540d52214082102e40e00b03100c004039000300d11841c9004007401c0d150b8011201828020442021070009002c000001a10310001c5c05880d0460101e41d2203107401e00c0c112220360002d802d487d9040504bc00c404140028010501541050400d900400c5128041012913242040c81300700c042950300e003095110a002c030120300801545c00c0c810040c080400c18090031074808105550241c0590401c240304600c03460841c0c0288200b01185500341b0100d03a9484103082040d0342001c0100340b400861003006000102071010802400040030b0080103d103040c20005c0e9240302540d0000c04a83e5100da10030180b03c010000d01c94600310300d40c041c2c65000409649a00900b2060349c425020800c0d510000c9005079100d504c1c2e90598407a03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 869358354 1250 869357104 869357107
    0x1a060304030903062d020304110d060209040b01082e0803040b0d050f0c0a03091106030f070f050301140d08040f06020a060609021c1d0d0f110c01090b0c10140f0709030206 75
    0xc071032170030025070028104581d0045c00040b15946503e40b03031070711088039000307840050303d4188580600042d6251581c01d84e0402c098102040400804c1044c00c22114a1043d800b030212a01d003035070003443c035105411515940c4004100003c200903c0e00c005d02154000c61000d0101d610303182452501a5010b070390040880a00340107000c1841d00c00d60000581c1c0f0b006419505540000f03c01007000d0368001e645e078490740384000003045866030700081c0e1040c41c15224030341503107150325000c44070300c1180c1c1401915228140d80a000e1090104a50503103001d0306442041c0c00b002d0340e41d8400039540d0200414103d4400b803c0000000d5410164400d44402d01280840042560340119107131004000502e144104110100780440c20103e0402c048900c200f5076071100c040d490142407025051135042440b50400d0b40c8824481c04169038020f180d10100e500ba200030309d4076004225241810b0884100500c1030741032a01c10010f00d0f030400e2041c520700804a1418510982d01e400504982c01c610500001e900040c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 869359604 1250 869358354 869358431
    0x40207080901230708030106020f0604200d0204050f060a06030b0609060a03020c0609030c15100302010806221a0607020a0b21010b0a0e01110c01031a06030403090306 73
    0x200e020075140003603025540c9052118410f1800290002c0e101901c03000d1000c07006002d030940400400b10f4440480300108658a401d958900141c00c1d18107800c48145000d0a05c1a1551989000c0800040d4018001d0204c0e18203010800302c0160100c40e0140b0401c2c016800007040e42c040d2042a201d0180a0103880c07601d49034400340070166210610640800d07508015002a200c07003031007581d010798890320245540b42d10900c901440c149850001000800600c41804590407080508604407503082c2080c81042e550030700001c0004072004281001e58038040d8a15075002c009903c100307a200011100501a99601001c0c070081e800f440ba002500550341420030302403c50004081c158040400700c01040c520202010840001c0080c0c0c084c0644150116070400c01c10b4101d00d864803000c10031f18028200542e10005256280d902c01429414140c0ea607101640c071844245040781c46034409000c003076690505160041c040a8144410340d04e05240480c1c010f420340c00f9800214025030846001ca41415 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 869360854 1250 869359604 869359607
    0x1c050403060213030204020a09150905061e1204050c0a063b060a02100f1b0e030a0c030f030810150302130306050c0408390a21030e040207080901 64
    0x1841110b85a000e1450f03060008011b035628001400e48150982e50040040d01d80035481c00b500a003912040d0a00a80f140240070584034402514000c4d0310100b4003140b40c101d245801c40540c030805200501210148080105204000400740103407141a41d204040343d50301e136070480d80b15540f0040701070380c0300e604102c206544840140b1190320f030314000341041c800048040000c200e0780c414120480583c112100c03a8282508600c19180004014041030024154034042c000b0210640000b080c2404090144600300b52020003413a03400c587d100903102400354803421704401000d585d00c2c0850001e18580d0002d01c3c1644004098802c03195414900881c0c014169010b5002e50001d031502c01c115110b8100001c045001c500905004010089503165a5801c02182a040140442c550761060420310700504000f078580700c0700c4d0140303006003914410070351070f010000302d0311100d0798801d000e80544000c2c0c04201c00038031125000403030710a880716046281440280701c168082c40201a14282c0240410580755 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 869362104 1250 869360854 869360857
    0xd0c0807060311041e171e070803030606071502031306050901060305190305070c060c1403192a1202010e07030b010e07110f03131d0a0f06081e1c0504030602 69
    0x1401d015a00c40261030f0103c0d450420800b0b80e25048544c4210070541c15103d50401c1c00c1f1848028030050a04d240c05d041c4003940d03d05c006032801e4000c00d80015071805215801c01c16220200c0c00f15415580e030f003017011442c180304d0350050b0203980c02c038030348404a42682c8052145c0d004681d0700c10041e001e84004014911031850640d4016024083c0401a0300c0004a801c40402e025101507241c5549030040390900541911a5034a4900302d68010849151111443c4c0c000d4840d54049240160f00c030040d402e1080541c2008920010003200020038401c10032542134514080740c2410380c020044800c1900220f070384d8689512019007041c01e144014814070b1580c0f05a543d210a5900b0554041e040700d0881901d8581000403100c030541001c0303000c0a01510515056005006600700e22804000101c0b008020b0ba80107014080a41c0c0d8034541e0085489294200e0001022410203030340c2c0e80c4c140d03410700d04002002d6800b84101401041504280c018014500083e03a807415036940d0700b802d04665505009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 869363354 1250 869362104 869362139
    0x6031203110c0c1e060310060f09082d0a03080f09120304020f04020415020303010e010e1611120d06050301470a06210216080310050d0c080706031104 66
    0x800c40134034100318940c840c030f4002d5008491502200b1943c525120740200584c03030702c00c080001c1000c2d14008001c0d0078400210300118580400e081d25144403444c40220000c1c26080003140c1e180208040c400031b050700450514429040025142665548c42a40300d841345180700c026a5110000d00114005d030070039010a001e405030151005103002d031500382d40348402c80c601c0f5021f0010303400040103000c0c49440c0350615004102848402c003450034091500c60600d80303441c0040c01000500e00c04007039018000c0202242c12181050519980c100e20400b030303000f51440f800742500035030902245050120444200c0c14800400800d00001c55481062440c8010919902070600402c40c4904503030940c2c0320782295009112940310000506c1e04041e000350307110002c44034207482074414428034481c1d984214200210313030785c411211940c0c2e55a560010300b035000150041b40e00038442c0c44684042040c007140d4038081d02c00810031503032501d6440108400340d51260b148500c08407000c2c00b0800c14400c031584010718 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 869364604 1250 869363354 869363389
    0xf0503120d02162d0c03020d020409200a08030928080d120b120d030c140708040303080a020403020a09020d0b03120421050a0816050106031203110c0c 66
    0x1d4041c40503554040841c0c40c1030f0aa540c81c1c002c08001030056040340e100e00e15610303c607040d8000e5a04944441c000041c1d0307071002902540d0060544021542c551f0311a00700141d00030a072004440004500c0507c140c0000207040c041c6000800104800400005481e0308290007410b1580301c0e0130140c11340040000c0c0d00c4500c034044603030210100780144248080d1300710000a980d0016181c0c0d0340580f0301d06a8000140c0d050103040310300c8a06450341d501083c600c1540a072410302040160f10701e0000c645402801000761000e0f01c0100e510020000714100030002c03240250f552031415103540080400b240704d2448000d61040c03221004106c50001d94010341102600d50704002a1481c480d400700303003001c15510404004040001c2c0a1001c1940003110907101c0c000e0441c8003040c080030b55622551030f410144040c00800012844001c050350b5400514866980280240060307603070303844c19078031000b80c503c40e200202c0c3c10f00ca240341c8810080c40035291541c120000901a00c0a99401e01100110030941754a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 869365854 1250 869364604 869364607
    0x1c0c06050403020c040612120f02030c0708100606050c0a06110f031003021005180d05010e030a020601030c0608070e0907020102090616300e240901090f0503120d02 72
    0x208819100d194401c80c080c0d005041401020000c11046606c650481d041480c5841152000b18410194102d2003402c1030520901005e00c0200991460045e400300110502c21900d0210301d004020039401d20402404200b404510f840b03580549a5005001408000d9404048103001141c039507002800b20b15030b00380701e43d85020318143c85601349a104442c8000c607018022000c200b18180800110443c5c5e075103142407400c02e03144480b000d48494007812006d2045041405050500000303601c8200c003541c071441100c0e40d407400c200002c0d4852402748000d840242c59190009811401846020304c920410760310222142c1401c0100107500c100505420308541d82030051010300d4032a40020300385824203404c80c0e031403000907203800036120b60284000001102141340484241800d10701480c0001468103151000320034100c00700341c3e40d44524400803103100201081200c862014001825246c03420703a51260600c2e11030103406d540c50070318820140c040e4012242c055100d60784070003800594803c644051b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 869367104 1250 869365854 869365877
    0x150807090e011511010605010507060f02040f0611100605010c0206031b0a021b1503010e090a0204050f04061d120a090b0a03020a0f110a031b020307060806030f0f1c 72
    0x114114000d802901c14007032210240e0103c590407403840000c0d00840300c02030090764204030000303065004260005003d0ae81301d070b10804181c10030b41c05032009008281e58881d405940c80c0c40c000d10b04440d003070112115000f1450300603000d0915001d0300e01598410303100c070003c40b052a420320215501c0105010240c000055a10620b608400000c01c0c0c405a25801007a1400080c000b038104044900c00741480b50300305035061000320454405507130440b2903800e118581503036034a03403107410400d245400940c03161502c0c080040d0340742c01c9034016020780e0140404101448251803107514101824528806a5104101c00003c8000540003880e8000080c504200c602d680d034548450160405403044001c6600030803103040c1c6a074012078840d079607009454180024007400003880d4441c4c18800d0003404004074500741604821042c12045c245940c090221400150740d1180101405020f491440c030901545009104601e400104199040c1d02840038010300d00c40d60b00400480d040c24401c0c04184503805400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 869368354 1250 869367104 869367119
    0x18040b0112050a060c1101110306090115020a05030d09170306031e1906020706050f01030305040b0d02040b03161d0f091e070201060602011b0804060c050c190b0c0415080709 76
    0x7080c02041c17594583c010030019800c00f05095a04002040018070002d004101071940c400c4012b030b044480d10904c5070003c030a800c408038107100030b004002d40244800200c01072420a9540300c8254140256110b41c01d007451015114240d120640e071207945948816056444a1a03040d04680c8071100402122330041d4020300030390000b003e094003035810035400300e00802808058003440740e00000100e240403031503040d0f6038068010f0143d07000302644803001107070000c1c1c0c210041d13044030701901442c0403045d00c84c0f038405151040800e40324141000281071454000031400c00c5083c8516201e00100030649041081d014800716100c02000a0083e04030183c8840d50410404040c5018022640c00400c90360306201c4040c0c20b44480300104000d803021056514581907200030040d40007640300d00003041c1d4100c444800c40e280d0140000c94440c0c4d00501c101c401d0500140012120064400c2204441c00d0303071400c2007101c0300c0c0102d1041501c140041da10008404e8031846181d50700c904a0300381086a541c58108 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 869369604 1250 869368354 869368361
    0xc09080a2a1206051b040b0a12020304110429040509010603060228050703200f030c0c0114030f04081b011803021006060203090f03030c010203040c0518040b0112050a06 74
    0x19240030b240003802e54180600740c040c5030b074045400e01108031082901c00071032049100d244196103002e040812841606c51042c450000c180384109010b544034142030400741d0080c1030200d0a50311480c41c0103800c440ca81100c64600c04c8600100384811000402c001c00c0c080a043c0003031400125541c0c8150200000d0001d03c081c04448113030b075206010585800c1a42e0011503101290202030100910001000a0307014500b5507210b400b80c0c0c9041144402d003d400c5240a540200a0500303000124110001110004030070400f508241d9400117080d20024540c24584020349182e4030a209040004011422080c000d22621a2040d0480000c404500301ca90844080d00203604601c420f041c40001416070400014808070750000041200720716214000e5130f280b04144c2114061040240145031541c0c050042d5032110381814020b5540b842d251824400ca10b00d00e000c1c2501c210340009201a00c1400d441d81280300780d0b40502191405c1e400c011802400c00d052505c11a418840e070444100003501901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 869370854 1250 869369604 869369609
    0xb1c03141305121207020f0f0310020a1206030203030a03051b03100501080603010b010e0405090a0c0e010509011208030a15050301020c0703021e09060d020a0b130602010c09080a2a 79
    0xa507418150070001000703c1c102101c82001555840004880ca4103a100001c482c0a294121214180e00d082200401c000d11a89020a541070090502c24101419160000c2030305039200c1d9520907035402111609021103072603000103509030303005210401c8542e0196000340d8001030150884003c1d00c0b0703403813414820ba9100b107561101c0c40113480020449541c215a4843d00a03904030b00034082400904002803a0401c0c101c0218403480d2070340c000c10114002481000c4002d0380050340755882c42d40b80c0001e1000e40b1000c0c4140d134000c0517140000110f030fa140c080c00341e601c1548135006500d59140c000029018041040c03d642948000d404000342c5550700f40b000348001c0911002030701d0010710314010803808010205540c4145c0012250503c810f41d103100407154884411030b100b4002c0e001030300100c0c0030601c1c0c64001c01d5650f000096601c500e0f14100803604221000b9600901c441e805020301251040098807038401da66008191401c0064285000c0e02034490403614000b01c071a520b10100c2015080c4d0b45e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 869372104 1250 869370854 869370877
    0x306270c0e0c03011d060a08030a110c06040807031101090f03060e01060e100306021803010207031e02121b010e072303070e06100201091a190b1c0314 66
    0xc1003080000c01c8224556801402860918110740c5007085100302110800120144505d866002070001d60b60100b070701000c0e00700f40f02100d0712042c2c0000090110310101100c036035980f189500d86a031502d071040444040e640c41d5030143c8040c1e031550703603541c1181840c1c0d0b49050610003e5240071501030f0710011400010341c010100401c500b459008406c3c02c540040e040000c0c981c031940c0800442075a440b07485411aa07200318016170300c2c0b600350b081c2c0a00403103410405a040d40000740000c01d1592011100c1c0c41240241c000280390406403200740ea83d0700c103602684607002002d00030071002c185003c001e40842041d035800400c48030040c40b041c60920840e900b0417912000708408011a85100f0710182c049600d060b0300034914103090030000074848000a2109200d41d409450071300300c9502c01c0d044101034a034070000360240e0920000041c0480c0c1003c54a8045a101140884580301d426010302c19030701101612603030550038036908404100880c00303800d4082c4041684c520b06041c20120003440d1400c100d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 869373354 1250 869372104 869372123
    0x40513150b19090e060903090d150f1401080c13050402060c06010905070207080114130c03080a020c0f01030902010816020a0506240109060503060f0d0222050a06030507030627 77
    0x10459404101c2d1007004c0184020761204007003040d8600c0000c11607501c6007003154020010b40041c6090040982134681e03c001d400c0c1080c0381d814007a00136810800d84a180d04040541c00c1c3c2e00c501025581e81e03005076a0982c04804d0946001001409601c5550000c3c00a0401c2d480c00319140c142600d130070070a0b480008640ea0350010407081c1c690500030307580a08241402405805485400106c802c0800381011141e07030303c04404c28003005454446103004540c02008161160781184019465480c00345c0650f01856070352011340011340c0f0030301c13a080d80a6170503180c0090a403107009030003031840d224211400640c0f003000d40103000b00d441000000d1213062034280b4141c1000c002040d5803408042d064407203050002544042c01300d1500001504d600804c203450500101100c0c80024400c81503800700a50402d11043d0700120392207449210350314180a019040c0190780701e855022044920610000c0e1040e00202d05c14400501e99810811181a080183c00c0308541690680d01c1048210401120031515 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 869374604 1250 869373354 869373359
    0x90402040b03240606070f0611160804030201031103010b03070f020f0f0a050c030a0c090f02090909061503210906040e010e010305100513020607020310020a0507060506040513150b19 80
    0x10303040f034500d910040544c4d500e42030080c40d80c3e031000b9030009044020080c0d1b07141c40110888000010035691252250081000e9100f00c50a1106450b40903020580c0003c0c00c0c1103201300c0e02691041101c1c1210f0550026074610b03903070140100d5200d1801807006007180522554403071040e000300005941100003030007528042e802454150b00d807007000082076001e40c000c01818408035010200c2300c0c3c00c40741c88081c082072820080488100038400c1c0c120103a03000d03100d2428000c82d010006081031040160080344400302440404040e6941003048111804a001394510400580b405000e05500c01001c0c290606103a1a10800041104241c006a194401d005d0040050203020000c3d807440540e00c400030045410207080110b0120025030002e030080e640000c640045440800041100220303010086440f101003aa0080c040d520048080d0f038000d0400022914600d0a4402e0300d0080c3c1c01d0600b450000380441c1e451030040e0410aa42421460b80c82204a1680c0c42e0a1100c0d211200c004808080f000d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 869375854 1250 869374604 869374663
    0x150c04080c040506011e0908030d050a0b011e1202040302120109121b290a06050109091a09040f1e14160501050d060906080f1218090402040b03 63
    0x40207120700521a504000500c4080c3e40c0260891a000300f02c0a45445199003400c2c0549210210380d0080c400c40c440040c0c1d0055944907a40064025540303100184078080003c001103640b29a0705002c000c040d1082c07440c2c40d154a02611200c080c520300901c0c09800c10380d5a030002000041c060003035a50a9445a084000300f20b00440d6a6150010301e0816440b80034641c0c0e40c50b0101550310f00c009100c107206c210350211560109464038100303900e2800d420010b15180501c800a41aa8800c5a000c58200700c4080b45100c11801a6080710b80d011100e40c1c0201515020810f4003c00603005a030034000141d82d240c0803440d4000440040c41c9a0130108101c0d100c00d140c0022003216041869510f500032650500c1070359481480d00b011542c091801e44d40390701840b01e0400c02004283c0c0080980c03450708000003800e00300401d00e00790400d042c00a441740c030303030150404082c1c610944820140c0802d103850300514618180b04610f030010f001400c00200703030f050345000c240303050807201c0001c081c2c1016941035407510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 869377104 1250 869375854 869375863
    0x3200105030c07020402070f061b0908071a03070e100c0b0a0e0c150409060e0412020c1f0e101709031c02070f0516140108040309031202150c0408 64
    0x40003031a1892031450035102864540c014031030000e00c0b860300041c000c0140420305a00c0a005508800c007080b40142a21440d68104002c884510108070444c4000a1040e00406ea4800712450907140c0c000d550140d801c826807680c0010030280901916035465039058407000c100e01c1704511541c81c1d41e1075414a0b41011404094020312401105007042441c44042c00e01003047c003250303001550f80c00101400d0040d1400346010300c0e004102e00c589050400195864801c000b0350146014100c51000002c000343c040340c03550384800c10300f43c000b504109140442a10780040305000b50b00d5140034074000900b030002480722a842c82201c40000c10610010035440f070105245608010b072500218075244011608805001803155010030403540414001d0510101c08401e82c10968401d0694203401c2d2220b80c0d2413000402801020088100003007400f4265004802680c0901c1e050f4036486141461550342881c0100b080400d01c0450283e042c120030450500448203025031140c0c694541c8880c105000103240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 869378354 1250 869377104 869377163
    0x2010c351f050d0f0b0a1b02070302010e030a0c0312050d11070201200c1c06090b1608070203030105060f3a0204290c031303110906010207090c031503 66
    0x9540540e003c800060740560b40c40071882c1c3c2c09141ca18850341c0e00c1c01e84400510105480c040040003c201c2c100d40a0307030124034002640e1003603c0d003126101510040c9590740e1f42c2514010101046520240b010070307110740014901911501c0e003035103060007220804040d50401c112002c0c1e400c5020072494215a041002050400c168000035041821f182c0c4059603600020250640952464030145128a100c0c8002400140d00306509202d40c003402d02d40304a00002c11645940d0701902c0700d01c074601c694803a80c45d803405030100358002c604607402c0c0401c11003590f0005070390851956040001e4001c091901000c0001c40c42981c014840d0111110115620090304040342c0700b090307104000901002c0b00508a117a001485440300c1001c1d840068012042c51003901002d0440703100108402c0c040d0b4045100000c283c91181c03043c0c013840380c460014082800f1381590320702d0140e00a40c50602004001d903106001100140c9408104d00514180b90031100400390000d403520034500f803405280103040340c5030b2402d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 869379604 1250 869378354 869378359
    0x705011103180f06041e030b010b03070c0303050604140f0601020709021c0b010e0d0813061b0f06110703020120030405030a0806031f14010602010c351f05 68
    0x3802164410282800d0b01c00d0000c140329400c41c0032109800c0d120a07095401410340480d2003030248444945d5550546440d200845281156a001150043c0d002d001d4078012009500e03100c07209c1c01c140d17a0607009071078001c044d160440e40c1c074907171014090003810025010701d618003070003451410300d1000207082c190a600000d140358010090300b03042c076003200c901a840a500d0070000800c0081c1c800100c1d0340761503c28815510541c81c850050a01002400030490001300040c500e586991301c5c9002e40c4c1d0080710105c100b98060880070202c0100b4200310ba03000700703c0d105442c0007031640d280301700107100d036000b109040d0010b030b545a05400310303603a084080311380c1e81d5000b40d8440e00710701d4255101a038038455111030b40200017a560204070305460030016000000340c00c1c40d04809103080c00c0e54140051501c0004c40280700c14000000a94030300620509441e00300d1a610980070b0b0b03884a0f00020400d440c440000140c5000090200d2260001c044442c02054210050301c10385001d0b00307602a05800d076400151 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 869380854 1250 869379604 869379607
    0x609060b1e0f090604230a06050a140616060e0c0108010906081207050c04060902090906010e090109021305090a0516080903040e1302030f0606030712020d02060c1204080705011103 79
    0x250070b81d80d03120070760868442103c43c400d035a03407281c000c500a02010280700076091183d20f40c45005051b88910b40f0300c560304a0104000e2507584100b005a038140a220700030701c034004040750040506001d401014180421b035012010400540e540b01d04503040550401440c1e0089400001c0540c1d01030010703401406645000d010032406c0000300c540340c2c5503c40c040ea100a000040550400c6030034880d056030280d00034002c101389541c602003a0061b50000909511503582800001c8056020f40d10422403540c01828401c02a82003a8400f0003d500c041c440310b102d103420aa0020310b070381d0f84c10400c8ac45286994008180703802c3c60b10443c1c005407600c2d41408e00380102d178020170180c2500003003a10101d07510b08490040946480403102da0450a20038080c0d01800780b850640d00d102c10008040f8002c2c1c1b4113400315007141d0fa484843d81013010700d010300207503c41c044171310385400340c50300c0303405410440f4004080c0e030000150512804001d0780503074411806900601420040ca681010050b0056071426001c0d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 869382104 1250 869380854 869380909
    0x182303060103201206070503070f1b140307020901090e070b160b06010c0f0b0405060603030c031b030909040c09050606070506040311031603083c0703090609060b 71
    0x107803a000700c00840440514441109040144c1c0e40d8408290448a000c4c01d640f00c1d82080c0358014500da2040700c03440d001c0b4a619402910301e62054540c8032400b507260b524600100f29030364400441c20740808a00490307200900100e00565900791415000340050710000400021a4907218100841684008190002440051040c158031010425503690001c404400b6564040044e0b60406070760f4000341c0303002d038071103102020041001c44960242e4025022241580d0b914000c0556900c284018044150030130b020b8122244500c0c9071100c0c50410200940313052040070b90100e40d04210485040d00c60100c604000c0101c5c04041c816540c1010042e03402c14030380912610f0b0f0f20b5640201400050070880d8800c1d0039401d1200078815a4070200e81305040c604103060a0500074007a60003901c07916491a16940c0c91b0304000030700e8204102060034907403881c10885400d0417084030355800410036014591a0010764000503040e218030804140f04402c0001c41d1401c4205020003c035992044c0340001d032030b11809 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 869383354 1250 869382104 869382113
    0xd020418060e061008060303130305100e010e21091002030703090501140412030c080315120c091f03080a050706050a06050603180a12020c0907140910182303060103 72
    0x1014000d011424120340ca43c41b4480803901c0c62150a100c401180c1680e0b01c084104071010403503890711603507000240718098030402d40c03038203ca284603010403296022a031010180c0c3e010b0040d0902c060b016070302048c1441e80040219a5510399007010000580000405008254110030541c0281500b072034000c0076200300e140100010300c034502a00440c0d03402c000010080501c1004c8203505641e1246009403207080040c0c050500c071468903681d6105120748a12220090000141203080d0036008000243c540c8800e25019942e03510b044405101d1903840d600800802e200400030a0b0181302d541d0703440c1e50f8000303a082003400c4030307000741642c8129814088208082e55480058a42050344801c400d448000900001464041030f0b01c3d00404079541d0082c1501c0c5c03250082481c864002083e114292a5610b1140c101c0b0b440a8810710314035070f9901803201c4015410010112025003003982000b921011901d2840000b16115500424000c1e040b0400c076402c0610400086d101588140c00034000765055599 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 869384604 1250 869383354 869383369
    0x1315080d14030c31150c0b0406200f190305060a03060b041401030812090a030c0f0f02041a040b0418171e0406030b0907170403050d020418060e06 64
    0x1c200101030000c24a00100d107000303042994030050010a5404c5003115040300c0c040c600302407065180c2030490124120015005900001c80c450f40700708901119a5255698401400e0b9045a40f1802c522250940089807900740106240343c44e2510b02c64031082115001c02a82108030b10900406041206200380340e1500b4075404283c9610080104468000c0404140200050b64010683e244040300000500000800501808031001c101024990300c2014081d660090400021f001a2060b00503002084a51080d10411031155158001c100320390f80001d026a8814a0041d445d12620355001c6030701d01c0d1910400303400f030304103503414803121118030709144c0c2030410104090400b10040c05141c1c4240c3c2200e00701e84020400f201d40b40303181c0c0d00c4103546103001c0c0c20038012031010a00c2e1041402d624606044003920171541540c481e640c0d8096030620a00c40072014000303c041c8030b01440202c011903072600250015065140301600c0302c450090301403040d608603601c100c2d40140d4800600c0425100c03a60b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 869385854 1250 869384604 869384611
    0x117011a010e01031a060409140f0c12070e09040602180f031f09061401030506060901050a060507050c06270901030c170703050a0309031505060913021315080d1403 72
    0x3030001e1045c842c440e004400002d03040445500c058002400718408402d5030100580d40050600c81c02955a148541c1c46002016100c3d28803003001400504080140000c81d10b0f405181481c1403002e150185002c20402d410944040303596903008a00d0308004008884203220014085a428014280134000310340c0b10303040444021043d00f040b085600754814030303802c52228550b101c40c1c00c0045001060804420600c2808203d03031902440000c1802e52801100c101d041c5c0b10700511051010b89043e0041d54590320218040700c1a014410361105942d0f41d0501802201c000401c0611000d000c1040f207403000089030440a22500380c00c001400400d80802c00c040550b001d10000344800d01e50407207107074502141684010b25510031010320008042d4032440807012244125840010f201c02001240282d4000f1100b694201d40040300003800d4482c0c26440403011070018100c441c40e85e4400c4c50000c1a142c10061051040c0da42602c01c00c02802c00f00321000204480c1c0c5800b0744074203414130f1100b907a88000b8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 869387104 1250 869385854 869385857
    0x20712020d211d0d020706030209130905150108010c0f020616140705030d15050d111309020301050a0209120f060402010c080f0c0a020a05060c062202090117011a010e01 74
    0x2d031401c904159642d4090445452080d054800d00e0007001212581c80341031360714900040c01448400600b0360301030300079130350744040041040441d80d2000ea04100208004c403030a9950b44908a090f00101600001c1c543c06443d04000105401e10504005401004030a00380411035103d8420008074042c0c540041c2c050800c07c1c40e00408408044003040180d006020380600a4040081d46501c0030055521a0405500668132044200e640c1c84c2000071070240d015010f00b080c00002d4102a881c605030085281342840a440015003c10381d8001c1713070071101c0840d040e1842c107034001402000c501e040072b84000c2144a540003001085030b2450819141c600240c070080c180300d9110100710810100c00250b818042e02ca078140c5441e24000103103550b440d04886020707405040038800116203030030014120341402c01800001d00b0103840f03916450480103c44161607900f20200a0034000698034401c800e402880c00e0141c42c2c0c803d030116403403582180d50000404c40301c0030305c100d000031550340c212410750714142c000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 869388354 1250 869387104 869387147
    0x71704050d110a03140c01110f030105010e01050405030a0b0a0f06060903020f1203120606160f0c090608030a11191208010e040209040f0c150507030215010b16030c080d020712020d 79
    0x21ba00351180503048601c0c0184c0c6008010032031400214480010314102d40003641c540340000c1e40280195150700c224083c0c581c0681201c0c91081c0890850340c0342c2a001800c0040000b41148646110b008842c0309030003400000e44507140c20020340c608820b10444a2034102c0302340380382c520044940355491043c4414152449294000107203203642d5141942c0c412403070a01c001003440034030300e44002c400900c03c0d412240110608404541010148a80015035500c00011841c0c0035003d00103860400d040701e441003030361280c0ca50100260b5001a42c0c4c1000b60311819018542032405040984082c005070080500250000100310140e0f80d1040d455030030903080414054a030750303581040103407180c2070340002c0035441039490307041e0000e5070200041a16a01075402e940100013601d81c100c03200b04003072281c0c0100000a118841c0a011008040f03500c0740d100b400e11140648882d0348440c426009554881079043e400301c2ca8400b130002c5c2d548203c60860980c0f0203803803000e14105000e040c01044100d0303030180c2c002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 869389604 1250 869388354 869388367
    0x2d080a15091a180d0f0e0d080d1d0d1205060105090a150e031516172a0a120e100e0a0515011508071704050d110a0314 52
    0x11640300320012500440c1020310144814100c105505041d07420700b403d00380c1c1c419003802e4000003150380071001d82159241c45101a044c5411142c800d10000d88070b51000da100c030400300050808000304201880d42c08041040000c4802918410050040340b0400c1d400c40c511440c0001d03441a51080c1d482d100740720000380c0d0303108c50340100c815000300409a45c021204903c0850034225240d038803040c50781d0aa45000c6c0751b40e120001c0c191541c00401c3e8980304199001c02244600943c9000d80845200c140380868030142c40c0c400d400c02c141e00688403101e110000c02141d404429048018083c00704e80b5101ca1850724804517002456502d0100312480150750742c0440321010070041c44501c46000901405111448840203182c0e140c04000004035500c0c4036003442104c17a106041030700b03812903410300c1c0407580c0311041e107205603000c860040940080000c0703054043c00c90039600d0314050250b4005c00040071074038100803015212900e194100c40c1103a018040d0940001d91014041071400c2d03140c10056214078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 869390854 1250 869389604 869389643
    0x3050301091a041a0f040902091b250c09060e13030e0402070b2202030703031103130803070c080c0d062003071215140909070e012d080a 60
    0x11040304050b030340701c3c1c142130807102480384550251500800840e03001181d010304030100401c494801300025040310880700020355041d46605c400d000c2044070114a80751545242c20450f010155282007010503d200d070911040c400800c199030054070142c20200200c0c0e007402014129250010888074030716424009040426203c0c2000c0081300300d001d041503484a55a18101021000840c3d07000c0c4000440c00700c072407410b01c403001c1000703d880e0050058240e81c0e0964500b214082c01000d41c3c02024842003050034068005038610000600c04301c0050b64861059141424880015501640d07851780321490501c03d5680d4046244100b42c0c0c03242c0002100111141c884142a000d091030002d40c003c04020007415542003c1c1d60300c080700d6507601c10054030320305080050004446005101e500105140e1075034250600e481d080f0b4000754198210340b222036650700a03c042d84005d8015061003d03148290401c0301201d011458107a810080603a410b803818441c0c41b030b40d40c407030040b00945003040c05080005000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 869392104 1250 869390854 869390891
    0xc0e04050403020705040609020904050a09022b020d0305070326150112050a0203010302280308090f0307031415010503150415020c0106050a080a0b1501090509150a060c0305030109 79
    0x31710010b07200b4071802e941c1e115418000d400c14070392180074606010008203048100e100d900300944e40109400b41e85844c0c2110740000342c10900d1802c05a40c0300c0148440581c0d00d980443c50154425610140d490b030451500515440312040054441c400c0321300441c038004440750069502152041d00b600d54200385e50012a000c00c072100700c0c140c40311b280c4400c1c0300a0001540040d4140c0f4002d07100800400a02c02650200c400014015400d0f0a0280f81c24400034521074002c20381d01d40018502242c070f10401c0c00007414110b09600494101d084d10040103d0300a050103405a40c03981005a005150300d88808241c50b9092165031454005800c00002c00301700351184480c101e60344e640030031034907448260b10082c000e01160003407600c100054040081d41300390001e0340c054501c1c0e00ca22a29055160000c48100841d4100381d4903050041c4c4c0c6101207016110302c844140b11b0441504100b0300da1200000340145286141c010f1010884604410f80102e0f400c081140e0440d4881d9a0020380c40c00c0300c04401691 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 869393354 1250 869392104 869392109
    0x4020d0b07020a060e0a050d05030714032d0a05092a060c06040c0305070e061c060b0d1a01060f1403130c060f020c100e09060310060b0316030c0e040504030207 70
    0x25074600385007017100020001c0c00b011a14801e4080300c1e148001c454090f0341e0f500080329041300061059446010602040c0e002c0c50b04003c5403450800d00040080d542940c0c03030b03d400381e03d0401c0705820b070130428003c1c05402a55000302050001d0f00d010036420f02104001540e180d000d00011103c002d01a81640b200002c40d41034828100c2522550304091514818241003448260b8252041e0500801c491600b502218020f080050260039280920b19000145032010303001076403501d9480c043c1c1c104548070b520b1010201440360340b410300c0c1e50034440040b0300d0409040e004803003004000b00207100a241c00c1501019407140700192907071683c2d5640e045000c0c003480250000d151882088002031400d8022000641c140e00710780a59600341000810310400001140d01000000c0035450021164246864100c0c4c201e071024007601d03416480074a401c020340b003859004d00001c5100008001e8103030400102c061038041c5a241c18440040d01c0040208075101071092244250380e42c001080425008100d06c500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 869394604 1250 869393354 869393363
    0x70f0525020904080c100b01081612060603060603060e0f010506074706150703020c030f03070b0702010605060912030d0c080a0b010c0803041403210a06090504020d0b07020a 76
    0x24525252601e080d2941140170040303135a00c00c001e0b03820b141d8503403401005409441a0744502d955501c020025080e560b800f04010180601340d00030750007462043c042d91001d009640c8002c201c040c176040004003150210390010540f8070b04c203400c0c001e400c0601a03107a8110340c4101c803280e460303460b582480320b0b0712049081c4d800a0540200101c410b51400700020a01c01c0703900800354444641ca41503041d064800c1180c19942c000d280c00303c426022044400a0310210380a0300c121001c40144c1c0c0080380c41c01e01010200f22696001003a40d03800c1040c0c40c0c03040d07039004c511480284101450700001c00c2240c0100c00c04684241419500380308440810410345208282035401030201040411020740b1049050b00d0602d04c1070308101d4444e0540d40540c1c52084840c0c0c0c484016803031a5540d0300c6010410580d509020707094002001101d010b03024038421600308117040e5001c030215081035075114088884651001c010307241001c0401002d030361100394002d00746030012610413441c1d444040413400c11300d80303110041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 869395854 1250 869394604 869394619
    0x30e1603030c11180c2d090405161d1309060608100e0a0b0a060e010b1c0902060a0c03030b0a0806041109040b0112020a120515070f052502 61
    0x515501030440400340d802241e0005601c2000b83c24090900d901c1154103040310341039004a1441d20001c0010305281544116000180c007000c0031a581c080b5402c0200c0f002030f0030120f40ca080c0351500703125040c3c00c60401031003103408078401c110103410711854059021210510a85800864480b5031a40301011042c0c50f040004901c10b15100e0001c01e604e0042c414244100e1001c02e00c444454410707901e01128540082c40b080e03000d44d40d58030b00d640f0024041e088407519440000b5040c105208554017a0480390761464440c0030042450b50414844962440198280a0030b0740150b07d4540c2165000401d0b2700e0302c00c00d441c8041c01c0580140004941c2c0c690031000150000480507030100300300380103074440d250600325040e94204101c04c003007054901800c102c04440c0104801511505007454692020b050b41c050a0380c3c3d2501701c1141894a041640d25401120103001c9803800e0310344c110f41c000001c0c1840c8090030000c0030001e20034014201d020103942010200e0843d1020a4151000350755802490761 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 869397104 1250 869395854 869395859
    0xa0e0403020a15020c0f0f031806040905090d0f03050c0a08090c090a0e06061905060309190807050c0910150306180209011d150d1407180b19030e16 65
    0x200300951190403d0b0081b0f00078595417000040020407200c54403120600198240b0599081a0031a0081110104d81c8078108200015810140b8052148036241800250100b031003800009031a03c50000c682c002018900f44c10002e041c90700c041907603108841850700425035910701800516103880c0390b42850340284420200109000c03550081071928540c4004d80f40385407542414005103202843d108235071645a42802e01040c10840040c6620106007001c0703c1c1c807007400c0d990b080c4041c0d440785030a6603a100e0011301030b07081c40001c001111520b00b05580307440701403030b0224040081d500e6a001e448000c800301c4281401151007a0040000360948615641506150201d400000c1d4010070a403400b107103000e00c0f9848001060310100350103010180c42d1100c03a90051400e4001355000c00f54412440b6034070030300d40320f0030360034010407074464203240d15507600100f0390081c0380984817115848254107000070841348070000e80b00e82124049003450305011a00e8000c41e204981044c0c80c0c80649401e0300c850303d100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 869398354 1250 869397104 869397143
    0x6030c0c0f05060117071505131d060a0b070b040209060f120f0c01080702120a120e06060102060c070f0f1e240b031b0103020409150801050c0304020a0e0403020a 71
    0x1c444c100c441200050f40400c070342200054a034486441f42c4000391500c0245650844e00580060404402d503d554240c49030b15011150441046480c1264060145a0801480d41404c2c5001406071106060b8a07003482034035a01d10743c000d04001c0000b8003440400001c28031940303400b4010890702c20000c05a0960100c1202416a20078110440c005039210348065101e0300c0d405843c17554041da0b00d42c1e0182151030b5140c1c0c801e0240394010742441080004a1181c0a001041480f07242410405d21001c0c082600784000028909a0b0240503e441c50504000790000501c2403080c0106840c1d004040e0150700b8035900300700c003d100e01c0840c841e441150f0076034040c0401484825548803884101080300c02c05a07142d0b02481115101900c80d43c15a01c40a00010485901380281100348014503015103002c4c0c661000d0001e80390310002d880ca02468052003844110428006c26a00c00c140c0b1014605500e07103500000c498034150b11900b28840032010104060500c2803200c0b208881c5c02030303440003d4100481e40f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 869399604 1250 869398354 869398363
    0xe01140f300c1807030c1809021c02030c16080903061611160e0619080c0102060a02070c0b0a0201240815010f0618150905150c030406030c0c0f05 64
    0x30018042c042c0400790740580c94000050105410780b100703039510507a101c0006500820f0020909018070082212031940340641d010400e0207405034900142e12159240c00514a20404080018000d8014001c0080210080c01541c000154081c4804405901400c2c00c614900c40c180005405020718410000c420064120001d06010300795103450b0960405a601a202d042c0e250303802a84030300c141d50400005041100468100c8001450307007118514412180003148030b50351104034103400c82c0340545410360301846016480a1045c0d0706501c0e090381c9503142c2c40083c4c07c60054a441d801c011500407140e92003507100c400c0311410540020103400342008494401d6130a0700c9179003001d00c1010700341c04c201e0040320f060720704885454802d1404641050410380b4a46110000070003803135400d010020320b00c4144103840303520410301d0310342040541c1043c00380015031041300b488402c503030001c2140c103464103070000072141196000c0c070380003842019070481124203c8a00002610301e01076000c040341440004035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 869400854 1250 869399604 869399689
    0x9030f0711090a1506020106140d051f0507030612050a02010c03050d090510050105030129011803110109061d0402070c03060518010e16151e03020a090e01140f 70
    0x705080e081d175501ca0403401ea5205005c0e2601000c800c0d060103906d800c080d90360300800c0b48900b0039500c00d410300c022841c1210801302c4241d4011a15041848171054140c0b0503103004c0e01645140102070708454a41d9a6a415403040090401403124448424103100d00103548a41c0180001441028000e0905603a00d4807941580031131240b50200004d0325290500c0f4070001c41c2c18042c40304041881c940701070300610000040c0d2905203c0e400c0140d4428107203101ca010040c602c9035858441480c0c0440005203c500a43c0041c0d0602008246141216541072202d4503480f80445d400740e900d407601d01e009103030807c290303000901150805040c40880e44200059030344440620000300080301080d030a44d6134605504007268041105500300340701224a64180000403015030402c001060b0050b80006480e0010200d0300c000a81d021078580c81e00380e0b000d8181d07402000c00b0480541c003541000c40340000c00c840500c590748100c80c0031000040c151101032803600c20107144064101c030704100c100304921155107003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 869402104 1250 869400854 869400881
    0x30c1303060e0d051c0c0e040c0908060f01030305030f09010612140c041a0d02060f030403020f0c101e020a021f110a080306090403020f071d070809030f0711090a 71
    0x402c402c5181403054095812075203502043e405c0081c1c2407694a001800c00e440c2410410030f450308507040a40b0b0b030703000d031403c141081e030780c0c805640703181000150034280c005e0302d20026816030100400100e80c0c0701042d80d4101444040c031402e541c41e41451701e80140080c0d84007501c0d242004a4030414455140c420300b842800f81c03020740302000b494004000c1152060180888a2000c0509961081c10100049003049102034210303481e065101b41e885512b604112000c0380140d0000c0180d00d5100c4041c050b024510340c1c02d803261014040070304005801c1075900c1d0b101901c01c551503131b00c07014102d208104a266080e005050202c01294242c26000003420303048a0034045040d0031908885500000f039170b2000f00f6080022241107031034030010881000e00240090b811403041c04100c2c500d890081c001507000704468032104901906071204c4c1030b47c01000030503000c02e00042004020502d00c000c4200c0312502140614a42d584002c1d1a00080c078080c140300341c640100c50003042100f030052540c402054a500c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 869403354 1250 869402104 869402113
    0xa14010611150702190201050d05090607120b01090501080408090a0806070201240302010f0c0b0f01030201080c071112030403170901031107030504090b2116050a0302060f030c1303060e 81
    0x4840306151844426103144005170321115400e40f40c401c84803c00d0000901c1403520a28000d13003d900b030401e4800548020750141c20030801d10000316003050f00c0720980c00502c0c50a004040b80707140040c2001c101d80c480c032411f010413040040d0401c04540c00300c2d100c81000a21080034552162285965400c0896121000d90728055070113401000c50002111032074007240039141c42c1801c542c011a082180c45448034180121095540f00042001c01110320074a10481503c00c03a42c5140001040c02201600710010440308101c00d00100709100345001c0f4402060b541d070301e00070000050300e92462096074400380c03400c800c4105424100705900001c2c164030400341da0030300203018a55042c44c0f0521030143c00902280007040100b00380100c0f03070825058284020540b451040c408418060890a0402c4409680e041035456014200c6526003840140c0360036100c40c00042e042d03502107400b0344514008042e59000c040000383c1072440700300032200c8004404810103015940d07407412102910a10440d074081d80507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 869404604 1250 869403354 869403373
    0x51e06150304060f09080a050315090103050606240a110d0504180b040b09070e09090c060a05090d0507030c1a25140304060905120f030f030a14010611 66
    0xc00e80e460481030340490145618540341d907691103009208031380c00c07a5280d58031003909601140e4034201520300b900a503290345642e0700c0c00b868401420213190040d1842482684011f00128174006846c5500031016125501c003030010400d080c0000040a1665200c003600103074807940940e11401264168040307a0440d443c00e81c3c560002d807002d0040380205020b603c03c05100c90300259558002e0a1440f0014100241c5240c40350302140c446003088540001103038031015108070714104401c005510060b0440507101501e032240c0003a0040c45030914850810501080031700c0c040c0d8a1240341c1d0003480c0d00c4811500700a6032031600b851040d200c0d204040c1040480c40d4100c0740310b9035420440f0455065590144000c00c5d100c82c07082c0200d5003122054555002d440e610a03590700e4200020f1015000c030362180da5003d480e0404100925030b130414000b0160300405041d4940500010a43d01482c110000d0642c80c1e658090006008052034001442040031000c00095141c3e040148103952004a0701550751440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 869405854 1250 869404604 869404609
    0x140a08060a0306181e020906150d0f0b031606020316030311030a05061201090218071206240507020a0e310c080f060106110f01090c06020f0d080a020304020f0301051e06 74
    0x21000047c1d01700f613644000410038a00a06185207036244110020708142e07140c5580d604075520342c04240b48040e030b9a10b500d0901d01d400c0141d004080c00c00100a04481e0801500039100d001c2c40015807009190b2004900c00c050081d08200305c04100c6804841c1c60b0710701079021501034a01035510a006482000c0510f40107801030040405030f1703401401403031501d00c0485c42c808074480c004100c0341c1003180105503e405440d032409544000c050301080d129000740540f8410401144890b541300c18130008000040042e211640700e40b08542c110500c2440c1940d4801c2c02a544400c1100e0505001c00c400c4080c00340c41c03060326003545400c1e004030301109060b82c46098030344c1d9035440d0100034400343c0d001e1801005950301c10f9170340714200324050302507681084200c00e0131030a561071a80101e072031500c40802404503030781c1000717801d03202ea580d14000d00d8010300014000d02400c40c00f4000020aa400100240a40d114104001200c0324081d00801440c9800700341148540c0f80520510302d00c0c1d580d0f101044072071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 869407104 1250 869405854 869405903
    0x100b010906091a03040212060f07021618050705070f06020304031704081e1e0702090c04060804030f17150415060e060c16030507090c140a08060a030618 67
    0x481c3c10342c0d0206500042c801d00000d554000410899000c202d003511a00600c0c401d200c0c0130700880c0010399541881c2480f400283c00e10042d14414000403003000c408012a06c1403a0104000b5001c00c1400603482d01ca18908440d80e1240520103401d86503240f150000b007150700d60045100d41d00030758807070000c140a0b221800040b40705903006001c42005020100701130114820190f4203911078041c40c0c0c41e1101002c508541000304154180c5241e60101d281015400c100c0800d03a0302804c0c40040516190900320094070000b0082c001400304400c031044907418900941101d249030699034a80b210700e140c1074605c1602c028840c3e000340e0049080c000e95502e0001841248800d892a980f40d07542000d071040b09004464021080702e030306074030500300d503c250110b0b00b00000c8040d50045c1c01a00c0f1082c2005500019904111140c100700444040c42100a881c200c047c0d42c015561440d1564141e242c46000568032451034002410780303890000b00403a007038080501001d0340e501c54440c24011114441416408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 869408354 1250 869407104 869407109
    0x100506090d0b07030603060608010c141603050a090b03190c0201060302011b1e0f020901170a0609060b1f020d0201050606040e1b0a02010c1b0c0e060102030408100b01090609 76
    0xa041001c50030700007101000b01c564410000e1900048103560fa40741c40007075555581c001075550b50740d00440040c06901400840c0710720145070800c3e20f000d442020304503002c031202a001d003c00a01060241503240309110140082901a000b240ca9003060071000c03000c0c3d250a030000341034501e440c81e001006401030103450308030381e01615000f441d050500e81807401c00f064840101ea0787c0812405260302890060324921000d8008c4004800341c00707241c07060100500040c1c024081e05080780000c8246c42c00000707030052031107511030400304642c0741034601200905103030080745a002e110010b014002102c5c8484815641e00c0c1a8210385044104640c01d17400c0342d0302a1103094100d442004148040c2d41d160074516000000312440c28155021201845041e800009510340140d4444608060781580880398441c800c20040486025204950f00c0441c80e00340b503c00c800c2640764150001c1c0780b9a000b401030343c00a1100d9015948881584405400145504000c50307022652a00c1e010488601c5201500203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 869409604 1250 869408354 869408359
    0x6021206120f120901050c010f050f091903030b130c2f0a0210050c0d03050a0633021e0a150213090906060506070609151b03050c190810050609 63
    0x44040d104141941d84e0101c0d030b003141803010420040810324000d1142d84550003c288000070a401d120006103a0039501400300c20721507100320300c0e41900b03600f4078038108440c50b81070a0004090b2250030108003540460980e024040d440c05070308010765600104040b1004401c000000d035201c0c18080c02040c81d0038107110f01c2642c0c0d80449640b90050520103107880440d582818101e040007030101d40076103061f00015145000a4a40f81441515141401007a0140c02c00d09480c1486861072020441c109841c00c080c007030b14454102e0105213140c0240560003004d040c006a9080100d0701c1c2d40e45585e1036503668000c580540001d0400d40765481c00780f003900c1d079503a084e06048400c0c0e860b2a1401000d072060342010f45100e070761500700051640d071340c0000b00b540612450b00455a003c1c2810311607904c02d4054811440181402200300c60f00343c01d000750303500410a9040001c0c403500d441401c40f0242c021101880803120440d03031410607107504040340f1449002d82100e103070080c035110000e201141c02107c08458 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 869410854 1250 869409604 869409613
    0x6110a09050f18100305120f0f030a060e130c0e0f010302090915070903030314010e0112030311131502070807030303020f0d06060518040e0a02041806021206120f 71
    0xc0d1a00021807910382c01e00804618545203019580c0c4198502559814408102400300f00100315003070084101e0312803e254054108284030340316050301c0c4039401202c4503100740000041e000360380b142d0000f80a8000c070103c0320b0a41c0391400c0300c5200302c0040e05041e955880e51610000b101c01c02e00500034072178540c1c28034464403a440c6600b880820700d0b016241c048640910320301d0b80c1625090010b114841c101b81c1e41d500364090b02d5410098200c4058a040c2c0301000c24400c0140b1169034030b641001d0445407061143c4220241c1d60900b14000c00c202d002e4840a52400210040148040300f80f1209132940c1003070102c0351401d0300c07400742c2c3d030f61205200714141900b00c09800c0011030302030340c083d006001c14561380d90710388a603005489080380d01941180001c20004902174100d500e90f0001e036204004155400c00014403c1c508880c0c0e0f603d1500300080c4110788420081060300c242612441c4001d9006c1c070150744643e450001048020402c031a424001d0300c2811145c04103031030005000518007030080140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 869412104 1250 869410854 869410859
    0x90806060a09151e0302090901141803120a06140307080c0d0201090b1216050a1e030902060f030712110901081f03080c100c090603021303140a06110a09 67
    0x800f038503045075416500980994001900c1084808400903c400c4081c1503000504501c104188a24054085d6420341e14008035540f0040c82000110b030482d400c208001041e00c40c1d114440d14502c203900381c0d440c00348600001e00140e010560450001d89a01c894407071490090f100c14143d4400c0035109210096102d444020894180041c2c101c1a00c1c2c0107140030348050b5101c8031086000e901400ca80c44035204502c0401460800300221241000618034046c0e00d009440031000780b5200040041c40d4418007a042c01c08a0745010f644411141a406044a0740b16002c0042d88061900304464440c045649001e800100882034850b00000084202d181c42c100395043c001140d0121000340711040000340c055a811a2200300d40c02c0c44001c500ca840e14a9645440800d05420001d03101580302d4480d0810100710781c8944c02221038016a4010b01c1d00507180d514462501200c40d034540d0020344090707908181c0354004200428281016405200c061105860007074255a5610642500d03400052070007405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 869413354 1250 869412104 869412119
    0x100e0f0c060f03100e25020f03070b09010608071d16090902070c03020301020310031a16050a0c1a160c0b0105130f021b070e220204090f06020406090806060a 69
    0x50342e00582c0c4da40c0b070b520f40240c45040c010455030042e1100014081c100a9021141d40704200380b61038806079102516103c8000c480003131ba03a01070307514014042d07200b100014114200035801079004040701c6044900803540d0701c1075178111440f10400004411b42c4003002481020b00040d081100307450303e68508883d10f260007201c0c0c0003900040e00803035407403500d00b8000000d41d400340003850188071080b40c03062900c1d245251901c2014007a81115000c0d0219a0030025120010303035041c50302c020f06090036695102c10309030442e50030310074840080c025880d038aa6640817513004040d040c407607050800806c8145461030000e0700d020727548041c010031540b1588018030242c28014200c0c644c2d68074548020901b00c040b0440c0c0d80c16604405420014450290721422107100c0800020005010a51000729142841140d0045003c82a01c80320007000380440341208644480d400600865045102c1c507213494148d14015020750300610400300028400030001c9002c440c0070507c58010880184907940c55803803c000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 869414604 1250 869413354 869413357
    0x210020c03030d0b1804030e030f0c09040308280606120902030c0114090a0b030402090106080f010e04170310061d06090d020f060a032304110d050f100e0f0c060f 71
    0x440d103800405d600903681402c4814907000380902d1083d1a100340c2c03281080301340341c03034014020102c005540c0124604074040d1116801c0a8006406140a4503565a8140042400e515200d1366911031100b04619105400a981c46641501c1031940c42c0c414280b0340c00c40c081d0a550320044041c0d855044a1a03400c2e096026403803881c1d200303040105840c1041c0b035002c00114800e2940e4409420741c0400410881140791200300310f80074019505080d441410281ca130864140302c1401140014881c0c000403c0501c44140040e24201705144402650b0b460546080c2c1c00d10b00c03c500c1203102091041108400c944010f1601211116018260504103841c410800c07010541d810750580e0003542559000740a9190400180b04100da280c074086150940d8a0700e82c941101040e01034500d6125010901c400901c502040d0380d403000040306c88001c1c028403420914240542c0b8a03a4241520480c80513000e40e0300a034002002d082c17610402c8e21505640f10340b041e40c17544042c1012681c0041c0c1085110000c0103ca030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 869415854 1250 869414604 869414621
    0xf0906160e0402040801060906080303040305041701020f0703260c0a080612031207091a03010b0a140c0d0813030801060807231804090c050409080c0a0c030210020c03030d 75
    0x5000400940407802141c201c2e03000350805501079450750300900410109016040041070b038103000314550b14207914001c12902450065110b105404c0000d00034600c4250142c40911440c013070041d60310199031401404e42c441407415010300c0054003040c0850020302ca04060300c50303050204181d00e02a08654100c0703800e28000c0100d030384100c4815a402003c502000945868510071403101100d080c0010090700038030305980b0040e05002d448007010042c8080100780d070b0440b10380311021500d0301c0d01c0020aa81c00c00c07043c1850523280102040c0280071138000505540c015440742c40d20340880c1ca4201c1b0404061a60800150200f803190b001001207510410f10980d1112607450402c80704e200c43d4105040c1a80000d14085002c403000c6040000d114a07a52a4200d06008a4040103e200d6035076800c81c02ca0084d11030039104039a2500401e080c04415801c544034528500250307003c40189140403154200103010171b82c00341d500d4401e8425140e00005040120880080055003402007440005020f8000c00c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 869417104 1250 869415854 869415857
    0x80f0915160915050705060903091804051f05010f14060304021207030b090601050f010309050a020f120f060406050612070302100c05011a10181202030c090408070b0f090616 76
    0x25100051005415481000d200c8010b07510139642d00041d09200d80703007c0002d0000002900108141509039a03240460100800e80368400c2c1c82e5aa11410030608203d4444803600a60019104415042046900007410b894955038504040c94440c1c500024150090385642c0c2c01003410000704000d03150002181412074001c204031600681c4a540300c242400082d18031201a40c85280140300b0362400c114113082e840000c2ca0200181c9050f0344515a40e803180910190082c01d5060a00d142911803102c003205503142d02d4103d54a440c003002e100ca40d694803c9a09403001c61900b8081101450201c00d8070398400e4011b80180304544c1181c080100c0d0850b881c03940340501000c5814200010000c1c080d9000502c211127281d0510742c80740082c00b40000d1119902700411400c40b0480c51030700301404100381543c01030450a084111288003080c6061b6800300c0282e8003202590401041051040040c0340302ea2281c50598115100c0b08000e40c0000700035112880c00d604410300282d0002030440030869510300c01d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 869418354 1250 869417104 869417117
    0x3010209060a180509090a060e07270501060503090d0509010512130c05090702150a060509010b1b0a0314390105010f0f0302061c0606080f091516 64
    0x10203002442507840041104046422604444503520510003c44010031003501c0c401c0301c0b07140c010035243d2078030001a03004145070f9846415490382c0c0001c011100181c018014402818002200590000b07090000308929007800d103000480d14500c1007098902030401400242071000b501401a070b940d41052907103504001e0140090808000030032261400f032410302840e00031110b100d09104c0c076030087c90b030040350040e50440c0a00c0361443c1c0c0007c84e48556559a40f080000340c03103140092010b40000e50029911220000001c6240300c1420002c002400d038600220344c0721014520406d85580034084080e000c00d260b1745822152a885900402c0403079020384070000d600c601e00781c5000d48a805112000140100480f03001c400d070b9000d200d207034098542040441500d5181c290b400394003200a0100a02802c400701e5100d001d103c0d560141c041c0300d8001034003404840c0c0c646800a0a0324000c40700880100300b43c00208500c7c480100384418040a86200c10b4991b68542c401c0c1e803a80d002500c01001000380 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 869419604 1250 869418354 869418367
    0xa0207020a23061801020607080408041401050c030d0204330503190603080409151412030c0616030b0d1122050c0a18060c0303050a0b0418021302041404050402030102 73
    0x200e40f0001d28130001c2d024182c24514030070000080c60014018001c809004c14102030001040780e40041c0c070102c503ea03c2c000c0940100780d50040b1241d002d001001e403182c2c0300110b0010080362481d0050403e0b01c008550310121980800380b000c05c0703081081140b0408650b25040000c03020300c1400150340c00403403450041c6642040c001250112101640142d0304072501080501038002d0901540346000e010b10350340c505242c1850714002d180404010300c1885015150b101880781c0105005551480c1c10200513211385107071400c806507007071008020000000386410041481da10b041380d04000c0c800d8120502295031101c80c01803100002445d081c0341c2030b04c0f1202e8044403028503a80551449003038103580150719104014405416410460500402e4040100017482055440802500ca40f501450081200e4941d110194020700c0d00c034014075081030810426a03104425202c82d5000b0360b100f9207043c0c4502094100c1e0304100d000b18080c540b5126078802c888482850706403c829040380c0010700042c40c114 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 869420854 1250 869419604 869419609
    0x3070516060507030605041119020a02030a0b06031204030b0708062b0606080c06120c040306110918240a081501090f0b090a020a02070515120a0207020a23 68
    0x10050002110740c192204100810540d05019040080000741c400b071108040721a000e401c18014a50301c03c814030083c0d51102c05840c402c02614080a03005016900ca10342e43d4204500c0800088441e0f5010b88600e03508610401c08071421141200d8000b00c00001540300d500044602180227070515a000d049418091180744c0241898411044071a4a0f200d40038080c1c034000d01079841507400040541c000303900003003807603d847e800c88440392641d1048902559602e4481d41c140d0240d170304040c102c90300d40503207100300d021984000c2440754021a4090404401c03500703841c0032008104c5182e4856016095141880c8020981071600c0c1c00c00101407011080c0c4649010b4508040543c4003052089407400412a0107454851001d80c016404030078010b5442c1000412060480901000101a8002013815a4910a2144001800c0000c0c440e4040c0084c0c041d510400d500f2685441c10115903820100c2c4d80301200d0f200302d5140e1507014103c00003103450071040c1607044091450000301c500942c2c601203085c1c1d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 869422104 1250 869420854 869420887
    0xa060e060613090f0b10050a0f0f0612022a0606040501061407060207080a02071a12191b0305100504090f0320010603060603060c170402090c0f03040623010f060302030705 75
    0x400c4108803011b603e070300d8a010020705841641c402c3e003120740154401c0c00450249040c01c030030b446c09030511981140d09186064002d1041c65200c02c04030000c0400007418003c2c001000c031400e00300004540f032035110b00b000c00c4121103080c4118408100ea4403d0805100300000141120a000e60750060421038145c83d6144030b5844010f055005030030024007840038581ea036000111800100801e10b0920b07020040a00310258060810300c03090450004001c0e0014540d0842503603884540e81c0380d84044080c14010b40509815100100b500ca40c208001c180780c00c040c464503002ca6044826804581c0440c0c5086d02c003480c0880000f4614071009000e510100000d0107035500840c424500050ba1501d035007021000c803111401034030104880d105030000c1c440075200c0480d402c9a0100c4121070141c071840075400e490700c0750099142c1e068001204000074001203078403404035800c40841d88046901c04140503030142c0c50034012080b92007140807091050911a80c00f43d503200e000c50034410710304640d0314418400c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 869423354 1250 869422104 869422111
    0x70e0613020301030507170303011508040c0b0c0109230303010e180714010306062d020304091107020f0913080702030a020604080a0309090e1b03010f0e0a060e060613090f0b 76
    0x46606c0840d08005c00000e98001c01c00984001e40a9800d45d410700c9455224114510000410800a070022600f03000562000da070050400c0442c0a030340707080f2044068080e184000060f26100d0040d4503c9407107146601404040c01074801c05913165a00380b803c07040181c40d000d080c0500d07000b41420700c3c19040500f000000c0c0540600d018a9207000d0380c00300010140d6016411207001c0151340c6a002203400c12800322607070590142c502030a01c0145110f8201c0c55409a644410103082c200100040c507034010800400d01c1d0350090780c0e240700007000c88041c00340b4240c00b0b0341c04d0a16140c5002d140f1001c5628200944002071005080d200c4240303035500004c8140d0056004480709810910524041540040040004000400c8140400c41e4030113a19a1035061003080005295004034a02c192a5401c0d8011080d0100140301040780d010046d0031290744078420700049403d20300c0c04440019071480052158802d460050600c1c162014183c0341c24042c1c01040011104142c913428003100254110786110320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 869424460 1106 869423354 869423363
    0x2007390b09130c12061e0e0c0415030e010b040501060210090602090604060507031404030c03141c020d090e06090403030c0504081605150903070e061302030103 70
    0x10b038410b5034010303840001c0c80d04104040305504401109074401098408001254942d060401600220a1000c1440d00108070820104501016180e80250041030170b41c2810390760781b603a900e0840c1e00c04004010946504500b030340c0440902c542014901c0c116004d228551600d200a510348a40d820600801ca807240da004042c040d01e070301101c4c0c216802a010a0b521540d030381c0010441d0700003820460004000c0d403040f5807040d0a420640301030366004013501c040b4a1450760340e4240c041812407460098025182030845140d803402103c034107042c0c96009401c05003002d04001709441001d80041000d05100c6051150715203800408a60080d4103060014507600900e03c00d8585000720b501c01015446050300d03016032813a0451100c41140c000340c840220440d0030780741d02d41c42400348242c00354241c0c2c0461340030021b40030307004410341c1c0043c030241c0302d41070b48000740d1040c0303050381d000340c00030348 = true := by decide +kernel

theorem cover : BRFrame.Cov 869244604 869424460 := by
  have h0 := BRFrame.cov_init 869244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 869244604 ≤ n) (h2 : n < 869424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
