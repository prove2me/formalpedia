-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5089
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:42:58.304822+00:00
-- url     : https://prove2.me/submissions/0b87d12e-d471-4862-b455-767594fc45f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 915107913 ≤ n < 915287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 915109163 1250 915107913 915107933
    0x3020d02010f031b0c031709280812060922021011060c1b0c090115110f010f050a0212060f0d140607090b0c0705040218040911040b0d 59
    0x8000d0411036504074039000b6a000b070b08001c000602d01c031a20078603141e20640c0241442da0829040e0005101420804480890b03448541d02811040015007818030200c00207001e00c07402100e16115030003500c1e01042c0071500c5007014280820118504034020704100e010003003501c40c0980301211558100402c0905000d00f403e80e01101750341540d100300c4c91600110b080d10302e41a03114032400c0034040c0004000b03240348084003c221800650305c1c000700358850080f030f440d0b452800d00e10154000300741400500c155500103620071034005082c0341c6584800e031003110040c2042c1e482c440c615141e80d142c0015821841082c05000d80c06100007100b182002d5000c10240900c00010304410b0040342000e261070020b4a0300040b100700207400c0b880c40d0710b00040d10303d010313991030300c2c100c800c6000501211008181e4890b0f070001c661030b0f800f50360020b104090402c001c200095000710b6110b031440c49040300ea0030003038640d13000d1041750601446c0e029010011000500c010b03134041400483c8598901c581100011700c00c41c1c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 915110413 1250 915109163 915109189
    0x130f0b0313020f0604030f03090504060f051e0f0315010303030b0f33070c050a0e010609090c0201200d0b03011817131502010c180b0705070915031b0302 67
    0x43c4110451052030101d400c030b110b1070704050914070a459641d0103254000b00345a00303c1e0b5065a0810810307560300c036a104100010300a10358000c482010080b42407040641c604400d0310000d24203c3c505000f040001d141510a1012402d0b41c0c2c503520041003415014811410082c1081e140c0c0f0001c00b03291000174061050684440701200350f50360755007a06080821150b2140541c000b000d030760740c44550801411803400341c80740034800c1550500209118242045e80b5040303900540b0351502980c00c04206201034070142075200115980c0d01c2e110401c943c2e043c01055050088140c036160b42d07202110491054821b024461f9009030304006440383c0c100000d1502c4081f07507070003500d0904002e101d00d038030051a1050450b008103e00b2200320214940e03509001850100c040c0c3c0d002084071507140c500c25598000780c44c252540d010f02105e420800503c40e1001410f00324421001e99081d152117030038600458022080c0c500740780c1544003041c4100815071b42c0100c481d40c40740c0b4142d1059407a650020700000100c20f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 915111663 1250 915110413 915110419
    0x5040c05190e06030c0c0106090b060901080c130b040e0702010c0f050d020d0606030203090d1b021002012009030f191b030f060f0507030b030d03021806130f0b031302 73
    0x6070404500d0707440b8044541c44100010b080c2070f0b807402d050310401405d4011120500c440d5190200015850700f10384070304803003500b001e814541418140f00040d0303022500103100301006581005034011100d60340c0c644d4406010008074544e2550704100d40c804543d00010420000d582c584000460b4944e0012400c00c540d40141c504240e881c101c0c0b0001341c01074000c40040f100140d060400100304150185c020b103115101c228112044c44a088004031410311042e00540c5030015080200320150030940c029520b007008a00010030101b00b844002c001d03480ca4034071a80c90034000420484a185800e220b01f20030300b00081c00800300410b1700c061944400b0b00483c4000c0141e00002c20340c0f54000042c4103104001c60300011401c000000c942000f40c090003a036951850031620b0200000c100a019101d0000142030281c005d00309034041c01c1c8154002d5000000d111a00044005c9020155544100a100400c000d1039032061103450310605040da0351264105804011090080140035018049215071103a011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 915112913 1250 915111663 915111697
    0x20303041703131b0602190b0c0d0e03181201090308061215010b0702090c0301140f01020c0a030809150306010507031d04020d1407052514030301030b040c05040c05 72
    0x89003010444500200d03001303000520038400f244540300c00810200880d1055029170360168a50036a43d03100ca400100c0c0180780201240105626000d00805040303416401d0000191802803449d00c1072450f0000c0b0b9541c2314040c5c88400310007032410320001c1080710211500c001d010000782e654024000f0500200110300800c10508540300800017041904007600920b01400b24079611440e4100380740c1e20044050703000b090146d0201c0c0c0700c00c54000c100c9040300d6072a04401c1c03240441d007041000c2c0c030b00111102811803103a281c0b03046641c0d96001194004500c103041039582d903281c800900c4102072030301d8841c91a030b103c14820868a039030040b049814a0707a062615803400040380031404003034000420301942092020a4030707400b103900ba40c44230031501d03011a1814001c0d5a101d900312254414001500200030191103455080c44076038800c0e010551080801440101030400b0340c13803554009a1090700d144215400348818041c0354202c810261405031000c0c0041c00000c40301030400d12407044420b640b0440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 915114163 1250 915112913 915112921
    0xf01060e091e0703020d0b070806180708191a09100f0302060c0f0d050a02010e0a020a060e13090303020307110109020603040f052109010201150f0b1c090c15020303041703 75
    0x109000f140041d550080550789910050304241c84c5c0f402c400c031109408030721540041281840c040f070301000c400c42004054282560f40c4c0d001110201e0300a0001b40482d00d110403001c418403018054090900c14030f507151900403000e4000c2000040014200c46c40400042400b80000348500c04080140c13a016185641c0d100850f00c01c0500d00748c40324203180c50303e0180f1040008180c0e40721004146c00000c60303000b4469580000c803c55114544800700942c800b40e04202000100d0103800e0b400c1e440c0307400503c80da0005806400c801c0c266580b8900450001c1c0d800801c0254045d000b400395140552031314020810740b1100c1d40801c0c014400580040d008403c02c21505040040810035000e556200c442210700c41d00500308400015007050400ca800340d4245440c0c00080c080f0105510b0485d840454030000301444d2807181200359000c4103050440030b0100400d110f46a04e80c1c020821298480c02180368003034038044880b0070300b200c01104101190800c00034080403400c480102000289080c887c04c1d901d4807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 915115413 1250 915114163 915114223
    0xd0c0308032806151d041509050f060909030a050a050d0603050124090c050f0d090b240103020301150815032a0a0b071401060f03050f01060e09 63
    0x4429100c00d22500c40c5011034080070307640040f01110407600c031412803558044001c0d80c1106500083c0d07400d08003480d80010319440c0c650069001c404002c01d030440b82c1500c8050040a0329001c450004540c0002e50034000c0364100098115031112149010314101158558014818410700c2c8a120170400d02280003003030b84030140c3c40f181c0250303031010080040140000d524079031801e40c2c1440e0300700c00e0f007500c00c000307007024480c00f4020031030500ea6945440c054140703c011480303400901602014aa44481180004100343c0c00d450013040d1a2039010004252002043c00c40441c00100314105801803004102e400282c5880250081c010300f00104030ba516540c1e9000b040024501d4640e1500c1042c02c00760208590807204600e800c410b4000b0724411413180180b01c82c1a140f0f00c902d2503078a00c10000103002c42c21104100c0540c5c0346003000400c1c0030365599405050b8626580040d00c03541c0200c0d81c8182c1c50380c400d02c90403006060325520410311b49482200c880d12000b40215440903e0440c2c916086002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 915116663 1250 915115413 915115441
    0xb0403060209130e0615030f190f1a090c01021204050402160c09090506090a0f03050d020906030c04240806150904020a18060e0a0b0d1d0c0a050d0c030803 68
    0x26282d001e0400844503004403050783c5c2c000c1600d60351080e202205200340c50342004508401c0d628130703130802450840740210205100c0098460305075180480c003628000065810885048034010035018032116041251125007007031403580c0b455056500c20241c0d905141030b0b070b01c1990b003100c0c01203400507110311020710040e142c0007400724000c1421406a1012035694031561102001c1030280040720400c1c0d9604d0416a62a0401c54001c0d182808660707140c000a44500d0007814ac50380d0214001d030034007010002143c1103420641d00e506071b01001080034071880408054100c00c0030f800340320040b940420b08501600030032014051038003c98403c82d40000314402801110b4000c04054000c56030307030803000b030000c020700440b085c44088001070450004044c1c0c0309100560304060300030a1110154034080c00815640d0002c10a56102611030b2030381c01e4940c0e034829a0444007804c00b400b5140303014103041049804c204a4200600c251016004640811f000d01003500903070350702036645960b9449050040e2045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 915117913 1250 915116663 915116689
    0x1203020f1201060504090b1912083f0708011802070818040605090108100b120d0c0b0112030c0f03231305090c070b0403091d100803040b0403060209 65
    0x2a0101c000150f10754041c3c0100300b01c4000090802481441074100284004c4e42c190158400904030400c0c40b4000c1c3c04030341c01209034482c1032001d02c0e180c1e110800d1005003511203040c10010a1821203d8a40e05401f0141040030b00598040301b61441c080802030801030041c0543c627444800000070040c800440e030f040f540c0c4181c1001c205601c402d0941400303003141c0c44480b2418080e5041c4070000589041c20903c144c140c40d06c040c0a4428149480c0005d802440c0900285900905c2c11140609841d4184010032460403980c2e901041d505103818020000074040e07000042c1440b245500002082d408188075181e0395105850340c4046460781801c13103121000c03c495095010800401c0b50510291000030322428680300c074900c02c0c80303030f80e401044031041702100ca46601240c104460f200068a11045540c401c0c428201b0045083d16420103e0f82c0725001585041ca1140100901c05d881c242000400000e000d050021740c80c140c201020075500340200e10005182d180c020803030000c5551040c41203014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 915119163 1250 915117913 915117937
    0x6060225090f02071104060b160c03060603050604020f010e03120c0f031c11030106080606211e010e0601020d1b0204020a051c0e0601120f02030a0318090203041203020f 74
    0x924480003051030001d5104d03040072141c40c0b002c501c0c00022030402d4020705e400c68852400c1642400181d4044141400d600e00080b0b4442c1841c0c18003000281140c818500a036025a005015520749031041c07008528889070304a05100010380100d2242d600002c112401d050f2030481140c03160900c860242c03a241100c0400c00e00f03400b020640300c0d0305902d8540c0b103441048454034103201018000400c200381d131000b80100e41c006444400064498200b420040108401c0b5488003070b011024155a8000810300382c03809440c6d0010700401e0403003401d1550002e4098034810f48072403050b0611400113983c61101c400c00600307010400c240700e601041c441e030310350340040e801a006554a40d00c418008007280c3c07180800321390205200c0008444011180700c0c1c9078407814810300601059082c05040849078607040380c12507500500c00d0072500141c4083c003003e4a40ba01c00e0301c031301500104803241c400700e424280c4c1015111610500800010429080039400c090034203041c011303175801a80744a581c0503c550801c1070300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 915120413 1250 915119163 915119171
    0x150c070204020405041409060c030f0c07030c1208010503160b160219031214090f01030b060d02040e010e070f0207121a040b1005040b24040e0a020d0c030606022509 72
    0x400d06100c6c030030103132140408900f521a141c0e981001c1d4000c5000a540317061003c0001c20006684545200c0180700c0c05001381045200c85100d59a500e031508a200c540600041d040e0004110900b802c000d442111610a0303c2402110304080d10000d0a00070031240c0405000e41504900554942089940c10070050056415450fa228100300c203c403a650010360380000d900780c002021407001c41054544171303a0b0091081035180310880044010b0081f0850003580000d04100d01e80180c0300e54070081004021801a20460b03600d805891240303010000d00020500920344104d0450541c049a0441503900140c1c00301d440b03031403904100c3e2000514500c3c030113550381d1180030711080c0842c0c00c06192007041a104601c4115441c1c01c248400d552909011540040a5080560081301d04108a03910703038007400c2441d41491303652180c1040114088e10080e038510740c0001d120348400c24070b01414040c6007040c1014071080d450410000d5407404001203986520800c092a030800f1032980c280b00000f800e10f400c0a02c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 915121663 1250 915120413 915120431
    0xa210e030a02150106030b130908090a031a01080d080a11040e040501090c150c170d060308040602060a02070f260a020c190311010f030f090c060809150c07020402040504 74
    0x41c0d0740340f003950324026811000c0c10000031594464012215142030141000c500c100340764011034040d02c41703043d04031000b441c10702c081406602e0f00f604400003075004450040742e460103d900d04002c800c04ac0c11102c441e0b00100e512032882500402100e4220080120006130711003150f0350940f10b409107411003480d50040e10144003c1c0b04054011100e030034041c0c03400034607540d6103103001d0801c0c4d40c116045c200840d21541c003000100311070607203107101108045500c47c50041d0500c4e00d481240c2c0c00d600122914000031805000745a81004143d9015500c0f401c11468000e00d6201c1482907018804d0041c02d02c201d0300c14005a4581d0b802c0a000301e0207494500f552100c4041c00c029450700b450300d100c24041c1c10300c00d100c001d820007520081c0044075008002c180c60080700800454114034003640801c245500d400044100709603501c03c4030741d00c500031140a80c009091140082406502800d241880e500100c1c2c441d50020031041680e800ca0898040d440d07039088584085006405240d110b180d100d4039081280b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 915122913 1250 915121663 915121667
    0xf020705030a0c050319020f060a0e06030403020f150c040e06040f09081e21070215090d0f0e090a0203061c0501060e0601110c060706110a021e01020a210e030a 70
    0x201041e13600460640e0300511001c0d104041d040301a400195000b071980341c1611960810350020025a401882c0411008000d4030120741c40c5d600c180c40441c01a400400804001c0e602071282d02c070301891110f07c5074002d00b000120305030075000c0ea01600c01d125100c0c20229040703503100d501040315042400001d0169031790f0742c18402c03103580140d002c004021a0744441803036090b400c0e20866100d03006404848120030701550700c0f81c0000c5070040c144001d5205809000115400286220b03108101c440010304070940307108801491200c0800c000d4061150b14000c0c603000d03644940391a54002d484050050300ca90340d0100080305400410141184441d02144c55000e12206421150a44205070440e01c1c1035150700004640d18000e00d504c0851580112005138400e1610800908165004840114107034142c0c640d0102c584d0300c000346800c05a40423020b00c0100c0c0340d03a100310503a1403802034000c5040c00c003010009019501000e079100724520b02d44501c000d000d1000ea20903203204500108490b1220004540 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 915124163 1250 915122913 915122933
    0x9040309092a032012010b0306030705120304030302070e0f04060b4b1503090115060c052b031107060c17060906100e01091703130b03100302010f020705030a 69
    0xa24a04c811002c0c14100c400d502400c00ca6110721110710f409150343c0e2a00021f25240c0e00003614032603050140d0000000c2d10303903410071601e4103403808402841c0e80d9460741c60040c0c40e00c6031036802640f034680b5900030001640169050303194080c0e0018001b0030303c214800d0015966501030600c0004403800700c400d0303442000070700003810348082c040c2c88070082490003010050050001c0240315684145003101402150101e1001765420002000020070101345015441145036250303081080019003250941c000e00004200c2002c20310100640e500c40070741c1000300d4074405144601002d0601d80c4403d02002e840e05030800316400180c1000c42044044c48481d00103001d440c0501c3c0d249510011480420703240c0c0f4003059814016840100042c0c05c8084a04003500c505840c3d0380301506108150b040000c0000944000700065094000038596030080801303031001074550ba0f0481e41e501503050040040d6241302c0b4401100b0b407034090819a00720103003420102d150110300e82110350140203030403624042180c0340070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 915125413 1250 915124163 915124181
    0x50c0106050609030a031b0b0c0702041415010c080909010807050306161205130b090723030607050f07080d0b0a050f280909050a0506010509040309092a03 68
    0xa0004640e101c040101a000c1c080d9210b916070058007a00780024012a04e99206e251220740300039642c001601c444075245411201c55071205030002d0041d046282034030401031151083d10006201d410808001c0e00e0f00e802d5010464140f1a680414000b401900016600700050051070030041e50785400804e40c82d40b40750301c02c1c41e02921400010440840d6208004151020250394202110781c83d40460000303000f002d400800386512113501100851310745002e02e8821206500103000d020b01d02821009101c0d0264190103841810380340000a580d00880d5640d0400107603c0c15986440c1542002015442940c500500422001480300c00e6a01c4d190000b42075054102c2d1600340c07035582d40050240019490015603030110074030b1341818146c25140700d50f0741c58824404020f9222512259283d0072510845410745147d4415080b060801200300700b024003504060741c0d007200b642025500949240ca2500071107145517211070302001310a1000b00600b4100c0d40039a001007140b02841005402008900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 915126663 1250 915125413 915125437
    0xc070314010605041b1e0504050d030201050f130206040b0a03150608060a1703120a06080f01090611090a0905040f2102010606020106060c1e0807230c0112181205 71
    0x800000070300c0780b440c00308610203003241d1152150303001a80010049440c45424206c00d0000501000c0380d0360319003c42c0d070440c1510a400004503410140742408540c88010581d4540000280300d10006840d81d00544007210b40c6402c40648400c201c0105074003500c1051143c0c2c0c2802d04d0b0b80f0001440d00c0d403220b40c040c050442612100c2800341c840d03101d9403455414994141841e8010400810b240a50455599101c0c0d8400170000701242c0b121507050401e40200d403c00c1030b50307445c0c040940500c9854030030410035080041080380741c00b507024049140060340381b1512a40d141e07108001428005c42003007000c0b80c1c17031f4820fa81005030014040440d03241303040b58070700000662901d5000321b48140140b18490507200340f038984400d0309000391356844182c0e0740e0704641401d60611030800d0000550030b2001d001c0c0e0502c103510501c040941c0030b581c4c1c0c91500c0f0350007040300d40380d02c01004410966000b803125030706442e0030b81011548806180481c980c8042c1c010f401018a01e4a810150710700d84d10502a1400014034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 915127913 1250 915126663 915126671
    0x1a0c0403060e060f0103030c03020f240109060e010515041e08010f090c0b070c0e010608011d160e0f0a060201020d0609090b0610020708060a020415230c07031401060504 74
    0x1503500203540c3c040032603d080c02a182c040051011034062290f040307010344a44100d5040ba109400307101d040c2a200b510014800000d0032501c690794000c48825409010154400c004040c075005440d0446001803089078024013022510080303d503580004c5030040c04046c01c20412103200005080f5030300010f80314100003035203032161440d504986030007002260340e0031240d06050b40741416104929680a02030071078140b1458440080c40d1800199204e0090880e030300c0e07000466150402c12030f02c07010718107210000600c1440070040b280d440980702042c00d41140c030301407007111000e90100d130015880d2007401e9405480c1c0315001803104d5054004001d02030790000140103481d6104207003002d48054080040180305920001841401c180503001c00000051040721012503403482950705084069440c50302050300081c060040104030b996112400c046494500e002c3d00d9240031700038a800a03100541c1440310b00260901845c44204903c1340070b1900300c0c141c800f08540c5800303000d00030002485414000d60070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 915129163 1250 915127913 915127931
    0xe0321071b0f0308011d01140102010b03010e06070f0c0507180e0102030a090c0b07020d0206070c030f050f070f050105031303030b030d031406220906090b01032406211a0c040306 78
    0x6d40406031070b00000c2c8001d1000da0f90a100c0c0e420030182e1401f4240341150350f80c04407000183d0b002d000b00100c101054010344100d00f0711110040c640c2d800240c0c400c0a008140c04050b00003140080d04100300ca40100d00490102c0301c405560000e018203e0490807079600203c103111031030740c2603881400a18820515101102d5546440042c280a500310181d4010354080d10b220250900400130030016115010b984189900e9036070300040d540c44002e041d100c0d60303c81030410102c80b07010080b00000c3e10404000c680f91520b080f0009140c2d210007010500003010f200072550425000350041a031455005003600e80c61548540010001d0202c54103d043c18105d18011a40d90708148684004034030701c05902c20070fa034020501d004098011100100c0350a991500050081991102518042c501c115041e20b540c2c042242c81d07580c4894200220041c917071802c40204146103108201c08034040c82d20b02001203c10217030812a0380d00200b4212a64100c0d08001000009140000144103991180e0380c10040040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 915130413 1250 915129163 915129179
    0x4060203101707050112020705120403050d1e0c060603050f030c190f0206130317030f07021204090f0609020403050c030715170a020c120901030e0321071b0f030801 72
    0x410b8240c1d04142c0092400b804254070400c0220303060004100c026140569a6503007a180c01c562444200308164003207018020410240400300c0d00c0746151801c10480c2c10905680c1c014504402c202d40f040c042c40030000410410590000030045030000140c0390803010300088141c89601038401032519002d803450000b4440950280f03030541c1504034502d81c50f800d00c81c0c2c1c00c0c0282c0340d2100c00610f8141c8540306000000906440e040c0d0003181c20307105030355101e01340580f00324581040681004150742002c40b040c400b494070306040e40c04903162450041039034140242040c00a02c0243c2104820900015003c002d04c0800920342000c01d074160100c605099031412000c001940c50311a28000401446030400008803070581d49800c200501c01c010f240a880d8100e8a00d030004440381804055030100b01c9801d00d40c1c140c49405094400c490240d0f207031075000c25403902800e2155000c03d058264000102d80c1e03d41c424641040400e0341e402d030b910341074041d07030400e076040507900c010840000b04100000315084c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 915131663 1250 915130413 915130439
    0x106091d0303040c090507050f030a020403020f031b010f11011103060102210726130e011a030c220603021e0406020a0201030b1309061b1103220306050406020310 71
    0x280e01300c100e40b0000b0b8100100c5101405011b02000c00f00981440354181c0d12040d14001c40c00b681203200d005949900d9881401030340102402d10307034465005082c1d21034100c2501508107007103c00929010f5102030400000342c41003111503180754990341c0f030548119001e40b2060010740c0142026021601d100410a41a101e001900314007242a614244644800142c0d01c5040d01c80482e0f100e645500c1400c04060301500a0b00005044000b018102008001105020300c080c1d000d000f1188c0c1108103140c0b1501600c0d00c82c030011f40b03855080c500024445020461001108420101014502070882d41d5031030001c01a42103a40840a011400a60b900b01034400c58201c0e0100c41c896000b405140030755400640c010500d42400d180c00600e4410400071240b1a4420803810038400c0070001400420480b10f2080e002801e241041401101c021400d400da8000003625071022003d070031b414828103100f001c00a035014540c0020403180c101000c0c4810407070aa0080c1d44a1204466240030641c1e03243c00e211004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 915132913 1250 915131663 915131671
    0x120405010b040e0d0c020604180504030909020a09031728030509070f0e071e0324030c1203030603050604030c02030f150c0d020412050a050d0518120c030106091d0303 73
    0x784d8008008000c41c1030241030490300c0075000802ca607061541e5036815180d01c20203800d903510100c0c1e0b07400405c0200354001d09024098041c070441182031890305440078185c000315000c05050501d441d004009410751410407107001a200320003410340c00c000704060307442c42c00002c2d141b10046414200007441d080c0001a080040b107aa0303046030081c092070500400d80030103028043c80104a590300003600720512002d240605450b0a9800003008685050365600d038007031803044c1e41c140d0f0301e01010402c003103241c0300329000c1540c2180e11010240314040c54154001c2c81c040d0300043c03950161004000a164001d0200076006000b9000e0702d01a4201044082d1101c0c150000ca9a10000c1000406c1e9404030701e00150143c80e01c10100140b601d038585c00e42c54407800e000c02007110580c0c0242c444200b048024804124051510b00303015050140b001890301c61540c0c12a01c81e806004910601480380f08100300c04c868806000c3c0003001010f40b203243c1803004d40031761000420303034141c0e4079211030741160000100c0740702d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 915134163 1250 915132913 915132941
    0x30503041a1303020603180d050c1006050a05040b03030c061e0112021806300f061315090209130215252f0f0d050d0320120405010b04 59
    0x103481c1950300300f00c0d45d40c101034254500505111803013032008004006040080c9021b8541d603840f1043c9003961840c0600401e0780c18285403c1c50000c0010303860f00c3c1c0c1e42c40c081da0021070340802e01c0d0718070001192030340c090f0700d00b00b2550b44110310601c515000800b005c441030394014030302c042c42d03a80c9407082d8801c00d0154050007500102c505507040d901c501080f04154000701c000b0528200441414080703440e0300f1204000c40760302440c1c41d10b620a2200200140200d403000100a40305500e4140e28504c4a50768000020303003c00b40c00280c0909160f82035010310043c82d0300800e007601c3c1c0e0400c00d400701084103049500324051368400b55011440105c01d015070b01c41052801d1170707048002580d9084201d034a03650000b290790103e1450102400300075288039030315040c0c0b85416214503040318020000e01c9060085201d00801e040b08aa00110f1804a13200c035142d0316605010600c4c100b05208054103803448030100c8201580801c0348062440c0e03240400d801140114024451000040200811035900c0841403403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 915135413 1250 915134163 915134197
    0x90209040b0c0c10150f0b0d050a0b130f050c0310050d0213180614010513020a0c0501060807090b090903030f1e010f030311160506091504030503041a 66
    0x40012000c40440354050b03072490040e0b0030854000d1985151110200035002c58984510120400c0c0440e40703040c0c03009001d4561540e00c90b500d40400100380b44984412500e90340d850f00d001510410745500611070a0801424210a07026078400150051034040120641c02e41040c0100d02a0440c1d8015280640060900d08161a28102c10010100c0400b1412a0031100000b9400c84075001e0703101305480c20006004240d284c000602d0f042003160114964804808162130040c032850f1142c01802c03001e803280b00d130010b03680c00d152542550144210704000340258281140031a40d094085980700488010072414400c50100c0020002c0c07581d41101c0d211341c580d0061001403400d0414a4003075811480c0e0751200554000082c2ca54801180240c000042081000100b0800c06038040989004241580050625100100c0c820381c4100d0180c410903104040206908100b0307502c2e140000544010603d440f0760359540c0e8604151241c100b84140d041d25203440d4401035042c03c0702c000715940364502140c011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 915136663 1250 915135413 915135421
    0x3080415020c060c092e03020c07030203060103210c030e060a1701091d012703180b0307140703020604170c01020c0d110304030f062703090312410d050106020709090209 74
    0x800a400c03072740384050540310f919000000f60320207000c10b50186003d2589803001c0041d041c1000c1688048014803810003150514100c0480d901119501d002c88003203880c141da854500c117044507400b92440f0700d8008190100300014110a00d9403040c881b0882c1c04040c40010043e16020b607088407031070560b07000214500c0d5000d210b030040d2000c100500520a0034034401261031042425040c42140c2c004445000002040c09000c7c1d400c1403c02594080b030001441c40c00d070096400075201c5d140a0b000400000c0b504900c0112100c00d48155070300201c26600864036440b50f080c00c4d0342eaa80061046002103a075060101c51a500302204072016a034011410a074403410340d540c1e040040440300c40341c40301c4543d00c210401003140021440c03140540a0340c1d51600840c00c6081444944241100440c14407128400344180c0b100c00c181130b07450310b80d4810340070030000030701400d00817080c20015030a076550400044d00a201504ad640514107894540d422600e041e6258171041c812104142e8000c0d41c000512800a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 915137913 1250 915136663 915136667
    0x51008090c0411161a040305070314040b1c0f0e0c090f0721060902041d0a020423030c1008220b060f031507020a03030506060703080415020c060c092e 66
    0xa04c04440c440c0304e4500c0c05005003c406558a82c0917201200014000030f207140074540e00030460848078028402c96850545000d00e9a5858400e40c061402d01000d801303a816032004550b404000c804140003818040020500c0071540c948011110070307803081071904041402d115600c004e0620468140e25103e4901c0c0039203000c140008e8800689504a43c0ca620303021441d0411400900000d100154040c00f02a03102d0800d015501c000821a0509038070500c010000400030000c03c1d01e411022013021010750300c926000ca4209400c182c01380307803c0440000d44600495011940c14490320b01d048092200200604601208081c903072400713086a181400460b07014607056800c90182031005040300d50031080580483c1c4c070641c08550990140e04150318079418182c0501070701c5d84c043c8044604924040607540e018004101c041c102406d04400419100070b050f6290b03048803a8501e1510485031540740c07603500c007811903000040031401400010940c55184c660a1405000282c581c500340c2800c160b031140c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 915139163 1250 915137913 915137947
    0xd0c0311010603020d030306032a06050901090b0403110901120206070201210501030309171513030c080c061b19110102040b0c0a0c0f1a13051008090c0411 68
    0x500c01280d5a9410000010381e514000b40d180301c0e00c079803008074241d440e600f00400390a550806106c82000149107002070400300310205030640d41c141c1003036034988280300f00490310003000360004188268005804018001e0045896090600c00c99a800040c3c1e00c401141d05040951030009400c01c20521030307000191f02800f0014000e661000c81000c81c40401201c20090b1a020707072040d008585203200c1444500301c10302d40c04548405000c000c2c0714101021b1070419191200503c00e100c078021500a55040611610337208040a4202d00030b942c1352003400100c1a141e08081c2e80031605c0070000040031901e00c1584007903442c002c00e0000c4104244070b0f0040d050390015104100c0982a5600700300112395030401401600480c102d0300014107a10b0482c1c035005802040c5900300c0420300b032440404000c6140c481d0344003140220504581340c0c880440d90400356641405030001c0d035028414140c00c80001e54000986442a00d20b20100c8442000d007400307100807207500150090050808101d00300c16030b82c0f0016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 915140413 1250 915139163 915139187
    0x109140409020d060c0c0c0609030312051005060408030c070909020d0b18031626041503090c0810140c091509030f0f060906060607060e1002040f050901080d0c03 71
    0x300035020240d2a541e01c4c0201c56030901c0d114045508820150300740041d041e01c1d04081c08071410b00790101415900c01600d1000542c000302c102945030f400003160700054854000007000e016283e80c3d19a0740b1907000e280c40782c00c24408404140716141c40058002080d008140b01176030040c00b007035034450060311001c2d1424070080081004140251040c900407004000a0001f603d03500703174403c086d01061505100109540c40080307410414100c0700d000b1003000d041110119018240810f030f240c00c11842c02d034080c264109014003072250702007002a01150115002030303000b0000a042100e500d040d025540804ca007036403d00d4100d542808a0840d0f801d2109075800301f1240c1c860132500344042d01e00028904400403003410600c0e0002d4040f10f00d211410050140c0040d44c90002d002a440c1c180e003c1380890040040140c9101e4552012107698601401110000812070500303655868882e18410740d8070629215040c0a0544a4000241084081552854600b041c3d441c00700103c05624111000d0000300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 915141663 1250 915140413 915140419
    0x11040c05182d0117040b010e1005060403060e10060312031107060501260a110d03050c0129120615060c0f0d030f05100e0709080105011d0105010914040902 68
    0x14941c8541c0980711040000707001807501c1c03260b40d00c04140e800101203044032001990400d40000c14400022100d4000505485440f440285039907140a1240f035590616885640c100c01c00182c007205001c42500000201c0f0111021a0800034030b8002002c12a42d0700d1001903c0e5081002c1441c205911940024004041321a5624100521034565004444080e403000a13200e0741c6209070701c107042140310148103840c1d40e403010b0000400541c88080d00c1841c4003174080c0c4101c0440003003000b010b028000b90382e8002c0c06480204281150340c00207112101d030b840c06d64000d46d8289400180d80d40341c209091000e149040300980541d80311034144c0b0440450f2059043d500503c18024900318810400854491a001c2d034002d01e01b05406210140413142c0c2e0726100e507211030506003080404c8880343c0c0c61104807120410142030a540c0e4440480f0000e1080e00001e450754282000092000c00140404030540ca008114644c240d9882c401950314000034400c50344041c2e0b00c0d24802d095458250311801500e4005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 915142913 1250 915141663 915141679
    0x604030e13021b06180d030b0d0b0906060102190804140303120403180f03020120010e0a05070f0e0108061815130606090203011a0903010908040605040311040c0518 72
    0x20341011420ba07000181811502142000b034216400c004102036500007019907011a038140302035050b0b58a03090750000784001c1c552181e020004503151a080101c180781c200550810b40c1c107103030b40f1082c1c5521065440c6801445442c0c40b030604440c032074444d0117280340d000301e0f101e241034a008800b13072408401180540e89400288441100308601c1c0d214284602e109507600741000e02440009042020b550300510b1143c01090400d000603608000b6040c180e80030030050302c4a07080d41894041c090540314401034154060580003504020001a80206448000711150600c1c5d1f00c038403011120030380920072160f0aa014034003280044030303040d5885240800c1e101c16200038021100300007102e48400c4d149001c0c2040051070a10911603070740306000c040d04205030705528651500c1080807034090089100207411400180c030b540b04d0761302580100447d1b980080c1d0142c84599518001e0702d15085880243c500d0390240c5e41030340c400c2c9800e204114003991070313455643c20094540c030162150248410805d400c140343d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 915144163 1250 915142913 915142939
    0x20906070f050709050c19090e01050409020a050a23060304051f020c060c0304021306050907120207020a0e040b101203050a120e0706030e190b0403090e041b0501020f0604030e 77
    0x4540511441a101250b189031f56007074a0700241c2e60a4426a0120104042040180080d10307914840e1411113904440104e0500352a000140d00000e403a407001e030f8050100c0d1400145a800c111183c0386040c0a82c854a4040903c03e0a0116030322080314014140e400604075090303603100c0d0a901c0d40701107004000060038080ca072542d07146410300907110050078020100c00c100842c40d000344010006c10020a013402090b1034000400c00d0094050218803c0c046100c0139060480d90f07a80c151340d090341c0c00411000c0c1d029035030420003080380c600741d40642e204801d0030005031010340f020018004899a90300e103a030030030f50a5181107031387e50020a4000108104070484d100b202060740600701030500642e01401003036141c18009011900e5045024505411000024540115043318105400e03048004490036949603e0216030018140d0412022800004140b1003407003920161401c80150044486a079281c4078001a070b034802004660748600da021a0025002a11884010901c000c000d40f4250300199 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 915145413 1250 915144163 915144179
    0x207140304030b0f0105031606211104060e10020c040f0615210e0c0f04110f0301030c0f0b091009121a060a0609090c0207030c030506060405070201020906070f0507 72
    0x405580305480d0300100b8004c0c89040c030708420000303004081c00c600500815410592408007080b8500c600c406202c10070201080310300c041a209040000292820000304800b8250a0880c0c0c00c940036550000d030b0740c0070b150304803030921084070304940d80c8640040403281d2280c01000003410014041800b0b0586828001550422620f1416001c1c7d80e80d80310035000c40711020110902da10411140a00130381015007805099a01282350f00c2001e8003550399110049048001c038001d03250301c602810b103404e000079180c01d1865030039010b941664454140301446039900d810300e0701004910b00612084c03000400c0586802d00e017420004006003400d00740b0100440d0390308050008011051025141c16441c0301040240d0380b40465000d90154084541c008a83d0409030024680300517401a103481640d101107465145000304030101c01103030300c03002110b50a504e030b03e0050740b00c10781600c10500840c10040440d00080c018000d582d11944090f0142d81004c03160340f50102c00740d210640a4031540105500420115 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 915146663 1250 915145413 915145417
    0xb010c060e010c030b0604050d14122a03040e0a090c05030d030f0e06070e06030403020f060a0207030e101d060d1b0807050a02060c1c0e2112040602071403 68
    0x4080900000340c0002c0490f000b800307484244103220712500f01000248459612030302c5040107180c002542c02c41c81c1c04151441880d0150b41c81a00941680114490254100348561440501044510100d06082500e015a600c0c09280030700f9954208400004490404036889110034038041c10303800c0340066803640400c0c02d1942c40401000041e0311540c4150022880340034000d20044100001d103e24a0115001040d009036007200030700c60034002001ca030601d4820415062442c1800054034002d0828100300c00080d444014100c1c082400c00584d44c0043c9041c512000007142103448980120350701c07900819181000c0204540d00078000e0100001c092000c0c860003d030100810502c003695007860601401000c8014150170400030f0802c00c0003441940841e001c2e40014410000c0e42d2250b8440c103040ca80c070109035200014841c0b80641e1390300b640400090304408550a045c2480c5641c0b40c3e180d40d00842d1003280074013964101c0c000c022800295481e030040948070300401902c0c21800c00300c1301081c00c41d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 915147913 1250 915146663 915146681
    0x1109040903020c04110702060a320910030506091609080313323703032c06070c120506010f1d06101101110c01110a050d0b010c06 57
    0x1644001d50f5801141400d1152107941070218103030505040710703580095900d11070a03502904000205890000c2e000200003110103c1c030b030409805000c4200d02c3c00c80340c402d03001800180d04c41e002003c2a503511034001c1c42400d00406000c0c2040440d40c2e07644180409685684407280300b04078a0313200c00120507105201070444080d001003100815440e041550841c0c1c4040031031248080c2c01360294403195044507040a2a55000780da070004900e01d98010a01130421390525001601c48881840d4890000941d44ea81624469240c013070683d410b526401194a0f80f50032031940e0208050300d40b03146458075070060003a0038452640707035000301e48410700c080072151140c0c0216025440b02005119066949038620054180301c140c24402d00c208003032402007800083e050b503000e400080c0b003802c1c19901c01c0d4403d080c00c2a080009021040701148480501d41c0010700034041540b030202040d4400f40b00c00212002604607035580d40c00c04d070809210340e00800313440942c00d0502c1044c0b00184001042c1d03014410f10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 915149163 1250 915147913 915147917
    0x50c030f0702040e0106050603190f061203030c180b1c0606020a05062a0d0603020418020a14031c11010c0e0f0103050c040909050a020303031305070b03070509041109040903 76
    0x8480c0c0a105000c01c1e42d03a404c24641099041c10410b020607107914003900d510070103c800c9803c04031801e08128004011038400d01c0c4441c3c0c1007017004203a00c2c00d18481005510705c00d0340c0c2003001d22421942101d18820b170362289004030750080003c100701c1200300c01802d07410b08040410303145644280c40c00011a41075a0040000d0f0b0014580d03d0140030051246c40d034804100e07130500d04041d0204d0f05490056002c1c5440007080c0f0008144010b00c80343d203074084400b840e4041e200f0000691420b20100c0c1c000104601284034521751070b130200d8040c010100d00c8100440140060104500c20ba1080c1c980e0600e04c00341d402007040301c2c13034080e0f0b556009024040680000e600c83d150700100050134010081c1c3e2181080b810f16090001b4814040e110350300300c80c2119440d001c0000d0030221440c3ca14209008400c019502d88801b1040c0303d00c902c50301d007100d107010b0f100380201c4c1c100c40d0303848842012a000403070700d040116201340446007881c100b42d0004a1051180c80c0c400d407914202ca0000b90403a0340d552000c2d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 915150413 1250 915149163 915149167
    0x150901021c0f23041208090405040b0a0c1115090f060a0c0905090603070314070e090f060f150d03090909060e2806020d060f03030509100c020d12050c030f 68
    0x7042c58004199640c260804a40400d0120708103070750800c10300c194400c000425031070040c5001404004400c1c6c0d0103171100100180003604003070802c8902994240c40c0a0382145c0f070226048810ba0141c01d1004003001d02402500b01416540045000501d0040606909014540d40346484500c14441644260035071070300003901c0c040c213000080580490703411481c020709241c424031049540020310841105d03484200c11039010b10a0030043d0030714003a94040032110640310140b0038040c030301003400503e284902c01107501ea507542518444044005440f00985480000c9003030042d42030850a030843c0e54001d0a0906209540d006004103c4800f030000340c2c0d0980e0f81c1d914800c1e5200082c00182c0d15815a25408101380d0b1001c0300017911062103040062640e0340c0052009124000c5801c070380000c0449071035070070340103a403410054001e91081c110b0170700c912000c180c038800007030241c022002d1341c80c0c002c0d0125801c0c02c116a100d0442c51a4046c850044c88028040903043d11410001003441401180c0709a07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 915151663 1250 915150413 915150437
    0xb060409051f03080d050a0b10031d06011a090102010605060f0309160612270c0807050a1a0a03152606090c100c02132405150901021c 59
    0xd040002c404000814642a0b40340c1080030848502c151401940040400903041d169003409500902d030b00d041c00e0b90444004030031034802036013503032081c0340d22040c0d07140c41f4032032418041007280c446109002c0c0d080443c81903595a80c54000c83c4000e040300c0e041c1030000040c140c1e101c0001460641188004601c00b9200008016902805025804000c61101d0300070307030b125080841c041c0c031040e8080b02d10041983d40f84888002d4030074075403203001007214051802e4038428040c281495400c2490050041900c1940f00024031820211160b10031100c1001c9103480c50000e0038100d0000d40c1c052400d04041644400900b07640c06c40504002e4010000803208a4003602110000c20b190041405402030640050041000b502000b141c84242070b2400c590031414001124820b5910004441c4080c5d000b45851486103401c00d07540c4d0028694064207046440c0322990442100c558090900507103801a441c42003003468200e4002c09404a458140180c4880071110b91400181c045020510000038007401d200d2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 915152913 1250 915151663 915151681
    0x15091f0b0445060914190b0120010e061302010906030905010914061501050c030909040812070305070305061f051c0f1a010203071a1e09070f050f220b06040905 70
    0x4002d045c1c0720110901c05803a058181c0c3d1400703074280c99030070500c4e40c40c0c1048541984c4900d504420440702c200340c020b00c3e001880c00d014000c0040170b4041d207080c0b090b032010850780c601d065001c0304416030596607410101d050000c2140030b4140584200c0d665900e5804101c0000c0e00480000980d031f510b20024030035441c140c61a80c03050840b100144e81442001c0252003814480402110721400003650180c140da01e6601d005200c0e8030800307210803048180d131014068850340c5500001e0140040380d03802e00c42074646004201f038a1091110528400f46040680e48945004d24054220035495091030540c0c03000440d405029120608030f110031090340c078480d890840e1010f51480c9184070081c8000c504040320380d55100341e896408044003004004110000f426400d410203030446101c6501c0c15441581031009180390b540341c16000d034001c2d20340d40c81c0c40802d55042c5032608544c3c081c001444900030b03001300c8803d1900f00707850b20240c000d913944441c43d000d500e0b04d50700002c0c00181000307000080c05d8900400701c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 915154163 1250 915152913 915152921
    0x90b03090d0906030b0d080a02070302060d0504050606121e1e150a0b1c05010213061805041506030207290103030306080c0907050315091f0b04450609 66
    0x843c00e1614244140c40b80751941c00c071119095511448260792821014820f910f441e040e584000e500580002c2c0402c1e0000d00d941101c0d0081741f042049070559201c0c2d0040200484026060a6031507100c1c19440d4144100c0d08042c1760306990000035104142456440c038036010304054031094541d031240049103030000f01c0000c820341c8422440420040390b0740e02c07000580d1234440e030301042c000402c095a030801440700a40c11035520201e245942111940d032a000a48034152002e1155520b404a4200050700d00703180c010840e8141c00380d260501100e0500c2020380080d0056503081e0f82080c1ca0314061411030640d00c0f510784400c0440703400c148140d071446c40c0081c141d44082e042800c90750070186940d8481d44805802a4000d901070130b01c6901da58880340c14201d6111008441c65001d5038278014420580b880c1003034408809060303410806000d0f15a40c1c0e21b1381074890383c801c810008013035801801000882c0d440b041e00d00140c40b00c41754500016400041d180d030500a10100409a40c1c085c02c000000f46446 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 915155413 1250 915154163 915154169
    0x6080d0c11031b090903130f14040905030d15122301020a02030f03040609050d0818030c070b090105070507090b010314060109050405150a240825090b03090d09 70
    0x1009080b41038541040303205aa040d0f032100e41c0a81c4502001c5000c004050041c0c0300e0101c11200c616000d196503c10340d0615290510a00c2040c560b100c02220309400c0a0040d90704caaa0000015881c0200105089009100714040ca00300080c451a01150b00310045040d00b41081c01888507044c0c1107601401d5420300c26079201851540c1e0b104211000011b5000310a8420000c50107038000e880755504d0403c00003802488000030032900941c2842d4500c55002000140601581c1d17100f945030002007140c10f0750324440c65658520030760202004000c420382210003010910410300d030a50508045959441c584001d030b41241c0c9a0075200c44e50401996071520444841d0704004c05da41c40d540c240080040d04850702c90040b903020315100d400080002180d80c04c5100c88403001f42c00c1007001d036030300c000b244032a040d41900054a0030a40003107100b01d41c441d0180d1401181c500e00402c0741030360200501240c0300c0340140c214040c480d41c400300007a160340c0380d009144941c0c011030150022403c00752000f040900d00390 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 915156663 1250 915155413 915155419
    0x80403030f111510080312070e06090306010e060f0a030609110904030e091f0609050f06040f09090f0b07050d0507081306180f030c150b0d02040f06080d0c11 69
    0x501c2d80074020b0b40060b400300c08a007800f4401040c0c1e101c84c95698880311194104403140d100024503681ca90b0210042248a0500b41d07a51200300580c50040040620819520503850b600c031304018058041148405900400000d001c41ca50070b2040d000300709e807182541e01c103941d000d58844c989000d0201580c04290740b240c0c03c8900b2142450a6a0081c004c84031400c5150b01a031030100000c0e2023001803c034042d444034080a14680002c1c0c0d1410003c251000c58050240560300041c0c290031203003050010ba074240c0781c0181a403c006420480e84000504072200d05555200c0000c07104004030390042825402103030980c2d139a42d40e031080c1c010100c0035244050001000c1000c2c07401000341701500c0c2901218496031261005c2118052008031850340414088054502c20300106101d08040d0080300b40c08100303219450821b40c10105030314070800c4649488082c0d4108115281030401450180e00401c1560084040000c515440701011072602c1101d0411002007807007414410107000c8080f41e0605102811 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 915157913 1250 915156663 915156677
    0x602030a2f060a1b0f0c0f06050108300f0d0209040606170f040308060111010f020d060303020f0703020a0603020f0c010c0201230c070807170a020714010810031e050109080403030f 79
    0x1504e0010260f12901000604101c881c040490800007900c2c2014051034208078148000d5860300381c0d00e900d500540410000d14544002454032817401403408920f8200d00c411804c2c10301c00280348901c416817155008485050b420040003407a60b646100d084d0243c00329996040700c01603114400150a000a0302140c0940d020408101c00a44e024202a5020f2000c0ca0130a051104041d1218003505191800300340c1180040f80c0032001c0111070344000c0490b8041d500711440325508051080d00c0380180e0101070740002c034a041c14030025000340c00600ca560101028079141001c18402103003154180c03c10500140d445814500004404107400c0311040914030b40d40f1181e0400c11020612031040c0b5138024040f01c0701160000502c01e00744104010f0a400781000ca40e00c0c40701c0305000b5200e00c0e6500805440f140381c881e44041e603500c500e8419105030b240b2107168212604640f90300c103030011a40da010103240100c41c84140011070a0003406019032050188a85803030031454083e102480c8080c04038200a14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 915159163 1250 915157913 915157961
    0x21070f0e091612090b0f16020601050657070e0916030b090d05040e040f110612090601080f0a0b1b0c0a030f0203040602030a2f060a 58
    0x1d80310105402c1480044800c00d100405803003038030700000c1e5600c0324940502c1d001400c2d00703010741d002d01103100b01400410740301c0e0765507104680b56030425032005120060b071055006000c281400c130700400c0700c28140394148540307800e41c80503005000c01ca40c41d031100c416035250800030a281c08003070031081031403070b5003079040000340c900e12207540c1c1c013000d1007540403400320b4401042003a0000c3c4010401011191460511a500da003040210101d040c0c804051500c2140085c5454510500540d8140d948008001105855039100d13170400605141d1306865001c0103001d400040d0760355030000d060b4500c1d031250b44451403811003009402d15005900c206003a4001240e803025101000c9950280380d41d200b6088540c0d80c40382860080c0d02500c00e250b40c0311607440001c4140b15188002051a036040c07003982c0e200c2c80500e6040703040383c40340a181714000142e4400d000d103802c45400b441e43ea000c1103200d024011800038004091005c0203104421880302e40e0000014400c01d0b600701d00802c1010700d84500c644900c615 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 915160413 1250 915159163 915159169
    0x50c090102190f0b011203020c06030103030905221a011404060f0c050a080417100911151e070b01060305040f12020f06040b01051e0303031b21070f0e 66
    0x80d680070348420307078a04a2403610420010490740f403240c030340103070b409840d0b0740e1941c841070890416048180e000d4403440b15002228a0304104803411780ba407560320602828035040074071001d12000d100d0440d01100119621500901c02e214500c9040c81e49081e070440d2422010001d0140e154204880301402001c10041c4061600302d21004a5940c0314500680405020304000d42409045240146107030000203000035117203220032a0b074803610142c40c10307100c8840070540000f04960500b031000304113003180301c18420140743c143c440300c442003000c2100e01e20300540d9031000d420903081c22101c20444500800c0c40410f08c00c41060903805000d0302d060810480c18603403541110038a141c60004c1903400440c1c5800250703072084c000450400d80b9242292510b040520704541401c00900440d4080c8254041c3c046408000ea00c00c207019000c017801951854581c040f0508124249907049000c0700d000300300326a100c000d010701c160f2004003280881086420450001440c01c45244802000c01c115840a401c5c10b07a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 915161663 1250 915160413 915160423
    0x10e010206041109070507080403050d09090902180612060c0415140706110405040f0e0f0a150f0b06070302030301081203190b040f0e1006081c0315121104050c090102 73
    0x80c000c80301130343d071a520003504559034460040c0041c10b4150100e40081040302c0010300070003421003a03ca504e00d941d1079001240032586103510107503204580140b85060081208a5550020f038080c01d40c00e008502c40c0d000c28079043c0c05880300c80741028002010404486009032440520700d00c0d00d040100c0e580701c02c05000b4580501c3d80040c203090b6403203441150705012001182c0c028031f0042c106100e204102000c650040c1300721034006c5101c4c0502c990000550f9008a405103459078014500310f03481800048000090800b000c8000041da034411440b0110b81e1220007804010340709174019592981481d5955007031800c2a0480c0307601a200b842442030718403540600c590315680c020000a180090200054081c0c0170403010240c11600d0500044849000812003005d00101081d00307102166a0b0380010750b4428640d85407403e040300c01420000c00b240729420242a460881f02e110a007a511200d0386e0390300c6c0f03407038040440f40c0c1003035075003072089074100f5000d101c0c0d0141e4260040f80c100480e0b580040d441e9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 915162913 1250 915161663 915161693
    0x80c0d020f0a0b100e150406051207090f0f0203270712060203190609060806060d0201080103080a1101020325020f1b1201020d200906182706010e01020604 68
    0x1c0203850b00013030a03002d0180c00e10740007490400f51014160400d08040402d15900c409040d0050f030a110010540382030000d20304e800a40319000810555182c284244010485e0041811045444103281041e480244c0051801a021151000449a07510141c0b9003002008031034003100d43c10000042003410f0142104a4005412000261f0f495540c1610440c000180190400c41c81d481d00001003800e4103658422025240040c0455a054403001d0404c4004000355000900203500d0f44014000941c10700050b20136410701d4108900300c030400012039426600211903e0405410715142c08030800302c40c0c080030b800f407209030000d408a49020b02c040381d190030489404003505d0400c00f482c0606919001c5480d020030100b00006c5403a03400001c81d8201516040c03180c1050011000c1c0c10002e102e40c004116013480b02c00403d041e241a542c00744681c0b110b05540101640482c40d90a0380300003007410840340001407502e0161300003a2034054005040c090301312001d141103600c41070810000540c040c0c0c0505c14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 915164163 1250 915162913 915162923
    0x14150a150807141b06090f010b28030501020d091707050a060e12030c0a03141e0411090f06010908010207110f0d0213051009090503091912080c0d020f0a 67
    0x2000490010050503c03031140224410340004268103070704440855064000c01c0c454098a400200ca50041ca003612100c44000741c0c48008070815640341508ac0c1c0c00005070b103c09103540240700f079481e00c03140d089030001250300b12450b480e12416001c0040ca601d03000c0030f044000780a1800c012041c1c840640d60240c80c40300401040da0303048003c110810801c108480010400c0801c3d5491802841c00942a000101070700c0100b822325016405c00040091a5841002c45242c08400b01c0d4480b00d65540d1840c01a000b940c0d41a019048030f14191200603889100e15180c7d0b4101d1900d0412000040107100c0c942c0c0064181c0c0d10502005001483c90300b4403101901040701c005002140c0c4000140740c0c40d070480d0000358003010b4660250b82c8501d05070001841001c0c0ca84282c2020b642e03e126802c19181038510003046030b00100003210492070507000f00d502117a0307024a003a1410751a0410701c00616000c4d80c050711a48004100c05d021a6410410402006401d201424104800c3c031440b6644002819005003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 915165413 1250 915164163 915164177
    0xf040209040804211203090512030c040f06020a0209090c010c200306040c060806013615030f060b120f190218010e030106150509030114150a150807 65
    0x1070014400a403000b03024181c6840d408460259041324808510f00f20413205103507004045d00a59000c1d105846856400801514482e00020f01c0e00c0e441d54001060350148013018000851000b04952110707010746002d40003004604240c0c0104201190010072107211a0302c010304c60012640c2c460300900c03001e5444031514281100d0f140e0852199009100b0154051040e4001c0000b03002110410204849180d00d60003000d0310303284011181451054a00d10074081c4080e1803e0030441645003001c600d890107181341600079201d1300031f49e60152000603a0000281ca910b4401450100707486068010b01c00300201c10310f41400e031301c2010901600101612003d058010000f017421004400c8030031010460b0310115a01c20101c10040c41a10038001024006903d6003512446030405200c0c14007aa00007458010503100c3c11002103480e5400046010b0309552120645111120b0202415000f00c00514020b0103250543c0c003400000c01050303024003900301300301080c1d64606800c014a56000300b450711b0829 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 915166663 1250 915165413 915165421
    0x62a030c05011b0e09100f06031d010c0c150b010806060d1803030e010b010c020f12070e09011a01080f06100c0b25140313031e020601240e061605070b0307020d0302030f040209 77
    0x40c1002c092b0071282065403e00102003d0154007818a1204501c926101c90305131181e09170403012980500d50090104224202103191494240041e102809071500c0104002001200141e055004c20404501080d1144092141c5d80c0702801003400b59902072900395001074994000603100c04130321414502540709070209001035101071280c10041c0c15600399407a0b107403c190740304030300030054451100d018414011320091503603c19142c250042310f00219000f50380d1035600420201202d10080007080c091014441400a02c1c10318031b5511407141d2410340d01055181d10b40001700304500030f1b07080c0c0030000300c03010340d0000c0a0410196034000050011500142e100303841e055134041302c48201551241d03103074440c00181aa002840718181c0d8641c034003242003a600c0d02c400000c0c0da01155908004a0252030039002c850600e200030700034600e036076250b1100e080382c140c0324035003015001d03040000100000801c10103155010009440704a405140031491850500c585485004028000a01c6610000046 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 915167913 1250 915166663 915166691
    0x91a09041a03031c110405130b01021e06060405060d020d120306050a030b0402040b0910030206030402300f07060e01050c0115080304062a030c05011b0e09100f0603 72
    0x100031444400b030103c2c0d42d40c5540500b43c035400d515040d1900006420000f141c0300d988039030802d441c204c031b4004e4500050f00750800e070b40c80040c0202192107030442c031811020484a13064102a0b480c02003000028100c542064428442074450040c4050b000b514803200c003100580307800b001914450780080c07100f0705210605070308501426055200d1a8403080c42c20700881401805400c250003540f00b150200040c0010105000c0e6041c02120304010b0440042400c001508100000f141e002d440100f42000c1490080c0350341044032072080c01c00d240006003111480c1c1080080121201148030b0700014010315182000040400b01a6005141081004640340b283c4200940100b02000c4601078800302d8952103d200035641d0300030b4030440380000c003503015035000b040c02038014842800c01000d42c0e01c0e5240712504d060b144068400340880e015076903400340c101103010003030b400032840c522a6107000840c11400c2c104480c0000251050711a0000404100201003001c0020390031130308182004070340c0b45101802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 915169163 1250 915167913 915167951
    0x506010c030f1803030f02060604060f050d0303111201030c0803070804060c08120114010306090207080a08060d0b010e010e060f010e01260c030405120a2f100903091a0904 75
    0x151091070f0000d07107404410140c000c04001940c540c150308032034441d5141010007040c1d481920a5141d03145400c0390510150030401901c0030720034043c2c103002c60744901202c800c0c00c83e64480300318240d004400000500c1080340c0c03501d20000920700c2100450900c6002e0302c070b2039aa40304512820b02070144000f00b0004105080054a2021500000c481032969442000207802e190101011f80001d2502c000410310696038420707681d103035400081082c1841450308041d903a045000e007030b41e07501c43e81c6100407400043e18030034101d0280c800386110403000d500d44141c0c2e40081c44041d00c031520921a11030410803903640b00c00c206a40583c2442c00b49034501105800c0700300d00c1080030144516070303d0b50341008600c4007110011401039220b10122303141450204891110703800b62410000014100c4600050441d800d583c030519a16615848016100000c584031898100306020380d02c0d1041d150385494051541200e02c0d01d000700b000c0030304001c1d141c3d4104034844445c07080c01d07001d0303219642d151038198030300e008542 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 915170413 1250 915169163 915169187
    0x702010c240506061216230403020f01030509030a0e040f0207050106030203070909050303181e06270c130e0a0507081b0108060d02030a02042309010506010c030f 71
    0x2100c6000318000d001c050301c48401e4a1100c12214101004140b0605200003101c00805140505c00c903143c07103405134004000e4103103480504020018880d040455107003040491140b605c1c0300301e1a65203181d44180001010351a00342e07418503140c0420030080c50070110445104400390315200308501c84440014004020001600560510104030041007040540c000c1341034900807401c0f16004c84e40c54021205035804818010302c103030020710116886c1a030130b4800c0b0600c151050151034003003c0035500d000080c0ca400500c1410307540310a0602060b401d6182d00541110b41082e1179204601d010402c440c1e890701075500e05030003400c18035506d80b031040b41a844194103d130302d801500c1c905120703410700c1543c0301001d00a6003250b010340901101c803507400d25400c0704103003010784454000d551007008002e40c80c0b400c040e0a03601802003001c40001692540300d29084002070740201101400303080380d207000400005040390131603850034040c0305141e0381000002c0180c81d8146440b0242d0402d2080403a441d0031260 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 915171663 1250 915170413 915170423
    0xb10030e10020d021201240c03021c0e040b0a0b040612020405031009021f0c0f020103090c23012a140d0c141b01080c1312030e100905060702010c 64
    0x108060000c0e10f4240c0041c940901d810340c010076540d1301e40d0000000940038a00c100c03c1c030710043c40000101c0e030080c5003804c0c005009005440401c2c04901c800184040c1d00c856a400050800c295800319252a00c558241084103941080c071484c20407111010a100318010710080c440815030031107008211b03404482c003500020302600e41410080a10b20090442000100c0c851012040b81c120600200447e0f03d0002880c0d41c2d5200c0c010300036850f04130226000c40c005a040540302c25502002c01d4042d0300c3d003030007445c0d1110f4004241089000c000e10003001c0c0c1400604001d0041c040010060074800050b0810343c0341d8044a13104a034520300000c14014549030b942043c0203a422400c0c52035004400c1002030760191500310120454043c20039201c4243c0c03901912192102040441c042d403082c940c2c2c680c00a400d15549c0d10b4068004c0e11075000042a9100310000326501108000b00b5a1154020310b40110550303030f0003c1c01d004d07004083c145268902407503000700e0f000700d01d5100396032040704164203480d044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 915172913 1250 915171663 915171667
    0x306020906040b0f21100509070c02040203090d0f05130e100305060a02030109110712030c020118050f1b1c03140f07140c030a06090c0302091e0108010b10030e1002 72
    0x4244101904400044560414490758075421001180100346c03142a188103401c0c4900c1c1001c080155600c8094404070800a2003500c81005840c0c5100a60041900c0c1000701403c00c4c48103401004000020059010842d060140f260000c006285200c1610718900341d0b1842c56881000b00c81e00181c203540060414132a55062003105103190380218181c82a41c00c00340888062406005103d1041040081c16907000341081542035200340c1c0708004616a601c0049801d54801d103181c100e03003801c41403d5889400c100700c0c90403030501c104041013400003904420b100400030304000070790426421524101c07081d40c2410303100400d480303900c6d501600b4401e41845034440d0b03240e8009176156045294101d03100004249292541c1da4001030003541c0e00c40040c02000c031200e59980e400090b010403034084510341000c0f20044016955a83c200d03100b03180c00c0030b8903507407501000c1890007401f41c10381c004003881e4035200c0c00344100e4480e886a2011000c03030341004184e00c82100d40d51844c0025828120500c10301c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 915174163 1250 915172913 915172927
    0xf020303120f0a0f060b07020d0f0615080c040606021e03130e060f04090c0b0c0109141c03141b1e0a0f031e051902070f2009010306020906040b 63
    0x2d880c00c11405080388001c100492400141404201c981c5401600c507800424011034006281c5820800b8000703100d044410271040702941c1d48001e6640400c1c107451a18012541400624410844200301c0340c421181031129038038102029450346516640500d400450440181c0303100340810803601981521f501d8284001d82c1c82c0d07102c40c010441924881d200b50130030141c03410645041d02a10446540058500c401d2502d081d08000b0b2651003264540065520f030311200020640d0b100c09200540030305030240504540c85280914503542e849190001c0c9031520500b4540c2444401d58aa80310020780011007401c2c0c41005624514041c1c00c150140241c080c1c0021005032101d40007074064502151141c102883e041d003015030548562031070404a407140c2074400807580400d030304929000b850035200212883c40d43c0135070038140d078400745090f60644030001190041154040d4000350f80e803c1514401101c406100020b1615601840050700305600411a801e06a60340d508640040c01c051040c290794000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 915175413 1250 915174163 915174181
    0x71d2407050609070e0609040507180605061303020a050901030b041b1203020705030105160c1205120411091501022a060406030f0c0c05031615021210170a0f02030312 73
    0x10240038000f05c980c1440302085c554201002050b0041c0e6200b0054021107040c510035504556501c2c609010554031140005103d0f00e80000800c54043c5c864a4106881d0031801400800d002c2e95210300d0003181010010400314003410380c001c0e04168040c1030280750350141c50400403c40116000104080c001505c542c08054001900c1003c40380f00394000d000c0c0f9503545080340c900c244800029004140350400f220000380800c004002504c0c0c81e420018101030031107000085003102150120341c00d0207401050011481d00120090b408862919020946680c060000791642c40d80e9400c0070340100c00800d50407038034180c03080540c16000060f0610340c035182e8036080200035107075080c0311000c11417400c2000040d203403040c0d25150410360040015840c0c8104403030a0625102c8095050380c0d801c0000281548900c01030004111503500c000e0b10702841c1c00d082011038107812842d0300840c08a244207240542c5640085004900d1940210303540401e1003d50005ca0b00314400e19101040c0441c1400400c00719807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 915176663 1250 915175413 915175423
    0xb0a05040f0e160602070302010c32100218060315040e0d0909060e06091b03040f110409020112152d06080405150c1c05071d2407050609 60
    0xc0241c504440703401c52481150062001580204c5005030426281400036502400d01d08030034510881001840307202142203a1f10b18040c031781007072280c5401c42000c6080d41808206417800700b03803403100c114500b0200000c0041442d118281d001d000e000080002100c4042403d00d22001181c0504184446e11462007411389078031100c11a10085000c0684c041200550380c40780d2003d998800c0e0003035400b40c0b140e10130001d40100042440504440300054032500465140103180514418a08140144507034940984115505007031140120729243c1190007503030f44501c85002040c555040040d46031942114050040b415810441140c81090401440c641c00c000d1074076140d10a0450a0f80c180c1d4898104941e5034005441c003074142c4d80301c02d5024040400001045c0d400040d20040185003080d99411209110180010300c0d02c020b50f5981000211a08098542080b40c107101c20300e00c1110030039000803a030803a083c3c42841d003840c501443c1440c6403080411501c2c00c50b0440211192840c0c0084281e65507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 915177913 1250 915176663 915176681
    0x10e12011b2613080706110405012a06020a02010b04020f040f050603070c0b071115040b060a03020102070e0916080102090f0f0f0f1f0201020c0712030203030a0b0a05040f 75
    0x40d41c1c10b20038400d00b442488210080401c403079154440d07501c80ca0920b071000d8000600903510340004110300343c0000c003035110700502e41003070488080e00c0e030389048005019a6a8103da82d84000c0c00005015144031151115071215544032000584507142c682089005100c0c1010085d00148000b5200590041c1d00001d8001c0303c0200c1c4144210580b102d080c08100c3c0015580000810406138140d8001411502c0c115841001071030400134080d00c00342181d203400b101107203407070041845034140020700640c000b071113502c224180e80d064001843e5600007035407146d103403141241d0848540041001140140081500320060a80d02e030103035911840308900030341c013900724640315510259030000207060004d0ba15400f1308008200d000203550400a00550f1b42c04e80c0b210356404070041d0308507103500884040e4070030305107810f44c00145c0350086a4942440c16906802042c03540440f070f89403c0000c3e5001085075404010150b0125034400c00b140400d644c0d800507045203a201c0e0415105500900c0c40b0b601a82070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 915179163 1250 915177913 915177917
    0x24090423010e19060f0e0318060d02030a0203071e0e19050312190e060708092101090605060f031213031a270d0c050a081308071a09010e12011b 63
    0x82e0317a150408031080f10884080ca842941040c8000d2407180456000c24a5480020f07101d03614002e50000824102c1c0d0084a81a20b41c513400f005022481c1c0d40880030324000f140a0f4a084521020702c80090010340d00e0f0440144141d0030904580c6040841103204801007102504840c2d0500710050300042c0350b084440c1201c1a40c00c104048540584a01c41e0300c10003d0000e0700d001d26000c819100d05240760300152045400041f440d03418601d541c2e00720704551000c0207860000540c0101842c14806131039000e0003c0b40314003006030740050150382c00b01d64034085508040071241e940c11507102a6503403100710352000e002a241071141115031506100310030701c41c0700c0e204080000600b031200c10310b00391032103908052a154012300c82c14007418040d07803000035568002d904891484045548201041e40940000402c030f18115008010841042200348046d2010031080c1d0b041003010103d02106029070418036040001c1e24040b95a103484445100c80544407800c02408002081c0c00e00c2021050344581d040c1c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 915180413 1250 915179163 915179171
    0x203060a2f0a12200a0203073302040e0f040f0507080319030219050919030f0501230f04080912070618030b0a0f1424090423010e1906 59
    0x50392000c3d52040300d13212100090541c810300c40c0303c440540c940e000b00d11160306510007000b4440102d1050000d60022900100e04200e1071865072071300080c101c040300829046540180802e010303054100e01c2240e48a904000d003103074150360350b0814100c100e280d0000640355000d2800c01150b0190044001c0078041c194540c8004601000c0b90114120320034a40d650721206a81c011280003039200d076008018400c0b00400e0120704c0800d03440400e2a80aa0741e00444040030302c0109502041400e026a5201840d50b005500f40a0b00b0601280e01440008004a01407207580000404020b0000160381074080042e00301c0203528002c0c1005d81d9a0140d6004400104011b5806d01421011300503104041c2c035400740020915448180300c11000c1d007180c4818040d065115070b4020181501d507c01603108034103036012441008a0006540c00c10700504075040d000b09544002c1001007055200104901c6c07100034100352801450f034039603074010701690303d9025050040c9995181d40707601c04100d4203840e80c010f081c100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 915181663 1250 915180413 915180437
    0x90f031d010801080a14070b0d061706041703131a06040b0a120311030d020a05031e150d03021c030c14121b130e0a0e0106030203060a2f0a 61
    0x3603100b040c24810810f40f0f40c000c8110900280006084001c5640c0c03280403569950380300d01c0e01c031007036411114040c6442aa070764400c003d5030311340c8250b4541d400100c002600c0280ac190300c810015914104946020315030001c0850316a03000d41c401036400780d402c201060303100e221440e640700c0b40050981c2c3d094072940c1405000c0075986080c0c410402214010b000400ea00b540300c0c0e03001e4402009681c0741108600042c0444032100c0c07802d0000f005d0780e054550b902079582ca0041e4481c024580380600134074558041800f0130440c6000e148203400032410031144101030b107180d031900324a00360680b10300b04001e6102d00c0c40405003c1d0141c01c4494100c54a0b25510b2507000000d230864100d0141214010212170100c01090f0b500b600300300d42c00c11400214200ca4500212106907020051050740203801e460100b034100969410307e4810258150016802480b00a01e5500040d90b1104090254040c099540c0d281314016149409050919200780c2403015041040c1ca4110f0006c0c0c001d2035102c40842c05a91603d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 915182913 1250 915181663 915181667
    0x309100504050402030c07050105070915120908030c1c09051e010b040e0706110f1011040306050403020304090b010c0b010308090a0812220e070e010c080c0f01060b0c03031504090f031d01 82
    0x4403080d140c1c001370351159012032540c2150041030700b001c81d0450680e41d00c0440049000000110700c0740c4c07440c100080d6108101d48400d00346964003041c29004518040c90307140003400108038089511094a08100c8143c0611070040c0100325590103a50b0142c81c04412550000000c1501c204880c030301e4a6a0341c44803c400300690b100c02071f0030311568640d00000e524000070f405076880008001c8640790721b01c2c201500ca036110070448a0640e81500543e20210f170820000300745002d83c0503039000a191500503040c03d9694405036080c18000103021034004105941141c075171070007540042c22080c044484643c0803a0103040241d0010042440444859000c1c007000c86001c04050200c855400c03071411181d0b41c024080b40d60003401105581017001500980c40403c1314440500680d174146805480d401c0041e410baa401c48401d54040c1c0700400d8107110050b100701d0b001c02070741d41c80003411a03800b030f1041070380b0001780040134000001040308260200c0c100500d03902c290780484403051620b107280d0f0f6102d50001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 915184163 1250 915182913 915182927
    0x101b1e14010c0309210311030406150f0e15031002071b0b0f0301121a0103060516031a06070f050f06070306050603010b041e09110a200309100504050402030c0705010507 74
    0xa081c11703900b41546081c200f0400b80c40102000ba9140006006100d001a0001540b06840903110035445400f88803200c1c100c2000003009112003e103400d991458a840d00444500042c4504403d0700802c60206103510140901c6d5a0004103010440d0703104c920340b610b000000c0c1c00d00881c006481d101c0324041030013440d607401c071024200170b181c11034290ba291a1200c80c141d01d0041044401f000a45200a8a40d58512900303018520070680400c25150a50240c5c0703445601c100d11208050424a80c008240c400b200c900003012802c3d1192581c4880c281003c11150104a1004210344503481388600306100c0402c40034000c05d0286d41c00e02c0304e160b503201084102e0000f80182c4504881c00c1000b005000c1d02a407607900e50210200707034580c103681e591404104442c810910f074001110001074102c030055105545500c010503980035901c50f001540c12555032400340c8409a401083c90310003805071180510103a800401008005640d00c2c58041c00c84e141c60307001124102c406608040201d0400c40c00760311 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 915185413 1250 915184163 915184181
    0x406053a020f130204030605040f060509160614090a0b25150207110a0806060312030f040b1003050708100612150b0f040f0515101b1e14010c03 63
    0x3018400710082c20003803440c04001e22482907990801000001880034001c0a2285000d0807002c07503501c1c500e05205081d00c4006015098a0700401c41140d01c9038140e8aa040a0f141d0074581b804801010b4103460440348038048030a680000315403000604241000010003c200201d86045000b511207461000c19100c0b43d60300070001c16281150351030340517282d409840b4181c011038200c030a08003040b0115042c0c0490790000035498104034200b01140c142000410701d40c0307420514140c135500d03000f05941d04a690140005148540c55400325043c000048000300155400c003007540c040e1962000344581d500300b00020a0f80182c108580040c20000c84041c0100c02c03a0070091050030610341c1010180104641c83d10154020745c14100c650030b50b1201d02c035408110b0301c08100081e180c10298511959901c0071188148282400f40c1c01c45030651740a4102000f048450314100b001107100d1424014076400304880b03429600081e403c000a01008203146000007681170000c001209851804909440c0000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 915186663 1250 915185413 915185419
    0x30c060a060e070909050c0921160e04060507022b0f0503090d030c03061e03060b03030906070303050703091403070605010e161407080f072d0807020406053a02 70
    0x6410807018485d031300031079440041c08802c14034006074040042e07400e007005641550040c0c406510030710741e1007041019648401142c801d40d20382da880d01254080c0c00300c0041000707210584030308c003240f5018020800c10000c880700d903010310390342501c1c3c1c0c642c44038254050f148c0400003042098094261409241168001c209a502608001c040040c00b03030054000b07075018204041c2d50f084001902c0c41c483c5803424031012700d25890342c4030034518141241a41c0000140c2840390300100041c41450380e461044031085a81414042000d03a141e00055005002c113001c003400d2022041c55080750a100480101f5030284129410011641ca80344083c40041003103907000060040b218031104d0380e60140d0096082c0085a186180c605a46c0ea0b84d1684e0940000700030390506240400c1800402640280b100031140c44402c2d0044070310f08508000300b80c0c040421000d0403030040052890159100c0c0c0e008003010b08400342507480384919021840c4c44402000900c1003008250b1402c00c40d2003150705505120359a001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 915187913 1250 915186663 915186677
    0x20606300a0204020a0e120304080304030209180a0c05121618060312020c15030907060804060b030d120608010b100822051b24031305030c060a060e07 66
    0x91400e036954040c02038500545100d1400e2010059485000401154040b9a01c42140c0c0000100740412269005007500054209000c240310841c1c0001c10380c0c0481e0340484016a0303980703900031940344907000c0d841a1f042c28050441c881040c04107000c20081120000e894000301d0400c0480d520361610000941d06842044c0500208020300c0300b036110390650300000200056456a90342c6030358006410201190158002d90544800c602d410358021a1042d0500803080c03440c5000340d28107440d952980150024030085002003030610000341c1c0f180241100240031900d154400400250840000454641d40141415408182010107015000c5007103400b4110801261075020141d840c020014180d40d07400b03000210141c001d44402d00320007001400361014020380c1d9800050711100c0b42c44c0c03244003800340c040e200340b000701515050940e80303c0805809190340c80c3d49885a0b000306013100b01c00c02825500c0003258a91041d000810b8290050b0340d00302040002c00e98400b584104080304440000c00301d081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 915189163 1250 915187913 915187969
    0x906030a080a020c030304090b0913030807050714160918030903061a1509090705030105030c1018170106080d0807030f15060c03020f07121704051f020606 68
    0x7081c040c1c2400002401a6840300c0f0030180802d1458005901c15a12180c68491141c9c881c00c0440c1e0840d0800c41e60405903603210350607100a03008000181c401c030104940003880308144001c9040c61035815888005951030512442d000503c00840d81c02040b00e5180340409800b104c0c0120b00401c07500b20f0b81522001205031654031004014a094500350b4030316286100d00340ba242e941c182c40072511003401c0740d8041d10381030b00360140280792100074004014008104018072044d035000551022891084a86100505500808552450514404414550728020b001c01c80c8081c0b040143d10300d8841c04003c0120583c1e481e01c103a550800100b00e8800300c2c1c0e030344020503406803298103d040800400720002c42c8420080e080f000100d01d042d4007050014a0b042a82400c040d814080060500d9071140184130890074450211200000103600030441c05a002c058102c200410342503500429004010400038018035060f0010000984410001800781b03100141651900c1c1e05080c070780d5030580c00a0303100b0f284 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 915190413 1250 915189163 915189173
    0xc0d06020906090402040b0a020c0613050d0303110f040618060c02011206050312031906050105160510020f120f01062f0d0f140313030302131203030c09050906030a 72
    0x7012508007a00010100705408142e15103000802c001c000e50310240366601d01c804002230400e000a480a480341e00c0410002180c45030800650382650340031aa50940708205150550080245521489201001094128042615502800440d0ad9903214102c1854998008103c00300941c01028049210301c9030740009540716080da54404002c200c00000c90a4841c00041d192400403c2d1034501d0410000800c0542d990300e034095140c02e002a80180b00b214207060001e029806081e07851210903c506211200748841040329028201980703000f150345100d0004aa10f095012002c0180002c03400e5001c10701c2c4a4816002904030340090ba100700e40c15022548401e501d401c142151548200003800c5056801c10030f0001c03c507507071a161203050728440070360f00180000070b081c00002078030a401d2080010103000000311050495242c41d005940d101501440c14034101d00e42c100c0d200701120174074500d0800d40c041e4401400300c0c0c1541c40e15017415556400b04032640c1800c6819540603000b4940d460001a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 915191663 1250 915190413 915190417
    0x5030105092e060e0a0e1c032c06010f06021c0e0d080d1401091e23010815010e151311220801020702060a110a02040207060b0108090c0d0602 62
    0x5078040c060b0642d10108205020255000c0fa04015030461010083c03007200302043c802c0070602054200a00300052106014200c1240e040035800281a2140380940290110500d180040740502c508603143c0c1e001c1c1c4410640e514030900441884010442004c103210f4000182490102203402c403041c1400c41414003255090b81058610350007900b00801180082c08178400307080c21400b2000001070040299139480b230b64040c180e0080300700301d10302940980f0116403140d4000d8407030010180802d109072120f04500413108446001076210302e003403001045132480803a4104086001c8440846141d03283c00310260348200c02e580324076544001d06000d483c503051061002c1d03000c03640c15100140303c180c4c16400e16101d51200011099070014255003845408012010300c0182445e0b1008504100880d070100c1e916100320f01c285428081a5204403003810020800101c803e0390240c81503403100c80914002004c0c058031514117022482440000e00640340007d0022500c900c000c0c0440c044001d1511010029 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 915192913 1250 915191663 915191713
    0x2090904110316120c050103020a1b140613030914060714101a03060c041a18030a03030c0219170f070c0f06021501120204020d02070212070f0503010509 67
    0x60203100e005602c3c207003002503d84014184c5079200d08480380070f4944007240707071115000325061501c1030001e881603640c4086102100c0d0b940c407001447c0c400300c90070700c050380d1034005441e040903206a600700988038003a41c50b01c00915201e611610903041e110b030101e100002d8511140361b040b0505100500200b1a5841c0324000100c00b4800e86048268184400e01034900012000140c031041e00000045800e0810078030342d101034010540343c1080d090004c11440300c3d203001e01c501644003001c11400e600114250040645c030380020101da014000340d142c0030b405008554041c402501500b44541c11030021004900038090340186054070301d410700b0031242900e800017024464102024054800090000b2540f04090410040038a80c0a480c4c084001d1038201c0d03078548a41c1105034032004000c40c244000403801c0143d0304490150f00e4155000603d0000e00400030043d500c01108120401220f00c042119001c0e42e4404103680f0100e91a00181401c1cac4a0564656145910001030842040031000c610010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 915194163 1250 915192913 915192919
    0x240c0b0604090c0b0c0d0e0307090c17130c1401020c060d0e06040506040b09070308090f010c0f11010e030c0d0609141e07270c0e04020c1f0209090411 66
    0x8581c40c0c3c680b11101c000340d4010f00ca841c000040c035150704030340400016908441d0391500c1110000d00c41e01198403a440c1d4401d4511043d1200c01c00c0703424501400c005d81c110112001080950315020204030000140f045041e10029504003000c50802c551403034684080c1c0040e0001c00362440120203200c042c1e44120b0012515650b0b03401490700340c41060112a00850050f00201020f091030300b40b200c600302010308070038002d50120404100084601c0180e17014408200c6100a0b400711810050b01d141c000340d100100845844100d0404110101480b003002480a98410643c8030444040c507a4071807007407029070b50040c250a40000005e1140d0010244a0320071000c104c174023039480410524050305003096410040101603060010314081050000500f145542900c0301258940c0c0e42d0300050007814809501c07a02d80e0103d0002c0390007400070022448000d001150344000403420245c82d2142103c0303000c180c1060705901c035140ca480340207480c41c80c4001094892152507607954003c40d140c0204143d60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 915195413 1250 915194163 915194171
    0xe0405131b0b0d0209030c090f010303080702100518060601082404020708030c12160816140a05070203071202180a0e0604030305060f01030524150310240c0b0604 71
    0x1d40d585071201920010f5003248000d601c8105803803c0605200c56103000c540117100b02010420f03100010541903044036050300f000031440c0c80d01c15040b1b007002403880c081140305040c00280020200740895610300c480c0c0f80401d41e24103440320001100d009000369042109000340c0114001040e004030a1311160f030000a100625207c4503a4804806800440306442076007400b00381c14126210b526216603001880840e00c0c0132401c80400060300c2c0c2d05001e803007012681c0c1c0c0660080301c02400b0f54070001c4441040ca00340340d00d8910f640030090581e400000124007134001c0d10000146040b041486a12842d4000d003410401c200e440b90114103100000c040c21103494543d070f980c600c8484140079a80c003c50182da0013103050700d00728042c4401171001c400000e041600c0c10040100003851040816041c0d80c40c10400c509c114000302c00502600480264541c0c034800020902030600014034004086801a0315254028015400100c0c02d01300c03c00326034808541c0c240c00440001d615855541d40c4001e009000103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 915196663 1250 915195413 915195419
    0x6070e01050d0c030605151c021602031606110c03030a0c0218040506042009060424141f02030a030b060421110f0a0e04081902030a0e0405131b 63
    0x1043e00e40011114003ca0394a440134130040c1400c241f100100c0d0f42c8020b80d50711f008040c81001c80340c0c143e1055405051540410402c1c0b02c502d0005030f00c071001d80c00904a80e100d100410f03c0c0c0d0f6000d506480b546000c42c200c25010780c50500040755240302078070f00801840c103106006606540c11002c00700100e03400b00c1d500e101580d0343c146040c14140610b000380010034042c94640b40481e1030321303c0f4010010b02e0f0b8803c824540307020f58404640039882036041c5c80c00301d560076450300740c2c6082c42c1c554580c48000381801000801c1d0b918803c0e9605080a20480e0740d00c503600001c2040d421726658050903407006800030001051654040e40000b2540c641c0544118982596007803008400e152074013502101c00b04031061300d401c1c8488100d000240802c00c451400305000c2080009019070302621881c0d2005000d04c0004060000320301c1942c9a8005c03601100781d0140e1180d900035100d43c091068040840c0c1851081e81c018240361003074920844104090107401c2c001074a80c4001e242d8070350f040c0c504c040154070002c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 915197913 1250 915196663 915196687
    0x40504050c060a0302040e070305270723040501050a1d07140a02030a020d031506110309030a0f03021621020a05120a060506040513150e01110a030f05060306070e0105 73
    0x30f0003a02d010380d60042e1240d082a14004100d00e011b06504c003098140000d1010480d035000020010350340c444078415848043c000e1190610009501c00340d0781e00c00d0500c040040e03007448131004400300d40480e0100802d03038032242003054441c458081c001c5660700303000d481d0345101943c007801c50308010340381040e0202d8070140400c5007150f80000c51001c01a00042080006180c0400211240002605003071020f20141000b40710480b042d44034200c200540401c00002005040c011260170500c05001d40f8070452180c200007041464a0400b02d00510a81c19500c016500074000102a0303902801004800040d50034101c49025101e00c040e41e1041540900140760b03900d00010030b0070265010054052944031f81051390441300010141d501071400c00c020002c0410341e40c1214920568003801705a00b00c445619584000c03c0b00d40d5a40c68150301e0411141420020000903003010703070b107d64003800804281405041a0380c000d0740c9490300350744010302013040c0d113028110180c40f03100185401c90504c0314a12131 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 915199163 1250 915197913 915197917
    0x1f0c1103100c020c0a03030e010c0807021305070813030207050d1a0a06091109030a0602031b0a030f0b031c081815070e030a030507110a0302030105070e1e01090302040504050c06 78
    0x14031081c10b64071881640c81503010711a0418006040fa0002d480ca4507580b406405552480700090420110703680280c20005003e00f52200c1070780181041e040002c50707050101c01403405a8032400402d020344000b030a4101082e00e15841c40741c1c0b643c0a00348403413a01c03090240d0303a848840c00f01e440070240d0f60065141101c491265120f01c141040200302649007006040c00c8810101007005000400c1080b10b40300e131000940109001d0348510016520b0fa1501a0b040002301404122003034103a000403402c0e1342c0c90307060300070071524060b6520420401c4282e1007096a281c1c3c601c07030301c200300d0307a503030b003040c00740b03507006540582c0c1c009140300e0b1032034602e0540000f0a00b0f00110180c0c8400c5201b605082c4210290711100d20b10448500742c000b03014054007510007402500039114000c11310030b000d00b14080692a4500814015076000e0000d01c004e0030710a501516000aa03032041c2d0145210305a41030300309004100c46142500e040c1c40d00c87c02c031400c5800703200140c00000d02c19160340c442da00c103200d903d07100c0d800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 915200413 1250 915199163 915199183
    0x1030f0f06031103151501110d02010b0306060f0d0f020f1908100e060a1a060d0c0806030313031709090c031603020310060f1806030207111f0c1103 65
    0x907000303055141107030090740c000e0070041c0a58072802c1e03284c201408a00890390001e14080310400c2500b0742c035004803800820481c00c007a43d401080700710000550150425081300d14128160f9030255030300c3c0148500310b4503440d00e165003c044080c880005c940c0b01304070407145900181210b28441e62080106d190440b007982d4004c1440b1140100b000403020610400f80a00c1880c5014858500c040d0f00b229520030001d002a11019907507149024122a840700080c00c0e96070260030700762541011101c250050010084910128448a00003100c52030b0100c1201d07403040c030040c442c20b40103046489034150340e54140e00d00940e01204001c141d07107982c2c400350054800c03052400080e40c0c030300d80307401e403c2c200f1040d2f00d261400740340c0140300f40050810b001040c0402d0790340514050020704906a021500208107511805100c40e1044011840c6a4107070010059a4043c2072441101c2038140280b0282c41f60301c400c040c0001c82c0c0124405039070b1f40700748070001e229130042e1007880380c80c0c158a00007810300c01180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 915201663 1250 915200413 915200441
    0x2011d030c0c040207230f0a0804080610081902120703260a0207210c0611070e090304050d080f030106170f06090721050907053c01030f 60
    0x800e50804101c0d040200c0014580300b0f440075070925800b030f990041202c6102c02c803920030541c8400d0500214000300714a181c0c14030120112084103501d8141000703541d010740502a00740c00703600001401120100c00c81d400721480d0740001c10300300c3d640c1d48100c5103000c414034040340d00c9515040201303000b010401814010350f01483c1c801080304003103455014a1082084052410b2405000c6c2d9601c03103801203040822115000c007860416614202c0d00240f84000030401450500f04c010007081403580140043e0a00100c0011100501e07211500300c0020305c1d0440d03d040e140e074400c10003888035044c115042e10702d45100c0c036007190070b02001808041041d0026001180020300c1c00380c1401055101051054100c0e042c0e40c0780302010b08098012500d4090000e1042044c8030814007038004c07403894100c0e11071844111801c100049d00340a201d142e1980600e1007139611480500e818810014034031046032080e2060243c4510b080e01c04100110b03011803d000810341031591b505c00c880c0d020711450007001c0c0350700d0500d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 915202913 1250 915201663 915201667
    0x21020a030e0f28051206061507020402030a14130809040e16060e0117040812150a0305150c03010b070f06020403061a03010c0905030c061b0f150f060105040b0a02011d03 74
    0xc4400b6485543d580310501c1501c460034400d601c40030101e00150080820396440300c0911001c018021184a00100207400c18400010400075000c02e90080000340190741903104a5110802c403030148450b5034401404022040007100d00c1e600c0c0c83d92003c02d6007020b44003030301e0000300c08910340c00700725100750b0042000c9001814200f0b201e6a0110180910005100000b40c01d81426264000070b80100880c0003210100d078008214002c011b501c401e850350300c0040011071826140c0c500035031540245002c0c2c0d188017074184c0101d010039050b0001c1ea4117850f0080c00725030a00d002600c03502c060058429003950517a600b0800400850014011480c4181da500400c0c030902003c0010325007103850304080c4800b00300009105000590300416460210b000c01c0725039a80b2401c0e648441d40b0810304801c2d01404d544900314444a0050703021450310030540b5040440310705a51800d9102c005c0380400c440490010380100f0082c85100e10540140c43c205502c1c1c400050310302c0c01442580c2e90500769003501c409503800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 915204163 1250 915202913 915202969
    0x4051501060903030c060b0d050609152d0a0e0303070903031d0906040e1e0c0a1a030117191103010e0a0c120213020f0721020a030e0f 59
    0x1a00650040000b4a010111246036031001011486291401017070f580d10341c1400205076550701011692103411406507010303400d2200b030701541c54a80b10080040c08800200081221002641e940c46220703074240341203003116100e038443c0011400280030018456642d107008000900800107035108404a48400c2d071101e00f10f042c060300343c914810420004000e0301c00303101c00f180c0742d800d40e06400110940340807550041c40190107007808245041004104c14442154245110001d050a038031a41520b0041000b51100e051000010121703000b240d00c80000c00c0108455000c2c01004c103490060f000035590422000764041c503440000741c0056400711041036041030185030078440c4080795042080104070840c1700781d07914002c1c1e5003180301d9000d4070b90100c40c0c480c041d52500e01340d05040b00212801155035500201104140360003050301074810660540035218401d0701e10080c040381c11403a4006100441c50385e03404a619481e8410000d801001c91442428192103800710300c18a249400c0f140754203519 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 915205413 1250 915204163 915204193
    0x1e05030a031401120c06030f062d05061e090a05030a0c230901230306180705061204061508070602010504150203061f02010204170c010f030b01050d0b030f060405 71
    0x10613040400144030903610b11000580c0a0307140030446e40c0c00d040c041303030910119181e08010038150b80070074000c60342c0300c00c0101051030018480070745862000e12021a55164024468540606402d000c0e480e002801c00803003400500d00a00007207000202003081464451000c030341400c1800e601207940c0441c0c24010311500144040c801207089e0360300c445c03144c444a2200043d410b12018030944414817491020a19210031000d421403000d03a001c0e00b2a01581425100280da180303041043c0035080c051030320081918a40101281c3c2d155040c811308140b261696140c0000030188140e002d103220309020360002c0c0d500d2060000c00d0080400d500002a44c3c60107050921039500c5545030141c030315104108102c01907036100c86103151002210305d910070141e07083c8401d90092189400081c01149400084040300780e0008030080486c4003a601d584442c600000b05605548006210a010a0341800a600105141e5110740d01e036000050842c0e441d00d1071310382c0e81400e082d015035050f03d440d08800040010070f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 915206663 1250 915205413 915205451
    0x60a210b06010302030622020d150303030b0a030f080c010906060602030c010509060103031403041511180a0b03011205071502071d0f0f131406060102281e05030a03 72
    0x1c0400e0800750715526081000940111189070010700322072000d03840c003010075003d50640d800c0d64012182001942800540754143c08605d10080f0002400d0a02034880d90624a5815045960004180400603510740d100c500325004820002c044d50350f5040d050010540d0741c000d070340c0101344da9009140e8411401c001e50782514001024501558040d40041001030303403050003403200c0074041d10300c0340e201e0300c0f80d20304042a1034400000f4484e035400e0120700303030700b104000004002d140044141e442d9003c001d0003e00004510318807a4041440c41480100400020400d581c0b000c0c500c142c094071509511180c0c40d8164002c0406400b0050307010160a100c201601c03c0320465040e003035584001146410803950400d510000c0403003a0320104a4007060109888089800e00305600840c55200a9001d503c8075548000448145006116010066003040c0030b010141e0a80c030a580b990600050041d152003c288010030f01e0788041c0790700403c00038040740090014148981566a0224400f501910480703164 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 915207913 1250 915206663 915206671
    0x712200a2d0b06150706060308041716140f2206050d050d2303040501140a090c0e060102160f03030909050601120b010e0d0606090c03020c06040308060a210b 69
    0x99245160840208020840c103a521480031101d0503000b0f04c01081c4228103002e1160020003640c20840040208490b00c0d020b0403da45042c0c2c0d0410841e1501036406a990400d000706440d180441030b0240440c0f80080007480440340301411034108410701d2000f0a20f0080c102c2c04005081e0004121800c02641030300424000700011074100c0501d11040e15030f20b448001072500301e001d100307982500c0d00355000d0364900d806000020055807512407400d402c01c45e01900303e1f10409203e161200c40004c07030b60300c41071107400c0c03029420440444000d810111201c51081005d001d0034154802d040f040008029081070100141030308900c0302e0340680c50740c540600121060b4111f2500c1e1070515007000a030340d80c0655603441081c0003400c0407a1070003030040180d52038214031301c1103034100041e42d00460600100d500510115044250f08201e449940c00040b0200e0180307507002001600020003040204c0d10401c0c8180e042480142403000c0e1320703a03a1111000007035130036600303038070b141050001c000910141030b03c0e503a44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 915209163 1250 915207913 915207983
    0x54209031c0503010e0618070f02060105040516030218031e010f0b150a030e0105070906021204120b1503101b030b1c060f0608010506030709020712200a 67
    0x40c00c0a50031025049002c1400340c0c062280700c05c030010300e69030340780e00201182080c2506c0d0b0800c203017401c501c0106205104c1c0d022402620481c4000101810a803103041d11540d04e4484404e0b54480300035044029501c40c10714000e81c00c40388084180700b41d40501c8002c0292001e40019030b248000c500c01c1d00d09480c18020400116440c01c0340c0841c098958942d503d6847c000c044031659550b1804400303030010301d01a10b6100b421740c43c0804001166810451501c01c0c3c4001e902140d1080c5030202d9510200c3c4154011982e18000c44202d180c0010003011484d0340016a0309102c10041d26440d020a20b0524150209294180c442020401203554100384241c000003514080c400b1455040c042142043d43c041c002d20b0300a54075000005021140c4d1042e1000f90741c02209209442da1600c001c0d000c2c2500391821172003401032890014112400e8402c56190650140110008104004003510001c00403c045801007500c0b4024420002003840040204c5e88218607016045a49004920f11420403680c2e00381 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 915210413 1250 915209163 915209203
    0x1923012604020117150f0103181b0e0103150b12031215060a02070509090a06050901050103023c0109092f0a02060a0207020f10020102040510030605420903 68
    0x601e807105c40000300c00f80c1c2503c980130f030400f044004034014008111012403c40e5490241010050040d1280c251442c0400c00003000c586c540f005842045020310000709206501590411003101a40200c24810720041480c1c0c0c0d190024041c803030541e030125041009140319241005040c0b03c28085210380a48140e4940d41010340d4828065914044d90080794403850800c2c0c00202c40c41420040d0240c0c40754460418007103820103190702c2e4080c00c020301089200b03402001602d00340104840403a4400b0345004103414144a45140506034032030156117030f07810400750003404185480c01b4040d01015062116034000c40030b000344010140350f22003440c1d18650340000c0000440160f40010702c16001261a940141d841149200083c001080700e204c0300d41201804066040150701035015004a6900f944c000f40e088141034030031411101540a041d030702c00c83c94400001c4c0182c4980000340c06e40120f04034050680792601d000079030060154001134003620300083e900c5190a00f07001030040e448400741400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 915211663 1250 915210413 915210421
    0x3030315060e30030f093102030c04030f08030402040507020c10050f0702030708030705010515060a0c050a021c0c0504090503220b07030c021923012604020117 70
    0x1903080600304803c02600003544103501061600b1000354a20604800c1143e0707903003860101d00045a004284c2c0540300703048086102d034882a0307840e00c0d0040341450612a9800014902d0120000d4001824400542009000200c0000c03164040001d01c10b00038801c15442c3d141c941704000a03900001d01d524115081802c112007180c0b05c0c682641540c0803e03050107a114040c00b1001d10150044501c00b80d814420f80d0400a4500c1010000f003280c130b03020300002c2c01a030b40c2d442403040070500d4181400e0f07000241084025031041c416000400a184200252003009800346c0000c0c803403015802c650b00b0080c010001840c00c0003104c1d41c00e60011f00302954140103010b00c60320f469460303000380c88843e000c1003054010800c48005148420001d01203885540361160038a003001465003030860001c9014200008980035910040c07001e542c1203032990070903801d030f030214076200200c6480b24400003410b00203161a550380f075403410550310f101e04660030618071aa117050700005082d12410801000c1e0a1a464244 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 915212913 1250 915211663 915211669
    0x7080c24090f030d02070614010609060206151807050706090b0106170c0712020f0601180605010518040b060c060406200403350a03091401062702120103030315060e 72
    0x558008804e901c2c0041e121103150502c88054100b20f2401d44102ca51800040b400340d130440c000d081075442950031245c09a494513001c11008194544482d84015405c41600b580081c6525441e802220752400c98205100f9682d5281075850000b01107a884002c030005200c0544e1110501c99030f41c9010003503031030f10300700480f10301c030f891017078000c0640928800b540080c0c8050080251880780388000c001c4400c00d40e07441c01c1c41080341c484003103c41d42c104d041c42800903c80d80300e2815210716610034000c1204820345001048020302c2440e4016400190a200c000c6080c44140841c900c00c078041c1101040780c1c00c04600b410314405410a58610b202c2d001d0100b440030441c0714800d0051603000e800d0140440d030802c40c02200826074440c40c1071500100107031130710005a064000e00c2445204800f290f80f0b014220080034261030316030241c41540405140a000e201c3d0002f401802c0181d000500180b5003081446001c0c2040c10980094000c2a282c2c920b040f0050300c110351880040200b490450200301c460400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 915214163 1250 915212913 915212917
    0x51204050a2903090a020f06093a0804051504030c090b0102010f0203040f03020607020d1407060906020403081c1404020402090f03071419150507080c24090f03 70
    0x290322030322500710b28101d503040c1c5241e03650801d44140b210300315121301e0808940f599074000044202d00502181c40c44107031504107074040e52000200202032024030283c0c022041300445030a2002c104405004000c100404aa840201080c0740169a00c070340d47c41c00c20040c424494604059042c014004102c200007055501059805a0754410030218044801c640102e0160070a00800110184000b05010820115010000c0024825026541999101141640c503104100c0146002c544409501440400d5580040c081035214540c00120030085441c1c0f10100e030026042142c1070f20002031840c1e0805056201256a804031700c806010201c14905a88261440a800240910303008980c3c0c005560f101455401d0401e0b010b1b0444000998400314140c074101c01c145170a0003a964041040c5000504412800580e000d829165641c280d5400c0212840d43c030000d82580d000c101880380d0202301c1002d220000d030070601c89295030201007030841210f14006010300481515400000344005800c0c0c0801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 915215413 1250 915214163 915214169
    0x140a270c050d0c1a070201030c080906070f02030c0105070203030106021c020c040f2a030b061602010f020f0607051e030403090905090f0109050a2a0504090303020f0c0a051204050a 79
    0x94200040e214610f01501c5000c455000118010103c513844d10040d0400c2c40500f403001e000340c1c0e05000c000b50f441710a0740c9800781034403070f01d061fa044840043c10241c050146a480c0410502c1280e10f0501c0f8035400c242101c0c0191560700040c0c00020041140581c10460042c4c0b041c005404003480682c01a0042e503034400e00780d403140c029501c41c9001241d07040950700c54503107040c100001c54081001043c0c554401840b2100d520042490610075a005050010503511910041c42d00e000c040042500150380d07007010039483c6000c602c21820144090f0300305011441c0513041c0c0e61602030301c618a0780c1c200400c84c01c0c10112040c000806004100c042540300300400d007140c112007000505a00d9007040a030500e00a10b00c540c07541c1d0f00b010310f0102000000150030805a0040c2a60050680da0215910b800500022454030f280c4045909128a24081d405a80c032144a410010302d0001c0311407914000307410803450328256411140d10f80c028444144115040508444101d0303107014240310000301307410b5140c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 915216663 1250 915215413 915215419
    0x5120a0303151e051005130e040501090804080a0c1715090102040f060c0209010518011403010b0a030b1006031118030102121f0b181201140a270c05 65
    0x503819900401c107064180d0250a0103007061000d041c0001c83c0c00b144040500c07a00b0300a4441c2c0003101c070481c2c46002590403e44d1111510f180302403074807a100f00196009401581d55541e030f50b81c034000242c0c0c044010402011540050141480c490034841c0c4802c10b1540000e01550000101009200011442c0b00e201c501042c83d4030b00c80d880d0041042d009002d242c10541000c12245000b041e4240c00c00d1104009510031102856141c0e02c800a200c000c40408402203550740d483d02c011f020700120100c482e42c100c13201400000b04c8943c4000000c101c100c2c00d5100f0340d00240700c5001d125016158401c40405821541024028125980034503c99446805c9220f83c6180d10401040343c3c954007901210500c4047c0c403034600140c20107401110b076120307940d13400029100701c8440016001c5508420f84085c1d286000e484942948041c0500c840c20407400d0703014509540e00c5203501c0c0701d0311800c2c0a0500a459a840016100c501c510310002d00040c0d02015410542d002540040040c0905c00a402910019 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 915217913 1250 915216663 915216671
    0x60f07031d1512010b131503020705030301062a0209190603150b031b032a040507050d06300305190c020f0d02090a0c110111040f05120a0303 62
    0x40c0340700016501100030950b000310501c01d8041800100405003806505280c0d680b4041e0b40d179090020418170480c4c15100e100100003604010481c0740c90102402c03051142405441c140320365442e03900b03580c000d07081075012a1a00f0061a80c40c3c49030414046060700d03c603002a001e8010b41c0004025030310041100f40e20120880301c1400c0303507890350032501c01103904c816100b43c8200e0800b803103000740201810340340c0a445540d1086000340e07807840108803500b41c0680a0710b565a080800c84035005c5c4402e0701080c0031040700c00942c1183c0c8883c0b0800e40f02d40c12a41d622074884266200542c00d50700347e41d11540c0a000901c15000b40010082148030305082c03d14058000c0c80318a01d0140d03601d020310780c445d1803221003480c004c0e80d1142d009640b050190f40308844114000002c02c08110b600090040082d4100071400300142e5014842c0d84a6010850a41810032800544c41e40d541d0940e880800c4195010764007203000c000036401034043c00064030b401c550000d0401c0c45c0c101290342c0c41c4540c8502900709516 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 915219163 1250 915217913 915217937
    0x1b01051b0310151701080d0e100e0423100501090801092109030c03050a0203013b0c030102180f040b0310150b030f15030705060703030906020f130311060f0703 70
    0x40c0540c0c0408051a0080201355a590b0741840d840b0200030046802080c40614041c0c09842e1a242440094045894500c5c240700c0341c03414400205003200b0358111042e9000170090004840303c00c20b80c410030075a111000340301e003400c00040460900740d020111903814240d03044001115040445076001175107482e10348107241c2c84d41c2203134501c1160b40040d0010000c1c03603000c01031100105094803040d000364020b000000e03c1100e030390116801c5a10132240070710220201c0184581e9800c49400c1140245e0031a000c010000000908a0740a00e00e02080c0c00600a140300c0310341800c01c23402034540381c1200c04001c0314100c200440e80700e203540c505259419640305440200ea8190405a0b405803000e042e480340c80c1d140c00c0b500c51140b00da00369180600c054203501c4040c10761800140748020784130080c161a0a00e80559000e07000b4103080001254081d409021030040b4240c8107000e40480c00c601805031490920310b05040b8a0356038090fa01901070301c1d04000c900300e4402c03080d00321142c03550301d480e01100d110300c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 915220413 1250 915219163 915219167
    0x20032a0f0a050d0b0d2a0608061011060a0b12070b22030c06030203150d170d0e0a0f030906090e1b0903010c0203040528060f051b01051b031015 63
    0x1132a83c0c10b5951050700c0f41052018058940461030410019004400360f10b00821031840070840d0f1440f40744001201d650018800d030500318505546a403e60400041e949a6800b007036081c00411600070100c0ca0740c070090b036400d500e00b010fa84c2c4114118074020323000446c107240042c0200e10481e4464007c032880000c0b171107010345458900b40001c540008035004083c0d00d40c00020003943c81a141e08904c22203240d41c001081c500304181000c1c060b0f000568011032850140d24040d2500600284907001d552000008016641400030001d154030403c181c00d640c5202d480d0103400381c0c1c025001b803020001c60410601902c0e4000040580044102c01800c0100c0c40f070b002d02c0e04041c42100822501075003003090311074100e03070000050020344200f00e40541211368501c0c911480640381100720486840190030070010306009000245104415260552601c80d0a0006001044000304d84420903075580c5d00b000306414403030048072090900d04150341d145043c00800003680421078046c44441d80103070f03074280c040ac80c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 915221663 1250 915220413 915220421
    0x20d0909151202131109040b120714010203280206180a060b060403080a0815120616020a08040f08010b060c0a02130f11030a060e0403090920032a0f0a050d 68
    0x10700b001005000307900f101a000ba925412940307250340190f003090f150396800e28161020a0016141c0c10082802522f4202a200e040161202c950705501040068044072458428035108184c02c2d00302c3c01c000c030303041003000a00c0d2035002030000345502005115054408000700f48801e086400c25400310380614880c000414500c1158401400d860f400660752490680043c41c40b8410400042e0a038244080c0500b070001c003410800d20f44005d40c0090380007941d80c03044247c040904154a204568a1402583d10003079240e1254018108100200d002048284024000e0905100c415100c850910610300d021035500c4141c841e001b0f106207001c0c3ca20b107580c00015403181c4803505150700b06010144454230030010a41c4180d44a000790b9042910210744007003482d526600950341540e07414032551400c00039000410300301c1d032041e002c050713485030341c40104a01c080910701034a040301c1c0c0141003212544814901c0b400d141d445d44801e0500348491003032030342c0d1602030b988503104904000fa500c0840c41502c01c014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 915222913 1250 915221663 915221689
    0x20301020f040e3102010c150c0507050c0109030c0b1806181c210215040804060314040b15150c0304181b121b020d0909151202 56
    0x185800b00c0c0004503490b1600e45140110110181c4124050054603034110782c040c0301c000c40303006800300088000103510806000c4080c41c0070301245260154444800c1040d1703184545081d0010f280480e04005000c014000142e4031304003400c2c040b03031310340ca195604042c5503528841d2800e0b0110100d1703124041921502454144103004103030641c0c65200105001e843c40010303940c5401641042d00000b01050054200501540c03c07a17491001281d54203152034407611960515407c50141c2d054504202c0e40c6880c4082c02103105240c1d080c0ca550400a000702180d10b00c1c091703810102100030510000c54621004181c011880400485000b40c1b03140100301c07050540d404004203d440007509032010070b000710151080d219000d4070040443c4040b44040140c0f005c0c50f403200140c41c051940d883e1094000c0c1010800400300542c0400c0041c041402c00e543d82e100034441e80090782000240000865100007280b01802d444a0200a261900462000d254040c2e000390740769030a80b103541c507065642d071031031103000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 915224163 1250 915222913 915222937
    0x5010e0310090510150b0315062104020906091608092d01050c0310050919091b05190915080d2c0303070b28050118050f0c0702030102 59
    0x305105150190b42e42100a00b00388102d03161051740c0d8050340e501d01d4040e08841c41c4490007400c540302e1140074060005024401075101104101010800780c0c0811500400403e10081c030000c3d10b081d006100c1041c000805451080841c0c1003005114007011009040e05d5405191413680d641d228051949004a460a842000c3d510420310b555201c0300318085054001c8058000e11260b00e9a1a80090b9800107441c004040c0f55618024092418070015561340318811100821f08400f808186030300311002c1d103c003903881c9450544404001401814400000c001c2510305074a8029001e812561404207400303904520360701c54807a12641c0405442c1800502a02c405444a611030648003030f000f09015101d49a07240442d4a070001d61402d81500034000d0140070300554900b00140d0b9800a80d41402003c9007202d03517000302502155503110034081c90545506100180a504001151281c569104031900d0f20b1828a0204260340d80c0180d483e0b03810000c020b483e80e4840c41d25200080c003a010311444100f03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 915225413 1250 915224163 915224171
    0xb040b12010519090c0909150525020c0604090504020f030f03120108030310060e150a0207030302150402060a08221110020d020715020304090504050106030c1e05010e0310 75
    0x546040c103502450082c2c55480040204204100c40401036480c031810180020340d07210740400c00c0300c8054000094061090105072a0b603410340b921602100c0064030300041d401026201040c0d100010824101c00c00c14900041003100c00c46800580c1074419400b5040fa8507481f50041011912400b85008669000a041e200c3c0c2000803281c0580c4c80e0407180c20040f0b0780350302800018010f800801164000e110b588401d2400c0d50400c1c2d000d55000300b1b541c0c40c0a40056028011113080e01180024001540081d40604421451424001e1511038000005030300d0903600700c240001a5a11803c940350004141003140540e62070400010144071012080046402051034200400162040110b8841d00807503a00c0c144074814401282e0f41e8032001d400a01507808a0720034040b000d0243c413151045003544c41201d107002c0d2a643d220080c0d5000361012241c0e60b4581e2403c0c030030000058000f002912074a500100342400d11841045c8800f0944941c074180314138080724443d10789050003070141071402890140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 915226663 1250 915225413 915225439
    0x14090301020403110a06050715050601020c0307180c0e060a11100f09030801060f02151305030d06060e0312091e0402030712110c06062107080309040b061204060b040b 73
    0x2c4130031888415107200f0300714880c1c0401d00d24040e005581c125500040300c146248400b81c4048010030014012038150f1140000c6681c140e035007004580d028001103154031142040000010003510301030446c1006000460300307280108c0d00d481060310290a500e00c0c01700c121008200515090414080d25000042d0510f00c40c400051040d80001c424640300e592510300c2a0790b40d50049804965046800c0010303040315108102120069031030a80000361000009200250760740d03080c2ca15445400c0740401503032035010802c000c1d50440410445510250b015040d04203182e02c11607180d208210381c50f44500d1410b4504214890a588520380640e40540115982d043c80f038005001c070415001c0450213a4101109803800081070015520400703172407002042c05032500e20410120741d04217a016840010b10010130440348008000c6203000300841809181d6a0100030140000d035028566000d02903801000480c40d2800301104082d0702c42e030000300000704045044002005800b500081030f50044002c4541 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 915227913 1250 915226663 915226673
    0x7060216030534060e0c03010903030603140d080f1b0c0a12090803070b131a01031104060e010918020909011e09210516030f080f011514090301020403 66
    0x40c056810003a200307901990240c0b880741e001030512070380445902c0d000718076800010b2190b004030044981c5c14080c0c484841200f8003003401c41e96101d00642c000381e02e581d01042802104900c082d01c03100d40c50f020307181e0040d0a8001420850f40504032003c1c5c2103051000504000c0d050104140c21448980040c0c0d865100c0841d40c1d5680c018540190740340040001c030072035910b0180f080c103000c407a40705004d1410f110040d01c414105ca14000c2454860010501452000692059044c611001052201f805950441c06d0003504c00c004001181c0c00303103281171810b00c000b80800351018116541d0707080106007444204c800803d08141180300940106171201030203401e4006400807540480b102588804e0607a294412400752a40c50001400303500c2251160480310245a01c0600024881e0410360b00d80100140d44021203018100160f0004a40d54002e1101982c4862056001001000d02210550410f44c2c0f0440e00758446c1d10f410188501605105490701d5582c09491032504014000c5460310b64078144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 915229163 1250 915227913 915227917
    0x60a0c020a121b051c1a011223030414060c0f0c130b0f0d02060408032a160612060f08010501090c051e18090a090203010509010b0114070602160305 65
    0x44a51422000c43d00091011a42c080011a10020119255041d5000c560741030042050416210300303082c4002c1684041140707840314020032a4110750f00c20480d00b41015020300358862000c00d20310502c0038215081800020540b401d90f03081e060340c9100344080800040b080d209030f54004200e4003d00200801200380498180000001a29055528800b0070250030403107100031980b640c00801068100d00500b000010004240d01c044c001c06e2a2685402006195800042e556240a05031101280303d0350b40e202d0300c40160351481d40080141d10581d088191075842640103c0c01089542c4058002910303954022800400c0c41c42800c040483e110482c4a0180200f4012000c0441c2403204440816210324101d40b027041031344144500da1030584007480318a501281d15459031002290307001a1581d150b07588903026014800d000035030a00944141420750b00000c050021507450410f2020381a6084240c6191100039802580c2d80c41c034561510710000d019900841c456450000d05440c201604071700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 915230413 1250 915229163 915229199
    0x90414090604031805010203041a0c0f07080c0a0b0304022407060e0708210a09031406100b18150c0604240b01050405040f24050405010906050d02060a0c020a 69
    0x15a10382100f01c001030b0030481880a00c05c081c0186e01c204410007034001d4254000700c06140c0d10b0710365490211041c02c0107107442143c49065016400c54507080202040420840b40070403410784c1e00b0180a441c0c00f21610841c040200081e02482c80241980c0a40403d16181e04003d0090460130392611101d0500c407000b48009498144144078108010580020005100241581c2c0030f020104d800d4041d100e05455411015416040c0034280340d000c00018112415200c90104c1030008151a2504000d40070390803880f640300e6444c403103040050b20303030501003101401490304003a9241d400003005102c41044510414482003020b010b442c090104100890703150003034951400d03900c04880402502c0c008210b075942d01f0683d010490410082002d4246508908614184980000b0304640140c01c2100f507489541420200640000000e0145241a124550150507404000c01c003030360409000c40c1c20b07104d24041c0a1304c1480c01140c2070940b1072251042050556020780407400041e035844817056000482c071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 915231663 1250 915230413 915230417
    0xf080f07060f11160510060603020a08070c0c26060703020703180f050d0203031909151d0609060403210813030804202205012909041409060403 63
    0x1920b04003540419001d60030580c580e86521610b0440742103204044d403860924111144e010702c04c206a21404944100070003004503071405691442c82400c018001c0100034401010705c44020540d8011030030b1400d0399829100c1c0e41e118108400d00c42c0452a03a85600006441401c5c8614410049150f506030041d10a50b4803c2e11a102800060000038556082d1402203800c00c03500040300b00000c3c82c00c856440292130016040e42d1a10140640440318140e12003a8200851190001080b01c10070595465010440c030b0b02d4290020100f041554000c1904400524403a0101213600b60b196501d0300b0459000b103074000c58900120b01ca501c04544000600d016607004640e444001076a8510030550003855540c0c16915450301d5a80c40e600c8840c04210074078212810401450ba51182c7d4541c8407170a205065911a610180c1c500710403520295041600101c0d4408000142c1e04044000c514000b190318080040710340c1c880400d0740c0441c2c000d00c0d80c04446041c1c00a50803d000b0045004540c29008502035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 915232913 1250 915231663 915231671
    0xa2901050904080315130504050c010e031b19051305040b10180504030e041a030d05131518030602190201110d05090c0604081606020c13090f080f0706 66
    0x2580402800501c102c4018010b60320400000b4100c0941c582640c01000c4020f040305d050344078040e80c44080319401c4408071203e90003400600747e95a0059030040151604070000d01f070917011850100c5240078488401c0703004001e84403010125200401071080a05000b500d0701c54201d1200404502a150944003666546043c4003c0350020050b151030b082543c4a030faa0200e0301003282031a600c0140030061041c0c041103040041c1d0113190f959809926441c1104403280090b001005003054281080c0c00e00f2541030060821105406d00c102c1c0072001d0403030b0703a11941403281d8103203120107441c0240009000d04501c0d00c00180071040110aa0140142440c030651104400400c82d506900301c401312044424410000d2011480030b40740c50b08441e602182ca02c00b91002c1e000b001e000f1030010b40141e00102e215400c110340d8031100312264103040f0014842ca1008001302c40806000c90080c50090400c41c0e880c68075425010248001c0d440741907450350740011003a0344d40b95a503142414640007984104c07117603424 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 915234163 1250 915232913 915232919
    0x90e07022b03090803012616120c1e150305061c050a080c060f10060507020d060b21010c02160b1312060504060c05120a0e0a2901 57
    0x40010607446825155007103059501508001050196403210003078101602c030500c00c0002203400010318000c0500a005070041030391042c58050507180b00c00c8400c9103910129880c10107132011500801200c070f00184a81c400c16180c144118841da4640001960782d80600c0d00c00d400c0101150f03080d0403148802075108440c190040700710b040d03500c103503041d90b0f10424820035410445000012054403522610444121008580d00c1840c2c603040315481d4059900581c0c100301401030140c2420342e01c10914044c02401e82d0402c0c0d07010381136004002003c0d01800042d0781400400034103501c1055154001132940c1004400790709810714006040308078102550078900c440d41010f00004e204500c0d040c2e040b01c10903100b428040003d0264003c100203a1100e040b007100000c4111030f4070270540890b406054081482c7c9054100401030b03c22200010741004420844065555090b0000c103805c460404c01c04602e403410004018504401d00c000a040250401c802c1e8080c003907a0180ca01d83c64080300340c12401a0783e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 915235413 1250 915234163 915234167
    0x40b0613050906011e030219030201080112150902041d071e06080c0c12030a0e011b0e0108060f10020102070501050105010f17130c150e4c090e07 64
    0x2010b54400120703910038401800b0451a4001203200c001e500101500400d41e01c0d00011408000030807402d40341100c80d10140155640724180728090140c48a42d00c0360113103180c3e41c506c0210540081d001e4200c1d80d6144440031591640c00142105003442d007810050a09481d1003a11003840c0d10602035040007140c03000e030203510464048012110790703484110044c2c0d6008180340641d44980b1044e03116000302040000081d402c2000746010f41c8c1c0c00500000c10380c0c640380f0b8090071105260740c1034115210000c0030319001d030b5021141000b00102860280b0b0300e92030b4007000c40c181c0c45910300344980c010804008660714960540c042c194446c01003000340040d990383c80055908629054410300040c140c40541051007650200b415080b401d45c1c00e11070000650740d2541d802201e11900059031105c4c85461007459543d219480c5400f07880c04441c0c03410740d0303007881c40d28603030401d600100561000d402201070443e682242950856049100304000301e9002012002441c09003580502c0c1221481345000c03d081c54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 915236663 1250 915235413 915235421
    0x603080306010230130b0a0804150501050603041b08011b1b03021207051c030c02010c14160f050f06010807170a060f1b03021e09060307030c17040b0613 67
    0x9250222074259025000c0440081d1742c0009071000703004411400000d40443c82c10014180b0001c2581c134039901c0d04052801110b010103580744a1009800c02e001440103035949011250000e600c20756580c038550712600300e0042c181c0c80e507100d0480ca502c0c0444841181c000380303054000510481d42d03207840108090036414041030180340f010300180e200780e4001d046e006034100240081406001100c0005040e021201c588030003000100c400217448690f48804140c090203010320320b81045c24019159500420803401901072130908002c102d1918110740c5c00e00c0380e920b4145c00004d030080250380c0102140b800a590f184420f20405808d03114980303000800c1c01108281003282c0280c0e602030002106030b41c0700c4074080d00c00c0b00907150b40c007641d46480780c400e12508484051004041d0f04c000d038a031a6184c0c07075120030480500e04500321001c03c01083d0b0083d580e5404030781c1e2110442c14001641c80c1607071411983d201400d089041c0b0100023000703010034090903030740725803140e041200c224400c103ca105070f0000b65 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 915237913 1250 915236663 915236713
    0x1d0312030705071509030c0b0121110111011401030c06020d120515030f010608070605090d0213060e040605221e2111060907050a0b07060b0406030803060102 69
    0x100000344003240c0058407030002040800d006610300584010680300c1582142d0043c403003100483c048034030b80740c100031005c44440e00510442041c3d082030f02610605018000207540000c1c1a4141c18408010681c0220351084070081400001c020021080180d1824091b0070b02081c1d8480032240c01c00240e80380700042408818000340d0700c03421200b040298040141c0400380450841d0641d00400741d940e61800c210740303a4190810740001c540e80c5c3c507285d6042d080c00d00d1a00000d0400c1410030810035152180d8078a4210a40d04ac0e80c00c0406d510361020200040006c0d8000038003005002d01070205100341504214000c0d86200c1c415482c488060384035070314000080c48014103043c80e40c800071404104044141851a008188028034410440b202318a000119184c0c01c01180c0c081c1c02c050b00c001010800c02c0e0b40000100018a1a941020001804640188101c004204000480600300300458025420158010b0710070711941c0d8036441c0110160308100c0b840ba00601c914011241c024030507000d41141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 915239163 1250 915237913 915237943
    0x16050310020c1905120d0b090f090c09090118080a020601080106122306180105090f070b0a0e0a09090227010504020711060703030510080d0206010b03061801061d03 72
    0xf029241043c031141039804203000350307442c2c0504641c8400129900c4001c01001002c9000015542402003c0100591001d4003802c0c05038036900400007100c00005036141500c4044900f01010b50301c03991868058500c0701d9020309120314000d011001c000e1158040c20400b0856001d0390510381c0ca40100c50700326081482401602480d40103c0d2000c281c0f201c01c070300740b04072035582d0000d00c0940d02c4503102d1500005451048902034454049140c0010078414543c2016640c0050081c1d1900100342950b907031002d00070014101e40005009040d00e001d40d005029844002d0403050301c20b9500e102c0b020080110000a13805103043e41c0e4844595082e54203000c4a0034211400e54030301380d0800090100035000703400200e541411030050044a541c03200b0187c11010300c00d59020440e454454241e8102c0011980b040c84c0c10390000c020010aa40c01191190540e00f03d00d000c42d40326a10040000c941040002151112908400010545a501c010318010f032286800700510703414081c3c024035998038240a21016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 915240413 1250 915239163 915239173
    0xa09020a300b160228020f090117010606090308032d010b1201060c2001140c010204030309050102030c0c0f150a0f09120b01030605040809191d01240302040816050310020c 75
    0x10f100070709400031440358006030020b002e80d076012001c98400142038101c3c0003003900f1000341c08ae00c150f09000d110064a194a4001c2c21540395503135916250101614030a80d041c030300f44260904031010310a000c00d07500c864041c03000550351042c00e5066a44144036544a81d5007002c0003150150140d0703202130207180e0203100d40040c3e1a4151002010011130010307181000710504036000c410781003a000d07004040e030348000182c3e04d07851407501928060032640001e0541d0410b01c61a05da468012171048442c0c58242c0d164602c80031030314006181c11900d40039512124002003038003050031798008681c04403652181c44004609440b0b540c0e0b08240c400082004000307c031810010710004946400c459002842034182c1401d2061400004880d514403020070310b82d00c41441c100b04801004101080401510482e042001d54182005a0000565500f00140740003800809048041c1310340d04803002840390102342d07100d182804841441c13501c01849150300c280300b010b50300e020015151084584d03091107a00144 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 915241663 1250 915240413 915240463
    0x501090c020a0f0320030903060609041a0402030a2004051023120304030305190801050607030309031107080a021f0504050d0309090603060209090a09020a300b1602 72
    0x304206249000c404005c1032980482c1091111100c0c145026403801c00b55032504004c07024549058002003081d072040b00102c080c44085200c0036221411400d800c030101960790750740e0000c00d281140095000700f2440d000f000c1c0c00c195400c81001c0d00c005140440e0207114a40301d2032604421a0894069906900040d40c00c0405000c0150801500010f003c4d20301d00107414004c0c42d0300c4c211b41141d803040d00807507400564012802d000043c1c032840c085407400c00c8842c950609000c00c551303024001c80141456071340c01c0000141401524a405113072600740032204500d455120b1180c9400d01240103d0144071042c081c05440343c1c524130345600c510126074031981007a241c0010000c3c00129400c2c15014449030381008100c8403c0d44c00350710081d41c01100c000d81d40310700070b01c10312040d030300000d14815449103042d0900340103030b903922509021680300394a0b07241141000c071051100f05004107419840c134010030300500204020341015a21038050b58445582d4121800340030390b202c0558410107040151066150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 915242913 1250 915241663 915241673
    0x6090708060703091e080417012a030236040515190806040309050f19050622080a12110d121e0b03010f02040605030c07050a0f080d0501090c020a 64
    0x2804a55018489170b802040d0301e00100480c031442c0d124141c580c000005001e01003900700e00c40402e0283d00a00003080350700d003089040400d0381c01c01c40c0c80e0b4a4000c200d141c410b83e110b1007078040e41d80a100c500d8604c000030b03265000800960811041c94100c04608201c1100c11307107030500c1207604c0b0360419500c1a100903c00341c1003110612240411241844410b01d01091201c001c121440c03080c0d1285e140e124805003083d00f049801c0d6000340d10319119500340405c400c203074140002c01104072042030310309613110007024001c0b07109102c4041d840040200c000500240d41140003034100c517403d0140c0131304244000d407880103d6901d072002c82c01e183d960f48580000750703d84e84941c140c1006040c55081c001401e150015940c20b08195010701aa401d82c1c8aa610043d28a000e04c10040a5410b600c4218035252414901030018007000b4449d4020b804081500c0060180c2440500005944401e4039400321450785048204c6401101080f50f10500e0000041400111072164040400c01600203044070030300c0ba079407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 915244163 1250 915242913 915242921
    0x20a0e040f0b040305280c1211010e0715030e060f0406020702041a090c03070f0e030c04020310061218140106031b170303060d021c12080906090708060703 68
    0x801c84040da9491901008145a240c2c03080c083c3d0b00ca42d0350580c0d60540700d40c824411101d000e4513510102c0f0303802001c04d81d42d6045800940c481e0780c0120702290001d050341059541408580340f4140c4c030b509090b140d4850301004203002003550080e80c024030030800d415104504850410b00508030030f60064000c51350584810ba11254000c0c030030380015160160917070209040d41c03260042d5602c0b100384200d100c80c0b14900541c46680c00b03010221120308520b0001401000740c50342550240600013081d2400d1100c1c1c8051058020b901e1010b80155500d00b04641d070b50039032101c4e0744110000185038443e8012405024082c1d05840c0341ca40c40c0800b0034000d1600e0f40c0150007201d20040700c00390342e901c10010010300a1a41e0490072030445000350940c0c2c0c6046280c820403c000021031085400030010442e16645d4805201400da805507070700e694201500c20300d91a00046100003030440d26000c0038428945510080f0b842c41003d5160682c0c400762203032141c03250358016030302130944140c000d240020384143c800d42c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 915245413 1250 915244163 915244171
    0xc0f0501110a2c0f2b2d050607140403170316031404062301030b150406030b0411120102040b0304030f02150604020d1815140c090103020a200f0f0a020a0e 68
    0x5c02a0f00580c03003203540d01d540d60b1001d1000ca45aa801c0c440711040c5401403044404400c04040c00713240700e044140c1e03800d504c52000804a500b803214154030508507000c1d5405440255074464000603412603041c810a006030000c81d0103101d0701095a0b01d01c2401c610034014045501c01144e59807816803255a189006003001c0d980041e90702e420002017004207003294072000d0096024540200d26400c10b890755000d0200d4908820303000b50b05114040000680302540709a000d0341100f04015586400070014041d94a0040110120744c004540400c051001c0402540903c0c07103038490800803503840400740d850b10034441c00004951515800504241801c0e0000c1102e500780041c0060708441c455640c00b007080c20700c00c090311032270807100d01c01c1c08005030b030310502d07079110841d42c1a04140c0c40e01c200d40102034440c20251904160300070548616090103080c1c41206500c2c0081c40d904c1550809a00b19036400c0810b05140c10f9204010040d10340c41c0020464254194000e2310000d800b500b060220081d15002030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 915246663 1250 915245413 915245449
    0x506011b120507120309020406120c05040209060f04090c020c100827030d2909010909150606080712150b07110603101401050a0c0f0501110a2c0f 64
    0x400c0030000340d070004008404405a8030006806c00003070050204407074558011008000265030801d012600019400d0704441d012100580e4441144000c500e050181f025043d0300c80202040210f4554585d41110000644075421681481e9204041211402d081c02c45080030481460204905155245041404112004042030382806d1030b46243d1030b5600000b49042d40668802c110342500c2c0c650070640288042e141804909030600381c1c0012003008040c441d075400c0a549001881c10043c41110894044044c1c007420443c20745d80e91006098044c08840c0b88001640c802406401102c2d40e03c12030081800c65044c4040039810000c3d440f16aa100c9081500da94501440d0607056540700300c021440307110724803103a4144510700507080240b0720050040c2d0b418404203010360003110358030050300c101a075000554944002c8003403d005006081c20707545e2440c1e0450016800743d8030f03600114007480083c18001001142075903951404010450500380590002020040c0c1c0c040c0c0c5804098400484168 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 915247913 1250 915246663 915246667
    0xd1a180a050c03073203152e180306090305090108070c1e020121020703090e1e041a090c030c030105010b160302030409061d09010515060a12050c0403060506011b1205 73
    0x6011003185c03503041252001c40c2890910613000103401c10003c44404018001e207007006017008822070343e40410844400404000082c0c0400e042c0c01288185d8200071078100200300203000150500401c2a8030912825020483c035074040b4811ba4810a03021b0303070f103a8101d68040b2404000440700a4643c00e410030503410041c100340c0201c0b508419442c5402104c4080d5801aa242c08524010300500f03242c0d444440e1042c0040c04010842020714464180742c00c0f400c0030005260341e00d01d0003201000b070626803100d551561200300300510340000758180c01c4140403811038540600e03000426080c0c0703109028607060b800c010b202c001c0011006c400c1c946403240c441c1c010b0784d0030705032100d2012049070140e43c0101d00907440700d42250460001d10808541083c0104000c1c8014940341d20000041040200301c0b40c010100000d000c1055440b50100c900c40e100240c8051003542071040c40c4001da50002e00064901510340004521150301501c9800365260154041d44207910301c50b100c0b0290701e170110710141c05201003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 915249163 1250 915247913 915247997
    0x1030b010e18010e0108150c0702121b0901090204061b020105041205031e0903060727030b0604050109062619050303040506060a08030d1a180a050c0307 67
    0x11603040005060b4101c2070b50310a58504401110030007010b82c880c490a40004181d14080040041130983c49851782e00700e15610a69480403440c01c050900d070b004c00300c0c0290310310900c4500706604442c0042d03404417440c030070a90300c0e40624401c922886c03103080045a880d03030040c2a240f01070941150054014140641080d40c0c980c0403161714015001c049899030070000354020b9088451a0400d00509404041814040c2c182c0102e983c5040c0038202a0910450602000c0da00c01207080a0700e80d075081400c00c1100a580e450118540c80301511203920035800e00c400464031465030700c00c0d8002c0711032540b42c02c032241d50a010742c100180300c00d40e0b4500982c0a00038502e02c0342e05070a42c0c1248214410f5005682c1d07403a2609142e400c0440c00748c40e80340304086094080080c001e00205541d05c50302810701c0080c03102203814045688003002140680c0040042c040300007580c121114913480354408000a001a9030344040c003490a03c0216404008911448001e10038120750f03400c0d10f0b001d61101c0e00e1400140311 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 915250413 1250 915249163 915249169
    0x1120e07060c06140105090106181518080303220501020c06071d0916032a090303120c080c0307020307060504110a050102060108073501050709140f01030b010e 70
    0x200c039801c0350011402d0351001c0000c0140a11980f0811030b61555000801e5042c08005040d5100600c144410801d52900158001126480042c010b08070148850104905514050180d291a400c035218103900c4540c0003036180c0c8040120307031081d40d41501e401103072000e403890317921780c0c124040b810740341c5660a1111a50040c0d041101d43d004504030f842d51072641140b0b24420a0080d580c0d0100303400703a00c2ca0824400c0840034105515103103001030402151030401c144000d810b4a20381a41c401c10301c0c4000d1001d0004641110b87d10f01036030b0090351040b03002038090b120703001511141c801c0c01d40010517080c00900c22200040185410501510582745004129110082038801c140c03803d8032410104058040d4504e04035960f180105400c0c00500741962410030166102c0c0e0051050485407046144240c580080c0680e50f80480400a0340103200c2c00808004203000f413908641b0400851a810004208207040b00c251040720345008003a1482c1c68107120045018200b042900ba043c0301d942030090030380303507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 915251663 1250 915250413 915250423
    0x40b22031b05100909050c09151209030313030c060e060703050f0703090f020405130803010f0303020d03050402060d110904141e04050d1d0402030a02030f0106140901120e 75
    0x14060016905030307450480003050525001d03804640b084074158042000c494100707500d881280c130000d400050643d144200040c541c070903004425481140c08156501d0104d560f4060310900b10703013004030f41d9513035a00d04905550f8841a01c004c2c2401c8800b090b0500000e11996041c030b011032140b02d0104841504010f200d00d0420143d41d440007081e11141004088294005084d52210861505008070500d6486207c440c20195101074003440c8c8540c00100c400101c902200e00d06a0320580c803990700d6075107100c1803103103c150340404c500500880804003017652082c00303040d0040d81c006201ca4175144e11001e6120040441005844284000340400843e50f03550b44181c0000007858881146a072400c11281d0019070107020581c0c2c50f002a050034000407500000d0010105010750420314015070321008104119407035240d500794401d0002081001d580207a8000e5030080b40c0c43e030180052a601c0c1d1070155050703500c0e40e084d044d02c0c010030b000306200340d846840030781e00c032000501300020510b881d81c6540d4201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 915252913 1250 915251663 915251669
    0x307022e020a03050916050d0303021b0703080307030e160909110604060203070201090e042d1e0203010b1f0509041503030c02091e0a050606190e03070603050903040b22 74
    0x4039543d00b0805c4003400007401400d9000c1e48208003428004d041000081c00c410308980082d040640c0070030140c0d9001940f00c1014940c040b01401c4643e500e0740d03860244000c0c1d004403114800203041900140362100009442c06c100300b40031808411030b03410078070a84000c1c60740800917038007024404801c80942d1140801000942090307805140c0d01c0c034141c0009086c94002d035001c03d43c441c5e41002080045022080c1ca03583e001045c940090382c04c5903240c0d5044400c1c541420103450000080028a4041460b100384142507200fa0024081075600c3e804003d04002c20507980c055040481c0e561081040c410002405c00c00380c010000107211f444810302201c050f1843e041200031400c030703a19000039071510480a42e03204d44401c0d404812040c1144a102c44804054074000159403140041a00da42c0c3d03c070b0a0301c0c403012206100085103806d00360300912141c103071a0744034024028090003040c0c00b4403e01640d445002002c00451801d4546540d52006920071500302d0104030485030005e60301d040c120000001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 915254163 1250 915252913 915252917
    0x902040e0304090c0503010f030609030c08030c0d0e030a080601032d0609060e090312060a210209180303011a041d0105032b0c0204060b070b0108120307022e020a 71
    0x10740d03040c4008182100c881d51360000c18040700788010440140ca6604031800e8962000d801f003100213641c42c05442c00100c0000081400e0004400c0082460811002c0c006014151206020030200c102103a034580c8031702080400044c0d15580000c0c001d50103034203c07918408a00001d00d003c88030060000750640e000340069800251540d0081020301014007500c8050201c120400030350f070800303a017013990302c3c4211300c6038a81c04507203440003c145a443d001c90200505483c0700ca90306402c0350105074054008001d40491013651040007291070180a19400f00c100760b01203006511b56420074840361402e180c910205105a2001c100c0481d01e1441104501046079440d03d040c0b440e5410102014144000710494088004407160b8043d00110181000c10034200141003000005d201030000c207005d042030342c1188c8a0180c2c002804010800d40c050f80504848022043d20b281c4241c01950b04030b070b0b102c256005070050348688103005e40e90840070005070091400440108405400d16480705c142e800c40a00040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 915255413 1250 915254163 915254167
    0x18160b0918060303030403032d021c02030c0414150f0a020708210a0c021c0c09050405150711070e0402100c05120f0405040203010f2303030313060902040e03 69
    0x1981404040c001c07006100024040a61401e200800e0b624040100302908068031407640c001585000021141074427203481d01c403600c080c90400848060341c8180c10700c1d8140341c00c80c3c035032120104861080d00d00030351000d00894642840e01c0c40d6128004180d1a030303103034016081c1502c1822007581100804410381c2038550551076051450003e4149003d0f40d2000816820841e68031601044829400e0181c0f08011485a103808030307ca0216059141c440c00250800400c50303403c0c00300000503210610491050020246140c4c6480500d000d0ba107065500500c1644400c807428040c0c81c84180a030b5021403180780029040c01c24000982c035003101ea6020050f44400c1000740170079070500d80300c958905101814141d000000a94a169030b600800804944102c0c021960081200000d82140d00402d80203006640303130358491030000e110000900c94000c1010203100c61180c461901d002d080843c0340000c002d141550340314a1110114401030b1001c542e031075602c001c14001a0742d07502c10801061003902c000c4d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 915256663 1250 915255413 915255427
    0x1b0408060717070e012f1e0f0705100503130609060906050105030a0c060e01050403050a0602090307050d03080403080c090414060f03031e091813060b150318160b 71
    0x1052542c090710a6040102c3c052844406980050303a000200c40e2054003040d1800952480a6461b143d04c0c00b074034201c0c0170b00c0d0101d1450580910355160782031540780c00d0f214003405480409139202c15500c6404e030850100705280c19050f005101031903103c02d5000360620700024550703801b4102c40b0700460459480366581e00c0301e03051189500c215405050298010494050180c035180041071103841802c04009076402e038141503034419402d64006580c07003801c0710201c0c4446d01d8101c0180d0820075007540207101c0e048001405203040c80d1240000c0c0c5d01511400b107107485585080f50038140003001c0c3c04955104106260319919281720719806030740a200740c13009604190042080708201170100510035442800b0b40d00421110482400307078158402001d60f0741e00d12000c0416840340c481d42c11210700c5103e030004c0020303030b500c8030181d046224884e420401c11811800c007041964840b0740350103518403000b4400a00d80b00d007180e2040c803602c458601280c030440c0c490481002c42c0c010319004240b071030b400860a4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 915257913 1250 915256663 915256697
    0x109110d0507050607031116060e0f0d0b071101090606030b07051e0a03060b0c030c0c0402040518060409080a1d06040f0504051305070906030308011a0703050711180103030809060f1b04080607 84
    0x2b1000c1c00500321440984518904000f0700c0c04034030414090420409400807032036580c0155800717102d1560000003404201400c1c10020010011884291404403940d000075810300d11803c100c4940108114100301da4418003129803c07a0313000404074406140d42c910010444000e6030f00909411081000110b5079182c0f00c01101d030070007000940c09400780313005002c140305954480031880c44d2900c2c1c80804890958074200007138050450002c0291442c0000114a6000380d8490108a8045c0902c070b400d051900750348043c00064400c5120f86e0307030500c0c0511001d100a1400ba008a42c00414a110340e809a002d69102e1904018841d401201c10135501e400410415400003000c6004040e40d0845040300e1645041d1004107210b042c0c0e0040170044005203240403c44c0120302e0520800c4080c0620114007440350900012100c01c1c01b0550204413100003f031203014000448620400c0c0700d03642680e5548a0150350106034007800d50840e0488005e00c00454881c03401c1104522842169a605401804101c18 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 915259163 1250 915257913 915257927
    0xf10030f06090312150504020903032811120a030c17190b0109230a030501020406050d1109011e0c2f03060f06060d0b030f0109110d050705060703111606 67
    0x920300c43c46007017001903e00003142c800d01c0c600b01d40041d14090381e42c6031000300003407d610411841c1043d10629410a5652214003080d103450342c517540c0c450a803400d10072030b1059618a0100c00c040040c40c0200030104141c1d100f81c00400030030000e400c00260031001807015100d42c030310480d40380b000d842c5442820b101c88500d0340501e000c00c075000c0c01d200e2131482c04d02503800d41007a81d08100b80e1140550328800900c2c0d4860348901e8005640041c02103480d15187c2c0341c001c205a114131b140d0440c450400200c6d140c2d5040b4102114511031058403241c0c02140103101d03c80030010094120403d00c14681042404540c0c0b050300401070b00b03280034045042c915500314400548420280c8103000c1d81c070100403c50b4404550703c2c09078000800f25211fa41798544520008050b0450043c46d0341c050007074042400c191401504030204a5214500b002400c01c1d01300188a00c003070490300e003e401c5238130010042100381040300040c1120341c020701c1c003414032200c0c04049514080c000e069060305c1d250105e80030003813103601c02c031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 915260413 1250 915259163 915259187
    0xe07031b050c060a0507111b091b090d02061c05090d051c09020d08070f0b0a05150405100302040c0c0b010608010b09120f011e0f0c02060f10030f060903 67
    0x100075050001500540f9a2040003d00301c072942130f500c1d0041a4284d00440c4041d0440c501041195440410040c02441c8480c0c45801940118030f1000032031001d04410f08403010405a15074103a00b8a41c0c03480230003100c0e410890041c0d1700007404000c03440d0101000700030b10300c805a2000d00400c040c00d0466030580342020115504041100030701c911100031401c10416165000c0040c0c000c10001c58600000b0741c14140b06000408001c1d0000c2c2c00b004010705240b1141c40240030f800d86001503a00c5240300c10554600700c49002c43c1c0c0e0020000030215203081d41c05640c00c051003400c0035880b07980300c1c0e000c05d0403590000e0300c6c00d000c00c8c09100c4040c200f011003209580075043c0ba1800c55055450020080098028004020320540c4070401a210f00d1300200001d0000301c00355002840740d42014060044c41d00c00192540c0400790800d081c031505412140229088502e50785d000300703035650b0350040741340403068040c12105010409000000204094500e0f0241c91030043c01c000510165070300d005044a0304920b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 915261663 1250 915260413 915260417
    0x209011707020d080403020715091e03031202070309180203010509090a03020a030f030e060a0606110601030503160515040503030703140402150f1303210503220201090e07031b 77
    0x5401c0102295001c25943c00c2c004103030800f449291164981642040c032950804200c20203034811208109a203c4050000c4a11032001034280d402940da40d015001040d02014010603540032084032810036507030040a40d2802480c0514580b61181600e0010251032103074012403940102c010b00a81c13070501e500790b4014151200400c1c00d8401943c0203902d4841849000d418014a401580840c82c002d410000e00801140142c1d4003510307190b018080200200c0c000c107400500c604800582007080060b034107050301c0cac000700190b003401d000a024602c0030000310801c941c5800780103a80800c1565000300e0714002d0344900c01454a070715003a0001002c42d11a070307413a0511141b210040c00b003d61a810041100e15100d400070980e540115540c8451a03c601c0500c3c90980c03813018800018001c420100d0b041c44251090031145440c1080b000302c030103000c191511072507107021001f414050b10403100580c80881c41810990380c0c850b030300e2404160b0404c003160610b000c01d0711405080c0b0b084048403000c3c15a80700314 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 915262913 1250 915261663 915261707
    0x609050906070801081002030c19080f0c0f090603100807080a1505012d172103011a0a090f1706070504120b040501110406020d0e090106121a13020901 66
    0x1005e96550f4a0042451400080e0303070000104840510b0082101e031807400070f661050329407c401c900200b42d00c100301c409035604412180440c80a076501c0c012180b100881040c200c0c10030f6080c90800072603900151100720a2006058002410300040c401d9100500c002e8010785640041418105c80071031440640d4621945058010701202c06201d0800c0c05c144031082401400c44050f100d00b204442460b00154401e020850340500071003400281605c2c258007526050b00c500d8155100c03807600b03001c203004d0b40342d2a07040b003010751802582380c40180c0003201403842c00364411584c0b60440c0e1654161908918419803948140c110308000030805e07540c10088516289107450718080b0810070240010700010700b0100c442c8040340c1803180c250800a82503201d0a1480d03030300c03582c400e4040c2d03598000d040c0c2030f004039692280102d40c40c68055680c1d812184151604241151540ca01900070401d0310502c00c070040c01c1c014040c03d641ca030760903170300924080c01c00012380c4c038520440050420b0346941140e401c05540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 915264163 1250 915262913 915262919
    0x81b0312010902070303270501140402010e100201060906090614010806132d0b100206010501080403080c0c0106030c050a1a0403060507020708030a020a02010f1e051c0609050906070801 81
    0x4503401450444503049401a01ea01151404402801c0c1e48685101100784190b0b000c0380011486c40c04012080c880d44c020400d0b090100508207240e60100e40103404910484000c1c11541014100c0c07500780d8405100000701143c07505d10305000c60b54540c2280750b0705a40c410050111b0070641d00310881001007400c103914145412400280c001d08140b18003042262590000803a1001c45052134417600c411007000c10340c40785992414030040c403c040503d0310541500c442d00034110300100e800783c1038034810780da840c9207a50741d80c4007a500d08001a01e4020100d10401207110601028403448019511071200b03095458902400c10a140702039030841040c41069203031651044003070400300c0c1c089a0b4480004106131b40d5000090b420100558040e584c24080042d065103d02d07070104030b190105100740c0f40d0382e00785600b11030b0885031088011501d82280d070b183d12400c451540144098440034902c52040c00b054403400b400360050702d000d5440000c0c019202c0042c40030760a000d000d0365a001100e440d281c0300c0c44d89 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 915265413 1250 915264163 915264187
    0x80309060f01061d0402090d14060604180c0b07110d03080402030f010b0d0f111302030a140105010507031220031503012906040b0f0c0f0c03070317040f03081b03 71
    0x204c420065200d1540040c1b400803944584c0e440400c3c843c0c0100344404045400700551341c6a036411140076100e20b103061102c03d03103101c00c41e102c0304485402c120185000b50420a1903000da0f80f0541c8165441c400d004200150380c1c1d60750034510380461183d56429184d0070b0600c103041c9080080c107420907c69040840d90b4030651030300715103802c030f003500030a00604006841c10082c56600082c070707503250060f800444031000c141d825002140118461507040000b84c1c1a00b48041e900d0300d00380529400624100409000709110700702c4a000c3c803004600004035540424038440d00b485280c3d45002c9031203800300c10000c42c003168500b800c02c00c0c42d0540080c03021403295440c2c4903507114013203401540742c0c2000703000307100d140c481d00182c5025140281c0b03100da4170409a0350b41d840940006410007040e10802240e5034030803902290b440c203022005030061000c2800c55440511405103e91202c8002800744030028079440d17100149002036000300c032025503c1d0b41102d0a845540c907446074080d5070303610801c00e81162171 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 915266663 1250 915265413 915265457
    0x703050a030f09300c0209060612131e020a032604060f0305090703020d02012a031d10140903010902030d050705070e10030602030601020a05120903070609140d020d080309060f0106 79
    0x203a8100e0b00941c06a823400300141450042c4580301c16049204030401c52400300c104100d44030700d070007130012010001c0b40058001100c04400700007908a00851010000a100307070340309881c00034440f44049454007030209410055082a0300100008820160441406030184140354000060740050114141160086000c00072103031030090410006104007104400c491114503001282036a40300103000740390400130003404885411440101d01c02e00040002c0c034107070f0940841c0c180c170780d110300401c1d200c0182e00581d07540045140ca07804d0b540310001100141d805004c4003820b0610b9403110390301c03003069060040c507102c1240c00001040d118002030005840340055000100c9a00400140e41d0b5900d420040f4100711580400602502c10039418601883c686000340c405e04400b60f0444060301e44e01c50040310715402a204103a016200c2107004c01d510300700040c51451050014000603c58020f680d504c0910b5802140c150b1481c0c0c0010307050100c60303070940350234900600701c6241081c100c1c000c1041900c1c3c0380d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 915267913 1250 915266663 915266687
    0xe09130206090d0b07051209010e07090b04022a0f0d0806040515090f1510140c01150906090c0806030c12120a0207080705040c050703050a030f0930 65
    0x101d001140d40403460f650311040901e811340c00f200c01c0c11181084540503001d82c10405801401d4986800019040c1c14144600b20002c00c410000f40402840c3c80310020040650300c0d0266040ba400f0801c0f041c2075203944032000060311151132203041030040208114100464503445105a8004503000100c445d400000c941e00a07101300c50010b6203468102c2d8640c00603d40b08206600700ea565410040040d0030540c1c1d50b07102c0c4100c0003858044851000030856640c4400206001152200c607840a1001d600c0b409411000603502c00043c0c0510041082502100d11b640401d005d1a01c4180a002d02c450601a200c1100103030b0a110000d800e05034006600c038445c1c031604a000300c0f000640e200c400e000402c40c100c3d500e00742d41070b0701c2d0b91114100002500c038000742c020841540710340389001480b03083c00d02c24145561081d41c0c580d030410040b50340444050780149032100c20503454400c00480c0010a00c40d1503019403240351070149020b44440e172115000b0101680c02c1000d208170b80002d08254004503c0000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 915269163 1250 915267913 915267919
    0x18060e0108070806030a0c03060902010206160203040e0c09041e0e0d0509040e0120040329190f11040603051510051608040801050916080d0e010e040e0d0e091302 71
    0x210341c1e00e040111b0302e0b02484c000e0150094100e5407000051000e160310003150b440c000c0c0e00f030b24030035a0b8190f11105481260b201c401e0042e44108001c02102c60103d490300d07080b80c80003200520b01110040000c041d100392200090321150304011581103003519114685a028540028118009400030050700a000c0e41103080c0c000c5454500c3c80011803001c0d4032212000c2d0102142c0c840340103444d4074040060f0000c1c0411189850800e1083c3c82400000d150b44155080040001580d07503240d46052800500d00440c25001d1074640c0c0c4c0b204801d010074003a1003101171800354a103480b03501d4240002e0070744070060031200c076421240300c50000c0c0752580c2210242c0342550b8104265501031000402462580645001d8810040401c0c0416601410340020f40543e00d40000c40d04000d890b40395108007100e41d8815042035501813910348842038050381d07c103032091005040c41002c503501440490192506050880c800340c1114100d8031100b60031160058000c201074271806420b1504000c4d00f00c500e00410b0b0044c0c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 915270413 1250 915269163 915269177
    0x2030319110f0d0e1608010c020604050c060c0a0c0350030405040e060403020d020d0207030308130b04030201140106110c090c0403050714040c030e0a0b09030c03040618060e010807 79
    0x1030446242c2c0c003c0b01d54403440104a40902404141e5441805c419001d514a00d50030a041c001126100040590145400402509586500078200480342e4045e80503940f0b54050700c0312140c0403411550001d4015802910361901c1001d9202071100c0c91400b14000d0903540312141d15004241580300c880c21401071344003100883d01c0306a0000d85246015941c030550f481800c2c001840b030001c2e80030035224020351082e000c41380710303050700c61003640c840100e0001400143d201480400200c1d1243d80f4842e08110241c11240c0d0302401034445090109003207030150050b03911200800c4611946c90455801002d452610400100034809429116406007010503c070b41820400704007070498030310468004607407000441d00d8041e039610310690304140441034644268a4056100041d901034080c100d401104071000c0e0550440b42e555801c2e901030003a0100c0c0c3c070b17448140450440e031130003040240041c0810b0307140e0070030030500f00b55801d00c2108070750030240c10840c001c0401220b69800c407034035076000305031420f000d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 915271663 1250 915270413 915270427
    0x20f1b161e0518041b090903021b040203010506030f0402040209062808062206050a12120804020a060305090a02130b1320030a0209040c080403030e0a030e131b02030319110f 76
    0xc00c8400d2030b4000302e880074031f031100403020960001000d2414184d031078a580d081150301030820080b40400d02c11650402410800101c0002c4415102e580c0980300800060070295035901058070780c3c02c044210401010040d40403d00d81c1900e9851203012006880c020032545080804200600014140000400d00d205012004c90540c0d0304040d000c1c14018007000300c01c903581c1c080d0b1840707410385d61070583c3c40c4200c40b9000b4803028840c08180d0700c25600079154150032440d0200440c001c00e001001100c01d40500108400113a54038680c4c030086000c602d001140c12059181048940301c52a052002a21300d040c0103018a145070f00320400292500485161710796942c031200b20003174030518403403e03401441e0038003260303615400940760350089000e65000c00ca002d0803c10115607854801740050007040210700011068076222800d0084800381600204000319024900c9141c0d018400710b03030000d80c00101c00c215404080c10b0b940d40c1203115100d41808080900c480f20070f0248039481c0710460b40c90b8001054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 915272913 1250 915271663 915271703
    0x4030f111f12020a090b0a090e0a02091e0102100e030306040e16050d03110f10110c250b0f0901180332060a051801020f1b161e051804 59
    0x2400501c0c020040a9444070301f05001015420179004002225900501080c202e0400e80b09840c44000701619110b8030107a4a4801480c414510503183d04610070b040180c58000c900e0302a040d0018440070040d503d0f401c0c80700402c03055901103028080303158404c01070718101c00301d10442d030800c0342c00070340d1216042e802c64107044aa840c4460355001261240005180780c0785000203000f03010758200c8000300300c0c028990550781d41034450360b1001507190307010100c00c0400030000420050810740103607400006580e01c40701c4c003030345400c449400c0c4008600441c02e07590550300503c4402c07218003200044006a415a03442c2c180103c4500c4054003488140c5254203100c00c40b210402e0380240e2120116070390340c680b40c800ca101501d03040391220080350341c00e000702c1c2c0320040500a0b241c00c0300c0b0380c10059003800b100015000c10403400081d0403069115800d038060b07202d0400c00300100504071b0708100384896825040300e83c44071301103030348154000c0b000d0035480440700342c007441100d40143e8401405c0080003521051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 915274163 1250 915272913 915272927
    0x60c030b0315011d0c0a080a1503050a11011803110f0d0b09100c090b0304080d050106020d0305011505030c0928180621050304030f111f12020a 63
    0x4507050b11828460001518401c00b8070b504864000c0d102800518004e09040f03d03040d000e9580c0242110140001e83c040c43c082c05002d58000300d01d01001800d10216010824258060782c42901d4070f801c0266888140082c04502004040080c00c28482e20790b03020000c210701c803103640300151041c5a040d640b00c46564442103030004d00080100550003550f42402c0042c0700381820360b032041d054820b00c0f090078100c90300b50141e02c000c0c1080381c0703401044914140c0c400303220b540300800841d0020b40c108030511340b810040c80765502802c0c559000340304071001060040d0403a5010707001004086808000f460603694000c00b22070380545e9100f0099280d604010124400c9004900c1000c0f81c05100e00035041400c5c01761034002c0444101c4001400c1d416007104512007110424010150340f10042c000b000c0c1c0c600e40d101d000304040c51040c8100c1e0720385582c03515518041e071104003084070701c05e4101540003c249015042c0d080503004040d120301c4501e006400c0a485221096402040c564004c158050503d00481c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 915275413 1250 915274163 915274181
    0x2220807030f0f021306140f011e17091510050a05060f0c06160314240109180507090501030203130b09070b040b03040b13030f030f02250618030903060c03 68
    0x42d101044402c0500c40039002c6c41c050200500c2200c0c01c40b6006140000384003032480c0c41a119501840d2082100400d600188200d00e01032240360481d85640c0021820507511401c03007a400341c8081202005070003070002005e00102a8564020740c00d00c000d9a8100072407044880440d1a180d558001010984450059a030004a140100300030040b0320400002d01402c50640c42e5000c00c03504501240041552000342d401a01500100b200ca500d8407007061483c9440210504000241c1d40d070b0b509071225110503c03644c1c0b240040c2c50310140030a02d81c0003001070000c0e21003400d0950441c60030180c440e00703581c150300002e41000d514a02003100c1001c20f01620000d84520043c3d0303a0345940b1004880002d41c8261000c9074075031032a000240521b0b5000000c00c1e841c0360315550b00090385800980480150050080002c1c00640c20003410458182c0300010b10b090114400c03000701084203d0500100701d81c42184100b00e541d450811a00009922080c00300c203881c0d0003880081c01c3d0907664011002004110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 915276663 1250 915275413 915275419
    0x8030a0510320f0607030809012d180213150605040e070c03030b0303070506040c1a030a050403120e0f1606050d0e0325050c010201090305030601030e1f02220807030f0f02 75
    0xe00d000074947d11240c00361041c05510000c3c8034819075000801c44082c140c54881c8401102c0b219a50f550b602c0d2600061038a02c4450240300e22140140c000811520b08800200080e07a074075031002100394048103400d0014042402c0060402d40b80200c46542c0c010010010010803400071315030801c040c0a41d006203940c00c406412030342c5846680c600a99908015501a10441884000041da0600003400c0186402512a0f12801c1d0b441d0801594058800a4001c9081c0040d546070f00c0e403004460300c210102d1216501c000c00010744920311003401c1900440102c061011068014060503400074210340449a48960000d060503100382014150700481c01000071121540c0c0101c40c0d10850503909000f094000c1090b01c4d040d009038001a4200d40401000030b022841c1440025034960107984907030603c2c2d040c0004c1d43c0200071410261b00041c09444102c01045a000c65881d0340609850a070b10002076008901103240e5040c0384c46036030f550707203d80b00041100300301060f06400c00640e0b928806d1829406 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 915277913 1250 915276663 915276667
    0xd120908030f0408010b060901020c101b1101080604360c0b070201110115030209040206070f080a0201150e040f1b18050702030703082208030a0510320f06 68
    0x1c80b81c0000d20390040c80361000075800d10071007401916002c0101c0c0d600c42e074141c0041a0310600c1d14240200d045001d00b1361700c10b0041c440d202040408070700c1802400e491240541e20f500120620000d441c810003d400d01d07004e185094180004000003030b0540250380340d01844c02e019484200000c600b40c514461b8005c18003501d5040c0010710000203c0034090a03803003602e5641c040282030b4403040c00c8074046083ea0a0103c00198104050b0905050f15a089030018081c0c0c0e03e001080e03103d0305d4120100d0075040b203032402d0019001c100341d0ba080c070442a400b034101c01e802049e03500e03000001c2407921010b80045c041703241d099441c1c0f0800c03404400a0319011042e8013014111551440c8001d45c140f00302141c50817041c140b000242101344003008495030160703d515070705902e4070384160802580c44000744103405028211941e81c08113003514040c52190b90300d080040791a1401016a282200c5c040d4000700106181c0c0c0141d09001d180c58612007100c4e10130b9650304032902d061100003a15150a00e400d59000400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 915279163 1250 915277913 915277927
    0x61809190c0f050d050c040906020904051003231c030204170705093105070533031e060d08070b070206150609060d27200d12090803 58
    0x401c51000c0d04607900c100d01c25003429503d4051003402910000e0041a6420000c0c0d07900151410358052000c6a0150000600f01402540031034200d5406a61003040c1880100003001006044070300c218101c02210303c1c860300c2e50628040b807036581d00d54044c1c80381d07601d03441c030b0405414600c030f54150380c010180f1800b15640c03642d1a140c2291145041e008881c0607500304400116499103140040412000c4044145000400744111951440100c00111520b016107240081e80b69113450f91951341018952840500c0000303514081a40b401d02074035202108001e00030003010307000c01d01d07886c1e443e86003011a4a0850351b645000035915240188020210003020601d82c0070300c0084e030240b0384510b450390221034058440c02060b00b516050a507a880c1e0065040007a01500d08107000589180101d21102003a005102c10036250950020b407107043d14010440000300c24400360b1084400c1d69040c1c40e101ca40207610000104000c1499440054a4a560f800907954000d01c14203010000b40011415251900d40c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 915280413 1250 915279163 915279173
    0x80301060801030b10031208330406050409020a06081f09020a02012301050d060b131401090507090302220c03060f08060603060f07120c0905100806180919 68
    0x41c02e000640342400e5103400181070030580000c2c1c0050701d4018105025141d40c011044400c00401004402c3c078810346a02d9101c40504200c0685a41d601d002c0f01100712911102880212445540800e100c0d606000c100d602584640007294282c4607a0f160000e082d0781c42c405003201c00c2e43d103489002c4110100c107a000032000c090303a01801d03425055078001d202202c00320a40003216861844a0a8402d818a00402c41490a80903008400d0300c103480214101d0404c0c0300050329081284011862551110400b41000b4007026140c0c0c0902090f03102001a1b007821b00004142c04594000280240389500b4062051140312074024412440780b00180889160300780c000303010340801e10418560410610001c14220004544240700341d00190052105031f9604800d0040303045e018054005101100b810100440c00380e001c0e50f44d00c1c2d505520744000c483d00c1c3c042070058492494405c4020001c0381400d105055032560904035503503d00c42845240d54545007002804c088030744d406400300b03000c080207820802c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 915281663 1250 915280413 915280427
    0xc0b04030f08180d0f18030c030212060f04060207170d06170c0d060203060103150306090b07030903020d030b012705090c0333060a0e040b03030c030a1b08030106 71
    0x20420ba503209000d40b00c403400e00c080902c003401070a115403c10b102600d84684111503c59207001a45040c0c41074025140119007a9802ea400c00d031508550b2240a0007981007c4811500ca035010100a1103540780298041d5131805010340000c10712a0002503440a1005c0980c01c3c020120000c0c0c0c0c4141c1e070321038008040005025511840691214403404202e01460106121300c040740c0180544886566903034907070000f54801030229050581e60410501041d072905001c0c0080e600c00c80c0001000303c1c3c1070420b0032110500401000c00c044c00d003810800000c1e400301d2140000c00a80c280452109055401681c4101c1901130850852546410380c000300c084240c0002304540d003c0d01c461119845403925001c661004442d04440a14035941c103281d000e034151009901c0c1c030315403819510003513101000916281d0000410100043c09100c0001251529202e0f01d41c542404070015450104504612034130703401000c01240c01d118105000300b41e401c45811220055941c40588943e0760760b10f44030041e005d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 915282913 1250 915281663 915281687
    0x809030d050112151a0607050a0b1e06041505060703140a17010905040201200309100e090f0103151503060c32120a0b120d0f0201110a030209010c0b0403 67
    0x124081403003d0104c0149100d101e00b15410900d032001d0460000c1d00f40400c9520480d003c82d994401c0d2510031000c10000302c0c165000b02015048044101070080c0400c44005003d0040e521a0b0b103860031500048001c0e40c0804121703142034030b0072516120301e4182942e180000f00c40c2d0080c198000a0740c085c03034a501c031031416542c80c0102048000c1e0703600c4101d10411100201c400034040b503064040180c0c0d114403c100d4010108944084a20303160040c404628880c081d80c00201c00b0604d00030707a45220345000681198030002c1c40b042c2603907540c90750319000303040014284a42040340c0d4480c8038810fa60302d000c0007440507540040040c42808048a00140f022040b0303a100600c1d010101c40c55404e804070107150f80384e000c030740c802001e081c600b040258044030900504445a010340e9981520002d858038000c800b0314091030030281c0600300700e000d0050400100080204110f9140102c010100744690040d1002070358a03103001a1101050001a980b201002e000905100c683c4001c1204166004041d00300b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 915284163 1250 915282913 915282923
    0x30b070201203705030f070c02010c0b09071a030f06120c01051804150608160203041202010e0a030b160c020904061a150d0e0307120809030d050112 65
    0x240302080c07441c20001c5000c0505400c0ea5000c100302d28800102a080b68414400000d00e000c0b4031072600f00d4084106150fa000c80c1030208401008104000c0d5034041340300d5002c402c0d4140041e1018559000800201c241080100041010750100b00e9800c41008140c014141a99040e00e4201d0b107900b501c0a56001210810807104038a000911a400c5c1100c0324480700e24210020518407a6803801500c0c0307500200d040c4c0080445210702c0d00d116588a010b00948005441e0406103840c0c146400100808401004e21201d01e08944109510b2640041200c04a4400066101c0034226520040318ac80e80d4521119900c0300d00008084107220714404200e0140300c020550014020020100303440c103811840d4080d41c422440300000740410303d6608481446080068020280328144000030070045e040c282280034403401107040b0314414054440d080b03000c800c4a00550a2000ba596200e4050307040c0d41c424000c004810020403400d0310104243c801d01c0300c8210082c4008d6031104401c2c40c1ca003403040c6c81a22 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 915285413 1250 915284163 915284171
    0x3030a032408060603010b03120328020703030c02070b1c0203190c08010e011409010308180613090f020304081c0b0319030e24090609090705090918030306042301030b070201 76
    0x103c54030b4005251189803030109ea6150850b0764010307081c0c03100c0e07603402c1c04200c0c803030176924a1a00c01c080900c0204ac20328441d4070300281c08208c52034000c0c074202c025080b001101808001c03d1803011100300b400c0d0001100b44002581e04d6481c064801c05c01ca14582c96440c1c81030030b281f44005c59940015500341a40c10705843c02d10640c1e40c40011240d40d583d030802654004a0000060010441d404001c012440c05d1512011300002c118011581d40c1d17002c0c040380010b01c0681041440500103600139121000c83d0a2425815410310340c5072460705100310100042101c4504001ea1040c800c03c0d004041145030040540324801c480030028800088a24001c80000703211041045403442c00e204070a40a0b000150b08102c408426010010182e0200b441a83d00c480c00340700071081d0b039a070340d028244954504d64130b8503241da80303000501079140070103810080f21a00227502002c200000005a030f60086044034041150907010302404401e44800147c0c002c0c101074800044244555030031814059107a13680208 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 915286663 1250 915285413 915285431
    0x1407030e0f210d0b12070f0e15060307020a150914030703020703030f02030d021c0e0a030f0813060c0e031209091504111903140603030a03240806060301 67
    0x545500d0902c2c00203a400c0400c02e40e1002c401c96031805840c0d02c801c0d011000940e00c85800006041c0c16a0303002805190f4003040c1d0030b1124500c44980c10004144a004101231403e080d000480000c8450007020b000702800300020b50308501c2005100001ca030400c1030380030744444e98070010300640314a071010356400074a034140140c0700600200b1290b406806038041c0400c6400c42e40c04035442c1184503074200840c841403000c24100c0e611ba1008054903900140021011100f04002c13000b564041300c0144020342007203000780082074018041ca1040c0c802441c15900310364961402c15121501c001c005440546880c1046a0317443e00300070407881d00c01c8100d04a85a484400041d45854894a411250803902200105081003050b01001c2d00d01000100301041c102c4144844003075a0b0000c66000305031229100c910416070b6018030510340002e81e0401144250300d4030b07002280d80d070310030814941c0030541d80348442c1043c000c2c80c40144070011403114009113401c0d6901c01e0666514016992507200b03518041200c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 915287769 1106 915286663 915286693
    0x4020a090e06090d05090607030809012903070905060a0302150c0321070302030f0c180a06090905010914010501050313241a0916031407030e 62
    0x2c0425251000143d40740c122a002d0043c03d100c0100405400c50701c681085031141901800d001a45071117401806004160440304480083c10300c002a83c0e5120740c0e040e100145403030490031a03d00c540c1b0303951480b0403980c003604e00700c2e88401c1c0180100300504040c0241d60301840c51208003410105090300340e80c11a03004401408040c0120031480090081d80107800790043e03003e01e411811843d020041c1e5004078800341c0301c0d002c84031011540302001000800c80303681c0003001500c046041642c2d0100a40328a02c18010030403040e0404001244001251280d00c4200840645001890b4601001981d29601c06030046040e01c0410b4040c0340450302a0211102d42c1c506a503406105854802c41c0c00b040b9141700314401c50a03032114050000303d5440c0e0038960741001d1244100a00712041c15026401480c8041c44c021270422101c0801080540503400100402000c00585035151644485 = true := by decide +kernel

theorem cover : BRFrame.Cov 915107913 915287769 := by
  have h0 := BRFrame.cov_init 915107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 915107913 ≤ n) (h2 : n < 915287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
