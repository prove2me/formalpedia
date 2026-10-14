-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0014
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:22:01.368461+00:00
-- url     : https://prove2.me/submissions/e862df66-68fe-40a6-b862-4201842e6992

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 2338137 ≤ n < 2517993 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 2339387 1250 2338137 2338151
    0x1003031701120303020703050c03120f0615030606030618010905070e0901081009050102090d0c080d03020c0307030f050706020406021605030111070206031905040b0f0a140408030711030d060801 85
    0x2001030000d0003420310020403122442c000c0391180e030240c040c1c1d910034200301e4074140032405002e02d141c0104204c0040b40399613004000e80e00d030543e400303203411800c1a07504071403447c0d20440741011804001c00c04c0d4081d19011000031110ba03641400052014243c3d11510410350b103842c83c4002400c8121000404150340078800c603a6401e1031104c00f070481e900280500480c8003050004405001c0c0000c007503c03d90740034000e1b0340c1e040d038402d020140800d20660100488a00c3c0c1080c0074100f1210b501c0c4002454414000c01488850201c211154103502d8545200100f802c0001030f2184e0107248405030880307102081c04034130507400181e5146074400844403818149e5603641058243c035860f141c4404c0040090040303030700508004024540260054a41505140c0b400c4081c80c01c4590469050324103401040c00c2c0146101401d1500350081c0410310706209500d54100b00c0d00d25a08050030041900310000001035000b80f1802c885852004440e00b81ca0b0380300303000c48202e0301425031800f45104a52a00d50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 2340637 1250 2339387 2339417
    0x8030c060115050a0309060f0e01020409050a05010b07080a03020c1204050102010509070803040611071805100902030c04030f0201030e07090e0c03030705100506030f010203010603060608010e0603061617100303 92
    0x31602d2840469a940c2e140703052030b42d010483c05424100411180c403512445007164000c600d00030405a200308400068440c0c4c40e10700d0100640c2c4010781307840c403000d2a0100500444e20302c2c4040300c82d6540c016010300e949203009a801c030b00900c6035591039000c5018008050045200e050000c2040b610700b43d000b4001611801142d9489102a110b8203e82c0e500400c0100724050184210f004c0c2e140c0d081c400c3d2800b1540ea64040e44200f01e403480942e031680d507a0001c2000c480f006410792400707805021800c6007185443d49115009208601001d024a000040c4400c11a842078101c0321400341441c5c2039840560b51801c20304060040544400c109001d02000001c8509001040e86c0113150000020181c10b49440d90380c000401002d00540c0d0180240740030541600c1c4240010b41c001c2901c0d54000a03a00d14100c4c005061f800182c03c00340e0408401c00a0202a5900013595904050030b4410300401704c04003c4107942c0c011081400520403840700341040194450111090200c1c0c0c02038a40010300c1d6081a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 2341887 1250 2340637 2340659
    0x60c020a06050a020604030e01140706020a0f05070f030c0204060902120a110702010203070605040c050a0305030903010f0e0c0108150d030804060b060c190203070b030a09030905060a020a0305070203030906030108030c0601 97
    0x40715070f0040e400f110000d00400d00c9403a4170034074510113050460907080b64040403001c07544508020344183c1d4000581d0007419502005914040100d85000e50800229a8820b8400d58032240c0c042c00b00804090003a0070f5644030b074004401840340001c00c5580b2030290445880241c3c003264400318a07860030208130088000030044548403a4168040c52400d09240c2e43d1100400019100350b0700780308881808215503e4074881c00001c4c5014800540c1c07610248000c2509407581e401c1d0800c4070074240404009030160000705003041d86401d0900b00c0040e0742c0c1040381e21a2201e2400d89541c4003440b60030400074076070807494050165018000c103005120fa101c003440702600c07640381d9501c02c6602c441c0c40180012188101c0d03001c0184010280e074138403075035500c80f01d80f00c0e0002d80700c10589075614a0b2100405400402140c01048252030b030382d00304411840081e40b1800351050240a0000008922045580902c2104e0340300000a04058036540c44030542940ca030070580d8500068881c2c1000440e81126607 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 2343137 1250 2341887 2341897
    0x50a0c050303091c0f0206030702060405010605030a200f0a060507020102010f050412050304030c05060123010c1112030702060301030609031808030906090103020c01050108160e010e0a020702010c0501020301060c020a0605 97
    0x203004e000811040c0c056a00c04105100d50554600400050000040c0d58080c0114001c940079030040c4050709060800500b121300c01c1d0b024920990003e00240d002408103400410300e07061492015a21807034450102d20b07554000c2c103100740d11540c906404218140c00c44007825219000303900800c001d408500d07000007122425580901a0048100201070f45886800215801407081c5011032040c140d940c0c0d2603290041c207820020541c0d2000c9c612400d00d40c10740201007265030b4246041e41c0903200a494040c0b411414809840c004c40001790f42c0140901c0400455116640c003a00c102c0d0f581d0b82da410220300401180c0d20450000c6c5500c0030344442d05d100005102c1c207944000700a0340c980810082080b040381d1010030103c0c1815020322000c940198288901402494800050491050141030380b2032524400e800101c468240d88005200403d404250250f00100c60200180c1e10754041c00160360140f07401e01c00800941c0000004290554004c1c0011200d9100380ca070b0803559034981c0307401e540e94054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 2344387 1250 2343137 2343139
    0x40b04090c02030409020d020301030618030e04050903160b0702070b040b0910090503010c0c110301020406020a260309010b03010b0909030304020103111312020a0e0105030709020705070e0103050a0c05030309 91
    0x105100520504299902220244426004a81c42c05070744002081c10313a04000403440d00c0a50100041083c84100d004280c1501100036114210380301e0ba5401802980300f414616025a0f520b0000907807200c4200b0803107802034203000749603018075035901e070402110f0401c441120040c0202100040d07503088400030b070b40a6800640640d03003800142c10601c110034100d200c0070000c01181d4200002e03a0f40b800c1c820302010307810740e40e03404440e003500d8113001422040c400c01e0240203a00c104405c002ca2980400c01d2084164420292400c1000221404180e5008400081e9074080d000040c00604441584007410668040c0d000340104500103040080794142220000a0ba80003080080d00542c400d43c0f08032007041400002c50708000000e0441d140019507034001c4001c0c0004100b002c000c0d407400400302c04c02440c80380d400d07a00b40d605041c08a030701da1081d480b8090b0941c0e00420b0b844100038085c0303e86005403211640c60b12040d0303074a01b0120341e41e2078510030984840912440214050401000b00d1b0b40080c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 2345637 1250 2344387 2344409
    0x8070f0501080c09030a0f03020c040b010801081509030d06060f090902040f050f0d060501060f110303010308040b0304030c020910230f01050c010e03030103030c0b0109020a0210090f0218010609060504 88
    0x560080704003c0c0c1c0e40b040c5480c5501d405980d03282d10000300003850a2428900985c010500c2501000c11301040f00c00124465041c4291040100080702001541d610341c00644100042684c40752811903141d4050034032500449401d010021800701d40c82078001600e20115036444881c40d0b0348201d220708074440c1d8041c8001d1171071302079400c4c00503080281a0304070036000609034141d459030a840c0e80303046075000e030001e20014240921b02c0c1c0030903a11090601c21646040065413841d4035564031050588510f21a0300c050740070100000741490300510911000b550060001c458a20b00b902c803c0c1d4a845090095885a4070b20a0000e4100c414540c40080b040001401e100c2881d1015030040da616000010380e56859074982c8419160f0040034406140290301c242c039090321091040c500b41d03140d020140c02115070f0a1040c01500041a40010141200d80e9540400140c104560800110f500c02c4144041c2d0860144d5445401b40c0b103405800c54102c0d00140d44141146071144d204850314466482244c000702 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 2346887 1250 2345637 2345641
    0xa02070e090d0c020105090409060501050f030304150c0f060c030b040e01181509081801020f12030105090c07060c0f0f093209010303020f0106090209010c060b01021905060108070f050108 82
    0x2070f0041c0328100596005051590a015541b8006015036103c010201c443d103443c2d6004110506141140e9504000120085d60620342007912116010032111942c0c4e040010308445e0f002442101c01d184000319400c410140200c1810646c05405410b107c240301c0d02413850142446200541071088154400518008813411001c9482e004908414002c4400f105a900d15415002402030002006541449210401d2a404007000a030800d002280c500c840c3d900a0450f9105901c07661080320705403082200c00c0306603525002c0b1850140c4c01940801001145481c00c54a08a9048150102560800e80d00c2640c00944640700702d6882c0114818503003025040c43e01d034100500c108940041c00030045801110080044000071041103003a801a030168100d01c140c600c18801c00c0c040c400151803601d10540c03810449600007401c402103104040c0c9000e0381c1307542945580e8402d01810740c418085412071a46014a41001511140b081c0314428091250100c0011013000d821500d4080b01c0e41611040b03520307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 2348137 1250 2346887 2346913
    0x10206070504050913020f03010e15060103050c04090c020a060609020304110402090d03030504050f12120702030301050d06090311010203010603060f05040b010c08070302010902060406080906090105061f020703060f020a02070e09 100
    0x18032510f00300e911040c0445103001f161800d00c40d51600000b03540080940400000c2030101818003c0d004504242c140001c0044010805007104c0444040d0140042c18000110003203080440e5600d006040504015000075004400d402860003079000d94041442807410004010407481105107140d0009045445440840c2c080d5102a900c00c0c062402e0741d82c000802580c02c1d0a0160311848480580401305200c4c3c0c50140c080310840e4042e41d41d000561641d410030f4009003a40020300c6000304559281c5034120100743c41000341d16a806180402507445e561a6034020b00542140d00500400004000e4009540d14042c0141c172404003040c0c45540302a009a02d03014510f0380031807404d0302559200c080741d02c0162030700b400900041c105a030310400a81013081d8024103280001e4540103541c4c2c1454144032181e52055031080c1915845800e581a1405100059007010051b900281c604c9180c480c06c3c00e000c0d00c90750010040107c20307078280e03a2840d4603850014500942599610f00c507500c0b001d13541146c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 2349387 1250 2348137 2348161
    0x1501200718020705030403030203030f0901090c0e09010915020306040f05040b01060e0612010303030f05090a020108061002010608030304210f080103020f15030702010606030617060c0d0902031203060102060705040509 95
    0x10406180d005843c02485440e2035241d0b80c000e40c0114010381c400400c0004c05204010308a8001c50a400240700c0c0b9034040d201d04828203c2070140401041e80d2001266080e0f100754040c4034051350042281110b401d100c01c89400030b4004480c030f1030246042414144000c0040e00c1031610032039201846400d56420103a00720f483c001c0070071030aa00b01104000b2901d5544d0791042c2c50b4001c62090b40c001c10000280c401380d01c191103003e131089455a104512100060b81c01800d1940d2001c803d45990555521429080740074000c070f41d00820242c0800070510003071203040b15070702400303c41e0700c000e43d260f50b030b455201298942d0b01560700340001840307800140010701d821080000e032a0300c014240320b102291075002d11819070082d512003026030342d1550304100c0c568041c05500c0061003180c8035021150300c107208458407007000406c200381c0254000384042408007903500511840340c001d022109a050301d940d80e50a964020383d04180035110f0300700045c0040d4031030000c403000c0d00c40c00740c4440352544031090b213120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 2350637 1250 2349387 2349419
    0x305040b0c01090209010308040504060b0c0a0308060a050a0f0503010507020601050a09020901030207060c11060603060601050706050a0e0706050a020c0901140904020a0315020405040b0d0503220b0315012007 91
    0x1c0e555240c020b02809a0786419485010b1402510f96603580c40c07801080000b10740c2954403402d44c072001841000102c05000c43d400c03590507090306222115596080c000742e001d85c4c803600000e521810811000c50901d10655202040c0c1b0010b0f4000c20007501c075144d05076620721007403080781c0c4d0040e01c000013800140d07102d170007500e460704041c10050f091180c01c1d0f032901d00b075620715141c0000081801c1942c000900003004280e03003281c0298050034460900e103000a055120f030200140c5000e4407a40415010340203503114a080849000035180c845450303400003045a4000086030005201d4079203800124905a200c0314120344003001400f44840220044c40782054005006aa010700b040500002041e00c1c00e01d10268810382c2d281c0140e41d43c1c102810001103429050f040c80c0a11146101e07000003540c00011201900011240e65031030160001c5141020441c0d90030107095214040207010208144216030b001c0750100f6258070411042e00100500740020712481e0070020391001000304106050200828 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 2351887 1250 2350637 2350657
    0xa030b1303030e030a0503090c040501050102061314060c070201091707030201030c122a020102040b070b091c030f06050105120117030702120705091806040305030703021606050405060903070305040b 87
    0x4251450f1044500341583c00500481005c0b075000410011510000d206940c00802e00325810032040d414030340005c0d13030340300700034490180d0340781701c02c4204148a2100205003000000b84100d5400e440c020a021000d41c11240080703000c80c0140b1800700e85070343e8808420f0343e8100e481000300032242c615001140031f040500040d605102d800181c5400c00021070244450740d45208582d8040e0030603002c20300b6065070f105000700085903c1480203001e8130084508813050981c00030540d044540741e0360401da00f0a03100030880e505035400b20101c039640d9901038001100151116504104c101d50301d1005403500d1040c1580e5015401c8103000511160881c2c3c502240c030001c240084904014840d40441d80d00d0b443c002c8180d84581c0f00d10402c201c00e107400107a00d5800401c945220708401741400d0903664400700500000c0c1441000300014094a01c25810b50761040d10400103c500307600700d410403034000d090580f0240c840d40a84400220015000811076042c140d0550350249000d1508500300140d130031180c00c032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 2353137 1250 2351887 2351891
    0xd17091c030c0305090f04090f020306010b13090c050c06010603140f04030503070324060201050405010506040b03030403030c06140103140f190f110a0b0307020c040908030105040903030902030609010207060b0a030b130303 97
    0x6d09038560b0310864421921a2144a0400700d0b41d00425141040503072010500e080200860400043d5560107401110708400300814000300301c010a40c6c55000d100e5130600d407486104000110654140c010003050344031901b4900140c3c9441c265000721940c1120050003140e8200041103116200341d00000c00ea400048501c0c2c00114030800a01950046901c00c0340180e4481d001e100c244003081c0304580e00080c08917003c01c0074541d0703500440d8980c0114840902400110f40710003040c4140c541100081c1860445150904d40c2c4910700790101c402e48145607100d41c40344030444648000300254a0020301c0340d4100d041c01940d040da44001c0010401c402c2218804140d0104217015220314010201038075070400d0940d101d2510030780c001e2511080c95030061049051a4035403000c1074450040364150703a4151800302d406c03d2242401c0c4c02034844858029094412041000721042c2e0650240c4000c0c0e210341e505001c241040402c00c4103000640c040a010b101c5604041071201d40740d144101c007820300c42c8c200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 2354387 1250 2353137 2353159
    0x20301050604171e0114060909060606070503040b0304060207060c020703020a170102040b030406020403120203090904030807030b1203040501120203010509060402030718060801060f020f06060402090d17091c030c030509 96
    0x3854101603001101180701740c0d10340f1000c400410145407483d5020100352800b047da8074090001560b924006001c05018000c002124070a00c401401201c0244c02d104245607501c1c28240b03000340081d0700c0940c003a034180c1d1804d00c0207812644082000b9046a8005203c0d0501506012604020880c50104401190341c00c1000142100101029504c11030007540c0041e00d5a103176090003a07080003291400b00c1150000c10050000350b0740e081504d5040380e018581501c0d40e55039140300307034010000c68640341c2d80401078111038045608000018003d9504c2070341c3d510070043c800340c9000300b80c3c0003c1c00756591004041e030029400c1d0030568051a4811078031328007070b1181000f241c0011100070958124500141109006100f8603402c54000d10743ca0045200820724a11121803180e200ea0001e08203a2041d900050032950658441034052410ba41060a00d8204040700455240e00d40c00010180e0140b511907441c465929041d04004c161660107840e0103540b8006550121040c1c3e002450b029844140016 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 2355637 1250 2354387 2354413
    0x3070b0d15180b0109030305121302030f07060906050406050906070503070209010905040209060108040206070210020309041508010507020c010c1203060306020c0f060a05130b040501060801020c100e0102030105060417 95
    0x1d1254014000080064482c2d44200090030642e044190590b041c017102c000c0410000c0e03445004c6500741c90501c1480030f9682c60300c1d101d05041e0040004003962520660f5a44600c0703400100e9004115502c41d01c910000c203580310300c1940c241c003491143c4030108800380411850780c2003d000518030300d842a429a841d2454550018800c82400c1c1c20003009030382e81e442001f0850030f00c00c10442d04050242007024141c50680c0c00076240707104184009006041074004a81014020001d07102611801001403000c1c0140504a144280061140311000e608010120303c11500100701c2e003001b50300c1a50b48040c510a40d480740004070f09411a0281010303903481c8000301141e06072018004660480001d0403450000701050fa1038032502400203000b6a140c00280040c518880c0350072a0003650000c50000c40c0c0ea04c60820b20700400903540100450750002400c0c194407400411441c81007101c010301001a1120141054200d00003401403e40098041005010b1440d51220610503041460210340c2c0d43e01d0100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 2356887 1250 2355637 2355671
    0x30408010504080c060907030b04200402030901090b060607050a03081f03060b01020607030501080601050d03021204140307060908060105010c0609020d0b0a0e010b100e030f1b12010b03070b0d 84
    0x45041e60f4a54001c100c00400380824000c01d500060840e000701300c06829a120001840360151000740109030740b01581020b0b00101c07541c1154944014400c42d00c80c40c4c0f40344045e02a00308000100c1d0791040758800103000d441c0040a0702c5c03040d41c120006108043d401d6030196003a9a02510014a90310145030032034400c01804e00b14005144684000304405030369000191a003900900a03178141410b110050180c08000500941190340031500202c004007035040582c28030b403800b44240b046020001c1c000c211110b0101450341102010b4084034031440d0b0703c01e012500c5206c513019801098101d01c00403c407641c0b08404034202240100000580d0300100c1d80007515802d09200c04417244881d0008101d005040c1d0b10a49411451000c002d02c040039218000401181110500314180408081c0490345900c040000042e00c400d408215000344007401d0f000c1d10500855080c40d0b2103071002d0841100148010302421a0211002c0c000304490b609081052001c1d401900e011180a03a8680b0a010303403505203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 2358137 1250 2356887 2356891
    0xc0b030403020312090c030d03020f04030b01030501060f060206070804020103051503010203070806030d0905060d02070c08030a0c170702011704030201020d0c0504080709060f030807110a0b03060109050109060c0f050304080105 99
    0xa4000750380e9000b0368181030a4100008000503450707006103046e42e1440d01d0200749922806220f180040c0e542e41d1008641426000d01e400141c0364168400c004010041c1c1544030200340c07403400c0c05201142d90b80d4070089945507000c07260500020400300c0818010b5003c1d410058200701c4400c8881d10001001011a003283c01c112032407000140d0420612150b810203000c5001400030600c0c01c00b19072414400480c2240c030030070786034001d1103900003402003d100c045030829010300404c9040e00d41d15011600002d0161380d9081c420f880050740e403a07120441d0000d000440b14440d5042e1101e01c41d0f00c86000b41092000d000401c02d90940d5001c01c00c410025070148110300c1080f10503110303951640c1c1011080d52402d040b642100e0f088a1074000f0900c515000004100c08032980014801c3c1e48082501d0b0044698001e0341c022504030111901c0800c41c81b5860f00a10303c2031500fa44c0702e06071070350340e0b400451b440e540701d109010100e60818141c0001c185101c0550403054003607822a45030541e00c0258a084441c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 2359387 1250 2358137 2358143
    0x40b0d03020105060a050307060212030a06030203030a02060406060509040c060305040501090605131103010501030305090907020c09010e040201080a0c080c070311060c0415050c0c040b03010b0301090b01090e12030703090c0b0304 100
    0x150f90100000c2d17107000c182407400341c00f0680080240500f05071010350b8503c000702428490040100000d10700c0e400c42c0d00000003469014003500d45898035088007030360b6500c0580c0e00b10360040c1000c101045a040c143c00d00703407013136420070000440a40340072000c1d402000c028105035019501c0d12261400f01d4094054140604e03400b082c07407500302520b0300301814420000f940061280e41031200400c0400d0f0b200065501c081405c541c206602d40303406406a1418241d102400d420003022000082c0c0824a40d4100b07200c4c80c005c1e02d4405c1243c1e5000441e20444162502480200e5581008103241c01c0d03581018041c0d543c424203102500c103090750181840c1c05030460f15640a010000b80601c5840c4c80c3c000603d0b40c12090341003280c10b2120400e011905c8048040201d40603642d10343ca640303400c1d5005d4110381c00d0281c0280082000c00d0050600b01001da00034080e41100b182810110307040510001401c50003145168070440c190745420031301310082e2042d030000f81c0395070048070380204040070001c00550141d44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 2360637 1250 2359387 2359391
    0x3020d0203031b1006060201140402090606070c080c01120207030210050a06120c0602010e030a0807080601091502010903020f070b030a05090c0306010e040203070f0803120a0608070815010b090a0e0402040b0d030201 94
    0x40f4144c0c4406a400c1ca4010784116414043c1c003d10700c1d12551700b400c1e0001e40c1100d02d20a20360300e000100d0400e0051200140c019a1405400a542040440c40d9200c20f5820f80e58904580c0019140b001079210b640c1c801030040e0710001070302c5410b28040e07010036048001c8180101c0c40302d5840a15030a05806ca22042d05c8081151104004a54091190a800340d8000e0051401c1201c50b0351302030720406000300341e402848851000510740e82c1c03082e01404051304184040001008101070f00900034160310000300c0c051312801070550398905000916200b16070003c00594a0356580504d0b00010305005414241281702d407115100c0c00d41e60074000355002e02111080c0b4069880c140c0109480c2c12004c0d400802079058428042c040c04001000322141c042021044100700d450740c80800c001408141d200820324040e08101090800b404100c901070f140600c51000f26a0f600c9140303200d07544c41a4401180c0c0696801020402401001e4a80385c2c028001040001c8002c001e1012a41d9049015402c41c01070f5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 2361887 1250 2360637 2360653
    0x20a02010608100e07030b04170304061a0603010b0d02070c0f03030c03031107030509060702030a1b0602060a05060a06110705030601090e01050709060206071d06070b010305121303020d0203031b 85
    0x4007080100d81034010390f6400520507040d16003100c1c0e8079044640406008903c2610029041c002c00001d0b2141303281c00000c49959900e82402c02100410010110440c240008200c0c0310880ca03000f0305881c16600102490340c50705607a058040c0007503200c0c1c1400c0382c00d01e030f054034001440780000d084480114000d8070b41c0d40c000c028a1400800b11022020100c10680b0b05000e0000425440001c1c0d6214003019101142e031044513000007468040750100c010810a0007024000e00714800f0009202116000d07021620181c0342c080307810066460480300950091a00c0504000f100d10458164213240211019a008280c403400400c2c10040700f6000a03280c0307a15030310746601c80802407055030f9000d0788520b04480303d41c1c2040c00c000d45441d400b5064108011604042075034500c1c1c0d071180c139030750300000404041c2d4403d01d07481e108007004000d110551312070254000307003030200a009044684050368040007511f03440c1541c0c20020811a000e509980604c002d01400156030f501e55145800c080c2a00000c0c8440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 2363137 1250 2361887 2361899
    0x10603020405150f040302060304020103140702010b0f040b031b0109090203010602010207020f0405040b010501180801061d06030d0c06051806040606050f0102010b010912030309020303030f01090c05041203030507090801020a020106 101
    0xc200f074201070300c0380340c5010840800c140c02e82da815141541d9040350101c1e035907111400102c01400305800c194a81c00701c41c106005e8010b0701540401044942a11248880410341c0b00f00022201c16918050b010b4214000e51403100c100031190141b5954141040c030115030303e030b04400702280c109070800c074051b070343c0003075044190b18069014001d110f4044500b484079103010758074149808010300c509814014500c00c0d842e0310160740e95180000d000008002c200140c0c0c1da17552444104001c050303082d108104840460030504005c00c142001600649991020115039a00d280c01070a0040404410036481c2d5101040e90006100450180f03002c1d810100f605801c1c030003000810003181c9030040c1560b02d440200c0c8117590700720132103030201c500a4058080b500b441d41030903006040034410003176042c040042044515400b84460340d050703e480303280811a026a030324040c0c4244c823882c011104040b80942d02200020303c00c0e00030640c800006d20701646070f00e0f541c03500c850aa8103d080c5090150b51511400d10103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 2364387 1250 2363137 2363149
    0x20a0201140304120804020103110c010504020406080106080303011401050910020609010507050301060903060906020d0c050403110301110d0e010608031b0c04090305120406090b010311100804050d030e070302030303010603020405 100
    0x5072041d84065865030510740d8501d10043c2e40003020f042030014500009007076a0081e0710122004100c1d21420342d80d00c0c2c1c0400e03824000d0404940491185141c24000309a45d1014030811050302c0360399004600e1a424190300a54030090064901d040240401420811381c0340c220000c0701c0c40c0540d400520307003418554003243c01c1d02c0008041108006050004004450340a017185040f00d40100001950300503a0070501c0c064410a6844070115040c030b04540c0045e5440b030000c0040302d0048144d2030110a00070101400e03111b404012010002c02442042c43c501070340c0e402907c41c2d031001000002c100c0d030340d41d5240f4156080b500b51114100e60245c00c10000010900c685036406800b200c0400c90117615940180850042c41312440451005400113420084542d0020015a41015140d0100d682da440c082c150701e41304820550042e1340400d08200741c1070003890800e014035401006408040305070b000442c001d04194540170b00078460a4400005a10107000940c081e0a50b50340240e501c40c204411702c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 2365637 1250 2364387 2364407
    0x70e010305040302060112030302070614010501090602010506090c0313020a030303020c010c0206101e0807030606140103051306020a050904020d0203040c05030d0c08090f03030a02070302040501050d15020904021306020a0201 98
    0x41850704003000c200c0001c0e40850654151280b800c0b0b000403c040b281400c500038000c1140c020f10003480c20f0040401c004580b08554101e403000d0740c924844035101c034001c900366401034501d5070b0411000c1022685c00381c0d2290107143d004e00344c49030800040c9942c3d000600400c3c081d0348140c005c00e900044045040c0c4080c05003900000d901e00040941c3d041500500d02648100d1141c56070264014000400c50a10791101100818900302103d085070313124203120005001c40d100b071880510202900c84503550203406610310502c500b0140004070740050300c0300d81c043e62002c0b025808020301007110040c2c9964910240c803404880300b40050b2a1b01c0d00345088010002c168101341e00c01d50000c4950b61816601403082940b4683c00801030351150900004a4a1701c6001c15540c0e900d400301042820b40a5800118601100d000700c400784410f9a9650078480e90441031040507102d0f4070301d10000c60045400d0b400611045101801c018640ba20070080b0b07500e0110240c20080043c3c010082040540d070340083e241d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 2366887 1250 2365637 2365639
    0x1009032108040602090402041502060a0507080106020309012a030503040b0106020703050a080901090b1204030f0f0509010804051005040c0602060601020c06030601080603150a0b0a0f1401120f14070e 87
    0xc0c014031004002805030480100000c00703407500010301040036240c58060340c00a0030346500600c0000030400010707455001c1180c8180203103140000180d2a07a10921440781202c030076402551a0422030001100c2c446542e519555100c0b80301242c0300196400c0d85500700a0328000e40c1e65036264105840e00212200c810380c494800c55011132020b101042c0c001c6100b0707420a5012484590310f000080043e03c044201d030703100b50b400040c046803043d40d2402506050b44034501c0f03541e904a00814020701601c086818000c160700040003806040380c254056400150010301550441d610740a10b14003907004e5640480c0c04a60b082c614400811155404100450700030350240040c140c5100d03c0408103c843c00005c0503181040000f401041040e20244401514041c14401c03881c01d5151040020010380031050301d03140541c0071820001380c2c4c2480302e5003900945a2048043c51900d510b04011503800380c0252141c9a401c1d925060341300d00400600c603480c00210b00e030703691070b0ba21b241010018100700c00740780d696 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 2368137 1250 2366887 2366933
    0xc030b030c0109061b02030a0f0302010b0901030c0b07030e03030406020d12050708060409020f09090706020f06010b030711030d02040e0703050112020a05040f0908040e040b01120507050609060702100903 89
    0x40c0380c0c1a030f004070455043e01e01d9864921400601101419000803a680c0c019405000352001c82c000d2000c0c07461010400d600a80080c8280c054440034040b6031042417002038403c4503501020b001201c0068003c2500764041c0c82d044051421300c00010b82076500030b40c0004056804503135008186900b00134000c101240c030040400141c544400e001d404004004c0446d031044d83c2d1018023200f19924007440c8659081d01902d0b8240d280b40c8060f015680341054000c880c0544202c051264560200081e0141a542c01001c50303411500c401c042614809407041c20b804c001c0c08103025810900300684051b100a0100982c89969401c1c000e1014017114010b8000542e00c40e04400c0080140e21228858000c55006803000030755801e101d60708100a00b0312040c0200f00d030100040002d13421007059001801036010381c100f0119640da4079042c0c00c058041a6005015800030f4108004a1030041d0241c1200080548194945051079000851100095400b20041800000c0074424411000d0009144e68500400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 2369387 1250 2368137 2368153
    0x302040e0f0604060216060f050901060503010207050c0d0309030803040f12030608030a0f12060305070e01080606010c0327061101060501050f0706050c0403060501030804030501050a020a0c02060c01110408010c030b03 95
    0x50390742c88440051014206a40019080f03507450741481c03995990716000a410010783e206828900054007003940e8860780f41d030030814041740f02e00d030600c2140c0009511400a00182e070080b41400a10418904198240282140e0000c04500001d00a5100f14410507201e50f2010a1b49030031410b40c00ca400d140420503142030700074030450300c0001c1150103009050501524100d4000422030307400178800a80c24400e4240f407800000c20200240300420395020b4156000140e80b20300c0034a50360b8004940a50021704070903500030100e401110a19080d15000078240c03a03000510300d07001c1e41c2c4183c9521010000e2514281da8a10550030b00c208009400e0901c2c1803450700d4030501c15107000f401404400b41c8625910008240c030584c00c031080710001d503408101800f40e50307580c0c1801c51054000e407000f40c515500b088002800c66016200f25040035000c9c0d154011a8540c079002d105880e000303902d400200d99a14040e83c19407050717150150005102c000e0011071006061140242680c4180c40d00300c0c00f80d800218 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 2370637 1250 2369387 2369413
    0x20106060801030807060605040e030702090606030c09090709080a03080106030e060108030a1812050f0607050702060403080a030b0d12020705010302040e06090712021c05010e0403020c06090105040f0803040302040e 94
    0xe03400b8112904040e4a54a6120074101400108155449298064a05205034003080c1000c0068281180202c42e401000d036286001e0062610007100d190380c1e000c1013008060101d10313144100640000c03240c80e02c20311712038486085d10700d001c0907480142c1c0891015001040f0b11075041c080d11907002c401c05c0192980e94500194243d4a018070000c0c030042c045c40c0c001c0d1110407244042c0a130004c0c5216240107088080d2403c095880d0300c01c1c450708000e54020400000d60580c01141150225540501900c0c580740c615100c001003500300410742010941c41e0000c0031219551212030b14081c0b0300480840301140d0210401929208156104905060061004104414510703a09503800242581c030b610050f505c2e0170f0f04680060441c081801510700c04296405020f408a00c0189410b061002c01c000503629a0f50000080310b00712030060040c0e000310020740342801e245014007c0c00c036060402034203082c1c03900d40c82c040b88a4240c110107626840480d04009518043c00341a910f200740401074040000c13120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 2371887 1250 2370637 2370647
    0xa0b040c05160201030506010e090f040c050901030507030204050604020921100b0f10021f05070e01050f03070c0809030d050304020306060402071a090a120201020a0e041107020925020f070602010606 87
    0x2503003c1d05140d42c400c00154240d0240710882d4554000500c4684203240821011004820941d0107680040c2011004175a40c20004a02d43c1030380d0304031005100c550315543c00c010140100403c0c00d90041c0d001c0c041c03d5117544413032011a19034101c200c210000c0340c036124225071500354041021b800d103a00b06a4481c2840c4c660507800c8191071070981d0f00500d100390801007070b49040480016202c0400c002c1415042000569000901821031661400603602c90600115031900440040d0540c0020400c0415805401030a2000410b841083c40b541401c1c941c000190505c5100c412003404a440041000114641071000c5e9500c004102d0302141011500c0d141c82001407000b198081400d04104081102c0030010000300324407560066102ca81003138aa04004d0207500b24003410800b00740210120080f914060150900b2110103000e80341c1014070980800402405c00f5256540d64501c00c11541c580042a504c941c47c501c1caa03800502400176070201d800c1c80e01d1075030f1303000d03030210b9141507003e0200e25448 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 2373137 1250 2371887 2371927
    0x30509030405010e040b0303040506030c040e0105010804020603070f02070306020a090609050901030503031602010b09041101080901090b0601030b060403050102030403020a0b010b0a0504031709090f061e090106030e0f060a0b040c05 101
    0x6980024941b49030002003450362080e81c100c2c41d8049404030800c1082610303440140151900c40f454461503999900040d2010071040d03034000e41c006400c2c000544c4051103a100c800f181041881240e0303200303540e510782104907445803140500003542208107210880c0c210310b24000410b01580c0301c2002e036245807605074482c0000b4103d08914011a0b0846803e68400d4200101440008040403070302e0401b0714201e0f0038281c074002d40754040f41d404800901d5120301840b48140450b0404102e02c6035941d0600114014144040c0700c5502080920003c070104009102a600c254070940003000340469504040d020301c0d605034088250391404100d201e50959000058070100c0b640402e4400103101c8002c0c2400791406404401a04048007504100d08294102c0109000b85003d903200384115220700c09428013100700302c034056081003a600040044074425440318481c5078115003030b25908041104c2190901405840401089032110100405441c00d4800c0b80080103ca04003a0703d00041483c031001c0007100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 2374387 1250 2373137 2373139
    0x3030e1204050f01030e0a0c0905010608180705100203070602040e0901051609050402070309050303070c1701180b0a11030c09130e1902150c100b0102010905120706020d02040305030901030509030405010e 89
    0x2154001b030314500d000c02c442c40b902d99004036017150742c0b03417100100300090809200d040000760101000c00c201c2c046804e40ca003044140007002c0c0410504000c14025407510340412101184001c200007408a076041c806030001e0003110400051038244130a1081c25620090b041100810107419240c80c015040742e0000121002514090b80f500090f06054924284030390006406003c005443c20401c035440c42c0b00340640c1d429461480180203010241400c8540c00484040d98031188100b01000c00c034110f010700da00404426020502e00c03204209411300d03410075688010500004912140c007480c01311100c1d56a4080c0743c1c400c020307002d0840c0340719940354500319042031102480c40800040d9220540c41903256094441e84560710804813040c9680c8445000291410302e142400c1500c40c2e44c4107009043d071158020340200584101000920034907402040c088441c1c030760030082040c82420034005040118001c4000d56145d88840c00003405a036002440c6000d04d820801040c4403507a0080208044803030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 2375637 1250 2374387 2374391
    0x80c030607080f0c070f081c02030603070e0a0b030f06010609050d030906030507020a02060414041505060301030b0709081e0f070b030a1e09080919030515040204090b010303030e1204050f0103 84
    0x740c0c644d140800d8031402038040d05070440342041e001442540b00c002c00d42c265038440c400341c142c0342e4581c03000c003240001c0d10000d40c107170420b401c20071020322209200b40d0400d5000c0c10000b1209501310000b0b00e8603455401d1a84184c010710010043c1940181c0b10b080240400c0c0c3d146404080141d4004159511034040e01041c55610404030ba00140308000c46190030f42c2c060700e682d65a42c2c45645400c2074030000049284624103146840802001c01480d030011188041d1105003107908550392034030300950081c03c0900300094007600040e0982e00300001c050004141c80c07400005800c1e00201d07410142c201582030a654040882000f040c0481011079a00c417403003103000240302068035891840c503011003922200d503904112018052047c0000144060f0382c040311080007082c50b00360b46e440c0081544c80060610b0308114030701e6580f500c484c0100342c1c0c01031004100098925480d62804808802a041a000255200504244614200800340c0c200f00320503c02c3d41420b2601000810f520550f0a90a040503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 2376887 1250 2375637 2375641
    0x30603071703090405070504081212070c080c010603060204030605060904021e0604030506010b030a060e01030308040b040804050d060b0102010b0409020604050d03110a0602070309050402250302070b070302010501080c030607080f 100
    0x700081c8180da00d51800240244010b0a00400040480c0c0050142c1d21090084000b0640c3c1c1c0400c0313130115070a400038840020104d07500c480b000e940c2d9141200c003e45a42c2400c1065022160080c07040c8006580305441c0103855609600302003040726801483c00d0301401c0d80c0f0382404050381e0b0761004801d84107030012174411040021030100c2c0c118002d90b40010311a00c41c2d8030020441a0b51000503501c20f21002000b084601c1c0d460101d40014442840068080741c1c000c0089808030b07404c0070000d81d11038000c3e0701d918602965240455580281d242041c5e85150359800b41300b0096034280075200d1110800c69050001c0005a00000d04e0b0303208a1041c10300c6100544401c9003003500400701040c400b5504016101c9403034107400e1000180d408100100c00140d420390740410a440c2a00c00d60f0b00913828034644e000c1101c000300f1003420000e410a4150103503c140b10000628072241c10080c00e000c2e10941c000305195241010040c41e2495908040f03202e50042d50821541c039902c9000a54400500d0221914903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 2378137 1250 2376887 2376929
    0x6040e0c0402120117070608070e0613031217010501090603020306040902030a1a0a0510031b030602030c090306090601060503060913050304030614070c0312020a09051801060207090203060307 84
    0x90401040030707080340c00481d50040c159212480e8504030350301d28400c030071000d4022444940ba1001801160045024100071500c4103124200d90350f5020009083d15103084207000e40c00e5202003c03584100d031280e13040240d07180781650003040c41140d08031003209100c440d414280003a0480000f4040c0004041d404400603025a4940c1c000221454001d0260341c507031011414488202c10840100590901840c404189508a80e1141c548203041c0007144030b41003030642c1d0350500e1900049901003040e07142d6450200c04520300744000d50040d0210001c9a07554510700051500b0408010461401ca80020004104468010080300d510290072200e0220503510603188440340c845194014020388004074020081000d29440309070781402e0203840710b2a5907a0071000b204c1d0424071241c0280003440742c100e0903202c4d42ca16006005200120b0030140310541d12000401d04503071103601c0364034802d003500c1c0040109039018807815003e0188001305500e51301c0e000010036994440b0b40b169046111103c1c01d10126 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 2379387 1250 2378137 2378143
    0x1060309080712030504031103090306010b0706090b012301050f07080304080c010f020d0b0d1203020309010b060d060905010806040305180a03020d0303050402030607020a0c0e06011b03020109050d08010b0306040e 93
    0x20890340402210324920103140d00130000c0900712003c07000302c0d550401c00140e4940c00070503964505001401455141c3c2072620f2402c268210b02c5d012902d003500c0b00c440c00c1c001509a21102c0c00380c03211400c0030303095181140760040c882c81400b03c807070305001c2e0400981d0314000c0c500d401c41709200c0e00400110343d60f480d9481c001ca064812900403403515442c000680100040d40c2c1c0081802c50341440c010720803052207000700444050502c0c0000d00e402140c5603180071803402a00a5580000d00800001d08100038201055942c0c3c85506c07800c1c4d042e1754400052044c07030413620420340035241290040c25503243c541d401030718501c94100041c444800c130f203440760100d42d0748032100c3d0061035002d0800b114480c018a0090042d01094500b207109008480010340d6243c070000301c1000c115000b4100000d168074041c1030300540c45000c0e24882c100084001991603891941d50006804c510070750000a001c200c4e410024104075040f80380000300110a801005046040815250030207021980042d03125000c080f00c0345 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 2380637 1250 2379387 2379397
    0x303051603050c03030103030918020306010e01030504080408010e03040302030f0f030d090204060308041d0603011a0d06090507080a0605010f1503150504050a020a02060903030405070e04050c09010b0d0b0312030106030908 97
    0xf140c0d100010000c0101036008407100212101e10074201100712030415440e00345e010031a02c007070009000d1100907100758401e4001ca600140035001d40740c40c01b502c600c9402c1c03d41d1091341103001c80303038400103003001182010800c049040c100003014181c00c1c15000e1107191a4451350003400285a1908450400e564444e07204400550340301e49004e6a9503500c4096a807204d940041611a07408114001601810180114074100d403441000030b0f8503c450740100140c000741d110068480320f0b650a0100e0004d5070400c810701c05040d6503401040803807100c3c0340500a84105070400011b038008104d080180f441e11202e040da07500414200851904490029030b800b6030203582c000303907100b8100b100b484036a01490b8001c00440300158292030302c2c2c1d078603030100d5070f52440281c074024580d0b44108010011a402040c62581240c450340596083d20356a20000d020400700b038001414986000900154000092140c00c40d000400d40c060310100400722022400ca0205100b43c40c103254855003c3c104000d55601221 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 2381887 1250 2380637 2380657
    0x1030308100801050109060510080106020c061602060a0309020a0909020d08030702030c0a0804080d0c02060301050603040807050a06050a0501050d0201020d050306010201020c0a0b0714030f07050a0c06020d05040308060406030305160305 103
    0x4070365a581c40505001d01008c0c4500341c0607034038182200700564030603c2864103a600d590001d120010b4000d00f8001e695105440d101c540c602c00030035810040c4e542c035000742400e00c0c2c184c1d030200b50b005441c01001080205544982c003034518181c1c141005855821901d1141030700032010b00d4480d034604200f41d0a5104801500c2c1050040e030841a003000b0b52007000d4010303154000100d444044242d042550401007030800a0360201c1c0a000410807454040c004541c002d10651030b503811b0000554646140803074200e4126841512201008603003402e512841d401881c0894403c10a81095000030351115003001d9094104400080001e89590003501210507040c80381e0111480d00d04c0e03e05000d10700da04180d0360741001540c0071002850b80c00702642600d000e00f082c01c10030b20040d150320005179181d50040a20b01c0c00d203d0304007000b0020030318034030203841c000c80c0c41c050128103032526190041101000428041c0308034a031203024000b00358130906880140386452000240032407242019034071801100d180c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 2383137 1250 2381887 2381891
    0x4111504030b07120510080714010c05030a090801050601030b0603040b060406050d0303020d0b060c03160201090504050a02030405010501150906031107050303010807090f020708030402091005030f2401080601030308100801 97
    0x844010703588141244620001c0344c00c02c003c9915400c1e0840c1c0d812001c0d124030280356100e16010b00191641c3d0144140c4613030f05041070a007000241c2c4e1840d0540d0410303903d5902003150408108109902030061560140e02460104142c0b074042c800a8240d01001d0400781c0300183c144005401c68aa41c0e000c038020b4a4001e0000b004443d882c0f4000b000b9600034080001c8890801215501a0400c0f000791420780810358045c605048403030640f180304000a40c1c0690420218400001d003a46440c81400d008510340c400c0075a81389440d060207070a40703406a01802825076040034445049a03c881400b007515100d140c08203054942803905021402401405003e03404000300000340074a001640c401203508415040c810410850550802c1303000d580d5001e4a168000c200040051a28200c40c0303902804007001620015200d00220707140c00b902840c075441590148024001c040c03241601c5004004103c0c05020566062140d0036484550610008082c0b111a201180d003a410400400016185903002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 2384387 1250 2383137 2383141
    0x402030901090c080d0905061e070f052103060402070503090418050601060804080a030c0201180501061d01030804030303091401020316080702030a0906080702190503070204050f04111504030b 84
    0x4180203025070107080b241441802000200c08001084600c0c18091544910054900c0c010521020703501c82c82044689e450700900500300d0300d2052000e450140c0c0100d102c110340544501c2c00c60320f000d1082910007203043c581490b1101007000c0c0301c00c0b258080c20079076015803a421603141552840c0907040d11280d01a080400c000040e03038401c580301031b00c14001c404886599907107072029661507905443c0504100010400c000e0001c1c0690000303807080000e40300000352038120929604c11107030354074400c4816946500042000e0107141c0b00c0000010040221070f07215500d5555404550300c0b036480000c06140d00e5150344410f000d6500024007140707203810020340d902d1070104005088c2c104030540b600003040710340001ca074001c2e1000003a0380b070001c59901da11440c1410194151440107009280804520880143c071002040c0803d46040d074611403001107458003e01c1c4104826038000420141a810040003004003203104181c1c03091003110152580c418104402c500c40e481407086c0d401c01b900488201003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 2385637 1250 2384387 2384401
    0xb0d080904050106080906151206092a030703020d0609020a0e010504050c090904031110091a090114070305060a03060504050307060b0a080c0f03030c06010b030106030c02060408070b15040203 84
    0x200511a080003210304100503a01c0391420f55070b0b810b003620380125540c001c1002032040e80050010001d40c140007042c481c150b40c150320500d481c0c804226445130081c1c100e400f00310401c02c80382050808007100c00c0c4551700c0064800c800f080d13035910f140c4800f80c89003407152410418008140d00492415030050150f03941103864000560010301e0a105250241d864000018140200501924000b4500421042e0341ea02c60347c0381220800103460259829000341e841464124203148502d140039849000074050079546410b0313107207400300e008080c41201e9041500079a41c107454241d003250711046e5800e00160ba9101e01010800c1c00c1104d80004010900d080140704c14024000081e0071020710031001400754885e51001e01066a296101d400110381c4240c0c00b012051810304000c42c1c24a40103003c590501c011540c140e80f80038002c0c0e21080091070000018004964940180c844140e0540003d0030281440c1e92429050b02c2002000780c0075209078004034020340c0010100c01040c0c01c00910640d00ea0410003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 2386887 1250 2385637 2385653
    0x100303020601120f02040203040302071e0602010b060c0607050a11030706050105030c0f0307051c020405010303030c0f0309030203041203030b0a06020102030a0b0306010302090103030806060c010903050901090b1206060903010b0d 100
    0x1000950161003481d00004a80701200641005030340e0100420060484035400c5c800a900081d200710150700401c030b030100300c05540300701c1a80c40c3c030249000e0001051505038046d0071901400540350180c98100491044090005801038100d400b601d0040e959822051040750f80c14080e40208019010000304103040c4200d41c1c10260603900708400f80c1d9100034040d81000349090f10034500c80d4242c0c005c4a400c0105203071402c0706100d14000e0071040742c1c0383c445580c0020700f212000d03001200072a5903442d4880e41181c0c45542070019214070b050800c0400c0e150385000e50b907802036201707003c069070079038141c2c8003014402c1d0010541c00002404265015031120b1029010350021540c1c0541d45103004101c04940c41d0014106040326000f07441c3d105140d0854408a4643c40001c000c0d98001e2000c000e0701d140003000348110f84025000381c1d9110340302c40443d07000611441403035201c80494542031041c4138119031080400341d007007035040381d0080d038405203240800d000d40301c0100340650041d0307604020b805100081c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 2388137 1250 2386887 2386889
    0x40501021b0102070c0b030603150108010507020601060c0305030402090714070c151d040f0605030a03020a03030c050702010806010804050f03120402040b0a03030807030207060209060a03020a110105010803070215090910 96
    0xc034252411010300c1c400d15402c0380180b0390050403010b80b0032403c001115420f0019034004070040e05132210b200c0310000100001c5002c0c1e0003160141c0d903400400009a030706201860142140786024004040d19440040640c000500081d1003501c24102084105015081903860b8418449030503403110782500704940090302c24400d2108241500d0907000702c40c4d102b51034030405507100d9108405440130007400e06c0b0042c00710000e0350301c0c401e03542c01340421590b50401024510510960042410300c8891400500383c500382c040c900107011050068100507a08005010360243c001e180c50000c996a5042c100e18011115004032010300000507080c2d0390100055005104d00d000399810700030318810070305108001000344400b90001c0c080d2808224034901c250000c0040c9405158054148121000015403c3d40720b00a0100400d40c0050400403181d046420007030380c20380f0f040c020030103985091b038015141e00ca0031000a21480d82c511181c6205102c41d81510071130540505550f00380c3c030303042180140c00780007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 2389387 1250 2388137 2388157
    0x9060c0c06060e100308090a0503010e0f01141003030c03020a06050a090b1008030301060503040c03120e21030405010509040204080a050703020109140a030f11030d0305010f060c05030901050903120304050102 91
    0xb8007030007144000d0740794045406800c24101c440846481e40e107400c0c2c1160010408035a0060248500180c00d507401d01590b400410000042e10807120411405402c441144007980c0c14200e00500300400381c08640c599004403900f5050181290b805807404a0030a160f4800007030070103182c442800540c41895001d04c040c00d1117201032146689541d050000074801a12500728036070b104200512000744210040c0d80c22510440302120712544a41e10700e180407101084a0303000401c40b0060078081d142911640041d6103140c11140313080c885441105e82c5a102c0d5004003418410009155031150b1200d5045a0040c904007040c1d51404600380b4125841c0c01003440183c2c00212084400b060080300240703030b948448070040620007441e282d42d9608124070601d0400f52040ba25110600455882c00e1002c41030454182c0c1d000a29581000048080d980d07442d00504200030403003c503000040c0f800402c0754210082400d0090b01e42d046040000d00c3c00400740c0150341050300c080241300400205402070b25070303520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 2390637 1250 2389387 2389391
    0x3070606170f03031012020a1502010b090106030b130b0a05040e07030b07050310060c0303060b0307020109050106080a0201080402090a06050307030303050907090c050702040e0c03010207030207030b0106050a0801030803090109060c0c06 103
    0x2c03070502e0300e95890100365203560354a040c1d90720404c4500715001000b10440e02c0a094903404c182d41d403500c201910003801c6440c015075100e020b0300e41c0624001715200d000d805281010000c0b14607200105d00e2103100c006401d110185d541500d0a4541e035000d1030034004040c020420b12008182a0805440701050302c1308481c40508a404280750b540100180c9200c1c601c11810f00710b1031450940201d88004003c8420360900d40c3d181404a008049031700218031810b9250000310310402c0c281303030007030840c2c0032a404548280c02807951080181c0c1c0c040f03015a003003501214004503070388514a1490041c403c035880f86030705200e00b103800010550941c110622481e02213003901c1000d5518000f40e420f4540707200d0310800054040001e000145000c1e0322090b1640905000c9036200b444442c040f9003240c0c001807040d030159100240400420074818441030140100349400e03402c0900ca6000686440701c10300000b024020040f0004010310801d51146801c43d4101105015200d000d51002d000d40e0101d600075a5024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 2391887 1250 2390637 2390653
    0x30518040902060a0e0f0907020606090a110414030c0603010303020a060b0405010501121a09130204060f061e050f04030305030103060b030109020306070f030e0303010803040f0906050303090607050307060617 91
    0x200d01071080c258a80e402400c444e161845102040b9541c080c0500c420380e00089000348074400d902d54607001889030b60242c00400190400320108403017450000c1c00c3c1d42000341041000c540540d01c2e041901c080b140240c00c038107022400718002a05003481049460341002c8080000010703da400142601658011202041111900000e21007501c900340101da0105d001030540b4200030714140d2200c9095011384248581c00d00a0a000031803030351040d078220b245150400702c554207510f003500c00d0070f0003041148440c0b00580d150100182059143d041e004203818000440f4243c2640100f0840b0005002d03012b00390369440c0c4905e4080e02c84d800a0009442c405c0c5403007150200c5050512403512a0b540040c000c0190380d950300302c2242c140312050912800c26468446400f401c0c00100f01440c06403015074080c2d500c4500f4030006440701d4a140d840b0040b030303e00b040020050340d200407044480d01c000c01d40f56a90786119038104945140304091009140c0742c5048000140100004c2409806440781c0f01501d03650 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 2393137 1250 2391887 2391889
    0xc160501080c09090c03041103010507030c030b0a0e0f06130c03020a030b060307080604150e09010507030b0108100302060706180606030302070602070506091c050a080301060e0d0305120603010209030a030518 91
    0x70f401100c001036080801e50b00826651101e12000d164800d10a410318601c402100000c00d0170b60302c3c140d803080040394940f02981000c0e5003600618044c00300944842549518168402d000c0c041c014001035458501c84006c0759190f110100c5421038940d401e8000e20000040c110020000e5000800540010f0310f07060341c078050f51800500304c9014031f00321340d81d500244c1c44400401005151303581c16620311226800c00000e40180014800e440340c000f10300006200d103800c40b00981681c000300c2580f070420034560100001c1003100340018042c0c0740c042d42ca00391a0380862420000805241c4101545d4000e411084800c02030076420900c190782c030980c00e550032140d480740c00766515949802210350060080c0600344241c204240d991860440c210281c208102c3c5540700c1034245890341c0019915210f00000602100750450b116807031001007139403071076001090303500d00a0450241c14140320302036016001142e4542c1c1c0035015542c03a1300c0b004003554840003c40c540034182d039000e05099110b04480d04020021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 2394387 1250 2393137 2393161
    0x10e0f011203120b010207150801090b03030a020303010e06040207020405040f030f080606070201050903070302060406091706011203050a020c03030a12050a09030906050c03120c09130c120e030c16050108 89
    0x20682c0d1503100c03014203072102a02c0c0c40c0900b070305800c02d42c1103200d00000000c03a22035060042c400780e040c5454003040f03541441c807254140c42e103800711140240d00030000248907540c000226411102612004140d45c1c44031400940070344100d09000c2d61207810281030000b440002408256451702c42d40b5180c0035485803030016110280c04896080d03111009004c00005540104002c048107080101607408103920b03603000406642058110000245140000380b00003c4804400042d4951101c02085c0300d40c90003140e44050304003e60010200003012400c8040e541c020055130884947c02020b41e0345941c0000030040500d540b508814419038101301c0450810541031186842868050b592140c0d00c2d41411800c0d9141d9114076007100c16444100a005184035000c4003403405050340c0a2026500d24103013003005a100040d601ca0f668580c0b80c80312811010380c0040e0b60780a440385d0000045107a400b400416802c5000c0c035581c64826006566249824948503c62101500d00903242d201e01607c607008140c003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 2395637 1250 2394387 2394419
    0x30106030e060f040b131502040906051c0b0402010309080c0706020606040f0e0a0206070314071a06040506180a0b0310050402120f030d020d1805070503010501091404120c0209010e0f01 81
    0x5c0b0700f0020000c00c003800010454a1400f600031108080d5880311319440c4c00c100d034040c1c0c3c88400070a645607414411458080d62100c001040020900b41407800da031148100d0f540007400007410701d03507618060410050900b01742d80510094078242d402140e5502c3c0c01035200c00d004c0702c01b42d00c10351520301461030341c0c2c60902c030f020b0080c005140100200407065003480384c0340e84081015418080000e05a400f20380f5808000c107110351081b0714955006056016814014402800303552046007000304200d20f0f9141c5003110300382c0311690030300118503888603242c2e04010440c00f482150540102c950481d00d48409401290140d40300b40d481207510b01c62212038a4440d29092208a0960402c11501e0b60b14041034002e8000503a103494002072904240700c034410880ca4108040340e168014020401461500380b055500400c904230042c4420301101402c54002030300103000078070508180241c1d140c2e40707110f48031860101d070b809031021006584900d907216080f4402c4540303a00950300c0d140081941c120b01d4402e10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 2396887 1250 2395637 2395643
    0x9010207080d0506030f070b040801050f07020c0409031101020a030902030c060f160204060b040806040506011a0702010507080409090803010305061303050301051c170d060503010209010c08130308030106030e060f04 94
    0x42c204100440700e44090300000d801103031706108240304000c2c0e1344002c0c0104002030a20352a565620342c601401e03142501c40c0244141d04801848041011036034011810841040c81120002200b100503c0c0580c0c02c8101d40300451b2296102191440210340c140c4c0c0407000e03403402101182c01c0f084040c41002003e20540c1d01040c810202486461541ca020795008202c4620040c0046182a192440744640c0e4105a000d080264030034000c4c0300c2404001d0000d14007400303051000d4841414941100d111a1054102c000e0400030001000414411090242c4011b440700c7c0f03a0900c4200c2c81c41c1402007480d0420700007542c0c13500501010030210503008108a06e04c5a05813035080c03e50303207044100700c202d01c001d030810300003070354a210600005040a84140360b00c600c0c84082c5522400d15003921800c842d20741c1c1255010740e00c10001021207a13001050b60b5030381580140c0f4665104150410b400d01500386500c0104002e00c00f1001042c0d15405410080c1d552580301d0442c0c0c059034503030f0024508000c040e107000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 2398137 1250 2396887 2396903
    0x20301050105070b0408070602030c030a050f060108070513080102040602010e25030f030e04050702060703060e0603060406020307020717030703031a0a0b090411040306050106080603030703020607030506040f0203070306050909010207 102
    0x180c00607200e1304210354070600810a132402d082c01e0352110f0043c0c1e1b0013204d0f41107141ca400410840f810520744115a00030840d604030b0510303031a03c100080c20540c1c0103803034401030141c0880c0d6603a00440a0354190081d0840310b00a6440f680d42c2c000180c040c0c04400b203021b40318041d2b606441e00b0b410160650501440005903501e9039149152101c41d40c90b002610244c04020320114800c5194890707005a6000e020300d0750003440d4511342443e00504640f1a6000b0003903c1250a06002042da000512144c201d0b802040040e03890300c0b010416841e0901c0f6501008030300b048140f60f114140c80120251114500a441c280030344611180859000543c0001e2154480c1c6440c1c0144840075900300640054000600002220241803801c4c6001d604140c2c41120075544880061180c0b942c1304403590b070004815030042d41071640d641c2c3c001c1d4a54100404000030155500e0003e41541c0d03441c0c000b081c2e5840d441e5411960313400c001800501a220340e00074180a80e8000300403901d02d0105200311442c1035002038003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 2399387 1250 2398137 2398147
    0xb0901081b040501030b0d05030a0c0c0603090312020c0705030a03031401050105030c0d0f0609060b03061e0627090109020a020d02030a02030403020607080403050102030f0405100605010905090703060803030106020a060b0301020301050105 104
    0x550042c0300b400501a0007c0b15140782000007081040201400c0406843c0e080c0c904a092600c20b07509241900210101406e041000c000070790011405503c1200300c40d0003585508013692240d01e010445e601a03030b4180b040021450a140c1c0680c0150904444101c148900b41c0c2c0315001591284000e4403191a0140c04121222079000980d00c1401da86050700e001269041d030343d2401005a803015080080888000400e101051400c444223022744d0718503040b1014400a48800103500b800b901c49488410b00300c8d600e4000700d00340003094201440d100142001d60b1941c655070b10800035049200001c0c058070038203001441541c00001501d00f03410b0550300462610303040d5400e0003010340040e801103e1070002444080005142030015502c65803a040845095103403506125252203410503100514030b14210090000d640c1c0410300c0815680309a900f0344040d101c03280110020072040e400b0408501010001250302036021591015180c006d0300300b131000d48043c80415080f44020300c01c0601107202005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 2400637 1250 2399387 2399389
    0x120313050c060307030f050f04021c031407030903060e060603100c030209030102071101090b07080306090405030d06030605070e1806010810031202010606080903030402010806010810030204060b0901081b0405 91
    0x494004540c400c109540000a40101203403003500161420350100b9210344444180b15840d1240b254095500d4107004c645003001d07004a4044291220030b0b280184a0440c1c81c41030500800000302c1000c00014015500d58003404c009000ca0458002100d1490800403654000710002076058000c520007070181c0081048214454000c06442201009054080c0081c0f41c066600784041c001c07880c080c0c041440604c000e040010180202a0000c0b02e00100600ca0701001c21a072400762503018406907100d84040d04c4030b0501034030314040c1ca4110b13020141007142c04420001d0031742040d4082c0d84191500310500e0303d07050421142e10024a04403a40c000104005000b40d0301c56641103400034140d14600001c1c07030700d0b43c817001140d5002400c40c4026039150542040807503441700c00b0961041440d00a14214146540000d10b0302c003001e455039040003a41c20208039040c0d50482c0e158011071740100104041607444c20082002d0f0400102c0d5408183c940700001c29017900341a14a8051040e4081d891910781020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 2401887 1250 2400637 2400661
    0x9090b010e15030a2021070c0f02010e09090a020405060103020a0206060d03050c070806070e10020c0904080904020d060510050304210306030c090b0a06050c0703060504080c0703031805031203 84
    0x5211030086a1110807883c000081900d243c40e018203c044a1540c40c03403c00000d28212100c03411b2003c400e0003010404c2002c44d030101072140000c2e4031091024401a050004031110301d03048a009900c994000203004100c44002140e1030240d1080da410f000c1682c07588015801c03030140030248000340c2c1040380000c00f689404003c5070b10862181c1400e5042010b0100440d2400d410340d04aa00c0d20360001c001d2118080d00605da0360400c50b81150050001741312418020b40ba0410b0030555406100300c031000c46c0030003001c501130f00d415000141c011074840c007003600d44901400661103098024800b100404540c1c901c15421648125003100c54000c03124102c400c1a501c10b5010501c5500701652840c000c030001d81d583c00060014406808003240ca03e02085c1080b12104040e400042071000402c80100b08810108115085913080b41c000030b9590b6641c1400c039134a1107040360031800ea0003032200102c2010381011000340e0845111a250410b280c0b10818142c0d5025441031080a1920600000381110420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 2403137 1250 2401887 2401891
    0x11202040f02040e04030804030905030304180c03061505040501090e0108060403080c0f070606030b0709030309060e0402070206030a050f090106080a02060a02010e0106080c03010c02061b07020111070609090b010e1503 95
    0x1c00c00610b000e5070340c0c0380700c80412420fa40481c005060602880705040d444441d501c041c000c00c8002d50b00d0149800001410700020b590501c4465840d11b0040380b0301030103540002d0041501c4081803a14261183d8010025400303401810f001c03a42030070010034104c07203021034a030603a640040145030341e0712162800d88510704002d00c0205410801c00008114102d29805060064440c40c4081100c505510b002d5a0f1103000401800402038560300030008668001421012a00c80f4140001c100c030750040400c01902c60608003135000714001042c01031880307540c1d010610030b50040b07a110a01e0340b0f0b0000b20500762207151050103142d6001d41607041c0580fa011000b422420200c0c000000d0150016820034291289030b88480c0d0a60080c540001c02c130b06082c0202c0d150310000780701500740c0e890103000725103030b02c1035000104100c044041960011640a15902c0984c3c9929804079103090307542d00340050000c4002e02880f0748240c2008400d420b00c1d40a07030403c00342402c0c024034501006c0d1003040280041d03000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 2404387 1250 2403137 2403161
    0x60613020306060f04080a0b011203090915050402040e06030705010c03020c100306090509010b0102010b191224020301050102070f050d0201030e01020d02040b09030610030302070303030507020c040507030207110901120204 97
    0x300009480f2a25500080000f0304600020307094180e008c5c1001c0540f40c6050384031511031a8070018400003c3c0c0d1180040e410b40f403c1200014140e08054030400c811040d070b400803a0824400140420541c0404020f01c0c440c4004400b184c0c1001d45410046440309d50000008000d45c0c001c0b9000e8039545811403003a00005030f1450001201c61b039605851055400c2070380ca012080c0d540740342c0342545503421300512444020645481691a90f800b01d043c071580c0442c0b10f8040b264600d541b1040801107425480600b0b00e40022240c0b9205480b00700c600c2c0203500078450300b405423003480c0000904401c5400f40c0011034500409100c48148140c00540181507000d84414180d5030070094029141e0b03c4c0c0c030261024110280352261225925024140b03440d001a21044001c07030403080800000703900041003000c0d41e50625000c191034031261401d0b40303001c19015a0651241c10041041010340d8544c0c080c01c2c40c0da00130982030001030307050010b121101c1020301420710302c449a00020805070800f80c00c01890504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 2405637 1250 2404387 2404399
    0xb030c0d09060f020705010b06090612090102130303090806010608070e040504020d0203100b01031107020901031203090501110c010c08060109060c0203030903030307030207051204050d060923010617060613020306 93
    0x70050361050100e4034440d010444042e40030a092003808802d11418140300030a44086144c6180b0700005442806989a411801052071380003800c80c031001c0d01a16804004800000070803030320380c90040d00d542e160b8022881c262040400015200c0d209400e8540180855210001038801e0304080c4005030100801c1640c10042d120503207001a1002c01c000714440800e100d000a805e030980000405489500f040d8181018082c854100584e80f44108607046a9101642c1c00c080402c17850280c0160141503405046541b920281504580b80749005103c1d05044a00821000d050303071605854080042c2c45160000303601c40d9080c400380e8000d441c0e6500082c002811a400c04500000192650b0300403103100b00042c0c2c022030150700f0040100400700c415010500f01d41d0a01c0d0030000450300e00b40c403895010708002e0300c49060109003d021140100c42000030008900340480040c02c140c0600580e1080030a81c1c0c0507100c3c580e005100c00701d10b10340103a83c0181003606008090400001940000e014658044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 2406887 1250 2405637 2405651
    0x40c06030b22020d0b0307030203100203060a030605070206010501110d0207051908010227030f120906070b04030e0f04060503060c03040813150201051506120403020f01090803090c0105040b030c0d 86
    0x26200507071200e410300242c000507a42d03c03100900d02d03040d100f40d50030060107030340000c4003440169008601c8000c002d80c1410010785a0b40c40000140d4010301c0c50344090816460b01061201d12640850340d24180c0344c085e2114406105e0002d441613035410079140d960700580080783c1c02d2256140c8a556a07502040c80342003250030549412640f403c90784007d10451034802051001d00c40841c12040d176500301c500031005490700d04d401640250b105c6984808031140340d240012030302c000740e58600c241d800a81c0c01c80d04041c9145081e2a0150409a03c802d407588038400031118881c4a1825008010955402a0161650b901c81140c060110340018000310360309103042c48049203c0c0010509500101a869640c6188030031030700019003100c00c007a040b1101d0302051a101c0c0d8181d182d17441142e04264078504242116039450500328202010441c0c0d8040c15400d106801c018082c10402a40c05414200c1c1950303c1801c0140054a1070300c038030701c20f608020b00284000b0f050505508040c0a03c9064894042095 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 2408137 1250 2406887 2406919
    0xb040b040e0a050706090e01170a140604031e090905090a050604030512091207020105090307050303040f03021203030402180403020c060a03020703080604050402060405060a0507020a030c080f010203040c06030b 92
    0x65210949001c0895000e0000342c01400310800250000b002c1d5410051011820808100c4461030140900000811542c58a6000d8441044030040d031941240e0028403040600062644a2900365801e4001070001000e460304103280140344d03400e07081c043d111409181d02d01015840500b40c0141012094004d603c4080c010072018008244241d201c1d070365041e44c50080e140d80c860060800b5083e08010b134814045034080781034420481d141950242462500c84850724002807034068580c11403505804080740014481c40941d1918080c0d03482141d01d0000b08003189101541d03404100d40180d030020462407404980030b0420211908079000f0301c1510300d00d01c41e03500403c425520902c1d100c40001c1d8001410418503521903000340e084941100c0610030b5007403580029501d4040d034081d080c419200021903160b0b031405031003114402c0f580a84150449a80ca0404410202c0d035881504080c1c01145041d0080900610880344110b600c200400d10b4103007410b0003140240081d1459541041c40c23400e8400135 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 2409387 1250 2408137 2408141
    0xf020301060203070311010203010e01050f060705010c0203040602010b090f0f040c0305010501060c110f030a0320010501090603110306070504120809030118030201200315240301030b010b090607060b040b04 90
    0x30740300d507400455442c0c2c0140342c01840804180803c1c07815900c10300045c40f807149140aa1340c1100e00c202c801b08055400b84000480501c10740c0c0004000e50310f082407a07a211600400030300300b00d0310250000c0000712250414002d03200800c407aa810400302000018045076807801449030032901444107102c80c80e07180c0c0d8a140c01c40c1c1c02a0003034030101c2c07041c0904008000c10200d045c29143d2003610504440e200300d8010944e259152800101405280302c000300119010841d0302181d606444002e00032569682c12081c003e2015000940f4400c9800c4612040750900060b4a801960655205442c01d032404943e08000044850216106e20b810000c0700110340d0240907108020f0110207000c4c800340c41780e250182c21140c0c10f0181c0c1c800e4140c00b10011200c0d600c0401501c0c2d0100b52004214000f080b2140024070001e441e0304041c0d0f456107441c01c05039800c88102c000d5810781c0e200d8003011b101c0b41d88900c20041c5e14019403140e0343d4400410400d060001d115078220390b0b1118005040400d860204e1b000080c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 2410637 1250 2409387 2409389
    0x2030f0403060203040606050406030f0201110f0a080d050703020306010c14010b180603010e0d02031213080f071214070f020a0302060d0b1302090a05210303040c050910080309010f030f020301 84
    0x40c81c2c0d40c01005000900480b03109141c0103080071142040300900c0d40d40c0383d440e60000542c1c042c2c1845010030381c8401450b000d02110000012180554411a80516280e00e01d030b003010f440c842c600e03131900740003400d024045d01c03c990090805031251240c0c0c0c000d50380c94441701e00303003031a444106548640c1c0c0d2481d0b50f210b5482c81501e01c00c010540c2c98241c40d08005060864180700209485907010301104450540c012003100d003040b40e200c41c140a00d913203046c641480340d02e4900c001040040c000a07034008492401005e0300c0100e10a09142010883e40301e41141c45e0110881c940c83c1c0701004000c0c039400501c000f00c0300c030300d07082c0b000e01800801590f94000403283d80006a1a04083c0c0d111000c0c0905031a04030006103825680072005c504080e03150b00400c0a2106074040c160080e9011003000111410410928010000500c122a40c03440c0c5803401304881c0465124907400b9a01c0c04000c1140400a0030045e420359002e00000c43c14803001e07400459900080702c8000040c5992080f02140c0c01500d400114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 2411887 1250 2410637 2410643
    0x31504032606010f02060c0a14040f030f0b01060f0203030708041407090b040e0a0b0a1d01020f07020901050102030307170a020f040e040201080105011803020103020a050f0a0801080f1209040203040302030f0403 92
    0x610740c40c103100090000d01c405080c80c0215040b8030100700194240300180d81184101e86405400b0101040400846200b185c11481c00e01c64000c03400400c02258020001100d031141c001456940d98403c006d44501308000c01d0840903030400d20005400d01e1050300000c1e070103030080f58401100704034681300320309000307a940012041c240c80310105156824507014801c40600e41100516445c142d640300c406201602500c2090f8081d260007808a0035104000e001c240580060021540d8803580c6200628950001000324024207441d00001259030020050328401c80c156101e17511803420368809a18100c100410310000b042d07003444000c48c0004943c0181018003041c0d0402c1c07403281424000034104d04c805030701641c100300c01e00050224400001d80d0480840340d0a080258903043d846100340d801d8000c000035010080004500092001c0d0711032600c83c100c4030b5550a864100000080c81034442e640d0010808016104000c4541d190401360300540e8401d000744192030400d440c42e4008d105551042d4802c1d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 2413137 1250 2411887 2411957
    0x10306050403030b0d050f06071106041203140109150b0a02030706050402010908070905090705040207030207060c1502031906060302090f0108060f040203040b0106080c04030c05011b0602040f0602100204030203150403 95
    0x40c2070351f12410050203400100c141401440c18a180c5a41503444c2c00003040200aa074480f441461224001c0d04030450790384102600c0d0809685030074816000380341c09407040042c002200800501c0341200d0007158008030b079640c0603510700700355038844802500b400b0300100e041160072400007800702d8041c07101c0c41c05401d600b1804100fa040218420f46000903641019108500c10411080041d400042220460f101405c104075030301381e80e0400079040c5030042030154210380000f04101d03a1120102400b01600d40c2d03042d0030880992141f40031030403809480f4a03d900320000c00e002d5500781d80942c86850388100b00910300d2a00c0f0890201140070382c0c10587d4119180054200180082504501c10750b500080345c0c0c1d0100d040c50320f581c40d41d000e1020680b00300e90502c110b440d000c5490441e200c144107040c0d5080001035540710b03554001c80c3c000d404d091060354018000d5650a803107142841c022501201c2d0024011712110000718000601c042002d80110309200c91f160300c6944080e030a00318541030807460001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 2414387 1250 2413137 2413153
    0xd02010902090906150909010b040606030b01031401030305030105040e100e030304050609030304020d0605060d021203030a0606030e070b09010c05010c020703020906010309050601090b01020115030804050411030c03010306050403030b0d05 104
    0x103000c2002d2015000e06100d400c00c0c030401a21102c2a0070401c1202c0d0115841d5400b9102c51288600528114240360b801c2420280c001c0f41d1207405800c0304483c0402a64100100c402010006e0f026840a00000300001c03070400040110b4a880d030001c405a0000b4070684081403103203078200382165200400703076400b41c002004110038024144941c5900c40c152402842c603503d090ba0000e075030582201c000502c50b40c3d079200402c0341034079090380b00c07041c0c1c5601a041c010504005a035080c0d0780d0300304a440000150605c03102081c25803090040082d1490180020501203088c44891034803504064062410003d21006507000320348240a401719140300c50300900341c0c1034298014402051002042141450b0800c502d03030000400006074141100d0703900400103019102000102d0141c2301341508401e2410103047c0200078410341000600444404440401000384180d03800201c600045a0814022006000400109130b8581255901c10b1192400103201400c6900203120100b421400b80c51030b0b4000c80e2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 2415637 1250 2414387 2414389
    0x5120708010501120b010b070b060108040609020607050703060b0109050a140d0b1003060606030c080403110c03150603070503010902060703030507050d05010b0c0606040506100e04230702010c050301030f0308180d02010902 97
    0x945c26000d0010581083d1034031080d52240e01d040580a01040d0421900718005400c0c040140d1041c060703070354000c1001da650030341820b00320342d124041c0c001615a00d182026000c0c4560003400302400f21140680501c0307030b80b441d011488540b03822050301140c100018240e01c1d400a02c0748003101d4420028070b81014140e40c118200007045600a800050030301d440c000040760500e030049101d0b503010340d0520300071034081d481c004c1a0742007820702c0d107038140c1511a181c0a119254603495000e0322a41c402c0c1c085522056640c0b04140c2a200c40890182d0400f60401000010a1198008a61000c070b6400e21614103c140300c0c814044030402da225104034400410311800c9914148a495000342044400f4401e0b410004001144113221071040c2c81408106020f4007040d488503007000c4010b194115030300c654400300b0f0301c0322204e0b4442121400015443c00c508421890300600030f4038160b0b034000f03106640081181d50240d8240385e000d8000060700c01c58144000080908011244819090307030b0000c00c030705920348 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 2416887 1250 2415637 2415653
    0x30a0807051002030105060f160605070302040608100f0303050a1e0804030e0405090705040b040f02070302010603050706020105010b09060703020307050a050d030b0d02030319050c0a0b04020a1e0512070801050112 93
    0x1c0e00840c0d00c2d40c010001005560754101c00c1d580c02c066044407a655501c4461724100b4202e102d260300030041810441040f42080d0075501a0007240c45540380e040542d56120000c01c03040200340980040a8a080001e0010070f1282c07000c2c1c016881d4a0428030031130100400c9042c1a041c80c0550000090542020041016400000c00d940f460040d50240b219080803048551034040394000c16020b25a91303150b00d179555030f45410160b6009040501159154007504009010340000e000a0742c003442a408000b806910501c43c15040f680c0300c072001c50900341c104c41000396992100006908501c07003806481c003c00c0081c800100e04c0780c80341c00200b480c40074101015003a140c44525035440340e07027030740a21400341e04d0120850b091625407032905610046207000654940c06011440601c03841782110500410101800440c0100c0c000c40d9280541903079213144203810a2076090303050391500380c07540402c0241404441030702c100c0000c4050b9900540c81d0b014813800c5400982c0113401050300400c0344c0051192507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 2418137 1250 2416887 2416903
    0xb04060c0e0d020103020f0f0301080102030a0501050303030403170403050706020c010c02010c020f06041b0305060c030702060a020a0f0804020a0b0a0503010f060306030308040b090118060506010e0102190201030218030a080705 99
    0x5070420030074011041001805881a03641c01074103041c0c00241440c02004410111400100320119280c0ca80d40c4801c207845c001d400c01c6902211103403402001240b940750000a03030b4400d55242e541e56180d0382c100440d07954041800382007142445405c2c410700c000145140040d10181000500020301d021101d80c0c0242901d001c1c207588015900042c0303030701120540c040341d402da120380c0040d9441003000d43c421040300c0c200341c2540f0290003030089405002c0c1d6001480000c5005a94a508681464580c0b1000f10100d00c50140010046a000302c8481c0c0001c0c09402029840b40c0014000225035945080c001140d900c40600700c00051130000041c0120845860008058142c51508019050444e540540b03c1e0304054030107015126808000b4165a07000d400c410800140000c5c138207912001d620303002010306000d03030300135010a450380c4044c10301e9440000e101d1042d0307040326130100340190301e40c005500075440400b90324803040c28040e0100094408004504000e807184201ea0f031b44200900f0918100505 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 2419387 1250 2418137 2418161
    0xd0f061104080a061d0706050415030b100c06090203030c0703031407051207050a020406090b0405061002060a02070201020106171c020303090303011703090907030605030705010207050d121b0b0406 86
    0x90009100b11000020442a00365120200181042a803a43d02180e41254042542c0511840c5030104031558400090812105842040341e28400e1985081d000e6481c4e5230407854000f19034889500455201e051418016030050030001122005500404c1c110f500c080207041a9a000110070403c240d804554044045250205181001c80d02c1d44d0b02c540750888443e69948118021580b00b01303004007440700c0380e50b0950062003000700c20303564034604015121480b1018030944c40c10002403c203003010003081d102e54050380e01501d2543c0d134949045009401130a41030381199698403020946c207022200c0611041c20410003421618003c0440500c00d082d144a4042150828020b0007242c0b0340c00030a484c15a204030151149843e0f02d1580c45285001d1b0302e1059034419240e9050000298055001c034042d96002d0b0142d9854648400c01682d8401c081d00c40c0d40d421100c0075040c44041840600c404a01e2059440c00862f40702000300c07a20500e030313110039040d40c1c90500c0c2010b000c01c126141c4107005441c80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 2420637 1250 2419387 2419421
    0x1608030105011b0b011401050409061404061203090b0310030606090204050405070c1106160501140406110408030301140a030f05010218040501030305030f0405010204080714090108010204030209040f0807020d0f06 93
    0x19141d5a25800300b0f0041c4030b006629101c00580c3c030754685c09441034270081c0242d603d04000785940c0d4040c8107800b0f9030041c80c00f40100d03d008404180501d204146d2030700300b50140c0b21841400d10700b00c2201595440100000c40307900c4814004000540c10303014000c001d0103102d201503110340c201030800049440180c449000e01400010307600c001200c22000c0d4000d0a42110081e89581034580400c01031045100020803551800d140c810214046e03000d1207020b40c0c004d0408200140c00c00c1d40d9010b2a200d9401041402d42c020f0004100e40802c00711024007915014181e0104241d40382d40c0c2d101d0002e042602140d5594001c5142031030f5201501c0f120080000c1224144019491920b01030050321002e00702c614500c50030b078002001e0010035011a00140704400460700c4036039887c0c0e4580c031005944164180f180058200002d448101402030f00d0540f034008080c056a5103a968030038200610815040b00e118009108190150780d466181c2d484a6014206c000c0d000750691500100f1200744d549501088c076 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 2421887 1250 2420637 2420687
    0x6060105030417030901020d05070c03020d110705041802060c03030403080a09020108010302090702070312020705040e01020c03090d1407060905100206040302061302040605090a020a0906020705060703030b06160803010501 97
    0x183d010855030000000d010780107030344c980744d2445040c064070032a03200880990901007071200982c1c0c85980c01c00d4150296096a41c000607a9004455140380307410126129401103609100da0301c1c1540c44161801c88128613107144201682c0800c0e040d8100d94040400743c4c1001c000c1109150300629042d40c40340049004000d25105a80007800d841d0042c040a4000d88210300050081c1d4001c0200c80d024540004003070010500d2080025511001c500606001d075040c41c0d90070300c41c181c05009980d00032485030044c3d814a2100701c00d014551204000079107614041c100140b114043c140b01030405003410741c0e50044a40d06000c148141e003994100c0c0c0d5011907015204000100b94081121078222143d2040d00320540f440b40005000303459035030400d692201010b400c0c0290f4641950003440c4001698480c000300c190340f10000c3e621104e90f03104a40d00041c0420178480081d110740c0c0100d03050600200400c0c2803040c0f950120010904c2c00204465030000000103121968000d0342141446100c0d030b204d08410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 2423137 1250 2421887 2421893
    0x15010503070f170108010b010e060405100f021204090207060b01080708040201030f02070803150901060206040507050105070602040801050a0b090c130b03090102040308030906011d060303071202030f04090608060601050304 97
    0x40d200041c00c00c01004011409019207601c180010400c2200c66903250401d540c41350b0ba281c0c020843c4803c01800300b54041c10320314841c20038409440845030024800310049040480550f03038820a280c440f001c500502c040583ca9a50603c0034001925071000016107662031403811500321050001042c1c14800300404000030a070307105003040d030701070350a29000c91884a80c108400181c0900040180300c10f00c04020446001440150841c4101c411901c1c041107980e1a082a03840d40c0080e9000340154100000a10040d4000c5004108651003888014505a601c05096007101da00351a40184c1544980740e02c2c0d6207140c016800da800100080101b4903207081c6031800c00030a0024482d2a001c1c07800032000450300c080a41c140e40096800c031026550700d00e4021b07100b0343c0310701013400765001c10b401c840c0a000025205100942c440d04018000310720b044103548545a5000b45400d03807a0441c0700411080394241900b0001d08010b0102510105403a400c00014501b4800020025810000148208004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 2424387 1250 2423137 2423147
    0x5150612070e040615020a020910050d06020a0c0b0103051606090f090b0604090908030a0507020106060c03080a0b0a090c11060601020c090c040f030c050102010e0c03072d0602030405091501 83
    0x403040c24040c0491500c000440c0c040e141e1341e844440301a0000710300314409500411040d0030b0310f10840d41540c40c0e41e108c1c6070600500440d80105034000b1821a038100c0040c060f80e00912600c00e0030f043c51072002e20640d461801d044000d8000300c1c1e0301d07001811a906028441180c04001c0e1910b414000c0510382045000b403504902d52081038041034560380e4812081d240c1d2001c440c00303402d00c0403040c850f010042c00c16a00c00d84c002c1d03480229452901002030000c1d44180710f0801660b906603150461518030381c0b0111600344020340400395040c0e0300c881d004075554401b680b9100800c0c038101c000c544500105006020001c00302c3c081c07410f50700700d40304008641e07902003142480590119a9140b05460702c1600d811680616004074000035400c08001c4184100000600700301c0360f00364000c1c40301d401806601d584402c48060305541560105a040c007641c080b000303010b001c6c03883c240d0300c88004500203c0e080c2c0304ac02c840c0e0300680242e0000101402641049600c40c0d40c07080d20120910a8480007000080c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 2425637 1250 2424387 2424391
    0x6030d0507170d090c060504050102030702060702040e010606121401030209010b071b0b12060d0209010902030901020702060f0a0e030703030207090c0c020d0b150a0503071202030312090105150612 86
    0x1080100004100c4104015a42031401103260515281c2d100e8504081c3c1d640245001c2006035110182c00d00001091446502203c0070340b54180e0140d03003442c4443e801d100c1c9641000a040380c1c4140c640c1e240301c80300d6100344a1000203001075520102c0109103000c81e5021280407484903030141e0018401030016890f01e01e81c060440d21008809540d483c40740c02c2409000c18040221f44100000381c20028000840601038051842c000c403148100707441c2c0c80c00700a0f8200d00084000d42101000307004201c03001c0303650302450748203d020002616100702c170760014031154440e0190000b412804142c8081c000d5000342070350303aa1801600180201401c5d52070103551018144144c0e4032141d00c07011201c03d02841000365a21059020740134400034001850125000790303085500c444001c1c01c22800c6c081504d0f1000e403201c01c403500600078042d05801c1c40d0310105206241c0c40240d80611007004074442c00304500c00c0b40d911076110b00300005928285201d644014849840e400340c4035071000c1c370500c0814000c0b400b4241d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 2426887 1250 2425637 2425663
    0x102070b060607050f06010f05010305070305070c150204090204030606030b0705030f0c0705011506020102070605060a050a05011107050d14060603030f09010804030210050a020c060c041a130305030409060302030c0102060603 98
    0x10f03031105071601e001480c052001c5540445070042e900000f0340c046c24a080541502e01c00d0300e05222039078460300c045045810441c3e92000251540c080c0d50b011400d0102c90b014500d61206000d4074080e11000c03140300340d13403056004503011a5191006c0051029030306c0741941101c43e80c80c00c90300d1400c204801d10300302c6a003d0184800d942c0000760400c2000000d501c624401600e141003440e603185c0e42c00000c3c0c001d41100b00e0980d81c640c10310300054424030300b00c48654144d40c8001d000b00d000301e040200440d089092812444200c0c403640360040b803182d0b02d90700c6105003140314a10350300301d92604c0c801603800c011000d0169406948140249400140584242d40d0710384400c0c038010720b460b561401c1c12072501201c0c046904403149400184106003000e600107100d01883c40f01104c1141e20382e04141041c621440c80794800c40309524101c6c19003002500000c1440440d00000b400d84903481c0e03190b003401d503030181d400070480507030b6907204208500b004d0001d0072086c0000d0024041d14900b2901107a21080311500c45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 2428137 1250 2426887 2426899
    0x901030201110307020a03080703020609070e071206080703081908010302090a02030406091202030c070501080c0307030b030a05010f020a09090b10080601030908040e100b0304030e04050c040305150709080102070b06 94
    0xc80b2a0004105403981e041d00200f440154542d20304100a0b0781d40b01110540041c0500e100040040c0c500040d0001110100030b0302a05a5545907021280042d424480c20401911082c0000f0101c00c1000940083d42c000d801c0c041da22600541d42006d41900b02000d441800b00c09801000981d0710f01802a503c1001c0c02000740e0f0b02c1c2e5842c94500010164540e0040c01074800425188516900001402c002d100040071a142252a2030040d54041403c8402c0c3c80308080c100300041580b40710350801c0d80159005011200c1c41c520a40d034550035903080e850800f00095011884003004c075072065a000080c032070080100115040c50380440c0315070900042e0601445001c80c04901140d200e9030000703940c543c0120355192070700d8039a01c40c0400f0020a0701d500940c201b08040100786034080e03a08a0b40116459118003441640e000300703100180500501c5100850801ccc0000000704005110018411302c0c2140c034000f00e031810310b002a02107130a0307070040d98072a0b2050014034005441041d00b00c2d04441d0440349 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 2429387 1250 2428137 2428157
    0xc040503070f0b0d0906090b040b060307050105090319030c050d050c06060105030402030c01031e060902030103020a240305090a020904080a0305010b191206150f0201050705070c05061605060c040503010e03090901030201 96
    0x89140505887c1d84000d14480580d010041841a240001350080380b048050384c82c09580e4100440f4507014103030700a40e0503000705a41a4180e0ba1820000c0344c010711a00b4003031a19042519202e0030302e02043d815a022850000e4162000d0000340001d40d408042428280d00310700323107900800d0342d411070380d00920705145d510000c114806600072a503070718016104000f401629111141807020350402e210403409030540e504045940d141803019042c025083c00120744505001d004218060400074090079090f001d01142e00000d0303241c0040d107a20490203880301c5641c0c0e006000000342120016440403102c41c1c82070104c3c0e41c000c5800e0100d007014103d1031070103441c0905d061400d50020007641d8022501c0e18402c01c80301c108180c00030303140740c0500d41c1900200301d990b80d0100300b60703814418001c0042205020304c40c01c0c0b00d585000c80c0600704090f03c0907922100c050a560f01c2510388442a0b8240b484014007082c100110700e424020010030f000d220014605103107074800440e11a13141030000a0500c00b81e455 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 2430637 1250 2429387 2429393
    0x50f04061e020307030603030306080a080906030c0f1308060907030210030c02031605070518010806071101020c060906090c03150a0b120102120103031205090a03050901090e0c040503070f0b0d09 85
    0xc1d401210720540c1811592030404000160051602d4030080340881e0400c0c40018940001060030701320682c200001ca0301e0140303017101b0400c40e0361005103601004803081c0500951506e086024028081c0c002d55803600040c00e0600742442c0a000811508440d07005901c07c1c4010307205c140070780d200b00885040204210342d508a05a040d409224138030600106911143c2081c01800505002155010b9401c01d201c030102100c110304444090182c80125844600417a1a25114980b90800da14203c000182880444580242440d500303941c1002564026014040035034014800d50400070b80c110b008000c0144440110402000010000c5800d41d507984c0080c2d1031500c030b00182a0345544210000c558425254020042106007030000b5800108400401548507825102d0349014100b01c00c001d020340d04070365500310750b00d5000f81c2d80c05040000d00709000961079181c801c1d06001b4001c10b89581d440c2c80c00c0005251070b225480e405a8014000c80c0c0d82003105200351811641000040c1c1c0000c50001e042d81 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 2431887 1250 2430637 2430671
    0xa0f05090f1201020304060c0c03090506030a0906020c160501020f0a020405060a080601030804080d0c0503030a05040213090303020306040f06060f110106150203030610090812030a060506030c070501060801050f0406 94
    0x1814194120b001d500841000100c190700941c40f4a00c1500100b00c83c120642040300c14103100680280803402d4890140168500200615886003420b0f4011500a05550710742c002c0e0f07041790400242d00d521420303a0327207043c0688010581c0541000e1004258016010059699030115000c019000795540d40114845440b03001c10328000e080390b001120b080b96524a46007110754810320072001d540c011a600c5e1000148903884e80c00305603401400650442d254000c4400040c500a402242d219040d4038080e03001c8401e42c040c07611498000d840c01a100e07c0c04509100c19503c0d001c0100d0f0410740741c10000d002458000c1c0b40344010b105546404400c004000d48424018540f90300581e685103440745000b84241e13070001c001c510808040d00c4412504046e0042641e020445004070841d0790445120181304803c200d01542d40058181c0c0c01051540d035401c00b1807501e901c156082294450000f42040074032900340500c000070310409002704080d290486e222074440c0300150004240c030780c031102e404140d2a50f103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 2433137 1250 2431887 2431909
    0x70b0901020f07150b06070507060801060512010605160203071409150918030904090605010501120606050d0207030210090609030915080403030f0e0706020303060109140a060509030a08040e15060a0f0509 89
    0x70307214035650751f00c5090180c2c0d030308030310720070400028061000440c0d85441017041e5103020925558140c5140d00300000ac0d07071543c000c01440000c41101e0b5402d1405a0740812640c00200b0107030394030601011580c01030041c2d03580010f10301c100445141c9a480526265200a15407100708042540300c81518000140d0940c402c102000d5846400c040d2000e092044503809141200c00980b25210603481d034481c40700079980c0030f00c603c0340484e00c10700c8102e43d094001d400803e080c900c41d2040d00c0c0301100c42c0040e82d0807500c1c01c0100303840171540d4660380000c16411401c0a4040e0800000d403420070064102d00500c0000010f2000b0105901d5282501d80d03a1901c0c1c000c0124101d1420541e450300d5241c4034000c1d942d4208603403030f60000c1d0303d031a40011824002802c040078030601420050b1514105a800d075020391040d2801038043c801c002404e0003003130300240644094000f40d803140d011820928024070b52054406140380c0300e000200000030900e508007685030b2107000c244c109280c48050480008942e2504 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 2434387 1250 2433137 2433139
    0x4020312030a05060a0e06010903021005090307080706020c010507050601060309060b06070b0708060a080a0206070f050f0303040c050a05091f080f010905010c03050405060a0f060909030203070b0901020f07150b 92
    0x1020061200d078480d00e4210f1807207442d099841440e19940c03402d60040c0c9078420799100c0d011a452040900241c01d000201d0f006e281407500348146400790040100e8074080207a03101c0925500607440901801e80d0500010f403160303209207405403c108080d1a4030b41c64000c1846040241692922500204445508031424840009049a84910681c1480c00741f1500807103600002811903000151107190403202c84040d40c0c1010300900425510794203102482d0700015098a01004031030380c80c4000b030802c0000c841c500425402861b181e040c907203041068031059401161055140c504184480d4889030401c40d0f011460940948404060300390700b90280d24240c01c44007130340c01400066000808150084402148110002c219015101c82c00704c08480e805d03035008055810003000700c0d4007030485402c0300c007070001c1c0b03400005506079481c03140c00104d071001070040340982c002242c00c01c2440806080310781d0102c1c40e00001e515140d5105c0c1158140e20030340c00028162000071000380310086040d0b101c4003400348 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 2435637 1250 2434387 2434423
    0x10902091c030309030e010503090304090e0f0d0c1203050106080a050a09060509010204030209060f0a0302060c01060e04030e010210060807050d0501020c07060c0c06030b060304020616020a030305040f0b0304051203040203 97
    0x101c80e0500901420501400358045807040040c0c2da010f5108004176031080703800d400518280743c1480e070114061303c1003000681443c482c80d4403a1008820900218402c207041e0b448e12882078403a0b24040c05525110b108a0342030518000042208a0308100841c0d40104c0700c050010701c65036070350302d203070024403022402800c0c051401e02000f0305808154014803e490089445141c155503486c2004041d0703815965482e00208596820001820309602400e400c078080b82c000f0810b075071520030034010302100300d074280c0018101085a0384196010f0000c0c6c03011000c0c2d10814081c2c241880f0312156240c51a1040d01d01030b03440035000b8030a22400b0340c10b5860015a1301d06032240303566604001803155110785015100007802081c0044d0081c0203200d004c01412004c0d252a045a5840e002c2009035040b0b44094000344807171605c07820040c0c0e901041200910312035150240c40b1810410000e121b8861500a990545403c00174840820000070361500314018004406540799101c0c80800c2c1041d010445c510f841007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 2436887 1250 2435637 2435689
    0x10e0103090206070b0411120f030d0207020a03050109030c03110102030f0403050906130f0f0501110a060f09080a0c0b01170a0204050403090b03010b0703140a0e04050403020f0d0309020307080a02060301090209 92
    0x440281f00181220901b2200e4242d00054448240d03100d0140e0b441d0360910350b20411401507130740c290317401502140d800106090201a40c0391034142c20355082a03011000614101d00003010140c00c2544292100c200000071030862401c6000303041484805071018041c003d003c00c180b21260307240021038043c05200400c2c085820340e26600070120b04480d00805080d11581c3e1800304071940300d0410020302c0090b035402080e06a1241d01d41d4001003445245c503e003e04c2d100c500c1c1202064404004000400c2d183d540c4021402403810551441c840c1a00045055000d44104540c02500082d28022040e01205c00207165192498144c0d8035920562028010030310100000607180040e5001e000094004d0b21035000c040224051000035100701e116180c0444c40d809002100c905003a80b0a991003403180c01100c03000300c105007015150002104d100b000280d221a070600450070180900c1c4010112000200740c0c1c08030541c0064028001402102c8810b07034040f403900b00581d01d004891810341606c1e44071419036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 2438137 1250 2436887 2436893
    0x4060e15120c030a1a0901020316050901020a0b1e0903040501230706050c040602010c0203090109060c0303060e0c090a090506010206040209130b160318020303040b0904020d2406020c010e0103090206070b04 90
    0x8101c6012402c0c00c0e81703807020008440060600850b44510844440225072031195101954550800d901d12811441414040b030005400c2c031441900441132041e59030520a0960840b600d8001c0c01007041405030401c0c0b008100c00e036084148202058a180144015a280050040c0303482c01002400b41015042c2010b00c0b032503102036001401900d00650090010032101e64080ea5a0b00c40c80b40a140000c10403031080001c4c510600c01e5181003071003890085030081c6d4940200c0040d403000c2d24040345003100012589600e14041c14a6030050036100d9041c8214507011001035181c0200401c0a40241c20000c00180380039102c5e00d280504940c031503e460080e05211011000c40411201e6030780c0401d00c1c043c81c110900303013540b03820301500d0f13402401146080d0900d5a942c505402503112141c02a800b4040030000300180c6c024480c0d010b5104035042c03c084107070350011510031103903400481917422540f07001d0007699024104085902d420b09010075040418404200640301d1400058034001c4007500348410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 2439387 1250 2438137 2438153
    0x8070309051309020108040f03050d0c0801060f0212030406020309030c120a0f080405060a0e070e0903190c0b150105040306020a020d08060102070806010312020708030a0305010504060e15120c030a 86
    0x340d4a054420a941c0141200c000b02220b0b410300300079021030003d40001d000500c00b031154001140c40780c50700754100120555103409a54617520b9100c00710781c42c80010301259a020307112541c0317121144010b00507242d0035122880e043c4006000606000c0d0000001000810300b00300300c510710b10780c070b0b01203403052060b06201008503040f04503940000785070007098003d124402c81002c0c3c020740d0010060915611a00c1a031001804480c82030140b50240ca84000307008442c000241c2d10074202c64002d980e46070025403500e070000326882083d1050200180359140460b8620031000e520072920360046540382039090040e41e01d401030360704c010001400002c3d128130241d4045022060003140c0e46900015458180c016a2a0016400307601c0e11544044010400705001d0b1028081020b01401540c0010b521024528110350200c00b80602203621100100103038107180c0301e10401416031000d950031a04203113014030140140d1903003143c454051303107070200c8a100044c4009510b010740201142c0d604a024130300080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 2440637 1250 2439387 2439389
    0x60504030b0f01050102060a0903020705040c050409050901020c10020706020d02040303030207020301050c0c0d080a06050a030b0106020601060c0c05060304020415120605150109150203090423090d08060103020d020708070309 98
    0x40003603211010030714008541d01d10b54140c804c1600945482c0d0345445009004100c0074030150210701c100a0006029140c3d486940f62070603c666610340d49500f40400c14050f0350014040d00ca440e84100041c8913100d01c0400c0142c5203c100b030b0405603031900700b401c044002e0301451804240e02440013038008101038066005202d418030030303002441540c1d60303a1003925050080344500030042d0010840455050b2107801e0241e849034402ea00042d000d511400030a4070100290400c03281492844018084580c040004600600040c5407206941c9003d9a0b40040c441c03251142c24090700e00030000c03504568071600100c0d05007013241080001076903904050003425003103030425a400e0b807070103001c1340c2c0d03c0e107100030441103240060b154842c155103405a101000340d00040c0c0070007180400c2c82103a1403961140908500f81111454507034401e8000c072003003102903501800301c031003da100000540c00d640e0001c0c40b0301d81c44002400d00507103c42d900105079001e0b02c1940310040185d44001140d1341010380200e400340c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 2441887 1250 2440637 2440643
    0x60e010f17101509030c0501030b0303040b040303111501050609090405011409160506030c0306060703050c0303090c010f080601090b030907030204020705030307020606120a02040504031b0b0609060105040612090c0503060106050403 101
    0x4030043c03080719000e03110841342d408040c2031034107400414031503540650000d1801420183c101c80c0b416544201c0f03039100b80c000c1c1d003003100095190343c895000024204000280140c10f00002030441d4506400520107214640b941c41c0510500380c006000d1001c29030068400c01c2c080340340440e680c5000d4161a40354020011901038440c221380300410641400801d0320312440d030110082c3e1840e100c40f01007000c41e0300003450840411004011002601c04140084c5002e4902ca000410850650340c001420120b0300d140c81e5001c0085000270030640380e9000020b041214030400950380d03a9283c42262a082207803c3c1c101a402c54000180301c0f0030030070b00100462160380e00d5030035154280c56410802c0301c0151070903d4846290321a840000242c5041c2c0e102c103421602c21300304254a0806e200c840b111880c0500f006031207480e04075040002c81e0402128003035100c0024038010b40352900f031200c0980b9100b405d04d4108c000039600c0742d41d08100054115960041c080c0102180c11942e580d8400414680c400d000c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 2443137 1250 2441887 2441909
    0x10e0c04110406020c040e01021903020903010f0209090609040309080706181203020312070903020904080a080601050c030a0c050703080403150b010c120e010306030b090a030216060e010f1710 84
    0xa10508070850040d58203030b404a40c0500b000045031001c0002a0210010360038555500700260102c0d400c500401e6040c4a10a0300c3c0981c8682c0035800b09405c54500181021109004100d844c10550f04c03900748075800102110314070410b840303d04040340d0000032508401d91501c15400041680c641000256110040b0b02e440c11401c036031130300c2c40c0d12a08584400c0c0240564414440e6101403458260240c1c0c3c400804d00e0201c00765503480c1c00040c00480180c4003658008030001e40a00199880a603203075200200782010f42c41c00000728109aa0b030b01c1401c5081e000c203c0202d40440402c00c00740042d0008540041c10140c660761a41820ba44224110300308924541c9016400d407155401000820301e11900083d160460241614040d02e20344442c9205604041d42e0304404000607a40c82e07401c500800100e4001d10911283e450064a03240c07081d0b0131066100b640f403d041109030b511504a040848081c60a01e00b0944031401c103aa0800c140200d48103000c0da00c0c000c202e40c407c500c4800c0d5007103403111104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 2444387 1250 2443137 2443151
    0xd020d05090a0201050319020c06100806090601030305030105040b0301060315020901020f070503030d0b04020904060605090102010c030203060d080a05070c030609120302030f1f0302040603080706052203120b03010e0c04 96
    0x101541c50712140701c0207001c80c4050000541c1e07c9066032083d041c05105580245c64284400360320790525408444020010740700c01000c3c008070a04001e502d500484802c01880b80e03505640780070b0268001449111f00c5580c82d03400c110190b803820342200d4002c44c0c1c45041c428034a1080c0c88040040e42150300b8944c01413080f14848264404002082011200302030081c41c03070180081e00d01009407480104007078211380c00300107d10b52511944100303001015141e550a84802c4903500080c00d407043c429080e070402d401403060200d07036642d00490030440c42d40320400c9a680d4003458002d03120b6002d042400f0b8442d48502c40c0000a001103a00100ca15074410b0761081042c032002c001c02e07012800155604c0350650070740c2d4009a0100b402400d004800041040064401503407980000e003950010340085a1560300032803240e080000b680213254002c00c09c4035122205608040500c03074030448009020b810458820500f403507800c5c00744d0100708007200250081c0448020340c0d40711981c1d00c41801420740034500c1c00d21 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 2445637 1250 2444387 2444401
    0x50604080414010906080a0203070c050312090105070903020a0504090201021509030903060a0203040b04110a090608030c07090e0a0602070303060504020304030e030c040e070b070c090204060207091a060a0302071401020d020d05 99
    0x9031001c1d1758058032944201c0c0c40f00b400b008000d410040008091183c410341140104000f0005070200d0006020f07001403074980f611170103003034560161000c0705024202d0010300041e035400780c0e0213095070f030700307440c00100310449000407031900640c00e1808035900c0c40902805028100800240031034903050f41220007948a1405800892000b00c2c0c000c1c08180f00b007008900020a03a0300c032a0404000148401012030715500c5d1041250226889810180d000088140c0b10340418032261000309200001000760858119203c0d444115000300142519800107003902010b0080d03200c08094100507008644a00d400e14001d01035090540d15a88644940c20300b421142c546401035641f002c90301d40c090300c0001d00d4210841c40741d40045108450a00c0680d00c0480c903c4030600c00740c402045154018040549004c00000481e080d40074034400041e82003140107880d849800807100398210b1441c1c0142e5a0b942c50600b0f10540990030550030980d4000940ca2100742c80c01d8000d41100c00110508110780c2d15002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 2446887 1250 2445637 2445647
    0x6080601050d0204090203010f020c031b0a0203060c0a020a081306021005040c0b160203030c01060e07030c140f090301061401030f05040f02090603031303080406030c0509010e0f010203040305060408041401 90
    0x4820a9805002c0a50358401420150071070010031b440600041103102e00c0c3d800c0a0245c2e00440030104140c0e10108181d902c41d80340308031070201d620b4640098032210f0718680100e038a4032402000c020759040c00051f070240040c404c104107950582c0040b426902c0c0c4016003940e111552807031142c00300600c90380f202c0154581e05440f41c58015980020240345452810b282007003182c0105000301c0302030441550010141e241480140b182010f11000015101d00f014898440b91501412034000c1615000d444031195420182d100940301500e81e4580d15035043d14107a07520351140020294040d400c1036000170314050a1440c1c01a03813002602c0500c003901030800500b08480080310082e0040b00d03142e0040c0050304002d002250080b2020b41079915041040240400d407000c958070440c2c81840c005001c003c0030703070706100c4d9030000442442e03e07518110b1500c0008120000018085204100042c000d0a55030300810854008640c00b1090303980d40d1810703040c9160030390000c2c496030400d54a4090390341504d42c419 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 2448137 1250 2446887 2446889
    0x703020c0c010e03010209040608030d05090a0302030a1b05010f0e0601080307031211070b0708010302010806040203010e040215130f0503010b01030e070608060f180403030f11091201060e041506080601 88
    0x500018a4080d4801c0300455494280e40c1185415541c20044e02d0429107641c06400050a1f0306001903131342d14030b044610b80031210f00608500b1103400c100c180c0702c0025804030844102e40320500d8130001040c01c0e01c400316048200c5c048028819803a0110111115115070442c20001c4190001c3d80c2c0c00782e0b41c030050a03480b07105200700200000d00740d09000c85011480c0d80076150001c16140710701d08060381d903a03850a4003001a00c00001060b1600300400031981e00c41c080d2030317010307400351400e60440d494540c0da000203240c007070802132040c02c0a5588a000c201c03207030141d62284600412240c1036550301c3e065440c003041140121400780d428040c4121180d40203008000702e841d00c010091503070a18041e8111078503480940150f5010810344c40d040485d65442244207064400350681c46102d0800d458054115452a40640034141c07c051400304560100d2040c0c03055100d081c4c584500d01c20301403482030300411060b00b0100030740002009120602404d0404078401010070b0b4002c010487d11a46080e0340c81d02c003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 2449387 1250 2448137 2448157
    0x60a05010b0903030a03110705030a02070e060a0b0301030206071104020d0b1306080606061b010203010303030b01030f0902060307050705070504050705030910060807030213140403030213050603091015030b07020a0308070302 98
    0x204210480d00302c0d1280d848501d00420482025060102310f0342d984c2c0c2581d00c4541c001005910000e002d20800701d01c1c2d4a02600460b0448415903214545000034207240014400a0700c2001d0204810061100c240c01a4a80c000c004204568442d41130741c1000c01442c0d0310403068000d4114500300201904540725800035a103881c1e000b0641a0707100c0c4100301d032981c40800d850942c5104000700070418002400554040c45c8661008500c082d014400101110200700000d10000c0c101b80f4400d001d40c131a881101c1d0456603d1a12a5845013141001031401016500041d009854030040141a503441400b41d40603041200035140d0003080d2050300025262940500a042c0d0821031003040140350412004024270b01301e643c0414407c0c810400021010021102540401c1e00050384642054501403800003800b4115100c60071800d007820481c2d030b07840e00c421911030096510f41701201d0201e030b28001d900040d9400307592440c0314600f10750000c1d00d80c0c60022045010600c0000800c00c01e0b1300a0007034613100c890b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 2450637 1250 2449387 2449393
    0x114040f020f01020a080301091413120f03020c06090a0501150f06080a0e0105070f02120f04030204020c0c03030403030302070303050106090305060402010f0e12010e0c0a050d0803060f0d0302060a05010b0903 91
    0x1299020031000304000b01c0c046065100307520a000c00540560007070b5000b0842d446001513911014003402014000007403210301c2280c0c60003d0540042c0700760341c42c9058001c403031800c0c030703501703505003a06078002c3c0b0580c1d401c031000348102c10406c140000d0004003066042d104030000e202840501c6400254200c050003a484844003104040c00034a1099040643c05140d100c0c000c5042020040f4560031240c081e2154000207a12a0740c00720042d404100e04041031406842c0c6a00e0440390303210f00395890007036000080c4126000a001c0d580c0303490401103101e00380780007410340740d545690340340243c001d6100f8002107020030306260000400a016000d107108a9801001070042a9640d40c0112121500e82c0e81107000d003c1e05e881c620f8a9a10f41c08a9a9034101c40400002a1303c6400d030160b9141c0310b00d0078100b80c42413490031070038840c50302c903078800340403283c1d0003c000c545940302c000c0003c100608100540c2d40000d06254a003040c5503000030418092010f480c0d0410450344c07100400b000302c1c81f40780d030000c4c0c140d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 2451887 1250 2450637 2450663
    0x3030a0305070512010303020606010908060118020c010209090c0a0801090b0609010309050709060605040602060a020405060405010c0501091a04150b1c030306050d06020705060c0c0d03020702010c020a17011404 92
    0x50007504810350240303141c07510901d0a4558005114000b1003a00140e00590000003000000c1d41c100403500081e08100004042542c9002515003400030032160100f040768003c900c1511401094054440003c0010a042e84906e00044880115000601c800d03000a1041000080d2034060b40700c2c00c00c201030082c0410f40740c20350480054001c1e101949040740d2520a0010004981c0014419600904500d0703581c540d41d0740c03030204024901400074040341990344c8104410811076460f00304031012120f080c01c09a0541800741000b80c0146041d5030082c1200c0903c1c0d2040190300d041d142e0003442148a201100130410410f843d800c11500f81c001e5454000001d0f500c100340b00c1008a144015a0784240303404544241c56901103500c00711450000c85400341c0106401007002402c1c005180e00c83e21403a034186c14100300c160b4807692108c80c44014003d255000031204d0030b592148220000164010701501e00c2c2969030300c11441074040701c14410040d946424040d82c03904031050066409282c00c024021949 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 2453137 1250 2451887 2451907
    0x705040b0f10020106062006010509060303040b03010e010303110c01021002090604030507080f070e090303010302010c030302090d030905030d05070201080402060d06030b04080d11030906041704080a0506090d0302090303 96
    0x3040c540c803445a004581c90503001c4580d560381d501a00e49980e550000c50403520f0b164010344611050341081c10305803413200d44003403059400130f0500d0444074100c2c0e0124007902d5010100c0d04501c603540296002010000010644042d0000c81504a81c802e507038044204822607030180c0ca41081110702030050300444510503c81826030043c101c507a90040c450b51030156070303a81d428504000da5100e03030b1498000503084111503205001a1005064403980004c8078030b40030196036220301c0140070080c140800720000b10103151299044e90034140015114072234007503642c00c0140c0741355400d10860b4800d2107400100004c491249007a100c20a9040e100c1400769140d036401c00030f00303402500c00c500000f9070720f8500102203401c048140d4001d5025016580d41c035054080c0007000d9650b1102d1050140000700203105030940005401c44e4002e030000745410480d04203042030000c40c49179501c50562881000040702c184800824074138007600d0204100c9510503003c1d070041d0140c5c01540303826035141d041441107010b5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 2454387 1250 2453137 2453141
    0x20a051c0206071103040503030a0e040e010b0a1503020409050103030e030d020f03042601060b07060c0203031302040c110303070f02010b100c030c060609020708030103020301050601080c0412020d050105040b090d0309020102070504 101
    0x4c9034100b0390382440d0300c0b0000b00703145801000d41d0f000001c0b28484040d0180c1000d102d184040120f0000a109681050001c191148000c2c13044a81c44c0c003052609548a0f4400e0f4151006040c008030248807550796800c00a0405040f421035a1107401811004031000e4000500034084180c0c000265003401d2403c808080d09000b080024401140c8840302c07401d06c59000c1c4103010140c05400c401c00d03110903180c1400c2049800d04400c1006560040007030188102456100b001000c0d8119004120340d0a6250304450304e1400701d580d14820b101c0070081c07010503500480b0081090145074000c00c0302035142d00410000b07040c440040030110784102c1102001ca4481e40c0341d01c1940340038010214040d070340e80304410700300e0340f1006d0181c0f8601310200051003145000c0c0101234001009181403000790401e034003030320010310961044907200361f4549800c10031522006400101140c103c0700070089881c00d410003650401d4110f4003c02d0070f000350180c0c0d048450080c801e076000c0e180c060f801050020304060500c40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 2455637 1250 2454387 2454407
    0x9010b070c0f060804030908010204060503010b0c1005010311010e01020c090412050c1207020112022a01140a06090605030303010803030415020706020d0608100e0303040210180303020a051c020607 86
    0x6150400c40300200702c4036482c640302001010540d4490403980b4050400070b080c0e210542040c0003603401080304208499001c0156410340d00304100244d42d0b4003010450920b0240380401052203181008000410310240b000d5060340c1d00320a0301e070140f42400403401240c64400d044410350740081070302c010a020680582d00c03400303540d030b1505140d031901d24810680380c6440c601d002c540001e01000a481c00841d64808000d00b0000300c01c80d001c0d800c208080801584c0300c110081200c01010903c061807050007000d401004519186062008090074200001400740025000c2d100c1d1180c10110000b505040010441b8101d0b08070001450550703e40d59200300021f0964074407000703095001c2c031442010070903d200801c0c1d082044400010307003529000901d4140141c00030005031403860825803a400d82404400c0713079407184c3d0403204e13200b01c291620b50030b6828241d1407807a074010069070071010040680000e1f80814103401182100e101c0c2e980c2c09101c8290921555540005800034004100c10302d0040d01c00036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 2456887 1250 2455637 2455643
    0x90c0b13050a1502011104050102060a0915020406030204090506060913150b0301090203090606010206090a15060317031905040809010804030c0204050c0405130209010504150c060f05040b0603060609010b07 90
    0x2903081075403400015000205a04528503048004120605450b02445001c50f00d0440010850816242c00d00113900c58000404d01c120150701d59191404204000100040725215000308540340c0740c8640c0020001e411034028810702d140790101040480c507244e01900c0740303020000c10304142c1c03d2010b80010b000e803036120340d416030582c021007012030440755040145001c0d082c51080181c0702d10300b02c03c0c0c6501d07149015200d54195004402800392522010400010361074000707500440c914241156140104400c0c0c2c0302410b00c0040b181001d072440003020046000f2900c84100c0110840c2800c0380d07100b16902038500030104201007107401415409915180d6005020b0b0030a484011002e4010030b05841080399081906a40010f051203503107010300c4080d64500100702c045041207040d000181c9a44100d006e40307480b01c1d01c0581c002c11070301e109241c01141c0d80d40c010410b05c100784001e2004005028299001c40c1d80403d1600001c180f420005450380c410400103281e4000c0c2d900c1c09804120701d611080c03044d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 2458137 1250 2456887 2456917
    0xb0c01060306060611010506040608030d020c1501030c0f08030a08160201020903120a030c02031303110a0b0703030605090c070b04020103020901030207051507110714060315030d080a0501050301090c0b 88
    0x1000c64120b2040c107005000a80305c286032284080e40003030844000501462141d03103045800c0c403402600205480005101100040ea00c070f0b00c051055142c105185515044668088004820018028010301c112060700340186a2285c07940002c0c1d0b103901601d1080000540400c0004416000036840003801e0030329400014503040395440440e0070120094012522414009281d041d002d901d88212054901f09201640c1400840b0008400c100ca9521010b8407101d18541d013441c40e651001841c030001c2c0f26865207203039034811928014000e000b07148200b034880d08100c00014000074040c0c0c00c0781c02459101012242d1991580d0040d0000c1d00460a40c1341090382c00c3c8002c00019070300300051380140800e140700606501d8245d0b0300402030001075014a00c0c0b078004c0b0b0001c10060014001840c0800720864040e902c070781c2e99207941e07410386048100c803d0707043c42807040020034260401c000c0350007034801ca1400e200720382e25a002d1500b82c0300403560050000d02c01040401407121140c016110b11500301c200c3d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 2459387 1250 2458137 2458139
    0x706090203010504030e0909010908090f041404050106030c0f05030c01080406150b030901050603030c0303070c11062101050102010b030c010309060902061207030b010309030801030f02010903050303090a020f0a0305070b0c0106 99
    0x1c00e00310380088a048000c01c10b0326100d42014a0143c40099000384e03003030002c2c0541d40c85980c40c4012402094030303a81c010a80f0743c3c00c004244d6116004005c40208400f40110245404e0500a0207042244426101000c4241000c5200c0c041446250283c850250043c10896900401102c1020300100705803581e590b5101200790303000c00c800c48070b0001c15007110800d4690030124046400c42e100500f5203032013903104011048110310040252544001507050104450200d41031141065000444103075000034000780100420890041107a00841020505200d980c0c031180168202d40000c2d00b510390581c00001100c01a43c801c0e0007000c08e0500c1490041040203a41d8003144030b941101483c0d241c416028010030090940c948240ba06030350007403809102d145155140944502010301024001d98207403076403a402d59000301c100c0320003140c0c080101c90341ca280c940d10080d16640400c6089100300002c050303d240d2842c10740341c8802500c2d0480d0150003c207107400c501502541c8a803039201c503295201c1170 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 2460637 1250 2459387 2459389
    0x301020406050703030b0402040608010506070311010507050c2401090218060a020303010e07050708070b090f0a12020f01060f050402070f06050106020303040204050a02031302011101020d060821030106020c0607060902 95
    0x50310041c000ca459041e10b4468924001c1e069070100e403170300c42c00366205010400240c0d601020710f90440e041034030010390320450707410700305d034604d1800c16104020342c00c03c0f051002490340310000f403641100010903079101110920010a006500307181c56803100b40020014014100c090f0300806810a0b10030303c02410602900200340d03150000050b01700540c02c00f100400030f4103c140c12030ad6022086260070307468147c4565401d007140c081c1141c090303d0625940005160040200242144800c840d8101d44801a19203006012040000000001030182c0c1c1d00e148001501400348100340e400c41da4207203151718105000d0100a41200d641135500341011034a0801107500c2d4401c85001e030107d640610750b00e2900c0e005220968802419a08003035104104102e009410070040c0d21140e40d0901e0b29106c03001c0c1d01e90000b40039005035a41c001d01146400b40c00584c5070790011b01205c41140ca0002c0e440010040303440c840c8240000d01c01d42c3c0240c0c1016200d02d00600d086001040280c0c8039401c0003401c08880e030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 2461887 1250 2460637 2460641
    0x10030b09010504030206060603101202010504031b0303120b010c110f060a0207080705011d010c02061905030103120801030507120203011b03050a06080601060e0108060301020702100507030305130b01060f0207050301 94
    0x40c440041a942d00c00070f12041c5641408450f520200c10b0381c0940c510309020084204c0541184100091040c440300382004582c80b41007100d00464201d02031b01c102d04410700e40000b0010480c8401c07400304000840d0205680b10034081c00305003280586800c490744065488094550080102480c1d00402c02c00301350f070305075032502d019200036595640180403460030001c011703141441c9900464180075948a680030102080d880c01c0500400a01e0201984a46403003c111a0b00580000342c0200040d2605034060325400005141203e00450300010900340315001680d0054003804040d002c0d40080405005001541c2030882d419480030b0000200300700c00b01c5003a066a0700524460340066100c7e001e009845510380680400340204030090101549081d40262031f00d41510000d40c140440440000d0003a0303029030555034002d401070041406030401510041041e4804802200400c2c42c10021688d001c03510a04009035951004810750781da42454402e070742298400c244c0d80214858104042542e48084c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 2463137 1250 2461887 2461891
    0xc0c01050403120c050906030126070902090406050904020607080304140102030703050105180108031e0403060603111206090604020f030a02040e03030a0e120d180c06090e090d020a02040510030b 85
    0xe5450034a44280f011910041d51070000030302c0c0030880c017404840200c0e07440808a90450348940d070402002c1468145100c00b28031103980d40d00303450048903400148a0b400360024031490344102c0b810420030f81c5541c20880980419034001e500710400348000400992950002c5400a01840b24541c2000103503c1580c05c1e81c0c02102c03000c00203600d5400400003400c001180d011a40143c4840d44117545c10001c1e0150750340101c2e03542c01f00c5003090101d03001c43c5000081c215005160052414004d6503140c4c10b02e1100c1d6034404542c5409880080c000760cd10745400714140e805000400701034562901c40390200443d60a10391155985030241010500060740d5078880c0083c40385824003d10744074a00031800100302e0758405a0b450203600030315440c08150142d80c3c00c903004804648800288085419040c00369501d001d007004052600002010449540150f100022201c2e040e161041c1c0d580d0b18801c1c1d9450b100d00d05031f59009a4003c8050303000516027030b084640e101c0300b2409410704855803500c0c0c1800020301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 2464387 1250 2463137 2463143
    0x1209050705040612030e041d01020408030c0d02030408030403060203070905030604060b010e06070302060f041b0602010219030207020607060b120706080402091003030903030c060f0204140301150612050c0c010504 93
    0x211100030001030405000d0100140069000c02d10f8075102034401a042c00c0d401031861f4813840e0740d82c11242c41d0744006005040e401030031400840d203c0b52100c0c8041c0d601e078810005805035205140c81c0310503040c400001c4030107030f44c0b2010245041c203141d40e0310400030307400c06030040c02030025040020489072020020984100d005010120344200000005400c0c10f825603001d9005080421008000c80d400003407041d006000054920070035036a6050107114610740904000b40283ca642002549503415006804001d10000320f5154140301003030f06030704910070b8010083d044003045c4200004070f6481e074003031401c0070405051405c0c1c0041e5200c85c02e00f13005054010101045d007001c01c2c001981090750b90340382d0100100071300d07040c40340c210349024100310303864840141088205c1150750108440c80e08160507030b04540e8015900c486e22031003404c181c010803481d1140250700c0c0c01d95900700180001078080803280542c55025010144801502c00ba01c001403c1d440d140710200410544140240310f0a4410380c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 2465637 1250 2464387 2464393
    0x3050403030b060408030702010c020d05031219090c060c020a08060c0d0b040203010503070315090203150f0906060108010504020a09030206030406050103020307060309120e030c09040503030106030608030403050d050703120905 99
    0x5058600601102c0c810400b00340180310500044c044c042d000411906244c2d02400d004060722124800910148503020000f8040e010100e9906245440918402c2c06070b101c0742003511a001d0742c01c6890044800315017015041c40c09140d010400c2500902c01d400c9001c1c00500910003c039210410a803502406603036501020ba800205003a0b035078a1072046004803c422141580765514040009590300c81501000d403001d10505c507034200914181e80070485030703a8054180c41c03070100c8605c069491541d04403000041704d10800c2c00540c0490010610130b100d0f81c03058644d12a9a400c0409100080d04900200c0c0e003030100040c40440940c1d9180080c600c5a449802c01244560540c03060504086540d48510700741401d1444060008440c89490010020346c0e20b4040c1c0c0303c8100000007441d01041c400919007110340203090105019000c8000d605a50240c2c0b030074002140d403030203515501c0c461072001806030340000043c848150710800007000c02c5800f80c40c14803640d01d035401103001100e245100491700341e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 2466887 1250 2465637 2465641
    0x403050c0106060306050d0305131502060f07080402100809070308040801050405070503030a090b0904091a040507080d05220803031302040f0902060706050402060409140406060f060c0314190305 85
    0x14109004807400f4104900d070901419241c440403ea5174194010004d040c001c0110313940031100403400b01400209210103488201c44c1c590107001c5d440f07540a03203072071000e00545030000d960702d03008510903401158040e01110312450307052421116014007401c0700129010300080003001c1032511029102500c1804000240c80c00d0a180c501d244c8002070f4031071400781c1c0051102c02021900892104212941061004c3d0b443d0840070000b0000c0407a41401001920040b00045903902c0c0140858840c52140b0121020152501d600c00d44d01e10718200484e00041c402c000313a01041d0828090042801c0700e02003c006219103c2034840d003503400848526074110b03200541d41c03040d8034060180e4140302400e00810040d412403a00811020b00c12000e0203484261200085021500c5560840d001084560010401424044a800000d4000f0b44003a074545085c01400f02d054580c07021448215203094071216500005503406036001e00f90001c0c0707040e252109101d011092141000c0e510308030001660001a18 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 2468137 1250 2466887 2466907
    0x140601060206010f0b0a0314010801020304060501080111042607031a01091503030c0201020c0a090b0f09060603060d050109020603070906030c0c03020c012106030f1505040503030103120215040305 86
    0x11000580c825021035221400400412101a01000c04e941841e0100c3c3d603144640c01082d00540245090880d13009800800007540501c1940558000c0d4030480c0c003400380e40d0341c8120850a03600070502c42101184104400c20118010706040107028080c0403101e40e40640704410715084c0030340c3d0b60003681d002d0855070784141440964906079014040341c1078100200a2480009411000d00303000041c02e01240310842d9007568001c0100c1440da150081c00540c2880d2500c1e81303030340039000c1d0201c003900801c1401d038100380d24944040401c0c4507031005404682540d80761020030501c4140610150340a5507584048030150310368000862140c0b890b903c030100803529081d001412a100042c00301e0420100c00c04182c002540231420341d0740c2c50403d2038540000c04000c4100b00c007414038600080507052511000000700a254040312060300c1c007520218485600c0d034011341068400448004080307030001c0005000080818480b03401d07400d8030388111038030800c10510f8080084003d44054001c15800700d000f80c89 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 2469387 1250 2468137 2468143
    0xc0105040201180e06010e0301020d0516020c0402042907060f1401080115030b07030f05040606060216060503041209030213060f0b0a12020901020c03070b03040303050f040f02040b0609040914 84
    0x8041c038680003100a607190004c018500300300545074604215000c50780d00c5c5103070350940541e044a4080314003088203003400c585071070009101004a40150040400420240c80c0a100744c070200d4000c0d402078440d4bc040c01c01030984200c05400300d4210300074140701080c007095081c800d496110310388200c00601300c040c208069010001c142e105918581c109100341d50555402c0701040100c9500c018080401d8130749900990140542d80148240145000200420b008103a000401102e0140e02035030702c00c1a554111801d544440d00420300410410004640020303030100e29080550703803525021600079220b40c00a0b0140c10395480101c4410307242c0c0c80038007100003260f0030b110052860020300d40c40d01c2220b00019154211800240c400d4990101d14822070341d00a00c80c06644c100003d0568900c1c540300d030340d0302c203054005980640c0001d1030900003a43c0900e0702c81e0340b10f021b940c00110380c40c0301050a07401c0001504540044d01e40261060204090b6500c503070040010041c414051000c0b0580c26100840c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 2470637 1250 2469387 2469407
    0x10603030e0405090c0d2904060c050a0518010201020403061409010606020601050f0909010603020a080607030e010603020d080304020a030209010b0a11060c2703070303050417010b01080610090302060c0105040201 93
    0x80b00368a0082407060034200003c01400c4004c0982c0c00b580701010a00b410380c004100c90b50701c00300c10f60410022500380342c50007020f244543d10501d03040020b41140c140482e0140203289541000c92030811404600064050500620440520001d4613040d101d5451a094030000014074903954980c10510100250038000d01c005411248000c010a6142400040200b020210721501542c081000b0a480610a40001c2c1c007031900600324446003691b50180c2607580c242140c8010029250861a80030000107000d813a0840e0b800400650401c411500c0d408407a07840500101d902c5000c000c030003c0140c6032490317118001d09213140c010f5118207141c540903018041c0644080c405400141c00c201c0050b00700b00640d080020004042c5032441c88050b810800600d56400b40d0703038188244000002055404030050082c0d44040d03901c0b0724940d6080326040c2c240e8880c1408107001c0b40345a0001046800c00045a09000d141440c0424030103a032038010402650043e6410310459440d0400c100555801c01c8042c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 2471887 1250 2470637 2470639
    0x100204060e0f031207021c0302030a020610030c030204051e0901020a020f010506060f070203030f0c010605150307020706030b030a021203030402010806010507080409050a0209120601060909140604020a02071502010603030e 97
    0x2d1a84103501e0020ba100c484006425001c40303000305e424015500c510070140084d180d402d410b41203195003410b0195a0782c02c00d107001c4005101c4e000000e099041c6591501c0100c80e0301448500c41c840c03e650030040039140092441441d68446001c032402c103070f10713060b003d401a0980c500040e6648500f00000741884040f03030030074070f8682c14401806040d4886c442116255403418502640315042031001a081d842080c4001c2c065090221b44000300781c406601c006c0448200701c40c204100da0041003006031a000484005026070016002000814081e8001186942c4000e0503036107078801d260700059480702c8160a00b1525440402003004550700403070000c2d0045400d00b0420b0400c2119a12403403507101da800348030760040d02c4201040600505405440b203140004000104400c001450550744050134807465001601c44c8030001043c410510891806046d02d5404842a80c0d80c10705110195006500305000c5102d101c0c00050761402d42065584100150381c00441c01130703d1801c006240b15803800240d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 2473137 1250 2471887 2471899
    0x10606020309010e0d03020304050604140901060801050d1202010e0706030516030204080307030e060d020f09010305010b1602040914070807060906020c1305070903050601060c06050c030708040206070f05100204060e 94
    0x2c0c0381981c0c1000342452144012950682003c5003850100d0550007294050b0740c101c00041008242d0640d0031020000101d01900d40d00d00c0381c0e130703910301c00c843c144003c3c490207810284021504010460000c1182c505840794000812070b0b09680922502e4040c0543c07010340000d6441d0300b0311980c5c2c0e21502101c0201c0c104c030300d010750400e400c209a0340d890b0300c100c10000f410b0103998000c80c1c92503181e0005a503c1c00410700c80c03c646035000703500d00c0f950952201c0c03070850020385417074004120395180c8021740e40c0905108400c40901200d55084c8001086550415542801d800d0f00c1c017444000c00300310041c0501441c4005e0010390b0b1030443d01400200c01038004009640100b0b44181c0240c44e10346121500e00032004c2c0c0860191181d072000c2d40c66032020303000603216014200c0003003050b0390806091404c05206040c01c01580d601c14450440900080e02c1110001708454041000341c40c050380a03181d17003801034084623010021a955a803a00b09016001c0d00b0749a0080340803c80903070030440601d1070b000140c810b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 2474387 1250 2473137 2473147
    0x1d090a03021f0f02030403030b0f010c200117070201061509060206040308070e04110c1209150a110f010b01090b0a0909051305010509010609150303050306040507120c0c02030106060203 81
    0xc007035215142c410007107a00d1001c040304001c0300506a00703d03036a1441c82140440d035070f00f001d050040107400643c42c403600450110010901c5948038038460b40d40103400c00000c030342111610f03110a540e0f1701c1649055042011b0300141e071004010b28150340d40a640c0c40e400014529203444902528040c14038804018003490020030800c064000c20b0703469105525240596540d555494190f40c801348000c4103681082c5480001030401844100a0104040d102c0846242c101c0b5440b80352481d1155520701078115885c1c401780051803d00b0302c080c0c81e400d51541819580041c6400e140ea14000710652680b81583d140e91400f08503580010302c0b01c000e080104002072808001d22000303400410940301c2e2034425039444000403403c43c50048205200c5522800900044c24000318907030285c0517a01425625a1400e429007080302016071722001180d078551191030569840e881084010000101090184503840e444000700503a1440b0704d1a4544d403540f10072824031850700615086442c1500a4010342d401003207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 2475637 1250 2474387 2474393
    0x60a05030a031b03141306021b0102030f07060212100501090b09030c1203090d060203010e1003020a15090506040303080901050705031003110303070501050702030403060b09040f0204020304020312041d090a 90
    0x3c442da42d001c02c04140c2050300245881c2c116420341c24051101c85d410400b15030311403000e502142c1d010440781c0740c3e4220384800800000104190f042c4a00080c0980e01c1000042903482c0b100300170742405406001c005042200003111044600c504580f804555807410200340955a04582004090038680104904008034000426078903d8820300c0c4a10503c41d10034141c1d1180750400840d0303000400503056a01c0080240b03007142c040d4100b030091300e12244591002541f0f2020014201040300d40050601f41598030f8520301090700398416016204102d101c3c030012599445050041c40154465594142d0601d0701d4240c060854601526103c1004010400d000c11122070a04110070b890300241c1504241c484900003d02e90322070300c50000c211754282010410419000301c09402140d000320414030400c3c1c0048200860b103903080354003c110081101740d03c009030605502039603006101600302c910b007201c0b220b01050243c02a41c048032515107000043d111001d4113809441e00304c030f082e8004102c1121a95 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 2476887 1250 2475637 2475647
    0x60b150a0f05030403120218040c11010608030304020904030815040207080307030f0b0a090e010e01050702060702060702030304051b0f04090b0604140103080702010c020a09050115030c020c010906030b01030204030b0f060a05030a03 101
    0x801e5505907517000701d05600c2c0c000b608c00403007443c000c00030810400e05102d80c0018007100901c0f10304043c0b07075182810015246401008403446982d0084c5441c0c0e40d81c3e02c5070b4083d240b101d00904520540601c02184031800d40b0341d07100815110b8020344003036460707240c00c404c0141940e40d141c5001008500b03200c030002e1180c682c2c607400c200f0340709a00f8000c0341000e0901e05240c014111015481e42640c205820700c002d9a4010a02a010390b04690a5a4042d910040d00781d0352071005550080080d40040d41d849080c611128500702c407008020105031801e4024070000c2c0a42c1c80d1030b0700595030110310a041c800c072484c05100c0c810035010620805401c03036146072610751040c0207400e000303030500541a8900045540304a03080c0c0c007070b01040c20200141e50319032410034a4000090444404280b1b403c0008030b070580000354400492030160755040c855400e0410441c0504500700e11181810b4007407102100040c010140240b09a00202080d103032440c007141040a11002c0340d005500a03000040c4280210b0340c41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 2478137 1250 2476887 2476907
    0x80109050c07240207080d060303030c020d050403020906120607080708070f0207050906040b060301080601051314191d01020d0c09030201050301060809070906031202010501060305010b0d0504060b150a0f05030403 93
    0x240c045080c3d040340c2c002110081c0c450304600405101c40019603064100b6107030f10032800d890007590200f003135500300441640e6910705907040030003007003013803000700700518110541c5640300d9800307000814a5812a60807500c0d000068840d02c010400b43c03401c1041030b075400399080d031740404076240407000841c03014000b948842082c01600d0007003000308000741d1140c42c2d5400c03d6218034805444a0340c0c03980e40c3c0010300d4551900780240c078854ac6103c0700743e1400d0741c902d0084200e9202e015400c201182c9a6404800f003110304201e541801d40c1c4c40d5030250b084400000300f000b0400100d800007607960409800b100080f154034011000910804e502e0034002350f6032041c140c81c190362142c03c1c6440c841c0c903015030745840c2480036446009440d05120011041214514440320004216002030000766282d21065082d40c4090294203ca05130500a0b0700342103040d50403554006010f40e000042d46126500440c41c2c54403007440f0342e00c401800141c141c08442e48244000d4900000385811411803e00e554000c11007010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 2479387 1250 2478137 2478173
    0xc0a0b030a1104060c03030f0203060f090a0b06180a09020403081608130b22030510090602070203060702060405060a0b010f05090102010213030c15020f030306010503040f0b0106080109050c07 84
    0x10200000701d1a2407264410640300700c81d8000c05803203965500000746082e50341c000480000c1d041c940d00c01d200c0441c5000703072400303000001c000b1074000b05039078103000108000411845080703407250a8480980c4514008048002c04a88017403241c00f100c2307080c824000c40950040080078030412081000c16100d2080e20151000108002e18070845400c0034242400781140c640750b06454042d0006161807aa002001b2521406144014241d11860600e0321180c05210280a540142070781015a440c0c1e5400321120f540b25480050610000390082854028200c59640c00f41c0d010800303000a0020400c1007540c4129074190503c610541440000c00c2200700741d11150500c07030301007248682c682c000e4068618403254100429001c507540d00301358040b030807584a0303011440c903c808040c16a03440031607003410f1141c405009600c0c50300c90000442e0968801401910201d028004010007d0034444015008142550310015254108006002190009819900d00c403004000030b0b0300040030759001c4440342030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 2480637 1250 2479387 2479409
    0xc05030304170c0304060206060f030102070210030c030e160503060c0307021209010306090515100201060303021906020c120705010b0f011205070306090903050c010605010201020f04120305070204090503070201020d020c0a 97
    0x20040440b00b1903018614a0300210301011502080b95980043e20034810f1400b228419216076404003032608074801da0001079000402e5101b45480f281c000d07041101c01c83c007039140005024945207900c03400c14403007890210446c115404200304a1900f0050142c0210680d01d0842c0385040c854000f9582d1016000c00000e0b011010170742c8040350380260711100c010049000309100a181082142828807581e1039018411100003000c010103a00c141300d403030107490703154004048000c00d0107034003000890454001c4441c0c0307400b040f00c2c49a40b401401224800380c001c0704915140d1001d443d0190a68581d510490b0007004814005000e44c0c0e0320014042c0c3c4c010b0311540001e20f5413259001240030700101e4001445060900b06c42004240d0300800401a0304802c400820849031208012030903807180b01c00401c00c0000c280720500501d4400785c428140c1b0340c405e080440c6842d00523030218098810406007540e4540002c141d940c29942c0500110000003003d1000d852801c08400015040a84a0040b500001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 2481887 1250 2480637 2480663
    0x306180506010507020405010305060714040b040506160204060e2a04030201030f06080610180b010507080c0304030611030103020f0108040305030c0a020705031002190503010303020a0b041e0809030705010c05030304 94
    0x10740503e045a14080e000b800600ca41e60b10f82c00e156541c1c2409591547c0054010889a9105540001514103070307003141c07118501e0185002e0801550b07030080040701110320006000000141c0d26440303108024410f80c07511000e1440e0807003110410010401000c1e21040d13000c1e0014508854070000c0310300396542400d0000700b20039494580c40050106810000140c4941400d00110a5010007004100c3d0784464460800800405c4800d0554000040300340c0402c90030300503000000c0b1090090403480e4400011a0b050a59907194542910006414201054030010041c800d6080081c1824160380003800c000040b41015507004140d07200080045540000100e4481c6085c1d1007405080010030006045801000f00e410743c100095000c824801d44501000b55442c0449018405032812260103030042c01344c015080d11150b800280c01441140c031200166003044070079500b203c00304602e900401c856502d501c55001418a000c400350059814001e1900e44c0301d001940000481c0d07030107680315000c00008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 2483137 1250 2481887 2481889
    0x7140405070302090307030809100509030604030c03020a0507090506040e0303040506010605030c071a0f01060c08070803040c090906060905100e0103020f06090d030203130b0a051207020c04060807050f010306180506 94
    0xf8044c078070380c45a060041e04000018822400c020b0845034008a844541d803042100040e07074180b00740d030550360b0503410000c000b602203400b0b001c501c0300700c6020340183c0f00c8251895880606040c6d058124407507481c0e0350b000b0301220781050301c20b4103920001d9100961940c10035864480d40c80c8e0781440b5920030054008001005214480d040c2c9a000380d02200003008008100b0b2009420141240c2c0140c00d80549400006d4040c425810740c0902c036004185070386040210344480d801940001c206643d101d100c62030002e81600b492043d40c038000c2c000c1000282e1030342050110000d0b03884c0541080e003400040d92040c0030128406d10710604507a4111440e000800506003c0780d160f00403112025440501c9003000300070300d5000b00041041c2402069203102413611005100101d008a14a07407000600501504000040486000c0d402c28424012205090301010014041d1001a08007850940100034200143d0a2070903400403510000d080038020982403010910750319100000404a9648900104903a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 2484387 1250 2483137 2483141
    0x6020709092f0a030b0402040b090609040f020103060e090307020a0f05060901031d070b030f0601030c050f0a0c020307080102070308010503060c0702100306030b01120b070807122d1d071404050703 86
    0x18803074043c01203403460341d4038100202990300c1210264020303070801c2e101074018640006824803c1d100180303128487d490356186e00d060038032a110700300c1c14190758400101e103a60f41052014800c091400041d0390b01e492a10500105d0003007640034a40c000d146100070b00080e5184410341d90141000c0c03034002030704146242d020400500d105079030042c0c0c2c05058400b2801c6401007008511a1400000b4103501d07441d480011411503800076040340005205200c1d81000580900042c8065505860007610400560300068249440b550180700140e40c006400001c16810a07a070600504085018090920304243c48074114400e8040007807141c000380c0100c0a03514001d52050002d146c10408030301c119030f116942101580498171007624001071174400070f03440d075126420242c41a44641d50f00768000e040b01c2d03408030141680036500d07211a020403c03a9490880c541c25040d0305812418030103c2c111501d07400c000160b25511320680003a40140307205001d02046140d0b880e09800c01030f200000c0c565075028003200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 2485637 1250 2484387 2484473
    0x1409010203040306020a0e030706050c030904020c0c040c020105070e0a080a020111100207030207050f03011802040c02030c010e0105010e06010801030b04030f0c1a060301050705040302030a0b04030c020901030c0602070909 97
    0x2004c1840405e07403071115070384040d80d000c11b64003d40c2160f40164a402090310240200035004285610400c8207452901307041c1c01405070401c021003152800b600c6100043d00f600c3e1401007050040c2e55640400c400c03d03902140c2e0a113150300981e8123500040c20000c01c1c2d42c4a031104907020f414096400704d40444007404102c06404c1d034004a0b0119140c0186150082d11002c3c18450180b0444001e14000d43c03030304d010700c61554007115402d0aa120200c1513400c3c00b001d000158400740039800144903030401d200007806004600e01e4000c00004280d8181031951040707a5020f03110a0401c40c1240040c000100022400b54000d81c040c14107030307580000801d040712449040d074001007450050961504012080b0b0032040e0248500700d009012982d13407036074102c1d0310340034a1001940c0755129070890030125003100c40e00c1341c0090085c5001144040c2c0c80d004980703112021b078004c650182440342d0420400b54103210600c007500541700140b204c1181602d071104007407034a01395150711120300706a020b0b001c1d884a1000c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 2486887 1250 2485637 2485643
    0x10306270302030705010f110304030f0207050402040906080609010501060203030a05040204090804080a12020105131502070209040b010806010b07020105070b060a05090106090501031505010f050f09090c03150a030314090102030403 101
    0x30280310301e8029240c4d0000541141c540d130800c40d022800740d003a4091500c00741e201008107030a5079159201120f100506040903010750060f0100070616440754001000980400840407942e940790101440c035050f0010510740c0d0603490400180059640803080780d40006903c1c40116007a111230000800400600000a12184000074009907640c0042901405e80d400795503142005840c403c41a42a120226840b4961482c4411507400050005400c4040d05640841c0142045120b03404609540c1e000d8078180c480e9852100108802c001c2046914003400382c05036405d0401107643d0000c1c129000344407005203401c031108005409600c2c0c12080301c00a0400910b2009a541d503100040c4c0614a14000c40f0b0010307050454000603000b001e107480c0100d52040e910206805040c0d0021521034201051032944180d007004821134030b80d2104100750041500440c199aa4208644d200c0e0101d901c0864080c09080840300400100380c100e60b0000d1a800c076540816030340c0c208040100c1c15407080750001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 2488137 1250 2486887 2486951
    0xb090a05061003090c050d030905030604080c190308010902070f020d060203070201060b0403020901060305071101020a0206070e04090b040809040b030304030606050f010804120c02010c0803090105071b0308010306 93
    0x22102a84a40240380504010b603035140c10300c241100c048059415003400609074007600c070720402031402c080c444ca02c0e00354041c0c13600a1a85455100180c1801410740301550441c1e8003107003290081c1820702107001c0c100d404902d1040080742a50b00a03140c104148241c84107240c0c00f0425806101a154240503101c0d0b000f1f025202030a02864490b000350001d40d605c00041d86026030200d6411420022a000c2d2600148402e5050b0320f0500204c1c0903040007428042040001c100c207403078070002400506272a08164010b05200c0c5040c80d8010080c400c000e02d6a403049080c5020703d008200c007107240035001500309035165078030420040400c0161004000654052200060001c10312486510000555004a40b942c0740040180011600700000796405030410360420182e1101d1402642c4c249010780c410304002c2d000514585410341250401c03200300615944440420070201d41c0708010078202100c407155003d249000c0e0b20300a1030380e0414000100350590350402d400303245080c48120005164002c00c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 2489387 1250 2488137 2488141
    0x60905010f050f0109060b1801090308070b0106020c04020f1e1605010614010305071215090203070f020705060a1d060c0304030305180405011401050901030608030c0304050a0902030403080402010c060b09 89
    0xc160000e04080740c43c090504440c00003c0b4200000c4c0c01817008403528894400e00b000003001034041883c0c1640307c4c071030500643c0c4900100090f8090080e00c4411301076000100c8a42c034010001c0d0810101c00c1c034003440b49204100300900d0310395807403d85247c01341d81c0d0b0010700d144003880500f42c014800d808034000043d00081d29001008030540014065601203130fa40f0954842090040d804e0b00c9040d2001c0c03000c15800100541d02c4580e59200440041d69078240c7c025003540d82c4440f80891b482500d00c0340c0001d1094003c04501e540400501d0000e04040e02c00320b04d0a13080c020014010389000004840c41d0f00b201c802c171855135542c0019601200709180a030303584d603036403460701030003e07408045c01141d40920342d006415213182c2482010304a41c0a5020b210061082d0342c01110076522031190706040c5036407201c0115021100300060250120003200640e0390740e040c00d00300070f0341c800c00d40c2c40100300900400030800083c0d880680c05401660a0a1502e5070b2490703840c0041c094041403400642203401d00003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 2490637 1250 2489387 2489411
    0xb0603010b070302070503120702100207030204050f040b0714040b0c0703060204060306180209060409050619030c1a070507090504020105040909060204060801050f01020d080606040e040f0311060f04030c06090501 93
    0x1000b0a4030a202e9001c51309802e40e01c03c141501c0d8040011011821071042c030030350300581042e59182d03109010702e10540b80180e40740c0d400101110029140d60118400030000c000420103512140c6411800038101900e41d40001c194080c0e032403140c0d000d420f40494000c1034075841000200480000303550322030800c0d51901d0310b41c0d00040050106116140340201c80780c102aa01486a00c00c0700c00700ea00240041d445c1504140000f0301400c0d0141c41e01d074000740c20109600c0000d141802003c05103118031009880103207410001c101c07201c43e941010303005a404100c1400012800078070903040344c001020100d8156100c0c00140c60f00e0103264000d4108074200101c8000f041078a900a2054401c5600d90700c8003a62200f081c00b0302c0450f401041805a405203100341002d90080c9401036101c000109943d24041d2240034110100d41c090701d0440b503c80c051070548041682028110030b443c2e9605c0024a21868040bc00462003003001e40040d0038171041c0e03208001448419003113450010341050081c4600c1e0f003164 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 2491887 1250 2490637 2490659
    0x6080f060a05070504080d0509010e090f06040614010912030c020a03030807021c0503060904020402130f081002090918030d0203090a060b0103020c10050c04050a0b0d0501140d0303020703030b060301 87
    0x80c1c1d801030803454a0b0010300d56070b0261095509031008200103101c051020001543c80b68401c131381e02410700a01003802da1b21991469201c511500100d907035820a801c01900344026510300f50025030903000ca01804009590303000f4800000c0b00d038a49001c0c0d4400c0e071103050684520b9030a900194110841d00c4001c801d00d50001e020038040c11640d42110b1500c410b07551400d040b0805411040b0005000b0070100b140d601d0400b0080d90003c2c00104010b140088040700421083c90540c0b0808018601d40d4027009a80380903c40101c0d80d080c4181d00398600440a00082c00343c450041050a900071f405a1480c4843d500300706880160b00c038814119520709140d500240d64901e0301c1811640c1504200f410003d9512a0080c1e03801c40314894010302034810540d0154000d4400100034801e450803d01000485960314800c281c028242e0028860f92182c440559500b40c40781600042004501e516542d500f80c1c4413490840bc01540501d00107890300020315080b4080c080003070707171180c1c0014040008501c90a44e6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 2493137 1250 2491887 2491891
    0xd02040e030a090e0601090302010c0602091f031a0a0e040803040807080a090509161b0203030c070b040518010303020a030c0203160b03060a080c060d021303050a0303090b01090e060412020106080f06 87
    0x40c1c44131010640e07420b001150340d080f8500001380003480c245122800101c85030040e20007044018a82030380046e602172045a034240a01c11400080c0c0c41d04000c0203c003820a843d44e4a104013900e4002165040c01030f0318001103005000280180800800681800b4011050321081507100740e0071551050842c3c0d00811506007405198840c00d12a80800d6035030342581d02c00c03509d41840c2e45540a041081408081c3d84c106401010ba8143c0030400122103550b00a0010002801d4509030054541e400c00341803000301c40b0f4843c20a0054001318005001182c0c0000d401c841956061402041c008058400309003040310020818071b01e510003210102e0030020304000703180306610580318590403e50f00e550b02990f420303000d0107a5030044401c00220f1860200c0f88c0040c00c009403900b0100182c0d654039640c1c0752824107280c8041c0c000943c2d500c120007c01515a035094014000c44074180306a0300e02c0d04045484100c081c1000341840440704000344c440b03000790003040c020400307801582d18811041d501c450303c946003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 2494387 1250 2493137 2493149
    0x60203010305010f05010602030c0604110310020c060f01061103070204050604020c011404020f01020304031709030109081306090b030105011b05070f060c02040b0306101203090504090f02010305010e060f0d02040e030a09 96
    0x801c800411f280f0b10000640e030050a400000f008c2d917440316150740d4010300c5014100d82d0580101500114001842d0004110241440c8006c01e01840c00344a0000501da068000c40108644c920348141c90480c0041900c2140b901143d0000c0c15848000018000340300714201d0039900d5007451031000705010006a000c0c4118004e0ba58036800c014200c0c012a00da224501000b044020800c03180c1c200c1c1025034001c0d041426028000260850050b2a00c0ca9503400a14040d00d04a5240c0814070803d6130011007840140408003084c0d045504110003e003907008a83d00300d002002c107150400051000c00c02c0824000e00400f40441c10700341d00c804000b02048405441640510b0400c000d07000c1d1401d00141c0c4500c5581010700e00107a182c14030702100c4e40f4501c81041901000a203c070f000c05e569480c0d00c10400082d02c0b550a60000b0b000300e00c00034068030b90507400300ca80c00d2601001c0040c2030300c034017000090307503201116600d042031694400200144201c0d0011083c40c400820300324810350b0040d01810a45030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 2495637 1250 2494387 2494391
    0x70902090d21120b1005030405030904060806010807060f120509010b0406080705120d0203090d1a0c0a110105010602060109090c031208010302130204080c040504050a0210050a090905040503070305090a03060203010305010f 97
    0x151550f010648000c1340e40541c02c608140340345842c29103e10091500300c3d103d0300c02ea071f2804100703800090903105103400020711500400010002d02004000c035500900c054144900b103035049035000740c101b48455500c0c0e11520b403581c001402100c1d0079445151754180081c020090f0341d032560803169903803456000702c078000c40407050f00189845001a0461410b1140d900442c030b08195902400500402281c088682540d40e03080e04802c120041603040c85812400d4159403644249480102015007200741c00842e40d1403d0014003c0c1039000c03d0503070548140b4a8041400c0703409240071048021190320260990b5400c4100c1c29041d54000500340c12680204c0c0c3c00000402158a000704034421840740c41d4107130344480058003203424603030015030b80640180280c60342c100080c0c0106603000340705c0c2101030014800103800d510850b0086901c1c0c02610aa80c410000703480e10303554a40e9a4810760a0142c05e1190114020780d080d61049480000303180d100c0015501c0e13507543d180040c06403600c1c01030a100c2c68 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 2496887 1250 2495637 2495657
    0xc031209010306060914010c020a0b07030503070807050c070b0a050c060a020705010b10080402040902041803020a0605010602010c0806040911120307020102060a050c070609081e03060405060307030302070902090d21 94
    0x910480d0f2060a03502c000039035a400c01c200400646030306c000448c0403a084004003078001100c00c441005022800d01031303181e0503078070701e040c0000a003007131401041035040c028180640c1c039403030344001100e17400d0342d4082c412596100c070118802c0d1850f0058100b0030174903104440030000c8868560b006051702d544508024070011062000f000041030502348ca070400a01c10000040151409401102e281400070344001040703a04400c0c0c61031b5504011405402580c02041c4180030840144100c40c01030045200070400101420001810790704c001d043c140c440c50702d8658800511102174108900500010404100240341040d015203a130000c80f07090307002d400b49100207220794250b0301070a071080c40c1c040401850100741c3d0b5944001031401d034400740c9880728140301081440c00302e0311031560544810380c40c1c55200e1520f00e040100380c410040c41da0703010340c210003000c2001a400040d15001c1c0d4140101c003585800300c01012400e0544000005401124004100c1c4141d080382011303509100401e82c1c1f0f0017249 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 2498137 1250 2496887 2496899
    0x603030c02030f030304080a08190204090c08060301020c03090103020913050f0702010606020d0c03030c02010b03060a0f0e010605060a050c0114070302040602060604060f1502010207080403110a060f0c02090403020c031209010306 100
    0x1740000c803806400c2440400800412911460600b6442112498115038080480c003481089030082c0d0406810a079450901c46005600400072543c000002c03070080d4580b40c10b1096840d2280205150503040c0354001c90b52003065914210b00940307464000000700800c2c41c1440d0320700c5101209565440140d4600080400c03d140b000c02d001d00a1005511417081d0610b10307a030214010001c007000d000440d540d803420118241d40c00d01246005503203180f80070400c00c4011881900315030403d501c20741c0c181c1c9402e404005544608007620b100001c281000c50300d600310000c030fa0740940802280c0c0b0300d102d44030100700324800e84c15502400c02c1d04c040303500720b840940c0d40c0d80c188011900d05000b06a81c0420340c0e0030402c01985c0012042c10b0000c224030015040c400256542841500690001c84040140040c11203450a010241c40000c11152400e20303000c014605001c1c01d8405100400b80c09a8203110026003454006c0125040359100503080b107410014128400056070441c21406000038100b080c00100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 2499387 1250 2498137 2498143
    0x3020909070305120d150602031902070503060103020108090a0b010306091104050709090e151005041104030803040803060f03061302031b060322020d05030403060605060403050c0d11040603030c02030f 88
    0x55a0b4000000d01a00900c1c0d0800d4000e600901800d00c00c103510740b0702401c2d00b9841b04000500034a12a001151522a003107901d035690491984003004540c010b0340c082105940008207181165022700349458580c580981540c28106945405170110900320000404c1041d1070b80204001405007180e80207458001d002c00c01910810380d0368000044602c070b000e20010559500444288202004985070205c141c04d2a5850100c01c0316106665184407104001508145c020000d00c038041c5242c907868242144c0d0703007009a0201800107080d1000101c0020400d403108603080f1050b442c014100c509031302e0f2942c450b0940c616803a20881c024041c0350326840503040150804420701400804050660b5110b0380000e40545580105224007844180030a0240c1c0342c17140c85400460240000d59900c0342581085000e46510b6400103014410820003040481d00c00301d0800411030089a1103403d284807030a180701c004e41c202d40440da01030310b4198000200b503040310442c04094402d805484500000f5240ba6031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 2500637 1250 2499387 2499389
    0x403090f05090601080a051008070329010b07140309040f020c1e0d0804020411040605030708010b090604030807020102010902060d09020310090506010e0c1309020309010506030705060d0f02041703040302090907 92
    0x40482c8000c404100810040d070002c42d403004180c0070404130072750385643d602c0c54000c2651007036840f0360150300c0c040884c441307480c0840d244000b881a1041c482d454008005010710641c000900002c00b0921380181000052040303031480c0000a0040c405030380b01800c0c0c100298004400c055271441003100c0c00c4111000d54a0340701c00910300001400c01c1c40c0700ca01c81079400c110002c1080381d00542d5030002140190821300588090002696119141c0c68021400b9001300d41c181c000c45000354007403265003500d40e00c02e0216029039505c42071064a483c02840140d0150440010007540440082414549400d01d680b2041210340200e0444520400010b5031400b15010120042c0113500082c005002690b8034812958000000d82c007039601d0503040500f50684072010381c000c07800064000050100346102400360f0758100100320054510b0324a0f04000960b07e00c1000c0e0307907201c034a0301c3d50183c40c0403800c3c42c0c1c1901d00400d40002d45489051007501e0b0341d600c80e0720600040b442810301d0800b00e040130340c00040f242c3c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 2501887 1250 2500637 2500639
    0x1020f06060108130507030506010e1f05060a03020c0c030109051c0306050906100207080d030207030e0906090103150204090e0303060306010b0322020d0204020a02070e01051002060c0c0106050303030403090f050906 94
    0x5039440e01e5464038080a5134003d242600c81e407081140c0000001c0c0c0800005000b042c0882090030941441c1c4446035603010584109940d40c555000140450f5a4a078100e4403580e2081c02c00580d103e0030440e501d4145880307410f445516510f8450020148000480c6a1216070b000089581d6443d00782c840a80440c3c0b0301d4000c058010340c00c0f90004d005d034145650041d80904590040300c1d00302c0e0703690300714900e005e03070311034071003000a8000c285c00d0201600556050080d581c112a6071209217060380200d0802e020500c400b60040d000c040c3c10359514401503040700d010b860850018050300d0725a01c0465a07a500a540650003885510000600d0151200c03d81e4024004a04013001c0c06031240e089800c0036994880070381e0300014442c41480181d40f14402070040e0313041600940041460704064819a10059000c0341c044c010344020405c6565010a0f8285d0018034107084603103407030400260900400c469003160f60940301c00814402855040180b090440e40d1000d4159441074a440600010b000c0c256411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 2503137 1250 2501887 2501897
    0x3030109091110050d0513050303072a03090305060106030e070909030509060412050105060405071704050a120503010801050108010204060804030c02040b09010603090203060906040c0302060a12020301060e01020f060601 96
    0x60100048680140d02041e0091403a04011480000001c0712100901c0f0b843c0e0100d8400152070000c06014003031160301c03c848500b4081c0c10722542e1500ba4a91000034a1030341004640884c2c90f8910742c4843d0ba00541c03807550500800200c03001c2c03601401030100740c0016141031060302d000183c0c1c14820b000310000301d030684004c3c0007550720307000401d4007510440c54100c00744072051180c58000d49403c5c2c041c0000b004c54140004643c4014100390b400c646000d0805130103a8281810000190b4002c10b16418000c0c800c01000320503603a0f0f05125051440c03d0b04020b21082d8020302c0700444c241d00401841c103071402c40008114590380c0d144501e080344141d1107507400bc6803a020018000c40c0c05800c0d1101030a001038800b18020b902c210000f5a0031400340c02560200c2c1d9920792001c10360604000c002e80c091352031402044a4245911380001d80180b510009100b00c0c8000b4000090380d1140344904060351070380c0d200395125616400e0180c1940c204200c004d0042c0301c1e91022880c032040000e0b200d80512010307128 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 2504387 1250 2503137 2503139
    0x1060203040b0d020903030a030b0405130c0b070303060e0a0203011d01050109090f02090d050106090c0914040b060714060601140a090b0c0102040b040305070303090b030408030606070f0b041202010509010e030301 93
    0x3400c00b0740d80064020703045260b8248640380c1c05803801d00080100e40c03e29034000440540a104010403214040e054a20003110b18a8a60015030000f9480d4182d400190010361620002d2a044001d400a500680307070308440807061100c801c1e0990040e40c10303108291400c0384028800306202e45d854009120b09800aa01c0010805c80340ba1540c2c809000d07008011009403403c3c040101251110a54036411a01070f95030381410429620140718a0350240402d03e0141c1c801403401d00400c550a14901e0403511455540d0140100d568a03801103a260680c440201604e04410144060b00e0310b80448010f40460307400c65408034056594022141c100800d5143c00c0d13505410034480c10100d400c04081c9121075982044046401e44465026000a51182e002483c080e41180703030007405100c85900032078a02c00240305010000e00700000ba00e60098041d00e01c07645072030701401d0611030500391100140c2200140024031092000e4140220044031150700240182d4907200316503800c0318002d2008084981080c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 2505637 1250 2504387 2504399
    0x80405100504061b080103030e060f1207030902090405030d050c03040203030a11030c0102070503030105040c02030c120a03061502030d0506100906080402060706020a0c030306060905090403050306030a060608010b0310050106020304 101
    0x40002d4105000e40c0d4000b6050b50060075400f40c801e1008150b5010410440c01002050b80c41316814242c158203640c01030a001607000c50420500408030003400784045c450000712454481c0e844452055002400c0d204c42e8105400d240740c0700e030310003103140100f50b0420f00080c43d549042c1084a003d16800740046181100c000c40c12242c890101182c4086400300708019141c41200b4005480524080c001455880d4942002c220032940c071001070505542090084440d00c2c1d0303020840b581c2d06d120b03000d403055462803481c0e0210007c12003a00008520480541c0c400c4411f580007000d0410210440410841034a5680030404010b03107000300040002c0c2d4520003032001e288103a85050700240301902060a10b1b800350b98079000da03040fa001b9100041c10306803030003050581c1802140700a00e014184a10b11a0801e80400e0b16010300800144c1402400070100351070340c404000c00200607400400030401d0035101c1100038080d081440e0941d210f80709141c075030400e000c0c003481023504840c520340065180c646005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 2506887 1250 2505637 2505641
    0x305010902040b0403020d05070806090304080c0f03030a05030a020403060612020405060103090b06040b060d050106030903020d08040b06010c0f0b0103051b0a050a0302120a05060103210813020105090a080106030f1208040510 98
    0x1c07080b08c1d24050810300180d841c1d401c00019009000b810091a10350307091120241c030b0021800d41c800d200740d2100c02c8444407601c0c08400c48107071008505d029a80d9585400340c1e0741c0607101d245d000904d440d02d03001c80000c041960700c81450030188200c60074001e603201e000045050703813103650300908803040510206007030b45000d6001e07030051200a019141440c031090116000c46000364000b10101ea21034201c4401c240c0d0504c00d1000604850030450b1240c02c182e190f0350301d0201c00070140c03418051518060802d00c580301888a204d1a4046040c02440d0303104c0c40d03d07a0f143c2c000743d5600b04644014001104e6140303001049030098030340140400480900c1c640810080016443e0781c00e45502485101401041042c0714060203540145c5801041d0b030a510030380c07541003003110740950812409034144000802031141040f103082e0246070a90b02c41510400040b0030710721940c0880b86641c40d03c10000100076442e808031070803901139081e80b0001829880251442002250b000704550450508004407052035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 2508137 1250 2506887 2506909
    0x120305060d0602030103050307020102010c0813030f050403020909010c081602030f030402060702090c0306010f0503072708031b0c0102160b07061404050307051b011b1502070807030305010902040b040302 89
    0x1c0c0041c503034001c50b03100c1c5402c0340d000ba08140e500d40c20010302002556024003805a00006500d0002110b18101d540d15040e0380c1ca00b0401810440250b500f40c1c029441002a100950b80080528910742800d031040c600a100d90030341c01c00803945000000e0140302d80d40c0d90f02480210a6005140380010f20403022049502c0108101da0200042c441d0f100540c4640c80e0702442103408050660f502e00f0b10000141031304040f40204810007100b0410882401d5000201401076005085400305a060f018424055400300b50454407541c40003041c24182e41142800f0800203007201d1007074603040c42c9a10f004a848000c5c0680c4149401480f03070040200e50f10103801130918a0240074000740c81c0c41c01305010021420203803000d42d0584c0c00850348506000c0f0a200e8844a450840950080c04095000181800c110802e11104039840c1c41a4a0141b191401c04e4090741100e14030115a50201031a1259150300081d0054001900d031030b0000c40c440e801c42c82143c0c103585030350021500702855a1708005991482d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 2509387 1250 2508137 2508139
    0x3050310080d020a03030b040204030809060d09080307020a0c08010c051c090c0608010e1303020d050702030a17030103031206050a03060b0112050f180c090402040c110307050102041502060412030506 87
    0x10340c550001d0450002e001840e1031000ca607000d401030300210b040007001d0304d0b04405030f94880e40c810481000000c0107441101e003084410b54403280c8542a0b14945401801c4e441d0001d01680303c0001008806603010505a4405120340c0d0401101034898070114201c900d454510404948100160300300801d42d402441282160144089507149085c0d880c00c0c00b580c103540c03110020422a60042c40307500c1a1011542c0e011441001d080300340c600c40e4800030341ea0800c0f1070640c000d0000c00170794041952024020f504029030081c1900484001000407911554424441a0006108074804a603040e0703440c06548103c4600030106443c0d2411500c0342e6008000340302005041c0102e0030201d00e0452642c0c010b02c1e2140400c0d202c40140c81c82d28210f00c043c0f4a0075145108095000528607602698820203001e0f08190151000140e880030034030261541c4071800c050400601c000302d5400201310b0150000c005035203850000c40d05a4800103020f90f5940070544009010000c0c400555221512a80c445517010340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 2510637 1250 2509387 2509411
    0xe01050408030a0e0f0709050106080106020109030206070e0105040e1e060a0305071a04180605040f02040602030d020309030c0609010c020d080f0604050406020f0a1211040f0b0304080d050a0203060102070819030503 94
    0xc0222040c602d082161f07881a40002d0300c4000410600342c00a480600514180c0024861b40b80c0f1b9a8000b511010300a04210500111002c494081d034840c0b010355000d030120100803401402c0c07001da003000e4040344860317031806000500006886802c1c070300004011a54440028401caa0801c00200c20806003070352081c001d030509000025181c543c0e00400404001003440001d900707420902840159242686860400e500411003000603d6002003101c80146400a0060b00c1e9107030343c150b540c01c512440c07079601424032a08040c011080070644c07101c613901d41260202d8040803200402074442c448100c17010b412000380c0c4400150035041075040319a010340b0840c0014500081c0c100c0052243d04a104048001030003442d180c0c100c0c0d640382c490f006031284c007202c116086c0352600824554a81c4c00f1301a11460b080c01101150400c5604800d1b030311440c03038908090010303142501c10303040250005c94003680180f06440340000c6281020510401400920383e02c0707124140180c80c2542c041c1c3c009440399031445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 2511887 1250 2510637 2510653
    0x20d060c030f050a0c020601050301060f0e060303130803120a060605030a020702030a0b090a0309140303070206070c0503030324010305010303020c0103091103070603050f0c030709030609030c14010606030e01050408030a0e 97
    0x120691041c3d070b110703030070700030000032000308040c0002c6c41c00304140c0215000741e1400c1c009010f400844040d03d4100c607641007441d0707959a28040440d0550246400c901c84529224002040d101408006806100e02c01c3c00c00c0c00840d501ca401c4c1000b922741510a46010400030404134030480d0654000301171a0340042c0407150300d07034481d03031f11840c13041411540b042c0c81c2d80002d00c4080425034000c907014000c03d207641d098031146c400680002c0e2244520b0000902c41c0c000000c40b4070802ca544004030006010040c150b80d241e28040703507801403c60f584402c201c55581446640141c039030091190300d050365015030007400b84208010064008201003602518081c214482c03c03003450b9010810311010b4141942e01050780c1c1402001c000c104800a4448590b000040c0200408143e00010f91005c0b2604403002180c0440313581000c4d01c0340c09038020060803040c03180741c00001c0e4100c150003003c1119625502080f825090241391400c854040d11300400710103042012803418040c030342001608180741802d8403404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 2513137 1250 2511887 2511911
    0x6090d05060405030901020d03020403020906100c0c0b190201020309060609060604080106090906060501141204080c010203100302030c03030403020f0d02040e0307110a0501050f0316050408030c0f060106030207020d060c03 97
    0x40072181100c1603800025140b0407543d050148100c02889801e040d800c00b40ce50340043e415100c000c0c0160b01514040f174103110b1031803250b005418480e4020304070307a800baa01c680288241d90700c02c007005030b0352001900d4851a1a441442220f1280d20f81401801898031210200a04c2141c050907042c1d0042c0c05100100c5e02100a1155000070a0000b80000e0601e6051074128281c4003141c0c0a14140a081c40c884500c43d801d42007200c28035508004108000d035940d00d02175409004910102510390302c08410030135070520000c107800c2540d0084046402602454082541e2445140002900b00c0c5460b608821103082c14110400001e00c0244041610400e14000900d03540042070191250034094554400e1814482c004001405082ca0001e150020601f201502444060b07c49243d1190200c4520f0440d0710803001e890183c002281540c2e1342e290385c00c4050b41e582c0700345c5c44100384500480c4000580503001e07108603800d280d40600744104440e03050311a00c00808840407440181034440e03100c4510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 2514387 1250 2513137 2513143
    0x102030d0606120509070605040303050306010302070f050303060a09050108070308090324150303031506090301140709030c050607020102120c01060b03010b0406020d02060928050102070308010806101406090d05 92
    0x14155560f40d000106000c000d501d0f040d1000680b200129801c1841c050156603030080c1100c0540340c060401e81da8989400b80101c000b4880c45e540601001710b03d6860a040110200081d400740000b100c58240b29504d894854044540038031514060f68031100c800c0002480b1400030b05800500103094030f00f18403071207880007000c2200140c102400550401081122035600310a005500000d90082d07042d80f600c3c2c2c01c805014000c0f1926107110340000310704942c095509410400402103000b4034a0400c0c2440803000d080135500340422180003001000c08241824084150381159030164001c1146800045141400f60700c20340050b0301c1035484600c00314806800702d0007140208809051543d50b1407510308000d040040403502c2074110341060090100582c40000e00e02c50201c0d040d607980c02d035409080529078032007481c204020803950020540405041d08410900d0407240c803001990550754450310301c200800130758010b07486030f40c5002020740128100880544001c18003c0c1031141b03000000d0311083d107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 2515637 1250 2514387 2514389
    0x60c02010302070b09030304050706020105040803010303140c010c050307090608040209010306050405100216020a0503030a0c0b070e0d05060106080105010206070c03050a2105070f03060308090907180603090b060109080c0108060102030d06 104
    0x2c446d0310000c1400104202042440000c08562000304403500380f560310029a48810307c005130070003d0b43c11108008818000889604c0c5080303400800003944c0b40e64014007150405c0740c0c82d40c041354000c20b000800c5405080c480e442203a00401007280c5038215561800200f0000d13106071490700c10f9491081080c1c0051004200c0b80248691902c0e40b00100c0c810044c0b00310543d0800360180c1c00138081c0240c5075421202e049611580540054001d507118001207455403424400207900440d01318540062001c081881416a6690303511000c46a0300c1d0001685e60319004d407402000603030a074012402203031040015210000007440c021410001d10198405c00b2118481c274001401d0b030314002c0c0034640e03400041c43c4214225605092000a1558484030910700134a080140144944400100360074410a003107449800080070303811a10b921000007c0c000c01915408880d19142800810b80b550b0040020318125261040101081d01074003004603105e402c0078003014150b02c002e102c20b41c0840c1d1035003d880 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 2516887 1250 2515637 2515651
    0x309120309030d1b02041d1006051c0b04030c0f080309030a090801050c040915050d050304080c04022511060a121b080f07050903010603120f0f09060c02010302070b 72
    0x9611128060308042c1803c40d04003094003440124040f80340d020305095a882083e680445001440c540596004500141643c031400c04501416031145140c3c0c001e07a00c45e4007683c40669502003a804640c03072900c1c00c900784903000f51035949010006000640f04020f0f101d1050310482040750701420994525056400c1594540000d0f080403844030706c019444144007006280140c02030006041c031030031130a035510640c0500d441b090f45400349080404842401840106030140070500080d90318280503403a50030501400d00f060003403401152083c6824020f40b0b0780040c400c4040c02c1c820090302d9200c1c164468030361080311000b40d106641d803c0e0f60f8802014001541c0b66031904c44000c0002c00e00300d0b0480d0003808080c440c4100308100390b545250f10184195110b102d2495245242c2c40e285000d95442c0114640980d0640c00c00314080100203021036041f2046070f10b91110402c8031804041680c0d841514420140007500b2081c00704003842c400c001c05e03400300d8010b060042c5482007035140c00c4402c1d08200c1d510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 2517993 1106 2516887 2516893
    0x60105012016090605090a02040b0d050601120c020f010b01140307030c02190c03020f01050910030b220b0306010f030308071202040801020309070509060411070605040302030912 78
    0x89410401c0c00e0700e904035407540c3c41c46508041c1c0f545004041c02042000b020800781290350013070b0b03015034038034500031402c096800c0700040c01008010009030402400040d888410b4010344149240124254003800550f006240b0031429946a65240c03410401c507842407018a0041005803500001c207854042441da250381d10492a100b21401c83c413010b04800c6500304200f0000055003822039100391150080442c11078010b6981d4080c5401b01604641c202000711072040c0700381d1040500c0c510040130310240054a64610036408082250001a00e940e03820b811610700e420408076005180038881001e0544c01c580c2c005159103809400c020038004495010300d501c0ba07150701660050500c0078021501c0c1d203001c40c0c1e00b60b40c940c0c440c400c05001c2c115142c085280c90501e400b80580315100e0321126441d03d0035596400e802410000e1003501140000c0c45641401d9440b444030203803003610340c1c000b = true := by decide +kernel

theorem cover : BRFrame.Cov 2338137 2517993 := by
  have h0 := BRFrame.cov_init 2338137
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2338137 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 2338137 ≤ n) (h2 : n < 2517993) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
