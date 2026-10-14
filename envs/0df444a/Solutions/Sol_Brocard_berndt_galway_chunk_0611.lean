-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0611
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:43:46.075203+00:00
-- url     : https://prove2.me/submissions/6210e053-092c-4ed9-9fc5-a1e1ccc03398

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 109712230 ≤ n < 109892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 109713480 1250 109712230 109712243
    0x7030206060a0e0702030f090607120801050f09130f02010c0b04030f0f0806031c020a15241d06150c070819020a09050c07140606040605010302030f180f0a 68
    0x10324101c820b2002c0640580d00c410300d040c104105002c81d00b50007008450940c441c9400041d910000d290200c2c1d410311030002c0041980503040303a0700740681d40c0140c4581c10b0701c4040b58030044141d40324007086a00c94040d500200c80c0200c04861400040f1003c1d507406a11748103040500710b502503034076222111030301201c06401043d098041000b442e5841400854460741b68245481d150520001207660780f0407050300c1c0c07040a000d2542c0721241314000c00800c080c0a1340035020600c00003200c0906d4001d824503042c50000c1c82051020030415a080480810684084410040405190000700100b0b500d0180003030340c1001181c2d1181249040500c02401c40b520484000c004080c0351100403403512494407103080038450b00300f5000c0d0050b5102e030307604400ca0342c181e1800f081e07546a14281c0310351807141920040c1201c0d1003440c620602540811500c2c03103003c0449042017a19510b20056059100031a0100f11030400c400004030181e44041413001c1400c003907403c0b1415010400b07107141c034028004d5802c0d142c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 109714730 1250 109713480 109713493
    0x705030411040204140d080408070b04050a140d03030f020f07081b010b150c0118050a0302010b0d0c120c0314011a1804260a0302030f100b030601110f0102070302 71
    0xa0000125080d895001c1c191811440e1501c0c0613070344001d1580030b41c0b469225110015105051210090503074002c0c0c40c400b000c0c0c40c40d1a0743c4402c00d11080c0e110784551405583d100100146000d4568000003c03920b0103400c050900500f6035086009054a410285403540d0a200482084a0034406401034501c20805180c2e110350400c00f03005185050705014003079a052a509105584603504012440343d007449480343c0310442c4d0f00c801e602405107126480521904860034009105c40011103100e07143c041c0d002000f20681c1340007408200203804034090099400d801007040a01044e1070003107510303802002080401c0da200e40d200028042c0c43c582a104076912000c222045454401951905101c00c40741811203440741e0301c50850320903008002510300034600c02d8101d8a40004500030000c3ca00c91400642d03128021800039000750002c0d6800080000c0307540c000f800408246460000703507980c0940580c290f0b583c44004455207030f60164001441c0c01140505400501e09001030044280700341c005e03280 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 109715980 1250 109714730 109714733
    0x7030320061902070312050c1c051005010e01170a02030a0b0306061804021206090601060f0e0f04020a0203040306020f07050d0f090e060f031c0e040c050f03070e0907050304 76
    0x380311a440c006000640002050015600c2c00441c0c010761060311410141c1c481c0707140e00341982e00c1300914280d240c00c181000c041082c41204c0300000c1c09107040020b1172100c100411441032040312800c944050300d11030090021301a035070049003070951080c01454440710004106006803008881a105405526000703c140a07403c0301074000d541501c84c09400801d114545580000c620501c185503400320842190089420f5440d0070255040003400c5204a43c40b07810301c05282d0303586181c01d01c40c60001030710030401045654490508250301250050080e602c0000407010800290300c000a44829440100000400941140044c1810070280d4080540341c4100341815820040c7c0e0312000d20070000d8034101c2c100500d42100b03000051343c0318800c102c80d842d0380b002c0c04176901c482100100c50345803180c42c1410643d4441201600c07030240d01940d038114070303416a109000589862a4910300845d41c180305c0b2012840e05a005940e00040a14001e0a034411500c0440c0b50120305595120000304000100b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 109717230 1250 109715980 109716017
    0x40b0c0c040c020115050402030c0403080a05121602061602010612050106090b0f0d0809010c02090c0d20040e101d0f060d080d0515031006170303040506011701020c070303 75
    0x10b0302400b076800288200400b8410f1103040344080c0c0200da1149a010000c038400c400d801003944c0107580e010f803605540f01850b810260076504110021101c1158500004446100c12012402c502803642c0052510b6240c2c0c42034810f1041100900c036086650380d40c0001450960a4051181c80340900f0002405504281c1c290040e101030030303034803030181e0903202210b14540c541c1c0740003112442d002810182c07a188000012a000c010018020754010705d000e0910111451203001000c61030031220040241c00c503000d154516200340d00040c51050710043c082000340b2980b1640c401d52009001564403240c9456003410141e49103e03051446104000004002400a101c12075580041c0308541d80201495140d440b809280b280810010200742c451000ca508005070380c9509214100040540315000040500440244014800c00b8004015507a168101e42d60100840e406141c00c00d0103401c00d42e0170700d445010805403c05020040c0c0d98200140300d450070b024001d51010b54425aa0401980c40145c00f00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 109718480 1250 109717230 109717241
    0x3180b1513110421050a0c091505031c03060b040609031a0103120c0f0b09060601120902090a0e0307060603030f030c02151506070204050f0f090d020c060f040b0c0c04 73
    0x20349031441d00e07000c5031258854005075011280707440c60302041c800c0002c0880c41d884c001c2110081c128800c0c1400ba4042280b0180d516041e25820301c020410403d694144d200300080a20030310750103412002103110115295488950000401d042c04141a136940c0c1540080d5070195101400050a580044c000c10400103032201200900c02a41266541591540d0317021100e030004110038098404001030030402600103484009810410315a070070700d8054980b9884000c03c442190008005030304100c3e1000721807040701650b6401408400e01c0d9641d00b03050b10000c00c140810000381f071205121800000b6500e0040c135010f18402d90310360310b0000d40354a02809236125080644291340007510244200b50041ca83c3d03e41c0502e0700c0e01056040c640c0c90700424124030030080040c0d041420320080001c3c4901c1d03101101d01450601c0c056400a54030140c001c0e0f250a00c1484100040c3c0055401c2c01ca2494031802a1a05101e101c2003180b510b90f41e444240055405240c15900e640c0003004c040c06c00c1d01d03051081 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 109719730 1250 109718480 109718509
    0x310080a08030601120608010c020703060605030a0b04060c050708030a0b0405070503090a060c030e07080a0b01050d0804090f0b0d0b09070603050115180801060816050a05060a03180b15 81
    0x81210350915980c6110030702005000c0c41c100542c60729103420441144e046907004140030402000081c2019400a4079140b0743d000c190380450414074009801e040006500582c590490310a00541c1c555070381c1c1f1005070090300b1002c020000b0510122000c2030700040254052800700c4400982d41c02c07000184815101c0003041f0300244541402080b403114004244500d9595005500151090400c0411b500501003100e05454520500c0c4000c21148400680c0d0f06180340151004041a80d9500420250700900c070030080046070140420002d800d032a8103e11104481410040340fa0301c4000d0208403154841c200584490380d444051014080c41440008050071b110b1405008a41c1400d05007040b600250180c402008803c41380790001c1d641e8210030a0191600e14020b0100a0303480c60340a541c2c1c121260109030401c10100002100d203071a030a52011140040c11842c24015400d1090f0010036900201240c2c110395000d1003800500f00e0031040b0300c51041901100242c2c06010144040f20302407800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 109720980 1250 109719730 109719733
    0x30c060f091203041509170d06030510020a0504030201081b181c2d06090c0f09140109020304061b020706021218211209040c0804021e0a0b030903031008 67
    0x50202045c0041c500d80c4203e5040301010542c02500d21b0511341c04034003461107070b0002801203000402040d0a0300f119041328000c6049030f1200442001c043e08070711542e181e59000c51800c000800040d401140300035400344401c4510000c181350080c0041a03580f02e0800c501481d05044041c070b946d89850a0549400c00004000c0412000c241c0e0715446003002c09012410145001e44460f201c040c8681c17030080c011f40d40064280a0143d45246c014041c180301d02410b9801a40c4d880081501943c9203c2c0035102000d80391214126460141324034000c2d1300c058000d0310015192240030318480c5907d49919517008095000b4610680340080c001d05003032841032a031403428410030803207000c1d00e801d41490000d140b0450768807040301ca02052808a0b420408024000390081c010803554581600c0007605804606075400c1c0300550300541e00725021039040b10001d5104400c0707201200300d10b841c0140310035a050003500c1d13106031641b0f403080411a604100ca0b406003a5100000300103500750515518401040440c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 109722230 1250 109720980 109720987
    0x20307030906030c170c0705030d050a05010816060807030b04020a0903020109231e0d0506060f0108010602150c1b030301050f090103020d030509010306030204060315110f07020103020903030c060f0912 88
    0x71307001051820380310350440e004c14018021480006956040f26440c581c450100c83e44ca211080034000601011a562101c42e80303000000501e0b8640413038440c032801e494005000515003484000e4a007504007034004d0080541e40d6642c0d22040c0c98901c010032508400d6151504c9103441c2d4800140100d80030307000540e04c022001840e0304803409284012900c0b08007100e148a400900180214210044c811401e5000c0070b9046580d0501c00040ba03524068074065421003d601e48010041d944290284547d20050703000301c5d04244640c2d8044103540c0c00c9444010050b1801800303000c54086500c200c01c41d0040c41d00700000402c580d2070500c54120420310140c0b50b4510561464000450004441101600344180002d0780da00caa8845e80c0228040c580c0200b04024003500c0f0304201d5500c05607000000703c5149400c0d141c4605c5044141035a020042800700a4908096a401180a504403071600c5406100c107006009540109206180c4a803401178140c115515000440c20319010100320012441a000c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 109723480 1250 109722230 109722251
    0x4060e01110903070e0c0d060b0d060b13050904050a020402031006020c0d021c030c05100507080a2007170a050c0d09080709090f020d0303020a03230103021005130602030703090603 79
    0x31a105007202c480003585c000c00d5440d5040a14284107044401d0541840e00901040011803000034120b01090b0060801034a912010302c84e54510400e1102c0d962499000800c21007460403124555000b03106030705543c29500a030f4042410b82c0c0042e07035030071501d855080040c00b00641c10410740003c00c07405c0b102c089000c2c4042e004038184104010000ea811113200c0750b10300c20705000d010f0045202d64090112240c0b00c5084244800800f002d0b60780400150004000c035100303c429000d1100c10603402c40002c0041c0103881c044000076030114a003100c1080d80e40c040003442061800107040c02422035201c00e0395801c08100101e00f403044e100c1040c001e02511520501c00300100142d140261100e151001410014904258405002802009500001e5440c40d03004040d8113401030401c44204e07860900c50350840d501c002600da20030954041c0c40440060041015140411141c0c0e0030f4085800d145250508416002001c1030381c540002026174000580030341050350000d03110b80100918070b010441034014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 109724730 1250 109723480 109723483
    0xd060e0f010e191101201c08061005030603010906021603020d09032109080109060617010b010c0b060d0221060c030105030a121107030b010801050901020702220605060304060e01110903 81
    0x205001609407114001c0c4c41c429640284900c941500c0300c00154040c00712008140c1d591130101d200000398001510141809140c02080c010b401204014420b1203210111003049a0f240c000030200c0341d156403a18403030300105002d88010503901c02803601050802c101414068a08443d102080f8100a41500d0400210b140d54450215800074906c8000521200d50310884000c0a150490552035213082c560030708010f42680038a0446407900d040ca061020b070031001908941203107850a0105210320408000191400c41641c2d100c1d100901c002c107078038419008501c200b40002c1c00ca280384041c4a104c109818000c20616901c1044c01c00c0300c134515810300001c40d45403589410024030008501c3c8104102c00c6c020076984c80c03d09010300841d41c8041d90390a02045440080c810f0642075442c013008540c0107181030003100d03450740d00a400304180b42c0b2078180c4011458850003810f00c0080d6078800208099407040000d40c0240d0144501003051f01c0300c40b420034210340b0088641c0d40062010480038005840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 109725980 1250 109724730 109724773
    0x21605070302121f05091e0309040e1c031104030b010608010e0c180105030a0e162d0303120e01050103120e030a02010906050705031917090d05070209060d060e0f010e 73
    0x70f0024041205c0e11b07204540c0d4a400c0c0c1c0d2011010280090700302840d0f5108002018080c2003104580610025101c08103050301c075030381036401000cc11000c41c407070021180290030a000a10145290070f1802e0758035100c100100d2000e8000d04002008540100400500300861a410410180115180c08840703243c20031138547c4494030a041c0100400080c82c04038003640800c074608250760550b585021491001102e0803c030b40101d920900012107195840708542d14020b01d81d184401030b4003880b505546081e580c03084c000c040200801d480e0500007203007100178010107000354413441c4040d680e140f1951000d40340400205159019034440d80011001d40c1e444169081220102e003815681c43c140d03030916038114400d802940b021036120800f169080c0d075000c0d01c0c480307e4480a02140110791101900641c441d1480c01229002410910070708008d4542000240c1d00b0110003404c1d1420000303d540d4600907a402c408109100303801040c0c1b004020030081c000c1e14040003a18001c0e18038142181c0b5103200810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 109727230 1250 109725980 109726033
    0x4151103030f0603010f06090519020f160c03150f060909240204080f06092802040216020d06060f15051c0e0304090207150c050a1202160507030212 65
    0x140b400856401d4070298040302040c41521070034051292500e42c200081c05c0c0646008544c000105021030001c187c44c802c0e6080c2071501c01d022894041c0e01300d198804d1040600c0160f8280d54824400000640125a0a0300d8071002c90400321701144828504022034106500066450741040340060004003094004017a1042d0380900345210010062031100a0050750002e200c244244000c0c03c4106900054031031041c13031040121551801c0f070841304d0f001791481c5c040a00a811000c0d440c50010318260300a050400d501060100300601d517600054030301e21102c60b042e900160703142014800101144003090240a101600c10408440f035800202948120310b8814901c0031142c0500088a5040e0850036000005e101181c0c0c8480d110103a544c000d52021804541c0207048451401140c80c01d4091100381d4044bc0d180c0b14184051854152051421141000100c0d9800c000456080d003d0100e401c81d8240658020809a400c40c818042c80c180340d40383c0103a141e404042c2003c0003070008010154802c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 109728480 1250 109727230 109727251
    0x50610080a09030302040b04121103030403030c08161703061906020c0904081207120c020c0907230307020a020a0504060e04021509061818061e0112020f0415110303 72
    0x82c40505044001780602d402603440c440c40018001171005a0041301002d007802806104403000c0320400305680c2c1d05c00c600c00140810a080c0c001d00101d807880e4043c2900d40c00484455204000c26039480400d080800005650001d0100501030305040294189201e10341c512900040c40c0e08055019559100c0346004a124030400400202000861402c2d1809d4000303501c1e8a01290800d50300140c1300b00c802d40f881001709850424102d1b000c0d48001010300c107686014150b81d60300e844030300085820407922905074100d007000c400f00e004030103400702c01140b050b0b9456001e0000341500e44100804440e165100c24490350034000f05001d910007001200303802907030407200300c04110307083c16805071903000c0c40440550243c0003060040e9140811818114140011656080801307600c184521800d902510201c0d045480061034010401e40c03129038007541201410030005100044075078500341e1340301d403c1c1d8925102001c00c04020750030381e60700c840da0184010f00b8600013021807203000f41d640c0d020051094000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 109729730 1250 109728480 109728491
    0x618031902010b061815190c030c0b1f080102190f090803030f041106120a0b120604060e161202040f0605040219140a09090e0c100e04050610080a 64
    0x19000f503005044124001d0b20b0f440d00c455081d910341883c00c41c0c405145024030030488030b901030849881d0890b0b1000451600c915002c0009240450310160315030801c400b8400108200c001041c5042e03001d0b0b108802022944012400410040c0400700003070b8403154040c0c5c0140320700507100c00c2c40704200888094924090110040000c411601400307107600115890000200303100c03c400030005030610841c01000c2c18a0611400024043c1d24455200c0140312031031208042480068140c11030031030444024051201941000c081c0d0782050f4007690101d0b0020b41d649a42c03941118288490158020310031007040b105441e040800c3e00c141110300c2c009100d19641c0024507500c2e00305d58000b1010f0f1030040c00c1151581c2e0441246003841781c4114031600421b804101c90b8542d402880c04442c00580c160f0b54918145103031a0164004d030003408050b0801c0d026080baa68810f44404440d5001c010845d650920047d49003018403044440107040350b4020010341000c0810301c0e41045c01c4c16040345060000280 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 109730980 1250 109729730 109729777
    0xb0304020103022a01060f050607030e041b0e0f0a03020a090203040c0909030e040b030d050d09170319050105010806100503100f080102040501030f0501151409030304090608061803 79
    0x2449016000030032005407105140f50502007005940a64041130002c11038540c985010f00d00031040c1d445041d40c848401c103c118000b070f1107038040c031343c0c034001c06031000c00d210b00c01d810920b40c1c10a88200101c00640c00b08080d64181c03130300302000d16199406a908201d210f0868022912540750b42c002d0840d040e0700000410108101c12020100a00540360104500241031074010120801c03c006a8800c07810300c0301075a094a00800c9980442d84580c440516014510140e42d0107030041c100152400f1009840d604c0c20340420f90001c0d442080342c074560b40020641000d1250440f00c068204034100003c0d0020411a62600e03003d0100303406031818819200d0740c03525800112403026401590b103e10708094001a6188150003a1054400980b814003001c3c40700310010080364424890000028500346540000f24042d40102c0b00318101c8420b050700c0c0c0100480440d00d0742d1710981c000c1030496928041044024002d111040d080015803180201100c2c1c20058640e0b64003d07041c2803200c148505c0080c05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 109732230 1250 109730980 109730987
    0x108070b07031211030a050f0105010e0d02010e03070b030103140f0607080919061a0916050c032b0e03070209010e0711060a06050901080a03080c070c030f0b04060c0302070209010b03040201 83
    0x11408542c460040c0030344c030b10300340d0203020b41c1d0000c0e00c00074041c43c00e203c0494481c52011045505940341130317540c02d02e040c0140c010000318131800c00c0c05038140b01880a12000c29101800100c01600100407015529491803902d00880d20403200300080f2a0020003004842040116940c0d400a810b8034240c0080d0300c40c84211303403c0c01611290807607240c2620a104007000626000140e10352454000841108825014090500760490750342d040710311405101911180607d01810300801210100d9080116014181060801e22442103103001e00c80c0103401e515440a028201203031028402960521695038086120184107000f40840d0f41244000900c60520810401a045440c00125251414480000e00050005000b614010044c000000c600040d0014495807600d2b41542c0d000c5803940c07150480c000942090303000311440140c49030004049061106143d00181c01600140e100c0d050600e004812129040091401d2600500c00030340541e42e82ea12445c11034103042101a035940e19440121b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 109733480 1250 109732230 109732247
    0x30c06020f0d0e1b0a090510080303070e04231b0d18060b09060d12090b07200f0d03030e0109080714120316050705100e0c010e090108070b0703 63
    0x51042001c0481c41c4850a00319800035010402140c0540c0d06009400201445403000204420b03005204680c0070404403c3d1644442d50144200c5a114113284c2c07030310810b90850b8001c0e40d8141c005410a5101d0082d4645840303078900003411110880c6d4420343d801c80d0814410f00c0201601e000c000032001c4986010080c41c1220700c0c2081c148400c00c15035004000505200010400a8442901d810280503050500d44109401040300504041030107a0341c0d075603400e000d20403825480802049500000309803080307002510405219030382684000080c070b03600d040705c40e0b0603501c0c0e6449203c002ca4109003a84441648a030800c1e0980381c00b19034150402103442c09020076650003040a10002007001c11300c6100010881e140d41c440d402c1d540007602c080b21403420750000740c40e080f031510b070190340908040d4040c6004155292144041d1a0f44001d4100102d0803100991140a044e400c003080111896a00c0159500d030440201d625107030950404035102d0707469603140a003407407071040000ea4009040c00b49000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 109734730 1250 109733480 109733497
    0x10c0512031f050406050105030c031302060304030f030f27021804051c0806300604030f0905040e120a090f1d0a0b01081603060b0c07050f0105030403020307030c0602 73
    0x115039281030181800107910060b03003544071040604900800c544c5454021001169416510582582c491443c145907550001d041008020650081030006843d503002442c4118080d860310440600b06c00800b400750b9040c161a110300d549018038412aa54a00c001c0030f607a170040e00b0141c1d100540610104282c4416049501c02c842c200d0740800c010400001413001d03101c080c1035801d105110144001fa1784840d03090350a60341c40181d2161251208461031110181c903280c000c3c0861018116082185c1408020345003038001640440101800a800000d148014941960104180960603003401d464001da0621039016420024500b503001c2c2c440c018800c040c04c8200b0140300110b039915440126074840b0003030104030001080c0014600307145486011032218060316464480e0355209040c696116040c3e83c020241b40e610712011a0500e140c0015002c01d6881c100100280c508110402140c43c0e0000702c9103041080800c01c110001b64040142c419107549030078040e608070041d28101019010710f400c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 109735980 1250 109734730 109734763
    0x1c0e0301020313050f150a020304030e040c030c090f0605030103060e0322060306170a0b180a0605040b0c03010b0d02130e0c1c0606090b030c0408060106050c100b0a05010c05 76
    0x14003d4100702c3c01e100c5060603200e0021500e501040894907515402004000f007580e06407180041d4103c00a6002981d010344a49440e00500b103158000504071120400e1800010340d503102c0112910380c0090401010b86004191181d06900c0c2040c0200244414000200341c81d446442400c0344c81c400700245c0b8400702c1c0403401070030410170340302004442c040340d8883c980020341010400200040103029000c03022154002900018005031074191a50301c015102200351a140c010303201c190388003845682040e900c0741c2c5002c15039080c94288441d0500700030f03000c0f45c11001c04200400c100c2e0749050455503070b0360841c5e4000da164551304904414540031035001c0d0081c0d1412408101a01c130500c001003444404207000e03140c138260b47c070319003001300d5441d4015040031038002c207020b000100550300134641c4821010051854140c0b41c80540782441803e9001d5004120041881450784030144141c1e01c200c20b150b4800c01c90700e080b8800054540c040b6110740d6050200480b10007090000030701500141109488 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 109737230 1250 109735980 109735987
    0x1030f15030b150d020a030303150302040f151a04060807090504020706060816080c0d0606030f111003020a020a0803090a1a0601020c181503070f030303020d0b040b031c0e030102 78
    0x10810b040e0b000444035600c08aa48640c494602d140513120900f0490700a03144030101e5040d60740560003040c500b12202e180781240070f4000016a110b004010500c48081c0c400314083c146a403c21300302100d25000a01d481c020081d0340e000400c1c034101038400310f034018900f640741510362803000c0e905c01000742c0003907400074000107840045c230003203800c81c40c12100410222086040d143c80e82d547e0001047c0204680d0f0b410034898000d2614040080102c01c1d4041d0300700243c55a44c0760346480c00e0b82d01e1010b04641c0305044800c0c2032542d00d00140101c8003592076040940c503003622000c0c001d499074820700c0010310441001c004200012020800c1c054210351022408a01c200701c10103910454108803540d900501c2620f002120301e080c030142c01014a0903014000c015078403071120114000002c2018035070144101c2000207480c0012183c1c80300154001d840050780c50040704440c4080c2c440302d5014500035802c110701d00c0c1d02c0351000203846400280d003c94142d00c501c0090811903601e88a042c0c9994190b0011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 109738480 1250 109737230 109737233
    0x1119090c0c020a1401091403030f0c0a111e10030e060421111c0201110a0302071e03080a050a02130b04050a0e010803031303020a121106060604050f01030f1503 70
    0x2402141c0c0e00850308074107402e641d403000881644401911a001511000c01044481912904000c40f020001c0980e420a201006089980c0c0c0005c110201d0b43d6220122010600c0458110211100c0c13040d14110076011606040850681003040018000d48214074460081031003a40b1031201700e1421b2080e6019403c05050030000d5500500b00c01542104240090003020f0045c0230b11000701c000740d800b50443d8026402c6603140b070107000280030309654030350f490000708103040d034000d050321609600c0040e00c1d490913013030011079128194891020081043e01920219800c0b404190303200c0003401c4040b032035640b01c0d034911000e8003446454550030b00d0318800219400e40345001600c2a100b007514585000340e6110070110031010203105914440e04200003282c40120b401e0700c84000319000e401101d07007029503a52200080005048100002421030014a04140003031040c00d4010408445403802c15041c480010008030803041e00e60306140d0382e0500210700319600d4204942130203140c0300000600760380f07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 109739730 1250 109738480 109738487
    0xc1e01020705090c030402040609020c0a06230709080601060512040210030b03070602030a02060f1312020a051b210309120a060c03091203060f0608041505042d1119090c 74
    0x940d407c170300c01c40c00e0002c00306030607106100f601c103110b110718000c2802c907166498402c0102070300c25140038840100c594158652666086444c095113042d0f0706c00341024580582c10b0700301581a041081001001c000c02c452403500c030f104440d00290100e490780c402086820b001d07002098481c440d80c0d010700424800080307084d004000b42055149580039107156560f40c2d06120f4860408948030540b2002d0710181101058045001c000c0da03403150300480b0781c41c0202d82c40c1d00c0e28042402801c071110896240480b261410450040c0c12401c42080f04c2070404c0000c1ca07189601e074060315045500500010b2011800244104020a0301c0d81d0408401c004001800340f0040240111800076680e01d001114406411842403141d00d0031078241c2d201c0d040511382810030803140e4400250084c1c514031400142d000c1c028005219060045125150442c006d10652540f6554402c904151195004000c5c803494046511110300c00343e550b200320b81d814943c1d586103030700400141f480d810003400c143c507151406180980 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 109740980 1250 109739730 109739737
    0xa0210050316090302060706090807050105041b061805062a0304091b05070204050a0212090a020a060908070b0c011503060e01050a0533061612020c1e01020705090c 72
    0x40324102800c840b0a15035060358078000070b110080d0090341c1000b0940104145512800c421441603107042c0c0b51100c1602e1726425100240c50035207000045082050f00c0a440e0a81c500081c1403500300301407801074072038942103800e03400d108141c014000043d042500140d801895195061070004c10842c4107600c03641c1950343c1d0040c0c010109024500844004c01d000d0000311200e4200c129170b50b080c85e101e405c1d42400301501000d021941c80315000d00060340800c440d42c02051040c5c940d000102a80c0046004101c2403031802c0c1d20440511610072030a001a01c40455035605a800c02000c00380e0710300308818114010618554904186004180c2c040704200507034000644812142d8028804d80d11101c0e0351204840c003d6500c50081820002c180f0500c1d03051100950300d0a5607401300002d0b210b84400443d010364400249040d0088250741e86004001da84191a95071007200e10080a4182202000c101964212505014080f01400b04888140c0c801c0100f035015050182c04a0823a00700007030500d61607003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 109742230 1250 109740980 109740991
    0x90a090f0c050903030703140403140109030f031503021203120106050c0d030614120703081903050a090b01060c0516030f120c03051e040e160f02070501140c0a02100503 74
    0x40c142504aaa0944a40b00b654160b14004010b149002040c0e9020b0724281d6401080b042462020306c0004046094620304154505515001084496113458001c0c00b501e5000c55690515142008103040d1940c00600e0074280e90b41901c00406100a502c0d40e1890341c003e81c00a40320802d0302e100040790f4541e00001400c2e0f90712441c0211101e625910b0829030588002e8044e20003107a1070142c0166441ca41840f0401c018450174040e1090107850340c81d211703031a0303100d890b030301c091984030162100455915224003503204078054810800c8040598940d40110018428201000200650b110900c44107000360f172415000d40d041180320950342d15016058481c19101591101210816000c200c0d01030a614568240d140d80c560346001e80205094035480c1c107994071040e00c010140008185402c50070740c12401a00e0860000c600780000341c0009020012132000c800c11500950070400071643c02200064101c000080d199850343da403001700da454850480c002941c07085290315400c40464101d0021070050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 109743480 1250 109742230 109742261
    0x705090609031618050702030d0f0e010906050106090902030105060d02090a081603140f10020a03020d050c1b070308090d030311070606030c15050f070507170d030507080f1b090a09 79
    0x4003200c0e810f050403911700701c600d6005604100300c400e400e02c01c5035100c82101c6003000706c0000c0c43d0781c207501802e0845d50300e0a003c549076940e0b140184441904075160000801f00f482083d4690340c10000070426900560351001f00e22900450150742603a502c4400101805083c021140709100d81c40c42d4407031440462105a0340303c0c52443e9421405400030400d9003944034038000800b202d007034898401c0029842102d00f02c0030154207001246061845004180c090800c1c07000c1e031134403000c44c020b4031500c2c51800c4485141d50351110038200001580704060b108012000c90b40c411440d40142415130203881c0c2c10403c801e0400300000d840b81041000da10140982c1d0044500402d00394079000e04040131a000007003030002c11302c1400410440069203004011861146041c1c418443e42c8855040c030202c80044003821a80001c45122101d903807501c12903500c02d02e2031400c460a810020907a07242c8100140c0154540303c0c05540c01d00c415442c500c211341c11100c0180a84020f550b0b1442c1041c020400d504606100c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 109744730 1250 109743480 109743509
    0x9050603131b05010215090f030f04051305010510050309030409061e08010608102c03040e090303040209010e06040b2101140f070807020a1211012307050906090316 72
    0x2500b400c910b50001e035101a00102200040400d440880c03a000500301d441e0780c45403a1401e101c10713200740007800110b80500c00c2140c54906003c100081c4810203260484040c1c40c1c000100080c1d99801100101c240380ca040c41e030b13038a03202e1250701b9040d8031640e000a640b650600500151010007043c25036007031004c0105a4511507100c1285a003070745d6482c8a4506264000a20798003201c0003a070000144001a0000109840681c4602e034103080024049021517040030804000300303a841c10407503510a4040707021354a03618260340010300000b0107010704045000c0c00000620691500d51003c1c1509074018100480c040c20301114241130407800c10404a10350030485000e4900042e8682e142c0201c124989074409580c400400719004140140000d0440c402c8001c1580420f14164515420211a03906d204404c00090402829102212074015403008203501401004172404541034010342d0070f28007195038514082c0020758900803051000c0d414058000c40c0101d1200759000740c411075860075014030300d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 109745980 1250 109744730 109744763
    0x1a091c030305240f0409020414010503070f05011409010201020d0f020c190b0c0a09030b0c1206100c03030b0105040308031015050c0307020f0111011b08150a05100905060313 76
    0xc000154080c4500e542c01450303d102907514042c03207100e40310000036000250042c12900003809a07002d02900c0c004549030030005000506003400184007400440c682c010309135240c100020108020170340c01003107420000c01d22081c1a81700b0b40481d803c070340d4800c1303050059109103c1000c00941c0443c64124081c4140070907004011306204104180541058034000030740d844d80141403040d0712642c0107504100310700002000085100400310f008622410600e61207542030800e080c1a04000341005109201980d84d00ba5210340c00b4001104c607690510300410481d4034440160b84902403500000e100755404403c006044020307080c2d1a0841d080882d034042000030389881907d1912070441855490f4008004100240c20400702a000f14a4180350030301c042600e884840e801c451140c09090035082e02500c02c8103120780c3c0102400d0304425001201900b890022000075081c80f0503203d958003450b01c0b4055410351a0003080980300402025042541e68a42010f06004000b44c0102c200c885100c240390215 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 109747230 1250 109745980 109746001
    0x6030e010e0709090204020702090108010507020c220c0504150c0b0105010804021302030417070308100b030601390f0b010f03020906040506130e15010803070506011a091c030305 78
    0x1484050034805019080c0c00e2a030b034075001d0209480140c0c6c006408014100058440b40c0c83c045c001c09040000160341d04001c00000d003011503d0035000d2050303c0c003000a00210340c04061414030004a07080000703040041c03000690f8240a50fa0140720500340d641e00d0410780319004043c0130042813060040c4585680c0312070040d078046d001940c0203900319419260070203030300703400c0e50007190054003580004e020a01c5051504089500c0840110009082c2340d06002460046611020141415074081390945c900280002c200c1d1000440d102c032403103202000c61250021001d0714000e81d0004c0301c8015055420b030b041c6480d42c607101605c12110050810f0000403062000e42e90041505d42c018610001034885204002c06804080c1c165944648030b42034901101c0c0013071044142e10000d24014180c0314412000c08110080c05902c00f0074241c204002e6040040c1c8007240c45415194154501c120030441d44500b10464042e029035660400042400302d105610850142d803042d42c031960302801503949200b0602d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 109748480 1250 109747230 109747241
    0xc05011a0102060c03070e1504030c061d010201060b09060a0c050d050a0206070f0c08030406021201090f0b0d12030e03070b0c04091a01080402010e18040804060e01020f0c0d020109081606030e01 85
    0x1000641000c0d914640385840d400882e0300323851880d0842c1c1040e883e502e80c114400c0680c1e2201d13001c0f9410311080514081501c0e00d4203440c080900003040708074a4425002124031a00d00fa00d4803a00d0002502c1050500071b040e2105043d4000303048500810760404050060341c080c40702d4401500c200c4c4001021640701e01c10100c0c04403816503800d1003011143e6107411007900090700498a0a4003403056411076628441858020116800c000c00c1028042200c0d000b2100301d1003003140981b4000c8010404200032922255982290f4540000c15804050000d4110b0040000003080c1c1c000700d20910240c1d0004501078001d4500000003000b07106900c128141c6d6101c404400716020540042c005000341d030140c01e16a51541010380300903a0981ca101c450100580e048504840d0008041814010260700014111801a081c0010041c000c11a00250794504540300c019100e4008044280c00716441413014900a015050442d0500b0100c00e071005851140c40c051000024a0448041240141401070f0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 109749730 1250 109748480 109748491
    0x40b0c100b031b042705010f0c05160f02040915090b0106050a020a0b060604150306080c040902130e1c03050f060105031905040204020c03070b0a060b0a080f04030c05011a0102060c03 80
    0x10a0400c0c107001e00c80540b410205c50150300c040c03055030f03a201d14450a12042c20912400000840c0c8a005000c1411a01c4082488040000174828483c17119580800180c6c181c0c1c118404000e05280382c030014028001100d40202150004244140301c2150b40d0030a411081c8508840c94a903a203d200c1150740340641e004007001a4050103080b000f25440c50009500080c02a000c1d40c42c00d82c491a111070449000078203000041d607204ea04000720042800000212041101c081c0800e1005d90002011111a070074410b00142c1d80701c00820341c82d40100140007201030302011a4545090665016008205c210383c090b203110000b10001d01c0c298032400490f4411b4158083c017640440030500130030700400d40284100d03049a405c02031300e061244108050590381d0f10600101d2018501100e6031003e0380c41c0c1d03078040c401030807083c403c0603049a0050a010f034070080400d040a003030b980d42d040448907a4074200d4080d125510340034828500301d04481524940392400e030211202603e59021145480c48221030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 109750980 1250 109749730 109749763
    0x1050d0213020a0207031e03030e0d0c150204050d0f030f0201050603031e131e120312050403031d100e070e060108090f0304060302090f0910030611040b0c100b03 71
    0x19035007600791055001c3c06451202c1d00c101c2c0c400d2a2030740c1d140e014030310180a00c401030b4009440c0710004c142d41030098815140e080005081d030303030b0807100014060407800794000300301c20302c9603950070107590250f41600c3c01408020070450400c0014142900040304030441640000c100ea8145c00300f0600500805005080c0179008502e40400ba082221070255074451182400c1010000307030383c0c41104c1201c00c102411524208007454800070500c00900c40c0e560b4084062043c0c5039403610302003030b0405020040101401408155035503140760480080003246c04880c0c80010344540101d800c000000c0622048514000030060035000321092569800385104004a107458032002414552248004030341250321070045070403aa001c483c205055810582040d00040c2c3c1c04100c0f003c9a1071b109000c945000015a6035121605040c883c0b05c80200c200c2c04003503e01c40e10307403804403140c003c404c00303c0f8020240f91454545440140003450340382c1003c8222662124141307804a44103103000306046070b280d228041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 109752230 1250 109750980 109750999
    0x1101320a0c0501021b06010e04050604060506040609020a0f0e0a0506030c1b030c0f060a060b0a030b011202070503030105040b03010b0102060a0b18010e040302071a07030c050109230601050d02 84
    0x80081209a114002180810022036514800218240040d11002056580340c0c030080b81030021451034003805034800c000e0b008100040c040400d00c08a0030a81254002c10b010030305d40c0d200d20110700503064641c40091810f00c000350003904180d00443c0340080a10035991000701400301410000c807080e4038018264000b90030408180d003490303050020808031841403048400c1c4901e00e0903040c05c507007201030710712003d4108407001808201c00340802c56100d94081c03410031049082c580100024000d00981809055845400c1c440076806010071684142c0e42900a40d0354030010325004c0c1c0c4a80081c4074080c000e43c1002c11341c004a1506028640c900f100607802061161745040040020304511004150010032580d003000f01c0458418400c0e000c0d09141d0802c54542c00e0a1078007d01e403440660000c2e60101140586089054001d4120345002d0342500d45900080800c1c10010f006100c003e000501044c04228a00f075a0605901c00100c0e4441c000700796442aa82c54050102c190701084000703502c4104070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 109753480 1250 109752230 109752317
    0x12a0506010e1005090604060b04030b010305100203100303030c0903020909010b1e01020d051e0d0501060e0f010914010311040f03030f11030a050315030604030806030106170d0c03110a1101 83
    0x4030f2175607120100900c0860466a902c1d40da041d40d81c080d401c290794072110a001402806001c00032082d40d0941090304600d14940212000b205001d103000c0241015102c000c5280d080b485203416501568004010181c5800c1c984541c90003029000c0700180141800ca043c2c00c40100b50301d80700c511041c0181c016000c601c0200c42c0440341a800010195403000860302082c06003c00d0402920f50751b540c2c080c002400307505116000c0c1c201065466058403a421a01c0d050000b030b603200411004032140005440c022a403100d0058024084444010441d0b80c0041000180401d942c0e030b0880c1100d0003912801e0056550f048101c9903031a604100344816403040140507800c1c0d20500045503c08520310841e98540340c100c000078100b842c203036015000102040c4c280003a0b450203208030801403800e291100c2903100420000c80c1c5035658401204117108000b42c0c010b0500d4042c25840381c0700381c9200161829a0950302d4030485a003028030720140002d12801820305c51008648200c4c2c400449001d201c4ca001911 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 109754730 1250 109753480 109753489
    0x31503080301061b1505010f09023a0906060e09070f062015060103050619050d060b03060f0403090b04050607060f150611150106080a0b012a0506010e1005 68
    0x40302e0203030804044801d0a1008117a03c0544000010a103c80105155241000541916800e5048000c02d14810461580c0c0440301384541c1d004014110049041c1e03460342d94600c6903503503441c1c003000c02840c00d1408142c20000983c1c444011348c1c51400040c90192900f01c0030581d2145140a41d1100203513030b040601446015007019148119286811121030900d000203e051050301481c0100c00c48914052000568240c0921540100c3c1650210007001c140040d00c9440e050340c0c494207003d1098145414103008040e00b180203094000740450745a82003650b6514030f294000c5500f40c0c0040e940e44070101e018038031181114104c0d10020071190516043e5200c10006003e03c141e05001307203580780c003400b41d080301c0009960000c204a44804030400b4403214018203059142e42c1c1c0f039448040c2040103001090300440d040c1d401088419000441ea540c0c2d01c0142c81106c82022400003410342c3d6110580580c541907988102d15202d4400d0350b8150340d07203603102941c00501381c038244242e600d0a5024480c5062 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 109755980 1250 109754730 109754747
    0x603011b020a0b0c0d020d050a06080c010504030f0f05060910110405150d1d010207111503010621050c0a1e020d140409090614090703080313050f06070201020a03150308030106 77
    0x100c004019180c05c442c005210701726401030500c003502984910800003040d0b00341c8505001028a03030050300e0180b40d8000020042d101e6400014120380910058805100c80010051506580003040345c801e0f04010004685d1000d20f003440c01842410201e22511201d00001039400315400648807240b100c131000c04174070040e0001d000380340b83d265a4582c8402c0042014000e40c0080c800580010703541e03406403d2400d00140d1035140c59020740c1c0900300d58000d810644040b6811030300d5a1801d034040d1407459003103410385601a0001c0c46018249414011204210401092004450b890707003c00650b0080032004402400031041d805600a44e6944003494020701c818180501c1600c205071500b0b84031558841100c40002090303401c0c1d940da0320044510005c070581c2c3c80e00194800003c200e02460340ea01c0c92502c0c0b10060004840060004120741006810040801007007002070a54101e442d11103070003130003500040c2c5010002801c15401003803400d80402c4540070389800958892841c0e007010010b035603a15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 109757230 1250 109755980 109755991
    0x30c0706050c0705151603080106171b0c0304080304080105010906120b0103020906060903010e0c04140108030702010c06060306090b090601050105040305060606130b040815070905060d0b030111120603011b020a0b 93
    0xd0703040000d104c0406e008000301010510070340716601c1550500c071000300f4064a40342120000360890050014000404140e81c2034541440001c81da5000c000380031504601455000b42c3c80c85c41b01003000700322008190000c505031400c00c0030821801c1d65a02c041202111f45c260090000c120000051015041c12228290700c110050401481c0a500742c0203c0e003120000781071017949400c02040e1118524242c0501c2440403e21540c0ca035007941007001ca00e8072031090160090620100504140c10455035030081001503800c05010844114642048841d04100f00e4006000d4018100080340c25805001550305607a000700c0104102d503541024030920340c1c0404a0000d280200f02c000003106223003a402080079026603000352500c1c00c41200c242c02d503003101410341814003441c9038040c0b04980303a0380161a0449441c11340481e4456808011a0050490142180280c2800900c1003070820b01000b8043c02880300b40c001f00300081010300402c0488800644200040c0c10014401000c66000484180c104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 109758480 1250 109757230 109757269
    0x50a0f120209030f100b0103021215041b020105100b03091005040809030d050c070918030818060106021e01090305090603071205041101032a050a020c04090302030c0706050c0705 78
    0x144142c0068509812081008119442495400c0d00240c0364082c0704500182801c080d400c00055000b00410404000c11200e0800f003c000106041d0b03035217800107003619510600424544010200080c041c000450b0301d840101900e1000088810489003202d02c035012500c0944030310000800784402400010340190b0300300d10180324000160341c050080350400611610f62640c0c0ea00785c0829941011141d50144a0b803d00e02060405c10112840f04800229418900000d41d9950280071140881d8945403070309079481140d001044103500007440e20603a44600c4000303669500d02c038a01500703a40c62048002d0006100744144c907a03509220b409542c1020450410303120b0701410035030000442300300711404d03075681c0301484d440e005550b003611031181a004210f800780c0041034022400800208040180070411000040d9124524820300101052500c0204240300071140781c1002507494200c100300f4661030050303080028109004108460f0f1703400c100c401905a4600e02070410142000400312a41350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 109759730 1250 109758480 109758487
    0x121207020a0302060f09090c040503120714010905070504110c0322090f05060907080403020a15060308030f090d090602120a030603020d05060f06030307030806040504140a060204060f050a0f1202 85
    0x40e9541806414400c150408151b2280c1040c810842032801c080e04d81e200d058070800042c400d070b460200701c41c0340030841d041d40140da0743c42e80d1501e051031000d031180861071540380040307c20400038081044021180201c5090140f0b008240a81e0868401c0403006600b5a00030010100e003501082203421462501461220949985800c403006846402d641b9010359651102004042c0c038054001603081200c0e4680091117107860790b0003a6403983c070300c0000340901c0b0f02a007030843c50b00d55a4021030051940410f08075101d00300071091981d0307290299100c0029000d501d070444541840341c0c3c0c000c421180513038010511081020005541a07101354001e00415440301004009078880003521040036100c2c1c4020551490480189040e80c240908104d05c00e0300108141000700f0752144a9980241381184c00289603222880c2c03114904051154002c02c030700603405400306002c004c1d4003400403038000b9100d200041c1c0200702c013140c0134402c0d1807104d000b09002020000a461054001e840e00209107d001840e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 109760980 1250 109759730 109759733
    0x117072003040602070b0a08150f0627090601050a0507030909110a020c1c240504030c0501200409020904060f090b03160e07050a03020f030403030515121207020a03 72
    0x20100d1180901101644002820824944d0400c8800000e00c043d00fa0141030445c001070044c1040380280030b580240d184008416034540d01c18403603030041b2030003d22044e503550703070382d200b2540060244d541c00f10145038a000e60403142c02c1480020340304000580d2151304e044001042995140c0064800fa020008810720104000c2d510307105036040021040145500d40000800007881e0030250101240211894070b54407499540444080c0d0300240e01c003a01000c2c444082c050b4450520b0320340c50518407a070500013804289a0000f5038006a0707030056000b800141415404c021058102a9265901c035100b0081001b501c40c180d405410340100041001c14010390b6450701c440c411a40b07070401110305a840ca5005481e180030041117580d20744911400c0e004610300a00700c6a4648002d0215050020015400c82140d109a044600c0021450002c07078903401d083c04c00a00030841100c1400c620364002e28051014681a8010a00300d03900100400344c02916083d02d481c15000a0350403604622810f10200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 109762230 1250 109760980 109761017
    0x10f0513031104050703060f060f02030903030d0e070605030405030d1a13022703030909090304030c03060c0e060c07031106040e010305010f1b02120a050d021308010c050405011707 79
    0x8001c60090088007061031060b000c0104582c000703054103080c180360050410054959500d0041292506c2c14401168010042c069096100302c1c4241c0d907140c04009445541000d00b5880000712a0603582140c0f961900d50700290380c3c0d40300564003c2c2040c2d2082c0004a00401580c1003034003421140031000307680081500c04561043c85000c03d40303071440d0f00490202c5c12801d0b49003690880304501450015601c010724082901c07031141c1c040c1d2500440c1000c0005111503410801c407401154814020309120707076170341007881c01044c203100704800060484594800314640784094680c5009141c000d081290301d15627540d01601d503940e0a0541002061000051104030401b08900850203900003107005501c000508084074a2008080701d905102c01205111680c005000d840b5400d0b000952a0340e40c2900c1d409942c2809038800319040e0600005020b60032031a010108c00440350b028000740900c0c8201c1074155950b000e5401200c5c0090f07a1800041291403801a03444c2e004155801c012000b10407080c030300c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 109763480 1250 109762230 109762267
    0x131a0411100806060f0c0f0c0102060a090213091115040305190b0a0c0207180501080607050a3009050a0209011a120a0b06071b06020102030712020705010b0405011211120606010f05 79
    0x1c421500252440d40c00e81d4ac040c014075074071801c801001c214190300c95001a442d26041030494800540d030700c4200c1d04020060040c4c11000000804a004640803050705010540c45800102c842d800b41344280075202c0d038001d000440c655440003200215603141061000100030303e4800000b14810f01d0800601101c0030590095411030706500440d8542c10841340d10b24029002d400042000020400245d01551000c8a800c0e000701d0001038440e0201180f501400041c03484441e407401c00e140040b113804101c0c00041200c2c50301e1003038410290f41d0782e07280070010030342009010708001d01c04100940d07101c1d80681042d4a52281030050001030381044500426903540200100319120080300c040b000c60001d6580c122401460284002e5243d0f19000d08002e00781e4403000380007910907801182c410200402900600d082c44005401006a582c1d1143c180d40040f90b581c10a890700d1242101c2004903040c902c2c104040e4424038002044143c56040045403414002c43c0d1241c10400180402c002c0d200c00f01004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 109764730 1250 109763480 109763503
    0x3030f1f0b0f0403061a061c060e190506090610030b1801080705090906060109150c02460b030601051207121a0306040b131a0411100806060f0c 63
    0x41e64649040d4900f0104543e09002d80c40d0468200103615170843d607c0c0c1d000c44d51016441005c18601032158200e020203040c10f82c014200600015080040d03d0803622908030011203050014801a01c48100f4412125016140381d44c01546905224004500a400030344a200d005080d4205401411004040c04d1030700ba0880038150b044801c0c2000f0034940360107099002507050010345441c1c10710500103800f4084503c00c0100c1310042034851402103001c0c03107252004980281c526281c0214018071a4218041303010320130040f001c40d07410300d4207226243c1016140f038a100c100b01401c1074205080966150030040c81c4074100b140030042030a49a8078540c0d060b004104545036960084121100310003502d900a00e00d844010f800e40725584942e40005885801c160010702c0301d4030350b8494910320118104041009480c81306100b442c801d07026088000180300301e0089041428582e0410204003807481035800240009000f1008203403203103881801010350715035002240e803400c141104c50606240c40c0c1c124 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 109765980 1250 109764730 109764757
    0x121a0d0809041401180c090902030f04020405010f060507111f020105150103110a0804050c030d0c1101021c1d10020c040f111206030106031a0a06060203030f1f0b 71
    0x600c00c03550b04107401040c15041d40d045009030150b05151040c5a0f90b10400c003502615034440e40c408803030500429041c0054036142e10259907901d000c2c03609090707510040d54101d000b180b9140000030036013010b40d0001c0135540d4035901c0c11b1030540b9070340710020b454500325241d40c3c1c0700d4001070165507110390b01101c2501207000c80d0008155441d100c00b60011115410704038605150a080441181e055964200c580300c14590900d030300c0c00d4980e401e2581c40d1608040314180c040c030802401000c159000742c01807812500c61192920003512742c1004a3f1101c01900566103410340c444402840203000f050100c81c0d0803c4011202581010480010700302041c030502c240160704078108582e0503043c41e0007800d85a29043c030341807040140c01c0031102060710680d035280408542500200c0d4040c0d07030a40280c802141c008481d400240303010301d880d0220b1142034072100c403050310301070001a182c2d0012045e24800c0c07138885e044100c1a0342c2e1901080e42c400c070103940c40306250304042d0007150300d00c100c10181402484110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 109767230 1250 109765980 109765987
    0x318031e0304020a24030e010b010c330603151103130302030705060f0a0b0a060e0d080708030c03090f010603020a050d0f0605010915080a0206072907120b01030b01121a0d08 76
    0x100246c126103944020001780e074103059441030300d41d8010768100400c907032103508080c180350200c1041151180840303212221561860045c10a064942c01c02000e0340c1c00342040d6140180803900c4441114500c6041d030040c0c020603c0080d00091503000228101030203801501d00d000c1c03107a5074007410b0001c00c41d080f001101d840700900c01c444d10284610314a8078410f60f156106c0b5420058050803021601d4003242c807072000c402826003001308240603500c03102e50000c002a213038141158803561b0381d0001c41d1100310303922811040a5101905006070804c0b00d40250010749000e00304028425118454a8140c0e0b00c41d010b00307902c03000a00c4a1040c0c6009150800c000605021085c0340503114940030703440000035601c603080300302c050303501c2c1412102101c1d031250071008c005160743e05030002d0400300c0041c100306818480401103240d1b08504107071021a4071a0b820081785403440f00641c11600150390f0701d80081c1a0350014403d01a250340110909401c406022090340351000c001750740c6184181c0c04a032100c9010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 109768480 1250 109767230 109767299
    0x51906050c03090a06020d0e01140109140103110d08270102070602070602070506030406090c06030b01090b0f0304030c0203030408070f0f0f12030c080910050318031e0304020a 77
    0x612036903800ca10104071181c65814903102c2c282c1e842011141c00b908080d40002c03501da0b1902294002507445036050021302241c01c501c0003007050f195092043c80800d41c288403071640181b003c0301a441c10b07203a210200e103101070f403000140114100d51010803a0b203044c040040080362442c400780b20b840d40701607103010000042028002410300e41d40c0d9000700c05541c401c4209108040e00400d40b00c00303a0f8070640340b2644a40e110b060010180401c01d001030301040000801051442c0e060300040030382c00003a20b035684000d03951500d43c2c2080c402d0f58560b07825041c091001c50002403050b1441c0c0d50290004040b2400c141c1c603504007a0038160150b120601200b5451410403040e02420400c1006216054907175440c0b62400700440e04808208400808100206540e4400c01c1000c1e000d07a00c0204015112404214903840b000d4444c0d482542c0760b401178140100c0341180028008200c0310f081400442480d0310f40d506000d004100d4202a00490307000d11840c0011440814030082e4140c00c29035036002001f60b0458 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 109769730 1250 109768480 109768493
    0x1c020304120806010e120703020409050304090e0a03050306011d0402040801021c05160f02030403050303010e071106040c06140408030a0c03081e04020607060b0307060306080d0207051c030c0519 85
    0x6100004042c8441d4a0030004143e802c0001a504180306850b030440a80900c1080c0b41003201e240c00081d8001e2030441c1c02000e0100000103017003a100410010000801d40e03245640d03442400c07000042c0054820000915154410960031140c56441100000c5080100001400b6030f0010380150780c0580d80840d00101d11034200c22000d4076010120010015802d21000460b200c07030716484034005000002c1220b08082c0d05c20800c40b0300441d0040e050300d49a5844030312141da00003040c2c585100140b441c04d00007103204004030f500c80c000c90744441c1d581e807140c1c9000829542490070080303a9a0072501400005540c003c01c0c0014028100750360740e640300a5240d80b5000c0c05440c0047c0c440c20345407a000f809445101098a036154201da01203851907142c9495142020151031104170550705401000d0000507010f416030006415108403805480d014150034804a0791850684281c941c444035800e414101d844c44030b5803d0400500074030303290950103100d80301c0a140001c150030806040b49040b2551003407009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 109770980 1250 109769730 109769753
    0xd0311070209060d1a070f0e0316060e1201020301030c0623030a0b04180f05010516020616050702030304030b061003020702210118030305041505060303040e0a021c020304 75
    0x802128403800d00195070049002e600c00101000e0290065a0096040c04404506100100041d1001c0034179440d2190b001488000881d00030700c0421001c00b403c014500d40418a40110401d103c42c21803007500d08001121a10403510f040d541080141d07044c0d8540c510280002d50117907000d10440c0d400d03245042401082455481c1d07000c0340114080061404074402c03001141d400611018010801c1008400040c006098409a8190750001561010100714024020440450140c1d0081010f99650030905400056890404005800800004519110b0842594504200c40c513249003415030340c0d80844e1450b841074005030703000c030321250811200389000400381402e01090301e815400e200996022580740f007989210740248804100c4040c2c203080f004d501c0404040c01a400c0c0102820b203908003d4000c042c240c400741c0300c3d0070001261459042c40d6010300703401070303c0c0500110300e000d14100900400c0c0c040a0059131410303800b000b03884a1440001c070711452101000c0801a81d905040c41c1c043c1d036029 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 109772230 1250 109770980 109771001
    0x71b151d030f0601090209150c0c0f0f011b080706020a05071203150e0912030c0d1a01020a02150d05010303030f200405060d0216060501030b070804050a03030c200d03 73
    0x40c40103101c4188882c01042a50440d901c0351000342e15120030000080c501d140c07a071503242c003900c40401d440b03a1103a40083c0c00340c44004259424003240490701c05000310075001160f414040340b441c003080b144000b00311001500d524080c144190a01c0c49544d1203034161703230021522100161020a101d014007948840340500803101381030801940b944051807121040043c070a69454940410014184040500c114501102e40b0f0720352650320324210710280c0c0035801400c0f020b03c0c01450b10701c2c4c007a47c20042502012500805030010044a422a420001101300000340e040f0320079000c1c494880c00703c0540c000d55000e144039440101311074400804440485d0400380400f86e00300e810701203804001e101c07101114181c3d0000d603012603445d100c07020081c0103446104000b5030310704400e501d03040a11080f640102d05991003a00c560101d521103034012155020241c4000e06039070800218480041d0181c1d10011205541c0e0425802d080300c00e0f00301140820b0780f13042c0d080032034201050007006182d03d4401c0480c0407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 109773480 1250 109772230 109772233
    0x5041b03051b0105090301111305030c031c022e0e010218040216020d06090c1208090105071109131103010e1c090b0d020c010b06030903071b151d03 65
    0x40c0c60360300c0710360303480c0b081003004070012400302404040d69204104807002c416010700244034000da9510141801d80c000d580e4a50500d4a4080c0440c0d540340100b00704510f410000c00a0010b1400c010200d5a800d070511001c0040d8401c043e07041410181c800b903621001d03020b1640c405c16500f10429035006865445d14a80a00d034030400c4a80c03e84040703002e0304c01141c00281c40050b15480c3e040c0e0718400108606501075449281c0b82c92180030402d03035401c040c0b0b840c3d1048840f03d498a03520b981c20500001003c0c801040b0490a002c0c44085504c103102410b070b640d0194403440d560092590104580342425245412803481c0c140c0b001044c000f420034620840b01d4294000c01000507a640301540b00c100c0118414003005005040380091481003600c4405804086082c980c1e5000000303070000254001504c8203450350038144107502d14a800c0b0180d03840350829030051483e0003616a11030840042d206a0a00e4245020801044007503415036055500c41080e2a440c4050501c0b41440d03445c0141d401843e0711070b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 109774730 1250 109773480 109773533
    0x3050705040e0f0403120f0902030d0206090a060f0209060309010209030106052236030909060b030f07020a120905040b06030408191e0801090c1e23070302010504 71
    0x2000c01c666411a0701c840000ca54883ca501d417858103c46941e2000e002d01400350411051594801342580852900da100b202110b21206020b00c2c142d0325500300729992941038211400c3c1d1004541d15070400906100341000061500d4040000182c86400603100d004842e980440e4100d040e01b0709100d400701914007100c2c8204d00c0040e01a0161391001030300583ca442e81c1d110507151040b0400340310a030039040c040d40808004000201d4000c0c6c1000201d8400b40c000035400ba4001502054900c100000c2d0380e07003900c06074515031741c801c0c0b05460454040c01507001c40c410400e580000c40c2074410300c400469600d94804204600d000104410b4604403030010740301c1d403410010722001072100f104a171701c040b48601c941e0322400714811007911001483d2404a88080d41900416440c07540140072506882460780100030b81420300c00100c0c0d90040320030110000340324480d01c03540b1070b0f40200c050010211a0010340c1d40e00b1449107080100580120500300c000d41e4450081c40b0070040402101c01c0e8030303c4c00c43d401d075aa = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 109775980 1250 109774730 109774739
    0x5100c0615060305060901050a1806030b0408090102060a020306091302030f0601030303060503070e06030a1b0b0d090c080109031719110702010201110a2c19080c0301090804050603060a05030d0f0305070504 90
    0x112242c0340c400c3c2105d2b0f17031501425501c0801e40c0e030011401035802111011032490141004900c075404007944d940113005200004d482e01c403da02c262401148040e260b003076540e40d03c0b45055040c0348580c6041c1e030b2622074451040c100030005c02040c6c0c040d6100e5030700401d0f490700c2c0c1014580703002400c0d00000c500003030b80e50401040d521b00207500100360b50032000c80c040c0c5080c9204e520182d9401500f000412610000328107082ca0304039044101010b104240c0714103005d0f5901c00ca1802c0703030b000100040c0085c080700d854aa8118418070b42035005560915080c00140704074a4280450350608030800d480807000ca07040d01950b8080c400c600c6030540305c1d800c1f10300e0552418002402070100300101c4401c005030380030382920717104031410b65100054050016032034003c44405111852a8502c20040b10703200e02c41c40001d240c03e06000b401103190303101c2d484504150820f410005c0c0b40d040108802d0300840f584c0300008069404104050700114035845002d02c5000c0585c00500341e0340003c15102c2407107400c010420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 109777230 1250 109775980 109775989
    0x80f010603110603060d02030a0501090209070f02032a0a1b08060105090109090606170604060b1f03020c010b0d12030b04140402060a020109140d021006030b0105100c061506030506090105 82
    0x22481c2c5011a03000d0b0742c035075607200020070070f141c0b401c006034142c86507160000c104081507000e0101702d130086400c00182d549008017241e004c030b60310301403100580080c0710302e0544000501005005500d10441c0c10500c484801038240742591400003950b0070000c648c09901059a030002c828094401a0080c050340e40c14000414416201841101c140700c0c0d0714002242440699031112001d41104400d540114900700c1c00e060f03842c201a05d055602a26144884866181c5a08011440c0322034484000e01c01e09801c400b0340094112180c003003100d54841a0410041d41c03280c0d400c0d0382817071140e0744203800808a41e40007000c81e2610000740b4041d5190081e07480505607030400c1d032980b1681c12a0125036844220ac002c074058609100000d0880c01480d8200c41c04803030104104050746200da080300d03130707401c08040340300140e0351a07200c00b03848181c1c0c7d640140003604007a1948000d004603410f100604002d5580c0b070f40c084414040840d407040c81644400c4c00360359454021250002c0307003190848980d504000015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 109778480 1250 109777230 109777253
    0x6070905180c0a20070b0d05060a03050d03091b09020712030b0303040314190804090b03010207150c02070b040b2a060f100b03010b041d0403090302090703060905070306080f010603 79
    0x1201480301102d04891030444807641d0344006a20002665101aa41d0300d46c164603802c0400c0202ca9282884005582400c18054203000c8942010003840145940c0700150000d00031b8000076501c406a206104020103c800e8148008000100c0700685d2103125040210f9036002c1a00441c042504200003a2126540003040da01600d40041d407900c00300d03a03101f0502e840d15034001c00310500c4028070002c0308140510400580105e03000e07800284040c1071020109800c034852500024140c0348020031107a441d00c500c1e4000c51404002c1e004440301d0369111701c0d150b110f07a040b60380b021201c800005000c007001d83c040040b055045c0c60428500c00d500c80c0c404031203501c0d618001c00e00186501c0110004494401842e9230800410720412000e03520350b142c482c1c842c0e541d4042c0c05a079501c8100d0005e041105030f500c2c400f25114503050340d59041194155420040c0c90314014000104158a0b00e00110382d406c000d00c42e00f8064000340c3c500007615407038003620b20f040403003641c1e0b441708a9240401c00c0000c1911603031903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 109779730 1250 109778480 109778497
    0x702060c040e1510020d0305011a0d0b010207051e031509030304060b1c03030e01110c030307030e0309040f0b01080604060f17070e1303090b070f03030203090f06070905180c 76
    0x62070095880b541d0f4103007602d4141e0b0b00c0c10381c0710842c1800d811010f43c02152403031004086507028815a81c80b1440d1240b41400c02020200d0003208001c2503d00c406641d10070b6000420510544000a5540b40081c010b45a0608200718046801a0031a05807030b081051000c11500e860710b400062030034040ca26100e0000500240509444000614682c0e4035842185205030390b003034221101d00701a0800600600000f640210f140d03107071450004ea000005000c0e1450808403100440c5540e4030040114054030b05103c1c100c00f2488180260386055450740242350903a014203e000074450031940004140c60b8000d007215011760701e40b41c0f00340034900c20080000c0c1600c1040c6000120300c125100307682c1ca0003025502c0840e001c0c1d140d8003030140c94801c0c0d080440200340255581c84120f41c4075a0825150305c1034140040a4000000c50500003034000d4000c2d41d8401d05003c2a00c81456009a9040c02c103c000c85180c0c002501c40d62080c4010f20341850350ba41014180300700b0101c146895031404c002c80c8601c600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 109780980 1250 109779730 109779749
    0x6071d0d050a020604090e012009010f020a0204020301141f021009030e060309010203010510030c091a07050d050405030f0109051e0f030f040614070201080601050c0109290702060c04 80
    0x40e100a10408200e005650ba502504540d0380c0c0e9a90501c8400804e00300e49100f17015400d00700b00446080040d06548490f80a402c12180713000d0b4000010744400c241c628440065001d05405500983e82d1031000d0760003084410101006601c3c2c1d042005403032210046a00c909800d882d8800700703410782c00104420b0700c106555000135000941d007810303030b9045120030910354040e200000b00101c0310019009103040f984260749600c0d840030802d0080d400c0e0703013912050f4030002c1c240c02002c000c1d00c0d80841221000c41051304866140c25090b440362414200a1003581000c1a00014200b0140c241045074007204680d10008002a40091742c80f680c4071446c2881c05c600c0c42601d00d00010700390100b40107100300030301c28078116941c4103410304080c540b940251145c14081902c000d8000e03003c801c4a4204d0303241c5941651100ea03150b48410055076950441c00000c02e10f9943c0d08007810020301585180d040d1556901105100740c128a91060304020340101842c045410810034000c100c11000b0665081d40c07030701034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 109782230 1250 109780980 109780999
    0x50105010f2001090b09010c0809030a1403071b0309050109060306080604080c0f0d02070510090305150a02040527010f03080403110607060504080306030610051011030d0c1106071d 79
    0x40b00d082c0034260902002c0c0c1821212420b003c04501c0540c4060307004501a2075400c026a500740009442c0c1c000d14950383c000c00d40d03184114500100000003194004200e04001081d1001c0c10060420860100004c40c00304508000034881d540c1c004490304000e01251506202c85800d00000a44408000c0c0009101c680d010400082181e030a0048a61021184040381d201e1010050b000759117403101c0c425180a81c0a18012840c0948510600003e694003c00180400440c0440100300010b0042400030706a50a010118059031256483e460400c036046215410402d0024030300544901a406040380510074141000090580b0007614220b81e04440f80e007095100050200e0a01e21401d400100802d2401041108100f02e0700302440c050802502102c420750b4850050913540c000f1809a250301000d54905900846d00c16900c100d64243d5441c107590603c0307148404e00302522140e50701100031500090401640312810082a50300c85005c4ca803081d02c0020111030f440c8904040f140544c0202c800c1c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 109783480 1250 109782230 109782287
    0x3060d152301060801090507081f080f03091302191803061814010b09010b07030201090507060309140a02060d0e0109050604081c0603110105130f030c0504050105010f 73
    0x5900c4084010085921024a0719008910315112030090248a01041003540040b071700181510842e03110b20300940390b22055071200c9071880001c507032081c9151280d0040c8600801c0141d0f081c000440c051f699800115141e540c1c18081084030b01030310130301580c103510600544c2c085400700d18070301e0800f5406007481030310060580c81c4500110120341004d000a42410302c8048099950551001d406018000b840042c40c4e04e444040d007620b4030200450303480785030040140170341002080180079180c03103400000754045041d50303403e00b8004268400e40200795950481018408640840c0004818030000b4044401d0160300140c443d000392130070085030030341d61039020f000c15809500070008550060200d030fa50b443c0c240b812150b1540a00144025812100e501c40c2d440300c1a80118800c5e2980003003002013088840004541e01e40000c01c41c400241c081140003e66071071003184e418007842c016441d4503a10360401082c0410b880041e4041410002a407940131042d41d8031a411b1916608940704900058809 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 109784730 1250 109783480 109783523
    0x11160902030907031209140618040c0e041b080c0a0503010e1305060906060a05060a080105090c0403020d080405010212040e060409060e0102120405060105040203060d0f031403010905041103010203060d 88
    0xa1350001440700c1c914860443c082d80c4c200001500712158010b500144006240502610340103c94451b140b20942e404035a07104e10309038101c00b2141c00c15117081a001200c0100017419900c081781c14648008295070840c960b08c1c0e000911a6001002c801c1d440d18040c1001030090080c481440b503016403107055070105618800c095180309406070004c08452190410380710b1980c07144d800396a07042c40792801240014a60810505490305005103440d680c05a81c40c080900c141503034000c07c0ca1048410400010005a031140b48510038540640c07501c9448a0814001900d060108010184c010b9401e200802400034000a44d43d0b02440c2910007081c548160328080c0c018001e0101000c04035400030952905044403200c189101d039014004894050740d035042800201c0c8400d0791f0040d0841c0c40c0e42680008603001d442918405880703403520810040142140540f0358200b81c01241d00d031500c54080c001030000c3c0e200c0c61100b251089008500d14204200000c200854622008050300003001c07810964883c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 109785980 1250 109784730 109784743
    0x8041505040510020d090609050a050d0609020301020f0307020c030604120c0606090c0e0f04020403080909220609020f0406080304090e010b09040f051605090103020f041d0607111609020309 83
    0x30090300c0540142c0c0c2104020352220b0380c5c081842c3c0082c45008000411034480c40c042802c42c3d40142420b00b0080c00d02042c441481003642060300c0b65070302c9070f0ac1940143c809100800301380038042201a128204040000d0900c0b90349805103219501035401e00c07000c11070b1450520003801031070a02048880b8589000e01c00b400c501d0744035502031480c002d4241609034001c4180382c14110101c0d11501e40f020280d00304801c9015038080074250351401e00501c421828007400a85c0c0080d40c0600d080c0c4401000945810031841000d41110144e032144100e408500b020820744002c1c00382140e050104c00e0a28418903901c0c080ea10a41455584a11b58030030f0421080d8030003003200c1d1014140e1105890070f0b05020000b404a804102c44620900c0400742d10688080c40220aa0302c005251101e1039107550200710058001e2004079a005a440400e42c04444c0f43c5055110300c648000080c1a16191444005d00003190381d0b40e0408440c1c01290a21a40a2322181c0340e8040c0c400c0084010f84a80b0703018480d80c03a004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 109787230 1250 109785980 109785989
    0x1506090f040201030e010e071502060405070b0703050706020c030a0e0f0906090709050d120906140301060e040e031b240f1302190305010b01050a020d3b040b09040804150504 76
    0x1482c00d1f45208040030f0114100d001e96844190100d101c09140200b00d0b0f445004880140c00e641006805002086000f00200b541c14000d01e03100d818580503455410882e07011282d802c9107a40000740c82402c2d035401c03a14038501c15400301c485c0d043e0760310303001d011079003e0b08000c00c1e0522a841c0d181c00140ca00307000e8400c46000d400701503c940200c040300c2c6044c00c61049600c6004000c14000703100000d00600c101040901900b40c49000f03415a441c04e00700703960700290400441e81c02500c81e8941010000204098801c600000304406400e035440441c1c0c80c00c201544101c000743e0419900105030b108010325034150404a140e00400090755440301c0180c19051070000251f02c5200070b4444142c1c50040840e40e0709407030088000f00501c4040c4030040d43d07180700340300d40c10001d42c004100800d009802400d40da240c4d130039604a003012812050b0300d1030045400000104100c4640d81c607c0e200309051512503140340403001d0b500c0d11864106502c49030354a000d148900c68504d4031081c10301c1401d13031041c3c041ea002407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 109788480 1250 109787230 109787233
    0x2090a0f0e03031f05010906050901030204031a04060f0203060303040b0903070308070b070921140106080613030905030303013002030a0f020f0a0f150504050303040b09031506090f040201030e 84
    0x94806003511a01c1e0b43c401e4a81c43c604508552021000710700142c224411114141c49042c1001d1074880140d400e5040b00301c0c0e050600d40e0900001000c10700c0c2c008504414407c1221894891400346032075400c48440000e0f03010128410320401025842c0002128141d41510398100c4e1a0007003c40000d24040c41070704018407481021511340200000c4141c0b43d0300518864031403644181e21050080440b10102240200075100002d983e4007181041e0700e0880604c1c1d0340c2c4008149652280022845c015069500b400c82c0314024081c0c0b0f0034190b003c0c03505005440304401039459540740440c104601c0c41c0151403c040491a0454481451719006100ca40664040c096985141d41414841e019030000103041e0b00030303000c000001c481e91a1048404041c0c40101d080300120318188960f0108a0300130f07a81e80d8040c014104004100c654041000e0002445002c08070b690714280002858240003034054880812550700c024000140c2c1d912100c84d50040c0540c00100c11613079107000490280203041b1490805 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 109789730 1250 109788480 109788491
    0x6090a030812040b0906060102030d0b0102190c0f0807080703080912070b0306040525051b0304150f0c050c0105030c1b0106030b07050a050301030f0206130906151b02090a0f 76
    0xb880514851145000d400c2007049036803564036054907464101e6410740180c00030446446181510703402000102410300c1180d2404040e0300c09107050304080c40d015140d805041208120051420585030042c5c1210702c060000d2618024410b40c1c2c2d42d01d603000090202d18085070100076500e0b0001c8521484103c5011511030566403031001802d03a109480b240c0c00b55041800154401c4114207410440c3c45041c00e030500c0200b01c005044403150030000107004111140000100f0780c440c00c001600c080d040320300700c031000c801280e0009400e0020320030400c070501551440040110f0800708480342e8080342824419640e640b6103405100c24460b00304081c0d580d0b0039101078681d81d240c055200c6810789104054002903078072000b00640c1c40d4081c2d03d5142000031003c10051001680107812086090303c00b816147c2003896a803501c2c0207100b1075802181c80d007030769074a0403c8003207440c00404c008400c442c180302c084d014440c41c2540ca6821002006401000c285001c41d40c1c0e0b181030380c0400c49403810719201b0480c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 109790980 1250 109789730 109789747
    0x20a0b03040627050c012109050709111b12030c070303020904110a0206010816090b04090b0408190e0d03080735180a15020f0a0309030221030606090a0308 68
    0x202c0250550042d030340c520a500c040805c0d0350044181c04008188101c480c4400b09001110320f029020740380d0300f100c2c10f0048080c009402551401030031501c3da69451002d85030000064489440341009590b031030075a2022095404000c2b07502c3c00c403900a507001407025520030312800c0a40283c400c81c04c8850300140782001c1c4c2840e2581c840d01924a01c12958250b0312241d0360b4980359907031400201184000c1040024003081050341c0ca9000c4050400043e2000c124010241c0b19400701310b80c02c60741a44d04000c002102e44110418205100041c8000d08141410020b0040030070342500b00c61000809020418000c162060f00848003100150510b05000041c080c844d900090000080301d5100143c48140002c24402a00c89601d03100c8820160000c084009613515003220903c024801181c0c040c0e400c02c10f100030b070fa20001c003e0508200300c0d10003261103201858028034145803913048408220580b503d01d82030000c800c0490f40c10841c01c0302c0f4180c41d9101c00d000508440c005a00003071a0460000d031400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 109792230 1250 109790980 109791041
    0xf01032910060f02010b0105040b090307080d0302031905070f030209120a20060c0a060b1c05010522030f0f020f0a050615120309190503030304210309020a0b030406 72
    0x10a40c1e01c5650f601e0f5507120310b80c0c8141c2c00d03034882200c81da01260f002e110500810051001801d90070350010100c866417030b500d8010500f081700c94025080001c1c0c001041101c0c051814400064441c44442d041010b4a000ca4004203031a07450440403080640008a044069440080d08038100803000c003560242c2e003a91a1070f5012840300c9411440811f01030740e52030a986000b0040d00e00e00c1c1c04160141000c001240c0e105402854100449540940c00006602d5200c2c0807004d00c0c10442c2c46407000091504060100125a6055074007a110b8070704c5003071020300040d030f201e0030816801a0b141410b940d40d11080d14181c0c28401400281502c41c46005a9501400000a481d6005140c110381000d840301d0f1441c1884030104520408115542c0104103113151814003d4150016604541c0c44864090b143c3c2c3c00079080d45c1c425182960188a40c2d10021503104d41c031001910a1401c9041c02c20265040e58003064031005117200303080140d5808800a011700a07240c0001c0c084100c0b05407545078829040c04d500303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 109793480 1250 109792230 109792261
    0x4030311040302060d09060c0c0809120f060705130e0105010e0f04020903010c0801140d02010c0b06010309060905011401270b0d0f052506050301050d020a030b09070302090a050f010329 81
    0x1c7e981141042000d04107140140540003103190804140c500d002c50500a1000781607109031203031410711820b0642e80783c101007403281500910b100d44d0b07103030f40d680d5a00078429004030b81a0011040340c1c4280004000913a0000710000e108c0800784c494509070b640700c1c1c0000d0020b000d0f100c0e0301a055404c100b0b24440c00da5028095905907102c40e8403120001c02c03c0000e0000c541806d050003404240c03008004004030f800003490365884101494080b0f151000d50b502c800a41d40110303412600e50303464007100c80c21042007052031405404200e140b44c607603170031380204041039880025001c0c14445c4e440e824003120340c442c140752602c1b407500034400301742d049000d16003a5a200c3d010198188a1240030081044088690aa240c11210150388190a59080004000162042110803a8064140000000050811002c20384101c4201010b01800303403031030040c0440b440c2c00410f41014645040204000e60321040c844c141500d82181c09040c0312440d1590300258142c0003444541c4210300702041014401c28000d05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 109794730 1250 109793480 109793483
    0x1030f060b0d0e0a121206050a0e070f0804110607060603020402031e0f060f0f120616030b0303070503030703050403110a080d0e010213050111070e09030c0d0206070804030311040302060d09 83
    0x7005000e003c54a41501c0f000800d40081c071070250102c0b48800705201b008402c44242d4540c00004840c1d036501b001644131102d99006a120150341d41c100540e064114011000e0131040b4200190b02d8a8144c0c2d40055890300c0020440c0b00785004283c10082c0310a547c03000d00510345c060811580e078185030708030403050800b0f2050300f590030181000252584c3c10001300d01e030213000c002c0c2100c90210f68440400448001c14081c00d50030254010384610b000104014840c050024003a45102001941d40c0c018180c91a040d82a4020b0b40b0810a060000700008201c944c8011140b0300002c45448510b421200c10184002c80400780c030038030f00307500700788000c42006000000141c1e00070000000300c0f0141900f070f401410001d001c0080d0400003000103502601c50b09408228600a85e58965220030a0702189203040e00c0c4a0840d500121345e411200b4030420144040c010240001c1840b49046030307004054140041c4002c003015203601900c01040303901030948018540c01480d03541c035a107021641c0300080045080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 109795980 1250 109794730 109794757
    0x70f05030d0f090b09040b040c030506090907030804030b070507080c1b040501030803071101181a130c1a04030b0705090405100501023325050f030604090201030f060b 73
    0x1c00003046801009100e450300801d031140f00f0207614120300c141d080d8002020040e041901c0b8064500c1c2c950b254031400c030407100c840e1000038450920034188000c0260041c00100550322030075042c00441e84103400d403800c495000035034000c940d441d0310044030240500000103140c4080881c1031501340c540032a110509011005000b40785092a508010940d102817201800c000304c20000300700c9076072140d6000c162010f0410004640e10401058030190000004401c0e20b141024502d0222111402242d55030800d4204a0b0f0756485042c0791100d500c1500075205240c4c440d9441a0140c58141d500c1c3c00351780c015600a945480d1518210a024200e0340c441e008452260307280500081c0c003442c500302c6490541e501a0300902119010b800d011840ca4010000b5580c0c920010307500034100b000101c0854400e5598056000030b5803108007900003044032141001c0c00b44481841201400804841641e80c82401140c0c0810602c00030300040c2d00811070068020901410700001184450b44007004010309510f902 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 109797230 1250 109795980 109795993
    0xa030903060b1005040b03071701150212071a0403090b030109062610020a030b060403030f0216060e060a21050613060b041403030c0102160c05030a0f02060f0c070f0503 74
    0x3010440340e86121100703c1c0109405100c18403945a01c8806190b20100754240b004000c000e10307181c480151b209910060f0040c40d89504c456080d581170108585422008072a50304040c080e6682c01d00d00808100c0419a44116100040034103105499140c024090a03050340c0c0d5a5845a0658001d003400b8024420f42c003440e40032160440131400183c41405141001074460501c04a02c2d5030042d42c414180241010b445184031740203079460a0061005610a031108001050308a01c06800d00388038507000c160300c4120b0241048038982207501100a0729041301e210b50f403080141d0055801191a445a15041b140c03d4040e0115440c598483c5008034801c9030780c4024050003501000c20380d0910301410043c8102403004000c881c1d008184041d00703100c001c007680e0608403030280d5030b42241c0209500c240b00100c0343c50503806101d80c0d01a100c024082c1500075142c40780720307600c0d1280300b0003417141c000340034a41c002001e1003c078208205580c0100d40720310a56000550f940404031548116000700e030711a00580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 109798480 1250 109797230 109797251
    0x10e030312040b060411130801140408120c120411090a111c0908070b0703050c04050904030c1103070602030408010c030e191110081806130f02120a03090306 69
    0x81e524480d109420100150351107980b00001c5000280646421603100c9540d90b22100500003d0030807001d10909542155140484003400d456000018403400e00f205400e00c00400c02d04000c940360780340c0c00c030390105594481121480d014400c06072303500d0051074408144001c0119858024190350400c6945181c507494000030001290117414164030030343d41c10400c20314075602500300c40480603d400c0300002e0581e001c2d110303008154061542110f01c04544010854400d800d8415280c0025042c1005030809007403c0102e04180b8000d00003909001c40c01d59144200444003c0742d007846900982510103050341d03400f01035a84d421a014600c459402c1c01035100c1014403d100700107200d600034004110b10a050402e083c640414140d0545401d40d0001c50744c0074030f807207003608584a2240395a0f40d03400d03490400e0300058203207910f40c51030407540c10000500018108008061300c2d03d91304642c91408010561000458219005000c5121402400006002c1c181c01000b40300403a40566014480340804 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 109799730 1250 109798480 109798483
    0x1020c03011b0804020f0909030408011107020603060d02150c010c080a0e07030201050307030f140105011d0102030a05090a0504060e0906101a210c0c100603082b0515010e03 76
    0x1d0842d0080000d000010034400c60b2080b04819003203030000c1c080100b0307a400c0f0300224810b5201140d0080307440c0d00002d41004a03180901c00d80c502c94135081d275480c2c01c03e216a03002552600c00980514400c0752080032540656655450a400061801c552030795295403808405000e011103003c1c00001c200c541c40015003648003400340e104080a8400030f042c00d241154010b40e00e03500050680c0c020150303686502c108118a52040c00103d01c402d4941000c5585402c000401e04201c3c01007540105039680d030003c5159800001317446031003240b0b0800741e071203001281c0402c1584206074040c503407007402c00d94001042044220502e0003401c0c86010740b0019a201c0c00c1c6950381c0c500b0342c070502c110781c0619a03038034071050111f401900001d0207088036110503003c600401c10f00c104068030800c41c4000300150016801c9010001307451042044134041c80041d1440d112042030340206e40c60b100ea541242c0380700720384d844085207107140c4a07003084c0c90030065810502900c170034100d071504481d03010845441c0107134041c0c0b80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 109800980 1250 109799730 109799741
    0xd09210803010312050d061d0106050a0801060e040b0306191b05040302010309140d08090d090602100c03020408030a110610032f030f01050a05060d0f0f0f021c0201020c0301 76
    0xc21110041c41c0d41d1031507030703a18805a80b422016080080622803e6107401d002d001e0340000b84107522004030000b1099040e0f504403507041e03101d4000d0040c20030103591a0b0350458001381c111072507410001c010b02c0540021a02600f000055550b050061900b0800703007650444c00c5000c50070f41034504114038254007c0900039103110f04079030000b143d420301041005610940101070f038580b00701c058540c0184003200384c9203803000e0703104c00c1c0000c80c0c0e0400c03c0200c04041000f03050a184407601d4100101032606102235140e0301d0114404108a0700d0700c0c800c14115000390103c0c1c00408801c0100c990311610150000c0100410b0705242c0c50714041c02c004503016900d801c5409094a400040142800c220603103014441203015080b1440d10700b140507801f615a900f0300140e40e558202c02e002083c50300d00a03405201311030000b07020a1003650000d080f2004141e042001f820380c6a4000030300c2c008007007039080410300300b424140300a501159030500c40071003072000121500228400e800f2034000100b410100741c02d031030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 109802230 1250 109800980 109800983
    0x3020303041206090c06020c0909030405010c0b0c28021203061302030406060b1b101404200d0f120320210c03160e060d0c0509030d0921 60
    0x14000e001c148805075000040840c01445440c002500d4122a655052464001d44c0201d01503004552041d000f8241142429844071402010303500e400d04010011b00001c0d01c44030041c0c41c01407140002840411000215008011080101c0c2c410f408243d10000b50312145500340c2006005480381201000c0401069030f0040342d0007017440d1161400c0d03000610080d0001001a604152035200004021140900030119801400030070340c0c2c2c0c41b0303904403081c3c5040003503400103014620340744140c040c1c00300c1c0700d1151350056481042c8107542000c500381c02d90180d81c50721703005500c0492000340d00d08208441004034a564400d42801e9007441803500140e04841e110500140780381804d81c85011a0301c18200140064a052440c038141c0b542c074400c481144100482c4c0100d000d5100105010402011317211007402280d00e494842c0700b5280107400304095001c2d100b04080c4a41d2103c0f4500c1d40075000d1004e541c4200f20240403600d00200c1c0d110014940c1071242301700c0c4899900398100381e1029402c0c1c040100d406 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 109803480 1250 109802230 109802233
    0x7152f0a0816030b040e06010906051c02010509130e070611010e060613060b03041518050c0f010306030506041b06140415050403080c0a0b0f0609060103050402190b04090c09030203 79
    0x1507840a00080d220340b0031140c00010180c0e16110a019070b60ba910484c1805180c030001425258100800c00c800c444003608918400c0d41400c1c0300c0700031888005810030356aa42840c28030346405014020a1280038000241e282c0d076030901400104080e40001c010040318416518000d104a41010990803101e90341c00d15200303a007204c00003846600b80901e603201000900b01001038029620325038029181c00c10b840840740e0f1030100d1680c80c4001c441c0e000e8049a0420284031942d18405a0b80c0c1035582c4601402d41402040702d540c441400f030b8040d6001c0c2c07004580100c00d541003442c2c24900640d00135840814010007001d95000031500070320407181501c040107850111441d082c108081825503841e044003010400401300030110000755140003402c00303404240010030242040d03103001110301038020411b50084d80c2080402010340d40d074809403500b0540a00b00000d013500c407800801d00c10306500003149114440130304000740010800f801001150b031001810040c540e90904200d90340a01880080d526 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 109804730 1250 109803480 109803497
    0x20f09092a0301032303211009050108030a12090803040503130608060a0303200715020601050102030f030a0507030905240105030604020d1202010e120d0506010c1707152f0a 76
    0x1c0c01c0501003102140f04064100ca0400f200901030101088171f0010300c40034036440c2410321044c4101c00c01c125014000621007032180c0e40c1001c0c1d1a40d07807030041819410806c24010022400b04c541d0b503000108554020402ca5a00d00e02070800301d50380d900080126582134010000020102d1290464901403072000f40482c1903d89507031411500f0440c4030f0441c07401e000001190500c50201040070030020102400b000300a1080c400001e030410744140d1046065400030032610f01611070000c01c0383d5010300340350400a116250701408400030415000f0050081c8500d004911324001881c0f0040c0038800c020446841980c0c0f5a0103050301d820b02a0703002074100c0b10700e400c1200000c080510510f0030380150701c00044c01003490b4900794075000001d900007550b6600020300c1c29031807500d070081c11b81c170605c2820070981550040d640d103010000381c0001c0d060324100c0844c52504010720480120300f01c0c1034582080c8254051240c1c55035054203104031b0b800480005c440030b040303030041c04002d0341d045281c951982141c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 109805980 1250 109804730 109804763
    0x2090f0f01021e010e070602070602070e01141002101a030f010e03070204020a1e0f140c1e0109060213090b09090309041d0f060a0b190306020f09092a030103 69
    0x724400081541c3c49540b5149030044100c0104041c00c001c00c1e10f03074028a00640343c10400b81c18003038190808040e05203444014030100d20500381595840760281d0350104203902082c4100d0600310164011801c00d800c1210100c01c85552103c2400a801e00301d0541d4502200d00074034a01301c90b0760048595003a04103000000c00340c6000e074080c00c00c144c02410009401c43e0074102940c01240c4801040c00852118121340101680c0710700f0726440d03605012117603440c00a800b0380107075940842c1ca2030402008051480c0b94a1228207400c0200c0140d80044150740750542924400140003190141c6880645080c00350035007840d1011096010f44c403100083d40c40d0158000501004d442410486079203401c480a44c039a100078200301c3e60495054a601a00042c00c1c03550141c81a900c1100030717184501e4404016442c040400f10071501201da00400040c0d0f42c2500308a07400e2103010f001d9003140d01030400c100f000300c1c05200d1a008094904002034404c0789030b1144601514600007800040e14220042280a4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 109807230 1250 109805980 109806013
    0x90503011802031b120f0109032303180325050c0a03031409010215160305070503010f0e090c150310060516080c0a08040603240b030601080c0d02070602090f0f0102 72
    0x3d9a002019040120f280d4420035017500c0e0030520790020000381c0d5591500c1040c10b9100d2100c1811050980300d2005e481058604010030f40400340400c28044011002034445c000c0810466654000e480c0c44d03851400e100e40054140181e41b140d081d2182e0041000921851a080451a05813075254690040c0c1c0e5540b451443d00d01c1e0020b020060540c03140300182124071408501c2e02d0302c62034803600043c00171794220000809a581c064003000920405000500040002d28100c0041d00d0050b00003000f5551440d0545103002c2c079024495800502c8088207856000c223201c021407090424001c00003900b5a100001c445500c101e04008085807505d42c0c940c2c00081c445001443d29501c407004a81041c0302548488540d81d00c95400300c4082580c41d002034060402401d03401d0780362510300c40d00208091a00220000d01c1c44000c00b2541004410710025580c0c0014105036110114032240454a4554610300b11000754402084d05114486080151185241500346219820010390141400f8891000c1c000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 109808480 1250 109807230 109807273
    0x9060129030f1504060605220b07050706020f06011208030a0906060807051519081b0d0b010305090a0201020d030209060913060608090307050c01180b0a09050301180203 74
    0x405403095090310000ea08009000c0c5002d00000c80e180126410881820030452000316001c5005038100300c0c0410000760400c051700c4600c2c1840c010301c0350070b1820109102c0c4e8860a0f4110950100c8089520005d2020024260702915443e4003110b402c00410310303056a40744402d1040000a1410418003000203240c40301444e0080b5001030003044035a41651480e00b61000c50300030003c2c56001090801c0145008403616a040b082d042d070b041c0c54000e868100207040102c1c000d0000c280207440c000328030301454078050350408182044905403102c0c41c0000341c0000c1c058070480c2c21300190030540400d6a440d00454178040945d8160005d00081000d080b05a001e0342000030001d600020500840e0002d4640c802035072031400300f80e00001903483c2081c401805142c1e004d02540f455510a00c940300000b140000c4054043c0c00908019074081c00000502500170a2038020400d1031201055081c4810b4103d585417040c0c98045000b803110f01d01d24614800481700b1070202940c55801442071450420401880d0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 109809730 1250 109808480 109808519
    0x1080703080d0f0216060c0e0f04050705041512110c03030411011202070308160e060f030a0b06040305060411040e0d120b0d030203030a1b050306060901020703020307080c01090905090601 82
    0x100c3d951022401e21012600944803440000140e990901d080140344d103e003200303100c01c9040c4050303044d0341400030440a03080c1e07a0685000e9039681d004140e40c0e0b0b018030280c030024219854140e4020044903030081c4103840c81c4010b40d11450805c5000c00d8036022410644a42484d8040110f045503115100c00d034840755103148040c18026118200041411107000401c00e50740203858107642400d26021402181c0f41451044042100c0703050302d03074a542d98502c120f40d441525821410f8480d10303072181640041400e006880d500c03400c00240042003003404100284a00c3c01462410058580e260070310054483c030386002c032515000074000d800d0440c000c0115180403080180006802d040c1d0313201048040c00d00d01c0040c9c015034004000c01004c003900f805a1524001242103440300d1100b5254080c1c224000500007e1040101284950150344200070010096400030201d80e01c9941e181100364403043c03844016400904607480100d001d031b219020f100e015580d0b802c02014a40e182c124104c00c4500310795031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 109810980 1250 109809730 109809757
    0x60e0406330e181005030f15010803070c0605071b090b01110a030f110f0304091d01020a09051c0b01060302043b04080d061e14010906030f0204030b010306150e0108070308 75
    0x3c0110317032a2030030418030884030407000051001c1c0e00d001080d0105110b0582c0440c1d031a82c000c00068000075540a0114200d0340141040f83e21204189040000c40300b101c07541c03103112002460001403118a6170480703030b105c0c1402c3e01d56900e141c0c000c85d20b032500c407000c421700a00800c1c510b0280c039010521903002000c00d14600c03000e560100001229880c2507a0081c0e00c811401c0c2d440345080c0b601260030900f0f0707120941d0540e008515081c07054401515030205032141c20720445a982d0080e0103103218486e20011135500040f40c606568480f170020700250400c0c050400b2100d503040020505c01c594402410f543c60340100a01840e0744101d256440b20320004004943d00c80050040c0c1e803440b04207004040141142d000416207040c10861114003911565001c0f8000c0007040b8103e02142e40c00c00407810903183c01e4600403d1001c00c060032000684265030006060002c080d000000b401016400241ca8000c0d010b86d000c4c58a6541c2c5008001c5034085c001c1c0c204540021900b000015081300040101210300b50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 109812230 1250 109810980 109811011
    0x1804150207080c0703030311030108060103110a03060213080d09120f1a0a0504021003290114130f081c030903021c020a0302060f090304060e0406330e18 67
    0x50b40c0d0042c40d0440b80c100c07240390380045800d0042507054003410b400b101020f116617007192315160354030356207020620000d42006900c452011560f141c80f429040516000f80080d0754900c0c00c0f0031100d11401c014030034500b0340c1c029100025601031007003822500703c542c03015210b2500c02e50b40c0c4581d2400b220340c0381e0803030750b90610384240c103241034242c4081440f1340c081030703800101d524050051050401d0783c0f5011108161820840501d0b40f01041e5004400d00b10050000100c0c0444000594426184403148030140c0400318145030541c0000300f0030429034114030403014082d40d441543c00d03501d50b086d40040c010780d041084a45074a0b84a644005c3c0e070303240248101c9601461042aa20401040500c01801078010310881424160100704a6400c003c0038180c5110524100c00202e0312400f444c01080704222601d600841c2e00d40d50b80d003000c405005103d021420400048107a400740c441d050300d00c0b110901103100e5010105001c1d41c0115000200039004a819000c002e180c2d11000c0801042071400100c00b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 109813480 1250 109812230 109812233
    0xf060904020d1d060f090d1710050a0906080c1005040b0f22090e0703210c080f03040309120f060f0905060f0a140c090918030703090e01051804150207 66
    0xc4a1400c0300c1041e43c0280006040848104490031707001010640e40382c0c400040610b155078000c80b20700071060454000b40d4951605054406000500d9000b140c0c44480307020b020840c0442c650000c8100c5050500300c8010702d0140040c0440f182c8500701103008500300744401c100f11b041c860000e0915400c0509241e1034003102000c0200c2a80781c012458460780e10035403050204098901c03e85425901c92002007100c2895030303032460f828040032038544903507005030402c3e0807400c0e00400c052080981e0188090345c590440240c90303061500100d03000d40c0001d802039400030b20004104605100341d9084601c4105120050b1101406059580500f004160b40c825151002c950107004071402400c46522081c250305103041c001060302c4034807503900354811890003031001d40c4c0084422203080c1641500e10301c00c81d80d02c113030801c103454102c44458001c5000c0005e00c002090391003001c0031700b510640c0d0324080c00c90740c0f207205010300c1021340c07034000d40480181000301d4003103003091015009114940d0009413a00a49 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 109814730 1250 109813480 109813511
    0x100c1a09160605070204050a05040c091a06030a140601051c110c0115050109050604140d0303090c060f030c0302040b160c050a030b0405060f1e04020a0f0806040606050f060904020d 79
    0xd0b070b4016000076a003c1240002c61409014040d002107624009010a0a00b03071150384d41d452291081403c0b4940d2000c01d2010b0412040010b801440000d21180e201d24045001d100500766804040750b2404c50100025450341c011400d503200038000d00e928010201241100500401049040040e03140047c84a05c8640009000d00c4207800c08080d440d0729194a0b0100141c04029241c0246200740b06c11700060000780200200c070303200d01001702c40f0000d01c40141c0c00d040d0b00409000300044c1421001101c007144c0603400c18044c036200300099800700f158640c5a0f204800700e0055005d0400440d41c10020310680c0804103d5403640f07203000d00c180c0100207580d90005624490254411034111408030100018802d081c00b4080c0c1c000c1c144603104242d031801c60306910416124620000701d40b81c0440104040d510f03007081c818054104102c2454100d0384a8001c030b5540c110440f000c54066040100104290a18a25a035031502c0e025206500740312000c010040a500310841d0700250b940e41d40919100600c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 109815980 1250 109814730 109814773
    0x2072304020408100f02041a0f04030b13110103060e010b070c090204090c0e0d030c0f06020405150304050609010e0c040f020910050408100b36090606100c1a09 70
    0x700402001c59010b2215440280c1e0703140001017180b94410b000410030802d1100d40b803429400b03400d80305c03035442d684a681c8038814051908042c041c2c160403400c00c180315201d40b034120300e56801070707200c5803005200000440544030350707002e811105e0010704010841c60315508060441e1030700c0f41200d40c54954550003401e04a8115a0040441c1da40780e8295800407908403080c44496001034038910150b61302514050400003030124002c1c04019610030340b60070300c40c1c3c1d503040e103002e45002070400c00e441c080b20b200d640c0140c00503035003030f62280540d10215119000500c1a1004048550042c000c040c0640003004002c00300020000420ba0f000c210440082c0d84422140c00310302120f460b100d4030ba5007032600103440c11805110323481c0002e140c841000f02c5070f6102d501911100980c8091103e01100044800d01110034071030022581e441c3c45014403c0d500740104529115003410b540900305a551a60201c23040b1112800242c413112002d800d42c8940041c00050540c440b010340708880310241c15500c0c0080f07808 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 109817230 1250 109815980 109815989
    0x10170118032a11010503090708060a06030b090604030206010311060409050907030501050f010602070b070201030b040207150e0102180f010e030a0b160f020312040201120204080f010e030703020723040204 89
    0x100a1002012803107004540c03480701c401032094124034031030a940da03802001c0d455640c80307040c00360110005910303240c10408e0794054031301041900c100303060031807901d03001d00220300044031000c00047c001030302940d002481d42c0c81540c0542c000c003896461a200d20405040100c0c2c21a0840001c0001103820101402180d0050702407200414107545141030540c02c458029051461071102e0000401145030b0000b0b140d82503407a2000301c4d59580840344016001800b00120b482d40280c0085044014050030b500c2c0e0389840c40311484140f00050600340040d080b4802c0310344000c01a041401101001e0a25501e918100c0308107050204074952000e00003450181c9214084030070940740820046440301c041c2101d0004555400d02111256101c8030281d204c6c0a40600303030f000f0518000014040d603101c0c0d140d40d41281d40241045558039200c0a0060316101c4441540320b01d5820020001c00d50b210010071501c030039405601070f2200305c2c10900998140704591303115081503040c100c400c4405035075520082c0000d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 109818480 1250 109817230 109817237
    0x1303050a050d08070206041b0f090e010b0f0102100b060c0303040f0c150c0308072001020901090b070b18030408010f050a0506010c170903031903020c12031017011803 73
    0x49140e45071503403501c010099044200300303003076092013549034001034000c3e00168440200c8111911900c11031001c01034135806410816482400054080203e51029138090f565200900000110000f88180c4031505284140146d0240c482d0f100e0130100c9a002d1011450010080362a0004512401307203990405e59081d034000a00d070700c0d8082000954a0403400610080c021441c02c0035002e880a40980381403230020b407d01240d0030000355505e00c03441400411071010029640c5101090b035415000750001d40099000c00c604440118403182c040044d101c40d107900401101c5940d03a061422411408820081d1066100a0001080c001d5080c014141095880d800020f080e01d40064002c007a5070010f08950f05000c078010403c00815500003020398403080c070100b040d60b51381610380442c0c038512840c440c03442c02500140006140d683e26800800d00074106a0454a4205030051280782c0780c44103440d0f0009503120308808010707a544441c1040c041030224000000c200d5611182080104008181280007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 109819730 1250 109818480 109818493
    0xf150506120109020907030207081204030f02122505070b0414040f0c0c030f09050a0e0406110301140904030c0614010504050c0c0c0904050f0703150609020901050a0311130305 77
    0x6400c00300000252400d0003002030103d41183c1c0c0205140c1040a00401c0405130001071040c00c1c460a00c00711051510402c000c0c00161809080c01403242c0c0b070850801c801805540002568401e44d10300355004004210201060540041340503600b0210f820070031a468000d800d4000303901080400130704024508860b0107462480010300f0042100c7c1c40c0f001c030b0030340d90340380c041b04807089540710503518406581414040040041000182c3d2400001e61040b644140070380404200e190051008a00071403103403005100b140b071000a180e4841c0024041c500e954441e11620414628203400420f030800d01a040c010403020540e1200070980b00b0100c1c83c0307042c002144004001c00d00305846020b0703001034401d01e040e05100b901e94a80740c4548000c49003500c210812004101404014010a0122420b00c000c845099550349040d507101d035000900481058500b01c4002500502030037120a9140d05030741e01841c1241d00d41d0250014030a043d414210090103003c9819050140c0c1d01c01009180601c00401340c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 109820980 1250 109819730 109819741
    0x6091401110d020a17040308030a11040b0a180602070513021c0603140f011a04090204060b0a1e140703050c01060306060b09130e030f180409030807020606090f130f1505 74
    0x186141c0c2c20480401703040421080000c5030440d02640c1e080711a603a40800c40004502c60180f4500170794111880207400083d80d001c04941044004a010460310041c0702003d9030b900042c0d840700154403ea50700305069141c00888000345a0041001e01480404100864461020b110403907070035030411900700c41c442e450352805210401200726072640e400001d02c80320130028251b1801c24410f107680c41c0036917110445003046640e15005207018040c600c1600c0d8885d2010400106403191217611107401c4200a251642e03000e200752003132552420440b54052501c585582d00f210158030508030724219540e0703110088000b40d0301d401000001c080701500580c40d80b81d14810002240d0240e09464421413501c03104100004e40401a50b0f541081c001c00386440f40241c2c850f07080810152400c40c0d900c945000098410035400025050041400c1d0b82118031580d522414001d2a10b001c2e82c250f1425000c0701c0020303401c07030020a04600c403944030300d030300c032180c59011754480d03016580c0703850560400c40c2c65070708110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 109822230 1250 109820980 109820993
    0x706061203120e070b04061103070b280504030c030c030c150501140d020a0e0601090b1207080603060603061b070807060203060102010b031207020105070816060506090a0606091401110d020a 83
    0x21154410710251005500d8400c2e01c1041b40b03c1c510440c41403240650203c011682c003441581d443d15040740702ca0200e4a41400f110503014000315444403d28051085008080c905e8400c00d80705d1941a01d544680402d241c0701a107002c040340c4801c0301003013015040d070000075841c02c0d180345101e000d000c4085255418603050400719010341c00c103903001c2c44000307400d01c000d0f98400e0344030f000322500e001c408541c0d0b03124140100d900c880960440c902002002541e10030a107100050248035003000c0c0e5420ba99a1503620402d521540103585460b4103a100c0b001060400703d5800322102c03414090349038185031809950b80c0c804550003981c1c003580c1190703002c81040000e58081c0074501d4180000c4000d032040b40c0103000a10018000c0450107410800041911410010030008132170344c286002e01e803c81c0c0c0c17080c1480c0807405000212000343c01041404081115121240584400d640e881e80b6006905400d1401481740c405030041214100100c54241449494040c04541780701d030381d16805000309440604008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 109823480 1250 109822230 109822241
    0x50405060604140103080a030e1605040605010f08160905031905010608030705060420041410060905060901030b1801080a03020c0303040303080115020f0105091f0e06010b070606120312 81
    0x14002d904002c4031101c0140031105079819207a001407965101c030b80070035085000700340c1d041852500e40310308e003c84817460050f007840f40102e071802c0300c3c2403200301e40b20401144c4614560301c000c40403819400c0410030302900d80a04255130340c0d1034074101ca40190754500003450401444516440c0703883c422000d0061090170f0140b0710123020b05a0007113140c0402039a8079540d42c4c07001040500b0423400001d0a403044d6110034403640c0c024000030400c0c480200c0518010580708810f40e1400742107200e000000a00f680a0400d810880b50024006404c2c24000c80c01500600041c1d42c005074440e5101c0040703540c18545551301400707001020b006040c2649070b868083c4c03800d94006141c0c0e20036801800200b0010341d103c1c02031030561302d109051098041c4100016450f01c0341e00b0040840355402c0904001e10000e000070307403540d00c3c4031a00341c040f180c001180c988411103040c07021400301504003200502035044400000c2900c1c6100c4c0000203a500e9a800000e414075400110880004510060602441c00b007070198 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 109824730 1250 109823480 109823491
    0x14120409050c03040302030906180316080c030606030c0d02040f05101a07050309010e03160602030a0207120b0c0901180306020405090c0a021f0e03040b0a032328020d05040506 77
    0x30705285081170344010390740340142858a80300300800071f80000380c5008408901d1800f00c02070200e51200a500c0d403203000e481e0450243c8440c5205c5d4010801251500180d41c071300850340500940003000c030b81c50a0000d514000a07082c0d03006516071070007040c0460343d07118080c4a8a152a200b01419050070114108803c001039088895002440803001140010044a0b1104d0090034154242c0d960000403d042107c07503526950782e600e0b02400080d5042c0c0100040c401104180d0a0b81d08554841140c400e50b0014100c015050144036000501582e4603071004090300c103c141081070542002455a0003511040e0300112906d9802090800c480d041c8407000703036000000494140d0a20b51580380c02556120541c62048020304d21a40e410448503581c1c1c008140e0341d0311441130704c0e82c0d1a1281c0c400f1040d5845144c00c90700092400c00a44018101500d4041c048110090451516100c0c249401c200c52821050904e40c12040a0180140e811a10042c5942a9102000f01e03032232605041243c20310030300400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 109825980 1250 109824730 109824751
    0x220302040509070308030c16080c0109030810270902100c0c06030509061b0f040e06030c03030f0412030210050403081509060a0506030a020d0e1f061208071412040905 73
    0x81400003880030400d4a9200215002880d11500c10600c0529008230025004e08940e000007201981004107400c40c0302c0305402522001c00c40d031644aa0403000520611480505030302c1c40c5404480b10030130054181d5904c00c06140483c41c1041030b00080c052941e106030b40804a120807000c0801c015050083c100144402d0130104030905d851070500c0d49031000180040c2200c81c103154010034a45030103040d10b4103040038a85054950b40c036018801800302090360381621034800e544a000b61307403070004101c1d0340e05003090404a00381450840c06610021038074804400f907000740d5003003012040940c071446210324003030fa07207070081d500342300c2c800c0380032450160506406001d4142c00c11960b42c0717031181d410f800c945054507101d40e05d68a0001d040300902929000301101400c1c004400e0030504002a400700c0711406000c001c030f011036028146003c58189100e03800c11010700300541c01c0440c000e08054200b0320301418086c0c505500d88600941009080e500b0200c44500c08a818025445540305095001306004c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 109827230 1250 109825980 109825993
    0x621020a0504060f031508100e01020903030717040b070606060e1f0c0c030b01120b07090509060904020102030c1c0f1803022421070e010c060c05220302040509 70
    0x10001032461040b400f6000c1400310b074180c1070780701910030341c401e0403008060070703141c10b1154851081c180c45941d2805802c140b203042012607030f07112034180308840078070310001c0045241407240d1b6a284411030700380742598209202841f0028050300d40d40003c0c201d051143c80c00007503407410810003910b02c103107141c1c0ea40d010b075143d0341607200003a1110910754140709242c107087c1580c0c4a03524104144030742c1e540009006483e46000024000810754854280d68800c0581c105ca0703544044e42160640c0c468841c041d48104e8980100c0c03094109035043d640c001d401031054030f14100a807214240340140401ca80900c0381031502c6001c0b640341e80034000441000342e9240100300c4286a0104940c0e1129900000c0d10401010010300b0000e8881100307012451500b000640d1202c0380f41403486000541941c4441550300d4080c001025248259200080d2001c143c541c40b100d5109a02d4240007003490841c0c21040c0101080840c4803010b9108041202c03422094101d0186811403040c802940d0029103004056030294 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 109828480 1250 109827230 109827247
    0x9080606090a0f0b04110a140c06130f05010c09050306090706050906030c090d050d120b0d1704120b06100305070912050304030b0a0209090c041401110c0901062102 72
    0x1040c85800c09a521408106000c051030b03c070005203015110b040e885850000d0301700b8600b0484001d0f0091580c6510703080305068144504420324803800c2d1400c80c1d982c1028000440c0c10b0380b503400c3d42c84124018403514400c502e0558905003103c6900c40b4110218003000d00400c1246400c001302c42e0320100050240030340d1480d08102508501584620503c100004400548803002d01c81c251022018001c1441d02c0c0030340241489611500300740e80304c0002409080c0b05021a44242c06081c04003140a080f240000404d80c4030321000200007902e00101d80020000005c87c0300003000312a2421f8000c5d040e4100b20308200007000980c140082c2680141414081041801c9402c0112202258005042c5d40134516003072814605608c503135000100072070b201c40d050042d020701c61780c09881420415181e4a075680c03207141c20300a07540540d208a50202800d1542c00f800d0754410f200207402d009203082198440301500c00020103403002600801c00140d990200540004a0f86110006140040c00114030b007800742c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 109829730 1250 109828480 109828489
    0x1020c03040501030b0d0204110a030f2313080a02010605030c10091a0c15191505040b04020c011b0210050601021c020c0301150f1d0103060506030f0a030c020109080606 74
    0x1c900c10303541415541d02c0780300e8035501c9214841c0440796000300704010100e81c91f54548002c2c0c01021192002919000d9007140c01000e5100b589034152559400024904100140003038420004100094074460054040c2c000307080500500103603d03690b000401c056051000b410724080d041c3c91118840c09010040c01075158002059101303880c01a0301d88250300c0c628242c2c14115226000f0a003101e449440880381c070510180d01c0d21809199a03180509251200142000c15074001480d5140041c2901e04200100d2038541c2c022001040044e1001d41000d190070043c500f10b9114000080c0401c0c0c54209804245505000300071042d4605801000320341080c5000035a2180d54580828043e0350f882c140c1901c0c2ca000f04680490140010f000341702c0281e0f8840c0501620549220300e414a540900b00450340d501492211a008502481404800d070310703503103444028210182c00d035038150084200703180c4010003d105030030413035009850308000041d1501c0018004203250740701204a812032300501826565 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 109830980 1250 109829730 109829737
    0xf0201080603030c250618050108060a0306050c03040308010e1302060702010909180c150219080f0708070c050f0d02040507030b0d23030403030c0609030216120b0901020c03 76
    0x1020300e03024a1940d070305000701e45548a4482500701a21a0711400c81905c2101040d0301284403161075640c00490b82d51000b174450419182c1d40020300740103c0b0007801503500c25080907a000f02d004207070b4403616076030f6124042126407c0c1c448030145a400800c02c8245508040c459004100c280b4403400246000142d10400900d501d01c000c0c03041900055100c25a032140c400349014102d40c6200700b10b40c0c004891b619031a000c4c8001b0481e480c01d0340340400180038200c9001500d0003802034000d44104c0c000101048080c00380440c080300ca0000500c00c2c5a498807109018081803403182001990303580c90350403d6803c9245031380c4081d01c13601800301e0715402a101d0b6003103000620b5041d103000c24181c845200980c00b400c4284109038000310f00c00400c1d4107003d410350300303051141d10440180c804210000c000d145c50b0300c07507804050003180004098100040b155440400081d0103441500d0350102c00340c075000d5520f078080d4003034020540010766540900440e132012680001d070000c000c5242c1080d105442d5103070301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 109832230 1250 109830980 109830983
    0xc041509181e0303150e040201030f061d04020d080a05030109060504060f0b090a0305010c0c0201030b0339090408040626151c060603030807080403090b18030109030801090f06030f 79
    0x2c480700e107203010035003e900f0150968803064140300100307854407411072460000300c4090340080e040074541004043d0900c81c0c4001d4a4140e80c901c9004059036020102002000d0030803600010094802c40c0480d0004016116a54041d615203070760707516110340f1800744c4202d60403c501c02c51520a040085031403c04034001100e00060b43c0c5626811140700107560034507030782e0004d040355080013509041907a00c43d20710603085100740c0b42046007141310390500d0707500c0f54581103402201801302d21492a41810300342c1c0140d00e04841c0340c052740e10040304000c1038140e401601c0883d401741e0045130510890350419580380700b400c0300f03800c11560440b181d060781c411000b000d024646d4021034042c440c0403d84548980c0e00c0c1c044200c50441149501a14005004295500c41074000074040c40c08070f01004d1080501901940d050b54500081c1410122072450a6010501d080e4020314120a00c00340c40d1000e00540d60121300a0b00c403d80203624002140302070303441049250300321a203000c50500006a04600d22030b140d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 109833480 1250 109832230 109832273
    0x50c0a14070b0115030e03190e0d060e06270703030f120216060506030607050d021605100c030606020a2a030803040f03020c040b1e030c04150918 64
    0x988a54010285901c100c00e0040e020000d10030011980710074802410300c00d0215940c00300b117042020000561280a040146000c440c80351501d4500c087c03060740c0108055500400540240c80b16550f048211003241d4000c034999000001004810840d18141804000401e0201544040d410180603200c070f03140d010007030a00403941d130401d000d54841e5844070f4443c040c04404569a94080682d0b00e00b4800780b18048a0182c2000c0006886040c049101406013070355458503030a0a00b4105000083c1d0860500c00c0300840d1200412070100d9400c112040000300c5c0ba4800046242820600a06851130364004c10155480726601d240051054404091602046801c000d401a400c01c40d040c01241c8952010341840404001d202c14001d494040600e15840b03a001c4410f1081200184000e031548002902d07405880400d0000c441480b540800280080003810740740803044d1200010101e603410001444480b0340c4040c280004040e03441100f000003800c005480c0254469036550a08450458102124 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 109834730 1250 109833480 109833497
    0xc0d1e06020c010608010510050105040e07120902090a02090307080708030f0304050705090106050c0d0206040b06091b0307020102070c050f030706050d110a080402100914010f0210050906041203050c0a 88
    0x3408090707816100c11408000092242c10340da170110382e010300030548800000030b0b0640400601580034800b183c08030340c1880e0441090b03603903800c81a42d42c080b500c0c8189042d15107038085140181d5500d043c3d5481245a40300060315500300b0000c0c0751600540d900a0303011603001d02001e10003000000306a80c010418070f00321a0307803070382e5914182e4201441036001640000d0104000329510b50807101501204d100b4a0880d00702926043e403c90b030701c0070242c0300500f0541c238000200d02e450804000ca00d45c00122100c0400d40c4003080801c0c071325181d00440c0d0003c0103035404100c0314108000100c01c82c00811089843e41c00044058000a0300d6400d60b11524040c087c0000e04004c04170305941110b40320303440044d0043e4a405850b400909401d00403181244203200640c9800c812500900e48035003540d0000c9515502095607000540f180f20705802c0c1b20055103d0040b16918106580c0200c6220f01000b001600b0300f81000d04c0d000c083c002d0800c8401c0d0505041000700060347c045d11043c0c440001040c64400705 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 109835980 1250 109834730 109834733
    0x3101712190207090606020309030d020712110303090a0902040801060e040b0c0a1103040605030121210509040603050109060c0f1b0218070801050112020403110402090613170c0d1e 79
    0x3e80481588074030302482c18940001092500880a002c0c10340c402c1e025140d0300c2c15008001ca803180703240d008070500b081a900521012400034284c6020302c2001408a92400701e0803030010301c4000c2a80c0c06540e0306900051300340400c00080c05040000c003050900d03400603080c0f41e543c100c15080001c10880f8546030100e401120b5038030a070b041c0c1036003100c0710058903602c54864800900d9036000b4010010200e01e03484102c40c1410700c40f00e40c3c000d200d400500d5801d003450080410806004048103c008110742401100d41c1a500ea114242c01984a60300000d0b1101191500c0010749854180d080240101c120000c0210b9403c080c11018142d0080780701d000c003804030b100040450500509004201101030b04000c092500418424162642601c1f121083c10807905d40c07005038400d600000302003c3d20b1704003c200c181400e401414250720000c05c02400c2010b02102c900108900764001c00c2009c442c042c14060401d400e00c000100750300142c80c03030811490b4540b55011504400c0007178166582c10103401c0030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 109837230 1250 109835980 109835983
    0x2060d0b060403050a020901050d021018170f1002070807060509030415020a030201050105030f0a0305030901090f050307030f05030f0f18031314040917030417031017121902 76
    0x1248030900818841d1641c1c2c030790400303031307669860040c04a00401d680c100111701803805c0d001131032002d980240f0544c070001e0031503002c03200064030341c0e1513403600241128081004100e18045910302d6050000503d9040d00a0110b41c0c600070914a10301186481045001c010544000440300215000440842caa440d03003909503195110f2640a02c0107400030200013406660f012500d010400c2c001e600038840e07030340c8030f20815848640c5043c2c2d4030700e20b600c410766180000340910041c66104800304000125240c56803981c034001c040c0100d003240c4a4000082c0c0904154020240045000c00c52a10900b54074000400c0341c0350550203080b480e091100d0500140c02e014041c42c0d0a0041c0c0903460599841c0c100c0f907030000f062045d441c00f41c107104294013407502c09117040c0391140c055416008500201b101c064000b881c00c0c554005007003540c04019009c8500c4c50440044011402480c916903503080151428000e071104d5141c10608400361b8020f10034101d00f40c0485130940d042080d8581c480e44502000ca00e081c1d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 109838480 1250 109837230 109837241
    0x4021002030c060403030e100c051b011d0102070b0109050903090d050c0d050106061103070f02010822120906030911040b01050c01050c03070e1008070c030311120402030d0c0f02060d 80
    0x524856a010007080580c5604920042d0007e40300f00c4803000001c59216040d14440e0b10b80e00700107030007407001e03907400040645180f0004040c42c3c00001c2c642e42400381c81901c070302681e1011003981c0d0006150820811510050b500405d00903004200c2c9060056249490b0300c038440045100320714041c0c4510a0000c144240b1580c0a0010021054030495260260107003002d8403c00d40401c0e0082d880c068050804001c55407503961198180035a640c01c0d0780151107620b0b01600b115980f003940115180040210000d1001d540d018a10f56041080070000c002c20a01c0683c01c000101420001d0080c000380d2001040071488204960100300b41d0411001241c4034052000c00c10003a60800041c0f040d500d07036140045019084030b503210001080340d20140030500f4000c80d0501c001903006e030b001a6050f4810650329614512034036010848129118400020303400c070515003809111810184811840c04000401030300a050408144038105038550441210607050068007880d40002c45203c010710940c004c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 109839730 1250 109838480 109838497
    0x3020405040504120e0a03170c07050907030506030712051f0e01060e04060621030c0318060e030f0601060909050405150f0703150e0a090204060312120609020901080402100203 77
    0x1044145807904000b41360100300210303900440d0820a00c0304040c02c021103800b0581e6040f0b00c03020b800c10010054220240e0060041c2e500500504201181e10395850351030a02842c541c6e900805e05007811810142004050b07408440451040041d040025601080325000382403100b08100e012444000d02d58060b0a000c404100154070b40700000ca11030044902540c001c500468042000c2611742c4040280f4182035602c402003005054100b00000c1c2c89040390100a6101c0d2500071004500031441e030400c01e00e42d0f0001c1020174800240035445040c1041121840e60144d0020170055140a10240000c02c00d8004c5500d455160b03400070342484170410041042d90350081c0103e8041ca0460a01544584281c0e29000001d05120011900440d8408444260340c801340c504c403003945410a0040003040a800704907042a1240c0c2d0000214031020921031401e2103540b1198010002040044100c3e81942c0110800c14410300100d8142d0b42d00000c050381c4181c0c16150001c645614040070ba107940a40504e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 109840980 1250 109839730 109839739
    0x30c0e03071203080609151207030b0c0304030807170610090308030106111b03072309040c090b09010e0606070c1a0d0c030b150904090c0e090f0d08040b040303020405 73
    0xd00180c0301190000c1c500100f03002c1d0f40c0b6282162a0a02004070700d20055550112200040192403400e01d0440310700300c01c034140107080390f07141a9070380d98800741039608607405000d0040120400c801e05410940d0258801c03040d150117400b0f41c00e91145c42c0b180d032502500e0300d4002d0300b88006100d1944d0141082501564120038801c4e01d9607500c0301d0040040310800844002030080c0580c02c040d44050011f060b0820100501422006040c0007156582d560360b46d0816042050811403902d0503140c0c4a861409030f406030f00e40c4150349050255050a44200b282c90500400748040108450b031030417802d00341c00440c00c446a640e0f42c44213040542f0048840d41002d2440c840840c16001c00384003000040c4a03d01c4112000c1c022004914000e80844da2803100d42c980009070302c2c44c08000030401600600b1601401003000610400c143c0b2007007201113517500846043c4080d00c042c032814400c05c0241c1c020f10388480c070040c1840c4954200040c02082e010300020161000040410101400ba406a4014150150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 109842230 1250 109840980 109840993
    0xe06130f02040602011d1507140a080708070c020d23070905150a03082a010e01050a05160c12200c040e070f12020d0b180f01020301050f01030c0e03 65
    0x10850030096001d88212009580303003180b0341240755281903039011a2100c0e500070f0310f01c00100059550300f640000300800c0c02c00000004881078809540c0180c408602e20755a0a89240b1305200c0c09054800040e00345020710504014850042e40c8400d1803140459108411841103880034400d400f40b0140506140c400340200500030400007040c1c0d00141c450814000398904c0080300390140203081c0d00500010b031009000300a2040c6100030202c12224038070740c09105001c0c1e0907061802c0390848640c581d1505c55a5190420301032210410f01403582c00003064008543e6000010101504101303688400410766204030140d204898029211201e0010f4199024900070b07540300c494685418200b509ca520491600d030740b404c0c0a01c80081e10209840325440107103401030070b02036522a5043c64030030417a41300c0c60b6041c070b000004602000d414025900d010705805899000d5004509110254140c07022030b03072051004100e070360344101c5006078a0b1002c0c01e00040032440756108545030210001025003511450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 109843480 1250 109842230 109842251
    0x7030507230a0507050d02010801141201050c120105040218150405030d0302040305010e061014150f071e080a120f0c080702010f140a0e2505010e060a090e0613 70
    0x441c02d040e25a20600954114645800c10400000940c0d10081d0003e100c0382c005010340c1c2c0300320540c2c0140000081c101110507001501c5242510011500040320000c0400e924604250b246469805040100c0342503081030b00a00c0d1220290301850f03d00361046a19036091300c80007002c00c1c2220081c000c0a01071f00c21110305d0090103006503010303101c211034941c07a04541c05080240424031768001d10359203035142c1e4840d181640021140ca01c0e007c5065102c0010803503e00d021000100601c2a01c9100700c04585400d900e040088085031030540da5040754150f00e0250b000510003508991019006003030420815058189210042090592904c031051a00000442640d04201c0041c032600840d4000e2000d0020a03000e0020359034410b10400b09a000000440d5000f9140d40003040c0c440c204004441843c1d10060251191500e44d407244d08050264101c18006568411032800c040e0006840051501160202c002c207a170545204070040c2c0c0034004042609551002600300104010060510407280034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 109844730 1250 109843480 109843483
    0x9020705010c0e062d0d0501030b010302010f02030f0d02030403090503010e01060e13020f0d0201020a0b070f030510060804060b030304050d06021909081b2e1706060703050723 77
    0x161040c40000c100d442c3c81080080c81d0500c1154403074001c0c00b2031140f0b002941d14960042a0086090303114a4030b06221226490a142c4143c9000b1030140c45103240d194034500026188501501505c070440d002009110404801c81c4221440600e0034000140d9a9444e0305049441ca00b640d0009035141d4286a8501800401500081d00340c0c0c500203030300000364858003440349104114650094024003141c841030094030b480c07131440005c5401801070b65518441542c60f805044801c0f40da0300046684800c50003100c1e41d2511600fa8421946c0c00c1c0e04160a04014010b403030540c0040000f41525158030900e500c949040c019074006000c0903003c6031240340342e4900103020f50440b8182e009035800d80200b908603103220b550340000700d8124401401141d214042e00390312761100040303c150400d840c0365400b8051410b002118000c2e001ca01694201a004010700030050301d07440440307101203c08002030210300d80d911402c41b258103516050180eaa240f080c98801c9112660f891814000a0144050590b0050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 109845980 1250 109844730 109844741
    0xa0b0411010305090c0102070b0d0b0a08060703051302090c031306060602030901020f0d0c03050711060301060c0b0703060f0605070507050604032a030809060a020a0204091103120906030a020a05040902070501 91
    0xc2628180420380c1c0f2071004544e160a6081c01a0069104a078108550080c42008000003904003a02107542c0701c0b0340e0045500401541e0040501d43e110800300260703030b42d0520030a50065040442d8140c0d43d500341e000030f06844c07405402601106d5000010035050100d0030189440154002824402140d40711400ba41700e03003101017400e015026030a0140795003240850001080a0151617003003c0070500d403001c0313640d60028081100d00008001c0c000c1d13010783e2131802a50017015955511840341400e032422258490000e803000c0d041c0b40c00c6c1301050240304002410403041e1501031070000e0700c981e081e0800c503113020401d6004a4201e240060080280300f52040d14200740100c4d000341019242e0f209442254095007448054401c000600c207041151a180c001054061a04d10444a110305590002000c84552250480d04442e12b025150801e04090041001c11a00a02018205034542012a803c7d10000b03200f83c009a60025a410b40c81c4d000b4800d83e40580180c9508646513281d9280c001c0c000c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 109847230 1250 109845980 109846013
    0x90610030c0626100f061106070309080c0f0a1401090b0601050a020a02040501140306010f080705040209010905100810290705010e030307090617010620010b04090c0314011514030a0b04 81
    0x1719035400440c0580c000d07038070310448488800c014017456982c000110300404500600702c82c84c1d00d04100c050749680e02040015400890300380074100c2c00c0c5241c46c0400c2c4140f00101c042c20b669042c11482c00100700fa100c0c0f4268062402e08015544586400c0100e041c0310184c5d1000354000d14003000400d881d100100110f0407200c0c250121003450b6254000240c2d06541c2d4402d007202030b4041c410611070ba0400e90090818050181800f5070800e880303c00248160798021207075000501001e0400089610000100740100442d10110040e10b0504c07021165000031042c0d0044111800100502004000d50043c0f000c0030060003980c1d00c90030124002000c0032014441d40d07000803143c14101c0f000c050848546412503810361969007282121720032454049500c1c501868a80d580d94a14513007940341e500402032898450496104440e0551809100d01207000c811100c0c0b40c4e16041031107500c80300f07200b0468141c91890411011002c80500082c0c60824101c40c02040325640390701740000c100c8480704800028 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 109848480 1250 109847230 109847249
    0x703031b03021201031101030f051317030606041e09240501020d080a09031202040807050112050402010e120a080d0e0c030d0503070f110a0b090610030c062610 70
    0x15500c50001ca09a010f040000e100c1d682070f190042000580c4d000050940aa060602041c01c94011303080004a81e0b00319100b00300ca4801c3d003909da00f0001145080060841100d25030b508505141c400b14000380118041c552503e143d1a0750900e6080b0060f100710010314901c6801c3c01650310940b4103920403005a408031500607401d640c04a001e40c00420143d042c01140c1c1d039a800c444d038414182c90041c0948030000e6080c40b01c2d80d00304414442187c0020400f404450006201e03013454400010000f580310120a4001450300080c000180c0c0c0c01803003081405401c80307410154190259003a821721401650080000c0700c00604032810071036a401283c2c8800c10001650903680a8030103040c1c9480044100310700190302000000d2501e4059801c501592100b031400f00710313800b145070341145030a90440058800044c80300400850807000c108031a030214005000c0e0403030720316503940ca02d07402aaa00413501403205840700b40b034405521154448026814120702d44690030300a82c44803145409001c0c013070310b2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 109849730 1250 109848480 109848521
    0xe01081315090809090f091006120201110727060501050a02060c0a0c050601082d07030209071209110f010c02030a17070b04050312130f0b060406050402070303 70
    0xc0014424032900040c0d0007070050110195050841c4005150310742c0c0443d0b84031828000c1184645606420902c01c000c4d800700041c45082140c95103160014660f00074886c01e041c840188184001d101d08115040d60a013041010b18000c000d2460800c0c4060b00021243c112056241490f164200d00164013501a00c9042120984640c01101c5d02d03c1fa80c540030740540d00100c0481c00c040c44800061801c00c0307580c50060100103680c1e48080c1403507401e902099180d400080e9881e40c00d01d8003a00007038000c6040194103020003d00c450246c0317560329807002921441c41c8000040c0c81c5030103152442985d0483c4041004000024a803d402620310130b03000a0103003140940c40e2415500450184031050f40080080c0080c0c803040e52040c0001e5509004000981001d01c401c02c0000c02100c01c0d140168407450141d9100e07492142d01d0030403454000c10140c135500c034100302072002c5551452a8401b003a044180511140d03034080118002e03100582c421504544001020024107034141c2c0310070b800c660014140d804 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 109850980 1250 109849730 109849741
    0x1e0b030a1509050603031b0f0f1501050301060f06050c0c09090d08070206060a0306050402040204090518210f0d06050604060c03080609161b1208011409040b06010c0302010608030a0e0108 82
    0x21990103e44540d090b5104007d11208441250554203d8107918421034030040b0f00118401d083c1141240b000101c0da00c29065684d00100741039000b0b000d1b15090700200311461070249000c1c503215062040c44284900000d42c809020028024405000c5001d001620941009040640e8448500030501c00013008840813488482c1b0101d551070064500402c03008504d82151034010003840007500c2203911950801c000510410b00c1d024540c8505031155850889400b401c000d903081c68520201d0500c64520080300410701541402a20048102e0107440b64a92900c070700c4840080c840c9800040e800100424000b551a9100300020003880c0f0a607500c50003a1910383c144520060203881e41c044904055610741d00b540d01c41c290703580c91119440c2d448280084507440d85503c84401200c07000010710f9910052201a4000080ca1103401d01910001c0482c5130584446910200183c03826040086c030065410030315100f50488400340c002c46040d01c1d5100c0a07200094407400340041d50a021601c50000181c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 109852230 1250 109850980 109850999
    0xf06030d030e060c0c070e0f06030d0f0804080304030e0d152d020c03040905011203090806040528020307090c11030a020a030c02040f1407020f0c03071e0b030a15 71
    0x2a04503048100400300e07600c8800f101074039500850722005d01803090450005110001c1d000c0e040c01485400c1e0b4644660800070b042c542404050440c0031f0a00c07100709100703641c040c2d11603002a03015030021388258494803103207004c07102c251101e108290b110b040c080307070102840480c1c0300340b0300540b0410800b00a07180700d03454190159500368440d00405804241000d1000d01150002c240811100050b280b92035103903584842150781c01e030040b0040c0d900403c1d60508043c1c01110b01380182c0f010b0b4006100e140741c1960b44030350700c0006030395031740c610030410030f54039002c001003072409042d154000c0550715000c0d10b9440a400034000200ac100014007000d070140d0350f400000c0121241c21600b076000d49034030f0500352402c1d83d921440d20001c136041591580c00121380c1c0f81c1c0d8820ae0740f201d07120742e406190604064070000c0c909101c6a14000950300021800840c0340d90018583e02118070440103454104400c104141001c41564454240c1c128004104a2258000ea115000b814848002c211055450310303050b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 109853480 1250 109852230 109852241
    0xa0509060615030c030403030b060d0b0114040e16050c1e160513020f04090f05150a081f090515072304060e0a08070b13050907050a0807030906050f06030d03 69
    0x101d00b42400b00b000c204003078910381c015a8414083d0801003600003244001c203880741e0001a80400c0142d03240310b8402190380c00241c960564805480031800c05081004600b4002005000c02c915107240503288000303903000340d0a40b07040f0300d601c50903114000e40b0007002224032100c4c82c920031110301828154031403060010305800161803000d4400144e00c4a01310260009510112103c010b40205000020304080c180c0aa1070391070018540c04a00b50516140b0150302035181c08010382b0500c0300d90740500550000283c0c80d005d500059141001901803951a00014001010301503c140292200043c12004004225005000c2da6503861800c800e800c2d200f94440c4410550341204900400081060b04d1103840b50f0b02d2542802031603004041d039108140d525080081c0d02001c41200003003410510f500c0c0304401d10b001480c06135801c00b071625050400a0440c030410707600b403051000031f10101d40745d503200740d000820361940200104140d003444603003501d56400458ad4148280f0a480a10701440e2090080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 109854730 1250 109853480 109853509
    0x50603010c0806090a0b0306070309050c0f0f0402090a09110403030807081909081303060e0c0607020604030308040f150b0907030e0a0201111513020114160201030f0e060a05090606 79
    0x101d0446443e5003041008510000d8502c1200c41c0e140c1d400d04e02907540501100d401941940c8000030b1244c46442c050781041c40d5101180d01c5040082d59507810794549684800450804450049c0c0ea00070040000b0b410075003d804c01510303c0d1402d40044040d4100b4802802600d000351078603030b4a80d46280c0101c03803040c0f0071a0322452031410b080070391611000c6504112100341c1700310714560411801d07104040d0b5084240e4015500c0c1c07034444c0d0b848051032506105c01021504c00303507401448d05900d90040381180c81984402010005020006024003a20750300d06001940e0201400039071044807100180a4070f039400d40c4030704c42c4080302d0100b6445e134041c2c81000070007200b40f0080c0040d000603030010b503882c41101001ba46140601030ba00f0741c0946e2208003551150364007881c1d0f0918002d05000040ca5261344810514424608100169814044030900156150709183c0428a0b404500d400005080d500500c01024071880003841000700c580e412041c407807080d0100b01e849a030b480a041103c0d01c4000c240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 109855980 1250 109854730 109854737
    0x60e04080d050604060305010c080f010b121603061a1201050a0806160e0616050709020703051902010b0d050d0806090c0702090a0b09130303060603020f030a0b040b04021c050603010c 80
    0x1203411154a1038010b540c1c4050020070005469a43c0d848080c02d40ea04018500d0004a241040004c003642c1c0310356040c05082d84014403410465640340c181034015024207002c0c11500c1903174001d80c0161003500608064020707400102018800248074078610740012114042002d0780d9000440c080c204400350004950340c0070000d01d40c9440d0001c50300c1982164044140402092480882c45611450010120064505800c0104d0749043c140a420039500c0c0c1c00c880807040c01042a070001c66400800e90b900c9445a603e403004070560100c080c1c3c014000d1841c4075402c03017202901c00080c0400030403803403016401074a540b0000e40d01e8a042007044c04e01260498083d6505000070005420078010840e032280e40f071080058508010000120109030441e805a03040750084403000406515000300d41c0106920b04043d03003022010242030701507010042c44a0f2034261344404400244e56150401c3d0900c44016104560b10410940c001c52058441d5440a20742c0c3d06180110b00d9074101489413020000c15079a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 109857230 1250 109855980 109855987
    0x20d1b030e010c1515030507080c010915050c0a0b0610030c050301090209060c19170a0e0906190e011509050a0b130b030a1406010c02030a03180e04080d060e0408 71
    0x400664028500b80d80c25158045011415130401842d440b64412034000314004605080ca149041440d115a41d0844145500b024a441e42141d8008600c0000e0b5160610006c092291400c0704071058022202004014130580b2032450034072003408241d5004441c00d0360022a01004a401038040c1c42e006440c20000400410040103c8000c075030141c41511402010705e40340606442c1d02d40e1501d4102204d4013904140401140100302c110700c1c1024014030880c50140c18440030140192940100a50580c050614207000400716502c064807032808440710000c0d880c0303d0392a00c6030041050740034010006170950103800b810440d1301802e04042100c40042c0010500c40c00c0040301c182c1600501506840d41000c54008a5020300120103580300d90700794040010101c81080005d180c0140107000141030145030b16416000d40c4010504110841e01402c014446002400921040303410a034040148514a4801d1008000c02600146403100c00d00b4424400d0980703d6190f039228250030f8600030441075042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 109858480 1250 109857230 109857257
    0x13110315331e0a0f0903080406031d0a03020c030706030e1f02070206040b130906080d0804030e120a140105130f110414060907020f0309011d060406020d1b03 69
    0x40e00000d40d091103406418005204210100050585402c2500c0d100104881c03c9450740b010340b64210108502e8071528646c0340d620b41103038910640c040c50013050340310401548400d400302843d03400780040310100c1e050b00589080080d1924200450350f40320340550980090028400e0280d0f148440c0100054021506229401c0b481c2c5590f000c0321a40d90768090003544e01503030790b0b80c000d080240492215140c1c0c4a4204111803007501054220b004464a42401804000c00024050f01000300f80c0c2418807694880e800e09030350740b800d0501f00a90084540115545001c1d003c50f40c084041e200d54540d0f04031b00a16001d080c02d942084404030380d0821640040740c0442d040e5032020400501601c080e01005c00c011010a094811040004024a03401014404203007030020405502201900c00703092285950140d0b551a841001002d030b04000d080c2501c082d030369945401c2180190343c0100b00980d200e6441401a44801c1c0d80203001c000b056115036547c0c600000d4415005419505176030b0300054110f074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 109859730 1250 109858480 109858549
    0x150f0a061b020604230402070f0308060d051e01140103020d0f060e011a10030504020f04021c0c031d01050114010503151207080c04020405090f040213110315 69
    0x40444070404880c001d0900809a1503410003040544002d1030f00692030ba611420182003aa00c220895024a104020800200d14403143e03043d0603607410301e0600310756100c00000800440c820040a001030080203040a203c2016501c10b4400a221a0007030000e0110089100c01c501000d2002940040e40310742c1a800043d520440710007120700c14580016035200101100d42141c0003c495611aa0101980d204030b0707251242051080c174425103801d00c5a85020b81c045501e841c0381c0070016020b04e4004c192407000e00840101002241c000ba10b00b00701c070400000e00200685070700c1c03061984040f00720044500700c42044c060341d070580d0102043e0601808081d001143c0725031000b090050b02d154003065159465440f040501000505080100080c5040c0040b41c0c3c1060302c07a024030b510492042108101c0341e1507a40d8100e074401d1215101541541c0c1e607002007801040c04003625848549040300050b000c1e5968130241d1b0265041d160390141826850b230511443e0800d100c030030800c4a40c0303c200408221003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 109860980 1250 109859730 109859747
    0x13050114093f0d020a0c17030403021506130e031809070801120309350f060105060a0e1801080610080a020405090118030207030b0a0b0618012105150f0a06 68
    0x1241c144151038400060880c3c8100c0e00107416400c000344400040009104000c668180200300040e1450f145042c20b640c00f951f40d11200d000014070210318000560195152503520b0000604660244238892110700c2c03858680d070091015501800c10605644010b090211906224103599100c2d02203d0b401d001622868002e5403070110104040d280c5c0101d8074040102c60b040100351000b0f601c00d40209043c0c40311468249001094003241c0c4601c2e40007094050005401c0c0c110b40c81031340d030140c0d14060138200b22550010010380130341000c5c0e04a00c541e40c000e600303038105049402c040b06440c02622031410f84502c2d1869440707105065800890540c2c050f00e080c1d40184e80000b4040f0000581c89020018003032417881c00c0000742c025800040701001400b182c0c040c11a40f05100c4441000f0400303409001610328020b4203542c40c0640100380041103141d00440000040640e071200b40c08040d035103044600041d0004035083d104060701e80c076a61001e03040030304118464a03c0100f0804000f07007030040071184a02d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 109862230 1250 109860980 109861093
    0x4030f030c060216080901030c05090a260303010f0303030f0203040c170c120c120c0d081b01061202100806012003040b030a05100803030c121305011409 67
    0x25401c104882940c00c011340011405441201404e4558031207a00140442c2c1c41d5008240a2200401100c0c12540d150145041614124600800d1a42d620068284200c0c01030500c102c0f5440f0010010900300b10155080d03040303900c070744e070240000428070454000764001a44e005011504106091040181c0850034000b0303014504c045030078041d82a000581c1d00c84804103244015082a56041c8080c00c0c144500f103211109003004094a07180103000c140900c840c040d015083c08004101d20407a4902196030000c000200002841000d03160080c113400c030020400304a101d6240b0507041e81949026400c502d204200586514100f091101c1409104502031058480c2c036000400000c2041807100f00a5070103512001c0300000d00e49040c100c80120200300d80c00540c00c0358418820005104101c00880e01d600400121010581d11403180c02c2d00718814080c402403180d420040003101d803c80c80201680718840703040444071101024581d010703081040900c26898002641e140c00b44281d03551003100b5000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 109863480 1250 109862230 109862243
    0xa05030a030209010219060519050408090402070503120106080a061401091806230a1a16020a081c1d0609061312050a0201030c14090405090f030406021501060504030f030c 75
    0x580c0c1d0031102c01282e040c0316004071f03045039940c1c0a0003086543d000302c0e00d540c001e252004210908213034a03002014000c440c0320710311841e00046d41030100030061003503a040b008401c0314042107584030040070344854400c5884068031840e0140c00039065171220740305400440c040e103130042c250742450744158490074076070a5000300980f01c540000b01984000c10f111321007080c0c000380c2c1c4148400c440401244058541c030040ba00b409500e0703d48c403150880340494807a10020501d011072004d552010510308506580080c01034080c2c0c9030b030398a00800b0034000c60b10300649980c410714000e02d5040c54002c80d404004034540c01c00014401406a03003844001014a0108240580c5845039640f45040701080b104004590680003d5086403c41d41c040c05415401800e5040042c00794015040524107801030106a0340b180b92031342c020030700302e000500c001000318082ea816290b4440e00c07080b000c0c1d80c6150081e121205840c0e202c000089991164080d1401d603079102c0301584600d0a1a03e08449100841e041640c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 109864730 1250 109863480 109863493
    0x204110d0608010605030607140711040c0201050604060f1202011d03061003030305060603010531110405010e09040803040b090c030706030b040c081902160209041a0106020a05030a0302090102 84
    0x1010420161081040440c030225a0505000165080d02c24503400b550082c1d20203420b2110711900194240c0f801c00000c00e00a85070300c03032805c05a02e1f68401001c10fa0b0024909110503c07556410b41011f4441e40b01520284071450341c6580d05560001c00388541241225142014001588030b1681c2c4040c20000117980300c0301201b03004c0003070306144045d102c1404101d80c41e40d04104040d0140141980540b04403001411b540c50200031900b0010034003c030214902122460160b8400c107298058500207070644108458120040303030200552050150b01d010036040b9441301010700c1e2018a80d813046901c003020f141940c942e07036985204410080c002c2034040c05141c010884a8804021040003025540d0340802c16114080030b0008440d000380c5030350204182c4904100321006140c9184100101520005a44a40c0444422a15852200000d520001d500c0601c81030104508030a800c40301000c2a0f001c05903030307030035059949a4190074000c0c20b541050241d18280e0b402a070180100007010300503101d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 109865980 1250 109864730 109864751
    0x30905150c0703090803040501050706020f120406150b071e02030a050303090a030e100e0f1503090f150421050903010926040506070803060f030607030506030c04090308070c0204 78
    0x2103180c030466050118510110790035081c10790240c40507004025000c042d40c601420040020031510607070300c0286c601a00020f10051030f0340f20320115880c4410540348403a150420703146c500c0240c104075203801e90303549d00301c1000b01d9080380324012240d190340d004201440c1440103900200c400c035400f11090b42c0c14001c1101200104a003840118403888440b40030f0702c0c0f20340e151314001e88402e600c01041402203103101c043c80403168228140880d40034044070040041c00c010800603403101c135860b011181c070410200500812170000a200340c0b403154004155142c80d108446400407103401118003512200c11808150003c103161010666500120b1030300300d2034030140390082800d454041e2012104d146000840c032941410885105042c0741d2540c1c03c0518261400c030028000d40110700340a06450000004070f082e5a50360504503001003030250035180645401d88000c0c0050000b1184180280a804003680c1d07d4a4244a001640c40c0e160315005425151a1b000b160000c0705a8412a0044d507100d00181 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 109867230 1250 109865980 109866013
    0x50712111b070b03040308101502060604050a020409060f1502060f010306110708070f12090501120b1306080610060e0a14032a03150403051e07020a120320030406030905 74
    0x1417155000e601c400506003484507550010410702d07441100002030381003000c290917038041501908080304a6010500b612040c140d10001d12507580207854140ca00040010040d54070515801203c840450344402d0f40d900030402e176282e071402c039100ca002c40da5803c01400001c1580d8022045d244c7c01c6600c0e01c2c01d054269541c04030300d1f848560142daa520500085c4010080c040c000380e4080c10316403924030603003881c040020340103600410b01d0114507a05c0d007079941a03a49900050390800c0d27040060170b0210581e900f240039152181a03400e8990180b0100021942c0d5019030003801e00080c01500b00c0c00c803d803401d1101d51509001040d483c1c0c3c10301888a4501207000781c508580031022a40580c00e1302010180105450004a004c452100454030b00410000c00c1d080720030b54014041000c035000688041300521941d40c85020b80c0250302c9000f501000c20400075246e24100007510a40700c0366402c40e0802d144050005103000c04070040d9204000602803103109400a02d000340c4920225112955100800c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 109868480 1250 109867230 109867237
    0xf02030919090b03010b0f041d03070b01030b01090203010303020d11150c040503071d13080f04080601060e1c150905150402030c0607030f050f0c0d0201050712111b070b 74
    0xc003140700c8040300c2400184114455036070381c084110001c00c844130f400000f280d035486414244620aa5440502c00d0000701b22002e100c00c0801c100b0705807079a540241c038005440072000c1c0410fa4080d005840040346c004814421a41a41e1f01034009181d1900e1058040b500800214860070960151003003c001c000040319030b10b405519400f0f0010f44803410071040c94a00000e40d40864000155046290f5614651040e07403500a021004803400704203260520398114460804502031007500000c0c005800c41d00403c0040c140e40d4960754814101c4d110380200003071594009090f01c0c9203c5140c4102c4d001074003946c0740e2141100400c40105040d002515144e040c003201014400240340050b04110441c50240450f884103201114a03a0814119480041076124003400b468140000004ca003500f8401d8042550100800c0700d045a1501d9000c00000b4040c100070395040c40458a140c204101441c1c9901a11141504034070226080076070400c000c41d0880b0719072000f04180e010b041404120300a080340103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 109869730 1250 109868480 109868509
    0x118051008190302010b0a0b0415170702070501030b090103080a031a1e0906040203090604080a0c060606030905060603030315041e0903080f0a0603201305070903050708060105030601060f020309 85
    0x90001c2d02582d04000e801e5845210120b403040650480074400b241940b42510191601403644200015580038140c48030300035508000d80040d4a0010001000d50008100c4252442030340e040c030440c042c1c0010302c0340e01340b001c1c00000e003480414061a130007284681c1c0040d036444144001c0c054111140004912038003030120703404a070301c0401000e440060400850050304040e066808600d9441d0140f41143c4405020304001c101c00800207508040070720905400010a41200c0200f05d001e1fa00c04001e80180031181c4200c40600442000030840e01c2c011040c0d0b44a00c8010414089844041c0104002800e55007500700c42243e60100c000000e44031032003403400c4640b00752104002c0342030208000264003001001541040c0c02d02500b4000101d03600b03e0100b04403411060303050b8900e441c0300004e0880d098011400700c19498081080107955100a160040320300032001d4880c0c1c0f80d1100b10b02c030780340c01e000d00840b5016405240104802d500c07869209600a00134819241030904680c00152085403100304c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 109870980 1250 109869730 109869763
    0xa0e090a0207170406020d0c05030403060f020a02060a1401090c05041805090f01060b07021c02030604260c06010303050f070602130609060c0203070512160305010f0606080118051008 80
    0xc420301000f00910000f00901005039a00781000c0c07402400030740e00c3c004200a40104451444280c042180c1007003030328044c682c840c3c0d044c03041a04650010001b034100369208001441581c0101d10901c8092107030700048201d003540c108007682010700c054040c0500040c200100b00d003c0000250555034490100d40c3c03d1604040801c0c036041182d03c407450540c3c4001140c042d6403400f80104440b2a003038048403446541596000e00c148400010300031174405150340a901802140b040104000b0103c0380e104180c2c000da981c001c49120662070400031409500001111a4401d90060000c80e01400c0500440054483d0b4640f4048032a03486100380d030040d00300002c0c0358403030807070038010160082d44450140509152044403a04181c000070303594074184c494280503285041c0724840e5041c05210800c0246441410030282c580d40f8030b070460007840000d405243c0ca80c034001000c42c165200c1d800300740c100c911191201e00b550b9010080a4000d000240003007064003020a40015915000d000d0141a80c02094 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 109872230 1250 109870980 109870987
    0x10c14030c01060506040608070807110312040201031a030a02040203040212161404050415090201110d26010509011a0904060312110606100c050102090411040f15050a050a0e090a02 79
    0x41031542500c0fa40e8010521650050109000640d40f2506095025807e0301d044a0301d900d40e250305036186840f2044400b124000000c241883c020008140d500441c0b00784d03000c02052a140140910340003403500700c50743c517400809000c1c0151405070040e540242c0014101078841c8044c4280728648070282040007009000403000304411820310f41c4d00d1000305019075050243d89465a604d03c0c01c042e14400b88801190368a5a004c25a485101a0395100b0001001c5800b10180d0140103400c0510328685c0c107442404060072400900038060030b65040b200041e020342c201e0790902d6000003c1300038002d15134880c10014040d685c076a9486000d031100550040070107a40c00c2081c000001c1014011448584d0903501080511030a51202c04203035624603402c0c58100300061103840c1c05406442061002980603040158030b001c48404c00340240304a0303140d02184001c1c203548180c4c1c240d598203550b03d4000400e41c14001094040e01507001440d0a54a40c079269501c0d150940000300c217004165000341a06a010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 109873480 1250 109872230 109872247
    0x9250308070c24020c030a1a100b03101e0303080f150303040f0503010509010e1c090e0f18010902060f0c030d0e0319090302060417120a030f29040b010c1403 69
    0x52003040b002d0032046d030141001220680310040341311403240984c4115a91000001c27902c2d1848010407016114110b01d05541c1d0804660308101c403106801014004407081e200c00c0c00d406400d8000c1022250f1680350744400740d451250f4407140d00c60003000c4409010b10502140507a940510090020303190900c008543e0f80d0904d4289400c41d40c00821030017840c0e14140040a05440004840350718006800007501c1114031440125004100c55200b0102c4002100a1110f40d940d5240450300c00c0d4100c0c440c214000c8140c80e035260913942c0840c0060b400500400c10f00e811450716030000c10310800f130b40048910b03100744804540e00311040c43e15000074540000c60500380d0628001c400070111446403400c1c204450841e0000348851080c3d00c00c610500006a03181c3d10b080070309002000e15a4521a0070980326420683c0140281c00a9200124a545856502d000d1000300410050b0662081400625030440d100d040c8002003809034240d0b4140680e02c540003000564045a2266000c3c86070040d58840086 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 109874730 1250 109873480 109873483
    0xc100e0d0305071805040203070e031b180103110402181309020a0801020c03030f061c032d0806040903110a060204140105030115051e0c0609250308070c2402 69
    0x902520100101812030000b40c0710805400300903140c00b21b0300141c1c0e0f0744410005a804c0c40524000035054082d500100c4090305208003c1e0a0611040c7c940c1c1c24443c141352108420264240401032003000a00070143c401c0c14250301825038400c09110907460035400c1400146140d140602c51122103884840903021410198040340060603154029801c1c600450f1810340c403404000d102c0c19155280340000f903003035a51480304410b0310064608492079502c840c00c005000181c0002031454847c1e5203000d4001c059000e03010a50580a0b6544010490715042c080001070300e0784030425800c005551241000790301003441000561407007000300603921441c24480c40400300b00404101d05101d018001040703013448000300070200400b1494469962681c203a68001c02c501d240c507650310300c0f403004504188140c80010305507025141041c112100c40c0e5540703c61182403c201c251502e406000303400104005101180a01412885413403083c40c06a06c81c0c49001c44542c02c2c8921090140848019840d460340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 109875980 1250 109874730 109874741
    0x203041d1812070803040609060219030b060a080f06030a080315040f02030c04121403160b060406030c090c110111040609060f0c02090a0f0f0f0e0304030c03080c100e0d03 75
    0x141d98000d032600c0c0c556006000d10324024500090301826001000804203c070a40c000d00c2001d90040d0215104c01da509614034551700440d070100c003c28644a400302e001d1404400341c030101143c80d80d03000c0741caa94020301c20710f540340c0261441d078051003041e5040c40003540c0c0101442c4100040302610541d01c66000410094a01c0d014170350706054410070603c04111201c408540945a0610044842d118949010030301245e0a0800303100c2800081703003c42c140700101c150224a50700a08404d0201d4482808020032a041d5201c002c000f242040401c1044d151a82c10070003d0784a1428075020840c3c00786050703800d40d4021280c100c1c2503d4002414030420f0340108980c8050022890103000540940d84054110103001801030b105950100005110082527000010000d807220024400800c1d500c0410340544816041c8058031030900090751b4044100006039000c803500540d568058514544401038603500c09181c0704c416010300d070045031071285240104410800040024030794002115002012a003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 109877230 1250 109875980 109876021
    0x22109070b0708041203090b03010909020a0902030907180608060103050c041407050307050d06080114010f0510020c090702011112070f03020c031c06180e01050f0f01030f030203041d 80
    0x14070501c2074401148416060300c040d100b25148140781e0150509007030b25000704540c00080d11820000021840ca44150082450103100355084080c040d00e44854000360700084445140551140008001c074807403d103c0e0000390007140e2000104152254081401e1000c260400e86a550159406c1d040a040a10400b080210152841f10250070504401002c0d0712015241d0b004214003c500306075140d409078090401810b095008000c41d40200e4148011580b007480390407044140c0c1e13900043c00e42084098468900202c0d40940300c910352803410000740390000381010702159030b6000113919080b203070300060403210030404440c0303111b242a6800410580182e01640d082600500c44030490990000903039008a004004403510302c007a0080d0700c00100b805511840340315000108403003800038143c2c000401b50b00d4480c028400e5907501d0f00c8070f0310303000380a03201e503003044101000410204c1d40389102c0802d118424415a440c1c81e503604a42d594106c2e0700d015140030390b1401ca090242c071070050b1010a5800c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 109878480 1250 109877230 109877249
    0x5031206090105090106050715020d05040302100608070e10080a05030c0606011e1d040606050706060f0e0103020603090f03030c0a0e0d150c0302190201140106080f0a02090402210907 80
    0x42d810400411106901807203604d06200000c6954010030041c580c00050800d81b0100454031a91114131804c068681900d050323003d4021202c0a00038450180201001c0d140458000c210742d502d401d1300c10b45075440080000d102c5280341d0f0f5000c50801e0007440b18601e00d0707000b00f0055843c0c0d51480910b500b0600d02900d11070503c1640180b000c0c0b00b440660190000e4a1039082440046503918825581e01080054050b4080d05c0e1140c04a03406400030042e010540c0620700030040f050715103038171400e520000d00a241c1e4034084100104010314110700110381c04242c00c001d5447c610f40009072a4a5078105884040c0360305404286145910341c882d41d920341c205030843d024000e00c0106d4940300407441c40f10030704146450300d9540c5c61144900a40403100902c135011406800020180c0c0028000e00305614220450340f0710500025501d4071130060715000c0c802003800039550b610303020749490080d0b210040da81d8002e5000e20144200a040c0c5415810302145150200407a00e8500441d50404000b0303000044031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 109879730 1250 109878480 109878499
    0x1021e0310170a0b0618040803090f030903060406110418140c03190b0415030b0109051b04060e0109120c0501080108030a0504090b030309030601090e01050106090302031c11070305031206 82
    0x200c1d0b00040e01414560414029a101c0d101d07079011401c040720358100c0e040d03c0300e0342c0c00501041218800003580f044a540090302c2650003441a0b0b261079200c0da4501d50b906a20003808203021441d07540c002d10320a1030305042e0368505599011116070f10040c0f150800e580030354480071a0304040c000031080d0b5005890022452552810356022040d07250081b009400d0241c1d03d81d011155612141e0000401c403551400640c0c0c4d1135a01e1400d504524024040c085040d424a4007049036451841c0300303110451005078a082c1040e00702481160825200122181040300200d0001400242d80d040004040e0013903401d030310f0040c280800035042c000c040c0e2149046920400203022450340c441c003a20141c6181400114441d0001701c0000e24600890074450b9050141c08000101804e03150300280210510100902a680c1c2c1c03030500b40c80b203a21922000e90950040440a6500d01400141d003041c3c1485090412840e00400e031124502074a13604101c50b10340c400544c00d84100008001154800380c2124042d06 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 109880980 1250 109879730 109879769
    0x50f0f100b06180604080109150f050127110301030609060b0f0f0409020d06020c0f011109060a051b010e030909010e09030a050a03090501090c03030f2f01021e0310 72
    0x40b00c2c8201641c07030110800320000c0c11402e07036603001218011300c3e90b00001d0002c4086070901c0a90f641142d140f01042914090141c10001c1980c011241254100c0c1c80c607210404110f10803080229601000ca007030300c0d582e502c030107507032400f06800f030341c080c47c016400000e01781040d00d007030000c03203c0c4102c0042c45141508064001a036420490500c24501500c000c181380415101098040c8400140117111a0010a10029440b00010483c2e1490301c00b03402441180300903000c0c5022032080c1c0c80705940200081000c00405405500200119907840418003034000c40380200034211044615000f07110b4000280c013030024548644401c1c05403400358120301080c1004041142d9030700c1040345080c10700c40e001c41e0a801c81c6e8081d5010003030103504280203200c4500d01d03140045513101d80d0300044010803c02d0f01c092140c24410f43d0750802000c458221682c40c0500e403c3d604d00315000140800f00d5540d020841c804414110001e014522403003c00c401d62a4240740c607080000d1000d5030402c01c8100865001d001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 109882230 1250 109880980 109880989
    0x151002060f06060f0c12070b0115080a0b03160602060a0606031a27090a03030c0c05100b0310060e010905010522051905070f0e01030e060f13050f0f100b 67
    0x190860702c2200c02c1a034420b00c099402d9100d00449040042e81e0080482000c510011040181201c5101d58612052680c0324003d140000803034080340d000181d00c200008120141507813041e50340980090841c2e2050300380284018041205400c80700060308114207100c1c600455000745400b0f08890f05060110454a41044190101c0c002600d0b1003a250f90705000d546c6c2182e590034248044010060050515110390302540d00d0340c40345e03004c40000e450032410603626031103071075800e007a00e91100c050320030141d0804c1030ba07005e03242425620b6814002d000520b03240460900c210780c000e2044695a0b54950315190344d11048400580c03000303016500703081406d0400e01c130420b11110201e000d2600000c2c203483d00d5400c0000360907202501c0b2010340c80c0c9030511404941101c2142c0400341c41d59505081d451901c00114141c64448035501c08650102022400c2c580c4802c1a00768483d001c110f041d00c0844a03515100c0c90800183d04000068001b03035111b000c4018103201c15480321103540390a000c030303d4140c40801d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 109883480 1250 109882230 109882261
    0x9030314180306011d010b0f0d0c09080f01060f0b211b0408011407140f0d020909040f0c09140606090a0504050a0b0a0801050105010905060a0203040e15100206 70
    0xa21903010001d0003980d440040040540360620240848100d0340c3c50304004905c3c1c850461520040d280d0140000500200c440102c4d09450315060190303040103010302c00300e409403090018410a0012001021403980410818071403005400340010503128500668404110450340120520702c404000402c8030358018140b03070030000c1402104400b595a15100000300e030910460044080c44000f4000904150541024100c81d110013203030111a114584140d42c0e90064488004c4080814040b03440011044d502070400ca20021001603e080e56010000b44904800c40c0c0c119802d900c00610041070000b80c541001c0907220480080201c07003a07041d08400700c580010300151043d180041c125a258848248510007003001800038405030404c0d843d401c02404000b40d500780150200c0741e0004181c5014085c050480304186c607164410f606200c1031200c290702c000d203400250f00c010000040c1989100c4402c2c0c2c41400c48045015440300d08000b00702010b00c0c054811011907000f41d0500c00fa0b01000e0402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 109884730 1250 109883480 109883507
    0x634080f040614010303090905060a051003020c190c061e09050906030c150a14120604022101060e040b040507020c060a020109081801020111070506040209060d02090a1a01090303 78
    0x20569580d03210314040b8043c0c1080018030190a10400c000810503420010030002c1c2c1c1c94408060000d65144010300514110521440342d200c20402e8605003078034021340c020301107400340388140e502da259000d001108000c02d03403104130340c8440808010803420383c3c0100803000028466689000725080ca4100500b14840742c01264403075051040490013170b075004c10007890080340c050000e102c1c0030b4922a244e03071a50045440030011918540721400240103110403584410805e04820389580c944005206c02034100124101c440000d0107030014002810700700c03403070003440c0c50781e220032545101000b0300040e280104116402141402c00340304900d41c01050040c03003440e0584142da03d0b4200b8074400c0f80913021a581c003405004000540c600f0b08000007204d900c03420000e030024803405009402000d0644190b180141c00c0e500b040d0041001460106541a00843c0080c6102680c2090f034000030310503030b0309444c1103052a5880c5042c01440011281088580303009007441400d4a1841e02c0103031448100d41c03c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 109885980 1250 109884730 109884751
    0x204050c120f01061407230109020a090e07050604030b06040e0309100309020f090103080d0c0c21081605041205011805150901060501090501050a020708063408 70
    0x114040359a00585808001d461141c2201d42400c88a02204030002e0142000142d10910fa0b180c140300100122160a07520029180505040f0b03010040c81c202c21610300c141c1c65481d5808840035a40d01d4490a02414202000107143c40310400c5203843c0c01201d611031801440d0a00040000c2044910010f9120100b030320701250328000300d101c59080d4410381c540d17240c0c04510401d5140201c2c3d4103900980d1400d01c2940d404402151040c20000e1800c02480001d00404041001040d589029002600048902d007050a0080155610810b00c0b080c2d40021403000040000d01541c010303800144107400260340714141e0b0f00280000d000030018844c80c0222082000e1100b507240c100142544200e00203150542002505d082030315041e920b500c03d90390500d40441c2c1c940c0108103011410b10070a01203c00585503041a1442c1a00555494001d16000303c00d5002ea17020020321000107100c901c0c0301d82e01030b02c149582d50313548848050203d85030750040c511610744410203008298000240303640040041e40c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 109887230 1250 109885980 109885991
    0x507060b220b01141819090c03020d15030203030406030b010c20012601120f060609020903101b11031306020109020906010807080402040f151401020708190204 70
    0x201e4030411100d12401034100824403140303900c4900394401d8602d224240e8840e035002512084240c81d0b8050890000c0f01c4079004200048640b03400c9811a00c40501c01d03003039038409642c030011031045680e940482c02c0400d0f0009608025840a80304088d045803039400c6840c00c031419500803c0e0f490160740244010701d9560207803054141c1c010000b61500c41d5000603911000e00709008840040215400c0241c0860060601d1060380e03002100381c92401a000c0c1c504e0202a8a8291803d84a051000054a80351383c814904400b1420a0080d000600b019040151303031555548241071078001d5004445d94070501c1c1200480c06403107a0f00c030103103081e1842d24004040c84951610b035420f510030b900f044800ca24003220006030b0710340c040d00b0010249000b21042c481c2c40e82c40394019074405c08210760801c0000c0c19080041c00510b4140c0c024103008400600c000344515043c64101c0c050b69403a007020f01300c80a1400076182541c0e040024401501074180030303046203409900c070005500550340000f0321858503170 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 109888480 1250 109887230 109887251
    0x40203060d061806051e1506070c120224070204020d09020d0b0103021f020312061c03020d08010b041d0403030b04060b03090105070906080109110f0708130602071d1b071a09010c050706 81
    0x806e880d98034ac0c1003044940745568809622020048039070301240a0b840250b02185000c1072802d100009401800d05030340b42c0011982008025400017491003030042e610000000980c48010038241070f140319589010f020750540c0100700c0c0c5402c030b006012981d8000501e1000203654040280e5036035152100706c08504e901c3d020002404240c00c0c0c11040d5140a090b90b0324814158001030498083d000d1742c8420410780d03250219241284070314082c240b100c060140d8110706840d041100c00754000d010349000a6001000000501507a0142d84140c0c005100401071001284e82803082540180940c01c100180c0e615054000d0b040400510035042002e50b2105c4081c101980c030340499406101d40c20140380d032129903280850064018003000008480300b05000b1858600010741c83d016104607606085e0380c20b940c012188040344005015400301206c0000c0300f07110800d0b200191100e030f0f00c1503803403030030780f09044211401c0e8880040c0b0b16909681004d00c28010550420304403450a60400f00104455891 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 109889730 1250 109888480 109888489
    0x301150515090607080a0807020a0c140f09090a06140403020a0206030415020f041805010f0b090f030d050c0f01090f021e09070207050f01021b040203060d061806051e15 74
    0x10b041499411031400201c407410016840020b01c04a095030f100d0190688455004030b0b40c560002d0310040001c0b5039808148040003040e550021070300001020200d015014038041075075081c040d65001060340c044203030b01041203600c6c01240c60013100740c07080d02d0141c986510000d584001c1504040e014031000804070741800101e0410942d40b09036044c0942d0782c0c03002c0580c0ca9025078440e1090b100b6425406d030b06a83c2e003003010301a050403903400500c032821542c20408214070951008800070742c042c081c01c0c011000d0f9103081c001e03080c4100d881d0b29401d448681801445040411020624405034075140140c80081c601503004c80aa94065540d44010700d00c140c00d10740184d000260040d80540031804110712294002140c5090b56000d4440702e100d031101c480160f95406140501c1d60000e003100000351b61900781b65015552100000301841320752451900d91074219420749c0b010b11460411141c00d401801018050950000061220202854948480d000444402812110f48545044925640c0303954 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 109890980 1250 109889730 109889737
    0x40e18010203090a0b010e09100b0a0806010e0103020a0510020607030207060603060e0604051006050109151e0809060c0c031c0617010e060f070207090c03090b0a0f05060301150515 79
    0x184500210350324100200203980d02d0103000f0302103800c018010000f0130311503a810011030217840103c00404600c0d0190306400b002c0c0850309401c82d00265090b100080c1a2820443d85000f4080c105083c20694158010320004541d541c210340d0103004140c01420350070740d0011351564809403078580180c03111011316108015019940c006003016080a8104031490700c045000b40c029403141d012900f00e4101500c002090320024403605020130740a000821100869100d9040400f110b4070384000c90414401d10356a40c5017507007682c080000e50308410419011301c00c22280c0c0d00030301e01e10343c0b550a001445444030395901c58007070903402e1540c0c402d64540c800b094540000014202c0f400440c820341200352b2405000707046d07507484002c280c8100404210504c40603200039000d41555030180050504081000d0043c0a00403030b0002050b5440000c407000c02d4079910700380e000f0b5a170400049844031043c070b4683c00369000904083d1081c1d142076518555102c80101701801c45900755500c2212605500603a5510300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 109892086 1106 109890980 109891021
    0x90f05010806030a050105010608041a150d0609020a06210b01020d080709090603121e1b050709020d0504020909070308030114130608010b0a0603050606040e 69
    0x1441001d8481e030040c8080c0c01c40301c802603150340d82402c6401c01d0780b080c0c000401030f4051000b0000c148102c54121604c056681380e03a420026503c0f5081178440d1520341c441c5500140d07070b20410245822246880d0380041401214550b1141c0107030007402074800a2068584032400d1003a0034150b840380c4140c4107810f80c020201e03080d4503201600c00390340c040c0c403000c184054007800003001e00043c041d140c00745d80b0038a4589648809007074040c00401c0c4002d08904400303001924207581c10b5001302c0640c41d82481402d50303116424541000c509280701a0420001c43d8000104100c0101e12604440d002c2ea1094400741003aa503010034007500e803c42800700a124440810040024085035000c3c21f81000000300b03541082203140d1940011210554000341c0703165141c21001c08103103054208240141302c142414800d502d00540068124801c0d40141085440090049016484c40a51001c0e484 = true := by decide +kernel

theorem cover : BRFrame.Cov 109712230 109892086 := by
  have h0 := BRFrame.cov_init 109712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 109712230 ≤ n) (h2 : n < 109892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
