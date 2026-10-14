-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0220
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:32:48.484874+00:00
-- url     : https://prove2.me/submissions/1f251da9-d355-4206-844e-83c4d73368c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 39388494 ≤ n < 39568350 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 39389744 1250 39388494 39388513
    0x304080f1314010e0d060203061801080a02011e09090c031b0c061104050f090a11030a0504120e03100b03240f0604110304060207020301021303210206090705090402030708 75
    0x24000101038420b102400014800000440d8014020010440e0340a4250403980b0f20f166030314402540020140344d400078211100e0510000108510b034081c210f624000d049101060001400880034401d031a29100e40b04100640680da009900310101d58642402003840441e9000079006007802c2104504088005402c04210640c8120b49048a41c0031700d40c20411064074028008091041d4000c0c1a0420071440300d80f1242e09000a41d0b55020700010340020f20501040300714802ca80c020358081c00b0b443d0301d8006100c103000285940c2282e42d0901c0c1014880222030001213030b1200c1c0903150b1103c441396101d00e0042c45407000e018413911519041c1c4014403547c540d41c6000d00f0b001064620840690103000000c22a08152180101100e0b01c032000d541036581d9640c130a8089d510000c0e0403601550244a40301240b0764011103207020b54401d014921071080341584003042042a500003004541c080c40071700c1500d91001c01c1c004140c1e04180c03241f03d520ba071503001003850030015500140703043c440c40201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 39390994 1250 39389744 39389767
    0x12c100216060305090307080904020f040303090305010608012c010b09130c080309031c0306030206120103060b0108040b0703090309050a065913020a0215040f03050304080f 76
    0x105500c003400d00782007601d210b403a0001201166001c80e8052440d5008010b0a0041f408010182c51080c80c01003001d07151001d09880742c40c264115600840109404090500402c10203001781e002611417031000300f00065085400b0203003401a030f030307141d0320340c000c52030442d041c1c1c500c03c1d0482c0e100c841016140030010305003401c5242149003241da0550766206120307030204070080040b00310340000c4001001041c01d90000625031a814890510703c3c000d1503510400000181c40704405820348071144030301645a9071540c1130030340580b040c940b8034504200e5500104000a0032418100d0f42048071440c000548101a145c2130350311103d0717600019484424040f0010343d86600900001e08602c81c49000ba0200801e00030300c941040019a002140b03000403034040c1c100c0510a01003a640640d108101003642044a01142421108000c81010682c00048407441c1c1a01003102c16103090000140041900c1c3c25200c003c020362050100034104280000850180012a0f0954030107524124000360380f41070780c151 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 39392244 1250 39390994 39391003
    0xd03080a0e0717010c1404060302030907080105010801060303080c0307080a0e01020d020d060602010b030d020703030e012006060a141503072a0203060604020a051c0f060308090405010801020306012c1002 89
    0x20f55001660801c83c0050500d44641850703030760f0380500c0120b10b042500b8094154042c0d0130080c500e0440344203141c000500f1304002d00945000388081c1c000064428110b0400902d0341c0401030100c210900100203104035030b6402180583d0140036204002500c00b4480400c1e400381c4501c442845001740045101400844980e00550032150f86400030400081004c3c141070700c40384500c40c10390142e04011000c00210340200c0143ea40080d0515101070f038035003020090f0042040b040a60021640600c0400083d17041801e0382a01030300084500c0040d07112000b00240618000f0544500384c040c001c4003240e1014000c0040c01050003400c0200c03240360740c010a001036281c540703401c180d00c40d104100102b51a4201352080790021400350b9255460280c000740c800c9140450240c404003999a1070540d0b8402903e54451000a1803080400e540d4811444e0200010345506130031014007648100300344001682c004900c1e0007448004521314108140045420450040000005070080d02161030080711950109d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 39393494 1250 39392244 39392279
    0x60c070506180307111201140109051008102007050307050c0f150c0106050622060e0a050409020102100c030c03060f060c02090a23010303110a0302060112170a02071a090d03080a0e07 80
    0x3032040209035140338403050307040c01d64070071499190460022100d000d015900a409404e14102003c500400401410411644458400c0e50550404910301007001818004040650000c50320038140d10501c4000401d07810001800d0b4601c90f00004040407030b10800e40120b002442d000300503d89948104140c807504d0094007124500024242c1000b103207146c02081203030322800000e0020590242010140401040708081c180c0c190321900200605610150041741720043c0d0300c0e40c005c03403651481c035000340c02c2e41c0080c4c12038401d1000c440c03000d1001c0b40d404011a04c90607012909441f682d26146118802401d0f8210154849100c0448455141c080905914100c80c440d40d030b40a08405150b080342d84820303d20ba4024016000b140040007441d01c440e044820081c0103125081b14030405005140382e03039101e442c010000d60001d540030840301c800689108990007c03441d441e4540402440010260100c0307003c010107000144002c0f40452111303520a00503800f12400310b4040d9070301d03400c1c5400c021f0f0001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 39394744 1250 39393494 39393509
    0x403050c0f01050403090e0402041b05090f0108090a1218080303060f1e01050a12020301120b0f0106080604090312241a09060d0905060c0705061803071112011401 71
    0x414a01d03400c003051060503c640e805584c0c0d0341035181800810b2140e82e0003d4030503070344141c6507811700c1141c00b410a90380710003401c04e0b200c9039a110009424000d0b0039000740f45090600003200d08201415401150107424686d12108007079021179000d80c02d4071001809010052403614410003c0741c2120000010b5000e04030882e06415800e018504001c5031104a8020000d101c0407414075540a500440103080c06c0c40c0301d0b0501d080c0710070368049104100d8000b41e0003009161003132400c1100744402ea541d02c0e41c104803804004901303076050400140240101500c510700a580c0c4604100c18103104911b4008108945c11781071040c01410003403094140350b042a40c48805058030400902d01c1c1800b60711440e03901c071800c204c07420203031003804000c40e82c4c02500142c6000b40d00c40e2040d01c0001c10901c280e80c881c0003c034001d13548401180c00c00302d1504100070114900c1040000d58200000000000c0d9080e241e40310f4045101c161310325011034018000400850382a6080081000c020981d6040e901c3c113171a0617 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 39395994 1250 39394744 39394753
    0xb0a0801050901140103090c1a03010f08030703020604110a03060c0f020f0106081209040603080301080a060b060702150d06030501050a1a030a030e0d05010605090c0910080903090105070c08060403050c 88
    0x294020070400e12021302c42c100f00c42a0b0a03001120b00d50007030300305660940c0980d490204c038a0355000c00c202154000c1c001240101c40020061101d51003030407240014100590003141020002d94003e5554007000d0001740a42040c840c07651026503031f03aa515005154041c1060107509000c510182540d1811107049000d40110012103041640c14442c04044440305d0005103000c041d84e1440e0070b5598008030080c0d4000381c99280120104911a0085000340408030043c4801042030812008039507004065510580f020840800541d5440d03181c0303002100c800e4020b580d0707821480b032036000400d025403009095500342002c00400203541e44c0b105c0c002e8480c056000180150760b43c100751301c444070100d004000c50b01d5000b41c0e26850500140c1d0b41c010500c558000640941c031040042c20000c81151983d44240000608024505201c40c098506040508000015040c21803080b901d900451101c1410002c3c082940c20a0000074034200d401840d191081e11550b05040c00c006110350300000901c62039104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 39397244 1250 39395994 39395999
    0xc16120801150806010801090e0f0109030521060a0e0601020c030d0201061503020c03030c0304020319051b0d0b010512030409061e060503070909020f0c01140a0e0c03190212070b0a0801 81
    0xd41c00e0f952240748140d4440819a00b44180840180030500c3c1e421410712404c0100c0060107000d104202c00c40d800384c0c44254071051401c041d031040c0ca59592140020409030403d01c015074845001100c01d80c3d0319100030b03280039903407080101c0c5002c2600c000d45916106a8482110306034041d40540155043c681e2450525010820250142d1061468900c019031041000070040480305001d1904184010b0a4403030340e00c51415000c269142c101d030207440d15000b16400d47c144070040c003204070580500341c032407807040c1c002c2e5241c80300100703c1413051710b0050036032107000015400140122805048207440401840e5102c008040459803580142d0304800c0f1b001b030000c00e440b8013610075039200380515624040c805007040c141402a412007504480004020320200004c0d40083c01220038907401c1405c849418a03200c9405001e80d80d01c00301c6c0003656009408030643c16140828400031402d00408403095000640c404114421a079011882450080c07200101e9900344030001171200500a9607120790698 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 39398494 1250 39397244 39397247
    0x180b01060c030801031b050a08010501051009030519061b1e0206012103031512030201060603050c09091003020301050103150507030501050d031d03071503140f0c1612080115 76
    0x7000100a008078156500400020f01c80301020390140908401c3d01c50361682d00c0002c0384000c0500e070030600321651104014041d605200100c411070915034503002204900e035840b181c0c3c468440e00712004211407110303418418806150491912401e040d040c00c0048031084100401ea2191401c40c4443d0300c0b00440c034002224800201581a500c140d070703104150a00200000e079203d034604d6030803000e0540b03420007034410071168038804004010300c01d480595150f240c0f5000f07003140c0060b00604140352520040c4420810160241c40601c5002c0e00c09484a45913005404648080396000961560a02001200f0081c100382076013200314032a401480180c49209041d41940c40c00d00955420a0800c441d0801081c460929241d809030861860021560301101081c09c2010903080010010b900042041c40c0b154144200010600c0c03040103d045402d26034000d9220a501404241c0e90241c0803400c0190a061603200038401688403041c4031880d800d0850140141009100e6507c15210320301301c24903003d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 39399744 1250 39398494 39398507
    0xd0b030613050d051b0102032706070f030b0301060b1908010807031a0402061201030b1902030c0a05130f061701060509010f0503090f03040305010207050c100e010806010c06180b0106 80
    0x1d662210240c21046003000d0100c2e529040004110a10384429942418608081c030043d0b00540f9485200b0301c1e450840c031b84130801c40880803c468540c0e44200104000e80390300c2a003060030480c00740b0300400c0c00f1023414002809400c0b0b5800c52060301d4000640320484400355408880d41c07140b2a1101907590381d0b40d08100303890321154800907002110840034803a401900320b00450748544010051420401101d41000e41c0c42001d81045409405030002d011004003c001041c03961102e1620035071651503c001d042d8454010500311406200001ca00d0702c5414203030038481000740050f4000a4145c1d541c07440300030141003000006200030941000007103031781071080040b90800d020603110135121007003100d0110384503840280403407402c0c0950003881c2c054007001d0008200a5008100250b2a18860b0910341e0070204299182446041c0101800e20320320b811141d0160003070f40c01d003019142d070b9541c14011780740140c40780c0c00148100c2c80d10b52010103200003400c40c51907450040102d060f880c0e0700c83d041641c40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 39400994 1250 39399744 39399781
    0x90c02030a0c1b03050f0106030615030c0509040f1205030105130b030604110616051b01020106051003050403052a0d08060117090c0315070305060f01050a0f0e060d0b0306 75
    0x1c0c0314148084040b55581c500186121109180e0354901031307036a1107042c140003141c003404c1d40c0399448072401c000b809590301940e54580c2145980c11078007465a52424400f503000e12505010310070240000d03003400001c000b014450307038110381280500f52907c0030061590340f00340519849180410a0308049840c544900910558050024095600d580d211038091003a0082c1c01a41f00c9800c200d0004446030090041040078402d82c01484098030a0f8a030b060310709542c0c2010750440e0b15220f810091940c894100d200c1c120f90509001a0070f88031401d0440702c0d442140c40c80c5183d41c0c01c00e0803024009460b010580b205056660545040100781e1000f2143d0342829500540043c03500460b20958855541460f44c2084404d030484808602e0000420f082440e0108809403d40c04003003082181c513054000c4076841241211000b80119030407002078124002c5003041420060010b1510b081c05001d010b01601070305005100944804008900502528032191010f0003402040007007501303204800d0790003a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 39402244 1250 39400994 39400997
    0x403110109080306060c0703050d0507210813030e09160206070206010e06190306050a090506070f050d0b2e020c030303040804060302070512040e040303060806040f030e0109050a08010204090c02030a 87
    0x91034880d001045400e802003110610280105d1b00d0000000e4003c00c101c04215009440c1c1c00d859030601d0502a45001003000c040c0c0dc80c2034150140311505511203021036000c0080c0040b966164070350f080445802c140050026000307203141c2c01740410b20366128420900c140c41c0ccd600f01c0e141560313420002c0b62241400c0c42000c4844404030081120b40c90f01e0781000ca00d101440007010105c0380c1e603495200540c0d1382500c880c410655502e60400a00c8010f01041ea80702000d400c00c080c401c2880d0b0401403081c450305d1031606410707079141840c6200344d460702c0341d03902a07100c000341d200c1d009044903204c80c1d400e4041c0c1107004003510801c4401c1029090100c15648599001003240d0700b003034a469030547c080c1d8007560040303070f0070301990014030044401340303020300060507000e400e0701c4040c1b038103140c06001c42e0301981101c0203c1d48400c04100000b0b8080c00814200b5501d45000d10000700e41c20f0041c1d520800d990491540b080040c1c0c03000c1484007055000d00b0450710a040184141d400031401aa01ca00c40c20b0106030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 39403494 1250 39402244 39402247
    0x909030a021f02120f0105040b0307060801050103180212010b030f010902060306060a020115090b0306010f140d05210904050c0f04090e0c0a03030305040308180a0204051b03010806040311010908 85
    0x141e44084420301c00c185003200b0308058a032401c900d1604000c2c980448a600c41c01c52000018400740c14a0702c40c00c10403540c01e50041c8051800c00310003408070041445114105512402c200850302e829082012103903030b0203054001341101c000702040c040d0000310070b454000d206183d10203a900c01d0500840f5403564024140d180345440e10014086180d100141c1c941c190340d2074100141c0503040d03c0120078000d00051030b00003011041d01c02050300340b58040e40a10400e0404060a000702c000210074046820012909400c043c0c0d6103240080c01c3c009490703801c07200c100320f001c5495102c0c0d405100900c90300c00c00b02c1d01000300b9644c40021f041c2c2c5005004480c0711142c0148403c0c0122002a4131240c600030007401280c00703d8140e00001204104950801c40012b0345030400c0c4070815401024a81d00440032004146054241c2c070005580c40b218114040d2041d030f00c40c800304000007130485210303003050344596907290790f903031944900d40d501c40040e201100042d03803441c5d04021140040c03107049410350b4007d14a5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 39404744 1250 39403494 39403513
    0x3010b0a051b0f070905010e10050d14030406051c0603030f080a09120f0806010329010c0807060605090a02030603060103061a03060a15080a020a12030c0807030e0909030a02 76
    0x2200d958100d880200c1055401d20884031506100300818043d120600000b00308039405d001815050300c3e81a400b000d110155034040c0140e45055001d040159803042e03500e440c1074001420007658040c400386107030780e09000020700840c009500400810300c1c015811500d9858031411007445040369240c0c48003800055200c1d014403580780c0300b0100150481455070000c0344010054688681903120204a81c0100c0c01c00303607411500c00d4010044951241003404d0820a0320010140b4200b8404440e918410700f000c40d15204da40350f8000c01203065a59000030307509171200340c9490510000c1c060303405802e208404010002d0013030f06460013228481c02011340038001c180d1840d43e60801400c0d5800b0701001d244004d18002d01292000c10400384502ca840e000030a01c140c011881601070300e5240c101c9601030300b003a5110740160301d940340008201c9810030400500c912013428200d50404034400010014000051030806043d440500b481c08940111240341d900c2c1c44401e003c40c0c1d688100500307000942c0018061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 39405994 1250 39404744 39404747
    0x105240303070204021e0c1b090f18030c010f0603060b09040807020f06040302060c012405060f03090a08040806070f05090f04050c09040603030c050f0303091c02070306020c0604150203010b0a 84
    0xe40030b000491500808003010411400f003847e0401240c0495a40c0311110f10211126007da81c40d42c14041070b40d441205080161800034032000041c580a0305070a481c1040401c001c0c108200c441404050780200840070001803a2000b0b81158481656841c1c188451a9003078a400380195004031383c01070704286802c40580c24070480e003804075010365010300180030000160716440000c003044d0303200c2c400008186507400140c00c2c14a503940407250030352458800601032500c5010841d07030307018401080142c0300d81e038030013040d0300d81508003a00421104001c64001440b100000d5098081c02d244d499410011410001c200d0700e074011303c00543c2e480b04040c285461141403552003070790881074101c0c12034075210f44240400d06851035944202c2c00902201042c0303061220500c580303001c44500d030000e0361450074040541d81c1d84a18100980c0c80582c2c6600b41d0012035802080003600442e88008195101d80d8804080c80e21a00c08031815581c00901c0c050504040b111391003124182c81c0050641800c0900c035410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 39407244 1250 39405994 39405997
    0x807120506070e06041406091005030a0608010501050117040501150608010f05030a1101030b0f0909030d0509010510150c05120d0e0706090b0a09170c011404030506010513140702010524030307020402 87
    0x181ba411182c1001003480c20345601000100301500c036110643d823401c0c011010811940c2c203610035030569240c0b0f0018091a0780c40301405d039036191a0842d580490b100e600b09a80108088a15115400ca1940c030000f05660070240c5a0304071491001d01007807155441091640701d5400b04001440050005a01500b640c000c0d0b000c0c1c00840c0700501200d0700715a810010901100c419070750900140c4c001700d51070400001c0740c09071a46c071540c0800284403501340042580141002e0307003d603805c06185040440040c81c0700e40e0402015642010441e040584041c00d00030712b41e8810b0402c07911450030b16603107941d400000698582251040d90700c14078614038001e60710006410840c001010443c01502c0080c01415081100090003d043c0c05000300100c044005404030f07812809400c4c80c00b03424001000401c0c03001c550f13941103c8042d81d10321440303078aa4080740c004285240103521900f00d03200c284400d403541580445d101d02c09050881410030f030b0010b0720440c40c880b4072071b0255069208016035001400c140c0c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 39408494 1250 39407244 39407279
    0x21c030209030706050c070f030209040b060d060504080301050108010803070507030311030405190801050f041e02060c0609010c02101104051c021203090427030e0102070807120506070e0604 83
    0x50010308201e07440e00000e00b04110f40d4403d40010f1404503031843d00540c284462802048016100256070b4035607804641d440748010300141c500b640350800507200c1e80340e000c0507401c8903900c01c004001624103450020600c0d002030060b0f0f4002030308000040351400d4000111207000d60404000e0044a01d140d03404c441e0590740d14009040da02080c04000341c02d8030380c00d070188010103042d180d80640b98240752a02e42158001041a001a4100c0c028032011440024000b8070010849406005905250001c2040c6208031031002d00107200300010800c580d43c040d4440380c601d414503400e540121110507a580e003950000303440003039210010442000302e49800c400c401601d13401d40e000c6030000013403a000240c00e035804102e01c21550f08001940140c1d480e00d48500d24088145540c00c08046120401c02c01c41d0304c0121100a00303000305150700d05810380c02081060000c065400c12114103c0d111915510340b02c2074204110341c0c034818000031a0916001e8001240d0b140e070003616003070405150041e15400c2d0215203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 39409744 1250 39408494 39408497
    0x60a0b0c01050a0b0607030906030b06040f1d090606010f0305040c050301141b0a1d01030b030601260309030a031209120c02031006030b130804090501060e01170601021c 74
    0x211051144040d220408800c0300024142c03400204880c01d440c0c110503480d00c030354810411040020b41001c5031a080d6010b500d00050303000c0130036004c201680300300d8100c160558120840011a0200005440300c4200344040e040041d480d845092944c81509032015404200c81c03000c1000074510a602c05540140604044040e032a078800c08a800c40d1300b00d900c2d42e6880c0324018100524007a50350341074000c001c40035141519041303107510000d10b0910301c0c6903501c548515210100101d45c0c8a03800c1001c0a0500500f60383c900d50355900410900c3c548902d003403204d000240300c0295066804400e0b9410500c0240c0500304a40f0165070803200c2010030a00c0c2c04205039181c129001181840d40c001c49400c0d481c2c3c030303142d51500355801018a485544100c2e400703101e04000003400050b4243c0d91940d000389003803842c002100010301d001041d5000da030b0040300138680f8040001505a500c012480c04030503081e00c83e841e24220314400e1007180c01048030200d01590214060b841661944408001030040380d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 39410994 1250 39409744 39409759
    0x609050d02010c051804060b0c0a020306010b0702010507031209020310021306050403020d2a0303090e060306090c01030c05070203060a14010b040e0c030c0d0c0c0b100602060a020a0504050d060501090f02180906 92
    0x200c900500a030341000c1e000001c16401301e22402b0442c00c1c10003641d40540024408181090300c281c5c0028014411800002d040044900d40d03004e0030102c40d0090240280d0003001e032500c0201c400c090900035040388280c0404003c081c400064464050400c03241544d40103004054041066160926441e48028203100d0041c041070051a400e90114990f0002c2d500c01e940da01034041c580761080900d60390190045100350405403e10440c1d25000600341c04070311081c01e0108008420341d00c1030702d07140140840a07405006441c200048406540c0c00302c0340320b40e1141050407050340c0b14040c1d203a0380d0180c0d005104a00c00e0301d4020602c52040c04000d50390180c8000e4a0901d80b5900e4400e0a041c0c0703100440400109062500640c10030410284155010400e0f12564069500d008030003550b0f801c01404400702140c0c0001c81d4215203100b0070440c1c000e0f01024100e50820801c07854240004c107824461203a1380b0789413140c100d0200d2542c0c0200c400f1000780710003d42040d6041000c0110120001d06100e900405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 39412244 1250 39410994 39410999
    0x110c123007060c090510050d05090f0d020709150308030c09040209040608010207060c0201020a0e0d26040303090605030c04030b0603010e120d050114090106080a180609050d02010c05180406 83
    0x1030010040075898412503000c10301114034a40a00070000da500454070604e2400c0500481035400b5042c1e4102100c240000701d441d031600b040a81c24000d044080960390300034070407400120b0740c0010b60b110440c2c080794820491904090b200880b0403040340001012110200003045491903428007038001111f00a000510348101030700018100c0c0c0c41035205e007205035008501002800b03d2441000386901d0140020f5192240c9210010301281203e0090741c0b059604604034024410120b8072303410220308010f03e1100101455000c14043c5e0040d00c000c0300041c07100360300810940d110302c4c19a40240c080b1420740341004d05540c2c0d0b03003d4521004166541544d43e075811100c041c2c1c0e08101010994903048001da545400640040302960416049524190358000c9038412684a01c00d009045541c03038942030455480710106c02d0050840c05184200d00d01c06030101c902403041c1540981e000912801c1121401140e40809030709940f130034480800403500c00d21a825210303014640755110804010000200c05c0d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 39413494 1250 39412244 39412333
    0x9031205040906060804060c030b09060409060908030109200408070512010905010507051308160608040507030b1005100314060103020a09080303040c050907110c06090a0302030d110c12 81
    0x40e003076804080000c80c5c0406010500005101d40d1082202910781803250701c4c010b0022503141c4001500300f5010726590024070040c460607600c10010a6404102c00d41d60356951040500038005500109540184d05010301525004442c100d03002c0b00c950501511803546003c0801954215803258100c0035500e42115400040b0203228862042e052615520707140d046180301d179061211184c01c0070101e40d00841c620059110410700c89001c81d00c4615010387c9595803850030b182010f19542c402003c6c8206001030064800e00030740c00c2c6050b03031000d9949401c880c1102c1022429110140c0030001e4440c040c80c01f203080e03075200360000c11900000d414100d04031a40e8075103e920f0360b4001c0302c0c2070300c07820b81d0303d0b03000c1c0420300d85400b525810846514191a24603d01407846440d1440c0120291103801e0016080d031081e10340460b424001d5400500703880d00c40d602c15a001d0001c00c2c40c4801d0701c00c0e6001e1010494018946540d00e169441d011500805e402e03100391645210001a5440283e542c09400302d501c0c0c00c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 39414744 1250 39413494 39413501
    0x21040b07120e0a05090a0c1107060309060b01030b010e090405030c03040603020d0606020601051309291f0810020d1401060203041a0406050906090d050d030209120a03090312050409 79
    0x19481006000400e400c2001c0050140200c8140c01d84a4400b04800300140d650b00e05885800982c03908001810240e00c4e003094842a4145070000c400c0d00412034001103e6806038070405129014800500c96240a180118200c074070b018444c5d808142410b8800e07020b410060f11199000d0312840450303103402c00302c0031210f20310780184d4031501c002500012040404c00b0907000340c400400450000b00341d25410f1000280c8003070038205404200558030303503480d814010620750801804145076291444114900c805151000048600c1141411444c254021111908104038100c078015401340400d0410b40b1103000280d40110714020704244c507400c0c96041000301d515894028602c03030700159552031900300c0384e1144c030f2046105221580002d020822200d904841111400d00045031030580e10702501001624501e0304c680040d06038824003c41904058050b03005003242c440844441c26942a1301315503543d80e24200c000140000c10107101000011404048050030f00300070700b407031814951196848000c0307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 39415994 1250 39414744 39414757
    0x1120501090b01020f03070503030105060f09060d06061b151817280e01030b0409050a06020417010b031002071a070816030504020a170102040317070b0c0c21040b 71
    0x2007640c40c2e02c0c920056030100040039050441101950400c6515110301d5103074001440780c0381c0a100d00043c1d204542e01c8840446020300d2001340055240c0c420014420001c003428050300020940b9280e01072111110742443c901d007954083c00001513a05044d6114029240c60001550700c000e810701e105001401852207485149a84450030f034403a809101401110842c8804c03c2004501d501d40ea440c58690040c940d120140c000e0801042150590000c20000e0144500c045c005000d8070100a04000c440d8004208580c3c006000030303a86202c44a00038221054656003e5040c5d02842106a42c10f100d9000703801550f0181898040942c6020301d0a140b603031041710381c58001048a400c1040c0810b91103240100000e0700d1404212524140e408559100701c00d0098108130107804070000c01184094046902543e0302c8020428074100c3c2030803102c2d00da00301c05011070341007030008001b038a0b0314020010740384599042401490864151050f8200c1c01081a42500c5203140800000c181c404c400b0005060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 39417244 1250 39415994 39416009
    0x40312021303050a0318061d1f020a02040c0e010203090405060d020909010b041802030a06150807080a12030c080f04080706020a020609060f070c0303050a18031110151401120501 78
    0x850b1364580c9401400d800580b404c9080d8034030300b01c0052010592046400c0310304041905d10b0102003901c0000540001040130181145280d614070144641d68080f95195080d4401d032400e100104600710103444400c44141418010380c801e104052844c50300e0b410040e00700e240500006000000307500424070041007250740300000da440d03040e01081800c0901c210071000040307820540d03254400d5030019891302c1c60140007400050321464808104c0c00c0d0951100010300200080324405940c5d03004154540c964181e050310380340d40110711100182d0007030040038020174003641d842540e9550100c003510101c5024009803058401807042d4030024180d4802440c2c0346140381c005003098a00007200d00c1c039010000300400f540c00c5003202032052080d00b124280b07111a031302d4240840c007a519140e07a08028410400080c0107040c22281c29000d064100d010a015442401c059130380003070790b0854000030758901c2070024801e0140f0980400ca60001112400140681494103c01c1040c0f5a00800107a5070217800844 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 39418494 1250 39417244 39417253
    0x61520061e0c030105060318160602100e0c0303041502010e07090603050c030a02091501030908070308090d020319080a0f060305010203010503070e040c0303030c120603050718021204031202130305 86
    0x40707900d81100d0308180c2c04084202420718544c1003901044803404040e00724113042d440662201c4038518140182e05e06001a000c0e6032003002e0350780d4002542e8400e10b04032024041d180ca9622688004040340e841140700018005503d00341c0383c0390307010100c05064200c000c215541da0329042c010050a0004400038881c030000810001d00b90304000e410300fa8100d01d414400d44c005015400182c841030842c0303034841c1e800898005a0788000300141c2c06003000440041c41c030080000e900c0201500f210f58035000c0e0000d101200c00300e6081002c242e07528400e611084886490096240482a100c0d800e016801110010086200031504441c030068480a0300221043d0350003000600c2242400c104a000419451030403000740e003804e8030f0310781c0c220305140009020035480e4001941c20314012541000f1000d03240d07070100071960b52420043c0e202c014900800c002000d402c4400c520801c014000e40344800750a41d240d91007501d4a030381c00d0b01c1200a00103040300042e0240322200303052a00094002c0118050005031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 39419744 1250 39418494 39418531
    0x11030c030c060615160b0a060b03010b030403030513050601030f08040b03040c150203040518041109090604020301060e04021f0912050106030c051516020411030109140105030106152006 81
    0x6584844010307134049004050280464980d9604580c42c9205d0308804550660b0322182c201c1070180040e40c20103a0f03005400400060903102c5200214807030f034000c1e1f8007040503840b5000815100070908a014006901507001440803a03110642031405601c680105441d103692025814143e8108031002d4984100d03000c81003014265200f9030302c200000070310103149464209400141c4000e100c3c034024810903807910006082050942e140340c178101c4002c111903403038601482c003d61784071400c8400324003950034620300049030000010f0b000d0140b94010320100d4400b46504441e074031315082021200070051740380000910082c940c0785901c1c81d64002c00001c80c6d85815801c100245a100ba0711080c043c03480c540d140b04c00202c00509580500c0d401081031002840640000b40151100c81d294201880000000044040460380110340c0940900f0716042940c4e83d42040508882a51080d400c2c082102e07580e22a1443c0b10701c03121030504640a495440144502d0162864550308442c4110601c2108009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 39420994 1250 39419744 39419749
    0x30f0c021c0204140c0409021e12090709020304030509010c02010c0b0106050a030b061e030a060504140708060409030815030304030501020a0f090f030c0905060d05010504150b040e0a020111030c030c0606 89
    0x15048130341d40444c40001c581c24641c850b03d400d4400c600c103011b003d96003c41c545500c150006000f200185052240a0302c0e030014034108260408203980040f064400d01000082c80d1506000f600d104d10742540318941003054010040d203402c010820120304000107440240300040860622901a20555864540302c603c500c5028080321a201440351107000c061142e64100b06aa80200100d0380d0000100c41d01c0361520506500540582d8100a038860709000d01001b0303414581e4001072190b6495555000552117520600c0100d03500314602800190300e00c0e000804845007010440c0c007000380603007281e00d000c0e070741e44503142240c000340c1550f00080c3d0300c3c802006542d90b101615a01401c00c120381210b40d21b1454ac1d0f8003c3daa003a5219a842003030322580050b04541d035241001c0d2106400400030300081c039151501d4580801d551442139405860b2000c45450b50610384a081c551080020062003211181d0300152003150845007020034074403007040503c400c21f105002800c002500800241241c0c28403030308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 39422244 1250 39420994 39421001
    0xf0b12011a090405071214060a0b1309021e01090306050405010b010207080f030a08060109080d0e040507110309090a020903030d06140111030d0506040e0a0c030605010806040b04030f0c021c0204 85
    0x1510780c0b1500e260b90600001c181c0204201007100c2e2a2003003002c5a203001c1c503000380201d841850080c000c1c003e01c010400c4100f0160829245500c044940501c94120b900b241c204851842c50b02075041b0400b85c0017001e00c5401c1d201d000350112414108800750300c0d501d81d1400d068910403901124641d450340782c9410b0550701004118050003090021708101d07081071403019070b64003600100004101c400f001050050f40240410383c0a403c6c10380544040540c42e00018120079070304d6002c240504d141c640055081031084200198894441c006145084c2c03900c1e00f0802511000740c140c2040070307801c111201d41580c081000300ac2407006400c0110f20285024917456070840580c0c0c5150600906c24200400640e012084401d2078151110000d03058954001207070041800c0340d004c51300b512561400009002c0070fa18004112489007000744500c0e80c0316206035072200002e4500421441c80030300400d00090160480c0e640d10450b510300482106810b03000220801200410b2640130200100c504007942001e00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 39423494 1250 39422244 39422291
    0xc0c1113230c0702181f0e09100209030712020307050d0b040c06020d27080f0705190302030705010c0f120908010c1718030c0f060105100306050102070302040f0b1201 73
    0x1100c0c2c0e003003503040d8004c100076007107800d000c0c00d030300c0010b80c00a000140303c0083d844512000e4209092129240c400020170204291000403461040c0d6105410b4555280203ca07024071014001e800400d1038185802c0040c02000000caa240c080c4040100e0309844200c028410b00b03003c0d8103211080c0c01e140c2040c1694003402e400520464128185d58940d441c2c10034201811004064480100403162401c0070100640c00d4000d003a042c000c000e00100c12890005140d400d4501c116402c000403403d041d00c491447c2450301c0001d4260700880410080340d030150004510303c030f014503025046143c01d0760f1003200e6840b266210001055065005000340340091241d010701106030300b42004801400f40c5403181d0a940100448011070400c85035000a14003441034030100341c2c10804803021028039103881ea450302400d0041c54001d140080b40206a11320a003c1c2908030f48040e00030f01b08150031602841301800e03401c03031181022911440300d4243e94031540340a07040700c6a4040002000540c03d41201900c0c500700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 39424744 1250 39423494 39423511
    0x20a061b020d0203010f05090d0912021302090d05100203010609060512010509090a0b010e06090709061706060702180613090201050d0c0201060812090a090c0c111323 73
    0x49852520100050444140c254040710203a041c03a05500c0040d001d45100c0305c4d50324156050409203c09088001011300d60741c00951502030400c4d40f2101216035020721500d000c3e50101d464400300e0141600d81c0d005107900e140160079440a40f4850b2146031404030300318042800aa8000010400daa90201c40700c405010646450342c9017020242622000e402e042c09020b1140d105080418240c04081096138002030780b000ca80480b0b0b60755605000d1f1510b4046030b400380500840710001e540c542c400c015020030f0703508640750079003a0f11a1100241d00388800800c0f01d42c100f9010045000507903540420b00c40000381c0c1d45014030582ca882c04c28006001b0009000360740b4282001c0710040180c0c0c01406076200310340100d000080141001204a001d07089552040c1002d001e048280d54001a0190081c18100002c0d00c520a2030b40e90b407071384541200d07a4620b110001a0394501c0c843c00150111080001c03842c0010402ea0501065801103000c0710341040700420b240b1181031040544110302c01d0040e0703112550 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 39425994 1250 39424744 39424757
    0x17040e1e0114010e0102010204050a0b1c09050714010e0d140d030b130b04020912070303030506090f040b04060e0f16050d08040b030a09060504030c11040b0a0b1c0207060603020a06 79
    0x10b126280300c98280010006060000010720499964800d6040c0d03801071070300802440b4250303940c4c4600003095020082c03071803090420703107400032028a80c4c0c05404035440c4d00ca801480c4c1c461425150212a904030b0755018104101100c0e0b85035155156451070704840c1c003d40140b0010004080c00741d2070710450040380018503007003c4609000d590765695040200c8020640415402d01c4600001c000340314810f1503d520150b14040d0803400c079000114503086e02d21035101001f41d0340b205c1c01001202e010880760091540e500d40c000900092000000c00c2c0c0140c411400424450210b494407820701c40501c03424841a40300d04d0200001400c0039440c0030003000f0940300e11802d100c0d1741d102e80007140304600600d0304c91400007012850303410740344d8018140b61ba0000e100700424105807a0080c400b00307241c20251916107410310480b030649400d20030410380c030900401e00c008061905007154055048401c61040c00106050006407500041c002800018030510002888905600c100f001004860f00b214040044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 39427244 1250 39425994 39425999
    0x206180706050901120e010504021810030326090c10030203010b0306121002070f0605011502060615070606030b061002030307080c070f02102f0307060917040e1e01 72
    0x810400156034052504682e1003000d5401039906000e40c61103121417615001120b80c200d1010341c4840c0c01240f003100c3ca5001243d000c4190711801900351181081c0c0f0b18000d10820009002d20001044c1003801e04480301c8010500c509000103010448980c503032034005540301e8296240006007070b044000c10742421429941442030020040c00024105030056000400d145d00c4420100603a440111161030155584c500c0c070300d01244d59030034100d0100c511909040002c2490400d210451030109410f900401a40c0c0e03600041010014121000ca15650700c20425803001c06d200d40641030140d8001c1d500d4040c8d5003032030303020f00c9a00b00c2894400e6045410910a215405074464051500241e00001c00c0d84c513043d00d0705042116800b600002503018040c1c01460344410b402207041c040c903c0c1e8401e102c00b030103a580560300008000c1403060203456001003150600150b40c1d548200c5410f80103006100202040080c01c400d10750254104015411a010400c098845d03401403010130000009880600c0d0351 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 39428494 1250 39427244 39427291
    0x10b04021303020d08090a030c080105070903120e0f040c08040212010605010f210c020604060f0213120c1203050309010507020c06030402010302071115040801060f0f0302060a09090203040b06010206 87
    0x1c41d0100034400c04000c0f0303080090017100015200501d0005004002041d0b403460030b030514200a1245100035401c084c0000c0d41030303000301c0c8010200e03504800480100410a50116000c020314881180c0c0b0194080f002c0c90b0a842d41d20410380100e000ba2142c0c643ea0825004000e98030342810f12000306d903030502005012999018420007200300d080d041c43c2c0710405c1e0410003041c0083c0c1810400464070b01d80103c071620240d002600e03074000c40c0a490304000f09404070fa950001e0780f25401810340045150841000f0003d00c4c403c400c0010340c00307203805203091901c4e420030310401c00602c8010703000144040140450480284501038000c0c0c0240010490321400300045000750000800190526034040f5503801070186409500c2100d9600030b01496032500c490010310081d030028019428950301e04030002c200040c0210030700041e03c51800300001c182e46940e080041c00d9010742102d0041104074540000c491f400c3d070020f1400f4511940c090042d918049000900e010402401c9842d030100340c10442822030f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 39429744 1250 39428494 39428527
    0x5090a120f1e1a010302090708090705010e2205010e0c0901020d0809010b03010c05220503100902030a0807031e0e0d08030901180f06050601080907090203060a031a040302010b0402 79
    0xd503401009400106540d0000840b444071940024040c500d0041110701d60009000c00903050301d1003111205015141c1d504200c400440483d04117296500141c418005580290804d4868610007403801140500d54a00040f0040c60b002100c481709441d071006102e0542034000807980080722002c4182801e00300e02c0000d641f10b40b01c600349828454801e0110307a07182400c1d04030142d90070003d0000d001c0f440e000e900c001c003254480c0600c01102e00f00c040c1400c40710b06241ca072710012a0001002031002800c080e441900030001c11000300e915109e8408800001400325028010b400e02a417035001002c0600d645041034000201204810010714007880030056444075544104e0640002941362295200440140140050180303c050b64108803035003020442d41d503182d411524071070001402180c40b402d00650301840305131031b0703a5095000000280502d000a601031940540c0040642d410741e0390300d031200c90303c40300b941140070080541103007044245502405150803c040a541c03c5191280303161401009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 39430994 1250 39429744 39429773
    0x6150507030e010c05010515030c0a06090b090402130b0c01110909070c14030f0d0c080606120709050607030f030e191113020a050304031107050105031603061505090a12 74
    0x34807072107008500b101e900c56649520030643c0a8001c00541c01d204c0082002c0240c9009003030b02c207100c3d5464480160030500c88550450780d081d140c4c00c400502b0000304e4501034000d403901c160055400e0207101004151001c00724010300c01051880e0f5507440c6101000d0035103c41c1c060310000c0032810004100c172501c03505a116800082071030624405581498407141c51284881007000b64440481d2024004400c0b038001c00440c540104100141ca1218106465048084501302d46c410000e1080d608507040d407107205a8040d0003442c120200315194030005101c0d41207000c050740000c0c00c0309002c900c4240c041c0f01d05491400e051008202c81615420003460410500303500a01c404800c119070071298039001d030710005503c1d62180540d124051244018415041106c083e40054030303110a0300384200d030100744ac070141d90060b0b507640c0c65517036141500301118034807413840e008040c1d990324000361102031014000c1c146152541d602d0b41d211a45000c100c00c1040c1c5800403616501101c1004001500f0209000003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 39432244 1250 39430994 39430997
    0x20703080609072d1e05041a0c15010302010201050f0105030d03020d02090312300406020313020310051902040f030b060310110703030e03070b07031802040905010f0615050703 77
    0x4503590f41004440e0008401c0301e50ba6a1101d15011461a42030b02c100c032800c0d401280e8460503e030080d42c0c0c08100f1021903140d03001c085442000b0a204e90a484c0c00d896000d441900c4106241c0701007054902e10b071400a1001040381e41c1c400c00107008560782070041c1030b0800f0308041240b0041d410500003c1d25000c0e40e4032650189580021b404140402d00c5d01a507014080c0282625101010102000b000b90b001da00d64a00d03280000b40d480390700c0b24000044000512a041d803c020950b0340b076607800001d51002e400902c803142d82d8540c1a0059030100a600f00054200402254a003051500804141140d01803890310314014002808a076074a100c5000480c1e0300300d482641640c9607000070904083d43c401541c3c0c2080d041258414800550100500c0c10328441e80c0c00304000150712502c280c480c000c003000100b50034800404100001c5c0b00b42c101104680e104401500c1003003c0703500080489501000840d003503512200ba0802c00d1b0702a10800d001130500714904400415091750060440c42101c40050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 39433494 1250 39432244 39432259
    0x6100f090e07090e010e01050102010b0105120f040c0506072d0206030a09080c030408030403030210051e040c080a050105040c0b1e0c0102190e0a27020f1918090207030806 75
    0x382d0b4148a040704600074071842c3c0900300d030380d43c41d90200f40310644d09020701401356080201e94403c1d9449141210f004645010074031056807141e824008800700040c0080c1d0b00161001da005c0303220340c0d645004120591081c45110584072940c0b031820100b0b9806c103000002d540314810f0301805070b2500012250300c0401c010340060000e070580f602032545d016601748241144808940030950b80070010092090f05d019408442c000c4000c016280c0540e541181c580344002e400404000000320b8401e901500144590282c04076aa200d07001249084c103045010b030b4103603440d0b50a100a118690030341d42301800d002424145400b50b80584030000c01e22000105600c09000120240d5400c1d0a40c140c9540e441300540d507094408140f100201007940072504140720301284200001c4801043c0f80405500e0500203400c0c02c103000121008009411442007410310280030401800b09114912000f02d07009095100e0800460f40c1a42c0d9030f00a8140b50050b008040c41004803102203074000080e43d0740303c07000b00d5500c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 39434744 1250 39433494 39433501
    0x100203090114190903030809010227030f010f0213050a03050d0f09030203100608060709050a050103180b1e0108060405060f0603150c090f010306030803010b030403210506100f090e 79
    0x10000380318010900043c4841c82c080041e2103503118001c0303001c80703001c0d42e03403101591a403801d098201d01c24418010715040800c13001c000503801010500c1803001d4000d0940700e14200000c02c9500355031541d008035251550005091a45401c1014843d001d4082070700c0074840c260843d07699a0ba10400144401c00340210340007610001407003010b2690140d40c1c0502952003400030204ca13030002d0296402032501c0c81c0100000a01210306c074041143c1103400041020351120718017030056005100540c256007040c207515030400046040448081d01070000001c21903200c0d02144800ba50304241a042080e4039007000b810700010036000180700e45c00c000207052829882e140d0b24000f916010400e42c040030b040308502c04000303811030f48a000e42a5648190740c81e100b0034100d040110f0403901503020081c04c2800c244018801c1d0b540c1180515800307840381c00e0100364120400d18455814100004240485490380b00b00916424004032980c2d84803403034180780141420011000d01911500e0050a00340340c0c404c0b000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 39435994 1250 39434744 39434777
    0x70e06060f04080109030e0d0c060f05041e1505030c09040f020415030b03070f03020306010317071707030221030604090201030b0a09091b1a03060a0e01080a111002030901 75
    0x459030400080c0c1d00140da1660703a048024040c05030741005078040b501c2c030304183d9080e09107140ca401903d90303c407a12460903400c0c04002e4401202c0f5907070200820001f03100c00b280701081c1624800c41030952080390800c0c189003071400041f0048400c41f450400c5004e0040c4282007045d00c00380d661340310302150042031800100d1201802030150394441d20041c0003d10b2150850b5405a01151070048241c0503100c92035220800443d003892a80300007034250b840f1100400c08200341008001008015001c005c5c540300054444140c0048000558111120001146c80030150108944180c0422110142c1d004050008500ca031138000107000760b005030b0b1a00000f4045a100e07070f228142d000001482001010380300c204080040c40e17a240102e0341030344141c0340002c4040c00c060b000340440d4209d00c4420301610b00140384e058650809040c09400040d08400480e04400c40f03400c01c1c1c0601320034001450710060609202d491303040d00c100410b00881c909450710035401d9022040366046002800d20040c0080100207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 39437244 1250 39435994 39435997
    0x10110d020702042c0f06070f03020d090506040302061503070510030b0109051905010801240c030c06020406050c061003020603150d08070b010e07050c06041e06110a0f11070e0606 78
    0xb51641d101004404c01c100d403103160b8030501070460381501281c00322100c02c00480c1d51000180c640341c1c00700742e003680c407030b403c0a1090300108040390720031201003084d10169680c1480d145d81903c0403005600004200581340074008d07611040840308500900308549010081641c040940611004154075103a03c40c0843e40580307003010040002924201c1550301c02c8154448c8580c642c040c040c001132071030b0000649141d81d51603000740071103034620414454481c550141e400c481c0000007201401041800340003c00d4062000c0c000412403510b94560720b402003d10f42d41460f2008100407403001c03040005201580342c000540c7e60140d181101e0741c3c240d01009000078840400c7d031200404580c00003030004100300801503507604a420319001c03a0304545170003100361230034003d25024101c2c5600900c005030200340000c1c20301c4c040450b844180101c0b4034440d11008152a0043d0402003101000034101d0f980030340c800e4002e00426800c1c9800f0024003508d002d4070fa15120944104411601600c021070603d83d01c180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 39438494 1250 39437244 39437261
    0x503010314031c020a0f02030403080d3201030b011e0b03090a0602040803122208030601030216060b0307090603050c060906120405071a0702180a0f090b060310110d02070204 76
    0x3050f4262103058216078001a500410041c2c0000d92010040c0460b1400001a0383c1540e0b80300d085c1500703068825860800078060124810002171000703170159204c2030004483c0031000458200c0034041e40c11810840751004e4107038040c1540d0f02102c1c044400303481312100103100307540c1112f81d2180d0301d45640402c5861700c101d4010251460307100060000c0d003410004000c2440c000f03e2548694255129a142c2d03800304135908000300c40056114288000078075110007190f010605040040c10300300b10824210440e49080301c211159551421452080c1c40c00704070410040507800402d1140500319551251201040c0c44c841c0d000d448082940e003207654400003035651190303070a001c4100a00e400e0900b80e1381d49460340b0070304a89070401c60802045511400031603840c4c80d0060a80402178056060841c5240da0003894240080d60f150448001e02119005202d000760149849031241e040075410141005500001c019003036191108000c02d81040030b040e1440616100b0006880d10168004100a8001c61 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 39439744 1250 39438494 39438517
    0x90503030f0c0706080907030609061503050604060e0c010c03110a06090c06090f14061309060b0702090609010f061202070c1203020c040b01051602030c03010606030903110706050301031403 83
    0xc103000074400429030280c8152101081240d0140b5078400040e900d0a905035198107483e00524802d00100d42182c201001c5503104050018607034820551184103609150400c81d05500034006000034041603000e41032a60445401a0403c03070305010000c0e00c0c81c49420001420701640100a029101092100146203078102000740490103591401e0303102d240031801614040b0303072440c10110b040c011000c91402510300e90403140e281d0700c0312803080200d140c102c0300009084000f000310110315410140100300080c10001c13045519114241f0400c50b0707031840103080a0003120380c080108401c0e0365840d441e400701c0c1c40c242006003018400c00c280304083d21a004000d005120b201c0d20005005004070009d20000d402070342691b401c0c40c041c10420090310154040680002c03010b000440f5181c214440c66410b00b44020101c032010300f840f04c0803900b507a0113940143e0110765142c0340b080505403c22105010014000f01409c03d803401d1002c080c100e4001808040c0280859645c07501c4811070400032100030b070860 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 39440994 1250 39439744 39439747
    0x207060e0d03140c0604140303130816120509030c010503190504030c0501060f05010e042c0a0c08010b0111060906040807060b041404030315050102062d07030203011a040e0a0c09050303 81
    0x40c840c1d820354598041d00d003201c040e1f8541504c0c250424010003a40d00075040010a0302009000d5101c09410750011070301080f48104c1000601c0000d59040740c0c10214840a0300c40540301c480910401d070070001490703038407130610100304204001040900c0281058480e0580300007025201c906080300d140380c81410062441d840c220b0003207000c0009003410811188240e03520398000130003100380800c0d1100752080c002107501c0d01a112402e211442501207039009017000700e601c08007198071281800c1d10070782c0c41140681d64590400000303503400481050303003280350001407e481c1004a801c03691010020030152a204001c110803007000324507041034000041c028000d0081c95016488e07525882001d841c12008241380c00308610540280141f09000c0f104140c000c0c16803543c2d1502400468400001032810b40343c820707000010342d41d07102039081d07000c1d11181e5001616581400b0850b940718200380c039101070000051004105580b903000c1c01980c4100f841d607010407000c020384030a0b5002001a000305030305020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 39442244 1250 39440994 39441007
    0x30405070302131406180601140c070e150f01050f0d0f0603050309010305090f07050f04060b0a02161e030201030e0c03010e0c210303010302120705060f04090c0207060e0d0314 77
    0x3044d0400400c94169000162090300d458042041e0304074a07240420407a6032103400200c01c4c1d801050601800400e5400003490410041e0b0074900308405030304141c03c80100380050101d19416401501c0d060702c0d0503268200d6802001c6d001809a00172800c0d00f10883e140007805005000003600030460784c90030104103124198491a00644036082600300600007450b020001e11441d40000325040186400406804910b051200b03105584c0104401c0e50382142d1070750f8000031000c002038000d165001c950b9000d082540708082d8410801c0b0200d83c0300c0d82400c540c0784011075441c0f0322481d0748030859609081c00142140c01c131569034101440c5000060745940380026400d01d01c08041000d80c0c513000c3c111040103c18641d5044c00640c2080d05407005100d0b40f0510050005080034903070b400b90001031004a6401079554000991258058800c0c00c0c4ae402d00410304000c0d81c00c130b60113240013801060015040070b60070104014107548043c0d03041d0b44204400c00384242490301402404014855201c0c07810760b20903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 39443494 1250 39442244 39442279
    0x50418090204021303020405150a0504090f05030301120507080f1018020a060806040f02071104050705070605010605040303140307120f0e0105040c030c060507050c0f120307050d0e030d05070602030405070302 91
    0x15a05d220580c02141421b00048042d0340c6040d1a245030800108030541e840d081c082800010260b014045401a40d0702c801c18001c501c00300051802064040401e0140c98030703e1500606103580c40c2d000100c01e501580c43d100348aa4081540042007010b1400052040c910f071040391034098140c500a50050b102410102c0d51580c070548903403090344107540070b00102c82030280d980124494054050225240c0082a1320f00d4501600b0054000019140460520145482c1d0508480c02a4005004a40d000400b0010590800e40d498082c00c90080d0041c10b41c540900044d15100b80b503080c4601c0f2030765030a0403005000b0b255008400c00580b0a00070481440c0c5450441075028a0313000039100c64130340820019241303106008580e0030540c414060121940808244000c410464070381d154003581081e103020000d601040030300b042da0b0141c030041150411091015000700c51824102d8021b80118a0b01ea034a03d030000222071607141e100c200140da07691a810083c1c1452500c2d00001e6004000400642080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 39444744 1250 39443494 39443527
    0x5070206060405070c0b010308070c0b0a08060103050601050306011d04110d0e070806010f0b0d060905040f03030b030c030a0b0c09090c040f05030105060f0d140313030b060f0105041809020402 84
    0x4850542c2c00300450340701d640e41944c5256441c00001d00c441307050740c010b10016003070101500700c880c0306e40c0c620b040d410303200c8507551166045901483c0c0001d045d81c00b00401584e25020f05a084402030074050b141d400c04c81c0000308a42203500001c050781403561402812512642d10401c0d0070241c13810419280d900d2071440704081d19070121070f181e980c4512000400c0600011500904130307884580342103500351403d070040240da004003214031f920310b81d903d00c00142444103014041c03145224020000501019150190440d5070107002503006e1b1380034403501d1545460025460040c1034022203212504d84d1290720b1030071244a00020aa00154100e080c40702040e00300300034100b980d20200c1004840c60725001494225401251100d41c8191061541e41d0030307040560701c02c510a8007600b0555081e01c001000c2515550103072020038104110301d4010028080c041c01500d402880855038440003e0a40e00000e019020314000d018120107210803031203000c44540d01903401d0641c090029900d034034891405040d0b1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 39445994 1250 39444744 39444751
    0x1e0c1b18090a05030408071701050114012109121101050108070501050702120d0804050609030306010c020f06190806030c01050708030a0e0f060a27030c120e090a02030603120a020601121505070206 86
    0x448c064540d940e080701800742a040e11854500056100161001104c500c85ca201390840320b84080d4491001d0ba44803030103040304040c00341030000c0c2400661100180b54120140307200740e50740d00d40341c01489040008541541207a000f464403580f10b01d000d00001e80811000c00034049684036900c00108040d0f04044040d100d80d0044050b2262651410480b58580c4400c0b24514000386050001e6001490081190030441034003070121740c10044502507079150700381e0001a07038000c01d1655040100610303007000460303107041083c40e016040148650394441d032804045c18506d541e0340c566400b032107043e10401550500b4042c0804643d101e08000075103c0050070130010703040c20360a810442c4400280d00307090103403203107505568aa1084c005500c441080188507912901001008800750712955101d030071040c0181540000141d0381e04002c07003003603c0c20740c0800c8280d44500091110144264000c502141103481100451080c80032610b07060b440911a049909038081c50401403080d0740303500003100d610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 39447244 1250 39445994 39446009
    0x10e07031b02150a06090f0b1003020f040b07050309060313200904030c050f0f010b120a0807060e0114040303050708010503070b0403171e0c1b18090a0503040807 71
    0x3061441c0d03802140006003115a8400750703010401c90072001030302c0384580d544034021080000381640c8a0114500340d40c203000c0d0341400980c69242c440ca80d8030704100003401074206810214a003100702e150b40c078050300603840381042040001c5502403c0c4541401114859000280290303607904c1e0800782c0704601440d01c0001d40300005060714240300d24070a92035280d4940e00080c031005113581c50b40d03001c42d51030454100490b1940140d48034404080010844403413903441d400d001190f50800a01801030b0f001a4440c40c414aa002400c2c4038080340d4404112041207070058000f107003001c801403441d4094115036160708400caa4407810001811f505500460051714280c7e0340401c46d903652000c05690b4503190040c4552880100420000140015003c4c00c400400c1c08002e401c20071070400801403000f6001e400790311284c000440b249400003e000f800c0c440c01c0e2996458414200d04804200c0200c3c0c00b5000b40f4640d079808001c9045280104520320b41a90300000302d99440f81c8840d12241c656917148200d24 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 39448494 1250 39447244 39447251
    0x12040c090f05010b03040204020c01060305010e070501020111030115110a0503030c180f01081311030304030b0403090f080309060a020c041104080d0806030316030903080d05010e070c0203120a090509010e0703 91
    0x7508180c490165a04031081c03240701e5410740d15030343c080100030f601200341410259a0b030280000090001e000760081e0200d440c029200d214074081c0007a0035507650380020a1514010070042c00300c09002528183c0940040c035000324040f00c00c686c00c900d0b2240d203c2d405011403102008102c96004900010130b089038600300205100190a001d000300000d04e05030860100e546080002e996070504038100707403e980a0b1946500c040c0071a0701190940d0f01640040e260070b8010810403080c942c029000c200140300790840e0340c4001c0d10f40703094a1344070b018503440284240030000304620840e10800c040044020018410020620301c10150141d540c0988511882c5000f848010440140107900c0140308807405006146840300c80c1c03402c505c80030800303001101031208001010000c141003201601500c040c01c2e10016182d41081e02000000070300520207010402140e0310000182c40101d0700300d100c001c00556864603400b4102058a900034035401c00c540100110f000020035a00b2940c0050240c41e041c0c0303040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 39449744 1250 39448494 39448511
    0x11070b0310060f320706020708090306010e07170a0608010c0e01020f010903080a150e1006140408100b0406090c0806270f0603011107060905061008100b0612040c09 72
    0x40e074010344400802034060401d00102840b00d8040c20a069107440c0100e1311515012540da1100202c1c2c01010040d14090400310310f070341c5c072811308000650240280040c103540314940145c0c01001a8130542034404e06000c8100804e800300c600360001c0f40984401c000920102c0071010f00140070304940d40b80ba900600c960010f50949800610030203c1498069444900582d40c80c003168000d001400c4a200f0800110000003e0304000c014086e409423400b916101045480e203031004042c000001c40511404e036007044104a00700340000c12030102c542101020500920b50030010300140025408081c409042c00d20820a042d400360f1800e100c0c0000310303030909000c0841040382031411b40e08068108072120301c0700030510044001d81000e1380100014001f01d00c41c403040c4d080c0b240e5604040011251303140c55480f40020403e040c01416442400b030f03104d44200074a000055a0755000c01d0189031203656481c5d48000303aa840b0002125540c400e446c855031075604240c5004901d0340d440d071040380107091030001c80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 39450994 1250 39449744 39449747
    0x10305010f0f03030c110303030709140103020406120513020616050601080c030c220603061a03010b1023070b0105090702010207020604030809130c0801060f0201050103050a0311070b0310060f 84
    0xc016194070394818002e0070300310303541610b4819400f1410350385440b01c0001d079102903070300b00b0007540b050076142d60f1800c2e00c0d49000c025003489455242c0190600d401400309100440d8401e50003d44a5500100850240c4811044a5020009881c080d40221000582d04802e420a84140c41646d00c5a400c0f1607960fa621a07041d51074409400405034075800034810780145281c51415030304502c03508603402750800300c0e80600008440550380103c0d19035403181c0311036001d0b00c8940c1081c0c0311010b007a4024000d082080d0009402d0405502c01e0300140080201301e204070085894001c1c0c40488515039a03690342c103442c144810b01b11801d218452040c0c0402000034070007071040c02614002540544806d0a250841d91091082e0300a6580240c200d030a42c08500102e04a030701510065483d561a100c06650503c00002c14000d100c41c840c60940e0704100040000400006401c1c059980503d460500341d0b000500c0d480c02d1040c150700402031305002105108400325503400319021544c3ca0703290514003d0b4501c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 39452244 1250 39450994 39451019
    0x60e1e070b0304050304080a03031509090f170f0c03131505030c09010e0301090609030e01032a0302090607030207061b051c02010f060806010509010902041a0c01061a030601030501 79
    0x10000426085140200312881c5200003543e0030074403a03415241420346805000e8586654103c1c2a00000c1d11001c0608203001d004d046600030b01242d810034040c44030759842d83c52014500c0c0e20024401024920000306186009080d1485808124440396641c01920403d0303680c0d03000140780c00c0b5614001000092a41c02208800802600030786426084daa100328250310913070031180d0114180071032000c0640607a40c0030b1141000d418420302002401040c98140140006250001a0f040c1403504400044003a00401141c01c50881030f070281d96901c07141903040f00640100c500d06d50700440046003a0041540110b0400162100f0381d88507581f502e019052400c50201e0080042d00d580c11002e40440800b684103218842100c840c00041881c462090820ac1184c0c030542c060705480e0031a070018002480c040389154014003032903100703504050a00d25901341049505807001c0c1d0199001032103d9207000207400c040014036404103d180d0000c0d181020150380e41c42110380e50300080c944000030175110074004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 39453494 1250 39452244 39452293
    0x30105010c06050718080109030e09010501090504112b05130b04030e030708030406030b040f060e0f04110301050c041d07021906022503090b0403050c06030a020d09060e 74
    0x75242100d6481c80d4507288010100641007104200c180303040311004041c000d11031801042440c00000b40b5840c503041c003e00010005005500c03c03510100100100d0380e0105119042c0c034401c0346c00098090103009030034031f507200303a42d8903050040d01c2c8040c90b01441040681d03447c1a08100e1001d0140340d860600c04c2c2e50481c142a0020490744403500490040303403081c104004c400380041d044618585d02c481d856840c0d0340107544580d0000303489410440d200e08003030186441c444004601404000e040082940d070078a4002e110b20311440b041c400050510288a03450010302c5c00241c001c000a0a01c14400301741c2da400340c0603010f0001491440101c280742d4a0348501d10a07501e56015200c0003050280030641003c085806a03040b58003884501100707800362100001a0080100f05d05509100c0d25005d00b41080c950712000300d09205001c10004620302081c1000100c100b142c1d0590741307680343c603130020090094028a054180c03500c564082004140d51241c10720750701c0d110480c3c90194084521120010310103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 39454744 1250 39453494 39453497
    0x30506070207031709060c0609100c090509150310020a0f030501050d11040c02010209090901090507081501060c081c090303150b070b04030201061e0302100f05180105190509120303010501 82
    0x340191041e15502002c0c02030845c00800061034000300110461519a007074030303101071a8001070000540c04081d031140c2c51325410142031400f00140750000092840f14000c1440c0b0002d6500f084002c80d40d50305001e044103035054480b04548900d481320005001400f0358030a200840d19101c0049034a20f007002c200101ea983c00805090103020440074403020b0180310804031309564003807003079008075a64800d4891251851200018200c0300c181002c1d07203803158540c40319080d504480004d482d82c6d110b2003080e906507400340c1442d03002c2440600d401002c900c1000d4240d4160450305450303e406040310b1b0005030815000e80d40500c02140903e07110f4030b41c4c06051281c84481c0c6402c00030400001c2c50406203552190082c000007072000d6549013088800c1c40c0c2800c000001500d8104148110314145840401d94911403403e21490490300c4c40161051040c1010b0280c10010841217500ca070380704104075468448500400304100032200009081900a01040d0b0b1107146860b070b85000824001043d207040f541c05 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 39455994 1250 39454744 39454763
    0xa050a0b0d12090b040902070c120201090306090203070b070809130b130b060405030d09092403110a03050f0102090102101a090a0204030b0414010b04050105060901030c0306080a0c03050607020703 86
    0x650340b90780d605401141d4000a00208000000d203025983c805800244400031016a0b159400d10b00740703200b400f90341c1015480300c900d001500050b03640081020181c5e07502400c0015412420700000e0310b0b1480c654400c01043e2000100c8108108011001e441004800d0342d0f01c070819102c420194042e910003544507604907400b04401c40b403040e03140d000865209006480e40340780a0301d407808603003421032007507402d4080307800a1000c0044681a1007040d031000300c01c1d40701d901d441c40751000701c200004085c8400782440710b2600020903e60380306101000110b034088111002188030001043c042d41100c80c815025001360008d1500d040308900a00d54243e2402d4402d1888030f42a40401c006100f010300002d0205609000120004d8083e40d94140650700030140c070103012001100d20350a450000fa48a809641004010001500c44a00b0360f081c2100900b0082101041080201d0080a055000413118898024a01c083c083c0d450f03000b00540340154240e800c80c0c0d80f028000d9a50320071600c40200300030103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 39457244 1250 39455994 39456019
    0xe0907050d0c090306060306020a200705040209030c0909011a0105030f0c07032622030806090703021e030403020105010807060912110315062d0603040203010b060d050a050a0b 77
    0x5181c0c4601660412428403e000315280d4440300c0c00c50fa00c1d40c00454000d9030005a0300e030790a40040c0c82c800c82829518014002c40c0007559095140d11035807180c0c501854012440e54002e9030140205181ca800c003400120315490070b03080c540e0180c00350444602c44411800c1e00801d2a500c5401268442d4000078501180e239102c044d62540d00303500c4075500740d0070010900c0104051401c0b00c4c98280301d0f15400c0440507040c0c1004802401001c034024981c41030040700c400198002504940d000b54032000c11206003107560f8880600354043e01c1030000701304e075210b070402c200a4403020000203180514000c7d4001c01c901da80743d0608603511801c901981c00807032120301c1d0030072200001040030581907105145005031400f6510100345400340500a2440e581105000c1046070b04040d51095088500311403054641c0c401c158000100714281000e44e40900b100100040c1903444c01d4100030440d03000030704495564421142084014102568400540e07410007000c964810014014600081c4008290f01c50544 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 39458494 1250 39457244 39457267
    0xa2a030f022d120f060108010914070804031b05060a0506010509091302010207240e01030506010e0108060a0b07030c1103071406071106040f090f1107080313020904060b010e090705 79
    0xc8911030500c42c01e100402001c1058002c404455024801000e80354545082c201c001429400050f009040c0152401d008140503003103031020715800206908121010f0f441c1c03814112032184045020f2722000540302d005000704000011024480e04026400304526141c81d001112240b10340001281e008010501282e48107885150394170906105004442d03a0350ba42d11005c03205600342c0d08070b40d030078141402142e0307d0b02c40d003201031099000c00c00d20303003040f40f480c140f0000b0b0701030217002090038100b00545000a0035034582031100c001074003241c6609a203030107880ca4000c000b076801000860b094464640700026505001a0350700942d0040e05071403502501c200f090001d15008203005541c11440c00420300e0070340d1142001000a01103200302d00748541d003007000803003d0303500e030400f001552458407a80742c840c06c8c65481078503002ca0784503989a0b80c039101c4040c0d605080a20b81c601a60158204040c0400c01803664000c100640d02078940444014804017044060601103d501001c540d04020042c0c210307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 39459744 1250 39458494 39458557
    0x203010b040b1804140108190305040b0a1206120317040b01050d0f0209010b0405041d070605130801050a020d2306090901150305250812030a2a030f02 66
    0x3069001c10030020525580010b01514056117070b07060001e0350b803c01844038010500458040078002c016401320301c1e10395503000f03120384614461000b4440001c41c8480c40103105400b111100c02041000307000903030712110041c800085403042107000c0350344080d0b035501c0d55800040540c45144c0140655085078640001d01500200c2408112a10001c0b110740310b0059071090341d010f001c2d05186034019200d509200c180411500c0c0c0440424075111081d2004d08000340001c0d040d402e4414600d881a2140800e062a840200860300445829400c0004000c0781d82c00e59400741651040800051100720913440c601e000c50080c206241c0360207601340000031014141400701c0c81e002000d100c00007070304030081405041141d20940088680d900140410020540c07013030070301c18101104890341c80905141601a660301d203001b0300e92061240c00800080c10341c82d1560f000c039106a044030250f54400c006036a00200f070401584021010030300c0c159840c0e00c806440c0c0300356407070f01c00c20445400c0705205181546201 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 39460994 1250 39459744 39459757
    0x8190e180a020a0e030303100305121303120c08030a05040201020c0603041a04210206090c010e0d0f030203090406090c11061003020f04020c01110406020106150f0e0f03070b1c0203010b040b 83
    0x900000070101341c8540c4007000118402d000140c4e0881c10302d41103140090910001c0488824064420300140d55100303045110703e000c40f94040d01c03c54800e10000401c0e2030741006504060b18070030001c02007015006958015501c586c0c402d9003030300c404024140c1004818002991302030442980d03810a02403100c042c0c0310709038005000f1003081d00f516511422407251030141c4212000107812210511030560803c01c40644080c600f424860301646085000c1040e00c2c2c00368401a0201c6007558806003454000c0c000c503140c21801420510090f1303140c00c0d40d40090040750405900103290810421038800b000b0403041d014241c4648103147e45459502044030f80a034030308003a94000c0d402c11050b03000403401d1007041780501c212601581c560386029806400c54000c0e52140e50069100e10346c21004950110880d003141c80141408140104100042030044160b0910242c06201c0c0030b10100c0c1785200f807030140c040c170300564445440105540900400340c0c0001e110380520a54284824807406540801034000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 39462244 1250 39460994 39460997
    0x4141209060315060c010603020f031c050d06031208040308070206090d11030913060e09060106083607090c0203190f02100203040c0302040b010203070b0f060d08190e180a020a 77
    0x1c610f0594000682560b2051615640580d0341d40c1c410011401d140b00c6030191500c0c101c01a02c880d008240018000d010118030310700400800081c0412080401d60040c0055034105210b1201d0b600c0003000503004d40d10944069010810403800140503d1000038058810006c91001e80b030354044012003a100c00c0d0080c50b030908103010901501245032190303031030000c041c00d003698007084d502d103000380741003100d84050016400c1c2d401940042c00300703e81107087c1540104840010701c10244240d0044032000102400401c660301c0c0c1d45109006421002031444140d500c4000204004540300e41c0c00ea07524820107500c07000300b0100208990400d4024030030071521410a0055035003400d05521140202c0e40201e1b8201c0d1040d142e0700741032003907040c01e2240c61620312003800214034000312525200310300d25008245d01c4003103100740c00003038003500e40d054840001c03940102400d45030a252a6035000c00441072074100002101181c0700348191414400c2c80c050591107600328116a1184c2440c0780280d40803103100d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 39463494 1250 39462244 39462271
    0x305031801050907091416050706110705010b0301060f0e06060f04080604140709050403050702040b120d05070b070c02011d06070804080c010f0306080705011b08040e041412090603 79
    0xe1403180038081c840c812014180980956810010755600301ca00001290b80304071034000c200928803031000c894003401c0c000382c03d0690315601c0390320300100900141c00102500d03c0e80410312a00700b10701500200d540300380840080c044207490303991006403035409100ea10313a5035020300d02152050070240d004000760750384a8002483c06071102d00c2c0501d41031080d90102d400c900031b43c0c1555158001400144050140c0314014406410705460080482c0200b0502074811a41c03413441c1c50483e0f450418440100d441c010607600004c0c59503c0281c002e411421040da0401c02c0c000000301603130f210b031040d1070f40030368140c40740080c04204640d2025400703c0101c00303a0300400d04021000100f0343d003d000c0d10040040c1c00003002075506a40004011443d1007040310300341400c00c001404075402c0407401400303484082c038001040301c0c45605020010a155100640301c0312002030f01042c02040180740a21841c0128540d41d04011040c103103607942c4450440c0400000d07014001c080d104d10f0560300450300041c2041664 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 39464744 1250 39463494 39463531
    0x90b0915090301090f1a0a0507091503060e07120506040c08040f06060503031306030f0501141909050a0207030912030f110f011d0f010b0f0d0c0b0406050702090a05040f030503 77
    0x2203d010900050a4400903880440300d070070840880c1b0520b9100c2c1c0016000d10141c01c0c4054003038503802045c00380301d01512400003003a46181c42903000d41e004007940d0381b400f0940e0038070003030151400c4503000007500b0031428180003503400c0c145402480c80610780b6944944803999140c071084e145014140040780c005450708800101e070b80e030400290100100b038510700749101d450503101600700c581e40303600704001c40e00340340041014401c07001d520b00001d98242d40541c1040507020760100f00c6d20203600940b5880303185c4010f100b00345407268043c054580c4a40c075200c44c1c0d00d40b0f40084001a5505980050005018040c05c480061107549602c0d4400114402c803440702c1184a545405e6516420f040840300c500c140340b0607403100d000c21803010707200e104400801039181c8420111724003191011029004100d8480c04104100c00d00407080000d001314012940c6031501d40c1c800600076840414182e2007001d1041c00324248294500c0b4840c09140d2041c40840aa4200e0381d050b02d040d00300618011121004a242 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 39465994 1250 39464744 39464753
    0x306030f0312180d0c0210051b0a06180816030309060c180611030f0a020705060c011b030e0a030f020c030f0703050f060f0a0b030a150b01090b091509030109 69
    0x7424540c10001510240342c9040003481c118501a4101503d0b154080026110301d103400c4101c4007011780e01628847c0d8006c41d071120584052241c800900204a007405c1880140345020640c880c55900c1198140903050344c140302000600b048401c0a040741804000e01382c0c40d42d40c0b05004004131403203418003041c443c2c066280e40003150714850700c5e04007040c41583c1100d02c40f44000050f1000d020b4a0a200300711001c1e5805580d900d020f0320946055410380041c041c069180200001001008010b24113a916110748803101d010781080c940c01e02e01c3c5400c00d41d1240006010340035140c201e290b541c00410b58244551021560101640ca0b26415401248800a9161404d00101401150102c001d010152540c640701e0b2030f002090140810a811400600952410005000d03400c4200e4100118000394013000107401c00008000041c00c0c0d11210300b20b0305650742c1300c0d005680146402d0320f03405021591b032901c6042a02c0362a4130254045d901d03200340e43c10380410101801000f00040d00000c2c8481030783d6203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 39467244 1250 39465994 39465997
    0x406091107050105060a060e01030902030c030601080a03020f0303150906040b06031005090c0a050723010501141306050109050d14010f050f07090f0e090115090209031002030f0c0306030f03 83
    0x44010360030000186242807100900685400410170360714401d600307140c850005d10040b0711214107410161240b01c150300b550380420011031000381c024255907055070365000310366440620302e10441c00b6004102d03045010100100c1a81d01c62012401c0a200043c8890100f040120005140301d41c000d0361542080081e803110710246110b0070019400900c503d080c1300400c082c01100511001244604100b41841140d208061303421b400d0340700c0606480d40c004090030001e04003003141e45c40110b61800000140081c41401c1640d40500e040da10420048c100c0e040e0081a03a010340280c60126040d090f04100354109080300314030107070040106004a00103442810b094650610151301c4c01a110002c0c0181000f0440b081078000c0c00c0b03400c100b03003a9454070054050302801403242d495044003290000d24200030a402c84a050303c2850b8042441544a0580200035040044524002d100f80d290420b0074181c20300c2180e010350b001000c020001e035141742d02d8091a60006140355007601a041c00300051010410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 39468494 1250 39467244 39467261
    0x809010e0604110f09040c09090201050c0d020304050108160801030305030901090804090f050705030f0106031a0616050601080102070312090203120a020a021503060f0d061508060103200907030b040609 88
    0x104003240c000f40e00d0200114000c051082d18418140078083c0b0002039507031006032044406d43e4002203502803a90005a40600990090090310301510140302d030002d50200c0204161442605d400100d030f281c01c00e925030b04021314040c034404102400c0050011a000d0b101856003d0540c20004c00e2000c540d135030b51060354006a0015899070707100d0305441c960158900440368071044910341282180380c03008100d0143c003c1881100b05059070782c82d000160303289100c0b07101501e02016005070f64921002101c299294031414042c1c03114062980080354002d018002c64135451f425a65130201070f00311403500c90041002c40e00880e1b03d403181c4240b1110002c0e03810040e004815194010300350b002614018820f103031a018440e00c41240040040200703a50302c0006c61031000d041070b14121121101407505000804a0506040307900c040080c0000741200c00050090503a8482c03c05032a003141030155a0941c0d20741851603d41c0b00c2804000106464402d50001d100306000900109266070f4401c0b00504450b12035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 39469744 1250 39468494 39468503
    0x1101060f031401060602010912050307090302120a050c03010209062a0706020d030c02030a120207061d030408010b09060117070512160f020f070b0c0703050d051309050106080105010809010e0604 85
    0x80c1034040c82c140c0d00303101e18030003001070740000e0198841c0c03592112031103194568903070144040440880e0b90b580c4200c2e160000307543d0207003903240a0500e01c040250303111002c03103013281c1520607580311300c00340c0c101802543c60707820018122904203520180c45d0321200e154110090304000354081d0f684540441080040300800350f6030060905007041050003400d9540045503070065502c2048080300140d4485600140404540c00c01a00c6610714a44200509603c94800c1070b12860043d140007a200040001c00c102e0302000000c0003003900c0c290502c040c0304c0c021070b0b8590101c1c801c1c40c84412004856850583d103c0424a00b880c41d0401102880301d180c80207440301c0d480a001c14a04086e52900003803234be160041d1a0006181a00840c506150f6038a01d44c001c6526400d40462000c0025400b00b025030007459200c0c0507104810005440103203560041c030880190702482040c00202103400744103480c103a842507555805c4507130902c4019510900c0c0034005445640d42ca101c0030074408414003110b4020f9109 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 39470994 1250 39469744 39469763
    0x903010c0c02120d05030a021b0a03020303010503070e1b031f060201090b130b1515070501020307090f0e010302151611010906020c1f030b03061503011b020a02011101060f03 76
    0x90050048181c40f21142d006240d01403041d200816400000360381e0b105c80300074000760742c83d028000030f80c440c4110086055603920030212442e0405d82c02001450507680e09070200c4241303c0d40c9200341c15004000b501c07070078201d0340c51401c01d08150f200742d8001c59002e1107111850003140514143c0040412240e808900140d64458205007041441c80010340c1002c103007148150000c0182d120f480f9822030141c90007001e041c0c402e04003090368540312511610009004030b0300392590580d040442c044d500c221000c2c000940714510115400140100304010b44408408140f1160f095609100c6509013640341c08403907400034890701088400341d440304003003207200d00f65502c2d0603080d182c00503060a03e503811201c1036410502c48200c0b5921080d007602309004000340c07560f40a0142c0701c0e081d402062581c151039003500451080001080824944842007102a0000c03c4617411505801003201030300052600160172074103605002d58410140301c5a10720108000154003581c840c403100c0c0e0041c0c60b40c01211041207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 39472244 1250 39470994 39471017
    0x91f090f0b0301240206060904020a0b070b0901060f0308030708040c090c030905010f020922060e010e0106090b120103060902130204140306090604030912050c040216060b0a0e06060903030903010c 86
    0xd00303120300c84d00200e040101140c09100c4502a4039000010b0407103010307101400c0014150b5480f4040e66005042d1900c503180c0c0c810305410101c1c1119411206803101d9800d0660014458a03007803810300840b42c200d40c4603030568031400c030b04460b080406841945c04044c419000300c0c02800c2481214900da01e1034030002000d00b0035203400c43c00d4030b6051040c190070ba0b20601c501080b42e207500c10890b132600400d0b140001c801d038014203001b0050203207170803c50f15202e4510011520071041c05440d4107a5800391540c001071599081403c02c80e1081551080d0a8103080e80100001641a00b001006610003811041c000c540024150b0032a00030340d1200343d0050051910350460308040c0100c50f0090003460103030070780345403646001d001944c061086074020401306605205000086c000c1c541e0742c032402403003999161305008260b001091800c40c182da50360300e0180c0158040c5031482e1145c0c00c030755144000e0801c070350b28242049020b8101c07040c0e03550507000400c00001c07107035000e01c6001c60482240d210340381c2200c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 39473494 1250 39472244 39472259
    0x405060f0603071511060403090501021603050d0e01030905060a020315090408040b0a090312050702010f02010209010f031a041103150d030c060b0109330203091f090f0b0301 76
    0x4201820955140c1060814840c8684000c541d50702600c6880030040d00ea5560007a04461102005022100074028041440205036100546100710340f400d83c01c590205050540300080060700e448010260340c403018241740128040d55041204170014140082e14807216165581060b2003102c100340b40ca0b900100308030004e004840c101c032110000740c03440947c900e015500c0103400d200e540112031401c00c000c155410110f1103140950040c41e4801c011046012540d1400703402508800402c0b404216800c120140b41403051081e9000309030140e56a80c1c03001021081a80144280c68090300212280300740702c001a10385005098101000300c0140380c0e24948600394102c000d400d01049440b0b060180c1078800030070b0b4406103c000b00fa4004d02c0010380c846019006a40e1040700d94407145403003400c24000d640b4944520303440e05c0410810303103804066121031304049860384203084400358088941c00c1c1030403030071001c40384071201ca0549040800403962500324455042049500c03a01c03900310004014403016 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 39474744 1250 39473494 39473503
    0xd031b030f0228020d1e03032306010e0d080f040f090b010306030308071b0b010806040b10081011040b03090d1805151e030901020a11120417010902060d050405 70
    0x8011207210502c4002e405250b6002c28101400043e200c0c8603108415806e118000d00040c121202081d01078035480b40038980035000d008800c058010502503000c035082550880107115103d040142e48952140d6404000c100700c680c454581550811070034040c0d04c4c0c11040400003000038245001200c5c00051411034010195802248032604043c01e24108000180d0400c0c4800c4d000034040c284500781070459400f0f5400d003070190401500410708000002070051010030000d0089001e8a044540d60b540c0142085440081380300d0489554422102c0c0000090681c0c408850801c0100d40d0902e050358419654100da08147c0e0801c005400c1780703400115154200142e04070301e00781c0140e00401c45141a0001c1c013000e1000001d00640040040c22204080584110398014403003001160303124100145032a0007500840d0013000824424040c00036203460020300310100380380510328149400e06005808885241c1c01c00d58030318075901c03191004016034508000e00780300f1442c0e040015042c41c1604000f480e1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 39475994 1250 39474744 39474763
    0x209010f0305031605121606050907081903030212180d0201050f0606090d02130b030706020c150a090806010305060a0507030b0f01030b030c0a03060c08071d0d031b030f02 75
    0x2000280c181000040c0c0e020007528080000707002070001d600380e242403d41c240014464052003801c40007800407181e0038400d869410050188804001e91341d2030309051940c1d00300f00c0c0035580e0983c0c0101581440e2004820341c1c42c40d624805d180c00f500309000d10381007001c04603003594080015840c510380c0c170701d071007004000071104064244001c1c441800c10700c90440714014050081805610005601c42c0307140c9070944170a01d02580a890301c01181c100415030001001c0c0200c0440c464040d0141c0000c00501c002248030090074000c1c0b001203140b6900c0f20030441035010030100c105000080d1000201100207012003402140910007408040c5009041081107032002000784040c5440c040305100703e61155444440e4101d400c2c00c1c006214200600040d29001d018144280e01150402d000700400c4481d0700040b4005040d610380000c00e444000c4141c580b810b285040c80100144a1100c008500d425026900468041e050580c168201d090620021200aa0007174010a4401030400340140d410400d40c40c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 39477244 1250 39475994 39476009
    0x310140108040b060d1a1306110f03060603090a121806030e060403080a0e010e030c100b01080a0f18030815060a17090106080a050709060f051003050a090c12020901 72
    0x100e02d400d90b40c4402e00400a030505009803c1054901e04100c00c8060403d1588110482e903c12450004150000c8082c24241201c40509004a40305100c00c0507065860b0300042e9602e586c15540c07580244619508000d2000009200d50391019000c0741b0300304c003c840ea055080d0381c0e070390ba6044000684a080c244940c001c074205072030705001140d1004c1c04a18650000c6d81440c0c4003081da100c101032034010f05010580c04509510b06054008040d10000003401c0c0e40f8920720596400d15420b80c0c0c0719040b01c800040c1c81c0e0218205000243c01203000394400c500c143c841c40d40006440000c0c080070311810490240413400700702d1560a000041d0742503904500c2903c000c072030541c0741141d420001030408802014020604a100b80821003109080d00000003605001044880c0281c0600b40740356100c0240c4948801300d4503000020500d5030507541d100050b208003409002450041c0c0030100c00030440101411180750341c0b40c4e100b5000841100e0142e000f0702e007645419607111407a0040007041081070b4080403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 39478494 1250 39477244 39477257
    0x917070c06110318010809160f050109080c010e060c030c07060302090f030c130903020a080f0301181116021909020309010b010804110111030d050408120a0207050a0b0604060b03101401 81
    0x403c1300940052101c0c501c042071810001070348400030704602c0d02c43e01300790180140e0428807002c581c0e8503000000104a40f42669001c1d00e55a03202142901c801d04400e1480c00240c4425450555060110040000980c0c2504807468400340030340031402e09101d40c11160000382c00240c0c2e07694a1810200060761044102c0252001c088030100044c0000100d4104030410354443d403000c81854002d01440900c40d4000e0025642c504000383e0040e59039109016032804403220100c0400c84807186c0c8204840c10390360084030f9141c00c2d00020001d44500c0090012a4480a40d81c540c0e80480b2801480340002c220014000d40c807420501141c40c02e40b1450040d080c10040080100400325100000f6000100020301b0100704c2d03150080c8540d4150f1040d06000546241050180000c01c01080000c04400003403681a245944507043c0c850182d11692401a03d42d40c4682c4c441c1001c60499950140c000340b00920000740316548114958140e0012034141c2041d280d4164100400f8080e504240382c051024a040c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 39479744 1250 39478494 39478507
    0x20415140c0604110402130803030f090d020703031206090c020a0309060f0503040210020f031b011104031212020d0e010b0a06030506060a08060303070803150a0602010510090917070c061103 83
    0x207030b0784803030003000034180c1412099801d00f107450310382c11501d9042220002a00396525a000c2995941c0b0503106501c05801c001c002503e01ea001040c9074002072401d80c0a0900702e89552030440381381d2444021207180780d0303a4100024032418248201c2c11541c485401030101c5070103a04004d44039514541c401800e100c07580c09041c0c00f1541c00360889501c550b044884a900fa241c04000301c4c030344240078003008414807002800740040302c0034002982c050a0b44000910044981c48000090b6010b00d100c000c080c0a0307960300d644909402808c0003d400080e43e0f40042c140b02d00e1240002c280c2d11500f5000c0079030396590660a0700b600b40101540040c143c00c2c2810310550401d0004280f462042070388030810003c03c140172801a5401b801140c1d10650000034640d2242442d4021051007c07144020354032406854800255250040c0601417007140c1381e42d0280701d030074602400440502010b00044818021400000e0401e9080c0b602400304207005c1c0c43c44a580c14140407001d05252403484c15402035501c2441388 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 39480994 1250 39479744 39479767
    0x30f02060c0a0509120102040b030c13051e01030903020a0221060c070c05061c060b0a02010e0109030203091002070b04060302030f07050705060615130b180f0a0b03041502041514 78
    0x81303602c0b5107001c1c5d4000f030440c1c281e00852402800355400240c0d08080010038003036801c6510020b0a0a51491404841002c0d601c41c2000500801020110042c609075011a416503009a009544860190040c0c40460889070300051758484040039503441c450781b0b0440d0350001c9108000103548040320041b200d140c1754081c0c50b017035002107042c03152a01c520f00011b80c140d81c031080c2441c2d110301381d11049424807055488942990b00741d002203d85c000158a805003042032f00e401406032001e41c1d50950051860001064144183c240801900724103511441100044131103c42c00140005c040c1a40c0040e02e80c1003610303070740000707070b2014080d001044818009000444c45c04a1081d0300407400b160305c41d03080d0307941115094003401140124481c540b0000000202440450000e000c004d1000e58400782c0703040110308100d05402d0300c1da20340e0341003800c052040c458414446c0065402c180500c0000e4105a44035454905030b92058002d030b01554100b030508480a03030400008840c00d511002c4041c1071901c1040d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 39482244 1250 39480994 39480997
    0x30c09090509032a07060f03050a021305120309060c010c02060709240c08070303060e101a0711030708011401050d03050a030b01110d09051309020a030308040503090d030f02060c0a05 80
    0x39050b021204060280b07078041131010709010200441d40965407a82c3c0d54140207003000d220a0700c0d240c0400e00703041c0041c070800414801c550400048201044025081034180100701e250300c030813101c86120411079400c2a40d035010240c020b11718050000b00300110301d5a402400d102c8040c103910140048580248610807090032080107111114003801d11000a15000f141da0b135a103544043d003043c000040040a050303050300108195280c4000c1c85c58141c546e0748040d94843c82034444c89000880c0e02c1401607044440100400029004060300950400c000c00041d04044607030b40703c85910f0395581d4000200400f44c413009401003d044444c2c141c1e2a8180e2800390940c4516005502059910160080130342e0081071490b001040c00000c46142005284019260006178080c640c41246203c1718102c48a845024001156030702814801c0346a2541c1d41c01d40317110700050422150780c0004d0105000c603882e6110303503501207802940e40e4900da54120b82d020f800e003d009003c40c1c0e07450303208211000a2640000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 39483494 1250 39482244 39482257
    0x6070507030e100c0302010c021207020402090303070209010b12060105090f01030c0c060e0d030506030706090312120c03050f130209010605070c080105090d0f09050102071403010b0907030c0909050903 88
    0x204203035903901a241c00c4824403441920b032540540100d0101c5180ca500c11900416184a9002040004084c02c0181ea0760701c0b03036180035100490b040080c50018201034024200c3c648001d01100d0074008654000b82c1e4054003600211040040451f58480e8000102c032003e42050003800c1c02ca1804203030340085000c5401000c205818151107104807603485102d405a443d861740c120804110321035800303264030344511046125400290030800810700b0b61034003060301800c413011074031090308980c07441d03589000921030407a6080c103000c540701541100c40c1e400d01a59007101020350f4002041c0ca0103c1c841105100054038600f20411000c1400d8010785845010b40d056819504000b602e80400f450141d5813616940c10a0005500309000e002c40300c100041d40d40c0c1c0760501d03900c40c0c030f000300d00c2e8020880da00c801c83d126440c01680200c00400580403d06500025040081d001150174141c3c4c02c0030501b2280141c54040001c0d9503040e031900da1503400014400070740004042031000307080503802d259a038010301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 39484744 1250 39483494 39483497
    0x306010503060f0d06090506010515040b0d05130602070807121701092004030b010807230105070f05010912030e03040506041e170c0414070813020f060403080301031a07020607 77
    0x103507400b07462a6134044280441e9603020406001c81e42c118a4900c2d1544028880d45000b04034000c041d07501130180320140e81c1601c1f0069001343c205071042444030040c00014200e109072800c0c0d004e50304c01240c4140010080d90340034407180d6941c0e942c246008180e00343c84032800003c028070713504a81401001240744c42d04681518402280810007010000401c0f8191142540384440014000013003000c04000c00d4101c841000965503e25540d040749448803003504070b0504131400300c2c40060036035070144020f0840c1c10b008003422005007000c0d41d5000d003101c034000c1060310300c0388081c00181c0c9915854007400000c002c41030060b500302340c5042c1c0440e109e801240150000c06e8410300c02d1018464181c031a8900803c03410f41403415203a0707000c3d0507a4480030585900d90046003003042c00a40580e2020799540101d0b203d650301822996400300c0d000c000c003034240080f0b074807202500c0c684140e9034414000d031014501074261144da0b94034510700142011070100f8a14804c0920004100c0c9298010071425031140e6203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 39485994 1250 39484744 39484759
    0x7140405010518060f12010b03010501060206090607031505040c050c070f120803061201020f0301090b10090501050c1c0210180201081807050303070303020a11060903030703090302100501060c02010f0302030601050306 95
    0x40307000161405c2e114628030b58100400480e403201c4103205400a280408003030300200b02c0c990300c2d840126161541190070480d154420750224081500c694000d50320808a00350700010261503a00040660f101548100c00240c000301c0c011110407010b118071001010f0a0324814062031a04e04ad48030000d14584015021103408000285aa115178141c81600342889000315526206001d00d4405031b0001e029400c25036181161918160038032480c02c145280742c41c0c503003000c000c0c5800c0c0115015400f4294652481c020118146400e8001d03000c1c5041c0d80c0d94680241ca42d0a0443c45c091044402c07020220241c2e002c0725001d000540d8000c1010345d00406141000300c0407080400545180a020764840b507010b103c002121414147c1c1030b40606011b4003981d03100140500c81c00c04041c0c0e2002c3c02e03a2200b81c26001000850038480c003035070000c210648a4010380c6c8c100444c03080e05e07030700701c8002368042070105001442c07100c21507a100031031040103201c07400e0031810b40c1002c000007071903804000c0405006424 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 39487244 1250 39485994 39486001
    0x230901090506070c03170408060112030201021215131e020c03070f0503180603040312020903010902030f07060201060602070b030411060903030304030c020406080a1502070606150207140405010518 86
    0xc039242940190a0252903183c1c0c030000f61401c50540c10740742c0b0050f21240007400860150b25030503021074003103a032160300411199081c02c44130f003030f04041c407a030440945d9802c010500c100010b82685501c582076070003504400c2141c88040c094a1449000f114034150324188c80b00030052240030911610400519005845000d200ca0f62440d601c01d00f2005424000f1340305600c8100400040248801e510a415140010003030900340050307404241d4008011410380c6c44e503400b08481070390180c81c86c2240100085001d0ba180c0c4c0102c0c1c00c0c440441c80b40c41040c0c100e46d40610465809009507030041844e40700805a091401d00ca600e000e00004c1c1c00142407040c244842e01c19950b4000542c0d8000c0001070580780d0368109490068010340e03000b102203005a003030010000380800f01143c0e000e4a19000012440425035a03103141000b5070041d03130200c800b140d4424010514901180c100d511b42126500100322260502c541588a003ca0406e010320460070040140b00c40e80b641c001480700603030a42e008c01040d49 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 39488494 1250 39487244 39487247
    0x4020c070e0c0c0f0304050112060506070b060a05040f060504050709120305090301090803010608100f0f0b0c120403080c0c09042307170d110c0108060603040303090803041103010507230901 83
    0x308030503c0349054400c3c4085011222030201c000d00c101c03003003602d44401d5180b000c802d01055482d240b09a0341e009a0620151011950010003654001d40081489820a48a40c0043c007260300040e60208030903601d80c800e0040b4242032180542100580c00c09084591500011544207642208001e04000c00482c2200c2a41c034250010380c80075a04c52100750316580c42e480001e00c0018211215192800707500340c0011170484000d8441c0c02e464003038110004035402d104424205a1240416000c0c40c4520300c11512071440e4800130384013031072180900650b18190440c801c0c1c904a03103006040e00c200c1c1c20009200c00241914580441c641c840c0700c5021a1100200f4480c4c1442c51a500c2403001440305216414404404120300d030b001e6600e03468000002920314209540c0c1d071491001d1601080b43c0c440440d0351890300c24050350f803281c464074011564001e50754840c0e0058100342c1b4110340341c0c0c804001690a03480c0a025080d8040340307918001c1c0d04200c06440b42d0399050540c0144400b0450006115040c1c0e9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 39489744 1250 39488494 39488497
    0x30403110a150b100f02030f090303070206030f1b030601020d0f02011b1e030605130b06042705090f0d0818060c0406030e060c0703030209010324060201060504020c070e0c 75
    0x1181c0140320001d40c00240c2210101a11a0203081c0b4130800101c3d407905149809444401e4100110f0390040d810a80b2041401c41d0544c44207000d1075142c4802e000d510011b80d1210001e500c0355009140c04181820100c0c83e9043c1c0240040d070a10040750280100000342e60300051100c070b00c1200703190101d06000f803108140d0041040d050f0700e291000c8040101c02c0e0703658025402103046040740c0b003911302c0124a0807085040710510b0040990020704454088450300f80c41c0c1012104401c001e010520303260349d861006042c418000c82070100807200307001034075034440d02e0310400c1d40c00304403100503142d4510748100c000d40782c1e4250380074001400a1100400c0d102e00746000904480100441103030510308105221200c9ca400c40d02c07403900040d0a010303558003051000b141440c02400812051420908507680660203504000d40150405503150000e0601e5140116855082c0c0f5112200907120b40c2498402801d40d131494021300c0c021801005011042c00d80003602008039180040169a03580710a8014280e9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 39490994 1250 39489744 39489763
    0x1905030a0605131b09120f0c0e01090603050c0a030b07030905010605040218040e0f032706030c12010605031005060c01091b140108011d0601030b040f0603031d0603040311 75
    0xc600d40e00d50b544100040e0700c5101301140d0801c00300c98400554104031400c180c24024603111000003a400c00014800c405c000280902c20250241029110030340030f01641400d07445400050745400041060100c148040c103882c81040c0c030041909404c40c0c845046000c0c018001ea0201540c2e41007840600001394842405004018006c1d940da0510443c000c09240300c03003031885c1c42030b4500785407101055000114812082d02810240d030600c040c1c068a06440a06104d900040e001403400500b221341d03440b0011440b4440c45000c1503110455800c030201c40c034030160440000c1c00410800d1000c0c1c8901e0008400480d41d04542050303072001d01d205e9850240071000d6000348410b0329521881201c0314600303a40800d50b43c46015000d55200c1070001101e031850280300e0800300d020180040608003480d501896030011041c1404141254658046011100c0c980750405166513100024400c0603488902c442d88014400390100c030012a0b07900240141c8005000103050141e41502d4480000d0148a407500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 39492244 1250 39490994 39490999
    0x9070608130c0b0c010f0b030105100e04031107170607020c06030c070c0306050f0105090a06051525050d020d030506030309100c06050924070e01140403050601090b0102010e031905030a0605 83
    0x21030703e40e400c0d013060103421861540010181040e114080d03030306051203020f21540302c94000034000740c41c00e41036400700306001c1c1c419410000c007501440305041041082c10000c028000050f0804c10103060103c0c10300d007018080000b150860300e001e9007540d40d80019648c000a0503039032250303a05183d00d40320030500100d40c0000c2c40c85080904205030341e01d04004450407200c0035910840305554103554070003140c403103000701039200b904103c2c0e81720f003d024500940f55648040c1214400400c50441e130701601c2e002403004407059800a200c1d0b0403003550510000d0f001105034281440941001c0002945a00030120040d000ea80f0f03d91045c1c5000740715000301940e45811003000c021070300b0720552950300c4a0317283e0f0158a800307901c01d82c0b2101170803100074140d10130102c030b68513040155503a200442d00540d0156461030108814000800496018420b0358001c0205900004080201400280c252210b0b41507980840e041403200c910001140942000084110f20380543d072643d400003044010061604030385e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 39493494 1250 39492244 39492247
    0x2010c0f390c080307200607050307112119081306030c02010506060913090305190309050d0e03030403120207090c0512061906030209030f06040b070809070608130c0b 73
    0xc0642540940e50001d94024200c0295107600e07020b9441c1c0c1d81c0b003044d600416130152811140300c180b04140600b200004010215450295503403203003441c40c0c008070b5003a00d81e25000c00000c001c920301041510310704071050401000120b0600e80d00c948489403980c052602c2c0302a10b8420007000a0320084688200385105200e90998851500070300900c030103a403000240d860100070803130300c0c507040d001d40f02e214000034140c92010728001690005403071150701c11010311509000c401c1d21310429044989445449070b80c0001c40440701d08149140c4100030085506101114003200d619031400310846055076000708400f0401c0d00708040403445c03c1410760103151001c1c1361241646040f40e000000b020303450100103449a050312030100300582d8603040d1300854480d4400c0ca81c02c00240e4083e401822904d07400078141d41d207481d0101c1249041500480c0e0448503801c1c10010400019007151050f50442d403404024002941004c0e40034202c0f54003c0d10840c0d031000040200410000710441c000060007002d060107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 39494744 1250 39493494 39493577
    0xd0b010608070f0302030f010618030203010c0c020f09010803093106031a01060504150306120503030106080c211302120601050a050102190201051e03090604030f02010c0f 75
    0x30004042600c220740003501105840c80d40d28400e00980b802244000b084109527460b04000f694640c150120210702c1c0545410b001000d40d0707080c45240030824060b01c0340d1194462a00c10800380014494209103d50041001403003058000001e0b14010081500c0008a1107030b141c0d0550ba8886040110203030a2600b10561180c080c01604101d0440303109010402c40c1d10105014400d008509000d030000282c4180402c11060f5880c6031214020300244c00c00140c01600c4014144155804030010340f00780e4000070040040650101005070b0080f02c203ca03680c10b2512219021448224403010000c1c00004080403604004040b45e5541a05074002d00020300d14280c24203030358071203000748240381c40340c11141740004041d400800c1c0c08424400030038400c0d07111030b003d034015580340d08003c100c6682d400107041e104e0703180e44416009501541e0408020203251400c0d14005085070000451345045905100652a86541040010303950a0b69070070310035030303901090004450b6884010208002401e245415 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 39495994 1250 39494744 39494747
    0x715020306120d0f11060609040b1b0c01020403110a0b030103060b060d05100905090312010306050a020f0a020a0c12080a1101021606090507080a080307051c09110a0e060105070f020d0b0106 83
    0x1038045144c0c03180c40300e207040c0c1a000b11481d00d035841165895046001c04d800580018000c007403d5034007a154030f80d0380c410f564400e0721080450b0040d4452882c0341e980000d050090020600404c050200c048070190310705404d020050102c0c1c081840b0060a89440d500301554555a62040e1140540f0f101e40800940c908401040b24070b03500380c0329403042645010701064038a00040111a0100101002150301d070346180d40741c0c40140b5008040c0002980d0034009004442c02040040001001c0c9074028010074096051164500d100340e03000c204d0380703842e4221000000d100311042c1da2101c0c9203410811065201341051038064400c0b51091409c01d20305207419410411142d2100146a000c4c03411030b0320041d03e40358a25596601204007519080c410310018005a101d100104845c0041488000801000e0004601540ca5840d000c03a5444440d14980806062007981070f00100301540400720182407841c0060543c6c030030084086c00d00c0344041c04900a644070302c2014004540d22201d454082c2d83e40c0c0300c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 39497244 1250 39495994 39496007
    0x60e0d02090a051503010203090d0c050c0306070206010801050702070f0302040b0a0b0301090207051014130f0503122406190306080303010b0a021002130e09010f0606030f0b01050715020306120d 85
    0x303540d0305a201e8610041854217051003503d208a00c2c0c240142030312444048140d40c1c0e0b029070304040340c0a00c030300700c025181c540b024070880c3e00912a5400400d915418803210340e082d01d100074076400466000040800c034109060040c8400c03aa0181c40004004144101050018116800c4040c24450020000803403020a89c01040407500503000d0384c6003000c0b0b58842c1010303036034500700c42e00c004c004500210340b52000501000b2021882941c40c500c1c076500d255141410340d001605c0b000310312001d48040021290726203102d20030040843c040c0040d00341b21100041c0284c040c403240b45451560f4480064a4980a0f41c4140c0103440c2c00801c903502da42e9240d8a09005a001408d400d005018080d009610002c03180241c0354140181c035120020581000035055500305e00400c0c015266480391610614441544201406424142d60204070358040d100c00c1d50a494105010a040200810450380418255a41000c0302d040d40140035030740b92140000141d8240d0f042d403040c0030134040d0b150a070710701c240c1204 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 39498494 1250 39497244 39497251
    0x30e19030909060504110301030611070b0a0204170a17030702010b0a080a020414090a08090f09070809161d040302030415090612020a020a020d050709111209030a0207060e0d02090a05 80
    0xc0a0000c5034032a81408142d0f0308841900301c407000300781f0061000038869000240143d00c80d42c982d60400d00a0345920801d590143c1d0f1905a9581c000350078400c200320947e40c4901c140304d40d8024004c0305401d0b550030302c0b206649007881000e04004000304002c42d00c02e4000c81219900180081c80c0740c0e031100800e031303102c0c86000301c200d100e03d10b044e01d881610038031403640394482c0400ca0040d01580c0c205d5120142254032200840d41d00881801c410300460f910030000d2405080280d80b8840c0c00d14041c0c5006150841c41d010103c41c28140060801014028040001c220080001c00f030b141ca031100c0ca030a0f45180125040501d44050a0074400901680101c0c0002100c2e03640d5152443c180d00c0c0d4403040220311840343c0290040e04140111005420401c0d460b400c894812411510308565a00780e010880300d0004206801c0c0d94005120700001058803c0180c000841c1d074040c62915403452406940c5a0244c414841445081c0910030490354503913814000103034000d00303000d81c2454207075501c500506049 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 39499744 1250 39498494 39498509
    0x303070b0f01141509041103040602030403020c0418020118030221070605070c0506090a031b06031b0e09040510050106050304140a0c05060c0f01020a0c0c120b0106030e190309 77
    0x1c00010302541014400110510141c000013012141e01100d49540d402400d4094129881e0000c01902005500003184079a00600340161642400d11707000342000e46000c51148141e0604019186481c2c90074000d11180e0f50900704040c405a4048070450219080d07400650b014000c0511641e40c0b0f1651035200304941444000d5420303080c3c5960301682c11340960320014200b6420000300b440703181003000040442d08130050400c0310940e42e9a4840e49400018a01c0507090401604200103980d014041c1150350600c00160360041a501603000b42090003004000340320b01000c10125060083c03d00059054901500080c072556860b141c02801c82c1c1c1c000d88080f120144941c10301c0082c4040480e9072882680d003d06a0b018841c54041000450381000341061124054036000e1000210300740700600c4202c60a031207845841909082241180038a50300032481000c034096214000ba1001d4507950540c7c80c40d080c000b6608401001641c50017809800207101108009400c0c014035400400340407c43d5000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 39500994 1250 39499744 39499771
    0x40207060b060d230c0406110109050106080102040602010c0806060a08040f0501020310060f050c0606120f0609070e010f0e1609051207090501170705100e090406090501050703090305070b04020f0303070b 89
    0x41300c406014486003210066410300341844140015807054040540b01d00d40d040000c5045246030b00c4481c00c456250748048820307940080d0400400d40c0a0140f40c07507007111403d0020140ca03000c404146c0c1442000391003000c000d408400a020850000a1808000d800c003000b191a0b01d002d00000380c8bc03007024043d800c00b0a108103611008944680b04854101c002d0350050034254440c1c03130601c507207807a41041420340b038041d0341140b450b000410809188205060801460301c01d103020800c0c181c000068210000340104008144420a001c0c0c01d001d401c000b007003141ca8001e85143c44101c400000c00e420055104808601172401ca0100180c1a025641d542404001a90340d0b00140c0c250440340c0c520350809604000010401441c00b11b680c1c400386801030400f6254a01814006482040700303e41c12910b5a54600141050180c2482403a901541c81c2c00c04100d18803158030050400d02038020020b00000c4000001021512070303a0800310050000380880e0f80b911303424901948c2d1500200d6000300c42040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 39502244 1250 39500994 39501041
    0x110c0307020f0d02030c0103051b0f03100501091d07050d0f020d05090d140705011103010e0702010c020106030b150f06030702100f11040512072c06030a0b06040207060b060d 76
    0x18040c1d0000907a1354000d00a0030007611000054000e404002c00d0032951030342105500e441c1d1494a40100089091480e5041d5a85098401408204221707040241001006181441009100140c1d0b003209001c94841c00215900e02c981203403588901c3c00080d5009013032a04455000f2650740242c1001212400705111a60b1342d0120a6925080c0c609800006051642102c941002040083c40c0c0c440c0100c0010483c01044507600441c0c1c1d01c00e81c4480c541a515804111886078203101d0083c000d1414402403007400c0c0742d511218480440503044003106240c0404c00c40f840c0d901c1c2d080c03800c481280030b4000340d100d14117000041c2d110f0401d0403c0c65075490421241e40003108007445404400d031340e90301405040c0740c20300007840b950040c003182e020034078444c024021038203020504081c6003040039403102d421001481c2c0384104980e41c000d041d072402a8010600307440010780c6d0aa041380e0101065030010b031100d525041c000d000e0941111204d4200d400018000002012600120398034400e924900e5202d08 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 39503494 1250 39502244 39502249
    0x50d08040203030d0b04020d0c08040210110d050c011e020901270608100807030b041202030a0903110303070f32030306092509060305010503011503020f04110c0307020f 74
    0x101180e00a5042e0010442d88031800c0302503000300301010014100500704404101648216020858413a001c115a10100800c5140c80903590103401d21515000b0341d090300d00030845580344110715146061140110303103100c04220940c8441c1a001040c00303e03204000341c111101c002980025401800564a8002000700100240d0045036111901d20100c900610f420703000c964580c00604101844410302800003114041080b501c00954003401d1248031034200b510702415141c0c030303907a40041950010b02c106115250025034080450f07410000c280e805420000006e0300b1032162001c000c101035a4900f80030248801c100114035504a41307401c06010380800c4480802507104010203108036401040043c12700d023444818070340c010041452062410701420780988001e00d05a82e0180083c40608003041402c2c2c3c540122801440154003c00c040152111044480d904a000c0130b805944030140c40c00c8203032203980c4512900542260002e4441d001d03200015103940c001203099103e48402d035004040c40c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 39504744 1250 39503494 39503507
    0x90d11030106060e0102030d050402010309050604060501050118060e15041502030301030501060501020f1b041d060a0b0f0a0621020a0504080d0801060c0605040302120307020c0301060b0313030518060a0c050d 91
    0xc0c4c2c0580096080042d50304a80b00030708001070040707041540380c0380500c00280040241c98040c9105940c080703119030508000412003110551003144496586404001c919000050b1052044080d1003003d02d42c01004c00e0381d071140c4503941c441d0300600c030251000149542e000c009513059a11aa0080c00320966450049958070709180703a02c0e000c1d400030710348114550003408604000c41405007020a0b51030018140c0684900500061101c50704a1f20400200301c40c544034600514800311a0203400900c48004100085420702881c424006e801b201c010349a00341c044c4002d00c82c40403020541d80c480c401c1b10020a03641143c0304403480c1d48540da58000107103004008840c1607c100d80c2e55480d01d40c0c0c2c1c1c0d49a40018110240c415015030045040c541c58211600000b107210f200300340c0040c41707040f02c20010700d42154030a50044180d84018000c2c8640c20010160f84900150103192440c5c8401c0b0380e0140492180800d950668032080000d00c2d80305150b00401905401030180d800da41c01031001031000d81e800d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 39505994 1250 39504744 39504767
    0x16061d031b01050c0a050106060305040b0618070e010507120207050a0b040e0c0a05090a0b03090f0a0809060306030f03041203030506060a020a0b0a0f0204081e2808090d1103010606 79
    0x1501e01c040d0080d003440d48030780050710242c140001258041c00217034549600b1110590441c50000361107030104020710030300300003031600300e9025103d840d521040a039054040c01c1016005004000b115190b00c03200d03a00c1001541d103c16040059039800e00344145c0013075076590b150720400380501810403001404640c04010342d81114803440b4540d070240d443c002082d0746507100841180a0203024441d504264441d1405903000c0d0003a041d40507624102028a11300c0c204800744408aa90300c100c0e0994001050300007650414202550b02c1754407501d6020001c2d05103a920b506040076071101150015002e2201c1406494290094400b0030a58039680306215442c41505e81d20009039128104200c0001c2c2031606450380100b000030000786543c8581c4c6040141ea00070340c04410075a22a80d1102c0c582000c0c0c6980b030390b05544002c000d2914100041807800d99880008008079020a02054442849020011070744006c40040c0740420440262505211581558542c107000350f02e03244e80031400707034080c09c9840c51 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 39507244 1250 39505994 39506023
    0x706111908030403030608060a050601020c100203040e04050304051203120105011e080901110a0504030c080c010804200402070302100c0207081e030d0627050609070302070516061d03 80
    0x2840c545a04105500143c0b00f1401c00d55120b80c006000c040911030f2502910350a400441d003400c007403000a1900841004051045650300241203d45400104031021168010910040ca550301d04102d815801150b000d15040381c0c040000c0142c2c040c001c40200141e1010822100559881c0d0004491002800e11414900c0084c4c10300591924061202250f000044034000310f601100451000c0060b0405005140401c030042002d004202c5044902400f0b0400000107010320b00c0100300007421040040c002170480080c8003400c800d460030f481c00c4114042c0e0301a100390f44d250000c1c90003e54540000f0000e0305554507003107904144500c00300b0004102c80141c03005010602e0030382e1034185455280080c201c0144401c00136003903c0c1100b80a80b80052047d01402c8480c0307841d654003120700c045c6559850001501d0304080000e1070380d503803400541022640c80c0040c1c4030307030b01442d009207000044805001c03000081d81c00003070219400b05100c41c646082c0201840101c00030828103075195501210ac09 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 39508494 1250 39507244 39507283
    0x60e0f0a150305071502070e070c021c06060b1801170c0c15010e041401020c07030f08070b090c0406080312130201021002030106030b0901080c1003020f04030c08070611 74
    0x114400c14681005880c0001c442080141d540d4079036030303d481c04000c0e034801c0100d0340e6035211802d00c441d010700c0028001c1c0b242c40d02c0e1050074500f13444c0080050040c903000900c0303080c0c5460810406ca661644129000c0c0d0b00150801c951901c551442d00140c0240110400d16a5141418a0313554803480f006900a41d00400029158803850803200c4550445542582d803445245084c40c03084054001007030003031051701160307445800c150078484a0b5400c280c103511001d070300410051040407000150b0340101d0b6000425012048810f181c04a014031500e80007524401380f50083c0b0005200200d5214004030080f90204803071380e614292a9181e000d481c1c402c00d44100d5010014803c00e804a0401401780e105106031025001960300d0300003245c1003030704480c00081d0b23510b4200034141010000c01e805010300ca0010031401807810009000c54180070045000c15801003002d801058081040d240503561000d10119059250030019640c2c4000744101d40000c5d6488c0780064003910045030981d840c0c00144401e6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 39509744 1250 39508494 39508501
    0xf0115090f090f140102070b040f03020105071701060f090801020a1e0219061a0907020106030b0f060619050c03040b03100605090a0e060d0b010305060412080702071211090705030a060e0f 82
    0x50301c110300100c050013295000c018480006120000c0d40d4031403032107545d03d030900d10200d040081c02c45600030540d406000c160b01d4003015064011014a04503000e62074540000c10501c0c0013260341003460760010301e00d503001007400361001e80c00c150401171199003414003c40d50107101358104d903070351101006400422903002c81d04010404540101c008104250b024216000241c1c0209012000482e403800050355111014020010f10440040e0442c200452003109070a181c00012410f10840b08243d42030880403801c142464061419210742c0342010f400d881d00c407940c9040d1034100b503000f196088941c50b905400800c040e40102c05941a0107000f13801c840c01541003071a0500010000740545500006100c03541000035800d005090103035100700e0140045040a2078460352507c04c15040c40c081c400f1201c00c010486600203009812a00300204500402032a4282918906900a06c0c00d4105689a041101c40d075006001507000300b00d9484200241540d900428003211001c0c0c8030380c00c4002a00c40170 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 39510994 1250 39509744 39509753
    0xc1219030906060302180901140714030402040e060a0c1101060602031b0106051c02010f020f0c1e030102040602030a09080a030c020607060b030a050d030c030203090606010c050f0115090f090f 84
    0x1120309032080c2c40016405403a900083c40341022402d051014100050401c5000003082c01091380e200c21100303598225080144010f84a60318149080c0b019040200010f0b00799a695040014050850b4080d04c5050402c2d10b4280081c180c4074521501050100154400040052003400c084440541c0918100911003200707400b6100f10111107134043d9218035012078240d13151103206036101408010913490011520024091511200903c019500403104551b00c848002c600503080b600121803c07050700318400e81e9001e084c0b80510341c4c1a0558800b04003c90364075000801031800c441c80c0c1c4c44902c00103a0740c104040d40d4140c44000113000511405c5584010306000b03002d40b280034461072020891340c05040c04240f51041901d801c0d145544800810004a601407040440043e51440c081d451840e04e0750710303590769240c041e08003410441803209900601c41c1c240082e21446054100900940006aa008085550034092089200d240840040010314548648480e42d0740c072614040c2c0d0148075032035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 39512244 1250 39510994 39511001
    0x706020307210b0a06210c020102070b041101031d03070615030204020c07050411071709010212030a050906010506030403120507050409020c0a0b010f0806040f030207030204110c121903 81
    0x4200140000c0e9540c02000d198040c405074205142410001032449001040001c04d2819a04c40001c0c04034000c0c0440650340541700b100b055004003003000c126004007850890091081110180011f980101400104100d002200c08107600990b4103000c00e21030710040b95941c506245100f4856070080103100001613440e007000d400e42c101c03662040c0030a5a01d4001c02c2c04d99200c1c07081da280075000b40708144040e00e801e111741014894038220540c01d1400e260358010050f82c1c0000417075850b183c0031517000680c1c0c0c42004811060a0a00782d081d89900b0300f03520142c081e080988600302d0b00c0c09024008501804c000080d240700daa09992041c050006d48882c040003414050321240411400708000300d07604207030380000c0070401810401003c5015041c244424946010703000100d10b00b01030b0000700131030301002511580007a0400809004540a858140d10b00400c40d48000c1d041801d1889140ca0b85c01d6a00c0540b1200c1c80744006d4071824420f4541f000c0350341c4900b01e81c8040c2e190034011003880c0d0505c00c0e030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 39513494 1250 39512244 39512251
    0x3070f0309030f0807060f0501050307090203100b04080604031d090708060a0e0c04060207050307080606101b0602040513060f060c061409010608120301050604031419031d010903020607060203 84
    0x1815461141c07030751aa00003800100c0f1054038110000600ca00401483c0c1c403443c01d032040454010022941444c0000341c445842e44200c1000c1500132001c11030070008002c001009100d0030035045d03a210741c0d40545a454110444096000c61403110043d400c0784421320b1030f885844401400b200079685c031828213451040300a0700050300000e441c0c00200e0b80c0000790390341501074220901442d031900e241071402458a02d40e50441c0e40a600702400802030722400059680c0c21103021501c1c4600401148401c0754031b5909910301c41c19001e032107074980050125550090060382c00582c6c605103580d020107900ca050390600d101e000150341c880d000030026903214410340140e00e4481c26000c125024110003c2c00d6504c4180c0311603c2903590b0350010003a10100308180c00c032a00d01252464110b615020000d8418080ca100240443d083c9d0b40200702c1d171003024800303030980740c650003142140004035040c020701000604030380300d492800540f41200c403036000d481c2400449a004040038903000007540c0e494082d40014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 39514744 1250 39513494 39513497
    0x60a170102090918070f0b03010303050f0c030d06150507050601090b01020f01060f050a12050c012303040606170312010504020d0e0d0503040201031a0108072a03030b040506030304060203070f03 85
    0x2440302e80042d0340d481e031050340540f580411820400c0c0012280c0c1d418402213600c00e6100444100c82085070100b01c40940741103a4141c142242c0341c0000940705449841464980c0000b80030000700540200313a580d01220603100c1c04032620202c6604000e05480c02c3c4190036025100361f0103440100407a003100e400610300c055044c41034821402d42c00d03444900352003203a084880240800d520510460a00007041c03401002c801c80d80c00940d0403161130f00b0703442e00414111181000824452118003c2c0454810340303520076445102503031380c501130070b0440061400307010703035504101074031010600c10a000041d145142950040c141c0c0c01c0e442d20042100179402141144030040d01c550004a840100380111404d11250703803a01a41ca203058400102240c6172401001c50007403100317060f00d4503660301c10101580b0001e2030400841866116001d40341d01c0400c40c3c2c8400003692011488010113615810a8501020581e8188407640701c0004140d228042c80c02201c0041e0700611595010814032080b03030621500a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 39515994 1250 39514744 39514747
    0x40203190c0f14100302070305030f070c0210050a02100b01050a120f1b0305130f080306120102040b090a090603110d06060306050c030708090c0105030601030c051b01090201020d0305060a170102 85
    0xd4280b0401c110155502c00c6404030241680d8040c03504000580700400022132a08510b03100081d5405007c4d03000151044010025000029043e1070040000b8203800760014030b10b001c0f07281c640c1001801540400d4021740140120080c50311001130340e000d41c0c001104140c503807a044c40c0c0b9076101110000e0b0f00300d80d505041501c521034203d0740c00403840b826880c0b00000114160b00c003100345014003510405850003a90300309103c440004281403c8200c180d0b10340c0494066565210100043d6400344101c41031710007540b0006001400c0349480008010300307141a60602c4045a0350044101103c200b8407002d482043c80040d540c00a1408000e40300c0c07464402c071000960b503920ba44a020480d8421030700140800300010900180d25000120540e02c1007100c401400c12000c102c0c0000c1c031501001d007155041c141c403081100008d034000c409480c800c0f00050502c4c80d510201d910041d018150401703060f80940585103200314650b1103405050700c1440058041c81219103800c04143c0004480c095540d1a95070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 39517244 1250 39515994 39515999
    0x903030403080409051e01080a0206180a060305160c0b060d020a0e01030506010303030f1505010e0310050907051908070b070c080102030708010807062c04090203070602010e060708040203190c 84
    0x5410181c0054007a04c1000249454030900170b102c1e0342c040001403940001290010003081c40001104841e881d410b481061701da044401d446c40503200500320665010071003110106540703a15500c070f240705009601944e0104060040152040079071082d01800b01305002000038028101100008003441c0301034009200190703940a40905a0001e8004481c26040840104181b60303041c00345c820150f540346020004945464400c420b441072510070179040c04408a0160316560b010b03c84003000c1010030b4030510052909a0318940c940e8010300a042c442c3d0918042c1c05008c07006400314205440c0b50800400440b400d0010340d503030607000942c089440c015544000300d0224003e002560080300c0d030b9210188954140820070f400d01105801100c104040c000c141d000080d54074410380b03220041306240980040007200032602030705a032080a50140308815002030420390542c4441c055840010075510f40c0d4035a030104680b0a0002e5401039819031083d0480c05281c406d5084000b02d40384250301c0c000c00c2c2035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 39518494 1250 39517244 39517253
    0xa0213050909030403020d06020a0921150b0604060c02090a0501060906080406060308040e0711030f040303030203060a0e07120501080105040f0204020c0709060b1308030a1e050c10020301031a060a0b0903030403 92
    0x10100b47c1c044590640214100034902d0700b187e400b4002d840001510004c444008181d030a0141d59040058103110100101d00004122a44001d0a040c809850503941d20b85030103001d0806000075030202e004080500003d00740c0751107482154180c070219070301c010a10f8a00401101e5006d8041c00a0b05c1d01c640d117140000c00141c000b0002c1c4020300c4001c00109580c603000e40090507800301d0304d980b0882600200b01210022a41030101c506403681403c005171a0b13150301d0b01041242407184c2100f80041c008105200142d0b4100c011099a01c4d0704450034802c60782c0f1410704d6820381c2c030141c8008140c0d40c01c50144000600e0140c02400054100d0811181207550710324030b00042d91001d038042054102d00140100700040f11095130009404000025840c005407418000c0c0305244041a1510541c0b50140d0591424800e008442c00502d018003284c00a110700030b0f030600258800e101c100d80d40e0250444800040030300680c1d05108182c0140b00d07210081c602001056250f000c589550740c1070104000100008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 39519744 1250 39518494 39518509
    0x604080f12040c170d08010b07060e01060308031801020a1209021305010e060102010e01020c1c1101060320040b03060601110a020d061a01090b0702010302070201030209120f060a021305090903040302 87
    0x10b90296102c1555280390440000340d29603840c01040007504802038041e2940e0f003044c1c400f0704451448400c66503844007800c1c80c20050020b45403607200c55081050010a2102075005140990a5900d0789288000b801305040e080748070300c24621010402c0d81100407408281540000c0e940350014020510080c41d02d0012070454400340c000320904548501886034075642481502001c984000085142202d001055a40da4034120300244000d40c10b0745200e90741c2031050485165034043c6a0080c0a800d84915224086031704054500c0803590f40341c007600e031040c982030003101004100a0042d201545072000116007007035160181403401e100d6110034a0040c0c460340c100c0b1410a014200000da0401900d190740040f04000901c03078100f2000400c00c0c04000600021200e072643d0900f030050b0381c0c0c90309100590107409078408055103c0e40e00c04288003200c03000300341030306110b400d00292141903a0308002c440032030181100d81c80d506c048940e014080d030b08220a440d0b0300320031080101e9083c00d50f241d0010320700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 39520994 1250 39519744 39519751
    0x9030102030a0c020115060c02090c1902010606030c03140a09050c0d050c040b0d03080f091218010305060105040b0f13030f05150108060708041e06150302090112050604080f12 77
    0x41507901c080d0b03c109140d0a104000480c4049544950b0359441e19a008200030350414020348241c20f1240420a08091b0b0801c0705c000d49201ba80c801100e20004401074000e03c014428034010030b003803104041401b4400d2141100000901048842036100c44920b40f00a29100904403134501c40c2c0a00051a030762001031510205110380018100c82c0e0401c0140015100c0030b041c0d06020301c607885e03910310010f500300711415480303401282042c3d041e0b13407000e410920340780391803188410142000a4041e5200a460350034500d03600f0070b0304c0c05c1c0820745a41c80110344612036480f0b002d9646009214540220513018028080040007c441700d00e10394803070710340d100d04801c2074004480d40d621002142c20105074045e1000c1c0141000c8001d40414170709404081d100c078000804c002e00c01c803603100c841c01c00901003616403091603420050030800345014042c4441d044030f050009910986500c40002a030400090301644400c0d8840c014200d00e45480c2d59030390301a0417041280c0e0038810203010300001542801c691511 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 39522244 1250 39520994 39521011
    0x1020d060614030601020601050d050312160810050a060309170406090f0e0c0d051e01030c0906090203090c0f0105040b13030b090a0c030b07020c090f0601021207030906050307050903010203 83
    0x14218985071001d08004003400440303008060610411101d80e8010a01c241114802e031407600109040307182007400d520440c580f80081c14900700500029000c01240d042c450591500c07000c400303482d0320740a0144032960307110f083d6004520010500599100f5084100c029100d03141c01c802c406000c152003031a9410a030808000600c0c0200200030043d000302c1c11200400880089117624144052640503601c1450306001c4441d45a501140071115904031440024841015183c0359584a14040000481c0341c07107078a016906114011429010900c00c680c05511000e008041104e80b1200303100c0080c1600d00c856052003400d0100080e02580040142049141d0740c07010520182140381001c1086409002c170071003a40120b41440000718111b5a00d025a50071055002c20b9540e0500300b2480c10204071003840e0020010014010403a402880b0503000308e8098099078080d021084d072030401402604400707000034100500810609004100554018210b850b00d40d00c1c20180304042426644151029007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 39523494 1250 39522244 39522251
    0x140a0924060b0414031c0207060e0d0f06140703060605042603030c12070905010503152106060f010c0314030c0d060b0702090a050114011407050105040f0311030f0d0f0e01020d 77
    0xc22030701c0d0601151b02008120448172440c0300001000075034510322402048280842c150340142c4a0b6100e905d810702e080c3e80503240c45041000d43c40e0a0026000241c205d0a1080010b008243c5541c000d0059209a403850385d141421700c0e02d0100440c5100c02101080462241003524081c00c0382014402140f044054920759682c440c05042242c0081d44000e0500003000100c072802e2182d070703038407008603500204400c3c5c145040c5200080004d078400c0314103c0e4941e40d00065242d18001e0788001c20301c144103100031124400110000c0c0b0040d6046100c540004001880b00c0008030828209840a5900035900c4581d850030300805a004504032003c0d50840301e42ca81c3c0102c0e4150840c50608142c81d80311540032401d110329490301080310024044014900e05002520104484500300001070311441341d00480240001d05140c1011002d942e840c417401d90014188244010342100004221500122007401d00c51a2000845505c0004c0030102d100100103900c0e080401c0126000f40060300d00c0c0341e031707440000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 39524744 1250 39523494 39523529
    0x30f030a061d010303180e010623031003020a0902030c03060607050a050d050705060a1104120305072001020f010b0d060504020f040911130e06010306050c0f0d140a0924060b04 77
    0xd01189412541441100041c020920070102c40786030351f904648141c21710290301c0c03090b07980b41004e004244d848401544008010443d502c502c00089204a81c000d071200d08030b079500c61007040c0507440100e03031b4025043c0040001c81d41c1c9090003401000ea86016106640c6109076540d00c071170a00e00010380c058001200400c10304203208051107003d80103c00c161041209100c2c1c804045060b004a124050300d48840003503075400d05000e00d0071242610750147d0a494011103054080182a50340301a80c0e0042c4501300e10050b450005200d69540910014400c421000f000c0c0d0307524000e000b008100b00c0e0451800460407086444078080d1498070351044240d40701c510700020900042e00c8103030150350b00841c20001c01404002000c03504505403a000100072405548a4413200c0c01840f80c90800c054074a4000b80b80842e0200341d601101c081201410603140b0741d00c61880e01026140745041c0a0450105210300c95514491100ba102c0181c6010340040349440d0b40d12102e44082d001607005041201c1c0d00d0400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 39525994 1250 39524744 39524747
    0x3050c0f06010905101436090a0b0708010608060d060204030210020a0b0c34080403060603051203190b01030e2e0908030109090c03020d0609060b0f0102030f030a061d010303 76
    0x29280a017402c82840407030720005c0c4001401c420646440400c0441d5401100804440c1000c00b20030482c451092452083c00c108c00d14655644155400b42d03421030005000c00c0c1c40e940315180c01412034600d903031000300319114481080135000748060100d400940c2040f0000040c0c0b44e091541c9074030f0082c2e8002d00480c90705801c141d070b81c00c0c1000b840001028003c004681800420001d40d00315009240b5405003290444500081a4800c1250281100d2800300703002041040030f030045410350f4450300c1550610f8003c600c820201d404290b5968007100d00003013882000a0f8241d1241e658402c0514000c90050080101301c2d0802030003481800c800040181c0f2802e0900d40c4005400b41d0350154803040000c02101d0701c49803030601040c000c1d080f00644500c03030041404000442d01014503001002c0900203110707403424000610704150f0444485040401500c458580401c041d1104501a00074528200754980b050420384d00007003500140507903400e03021a9008040c02aa0300210040110700150350440c02c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 39527244 1250 39525994 39526021
    0x30412170f0f0a05010b12040f230106090204050f01053603060c030402060a08040c0302060a030b10020f190f0f050c19030302070e04062d060602150403050c0f06010905 74
    0x200e001003802c01d0010400030b5080d008035020300760000407d00031a100c0345000c4104102d2100d0280caa0040040c0020b80c0700c44861441103182d1044c1e00800045685038070000c01d0340034034802c3c60342c40105840c0c0da403440c1d4000c40080089416201c4a89440f4011044c12074940440f14100d0301180422070304180340d4142000402e03001004410340341d00f50700e0594001999849200d03880d03020080c5e0903002c602008680c801c024081e65005104944400c82258018001c00740b80d0b010610541c09040a4403a040c000304404803817410800180c001c41e103085010464138180c2101c1190120b0300034001b20003080c80390b80704090392441080a00541c10ba10020040440301182a00c840c3c003809040401c0080d4000030800200c90440b80412050b9a580c20844001c14030351007a8503110b8500351401c42c01d49050410b08500084000c0100149502d4020480c1d903228038248181c2104621004680428080c01c09451420361500484140e4051900504d042010a07406070f5039003030711803051000034190002c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 39528494 1250 39527244 39527251
    0x30b0901060815040c120b063c07032303040302060115110304030503030a05370902030a0b0103031103070c090216140105071b02010c02150904060803030108010c02030a05030412170f0f 81
    0x4034424145203600d000c0c1c480c94481403070489d0942d00e1001d40ca070344c011889600c1404034181420031a03120070b01c034100501601503001c1c0e0750907502a40031003c94584446070960340905d0f0142d00038070311682400c1c10880303840c0030340f4080001c0c05901c030012085a10100000c0015500c00c41c007071501c9081c042c0c590000d480d409440344c012452186640d11000340302501c810150302920340781003088041403001c0320041940c5a0080d42500545030040103002c3c0f10200715048030b209943c0d1540107184a00210748074000d0080c000c02e43c0407081c008010200d07664015000750071005041868495960361200341004945001c40070a0351148104801950170507a14040304c1d10402103a5084001540020500d400804000307119211708001a00d00885010560b40c01f020050020000039450324025941c940003407161950399800d00c0e040c251203520210640302c5120468132201c0c01d648841d40c0d40034040d400300012404004032030b0181c5080c0400503001d14003402d5003210f04e50480c1030080034001c1804004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 39529744 1250 39528494 39528499
    0xf0207151e0206130f03050d050c030f06041104030221030301082503030f1209050d02010e060a06030b010b031e0a1b0908060a020904020702090103031806030b0901060815040c120b 79
    0x2801c0040000c0391340000004540d10101105045007586000c0d207282c0620b2514003c018541001c02080503c2400110301600519440d0f00403513686000308401c0c1c81c40703107040e80c0009805110130001401c2052501c140c81950400c1b50120b010740350481b9213590406d0788000301c00d41c000c2d2003000ba5108400c2d00940400c503100544508641180c0b4060310002424031b4840c104910701d180c251940c1c0342d5600c03080c8c1041e40013040d00e000e0f04403120000e0203043c00310f0100c812130280e8008074548403c0c0340306540c2245d80c03255022003680e280c5071010303000e03800c01014940e84032050215034080d2504e42450601c51661100005501182d4144100c01c240500c814072040c060b40302410f01c84424000f03540740d40701898580160744d030a10707200464081d00400c100250081840c2001100301500800400040c04c09611031001855469000724140c40041e85d10a130002440c4005020080c42081042d60007410a0200a4400d90001c0072904039100e03000501c002421030380c510301c03107001c5d14041c0942c0380004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 39530994 1250 39529744 39529753
    0xf0204030215190c08030f07050d0f1e0506090105010e190602010510092c03040302041a12070b040e070e03060f0403090f08060a0216080301030602040f05090c03070f0207151e02 78
    0x280d94a8081d03511024015900610061f4006140c0c64810320468115202c210300a01c6400440d0311114050300075014070030a18001c5103042000349056110702417164030014400b0744d890b441e100054903410302182e141a0072500c1064510000183c0c1d02c1d0071401030a040d40002035500c0e00030031010010545401c244103407070500d6460500f41d810b8506212890138414075541040c040250b915145108541c402500079092a0f500c2c814620780b500038081c0203800752030305808841c0340a511603e0302c8203405500e45451090000b4483c00b101245025440790460130300300c0402201600082c60b020040300d0758403d40d0000702c1007104041d0300520110051260419070b02206062010a0342c070303000000e080f560300c03035404544070610310a40380102e00340d2034210311441d549586a0a100b000782d4045d000d4440800400580000c40e4102501564420001100302500303607255403034102c1d00340081000070300c2103100d500030124104240080c541c0100120351030b00220502c0d00c0415148141184034070200b503410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 39532244 1250 39530994 39531017
    0x203070e0f130c12051012111302040909060b0105041208030402130c050a020f06010302061c060503030412030909090c0303050f040801050711060901060302130f020403021519 77
    0x10410800008410308540740c442002052010070200419544007000140c1000f031501849500100320950311400c0f44001d20860707488650075154824144204090245440d4654002c9484801606c01c961002000c00b4404411810310030141d0700f140d0480703034000703a0743e9500604020103803040a03003200007070030417504207842c00700e04011a411804020b8141400080000c04558850b600e8601c0d01b400d8000400110780e500b82d00070415040b000071003002d407007459000c11075000f00051940c1241c0d40200454a009010140760020500c2001c801860f01d8a030000030030300e5a024000342c005001d0604c1442101105402c1c01031142e802a07004010591a150800c0003052000c031400703080d6601800d110380d6036003021192401c10300c84c139402500d0300c0d40b034517052000c0307103501960000382140420112401074441d008820300300c401600c0001e5200c1025400d840d03801d0300ea074215070420081050010305242c0d0701c0d008909448100000341c1115600082c1d050b01e0b40c58924100f0941c21554504101101c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 39533494 1250 39532244 39532247
    0x6021c15030804050d030509030a11090702011e0b0102010207060509061b04030203100903020f010509070e071b02120304080a1b0e01080d03050a0b06190206161202090105040308071a0a020307 84
    0x10541c001c0034011188174440f1024140200304135103180201404903201c1c000c580c10301d0020f01d10404440c6101c1c44001b80414551481401400c0b82d80407220750200c0c42241d0850700c0801820004280703419035400b440800080344052094511840504000d07040c01d00d440032420000b08558460702c904ca1609020520142c3c500091301100d508907020300061080303241c00c00f81c0c5043c1a84242c1d84041d803c150030081400004507800c0b04486400500c040d068550700390545c3c0316080c84039210f00c3c901c0504090340144c58a0118018102250350070740b482d058582e40702d682450300c041411746840403460004c1040c0b40180d04280014201740e54000b5095050a0401d23032514840c00b44a000c00d80c4400209010b01c0e0651f2007202c80c40742c0200412f03600c402c152401c92801078044001c1026005090018600010204150600b540d0035a50907290800c030361403d0b40290464a04141000707070501002c00011140001800c90a000385402881c031552500d0200942000900c104030319801441407040f030a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 39534744 1250 39533494 39533497
    0x5090102071502070206090a030818060a020a0213020f0f0403050d0c121d0604120c0e072007260601090204030209161103031306060f05090408030a0906021c150308 72
    0x1101001000341c0d81e80395a00006803e0b0041d501f00c3c5a000180745030000811402100810200704111003114241d10b0b50b10402c02c060041d1003e050260700441d05c031a0062820002164542c1003036480107007000d442010300e0485400060a21002c2240024180705100c81000545809003243c078000f440401c13503590b08400c840e00e84141605100c8a05031321007008121200150030400c001e0702141d103460ba06e40c0c0300d0664400034402911050001507022814404440c5042d102d610a51640b6001c0c5803591a010000600c0ca208075001e4028944003190003180140403410711048228200c0c1c00c0740414030102d003001c03810323882801540d104100c00c000580362503030f60f00d1f40082c9030315078501c842d00c41c0c85054074000360b200c0c84001e80303000c00070801c1802d500300f00c2420100c50096804115041c1c40b2008507203089154001c1d541d10003803aa00060014139528003c580c000300c00c40c40800c035001c1680e10301e070684e0000f0840603065403425001c11100c5500f0300ca03810f00384c05480b084060451650715000e05a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 39535994 1250 39534744 39534773
    0x60e0301020c12071e030801050909060408030c09190e0106080c030601090506070311060408180f030a1217041505280e0309060706020306041803050301121a040302010e010509010207 80
    0xa00f5008038400c0103003e0070a040122609000c0e02d200401003c038600106900300c02d01440e4815101940460a02d2000003441c900c515800b85401b481c40c1c50b0909110311580011001c560720001c0f000c61424030040b581348820090007084d0301030a1139410200701034504c1ca8000e001d06500b20302401008610380e8030207000000c84009540c41c03070350b605007410b0483c2c2c502a07003a02d03410648501d10904c82086101c000810340004020700410311807800030b00300041014569a103e60591000c8071260110b11103903001d04146d8581d08051940c20b0703d46485440f41c0004a40a448000d42422092405500d40c000c6961042160840c0d5140d4411500300700d0b881c009151030441c885236100c821001c114800c104031021400b0081c095611440245802006513200305c0760035005a00340108100b900c0c00880d190700010394540c40d402d04603820645050301200045405030303498607032017111f0960032820340800d80c080c9010b40d00203d04508424991400d481028240c0380480c2e104010083c0422416540e4000c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 39537244 1250 39535994 39536023
    0x1a0601020f1b0d08030f0411010f020c0909070e04050a0308060a05010203030718090f0b04060b091c050106090c0c0308070504050604090519020c03120c0f07060e0124060e0301020c 79
    0x400c0035001d0b02003002c40b810600020300c030350030010910614428200400d0f108034480d800c10b198800300328004540c0c07061066502c802682c452410b022151403d032008a910039105801c40d05059512030101c1d04124061350162a42e03000b0a00300024168031a2405520400c00d40e07030704a070300d81b42000003507603488000d151108000d0b2820f030501600c0b400003814401000d20400174444030f04440d04080042135040c0000784914034003c00080c107005003d050b2980004014003c508a115100f018584a41c05440444655680c1c00011a0f1400039104d0072032665807603030350441142c503103260150003409c0c080d1502e018008180410002175403410f0844064135154240420142c40e460b103164030340000000c00c40d101d680041001008400c0000141130500c00b03d0341000d410741c03224a506140391081d01200c0c24480000c01140010600700d407c040ca8000c82c80000003900c2c0c2c0310240c0035581103980002d00d060319800c094104400d652100003070700c0009044008628146084950683c0e9602c100076800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 39538494 1250 39537244 39537283
    0x30c0304021210230f0f04030c1b0b09040509120910030e070303170f01030f06020304050a0c0f090b04050c030a0b0607080a030b04113103020a031a0601020f 69
    0xb034145814444500c19402e0b42c0c005100350703200203413845500783c00701c0854004864420001800c0c00d41c0d182119000b5600c0100750005071b21161030071210380201d244140c1e06201076220142c2d00f001140c582c0001040740e00c1c040d170f49420b05c400800c81600d40103000000541d003c40d4100c0c5c0c04100030004c07603140c0c0d0012180c41e410030303000a10030f40c042c00010103014818003800313100009041d001000200c50120100f040c7c0c81c16594580d901070082c07c28000903100c143c10064490004100390700542d0001d005000b180d412183c0b81d075802c0314142c11034009590941040e41c08118035046130003418840441120301340801d150440e07900c240e17400b00800040001c1c0d1241d43d00000754589404844429030060380c503d50320060690007038040d02140c0042d078000c5191170201424041c0e8202a42c000380170002c52801d0107180c018030360002c002c00e0683c50311108100c036400030060f6205450400103601c00ca206034030081d008100c0107803d401c010010b5042d50001121000c00041c04600f08191480400c19038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 39539744 1250 39538494 39538519
    0x804021005130509041101090e07050d090602040b0c07050a05010f05090d02010c02060310030203060705031303030c050c010204080a020301050601090806010e041104060306151e0905150301140103110303030c030402 94
    0x955400303082c0e40c4100e81201074841844184280012440e0450001781c0390118050f544a20020003204100c0795040003480c1480006076181d0640c0080c07103000d029802c05418103450f80c100d48010360100c141944541c0c00b9a03c100a1400c001321490b00070300f003d00306110519040f84003d003a81c492400080d02c1600c00042c603000b10ba0003010340c3c4a095030040d10090316440c0560704c01c1041041d40c04182d00c030f4840c0c1c400080029110f942202d2045d00010034481e0f11550554059001d01254580041030140070302c07076884950424806000184103807002424025aa40189400c49001405e41c0d4100000b001c001c1c000c500c80041e40d281140d00c211610f5230255a6803c0000100030211031a940c060b01b1703d04008240000d5411109a00b0380180c01d000a469440d002802e050000700c100242502e24224200401d8001d5442198089162540141c2c9003002030b0000c0d00311110800140071300307451040140107000404c525024408801c0c0c00961440c141200e80032643c0c0002000240b00d102c048441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 39540994 1250 39539744 39539767
    0x1b020316050f0a0b100503070302010e04050a0e060702030409140606270405040b0103030f0807080612030c03030108070e010f0303020307020418060c030e0c03070e06010e03031e090f010804021005 86
    0x1001c100151041c10f0340c009048500c1d000400030001d85200b646640b00801c0451035150204184085903030503140c80d0b04c010380e44000c0c000a03140003085940b00540d24540c0300050035013400450f10494296000d950b4a60501c0c001100719072100024016a0b0140c00800100e0b03212031040f547c81e82009800c8a150803090980c0d080455100da8419400600340410301003000f200c82a018107817482500e586285001100301150b201104450309000a1145000303d0044d0400c5c400d8143c1d504403000c03d80385486050000035185030700a902c0050240e11000d0100842c604112032640982424044071768443d2541d10300a40d0b034010a03901a10496403500105a500350002420f418140e02120620420b0035036100a0b00400c69000c0d080710301d0184075443c1e403040c1380108075101030360158041e003a069200d80f401141c0d40310708100c03666054481009a45446450004190b14905181900355500c221040500041030200200107040c450700c2ca09110050759071500030b584649403480c1164860310150130 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 39542244 1250 39540994 39541003
    0xf020c101109010c24060302090f100509070e030a0b010305010b030708070902090406171605010e03030d050c071506180507020c10020102040f030501060905060907021c0504271b02031605 82
    0x4a6103903480d05c81d40031601140d81074024000316802169152641d03a9030603002d44140a0440300d07504801c00300350781031000c0d01d000401a50042c0309450031088404001002ca8586207c04100b500d07414841c400410412000f4000d6190603c026809800e400e80f030420255030307810660242146550300401c060109450380e6001400411040300c1d1000c840200078a22500d40c0210b5030188006030840c2c1d004201c650061507801d10001c0080c00440c80c000c180b02d40740c00140382c0549807201204041142501042840424040840c0c0384e0b400000c0aa281c082c1800320f0103001900840c0540c10300701085460b035000b282194000d4801d4824003200c45404c2d104074028800ca800c690300303100d40c650001c814404154814400d466030200700304295202c20007001403a00e0121801401a400701c034070000d400c0c1001300700d20701c52500c604005060685030700612000241c109010201606a0140f10012050178051640041b4100c1a6a4100008000001d4680c0f2440031080c0c41d095012030a00304100b010030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 39543494 1250 39542244 39542273
    0x604060c1407080a0f05030c09040203060f0904050d02010e0d0c1407030c08010e060105060702060a0c0606030204050c0307030b042a14030a020417060108070302010309080d0f020c101109010c 84
    0x25090342c2c0b811a40340281650f08034007051000501050340e580d0002d801281100d0040c0c00091201d81007021140c1048060340c03004103103035044064003d03803070308948880794854015403140010346004100014020f003180e410170000102c03640091a0790601e5500b25650000191b04884220b0307640c0c04c11001d4900d030440641c00142040302801000071030f0b141c10742c04982d16410107010f036081d59980380100446d0340075548010b0741c004010440e0b403c1081c080d1442c0b141d0135201c0c17000400c1040d9260000341c22610b00b100d0701c0031201400000c2241895051003843d038000001c030f40c01c1095912042c6003111b21300034440d81b004025180300015540c540240c8106e4044200040081c0e501c2c50b1066130b101c00b94200c0c0c41041540c200d03084000c1507031400410841e050302c0580c8010f04050b483d580044001d40801101030320000e104204c002010309140c0502c20952016507005a594544031410a02d861814000c0621f0035103010305c1c101448141e501141d40b050f0003468015880d038902d08200381c0b48139070318 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 39544744 1250 39543494 39543527
    0xc090b0301090209090105010602070e09030406051318090c0b07050604020609060d0e0a03091a1204140f1509070e130503040509010e0604060608010608070309080f121504060303020604060c 83
    0x1101001180c105c1500130038181d90155003074a5580d903903007110040e15032080e20041c02c15003040c0014010103200e0000f5081859807400c900c46019030368007050212542d0714410850f690b46030301d0742c01c0500c401c480d8400010000c581100f8640700d082d440d40d544600b00030300001c0c402c071030006800c145076407400700b0340d0303203801800e0400c0040e01d000c5e1030031964940088500302d01140f0380c890001900e5a41c1c1400504907a06c0500481c80c25000003003401003154003c0080701c074170341106010016402c08100b11100e001c00c00c0010450703003100880c081c0030b4040080017221181c3c405403090004201c2c6c010101d8205140d030a000200050302d1401a0840c0140c0d0440d41c1c1183c0450300001c0ca03000d50580a81c01400c05a808002c40c0d5101c082c100c540c40024011000850306004c00700700d20b584260b0180c405103000e0040c150404403a46203802076039000100910360340300781e0814015004c1081421658004040790700300492803441c1c0d0003a4a4090041000d440c04e40d4511032401e0580c0128020400082803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 39545994 1250 39544744 39544759
    0x70302090a08010501080c09041208130804060e09010807060c170412080406080c160b06030a0b09030403061802150c0f0a0308041a01080c040f06080102130e070503040c090b03010902 80
    0x4800b60075000f0007003440382c0002c504c1040146010780c06c0c8901c0c03681c001d41c1c024400006450b0742c950113640b040c01c040c0c86140e01c0da88140c14140403866aa020300054001681c48081884074041080160b01c0182c20400181d01300d50f80800c500c079000040c825126500100300c1e0341b0706c1070500f01c54038640100d921099080d04462407601c100480c0c880140f050758199166602192543d2a0b401c0c0240034011000c90090080100b600100f410b400030305500c26001804c445400c1195955482d24100540da42c1c151303a44003040c1070003000081d029040902e0011b5440c20000d00281d0002030240108002c010100d16002070504020749052050081c042e60003400c43d410092a45802440400200c1c3e0988a001420145e4103030b01c00e200c0e04c001d040b201058024002c10025500b08002899804c1148080a0ba5004000755110f4207002404050303241d0100407201c0d40c94600788100110303004003141c04001c410800c00c00081e0400c8104420b64901080001d605141d1001090050620650180d0311584 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 39547244 1250 39545994 39545999
    0x4091107051507090603020f030105010827010605100203120f0408070b04050d030501080d1d0105040e04120908030c10020f093c0d021017010b04090b060301030515070302090a 77
    0x1101e660303d00481190b034840c03058a0380c0784400c134102e004003010703001048000c000401c030341c3d8402d40359150055004404600c00e0100340e1451b1080d8681940c91040b282d443c0c0c1c1c1c0802036490041c00c80300084206002462070702d80121f28100da00840145401810200e0001040c140034003e0700340c0c0e400c15808056658542407505180e60b46107003003020034001900313100004c83e00700d90100d010302c02a210ba40362a0208250850100786200d50511040c0c1041742c01e0100180b501c80d0403018501a038080c42c0f5200040358030030303030060a04c0e040303400040c0b07d9442001824480140014601c205001d506001a2070750001d160040d914880c212500da40400350808102403002c91030a80751080252221003000c030380318041410f80075a81581c4003540500d00381003000160400003101001c41005203408447c66842e50b0050521000a130400d0386030080c04078042c44400040d1003070a0343d03010211480d5085614581d950f90b80c0e00b01000950a03040c0303075003001c1200756001381c0541c0c41d12900104140f01068 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 39548494 1250 39547244 39547273
    0x2090901020c01110403030c0209060103180309080d020f301801030605040509250306020304152f07170301080a060b04060321050d090602090111120409110705 70
    0x420000411102d5480c0c00019040c418814084804495140e01c4a44080300d0303035001c0101e00c1a00520050605841d101f803030b00b14483e45150710f0b0605220381c03a0b100c1468100f8480c4d528101680340c40300195841081d0240e0740100004401000c0e41c646030004003040f188000c040205100550300c0e14004e14081a649402c4440083d00b0000890a0740c0800006070b440e002c000660f4010b03140c030101c40d00200741c060f405d0b82c004590140c0400c010b4071410807580e075070f41c0c070302c0105e034011103055801c43d814180018150895006400c0200300c010124190120b80c1401d81010480400804109100000e00d0004000100c5100403040d0800d24501d40c0301d60751503240c6a00e90b41030700400c80e46586801d5500e030f11894103201d49015030360006411924007200303c480184114003404c0d12000d000f010b11001c02110168058958100e20070f41c40541c5410f0b00000140c9501012074030003002d074008001d580200c003910740c01d803821509400b0020410340941300401c1603610030081d0203071039401500300900e01070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 39549744 1250 39548494 39548497
    0x2010b09100b0a0e0a0909110a1809031404060503100801020f04060c030201090f0b06030d090b04060e030f1b040b0f010f05091503040b01030308070507050a02150d0e010e0c010e06030105120a0209090102 89
    0x14011a80e01c0491142c5808006a00c9c503a40130385940e640030304078500c076260525401002803511909140c2c0303d082d00100d018035550050350200780010000000c11200c000c0600890000b4041000294200911030002c205030340500c0c00380c48100300f500a8003005151003500304203074071600415414481c044508115034a00e001b02d0b856402840b4542c101d904151003402480c0c00c803032140220701d06150a015007210142c81071000d01e60305224240b40c1009000050000310442603107071a80300d09000e289010700c0181c0c0c422041c00b40c41807048045942960340c1107060614204440d00d0065542c00128000500c50324241503440304d1a00d002c0100401c0194182409040c0c80c021b440704900c5d5502c14000301c03030302d200c1d44000a26a4120158940c010f06002c1c1c0544110807803652403d00306101c5410b004112554030800c04910b070b44481202c8013409007400805400303a028601000e00d01c441001040a91106100e0203004182078000503490f8001400903e02403603005000010b54208900340f40e001c0e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 39550994 1250 39549744 39549761
    0xf120606040c0203040f050d1406090102070501060605040605030f090712031d0306010308040303210c030b09100f0e040f020603040507031a0714180a06030c02010b09100b0a0e0a09 79
    0x1d9442e00302c00c01801800007042c0d8084803018603415003c141002d00303000703a103a002031040701c0003500f1035080d40d0025002d1005a01c0f944018000503100c0f911414031600b0743d81940e000a081c014100014800f80d035001089036070144402d0b02044c40c07526841040d515040c110b60121618102407080181015070041c8440b010b030707892a0a100c055141402016100d0500307110040c0154001c0008100190154a050440c200403201010b1745040c1010004161500d610407040001d82e81c454080c003511745020100e41003850030541400243c148404800990710a000e84080700e200280024200f11962000c00401d41d40601007071346074107103450081d6583c0410b00045a10001c5035450300701403015911b4962050407103548101801c4e0106040c1c0a00e41d01004114080c040420a014030544495011400501c1141c2d03002a5180420900070f0842e060b4048180c401c40d001070611a0000e00200080c00340d03010581d29540d155028001038440c0d04460405a42007481044c00040045095126015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 39552244 1250 39550994 39550999
    0x60504030b0f011202100203091009150e090a09080c100213080a080a0c051603030f09050a050d0204111c0207020a08150f0c0903070b0301060f020a030203030c07020f120606 76
    0x1529224400ca12620b40402d00895124400110b48100541340480100780100400d00580b032809180d1000f0404120f0821194404620500701c20020001405a0761012050500d0030341304000e4410300140591802419495016445104190a12802070100d0b64032a03181821251b04088011101300603411030b649241e002c41d005800020080000314001c151550f20425007803600080140589002200040c2642d0b14800c01044a6440da04082120051800390301c07108840850300400910000442d00040d00503000c0141c01c00894581d4559042c005904607004280301e0006182444130740144e10b410b103c0f1228040002e4024401c0340d0003010403c0c02942d105490a03161510160390350b02c00720765020200c081d400000c00400e290030f02c541d04902d54558851038038103250000f034900030407030b008100806c0000004100c40758200b05018542410340c00540b603210027030344000c0d440c0d000c0108141c452541c0000c2590442d0340702c0c40304d0200214000e10404680c05482400c582e03c0c0d03400c803116030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 39553494 1250 39552244 39552263
    0xf0e0f04020409181a07020a020d0c050d03030504020a120c0506180303031302090a02040506031b0d020d0f0c1e0e0109030212030a030b06030105130917030f09060a1a100c0c06050403 80
    0x241d844804c5c0100f5100784010740041c0307440440c030f0b4288520480160015140700d02003820100c1c00755123104040491a001e40c0d0007083d1400e00e4010443d070a103050340140326003444140c1e080002f816004205049400c11184580c80d10380d0750550916403112800c00d2907050000004111030f64002d400c045c5079403030095581121a41d1810780076400c0340300b04d0140366030107941407001800c2217101519205102100d44560381c00d00e07500700c0b60700d01680c02240c0003003200394854412000c2c80c080f40c821001d0840180c83c2c80c0c04c816820600681c10b58115120031300410000c06498042a400f07812240e0046030b01401c3e81c041c44100c4210716840b60080e031526000a401c01104c8070721490a035090f24162040144131400d00181c0e1015440180000441183c0000304040c07450b4030410002d019500c11144000700c0c102500d080451039040c40001000e9682c42c9103045c0e524403004031080161304441e00140c4030504980b5a00700251086d4515000080217084074900104c3c00350390220103041100c0c425101c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 39554744 1250 39553494 39553523
    0x7080a05060a1a0d0507050301020f0702090c04050108060112060f060c060506030607020705010f0e06030f04020a1205061b0c0f010605030f010e03070b04020120070e06010f0e0f0402040918 83
    0x450540f01c600034030b1042915195525103452804118031050144240100d0b40038503540d101013400d80c1c022030581610150045160320550070310031141a0321044a14a00e80350074144000a40140d80180080e410000d00c0036051524644645c0200003030188c8210000210350303104802820b001007100b0840d4400c2c1028003040160400081c034034081c02154020b4456541007000440305403608510b0a001c026864030780b0842d0303131510030083d409220720b41410701ea00e18103401403140c090300c158440b03540801c4585860707010805c0850b041c3e8003c41e42c07519403442e4402d81c0c6440442c9004a0700308940b6406928a000201e2405500c000d01326041a01920800c110b049074a6089a003450401c0d05241c0040080500041e08a58401d034000d105040088110880074105003840c0c81302490003231b05a025203402e00404a0501340b05901007002d29040044000300a401031202c41c0d0b0b4003000b4051610b10400103040d279035035010368014001c5610100019180d05403102e40070b0508040a0314000c901d80c800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 39555994 1250 39554744 39554761
    0x3130e06100e010c020103020d0609050103080403050f0d050412020a030501021201080c0d030815060f070b01050418120806040f0e0a02090709030302060c0708130b030402120705030d03150807080a0506 88
    0x80c4030b000300b050b121032001d015213400560182d4480021096000e0380c480c00883c0d412428071405003c2d41c003540c280d545950462418518040c0300142e1070007154040b200407400070341d000c0708030b0b0706842007a8441026114688080341060903036400090036940042030050340d000028629034100c43c0504201c5a03982100300c1802403440c40c1000240008264600043c0180030f042d540c0c0c042408003408807403030044114030303100c0c0540004000301d507903e010400411407840d0a006a009c000d480c0e21011000030303940e680c8c0700310240d03c40a0060030300c07068000080c07441d40c50703900040c0c1a4998140c203000003090051107c0d100c500c485405c0380328030a503030081000706105440724800d90758142c005200c241c46a01d02c5843d00d80045404440c0c003c020851089061083d45204008141c080364451b100e0816204101d030340c641c400e01c1c941890388120380400032544c00184029242a02d81030003c0c00c000011901c0d0880410307500420000d10540c8000142d034840010881d180a0089040d13580340e4441c4281d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 39557244 1250 39555994 39556007
    0x50c01150611061810050907051903050c0a15180902040b0a02070e06180c16060203011701110d020703030603021203030601170702070b0a0c050708100e07030203190503130e0610 78
    0xa1144c499020703d1145003014480ea01c00d07904114207900719090f840c6e83d00c000820003100d2110711947d40407400c40410802c0420000c558404a00b1120802d40c3c2c0d01f040709242044140058038000c100c0c030a5001da40040c1c01030074900240440310020355032583c8555000202c0c1d407207044284014886c5c24400550325070000800d034050760000700540030034200101140c41e0050090b001c070141320010440303000410242000030001600c202c0003d40c0380c0d0303d0482e61103100c492b11f0384840c2e02c071b9060465508155940200311040040302510040e00c1d40740c0b50800300c001b805150402500507000000310580800c00002951042d1002d0ba1010900d00414102e2202c40c40e080d5000000343c2d2205c0820701c008007d100250810106500c0d266042c07840b19150b242c07602c0b45640c4260034580085245403d030b4842030050010110f01c18000b050302c60f1a59000c00e5460068003140c45030701420b0f01b6050100035041c0f04407004aa00d25510004068484105a0490509658580c0f1030307076000031541c00e441d02400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 39558494 1250 39557244 39557281
    0xe0406030206091908010905070e0105030604031713020604030516050109030b04080a0c05150708060d1104050405010b151c06050904030c1e080702090a0203090607050c0115061106 79
    0x40c4020f040010090502101250f4280c0c900903640c501100403030107480c2403090400f010b018100902007540b43c040300c10340140041e00890b00a401c403c04020100f0740040f400303018031070b1282d42010a81e44070b103000041c59403010710003940400006800030030322100050103071405110910032a403041d40c4a0040d24011018071004148040110004010517000c0c406420b0308072550410440919107030f541d00d810100006004040011002e040c000d0a9502252481d0b104405403040c00d000000c94845840100b041905680b240380c035980001d04000003908a00b44c0c54001038207030410004c0e0000f40300100d801940c458805203070410b0024102001e540142c5040314000362030700103039880d2524212035035045d4120603184280040c03100c40b90031488101840419018054650f100c0c0058810000da1480182c0030030319050041c4280071030703181c020030401c2e0001172605026a0301c41e200180c0e00d000d01007030551010010484640000c203503412200b10790644138113406481c000e603503107500b0403443d10350389 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 39559744 1250 39558494 39558499
    0x3020403120507120c050a0204020706050a05010816140307080f0303070e01031505190b03010602030405130e1504030314010f060f030908180d05060a020903071401080604090618120e04060302 84
    0x3088100741260055070b0400178103010350280d4038110055004507050fa800a007040b0394540c0e035181081244009842594058280000988000c00c42d1240da0f1402803054090308812440b24041c0080e01ea400704811001007407924107942d111141c8185007901ca40040b102e08012403c04203100507158801e214040307180c0e200c0c1d24002c40190602051004500c83e03070380e002c50340300341841c800b00e03074055507070041c600800745c0341e00569503039051106002e8410081545001014204440e1060b050400b06422000080a40d44c06a441c2e90700d0030114007500c9800d245800181003e400862900c1c011800300054131800c3e155181086020b95080b0203e0b00131000140203440c0502042405008028410b401c0d40300c01400424400890b45900b410b06200307890072098103074009100021130909010310310003000244245100900c4107000a00300b80d400401541c801c6a0f200320709070030803880b81d019843da030f14191f055030f030f07103144a10704000c00c00c40350302029002c9204410108441d00d454024082907030f41c017 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 39560994 1250 39559744 39559763
    0x30f1a07020609071503092406050607050c090712090f0c0506130e07090e0c120c031506030606070501090b060109090c1e140f090a090c0e100e030d03020403120507 72
    0x1040b01785200c40e500c3c410490704150b01e40e8a001c0210f0030701c85050790030203800180c00000100100744103080301c40c1c0da44010700811083c843c1001181001c11052000d49040c2e13481061607071703006011900800c43c1950401080d2034a03aa610038810001c03400901e0134420510114140e0300c0b802000003500602440c004c0c00341000c1d0301405110441a0169001401800e220405540f21400703141c03405003c4484082903d00400d0b010004054452015009000040302c20f1840c207190940411449001c1c13049401680008086840c1d91280d4040340c1030b180c0c010f4020002d88540f41742015070f049003580c840e80050441303400030890b06002d1017500c0445071907484802c5d060740004110018400c80100000a001c1e61038200c0784a10b0f01c8400406080c2610848143c1d200102e60400840400c0f907002441224503101c5031200702a04540c514904000840c2d10074142481d10008441070f1826000541d01405540403446407645c0507001740042d03d00c035a24200d2030001c0d42204841500840704040c080104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 39562244 1250 39560994 39560999
    0x9030c15090d150903121104060203220b0a0206091e0a1407030803010b0322030e010e040605040f020a020c0301090b0712060b0a0903060b191707030f1a0702060907 72
    0x708410700645040c80762141055240e070f041c03d03180403150010410b4004c103014079040003051000b84140c00040400080450429081c120003d641e4002e0700741949000c1c0d11110041c03000c904240c51000213146c803d031255600d0700c4031000251644001d1340c0c1403034548075600086480088160785200a00c81000052408059035100c045004541c1068090503005140003c0041405540190301030003410720080c0c2d880c2003a81d42c050281c40a800ca10301e00700d082c4122140002c0d40126002d040c2c0401340303040c495841080740041c008000b25880558402d18028403429008081d801131f080c5411140c00752989022a2402e141c00d0f51182d04c0c009140c4582c40000560843c02050042501406007100141c0c040e00c4580d01ca2990b40b20019000100340c103164100100b011500a00514000c20344841e0015006d00040100004c1140900340c07400105603c4c6000c1700c207040040e9002550842210000003c007810805c0f40103251040340c0d10036003e244000340717665000180c51806059400001c081072807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 39563494 1250 39562244 39562249
    0xf15040c05090307030501061d04080406030207020f040609050109110403050a020105031003200a062c0102010915050f1308090103090204140708101502070b0306041503050309030c1509 81
    0x3040c00264184081801440c40e161010440783d0055480360300000761503420310205861070391005034000c11107c0b8003001c21002829030016541107030094140580c1f40ca80d5440040c032440500c0d400182c2040c504140003c1c5055503420a6049072603a81080010800e20380300003807030740704070300005d4400c1c0e110101510055110f4002941d01031690012021079035126034854071314042c055101c511600c513412a01c5c0c81d0740380a1058038000c1400c1c1c20000e00d170182c0408607007612800c150751071003d556174141412440c0d0007034101d154240c2e440011011000449000c04000b800240c5040b0041c40d8030303000080000c064468080b110030742099141e42000c94202c0114041c1c030100a040340c00c591202c4c0c2080d414030f41001141d024207029212034040349850032081b07288010710b9100c1000203c200d52590141c54021441c102900c0c2031601c2c250782d80e680c81c00800c1c0a05400201800d0003440120004140003000c406400141012000d07071700903a04003002c0005891940d4100100500f00300020392091 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 39564744 1250 39563494 39563501
    0x6010b0703030204080d02030c0c040204050d0b070323010f05010809060408090402071a04050c03060112060203040c08070303050a0206150901290307030b09010518041e1b0e0f1504 79
    0x481c8286005031816440e09000c5040c09900d520803405030703001007031080117440700380000c400303082c401d0300d0441c205860540000d030703200390b1500082c1c00c04a0043c046000309200350887c2080302640e40e039440c4040d810b204218012402407180c0c002c410b84c0010301040c0c5d0361043c8590340c000e690200041c1416101e03600e400615601861100d9030265007003000d54000f585000e100b11760800445a065500d207230600b486402d04d4150b040862103900040014402c1c40d01d00703e190340c155500140c00580340e540d64540341d115245590040e40c3c40b4401c0001c00070801d41d00034020100071041e5800da401940300c02d280c8032924480c880415034400702d941e005000c803559900c100190a00e034000c42c4081500c00e40d1114415900640ea80760010340c80300d0036107003075042100c00d980c010003060740c03c003010010225803246101d0340600b000b40881c0f00c2d10306c110303025084103010044c003d4010b48000903862000000d6050b20000744910994205080c000500c00740301c441b421071040f04e0180700180901e482e1010000213 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 39565994 1250 39564744 39564757
    0xf142409070b0405010f0c0c060e040f0e0304090b01090f0803040f0602060c0a03020f130e1b03010e070c05070f080102210603120a1709010903021c0c1e0204050a0c0801080304050306010b 82
    0xb04016500301070f0205192381c00420050200c1e440d4070110301348070401c0c481980e000440c20320a450030903526000c0540c000080350100d80b004040050001072a0004840060181d8072201c110b010300c40740407a4102c4080004c104962641c0711415406507190790513030301d4110882c0d0b2050124014024030420074020380080003890000c3c0f102c240760034003000d2580e8a40c0b50350741082e11004055000c00001c03400e0b0083c80403020035070480c028203662620018050366803000b080340b01041090303044241009010004440035000c1030200808182d120081a4000c1d0840444101010110b2010400e017504a155841c05050b014001e018610700d4015090041d03070090035800c040041002000000d07090344501c09000c0d40c8240c0000c21103504a0a009181c516924000d0b9080c00850307410011441e000150600f103182c0c0402588403100103481d0802501c0607020b400303500582040100702c1211041d610400c003c803100e4481580a90301d9508582d03480c040d43c014a40c15900c554014001d0240d46030140c1312 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 39567244 1250 39565994 39565997
    0x40201030603080c1c05040f0317360f030c010311130602010902030606011704060b0105041a0306030d0f09170a0206160c050105070f0f142409070b0405010f 69
    0x10304030755955580303c20340c0c450b0075050070641151030143c010480324040954506420700d042c40c1018101031001107004083d1000400540b2020005c0603d40300d04019500c0d16905103100114181004220403800080081c8a021043c03582584075860301d000f2228000e4510094010607d04a0b01c8005400800010f0042c02c40f0140a02c400c660401c50441d04501170407055001241c600c2c0e0501c10305103005006441c5174140410368142c0304011702c5444806074855040712010848e10b4800300180c4035440b903a04075200d4001d0700f000c2525001828030080d4024241070381290061403a2510440715054034203403001c000340e01c005042062800444522810900d1602500d00c500300d1540000d945a010a50300344c4040c40001324001404203160088000f000d0a0034503a142822658480c14088842c0704002d00002240300c0c0c2009004001c80c408024209807011504504034081020340011078040071034480c00e86080c000303159400040b50200840380b648500c00c0c03d20381414015204450030940120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 39568350 1106 39567244 39567251
    0x1110a080f01080303190207050105010320010905030615010e06070b09060f0403021203040501140c0d061208070f080c01051f0b0a0e01050d1409010b120d090303050304020103 77
    0x1b54000030001440b10518030b00b507800002070064410141184d03203000008410001e0001d41034210218021894044c0c0c01000011100d03551140200394058003c0c4002c1090301000e100d844907001414149075000345000300204c0c0c10b13900000e0040c1c0e200c450f8401880805501405010740003c080030300060146410344000c1d5440d40c000f00c402d5055040080000c040c05400c3d40b00d220986a0710a202e1428109000a07000300d410420360070b20302c1840d01c1d40c0011064080c00c020f07082d5030341c400320942c00c00030140c50300c3e40908101003007a01c00751010030044442444c28800d080c0315010041420080c00c440c100280c030700314090341000c00c4881040007108840c50b00484510b01c042402d1800b03540c0c90b19107a441c5800707003000c81141042c5803440b07000d004c07140006403c100c24010064544000301041c1c185025954169004030310082402843e007400030030b20600003558401d00605010 = true := by decide +kernel

theorem cover : BRFrame.Cov 39388494 39568350 := by
  have h0 := BRFrame.cov_init 39388494
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39388494 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 39388494 ≤ n) (h2 : n < 39568350) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
