-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2084
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:13.093976+00:00
-- url     : https://prove2.me/submissions/a824b146-b16c-4a4e-a846-8677b08ba96f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 374640287 ≤ n < 374820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 374641537 1250 374640287 374640289
    0x5010b092407050f07080303100e070905131a120a200d0308010e011202101b05010c030c1107080309060c01060801020a0c02090f040c0501050703180e01030203060a0506090115030b 79
    0x2e400106007212181c200d07480d072030841001003080c1e0000d480c0600c040c40c41c0d4144011004d0143e8510310070800e00040c1d44000446d9280100c20034001041d02402d00501d00b1403c4014500800c90440321214503040c159000700b42d4107119840c02030703001c6090000c1c0111803454071880d20794228040d1001407503c012140c0b0543c2d4503159154a200d521a1f262008554102a87c580320a03c05802080c11480c00c1000301025030f40f0040602642000c40c01c2c2090700c10304507540c0908007002214090603d600700030203002d080350f146e40460303030341c0005a4400710501c0002c440140c42d02d01511a0780380a90003401446003601d04480144514a988400024003a035904c4c0f400b0b081e60400d170024800b180100e14050150b01381444981c1c3d010001c00010310181c581907807001e1180c8a1800b81c541080390206403030042500414440e41a00c40c10b4401c1c44140e90b0701c41c4800407000d000d00040b40640200d501040980e00c041c0600740c0038800042c0f0224941c0e0034009070351080001c0c4c0c4162000c06495031440b110b1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 374642787 1250 374641537 374641609
    0x5070e100305040809060d0624081815060f0916090e0c04051c0b190609020a020718020915090f0306011a0d020d050f1f050f040906020405090f070f0305010b09 70
    0x200b070416112030003070141038001808031b4000910032001d1040e403203000004bc54022456030300080d154001d6560503203490000c600999400d04029403c00d40c1d20003031209004521007000700c40c081960b1020102622601d0b002d030303800d0003a10020300700d5005000c148102c1c68182804051020024a00c01c10383c0101d8031a24050001590075030401220403580c2821250f040c0526070160608445c1540340c82c80c0c00000941d10211403042002200074500c81da00c0600183d01180c844500c010204880c5d0885644400340d03a521201c40c551194241204903411811701145d0305d4102d4001101400340d803d503008400460343c0c0510010300d45250300300b05840b158003843c89102c1c05000448005030140c0b9203c0040080c0da024043c4200040c00003407010030142c2d40c0d812485030000c0050b078002c24101c105141550107070185401c42a4051810000c211895185107d154400c4195950391940329000c03440c20340880e0020300a11a500604200b01100d6040285601c82500403949541401a0902001c404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 374644037 1250 374642787 374642819
    0x324020f0703050703031b080f100807140f1903030c03020313230102011b180e010605070b0a06050a030b060d0615030c090c09120f050105070e100305040809060d06 72
    0xb0220380c0204580c014158144106c503c505022450485500c4940c034001e04076040040c04281264440800607094414600303110004190b0541142c040b01d4403002e100504403c4c030787c911400785615201c0540a0301d403003a900a600c0c1218041881705a09544048403408010017041c0d0030761204002501c2c0d802c0c100701c07121000302140c0440d584602d0f040e24490080b0321052200034110380c145255140c90b07071044051803450301781e141800b481806005103a8003201c5c244e83d00c044081001040001010b68108005000ca0380c405c0344480050f0f42c5000c0e01d00c082b5105402030b550444400a4103200080741090003940003130004003400015145961501d0698100c02c0c0303401803051200c0300c1001080b000e4001e403400750000c83c0d070030b12891042c0280182100a10710035640d0701c409284c00c0038107100080c030222501c01e4002000b0300c96450040ca000d4505550484060f00512a06200c0c0914074030911960b070003140d000c11030754a071030303422410401e03190418180703085140d60b50b000c005052007000201807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 374645287 1250 374644037 374644043
    0x20a0b010e07081302090624130e1b190c02030604050f0f010209151b2a04090b0105060306060d0203040b04031e09051e03010c0e0a050a0324020f07 65
    0x203507900c2c0a40004240310b00181c00c10700c402c00340503031800040c0d8500c0c00841e400101a108140300215113510364201c805180a090642e400000c0c0060902d201c0030b200c0c03410303284244104506a1609500340910103241e040c1c1c16400343c2c1c00d000c90a401e00806252000e1110145002c101030f15035500000e00300003066074100c0c0d0545c02400300001540c030902c90710f02d4201c0003038001c50800c04200003085420038582c9165050803400544102030000303524242e60056544800c9035802542100c10b51f0001d120603008030750031110707400307484284e141c140121012143c0c080c0e02a8010b910340001c0c8000d83d00050000d83d4019814440b5a00c21003461003e103104501440d210f65a600f400e05010b0302c030b116042800e245060518000440d900d42285241007150000c0d1207254031001011861840604284403a039455400c1c803d1411146034011680c400240080741d60398000d5a80d40304014007210140300090903000d0030a02010104850103005d2140d040d001c80262070405800b04004c45503105030740071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 374646537 1250 374645287 374645309
    0x32a0d021909050604090803040b041403220e0c223515040f1b14031006080d0c05070e07170906010e0606030406060803030a022101030206040b0a020a0b01 68
    0x2044501554010f007604a44182c4080201503011749441105100060015118500321008a800c0008521141d03070386201d48000e59440b2800c05540842d01e0880f9050315454000b00400072501c02401464180995005110300340f51621881485200101041c03001c0504030b4038000000380d11160f000403280348c3d211000003442e01e68400380800d182d1a8281d105403031582c007116280d07140e000000b034515001604030340c0c0d420080555140c2000392903e080e407106805d842201c0300245454801d25480076801003142035500207118480c1e0002151001e1060b841c8690008402c07a01441c00b48010b030103110301950a40d0300f0280c4400100402c0c520903036654002444c03540503000d195810740a180e030402c401502130640d6500d84500d4210240e40542018030038030300000071400300b0980c0e9005070b004003001800e8075120314101400340e0007500403083c04c00d00f0002a910344070780100345890080c141ea50041819091506005160030f86800160306103003076210350856a404220140c003405c5c000d20034a030710 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 374647787 1250 374646537 374646539
    0x20109080f070f0b0405310f090b130308010b1308030c07080706030e030a0e12011406270c0c100e03071e0b01090203100b0c03030402030606032a0d0219 67
    0x80f510b009142d5500c400c0b40d4020600080c099a0386440300b106d17568101915101f4221281420756211848002e04d40c0740c0c0e42d00c1c0c4806081c5020b4540c20a802c114001c22401105940300f5007841030f074141e5154010b001640d00001400945502400b0f441c048025817a68082240c6850600c2c0c0b075540600d240c018560b10011302000700600c200540f0303001d0002440c7c00d03c20080d01c12000e40e940e005040c0389509000603035401100c40c0e01c503000310703d80ca5803042d0000d10440801140c001186102683c44a018030340244140041301c2030074441440410842001d02c3d5240d0380e003aa850000d4210210000d0079025808a48950f07042c180680c2c1ea0f80e641001c041c1daa08e00242c60108503411540b120514800301b05032040e070103c0d0800034554110307a001a8003513a00e0341c84603000d000700c40a68029500754000031400001ea0b100010295118610903800c45115486075000c040d6610384041214007042c1d1691514461280364041101410502a155a4640c00c480c0e002903240000c01036441d448080000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 374649037 1250 374647787 374647799
    0x4060e040b011a0f0901050702030d090f1509090e010e0f100f05090a020f043222120912060e0c0108070c03050304050304050d080c010e03091804020109080f07 70
    0x2010034014407200c1c850440046840c0400d80c501c0c01080c040b004040000718017620264001c1c0c0456003110340c003c0560f03038200c108000c003603e90b410900800d4441d4010010106091042e440107400314061600c501019900d000350700e0016003100c044100702c0e03540701c420601075034004100c000c0c0784c8011400030f054001d16a9031340008940080003600380d07440c00e02c0f0500222020200300d040c0ca442e010364800400e10403010200d005404051703884d81c00c298a01c02d4281300c00c0400904180311300b10a802003441c4e40c88518140c103c1d40010340b18007030040b140144020009861049c10151460b0504003076810559a02401c00d1000007444141d031001e403200607542f07174aa400d11440a18000909210301a0700305800020540340c19000000c09024000011a0611201b041501d00031300d0f0081101030b029500e4036000c50f258010791540c8003151700741049540d4045010090304c0d070207500039020540c1d83c9451071501004000103801a41031007510140411010000e0082c00c0074510300c0b40041011030f00d462 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 374650287 1250 374649037 374649053
    0x103030807090f0312230705100e03090108130221010c0228060f02281b11010e03060408130602030705030f0c030c0a03022112180a0204060e04 63
    0x10507150070840c5103401402801c00094046040d0b0760450071540e600304900d401614003500e1000b2482d1019044c00c01020b940c040080180480c52103501943c03a041c0704c040c0040203a0311441d450030000d800c24440c41d0019441400009d5100c0014540342da10f0800d590082003828264a000d0b03c404031544401009104003401240f26802d0f01c1d1009000040c0c1c4103290100c500440b1010f486185070260700403080c06541d401541c00942a00c204540e5a101e848910a0050400e034550f0283c0070700680400710907015107500c2120f54458a04034414a4599451124000d110302455042c081003104e4030819032000c0003418402d030310506901e40e0703d443d060f035000c0d284545580202c0c115070040129000094000c010303502680140d104842e2a008000621429402041d1806c1d0f000c4c070036100c90105160b40007400b014203d1000e8600510468500310720b044611440491000030084c440101b049a11903405581e21002114280c5440341c6180d40042c041d50803d40c0641c00d444100001d2000344002c038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 374651537 1250 374650287 374650291
    0x15221d0309030d053402030105071701050d0303020f180f0d110402032d0f0f0c070b0702160815180a06050408130303020102130605090a05090c0c01090b01030308 71
    0x1100250706220310100020f0381d0b41410102c45042000c041408281c0c00404e590034050107091040814244c01e0f00c0000e01d45e80f88082005074440d608100120b28400e0058107071071401c00380c2d40c0c4242a20ba0070700051080394925108110105070703080207020581035a0401a1003049a45007240f40c840a014080141403c4601e6140d44100c6208042c0800100b4501001d048140155009601e03540d464443c400008036031190f00504039405200300d139104100d1075130b403442110905622401a101c41d045502d4401003261030300030880040142101160b014081075a0040051044620184000c0c1c0b40c580c5054141d4408031090740318000030000140b45c07490040d4000c04002501e034809910003080d580c1c030707180c220000c4c04039550741c00410b06100200b402c48081c503150b072118070f400396568034000b8002d43c004455012500c4501e20f0200782d4600c02c00c1215070301040140712890807070401040043c2c14a01400703900a95008110a0240740400e029100049000d80c040c0005507145080c003804100e80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 374652787 1250 374651537 374651591
    0x180b03040507090c0f081e0c07150b0a05040915110a030b030c0108061c060c080601020d0e1e0d050a06240b04030b0628060908030309061522 62
    0x2081c0b1006202030744242e4480d500d545d81d1421028a490314240c52901e01d6400204044040804081090960460005010451084007004213100c61500d0000032585010001caa01c01c03a060800c0107540b0707064100350320f6030740190030800380130b220b05d00304408480007205903459000020401d44000c0760144034810110000303031701070581e0110240000f00411002013100303104141d82c4000c043d07150741041c560320f00d0a902110030002041030750006032080c031044030424010300c9002a0f80400b103205000d4009010405001c4144e5800056080c00b40000084046500461040956000704000300031080a0900401002400c03045400c0264600e030307200004a80c0d00c006984040103016105011602140d400c169050130684035140080c031a07141c804072004648111449a81128640750b80c90350841c3c65a0300c03420041556801856243e00044071079213169004900007840b07294081c00c111030104001400d031407200c282c20112401101408540d0045c01c0d42d280105d652180c402e802110040c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 374654037 1250 374652787 374652791
    0x406090827040c1706040e0f01020a09140418060e1908040f061d010806010512040c0e07020d0509091f091a01030b06031302120d031b080103020a15180b0304050709 72
    0x130070a02e5148403038034013802c29400340380da52034160855801401074084000c00c00d4003d6654501c04c0030024010001230180c1c812079041051030701603d03e00740c070401000c60000d0749200119110342e02c400c40141554109070405020f0150140c004c80007841c143c146540c45810129200c50400001c00303c0005581c11180900c0500b110b140c484071045801c0c0b01c40c8007004d28140a0a98034000100c0d040d01a6100c0d806007858154203100400c030300c02a12006403914002c3d4a20103070345a603403c9942d884203140480100b0020041641c1a06240b0055603203c41400c2044da54910404502500303c440781d8881d460240c0d9a404140c0800008020381101d08824603091020800c00000240c2c144000b81c250b242806214a11900315210403500caa80040c260042d205003050025020b0040c003420394030a14808030403003071070486c01d004458540c1030740d8028184107203460900b140000c01120404980c0d0500c0311010803614602c04401c2e00102801d404050781d9100c0c2098034017a031508130241c020440c024 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 374655287 1250 374654037 374654057
    0x6040308010b0703052701030b03030a0504170c090711060c0426010e03131a03040c03080d09120c120306080d0f05190903021203070302060406090827040c 68
    0xd502950850540e40980745076a6103008914041d5464803c0c19244c0f401c0160440300185444441c582d0034000300401c1e2814001e155050041649910510510310046041808203000c4804a07000000c8681541400c880c030340500e110000f150300302c0880d10301002440740249840d0b82801848200d4010f001d00c0c41701c1e81007605203103100385044801c00405014010106001e00708a00c25006040007080090a41e9621810440000302145490144001c4007581e07114a00c0340700c1000c0200c2c4d1160780c100c4880210141503688a88180e44103110426107640ca17014841d01003904036106103c1654152201203581e0b4003850441c840041c0e107076900042c545000410001c800c000700e8080994580c5241551961442580a50302c500402001c000c5054050340764691898000b0044800d403070086800c141d056400c044455038920030448000c0042c1c20000110340050610380092106d503100381c0b003490030201403114031503079003254a0071031000da142900024840c0c2094860554000a40c0c0b070205800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 374656537 1250 374655287 374655293
    0xd050703020d05032509080f030309101104170102040e06090907031712010b0a110a03171503030304030e01031802031f060e0c090406050108072f070e10080604 70
    0x40200c2c120307007000d201c400000a2492102c0c0500e2408a0301c0840c07944007070855006004201c801e240c02000418070886000c070ba00f8200c0003080da4850441c0000504004204e400042d002d400b00c51403a5183c204203000c080789100e0340712804040c940d503407000103885c0ea00e40b1414030b9010a000d002d8074054980c3d201405112030020076aa400c0c0c03504003a0b40609a8100d603440001441000300070348201c8184000440e50b8214500200f50240c1c040da40c0c00c0780041080030158880b144040001d0100b80b03550200c4000009458100394007004884401107104400404a81160300840b401c030700240170745101d01e11035a00b51054012102020402c0e4031010040c0e408659201c0381d600609081c036540464580358440b0540211015202d02030601003075040104600c41c658200b038a6292145040c40c1001c1001d502c1220f40300e00c075005554492040c085c0b40b940304c160034468807543d51240e0465281c5410004002c102e0a4010405800329151300d250241c4202703520100394010480b01c3c2c200c0c000f40008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 374657787 1250 374656537 374656543
    0x20a030f0b0f09062b06060501110a031202070f06050907091506050306060904020a08160311250b0c1209121c090b0408070203100606050414040906090b010302030d05070302 76
    0x82d070600792400d1000351900130004070240d9499942e2001290703000d4040410344411120240c1841c400c40050250988a10064070051090b0304104078540c0040d12440201b4800c407905643c04004880062070b1030080d8440b00909080c1000542d0840c1d110302c14480010010000b40b802003680171410401504e5001840303001c01c816110b11030400a001c800b0980c20755454048660001004100315940c0101e85400b84c020001201c202060380c10f03102c41400e0950081c050840000b40c40c43c80c061421228058080010100c45c540518070980c1c4500e03217000131007010141e8090440302048588401d00143c60301c1110000030510b4003680c0041e9851020411a4402c3d111200c1c041a0340348010000c00c217914008104191f00580810b848038140404e01507041c00800c103140c001d80c1602c11b40e80210311498282d950a12a920029208200820032400c02000700d4954410090000c07608180b55207444040e20030422094400b1090708004100b14901044000c030143d0017030034450304151460b207000c0c4d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 374659037 1250 374657787 374657809
    0x2070b0a030b0f130506030d02031908070c170301050f040605060703032409021e070c060806010201020d0f0501141c0204050a0605030d030b0a080a0c1203020c13020a030f0b 76
    0x24162100340c2d20341c1c0755503003000140101074040c00701c41d0004d000910000113054199451030080c010b0641c0305c07103000d1006c41214020102c2c500c8240c0082c0100c0d4080b911203000a00100c100044047d0030400245201c04000e0041401c08015031a9410002007140c590300c443c600038400ca19042d0100f150713848007030a5900060b010b007800101f05400140d102183d03c2e50941488610581c03103000b0412000380d43c06401600c030256841224840c140c54030b40700303d1041080141180c120100b08000051048038001d602410600c00541000e0a65602d00c0641314410012003000c3d8a80c001840b00c69031012007010901c00803030b401c200c0524492664081e102000c00003a0080d0b03103800004040c00c026810030b82c01403030040c04864080c01100790080c001c005141d6000c0c030911007c180098041c50004948080c982c1120302594101c1c5030031450000e41207070742401c90542c0038401176a00709a0725002c1401c50748641d1000540d960b65100c00c01000c640381c01030314007030484c50550707003166641320004801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 374660287 1250 374659037 374659057
    0x306040f23010b0909040605070903020a030803100b07021f0e030a0f05100507051209030f04030501021b0f191103060106050706051f270f020c010e191b080304030c140102070b 77
    0x10b0149c80d0b0a80031200030940c0e0b00080c0d00506803c0e0000100020080158858900b144058040c82e0302d90400b060301d0b01c039102e4003039400031041d689400c041c2036a400c6121030544905041c4480303034490000ca41400c4024030140c8010004403005c0050200070f114416464800d10320401031460304484c003030003600901c02c0c2441082140030020300c20001c01c00c11104044407082e100c0d40c5455491404c18041d40c88429081d081c01d80068111200050005036048600807100c040c2c0a1a100c090400c2409080e010b4240c42d2802e0328494010310b81c80034051a40600070f69070303c0a6840003a4240b20050b40c00103001403170041d00c0c440d28005e081040000701c80544841d2900f900403d07050f54a180c401a00c5000750f4030340c103172626050800b4002c10b54024a441c018120081c4160464030040e5601c0315070101c255240d400c06001030200003000c003540c4001941d0640b040a10300c98403100c00e107103035070040d800032075146000f02000d100c51043d840e216100c03100244000c003a21030038460a440325010300c40c014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 374661537 1250 374660287 374660291
    0x903030103141504061b0e010f051809040b0f13020102120c030c0f010501170c1e0d0f0302030921070e1b0c070f060f050405060306040f23010b09090406 67
    0x1120750194140800340f4503005a00c901041400c040c2845030080c082c03840383d5880c1c09903e0354040050390140d000a080d000058407480d00304414400281c4065120222191140c581524804425503401c01e070540120300900d03c1070410728241c10058005540074100c520f80c09400c05a2900503a40002c803594151f070026100707030319800c1001d6103a00d14003e51240d1b0000e8050b41d18600b012000540c0014125007840d0002e44454105e00035050300e42c950310280e1074004000d03180c16502031000001320240c031500034124012b4103481d9101c10442110310138040f0f00581000542444a02e05500f8403c0e400c05003141c164543d48580c403585a40303001c2441074200e00b400901c000b50107807440a00721f540c0d41014000c4195211404800151104800e00a0346200004003c010540511a1a1100035a2000e40701e00380342c80d0030703c000c000d000d400080c94690b000d601d860b0380c50790005da140600d00d141114421100d590030300381e000343c2c6025081600484a8400113221040c4180d0f542d888681c0c0041e00040c1c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 374662787 1250 374661537 374661563
    0x20030103110409050f0f060106030213120f0510140c030c0306360a0f0203060a030602070503190507110915090414030307020622030c0602090d0c080120030903030103 73
    0x220b8050142d1103c0540720780255a101c0c445080080317a000110060501a83d11580c0c0b50403042d0100e0243c0103e0036118108400d0a211500c00e0291010300070380074100c6104920100c0c2d03200751802810300c4000c24540d440e103004864031000c000c1e941e504500d00c92005030551910141141c07950000034a40391244d9a5882c209d0101407001600ca90501340211f03841c02c5a400100319a000041c0680d41188001d00d031010034141505c0d0351096038000d000c001c0041e60074920310b44801019401a1400390360a00040010940d00c01d020a070300480708a1036150180c445090b4200162484041501c80380151044010811449651051b0803102e00080b44e08030560340b10750408034000690000841c540d440008240303ca01600002c249201d01c01d0858000201588010706004503100c4440c0180400d001d941e03408000b03080c81e0040d144201d00070f0030270712000c0129214280010030507409043c859544800500c0340ca800c40400304130000081020078598181420019568401444003501103448800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 374664037 1250 374662787 374662789
    0xf030a08130f060f020a0e0405090703170c06070309110409080901030e01110301080a050d0c02030c010c151a120102130306020708040b0c031201060c031218170d2003010311 76
    0x30070b01074195002001042207420743ca10f40c0009510814a1070041b134041c06510009180502032503100d82007181c05003645920710354507070b08010011180000c08603418071079034401c5441007240f10b00c15101982c0c00704540c511410b00b00300441040325950700650400c1b40c4080402c0da0501100c80c1d6a0007841c0010741405860b50352030051110b018505c444c5100040001440340300014011429030041d0709641c080340c0c00760703000d0300ea4100c1c414009405800241202c102907008001c40d0702c026014022090b40003010303154110484e03843c460f8a034119015240c0c1c0c40c010f424030810260b44007040400031407610401031503865580c800303440014900c1d0380003c2c1c40010004a842034800401034109555102e00032101000d80700e400c400801d60018500d03a0000484a202e202e4180c516074154030340c0360800c2e83c155040c1c4007a088803030341e20b04071501045041001440b2084803001c800003c1040701c2d210442d40f49803905451540f01c10042407098815100e03411040790084074112a07001441c04001070a0074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 374665287 1250 374664037 374664053
    0x120102031b0901260703050919020d02010512040b01031407080c040f0221150402040b090112110a02010e0c090402060a030e240f0601030e070e060f03010e0f0f030a0813 74
    0x1000c10314522200d00b49810041c0f41040d007845c024005502e06004980d01d40310056580c22214581c038105046460754080503040c0014092034280c01803400c02d240800d1401d8401c81103205840c11100e03103e282004009100d10710840350545200000076044440c9418100c80c1e903595510342042c4140d07900c3c00d41c00e518015590485154942941415240c290144264054100101c903680c18a007080404615145040e208a9080d56000c0203010300b404108001110603003112040c4000ca0f07507440c104250310780003100c00f07058100c1c0c00740e00200748507189515082c20101c09040e52801400c1c007805100050b0755810582c1c02205551500052400e14201345600d001c1e070700008506048404003940620320b500a903524816201e29400c00450f45032000114125282c05903409000d81107040700344105003040d00c4c2503400841c0100704035440d009280c0000c1c02c46088000c5010590b2102c03008495000703051101580c0d20320404060760030016001800b030300240000303120307030700400524200404000c242 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 374666537 1250 374665287 374665307
    0x16060f1404030501110403050c01090b0703080604090804080102130510210b091006081b0d1508060f010302100e15030601021006030c140d0c0302010804150c02010605120102031b0901 80
    0xf040c000d01602540b0100b0b8074456001d0301080d2243c0c00f814021500a50260780c1c014100d4001e18062032908229480440e058080034001586c450344070b19003140454034810280000e00a00d100069aa8481800040703101c0c410360701c158020441c49411015007900090a020f00d8032081c10b2000c1400b1203030040c3c1005000f82c0d59031079030007000003051058124074050480203440b41a15068460346034400580d000d141d902e001504210f50030400402286180c0d00104600c07407481100555040c0c8580320396003428000c4846018601400004105614007041403403030140d05801c2c04c004603034000c00400c148185c1c0c01008502410000041034441c3d00c00c001912003031011800c00c0154035102e00c0c0003403034514030713201d008184150452028618542650f0a4800940c4813030708603d0030386182c1c01074a8042c1d00030310075601042c0d1040348044100340e50203402400b8031326500001d59a4241005c1000340e0440800c04501c40c0e10600400481c10b030811284101c0e44980b003c02500c071101000121003400c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 374667787 1250 374666537 374666543
    0x1804030804080c15060a080c0f1306081b04060506120a020304031103070302060103150c21060b03150108070c020102060609041103370b1b04030204020a050c16060f140403 75
    0xd01e03400c41204080f8513000e501440080b160010615643c110040d924010351190540c0008d10307140394285490442c000d410883c04480003c50800c0e44c0300c054a003004201032511158401c070214403105441d19120b0071018013001c0341c0841c24201083c00035410068004d002001d902d60020105d424140240041a4070040341012039035510640e103002901c8074820b1208548202c490016020140c4d054000c03004581c1d0203565841c84018200215100c1c14100100030507001e58403400441c2c0001640c0c003e510400040803640144400000010b0600000a00e00c0c0200084c0e41040c00044c1c3c2d0214070160400000c450346d01d91901d840c01e1050115041c01e00d10703941031040d05200e0318011884407481c5504840381c86610342c89205070002a101d1607040b280207205c1c00e10000000c09002151840c5c805020040868070b00385500d80d030219040781e0080080c400403a1012030034809240c410040032452520640c10b10300750500c1d0100140664040c8000c20041c0701800c1c40925601d05948266002190 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 374669037 1250 374667787 374667793
    0x906020705010c0905100509060d02040902040602030703170c030c072d0605181f0609090b0f18100e100c030509060907180207052a0406051804030804080c 68
    0x4001e01d0002e008141034051a00407074444140004c0b145807000111584416a450700d030300e006100010481e05521480c6c012603480d40c24800030070780300c05034409400a000c0301c0c1c00440c1c2c2d92116080103042d500e01100b00d101e507018a0030801030100c01410036681c1207510200103a4451804d843d1010170000380b60000201203100015403e101d445180c401d14405008100400039a00c1384050980ca452107040c001040e6400701e807a080340c88440c041c80740800c035010800000c4541d1281c502005a94103a00140d4a000d000d4003801040c0c0c01c6105010f8114170072242030300300140c0c90307400c1545800e24080d060b4156503541782c0140c200501408251101e091816003000020746055005d8010a02900ca00000740300e9440040c0100100041000c00d03145400d000b840e01100844004000e940b00ba90100c466004441b6103c0003e41d444401c100c80d00d02082d01e1040f106000d00c14007040722066407010780301d004121400814200d4408010382c0041d0986840087c82e911070601e00980c0c4100701c6d03a185a84 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 374670287 1250 374669037 374669047
    0x1203120507081009050c0703300c0f0e032a21150708040b040c0e07030501080c0114070f020f0d0f050c0621100b0a0306170f0a0312090602 61
    0x40e4040486441510241c907000b15203034071013224038100e8000700c91202d92030b40d0800c001804a0300030320032096013410860210704000c06c0c2c2c10b208080011001c151039400c039110b62005040e2600700d0301241c04030301c0070300e09060f00345c0e20341c4002940d8104151240700500d4046c886098080010303c07142e04000c502800d1810104981d6101d92045004524141c000f4081d44840620038200400110301030007940e51440c400f034880c1d07256001079003030180c000c9a504290344400a4076071541d84415204400030380300000c00f585080403540c1044142c030100d07410000d0422030303004484080c0701940e11484d0446110140c988851000c251040d540034070440d071085142c82850308210814031402c010303c3c4102c00355252100044248413840c01a0a19540c0c040e078419801c82113011171003e042e501c10000052000f480d035540808030f407281e02002c801000a40c8400702440080c0b0458041d8074086400001848141c5042131700d1610340881d03900013010003920003144164425190490a04c541d08404210f40e24 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 374671537 1250 374670287 374670301
    0xb0a0303050d1a2d091e01060f09060518030f061614030115030906051305070b03010e070507060e1c080603060106021002090a0306110a140408030412031205 69
    0x6a0000d8101c9180715050800d840f83c000416100c00003004800350425a040382c41d4582002811501e003012030360b1056601048100760b4a1485440c0109800340741400c800c15141e0440c480c60710160400b60034020350000b20703181e03258045103040c1110403520b002600c40c4902d204c84060840f000901e95418810400440743d00d8401003480d83c0110100700c1a8090214440819601007034024102c80e101c10050004100c010412120315130b62074458540050400e1007503903031070102c6406880880000c8a880429800c1010030413001c00508a43c0a04600307561500301e000300f01001c0101360100304680803d550040140310f030411080c408801041d0b0f21550660510300c403040400c180d49200040765180407035218103000c1001030582d6002d034041c1510b44408514040a94440d400e80ca4000710392100010111745c0c2ca00c1540ea02e01c0541c00129500c0b01c01e544010440400300042840d401030400041107030050000c1101d0440d40c540800051a101d04c0c10309076800000c00c1034403014141084100708c84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 374672787 1250 374671537 374671547
    0x5180d0b090f1b04020a03141807051c14030f04030b0a0605041a2809050601020c01090e011a0403081207030f14040803090f03070803270a12030b0a0303 67
    0xc01c641c060102c845140c2e080b40c405a994111180d2803006400c81507980c16181440d0f0001c201511040c01c2c04518031181c0360304032250010444402c00d070a55913050040d600d407810f20640f0010b200440e24000004c1003603071294800c1e020b140000b03001812646140050902c01d10607038581e00c0d0000035135512075540b4280300825030000c40d00c500203140f400a002c00c81d85060f2180c0541110461040b4012a00c0c500030b10400403120780701032289800e02d90050054204500720407014020340340c1d0202e540d0816000191030a5003c01006050003603c55083c056200d0600c0c00303a04503020358070080c901c3e8080c0c02000d2901d200c0da810183c00107e0005004408031401c1d0144c81c000c04580c0d03400c000940329001c44204855440340007030f96444000303011a020900c0100555084012501950100c1000000345480c640c0710340d90031580b504000c8100b014040c4030b20000c128910050201c2041456807800460300c13040c60703980c000d100c0032000003030182c424426030180703900c9080a88459082601d80c10045c00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 374674037 1250 374672787 374672791
    0x1060b03040b010e061f0f020f160f0f0803030403120209100c02100224060a0e0415060b16060e0c0a0f0302040525050d020c060c040305010b100203090105180d0b 71
    0x10f020b0590008170f07402d41001049400f044243d41055000e608034200f01301c0f00c0c0c915030200c3c40118400c1e40002001e01e00248900c609250b148000d0b040a81c7ca00310103c2c4c0034410310750280d01e0707010700000304008a2401004490340303d985440d1120034201560004e400034000d0102050300aa0140c0c900a05150400204003000340212064a8920043c0034101da41d00d0404241100c6d10068075091048520074823291500050000c0c0403034500c4d500c42c02c00003c5501c0441d030907110400c0e41c500d214509802441100b01038070740750820600e805004030b0400751440380010001c08050ba07034140308a48820600c1030785642d8200504098407140d4410621039a0007042c002a48540e2503c00458801020b40c562011064503076101c075a070f458100c61080d921034000c081800080c0d9000c00c190040340f0350a0018521464038407481c07544490540c1821802c40e502421418003400610042c0c0c0c0500d90004143c0c6c07004034003440d0665a44c00d00d48034011404040708002234000076000a40f108201a00c54558 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 374675287 1250 374674037 374674049
    0x418020405031b0307170307060504050c0a0909031d0d060c0f020d020a0c050603060d052d01050708040b0c0c100e0c090f01050d1e0c03110109180207030201060b03040b01 75
    0x39496080241038098803070b1004030001e130706a00c01c0b0810089001400301c1c2c0d0407003034045002c1d01c0c2454411340b540344c241d4a046400b01c41940010f0080c003910700d00304a0303160181074040c40c20840410185d83c0502070001401402c0722184001410803602e0340c41450700001c4903485401882692071501c070280c41a80c20000080c094020f100b120b80d9081c0c8006808010745070000700071100e2074a41400d1041a502c054400313604401d201081e8800f14008000c0210450007501210181c4001c0740c6101034641601003a0700070303d03410701051200680d884240681c00030f0300501c4010880e11010b001803039501c00c0e80005480c6004003400c507030880b01143c0c01070301200d00807415920400e41050800c1410f603001c5400ca40c00404590062040e810a8040e40c801540318160b1540d200710781051b00b40b40c0340c00e41e4900701d5040c13006c10400d104100f03041452405410082c20a0b5070706c6418040380b0400a4040c2140d4040154003080392406c0c5403003500840014400151400e0b81c1e0b0502e0b0605c030100c071000b400740c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 374676537 1250 374675287 374675293
    0x9020d0f0213020c0c040c0315060809160e0f0703021c0f06080a020907080a020d1406030709020f1b0c04140108060c07020f0f150a1106010b070f080f041802040503 72
    0xb003601c4485000b29251021440003800340a071050080200810589030610201962458054800d201c4c0f050b804018000030344a9034110319208071824034025000780001d030380c1a400c4808024481d81559955005284640d02d20880e54502038228001e0140d085510f00c000c1c61860094010031b030310f5020b40000c4d2100d81013480700e00d03118402c0a54032010701ca0000c1d045076a040028016030b1080c8000740d0041505000540b5040481c0030710010381d52212101c1000581110078420185010040800200b400003400c1d802d0404c011070904440c01151007000b4000004421000104002c1c04500c1c6141001081041900400844002c0c4940309001d80c040741e100743c002040c07058031983c0540c2d004a80c020300c0320988001e00003d1004c40d916810105030401074102c8084049a841c101401e0a0350746682c5503001ca030b00d091000c1d403510b0300c1a405000350f04402c12400f0041b4554422100f01d80340c00c2002d00c0ea4414140ca12014a40304580c406c17003c1d0101d644004505054680042084440c100c0c22 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 374677787 1250 374676537 374676559
    0x131505150118030302060c18040f020307120c020601050d0f0b0c03041b050a05150c060702060901150b03270609100c320702282108090409020d0f02 65
    0x120b09141c2c902d03400042d0260b800803001600a080d50030080c0010004200c04030300601201c8080742c15a100c1c0f02403105001d40100c00c11500c1640b080001112900a14003400807445c0d0500203501c9080c18002c1500550600390310760305006c08840e444810a60040c4856614070340301c071006156406c1610110340c402006590562050710803c61001a07440041c10b5001240c0350100300454184050180c408001007130100d00002c0300e05016207403103441030340c018041a251443c000c40c01c59440d121498888030410005102c890382800c00c1c0ca6102190b002c0d19103d4900d100c040c00340450083d54144400d11a5004000c40d605003c50345642c035a0903a4030910249411281c00d5401e1450714000c0c0140d6181c02c6584800c0640c00004401a554019000d07460f150407a00441ca480205010381454029690741c03000c130206076000420000c120054400e126071079042c0003088030684008026091600c0403a214005581356403003000c01c56402001c1c180010724515103415501883c0c3d40a078490721030303500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 374679037 1250 374677787 374677817
    0x20d08180a0f0602061303020607030c1b060515032a030a0209101e0605161b14030d0905091501020c0a0e190b010c0609080405060403080403050708151315051501 71
    0x722048986d540758001e801a66502401200100b80c888100c500700541c04c480000034035201e4285004903401031b40c2c00310b460319041f07042901d0010b4508400f170003980804001207011a00e04a08841c0844001c034a20071041c3d40400249803040e09800030303520a40e200180103142820500c0d11080303c1c0d81403190420300d00000b0340140300503168030031800400d0301005140b184141544640411912035905e546045801406101d500001c43d00003040400b1500760880c6a4901004101c00040c1180361003c03019040501090040c078000e020403507100b030203402c20506a8001d0100301c4102001400c00c0a1031592408081d022443c00c0e60011100004070b9440e4400e5200e40c054042c5510341a101d4201459a0b99150001040803460035209604180008107031540c41c00d000340000c600400b0f05686450440c07c05500b0301100354040f90301580416040000e0003d0350980340e41c00424002c1c1201c00b425141841030030310020114540c2128604010030100700701c180300ca42043d04003a65503245041c8421 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 374680287 1250 374679037 374679061
    0x6110102090a0506070203011b090501020714030c090a0608030313110102070e0720100c02060c03241309060e0f2b090f09050403080a0207020d08180a0f060206 70
    0x62400e0b4001c02c1112050209050000050482d41c1c400b5000103504050821811000000402c65200180500c1001c1200d50303410048040644141413800702c4407031412001070313990b105450000d8007641c620000103204035000c0e84220000d004010540c0d681b89440c1b0b91100081c001003404880392880d241f01e0348225480010300c2000c4d01c99204c0c250080b6101c5450a0302c4140d503644001d0f9900b04240702c250a0100e05021071003000c00310003800304041098582c064240f11004010202640c414001c004202181a451143c10a01c2c240e60a400c1c51049001c0344603044070b85070500c1564141001d5000b000b07683d0f070008074010000c40541e000d01080351081c61700c0700ca900c110b04115514150f03404080d030b80b4183c100c500c03c00c1c1d281030809803907039030300f4140b10000c00562100403030540e80c0c0200014150000b00751544294107410861404440d43d00242e50040c50680c081c264440c0403528164140041c000000408402448154030320303038440c45000c08a1084c0030308801030250402140c03100e4218 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 374681537 1250 374680287 374680297
    0x7051b0609060106140c070e0103020312270a03050a0b040b060103020a05030a1d0d030c09050603060607060911060d0204030512120a1503080d1a310207080406080106110102 76
    0x5000a040b107a4079140045400d803280c0c8594648003507041180041808080101100811140101440301d40c0345004040c2001d14019010103a00410000724240c0d01c0480d00d005035584030890050b41c4c01d05100c003c112a181c2541006109200d5051014140304942d4082c034801c5114200e0580740780c0e46d0100450076805002c00d00004203070240049070014209401420f840c8009044002500d400c01c0d40c49450290b42004200209548180254407142d20509500252400303984692840c102a0049003030780c800c2c240e028102941c1c031032903401080034051550044000080c12140c5498008920030000d41c4035100c1122548101c0101d082152104401c3e0387e4601324280c200c503202e40d56000c00c04090802501080c0005554940c080002459600a001e02d0035017010300007141c07554400c2818141a20040c07a61158051090079580060041a00a274500b0313031210240d01c480800000d64003a020b1040014003240022030302240080d880400c1604890090307071458071051a205a0508038424 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 374682787 1250 374681537 374681551
    0x31b030c120a050a0c020d1211060a0b010504290a0f080615030f0406020715051509090d0f03021c0b030721140a060f0b0a0f0b03060d020d060507051b06 67
    0x1042c041e00001c0d5002d001c105012a00107031404191f00c800da510580b03e070286041c060081582202d0309d01140c5802c000156022132803050812940c0b94000c000382c5280902c1c4140d101000301c3c03285200d550056425200715001a000c0f00a072610101a0091b201c100c82404800001c1e10910000b0717800c2c540b1480340c0c181c50540b4060315145441e540b2510160400041080c1c030840d400700305c0000049c140d842e915403032004040000850b4100800d0504070f240c81d60b020315105240d25002e12019074008100030801d21094100100e100300c500c0400e0f03000e80220302480018050340b400515001d04190080e0700d900108806a41100341c07904851841d48502100505016100c10300c4003000901a0110341000b900d008211440d1502da540d451080d00c01003184900c8050310303800f08a03024107102480c80068001c00c09096601400c01030150310310300006080791f00ca81c01c540c03000760554585000440c0c6044d00301006000615205001401e1036000900c2d00d100d0300c42c40001c0d00c03090840404c8440c000c2c22 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 374684037 1250 374682787 374682797
    0x80910050909130305042d06110d110c060706020c0114070e0103021c020313020406050f0d12051209011e110706050a06090e101b0f0f02031b030c120a 66
    0x103c4020b000d05210b4048000c8082c0042040301045c1e12200c0c0d42c01e0080704681218040307803100d020800741c00c10b070f04642c044010b01130b10407042e00b41c5880102d405100b601e1545401c0c403a415514040c0d51410a590742444d8200c1000511401801840d070001e020306202880280b14260038003000c2114140e049600c4070000300c035030702d5107907140d80320b81c000b030500400c000c10340081c810103c000941203030f209070303459102c8481a08130308045050074000d01c4000c08044804403610b80080000c246c012420000003803c105112024040b280c0c0a00241c03840400e540c1010480303450000002402001925205501e1030401e40031302101074154081c40090728420006070381400314650700c1e02c01501d00505800c6a1640320318003c248050306100742640c40000200908584101c02c085504844500d0121110300307604005641e15507400158009504601d03140210041d00800d400b01e0440c00742ca1404a45200c140e00c4402da110320000281004104840c04e81d01c01c02054110300c26680700740403010340460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 374685287 1250 374684037 374684041
    0x61003080a1e020a0302010c0f050405060c070801051801060b040501050a11070504020d0c090f05210f030307080118140604110d0c0206100b09060301050409020409020a03080910050909 81
    0x504000c05481c0003041030030110245405000d91040c004403586061006910880d00070081c560309010b105443c0354a0704021800c1d4003501c1009026115030300400b80180400a4401100442080540020712034200200034034202000b80f03007507260a107001a1101d45c202341010441c0310f6040110b4040382c80507120709140c0700d448181516030030506540040705001d00040003801c0c0c2c0352800201851007070110001013208840c00054194001d80d0444421810000c0c0148200e46940c125042046442c07104012851b4204004074603004403500307070391028000171080c40042904500c0403410f0300c002c104a10b89800c141a03481c0102c514144d91503090303c1d02c0320041a0300b410075a00400b01e440407003110714507088500f81e140007034500702070b4650b005920001c02c02c200366040c01800c00c003808590798180d2030002a040062028001801980c0c400c580d05c00e682c0b003c665403070b40011180b660103481a8042a62400c03c9003072500001045401a210810b084031032078890001c582010000405040442e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 374686537 1250 374685287 374685293
    0x2f0c06060103091103070801020c150112031b080f0415022d071a09100903050304090b0a030506070c02030c0a061d010315080105090d2a051c0503060909061003 70
    0x14103401d00003529142c4c10b641e091000d5440c10701c10712014110002c00540d55121800b41c4910300140802c0c02c403400b41c0381c41c0061091441c008013101d80b0f40e4062402030542021281c80749045494401e0040840c1d2000590907890401c83c0d000c0d004803034140480d1040200c101d18180d072114000007170075019044010003569084c00d00b10b50000050111030459400c642c0300ca40d19440d40a4a2100b00c80380100440c03503d455190801841c0700355000b91800e40b804d6803955440d150b8034045d84c01103811080d03c80208048540f035068802c001180c2000c06c8610506004c003000c2e10310001264264040d0145c00740c81811401e1100b1810211001503807105940c1c8001c08180c82d824258044080c1010340b1000701c0342c940c1801a41990240092000005041c1810340c07240745000c0c03203c100c200078001044113107103004840241d054812024440c49082245042c80d02e40c1c00c2c20212080b040f80d01c1440074444108517400b102451050005079014a103640341c02c1c20865a4000883c0e50348400000c0086c14800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 374687787 1250 374686537 374686541
    0xc05030618041104020a030603020306060f150c120a080a060512030403020108040f020603162d05070311030408010209010e03030403021c05030702030a0f05100c09090e102f0c06060103 81
    0x2002d802442c90000f0a4440c01c00541664040f1000b280001e4441c00140300f54a800d000494010000f110804001204030300452078a040860b0f03480244074021450b02040d4000b4805c1c0c0d4904080415260b603548162100645001000e45000848501e40f400c040742e1414100c07002022403958000540c02c281c9198011243c003040200211600002e4442d883c0068480700c0180d4080c105400d000042031105000044c2140090302c104039003d4a140401ca10111924000d050342c401180351141d510011800c0070749513a404045070030136500c40040c002038040c00650182c403035044240c2c1c41e105050003a60400d5682d02803400007035400724845284480b03001d80141044d21181c0300e00140c1c1c4c14a000b030780011382072010790402610050a0b8400e00c900300001403100c040142e5041c170301002110201440200541c08500524001e0303030755003159000b9200100f00200300036072640701c18440d4041d80c14a0380070304007481c204480f40880031540309551800400580d000c24202d039009001590382c000c01140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 374689037 1250 374687787 374687791
    0x4081507271d0402222c1902060405040c110a030e040608012003041e05101b20030c03030c0919060206150a090c08150a080a0b04030306050d0c06030c05030618 70
    0x80700a90f168046401844101204030300c41042070054039800840003080381c2011040c81f20040e00440d2080c0000050b035841d01030310292401640c0001c0c244081030000d1300c94415240716004d4610440603844201507002d440e4924034001914144803060755616010f080e20550140301c060349030721486100b904600304001d154414001d4050388162071500c2c4241c079511464180940b41074006205403001c941c00ca0041c8000c1c2d000d08189581071440400c0c00a0800300c101c040340302507804507840049824400c0040e20300b0010102c05880d079030b0404200f03554081e4002c508003401401e4080c041c00d0001d0007042410210f030101e4000e8109961003211a41e10403e1410b41c0c503910801ca500d0200ea42e44103440380450802041e102d6810324100003800c0b10200380c521284900c20510301c40305025501010492400441c0e00c0110302c030720f94840c1d260a8010b0401e5800564021754030100d41d00a0000309154041154007a0b182008190401d1804032013620007107900c5500b290404d005812400b2407034456075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 374690287 1250 374689037 374689099
    0xf06050c09180604050f041101030518150f07140301060503040507090204080a0b01080f0a03030e21070b07020d080c09040906050109020d0501090204081507271d0402 73
    0x303142464041c000707582da000c040c210420184222003007020700d041502c201c68108002c0e848944880c5481c1d0b40e800e40081142401a04160b220400301d0150b15a1040e007110314104001075a42001c101030001a54410840e01d2183c072000c0c00001c10a100d0180c001f984285800142d0b01b440e503030820b00b080d03c0552019004950a100380f00d0005841c081038070103040904070340400360450a98500b0f20300c0302800180c12500781c0742c201e6440c1441040000500590040d4113007000b15162401c42d0f4840c3c1040101c030180040c20701c0c0900041d0049804034010182640320300c01030400c50310780d4501280d0340c10500032980041086100815540d04d51840035018529000b403010034005515902d03081554000c0c0e0200c0d4205401250600280425010b028013401901c0350440c10701c0e1802c1c803455982c42c0c040407203140308284080401e0655110303d01d200c088111b15041c00d00e5100e25151044d202c590030344502c40b14000944100c1499540304031300c190085070010001d0404d400c010303c0118050032020520 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 374691537 1250 374690287 374690311
    0x9020a05120f1e2e0f0c110c100e0112020c030910030b0a060e041d0115080a02032e05040803040b01330207050405010308070b09030301030f1112060a0902120a0f0605 73
    0x808203444503028459100c0d41410022a07075a02e40f8001500740b400c00300c0c241d8590340000d2050402d580307800270303441020340785407500c000f080800b81c0040c0c0e8400d0304d10140d80e64490000486112102000000f040114020780740c05401001c040c1046040b5002d014141c1d6020030b14544c100911480740880400e00040100b0020300c040c040181c0310609000007109040c0c6035102c2540d48a0745141c511600010102c45018144e4111740390f001a480714000c03102d407152202003003000c0d440350124079100304180d4a2040304011034205420118034541046130121181c8140f98004100c008507280415400c06240300c40c4000c9004c4540040d50290146c0b442600310320440710000b8050340c660007044d00841c040c0b90402d5580c0c40600700002d80050040a01c0030701d900400c01080010171a440800003603800010751140c014100c00050070040f0341d101840000d20034001840300035019036200d0368040e03200304e80b21116040503828003a00d03609000005840f650340032034290007042140e04040e9220555901e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 374692787 1250 374691537 374691613
    0x40303021606061511060610020f0a030302220305030724090308060a0602010c200309060a051809011802090301141015140d09020a05120f1e 62
    0x280003440c51034904180d5490f40c40f141d00308501c0340c16a00d050308924103072800300814101d4001c5240c0e15500600a03074002c440758444000142d1082c001015801c00c0880ac1d20410029410001c002e500710442c1d51403081c0001d1007600080400317225410072264020b014509000098960030400c1a00040c1001b04201038001b9200320880d42c4510400c06100e0348460315207003010002e00c0b000c401d803030700898156850060030404c10794102c1d5601c2c03460103012200c1052500b030551068154090f20560351b03049040816501d40d519008006010048500c001c5080e80700d4021b001c01110303440a125202c002c420507140c0c00c4102c3e80d950010301c500c036009030012a80d51443d84c81031507036000444900c8100803c541041c0181c0e1400c0e4110140303c0907034542a4000c50007001c0806240c441d040701e80c01740726520275441c021034603540041001060000c4c00b41500e00740c40e00189444a49080001c03e4034081d410000c64403017084071500f450a102d440040a051007003055076510714040c3c44941d0f440e0816040d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 374694037 1250 374692787 374692807
    0x603130804061112040e060603100f090506030145140c120604030f0507060b150d0b03030426030c010903020d0e0f180c0d060b0301080706052104030302 67
    0xc028002802a596012410100c5940e079034149209041c2c420402c000410040005d5412500f2413a0001c60071034078a9901d13203d04121042041b800e40c00300a9031107000100040301a61640100d200e01001d0300288100340e08024030f042107010001e01002140741d0248080d5100c98400c9030840d0740d180800c0b404807a2242c44d114119855041d002c00d1030380c0e9200040d88072007402c009104c00d480000d036400516050500d0790b000340040e035804100310b04005c40426003506100030f42c0c02c0011011005850380d40c00111102c00300e0080d501c030107068030b0080d080a1442c84d95041c0002101c0c201d0301801c41d41615419001e20490781203283c0c05503004584800e000a85540500b880381c0b2030842c0c42038005011941e51803d02828140e20744840e180302d43c001b40c040000f1134403504005168010a4148650b0315030b11b0311789000d542c3c020004800d203ea0301e045004a110b401440040d03058075825802c5444041da40c0b242165039106200003805203144800c048402d900e121b016a0750014400d0a0160400044030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 374695287 1250 374694037 374694053
    0x1909060203090303010603060b0403120806010c02040e0706090602030c0601150203120a0b040501091e050406110d06030b0901091211071223010b0109050f060d0207051b01020d0c02060313 82
    0x92011503283e00004010880d281e013500c1007000402000c50000c0c2494a0354844087c02101c01c00b0f036800780b00301140040e00c1d40c0e1282e00b500101070782c000c0040102e0f60941c40410340c0c03407e841c09130078003103541c10201041e042e0000003a10703003a0b0301c0007000f45601d82c20080c10485002110300b0702c100f5484140300582c0307071141006038140708103421040024100003210800040e200103070321480b83c0d00d142c0301d240d0714901c40c21800d103081240d900c000030403203071214a44a4001e004207545404580e9011440c084200b07450b0308408110b0340190700350780c0503440301c6c41583d08950200500410402c010041b014400740240981c1015405503801d8580c03499a03000c0c82084515202e6049034000905200c00c02000e00211910034941050360003003008403e40340c0081c0090703541e401402c0c420b01140c410101103545900c02ca038102c1411400a54550100d440c1141c0c4c3d901d1204414510740c0d03448520007c0652000960462001d129960214004110f800f80000b690000d044030130568913003030030640414240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 374696537 1250 374695287 374695291
    0xa110a03050d0c0c0504020301050901030b041a0c0c100b010c0b1b040308120703050f010b1806070c050102071508010b0a11010e03030603010b06120c0f0c01090c05100f081909060203 80
    0x1644808802e4059450039904c060029000580b02e00e00c10b00051100c1d03240c103401d03d81540d60024058403292031741d003810881d02d800d407101224070070b0b20a0100185030740d00c20040c01e401c0d0318500450f003100e1201c2040800b6524508000c0e070014241d0780307601c0c01055056400c9074014400c801e40c03500d400071040d200030141d80140c2084d510114009481c00d0300b07400d4080301d40c0d80000a86410410390801c81c41101c3e1440040c0b00f0050502d001041c03003851004540b1103005000700090200d030355032015141801e6240100d1141e01d025010344640069410050a1482e54078413036a6a641400d81c2001e465200c00c1c1c2229414008001001100c0700708813600740715540711650018000c1d512403030020109030a50f00c07030798092030040c107080c441d000310520940101500100801001c6444685a4004441c28015148184a1907082c1800705060090083c042400d40708192415007888a031200e040e500c1c0f07105242d2400001d4901c2002400d2507120111802424000d044089031448031501c40c541030340c02c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 374697787 1250 374696537 374696563
    0x405190c020303060109060807020c0609040b0406090b0906090f0408032e1a07030c0b1f090501081903080402010315050402070303060806160519030609020406110d030e0a110a0305 79
    0x3030180d1981c0006d41030000f08102d10b00030b203081c60100740c000d454006070010140a0480810a40320941c1c464001101141014104004141c1d4072003120029004982c40f880c01052501c02091031400e2906400b1700c1030b12802820361807520f42da030740d007800307540010309004002004264030881e00e100082d41150700c859040c4021038050902654801004907250070325113860301004140e0001e9000702d1030284c80c6400402c1461290380c0d000c200c400d034142c14200440c0449400c8004607103d0b034103521082c141c8140303408a820810883c21204103c03030002d02d01401003071705000003030019031281d04015011030010116010b1181e0341d8000c10266040742c0011004a502c130203042c040c01d6400c00940c0e511a22070700303540740f00c0d0320705900c0640f0511400142035200e030a1300d402110680e00a4000e580140202d03c8110360ba02d0b0350700d100400c0e5898020b00c841d818010203119042103803103030013403032500d0b40013001400c1403102c1a903824905001086203580c11040c41100000459070034410003512902e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 374699037 1250 374697787 374697793
    0x40b0907090908120114010909020c1e030c15060105040312020a0203030f04030b0c070804170a12090306050a0b060409090f02100305010302120d050406081e01030c05180c090405190c02 81
    0x8101d00140b4201c860580000389181c903001b401c80d00a03a03201c4403031002c07a007204c840181c1d110300c1008070600741241080030a40000c40038000321400d5100000901e005a0900c06a5410b070081d0411405007010070348600d40000c10078403050001c0303008940703080c400d201355004035110300071036901190940c0c01040c400c1c0c4101c00b01180400601403c981880d61203240381405900d081d034071395185042c034019402170500081d8a0200c2c1545008108000d8042079007003107040c5180149550300410580481c0400c6031581e04210100700049014003c1d202148002001107050030306050b5450300810044d007042c3d0b00c1e0714404840c000940c80d214080358110680c0d039400705480d030440c0140321110460920481c442d5005607070450303919030f03c0410769050300c005181c100c00304d4030340c240d0000204240ca260729244020200c000803c2018000680c000c40c0c038165126210400021b0080070501412241031440c807504002004892030107510082d4485855242d400318501000303241421140700c0c00e0702201582c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 374700287 1250 374699037 374699047
    0x1021e091e090a090c0305030c1f020306031c0909091407061407201315080106030c05040b0105120408030a2913021e0301050a0e070206040b0907090908 67
    0x204009031410500620501d25030001c50301c110100b1419a0010300f101c0b146a0346130410010070286045050040d03402000700c0f902c03249440b044649680040f02c007841661384040790240c4010203402524460030005010745190911070042e841078451003a100000c2108007140804c8440341403241600d80d1f07000e8070300300f0b4840c10300c8c2944910f03011460300700106000580c08181e0f0f62114140440302034039402080158200d104106814080e4001c1c00402d42c001c9002915000d0454184c1c864211141071001080c0040e80d500d01140c00c0b1405404064401c042d840824400340c10940c101c8800c0c400c040c9000c80c45c3c40182890301d02813040c1560704490a00e00007087c4010345000b8069030511742d40c41c10050785650f07404d52880c510780c02d522900900030302c01c40d501d000042c222175059500a1200d14500c580c41c450400f10454541e00c24000c492081001c030030003160300380c1c50408540c070500b600e80080285407101e440e0403c0c0e0450052040300365120716500403900c00481d000e400d10040c852401c030b580710 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 374701537 1250 374700287 374700289
    0xc03021917180f04180809011202120f1834030c030b0606030606091012060801060e1003050606090421050d0b04050702030435060105090a0204240201021e09 69
    0x90041c0d003100c24480c504100b017040040721030052030a92030741d01141140da20020500113840b640d108d90500d003043d038030101d0b258040c12019038620744101448031600c1030964600d5240118141c9804984c189540840b81400c0240c07451070b0307003800110b201203e440e03a2802c81c403103900c0742e006180c004541c100c84004082080014040c0c1042d0002c0c070440b00740e07003907180c4113000c1901c85c01032000c040e00c5800d403801c46a031020b0040c210180e1030009400c081c009161210403080c042e12003842030a04d0b0206520010f150b11003203424030341c280e95200c800713032038603880702030811948207005001605c2d003ca10b80700000303450700114080100070361103441e03850b10b55070f03050100001c4a0300040c00c98021814003080060f03a9070701004503800c5d178103100650410110400388030403c0c0e2001e101c40007120700902100c80890140040c80c01e0403038808031015001c0703907119034401d8164012840395011790005a500e42003404004001800703100c286100040c01c00030034010803400e600b0070400c541c03410b0000003001009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 374702787 1250 374701537 374701549
    0x11509060e010c0b04081e090109080a020906010c0206040e09011d030a0c02010f1407051c02031201150c08192003161704080f0d0c0302191718 63
    0x3800d880c10184182084400042e00c82103075034200510480340d000000b001c209050082e40c0203034042070003600210403501440e40c5154000c200b0b06e40404c007040390001d8220000038000810640c040c014200a803188001502c24920040c03040303900540a1001045403034181d1a55449280c280001185056010031814400c0540d0740c3c5174461504200809000e085e000580d00c03107810703428600782407215002601240e0a08152620150f80140028454103101c0300040c0c1d05d0804042c140c41d15540b24840c0000e0b45c0c0d92003404d00f0203144002c41e800400c034100c0c050b10f141007005071900b080801e2130503650301c001d05039003c9603811540703104401c140c0317401d5540b103070019090000080f05a9034680e40800130b81c3d502d004006030604100180384110080010b041c006401c5200c424428507111a00d400855881d0b02c1c01c882d4841d03c03449a04014a6018803c0305400c41454268001d401ca90f400610780b00c018290144041e1001a5881030a0548083c52001041350030515482403a100030312901b0405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 374704037 1250 374702787 374702789
    0x20d08060d031e032003011d100603021c05010305061009021312021203070b01060311070c05210607180b0406081f0519080d09060e120114011509 64
    0x4010745400c25450002500944242101440d00c8890250100000f00480242c503081e180d204901c00c41e00c001d07a00307520b08100610b06131500344052a4030400207044c00b40000c14100e0741030752500c800740c07030821420f03020740c0c014107079942c1c40c0003200814030f0040b14642c142c800a078822946d41d8003200c208001100c45900c013401070b101d403050540c03800725240142c00c0c22811500400c0d103200c06440b481d10865070b4082c42850551340c020240c0c0c1c2c9450150500011141c4d0910804010030f040c4200d100c0808006070441d030103c2d5114242d820390504000900502da403da2103240900605802c90303a000410810405109003007554411740300e03244000c00052003001607807194a00d1002032105000e590703081b0104680c850808074a1084601e140003501d0507000380395000ca500000701c6221a4107468450241d00700b40c41d03c1c00110b13450042c00340070466401445128400c0040c0303094080c1159460030020741d02c445c04048002244d0065000090344c4450420790200c40c50380391104007245003d4000301004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 374705287 1250 374704037 374704039
    0x90321060f01020609030d0b010903061515090501120203060112090b0702012912150a05041a07090501030e0c1e041d0d0302031012050a112205060f10020d0806 70
    0x119003030122485e40d40380605000c820039662616117402d01d5074442c120980043d070308200c09101401d004950380d0301c1c0060500614481c42e81240108a103075000707816074021103a0694a0320005140c542544001350005440d80b8104136060515400180060003101007c60144003584140e0408200180c2107500007400d160b510015002048002c071282016003410b09010b80b00f0080740090800098148100000f48002d040c2d6040103100c0001020307440680b00310f01c0354442d545001000c004075880a44129031020014008500522071035120360070003003200c131200045448005a10340000c01c9034a400b0311070b02c003043e41d00c03101008900c2d09000c1c001c1140354003100b04502170900410603848103480f40c48402407680010205607008800c101e00e60040c112022001803c4000d86040c54071907400b800700b581c601200107514801ca14082a945680410042c03035104440340900030300c40500300c01403032554028030800070550356407507036a00031407140c1c1c059001d0301c24901000400390200070064595 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 374706537 1250 374705287 374705293
    0x16020d0507050102070f27020702060a0905010210020c0303150f0307030b060a0b0a092c0903070c0f0b090d0c081227060702040504060902100201020711190e090321060f0102 76
    0x10840d070a01181c4c01e81c1c0c00780e1401c5164054012a110071400b9100f8270303400a42218001428524080c1d0140e010015120f0990079101d54000f9a0302d0001a07005010710340401e90010000f0030101d08098280800502e00601251454000c03040080d003040c08d43d034030994044002004100351450034185075805490070600490803c02128030080031859540101c03401010314200760500c0701d07101038030050380d0030b86020840c03131500d020f41e2150b84036001030b0000c03100488411070110b8200e03450a180c109496001680710b040046180800c54083d16542041e100145481d01c0886c82030814442190703443c4041d01501d640304180440030b51004282030720000100c3f1485158180c5075a00822600045e804903004509903c80e070a00100a00c50218020744c0a602608005106c03a010340180840e5130060741400c00400103078090000380410303140c2200050151040030f1080780a5065032503081032040c0102c03802c0081001d9500702d6050340111641034445c40c102040b02c6490040103070007081d82d00380b002d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 374707787 1250 374706537 374706539
    0x9010305090d270f030c180606020606060901090902030f01080f0105090a03030b040b0d031e090305030405010305071101050103080d0c0314010b30060405010812030c16020d0507050102070f 83
    0x30040100b808114802045991072000707040303402d40c3c2140c1c40040e050350408607a071a6a40e207001008080780e840384e20042030300e912440f48209a5446010126081c82d000b8015039511072040002070b0b44803900d0141031141e0101c0202c1d80914070b20103184600060078030b0030041d5062245c5545801c250600946290303040604104807008003082000b82d20394141804199040703104001005402d05103e4260403064102c10310b0305040c2d101048040d45076055280c80701003480c900007101e03048403500000d083c3e544100010001ca521942c000303a4001c00600d07290700031400c1c1c45202802d54070b080e8010f0700e0f0404003190006500449100d0720b0041a120300303040010f241c05d202c0c50705081d5014400c412071040003040c181c5494101c86540d290113048540c88102065000052100c00b00f02070ba00c0500540c58140082505000002d0740755104d000000c0c09401d5a81e14414055a54003d4494000000c9041c10881c0142c41d16a1608515031060014010043c206800246801400c1c1d00012595480d040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 374709037 1250 374707787 374707813
    0x7051f051c020906070f1106070f1202071a0304051501150c0c050301020708030907060503010602060f04051501030f03030b06031302040f0b06040e01171b09060d0213020901030509 79
    0x821165807003860300c0c0424110400d081d0034030003405042205508114001006010070400c041606d030036a00c00d400c0711107601c0c40b090a201a6000e0a80c1c01860414134860b0070001c22040b07118000c02e5021403040b503924a844c0d11031900d4007500036000010f52500030081c131040240500404030003030301c1d03000460b183d585008098075840c0b040418800078040c20003402010701c4080f91b0b08102a2070094003d55482c0914601000290b00031190301d036040c000d8037001f11340c03039104604032070484281e64010445a00c4d017001c0202c80309400307041240c03a441079010206605428031382150083d0302076524040c488055003800f030161106440d12500c42c0f102001042184940311310f545515a806850010b540c045001b0428020100c0903061a4480c0c004100050343c0d4002801d840d06982d665507080d00c01d0f00e41450780b1540d8282030166813408102d00d401c01d41c00790900c54210355005c1402049032404090b80c2e000309a800d0268940385a40070340004c0c1103469940c05009503604036030944020030140e11510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 374710287 1250 374709037 374709047
    0x2010903020d0218090d030e0f06180102070210050304060e0c031906061e03140a0b130807021503011401050705030403030807120e031306081302040216050105010807051f 75
    0x300000b4490501c40d207420040d900c401d2040c807a4062101c501000324105422240d503600c0b030301e020003000179040c151203840c810000301c1c04042800003c00100010b440b074440c9035000400c8940154860766090040c0c030090b0f0758408028200c0b075060303264150350b0308060400c1e006807414211220546d5002c182c1c07031a50f1740c03400100d100342c00d8644106071040110524162010300441c0e48800403e42c16840381e409078500b98890002220b01c101400180e40a1001d1065281c40c21038001614840c07070100002e0f0240c51603010040511720412049280c0b10b42580000d10440e1440003d400004022005110b06d2904c4040e49541c0d9909013002400e0008645d902d0b5602e1017113000040801c0801404140d00d0b60241840d070000410214042c00300700c18104030a940c1e07070860040f0080310021041d0000d070090140c8859405142001012900c0321440d40034840690702002d1021415540400e180307020481c00e200302806081400090510503141204010054010b42c80010100301043d014010098101e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 374711537 1250 374710287 374710289
    0xd0902090a15090b0a050918011b09051c02060304140106090e30030a090c1403251206090204050a0203070c0b190204030803090f010605030a20060a021b0409020109 72
    0x4410082413062500700400e245030305a51220341c00404a005001c9440e01505100c0c81c61680e400081000c0c0d0803000e0704480158462041d600403481d1880c06000904040c00d41025201180d1501654590241c2c007180c43d07940103c40a440d4a0f01e004100320349404280980d000510314090103007e18428151140d84441c6007021074144180d80c40b02e408c0b042c5418200d0280400e1107101c0712a100d29210072044050b02c2a44d804582c4d0414024000c544480c078110101070810740076004100ca41c407810025030034645460702444885185030b10001c0d03110400560a900a84035140c0170518900e00d02c1400150b490242006c0c0e20b90740188100b0808950000d41c1103030803030300080c0400440d10307106a41c8407901109400c4040315400050040180800340300154003078005081100d012007001a8445d00300e4006010300c55042e045110088042030369900a11036405400e0885809140140c00003542e50b440042c3d41130260f0803800b0180f001c1c0404c0049581e090209071010b0000c55141c0e800207000c940b00b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 374712787 1250 374711537 374711549
    0x30403021204150c060b220c0305070503181c020714150f03100905040b1e090304180f0903020d08071b060f020702030706180506190c020d06020d0902090a15 69
    0x13800030040c045c400241c00001c10500090041081d5151440800c409041c41020b40c074280d606003043c081499200c0c2c4a6144105420758440303080d17803103090703c5071280c1c4100c680c00c0e0360702d00c50303d5600c84000081d103080540303442007600200703081443c0107c0300035041074845200d40303d249420a00c64880004c0403c81341002e05e4008031a543c1e50304c1482403056036049802640740740703140004210412100c0030b000c6000ea800400707030781102c0105400c042c4170700707000710703910402c5030000e0100300125000c01a840005d09450000400d03200344062031b16048407600d210a50042e8448100d000009800480b19900250700e4603201c40c00000c1064405612040060000e0100c0c3d80da080380711203921154113039a402a401019200c2c0c95070350b0350000b040c0e41c66501820101510026002499141400844003107088410341c816100c07a4030002a42e030880300401c1a600140260405000107507148002e0605003041000050816039900510941a4004103020001490800700c101100c00070302138802202c2d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 374714037 1250 374712787 374712797
    0x4051201050c071b030b0a1a032407030603051504110108091f140f010f060c031704030e0603041a0c07240204080f0a110a0f0303080a02120702010203040302120415 72
    0xa49590f0884c8181440d42c001b41180ca0414140404540c154120780310b45a0081743c1c0c3d45504003420105070f1102e17a050080502078403030b02070203441140102c09660344000716003000118035036030b034481d503003001d41000103e040708241c00d08100030003941c80314000307482c50286030101c0c00346400c44450703a8940182c030351104030380305810741191003200c2c5422426107619441d130b0300c81d141d0509190004c000b2100380a0361881380302c12003011078100e12038041d60390916016903503250312100e44d2440019000c800340098041020407001c4440680364180114019072044803210a0072082c0c0520145141c0058140313403204a0400a41001c10a109000080ea07584c0800c0450700e000d01c44071400c024861030344501041c0c0a20a44128059400714010392824003844440b00f4000030f0104000e001413823800f441504c07420f168418404240700da0b80e000d9000b120301c00c0040c40c02240d0b0001c0b07504400100c0c1c8110050390000704002c02c140d41032014000c0c042130b000d1440d05041c286802c0f404c0320406240f001003002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 374715287 1250 374714037 374714063
    0x1014010b030a06180e01060812091c02030a05030301030501050702070b04180914011e021e0a180e07020d090f09020c0309060a0c26090f040209030f0304051201050c07 73
    0x6600c84001025038084040da0f00c0d401d101c03484c01810303840c14000303242c0d46040c50005103490041400001d88018100b51860403544400300301c1c100c0e1080842c040ca000c0d201400d540140c604020768203d10f0300800c02551030390701d189040c50a6820045c030306021900f001404019100c1d802081d50183d907503a0000d1100184000146002058002e4010703250050342d05d0403032203414042d403080710141e001c2c001c89a01c3c81120f08400c1e09034030620201e00d0210a02c25450b65000101001803d600e074514a0000340c10003881095000801d540d070049081c4003040818860061380400100b00700003010f0500c01d00c7c061a118040391545c001e84140d640c05600003615000041062040301c05260f030003040305e41c58400000d80100401c508041c100e5124400c0d4170008144d00c1401070600d104908500060721308196041400012540108510b410a8080c4903124060368203110040110034040004e54803980f600040011003811f00a0350700169240c401032200100391103003121521170f0001c103124228 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 374716537 1250 374715287 374715301
    0x1909120212011e0507090b03061003021c090c090c020115090e0304050a0806010609052b08070803071d0d0c0b090102070e1006140c0607030b04020f040e091014010b03 73
    0x1426051040f807819000b5040c0042d58030946502160081e81c1c40da848001c566120000e131003a502c0f0584980b80c1c030043d90320072042210710030b80040010122181c00540c900c0c501215113026605c0d20303082118811040702c018007001030030b4130030b80710420510302c02400300842010300c0d001510114000c142c4001d031200c84909072a0800c00498009050140c2170b805074903070f07070300b01151504004e004020002c0d03191000002c0510341101010364200740703258282c0d0b00403180e5840440360136003401d04444400d024065607020402c10005544034a0240e120f40000f100c0c04002182a6403000301150700c01d4004c031b0714580c0070501180d58402610580104260382c1c502c1400140d161818a0307100c22840300c0c600c010400b00755902c442400440c1d10f140c5501704086603c9000d00e2842c0640b2a40c1d4034170b0b501810001c0c0d00c0328466005801e9100000e080149410307444c00344481641d20130b40201464020034024410503071402c00814114151184e030410452181c80300c0c0d4008000c0c18800c240fa0303940c011020440c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 374717787 1250 374716537 374716541
    0xd020904050304150305060405090c01050307050c120403140c0a140915030a1b080d0e0907090803040f050f03031213050c04320603030f0a090e0c190912021201 70
    0x42c0200411168403031351100001070241000311180c2d0b00131414080424010301001940e41800c2d0416141c903401e40d584c01c94112003c1d003007442e0800291180a801c0840c4070a0320300203102946c00b945c0250042c1c00741c40c4900e454041081400383c0561014801004282c80e0810729880d00c034400c41d190300480c2c40b1400d240071044502402da80e4140140c0380540c0810095580d8000f412150781c12114105544503515030311045004190381c042113000c2030080c0580707400c950480d4403100900b00488515200e280300c5241d80c10580005650b843c0b0031030140001c1ca0603148107409003208500031490a602e01d180d81d034100a000d07000e2180c0c011034000b000104034003400103042a4201500c100200e50102c2141010b01100d0003000a5491024400d01c0c0c0d019000401e02e4410746014000351719040040e038110400340c1c04138550000b0044940c4d008581d100c0c0810a10b1700641e00d5810f201d4030b4500c1e80d101d00349050842c580300424400140341c01c001d1001d208180703a504a40480301c0d8081505800070540c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 374719037 1250 374717787 374717789
    0x10e01141605070b21040f0606060e01030612151104090e03091008040f0809150412020a080304030309330c0309080f0303040602031506030106120f09020d020904050304 74
    0x40511008696091501c0e010502450207500860031a11056520f080088241c803d40303420040e080b5240c1903980032004043e01840d0014826200220040200d403a02812110280c2007400010142e9180000301e6a01d8020900034021104031200407800f82c2ea035220070301000c001d113213100c107884440040c200c00780441518003c19603104107010204600fa6001e07201d03441894120700c07441c1c140b25031248441c81285c2d1301d4440c0e5803000840800c80c0c4c05407501e00c0b440e00014245036214056081c1460244001c2000d40000e12201712807070000845071040084035446500160000da00501c01000483d41c420f41396812900c0e11400c11204000358007010500b822040c408540c0c40c003102012442c8607a0254007416000e00036560081000c1e110498036403501d03441061071500d80c1c400c0c40401c010a40c07980c0295080106181e40c0740c0c010040c000440d1441c2c109911040110300c00c0904120022414026403201c04c09050040010000560000d8101c0307061000213806521003500280401c481041118 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 374720287 1250 374719037 374719067
    0x1031101020f0316050d081e06030f01090606050a0605250807020a0b070b060405010b0403060e150115080a021306030f0e03031314010c020c0d0309120320070303020c010e01 76
    0x2661404000b4413501411840c41c000c40d00c1e40300300a41400c0351440740300054050f988503403880c5d00c890000700903124101070240449501d40241c440750140807209124008081e841100082000c0b0b140c0020010040170a600c0402072003000c00c1440c00580341241c0c0040131080e18160b81102a140b400c02980714011210000e40040007040045034440c0403030701030001540b2449910480741d84d45c60502081c0c0d035080c85000f070981401c0c0000d0002940d00e800c41400c0c41030520888501328a1032020040f04642039200e01c45440280d17000e8800294044012a404240c00d4800d5180030050610a42515503500c101810180c0d40c1c0443c0f007082c2d1791b58000c8840d001481c0126916400c024080140b50035090380c0481343c50506002040c5031800601910303102000c1c4e50043c2032040e6000c0188100c4804c6403030102d08121840780081100078800f03486842c030034041d50312051944000c02c01c119010501c0303401d50382e0307a5000050810000f540041c1c072104401c030a182035074800c541400142c5186001c0343d910 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 374721537 1250 374720287 374720293
    0x70f030e06040611010f09121202090406061115070f050d140f09010c03091511070602030103030804140c151308190201090b160605270115140901031101020f 69
    0x4585502480100d41c0b403c41304020007185224000301d00484060100c0100003690a40b8201849406410b4022820031010001762500c98550001411075a00b5001140420319171603001760890020010b40c0c1007001135086150031400c00a01c0500100c0070900044100000050501070074940d942141c5a50002141c4842072400d140c0710711421070300203c40343e100c0d56180440e40d0000070301c00d00a400030f141d080b0307903440b40b21407240348450007412061594028501c0100a0100010140d00c02180210b001c5e682d0b64280e410306140208a51b0400000c49032984d100712010140780e5034140498880c942260119075a03003004880004100410394042112400781c00c00010b0f10b001c0d086882c14160b031003665103d0310262188080f50183c081d08207824019001c8004c040001100c3c1d505c0b40303800510302910203032003d501a40b10072500d030701e1491181c1142d4580c01c84640001e04411050098403000304920100e02a507408180c11400500c4003809440c0e000c80d0041d07090340240700c0360311803401c20000d0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 374722787 1250 374721537 374721539
    0x120604030c05060601020a0321090b040602040e0105091608040c26010e010203010605181306030818060f1617040305030a0f0302090d1202070b0c0c030606090c070f030e0604 76
    0x14090381c0148000361268051200011050341c07020070580142989034448240e84029000701c08401c0f558a009001c0b050743d030700c104001046004003414800d1303115110159565040101020b01c062045c0e1003540a5252403041c00f910743d00310740c40c01d00003503424a85038003607035102e04041d04500d10b10360041d00d0031155050341c1d0300b0b2003842203034104181c02c0d072500034040c2c6054608910300301d200920904001800600000103140042040e003008044001c1034200001d000310002c104130703070310b17a4000c9624000009446a481e042030113681c2e680201224282d04120504020011510030f02c0da00c9000320004500b0369080259483c4c00e851600200e8031001d40392522441c0056403a8800c00e20040456864400707000014400c3c000c0360103610000d03100200d800c2d10b503551446900320410300f90065014516010a5140c3ca0f0009030419224500c0103040c0300d02850141800d0001c0500b106020301c40309010001004070903000c035608240c0c0844541d8040c0d10701e040486082c4800500980d100b43e0000e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 374724037 1250 374722787 374722793
    0x405131b06110303060f1306030501140403020c0a0510030908070501020a050a080a1b050711040903090f2c180604030f171b0903010f1401030b0c070c0b0306120604 72
    0x101102a5101c0c2d0711400e40d40303042040016540d000807503082d6840b59910021030500d0400001000b0044550100410010303107035a00c1609480e07480130b101c900200741000304000c5c50340c108003100300d40301c0a84a40c490301d8109030200c0d280d04c01c0384082c00700307143e100d10140d4100300c540c00888040d1030b00071000f10f49413a07580300d0051a5910082003080000d0721140414140d25451241120460551110350032115200900340d441e81c12030316003559001c0000c0405009a01c0d42c1c00303542c1500d80700e03036100d05509042520134401403503a90091001b015120030380500292608088503810282001400b00c25591141651030100000082503141d0003208240020580c01605840a040603603c0e8441e130110302d01911801d20004640c0d03013661710180b04134208030f40c810100600c410301001c0c00210b403200d2103496440548161314410503000940500400500003803044c0329400440c409002407500c15582c8031415040c80b80c0c0203214105d800000812490340e9003081450649d0300d840261101850142 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 374725287 1250 374724037 374724083
    0xa1e1d060a170c1b0601150f030b1905150405090c0d0e030f13060f080f070201110c0a0c0803040605041404060909140d0807090e0903070c08100605031b040513 70
    0x2004813501c8900030600c0040e801140f660b050302c1701c5810070186641c41e1034040b030300000d480d80c446c03050542d00c544030440d640310340c00381c03400c0103448008003d078a40c68032040c0f01c4062034030b20304e41008000500091105580f03c071851034000ca8030482c082d440300c4d5401d000000501801d000301c140c038840001d501d02010040009001e0702c1880720324001400344e403800155070807080c0c80b01000000e81d0761000076004a03040794a00740c00c00a240300000340301c0c42615203403065512400b65800300e640400c5842d01004203450040000c1c05400c800f450a0130319000b4007501034081c9000b0340380c0100c0300b40da2241e13180c1c03129842000240900c40c81441050305030b0420316590b003400810b0903521301a042440d15000d00500e08907029811b9540d940480ba881c101051900f410003030100341e05030204000c0400812409494400a884a40050545801c3c24071808040b19102d921032030080d00100f00060148510320000c0450b00c0c001d58010555555000541c0400058408000e04005809118074a041200b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 374726537 1250 374725287 374725297
    0x3602040f12120e0f1207091407110316150b0307090b0306060a0609060c050111030c04060e0907090909030e03030711031e060705030c070c080606100809060a0216080a1e1d060a170c 79
    0x207407241d070030550300cac804103589a04c1160303481e85040d5070100d02e101c0083c441c0c600744560310b03040c3c0a0008200caa00b800207414900310340e001080c02038984007134200501d01449890780082084032aa40c030307142b80241c050b003500380030b1040d0310900c00307512490801c0c0300080d0000c0ca204101070326110f03a20300e8071201c0f04140307400c20301410380015000c440796001c0342085024980509640d0310742504052510100f5805080700c20000c404011400c02100e0a648080018100840c818000301c0080340a08060503d06960600503200c01020488601da4110f00400c003a90441401d00e0811342d40d03946c0d030010851174407444200400740d0b0004617000440341c10200300507008100c2102c0c400440342c844502100c44c02020f403a03820f40d41c1c01c144003082ca150b03104e0f40180041d07100c90040c011000d20700e440780034840d04100848004550151070741d54140742c01130103450a068042c240400c20000500d0700030340d04071910502a0244400160060040e401608061400790420054002c2e07494915a104140c0d001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 374727787 1250 374726537 374726551
    0xc0c03030513211202030c0303010b040e1b032403031201181a0409021810030b0a0515040908040504020403060b0a3602040f12120e0f12070914 63
    0x841c408144018104000f0707600024445412007282d0440d100da90300f0701403201a0300b0030340c40b0030800c025000c0d80600155000301b8070400000d40307442c6085c00741003d0704401440015070390316018001c0522000c08068980020920700080080c82d2030002c0d0303058680010603007a5041c400801e81841c850200800385040e11920608402062010764103c0152011744802a0880610038002115402c042c2d00460307030280003c101da1540100705508203014103041c1d590200c1e445044400340b0070b01142410481d0011007a0008008a01c2c1000c084820026441c0c006403140d42c550034144c080c0301c1d142d000c7c0d50140500820455a9a56030315006004288100219000381c1212400040104080040e07400125110f2903154500310481700140c0e41d003120b10600a003840e82801301180c4a2000403544010b4000c2e0060224175280030704040309400d0310302454904002e41001071070880d80312894401301c50041582e03500e007402d10050aa50500c640b60b00003400451502c40b02c030f4902c103c201601c500a00c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 374729037 1250 374727787 374727817
    0xb04150f0c05090105030c0409020a0c1a0705070206210a020d110a02070612063c0302060a0c02030a0605090a0b1b030c07062003061c120305070c0c030305 68
    0x4061040d010603101240c0c4128041a410321601c075043d4050002903600810340240c00d4945500c41060300f0403a080039581000052030300003c081000102803040040c103542c407000100502c1c10001c000e09501c5540b0000b801440d01090f0340342e05180b9617142c0405075402078035501d078904d8070b10100c2c0020341045c04800f60703040c101803003240c008140c1400c8582c0000325502030b140303d909008060710000301d2100c04481c043e940396030005e0322a14648205114941412402400003000e0200d000c0301020f0450000c03121200f000c0c1000169502c8080f515800c00c5400c2c625120125400024100020704002400460900041003c5054042003007241240724616000700d5464004101205c003c68030700d41c86860300d080002c2000007100002402c4001d00c21000410155805180c400c1c00218000d501ca1041e00c021061241038505100c42500800310300d00e134408042c1e1281c8403410442c40f0450210241591000841c001511480b401c00030f0030341003008801d046940c0d29005125500110448803502d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 374730287 1250 374729037 374729051
    0x91801090b040b0103020c0309040c11070b070b09010203060a0608070e060d1521110f0315010603050130031e050d0f1a0f030f01060f1a0a050a1b0b0415 67
    0x142c000d1007a6500714002d40020f5040c0520113042c080142509400c0d0014050f0f680c1c201d00400718204840e002800711248ec0584a070340602d841d1107900c4019000721140d900510811440780c0340c40f20440221130040c0b5010700c140d21000310580b40c280004d4112904130038002503040e290301c2646c00c60f152486180b11058101c43d07450783c1500c4410420110780c440402e07901f181e000444c40d1103440c11000407004200741c01800309100040e103806180044122401c9541b00100491a050b204132030040042202222050760024001c510b8400000030303150310130b00c0d0b698485080c148556014500e20f610b01d00c0a034038519190501030401d03045460101d841c03d080141070742c3e24013494050041d8000e00141c520625001403c10072001800c0782d1113254141c41840715085484009010700c100400c107803500160340e14100000c158130405040c855a0107401c0030056110000e03408070848015081501d840030421026000035150030070301d1907028005c021640c05103c10300442c2c0c58800d1400e805170740100112 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 374731537 1250 374730287 374730289
    0x61e050604050604090207030528020f0f100f020403050f0a062d02071401060f0611010c17040c0305150601260c09030c0901060f12050903030408091801090b040b 71
    0x2520550046542180d002d04c0100a41c2406801404640e0300c607081c5a402d1a0702980840205042c0c1d445240c50304100d03804883c6181d806000048090410b0703000740141070303450300d00c00d560381d020100c2444c05550390b00d001004000d0954190741c0907540c4401690303000003d0b8185a55103498840081e43c0c80c0b4a80014018040105500c440b0451003000a5002401005003214000c1d00148070589000d55407507424600054207104590160141c0c0052107902410400e00a25101e03801c10340d000540c2c5003803a00301d422500b0680162490f510b010b00c00801c2c2c0e4a518028400080b03592000f400e92080d14811041c1503104000544190000e980701180b00020b040d1030300c00a054a0b102d200b440c1c0d0103030040b4200f501503100801103100083c04840080711504086411a1340c2603004034000f07501d180701c090a10b5808040c00d210340c52144400d010701c5c00c105182507107a00c40a40000d100d1400001d0142044e1109070300d035280e5030136180300d4424640e5100381c1d140c003800700181903c5c4101c0c41c2001d8520700d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 374732787 1250 374731537 374731549
    0x50120030103020a050f0f090901061502010b03282f011706191a07050d0503071b0f05030a0206090708010e1b1906050d06060c02092701061e05 63
    0x40b01d8000b0003140205180506100210a102c805250403180014003003001e512101132680c090501d600001810a00d02611043d28000e281101011a410142c007140581e40c006101907251140e0030680c03000422001001d81140844200140203071034031400c4d030300403084075030322078180c20b255038000920350703034007000456030700c00d620410403c502c6c0d4480100d240d908040c4007020800c0c41d041c101080700d58030b400000300407244000000740f840340d0008199007003110034000d80e11101210704140341141045040a0072007410031458191444032072500c00c06020304080c0c1642101d17041429656504d0206000a440c2ea000f10340c440268030698100160f103101c1441175941050340440604020301c1034a140c0c990a200601006038040c9049022451003d640d40c114002091035445490343c400c2e24a4046050b1000d036403140080c09482110b01001d41c680d030605035400780910b00e0b41181003007100501d180070074809100442541c0b034404041034820b030080c0001c00000c0c6010740c1d601010351716410480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 374734037 1250 374732787 374732789
    0x1b1e04021b030409051e070f030204080f0c0a09052403101803080f070f0e1908160e0f0402010c020409060e030702032803110307081206090a09081605070302030a0501200301 76
    0x20306e6005190005221900c503101907a0030b841146400f502d0309a45902e11881e03c000703408034046903040604845024038060003c0d030300509102c0d40610030382c504500f0981904803810105c1241080a00e0703814495a001e00c0300200900c4904010410b012000c07011203400039402400310007007540500890480d41d9240b41040c890344035555002400750820001721104801503221a41008402420002c070060065141d00940443d0700104414071000140c541260700a0f408a440d444114007402000c10150b22503540c401d80a080250500c0b00505c007080c0201407440d8040c0003a0f241200c441c0c40200302200802d4814004c401325002c0c401012070b15004143e9003181c201030072030070110003c00a400b4414042001e0052010340e8100103e030348651146901030b0701100c85560f0b15104009051610300011a00301091100400404001c0c0da10301283e44100002c0e1102e101c44010381e031007080020031440b0003a60303010b4142c0d141181c091034124040c01c08240c1c0200c0340c0d450400400800c040c44000d4074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 374735287 1250 374734037 374734081
    0x16091d06101a09060d0c0210020712030c0c06150501110c03060601080702070e0c091309030903020609040207050715020601060f050301091d0318031b1e04021b03040905 74
    0x10010600c0e00300b003a0200e00201550210588080c411080595202c0c40541070340c8910b1403000c2080002138000030706009009600c242064414070032030001c40c51008416114100504000544c80140c036000d803a00c800c2410300620081c100000442401101c00e04001117440a03213400f81100c07003400d00309031a4140384106907055842038000482940c40399494a4201c030190055541450312500c0e40b03804968200d410300043d1600058241c1c0720308080440e13a100c00240482041400341682d0000c04a80c180e20000e446203402181c40c1a01d0b80d0780d0ba045500c002ea200c0e003218602c40d583c54034428015403d0071101d000d0b010b04400040e0007030240c0c1d00b18440d00c0780345d81d90038516800c0c10420f200510003405144c5e01d081450075480040c2078204010400101c2c003006407880708815100700b51411300c0c501c0c3d600c01c0e29103161800d00c096489100d0300303141000101c2541604250080c020a00038005c0c04020503806101c50101b58400b1400300007001500e084103028485039841a02d02003441c020f0f20200c2d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 374736537 1250 374735287 374735311
    0x3020c03010f140c162009070309051509010f0c09030b060f0310020c010204030614060901090e0703030e03010e010216061b05030406020304020a0b030717011217070516091d06 77
    0x180703288071990042c140d08880170984c3c00007240c00e03100d050300d5003035242503070680c501d04c14414801886d040c881039900600928040c00701e002c0990b00c807600c1e2491040c51380c511801201c04204182800c1d0048214240364420802c41200e0b00d00000380001c0c1184004d8842074103d201055050030000388404c0c0c00b04014000381080c517045201c3c03100070352200d005400b59560030300c0044001144c0b03008103c00309904d03035000666030610030300708103078000d040e406040d0701454101c4515101070003098920449801d814650219018580841c0c09050700a46038422540700142a00c40380c2c20b0494071000307081c02618108480c5894440802101840107200707800708805000140c0000c50070380040d0360062000c0c081001c81d41d8ac901130300c031090b002a113818000c98810341200c201d00486000041c0104540d0308861000c0c80305031140814515900400c0c2500b003c00034048050202c10080241c0d0401b04061040d10386980d000e10038000c1c845454801e80f000d007800648440d22200250715401141d20b4244 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 374737787 1250 374736537 374736541
    0x90b040e0105060d0e060709030210030608120a090e0708041208041a04020f04050103031214042102071e091404021305070c021801060e10051905070f03020c03010f14 73
    0xb0060b40f500203d4140c1200c50310350f400019140828411b4a001d44529140c451490342148100620780c403458000c4810036207052400c20210034000b6082c0001491440340650b24059440b0443d400351017604848080c0c855401444450f80c0e001121900c03a5000d40c0d0726144403003032200c2c125000b510985001c0c01a140900007140241283d20140e070300b0901c001c0c150f440c9040140040f40540d00d099105801141d80201c411046814030b004500554006101c0048940340641d01c0700c01c00d0100e41142c84040320180b620fa96814000c00c0042c1c054000901030709542c0034005400707090300d401405a200046c0c20202d50f411050301f0031840a00555004201f00e80291010198200800006106108004151342000b0260710380d02d034480c0c0d601d400c80103807910f1581484405030100150580c22409241104003101c0201d90200c203454810a85010f45c4030700e400b5040e011070359405a00000303400321412041c0107007015000101ca040e051b100350002c0c40304c4400501e442089489810b0701d007141a20300344c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 374739037 1250 374737787 374737789
    0x6010e071e2c0301090501150b040513050703021201270b011b060b0402040b070c1d04030c05070308030115110f030405120307140601090608010c0f110a0203061501090b040e0105 78
    0x108041041c0c4900351480c48480c1c080b80001d09403280c03031401b902d03aa5900d1141d10021007a24410f9806081c480158a150600d440c01040b904140520000c050a40c0c0e04041900e052180d011142c1d04501c811003400e46507100c03142c44c00f05c041002c1c0c0c140010f00d20713441014140c10150103241050070050319030140d40c1070800c40c0c280c400071114804070b60440d0b8a00c0d91714501c0d40e803880544060b2103060605038841580e460451151081c0e60400084481481d604c1c1e00100d51007400294015070601d010041c81c3e11034540140f40852a800081c1b0b0400040b0012402030400c0e411284600f020f550b4420300f5000001a0704c1d00e42001000d4020207410800080c0a1400c250841c40302048021040f2842c0c6074541d21f80c02c240f9042499440c01d6608907200400000485009034000703402248000c104560b0901000b81c1100c242c002c0076424814412082c116018061000e044e0003a00a8103455491070200f424606070104203150601141d421080481e80c12040ca047e2816a168040b0074103c60342001c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 374740287 1250 374739037 374739077
    0x1401050f03100606051803070f0b0f0405040903110606040506030c010c08090d241107061e0e03030601020f061b0c03040803070605040c140306150f0306010e071e 71
    0x11012076054480c2201d40d50b842da2041c8070b001c0040c0700c282d88281e01e400c4098046000346602407034003403103688030305028807c80440154800464545130400ca44c5d61100f43c0e040040b03409640d2110f5442031070038a03400e0500d0782000755080941074950030345002d50740e1318003040101c0b04240c80d4682c150780454204102c0d0350042070f0b078103c1c40c0d0052500314181580302c0e00142c1992030011040314a0710101c240201074854000f420b01e00d11700109000d0140040b000d562a245001d50f1030040c00d9142c6502898060040700581241c544000d0942070141c020070740c00c9136560785c2c010b40345540180300304803d06004603400b00300d45000d100600c8003000c07241e0401284041035000f51440d2142030208100000380c0030010001003090a205580205003840d0504190114814070f03803204506054955080c03519541c08595968443d0202240d071003101102800b28003040c05a8948030342600c9190300120b0780204444449201d074071140d07210101c9510402c0d0207500f82000003003103030100c1c4c0c0842c600c0c05000004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 374741537 1250 374740287 374740309
    0x50a0e091512031210061107080307030509040603082d0913021e0703080106031d030901110304050a0b130501020a02060a0819050718050109050f04050a140c0319140105 74
    0x60843c2d04166041000c1071180d0750640d10361342c15103507003102041225000450b1082000c032800c05401c5051800280a03264410543c000341040302c0014800e20320f554603841100a90340120700240c4410002541c8007981d0802410b01092500d1400400c18011001c802c071014000040d00100c0660024600d84002c0e410040342c00c0c1c100d980404d10441d401290b08041c0440e05c2c0a9961780c01503516141003c0e0840d012850074007007214100c0680c04800c0c0001045562144c5c080c41c00d0301c81d01070003070000c0303041d80503540207203038000484000000d00c554064080c0c0440450390030120017082c1d03100016a594040c0031402900280d051000c64a41806001e80e40d901c0414410034000550400d110041298001c407079000103d03202d2801004c140400c000c80310007404082c03c1100314581460000f1782401100315100344a203071140300254100d40d03c1d40040d030409010b120000c803075081ca8000d032189604129031390710386009014058205079016002d40344240300c16040c00d8580340d0034481400395603101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 374742787 1250 374741537 374741569
    0x325090603020c070302120d0f020c01080105010518060c03090a090501050d170903010c0306091d061b07050a03020c011202070f030c0519050c120304030c05040228050a0e0915 77
    0x182003800400340c0c41f030250b007031040007c6401030030031010504009003100d09250a91740855001c90140c140703998200440506590090a007507840d113480c94140c80301600d80004a40d00700002040c4021a0b010000246c4103a45041302c0c1404880d40b0b82c86002c0c00c480b030074400e20b5485800350310840c002c1a0805440b48120b4108078070315142004e01c3d4007003801d64880b02d03001d00c0020380d41c460422042c4043d120b200a4131f2001074805440b50000800035035280c1b40500f80102c000044846148400d04020850322004d03482419142490341c1800c001c3c1d22518003800003808621000744e6020b01103114804c4a00403540500300d0348000700309440032950030200c0c1204484c04d2203415809600004000b500142d4244540c00400c4014800c4051000d00d501585107001c0c03035031051002b400001c1c1404d48801c1941c3d001e640043e268004588031030313613042c00c69007645048403080108141c01c40d480702c000c1044c90750980321010462000020302200c407004485503082030300800d12001c801d2804020780121481 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 374744037 1250 374742787 374742793
    0x903020a06150905060607030806010e030a0f0f0c0611031207050d050a0903020f0f030304020d11090f06150a0c060c050d06082409070e0406110f0325090603020c 71
    0x80541d03210812281c201c81e49040380c15010004100b0507009000307141c0d0022044d200241004002c0e64042c000343c00180603581407184000e40300f1210b0702c08201d1309154503004410901e2100c2d50b400c10300d40140e0201000d90784442c0c0a80045242c0340500344210140303800000443c54410140022824800c02500c180c1c20000108400310b10702880b4002c503402601924070004003d11585406840e08039108140869908004040c289480c004010369502c81e4042c0d9006000f12034034505001d90100715010b2a5120301900e0521800b0136044242c0c0c0d1140405542c42c0c01c41243c050031164a03401b8250a2400250840f4403040000781c1c1c541114a51130024113000b41001030103581e040a444c0f0035000001c3c2640700c00148100c03500c4100000711105051410341c04070f0306040344483c0d02c1d500c4a003e00c2e82c90301c102d80041010030803264000e880d12403100c603100b5180d10300100080f60f99402950701d981c00000d030006050f0010901ca0780520b0f500000d4917402440e9141180550107904020104503840c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 374745287 1250 374744037 374744053
    0x1b09080d120636060b0d050603010f02030f1b041214010e010606180f0807030f03111506010f030c120f0902030307080909010f080a03050f0d06080601080d02031606090302 75
    0x140d00a00126080680c03c0151003580325454580c03a41c0d0454281c1c8070f070b0090429204000e0381a0001c02c88442a1340200081160f50f10040428050709100030003000c110320000800c024200362420f428010700103424141111619040d6601e0580103a0140c080035201140c40100082c0c801500c030410f500007140081503480c1c01c5d0020508440e903d50200d40880c0201001003000d11005544038090002c0c1c1207030441031402c00c2d05640c0d4030f52071804010507031070703240d80c07880107050003003c1990208402100321103240500038601c02c00c4240540f072140c0450494100310007058000d019545540c041655030580f0f0b801000214006481c5810b440d5011701d80e81c04295001da107040c002420f559016181542d580c96600c0300303210000700160b001d2550101c00032418813451002054190001c0d0b00752400d161075032071541300380300c46105d0b80c42c1c5000e0540c81e01500085a00010601a04803048102035070840c1c400c004050362070f40b0600c41aa030001d01280c814000154080d445500c0c2d0900900c1243c480c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 374746537 1250 374745287 374745299
    0x15010518040e07081b0402070807080f0d02040b04050117060f091329060a06080a050709051207091a031518030301062c09070815040f1b09080d1206 65
    0x40740c1a41c002e00e0b401d8000140d8081007200310205c0b1a80b100094500f1440d103071182e142c0b840c00740034400c030003070040000040c04460b4030b80785400d071000049826411035a6a588100b1111950b00c01c1c4902e9022540300e000c20002680140710152040d0809001114908100ca08001306181c00900c00316071285034100040106100c0007a2460800e00b101390741d00c00134640480c2c942402c00081040d4410080103105000c0103610814440c0c00442504010036503480b9814140c461000300d030400b40d0054110710003a0031606e800240c49044991840e401c001d4440c1aa0701c04c0c280c2250b0894070b40d0503030300004095084680300642c450b4051684054601c04410001c0c0d202d0560340280d00c0400002c0001c01e941040c04c0c10840c0702c6001022614818442a2204010410134400140300e2400d001654000900c440000d4540a10a1200a00400c100b400728046640103082c8603000e0010f5006e0f0603400d98481d406034036001c0a80d0f89039001001c85104254045410316400030040b00003e40702d810019039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 374747787 1250 374746537 374746543
    0x6130312051911040e100f140d080a0c06060f0b090d05010b0a080a0b070c0c09050402130f0c030f0b01080105280e16022a031c030203060915010518040e 67
    0x9409180000c166500e282c1700f013a10340614041c0040c01500c2da501c80400a0403200403003101140e480080304c6000103400070014090384040c00c0003a100310720010b0f040c1c0b0004d070300c0607201515501c01d0608101d2a5115090011850514041c1541070102001800d010307141a43c0304040c164440c0d000840d0003125100402c1700703002c0380d6025294a0b481384001c0d030100704100d4840e540c032004500c0c02440c2011241c5440c0c2417501188944180c4075074440100d000d40d00c1318040c0d614a002d08400c14400d1010500b0020010705440001400092900704010b8418519024440318614140d44098090f400c0c00d0030880d015501c0e05841e0410700c140b101c00c00e42600420b40f064001e213000381c2e003050303940360003c4041d520100d1174220307a085403c0004600c0c1c0007103910705114600c040d1a4254280144d030030b00400d1829007681030b2800701096a840d5805c225070700d6001540700c0c15080c1c1c2c40803501d4803202e07458900b58010480c281d010403000e100070040141c4a032005546020001c2c00462403180300003849003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 374749037 1250 374747787 374747801
    0x9010b0f0f150c061806070c12260a06050a0b071716050319030506030604030f020a0516050406050604080303070302070f081c2003010302060a0201060b1308061303120519 75
    0x3d09402040030019030f400b0107405034101e0410380d8068074407031030800d800400304c0b10541c400808040e40c00307003507680e42c40c401c0d40d0003d071001070120b81c154031481c0e0304010038890008451680000d814070384081500d0500c0003402c0c0c101c1b03103c504094103041c0c0550f0741d040e480c0c8403140450304000090150703180084600c0000041280142d01459803038604002180c81040e07040008000d041c00e240c2417000c0354a0008440da80190103182400c0c0031401d4034001c030b00f032180c580c202030f040d80b0030902440581c01620604008881003101c0400c403480c2c1e107005010960090740f180c014550014000030f00c005010381c00408007940b003056521110201c0d44d890103100e40102e00b0510321010000c41c5400b96440a10515408440c030300c100c40d0f01020044219906031105020080c0521404902080424005d4202c1001380c0003a19045403a0344840d01000d41b61412481604000e00c124000320f1b00050404c0d429401c910703050358868208210203e1480d01502000c1c045a085890219454107101d1551060803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 374750287 1250 374749037 374749057
    0x322030512010603060e060108070e03010e0105010f0e041a090a0b010305031c0b030d050d0f0c11070f1a2d04180528110703090e09010b0f0f15 63
    0x40e0701c0300310081549400c2803050708603c00b80341c41c0040a01c0040315240060f80e11850918000c610f5a4a42d03000712020320000303480340c0e055070030641c90304921401904668161404451241010b541d02c00d46961103a0341500c0c09402c0303446081490303440055036000d40d42d102c07a0f510100ca6020f94070303644084007001c091740b003034950703820202e004000310080100c40321124440d10381c01c3c005070446800194540503045c1810013801400110004200300c1e80c0c11550a004402004028000d040d0b0006003035804817000798010b9005400c004200500c00080745401d44a03c60612010300070701400020807948001c20b01104503042d0351240c18010103242004140ea6400910f2a0b11203241094099a80000c880c13546049420107003000714420083d201818455049990b07541080e0245900340000d00001e205082a4000001d5013402d00d070300602d10700101c0307000100e004000c0d0b0300c2080aa00f22418503d41d1588504a090281c401d0b00d0308040128075088000c110942c0080381d243d20314403e0348400601 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 374751537 1250 374750287 374750297
    0x7140c06042406080d0e1201090f031b0c0303050f0d050c091201110a05091306080d090512070e1f180507090605070615030f030825090902032203 64
    0x100406515060001c0714400c0e4424083c0916420f1040054640e5500344207881005444181d0000d1580e070f0016500f007a4441384003c000540076800c4c00e810341c0702035450903000710350350132240c0741c41c1c0b00356244941d00b0030b0308503480b02c40c07150650313a0441c0c190b48102e91400215005000e00d8000c01042c3c45030340c1c0959003420103951790380c11010030712540c140201008245a45090011500301800c1c13000c135043c00c140c0d0320380b00da50359815100161010300032441d0408141d14000300403a01d40c0307001404804a0400e03858254a403a5036a041101c00d0680340d04214030703a00114020801c1002d10400b058100c0c04069061443c00b813810700052030070b00d640d44642041c0c2e10300b607203500e0025880e108654001c0d10500e880041d040c18010083d10510550030024540396680707900d000c2066140094001856010b02055204111410b000340160b0041d102440106403e00480134001c801090b0418000f03190784a0705195803503c0304400c029003006100044c1c6411041c0b034042c5c0503000c1c14490707190b540f003519a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 374752787 1250 374751537 374751563
    0x51510020601060e0604141306080708030405040f0b10030c03230f0f1317040b0a0c060c03061a032205071a042303070b0315031902060307140c0604 65
    0x10003413142c00b0f80c80809019080c00c02c018080322102d019001c800c2c29050f507140c00400034100c40c1a0050501c0d5015a920b07005036000400c0c0d480010000b0001c03210111002d1180b0313034142c1854000c8401070b1000c0ca90220480c0c203008201c0d4029080b070020030b1498100040c0c66640001743c0e001c2064540115081d0f0300140301082102d81c0d2002485030030054000b01a01d441c039090750b50945ca4412000301400304d8480c64042d44242140c0800c44001d000c031110900d459480085c4064201c842924045070198101501d44900d00d00c00d2040100b103502d610b990180c2d40803103005400150780b01521981c10300d0414075985551070705403c4020075003845480240103880c90040440140d00d08403483d060304400400042081e8500007200d41c82a1089614075a044c180c52800645000346a5024029030b003c04010001e4004001040e07001f49481038007a1000e03082038001070080b550030307844000d42c07100e02070010400107403044503005c01c8444990046da00d021200d29a40703290200461b011540340c0e440c124 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 374754037 1250 374752787 374752799
    0x40f0f0803130b0a1503170c030a0503040201170402060d0b0d0b070806031b01020a0b0903090a03050304080d0503040c12050f0124080c031f020403080d0b041d03030703051510020601 80
    0x280365a201007142010481520310050540e0314a80d1884060f100d00f01c4807840701d42d104c010354121200840c0701c0040727a580d810180d40242075504104d03000e03400300b5030142c1c803000c1c01e06008004601c00c5078004c0c080c4c2c3c9414100d014642c001e0803240480740d0800e0312020309400058a284510740030300c045440303001031464a82c0805103000c2074500210a000c007600701c0c51aaa0b6000503004601e2580001c02c0d0305940c0d11210118a5401545600c41d40449040000400d00901200a0058465031400c1e1980701d0b01002065030306100c20303a00104190f42940782000914106002c02210922510507181d041c039401c1c1d0520b00717441d55503243c0301c0c4016015a810701a04c40d10b0304000020700c210f00191a40005600000c1d4540c40704101410498965006808200c041a8100c4015580c041e0140d07850344481020b28006003901401c0038042c81c60034442616050760142c0da0801c1d0f08046009600c4d50361511001c402900b00600f441d041d64021804080170b503a51030360034412595180d03004080c0e540c5020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 374755287 1250 374754037 374754053
    0x50c0a05100905010c080d091113020906160302030c240618060d050c13090506090619020703090f0801150506030702030a0e060d0608101a0108040f0f080313 69
    0x540110720800c00e101d0319001d410341045050003165801d00341211000024140903000b84903401420a01c1460080c111042000030014084143c0060380c032800e203082a60885812446212031540e40107070240b0030402c00b0701c01003801340d90782482031041d82c0c00c2010700c00703801d482c0000c48070201680c0d015114141010399a06182c056002d44100c03036000078044000c1e054900080c01804081c05502504204000c1c8041000183c00514003e040315102a504454800c01801054001c540902a034004100b0034200051503074050300c00b0200086410101400150080d40a01000c5060001400002400c1ca4140401100810110303001040c100c0c10f000e500c9422507500c1c5c11183c824242070052044c200da000042d200008154107080c01c1100c018000030303096001d416448400350b820000003250604010405000d41500c0d40b409003c031802c8a0b80703441c06031076180c17600742c00940700780c0001e80400d0302015088100c07405805041103208a5440c0c4010550088410305103005040c250002004890 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 374756537 1250 374755287 374755289
    0x50d02250e0a0e0a02060318060115050307051c0203100302010e04110412030e100f090e0f0403031d0a08090f09040b0106030b01050d092301020c0d180b07050c0a 71
    0xd003102044941c2040c08100549034090002e5000b99502c000500049408009010585030001e2001d512442c09a15a045860f209040c0d050180070703000002452400115031326500e00b940744c0301c150451b9200501142c84d9004003149580944c0e1400c6081034800c090310085002e4001c0d0200d226403503007035000150031013408468540c012840e1407504183c01c400700041d5002d4034407861840300c0c03044003818211032803410065110340c0181e0713802542c800103800c80000c6803000500c0d220b0319003070b9544610113812400c0c2101c04072103110344000003c2c0020f2203075018165002c40301d822000060038240c5518030301713100d420040340c8407400060030140300e1420030182d410500048848102ca45051b03030314481c00d828103209981c14540c90f08098406680103400381d07042d90080c20400c02000640342401e400d02400e4071000a49010240066503400c0c0040c02120003107a9100b0050030811286c1808440301d521420300c00500004c0c146021615407a10401049081d0181c0c004100040608003000300f29016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 374757787 1250 374756537 374756593
    0x1504050c09100302160b0109020403050105090f03091306030b0a0504030801151706030a0215030604050a0b0d11060c01020c0c03064c180b010906021504020a03050d02 73
    0x814003154645940382c0b2814100711156190241e143d0220003036942e50329040207402002c00155400225000007075078041c0084138090b0000340720301d884003e40d00391030300d015038440407443c3c004100500c100d0802c0c45000a05c803401810004915559403240c40f010070081e900303900c1481c1c694007444289503102c0205405850340c6003010001d99104075025050b990201d0341a00000e101e0400900655001e03c1410340d002c1d0040d000d0401c566282d90815600c0c2d000701c036a076124600d410045414005148a59290000b000d0851002d40c1402d844404012481d446180d901480c2002061a6004203001404803510400c0050038581c543c4400c0506050b4018000e0074070350760448191090482c1800c04032071000c1c1a02216000300e00c403017841d2000002c003683d000c40c3c02c24811000545151905205240c20b440743c0c00030081c0a021200441b0b281c440b901c103600c01640203965501c50a01d041101c00d030098801800c244c0401c0e942e640c0d450900c80070350a0340c0c0242e08000d0701c400d603108a280b145e446030a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 374759037 1250 374757787 374757811
    0x6020d0c0912061d0604120f0302070b010e09010e1209010206090c210f0a030503070e0f0f040209030a0605010f030203060a02040f091107020a03050706090b04080607110a0b150405 79
    0x1060802d00e00d00308800300009040f2548038041e00c01d08581103141503400c04101c006862051415082507000fa0b4260b40c1102c0006856005591000307100b44266101c40380c3c0541600041c1e480c10a02e0000390001904040361956900100c0d25214030070410604031b100303881b42d000d8851900500185c18850300a10342d03651500005075100c6250f44000d0385082a041041c1c10360302c80d04901400c546040200a98110781e031260480000500d03820a004d144940465920080546407400a0244100901041940003c0c9140b02c8009a2030560080c5c1010a00a0308031030b410003442c0c07a020305440c001c1c0d12580ca61001c040c0c081c01035003424080300b0303130043d8114015490907280484021003801e440c882c4400312541ca403c00400c00d1407100481c0c0200f84c0003001d0070301039a100e00300709880300c010340301e0800403900e140d078001502c803014820b4500325005080505070943d43e07544c05543c04e0100d06c00004290083d804c2c0c0000161110b03031003038003440d1070307482ea2030100c6542c1e001c0c0000c842c005080920450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 374760287 1250 374759037 374759039
    0xa0e010f060302060d0504140f0604120c03020715121410081f05061216050910050d0602210a061a040311120f0f010e0c090408121005060706020d0c09 66
    0x3c4c44940c100d414a490003a4001425035550030480e2030501c034400601da49005104455001324000550799014a001e081d07480499000c04005450120410300001d002d6040200200076084032101c0c41c0400701c803282404101c260950720b80c1000c40f01d0070072805201852550522100501c4021000d01400f0003000611403010706090380c090b180c0b1891200300c25562548000b030815242d0b020f20544c2c8030300c10b00840e02a50522107041d020040140070301401000380344005400103001d09080800c0351000b80c4502c0000825845580207580034441e4000441450580c04c4214114440e2951040308007650014540341068140d11842c2d00700d070310710754400b0000c1c4018000309100e044141900901250241d0f0803140c0c5440e603d00700025800d8a02d0180209440c0da14030300310640142070b0105c0c003a425150a00c40520402c07401c00d409440252000106100440c1100000d12555030000c500c0c00001d05c04070760300c01c0080c003154802ca40885801c0d4001c61450100440340c000c0783c0d01c407001414515451 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 374761537 1250 374760287 374760289
    0x20406110c0a063c030c02161511030702060c0f010605010c0213050915130311070605040513090b011223030a1d1008060102150c0304030e0f090a0e010f060302 70
    0x1040c0511340482130503400f440c402e140c498284c19040e01c0f0100c00c0000741e61a504050043c2c020722440721114054000c03482c0305076100541c90305440c10303282521084c010400c141d0804441110312a5803404140c07004004803805a61204050f03c0840860350092100d4a0950752403401d68250740d02035414010b40e504218010b9580246400c50300c8102000055269203075040306260418581c0c031048141800002d0007030f0250750a641840781400f07038540114005030840c100c0c1d82c3c7c04851040000141050209001e0391425045110250703d81c1640072509900c181c032000e803c95802e90150700e00c0d0290703070006010030030100d4100b55850070240d064000c0c1d401f2f14807034a4892181e030700c00b0b000700304442c01c10702031441051084003015403003d07040348010220120081c2c4041c0094480ca409489190346c210141c0c0e60380c0c105503100b00056103180341113032100d0341d05545001e20320f440964400311138020f03003032261105400e00b88541702400c404200001007040c014211020f401580c4040c1d41446014005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 374762787 1250 374761537 374761547
    0x1203041a09150a020118060b03010e0309091503030f0a170916090f09050102040f0509090303041e03030f0c0e01090501050a08010e04050f0d02030306042d05041401020406110c0a06 79
    0x36440d00d00b0001c0342e988200ca54224010030f00e00348000b103411100e901500030b00103282e01c8028070032802d500800c04001c200846a540b4040e9079002944294a0380004001c0c10000846d900e410102400b206d04050070340c2e00300300b5030740c10038098080050360507841c0b1100c102c81c40100503003103984803005d0511181c480e2042e0005030801c1c06685402038030b07110301c0b0092162039445040002c2e04540215151501d9164103d019409407103900d10034820340c404074100e00c0b404022031b402161f008040700061400030703080b800c1c4045105010717001d00d07a494403580c0d0b0b60544c80c050141121411f0365800b90010b0040009000411540c02c480d04200007030020880e03140e0400811415680c450072614903580c1d81d494110f24200c6900c084600600810040388101038000010b18041d1004840600803504064241c00f183c9401000f4100d41c400800070700000400260300c0700d80c001c0c1c05071a01c4a51062103032001402c0e07a000780e2101c00096158104900c2d250414046104150000c80d12510b501d8905640100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 374764037 1250 374762787 374762809
    0x209040b10050301090503130504050124210c1818091b06020a0b090d0c02010e010e040e070611010b0303031609050a06080a0f06081009111203041a09 66
    0x1006104800101c0c00c008200903900c0001e2000030b00a02005040c0d2030074544036040320121004d048517500e17010400f0300c1c00340142d078183c8050f0400c051411600c0014803204540c1ca00c20300040c031980500d600c00c0031201030200e48101e2001800030441d000c00d0800280062559091507400c84581681800300240050b80a441040d1452021602e40050309205040604010240c5241c05200000103081500404c010900e03d006011904040d03985046494030384459000e02e00018420b815200015030082c001e901000340103161071030504003031074041402c0b16400b19110003154031003401000304517030044c20051140c825400910240340d40201082e928040500715600940c024180c84031428420340c0032000901e001400c1c903200d507607200c001515041c2c06944200c90141808016040030006000f000100c42d12400101220001d56001400518030300f0400c80d03840510460b00d901954a04050b00700d0740240d0005960b0711460802c0c142e1406113444000000c1d40014025480250340c0c03107460035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 374765287 1250 374764037 374764043
    0x80301051513080c09010816030b0c0c0601060914030304082e0501060f0306060513090e010212012615040303051e040c0f053003070b0906100b030103020904 69
    0x1890465440707003403942500802c000c40480d5815030070700041200740028081e840a2040e149681c060f6210510651039480401c4140031041c1c0a05080000688000100b6440f4101c031001a003012001d42c030850500f0400ea01a100040c0300540a0121034502d00c03124054000031130040d4901890039141c01d4480c002d9140c41c540f0740d0b90301c1140001c101001004201c0c00d10000400300400c1d82c5841018010014040d03c040c0007030b181c5140495141c4c01a421980c48501201c081d4403c1403408003000050000e819030007401c0e540030301c43c0c00440c440709603005c5e003c6c014002881007001c0c42100d082c0c1c2e00c0c840c1c050201810394441120380c02020284c0c482c0f2900700390580b03000b040c1c650f26081800020403580c0180018000e8510400090160300e4100310152500c074501c04034203968440401804003002c40182c2500c144050341c51082c60740000310240343c0101a81502d0801c2016142e2034507100c3c048600c00c005820030b60802c041035414003d0000900b0b0740c401d0003800c41d41181c0100d82c090000410003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 374766537 1250 374765287 374765299
    0x10120b01030213030b0a0b060c010e1905060612120c070e0f0601051e091c14030a091701060f060908060705160b0714030a020408151b0d09150504021c08030105 70
    0x1b1610320841c0c0d030050701d59110050729056881c40c0d0302d6004c6009146450300f0240e50700425654455000181c81402000c0e41c001d00208003648501081041a540c1c02d0f01040043c03140500240d000c0343c4540c0075121000c04e100103071099070b1903c0b200c065901b400402a440900d04041007040580c4c0003010713500d0030b100c120710005002071407040c101064410200955846080101e040004900400d8982c03201441071880f201565480c0d18403564ae4011141c0c1a00070400d101c105100c0d0200070580340700402c810600204030b69964680800c01800580c0125000661a000500c50004200441a000f420920f42035140c0544840040004083c3e04c2006103481e10044c0401c1c070491040300620003542080405550703a040410088009603c20f200d13600117401120309411003041010307030700d0f440360180310004c84420304020180ca19680c0b0800c1f030210b505070b8504000307020840c03540300d2000c8205401d000141030709081c010407442030452602c4143d02c02002e0612000296030600741da0445005441c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 374767787 1250 374766537 374766541
    0x150f120609020306151f0813020d06020c0f190b34050c071d06100504090e0706030f181202010603020607080a03050c070503042310120b01030213030b 66
    0x86015020580700070303516104100a024a0b03001c2840c2c288445e10003100d040182440e400c40241c00503803020f00300c001040500c4006441f03074004485028600b480200f640c80103801655440080380c1203900720300202e61019180011104e400c0003440c02c58811782984500c21900c55031400c1489100505400310800d007800712702c010751240c0f81c104d01c18118200440300b801104041c020b00300d0704407849070b00c43d0780b0030a0300004132001c07c80080541d078146052000001c1e6210b200b440f0400640c0c080340420010108000a4103000c0c40c07061108031300f01540a08010ba01d80742c401420f403900001c1c5000018074025500d1003808201210388943c0d03a021841c0300c41000019800d0b0f00400080d40080d40000d40028020200103800000306407030a4651820001e90b00c40a001054071f004003000101070340c1c0300704010b024080f203040700c20110307044200502c4022034002c4049038940703002c2e10180000c24003c0f5242000000140103a1001d01d10070b20b021414400a000f500b016101144030250400c044100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 374769037 1250 374767787 374767793
    0xf090506040530180409060b0108130c03021e030a050601031b15030b01021908190201020c12030604060b120a050105010f05180612010b040303090501030510050f030a02120c0301150f12 81
    0x12600100d844c0050003044041c0042c01c0440c040c18050868900041c00d4500150210040c8080110701075005230003811114116406e01c40c8903103015503030000303004080c40025a540d504001140e422441100641410f51461078401c4030041c0012082c0d0800c14108002e00421101c02d031052404201361a0101704d001d21000107070308085603010040320402026800341d0034491980001c04c804800e0a0030901360710301c040b408900700d024002c21156035800c00900c40349683c181001458220000400000d040c030780d14140d51141d50b002c481c02c06c00c07405100040001c0c81c00544242d500401c070a00f0415020301d0720100c000d00070302c41c1200300d00e0242142d0030220b102d5164070040c1c410030005900844103651710f5071f2504800d500709100480000d146a0b001141c83e5203c0d0103094084c1000c00b00340201c1c0c038100001c1080710741083c16030039094030501ca0b100e0056680e00510b1503c240d0458050710551510506060175194249010702c000040f03050100405580030442ca400c5403012103210406079414a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 374770287 1250 374769037 374769067
    0x140909041b03140a0c090b010906080c2b0b0d08030a020c0c03030301060309120e1f0203070b151e090403080606040902281b0b0a0f090506040530 64
    0x1c2c101802140b107420910020001c0050302020890007000a002450380d500700e0703003056404001c8100d0008102190411255010380002c1d03801505812800d81011074662418006180341c6c0b000d800c50b00c40f10103001142e098148203e6000f00400d844903071045200d5294002a0312010340007101541e800075500040000a114a0340081e4009040d01d6076541d5820004029052015017565000c1c00c10052a090a0240303242e1201c140340900b44c801416011240d01410744050300b03440d030550008009450004820b142c04600c586080300340c0c542d20300060000d00ca52071140130341c40da240d447c504039603950503070740c7c10316040c0e019601d850310045070742c0d8000c0420264000c55004118880c004600f05100d1610b00b95107a22214010400054101c0102001c450f2044800301e1810520054061180425000c2d040076500101e04100420202e0b403c145140c00c44040240544007504203c0901003006014002c0c10030070b1728003d410305032074910702418446920440c220150605000290898032250070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 374771537 1250 374770287 374770289
    0x3020714010216181b0905010f1422140303031504150603050417030c0d0903030213030c140f03062e2301030c121d0303090d140909041b 60
    0xb9000a0f002d5482c448040480034043c00c0c07002c114104080040707902c1e10680c101902c0c0303031303240c0d00c0d032030014034000065441c800520180e000300f21181c00c1410b1801c058400604c003c0124080c050400c44180d1440b800401e840d40050000340e0342e84054121035500042503a030001d8080e036000000e1803000000400a0590350000f0f4820280d20b54000f612580591140b407281c1d0143c40c039280c8030030070f03900030f42e44a210880e6100d28440041c007804003c181a40d01c03a40d07020b40300b81001403400d000280c005809010961080340c6400f4141404d01280e014003001c28900742c8251603a204440d6114002502c80341d00500e160710600841018a418000039400c00001c40e0b500c40c10088099191455118071b60441811098030340905243c1807915442842a01c2c50f51105039124421103000422900280034000d03154401d0081381c08500d020b03070320705100650180d403ca80080140803600306001c0e2641800360949100f1031001e0000d10a5600c900222300d520a602001660001402d0400c0c11a841d01c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 374772787 1250 374771537 374771563
    0x12060e0c220b0306160807020c04050108010c0905150405060c0a020d0609020f0909030d0b0a03062307050301030503090d080d150501022b030c0207030b0f0f09010504030207140102 79
    0x81c054242404212440c1a54140c5689501030100c2000142410f580341c078291034903000c0100c079554075211688200c0055400c0100c510544091342c280388005400e030340007a0071045c11030355965a181603450704000388800070001a501c281d10342c8804100f0405c5030240c2d10405000350340000d550a0700300da01b071001d0200154001c224001580d46030810b0310061414201c2240151361001c061000c0d03240c07403a40d0b180304d940c4690003907141152802040001c0c010004402d07805c0040b02d0f80c00310001b082401522a161000b40d40054004180d441e03060b0000e20180003c41030000810040c004528040125801c1c44009e98803100e14030501d2030005060301c41d500100745042d140401e480c0411022100010444000740d0071188a07802c150601140021910002d00c1d071241c0500c18844410b009402c406404880c6006130744100b65603840d4414034290480e800c02d00400200100190449101110b903004020031008004500e803550b0301940d070761241c0c0902404401d41c41c04040c000d82c0b082046040540c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 374774037 1250 374772787 374772799
    0x2100e0a030c050a0b0c0301030605010e0411101403010902071a0103120c0c0e090f060105040b0303070b0403090b070845060c0717010b04020c120f0d050f0601030c02060112060e0c 79
    0x64022540c5001f50020f00041b15002c0c209000040c90000b0150b8541c0103a0300301c030900712018900400c2003200110f44e034144081c0024143c1102c145d43d424400b45000381204100981d940d800c619000700f44501c08072482c010390b400d80d0011700c041142c590610000f1011814000001d25040c109000d108181c3da00c0159036821400c200410000089a42ca64415102c400c640b41c507600c03841008159034449400740d406034010701001002c0340c040070702c268000e030280c00e0410f0019200c419107502d40d07120403000e690302203001603861003201143c003031181c3d0b030300024035032800e2544c0070085805000d03200d418640a1540d015508840b80c0d40310012034642d03200010032600c4155582c8441074a40020008428142d441d0640c4014513003014000c9542da4480100941041495565001120b800546141d042010184141d9000701074074455103024508021064115140400005042e038544841000440d00544010001301803008a0443c03a1540100040740030030368032081c40d140421000090f58000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 374775287 1250 374774037 374774041
    0x24180f0305010b0306011a090613030501090503030103120504050105121f1403012307080a0e01050a0e062a09060c03130611060c09040509010f0507020d02100e0a030c050a0b 76
    0x480150b101d100a541c054003a00d0a41c0e0f42c1f5a80c0036200800700d000c030403c00c0002c10010705503140c48401011036240e0824101c215a0b02da454850845100e090b00b125180d00010040c800d00401810082c54108e0303d2414030f14060900300002c1260080091500e03000c9508000b0820080241c42c110030003c440034403071101c95a44146805581514060b0503000703519016500c4100070031718502980f1080b01d11b01c0c14041d034985110885e00b001e4010442e048150340c0d5480b0f0f00100707000380506c60244500c03c0000c581410b844245d1070600d18040c0aa420f0b1080e056000900304103000f56a02c041c1503a400429190f0409501080d0a88260000b04015000015042c18513411401c010303000e807080b560300c2c4520041508407580d03580505941e180203c41c1d0502c400011842c05410055118002100101e10309c4203048071314058a00641c0d102000d608030000c100e1149604210030340c00c00864100c02e004030320301c040d5541d8403542e1010700982004103055905051090404c00240b01c6580240350203240c2c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 374776537 1250 374775287 374775293
    0xb031306180210050415181202010215040506041112071502030c0f21040308030f04030e062b140f07050c1b31090c0b160b0124180f03 59
    0x82ea2040c0105001c6e4030603400003c1d0314522a03400791200108509400c10210b0414044204034a02c15104a04622074200415003a5040110070f030301640c411001824681170a151010382c64507500d0000d80181c9904078070603581400014000d0072142010310000c41700303e840d04100d003540301d0b405c200801441050018841110009080d810441d00c2c0c01c014080c85120b0b01c80d2a00740e1081e0300c4080d000700028004546030a02039003041c1e401a20900304603036880c0002001c904180c0006900c1072002c5000410b0f0351015840140d5180c400d01c143c1003c000d000c8080003110550072015140300f42c0800c032203000902c5580200225038188001c0821158280507100020702a03017640300c08203024113091445040c1d07010900c07241c48840c1c00c0300c410035054903040e101400000c01c00d01d8020b0b110a6034900c00001c0e4040800700410742180e41c0c054240b0703074401c43c0c14110584501a44480c4c807162041203001c0c1140c1201940d105003c0252800e012201c81d800c00c40120719049410000f05102342c01000010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 374777787 1250 374776537 374776547
    0x3020307120503061f020321150a05061e07021f0f0512070e030109151505030606060405091005092502010c05031302030708070603150b031306180210 66
    0x145520801007a0103404401c001160301d40400d69072a43c120034005444000c00c441703000d01144d00e0480b8411070b41050403444608070f0240b42c41c01500c00d1503046405000c40c0400c7c1030007040075440103452141c10b440ca40301c04210710b403040c4298140d0b03850074038464006c84481441100c0b000b0741c0041400000c1c03542c00e000c03032241c1c803900b07000000405c0072507030014841d03800b41081e100d02461100c0c15426940c0c491030251403e032400c2a9540c5d065583c0c0304403a0004500384801c190691f8480d8000aa41d0030800303054540140cac1c0d0300401d1013503010b202005131540e50801102c00751641952090382d691a108001034402c0c0d43c0b0381101d9401540d0504016112840586401505203040c9041c18408e00034001a401c89400102c5e03900050700410000f42c0c10a1449101044c0341c0c070240440d101c141d62a240716041070030039001440065180c2620700d405d00341c03950704031000d82400590301d45141080045160503030316400c0024005a142e00040a0f81120350070f42ca120150060b20120303200c10234160086c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 374779037 1250 374777787 374777797
    0x80d0219260a0507022d0f01060302030606150d0903020624010c0b100306020d1d0d0206040b10030206190f020d0c150e070303020a0309140906040504031b030203 71
    0x1810000c40014991a640041a0114444400051262550340082c0082d2070010090002e520035181c005503c00703003c0b071081c640b001c2507001050031004008545410201402441001d5a040c900c060026170340102c0c44580100c0100c50003810091015118202402005040300845141894980a054010481c02d01c10142601500c60500220301100280b003a0f050715240001c1506c514000043d80c0c264130030360003c19500841090a98981d500c80c1039a00ca522070348502074403a1000341f01e00c038016620000240071034000d4030080e0029a8001d50b031b41801040600840c5800002c910108400c0350030101842d00503000c9a07036107120440c01084510010030f1100020504d00504c501640b020401819084090b42e9100170100c40351501e8448050110001d10801d545560314445a14104038800c002c51080e005072161401c01c0c100a850f152250340040d0001580000012550f80d0350b40003580d1010044400103560380315410204d420400c004134040c00e0121604040050580004c0030744 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 374780287 1250 374779037 374779087
    0x1e070311011103190902060c0d23040605160206040513050601080c03010f030f062301080106080d050a031e0c03020702040f060e0610020c0901030b01180504020102030a0507080d02 79
    0x1020b40c000e00746562540388400c0302c0c10304410b01400060120300f401604a9850039000a1131207080164100c10b480c03c02440740382c0840402c0c14000104051502c60345070710000800408124181032610b000030784a407089244817100742400f0580c030411540d5210a44001d400c1c00b90840e41e0307403559540094004c0c24152603140c007240409001410036a88242280e0580c4e90041c0080f050070f01d95074404c0c0004e4084541250000c1d140d01c10300d480350071440304140d10f6850b40501700c400e551405203a0750868505420060543d00f000c115400c0644e004401c031821252545000540e0351400041716240b003842e02580c100301420403440807181903254018000d468000c54041241015140f501012107109200301c17841c240407800090312901e0503407806013180c8240d00685141e0f9040d040002d402503002d030003c440d1401210300510118001582c070100c03d0299540c2000f1a040c940c0010303513640100400c2c80104a00059070000f0400280142c622445c007a410564803000d024002c00c1f220030449000e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 374781537 1250 374780287 374780291
    0xc030702011d030d1a18010e0a061203080612100b0a0e040c0b09030a05060f04120c0b011a0904050a02180d0c090504030e130c030b0a18021e07031101 66
    0x601100001000e041da0381c0c5030610003c51500020b190a0000303440c0c2040491038108810440f200b15031103140b071030905d015101401c8a8298100700c1000803d040145c1075540d1680351078418054201c0312001100540d405041060b116941e24000550780303000d801c561340310f60140e1054000c90784065006040c1a54040b01e01e034141c2600c1d800c1c41d08000404941c041c00c00e40341204104006142c074801040008800740035070302650000c1d2919450442c054500c107032204445000c000034003400102c2c185a800c1d003883e0a0b1040d800a0301c42c01c1040c0300c1070080d504c5509034046030b01519103000084510081d005441405186810700c86e030b100940002051172441c1030100040101071034180c2030000c040c1d50000340c0e030040604141700c420050034011320450520035501031340c0d034855840703000c0400840c04050340400c50300281d4000800792030925180c18058043e00c1d1703051050a6000d046140440d031404001a21070041c8220b01d0702c080202d120a51140c40001150001c0c1a800000360b0701c12280c0743c1c02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 374782787 1250 374781537 374781551
    0x72109140d020f06010504090206070f050604020406052e02071502060f0114030318030c0a09150e06010c111807091e0312180b0c211201031e050102030c03070201 71
    0x4143d840b0030710154054020b0b0401c0005100e1460305600101c00a030018110500f083c1103079940400e0b28242c0d400660f410303400035040004614150103904081c1c0006c3e250f00c4040d114419000c240e802100310940c0740990b00d00f50300c1084500c00c00000e002400210f00740340d1030300720148001c0d49511041d945042001110340000c90f070004035109820301150041c0c0154034040c5642d040040b06510907460380c1d07050190360f4501c1c0d801e0f92400c1032203010300014100001c2211800078400407219950344003900c0f80b5008410410642c0e040405d4003540b44d00003a840c0c50411551001a402e0201c0081c4c0620f80303950a42030244c920f0307001c41c00c90160380314007840788807540610701c1c0e501c0040c9407172000400540410100c0b800c041c3c80b6038100301501c1c4030003515a20032034988642e42c0b9140c0004101c6003031580600980c10481103140c0504c11051804001c0c10b14002c0e41c00038042000030140800341480303010f546c2c2800071031046007004840030f400030021926810440002280d992054070b0807001503007804a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 374784037 1250 374782787 374782813
    0xf03031d03120a0302071a06040b01020c0a140f0a090212070206060a090c050c070b0d110313061d010f0203060f0907090e060105040503070902120c0f0307210914 71
    0x100c200e525200400038080310038103440b0300049610002665040540030302500000440382ca5100040000b201d400c00d1861038250180011900c103496aa411540020202045034a480c0c1c019000d035001c85610441184d1400c001ca07111148108000d5003200b0351880000d035048056014160038200320704c451000391030300b4104036a02d1201f9228294004a004803c0040794041d50101000007210304000d41060000048141026100e600194960f200043c0b021840c6501d440340002942c100e0016605504004011310035a03909240c00401d0fa941d961f00340907004102141000c1c24000c1348000303005880c0b03010500c1019402c01c0c1c90700d82c020403141110398070601c2d00c8400341c1e100d82170540e1594619498800701060101c3c0160031981031050801010a25450a0002901a1884940141e5030b180c02801d144411040200071880c010303c184510900c41a11030120394103d91646000d0142150807600c100c81810794440822040345051103460410080c507941e240d4409504090710101c52040b2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 374785287 1250 374784037 374784077
    0x9110307061e0c02041d010f020408070504020a09030b011403060703090f0b0a0e07122a1509050402040806070906021603260703050c06070507020604050f01110303010f0303 76
    0x40140740100310b40b90b00102c801818194a90480705451501110300c0c600d9801040844a10361140e400c6099001d003041c4407800240101414021080001c6140c03d14107040350307495401c0b50103070342c0c451600042d030005600e00c11005123022310303007244011b2210b59442200e0182e080c28141003d019000303a0000440883c02445017010094212001349103c0400350303101d00302c8020040040503010350310f01c264040d0520802c584009048510a070082a65042c2040040a42d124100350055803419441044011103083c40400701c4883c51040c40034400040c0043c1c07442c00d4683c000c00e030814400b00d00001d901d500050402d00a2030751b6269503464540301c20003244c0325140f41c500d1245105040100f007000a211038515201680f0420032030300c1981d80300c024401d90b0ba000344019800940041002841ca44080c0b02d455009022401d140c0c0c61318507d940401e446004600c1110310034503441806400c6a4065401c6c0415a02c606050304da40350784614900d510b0b5140341c00158001000c15404040c500055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 374786537 1250 374785287 374785289
    0x31a0702010b04020a05040e0414121b0a1e061806020403110d0c140103180f030809160902030c07020310051e0f062101020c011b0206042003190609110307 68
    0x6541c5c0360300e45408d091000f2a0b0340c401600458a0035000d5035080000c500500250314902880c400711503071860041e8400586404401406180390082e4045c100003600d00d019040640c0100040c40d40c4080d51400c040b4028030250308c524501c00350f5409000c0800046a000b00142c1e440f401e4001288001d04017031040e24051400c00074810b0f0039841c000c0c842007000c080c040c0c800820524020441d40d01d500e2032100d400a044400b160344d0446a8803a0b41090381184015510803800340c000e0500509084400d080e1007010312540c00081c0d070010129850031115001c03515260340290440315200107141c2c6080061008556114501c0228410342e4244004020298004c1c8011801040d8a0f1120810800070900095011140000b890191217800c8802e001900303400c01494000142818250001d8509965026071036085401c000300b003000241c160030001c0d00503000c1041c00201c640e048404649081e607401c0c1e00c8d211651140341c0c0c1e40204044ca41003200c40310b1241a06410f20032103c000d040e91071207a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 374787787 1250 374786537 374786557
    0x525050a060315090209030c0301020f0d050c0f0304032015010f0b09010909020a020102280806010519080417130f0f0812090105070f060e25060c020a031a0702010b0402 74
    0x40040c02c0214900301c5d0090140c1200c002c003582d0006050800107400c80e84401d044485605022039550007002182c40350550001c00c90b0710701403800a109000d0b98142c88028002414404803d00c1a0801178085c1701c502d4030050104201d805180b211004403203030703000c24811207000f64228040442d15101d01400d41d00c1416041e16030b01c8256080409040203500441ca0b2502103643c07c4c440811200500003200d0705000c1d2001c034100c205902030000409403200145410305203c000c02018040683e0305503540119466840d1251090701c0741d181051b5642c07900e101e4035027007010208807100e0011501c0050f90441d0540380d43d580307a0310399403414543d003605c40e40300e0f400142c0c002110181031406810020701007481d051605a1411880c1d9071100c0d5032019401007601c4842d603a070140c2d520140e0411070002c008807142e409c401c0d450300e04611181403140c1800307481e0400241c0d060000440d260240c40c800950340c80100070986880d4426072400b003610840c2c030b0314019030804c03981c4446403c00c0e100700c40e103003c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 374789037 1250 374787787 374787821
    0x91b03031b010b221103012706080f1015050303030c1c060b0307020c040e03090f0103111204021c03080703090312050f01090b0603060303090d0525050a0603 69
    0x10781c044901c00c40125407803140415500c803482150251348a00d03200f440742c4080c10408032140c42640c50f00c0100c903e080710f142a40b00080006224505a42c541e0420b07622800815008401d01ca10081001d00069440b4480368854004241c103a4140404c1c21007041d000d0040800c500b0103a40e91035410f07015540b0407103416810070008141c074060000b0080285400d0b100461280704040300c1a101241d80d01e074071184038140c0200030300603629418010080c04001c00c450a000316200d0455058680c030410401610510304050b1000c11a40690008036814081d40c0066484040500a40045500450b0228810401041519034103413450b110f2950442e0035580310402559000800d074014420800c003034060040305203000140c2403041c080c291080706030090518082d450705140005466100742e016100c0d200c1070041081030f460002c160780c1000e004907000169210b040c1840350600402942076408101c2e11081c80c80c03640c80c0603040e203080345c0c1c0980718130703030f11661322041101180e29801090140172 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 374790287 1250 374789037 374789047
    0x70503181b0405091609020a27141903112404231f02010e012d0905060a020406120902092802130504060909230106090e010203091b0303 60
    0xc14942e03c42c903442000c4500b01d40303a41c40d00031040c40100d1441d5000a1950380c0014805040c103071300440030320040c0000341d0981010b40f40c15646009040c05409113108030780c050303041d800740399130380ba0500e00310100c101000d118815100d080c14030984000ca18900d01405000101d800f010403144011802001c02d0802c03a81098240b4485003544000000103e06000368082d0200181c0e42c0d03019101c16172580d411085c40c842c94003400c081d0070f581001c0d81902407649030500381124810300c005d00715540007803654503418040c458000c2200400c1074800240080c0300b40300c200584403425900030700560300c454840340140d2100702d41c404196081c400e002504401c10001044100422204070b400718444400003407034031207444100404a07000031031044151948110200b08a042900c10300000e080c40350001c2c448100c883d11982c020f1030800b0303a00a6082005003110f03402140a50010000d030889a105203c456030348841b9901030740090b190109130b4080d00d00d440b54070001d00d014000c41120060080d500301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 374791537 1250 374790287 374790289
    0x3030301120f29070801170a080f2203030207090513081605030d090201091502030a0f050c01050f040b0a0621020301140708040302060c040f0302041d06070503181b 72
    0x1142298004880060510703c5901454072148402e080e00c40c1c20086a5241d0b1038200002407a02070103070b020b100c00421045034444204400701d590044140c00c450865a40c05040821404910039500d0003844c001001e030001082c0f90031505c0040843e07020303508840555445444507000c5601c1a54490f0100000004600008000700c003c1c107a0842d500062200a40b22511564250780c00300c034030700c1b4042d662510408115030300000e000001c0d1601325404170a145024001035070700d2294040c10020300c030b401400d075065540300d401296074904e81070000784001c0c00c3c6000d0480004405550490316a80b00000040c21030230305100d0070084a9030f00c600d21000d2001032104140522801ca004d0b600f65403602c604000404011100c10b0054220303544000b154601810028100310002d0058440010208010070a00040d035200c0030680345c04450001c0c40702d8988140b090905121a89104540540001c01c22402e800202540c414210401800e000c1e0100301135041e2150039078a1120245800d41e007018140b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 374792787 1250 374791537 374791553
    0x20405070c0212071502060402030d0e0d0507030303020a09080d0e0405060d0203060c0403030f081e1e10060909020f0d0203040c0b190f0903030c240c0302180303030112 74
    0x100c4910300301000707024410340210786401c043e0070b050704081e405440d0400683c0b12803a450749181e40c1600c041c118030304299000030388426400e45510708010071105141590b80d207031903000c2c08031903025080301c0300550b0f00c3c40c2c05030180d04404211000b00d1520400025002004a52405410003642e150440d940440041100804010b4000c80c1c110310811168001038504114903400740300d60140301034403141f4603d0003c142e407144410800421003040c051248099895180c2c10399210b1001a0548a80e210200c1c4450044401c00199521480605000d034511040c4003c0c01580e030340e95074035501c6a8a40b0341c054140d2007400d2807920104030400c20824840020390240d60014811460741850703607601e014002a507080510402c21003124600c00300b070700941140c640203840b40c00d0704152400d6451a01e02404c4403401e01d0300600144610540102003405c013201039040201190345c01c00c0004121071004009402c800c1400c0c20486244800030018500041624122151640c404400160958404c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 374794037 1250 374792787 374792791
    0x108070f020f010603050303061302120106050a020a021c032309121e100f05040f03050306041d030715062706150c051506061801020a08030117060c0313020405 70
    0x3107002e500d09400391204203005000040d4000e1300115140d061a00412101e8809003c5101782c00c1d00c10491481010046503003641103504604000743c0311400840141c2c10110307810402175101c03404407407502d0065000c5044094140c00399a842403000346088550004440e402d0700e4903040801808036518a20f00b018801700c0d0b03511030f0b00c00e541d0f80d01c0101d0a04654003030320a043c00030b03d421003041c032580008030740b158050003a80724030140020301f49521258000d00b1a00005000c04c00c0000006049494035000340c120f83c0d0700c5c56011850011404c241c15200d8204903c22140c3d0906901000c03075004040c040e08068420790007405001801e405070100c0400c00089600d2461901c404000a45501c8041c1c00301d0071910302d40710748500e1442450241d00300240182e00305c0702c441c2d529045c450702c1d4403410b05a9520507407000000b45118443c6006038038001c20103500800030017000001260140007a0001481503a24404440041e112440103001c6030100315280100311028181e200702601e0039800c055 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 374795287 1250 374794037 374794067
    0x1504050d1103030c210702090109090819030c120623012d09061e030b030109051c08010602211e13050102060a060614030417070507061d010807 63
    0x640707001c0280c00400c1c21034104402048442e007100054100c09010702058900600701c04a0092400c0f00550001e0600c65040c0a0075100683e100206e50030000d0660440c1c42000088040c80005000c80400030086c0c8900d2035850005900c46011380f0030103049008440a85202100c150009c0d904d201807210361081901c10981000986030031081e80c20304215a465101e244140340390030140322528040c02d0242540d02178010000501300f4a054080c1c51801b1202116043c03502107806401b44000038050f00009002915900031208280000500750035155044910303511000a04d07a6074090590304ca24004020310414510091166404e140c08030003070200b041920b041e10030b094410b2411401c01c0d041070002032034403122184144825a0104915a131220201358107010040c1840401040c2800812000c84000000310101e8204140c4d42e03608102840c0c4e03c40c4198441000f0705010790b170340d801446584086818050b51001051100c0c6a100040f0011307110581162900c2d101100c5804100e9170301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 374796537 1250 374795287 374795303
    0x504020613120c05100516020307090c0801090516020d0f020106030f0503090909012f040504020703081005030c0916031b090603060f1a0c03090d0c0905061504050d 72
    0x40107000c04070058140281a01c280791407158403040c5410070360144141c01c01d6105400300d02a0340c0d401648582116080003030070000000b0f0b8140da20200e0720700030140d00f203206e441c0d003041c90901d040340e0300c400301038101c1e44001d00a0040c0d40720041e07081c016041030043c082c016001141c801000600480300542c0007056840002001a9252181c002856050b20100c40035040050254001c0c900340e074489070081000300080101c5254140e8411540c0500b5980181001002c254000031004072001c1d1002880040c0c001d5554229a1800601c5a40100d5903816920104600842d2034180005c0c18201d095002e4260310068442c0640810510325240f00c131001c141d10b942a0360079082400c000c0c1c1042082c2511001843c0e800c0c01c40103000c1c1c1c0c103242c01103075a00c4440d00c0d0400c014141809241c0108201104140d542d158014013681540708241c401500100d58403070040402a1400441040311490310b010001074852004003c064000c0c183c440e840c4000034803043c0039519004800b0450340e0321440740 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 374797787 1250 374796537 374796547
    0xa0e030303040303020a030c17280c02160f050f0f06091011010e0a0c051512070203122a0d0939030b0403050307120906091e0503040905040206 63
    0x346554000c07038048001a401040050303c040e054040c824442d00c9a0805120440c07048000c81d91170304000385105601e800180010401100c40c0c801080241d48000040c41120102d40000e9a02d04950080c0d0034144848080080c24600360f2000e40190356008000e07446400c04a0200400e0046070080b00364807510030402085240c1d10000e00240b980160780b50040b05100146d030950031640701440220322500082c02c6140068400302422080d130fa4201c0d5413000300450700c0c4100003c0d004481041d03451214640a104c1a01e80000242815912040c1954040d41d10300f121612180241c0310808e0960100c7d400c0e440a075000d540107806084030321040043d035541e190b00e501001e52120b40c1e442c0030540b00041c100039a008081484950700c0350f10001141c14a10390340c1c4852030200002d0016080240101c04a5202c500c80d080d1042401002c44060020040e03e00340030008100b1160b08489900080e4072055459041901007012980c00c40080e6007003a1620f0302003009000c00400490b4072190401c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 374799037 1250 374797787 374797789
    0x150f1d09060a1d01050405160b040806060616140327031c02010209100c0605010602010b0607030c03021908190207210c240201060806060607030318061a010306050a0501020705060a0e 80
    0x10910744164001d50091001002301941e0341e480e0000d075082400418410403040c40712ba900010641d0f0000c00564080b03a98028500003c40c07803221020000b04820b4950340c00301c403041e6001001e000424501c49002c03082e580c51303103469600c44460924942c0c140c0c226039a0710908a000f41d03030300340d030b2907002e800054940400140002c0b10000344135500c10204800150071010b11003140308040c0900b8990000308000301c1442c00040c0540281e09009003041416401081014030a01c0502120035882d441000d1446103440e20b4045500909a1512900703141c01c09a810103100184400031140742c81c400004107038550100325140700f800783e0250303924403400c1d40008143c4d0f442020305d82610280c520780c80e403031889840000d0940e9007940c0f002019a105031b007800f41030b40e28082100c114039418200003414011414080903140d24130319010304091b14101c40150b040c0710003545150b940300e00341e0342044069280ca082224603040c03401090300503440410107000301d0a1490060028622a04050742c003001504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 374800287 1250 374799037 374799041
    0x10806040e030a110c0f0108040b0426030f0601030b061e0f0c150a020304020a0b030411100e03070506040b2d0a0302070c170c1003150f1d09060a1d01 66
    0x10681c001103080c0c3d81d00803813080c180b0400c50050411203090049580070000240b50300d4001d44003034008080a0003160070420502c075a21458403512054091400d041440080303940c10071164000d0074044d03000090442d41c4a4442c5400400000305200d00741907502c2620070405c80a18018401c84001b0003194071064182805030618510400040900d0001200c140c1d9102e2800303001551198010b2040c800103070340c3e1080c40c0d42a541681410b903242e0b56282080d40c0350813076441d2400e400500b07a0403500c92495000041e43c81400040d0100c0342155552002d000461141d4410a940000103004d15080b00c1c20510500d40e188501031120340b00b008a02d06c0301c1099170702c510b010f00c0100341c2c00207000d02000040c1085400615a1020400149103201c1505456988503049644100c250503654110a8040d0780005400206140000030650315250030f504000111300035030300309000c0000c4840000c044104514861020382c00540380c03036110008400701070020303040f00440e0001e403088400e0801c0f82c24 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 374801537 1250 374800287 374800297
    0x2150c070f1403070e09030d0903030612030305010302040605010c110d020d0503160605013c091a13090305070f02030c09040303050a270b0c040506040602030711030c0d02010806040e03 81
    0x200c4002c482001c40030b01014a4041181c0c400c05441c50200200720803241d020095549500d43e001001c1400c0045180403801000b9640010ba031100700d49101405042d072603400740781070340c0c4243c6040151580300c80054505040d5013200814151403651240100d003003029081c00d0562010f08001c035254250b60354142983c02004110701a0f03c8040c07010010301000380034090062490103246000c1c8205100e0010b03001a0780c02c0d0440c61890740d03140d54850242465040c2c00100208a020403c0100b101c20072418005203224044c4948220034034a11812094032440440541c19160249040b02d2651540c4c543c1c4810310041c0e0785070040306c9140d0380d1a110000810b104074400d5800154900e440d9039014100c80070b04000c28410071014044c00c0348038401203803c40103140c118030a10010395622100240b0351007160070082d00300d4404a0009940c580010140c031003144182101000350b850001070560742e8100344030b40c95100080210120143d402003c040740c01003c003078404645d02c0100c41c00b4a29503802 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 374802787 1250 374801537 374801549
    0x90a09020f070206041211220510050405011401080606040e16050c0115080f0c010f18120f020102100506060a03090f06060f0f0906182703080105090901050402150c070f 74
    0x1030404002d87c1c00101080c03050215000c003003007566400500c05d4566041000c21a00d43c1d41c50104940f180b211042d0b50082000a02c00d2105603100e0305885c1c01e98003184007680c01f04440001255092034a401900d065078108054601c0d141c2e41d0100b1f4804889052441100f0321030308021001c9101c100303000d0364024134030801c01c01c41e4903481c0c20300a625101c60061010b5154000c00d60725401703030381c0c41022450b07083c0051400503000c074070304c840c000100d020551010b500002e000ac1e01004020024041601290003602a04c0e10850380103108000e81d1400c0b2401640620104020006c5c2c9010b9440f0324a014001c50200d062001240e540340200c4059420645000c4101e032802c000000801c014000a880351910078410b41e03182420000d507460b010401000b0031526000041114038104120362200c40c00d4030700040140500381406400c04c2000c0c000c450140c0d00c10000500c1c0400c0501070607004d20740c0900398026400020080300c280d40c0100c1c902c0c0e40140141000010f140c0c040308080009086 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 374804037 1250 374802787 374802809
    0x2010110409020f09100f080408030702010618150f0f0b0a030b22180803011203020307080d0b091509040f061d010506090702010b0a030f0c18051b090a09020f07020604 73
    0x1c81030341008044880384010300c081185070111106d22552116616400561003002203071031b81c07550f03201a40505010b4006400c03a1a51b4081d100f9401d00316008411041210304c42000c1c0543c0f0340408100c00c1ea928043c0d003551002c4e44074200a0312000360010158a000c0c3d24001524240381c1c070028074151112030100e0554001c1d81080c0024101074481c6042e0b804e8852004500e44d0b285565018550105210b103915243c82c52000f002454004c3c01124801a030241105549400000400009100b01c401d202c6c02030300840000b9a9106440f03007800701c1003c0040c218106a903440d51040314102c05000202c0d83c9a888602c48100c0c0b0788610140d84000c011034002040c180323854028013015101c02440c26046a05207584480107403680781c0400140ca401101c6100e00210074200180003000c60b5000801600780c84240e00300f0000da5a02650003026903081490804c078a80c20000380e5030107078903105903110140f907004020a015942c001c003480c0070300303402040c203040c556000240741750030a0b844107040710 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 374805287 1250 374804037 374804047
    0x60703031505010203160b04060905010207031805010203030c0d0209010306050a140102060c0909060d0303090803042a03030504051e0406080706170c07031b0506070f2010110409020f 80
    0x2407012030141c0c050402840190b062000c0e04440c0c6030708100c00d100141a082800012a0500c00d054001d19030301c54002000b50343d100514603000740780442c0000425401d254000d804902c43d807010040300e004454950000e0b040c40b030300b07002c0000254000c0f221141410741d1104c000485481c0d0059032401045103032159481d10302007100190070054000c091500205003001824034903030350040c0c440e402c0602030b2000ea0b0014560b02d4282d0051901c3c0c000a040745201000b00010040f042c078028040c040c84035081310400080c4500340d292150720740001008504184000c1c09070342018035601c14003200d000c185041058919000c101290995000386450350044107040c450b0703680014040c4200708001810a482d80fa01e030701c8104050203880b000904201c0d01600010140141c02d0103440d900b50010161021400d003a00e024004104800000001c030b48101c00101d01c0305200800d41816400100103031480490141d0340703400514480116000c141818407004c540181184080c1000c0c402c2208115510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 374806537 1250 374805287 374805311
    0x327030a080a030b01050403080d05042f0a06020f0c0f0a1e050a0b04060c060903053a0905150901021209032703030901210c050d051515031506070303 66
    0x13031182081120305108007040100009926101224070080d9030750f1000460340c4580c40c00000540640c1400741500000c021030b45038100e03040b000300f81c0c9580c085030505000f507036804040e40c88082403219914a81c10582480146007480904407170b40350380007040d9240c0291542d103800c4800c222175002016040302502c040c411801c04103180310250400543c243d007403070f2070103900030601c04241c44010101611101001d081600032800da44c40c4140140701402c450345400b0550307030a00e1860080c40709008800100b0f03042c1a0b51071040003403050700800038109001c04c4a83c1810ba0641c054081c841e250741c01c00c00c9082074000b095203a07015030480e4001d035030b544071800710440244040c1c205010000e5001003815407035660000c110b400d903030340c2802d000509510319100c800e01c1d0702070840c07040c0d4881d081c04a00f0010036840801402c0d841c1d00a1010401a160105c441101005440459400c80035589800074920b041d44040d55200c5804244039189194900100740d45403c075003001c8011075107554000c410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 374807787 1250 374806537 374806541
    0xa0c0e0709180e0c0d0f02010f0908121e0a08010e0615180a08030a09030b0a230415110418050903030c09031203041a0702010903020327030a080a03 65
    0x5030041c5452011181000440c884400100d40d400301840c0c0d0790088407001d09018000800c82c1c0310010a82d4600c0030007070500259104903024100e000500d1014a0b0008900400d00381c81542d018000905920004110b040f02c950301c400d0071840079041007131060044611060041204032001e65554002d03502d491104000000041c000303901c5203403e249005031000c00d84007602c0c0c0000301d005940c1d60504080020468032841e640050340c4502000600c54081d0740c05c04102c004880c0f2502800348540c1d81d00490008a5208284900600030810140300103070403e55101500103008408084402ca1840403402c112100300d942011b140c980450f04210401c410200710244060506050041c1e00d401201d05441e0311008100c00080000400c819841d51410031128421400398000355076a4203203804c00b40b0117240e00c002480c48030341103c4001140248107009003600c0581c5070f0000d604114070722500002c02180582844149580c0a42464580c0d40402c0b4441000d0700400c1ca4654510050800400b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 374809037 1250 374807787 374807791
    0x501090b07020c0d1e0b160e120a060c09091e0b010203031506030901020d020c0709060602210702120604031d0d0c0509101502031201050406060c1209080a0c0e 70
    0x540d00710454601c43c035107a184044c00d541d58070030210200d1600a4031201c5c20020f542d82c028121000950403c69054440d00e02648030040c6501e42c0103604504408100c5050405c00a801054110501c141d0001e201d54004001c80704060034201000c136101c5800f01d00b281c51001080c6000c1c4001c1803188040d1303925100d285a00c0a00784042c51643c545290007071740000005480703901400c0e0000003e070022200390305403503014008820030341d51101d0000c0b0203039680f211801801c43c0e0504c0e094002a0041c000a210040d0200c00d54880e940c010341c188010505400040042c1d8003c802c0c03000700e900c1800188030440c81a0720940b100c1b1004c15219581005d100500c200b0346024502c85121003021800c442d141d4401c072401203504d843c007036031043c00354074040c000c913030100f84074000c11070401c01c500e50040090300303d0703181c40401c541b116a0785a0400054074090305c01c00e03000c100104035850200d622005000d00105090074801241695213000910b001c0c243c10b400d68100142002c1800804c1022119079 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 374810287 1250 374809037 374809051
    0x30203070e090405210903070801061401020a12120f0507120b0f011209110a08100e01051023130207050c040603021c030c12030507020d02060c0f0c010207020d0501090b 74
    0x529890903980c0d05550710507a121781c26105048264001102c048030003150940b94001e01034401c8903503a02c250078060086801642c00751008c40c401300140707501c0040c4c0040a0342e00030502405d050b405560580e881c2c48a9440d25501503200c000d18880c40c02c030780c040e1a01500d05540c400301c0c540364500c09a0201c1c1c00d801246407254800c5507291400b80e03840411004032450cc0d54000442140c503141500701709260b201225080700700b44030b00007402d02c4040340d400e50668103084103015040c52090010300b01c031400c580300003410005540c1071141c1450f88012017650440080300c08892084e01e000180d00018451002201c0c54000a107201041400d2144c0c41480d402950203120984c2144d0020300e8007103607020481038030310382c0c0c1c08050309141c410001c43c0d02494014140c08400ca440f01401005000222800005881109142040680700140062040000c11640e506000c2c01114260031680f168a222145640a002d203501582d40c1d60b0001071082e1103507000103040c060300c0c40c00341c51214008080f1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 374811537 1250 374810287 374810299
    0x30908010516091e120302060615030105101101150f0f17030405090c042417070c0201050a030b09010b09090c0403030e100504030f050609010e0316080306040615030203070e 76
    0x44a809604424210107442000c00700c81e0651211405009011080f54021540b502c45c544014061540125445010b003000341c4000300745e908103d1141e10648002c2c460150005461800007246030312030400242d200307001400111740601c0781800f030f21100c207840d0071101d0703103004500040045180c00c60422008156160306000c0201000001035100c5c0540d06c1494043c0c060f0500240d2190449000c4030b02a1002c0408a028a414143e582c01505002c102c10000314035070059100580c3d92468565200300720a65030400ea040840c1c0c01103a00e03401c80d01c41c52050585503001105580d4416450a010b441e0b0380070390b80d0f100c9515400b0491081e03401b41c5000c0c03000f40c08100078808a98001c03501903c101c0e080d1040003e42038186401c80d0707580701d175074006484005405641c4080203000b20742c60f4054004403000f402800300e00c10030107860b481221060b140e55281c107050080056060006954010401400011001c0e514851840b203008503590040002c1d40c00000c020740783d034002100070305509065840c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 374812787 1250 374811537 374811571
    0xe0601021605060901030603020910030c170318010203191110020a09150e0607110a05011d120f060c0a0305090c15090310060f0501080c030f16050706090309080105 72
    0x1514a01d0011405290300501c0c0008500341140d000707030003040c01541d004e0103500e503900d041c1e1151841025140001c5a4114180b41e00249100401d0300344241184100040c502e03000c1c40d5004107080781c07070b2048642d066010901030020281b4070012805000310040d12001203c2c21001200b82c00c20003a100f00030b4620784103010b040d00050388403426030103581001da07071052011700c038110548218403002035181d4012000650207042081c00c3e044040f90707010640d1624840da4480c40155407101d00a1400d00e840e0040780d0304924985131036400c078500e2100c040700f582c00f5246040c800c941000070072280180305050018030312565552621a00d0f6001c003401001e0160082c4110001d0402c04e038116200d4000d07080490010000da81c02d02c40176110703400060080111603601c0c075029517000c0c058400c507400b01c0c500708005004000c044d012240309810b1207007a01110307514105107178803c50021010cd41085000d106e403000042d0a88213045a040c0680c07103681300d02d03191102140c00d40341d0041c44240481d0071055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 374814037 1250 374812787 374812813
    0xb131d060a0e06010302010c03020f0601091d06070e04091103060108010504030f0309050c060304060b0a060216140d02060a1209080403020a120f0809010c081b060f0103050a0201120906050406060e060102 89
    0x5005030541c0c2d030908c0c00400c15015420101c2c684108100c40c514580651303000003541c452140d0080e00ca40b0794041c041f0f006050b0610310251103d0003241c0c04408510035030280e082c40e00e0316038010b80401b80318180001c40460f124000c249070500076002403400340e560f54180002c2c56000100d150060442c1e10341406426603959907a6190640b400c0018007500c0c02201080c20054940c0140700320703d40140840d5505170b0389003002035a50402d41e03074582054503010b00c0450044886424880c65a4010388100c541c10f50039400d0044903444140380388204a1003005502c0e4010150180c0c22103503008201c82d13525a4254010460000200d9000b200c0c00054000c0810001e418410240360580c3c00c0f0000300e0700c0d00e01550050f07401010f802d000901011000034a149881a54047e80700100040012070310745560309440d11035805420300000d08564000c244c9840191310410841110118045001c41c00281c55074404003911400c3d14200c80903503e916040c03000742d040d9603009602180901c0100100c1180d03103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 374815287 1250 374814037 374814043
    0x8031b060c09010507060f0c020c011101020f340606030506070306050306150307050a0b0c060c09130f060306050c0306120613030309140d020f0d0507080901030b131d060a0e 76
    0x407402c40e0601a02140300307018808580d1080c520410745000522404d00d904100940b204040b5544e2400f04076548200d5088100510a5613100c03000f140c111440c00840f0320920200000503841c0803212030700030b1402c1200754409107600da44148a100003103003003821890a6410b00d403009203070070101403400108104aa90000d11641c100c1002a252420340b03c840c4042400c09205400071a0483c41d030b060005104010b10300180300c1351500c042644c1c035580b0703500480c200034407880c00859880202c242e60201580503039800010294660744000884590701d69801c0b0664104440c2c0d40ca40c60004401c1103440c0c2820366024401e0211a00a00101e1500018900f0000c40c0801c010f02003641d1840d5140c10081c050030b0380a05411400d007218030080034801c00a50b980c1040407140c84d00d0050b000366886007401002514480d035070108415040403160401100180016802254030200012109c0c00600103440381c811480c0d000030300c292070520444055440c1c2680686408071040c50800348100000000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 374816537 1250 374815287 374815297
    0x12250e04020f090a060305031b1b060304081b100209092a07020303041212110606030703060e01230603190c030809010513060c0317100e0c070c08031b060c 68
    0x202c40c0d03003c0e5030f2100302c0f8020044c1225040108140f10001722500300a00010310400840c5d851000c6540303002880e00c0d05007103c070351409110b4114506101240004016401601d082038283ca200515107501003070103480c2c511041c42c0d864210307600088032745332070400800007580b00d41090b01c00008035010075942c0c6140c00c1c035921a8012908007080c107a00719a002d00c11640140b4202d5058080d030190341c1411060040c101500e40301050462602c204000c0c2d01041c40740c80740301c008020702074051860326488040d02c0000e5150754655620740542440740d22040c07034545c0e1881404d0110b0007616001080c94545040a1040b54021882820040029084880f04416030f80d0008005444484150040e80c0c41d001d503258291944050f41d00109400e0750040c0800c4949000350f564910340f8000005410302008151000e4000c1c0d24400070900248256403c481e4010350b030f60310001c1c1307401141e407120710810f40340c0e8000c0c0030540c1000078811039804080701909046a0810050a5107003010001d0190318031038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 374817787 1250 374816537 374816539
    0x42a210b031e03070206041403010c0c0b06100e03030c0105040506060d1515030b0c070c062a03020c1002060906060307061707030f02070501200405030706050912250e04020f 76
    0x10301840c03070004040c24404d071084541d0141040d900c0c4e0b92a003030801d140f01c401502d034030b000790700c0c0c0203403101518814144c0100b41c07174002c3c041c0021603d8000c18401000c4c0094035070400c1c01a032400a40550302d042000381400c0301200300008407030616217030540c1003ca0181c0b100340718040e030700359010102d003c2070031004020307800034800100300f4081c0c2002c03007900316994805048101c410b420800000c00380c03c0100b082d07512a00b82c1c10300c61030b100c640540d0006086040012480501e030840d884100c0d00e0300107809050b0003801146d11000c5100c00141c26030203800c50000c0180c00110500480300301c20032040da0010b900320050418181032100050282c00c540f080c582460301c150003c600c02c28040d5208000c04d6100520941d07503080f49080190281c003151070204c0192001d0850010742c0c107a01c0c03060390196403009001d030072442e1910781c003107510ba040040f80e20340c04640b0140015910310100072110240c5011007030b400c181400ba80c0c04d0a1600c055500807501000180c0400c4016a10301c1034182a41c84 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 374819037 1250 374817787 374817823
    0x60a0e090d03051b2209050c09040b03010f1d1c1e12090b041a010302131a1201061701061401110f10061701090809042a210b03 56
    0x5a11184e110b50491500038135040010f00051912202c02c20a1505003160240c0e008942c115031746515007400c449040f24054201d04007401001c07140d15054201105080000740046084000700c520706003113805001c44030056071414a80c811340610f0074031058008910305d0741e42c40b0541640319805810812130104070701280c40c405598066441c00f8218880c000c092001c4100301c8030f09c442c5400a4455001d80f000e8401c0410601d00024958111010b6810380c0c2e8050700c682c121003040c1990b40302600c01000340311360b01e488840742c203030840d01c1e46540c00060038040d40000c1540d40c038210301000800004030200780c150741848003c0c4020340007090006c000d10700a1038070000b030280d0541d45608000c8601108a024005c1c8842d0b2034800315142c00043c152814190500d94035648409140e00302c50010400404c503840c1440351042d285443e0340038950902075111251f0581d103040710b0419012001c44104000316861f04409045501c0c1c9040c030510071010351400b080140c00b00b9002a503101c0c0c60548001c0071302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 374820143 1106 374819037 374819041
    0x708070806100e10261005120303060d08070203010f0e0105060f090109050c09130903031103041e05070807090f0e06060a03030507081306020303060a0e090d0305 71
    0x8a050307207420f06800758440900080c41d145840c4103083c405180010200c15120101da86814418004010054500054121000b0391203811045c000c2016181c07180c048003000003140d03080a42114030300440c003440d103050320441c401c02500035090750800041340884525900038030b1006507500003d109a55170402032004441d1060307011a8415003000040000000719401130750031014240d8020300c2d20501c00c5c0401c50580d941c5c44407510441e81c03041c0c0c1800703150703061155010f110b030450401440c5042c540c0300d241030090b40c41820b00d03172a00305c4404c0e14200f10080141302c00a0039020b0641c4d4803d56a030840800078411401c481c800503041c103640307a15001d00403038031611841000340407040d82401c0d9101150701d034001d0002202c3c40346040164141250100100c03c0090030154015a17482c80d00d40c0601c005510540d0100340301465440a100ca4180b0200307080200c1d04103494001866 = true := by decide +kernel

theorem cover : BRFrame.Cov 374640287 374820143 := by
  have h0 := BRFrame.cov_init 374640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 374640287 ≤ n) (h2 : n < 374820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
