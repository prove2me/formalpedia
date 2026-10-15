-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4045
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:25:00.077992+00:00
-- url     : https://prove2.me/submissions/ea2851d7-daf4-4150-a4fd-e9899be02335

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 727338129 ≤ n < 727517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 727339379 1250 727338129 727338137
    0x80d140c030a05040804080714030712050d271403060601030c1d0a08030c0f12030105010804031d030106150e030625050f13062309040908090d08030105010f 69
    0xc010035260300308203603a400401440c0c0407a4544803820403000707600c511f4001034054001d451022844071200c0d10315141d1341d0015011509219a5a101ca800010305200c0040450300000c0520391003038400c0c401d507840700740907030848810700da41940c00302c030940c0d260340c840190302070030340c61039091483c09009403a4048000c1c20180043c18800d14010400d849010607060607025881140c0308586404d0075040c003402c0b0800449039a00c8000e282c80e695a64080703241e003110300c62034102104180540050702d040f0385040c1c40e9040c1640701d555050f41c030940007040c07040000d40031030403003d41a94240150401054803410443c01d080a9400c010030901c3e5818195020703034019004c1c84030986c01600010b00c200c1e210440107104840112341145d440c401c4160b80030355610082582918003118010181c101c0b80d86460740030500000d880280c507401d05128108543e820240b158150604060300400c030031a114402d6145425124000140840c02000302a155130740007000500c40c0f035030451010002c885c12810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 727340629 1250 727339379 727339381
    0x100912080f010f050d0314041212140910020322050a0509090a080304080c010504080901120c09060e0102030d020d02030108010b0306010b09040b011119030813021503060f0d080d14 79
    0x207070071010510b04d2142d1405882c0409070041494031500001c5850071005d54019501c90b50b5006400010b22030311010768942c440580345280d854002c90f1000d0301240c00400403801c0c03809180401c205046045143c006500082250003141c00074908411010220b480541810a044c881803013400441c07900114002c00d4500103218400300b00140032040943d00005099582da62071401d2841405000e480b1130b80fa6081c40184010000514041d100c0c00000ba6919610101a0300c056801d40b0180711081c408501c1d0800c044c000188107004c001c44211042c0112440c00700311402e0300040f40c2c0003244211500b0f0b4048010310075120203024140320070a080303000740841d50410360f101c21140b0807242c02c01e1040d40c1d01e03c0e10040ea07900030300d504d110b6010083c040d12040d60f2311440ba44100401c0d1070741180001d40100004541d502c5d2001d82000b0203402800c1508450710b0201380109075032002d8612a03206900404e00e00e00c5640b10680e4500440c440c1280e2078854469017080e030151000b1b9022a000484410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 727341879 1250 727340629 727340639
    0x90506011d0603060612040b0402030d03050f040201230409051008070308250b0109050414011806020c0102090301021605070608010612020723030901021c02070e09100912080f01 78
    0x302a600d039440102ca8942d0381e40c6802c000241c05128122000d4040c0000780204014487c00810040c440c03402501642c5095066a0049044400840c1c008403c1840600800c0142d441004400000a00300402040c0711100741210701113a0440e91114180b951100c00708140c0381001484240240718482c010413849045030785000560080ea5140c55265204032003851713411072110750344600e5980104080d20315584414840000d0304007158103843e0340e10304045034002003c1c14444e452860b2107200101411204590360303540650b00608190200e90340a002d000141e540c05e100600317400742481103284001c0071070b160485c05c102840e800807047c8107a05004101c02a001510780c03210080c11080181d49110900d441b031308110200706100e01c2082e01c44042c588d841e50000040110181c03d03001c541d00c40e00110006022112600b14100c0141c0003010304200d654082e4441e181c006e00014180c4045182000b810303000c44280b0744c0c0540c0c440ca0030500c080f05041d000300a5507040140c520011480e507042c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 727343129 1250 727341879 727341917
    0x20c010614061305060a0219061a18160302042301080106140403031b0f03030e10020f0a032d1409030c0a0228080601030308060328020111010f0609050601 68
    0x41c8280d5005610006000000507c284482455440c0c4079040c65200040c81c24028000d00e05c0c2c0000150301c480c404011003240c903212859044071441c1103020a4643c1d5500701310304400c400c54455030107054091002091541144010304421036084010303100442d01200010980d21069001c5020300045044480b802c241c06411201900c0d010704210f2a008020b190389001c0c1101500003030501084810110201980f64000c1a0183c0d00e45003101d0150010801c644124440c1d9081c0d0307030f800381c03040040c00c0c420360090b0805076510354110002c5189074205520a082c0071404000e4510581e0342c2d40d940451100c05429890b0807075016801941030092915001d07a0b40d4200307000291086640f810141c403807400c6001e000100c01c1c450b054540300b003540c800e192030b6204400e01080f40840c0010b00021800e0400065941074105602100380912030407082c0c45004c1040f16038180d041100408400302c23081c0090181c00f035242a802800510360b850034802e0b4086903c00f40a81e0f04220160104001003a10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 727344379 1250 727343129 727343167
    0x2010516080402090414010c020d0e100c02090402040605090a0e1c0813110604120b0a0b13020d27020901290d02040812030403020607092709020301020c01061406 71
    0x105480324507a0391968181b0302ea5425102d01085659070078107044058983e03001c0f4100000040c40c0c0ca845645030b11060800c00d030300030600710060014180e04e12010242c170340601140e40040c0050400a0300d982c4800104100d0b401c12220301c03010303a403900110341685008204500c1c101d1116500201a00030700f02d030040200c50041d080e00d52800f601c40c4140306105e039030700c0381582208000b841143d4030f03990341c80805151540a40d00b950403116000c0000c0c9808100d001e50700322203a000f8045611a1107290042000b07400040e0b031400038aa48030a481003a00c410700c4d0540180c404201104c2000b801481000281a4140c1002400b050021074091603080c050010304103035400c090b08a600c41c6603004401d8001c3c0a641d0044540b845a00d00440300400c07040d000354000c0340643d09440076541e641ea016504240c07144940e440b5040342840b42840d80f42034200d1480e1841412802045d0600941c0009099030064940381800343d5548504004400d8a203a00c404815000e4070111b00780301541400000c0500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 727345629 1250 727344379 727344383
    0xb03010b130503010c020a061131050307240309030f111c0507050d0f0c080a0210050103051605010e03030909040507091401090b180403030b1203030f07020105160804 73
    0x3001090300c03511109031807070310381c0a0300026008110244814200035518420824140d40a914006280d0700070402c143c02c540340003052900d0516600d900c0030050b10303041e0110084001400c0310740c101244940d02401945c0c020140704102c107070341c21402802a642403029140410900d840d100d546000070f42c0140c40d56655603614185850f034881200700701c2c0d081445000400c07810940603030094240603080710180021034082d0b011100943e090001c00d490000b660402d001c04241c42460f800006901d9070010840b4444074416112849a0390f0305a0051b56800e03002290789422600c0c0b6002254503e851140c000d01091078001c0c0c440c00c0c00c8020a03124070850304c169001e5100c03e4002024000204910402408a200104140541000c0f407035203059082c003c1c604510300b0000d40305080e2410415070304030942104503a40f029211070b0380c240d000340703007594509070803c40c5442d82c80c1082d5001e002131445800c200e4036036000ba26028400a007101c1c00103002c96400f1035808030610980e039121491951240d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 727346879 1250 727345629 727345649
    0x5041a030414010212040b0604020705030c0102191b0611160339062a03060608010e06090718080a0f050d0507080403060b04110301060f0917101112070521010b0301 72
    0x22302d4100108019119184000d000d03440000744400031710b00150b0003455900c14030b00c440c0040f0703845100121050991106990b04851400c1c40141c042940e41d4401d03042e2120300003440b40307008040d80c001042450180c1c1c0c1540032454000d05044110f411501700d04424205c1500f000d1008054821105041c0d14030001038000c1342e82d09a040d0060b001c00c0d22224684081800405007108545001009044140603541c00602c0a00c0001680c00d00751200601841d4010280b0b1080da440501c111201c0da10300080850818034880000303404803090085040b514080c82c466480d00c243c90815034901580b044000081003400c003c400049202502a13034192944000302044864480c1c00180141c00c001e2080e0311a003070004000110715400850354410719034103889801045586950751913400303058441c1e603c501d4201d48201c0340c00c0541680080744901c16140010f0602480d0210b091003040f00f2107d6001040c0001000102e8991304d842c0c1c4c8010320b103a25460100d56042c000c40012600062180003c09 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 727348129 1250 727346879 727346881
    0x3250b16050105040804080111041a0901090b030703020a110c01051e120a0f0b031b010f05070c15021002090607030804030c061b18050306011505041a030414010212040b 74
    0x120541014400c82160000000e01140c00d003170601c0d603090361080c81000071540c6088210307200540c154050764200c0b1168030515191800c04894201160300c441d18450400c104040041000840c01300076600a00f00c1e5540140c90780e01d5504d005d0550800b101a0605c1c5a000e080e40303408507a441805c44400003148c0682195002c0302144021550081510042800c403105c01004040c0135a68062161400d0081d8240044240342c401d05444424443d9282e01c45e03402100b445a00f0350095400560b5280a40b0381540381840503140e06080703451703c0d0800c0000c0c034808203c0c0a20715070304005081c0b2048040c0c3c41146400459000250385110f40310000742813101620000f0203050103201125000c0b40c201c84284407042400c1c00080000100b20718030004200481c140701880c2000211030b40c16218041d005040c1d0b42d080001c0844c400c0c004040200030014200320203c0c4540342c0700241c0c20315a111500c200e40324113145c43c20700503826044c506e5030f400760300c14004040343d03e2405503d0b54015400c0403083d030071303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 727349379 1250 727348129 727348147
    0x120f190201380402220810051e0f0907050d08030108070501050307091a1b0105010302100315030f021f02070810090506060108100801090f0209060a08030708220e0603250b 75
    0x40c843d040c1d04007170043c104001000400c4071000c13900f2150f030003416004012642d610882c1c0d03440280c1c00180320010802c0e8a00086001160103e082e4004501d10211004a070782c0d500062442e80c280700b4121030311003020004100078481001620040c16013402c00d00d0462078100c40080a0400501c600a1a1541c3e200d6080e0201030382421108041c024111610480540f007080038040d01d4280700c124007031002209180b120724402e209144041c0c442d00e812032229451134880b0385000003240b03002d80c1e004012101c581c0164820383c0d0031000281041d005016041c0c80c0040b1542444003200b4404005424000001c001400c0465841c0c0d2010090070721805541b0f900b0311180e403d200039002510780d58039100090051002c42500c06d05040d2007121451340564410003071143d062098451440b841d0b005100d0800024200c00103051120004960300742003821000001c1e840844541c040c3c20b420740c001303090003a50308080c4011300505088051a100407046040b00d0b40c1004038500c21b0400b000c00c04242d000e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 727350629 1250 727349379 727349407
    0x903020d1803170705070e01080a150b090f2e0303031d0d02010204170705100c1b140405070f0e0105070501150e06180108120f190201380402 62
    0x296401800301a03c20381c1114045280380d0104c1800c0d20140300302d00d0001b404c4180d9101180c161800600500b00a4020b6031700c4500c95540801c16900c03242d1500701c3c2650070b407944804a4072402c007001d01c01c00982080c054003221643c0940f498407183c1460960f242904c1d928955100451394189800254040d02e0041417050707441d0707400d44209501400b50742c401c6062b4150003074019210780000c0210640c45000c01d9960310842d80c4100b80e000240341c51990311042c00707050105540ca000310088154a06054490180c1d03482541201111940d401204455818588a00755105040d030404010040b091080580a00140c0c0c00203410007030006009001c2180a41001c5230f4201f8500003821003c1c1c880c1c0ca000c0c0d03188012550503001c0c5e04510709144000382e4031b2402c8c50480f003030f401c083c004801d1038405980b01c2d9403061790ba40955410030003448190f51055200c500e541081a40005400d4240c0030b002c41c1c0a2070b0704514075500c0c001c440820081d40c121080100c0c1c0060741100d0041e075410038008020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 727351879 1250 727350629 727350677
    0x50d08181206151f0513080d0807120b2b050109050618210d090b090c040b0d0510230117060c03010e06100918060f08010903020d 57
    0x15081000c4a040103070148000814900a051076a143caa4094080c000d2265040c494602d10a4003c507680300e8010050081c0000c0c81c0500304440810302a036107809182c1e14042e4040a140002001d030820001c12945c46000031000106c1c07404248061501c040c0007458580301410070308280b4001119500703403514000d4000711a070354000c0080c07190740c00381d003021034440d42c040f104d401014401c0e00d402030740d4200100718001d40391000c0841990901e10311004038140c0c0c004a00314030141340e0395805080440c0200b851a4481d0055800426901c10450700348026100c41100f13a0340504280e001c0e88001960100340c81340341003681d0710002a003401301604401c0c2c10b5454200c21020f03580071700000ca28012100d07840550064104201c03401c5480707055194070503100c00d1060381c4200c03810f2004900a841c10f400780e1143d1144c1c524000c40401c2d00c03031400506c00d1044039810074115580380401c01c03140303907400030a20080c0f40c140005c200200c0740d40c41c040e4460300d040e4080d204000200d902280d00400d041000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 727353129 1250 727351879 727351927
    0x13200a0906030807050606010c0b0a0905120c0610050613050d0c091103090606011b0f0f050d05040302040b0612220c030614091609020a09080307030e011701050d08 72
    0x14407400b640c03400c000659a125540c251614003c0700001001540141050000c16620001d0075001da603a0304065801081740510844817030103001c115030250340d40e01c405050198190030240070103003008480361261080c16440540111014020842d0032035055003054104e942c00d84241c003c065207403401131140883c07500075400d028984808020020b520501840c42910070303a003101d150340c40c0c0720700654030301201d0001c0b40064040301007000c0010b9034001004040c140300b03081e820f240501641e00c1c0307402c200107100e000c000100041410010352401d0b00800310f40f0b0b00d0503120303d441c02c400010700700e0281c00d00505260440840c11240f00a110707510002c21015a0061041c0c084e41c2e44904e4024090480d000f4805a0000e004001c500014400706080c400520341d08040b501c89840d010b038140c0039410200d501d400f84500c4e66000103140c003043c0014801c152096070b4100850041100241000300040800ba5000c103610005001036180c0f40c0707040c0c00098109406036203c0510740f40044c442d280c00c00c81 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 727354379 1250 727353129 727353131
    0xc0906081603110f040501080f010b040306090503070209070f020709021801030528020324030615010c0b04120224071209080d0f05090a23011515030513200a09 70
    0xa04ca000e01d10300790107001513410980e5202d6450716001d03ca00915002070003080084c96041008100040d080d9101c40d80407485402580d040000760f80001d13800304421901600070910405182e618070343e052040b40054401c21500b1428038a003000405240c1080040e0b9505150366940401d521007540d11900c003514501c1e0116841100d2002c2c94070001e5041540d01d01e044441d5881c0255a5000000800360f000070050000d1516941c0c01524001400308030025505000c1c1012451001c6502c0c40d24031403260340652040880410f00c03c0d002464030803102c14806810000b511070016584400c6401138002e21107282c040b204a0003900c80900130844404002c01243c00000c11717084008003078000b900040a800010040c9548905001d61a90a4690000c140c0d82000a28919000d069032281601c1c3c14424000229001a000761012010142c3c000178484442d280a40c26819454000e403980603a00f40341380d40c0c4111aa9440c155603000c0d041c25488000540d00e003a59450b1a1064080024118020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 727355629 1250 727354379 727354387
    0x10908070308040f15021902041d0a12080103030c0b07141b0f0d0f2105090f0712020a090218040c050c0c0303040605041e1a04090c090608160311 64
    0xb40c02042c9501034030a03800380c00101076000442281080d121403a04180b40c000e07101c40c402004c1c800e5030320001418103d03031250766016807802c010b12605208a00e4075003480101b1403003c03e030030247d02c04c1c03428801c24420000a030f8010310010ba8882c000014565000d40c1101c02c1d620340c40c80c02d40360380716001d01228140c034000c070b03d2001c2421a0051602d411102d107003503a4000003134031482034503080440b0284000ca4a201c01c1c407000548143c80040400680e07507030740703000e1b4060380b060b0b1415a00196075100c01070348030b083c01d605500c1040c07040c800149640030a40603400620f9010513600d8801d4030504589a034045080641903468940000702200010400c02800101c580058001d412000c030345200c91280040d050401d0074000308550554000f070720b40a04080c5010403d00c00700319a03510300899940c40540c00200c2000c0c031490268009000d548450320ba0b4100080c5004a070310f81d90314542080040c41d0104516a005000c1d41d820201c80740c1e1300b54801c20300d000240d01602400407168580301c0005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 727356879 1250 727355629 727355633
    0x60902060a030c170108300a05091503040506040b04141e0f01330f0e060907050a08040b10080601030c0303030507090b1617030a0e060a0905100b0109080703 69
    0x15005098041a6840e0001310301018022440404003d004060750f07a480006500d007075480e2907040b0010a21031b071b15031000d1442808211441c0c2d400c00c0c0c0b142c00200d18041400c151503e001d124103d00ca40d890742280e810b501e000e88171541d80301c4d0090301c060004c0c1c01203000b02d01400039035500e040b15040c81000300d5810300c1c0000010100100c10b04000c803480d000c1d000c1c050f20362030010f0248840c807100c19a801e039104614074112045e1160300a000d1446080040800100c516080703a494000f000c03141c414043c10f180580900213100c000501d036404228040107510041034200c3d035200d0700550041d00281160b907940c5000b0341c8010254101040c0340c880c0500000800004020b0702c0706891090760180500d444800d015920751401e4010310081b07000c2840140841548061144489030080c03e1943d1075004150b0107084035032080e56405540da44600c106114800200507050700b01b146140c0402c286001ea840c0ca54a074114029242c0c200c2e51134501c1c040709a84103120074009082400140e038901542c034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 727358129 1250 727356879 727356881
    0x509100302041512080c0a1b050a05040509030307030e030f12040606050a0b12250c05010e0c060405130605040c0c050f060f0c030a24030b010b031b07060902060a03 72
    0x61104922860410043c14080f0602c2a000303422900c89040749110074070750b40c0e18460207030056441950342e40304d91050307000400d030a41010740138079482060304c031035450030042485880000741c2c0103a80500d0a15060200440001003100c0c0e00035402d160001340030008a140b44d04520845e5113486030030740045120004490105603d502a91054108009141d55035044c404904042d20400d40c140c00180030001c070483c0e85000156110200c001c042010907100d140905141006805000c001010350301180c082101c00d01c00c03043d030703215960300a00315001a900000d400348200d0213002e000e80254218040d803113203260000c00103031400900034407811025410040c200a024901a1864070401e04030500480c40030a80d42d0061030441c00720003c07651000030050040c3d0010b0000c40340f05035291044d0025100c4104038a500c04a000c041207051445d60034040b241c860180c101c030740c444000f0030500c5010301c0304c0d000418103c0380ca0040b280e00c0c0c400c1d030b04200006040c1c00700e01075003203a8002104900c00b541 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 727359379 1250 727358129 727358161
    0x70201060608090706051e3a061a09010201020705071706010b120c07030e0a060801080f060606090f0d08030a020910020327060c010e0616360509 64
    0x101ea612064556110030002d07650700ca40744100000316208001d1046144140407011102101d04064680b810b148403080320a102e0b1040c1102052084000340646002e07c480c0b070840741c001c503454040c003001c2d0800c4100c13034031846030642a0050b15400204c0c0d2400d64000e4064a90003900b1000766644140d0b00c004070900d20b180045e00106170300544c0008500c045903541aaa80e6030030071902ca003078580d03444041c3d1302c095011103400d9062006400d555249030399241629009000e0344c0d03640c00419450158074601e0a4007603d040c00303c54014908105041d21290141c03400c1ca8000c03a008039140314114081a0700801043c0040c05c030310400001c200c1c100348190000c0070348560030b54499400311310003041240c40c0d005002c6001824000c0002600c0d03607907501c4644682c241c500034005844c0c0315019480e54215030402e280e405068001e5810442c141c4081c1076034403861400e600b45003a49005020002c04941d001d407a4503000481d01005142908460000384030203008058a4582c003820980920205554 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 727360629 1250 727359379 727359389
    0x907031b06030c0c03050304022b2d050a060207030306081b150909040b0c09180405010b0907050a051812060f01240c081210080c0414012c07020106 65
    0x10034074510060041c0719030701300300040744c060b52a50f0550300c0c0d40c0d003002070905013403071003e070a594020089148955001c0c804e01c0c8081c0314242e102d4000003070748264240e9180728807402401088280d000300200750003060072801a5030003103005aa5a4482c601078006004c0c580140790341c0e04c81c44a4040d0715244501302100c8a040480307007800c6050400360130280902c1002d0b00613810811580c0401e0001f6108084941c0100903011700354142640d95012591491050204000e56a00107082c4000c1c05000e1041001045054904100754a80a8800f070080d00c1801c48000800100049016103010103520118110200515404102d100c040b00d071070303686400380d91000350300c4045000018881c10f642110800e00049030941e1060980c0079000f03582800304440c00f40c4070305104206072000c601200610758072a2140fa899440074605140c0b115180c80c885050640c01a40b41403901c4585d2001c9491640c1150941c080c1498804425140d1300d103400904282c02003203030141414010800d8046d0002d0080d60 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 727361879 1250 727360629 727360631
    0x1508031b0c011407030e04020a090e010b1602011d1c0605150a05100c080c010917070b0a0506120d020d02010e07142407060603060e030c0706080907031b0603 69
    0x2440d1034a040d1141c850710841c50100f1000c110702500e0540c040081c003002030003410507140794151000460140ea00078411400040c015a000f8002e1042c40e500b890b015200201105041141c255005413828405010190510202012034026465100cbc1005003c14028028040035440b814904240e0203408100b1900e041c14400040c0c146c4605042d0703c4d102410042046001610300001e0100340200b00801c0c90030483d02d495000d011400d04001400d02544160000440e841c69040c01480305030b5100b00440c142008002c0c40e000308009000701030b04645080000501a110300d0009180d90702c1c6040c0000041c0184800000d00304c0d00400c1c80340e804006d40d0024032a00181030501c3c2c0c1c0f50036150084420360420303885e2510040c00e00e4062140e8030310003940c409440010588403a02d041d045000200d810715104c8400380704000c0c070b40c040d01380c80d500c3c1d1000850810188002d2961144442e00404c0100110f210000e0904601081038600554014900d080d49081080a0110080e500e029240100b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 727363129 1250 727361879 727361917
    0x7120503091f080601080c12091c050f04030809040207060e060103050c151c09020a03200a03020306060405091222150807050304030201151805090303190906150803 72
    0x5842d51002d20748039016981e41c00d110384e90340038015a000d140c050212100321b001445101103031102400d01d14000c2101100a048200a1110500c44401070140040400c102405103c5103041e03010700f46c0d030a0342d80c4842c6258444481002143c000d000303054024000f030b03043c000701114145000c545141640c1c041c0c0c050343d00d03110f406400d20800650f0780c02504c00b020700403c428000101401309801071041420710200d40d0f580c86800090001520f500281c0342d00c13008502c0c0c100c141d4070700c9881003202541910440320b1311b403079a00082d444000040505002c0c503103c0e8000b900d060410300c4003d550f55441d5030855180d00b00d0491491412140da00403040c130151b03103240442c50007501d11808012188c0340d40c1c1c01c1310654524504503400d404c0508100c05541d00d604001000a02203142c80001e0200040d0700309544001e82c24842c15140060070a2200c0e400070014401440940c10015180c2080600c0100c3e1100d0b40c0c0c13500400400202440001980c44143c0c0440c00d902c011008040d80c8420300c524140c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 727364379 1250 727363129 727363159
    0x7050607020705010c08091c03021c030504030e01050307020a02060d020418020f0a110c040f0f0b0d030905040c140307020705010809010203151c1202010b0112060f09020702030712050309 82
    0x2a510b050f0140c540441d800c000c00030002420580240310095016002c05007510040d0300440e0302e0310b0043d0046001d03810100d10301111503150340342c42d00c460303c01d40380610282c20940c8010345003000d144251410031000000042015008201d008c0c1066409002e5941c0c0b1249014103200a40207070090aa02c04080990314403050068000e8a0a8000d6161403d04d00883c0203815550150b102001781c07034a00804101c0b00c0c66a0b5907101d407054600340d141e004110794810026000859110000c501c0c429060542114042a400003826090f242c09940004929014940c1541d19651090042000100000070040c140703901243d044100e42c4282c0300c114060301c44042c82402c0c0d001c22541c440015910440c4541c00c1e25005084074403008102040314004041798403054a090b11203044840544e4403409400150b5034488150b914000c000503040080a042010402c82030407180700c1d40059940202e0750340150342c0c1c18840b410007441007072458540e00700c40d482c01c00c1d03c0f900a240084d11450010607541c45c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 727365629 1250 727364379 727364383
    0x603031e02211e18100c0503270303030403090905070207030c120209061215060d08270a06020c060a0512070909060e010605190915020c1003060b07170706050c0705060702 75
    0x4e108125503c6400c25950800f081c4848036244040680411203101141c0012907014002444144206003814503440ea49202c0b20b91400030f2080c010340683e00030030070000400c0c2d1211055060b5a40c4201c041195282c07400101e2424240b80c00103050000101e80009042200e450280d00c160f2090b00c44210b076948030020050615100c400c50095034105030341c405403440c200a4079540c0200300815030700e040007240e180c44886800c0502a00d448400188408403440604c090001200004a6415050b41e00f4148000d465070b028120b154020348010928038105809030065641c0c04103064100d160300d25140900a1018a00784541800c2e989400310103e81d81c840c40e400c1d1416503a45803201841cbc01818248500c00c151441020410000481d4000c9036018035071000348480c241a5008145180c121300400211003184180d060525242603810004410302206580032940c10403441c451446614036013030483d00c14024020152407501c002c00c1841803034100500503c1d405842107520540e54008141c1e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 727366879 1250 727365629 727365637
    0xb030d2001020313291501020606060f0d090c03020405041b0b0f030f1f0807170c0306010e070302040e07081504060f0b0903070509150102100603031e02211e 69
    0x8011300d08203100b108046030318440ca8154002125042038071400c4100d0310315180c840140c2d088845584600c003803803029a4100030f0280c001c2022240640350072520000c0300d4040c8151180440e0b02520749803c0e4092241100390400103680140003442945451326102450500c0c901d58003e20002c0844040f030440c401c2d800b40da2030107000005207031540d01c0303c403403803441c12100504500c2c01c46070031010324078148a40c0e03240d0760080c440c0030b0007000d00390300301280e00d840c0110b60008011290301042c1602665500052000e0450745125851a060344034000c04a010348610341080100c4003001e402d20000b40d52282c0700c00d00c202c0148090180f40c1121808120a542031403140074600407040000380400142c407001048050310042c201c2d000c1c2a0750b2800302d450310004464510300a0145440002156014002d0300b07a02c0c01e00840c2049420b00319540070300528000346264144400c10054181958000c00010004007105000c00f080d0403813680d58400154481c120200c0040301039402035403544a02d0060b2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 727368129 1250 727366879 727366891
    0x1e03040b0103060b0301020903070603020a0e040e07030809060f04120c0504050702100e011e020a1106040302150712150f0f080c06162f06040312080405010b030d20010203 75
    0x14403034503440c5840398006410750503841980b55500b00141030303d550702040742000404161f02c000d62140c1c0342d800d018006000b00c18400740545d080c039004103c0c5a402003071f5002640d51050101d80c4a0341c81101207001b50041800700d00d0720070000503011420307030399103201c140c0c603688075400024900c1d444000344010b45406452180c050383c03210f1045007119080d90442c1d245242c0a5000040060406000c4002d000361203a41d036580c0366000450345441c5502070f03074000d50755076080024189401e00341e60007175550103051130702c0c1203131054080401c3c0781902c5000d0b02980c18121031014032000b00b6080f04042d02c05094481c4104519440c02c00054803110202460f01700c0b20f00e070014218000141c805d01105500c52481302d075402442a110701c00069054905049841c3d00f005e43c90080d08030302c80130703800001c030703200d8031a1046505120030000210100720504081040e4600220329880350318240c0d0241c014045c506030f140c05080241e050141e40029469010848440d08000c164001081c0508030302c01680c007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 727369379 1250 727368129 727368143
    0x170c030706110a0b0613060e0901110702030a11040906020f180a1a030903040e271906020702040b040e010207020103140f01060c08041a0c0d0f411e0304 67
    0x19040403a91070640d890303000714058038180c0703182800b406e050201c51191b000304520384596010b004002e0001d2103150141081c00000c203141008980010395180d44107407009012405900385c0c1d08071900c071900498506548064295282e04c2c0700c1c40040c400d60450b80b84420748031040d03c40b014241c42c0079000201141c240d18101110754002c19603184c0107070b00040422003544010000090041016030640d0b12418140324502c140c004085445010030f6190f1060004030381c4100810703032152803480030812005070302c0540166101e0051001c207001e40308000d4803c2d885171500c0c0043c1715820064008185052003607904221100280022041200301030300c0200302800540010701000c2c0c01000706400f1240550798140c2020340d40c800e14080c80d4940e0918020815010071700415801c0c0411841d090303101941407101751003038810002400c0a00c846200c4501d181c0008582e28060000890901c21080f034019886800003242802c000540c8980d88560b0840c442d410346800980008060328095540580c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 727370629 1250 727369379 727369393
    0x3150b0f040b0d0c08071805090304050d300e150403060213030c1d0c18010e0d0821011508060105070303060e04260f071209170c03070611 61
    0x30611008103090600c0e2600818108014404074290f00301d00001010714000929480703081100f041040c0001140d00c105142c20030060022400e004010340703068130001c2e155020140100e04080d00015048000449090010342058031500f054240310111154251210001c10003e1000c1c0f15a003030010078070160240c020701c8140700041c501c0e00141405d0b0700c200302080426803280c840d08a001a00d40c4402c03540048060f24140001e02c0d0880030368002c540d81d0500f0300f0711060408650318480418410b40c1000b83e100c0f0408810390355241e0500c0300907045420903450f054004264103020f07240d20a44054000d0410001500218480580c3c0c0d0603502030f5560049911a0001550560001c00e01102850303260740d00403031030003036510507240301d10301981c0d070300c20a0506800009100c064050403110f00140801030000e04110f032208880c611035001550f403a980c1c48102040300e10800340d0b000702d00985504120744001400001d02401c80303035021410344610301c0e510700c81900d86241c000c010900d5604205 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 727371879 1250 727370629 727370659
    0x3080304201c030201050c040302100c05120a02011509020319091109070e090108120403031d04060308040e10051305040212060712050f070915030e100603150b 70
    0x80800c100c0500c14004611141c0103100082ca007880319180c034400d0110400c1c0590203141c0d09002d500c0d00050300b070f402c841c5084d0130350b000314191241405600341800280e544090401404100307100d4071580720324503541c0307801d40c0e50002806007964000803401031000c00c002080b0304016100b1213000e8214402441c082040c4e88100d10054014940244d071101ca205100001d191102001244140c446613106000d1301206400c1020701e58041c0c1026005a220010800348a091401140c0a490f01824400c17000707000301040320505c5c142195a01e070072500380701c170000401c007010025000751081003101000300d03510749100c050302035180d00c40d0960000584ca1208049403140e4415070700036001606190841005824517031030000309840503c0082e600c1c4c4070701200d4803698842c0f242c00c10040c00d89a41c05050840008040030a14001c145040c1e0154184400c0e4074046e52200309520019002c2e10a52100910aa8000c00440c4016501d80307803004900c007120b115a1140306005440200248000b403603c1d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 727373129 1250 727371879 727371893
    0x14040e0304150302070b1e0f090c010c050f0706020a140d09030206090f090f15060405280806041b080f1506030106030f0507090c1707030b0d081308010b030703080304 73
    0x10b080d2041410340c200a824017040803480254851090101c42034241005050010f03019000104480c3d041d04912041c0b15002c080494600280c0c542403030840e01504050501905180c0b04000200c0c0e10702c107500e40029400d4020800b008514003e8100c01740350045e1840103621b40d280c80c0035400c002030350443c0c00d200502d0164040c01c00100003601640c0c2c01d103600320100e00e91700410345d00d90500c2c1c0e00380810800f10614100d041c0c41e0040c0141c442030705003898031340070590140ca2460301c0310b441b106400d1200d80c0d450f04514418010b0650100700d503a54141070070800071020501c3c14804404003c8200800c600c20b000508210303424440c07000340601c6480951302c03010810f010707180348d0381075494039400030109800c0c0c00d80301e098501510107080d5051400040104a5218500a2050003440611100c26074100300620341c0c00794443c2004541e03001c002000a86916a00c80e0003421000301050740c2c0c444003403c1070000141d80103030000b048021805000c05540341024800100400c4082000900003060f03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 727374379 1250 727373129 727373159
    0x10203070309060f0507060e0a06180209061315153c110f010b091302012715020604030f02031e130305120c10060f06050901141314040e0304 62
    0x25150035806d064076580c402d0240e400000f0765501641c0401d00d00740900000348145014004030b0b5a00640f200c11076030214050510003040c880c42030001c3e01c1d1150b03944071a60003030303181500f00c134407040300d030307540ba08002d8400701150083c2c00006581c00f55038015600104840b1020140034240003080c0751a2002c1c80c0760701c404038190301810403540a884d18001081000300c8544164410008503240030f1481c00c0c01003144000700010398200c1000d0404e40942d820070100040b07450600200c0254103880051a04008605d60005c0d0f803000103030203242d04035540894414041c034440d603105921001c100344101d80d81d014880080c904080090b07078110104485100402c20b141c0f14268a1a247e0b46c0c90f11001d05200400041034041400004c0c82842d9503001d020280d0300030200c040c104041d900340b001c0d00607515058020041482000658284240c0c010011083ca504c0c41c0c0c4d211a94a00c1400107000001d0401e20500300c005060345110340891070303e401100103000d038400c0114142031900c1100c00716120 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 727375629 1250 727374379 727374407
    0x10020304050a05160f090908090d1a0c0705060a1406010f090302030610090c171303030b03190507060918020904021308011a010305061003051008030a0f08070201020702010e0f1c120e01020307030906 87
    0x80c01800cbc181c0c0d05c2543c220b03030500c0703840030b44c0c80543c44111a06025062410003444400c12074a403900d02980001b5806005401c88000c0c41e002d10014081d13407083d0381c10300c83d03500069031504c1508200005441c1480b045425600701c50340c01d00c10100c41d144282c03113a19010300c4017401d1003150000144122200c1d105002460b0191402181d0401085c0101c3c0c204003008440340d041000e600e10044c18400704101d81c4d002050742e4038001c00100e18046204040a589400c2280c1c0c058000641c1c0b4070503500d90b01a54071051456005072503c9554400c0140244600d050030703040701859003402c51181d802482030340e1041d0b00142146840c03084840046000308001000991006503420b00411008002c002510056169443e007120b601d0388040003a0140c80010014000c5a004020b81001070340d11100741655a641950044d00c40440ca40000301c1290500000648072202d0480c034100f80300050480039400741c9940c98004042d203688004a8a0f8450001e015010a85e03041080107042e1240d1251070b8841 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 727376879 1250 727375629 727375643
    0x306090a060b03030706060b090a1710050a060b0c070e0a060302011706030f03030403051305090103021f051606020409110909010b071a0708040203060109050910020304050a05160f090908090d 84
    0x20340961b604e034121152900b150450344030204202d100c0d401c1560000c0050042101e00005c0441c1c6d07118196520100690f044178056120b0000c46d9422905030401d501808041e9541d5071182c04a1960555484080c031510620742c1c82c00d8041400b103803d034031520050300c0d01030f520748104070038a178084401c14202a20254143c89183c007440002c8805101440c0142c0c400c2d55a2a0b031440015880b00f85c480c010340003d0310030044080100016901c450360402a42c14481c00d034007461001c8402500c40d40500818805035406054031141040f215600400c1594803c04080010441d00b4240402078006d62550b150011b40b001e00500001d84560040e12290340b14580701d0b005501c10a0310b81840c03110681e0801c3c00305948106100840c03078244101805088501010000c2d0301e072205200b552100d070800c00304a03455001000c00c1c180032007404a00d41c107942120803100a21380416040c440c004081c0304030040342d041c0500c0800d442c0f00303a0190080340c0b0742001003141410302c2601001425a0b110030119028 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 727378129 1250 727376879 727376887
    0xc030a15120602070c0e041a061807270906080601080a081b07090219020d030c0503130203030705010633020c040b1c0c06030b0f0904140a05030d05150306090a060b0303 74
    0x80c00700011124407ea11035450440080790f00070b039080300703050050010b81c460b4155040702e074900010701842ea035006406241450042690002c0180c100661480c04014003188000200300310f03400b03410082c100d816500807210740340c1e60b8a500e50745070701540308014000313901000700040c00240c01c400e0108240480c42620152903480307815501700d0b03120725003900341e5009003119020340c1034040c040752480001340d04003886480c0b0365110007861448000d003003510034001411301c0d0341951001c100b80c50038658843c008028080c1c80e0400d481a0007080c1d0004c9081c4900854485d1403015544015503891050f07400901c1100f8220701084040c02003100126002100e09150080c003104040700a00d070070340103500c04090603003454001010740310080c03002c41c0100340b84d408140040c1c552002c40390b480340e0030042c203030345c0c0503c0001c0c068106208424098510300c0042a00c0d0500c469950001d070042e1000c44201000305041d00505071074030811580b200b03660300b11080b80008103140e90040034075940001c05480c60 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 727379379 1250 727378129 727378139
    0xa0207030908030d0b040e03030f0103120c060f0603120c080406140702130e01060f0f0b0a0302070206131e151404050604090b0a120c060e0402070b0c030a15120602070c 74
    0xd10f40102542c040426110170f00a0003034140b80c0300300722081c82c0355005075142d4604541d1285c5807503c1840001c000407040800901500c0c480c058100e1141d40c0312005028040324409a61301603c03240c0416280d088603111051180c03809101d44e0b400081c0d00908040c28079291900503a4401006071500340021010806c04006035110006401650482d402c0040d19811182031341e421244560070800308004020000d01c0645000f20610007120050000036940e030b1f440840c01c5001e8001e0441c001c0d009100440c03410001c0c44202c0c1c0c00420b0300c3c0d0864181550700007409034902e40d6107203072040403688040107200749442889030071240e4140543c41d090074503069440021444590107580100c1c5625a1504099228506200c0400c0140000c446017040803447d03450304012141144100b000780500c1074185222502d03a43c0603580002c0d0401580c2100f89010a0042080c0c0d00c101c2d00c200a03a45805000c034040d0014101d58800c0e07560140d1030200c0c0020325610603000358090202540c034410382d1000011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 727380629 1250 727379379 727379383
    0x1b030e120c16060f0504050906040f11071a0c090405090717010b0a0b04061707030608100f051003170715020a020733120f0504081903140a0207030908 66
    0x840350000c0c01c01000380b000c141e25036295140341d07a0800e004101050a03403030720459004003542c0540301c007220100141c1c0c4030340e00000d00030180026028592800c00242c203400750303d071030017401e1294002d45400035032203011000800e04650840c0c2241d2803550512003c50319040644c4246d501480f00c0d0116225561104010b00080707102174807030782c071980d140c0f2004001c41c203200002c00c0c005c00ca02e2032844d0078141029030151000b00340d06c2c071411600425900140d402071090b0820b0000f40011400d0350041d43c4455001401381c03144044518020b410040410714a02c03511070007408480c0c02414081b01007018044041a039400140c095a001d002286c0035584c0182510045c12113009036002002c80c5031a003880340c240c180004a038840c01c200c0c058070000301070000b400211942116482c0c100b900800c4000000004c005070115010302900c1e000c200010888020010100841c40b00030440030b004000000314243c407401c000c084582c04030035000c242c3c50317460343c2c000c0c2004502c2070400800d0203072070307001e224 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 727381879 1250 727380629 727380637
    0x1b080418200c070501020c03210f0706051006081302060c010f020c0a210906200f0a03030f0e030d0b01090e0c03071d010f0c060b0a0f0305010f1b030e12 67
    0x40501d15001441100400742008854001c01d0280003900e00507502038000307915641c0565458440f030805080110311442040d0072145910a41440c56448900e5801c011004020071951000c180f1000070740403e0b1103002d6603a503442130000400c410b403141c0c500e500341701d00c9401c0545040e030a1341d21090401d15501c078500280c000850b00400030882c482c0c00d800c1501440903c2e410312a1f030301e001c140401140300d6014521a0640d0010f08004041d1108540c080c0126084100f20000b03030f00482c1e8100540040c0810034000003802a40c1c18080c01c0f181d04115003c07a2a0201612190741c010040740100e03001541040961000c14104043d4003a602e00e40085640000c998581150100204024110790803164001c080010206080065492100040c0c020b010011050060004404e1050108042c030b401c24030340c0341c2c8050801442603507140d65035900c14a0a001c121455400c1c81586040c425246c400c105414954042039841d070440f01c0010380046c40c20403001c201c039004030f10244110488140082c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 727383129 1250 727381879 727381931
    0x100905070f0e090714011b02012c09010812090f040b15191b0f0203011e020c010608190f1a040f15050106051c0e0a030c02011b080418 59
    0x7861180c58560049810040d4540108034950410b0b000e81d58240d903c10f40c00400d0b0000b01141c05e00c0e45400d070004ac1ea0083d64241250382d51980f07070b00d103050f50340e002da180f20140c20030a4071107820a9807100050b035240c40300060380319032054017480722444134500080c416403c0c12000d031001078182e9803440810060115100120071344480041d228103110030310340f10611001c40c1440c041100c0084210f0040300c5252031800503103060b4411108001b50354081d0300801281c0745480c20500c491383d04002c2e0001942002c15003041d15407900c1400640820f002c01d040b603032800d94103003011200c0340942d59041d50501c0c2ca03201360f90600c101600305140f04010050390303008070b000750305c003060400170340c503099596006a078551091242840e004000440d0480107a8040c4074940200714410343c0414000e030018034880205a10700e04c80e100b1351000745900140d048523290f000307036035903c1076440d40145109201c20301203009056140c104400c0081043c4403100350f50580c40321001041c00b01000e0409131041071380c1612 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 727384379 1250 727383129 727383149
    0x1107080a0c03140418050703020c010c080907050103052707150309021c0b0f090c0316081c020a030c0201260603010506010201110315040b0607030206070306090509100905070f 77
    0x1c1c1040c9900704030080255000700c06054501810802111800c00d405030f07094078915204d00200d0700f02d50082c2c068581c5016540000c108100280b100100307a8175081c0c40301d1005000300b007008a41944a0702841d403184224041c594840c00c802803200c01300c00580310300c508407400b80000c046101c070303001070740c1190303030304569070040f50350f40440c0100400054241664005500804910b000203120401c9180e0b01030910840300e605581c44500030b505013150344800541c14010500c1ba1084600c0290000055034198011588400c40e0b0110000b61801e41c000c3e07000c00350703210100c600d00092140c0039221602d4410700d401d61242e4100560700002c4108446021a003a203011300f0801c480c1402d218040c0e202409100074480050044020012480301410184072224100302c6042d10703880d2600b100407010303030140025036038140c01c3c107000391525426a402c000007400c00e40c002401c00498001c0328020311011028000008146c0c010600500001c00304030344600816000103030100c42450240003c1920440b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 727385629 1250 727384379 727384397
    0xa0b10050907050c0a0b040201050c10020301030506090a05120a052a010c021903080c0c0607050a02070806040804060c060e01060603060801200301170f0607050c0d170a1107080a 78
    0x300308000c42500400d0301d810428144070418003414000749a002a41d0444403403400354680c1c0c00101d6240c8512215584c05220341800c410400135250300540c102c1e1300030001c0c1c0341ea9172200030189850780c010050140042d8000d6480b41d01c2e10010400030040140c81d410700d1890325000300c01c3c401141d251100501042c0c0d850036141c88048034280120510b2222520140182c898004010004403100b030030b0240c200b200304400252800488407c5a820900c0c02c8211002403900e018000d0540d401501e04034018001c901c000100c040b0001080c078040c0c0e90000e07900d403d003418844103d4031102008000d5031701c075417a24410403a00600703100310070280800b03540100e025070401782c925003540d820b07100c880d03504044031624004c502e07401c0003946d05540c2035105a401e8180140170140c6003100ca01c02c61861801100c0601c40400e03003043c0104184010300f0256651005424004c0c0d03103000798032154046a401010025003c001e42d507104050609504510b141002d100c1d4403403c03415049041c03a0004520140703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 727386879 1250 727385629 727385639
    0xb061302070b0a0506240a0f030b0406030c030c090b090c0306030a062c06090a02010e01170106120606030b210111130e010803030103080a0c0609081809011403150403020a0b10 77
    0x760301102201c0020002c01041289142a1b031103441a01d094030100b003060a40c40078003512940000280d03160080040c00340b00c0d20781c14451a0b0450611044031205814031000403850300b9800740c5020030b0030081910000d5030760840c409400b5440100260b174540202400d0900058262190f10500801c1c5180c0c3d0803441c091550b00300900c3c00a045900c0d50368485410480e86c6040001c0010a896080c81d0a034412503034100180c1e42c617481640d24540402c5407400218119078424051410340000740c2c3e09002e42a65070009030111000280c0c01038204845480030080da581c1c07001055201c4080000000310700c0482c045800c01900503401d114001721111100700101140c00e03000b140581421b60142d40380d54515070303c1030014410010620203000144c3e0130700c814019240e20105820740c1100b8042d940b0741c180d03811a0326000c4100709a600c0b403010b940020400c3c104610710030301406000307402480b04084200d04a42003c600038011811442510300110001d0484120039000e95900000312131440e00348 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 727388129 1250 727386879 727386889
    0x1050a0c0908060c0f070b13020a05040216170d060303050c0f01060f17030904060305030d0501090c0e0f0d060905060901050c13060813061a03060a02070b061302070b0a0506 76
    0x2403005401002103010060025a00108100d500182d2501c01d20390740313000307084001045008404029041180d50010003d488500c500b015400390320032645044466101d42c01c0008902560b50400c50b1880744035540400507031518641c07030016034413604950030b001c0c540c0c40791003c0e54120b41044000a2010a074070b5416401040300e0421602000024410a030a004d0105e01d18080c07403140b641e4031000c04d03024604a0b602032003154030030360000d003041c0703c50782d141e0404a60720b41c4075042511380d181c40e2100000b1505094410309411843c45e99030702c0b0001040c841044100442c242c51280d1000d18403040c0800a2020b103c3c0c2603140e48604064030244c86c2c0000c85c642140c100030074445140404001400b00b084c0c0c0c0e500700f07606407132041c242024943c850071068039504045400050a091070a149071f01d81c0e000c80b5202c443c00b100d040b4110b400550314069100c041e405824030081c4407907510000b14525103000c101140c0749401140c001410100540c50781c0614140640700b18800c0740d50303401400168142 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 727389379 1250 727388129 727388141
    0x503070902091306240903021816020d05030a0e070b040603050108070f181a09010f0801150f0509060102191128061107030804080c040c020a05030706110403060e01050a 74
    0x3080d0703c108112458000d03003620281840c01020800894064210140d03801540c071034010b507070007820b4400c207290360017495000b40314159814107000303515864003030000f8030000e0307402d403100b445596280c01e6403542a121406042400300031160307401101d0740400c44201000140008008681d0045019498400424100300e00c540064207540b10091301400041140400d91508a140b040d0010b241c40c51003101d1141000703c05807159114141400002d1112421034882003951a080000c114214403080c7d01003942029201e804e0a912200384100018640384241c117900180c10b0054840d4a9030140c0341d5485401c0700482160314290345181d50344e040c101000f50f410999620b07448611660701080d02e0700ca210380d2520850b010440e10040302241240306005e038800840d07010b940b040c2c8454541501545400c80d1a060700c2c0a40d2501303c140904510000f07040c9442c0d40c00401030b600d0301010f40c81e4540901a05001c1d00c500071030411002002134100e1003a8003840559000006550820300f40c560141c0394 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 727390629 1250 727389379 727389409
    0x1506020604030903020613030209090c030f011a0d140f0a0606090c0c021302043302031c0c020c150c010b0f060a110c0d03020d1b081909050307090209 66
    0x3014904100002c0d41180080c000d90350102c1e0040d8403500303400402c1640c41071642001f90850398103001c3c4603c01d0000516601541c40440541da103002c10b00403a0303401c0701d0442c3c11501b4070400400100390581080e020b405a480c2c040c0c0b04414603020580b00310b034070b040010100042c02d0b501c0314440000b070001620602c000740225201c24007810286e164001c08410f4041006407041c0109080c0080811380303507045800038090069102c1e1942152070346003d846402c0b17843c05204580503044c4115492000c01150706c130403040d00301c0600c103d801202c140c0040031100502010b51180743c030840c80c40e1707031100f074034205100103040d4041e55280448011030a58060621040c0114070202003100140c1e1903000ba20000c01c45803520190303034841c2c01d4440b0315040c1203800c400e41040c007070004101815404990309000c2846501c44080000b000c005150100c012490b000d0004c4205010014a0038081900e840070280c991911404194460001a003050301d560f0024080550000c0c01c4c000f01d05181c603101d65182 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 727391879 1250 727390629 727390633
    0x601060f0503070f021c120b040e1e070f090c20030901050a0c0c080109030921060506180901051f0b0f070804091e0509030910050328150602 62
    0x22031034120280c02808094103050070f200c0c20343c4218078030fa0300c00c1000d0107520404000840094000d8800a40110322240c2c0c204085401c0c01d031580014145800342c9402e10f401c442c028004416600d410b500004003000110b95a0300589200080446229408c0720143c5180d01001616001c19100607040d0313000e0f140b9110427004692062040e042c0c020040e0b681c0d240080c28599500c9007050f804071032041c2032000091a041180c0c0340030400000550041e00c80038440d03121803001399101c540099403260f8207810300c030031000040301040000e102178001e1b0b600008081e0000e07001c607180c14070080290b5800c44070045240e41d41c0040000001c01c2d40d001c540c9413141c0c06003041300d6500b00811030311288a054031030f880042d0006141020010600c0849004144072001007140c0d05060101e2744d008452a240c240d196400e050108605007008402c860038400002d148079402d103841e0000381c4079a080241199803500308044c5902c00c000f0080f000d1401c1075081d4000181138030703c9420300d55804006801010840d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 727393129 1250 727391879 727391897
    0xb27070f030504230102131d09190f0305040312020105090c1903080a260601031d0a020d170403030e090708040c09020322200f0d11030a0f0b09060106 66
    0x1240010420040aa002410640c003056024822501a124440c0711f41039840c001c0000180c0e50203810b03a8000034200341c41c101c121303030f0316508d0103540c2d5441301320340c9125810340c0038042a0004032144094a9154420706040b8109550b0381c5503034103240c2c0309024010141c0d459100304020018180409048608219502032408500a8891060780c0c40c80c0401442d2039000904100b009004014484071343d0b94444003410540e01080711400c0e02601600c03040e0109040c00390402030003d420840b4103888150300020411041c1680030022841e591640c00e8806003040d078941c03564038034a10020302c0918020f84410780120b03403034007e220380600d0081030601004040c0e0306000004005060780d2048a10544025840351140e191901108403402c84040100b080c01c50410100160441281083e41003050401003401c0c000050200604603688a80d60004042c007800000860b842c0603e034012134094200d5007040380d1744c1e0360150700e21146282079607110f0001080009501d001c024a40c09000e031403403c0b00c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 727394379 1250 727393129 727393133
    0x8120106020f03070b041a04032006010513050423030a0e04020306030309010c03021c110d0309020f040c0507061103061009030f0807050114010e0a06081209040b27070f030504 77
    0xf0703030040c410000c101d00c0080c004682400b5022400e0000f581c03c4480c843d103a814140340c080c20898805151001041c503d16000000c0318000c00c010b81203a001400c0000c0c1c50b5405d003821002030000802c1285c520184030740e04488402e120b05c4c0000344402443c001c40c1e5529a0f0035018140003d4408018403a50040041100b40d4502000352a09901c007800c02c0f03040c1c42c0251034144d003001180001001c000c9600c09408980b190321405480508582d941582c0e2400c0404104500f61f6100e5600039401c4400d8840b120101c1c2043d5011103030032000e0349001420b01030705075956419204900300100f8680030110520816140c8800d80ca0546221814540b44292465459107e94007881002070a4400c3c00715980d03041c420207400420600c01a04a165019a154401c4505418069031b41904240c5000001302d98482c000400e249800308603c92a410000b0301020403000d003074200c01c0a038000900301501402000500308500d866600c203051030480b0328103107000074010300402014108050031300f018000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 727395629 1250 727394379 727394383
    0x20d060801021602060903070909030302070209091603080f13030804080607080f151503040c080f07081507090e0a0c08160507030f02010e0a03170f090d230708120106020f 75
    0x103c81c1d03505650704d5449140700c0c00000c0c2003103526481416102e0400f04034004041c0e040d801041c146100b12a00c0007a916814580c690f101d0700c151400900034050a014008a6508006030951440c00c0311894545241100c0401d42030b40030b54012900c5003030200c1c00b480f038a481809a10b901649038640003281d46000c980100014501410741540600d0038500e250301030f156109400e0307400d00c00410b015664201072514102c02c403580d11038008980200090403501c088041142c0e41118a440006d00e03507044030501c1131040400282540040c0316002100182444400c6112403060314580e0000400d0305403004081c00b8500d00400001c1d945550b40c0c5061081038101c410380382050f40518000014901240c0700383c1c0140200c3c002141d142c80f40c010124105544264440c02240f1441c813201010348802801101c00354041e030b901c003c184c12010b4001e90040c0301c2c4d07104c003401080d003e03000207503141e030200301d0355180d0300c40e03901a00c0c000400103155004450743c00045005141c244018042d099412142039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 727396879 1250 727395629 727395667
    0x6022802010f030504030201020417030c1513030827071401051c020306150313021e03070b0a12060e150a05150705070506030c1201060c0213270501020d06080102 71
    0xd1513610004681494800d6040d03401800d05100017100059001918a90b26000035000300080c2c843c480b82ca8001c83c0d03071100c145010348009461101c121442c0d036005e076100341008290f541019001003081e00ca20195803601c1c00c427840400083c0004d9414070400090240001d10910305000c400c101c0c0543c5000b404006101040380181d0040e22070310340da00040c4051b2180804038007885d03000310606c081c00107010300760b008081c8202c036811121200201e236400e40044100155500d904405010042d4102e690002e107032035061460041c0005c0c911402036400c640d541e4100c0c0c11100744150410204581c03460095907590f404031040c01d0b8a610303200005041000050b545c481203400410f00c0c0d810010104842009400000c001c2912450107e00700f4049400031304618503460a4940000f0742c19010b1001150706a4000d01702107501c40e03604914a0182c00014a0325803401a0a4008448401d4500f0010001c5200354000360351000103400310815107910703401401d03c42e4810000401c204000103005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 727398129 1250 727396879 727396907
    0x11d010c05250b1e0c0109121215030b06010c0f0c0801050609060103090b0604111e0703091517042a0503010608032706070c030b06130203010b270a0602280201 70
    0x581d0741c545d4595221409855040401400040001030001c40140c000450101c0005d8050b0b0400400517294508184104d191101404ea25160f2000c541d40d03500c90100c010b0a540a0b060004030442a5620700b811000315500c22070103a503444007441818034105c8410b580202c42440c051100301c034207842d0401c0d40c40000e824107100390380d9000d503800000f03c00015a1584840002b13405c26411081d44400600e600100007100003408040c808142d11b032003400c10303440d180c2080e6160104100b035800070150703080d0041c00585030700e0040440d0b002c40010305014031020240c0392010b552107070b10b072205050030340d00700da0400c499a401c04e009107060340080600d244451242c0d401203502c603c3c0d01401081f1944250007010340070661410001c014010031003a401d025160545560120210401030300003240801c1c024001419000c00c00c1c0d80480c1c410b004001541c0540036208600d13000c1c118009409441d480d401140940c200c05000411a40c0c41222213540301c01088041c0b8141d001940020070081c0e8003100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 727399379 1250 727398129 727398187
    0x60a020d08070e1203030105310213090603061d0706021513171c0c08060402030a11160302160f030312020c03070f120905011d010c05250b 61
    0xc042c82e1184196045000001e009490307980f0030070a240c0d0300e030b03807090140da8010003200548400c6a401403001c006000d0500c4440540d43e6203036040c0101941c8a01500c900b48125140c0105079250580b181d40011031240c0c4000520841c4204854240040310240360b00c142c102003020850160086068199004154600075a682d141031803012070151001024049131a0035030302480000d0280000e10304075000f080034142d070940b41c801c14000c0e6030596000390000391250010502c00c3c1401d401440d001020f02c800032590750300039082c0c04890340001c00c221a001402c3c4800400b8107405205e4450f60380c00b54400403045170b0038000f0344415a00c0074030000b070030041e1800005104810590690780b01c1d80400c03080d240d03a001e550a1502c0880c070018810f440c40d41c910043c40c5015402a60384004490040e11140403819220200c180300010700c0210300d0600003000c8010000560910440e01001c0141e18400c2038503208120f1842c00103c00e800c2031541c54403c0000464407103061080600fa0600c200c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 727400629 1250 727399379 727399381
    0x3121407030f110d05100f0f05090406180305090a0902030912030c0409060f050108010e131704050d0f0c08060415050601090806100e0604020717090a180606020606060a020d08 77
    0x44280007064080c544454906004c2000f09406141d90031050141c039986006002181c5c9903217064440c85e0551144d05c44000e00ea4004020711309000c980030364014028640001c0040400081c0702ca4100100e0301200002e0340080e0301c80c3d03a454000f0700d540103860517842c1142541740605059603911002c00300c0c480c00c0580413002680c510303014402c840140c07451000c18807003541d0b58640e420050385280940b1380410f43d09030000c03038039502e800380007889404c0302c0b18013a144044070740310080c1503400900380030045142004040345e1512240000c180e141e00c0b40c216401a4800d9003014464282e203504801200d401a90030300000c60641c2e50710b409548014040010340d5151080142c034003031031652004099020329020094082109682c00c002c98030721303ca1041c51070390f075542080101d100e25800104141c214a030f01500011040c405861445805800064166190440030510380035410010b5032260315200c051080380e40c14414150011825542281001c04640c0e0207500d860150184a0070007407004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 727401879 1250 727400629 727400651
    0x4050d080702030f03030910180b04080d0c020705030d03200322060f0b03010e03041e0f081b0906010e0418060e0709050c0702061207090f0f030312140703 68
    0x110031122440d600604844d0f803180d0643d1000d440b5001201e40e4081030113004840c1000d400c40c1c0c0208507120800701c44c076040d0104550740d8400b40c468080c0c41940e25034018003200074200103d00c6000d40703d2440d0b0b002003210524000030940f0f00241d80444204045c1010589044101003100440f160502811040e88035603030045d64005d55a0800b9882c005e1114a60160060000c20340c441e490050f83c01c00248403a0310b18006040c280c9000313101224155000700010888800340007804069810341ea01c690303408660710742c10b0b56a034494a41011005030002102e0310324095090b141d00c0c00d1584261411206841d009001074140304074183c03140c2c011034075030360300c05023110f000c903080d000055215500300b06683c1c440c034800b59a10014016840b41d1450400480c80c00d0802c42c0c281c9410a41c02000d551500c10a101d00560007400617240b18103105e040c080101d640e0428482000181a03880b4540c80300c907181d030800400400707003800101402c07440c024050704604100780b91594800088d040114081e1144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 727403129 1250 727401879 727401893
    0x6060f0513090503491a031002090d0b041211010516030b010203070f060501051912020f0d0f030c03030506010302070c0302010e0d0f050313050105120412050c24011a04050d 76
    0x402498003842009045e43c0008252040350000900c030000400030501401c18905c44090722480341a072580c015098090740f2045034004000404026100610700890303581e803241a0f413400e540488444d083c408022203116417122803425030041140080c040e0341400b80102e0080120401010105034480d0404900d5034020412545400e6005010b001e400c0203c0c2440d400916003070140620400034001c031044170001c000095001d848054921007c0b0000f1070f0300f0400045a0460800e802c0509904030a0109402c290980e0135035000380c83e409400401131030b004080703410082105041c10b205002160100e10465500000d1301c2e420300b0204101c5902c0c01c0007031101450b1100c01841d0380c1c03451060008200011018000d200c038500d04d00d040c415161001503505006100c007424800d2040c40c002004207130b4007502c3e141c0710011400d0035460403034000c1e00c60382840b400c09961890664401825010902c5c0d03909124010103015465422414916560b19064401c520400744030303400040c6000180a14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 727404379 1250 727403129 727403197
    0x411130204081c0f0c1106180604060f0828090501020d11070605090304030b0a0b060403060515090115140f0c0304240e1302031306060f0513090503 65
    0xea402207801030000f9440000d16615580081000502402c03070b070401241c02200381c03144480c0c1c04035a0344003c1e6011010700856400c50405050341c11a110080402502c5520040c0050003281c0d403030201000c0074a6015102d804003a00380c07000c1c010070a6621402402c10440020404050200400c0700d0105007003c5001e80244882035400300e280040c0280300204050042102e640300324000d10003581d0700d410482d16030090b8403001d0154100d071400641c11119a50020803c424001c00090070642c0329202e0800312030342100c41508122404111400b170b89001909240100707031000c604d0300f4121181d480100310301c14411922038a81008a140040c2810210a0b101e0811a0804480d216903071181c411010074000001400d5815a840107000f04a01c11544070041000c007500d41409080780341c01000003944010071003461002810f80f81c6002070114010a0002c249070b12400c16410f0411003000400d210208031035076807501e89101103000a402100b900d02c085c1e1040c5841310076146e03029001e410800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 727405629 1250 727404379 727404389
    0x3070323090a05060f07091809050607090e0610021b010309050a0302011e0c0912020301090b0a05090d0509241c0c030e030c0601260a1101030b06030411130204 70
    0x2080080240d844000241c1820590180c0304913050b980344c4401540042d041552004000b07041c030302c4140021604001d59250000201d0703030001e12603c060312038030708018066039048000ba0002104200e100c1c01809444e800100881d15000ca100c41520065078450140c0903019000e8a03c0b8a245850b0f800f039401400e40700d42150a440d05c00c0c1191030000d00030030b8200070044072488005a000c2d00b01005100390642888d29031506400942445010320042507039a42c201e90540d2165081c800040d504800d4030b00614204402080a007080c03080c0034100814040761100f0084140038a910310340e0342039013246006d017400c0d0b10350800c081c2030380e450f020912076080f0500c1084102c81d16140ca0450503445800d102d181650704200001c25420b50503180e2140c0013104556138403000061007031641301524142c011083c1c0d0700e00f8025a412000e03190509440078815250b11000d000b0103c000d5030140500c0400101c201c0b419403544c0f510303645e41210024651001c900608000ba0300c610611070950448024003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 727406879 1250 727405629 727405691
    0xa170f060a0c030c0212040308180d050a0201140a08010905061216030b0f012610060305010b0906040509030301170a0c0e04031403011404050411100f08100308030703 73
    0x45030071100e01c4090107400412100081c601030103188000e1010a00c0d04032a01034201e00d9107040d2462704c0d4155140c00440b01190b101d4540d054050013652562001c00c00a4410005008030103d00c0c0009081401200a0304c4032a07042088400e107600e5000504505655400c034000486803107400c0401e65620702034442115511660003812034230070800d85e180302164826410300c00daa42e100d655007207240030280724131150065104843c80c4d403054001900400741d1000c1c400c03100803280030282441560401e92058a8603503651403411041d042405880b82e003c00127450512590038075070410743d52484144070358060828000c040c0d01078040b06010710b00090760411500f0440c0307611458580289041518114041041c01c41c0000341043c1c3c2c8819241207a05000b4840c5030050f2a40c10302c4040e20f0006c00031544d07180c002c0703007e01e03032030390b42000c030701c1052040c0c1d80e5900381c0c00d0781d441e806048480d000d445995120a601000c100103031018080b6944404586004140f16500455061192601541c030340d58030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 727408129 1250 727406879 727406881
    0x60f050f0d0602040504020406080a0b040b0f040e011e1401080a0c210204230a09080406030c0203040905040308060a06050f190c0501050c0a030c05030f01032909010603061a0a170f06 80
    0x1250b000078000d002f02e0040b074040081010050803c81151050607020360840d00d001d80e03c0e401490603512000e200c8010900200d01d1022410140140c0b50000300359080c40c941e45c0e0890100080640622405040b01e14010441d201540e21450143e850b24402c1540f00e80c0c801204120400003c0c14001c0314960280040c0902c05903940c18000c90b103070f07602403150301030000c0000614040442c0a1008a190007124541c03401e4201b040480c0600441000e06095103c01c2100141c540d10714400c040c0304a000c1d90750444d403800d0160400605401c9544803404102040c8200300348481c1c0142100c80c044a241c18442e00215140f00569000c3c181100240c081c0d4030f03120401055600d5400100764031582540c0c20803940c00c200e1010b4a1034082503500104e200310410041c000200c041d10305140c000c04100101c000d0582143c900410300c00221507181499440c5d00042041000c0c600504e0441c049541280102c90071003004030350300044501c18400d8609a036001018500014800d00010300c541c10309075542 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 727409379 1250 727408129 727408139
    0x503120403050904050606090109140402072019030c06080a1803180512060105040f0e032217030a08070912050105041109090307081c090510060f050f0d06020405040204 74
    0xb940140324001e0281d810100000e40c0b519210f000c0b41c00c0704405848071211107003455100041c2d081c0720304103250810341c00c1289601150128842c0b2103140d00b16040c81504119003014031840d000a40a031240c0f4501c407a06c1840040c1078241e550095800c0c0d842c0c00c1d070386650f8140508000c0c1007526124506414030443c0e040a160b4010130708020030f000550368144451740c1b142806029900500d1041e280d8000c100180b0544c6840c3d00582001c984c042d81c00329540c0d2030007901e07500359800300f0900d10884011050200b400003003001c1c207400901c000154a6500d01d0742d030761503640301d21840d80c501c800c0148400c0001d444034000d03003410000c0c18030402542000060791030402d00074a0160740c140c0315610ba0840301c40091420070000d501c41c2c00c155001d50f0600b561591242c00396042004040001e00c1106000c1c02008071a00c80c1c81c56060041c801440d48505031401e01d01180c0d0590081c0950150a88080c0040d407a6503e40c4480124181d0384445c0d100d009045c684028002c58101548c42800000e0003c0c1e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 727410629 1250 727409379 727409387
    0xd151206150b03070203070303051932060a1203020f03040f05011805010e31020702120115140109080304120210020a1505090a0b010611010b0405010806040b040503120403 75
    0x14140d400e60141d4400141c903064140840d00013110a600103a100b0000d100000b0f02ca500300981000780c0285a03000100100600005c0d02c101840c150189849561041c9850311205424114008507070407217042410207202250a40e80c0c1809040340901c0175006c1e000405100708022901c0400d0281a640c68540f1141c140c030301c80810b41300f00307400200101180303c1c1c0f443c1c490b1268400c5410503150341c0000c462041c14030503076059140002804006074240b803032204951100100c035001d44070100507a030358020300c10448a10301190301924560b15040f070f88488413a1090112040d00c08500b10b0344242c815040040381c0242040d000001580808603001400c1884466800d070340c2031080b603441d10f000d40e0a810480e5148840d100103002e050043c01c50046401ca140d1140b07420259610030742d5405101512001c0250200381d20040000e2260704650b05000402e101c0d00d04666000c660600165142c59106a034403003000e400070b49166140c0c00458200541001224a50040c5c0e50350300e03090b46800c1c00e01030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 727411879 1250 727410629 727410641
    0xa05040f0f121409130c0c06090b010303080a09110609060c0114070f05030c0a030c05040e0f10080c030a11030f0a0c03020102060717070f4407050d151206 68
    0x1c004110711032541d0340f0b0004003000b914070b91600070b46400c2c01c92034140076403000341c100390000c0c2c8240b2480c1d02c1d2032030110701280074242080b17002d40710340c4085500d140340c0101a03a1008114401d100c0c600340c035140006082006010408208580076034441546200080c8103100b0149001c4c1d040d07103030120205000340444240d500c14103a945a602056031038590968180c402200c0e840e002c00810460150214000e0340300038400030442c98405c5c2031944847c411151304800360344c4c08030f640792140c04000099218a20346d501900c01c100c0600f40d44007504010035a80c4500c070100800311800103810151769101045480b4500341418101c0c0c1c8105003500700000c4807011030100b03038014068440016100e0b4080e61105040304000c0442e005984d4614408403100c1080190102c104100791050414081050080c0446522610300301807404039240380080b0146031140a50483d45e03610b4040209041d0800150b038030510030240e020401076070718840e150011007160881c1c2c0c1d10302c042c090f0050520074182d1201c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 727413129 1250 727411879 727411913
    0x41e090c050a020304090905150f0a06051009050105162f030d0c02191701061e08060601050f0705070e0601122a111b09010609030b0a05040f0f 63
    0x80203006a010001c4071203209141d00c003009603000704070801158986502450703006000c0d200b540c0c1b441205420041560006540c090301c00a03a4505000b011403051060100038241252810380c04000350001038a090400e02c0340c0c0d0b061200104041c5500050002424002c1782e008803c40d00c100c400001c9065003031210b100701520b405050322940058240010107110340340340354562455410060303003000039446482890003500401504c1c00144d141043c1d0f18140025422000842c5040c10300010040600c074206407010502d8859008125107400070800310741100302883c00ca40c0d030b007000079180c0b040352140ea0f00c01072032446403003400154190034610031400340d4001d1b0380c0e00380301c100d500311000c09442403c944000d80e803c401080d01d40800844210640e51a0241001842c0c000d6003050642868202c040300d09000302c800600d521340d031400303d07078581c05400b660601c5181c3d682541c46860500000074010005641e81c1d0340403030240452039200c044c51350b91240c0603000004d03070f518148804803026a00707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 727414379 1250 727413129 727413131
    0x402100c170f130906030c0902160609030e0a030605010512010207120c141b0f03010b0f0f1207140315091c0507060f060509090106060c08072603010f050a2603041e09 73
    0x2203410360a2740210b6000d030050011024018280317440c4d45004003802e035000c0b018801651003014468440d220280c0096000368800140c541c500300c1442481c9488800410042e4410000200051001d4850408005061a00104101842ca131000c0c0c02000380704110001c1c811500120301e80010001c511204000079107200c22860030040c00e01d401d03039004400c1254080d0518110042c80d050081c0c0340c0540000040521840782c038410790480c10100a600107056150000d154051241800c100341c80b00314680724000e02c5c0300c0c545200100e4880038041142c1e01002011840590307524418820f803038441d0f401c44410002c0840b86807088006041e83c0c030076540103022030400684502da062041400300d5915480c0c0081080c178640e00c014856201420440342400c41071043c1c204082400035640e0840f160901041c0e0340e5041c1000c00041c900c20750710441c402d807000e81b4207000825485805580441075241c00c2d04c00308007114213550844c040c5400209001001a664100c040078180040d0304942044c44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 727415629 1250 727414379 727414403
    0x18060a080d1e0e090a0b15040302031f0f09050601030618030f05070614070804170a0f12020f0c10050604090c180e0d020a0c09060608061903050d03050402100c170f13090603 76
    0x4058100e03000b18132000e0b515802c0782071400c50324402d0700001e10220cc45110000740900c40e0011207401c50f00920b4040c0c8880d80300030014020003085105010207034a00d003002c14000c80d503681e00280710b204180c045208020000c00c40c4410803415070403010540c034031803100c0f5049152074400244800e00803141500e1801c01c00300c4400d80b4600640031209404e01f81c0e5204500401440025103500a0030383c60329160b00c2d403c00c400c600310105030001e02130444000300600b1042c00741e8071022068a00140407280b29610f80f985c50310018040300c0010341101d42040c000001c1c4e00320401070380014001500000e0781401841086603c60b82e01044040c500340c882d4004803203c60f20781c0b0f4040100c0d0100d002d258003041100000c10070a2816080e111072070140d000e07a02d0034941e100d546070360500364102000000f0903228403e00045242080f0360b0400f0641c03502e05940a01103c1d00c580d489003d0705004000c2560002400c1240c41c4141001c0702c040301d10601c2d29100c0190354031040c200030512f03840103403400d2160039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 727416879 1250 727415629 727415659
    0x1509080d0c082a131e031a0601050a030504050a12050306190b0f09030703060c05072f090a32070503010614030c0918060a080d1e0e090a0b 61
    0xf00080303501c04106101000c0d091911001c0701d8030781c0403064900300c40815810000d01c88811003d0880b40410001443e80f4282c03031881d1040c01107171420285445200b12004015042c0d070b015081e0b561440403840c011400e91200d00b401c0e400c00c0c0f5400300140c503858a85504500c0c41d0b070040c00850141c032041d20160121491031889000c0840180501701c040481008000105100c0c500a4251280010142c3c2c112035900e0750780e4070071114813000100100308003142000600c214220f003107003010141840300780d03140038a462080106028000300e44c8035827045000b052880119600400a03000402000d48280d1401450389242e1030a5840d41c0d9204403a00d000038209510079025a4121003080d202d000f1035043e1030078031602da604000e0017000700000910043c90103036100f4440c0501c00510915001d003504014007401000006174200c1142684002c030350314000c0f944032840031210710350051014140700e58007804403802e070002c02c6890313400b1010b8070622048490f10b80c00302c0ca46510031a684801131180d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 727418129 1250 727416879 727416901
    0x6040b07030b090f090102121807060816030e1c020109060f110f030a0f020f0a0f08070518030f010e0304090b011e030c020c030316030212161509080d0c08 68
    0x30352020b800c9420b035030100d000b4031078140d130254120f80301200145c01c04031011708070051241c0844070070307072050a6160b8622028000b840610042c1156240511a03403600207810000c0600f260a00e82c00c01d540c4e0305102802e20f40c00c1c081d902402c800c64103084824140d102c80280a071803040020740b85246040000c10185c40a48100134008454821090602c000d043c00c0481980009000c1d00c03840343c45051100c40d01545100034204000b44032941074170303640b40010091131602e4052101e818030014205211403036400074184c407110310714034100004001403080844c0c14001c44005c540690b6081080d0700401c2c0700c011000d0416500c070001d0400ca0011150011100b81c00301090b030745903003644da100010440d8841d4209190449180c0104c3d240030948101081c91507104c1003440080c4426811131500f059418000c0d04080300c1c101d801107050100955500d0188848014002c101d1010348200c1760407428150002955550040119621a10701c052050090850310040308009600c2500054100d00303d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 727419379 1250 727418129 727418141
    0x912061f0e1506030a0603051914010c0e0d14070b030610092106140f2202180907030c090603020906010201050f01060e06040305030408100606110d030c140c06040b0703 74
    0x1041400707810401c1e10b014802c00d40d0003d000d0030569500c80902201042007042040250084820b01446c124030509184d840500d044003c00720a0341061a005119503001c0000c1712990001c036103541d02240300e880e0a0340da4601d560030090240c002c02100090303002c1c110010703520071002074030248021840148100d4000e4070704d000701c50080003040e0300030084a4a05044150540c42843d00003410024081c0740d00a030481100c1c0511911071407800c00c500580c031507480b0035250400385000d5004e808140d001030400500f00144501995290740012500c07402040103000035900010800c218a848001400c080c052600099000300b0007240072900c25403051058504c04e507a00e0400800d82d074249007046402080401d00e559001740103110205c04100300340b000b4001400310000400400c01501304040588005034070060600007a0711420030071b0b4001081c0082c1a484528001801d801006029120121003c0401030101d80201c0c2100c004600054141d02a9008401c83c10141d91000340840580f29 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 727420629 1250 727419379 727419391
    0x6090b040b0307050304061805010504110a0807031223251113110d0f0b0f01020a080a031515020709060b070303110705010c08011d010b0405060912061f0e 68
    0x700c1040054541d52040e800355800512552001c1480003940b45080018005441c0c203440c26503440c014041003088903010080c403040c00740c81c81444145452049038503031401d407101414100c1d000c10b00042d12841450060050400c4d208962b2100504d5192072545030892511840c21400c660071a9103440501e8942c6400c0b01d0380708212040402d1190301b0b006442e04480d100c1808a03031540b400b554011488030142410082a01c00040d11a01a1804809803a0001551070041d5030203543e0031810f0b41d01040031294290022026552102c1c08841240184407210b04420040c0b0010307070100e00390107031064007064200b45608449100d0340743c0741100c04690b014810000003100400503400028065000030840d03140c8000c02604040d43c40e19018255401e80482500040f000070050000080b0316030000040b00c42e0020381040e540c1842d101c2c50841c0f0079401110721030b9002040c41c82a42e60b4080030310309030110752002e0306c4c014100301104503054080e4040c1d03003100c0041114041070020040020600c121 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 727421879 1250 727420629 727420649
    0x8010b090a0504091a071701050a030809122d0105060102070f060c110607050106080615061e0702040f0f0e0c0d030f050c0d1d01020309010903080306121606090b04 72
    0x10346054108002415410011a0404400e1056a4445c2c1e841d060851041c00710380c49014680900d00013804a42c001600403902c214001e0f01c080c008a00d210040c1c625001c03050714070000e403144140d4220b1811041d15403000b1026424183d49000000903c41845181d408400911280e101c05c001a42c803084503000d80d42c0240300707003482000604d209003d0390603114010070202405032001404a100c5910400c2c2c143e5190303469103020040410100106a440081d014120103864080800100c2c9445103a044603482c154040410f0600303182d00045030b0080e03a0041c000c001001403411171001402000c507a01c10001d14190300d4612064004c6074101850500600300b0943c1b51440c1c0d01500c14014039440f00007088014408800003083c02c1000b0b545403039481d00c40440c0c10300480c5100035000c81c080422811500140540d204a0f41c00200200035603900110150301c96581d640440d1080031a03024003242e9210304d03c841040c0280340100301c41982c8940d520700c0c0071561618107501003803085d4400c07141c4403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 727423129 1250 727421879 727421899
    0x10605120f0f0a051504020301260d0503150a0e130201030b01020724030905030a08100605040819050c06070c0302030606030a05100e0a0830100605070c1d0708010b09 73
    0x540ca0364031040d40038044032210600000c011020031b040760401d8001c4080c4a0300031300f903103071482c203882c0352512080c8403032000b409404d0703509074024160b003c0600388101032906180074608982c1c80171041005001e080300f401da42e501c1c128151100b00d070007101c401e80c040381c68034503c0000c82d4804600381064a0300258004204004d400c84101c01100c8500e200d410156184030300c80001d14280300038054000b50795a4503130340f070400f40302403e180902a0b01c081d040c00403c210400c400d503c081455104420811007401d1714070100d040560801a0741c1e00c80350b501c2600080c05008107c500103404064900a804451041c4d885000740341e40d40800c00d40262617a070204031000b02c12104c60f00b08044803001d82007580c0128149a807100b00f160400710003030852040c00c5010144888986101400700e41d05034080000c1030414031b2940b28905814019402044000604282030281d1220418014059004001c6500250005019040c501074400d100001d00f420000510000082c0c15100e10200082404d40740c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 727424379 1250 727423129 727423141
    0xe1311010815011101150303050309010b03010b0a0b070201022e141302120c0a09020417070f14060405100503060319050c0f0415090b010219052112010605120f0f 71
    0xb400009944004c2d03e03648030a49034000c0281e11480800840c0b2a80760715849041800790142540c3c8074503c2c45000b603241014103101543c0d641c1641044494054106964074550300040382848160846a00e11000c19034121307400005400b11103552241060042090f500300f9a01c0070420030081ea130301390032100c0c080400c002518100a4084481c00458101d03203007604120003140b54031071541d0000340c260b940441c0800c0302c12041e03440c85440000b2840508031503804d0404600c034005c0c41d4014842d2410f110f043c2443d5503111401290064100188803109014030950000c002da48111000c500a0090b008450403007440100610f12265101014160100300350781441942c4141d451425800b03911344042d0303e400e4034080b0f240000f500d2002e0020035541da82c04006441d080d50400141c5c0098480420031000c02c8000c20b8071424004545c21142c461501c42c6c030000388078083d0703228000c4202498000004c1180d04000103003840030060985201c159901d003514445a001166215049890f540010381 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 727425629 1250 727424379 727424387
    0x20607060b010c15020a0809030a080f15030a0c090c0c050a021509040e01140907061d0609120d0e0f0f01180801060b0d11040f060e0102070e131101081501 68
    0x501c1120614040e400038110707032161070600e80303101d5001c03480c1030780040c0125200e68000300c0141e200c41c2c05001949880030106005100c458000c01c40700310ba00c02e1002045c205400c1c01001348020500804640340c0744010b04118044502c4c902c680c600c09ca19003e50250010b02503c1c0e241c0490b42c100015011400c0180c00b4082903150314014400160700c1040f5500456513948180310303c144210b400050b00601913903111044120252124649901c144003c01c44241c0c040701440500c590043d103400082180d201050450082c2c82e10603505c0083c0350401c030030901d4006180201c0c0d002e01e0f62208901024041070010856468003603681006c82c8002e00059135004202c440600c1200014a80f0031660b00d00c045030844007140c1200480c03d80005546205203880d0003918038800c848012240b0f410310b060700b052030700c00031441805c081c019801407030605a8000e00c82d92000746014003500015180810450030381030155081100d00c42c101c0003211001c0d5100d1201a403040c0c81c1c1d58000300340f440d0307e000199 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 727426879 1250 727425629 727425641
    0x2030d0903090e090a060c030b280b030403020609061005061614030316080915040b0a020d020a0f0f02011401050d050703171b0a020603040201030c05091f0e01020a02060706 76
    0x760501c5500c2000150700d403000d06009108100f0f440291030760071107a240590a881c180c0d000c1d6010581400301032407443d075039540c0e4001080030300fa8040d454454a415080c12003005035021149540340407080201b4160040390851007940040700f43c0d00c25030341e9280806540b04031402015002002031004d6640d0034040140036a1960003440ca41010f000c07508001c40c9103034411214074051100d503560000c1c1c00e5030400d030f400d07800140a030060084144603210455070501d0040c00a0a03203000d21011813240b0480c0c0d8102e4200d4205074105554031502e100c8090b141d0720710321000c600020a15000060003a02c180302c0c04094040c0100b035034086900e00400c214400103140d000751440d000701200000000d42d105e0485040000005044c0d40344c00352645884031030b910704044030026801c14008180140e80321310803603520550909000901614000701162913000d150146c9411580a00c052107402c05210000c400d6650303d50307a441c1c08011510012078561000610003900000c040c00310f0400202c56030060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 727428129 1250 727426879 727426883
    0x3161103100c0f032d1806020414090a09170a0210090524040807031809150e09010c0c060b06070b040605060411040b1b07080a0b011e0602030d09 64
    0x441e04501c2001d2080116011584a04081000284042c031040e4150294040d40500007000180c60340300d03545500404151404c16004542c0c0c3d89444400c1c0710500c00c521408560840c1d411074603540c40300c08000310780c078890400c14858030104001480449090052030801035100c0d4003c004070594500000280c0c0001400303009601507600404950f0b04075100b405400c40c000c3c0020b01003188102100c0b102d03a008912194031300d10b01d540410020503507041c00c40d03020701e0f450300d4108075240e5032007080d14141206800c00458241006002840716411034980e00550b00c074000140050780b80c54103503a00700ca1030801200003150800c3c028102080d11580046070030b0802a000a06d00308803540e80c01c5003a00c2c202da088600b00e0b5550f0510003617003445d100c0c640340010407030581890141402041c2d0418002d40022040341e810303140340054081401d100c2407005040280481704045118689502803080034016510200701d140310046690440c0803046003110450f4028502d0482c014200b6806000e1204003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 727429379 1250 727428129 727428133
    0x1080403090b0f040f050406060c083403030e160618080303090d030b18040615030606090c020c09071e0e1e090f06010818010603061404050f03161103 66
    0x80d6401c0319500800f080300d00c40d049141d90350308005031032807044103903040980683d01c0c0070014003009800a040307a03610740d001131645494542e2100c0114010300710134032854440110748000d51040c2035815101586034420b88051210191010002e55540042c07543d4203462145644100801d80c000d243e111081c2003030050018607151200c032042d1441c0d00580c1d0003403440e0300c50100c007618250f16101340c05100c10100e4425142d07280046242ca24640d0180c4054417560745c401c0d41600c0740c0180e00840c002950701c940c003402007540c0c0e000d031540241090180390016001b8206c07500c2103031502c1030a292141c261901c0700080020460100c1c03100800e144091010301c51310b000030900340d50340c1f2146980b502c90150290381e00f140801091001c0c80038080c2001d04132441e0b01d010b0014036030b0405100c40d0300000030b601c028801c0709a01c29080c00340020340d101401c0309240c05641d400400390b0001013032145010310121900c0d000310b1141070f82d80c1c0c40368a90900c110748081a51800191400218004d44240202 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 727430629 1250 727429379 727429397
    0xb060306010e1503100815040b061203090307080c040f05010f06030513050f0c0a060e090c0d06050a0b070c05091b0a030e150103050f0120071a01030503040f0e1501080403 75
    0x3c807a9850740c429290080d101c0c030100002c10a2a0741042090504200150a007405007050340e0748000d03111018103038501c5660044c0031000c40b00020400d80b032400c1c40080850301800e54901c18141c40d030a20048860080f03042c0350303401c900d041980c02941d040312888410b90040510b0154210002c000181c14400380306182c00b44180880e1080048095051008010701a940b01000c10024205c5455200500b8080c1c0e04c0f040c45070507920f00d10f01550110108040301ea542c05100329141c010310150304007030b9010602e09400305d00413403c203008d002070510a0041e00381d030707a88941c10040d40000c2160440000341c0340542c61500442a94040c1164544d1820080352090061030014140b07081105414a102060801001030017010480b040010a10f440200044c1d44402001c001080d501144a85180000240700c8104071740f92401074006400041d844c1c0740c80d6102c0c5070550301c070b9005106240e0748007054100420000f6401d8250342c0203d0300d002c5480c25260003d00190f400d200018000e0781400038140b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 727431879 1250 727430629 727430659
    0xb07020105040509010306020306030639130b031b040e04062d0e0c0418030c0c05030f070905012102040507020a0b101703040602120c03070618050c01030b060306010e 73
    0x44c01c03d029500c0343c3c50262300c074980079040c0b600c4c01000802840c0c0c81f00000c413a10000241401618008a2035401aa8145800249404507600c5545080b20307a48071210b1001900c03e114002860040c50312030b8001104500018000419000710700511580300440804030300054803660000e0807000354008940c2d29024000703408001c903088101d541032001e0f1204e200c000921070900100c844280200e90030000b082030700714509a40c44907594000c05000038012481c040c80300b000d07403810040030000d0031200706003001030165484054a1043e0005d06041c180081a40c022802c5614100309054082c0b000245140d02004041d14004c0c0c024070139400b881c20400081103d040c9464030038841162010002441c0820382500d00d25202c82101181d0010b00c800d0080c6136000c43c5520646c0e0824409039200c0c42c6800c94242907100d40900206583d05d0305003000c02e441d240071040e054581c012003e4a03880c017442c600541c02d40708505034042c0d00802c104001447ca42c060006c034582964050034241c0400105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 727433129 1250 727431879 727431889
    0x150201060305011b0e0901230402090405090a03080c0301050603040305280519030203192a0810060c020a0509130c080c120d17060d050a030f030f090c0b070201050405 73
    0x2c80940c0c801c62503910741c441200c2d03400540b400c05c1d00d2415107482c02e26600d03007a034401003500c00c0181e161884030f516240860355911f5030145c0b000b48800401c100154240080042d50710745c8014021800314615200045030300308100c1c01d0728100e9201a14080c0f0303568542c1d4044500d68406070004900429444010118100c2500c25840554054548668504a01182d41c50707070400b1315614400c00d0700410421a010781415100750550350b4030540031035000307236660489564440384211030700300440542c20040b10710340c00070b1310600075030b2481d00c207448064450008454441180b01c0203500105914030030042400c10200b500c1d440b45c8428804640645999150710700e18085034410040303075012108110071440c14071031040420303d00000800d0400d0994002805025031610340710f0034095400c1c00034545440d07400f5005c0c203a070303440025502c4c23094162401601d948220300d18640024680300000c2c04a1603544501030910303411041042407035140c0f04043d802c56015550480c104107060000058984030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 727434379 1250 727433129 727433141
    0x120f0c240d0207120903021923040207120203031005010806090601120b1903050d0302070215161202060906162a290a020301030f15091b05150a020715020106030501 72
    0x1302d58441c910b852860040240c098020040700c0c0d03020003080000c11940d007540e40c0c000d00c0c82000c01c00401c4105c0301e10340020000e02981710045c0ca6110a0b41840c140c240c0d011009600c2446442d411031a4036403140c0044a010400b15089600101c2800114a1710f6010f402e502841e02074124000c6131250b0046c000c21400780400c00e440d406601013043c01d104000050041c40906a6070389011401c005564000a8903003459040805001c0d0700080c0c5211110b000415200b503007500144600d0700c845400720000c0d035441088071038200c00e000704804222000e0740c00c0c1d18958000103954820303200c10075404281c5801100980d90031560070a040c80a000103001002e07030b4403000c3c000030300105192259094003554840051100b1a010f10400041c40018038140c85400010f800504c4120346841c0001e610008082140000e005002405024289422140c010800303450054400081c0c0c00500410300c10140a685080809030b08440030a1000304903043c02040c00c440d00d0720001c11030660700e41b25036084484c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 727435629 1250 727434379 727434413
    0x50315030d090501111612030e06210a05160e01170901050405070e060a03060b01020c040501090f06090b060d0c1e0f14070b040209060a05120f0c240d0207 68
    0x309840100019a0040111110f445d5260054a004004524210007802c0039004101200b80070b02c5081c070030b052081090246003072024188958898040118403001aa81203560000702c1c500d03400201d49400c18010640035254a0705645d19004180b101900e91000c0702c0011030401c1215103080380301981700080c1074010208500001003508049c01c101e41000307541c1d00b29039000030098042c001c0c240c6075000b805003169044a400035001010500403400c003911150300d60b901a00740000880c6020041e032040e030301503107800300c10002155249045010f403000c6940d41da6102805020503401d907075564001001e100d4942c540301c00c200a0001140b400410065580d10005005029000f081134020707580d034690090700c403d058201003155441e0b070061030009200900681401001c034040e6141d002102000d031800070250700c880295090702070391321201d0140800140c40340000e8503003036040221f815261070462880c1c807048084010070304020340d8080e07003050080d15400c000c1400400c04049024000e80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 727436879 1250 727435629 727435637
    0x60d0504080706060503060f010b07061107140d0f1209030903210f082403010e010204180c080105130b0f21060106181403070b030c0424050307050315030d 68
    0x40c1c0ba0303052000c100c40707050704542c0c0258000c0301844010804024014112089640c0981d80d4882d14a0881c000d02500c1264035034a5401050240801540e000300c81c1c148041042144c8000e9244401194910603001000000c910070f080c1c0000041000d0300084c1c0202d009040c451021a503954401040460140480e050522034000207242145c3c4200f0b040d02c09210b624040c0100e0600740c550b0103045520b07540d01c04e81a450030400075078949081d0445441110f00c48002c6440c0d5a895182202030000301c1d201d088142d00d40100381b802d807800f41c14418180d4002502c0301e08448054842c600c01041002c1300540d100510b00c0824015075034000f0703084102c1d515082c1c4440010400c02c441c40c5041c006070040d0b01440341c0110140a100035100e00310301204d40304840701071940f04cac0768042410400150400009000000200480c8130312141c01003007141d50a4070b0100006038407060907280110b40003541400a641000846c400f64400c2000d0354011503407030584021245c1003400030703140192a040e0b5502207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 727438129 1250 727436879 727436887
    0x14011d030a0803040b13030e06031f060f090f031112010f021314120c040902061902010506130e0c28030606091a0d1e05032d0c070e06060d050408 64
    0x4500619004100000c080f00c881c00381f968050510041c3e282d159000d04404800241491690b4403120403d401d00150858029180c910040c41240e05007840c002007070002c0170004804120790403440440390000e6210440030000000c00c0058000030781038182c2c940d214070040340412102d1000340b03110b4004080d400c020502d81546080a40c4022500340d20400355007090715078403a80410135041d80c100032500050100050310020b1900e008079841c0041512402c008005681d40561186010301400c84e03030f55101c0c0620800c200c00f03480000c080071255405c07807101e844c1d80303040510b00001e20807a4802c46908100000118003821038050380306070349494441c1001c00c00c0610302c0c803418103a13007e40007142c805141f100000c200b00d41c01c0402c00500400c001c107403442861607a15209840765501c10103503940c4401100c4006126040e8a26070701161074100300115102c0003050480e01c5078500c43c0c000d456954900415800c00718801003846401c10780c01c00610004004922850384075610404040ea01c07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 727439379 1250 727438129 727438133
    0x2010209010801060810031209210c0b0703121a0d0f06050a0209060f03040516090905070b1c051515210403080c0904020d06270614011d030a080304 65
    0x20944041e400760050003411006d01062086400c403160560f0f4104a104c2440da10340c442c102c0c0c9000c1c442e80440ca8a20071505004124852510134044280c094000c3c6080d40c4e4444c3c1448000748101b480080208083e1444030111840513000382060310101c4030755000b9298844c0c0441c210381181d0360115001e481018a400c200501c0344034441c1c0004112a0031418034883c5008a11103201c0c2001c070b602100e00c00700005081082c200142c4000244000420100c2c55031341d40f580e00505182c44041b00c06001d4500041107c100e0030041c3d510111510755007010429540101c000100000760034449100d680c00400201078841242c0c40240a207118050350ba181e41c2d0700038078010400c3c07800c51040000000c50034070020035804250150446c0c803805940f039585044c0340004d0024456004200e8500f410322400080c01c0500c40e40141348000030031320702c651410400d1682000ca800e40e01800ba03410b090607590710740d80c2d489500c88400745c041d0701c20081c80c034803440400039240850b00c0400b120300500000070801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 727440629 1250 727439379 727439387
    0xd2a241b02060915430f050405011b120509040605060702061912110405090603010e0706120f110406020d0201020306031b130c031d06010807091112070201020901 71
    0x1049551010340800d040c2000195240c80d2000c140340d0307824007076102140da841c845402c54191080106065004010981032011a140303030042c1401117203d03c021030200d12402804e0045041c0e005a484526080c105401035070304510321035015030b042450005480c0085e0000426110300001600e42d251a050081d0801040c0c070183d8211302d000f1917007880400c0040e2502030a03110301d42c146c05803c04004201e14401c03100c000d00d03180800442d505040c40f601010084000801c00e440d400d4400e040960759483c245801e8465002401e07403158020700080140602ca09260360700018444404034054114024410640310005c1d1a1390000200007001c204094041299901c4030040340004d505510704200020745a502c4880061f11070b405042402c04c603903441c01c0c40078003e54944042008201c0e00a4002401001c46101800740d00184551000b105040020117504036840a001020140c3c242000000604540e400d88000000d0034003106129070f94410301244641021350006807076050000c0018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 727441879 1250 727440629 727440671
    0x3020601091805030307053031060513020d0c050901060c03050901140c06040f0b150303182704050628151e080d2a24 52
    0x40c40480c2d0255030000020b0021003501ea010b407184c01d1803138581004020aa43c04502c1035004510020300f5402148640c808040c500d004001c0f8914070b0070078490301940c641110000529446500090680c0340d0000359844e0451503000d00743c200da640740c460199004c07441882400d20111404080c1c08828445800c08640060041000b0b05c0c104115030790f60348010b400380c0701d00301d402410401035001290050b4100c400b2030b03200700550707000c840082c07900b81001d003038952100358111600c08000e40810181099044904e02480780140a0f625103101c04030202090304000c1d00480d0899175141101c800865400d1140c801120109022481c0d0710b810314049003442c0740248454607410011240348a1300540c1650451070064910000580d0740c03042844108008240e4840f030020070f41c00c80c140f00110f5081d850901100d060380121101e80b2260b040560700e1004602c15080004070190b07420103124803002c8905400750050a1408034080030308919640001c030806060034264540e134900d070000442503501c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 727443129 1250 727441879 727441901
    0x318051c020606060a0e030a0c080d0f0302040803040e18071d0702010216020622090b0a050306071b0c090501151715100e030f150a0507080604020307020a020d0302060109 75
    0x7600c0c40b0f1030038200003501030142d5218501003208013400328106d62000c0041c404829003007010101c40d40d81d11403e10340d444a10030341520000c0c6110000036130260090095a00360340149001d541403d083c03918200003110014100310b07100c003801020090140040c400007001e0001002030303200000e5004441500b065015250604680c07042000c000034003004814103800d0f55046030b41c9642c0c0c2c540d280082500086006414840101c0e413940000c41c03403410751080c15000025580d00c200340f5a00c0c010103032600c1d0b00310361130400b02e580a4104841102e104283c040418400c002c00d170344143e110051305040716000d0304208090f4005e210b017040819007102e4004480021145901c4407850415009480c01c80c90751200e9000d80620701208501501510300303645410006012940d903440660442956601c8052001e80701001002c04103518221b00c1c0620b51258046880d0a1070320340301c1000344030080d0b00c002c20742c4c401c41c0140144540184d07180140541c10300d0003640203240f65410805084119151036a0b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 727444379 1250 727443129 727443133
    0x180102120f220e0610020f06070e101103160c031208010914040213150e130b0903030919030504030602030f040b090a020d0609020f03120a02070e0405030d05070318051c02 75
    0xc01288282008013607010703509403081300c0c07140316961082e40b6100ea0424016818043e5034100301c2c10baa44501806101c1030211141031800c803801205459600c3d04040c018003d4000b04060150101403000b400c0c060b030300ca01240940700365a5120454148084215140007441440040203080210b02074110090502c0c80b030f011560610b0390010b01040043e8180d05000e40e190b001c81400f203400d80c4008001424402000d0750305150a201c08551031682007002c50347c405d11040030a052400020689128134401b0380245020440d244102a032403440301412020030034104030120003d2810300217180607e041e282c181c0c100341808d190501401600410340701c1b450f4051480b580240e42d0b135130f4003004001e4008030001501003840c004900003811502c84c094040c812004040024095840101002415a42a01d0405459001c0d10314414010380e40900940d000744a0012843c429500c45c03a00840f0608002031800c21080365400d160705505001e84846c0c11905200015a010140240002d902880 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 727445629 1250 727444379 727444447
    0x50103061d040b061c051f0207031b0203030d0f05061003051612020d0603140f010903050a11150c0c15011a0304060e0111070219050303180102120f 65
    0x1c0321004403000248007411030400e0307401044c210380f80c0e0101c6041010100d242d40c9840b20840c00d0259841207416400c180555800c12080041105882510411607250f5600c0d078508160401d041d0882c0740c03060003680c0c580420060211586941d01c41c05002d110810b2000c581880c0060401102d01d0320398144400703145c2000c0811100c9500082c9880070100c3c5070404148503011241c00320028000c4100708072031a45481d6010042c41700c0c454219840c00c10090854180b8010000b00509a40c0c40d408006c0c00b140c0288459201c007400b0342c17080d01d18801c0280c1180c0002116034407290f02038000707880340c0c5400c83c40014409035144c020b0000e40250703004c3d00150741c2c0d0345d45012040c1e103104ca2907113008941c080000c00414100401030f00614030003c2100000e00407005201c0c0700070310710303800b0b004202d02ca84081200c1c44d9840e40ca1004880c11036a004010310f090142030310694404807400e0500c60f045009840d01000d0724408a0080c1501050b000c520741e845103951050f411003c02c500b0300003010094520 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 727446879 1250 727445629 727445669
    0x62301020109080406030c030608010c0315081c0c021c0c1707230d0b07120c030902100e01170a150503060c04050d060b0d0b0703050c090a140607170405010306 70
    0x1001c44044034203500e00010700c11f00844d0101d00500180d00110450b500740b00c010f126007075050708580c802480044038a0641580c0d41a02640e41302d5403400c400c6c84000190b55060440d003c4d043c50b400590000d01808104c03401e54006190071032103000c0444241c4204a000d1000c010310102460403c180180106007040c02d2800300300309541c20f1220509540c00401c1d005400d600c480e18002003080d0b00c0140c0c2c840d1810a01c10140100c490040700c0c4450915000351001100d00c00d000700303480306801030141e41c824440f02c281100c1c07404640b103d560600405908075640e0310100304c20144242d810f00400070711004a0f070076140030800303141e0220381b10383d11034020702210f8541d5808030307000c48200719034445d01c1440c03031711b40440a0520030300600c1e8002c02c3c4200c0d00d01845120345603030340300d4802503500b00815554060041c000b40030740c0b441c60f030f0041030311001803189004800e4002c11510b0002c0102d0704000080e17494a11850007030b2001c100560022404010700d5030140101c40241c0600343d06104c600e00c0030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 727448129 1250 727446879 727446893
    0xa090308010e100312051908331012050f10090c1716121e0f06090e0f06070e01080c1815040e010e060906100201020c01062301020109 59
    0x40c015010b0042e5100082a030001040c1e905600450b40030301d4218001a4103580640150061082c201e01003044c140200c44003441840150301c201c0070f108031000403501241e044031142c03035291602e44190703500304080d03212a5106a43c0295070012a0ba03a40b20301c402c4a10304000f603078409040360340d194844070140300313200c450815000203841c40031b031000480c2d078030750074007110918034055041050443c50000d100300000040f0005400302502e80380c4101021206007900120743c1e0045090f004441b003040084402d6607030f0780040550707030440030004c5070054031064924125141b041d00741c90756074042240d0003903403c024013030f880d40715199040403550818110b00103044d0389801032800307464000001c0c01091010314064001ca0b407000c040d2400d1703a45000342000000d254424007c100ca1000c1810001a0a0340202d103403500ca0313400039010b5034068807104280300403070135040f65000655409000d4464a60024890300005102051110541302c25018404252025006e00c03941164142403041c4042410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 727449379 1250 727448129 727448131
    0x302011b2616030806041506092102060d0b130501080c06220303050a020f060402060d0b210105011814040212101a0108012103080703020706021605060a090308 70
    0x1d424104140014000c0d1101c4911810000384124500a2024024142c2c0810400d1041c10700f0f8070b00701b11980c507003005100500d41d184602c1c0e00190391550203000314014100d00020400b02c1d040201c0d1180326550019002d45c0010701d0a182d00e0baa0303103c0111441c0740c0143e440707030310b24170f074131010040ca50403c00b100341c40d4041614420301a540020781152012001c0c0380301d005002911180c80f050945a140c000e11642c0300f404041c005208100c0443c80e00200801d15038001d980c02011360307140c5041e04d4054000b50601c0300032941d1080243c00380c40000700c0c0a8242c1d24502a000000081540c10614907000084005900303030303001c0d4540201610381c0701c040b0b4000c0e60400c0d012100c01158001c9a005d85103400000d500c026019820320580f00c440c0c4605d0070081c080b0f048240c13180030350341c0e13201d01c8504100036600e58400c0d401c0410794111000709000351091500000c05150140c5882050385071a401d9a00001441d88400949112441844018810103400c000010810f011107030b1192001045608 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 727450629 1250 727449379 727449413
    0x92103090609120f02060d0516080901060b0301180b060304080d050c04140f120d03060f080c03030d020d09120c0209010e100e06040b09070c05101e020a0e0a080102040302011b 77
    0x42020044401e5581b0042607075604000080180700c07524103a00c26015444007102c0742404030380c080d008110800c1c8107018490503550500d040b9819686040700e690420031001da5401d031403c2e60fa00c0d20912945400c002948030320f0042c1e0810f42c2c1c40028141e50021904010f1600c3c80c0c040c000d0000380300c4024180c4804003800e104445c0440202d103100c0000d02c29401c0350358512514800c031031500d07003440d805400c52400c403000c5a82c614501940c60881c181c9031071008080d55410f410421111161002c0c99000e081c94030030040c000220326085030340d8031603882000341081004c40e0500b07500341c0c01c40c03400f100001d015100c004c9201210b810003443d80b4000c0c941e50b02805d10107002c2200040c440c0d4996900540403400014100d404504181c1d038050804050460244ca00d070182c041c900c140300e4414054509504c2030146030710fa0340881d01d051000250031903401c14080101003c040c58071503555090640c0503240f03120005a17902d2135480007610794103440480c800300e040340d00c00e0310000c100080c4100c50319003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 727451879 1250 727450629 727450643
    0x2808010f1422060504020d0e011406010507080c07031a010e151c020301140a0b030d030b09010e040f0c03060605040f1103130c030f05060714070b1609210309060912 72
    0x40b4100c00c2070001d42040d800c6181c2061010543c4103c44856400c44103400d071028000308840318a0211105900740e00701c814602140c8100f1046000514100041c042d0343c80708401c0c0d030f01d115240d81c1c614807200c020404102d46076103d000180154a2032404031508090503040c003103008142070f4041240c0d541464883c2c2c2c2080c050710103010564a080d040301022900f40086020240b82081c40070300101041d04c8000c0c0a441081d411401c814024441c0041d10000144020502c1c0c0ca88080c410b2021001001180c400e60480b4407a130009904c00b101b100903510070303640816074038140340902080365502411003504034113201d04016459951009c03650040d840c5000031071164405d09000c2d03006481030780020701753b901c0090241c00740500410042e01800b80b0756540e41500f130903041c00c035105000750f45014020414010110300046010042d00003500070340d007800e85034140d480c0e401d01c2c000c0310180c41425000b80043d40207800c041e0306c07441b8035010f8000350070160a500d083c0400b41200c988180c40060500c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 727453129 1250 727451879 727451929
    0x20d0c032a0504120606030501050f07080412030e16030302010b06040308030412020a0807030c060b0604080d0c03021c030e060606030705031b3a061404022808010f14 73
    0x107a407007079080b640134001201c8041006200d525014004148610041d2a95403034100490581e0401c4d080c42e5008400543d21103015881d25200c3c500c1c41e49151401c0c0b4145940d80c0910501e02c2400d006028807a089824403a00780303841c2d0f00b8061300395240030700c00a12a440800051000660a100356a005900450b01c0e000e50075981c00c0a91416189141c044c184c10404074414081580c40749580003003612400f0301b44081e41c5580c080c071000380203502900c48240c0082840000e140d100756400100e09000348111800000c009402604164232440c80c000002e2301c5070301008690808100c0d19400107001c0c3e400c94590f103059000200a40409003480790b0145841c8041850182000c091b00d00482c001c0001000403034080c880b0a03100c03100e0111050220718481c0e940c0103030700c403588120411244045080b0b80c1c00c00300d04003004000e5008020008820148089a410340000e80c0c150310000c2005440e02850365041c0f0f60790280e9059164405000610904c16020703003900e603141c1c04000364841000c0c0c203500b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 727454379 1250 727453129 727453211
    0xb16050106030f050307210c02040e15090a030e03120a14040305031216090b0a0c0303151d0a06061b1a0907051011030406230a03020d0c03 61
    0x545003030b910190070700400714044014048044000c140c100e1044202e451004075140980216084d980700000c04a0b940a00f6a40542010703008030306c01c1200e500a5801e0380344010405240c0006c20740c1c103100c850b40250010410150040c41e000d800000403401400e540c500d44c59104034910544a0400820095100e20040ea4000c40107a801540d07000054039110402030700441c00e0741b4000c0703520051a24480700c00c010841c1c000d603840c801341d40f55a8045440c004400713005035505c41030400100d00300740c0c1d2480d80f001d90030411040c140142498401d05205100400200440100083d000804507032400c0820010250407003c1c0039808620035250b07691031040343c00c041d2030302c0b8400c160700400204854200604401d012880794107a4204a80403d046c0034500400c0ba1040c03c00300c01d2903015071042005000b00f90203101001285403000c5a1680b084800d5640250303182c000c4802000842c0e000305544555805500444202c201315140401c04094940c828840190300815404000620464007101e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 727455629 1250 727454379 727454381
    0xc0e010e150c0a08030f0f01050d0b0c0a021e0105010518151c05060702060906010824100f03050604030e06070b1b0d110c0708060f01170109120e030c06040b160501 72
    0x5080d50130180e0a601c0e03180008550552000490384100781c40000c00c0045103d240044c5405600ca4211241400a6451b069a441e580d88560801402d40c440c1d41005554a0f800c890300388602c03004200042810f500d458103011b0700d0302108242882c04d08030300d410480c403003802d1502c941050707904607510101c81300354818040d16a081d41801a00358002c180400145540000300706014011500c2215140d0b80e95051490320359079160502204003041011000c101c0c1c01041040c0d07008036005584110707550f56540f0001418213142d2085420344c018108000c00d150b0031080d9081405001d5840f1458585207581d100c401d80d400800c0c0d214140701e400e0090300e040c3c2c554030a41d400140e036220304001051034614020455000201007a4051280c3da1010501744004a10903002e0100c40600320300d142d00f0001051501800d061401c01c2541d0783c0c0700c4080210b104403120842030985500c0f450902c2540744140360500d243c0340743c0e850260700d0800c0100064009101100c02c4140d219401c6150a6414501f42d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 727456879 1250 727455629 727455643
    0xc0d0203130204061d010602030310121103010203010608090106050105090108010e13060c020102180f010e010807180b03041505010f0b220e090d0206090d1218060c0e010e150c 77
    0x10b074005141c4a00800c1c03000500c030301e00c440304010b117848940c10b03a84c03064200d030b0780c1c8012501e41c01e180b0841403003001200410002d04403a079104100070515910760782c01003422600260b21980002e001c070750600982e02420301c00c2d40302420003840c0a500c2c055400d4000303040b00b641031180d01d20390740038100028911101c4c5204100300c80e0740200c0c01d1002e842e80702c0009010f5048440405001c4078840701c101903501e4000c5850480440603146c440324890f8810041d600820018405003d0040251203168446282c1160001070301010104540ba4281070510600c841001280710120604d4400140b040205000ca500111102090a0341d900d02d1801e50095600305807d414698040108601141600e180034806118900d004110b4540450544c422070340c03047c0c00e44810115400070700c02c4140f01c6110f00100400c0d11119603010a031a0344c4c0c089200c505140c00711066510b0755440c800310702801d9020004070b090003030134a0325003a03c44075140000c801f8030969810015005001603100c0104200744911 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 727458129 1250 727456879 727456883
    0xb03013f0506070e0405090a032304030605070905060319021b1507261609051f03061d1f03050313030b06151206030c0607030c060b0402030c0d020313 66
    0x1103408152245401c9541c1e00e015900040815000e80355a0110705082c4030312132081c584031004121002d100e850540c1c2c040390074001c0454130401132089040d184001d07002000150720a101c002450b180800e402400d031591904120310440d0100144054003100131000040030a00340c1c030051707440b0024a82c04a05c10241d9449000a0050003410100681045103c520950030364480310901e9981c003407220308240700303204001e1248c0c0c1000042480402c0000c0c82c40d9031941103040c90320615440d17a0000d81c529140c203602440141c05c1c1c1d100024040d0b414000d001c02044054120b41000303c11864610300040000e0240b0340c0365504400b054581c128103682030b0000c54001054a5840031114000e820013401400203845902001011034441d060034018401c1d5800808800f60a10110031b005a070601000341a81d40e0500c41d01044140b29940d0800074030300c40744a500d07030300c1c0e00d03458501e0841c5c180c4075903621583c4121f1050041000e1880d0880403950311100b20307040183c0d6640c50510b845c0d22045c1c03070640 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 727459379 1250 727458129 727458239
    0x20a0215190915020102070c0603050606070c08010c1d0f0f2403090c0613060806030c031b0306010821070c2103080615160f050d020a03090b0301 64
    0x1101807520381201c41c2030103403880c0c0720300300450a900b0b44044e401d034481e50300024441060a02c04002030f40c42644010740041c0b0007458685019407d441d03030300fa180c40e60f40042415035500c1044042064008031140d100000c1d610048040c11000000121100400512140240c0821145490f141e40b440f03c00b00e0110400700c25030b241c0100641c4a148150400c503000405403250030019201451314509444c004070041c1d80d205400f50174028212452100980034a415105c0d07000355002c5a80d0511544620a10340f800c01c808411940003010318090041c1d100505a412481e0802d060307913000c081c4800c0302d41040100941d02c4090746011454080caa07403155a03003500087c10941041d06038641e0030140c1740a0340d100d0200383c449408000c0d0090130f0016944404000304500e030104d001c8072000240180c022480c200000c0610784601d42403184e0303a20b070500140c20208100c1c00301600800c811026144a2728494299810080050540c5c11910440e26181215040c80048007003c1080750018101c0001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 727460629 1250 727459379 727459417
    0x807090e160807080d05030c0f070f02090f1b0c0c01050a1e090518090a11060c100b0306090a030e0103200d06031203110d0b0d0f1104050c03040201020a0215 69
    0xb04240d150040f03801140710074010144140b003079078426400d0b00e000306d00340c07070140386484281c450070401b07035000000455000407450f030031001690f00c242d102c1d489110b0701800e04c1418901002a0400c0e050458040709148200340001d00c0b40100c0001c40e0415030b50300382003244c0e0715046000d042d1400584074100316298000c100604a40a9200d034001701143d00558334801086000340442420b00d0f403c490125a5038800501c00d004214019070300c40a9800140500b1302c1d00d001322907002d0070084000e059072161034039000168003e080030403455500c401100083d00c01547c4e595070082617007040c0350106041640f10b10045040a995448400c00c20340d00c1c03803040f40d860a10a5010003c0e11142c0b100b9500c0000c480541d001445c000d0291141c100f028203200c03442c0c040c0c0f0803407050041840b0941d461b0020159000100000c0d8001d2240c42200c1c056104d4440607144401003000f56030004100b60f8110750240f05000040c4d0300098149980c03541107940003481085e410140d100ca000b908550f602561581c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 727461879 1250 727460629 727460639
    0x50306010b04050118032103020d0204080a11010906051b011404050a021f23040905070504032604050405130204020a0309021203070c1e030210030e010c090807090e16 73
    0x30020001c480c1e0a0300da0100c91405031080d070080c080203100c081c00d404001c1c3e82c00e40d0710390058001880c0c7d078030b0b880c240103040c0498900b0718002c903046a0003d03120755000c28181d000740001c528282040c008c0c00d10344168610f051280081207405240c0b501c9040651070b410081c80460207402501940c00500b00c50700300781c03506041466848100c84d6040c1d02814940c070030002a162010b032140d50071034594485507040d00f51000060700c17107003108440030f012900c103010204503242c3d540103180c00741d9001e5440640301c50550900008900d103903150000b002c1301c0c04070026240d1918406980860b03034100c6001545a64141e04581003200080000303501c01d100045540c0c106030117500a80301c2c0384c02502d0b09200b0f4610b00480541d00e20a0850152007450000c90030030028040b240405001404490380c0c0c4e81031640c0741e02094210003030300900c0d000300740c5481c2214008042442880f00030000c41c0b60003d00b1a240c12001503d40c045405010107603500e1b28020b10203084108034032404200f040403072a207415520 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 727463129 1250 727461879 727461899
    0x705010e0d1d04091a2805060108090a0203120d090f08030403110d090b16150219140d050622091a0601120b030a020603040c05241813050405011406030d170c0405030601 74
    0x23216920301191503075010948400c000548022000c2e4080c0c01401c50b0220151180c01a07040084034212040d101e80448000818034104110303014400c2c440c1c2901ca04003490090706240341040c107600703140c0c00503600a25a662019003442110311080b809640c0d08080c085100c440d494080c0c010701310810303052001d01c9040c800c3d0300800c5a04038899641000700411300c170440d20b09007031491403614040c00380035034030918007a54012a040381004089611600c0c40520714034080c40324100c0c40d05070564848440381440300750300e81903a01106200746894a0320b011030028101c1074402c80e040368550b82e1040d80c0390590310200304490aa50700100180e4580c505032900c4c2103800c2076409036a02426080728402d5650742807803030442c000111410280d00303049107010000030103d80c00c5100c0b64001551002011545100d1207050300a034050b100105032034a04e090141048075000e003250f4002c5d030250098900c400c0c2d01c13000040c4e40000626401b490760f1503000c1d00c4e03900340c02150485a814001d0000003d000448 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 727464379 1250 727463129 727463131
    0xd0f050607090612020903030304150914060901050105121c0509060f0c12040609031401180305090405061c0803061519120212060103020705010e0d1d04091a2805 71
    0x142d58880b95040c40421014085e03024485480d909940140042000114101440704003480040b00009401449481c0d071070401c0410810b5140c250003500600c0344c0080700780a41030150006a075209030b0711428001c0265506012480314506550001600a0321351090781140d401650003822030f6200d00e00000e00d040d250b0301c80c7c02540710780d10911040000401010082d0b0b02113a1203621408051465074075060320101c20625080b440d9540c5103c80c544880c81b81c00503062050182c3e45007030315a40804284011503402800141c800c42e0034080344256440c80c1d12402d00b0081d4002e6081d500d940710a404035810054405101c1041100030455041088000c81000f040558907540c030043c04101034562402c910079901188071490116002a400f940030f5001888070500c50800021507004601145007003406200000d40011450b045009401c03501001c074201d42c100c200c1e0704101e4101d2654403400e50050008989001c01e903030f5400100880c0782c00b04032004004111194107041078020b070044004102c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 727465629 1250 727464379 727464389
    0x9050c09030114010b0702060a050d0207060b1309050618070503030703020a120f0203070b15040608010516021c0c030c060608060a050106050a0e011407021507030f110a020d0f05060709 81
    0x22800f407001040307952090040c0d0407039410b4128640780c04642c0d024050a940000014004c2c488208951000c81000d84002c1c080700c2e01801c000140301c1031030004c00c40c40d1611400300d10040c50800c8910b80c007042001c91103507041103034a000b5014030a0300d880c2c21401c1003902c2c0e00890345400045103184c145034020825501291080c801d20745652a00303d420b80c1c1c04542c601c1c481d00140d005204501c000703841e10300b006400403941c4000207205241c4074002015039940c1d03000a611079446000b07210b401d072040c12014010384c0035800a00b00c0b0b40810340000701c0d00c502d081c6c43c01040048a0011206242c00b9030018400c280d001001800020f8032803c00d240e5407602900d400c11403502d01800041c0705441402641c20248181e50340c0c42c0e002c00c10100440b00c05001c6004501440c10070060344005079944e80058028078803011085484050070300700501030b01c0c02030801d0010b02410002070001050085001c01c0c6055049806148954841c10005800e900300c140040c12846000d090115080c0c101c1c2c1400c0c2151 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 727466879 1250 727465629 727465631
    0x6030b0601030c1e0c2f0306150d06022107090f06140a030e010608030c0f0709050c0d1e0c0e09010b1312170403030f08100e040b070909050c090301 65
    0x2d045510f0403907210350700340380f401180c5402e8000c402001c0d104680141c12180902c01594080102040c0c10100590350408940404035000e032240c03c034141801a07c3d0710006c00c07411404500d00400c003095446107025001070003203600107220550f14012005803403698007103141354525468048005004501240280c0440c1019908001040d07849082d6a0003c000c8051104c1e080c81001c0c141540541402000c500d0b0030f548414000c600c50204102502040c01240024100040310008403800c20800d60843c0c0b02071800c013402c00181c041c030041107404c213140441c000900320804601015034100d100e0013149105081090004656030311101345803940200300d951200c5641e81e41c0c0354050600c0b82031009000d65460b00341c06c000c1640d000c0e2894800c54098a10b10000811503402840b02d50302640003107021070f156a0303034000c606a009021981c00560321a4500d1040d041134841c14000c10001e1005200e4801040014a1203206105240c018400c03510b09000074140500800425002410058065 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 727468129 1250 727466879 727466891
    0xc0501111611030109140102040e0603060601091502070e040c0617040506011e0503060103081201080313050409110d060218010e15030c130608100b070b061c020406030b060103 77
    0x310065007101c480c003a0070038080c007a0300d0550390b035000c0781c1ca203810807207901d5540e40304c03003d0208100302c01111110400304001a0b4880c2081541b411507140580481d0090340008d00300000c60360420b01940540e00000e80025082114003801c0345482103c1d0003049030365440b80c09100c20403501004c2001610025202c7c2002104c00c1740000403030300c0c0b04860140c07076540070000401c250350b080b210502d56507030313580e950510315030f11703080402d00c1c181003a4801c40340301c00d000a0180901269130002405440401c001d14580034442034441e00184440c000c40c0d22031960b82603404204102c5109103d41840040c0000170b400f20b070760a01800a411040d142100c00c410303074180c91400d6100d40b07030558682200800d000104001030036609000e80000f030003030340030003400c2280c400410b0448400c0002040103681d00c81c4a894100800f0010111540c0701c0300343c02c207041c0412400035240d0fa100980c000c6054500c401e07124550305c216099507550500194000c3d180042c044180521840707800d01c00c6001382c8050003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 727469379 1250 727468129 727468151
    0x715030212041101030b06280504080304152708010c05040b0301090513020307080a030e0619030e030d09060911100906030b01170c07060c0509010e040e0703120c0501 73
    0x103a11070000c4500c0614030910014000480c0024071004156040c90000b540054a0001c80d88030381c081e0803160f454280c020100301200d0700c688030021000c0140d260142c105881c00c50501e659004a000d42c010f00300c88d000b0031301c044501c1a8180d20b080f00f40f40816800441e03400c1500301681e001c60154035003a5003000b1043d5450360282e002c0b941255400c4140502c1c5031b10b8101c0a00003004051f060162500800710203c001da9010440c0e40041d001c03002c0981402c520a00d00503001030040c207000b40c02800c06002443c040e17151072900c4040d5039a0360802041300b420f40d03002a81580b140d03204c01c5130418608404d030300501c16194029030400d8814003603403a0000c8031504205441d5a0742a075840014840d04060003018482c5d00800e948244c181064079048684681e0036000d4031040f1400317000741c6004520301081c8513440c004c100c0710300740509146182c160540002040b8504480c2d005000d50b4603241d400c801c08008203c1080150b81042d82c0030625072145400819410b2103100941d040c0d0b0800d199040c2d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 727470629 1250 727469379 727469381
    0xa05010f060c0201080a02130b0c060717131529030c03060105130f05070c02040513210203130b040611010506090105090a091505062103030612160305071503 69
    0x10541c0c250751203241c21200c031075004550001000304950784a40d028822100300e03e05031800036002c2c14000c0446034450b802c005016181c058010412000c000c50320020804250045d10f0031600326480046199400c0c80c0d034241000e050f146074660481051400b42c1d204a045030500c00c0c075800403070750440d5000041541d030405640c1e0417403400032079064002400400c0249020001400700c0581c0202c0420b0b25000b0911500468004540b0200070507040b400c4a001c40c9044d106541d402041c44030781000003402c80e00e5880944070b41c1c1c0c1d10030302000541008580031600810079070741404465118519415101c260203010343d0060f1142c1c802241e40d0081700e6603140018059036101d448041c00c0c0304081c0e031a1204114031900f0181060502907614031146004c01d0040c00000792541d400003022446080c260107001c070101c2c0c0106070302852200500c820007003d1020045035001842180c1194681440403445400c2441070300c850800e07682281c0b400030401c140810202c0c00c84500e83c81e035204100c00c0784400e030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 727471879 1250 727470629 727470659
    0x2041e03020a09050601022b090905040c09200310030212030307050f0d06080f010902150702030304050906011b0309090507091410030e0703080c0f0703170c011509050a0501 76
    0x3984a01c0c2c8182c00e100004850744800c4e030042051040310522040880e54950500080b0340c0740310800c00c0ca107401c002e0280c003c40c54074024031008504016611306a111038000b0354050103006d2a942d100d02020503852100301d00d29401c0210315400e5540e07420122040310310804203200403402517200440b0b506c1e9620300807050f03902c901a19261507180c4044103c800d016a4072400c06030040940c0d0301000300301d00c0400c1010603099010540009501444d0380100811912450600d0441c05c400708034800043e00c000c01541e044036400e640d0411241c40e801c0045c0c1d43d00d5112101480b0344000d1030702000c05d2661100c80c8a08480c0000010440c03a11101400c4922400301d00411400c15005810440c0c1401c18030545902c40019180c00100780c46410111810101c0e542d01c1a6403588010035100300018050288198910166005258251840c6e8500080b42420380060a01c403d0100c2c0d6024085030a41081c1c016005a0318201034641d1220030440042c0070565102490a16010020071032008480d071314 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 727473129 1250 727471879 727471883
    0x31d041e0e120703090312050f0703020c010809010c020a0201230c0604060507180311010c060204061d0f090c1e1207031401050105160602040801020c0d1106060a1403011e02041e03 79
    0x9891750558903442c8540000e1403482c81045000c000b01d0510141020260010034400d9010700207c4281c28001001d03018003a0403120300c2d034542458a0750881d00003483c00111542821300c0442250300c800e03030407400c59040354035100d40900010031444406002c0b50880c441d91249030704003d691034444007100c0ca0201b0a454401800c034008090011580b07400c1d0307006d81c0610501d0300340074580e41656100141d800540c088408201c154212010004030b101e49002c07810380030b40308a0400340c008000100c034100041c02c1d0723003414500090b03040c032074500e021500303120003003d60a071507601c0b0021390809680900441d04c090010703213000401140402460310860480d0710580d1032605044404020506100300000704440701d9900f00b00000320900280054510807038000d0240015820f012409001400c009042004541114003081100c0d6a45200035081d2009400c001e4501e030444808a070042506035070341c2407140c1c2c2c00220b44280c41d5094000b03009459611900401c80001d600d0500d20100040c040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 727474379 1250 727473129 727473137
    0x3171e0f0a02130f0503070e0c16050a0501020a0e040e1f1d0f0c01110f062418041b0303023c0109051603031d041e0e120703 55
    0x810a448a0014201d03004401c101c80189040f2400342010742040656101a45102041c0401c014910b003e0005900418120312111181c1c504101c040314144580814003103003ca42c005c002061110030400607500700da002c0001c55907002044030103400c00c1031202015104605015a0b1011180d01140c0f80391456070144a42c5a03d255846000c0e0240c04501018090072031252194011028108100c4100c200204054030b4841d00607000107107a200c80280f802c2d0355900070b000302e6000c914000b0b0020390100f128080c045584a805101c2002c0c1c840000340140d05c062415101c00708510070000d03080c007c621880300d80d40c0403007081d410102c469a01e840083e01603044062007a280d400c07a8030f0089402d884030781c07003044000c2603d158020595441c907e0b18440d07070354130901d81d000c200040003014600740541220b000c070f9603e5a517005203409144088141c10000804840720a6211500320007210004210401114046c00c00b500006100c05c0140d1310303076445a0310400030302042c03103001c403501d0350b415a403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 727475629 1250 727474379 727474381
    0x1210090c0503150111071805090102133b10080c0609040225032c0a1514040915090b090f04080d1103040b0912041511010903171e 57
    0x310046000590250040c1401600301216449074010b00400700980610b82c0c402080c44400081f0004665000385820406c2e03104010042d0041c80559403081140d0b412411107108038640c1500200d030744601c2a100101e4074507085121481c0740f00151a80c03240c4109855201321a50f41d10030b2030390304e00988001d160400d030204800204c50405030014a05800c280000c03c0c0410144100544200d040f4881580081e0501304512901c1c6080c4400305180e2260401424400c2c0003074000030791a10b40c2e886690030701c40703200d02030300d48003401940443c02680c3c0081c5401d803955a6206208094408506020302020b00d1a40200300d41d110380c400c01c108400c018054016135070311050440c600c0034014006880c540d5007444103907100703d545d0198419070f010213000b485d01c03410b2510340781b00d04050140401105400000a0800c40350000080d642142d0070040d03c4c2d440801107000580d4143c3c20481c860b4010f5080001d80c5061680041042c580c440101e41078286c10750f141445040d00e181040d50b886d165081e0780d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 727476879 1250 727475629 727475641
    0x30a290907080403200102121e10060207060e18070509040c0302030c040b0c0a0b0a0f06090e12030604200408120304051908160b10060215041e02061210090c0503 71
    0x1084190360b41a0305d00014a0580021747d000200341003220080b8031025881248882a03a6a100481c2c10402516041c0065410003070043c1d00d0f6151030041c08104501c84400a07020f640300e500070300e00030190710010011814002c10060481d80b004d40c00c1c1d400380b4101004891301c2ea01ca4401c491103900460304c61803d0a0502161714495800031130300e17070280d00c54140300e00d010800b141d1180f8000c00d54080b0004003529000b003a881960342c268045900f06280404001f500440820b00841189104000c242e070b80d600c000004008201d0881200700b28945041c500e0030030001d2030010010381c0c407400211895019140d040d90401e2000300d500402c00e07001031a03004070310440f0014062400c0e21a066840c20b02d00da04500780107a4054180950f6040703d0b52050100942a03040e40700043c1036644041c002c1e44002510b483e01c1e5420140004041080d1108242070040301c0c0d200510380c0036070051040c0e075070304108071407141800c0c400d580d004952145070500180342112442041a401800d498990555842c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 727478129 1250 727476879 727476917
    0x304061e02030f030f01051e0d0605091207050f070806040c09050702011d10051006171005120f0c03060403090b0309070b1b010b0f0d08030a290907080403 68
    0x441101020741c0700034400d0100c440720400145220300065a4448110742c074190030442c106009244034412106a5081c000803519060309225039036810103000710741c42d00d0f082070b882d1608017501c0e960f00a80d0303008242c2008000d00400c02c0e01c9081c10074012240d0654480c40101e407600d0b01520000c04040c00340d030b410016019540c0101c0c0d4400303d18000000c0c212544082e0060400d0300e404d440015400c00b01c4014820340c0c2c94815550000c14400307400c081c1c9400c00300040c16600400a4070f101c0c002c0341c0c0e0000794040080303803208400741801518018980e0351071811700759a01402078100c6090702500125544904000548502c540d425642c0d0180091812642e040980d2000d049000b4900a000300418050107540040011007820100c120006407041c40c45401c461500c003101e44103402060f120400c40d900c0400401c4280d41005200e5902c1c0c850712352103030003083c60b2140302a030b044007421a01c0900c0e079103202d03164181405a490f094a0764480300100c40c1090101c40c01000b2811760005a4514034403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 727479379 1250 727478129 727478177
    0x1211030c2b05010b0415030c0801051908030d1e2702122a060f0414031504050d110606241c0507020c03030a0203090402090a05091008010c02030406 65
    0x100550300e40c01400701e80310040690303109800c02c100c03030040060204401c40d448a50407004a000b0702e002c00045100003001841d62506202e4170b84110750305082e14a080780c41450341402080e580b03048a2340c480c8000c0c1074001605e00c152400014841440111035040c0d094015450a800003d03039901603100404000c50b92004415001d03030b00305609140c0e0190b40c540400040e40650045090b20140d14084100ea200a4480d1686540203440601c5101030102114013503a080d100d00d001c0e01546400d02c100800d02c1d0040c5500c182905032078050910080c0000400e00345103111040e42c51102c6c070844210000d80c0c0e1034094481940141100c005030f9800344210300e40035419158122075500c1c110082081c100148039154029800030307a5039040c4400140c0400418040044c1680a98180192220003944a00802c0e070110700594002030310304005c1c0e503811b8142c00035200c020f12401c40c40c2000e143d1001040d80e24054844558640340648a429000005490446040d070352860708411200c420f1500804d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 727480629 1250 727479379 727479427
    0x1030513050109031e0f020a0212120703050903010c030c0e0f1c050618070f0308031003210206330d05060f070e09010f09090c050307061211030c 64
    0xc112480800001c0c0d00b8010000494080e90b9500d001c1380a84861580510802c14103405000c2c0c0a991891460b4010802d104d0305901110750100100c4420511402c004944400c040002e4001401d0340c205a0404007512003400b040d0020440e09010754819011603880041d180041804400040364615001d010800d00e01405040001840782140c60905038182e071a01c21541c0c1d400c400308010b050710103031400040031000c07440180400c07440c0c1244059584203d01002c4c1480e400000081d42442018606a00541d8007003034801c0156022a401c003441c0f0401e010034401401008007245070400030400100d08202991100a00c40500d8114807004280c0d503155550400c0030084600c021030414404107101d21410325582d1018603050100a11905a965102d4030803e503580051003008803072016503007914004480015100c2050030300250200e111741c0465814807415501003000c42d4410520108040002c005000c40340744d40c1c03030303a120500040780e1580c68060248501600004443c443c01d0300d40c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 727481879 1250 727480629 727480651
    0x9090602073806090c16080307030f0e0304050d0803041716050606010e010e010c0201170f040213050412270315060503030c03070b0705190e090a0c02340807030c081506010305 77
    0x240d46c03540c841105030030490f81e903000310ba41c4001c0741e290b0800500500801040010207035207441d081400007800082c0c00d05014000e8034000c000901040001038091540501302c0d4503040c1c582c100c0410075000b268410780100e405003d2000850040d501a0222072102c1b41d0507144d540d07003801000011984c10315514001d90401c481c6031084450700d0005d082c178a0042403003c030042000d00c1c041c010301c00000c3c51502c80414040c80c00e400c000109452480c5201d0800c1c0344c1c0348c80703207141c011843c05a80d1860110084c10343c40c000d6003000405c1180000340454884090070742402910740e25020181c890280700245002c40e041006620002007100e200c103688009617040003030070180c00400103a03082080c0d00031500825070406104440303243c840606a8445583c110501100750b9042c0000e440e8503440910701c0081c10360b007110680343d8007801c4030406240881c83c0084240d40e030f5000140d80d00c45140c030081e14245640712000c52404004590281c0f003020042e1140c1e100c0c2c031290011030040c00000d110306000c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 727483129 1250 727481879 727481917
    0x1101050d11040803091014030a090201030b1201241a09010c05070b0a090f0302060d2c01140c07260d0204031b0f080709090602073806090c 61
    0x10038400307030191002d0180741004603240d0360b81005000c002c0c4130300000c1d0414400030140c0030b00d20b49100300460f0340c80196064003040c03051951006901414469000591020705001c401071070100540c046081d0780700c0c2c030032405440601c40e880d00b030b03141903140100108601080050040c174118180180190a018544040c0e40b9a981c1c0ba03060810f05144c12684840b840003402e09a4180d101492501500c1301440f103042d00d42c5554005220391194225070080b02d61640103150034500071058010702a00c150071000f101124035921580244005021104004c0c0a0303000301e0141c107a408262503c01d5800400011001398605803200407030300e00540c100c1c86803010020088150018005040194030480c1c07804040d0050030030100301d11403142c00c0070b10160107180f401c02c401d400c005204811200030050001d00401d0504154000c3e104091006e402401040e0101541c80e0031004030420790300d60740c003100062104d00c4c1c104090030403065990701d500c0f031021404a0040303004007005001a1425100034200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 727484379 1250 727483129 727483151
    0xa0309020d2f0118150c1403040612091124040b030f070309020901050105130503150601020d020106030302071401020a050f06060111010204030f2d0605060a080a1101050d 75
    0x2508520702aa00749448075502401c1492840c03801000582e401d080c00e894413040012006041c0403030b1302c950a42403d07001e4500d181a4040c6041d1840607070840c0413020440d007610307456940e07984248076440014481c50810804002240324207010150b0180c40c000c420b0400c042040001c59a03c80310601601c26800c0c1034051b01180c2000740010320b602e020740b68480c502141c4174405102c0041c500c0c800d01d4200111900140d4503403080d541503031400d00f0065268035403110f101c00700d070302c9035081140c00d0700c540181034020461108805110300001d80c00c580c10744144c107000302e00780e034240d02c402400f5030304c5428144007100344c40d8200c030007040d01841150480190350321614542aa09043c04170503801010510080f541c5c4440d6000340204c140e0000e610789032640d40c0c2c90740b00085051000d0070b051074000b0100c4102002c2d1182e100582001840c07060140000c0c00e01500411013a00c1d194400c40c074401001a41920100d100141c41350402d5001c401042800c0042d110751b80650010500181c1e16041498 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 727485629 1250 727484379 727484393
    0x4006090c18090c050102210a0c060603140d141e09040510030b010f1802030a02070b0438070e040f0905030409061a071212060e060f0103020901050a0309020d 69
    0x44141c0e030080110b2000b485060800d070440003608918110740050284022101e205000440c09072400c1c4600c59407040401e4040b0b82401510100420b1706007004000010b103c0001c1c400411504a102078a10908020406a03101c03841c01000a14240b03050100001c407910400e8000d8400c01611885440c00301041d0024049038070407540b480c07010940703220030f00a00c00d840002e903014042e4181090440e50800700024580c1d074019504500440e000400202c03240c3c001e4050703e91680e803000e10031686003042d1404591505000010082104040c40d00080e0810000740d4150904c0b400f0310090360b603459820301104c03880035040541e60455110f041b4008810f405104003030310b01b1f02030005180c985040c4141881540c07510391000150200304001100305038007a908640049a000e47c002c9035200011034195011500c015000041d14a00800014541e80402c000c4d071003a20300701c51010040007041c006400300d000d901d6074240010814000080868002d80c071115070140010718058001950781d994036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 727486879 1250 727485629 727485659
    0x1b01050702060f0a0225090908090301052a070803131a0c1809060a1e0306110a030b01080c16140a112103071211064006090c 55
    0x84003090f0002180910140d05100c20320080c40c591102410f0a42c5072003000c4818440c07400340085080d50380a0580c10130800c101100c2c41c6c803a001e8000d001620340321441100500e10207441110b6981d18440d90035001c804141200e0b080c81d8416001403e5407103a0030b60300004070707081c80107d0300102c03036800c035020703041000e40726a21920f20031440710fa540f4064110076040d0075408034960700540340501031014540d500080c040540b185000c0d01c103090b1461104909003420a5403014041c14070b00684050710303080440c020f00e444216510f0500503402d4000046070421011070347c1031000d42c400d016101c0b805400000ca035010601800741030440c0b014603c11981041c20700c050071520010060209200d80c01c0550907003003100c8070005c0120380381c0c0e10090040c0c2c6a11502d10f0080400c0c005180345251035000d2065000100300030400c40d155854032045041d0184d9411001c074480b41c442c019041d074007125815074030b102000e1000000540014075030b2040060705440608a50411102c400815444c103110000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 727488129 1250 727486879 727486897
    0x180102030d1523090112081902010b01140a120c05070c0e04030e030d080f071709070e0c160212010623090c07020907080406061a030f07020c031b0105070206 69
    0x19501500e00b083d204800203282c800c80c41500c00000e2141515a1401301341811566900c0149681d07214074030381010f6502c140c508032040401e01c980343d02011641580704030000306c400c1c0c0b96140340c04804c03107100005000342d4524400040b41b00d500e088181100307410510b008030300ca007420b41c2080740c250307079003058403800d50428400141c9080400c01030660084500c0300c010826006000c100700040d40003013003464010800002080c6000c0411401c1d03120f0400a021031400100c00320460815a00e0075880e072009118030216003d4401c0070404aa108404803001d02c5015151500f10385929070034000710038201d41c2c00481a5503500303800144041c0d114644a088494418050aa1a55001008122030002d000d4000013202407001100588855801b02e420544030300b0300d60700f15601d503c1c1c4003000d41502d0300001d0803c0301140e481100700d10608003841c09a05a0309081e0b03455510700c40c0491360351980030b06466040d88400105018480c210002d03481200042c9010303441c00c40b454010400503400b100c54 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 727489379 1250 727488129 727488161
    0x1309020f130f0c05040e130305070206030403031d0d0f08180616020d02061003060207050c060c0a05011805060106050a2703020102010e0c0a09021b010906020403030206010f0b180102030d 82
    0x9400b503000e140d11582d440b001d25803c04034100760038861500c2e40d002c0c0080003105460007215206050601660a48904940c000c0c2403a0b070702e142501c0d005014242c21261414448211404020315400124103d56101c6141c2d0b01c00d441c0303010040044507081c0300944100200d28035104010382c60002484198440d503d9100741c2c490b4220903800003850103584e4000041150800401e00801c00d0b03500c010074088a40280026803960242d06149060010341400d141e03101a002944500c00c000101c1d0648916000320001c00082a8a04007100706590740d4800603e42d4204000600003140190045e03c00030030707146000002c10034410f142400c0030302210301d080e2015007025010002c40d0780c240034401c14107010401514410700c02001007038101c0d149000344102c031500406c00b1031102c40748021340089025004003d015003001420408003e6204d40010b4005005150001c2007010005540004845210400358079200170f951384000d11840300c90f050760440c003041050b001c521005015205a401c10862 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 727490629 1250 727489379 727489391
    0x16020301091a0c0a14071a09010b0f060301050f0d050709060807030b0a2c0a0203190605010e040f060c090b0a09080c030c0a1502010b1e030c0405061309020f13 70
    0x955003450070b9005180707100c100b00800403203600300d070300403c0380b42c662881c0d035001c90702c8100a1410912032448928050202a103d008001070000d054110119100e002e0b81e401404a1030328062050b00d00c400d00801b60400211140b01c0c0c0242807203c0c1c80d15005021350180d880341600d03542d1040a6481c7c0380d0041f080c540c00a002441800548415550420501c5504101c8406c00040040040d6455180d41ca844e0079101c204c400740d540180480b48407281d0080a586580128040018002c42c000e241911410300d003000200300304041d065514041d5030051883c0410301101c3d039a00c0b0117407c5140b5180104200341200190070504000900150b80e110340387d00c1c1380c1a00301781400c0c1c6008804a0034a10980c002e11545a854a4018aa000351128142000301c2d0022480b0242c0c05404100c5030160012044002d0020300a0352043e082100d1308100d00f5605650125000c001c02c2c0c400130b848a552010999912002d0b80849521442aa070f1010308000703440e10301400080d80c00c4492210079403185860b50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 727491879 1250 727490629 727490663
    0x305120a0305070f0e0f060c0709022701120504110d050d02012912010e060c040608070206150d0c0812040306060e0c19092c0709030b0c1602030109 65
    0x1000d140d9004896141c1364140001455005040a046486481c040c039004800810030f070302c0d0a011283c030f07909100c6c1220103050750790036040d0003036100d8200d4458040510240c0d640b1156280b024103144081691200440041c03100707083e00034040500100c40c401d407407020180f525120900a40314990184001c1c0200c920b56480c00390035124000141d91b10340c85400b40f078205a10034558007028011041d1051039180c41480d440c0c0740100840e401c124150b204020421502c0110703c002403064400607601e40da0f283d1250707c03050b40d8070b420a45400760a03424420030800c0ba0300b8201071445415016140e005240781e42c8184003400c2c440309940da88403480c4002024803d020703003409110001c0190b0702803520700d407400501c0c4d242640034015425a1411145000c030144c00d01c600a560003414559121400c1081c154620b80000707030240c907442034100728100c0081c0c051b42c0107003612003c517604080c0381c03403c1c6d0741d41001002c51503205484039400f500018900341c0260b00c0c240702d40b80d0954400d40540d41d415040d1303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 727493129 1250 727491879 727491881
    0x90c03051f03080f0c1009110117090615030c0a0f0f06020a08120402010c05070603020a030b1c02063901050619060311190e0910030c150302040305120a03 68
    0x1811480007040e840d100420000c1c2081c1d003119280b402026000751240001c00c4c5003420301e009440e00c0c006041c10824084140450064a01c0c602c0d102601d9803a407050008800c03070140e1804489041c020b4019400081522920340c07241c3c038003001f0044c00c0e42e21120b16130000030306400c196001820402d04120050150360030102d007840141c1114001450320456655959980c1d00c2a11070522500d1219800301d021640568100e0929560040644602076201e102c0100290004c0e000a4000b90a0003051a03070341c00c0500c040c4850400c0400c000c1e220398944c2c0c003445101c0d0f100d4200402c500c031b0300c501111440c02c0f000808003d94013400000b9280c14102c4203403d42555005003105101e0000b0071888000101e51440391000ca49241c20045403102c1544d015040c1409540c0e80a08130342c0e00500c541d40c51030b51007000908008170440c0c0000c007944413400300c40d0180865000040c032210000030144951007114150708030341032403031070054070b03054603585e40070b0030800e031074003c8401000c0100d02c40e6000c42d01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 727494379 1250 727493129 727493161
    0x220c060c060e1e07080106080a08220b0c0624040c0e100c1703061807020114040318170322051801030308010e0421020c1c0b09060906060907020304090c0305 69
    0x2041c000340601410142321075224504d01600030000350303000130454062410300b1100070701c014a03512854842550340451030303100d500c000c2d2505180d0080c0700028941700000b8070701c84007003442d4120300c01c070003d101c005100007850b000aa0314144065284948610780e1403502c1941803d070190b40e01c4c02c0c0388480e8075100750360310fa0000f11445000018400c000803a150b0640c0500302220072500490551074036082a80104200000e54984951250802c01407542268003400f15095072885c8006156035a000642d0310a68807a50520b5500204040840345580401c41400020345620708070301155035000048100e5101e9800c40d0f2001c41c0b02c0010014150403e00e51401840b081040c0c10702e500c0c0980e245400b40c000b48004441345002c0005c1442c2c3d00c1d20800100e0321001001d8240c41c000300344400e1500c04010f00c1d100c100e0b00c2c0001040005c01311180800c0a0380a8a100001001503458503001c21a282e01c00a000404620041c000014611080d000d020003419007500d00044505007480c00500c4081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 727495629 1250 727494379 727494389
    0x1e040f05120d0e21071506030303020318060f07030207030e0a080105161d15121009060902070c0303210930090504020a0509040501030803220c060c060e1e07 69
    0xc08500c1c4052240d4a11108100308000320503540c50969140c4201511061070b00c06c100035241407008000c154040d0b0066004014a00b2504480f1080110403652084100d40c14134450300f90a01080400d800303030b0050405d003882400c0c6034012201220110f0752401e00ca601140f0303141e45603003e002006480550300071b034401c11843c03c00070501140003004607404000ca20140140f08e141d41580e071014501042e030700c5130780c48400c90043d14103140f10080300074119405407032000b40c5071000000e0240d5051003110841c95001409100c15442e503207056036502201080c3d40225001c41071400c0038042035200b03a210061091200618071087c8551003c0020f02d150310071040001040a1448403e41024058040b22070032240565601c500c110102d925010301d1b1061500241024004803c00c07440401079445140345107000a0b40058111003a00b94109007980505945c600b0390042c02030500c90492030b9081d5005030000304410401d03041c414600b48401d80384041c40e43c00c041940c0d507071000070700c41040108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 727496879 1250 727495629 727495633
    0x11031203090d08070f081f09050a0608300c030903120a0f080601021506010908030d05060306060f0a210c030b090f0102040b04091515050a03060e1e040f05120d0e 71
    0x6170450405404140c01802c01d8861002d461818031440b88000b41610143c8003c9000740028140315003564050032850081c050140140050910340440008030584411580d08405201ca0081412601a9403040c00d0034401c2c1e01040001ca0070b1500c08210398425440c0c1070701e11560b40c2d510031100601d204031010317003941000f00c09820300009a80c00039042666004225100d080c0e078035243e006231070034002e80e80030b4001400301140c139211010403644801c0c4580300580c01c1d81c1c1183e030f0710810452140449400300c0d502981c068002d003c0c205ca9080c007921b150f02c08100d2862010000c0d00e6015801540780d00448440c0811701c02c00c02600d10a11604070001c1c0c0c050029810b160a001c0d1001c010b0282d03001d09040c4903030342c824051070b95100404c2c0c5c100500d480c4c0c0261808220314200245140c1c806500440464100750300004c01446501955101c1c1140c400a000068044480500b0008000e4816500040c41c51561004240c0a001001141135100012580d07500780c03030141d00640c0c2910080c01ca02e030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 727498129 1250 727496879 727496897
    0x11706010e1303031a120d030e0a020a0608091f020a1106060901050d080702130506100e01020c0103110702040e06011e140607080408150105210a11031203090d0807 72
    0x5050b0003074210300c1c0c0c2d85402c011400007001501100c5106020440305d0703202c0740ca1035007001e601c0d6000c02c0034101620300c0e036001d2190420341c00204e1394480c0c1940000b900143c544800308a002e101d2005240c000100c84299034804500901c10013503814500901e91005a00051921840743c00c4001e1050541c0c000e8040c1c82e542c40c001c000070300c410303c0511503240507264250b440e80800c0103003c12940d16640c01882180f42c070b55468241c0004200440d05540036500e0040c0c600c03000c900038000020040700c1680100f072245038120045010301811400b400310b0708002d00103840180d89501070300303680521610041c54150f140100a03201e500b000d101c03a041030649101d0610910341c40840c143c84581c41a00c1c000c1d5545040e00d019051407055a0100c07810380542a080080382d00b00b1202e40b8100e61045901c0e040300b004a1504081402c0e2050400c52164081080780c000246460100b540101d4000c041d01e04004c101a1a00600e6008032410611038201c1c05588081e142c06c035070496005000e600c2d1030024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 727499379 1250 727498129 727498141
    0x905100e190510060921080f0c03030f220803010b0a03110703030e1212180a0b1501020d0504140d0c09060603200f030403051c0c08070f030c050703111005011706010e 73
    0xc0c406d1602c4015251031000036030703100700c1c0b030381281110b5610070f003882103035900d00c0c01e00141140702005039500000124812181042c61804540c00c6c103196070011342d46441d43c0d2905a0703e40d16035104080000500d47c8900344004125502d0340503240c031600945011480f0390401c0542800d0581e161171311040c4400c180503420702d00c0a09840302d42e101c1022082c8201082c008000285414140307600100611300090420060f060800504078002070203800b01c3d6030001d4008800d442501590184842500e44c106806000d4a44400c9288040d1f005460b410801515103c006066071003940140022a49604500c0e40d10302c0c450381c540102148154130b0340d00b000981c4401c0340075803002134805030801c0030218003801c9002e50b02583c107803105038003003080001d0000c036003000d4641f9004036180300c0450000740310340c3d035075501a014403080204e98ed075800d031400d030690350142ca0384405000108070505c02c0a110030a0b62280b44140d501821243d80c5d002000d900081080b03241100507004958070700c49800512207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 727500629 1250 727499379 727499429
    0xf0b010e090304050402090f120d030e190b1302060d06061803050a030c03140a090314010608060c0f040b0d0501080f031305060903030909040312060905100e1905100609 74
    0x41d00c40807038000da070300c80000700014240310fa248c101580c00b410140341c4071003490000549000b40002c1d41c509000780300d004100903449013100030300c0740e001c45001009040084c1038903d680e50301540034801700007100d4072500841c01c1508200d50101e4507549d100418048a0b07000040c4d8906500c0346039040301c6490a55a0756521405c160320020300780700411801c2e0782010702902c6121681071207501c4090321401c001100030404034240c40240d66043d003c401e601043c40c818010304042d10400801850941c90b843c0040e01964004014008401401d20010404440b458010518040c407030a0208440d4101051141008403444000d0307407a80c070400200d241031303a40104220031908101c8400341c9504020011034103611074080d919a006050000300000c143c0c0040e0240c2c0c5000c0104420884907840d040ca910480383c0c00c1d1014203101000040400180c5081551654020080101e1051040e5a00c51800c1510341c1601c19075a203030b01e542410b00103540d210243c03000612070003c004580020f101000c1b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 727501879 1250 727500629 727500637
    0xf1a0109120f06110403050a06050609060609031515030f0d0f0804031e0905090f0a052d10080f03040503010f060b0901120213060c050d080628050901030f0b010e0903 73
    0x900f40d5844021400c111a801010340e002560401c09958641401c2c2c503200001b03210840300288644200e0000c21058107004054560181001e001862603403081802185400c1008000340a00060481c8501e00c0391024800e08090b8003001c6d00412001c0a03884010340440d6030b0240c000d007004802c108100100740e1140003c02d180c0307000c00c109000c2e0310131084100c800300702a0700300c1c81e000341c4907400f8015103e0045a41a128401c81c4108100b0794481e21400c0c0f244000980c404010b41c1000d4a260000710744217030314540c02c12030204d00b10420640d034689660410020501c0c18413a44c0000c182081035040c280940d851001c46141d08005650a015100015005104c1603074100078040403900f039046004c0e8100c484d0050104601c894030780e9104001802042c2004c0c045801d03024840201107420f0203030300528050300d802008240c081c1e2901c1307081403da114020f00a05400104c40d40006c95483e4041041e01a50280103861125480c03414a07085445040c1d020103a2200343c8070420035480701c04416a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 727503129 1250 727501879 727501883
    0x7030504030308041a040803090d0906020c0418020909031213030813020a0906080c040f141b091309140601030b18010209130204051c02061803010f1a0109120f 70
    0xb0f14516161814580143d000f01011025483c641a0034170051080b1040594030901e02002241c41000780600200c2e841e001500c42c00f009640a160284040d141c290419035402d44842d40c0d000a240c49900019031021094481100c2a003001503050004c00e49440c07ca9403103546501d0001d2400400c2d80c00400071800140bc011030f00c02510a89421596105940c100804120f9400d00c0070b41e4481620b151030b2030034601038611031460040740011000d154010b20080040941660794150b40b005c80030764014100e80034140300344408020b1100550346d10203090f00818000a00020702427454035002821301d4180451300c0c41980701c1801040082e507900c0c0320342d0f03210846000300000c00e05186020350190162951103030b401001c10310200700d6043e05a01a00031510202c03141d28000c5828071002c8080703454441d0103508000104031070f034243c03d0180c046440c1c0d0240a400042d04105003400b01e03040344d401041e00c60b600704007480e40029a40e40400254003401040564a091905d10b82d12044e0382e6424100c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 727504379 1250 727503129 727503137
    0xb04290d0507020a0203010f0c0f140301090b060417030706050a0b0a170109021e010201151802070201052703102a17010e0703060902190c080f13050306010902070305040303 76
    0x35051901c213118461125074050000d101c00d403101110706014010a0344d4940c001a51042c00180c0c4522844404900c412a0b6030345030304c1c59007003282400140902d500b18540100c3d00300000100850582a20000001001c01454450310545170000542d0320140c240300c0381908051040c106c0781e840d0100750b001c845030018146410ba0000d14840d0141092040203076106030043c01c1c0b000311015060076006141c5003680208041e4000114913805040d0a0280c0b0f002480b180340d010940b444290300800c10140141040303410000304031008261900d801c6441c16101105400c03020560500300300031100b08402c51424032568842c40b440d41c0c13642d43c41c2e55508a04100c020403442160b80a44144441446007442860056031181584210200d0503075500d00000e140c0710b00001c130400c8500c26500420803a50041000c0000c82200710344882c1c80320026100c2c120104418036800301ca51006140c0041c4842141804601e494101402c20030141d109180301c600420031000000d07442400c84007900e40c90300b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 727505629 1250 727504379 727504381
    0x80606040519060b07020f030d2313060309111e09130821070305100b180a0627120f06090813090b0f1f030e03040b04290d05 55
    0x11880b08400140780e180d40301460007030040780c140e11030001011200e00036240d14074450180700a050382c1e4000328040d100050700304240d80080c0b03003456822200700d05d4170030341d40e90401d100d4104401014405034045d00100c0d035101104810404240180280d00c1c0d4111500254854440034045824000e0002c1c3c5120342c11100004829890005000c61a2900402890b031074460100b0120b1440a4500111700f20810180c006502d40d0311a000e06481005c44881d101c802c01d10344242d2a40307c0c0c00443c2c03401c01d0703600c9444445005440d068040700051002d03646503480c41c4800c0003034500313600c1c40d6501c1d901c402c0542c2005100c400c58032145441c1a81d440001210308403010704090004140b01c10004248040000e03808102c184072000d01000c0d5070500030100728000c040c10030000030055440201d508800b0107031001d220040ca046686494042310304022038010200003c0a066034803c4d0010180e0001c045400d0141080c5d103583c2c0742e8600c650049000016a01286034600ca016580e144d40b0b03915103e074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 727506879 1250 727505629 727505641
    0x10c02061606050612120901050a0e0301090803071103091c080d09080319050415020c0c03030c07080d020a0c030209041e0c05130c1b0519140105100806060405 70
    0x10046604884450010541d06075291510102902d000d603041441440e0354031500755000000300d840b002d41c0c2e8200c60342920b083c02080054a080d000080003005101d00005030a20f1600d00380290060248180c3d40d0565900d415407016090035200c4030019640d500902c0101c140e07860b07000324030200804041004c41042c1c0035190420b964840c03080c04801c86418034180408010040000d103006d1501842e0001103005e008000360304407501100c0141050745400554040c8a04581c001c00b123010510303055400c204007250109265034013507944244261b10610081100b88028003100b0442d0701c580c406042600910340b2410081c080360700000c5d10480d010000f0030200a807042011406009074a001e901440d103a082c1480c54001a01c11a8000d0003d80c1522450344050b101d00d440c04440e980360031018403860919840005039161048510384103070500c0d000d200070b0200c0003100452181140711010122803885c14251072000d44078910345510008280481c50b004148a580890140c0c4c00059aa9541d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 727508129 1250 727506879 727506889
    0x108060d0c170f0d0c0f0b060301150b131202090109240b13050108010609140a080f0610050604150f02160602010f0b060f1c09020303040609050117070e010c02 70
    0xc1c1c2c1c01100368003400d040b0030002c03202c0450b06102a054003c180c031180409407030107540030048a1070041500c95068001400511100340554001d20040c000003403d0801c0360f4a0380e4601b09541041c0910f02c4082100c1c000300c003640107460050107810303028540c02e440c46d0b070100d40303002010301500300202c0c1c46030b0013015081034482c41031480100c100c1150340840e0b03a44d108010320303910903501e5a50340e60034440c0205040d401541c5c241e04891003a40d414031000e00d00145d03500c1c0d15503039143d5141c0c010314404e000900070780b0400001d964464140c000d0105070800444a112010b440d030b00007130092000340410848003009090898040c42d043c140840c0c1c4140c80c0500300d04010000010002480000001241d0305605600030340407090500e00400021414804120080c003800c03128001018040107401c29012050700300e45000880f036840440c00c2c94455002900f11b4110b60469400101e0001c41081a0340c1c0c1700501a140100c0304848034024148008000c101201103180d05040c004a110082c0840d02c0e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 727509379 1250 727508129 727508153
    0x30b06060c01240603051602030a12090f03080907120210030209011106040501200301150c080f030a02130b0a080402010e12060103060506030705100905040522050c010f0302090108060d 81
    0x5040d0440110742100f83d04125840000d00441300007900c3e205c002040200504500d0007101259001035041100081e02280e02e00d01d114101d82501e602d9403003610026445003c0c66500c03500c26210610a0300d0500d00031441e0030072a51150840c0d410b00e0720b0035009a1070f0266040040202442d0241c2d6881400006841601d02881c94074000e01c031707020421040c4a810360185107400d006600c5424040303401c58a6104071b0000f0b01412100c06031000b00701004500030044503100500c030314040d0381130442c1c91021141079001151a03841c403d8001500841c9086c490311620040c040c2107d5850501c084124000c2c202c500081c002814800c0710002003103143e5880b224020030415807403c9452541c1c4a203000d5024040c10381da40c902910a018021507a40f51008080000b08040c4d07440745171480c0b0b0141004007611024111503a000c840100310ba50b880f07403605420705407900600c01001003080f403a000410300040955080101441807241d4490b50ba48500190f800c00c40407121038516441504000f008405 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 727510629 1250 727509379 727509401
    0x52b020403050d170a2003040302011103010303170a06180518030705100c0507020d150b0a0b030f0c031506030c0f160c090212130c0e1003021207030b06060c01 70
    0x1064400c4005095070111a60300005031350380300880251114240b000a543c454030078500d10b081c0c4280c0c2c2c050302000075005541d00c94068400821206c0c000e00c0005c1d4154000c0c0c10a0300041c40c6041c1d05940e11040c0b80aaa41090f00c2450810000c2d1520441452460110040c2c0d1640c03900c61022405501c1c00581d840070444103501941e5868800c2e240c880c0c0d032010383c0342886400030305003a4503240c0140103500340c1d140b081c1c0140150880e04519030b11180d41d500c0b80d200d0b40a081c1e03914542d500c01034440b840700401a09030422415030700c2c245560241c2c4010801010074403807c10400402480078200d401c20000c009040c5d8415031070707407241c02080d030b0f441c01405c401004103400440d034400710015803102c10b001c25000d10a9005196210803e4405030700c219138007a40e21000e05000f01d128403101c908084040c900420130310701c42c44d440340090307505008180c1340840e904180344014019460404101035080101d10010030f0203e2565403400d0300030318004d101c248280b8021801e0a1805004e4102c100000c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 727511879 1250 727510629 727510633
    0x4120c0c140310050421090b072004060513110702040516080123010c051e0d020c01030e0706030c050d05040609033e010204080106090b040c052b02040305 68
    0x503454101c12008241d14540e414400e1091520901c1c1120b81449001c2c040c5d500701d041001881d041d031b81e0340851202000d000c50100410000c0008681c83c208018002081c401d0800d101c56025a65a1050341058440071a114031b1902c002044195184580c502d1401c1c150340010800b6050140c13201e105020b40480a500030b070400040100701d1000e6803d0400d50481a1501440d40e6228028a0700c0c5045000d660041002068941d640c00d600031040ca8a00030301c80c6007201d40c07130350b0700039407003142d0307070042c1451088540c03040c014840c510b901845440d0300148281380820001480d502c000b40e031003400b8460082031540d90085c40708124420303811201c0324002e44505000b039041510b8824000c000c8200c042e070014240031001c4500480c41d01410036a0f507104151101000d0141d8040c080108000511801d55035003084002110202802400c0040c841d140000804411000500040d500d00400d4041004020043e29400ca48030b00c0e80500c3c403264155607842452100c01e4100000e10480e0030142240c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 727513129 1250 727511879 727511903
    0x711100e01090b07050708070818100f110d080109020a09170a03020c090f180313060306050a06050a080f0402041107050102030714030c1204020a0306060315140f04120c 74
    0x640c1500510030203842a0070802c0107a50743c850880e124058243c0007840446c04000ca9004920759002801420102008004122080400241d901c070034611418002c140d000070b400003019041a00b00c000d10001e540541070030b1810440c01440c846050040ac2116507001c51123800b420321416103038000d0a0010000f000e400c030003030040c540d00c141111040b0010300c00c030a0705180794200800150b00030f0002464000c1d454589120b00d4403050358481c28101d60f4402404203242900c2c545800c1c1e8010a0541c400042c4141484280080c00003250801803c0c0241003000322038881e0f01c0608194004040003d051241e1a00d100190242c06118503040c0c1010703020500e001070003810340c005c5009a480e621886e808603045520280640070803668096403000500040e80010343b22800c45901c1071008280c510b1898030b950780d00040321801e42003a980380482e044140390b031250303510581508441c81c22240c82c40e07240a8100704686200140014002d11002d45100982800b0f4000c0d20b5400d58012000d0300c1e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 727514379 1250 727513129 727513151
    0x6060f1806040f081c32160203100c0203070b091c0914040b220b0a030b1b0c0a080f0d0501230a03120302090307030c08010b13050906071110 62
    0x209400c84c02081914060244881c620b10305204007110340703841e651202003001c518050300f03410360a50003103241c0e4005a00e0f02e80420310520749004003001d0848455507090316100e80141884e14100ca41d1243d9054600b18052018540000903944003a5100d0004600741d03039030440007420000301c0b510342025501310a15024209801c040100709035070341060040d04583c4600100070680d2064800560010001d1b090499102a0070b050703100100e214405c0460410780900100321005801c0e84140d0f0b21440780c40511414a190041c0202c1c0c80c841219183c2c20b00746000140b44d01c503080010010184a0700003030b181030300943d081c2603c000c500020000c101f19a542c812482c0225480b40706074881c0c204203c1c4180b134a280c071601c2d003030a0320340040e408030f5035206400042e002075006d440700d16854415200c0002c0020030307804400c40645024000443c83c2d9120702c0a0041a025562101d5000c5080104000a4200001c1d01c80e0b072001684c50201040072400c1182800c04220f6264048594100148050307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 727515629 1250 727514379 727514399
    0x1303020d14010f0b0f010f14180a0b0a020106050a030809061e0304120f051c0c0509030619050a0b060a0c0206210f011e06030b18070309050c0906060f180604 69
    0x3c04003080d6514645c0c52a030100446106201403600804a619803080e1441d034003413903024010f070001110442040300e08500005900c88a298480c0c0085a400910a00c0c4254217000b6030004007416500b4158081c11540c9103030b210301501044ca80076090204000d5410103894212440b00980005200d43d603090904006034281011180f00e0041144a5442259503224208482d00100c045402000382d0450740100000380080c520241c04124060200080565081c010680240303510004070138283d15800e8080e095503c0104459819071a00d1060410b0f600d4110490314460601e14040c003100c041440026000e02500d88414080d81b968200358078022900300d409800b4a000c2c42e014105a030781c400200480726070844112154a10a010801c00c1034082d0701f01104444e07004000201c0444010341001c01214110342e010b002075140c0c00300d401800405e000c2103034512010790302c460940c5040800b02d1410321501035030307840c80400001c20070400701412800c8101e11300005c041c3c5503a907039140f41580c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 727516879 1250 727515629 727515641
    0x80d1514010f02060907120c050a06020d030b19030807020409061b120b0a0303050c120f07031704021c02040905030f031608010f15030b130f0c051303020d14010f 71
    0x81d011420620070035807841e00002c4c4180c072907907a0710028030700340382001145012171208a0085461101c014408511350340c5e08455a03024060310350040c4964021460001e05444401d0f801d0380c0102c18103441011246616040031007501d410090640d9644080c8c13003c01c5c010405114050011843c0541c500a03980750600024002455555903450301411280644210b940741000184d100c00c4031101000042d0254024050300860941a98010781a410808030154001d1100051000707000480508154102c0540d030000e02c0ba000403a01c4900d055400305032042021490900e14082d244c0704c2c54210b40c0c0d250058404158050241c80c0c0b250846104040b66410940d441e041c11401d01518010f6184250b100c18100c86d00b240c00c00600d42c3c548811541640421804542010b4442c00c000607180c44038a00010301034100074000400d084505e8008048942034208403041000800607403401c403810307440b180c003600c0d0101c6005000c40c8452415019030140042c552104c2c0d420000080c0b0b1211440d400b003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 727517985 1106 727516879 727516919
    0xb160206120103050c090705030906071b0213090c0b0310030204090305070501180605330a0513050402040c09060804142103040606050609010903080d15 67
    0x41c80007032800360029203503540706007141086420500c00259003c0030600c0d00e0f500354100403103000c1d120400a01400200305480310b0034840150314510b0442080d90084c42519100017020f00c0001401c416a02500e220780e0750034001540011000440f881448040c0010032800d080d035003000003c100fa101c0c2501000001d022040025009208001d51600c1d10307400b00f421800e0030316024003540c500400078414402100258816924840500350780070a0018018100350740c3c100100b0f50141c0d8a80c0415888240500c405461900c1030b4001d500580c000d460605c00048110300646880d0031500c28800003800800003e004502e1503004003540340a01000c3e00c0401d00110b140030848084107840041040340001403100304200c601c54080148030a41b611800c1262941c006880344207544800362400000141c084111031456100488844030443e0101d4061b4407071050041c4c2c07041c084c0c14 = true := by decide +kernel

theorem cover : BRFrame.Cov 727338129 727517985 := by
  have h0 := BRFrame.cov_init 727338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 727338129 ≤ n) (h2 : n < 727517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
