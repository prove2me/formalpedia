-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2471
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:49:05.017135+00:00
-- url     : https://prove2.me/submissions/68b78f90-c967-46dc-bbcf-01887df1e4c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 444244604 ≤ n < 444424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 444245854 1250 444244604 444244621
    0x50901090212011d0601050f011808030d0f0e1f090309080d18080d021002090301150303120b01080402240d05010e010608010b0a02060c0d0b0303040806100b04150305 73
    0x60000000e4008080d030b4141488981c040d80700c04221a814070f114034140c440442a552148024060b03540c0c00300b0081e080155552003200790030f03c003004006000024680342e040981c61a003064114401c42c603150b0b240c10034401018005d0010300080200107150541140c107000300303000b03036220005034819035038050b2200b4184070703020001c01000030a059550661002d00300902505000c0411006aa00c0b428000b41c9000c0004141802845560243c140501c0d0301881901a42c80810119803544d02c42a02c0b6242d8002c00c2d01c1c1720000c52290311500ca200c0c542140c0e6000b907900c14004181030003010b104203c050784400182c418815001d001c00e01c0480c80a02002c4010b0142076030a0424a24200011480d614455109416036406031203210719a030740d450350982c991069825000068200001040203990b110016060b07514600d640407401880320008039181d90095409091980e01c040b00340b0506200401d0407901801e03031403201514241c1030070b001224011000c0321540825035104005003419 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 444247104 1250 444245854 444245861
    0x290114012c04050f070509240a03050f07030605030a0206030a020f0301180b2707020304080a050705041a180a090f0b040201030c0914060c25151809050901 68
    0x40d0680d20707140c281d00e00218202074100901144140124680070120303000d0b1403001c501d10f02c2042c199449918003803909051004e600385d55840320005050404245228600c09400740001581503a000070f124549404142c82c40b0101600c80d0051601d080014066a200842d204030340c0d03501522050b503a0f4a0f2000094001d204400521041d4040403002144114034228101410403000720180714000901c002c04c54034104950b03900c000a0f42c0c0c0700c0c0b01c40156400d040441d031b2000c80703030041c2c86c200b40ea034001003424084100360456170354002600034400c41c60300e480b40481082d03000c240880181090030106503688401c603607000002c00501c0000303034000d46542046901c1584410307041a5a412071512070810f10042e9001c0f80824249042d851306103209400c42c2084641544d0748180ea004880c080c4902030307002c4011084140584450000c0c5950034070a400044044100c2a0712158641104588c418443d0f4202b03034108110341c0d031015007219035208400c01752030455000281035150307408140d004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 444248354 1250 444247104 444247127
    0x317090a0303020d08061c061a041d010e191e020a032d050607050f070c0f030c06030207050309090702010e01050a02090f040e03031519030f29011401 66
    0x1440e9100803080650118a900d90404261150142a11020200040c44141a030032201c4640030544440c00700d011230b08101880e1840c00c4544a040100001240c2511604004002c50103045205400400c409100c1e0703001425030403002c1c01141c8950703032000031400e0028602074a5200d0440840140000000c5404100e40d0700030028600c0715624640f10403845c40700f440f80c14500144041c0c0354a19801c0c00410000300340d202c005024181d840800644150300900e01c9080d02d030100740003180003c0c01e241804800780c804a0000e5025501e10320300825540d5060300040105030040c404480000d4000041e40c0d00407408588500031a81c56440407030040403401642c01041d8246001d00141c0f0620358014a143c1e0f0098514284e03824240e024081030310991b0035030110742d034802c100255a4a00040d503104900314000d1541e1449004600003080b0710360550010350b014020306c0d10241c10071141684803000003001803150120b404c0d13010301c1406016030503c24100b02e54010343c040803082e0f2261101400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 444249604 1250 444248354 444248359
    0x3020c070b04060305040308060907020d0315170309090c0708030402011d0301021317010e1911090106090e0717040b04060204080106090902040b030109080a0e041407031a09010f031709 81
    0x2119070f51404024041e120a035030035000b03c4c0312a0042202824000c4030148030b904941c00411801115030000c8008001e4140f10b824480b40680d80860303903a2501c07a1411a05096170001c40d140d4080c01d0030840c0d40f41c0c02911141c0760300310070802c400014041d00e080d01d5105409003020200280d219030340340700746540c40b41e189a15503c00202d58081143c800070000a403a480d41a02c4c030f0030102e107a11103003200d807a032110b4811a4040c0400741e1040401c9c5580c01080f038410764814072101c10503c0070460140f402e0700504042005070700c0c24030000d094a010715520241d540740505944513081100040e90070060005007101200038001800d020050b01241d0041c44850000c000307082d590250701c0e00a06528208920460401075860910f203014003812468503000b006c2d03c1d00c0d0009008003911501c1200e80c807103411a485061680c60404802e200e0f078421405610007049a0304018004554205002c84007481560000d00601165480000bc041079a07070203148020410191001c0030741d1402400c84071039 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 444250854 1250 444249604 444249607
    0x20703060e06090c010f0203120a0e07060225050d03120b060307031d01020f120a0906150302181510110a1410050105090c0703030902040906291003020c070b 69
    0x8151200003945500c1500c8400c04e46044000410045601c0c100203005180141d20a21070521500301849055400183c41f8000058000c03000480302c0c2000b5081e48998007607084403107010082802011100c0c09808075600c407620190a080001d410b00907150409401c000124184420004166010701c03854070004200c2ca48030b2500c41c01c020054a280c0203461040c200e460a031083d450814025144081d5400103414100048019500c500031001004015081c1d155507100d03001c5500d070711a1240c003503416008004800d00394010b002d003010b445031060110f18a00b030100000050580c0e600c40061800301c0d40740c075114490180c112507003a2004100e0712280104c2c440d2404002ca0340300648441500c850035144018981407089040318024030810390400c21240010301c418280600601e0210310a080c009805140d9401103401c41701905411508503943e580c5107030f4041c4013442103d000240b80844003503000b0041020070044240345641c802415004174a0281800050180e540a04004880035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 444252104 1250 444250854 444250871
    0x180209041416030614100809032205041a0a090c0504050303160308090613020f2d120a020d170403021e01030f0903050306090c1911070e2502070306 65
    0x34200000c0e0180100071904d49440000c1000e81d4801c5111044001043c844100020040035038641c1402000e018050004100c200b424422080c0e6030009006401c0000309024100024001146d92600aa940800c0348240c151015075a10040174180c80340d05e200860206201c04060310240195040b25505d8007020481000708590402160000d90181d0765040f031644030600099240c8106030b41240e00f6081e500d2070400542804103028034544005410705072006200030b081c4102074507000706440070740c101d491200760b00d02c1c020100200e40054017010300600c80803903002038100d480200c0000d03e40710044071030340b22036404881078030001e54001c0d21210442c8000c0154180240e440c882079400320f4a842140c107200c100314403641480329855100c452a40e1200800c014941c00002c0221013101d10810141d0700b000304038020100044c00d039444000da017407820105181032190781e8002c0c2105072401000c01c041b820785907070794441058510391002880d5000d004101d0a040940c0c0010f03005a051500340c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 444253354 1250 444252104 444252121
    0x30e0105040e04121103120a0b0a051c0318150207090218010305100308070c1e050f0904020307030c0b04050102071d130501020702030d120f480801080708071802090414 74
    0x8034400d8230f50890410841014104200d4141c1080c02010b40060440f004c01540c008801450a0790501908001011221501c03000c602c115050b00300000c4541241e0000b0034003034042003954090000700105606014120289a0b01e00d00204489410582c8a6011416001c900034510300070b590018211030792080d203824804000c0000d88110aa03001075516032038960080d565022013503400c010000001840440c04012100602420685c2d2500641318000300003201d03019010000e00f12403502d1600c440c50300001905000103a0b00280700042818501c0c0c07401409454029401b00000c50b01d951580020308025009009030040250103200b00b0020ba031038180c000b109015041c400f05403e0007840b6100d403400059507034118103004d882c0c1d2038170803030313240c1200324004c20070030342c480c0443d0301e032801c0c10115807404184200e0402004107164000500206000f4048d40c3c2c040d12154004208061070b015011006501e26540c6008140c1d0200d0354080f99515138100e01c0c01e0030440b595210690802030007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 444254604 1250 444253354 444253387
    0xf14010c02030a030c120f052a0a0509061605011e0e07051011060a0b0a0b09011d030f01060e0610020706020a0209070306092a031505040f09021903030e0105040e04121103 75
    0x17a021421100007180c0149c0414804201c0030704120500041d0500c901e659055403581c01c0545c501f503208500f0320040340c0081400013a6000c06000b000085031007550b0504101c3c5000142150010581c241131000c002c0010005080e001c0381d0f07060f5242e4030034507010407007110103400c1b014120006010740804c0c000c00d20f40075001a038031058210345044809070f071000d039080c017446000d683e2400b0a102011034402035416220600ca207540c060242c032043c0809885107401c4a21350703001207a040a4800a01c00241170100d4039007028117190004003503181c24032402035a20680c43c00000e220300030040014801510036004003004050706a000d0005400c1c0b2040340341403c295415442c0010b4001d680000d0280c800e00900c1d0740c1e0707444100d50b13003102c03420076041c080640303480c20144185a40341d1041800507110b06043d98083c4a1a0694400d55130652038001c2082441101c15810064240400c0c031012045844031a001580400c00c440d04110015060343c0c40003114404ad05107000114098840d80c01107031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 444255854 1250 444254604 444254611
    0x30b0d0c140303271003020301081f1104060203070c0b043002040606021f110a0c0606030206120a1103010303172a04090b030609030f030a06050406030f14010c02030a030c120f05 78
    0x241c0e041098550300e0f60446c22400b0910a4400541c407944200104112a03c0c480c0b0741c03c000c3d1f61000c6900c1006034040c03409a80140d0026005a00010703c140a0012002a44010300f45201419181515045d60fa80e50144211111a556031402c6a145042050340c6060703114250f014001b40442136564101944900d6034005032800181481640c0750700110700d2168065410b261140301f424101c2ea80012100b14800c42c03030840f40783e40c0e1480c000c00980d548a02620101c8420401c40740c5510f415011041500c03100000c468041d5020310061001907003001e41601c1c500405050450555549800b00c540401c110111048120495182c1901c2414070300c010000c2da40545414001c036210f078003c0c1076031460b04580001107908180078980c0321032004001542c00c01c80c41c103408204c02d034983d07002404450072a8030440d0308040340b4010380704010070503004080340301119008010034025034401039240c1c4120403101080560b5041903031000c9010703803140f01031103001c00320800c100c00e541400c1800602059 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 444257104 1250 444255854 444255859
    0x901120e0d0519030528020705101d010506010507060e010f05010915231009180213060c02130b01110303041a180d2a12030b0d0c14030327 61
    0x1410003a5181d8042c0c0030b500d010703031b80701c2e034020b844080301030000000c405881c40c20201c526005c102040c0498020001ca01e075030030440d20005048000300145042480e1307a2030720b0000d940d040004110590380c01209989009800c01c00200322002118270321401003070b901481c1c07074041d840c020001c20b03070300b0b403e40c0145d814012201052402c00d0711001c684040d240c00c204141000044851362040703034200b801d09000312107040e080c00410152204421140c40841d2540184078907030100b01010808011030a000042c8854201460b01417602d402003440100d81c1d848681c102a20340c00001e5659104214003581104140c023038a48030304092904810304080c41d00050341c0035446c440842d04413170800c0703050314207948030400601071050001010f8030519940611080403002103c00c1600210018010f0b42c640313031040452901c4502400b40c00f404444000328181d01907625950220001040c01c1c04c20010b8404404498003002c006100092852041d803400848070360350340200d80000200042700d0480303401e04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 444258354 1250 444257104 444257137
    0x40b0907091701150b280224010503060601110304091103010e060f06120a0b060a050a141e250f0b15010c0f020f031b0301150501050901120e0d05 64
    0x802c0c1c81e0307426a40f0084104184080d00441008002107000082126084407503005208500070411002900c40290700040540c10062030500880d100100c907848052100420038829410503011030b6940c54010100da060223600c1c0c84440c41d260307042003920020094031406201c2e20b017140a50352140e070003e200314078100720120089000c600c2d0801d5001d0001101500305806d03c2c00270040f0740e04e21140a418920a02e64515406459442d51402808540c4980e02d03a150782d52a401c000828041c0307103080f10300c1d0038130045c4a02800c414050079026414000c0080e0241c6034070341e0020040310040107007602d0780709880e980001000c015400000078001c0e40100005a010fa6440c075842d0001c51403181c00500180c2201d01c0d8a0000310060000c4d002da0b4006002003540000c000f010a03c0d00425180d078400100c964614440585002d02500c4004003038900c003c440c8902d068000703009400f4000c00300381449400c60300c030b15610125a00031121003442e402101c0120805880181c115480b181140840461 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 444259604 1250 444258354 444258389
    0x1401080106060207120506071202071703040b0711102307030603031b0f0807110d0b01090605030a170a021009120e01110604031d031c0f1e030209040b090709 69
    0x405c10b07050080b541d00640039080554503464100c1c2c0e4003440280b0391890039401d10000700450040b0a003e00401220700c0e5881c0e40b070a05007000804250300411400c200b1001d000340360501c400c04035852580a0380c82038081401c0c1d00640c008041088040100301c002881c170380c00c00001e958980c01000882c1d010340c41d0900d03001000240b04000c1d900c112005030204040c9029500040c020000401000e40594103903c600c04030b640018a01d52000001960081b503030384014850100184036100040504031700030180d80c5020303980d01c107100302401c42c000401d2001207800d480e503e0080c041c010088000034801c02c010b00c100c1c6450400c1c42c00f080d401c3c43c00540c00c0351014500303500032584519140c500c00000c2101e0399a994045071003d02c40d0801503084040b1021511554404002c5c1e00051a10000c00411a0041c65001080703519002e02140c104004400d501c24914000f00c803086c907402c0180340260359000007038040f6014152809c2216000b40c0e010040141d8160b00018503000d07035094291843c100300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 444260854 1250 444259604 444259619
    0x1e040e03040602120a05040e150a0b040608160e031510060c0327171e16091a130b010212040f122307090b0103021603121401080106060207 61
    0x194040c0c1d20150340008110410752030136501503ca008001c1c90614a0300340c89002c070000d10181600c071190425600b140210f003520300050904060004005c4075818203140210040201c01c1c0600b0202d0128800c4031101c0306c2e680304001c514258800030303044030f8180c1500076140502405c121441e19500170640700c040b5140d449a040000e07500c0e00f5503134a0249450f4070142c1c980341c0c880318512111501003010002642e44810426142d2580703003030085c258441d940420b916100b41030202c4604a038202030b50744110380c0d1503514010242c0d00062030000384461a07150108a10039a000ea8540c4510600807c0030f02c0c04a40c0c0004010010a07400e40d400a0301da10012511070065005003403841044400600000b40030700052003001d8014610003500c000b60010002c41c43e6840304c0840744039000960184a81d14860103410300012003840e0451805142e507a50b410301a90224005003046612103803199000c040d504440307076034001d43c4504511940c0d1509842d000704001d200e544058040d5000024020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 444262104 1250 444260854 444260857
    0x2030a0c020a080d0c06200307050c011d07050102190807150603080d0204050f0109050312090d06180b0f0c030109021809181905060129030406020a0908010b03070b0d0b1e040e03 78
    0x7c3d203081562411902d40306016105a0010044600c2c55940c0c0c50300c180008107405006a0900c0c0800d02802c113450610000908241035481c074a00c40080818954002030305050440300919044003021250080c000c04502c003410041d40003034079031240840d001c003510070a41d0003030080303070030840c5c141e482e507115030005460407a0705100d51645030308a044804a103c1110000307180340400206910740001c0e00c1c5d91440c048544100d90500d413680444401010084401c4c821038020500c000c0701c42940c80d250f00a80202d102c1409803140c8103802084013012106034482085480000504010b5075140601f400003100103158a100c040c2d10480d240d403038804044450001c8007940003c0170b01001da00b0039426a44d02c9484a0003080e00d0703003a80940b8410700c800d00001c1d601035440380c032015a0ba52400200149044030039089586564507042802e1a1070387d0001d40401219000c003040c81d1120000d4401d840104003080400e500500a03291880f4501c0700b060740c08400c0181140c04100c03501544034259a01d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 444263354 1250 444262104 444262151
    0x60204062f06150109031a040302060601020604210309082704020a0509040c17160305061215060f04141b0406140f07060608010905010f050702030a0c020a080d0c06 72
    0x503802200200754010f042e40b40c1c80c0218070060500444c81a9a503803126549035408a01f24070596002040c80109541803205c15002a02403008001504054032441d48140100d9200b104411441e0404001c0d14042d801015003a90054005516543d42c080b0a06803810102c0c41b0b01240c0d082614451001d103030500c240d40402e410340e0344441c100100c5206000c000c285860b1118103000e514201c103120203000700324141c4102200464030000c12110725000e404c0d6000034224a100d602c003220021107100000407440c607010318034100da1100d91034880c0403e901044a40d0001d4025080c9000b02240d00d40c00c010241c01644000300607207031560300c0c0f001480540036601030f0100003079036602021020f144820181c81c7c0da5501c54031492a00605503107100c2114800d80c01500c2c165119560142800002e1042c22002d00c05888180001c2c076001c1c0000b034070b030f04c9441c55040600c0300c241c00d00000d5407601225440a007110384100c0c0c403000f01c0358102424030070005200f00c8406003840d0b00429400c00300c0380e40e440c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 444264604 1250 444263354 444263447
    0x9080703031b09090906020721090f060f050d15060903020a050406050906011d0d12080f091009032307210503070c03032a020706110d0f0c06020406 65
    0x420f079003810b6681000c3c00c1200401e882058090120074003082d1070f0086d40034000b0458a0ba1800c003c0380500180481d401d6038060035004c02c5100041001c01d402c9507180115010500d00305a4894110140d10020101c0c00c810710820003100c0303004643c003038011200c1004c1e6402220780c010203503030b103501f00300aa88941c0901a0442d040d00c001c1107040d40104444105180103404210b094042ca101141c00ba071442c0c00e096507400d000c8006110015041002950422800d0505e0b104501d49030112543d522900031007a9500c0384d60300d006c0c07406d25114140e05030004207030340389009040b4541c200307403401030704140f00c240c0d125122007003901c9041100f0741031003200214a0301c8150440d41c030503030160307680710305150107030107268a91950350004201040340c0d5206010b9100308a100d0500001c00034509a80d5400101c103205030150380d030442a5001410070700d041020324114410a2400303000300c490004c0074500074050790010501080180d004a000da92090a18155129030034a420b10320f030516055424085 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 444265854 1250 444264604 444264617
    0x3503100306020c07030f0605010e0a0b0d020909030d05190c050408070902030c0f07030c050f0c0307150207081b0f090f0f0c040f06050316030b01020d0f1209080703031b 74
    0x10010341140c003e4004108103a007030b10f0f02260f0301d80301c0c903240c0810810200c0e40c09950304014001c25401c6025660030605051040041d2003002010034400450040003038441c442c01c50000d00c2c80001002141d045156009090040c0e04060400e804a2003200b04a1018a1700308000215028441c5055608481e855002810300710300d0541d801000b0b50010f41741c0c1d010b850041050305441c154182c001c01140e4400c1d600c1c07180000140c242103091000004400110703400030300c1400990740c4e00003110390030381c0d01e403070703d00c454241c60310750207a203401170590060b02e05019000009000441c1e41a000d4400b00342a140c10380c00780000c00820404103009c50304401176540364800310b84040031110009500509080c0e20b0b624181e1076804d5868035003403d40c892000a400001005010280743c0031209920271242400c0c49400502c50001c1d4460078442440810466100100e06040341704003010440141d81c6401088202801c6c1440559507102c0c0009402103030801c41160440d980410701588110102e50f42e00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 444267104 1250 444265854 444265859
    0x50613050a1b03200a0b09060d0b0f030601030b1e10060c05010905120a03110309071e15270e01060c111e1c080a0806030109350310 58
    0xd42810030482002e065600580c2008000240c1824a01800d040d0001055501d80c0c1404100305484040d034114a8080c10305024084054840006846401131007610219810b02000040380d600072003000c8855051269000001c00c0c4030480159501411220035458040400c01000551482d01614021140e0400400811243c0d114510319050548100b0011403140c12a4031028a40300c003221228040190004400e408550540303d0ba0302080401e80d1824110b00d4011013494840303040b8400c0500b00c42800c00040028140094070380081e0005110b880f4403090100d4004100100b441f00c1c0d04030785105209070320203c4040c04142c80448a000d4200c8019a00f4030394215103114820000b260400daa8105000342540c07401202c00100103005040140d1a00072810072820901c00030b00000b503203140050715004a81e505d0304940f8074080ca4142074881d0b4403644046401014600c0003d49401c0d0600401c2c0460401d001ca00311030b1003031740c803024050780c5000c1960440c1807009031643c010000d0140b204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 444268354 1250 444267104 444267113
    0x60a0207110d020126070e0a031e021f120c030207050d120905010222121109130203030705060a0606020718091703090307060f1a040e03090d0609050613050a 69
    0x21114410305d40703045030421294482c2d81c1036042d2001240100e04074001c01a91035402a05440140c5017240c081d000d26207151140c030075540c200e005014154001822890039900d03a007820400300c071948845252489004c490042c4060304441500c40c00600340b40500038018441d00a4031503158119018001c0c450f862031043d0b581c3c0030000c0310420f80320f4940c0030710008a030303081c400b030903112110704122100002909600d4200d005190486000c1c201c0d43d0f041c2502007500001215a4490305032008502911083ca0410301f451204030025030600c800035101e01041004141d4502520b090101032051a84401040e030f01c4001600800c0b00f003c030310014401e003505450300000c51040c040c090036850100b04203144000da034411140c515807a800052000e00b0001c15214214082005840400000b516a00b2000740055801300c058865a00c0b141d00103a80c010034421500d01d50001004041528103078500726000e001856416240c0d400703008000b850450451243d0401640d0160140c0344c33441135aa90b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 444269604 1250 444268354 444268369
    0x803100f0312081504090f212c09270607050a030f0f060605070507060203121512060a0603051501060c1b0e250903030f030209040207020a090b03060a020711 69
    0x4584d1811800744940410348691264104050142070562140d42ca00d003428500d00c40325034088203421100510031038466030301001c1184109402803c5642d62500c101135208604240c2d03961076404081c8a0900091500c1e021400d0017040c0717418424a007222840880644550b8104e43c8807011032400c124012586200390f003d40d41d040c56569002412065040300d49041300c2c0c407600443d000c10710005400042c0b2a0800100c0000c141c2e5200451824204804182c043d80004d031401d00d0000c0c0131a81411199250b110740c4920920482c200d40c050700e410301d284009040184804d44041c000c05150940d05d41c10072952505a0b01c240d12981e03050101c60341e58420352000100700c012214020b0748007142c01f00000d5401801007141da50f40c0b0400b8810040c50f030303122405404900341848810b400030000a90401c80c02c000011550070010b13240d40311880410040d00c54040000c0d4014030445c000710b4032500d9035026294041099080340c07011341d942100070049100c0c0780006042e5070b080780f81d0f464a0f49058803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 444270854 1250 444269604 444269611
    0x31b1e08010b030723060f131806030c051c05011e0b032107020a0e0106030504020109052719050a0603060606080106050d0209120a03020c031216200a030803100f031208 74
    0x803ca50719005100000020b5508508210307008e10b00315100410410520103800781c402c0e4000141000340920395528241e141c941d40c8207443c0607640c007482400303103404502000e008a44c0c004000303125144e0b40b06c031460308220304041d40303c00a51401d0000c005508000848211132140050b015441c9541321064421541101d0700882e8000821807011900c507121140081c000d0a844d100440c06061910024200750003035005280540c4584e48500013180281e1303060b041a12200424035056210030020701440c40305a0180b080c0b281c1010244809802c4580c8a001180d0003802d04000054680724103d0751000e003885070400046c010300c00070b030903501583c0c0140800c0c44001d009244142002c080c4a0802c503010320282c02582040b11030044a060a01401e2004094048031a20f4000d801c8200340e001140c03000301800104a090041d22000450101c0140346c0c01d00034800d240e0150340349080b00043c1d10480307401071308240c882e8002806003641134003101982c4d07001e55807540407a105501225403c0005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 444272104 1250 444270854 444270859
    0xf060518151905040608182a03120712081b2d090f06091003181a09011a010e0405060a0b031302041805030301031b1e08010b030723 58
    0x100507645600b541015600c01801154a80948a524009015203c14401001c00204003404500304100d824003081504040f000305031540d84145041d081d0070300d090400003000740c152144d8480c1030412400480603080003807081505500d66494141c0c2161815000e58103005180b1049100100d00d440d50005424003480000205100080c1450690040b500141c807000d00b00800040c0340c0303c582040c0494151018044d5003d62a10890001003442100440035607410540d039541481d503110403031183c4400e0755030001a58961100c0640311144010780c11748651328150b01e80104600188103681c0b140c08644016110f140804029500348005410010045a803054030b41d50085004010100914010740c10101155100c1c50307207105200440c0c0c03201c0d0b071310f5040444409001d00042c0c000001c49040d42e50211119502c80e14802d1070304003048283d008020113b0803810006030395240501844105c40260300288100c0c2c0d581001d1586a111500403680150800c00c5c4410306010b032180941c9901101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 444273354 1250 444272104 444272107
    0x1802010206040f05030c063103050307031104090c020d0816080402040c0e03010c020705030f0712061512120806060c0d0806031e01051006170610030b0301090c0f06051815 75
    0x900d01c46e9400d010341241c103a01c0e80ea61169280084ca01c242c18804003030400380300c1c0300d655401030303440180003400014800410581c07968a2050344200c0d41d02502c0080507105824054100c0500c8040d44030485881024006010440000d0141840300724008101e03146031500641502e03580c0a20001c0d20f5001c0c0d49605002180300c400c007080e2801d00c5a0210f1244a42c040d140d040d040108040c1005101da007401219030000d60140039000c0048003610b13036140d21900004085526080139006080303103611036441e0340301714400d50051052410403595a0700c1d40303544501c1996900360412419000f406d0100007190b0007005510200da0203030000e13540000009046642c1c0e0750165012104a0310507206801040e5114024007020028035031011024064900b00168440340d001d2017100a00c200a056504c40d480b40d40035908900d0203603100300c02e401e0010700240301e1400c0c02d040800c1810014810790201c0c40c007100000820602c12410341c0e604284004088100026101c1000742000c0d0442903031880840 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 444274604 1250 444273354 444273367
    0xb180103260c1609050916091a100e040b06030f0f040303061502070905010501030608030d0902010c140f06061203070b10050d15110403031209150c0504091802010206040f0503 77
    0x2003c1206940460003015401d244500b001e0050f4162240601010391a52000004c51045c1c4d0000008000b524000c41c80000da0004e00d50080540c4030945119541100d410700820100a51266180e44840401d503024407444808805000307243c0303c202c58032041e21718541e01150144a41e0040d440c0c101e8020714002c41d0740e43d22180d0000f05891311841510143e80300d48801c0120a0f101d004240c0108000d0030304112241c60085815100e100b280400995290f84650007030440e0701078045c1c1000720307030443c02044d40081e01c5410140d5460000e020144e0502c5100c0c0041d030710f840c207090f400c400105020042d46c00c0004036070f560fa40e045000f402d000d0702045a82d801007215140c420142640c17502a0703d4219540e014450854102d440510180c85081003c00040c80403940043c00c24000c81104000041c44101714200784101c69803038141540e0007414400003003401503008028005455680604010101d481c4840591748a036803600240940c00000c0018082105490300590070b50085054078039044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 444275854 1250 444274604 444274627
    0xf09020603070e0a0f06020606010809010e07031101081311060702030a0803070206040317010303081b090d06021305040218010503090a0c081507020109150b061209010b18010326 78
    0x30001c5a542e40040c07403802c843e41032454107403a800c000b000300740d40e5200102d040c008000d4580400a022034144600311010408040c825484041d0503d80002600c000a0b224601408d606104d150414002101400407039003144c2000c02400c120340e0701800340074051011000340800d03900074000a0703a01d07000d1a0500c00c01b0032144130044d0700c21003950f409020a403420b407401030600c3e0006c0c031001c0c980711054401130000a400094160300b18080082c00201da00d8000100000391003501800d0f03421100f00b141c1b1400b0000a5005000201c40c0c440840040d2501c840501c022802101038400302c0c0c40a040c11804a0350180c4003e41d0031842040a81e8030031105519000c0b404d0762260b0081c0c01035442540907121804555540a070441440c1c4001c0c02030b50525202c8080700e244034110006c0050781c44001c0301c0d460742c2d40b070304680c0343d4100078503000d00324901205954000d00344100400c1c0614441ca111491000060315041d06a941c4101c0080b856091508610900c010822803030400c44000c0040e92141d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 444277104 1250 444275854 444275857
    0x41403270613030f02031e0c010507060e0a0f2607080901260403020d030e030a0305090f1014060f09070e0a030614190218190f120c050d0f060f090206 66
    0x444c000c000000480025206140ca00780c80c241420f20600311180760912140c030701190603110410241380150300c950f558100354002b841e03188903004c50fa11505655030204461050780d4140306000b11950260000c03411a4580040302c0300103c001e090070104211000a0364103001b030040c442c018500040603550304015100c00e1301c054080046da0385000c03000c100c1055410401c813602c0ca1910b25090201c02625100c465581c025050307424185900c1e400010031801e01004001032900842045400e141d03460395840c0018501a6100f8910f11030341400140c40b420021080600684090300a2110390744a120031108551100c1c0042e03407080004000001003505d500400c405031484401341c8110341072600c60352441829441090620f1030042c041420503501b04070074508207084c1651880c1d1118583c0d0750b0003400415a0b0000c00c1542000a00407500d103c01054000c21503109054240040c3d07100c01c1040320142c1a008014134540260040000041e0300c1d40003144040d04944000c00c01031b26950004916 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 444278354 1250 444277104 444277109
    0x20c061c0b0a0f090606020102090a140117130b010b0301030b010e090a0614090c150d0b031903180b190c061419110c0604080f16030503041403270613 66
    0x200c1c10300103c1441101e07001d114010052055000841c6060306107008590860960b12800c00700c50081c54a14040764000d0000300040507000c0c0c00d51009142000e400c2c924818042d4041e128507101200104000d280202268166504140c5214180e0328001c4030141081c2d004145130903901039064a00d0015a442c010301441040c0110045040d00d03000c84c02a16202c01c44540621504004020b0784c2c0200300001119011030b00d00c400800c95610850100c2d1422220340c12070f0560020401082d0141580f0180a154886a16100362100c9644003000300d16030003032994504504075803035a80c03009980544810b80d086445650041451400c1c40781c5d800c00b00074211802d00185c41401041c43d1041683d03c039480d6820a60710815080084090b0895a250340c0200000e050000000740c4100d031011401c140c4e180c220030140c100b10404968a8001c08c140c00548003121003805101034000f00d10404801d0701d559500710220f5601d826074002c2240c9502004241458005208201c020710380281080f20602 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 444279604 1250 444278354 444278369
    0x61b0b040615080f0a2303211f03060c0203130f050f010c03050d05070c060e010b0a0906060504030b070908060901020702030c0d2001180f080c0301020c100504060b181006020c061c0b0a 81
    0x85400078802e000c0d440800400e0210011449c100c3c0c1078031208607000c800166a04200e0016a200070345405a01d0751059010f4104540480b00002441c5814034541c4000c2d100151413184200f08046c00540b4509081d00f40100450702c03e001d4a500340442d64000c50b4095410b241184211440d0303250903048038a001030209459459041c444031034144004484020550f280080106610b0070380000c0c180d000d54040100644210030214045034410100239006c0c05504050341c03644c1c01e28034541c40c000c0d808840200d01a004a150005103407800d81c8000e00000d405c181400742d038955140010003620120305031a414801460148442541c1040c98000907000c140c490b102e20320704100885107840c9400c02c010b40310f680100081101a580821544114401050082056110703071400c140900b40c90210303241c00080750b5941c00c0c804030b20710014a0251801030300031105551602000c80c0c0702d04020f618507070815001c0003050031201c441d01c03190b900f40401510000e5054040c90005414419542c032180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 444280854 1250 444279604 444279637
    0x4110307080405061f0e0603030405040e071505130608090f0607020d08060d0809011202040b13050111010608030412050a050109050322050a061b0b040615080f0a2303 73
    0x2c20858200521a00300d05194140c0c0e100064400c0c0220400405004220012203480f0100b1042d44040003903402a0800900c28003240800c80059a510301c400e205001102c08800100c0002c0c5019600300c0e00b01301d0850340b00c05c10140c1445019100e00e44003526040031840750140d460102c55040c803c690040b00181d0151201c02d0200b0001881a8005044d042c031a6010030860400a40120103c5503c1d0300203007400010b9144900c2210000c0c0640c1d4022040c41c03900050a40c150b81c41003011001759002602c0e49185d040104102c0ca00302d13005ca0103010b400d0352003080240328070380d287d000d80081188160100c5000340c0481d50762909481000b0401c60701c0f98000301d5984000b0103c01c0c1300007400390300c01c4440a00140740400083c92800d651180c2c070180318806c10406441c280d0342800008198101c0402c06071420140713440c0c030042c02c000b04da00c0b4200d030006a01081d07880300403c0f52078080c0314010040c40404010b40b5a86001c18250b61641500c1607880c0741141210002d01c0544580800c450104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 444282104 1250 444280854 444280861
    0xa03020a0e1f0f050c100b120a050616050702031b0d02060f0c0d1707140d1b110a050307080c03090d080a03061d0406090501020f070f050d0807080103110411030708 72
    0x5019002c0202508007800b0050110440017080010001c02110200f4004900b04c603c1c40c001c10081c5418401ea001c0380e020b624500c0051100005909001d039141c0b44042d540d9210006003103420f402001402503254105544182300c04140329011826403000402510b00040558009104ca40c40f03046030080c01d04003c5045a4400700a0200d070000c41294248406006030034000e00328021402003001d8244003038119101205080c190580310b035100c4c00c3c407040090000f80080503016181842050000611090b002140c968002c510802615400300082d41403021aa550003016080b8042d4941070f80300a010340296980d40110f81240240a03c107190b585420484000303045d1501c40e040a4003801d40280d4280c010465600000da103d80c11600018411038103240c070501a100305160800000300101e10074080c0004101c655466610072400c49030b0010b03501c101a11900300444480780800c0c030a000410128072035042402210000400c0042d41030b1004180820b5a0000d49034240041d1201c000c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 444283354 1250 444282104 444282107
    0x9090501061a030f07141602100315061101020c0a030503040b0c03010501050702041515020f060f010506030117010902130504120c051902040b0303030405010e120a050a03020a0e1f 79
    0x110310107003050290060442c0ca40500d042e02c103110140401411603000320004a4040c801d8007204840351500c2c15055854803d0080211420310103002603100781d03ca4041c50342611b0080c0700741580d8003c0b0740703140e0000078a00601582c6071043c3c8004810703d55020000440c00c120306012500e442c600c2500d0701c40c1c8a04082c10500c41c0210300510328102c43c04200010700080c0e0b000816110242c1d81281c0128181c1e004070034040c00a41c0e030750f01c0003401e074043d01801c500d4035401040010382c403c10641103500940d2407402c2d020101c01e00b8854141c101104000602070280c0c506c00541210f00c80600104680c450b0f507010445e2640001009102c06039640e00740030800030b0550569001000d2860603004043d000d40b10b0945507214805c03410100d07012a000407045480381e801c04205100c00400f41c0b0b440785000e04001e800b0b4000d010360001076000c0e40003604003034840c0106492641c80144e8501c1e0a00071948003d0b0000c0d0300104d4803401b44003208990003c180da500b103011140c12090100303400c9880d91a80d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 444284604 1250 444283354 444283361
    0x71d0303130f06020f0c0d06090c091d030301051528030b010923040f0f1a0306010f030c26030705150604140c13031506030203160302090a0e1609090501 67
    0x39800c54010360181500540c5c0040c500005240446840003501d05600d4200001e00340040014a000d50017513002031800c4855004241007811443d5800017a9956204242c50b0b00c4240209684000c201031031002810307804025098500c81a03044001c2c2000e00e1280b042c0c0c2404040a80d80041e495924540b0b0b956800b088203401404031101e5443c10513a10210003210310074100748103010b1540c07207500c40004913154120030441040004200030015003c0c04042190b040302121a002e8411032000241100002c4611400c8a800c21025000b45040c1030400d91400c2480741e50880d91601e129454500600a000a01d03285125800030060a40d42da005102040c00041402e0312592a0090800d400c04003220b2030790f0303c94124070301140c3d146040c1c0c2c01100044c1250300003400010029403e520480034076030201040d68000c9003220b810140307101c1050f8102e555030000039048121000070800d80701da59000500707010800c5058501580084521282e0000380782d100300401a25950403d09005081c0b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 444285854 1250 444284604 444284609
    0x705010804081204080405120c041d1b010c170d0c21020c071505030907080307030e13200703090803030408041802070c0b0a02010e0c09071d0303130f 66
    0x92048652501d621000c500c2d000303041520030b1021400c00003c00304800740d001c45003d00402050f002c0c88201801c00303d0390398410080001d000f58030b04003004c103800740c2ca040500001c1309031380014400d480383c40317840100311a42d40c0506030500c48040c0c0b81900013151820b82142003450b245c00542c58100510103c800e490f5020b0175a018454082800d0600200c0c120b0448032074500740d0805a50344444a4a0502d03010041c1c0c0701030344038884060302c000e80d1b42d03006008500819040044903505503c40c080315850b441200c000502281642210510a040081880d00e81e9000704100003400c030345100a21a035014425003d010503c4000303806d008040d082a4181e01031310100c4015400c40c6415a903042e40c500c46e60180320200030100301c1101207212590101c40d8070a50081d003c0410070360351482900c864000d100418099401c201c2c40756165400041c1060035054010b00200a5450750380c400d44084421403100c00d400c25080c2d03a00c607180d0f2810402440c4000f02805554006443e2020644601c072568 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 444287104 1250 444285854 444285857
    0x302010b0d03230706020f04051002011e113f010f17070803130f0b0702010c110303040b120702120a0c121b050c150f0706051b04080609070501 63
    0x110700410202e6440b298000d6030040c1603416119401074500501c06a001d00d80d0000d020700d0002070301c2403411004c480030700708542040c0c41c10300951200312400d07800d0300c207104a208105182e11852035807100340c035000204525044410315240005055040e100701c0e1040124040112803c181c400c40a041003640540c40110441c1030000fa50400c9889210b010040c03160020b06e14180c82c1c0300c00c0341d140500c40c030382c02045550210fa070381341402c600f00d8031200c08601c21559026130030040012100340a100303e6101c00c1d4141d46d0555444485c3d51811091200000d4164041c482804081a1021008001d04503d000100020154540360700f0080c900a00d405010600100034004580000d8000b1000d45100d82d10a40301d1354003000822044425250420f094140c02c81183c0191052100208000075054404e0312056902000d03c1c0400b8542e2190688504c11240200170381004510668880e0b5003000200d022000740750390b40c1c04d20805903080783e00131450b203810401c00d104801004000300401003000707 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 444288354 1250 444287104 444287119
    0x506041115042601021b0c150901080711030405040903030204080f01020702010c0b041e0317180703060f111201090e16031e080c0c030c0414060d030512010902070302010b 75
    0x70f2030581c0d100d101168040c1c1070700030500740f8000410b40c429010b95a4101b84030041c5e4804d11038900000c4e81e40c4141110071402500161290ba10b0190350404542082a060312201401d0b216a0022070381101e85600303454081c0414000490395a0f00e0380030f41c55a2500a6a0260715541004040381c180034012155114503072040200c100142d0b0040302615070380b03400c0901c03891f03a0b9a5a0070110000040312450b0400118402c010500b01604030011003000c803001021038610741e41d1640201b4103c40500b0f142e951507485400d00300005542c54128040c400c1420001040c10100203080e0011600000f40802900e02d40600600c4143c40c00e1041c0550800c01d14001c040c030f05290010311072441554000034140b0303c81416104807290001c22000902940129080c0d902c11013040d006450b42801c1d06064400d002e5040b0000d414502401600c2d000749642d20351340d80c99100c0b8010028549000242102400001c0c80381040b40e0345031072859130081401110140e9103013070b2498024210f610100d6030f035104899 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 444289604 1250 444288354 444288359
    0x6060b090a0b0c060c0f090604060c1104061a0c1e03070201081005010507020d021210050105040b0916030c110f0303013b1503030d0c11030408030a140403050604111504 74
    0x4002134042c1d00841c50f844060346c0d41c00b48501c1880b60380300700c0401f1500088001400039800313a010b810101c01500070303500401814005002c0000b55482d91003015a054403210748007100d000000c00500c41c400003c0c0465010b2004010b2040e11a4030380b4003022a20b400c040340791800e40d40c2102c00d41c0e07070102c1c074400d80a01c02420840060004c1c00307a02c4000e4091819075008404540301c02c074060443d50003020031a041c0c900c00c1c4070f070000604001d00603280118180768507031016082052059001d03801045c460501c0c0c0c1c0c3c403560700710000d0104209100800c410350b0400c58810760300340403502c0c04604440145a4a44c100750000344441c5250740b0b0070100000c45942814500300f20303120720224071541c3c19040d1442e19240101031503001e07403124465050100113400301c0e10f500e041d8400e0842c1c403000c0d01e80a00850010038030780e8490150344244000e9030404c119105ca01031103102c880300031100d071542c030605058594036450314000c0200c1d070448030700f85c2041c42e81c0d0742840e02078051a950070200000c02d14150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 444290854 1250 444289604 444289627
    0x503070e2a090405180d0201020405061b0c21010b010c020105120726100503011407260a0b030105100501050a0311040b0309100e0c09130303060306060b090a0b 70
    0x2040091044640300302505100005000307075048441c0d80d000108248601d082c00c0807480c40902c85804424480e208458010f40d6807070044c001d59003140d6000300000c2c1414528031160f02c410400da0720003800c3e4014003a1403201780d40c465a0030000c400e46014024070404540011070b0844050341c2105043c00300341c0a4179001030303a025089031280c103590768032020940c903401d100307540c500c06403200100e0740d555200000c424500c1d451045403141c049800081942990362013807600b00d500210401c00c000c1e41400018241c20f00400103d0701c188001e11680e20b02400c25100c0b800329a40c15280407560340c0d1516070701ca041b86400d000307580e00102e20f000c501805514080010f03109200300c0c4078403014191944000898607542c1800d8a0040180b219019038a180440700241ca440501404007111031902d145680c0580d400208096051009800103840703440d204042c000311700c04030320200d0406403684404000a6040d0203640e00a100d040c108a80380e8110800700700c02c07000142c00912100c075081c01800000d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 444292104 1250 444290854 444290881
    0x30809014d040b0717030a20040e012105030d0b010807020d1e031506030c080f01032f0a0905181f02310302040b060a09150c0204060f0503070e 63
    0x11040500c0303d641d260007600e04152182c425880b07003a4003140c00f004200040d14144c00c110109604502404501d2800c0202c1c0d04c907501881c060803007540035440051081c03003400311490544072020040e021142c0c4142d91503c3c510350200c0d215488032a03c42400c1030340d0f56009400d068004140c0d0002c1c142c0b075040101c0060030030907034092140c0c403800142110300e48180a940070307000030865010314040c49621803138003802600102803a84006400c1a0019440142f078100726816650b00a00c084200500e031441905881039550719080f000d04200321003003590341c80208180c003c04007854041201d142600710181c2c5004841d0500e042500a002c1d003020402022008940c00c04c1c1036000140c0b41c0130f02d00d40e80d0f0b40d8420401b21009040786043d11a0162042699581080b244200d50901079280d00c901405418007440d40f4001c0800c6450b0018040074081d03400d4800031109611788249608440d400060a680e0190310040c60b2010001d010301c024181401010302400d100003106d60541021048080315 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 444293354 1250 444292104 444292109
    0x5040c08090d0810080f160e070504051e0d050703020a080c06040e0709080303010e1b1204020d0303200301031104020a08070f02100f0c0f1b030809014d04 68
    0x80201003400103909041c03021a44d07018107002000c880c148802d0b017140c20303941d50a01c2854009411101000113000e2412000c4030b01c214417035583e850a062030f08050122412181a15007178107800030315106074a840d14440740c0003d03802a4000c000c1d40d0301d18010310494915641000400c0d0b0000d0b036104225443c1d00080790120f0380114601c05007a910000d080390340c03071400d41049c001d50000000001e070411207990401d001d25030000400401c065201c04941c3d20b44a218946020605003000007000b61400c8130b10341074900e00038240070544500101c0003e004d407201c00f844180b0884003000601c1800700d21081a0360303d080540d0214500740070340c1c3c7c014001e00c0c00149284200581d44245121031442404a11078032f02d030020082c0002c82c0d10441820144c100e2441070700004044009100e5018031403090800c041c40205440344d100c0003584c40841d006040140000032a42d2941a80e103004c110403200307202c255010740440030a00110003c2101407654640d800140b920701c0c40751a103a1012001e044504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 444294604 1250 444293354 444293357
    0xc06030a0f0b03010225060902041d0606030a0b0a0b01021608030a0e061201123824100c0506010803030f0a090302061612060b1c020301080706050a02210405040c08090d 74
    0x10705101854448023604000e01d00940060408104103400307413403000340103102c4955006032803807a6140300074580e440c244c51102809442c15003010848000c410f9029943d00c0b80f0603c1904d0300f01c18607881e62040c2102c04c1d8020a401d0b40000b845900b01a4026644404884201c400354640103901c50b00082005040c0500401d202900c03070f000082080e010442c903400702c650420101850f04020821800c400b41c11005901c802e50721001500380d07107122039271004802c050448250505210014031501d40c000e100d002050081d4220b0700c00c00718404101e010b0003040c00724029a541d15020105260b2506c001d080b5941182c2080140000a50007044082e844640444034a400b001c0c0c40500311240103503412100d81c02e503e40039003c560b0002c45001400a00d6901005047c0c400b0888002c50403444240f1034100c640e0406813042c84258401c1e8014541e8040030310440d91600d124600302e05400382e840702c850505010009080200741014044e5851010890800502c0703803611103100c40d1248446041c1e00d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 444295854 1250 444294604 444294667
    0x151e0503010207083a0501050f030c210a02031b041104080304030f06141501021e0a0b0705040e0f07120204080a170412030305100e13080a020c06030a0f0b030102 71
    0x244400f04285c203000814040c5088003010741c4000610320081000f03000d4180a80d6070812a65450b0500054200901c003003d08030448100321608400401d140e0b6428100e000d000d20b440b031401590b002c2122801141c3c0040d400134031400364604020448030040010010b00784144401c000d0310f00c000c02135900f00c90300070000c010306682071f04d003540c0242080055503c044c60307000c09108004021000306000c0c0c000c281c0071a00c48828011251721800300c01418044141c0c0290b0700320001500601e0350079004900d906201e1308054461526078408d01d8100c5440c03080e46010410089003540c42401c043d80507022800441c070b410305010109403548849a0081c25003035401c5039400c88011601d040300c00508005a008030b0035801440d006000c0c2005584041c0c00044884000c036602d106281c0d890300800b141604020000d02681d03582d48541c00c14071190341580540c3d840d0210644401c0c0003103129421802c80019441491042e1000316115002820302a81c0f05200d40318402d040e1207000c4008041c20209103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 444297104 1250 444295854 444295897
    0x10080a060e010b10030507031d030421050a030f2304140d06021614010605060301061101090f0b0402100e0f15040302060d090209090c061804151e050301020708 70
    0x702c0c0034043c501009508159001203100c03441c0e5050b44100e0240c4101d660030b10543c1c1c424803076480303042124007200c982c2d0b0b0000c10040000f003601c10182940001c02005d200c0d4502c5058685906225003100c0030b40c00f1410705124032094a0f8440c03031603140703108215800d69101c0304c515145505030107a405202130b070140e40511580c0c565218909607071450785c0410150750b101903109003d0b140c9802030b5411286008410700d4804042c4e81800392030207699010300042d05507840c00a040314010030003201c6040035540d908003100441d003049580d040140c000e2900100c607042a00c14070000d6205415210100203110b051106030b82d8070b1a030010000d94044034002c0482492218196041c411980000e601ca10b0001e80e010180396290450f6040038000c40746106180d0754010104d844001c80e4070569804082000340302000c0d4040384a140d0300b03080107040060b004250800f880801c0c084c50f04100c2c1030307425641c42000d050a051210340040c0809900950510405503140c140e107000e10f031005e40110340c00b40e124 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 444298354 1250 444297104 444297131
    0x10605130e060d021201020a020c0a0b07030507032007030b070c170f0c1507110a0804050402070819170601020a11040c030e07060f09050d031205060a12050606030610080a06 76
    0x180c5540135001071028032a41030741c40c0210b00030b500aa0b15140980518141d89500c0d01d480c462980c22120100151450152596022240c0d81d00040084060085002c0e581e1410f1101c0040300c002088148024501c050550811f5201354100511460400c040300740a04009141d90080a0210700a904040d888070501403424220780200703044030340c41d0320462401001c11002c103c0b52901419507501c401c1d081d0303e2510b00803905d80c201004007400821040100b04402d00305a402819003c0c082c01a59040c003008031040490414010701e010005881c030700b0896800c41d0011411341c0c005100340010200c51405030383e005d140c488440c8010b8800e540e5660440070305070194001c0c898250350344041e500e0701625901e01518031b0900d61120400144007080110740f034104443c20621441e019180c07501003c00c1c059089020702401070003d40c102e079a150740020002442400310880c544940090b01062401c207041c0362a03c0002800c0303000310082d2040400c40c8020109400d501e058000201091b0040c80c4880b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 444299604 1250 444298354 444298369
    0x1d100c02010e10060f050301052a04031a0a06141305060406090e0a290c07020a0b2109010c0e01110f0601170c0901050f040b04111201060206010605130e06 68
    0x3998030b038010b2080c51016405541c0c000025104000d003101a00790301c1d0b030306050032160102c807621a600d01d212650b506000c0c801c8042c10351264244011481c0c0341e240d0f80e48050110f410f040c80040d10030803c081c0b00c2e4184140c06400090a0104014907840043c2c6c1c000034a04009004400105503581000c5a481c5e1180c1c1c0262014003801c410600004c03611202d0342c0d035071700701c1c102c003c1d40c800750083c8441000b0411096042001b10504e1038060041c0c60380843d54400d80d105c3c110407644003100d0340c40081d030f110044000e410105488610b5504c1300c00e80126400c0b10407402045c00c1240d9150401071018075030000110304d0600130070718000c072450710300e01103c91600b000612000c1c0c4900c90f000c000900301c089403034032030b45821401d02a604c01ca1005014001009420300501754011100b804000f2181410ba00243c50100c00a00114128039100c4851100303502c80c81c40f000700340807400010300c60290100112030042015140c0303540b4140881c8241c0b00040c0450040ca0b100115107408900c980ea1400e6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 444300854 1250 444299604 444299621
    0x3130804030c03033605010e04140910060f080d0804140a0803100504050f0610031418122b0b030f07030b06010e01082a1201091d100c0201 61
    0x18603222a03204d0402600007401320341503c9020b20100780703801c0b9420142d080b50107665044103a20b00500d041c0001074848001180740150840d40d108000301c111300d00c80d40200e0040d01240c02812903c44041004c4042c1e6060350000c4844810800b000c0050440000d0b03c12040021840c0c401e181d40ca4501c0c010068500c803c1280c403651040820160030b01c04d40030025401004142c84016a403503442090000f603c03821982c01110000203000a9828101000081002d4040d4034000443d0700d0714142d0842003440503900401405552501041098002c0003509041c1e9400c0c03207603c1c00d160901d41034410120031404c078084a55556004200656040c1d0014140100024141c4415450340b8810541d240c1c001e101c1980c159147c4004039065501071040701d04503a8042c0d503210880e03507411140e2140150610310300018062212030000d038901806000d03240c0d540c6107888a204a52411007032006982c1700b0501d440c0303103603103000c03005944410000e100c10680380300c60400309829100003426030040c007005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 444302104 1250 444300854 444300863
    0x100606050d0509011803051201050d0b1501030f0e06060a1a040902090f06070305120703180803130b01031a06010f052d040b0c060a0b0105040620010204031101230313080403 76
    0x10104000c26810001502d01600340309243c203c09c4e0380c1d420810000465000002c3c00380d80100703004c561081c9110128580194060601080303002d4400680402c0311141c10405581303070044401c1c40302615040350b50900602c42d07080d280103841036100740744417503210328421038000b82c1e80000c0050235501c03210b403580078201d0001c1c1b0781e988414203814050711583c01000400c14050b0004000741c0c00030302a200342c1d07494410042184086610941e6440029400500074405c41c1c1c501501c1500054180322025010b54424400e40014107000340154001141c054161f0f8140b151580c58141460b601c00217950410308049030100f1480d65001c0030503000313201c108040c04451000a0003082a107003d900906080020074221859541c501005208880951401500050041008002c4203100310380c500d410002c030907000040748070521000d50890f80154800c40e40d9801100176040d0a680041940d5400c2c04440003240749001d604181002d544402010491140780046205047c40f00d00c3d426074020b194070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 444303354 1250 444302104 444302141
    0x6060801020d0902011b120c0c0b0d020c0709110a1409030a030302130603050103020609041e0507020a02010e06031b03130f0b04061107080d020a05190908100606050d050901 76
    0x11915481c0a440203c0301680480d203041260180040c0c0c80060005031a000903404c00300301c0804008890348500683d041ea8125030720700000c00d604811200402c04400e118000503540c00c0941c12060a00a055200012003460301f984666020035100c00c03600702c40154a001c620448042c408141103008050800b40c051080100c808105605a8014a8a0100b80102e5504075680c0d0f0811802c1c0c1da82400001d4014100b80f03c08405400e00e07801a03c0d010746c24040f5404085c1d00d294080c404c4072411924103006a00c000310040565070803036082005840156005d6240d490711405140c00c040b8034540d954014040000050564003070726044505050703000c850050429058100004801401c0c0c40507908980703001011041c5141d40070442c0e070340be81d000e40a58104446456010000d406c440384000a200c01008961440b81080d15008a008040c0d210002902d04000f552490841900e540c0a0f081e458090705101454000c03042e18031000301c140010a080c0e0706c0318101c1e8054480d65030080c0076500f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 444304604 1250 444303354 444303367
    0x406020d061d251e030b09130b010b040e0708041e0605090f030a020a14011409010e0c09090a02150c0a051e010b10051b07060906020c03030301031e0606080102 70
    0x4064060244401c0b540e40450140040c20b000ea0a0044207400700104510040c100881d840959103c044c2c00a141400100803900c100422203040c0300701c50f02003403911080c0510040103401440c085c0034110012000d0b007458203014114903410301c044d0882082c06103800004040102c0700744400801100041c595069040614011008d420142c2d0700e66224000c0f030100c022034101c00019118002c00300e0b4000c01c00c82d50381c2d480b1003440501c081c040303880c00e5480e05001c0d48a000c101c00c1840c02a0821000001c040a129915609207104210058804d40c81070040c4001c40c0070000306190519011104451b15645000c445189407003100700c007c403540504d903100b205118010410303071214441c15000701c460f0400304100750b0032100c14008040d44160440190501a44604041d0090b140070908907000161020300d600e20300012a4040700014021800600c20594140207201c11101c082d0025030440d411035a404400c210b00140d60a00800449044400e11901703401c218020007112000310354030748 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 444305854 1250 444304604 444304649
    0x30305060310020a110601050301050601020a02060f040b2107080402150f0706050406020928060305091006090605030c0402040e040f0812040b011d09071802040e0a060302010311070b0406020d06 85
    0x8000074013a61745002d50000010181018020a44500c40507400b42c444595140d00b042050b402259500e00b000754240008601c90f504000180707c409900342d03000d004800080e81e11190341100420810811542d4014400161254030508407284440c82c01c3c5a254464410811110300031114042c00c06401c000500c0103001050303005025060059412401240110f5900d05040f0381004401814061400040100301c0c0700f035010541240208058038500400d11070030340300740c0f0740301d4210a81d4240c0d943c0041003580b401300a840e00c0140c09840541c00e00c2d280240d0741c03521641c02440030700022014205a400c001e00c8104403107040e4143d4040041d1800c00d414000740c2c640f024080c1e1110180c80110401000c115200c0551080d0700e03007802003078200e041c03000c4401844040519000029001d000125a140304a0162845685400030002d03e40303146000042c00c1c0d400591460410140400c0044003041c03401001e1644107822610160b075030b8003c4080500289441d5211440701d0303400c0e04403c890720 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 444307104 1250 444305854 444305867
    0xa08030411032404020904030306030b09060109050114010905120c06030a1e05090d030b1c1b21031404050d080a020d0e0a1e0b03070207150509010507030305060310020a 74
    0x11419802c48001280034400c0700380c100741d01040d43e01d218000c0d1001600501d0715010f600e41c050711900e00032440781c0d0f9941d500c0625500c107854865a64000c00c00500101c00640315980c010300c101030700c41b41c1407101040003070304a0700170380070b100d00030082404d02d4032801c4400c002c00036070103402900044d520301d0003003403600052080d8840c46c03070130b0212110344910f0744945008032030058012102134020000440702c160000c2c040e200105412060310114001c03070000f404050090b041c040d031400b00d0414205201c6900d580740079000000c00c4400303440542d10b2402c0e200c40c5e030103841c0d42c5403d00d00c5115048003071100f6140640d500c001c2e4400c010305100020018000c0203000000c0c415021240c403101d11010980d000c140000515070044803400703041100d070a081111591300d42e0b40e0450f040840c1c2c1c5a00e0000001e074400c0751542d0250780714040030001c000e500342e501c4420503003d10304035090850000008080c0d105100340070b02051344807804900c80d60303020312002d9244800c4810855848601c1076020700031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 444308354 1250 444307104 444307133
    0x71401030207051c0c06060f0302010e060901090b0a0f26010e1801180b06090426210709060503070519030e06071d0603061810092a0f021c020a080304 66
    0x4160400c7d03030028043c0241032014007503e50513100c0d086800c04240910146030009554181009100400003c400d13a001d001441484510b41c0d401d0b0004030b0258018104c40c1880008184403083c0c0081d03440414002c02100341540c0000c0f01005480e06c45000c03401c01d646119248641b01c1d484e03c050f54030740c0f0f8800ca4079a60210302c0381e80003e03031aa40d540c00700406240d0446000c0c0094140110b010210060700d2103401001481c1c2010380d0405040c00c08595604000f02207581c203858105040c400500d40010080c00108a1841c140d403452800d40002001e90042c181841c0780064850301550445000703410510b240c110310030840e42c492800c0300000b03010402601d46200b4191001e1400d807003509004044910450001c1c0c5071880300681181180e9000000408006d407000707004502084c8480d071401f0b40e488000030102c1000014080610908115a64500100902c01c00350b1450a08540106140c2901050140c861001c10740e00f0b1016810182d01000041040c0c40c008100300030000961a41c001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 444309604 1250 444308354 444308363
    0x20105070306060309050a08030c040306090f0c0b0a02100b120f060708150d080a1407050a021305071d010324180c0203030f191a12071401030207051c0c 67
    0x1c801c0e03896100303070101c070005c0307201500c150050b007002c2000c0340300b90000f55006401c2006180c07515a0b80e486150441d2504a021035043d000c101e1040280f00f04201800c024211000c01c0c0d031f284c0058084081d41c0c80c051504241809503e56215a5156a800c074450307244030308140955500701541c198064848504a0b100d4011920803c0400c620040c80b10101514001c06032495401d03407240d8423114401e411801d040d204006a00315262541c42401c8050545103200354010a800d804030720410400c0718201030820390040c034000c00c12904903407014030f00e500c80c00d1810580480d00b06410048000d00b40e0180062041c1c540c01c2000680c403001074001c0780031101c411900c4490a21000009000c0c0c4888401c1400180d0007440030804840000440f00c4d00102001c650400204400b02040142c0382181c2c207003a41480c85001d4080c0c1400d000d10340b03440100c0400e000d0890700d410141d40100300010400482d04055001c43c0700302c1049800c1000e0042910000001654021290402071269400c0c4500f2035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 444310854 1250 444309604 444309611
    0xe0a0204180f0e061e0901020d0606090602010b0108041a090a0c081b03070b032d190e0721300f03020c0601030305160c030311010e070b0d09140d0201050703 69
    0x101c0310f06020400502403500d100ba8100303c42c060f04108410000054084046035508001e1115015803078400c14004006e140c851140b040d207050006421201c0e82100c6a040c014074804100000350403030040b044032071403103512640d036886103606a4509101410010254984144041082a0b0004040341c3c00d4804c80f85000c40800c411045c5030b16040948518541c41c102070001c2528040c281e02180c0000b08401d098a01c419103052070947d603c02d050700e190904071a40c840c80300c1400c14034080c140f2110050b00c014243d251419440c2c6190487d58011540500d442254403002c000112402c801d8500640e541c6000800d81d61000d4441040707500034a8010070f44c48545203e00754040d0090b90440d105481c041d03c01d6a195850581d51350f44848811105506880d2503007000506031055030001c2d500a90307809407052034000d43c441c01c494114448101690011804100c1c1c1c804000448040a01a40c0040781c810b0040c41d1200380c846031900301035080e005040d0525015603055005602c640c0040e9410b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 444312104 1250 444310854 444310871
    0x41104050f04140105010c02061303121d0d02010f030212010305061509041e0807080d060504060f05030c0d0602070803090607121812020705130219090608010e0a0204180f 75
    0x40701c10440c00103c611002e540100520b60240314044c2d0120300113001d40345000348540d10050003502c682c10440350440b400b8034400f07125510030441014008401900c011180000b000140d401c04004d030000d0402408034007494005120360155061148524219041941c491510b29212042122040c481d04000d410303064181c074002180390700032508491001d03d01e10111a07580030300e100c00c10f41581c040c0c408101ca240015803600003446031318241032000600c18142410002030f42c83c280c7c841c5001480803441840310f5680851a500d40346821200781e0b0080710030b8508000030b0b000354100603124000100030005007582c007207001c41c4600b8542c0d448250b40c9546155000c03c4407a0050b424650400c89408080018031034590302e500c1018038011190543d6035440000c4210200d00c05a51109802140400c51100c81038441c032400100303810700c500010300f058001020004140f090901600705040896003203016031381140c000e404040d0486091401c155840806044080c202e810700b54a05141c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 444313354 1250 444312104 444312109
    0x406111e09030c0a050a0e04030509060d050f01080607020309011119030f17041713050a08030a170106210f140f090c09161e03050906010909030903020402030c09041104050f 76
    0xc4d5010b851000b404c000415081c007040c107002e840300138401c80a00504100c01000c1d55600405400d207040c200d6000301d0a450103044440b0b258006034800f1015a102c40e0610440c1600401030311413159003843c00310554000d120b41c15142012404a0fa1031360028400c0c0081855881801c04034041c41c540ca40399010260051040d01c20b460840d800303008150310290303a410069200b8001d005083c14282c0070b03110a81c030b540c0010b60300f40d00346c0e1042c1d1003a13100040d002c1800b60080e1204a1440028000030f52640c0344c502c1c06400701d101c02e480c04400207503000c28074500440c82d5100d00c0340102da84408005181001220b0b001c0c0590503200502418507002c00030b41c11100000c5c40f11101d5002400c00711243d120900c451710142000b203200010b02c4920340141181803624890b40104000c40d0340d01145030300705265094141030781a004010b44c039040c100c040c404290080c41c0700b801c480d0706480041e82c0b6521484400c496009010649034028204100202c0c0e506c40a4060b00c1601c5085401e04014034000b0304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 444314604 1250 444313354 444313369
    0xf14100c050c06070f050106090608010b091006050304030c060c0203130801020a0e01080604060905130b0115050405102a0c120b0103020d02280e0705120406111e09030c 74
    0x1402041540002401c035000c0c01e006004c0d01109208a0201c49004000d544450945040750020354074240c0d00c1d00100190982405100c40345d0100783e40310981d0f410003651010303010b10140102018403c00001180406104214030000e580e0007030410040c0b2070b10810000d4803071340082c9000301805000395001c10042c0041c03007258200806a2903541e000d981110054603981001441f855026544d440002600303501c50140a10a100304041e0450100061402844442c41030708140340090f40c1c1502c40c080150800210750903114115003001a41300004012109000c2e00c8000608007101e0762101d00c4020300605800c0c00142c8559042c0506caa150340842095000340a0050120f00c5000010005030611616010f00203001a00c00014240340f954006032400004208940308101c001d41000350194086156400440700d1a00c14a0050060301d18119004068406803102c0d40e85e031024081c480d86e00c02107400d0140002c00c01c00480312000a81c1d0059000340d11410301a0140d010180100e103027041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 444315854 1250 444314604 444314627
    0x16140114030c0d1d0d0e041109060403170403020a06080a050a0209030307030e0a090204062105010b030604020a030b09070507110603090d0c060612060608010c08040201020c0f01090f1410 82
    0x1400d8140032440f050500904441e454120f1586190300c03180402c5031003440040050001c689880c4040e003446814441220380e00501c6081294041c801c001460350f03001d081310220b03908510110540d034203c1e00c242d2018421580000e6021101050000e0400c2d0880b1341d41e07126403803404007040980c0c0e80c915030350140c3c400c089041e54160010420380300000e010714610301c02e1180c0603216103c81d90702c6641482c00c9900c0f80e04088086903440041000c007800e4100c10240705454074505000e01d51401a0000780c9010180c4414420303500030488100103403182e400b031120040010921242d90910000140240e84901d0003541d0007a09030301c030400a0f08040089070b018a6549000f400a0042001d00304d90740d00c01140b08462840d00c03440e000403203500b0186c6541c505400740100103a0280752030f15060840d03a401b8071660500c0450350801015030780214412040c103c0c160381060082e031b900d10040f11004200d0f000000c01d15400031010031100101c503000301e85454141c40c2d602c403903415410190b403600d0614 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 444317104 1250 444315854 444315871
    0x5100806090f06060d03180b090a0915030807020f0a1418040f06020a020f010f020d0605190e0c21100519060f050c0d030b3f1614011403 60
    0xc101052441c205140707010202c5000746041c0194007034044072030618847d213a10a074084170010400c5140d918041c6000c4000300390308001000f44c041d866800701c8000d9200e110181c583c0d8008075001e002c0d51a1440c10600101d8028402c171030322a1541110444802c40c4450680180d8580545802d1400510b5a9901981e04900d00e51280e40d1213076070320700103540440401030850052494524807401c0c06d008501c3c001d0804640035842c0c40c020041e071011100150300c12032060200000164000c02d4410b451410348881c1018100c03d079542d400c1c00017072440340c00301c00b50200108280c0ca02c2c103540d100d0035841c00f4080f06440005070340d03a1201000340604c0f05a02d00440380d410f41d0420805c07180220500314041c002414854180600280c0d11070030003900869250229407200e01c0c80310641361402c00e800c4100344055480000c180000401d100080080d91800c42d03510035030761080c0b88840200001d0b4030b200e803c0103011100b19101c641c80204892a066400e0108074202209544003c000302a00d22440c204e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 444318354 1250 444317104 444317113
    0x8090a0b1311030f0a030f030b01120b0418031107090203071e0306030f0f060606020321060303090607150608030306010f1b080301060302040e060a030b01061404080105100806090f 79
    0x80c01c10012403031003410781c125100c0302c0460070507405841c01e10088064161440190083c4440c42c2400792400f00300811b40410103103000e40d1504281c0c0c03c48000b07101c00030400030004001c3e034250080b41c014105002082c00801d90f503000c900405500400400c1c900e40b11a056440e0720b5550800b100c1680426550000410075480c0c9210b0105004c030307802e0441640c145004601580d407925401c0c1034031620079095070546100310031032050040900424004042910041d403400c02c44d1040110700303605401c80070b400760b11071401294440d07504006075a02ca55004110703030b035520103520380090000c40700c81300240c44030704000c3c000507580f402205403031117008181c403440010309459070110342058080c000c10300591411b4201c5030109968001550103008103031030051780c1301e050400d43e4200d03003c003e1085200e440c80241c240001501e01c0f5046044541d01d05080043c007060b9550304810f0300a40e0001910346d881e01080100f03010030480f100041751880c4058400c01e07241c0e101005d0312000e180c60300d04d805512 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 444319604 1250 444318354 444318361
    0x1021603080a02070215070201080f04051c1205130b0901050411060904090f030e01090f0b07080328390f0302071b030218070905040b1f0f08090a0b 65
    0x141c100ea644024400030043c03404049a00094801210b2040c151507900045903440455802890031600309190043c0f200306450141d494585c1c8515103c40c0c1c03400421040c0d003070809a030288001c0d03450b030011800c040c0040d00d041c064a400c184c4613044143c4002c2842008200464418480e06000c0e030340004120b02500c1100d01030000c1c59025600c2c00750002c0e542c015400c04540c044000f080b43c2440b03a511012005828400180254101d801269a07240c2d0308804000072820001201d0301035a0101810741c481e80c500c440d51092032030f1541400145002e580311070141404035400048181090218141006185144d22800860030501d200f80e0fa80784115941040c0d00907501d03010003001600d0090300c1d107290b0390354003011280c040e400504100003200c0d0a00c00c601d00300306d102c4200850102900072924240d0001086001e0600c03405015035990744030a00581c030341c2c3c0c000c01f0401540c110381c1d401946940900030001c00d00841c4400c0090402c40111742e00d01c10103d09180650f401404078405900c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 444320854 1250 444319604 444319607
    0x81c1403131104020a030506030d02010204050f040e010e0703080a0807030b01050d2706050603120702060301090507020a0c0e06090108071505030c092e020304030b04150905070909060e01021603 85
    0x7031000340207035500e010a00342610b507a40c3c3c030300080032020900d9a011a4030b051030000e044c40c0910400c265015a40188800d02c840d1310307244260403849200700c2c0c001c6500d10360f041800d40141140003140100e80203006d0080203100c9481d005228007141c580e101d41f40307641c2c0c0035000c404445007400e6003800550108900007408055400461411a596030b4091b10101440340700040c034144901c04540c00da40721001c111040c5418000140c620b02c00c14070180c949001603001840c54401401540720302c0340d46101042c7c031130f44200100040302d540708210109003a12445080f80740081101c00ea80701d080002c002240340440031500000321102c01102180100343c2c444251034036003004110685051050001e41036a40d01d014681034104280e60011040b90500c801c8111404502450a800d55004100800010f240c480026501503044040141010141c944860113820b650101074207900c04c0c443d002c1410f8080c1d5114040c118420041040810b50000800d402d074040c42420b1410220199414004039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 444322104 1250 444320854 444320881
    0x614030429090c01121a0d1505150f12071404150b09031203010f1a0d1d0d02060f16091208030106120915020d15081c1403 54
    0x280001000029030a100c81c0c0d03460001104444050580d403040c41010345950300a0443c00d0741c140c044805010300b1006001d10300004401c00040c601840c2620219424050501c0f0395111902d1101000d000a04100e02031482401c59041168414481440248020b15000d00a003500b0780c2c07420054412181f84c802c00c203050044c014400b90b041900c64040d055955030502884016000b4403405a03110b41030a03090503c0d021480b2804080c10404000600900ca0f00c1d68184045441408821412103120b0400c00594080d802c1e20039201403e256203c003041c10070844400703001110508840c04103040e2142240c5c0c8801c02e840b03012000102c9070104290400790320300170910790991f040104804e42c0c1c82c89029421f43c4921001d40d50300402000602030290310044480524419040601c040b184589449090480ca140c0380b58a044c2d0010303000d2460240c5802030400003e086d060f4030f207072035940c8082584032504840c404d00440071a05010f0000c600420219a0014030058114190740d0340d050a809603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 444323354 1250 444322104 444322133
    0xa0b0f06041508010c112e020409020c0607030e03070320031605060f1302280f03050105010311010c03020601030b0a02040906120c0812092106070203070c06140304 72
    0x115403103a42c84040c440350101800000d010000002a0401c402103004103444040c0410200fa074001c1880c240c41030000d84082c4682a0343c910302031144d014029503040c000c1c0310b2903000182050002c80c010f081c4803004a922403007082140c40c10301011021340c902a80328459401c00a02190b2024040f5840f800e40c403190351115800c800450f440c0910780c4488201d0128011030403501030344110f0400c80c000080709080754000003044806074840351142e000924141c140307158140607000e5201d9410380b203050340081c4e41c01400401c0380708855585a0518601909007408150b4041c1c1b001e5102480c0c03544a07a00c8010400c0e01a03010b4801a42541d0710031048200c003900032031807180c080c00b002c01c2d006514403501004246100340303040082e0451411101c4214581e120070025000340120380c142200d40d004072000d00e0411a84040c218203441c0300c451413510840003c0c800c510806c002c00100580000c02417605600130010031801950324942200e42c01a40d10b40503900d0703802840890005a18152070416 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 444324604 1250 444323354 444323359
    0x50c03190f11030f010305070609050907030e101112010f050d030503070203090301050709030b09070b0418020c100c09120206120402180403080a0c020c0303071b1e0e010501020a0b0f06 81
    0x211000b08040c6003074142c2040d1001403407500440700400401c035042180300014001402c00300c00c01841c11001801c2c03000300900305c00038103031141d050f211004c0c018030401540c1c615040d01042407030214a8000b00036008103131204d900c0540e49001040000c880b05a540454000800b4014242d60039502200c468002070968415031000380f00b5101d050b582802403a01c10110b9648600f4960725605040401c5400549052070940100c0c800340b1003002410201c8042e40c56440094191b80080001e14000384a0003024103158080c0300088114602c0680101a48041e50360340d51000d240c454a400b0b501da040390000035480b07c000c1058080010195045580c410300040041f501c101040d12440501d130342c12901100024800303000c0010f4000d46100c2c01c01850f440f40700070324215200401199a0348113065000d0400c949240082111000c0030ba10030010b8858403086030b5289056aa040740c21019a0158107d0485e040d030000c47c2551001030400311341604030300120b01c191180c100e0801d046102406154 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 444325854 1250 444324604 444324611
    0xe0d0c090c051605061e06011e090b0418050705280905100c0209090f2107080c01090314071221020c06060906090606030a0f020d0513020103050c03190f 67
    0x804040905210049502840141a052901c6151110304000a122103008103158000f401f07996640000d01209140315030f2006010030703808800940701c9031081e5202e503088400004020810309016103401c0e900c08114070080c02117866940080d50207000b01005006040c88061300040104446c2000c4404d448081c1800e005942d29080490b540490000780c28010905d040050000c40c01e1039424154809140005804a000e6540b1070703030784600b03d6580051b1840b020a850101c48602c0c1c01c00c686220754015405a514941d00868034040c0c070f80751030160081031400e041c0481e4800d211341202c00c2141d018420107824941c441c8280c1c2e04104048044c0000e099a000012003002544001c10702c0c6002140282607a160080c1001502c2070010030050041505106000c0181c540c071040c1da070811040000402c40301c259124410003405542603100c4002e0926051000504446c3da60a0005000ba80d0900c0700703950380e410508152000741c0700075110100840002110400f103074003d0309401040503010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 444327104 1250 444325854 444325867
    0x607120203061f180506210a0f02070f1704380406030b04110c06010506030c09090c071b0e010501030e0106050d21020d1e0c120f0e0d0c090c05 63
    0x1420840f070b1018600441d141c10012400700c0c41c820030303000051108407140d901d04a588824445214007400c0d8089000e805c0c080852021605604402109113507010210b446540a051480c801490410300f510720105031010520f50405140c11513040d1201512401110030203a4034000c030b003444840194002c2c011152049280924110040c80102030070b9070f0100e20040702400b0401100c0721741d520704244160802c480f205503d008100141194011901c3c29100d55606100f400b00d1310a80da01654404c00c10020450f80010132405410440c0c0591000859950303008994134100c0c10707501410b404044454010451913210b40c008a05202c1018004130700140c0e504045240d00e0350390881140c44030b8003d06940c8107603405420590020040e4801451819a01400500520100601c1c036626400380007800000a01a011041e031140e80321907803128000d86040000c05010141e2500c100103a4940800016481e01001001445401c03d9201c95aa850f14810030010100095003100380b00050002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 444328354 1250 444327104 444327139
    0x80306010c0318080322030f03050a0c080309070e06040504020306010519081606021501030b06090637090618091719020c15030402090601030209031006051002060712020306 76
    0x2c1002490131030300954480c10700300c208080413603442c4207242103200990800c1010801c02c0c1c0f18000480d805052440da40c1c0c1021100310f6218600250182c000c41c07000007448507a03600011101c3c12074801c1111021700b6180c8500b00400e550080c2d8003e54550b002074010700c0345207030201038030403c0310a0000f1a40740c59921019141030041b0401c0c1074020342c413030090070006940c0500c03444a40351020080804550b042d030f540c0701e800b1034000d00524043c104980008540d0b07154a08058000c030000c45480075180707400c0b103019403403000c40000142100c1d0752404c00101c0081c1800703010300341d40460340b02c06443c14001007440003c0203410ac041da0390a48104005824480b40c0f0000d0499502001034194100c1a84001030f2034402280000380c041e0303607900700b60f100d110815010b894009034119400281503c610004801901580b0142c0d581030040090380441d00707525601001c121034003907401c2086045505416138451000b220800003080d65011703c062480d0255004550005005001500300c102e040103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 444329604 1250 444328354 444328397
    0x61501020f0d020c120a0c09020f1c0b04060f0501050a03020702060904110d05090d050a0c110303040b090f04020304080f031305030f04061805010905100323190207080306010c03 78
    0x40c04005070b0002a2409824100800d4404100640c4001410701c4481d070b40c0c403007c0f845070a00c29100c03411360106040241c09041d60488090199441800c0309420142c48000024811059854803507460004001001c4182c3d074046c000b104c405855036401c02d03e2445003075010f035200100407030340058104031034103240e03580d803065900044412809944400102400d03030110386019220304030a41c03140b0381010041c1c2e4420110b0722403540d03030f1030700600002c12454241c0b08000184e01c4980d15001c00326010611032044400303020310b9042101d4084103607000c54180401c84c070041d500909032410030001c45c1c04a101000045410294842010b84030030007944072281590807110104150140005040103c00c0d8082303218075018000d080d004803401c1c54080042c2500090384619401001e100e03c000b142c103070003640440c405039605901c8007103254030010b400540d0103040720040040c545080707080183c2d030360920170f13035400d04c0c2c0c44407560b407564840700019116450b00400c12820001d21450503501d0154069 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 444330854 1250 444329604 444329623
    0x9050717130314030f04120e150a0527040c0905090606030910090b101409070f03062706081f32090105070c03080c031f080a0c0501050705061501020f 66
    0x845c0101507080600e840029012240e846804110040035001d140f903540405580450201d41c64141e91054420010b0307602c0d001d245140c82c0c051034481c1c0441d800c1010b010840c420508200c0e020480c0001805043e5180d00540c000d85800914000016006040040c021500104844c0c00c94800b40180c0700b04a003a1024234108540e545110020b020b48100e600b48580042c2031419001803902000341e000c1408003c004003400c0070003c180c0b00c0d1095850080d8440310240501507407c0005e01d080c050450071410b2000050440745242c0031001503c0000400d03c130000c0c04511a8062201825004082c060b250711020714810017020707410811b0802407080700c4240348011004101d0349180c182c590f10708490000386582d0a01400840103000280c3c8560400c1e403115241034501e071291070f01001e4900d058690304400b280c07016005804101d00e480043c00400c0d9600c80c0300071450440e01d501c011240c50103031090042940e84003501140c140421440d848000d4034042c8110345000440d0300c08545441c4c4002d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 444332104 1250 444330854 444330871
    0x3070203071709180103050307020d060609150e0106030204051f02010b040212041703090a020d0f08030403051224090a20090109141c0503070206030708010905071713031403 76
    0x540d004542405444d4032031004144419041c150301d15140d407501c92044e43c40003481410080414003c00020350302c1000644003009003040031034403464080b0100403444c01500c4191540c0400055054402c0c0211401c0d240d0103000a03c0e01c8010aa041024805c00b1002a081d03540340c03240d20a40e925644041d001c68102034840310201c0c10107062800d48009095110480180b0030400c101d0400303c002180ea442c1a415221042c2100e03041c1010500d10542c91030041844100000303000c24954080044d11096034181e0709015075454076030050281c030300c04a4892520303502c40044114a03140500744698404c08480010500756008002c05101c00c0801d040c01300b0a4102254016055912100000c045d01c4041030280301c40c021440000c20310280d40701c038a240c440d2401541070400109105503081264050311454482c2403261002c0c203200070034000c1c601c220749080000b031080c2d441613030340398115100404091015142c000f90711001004602c416410310071300502da0a004602900150f1080c130a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 444333354 1250 444332104 444332107
    0x106031e02040c02070305070b1b03040e1e25030b19090c0302090931030e1002060403210b06120603071e0e0a0f0504050606100203040b0f030702030717 67
    0x120310421048601c0603503c54215032011209000041001640106407069000d099403120b04030010041010b2400c10030b1010b600001c10002400824940914003c604000707480f0307075203d81d503800c92116000468800c007040d110580d5000c2440b2240c0c040d0040c1d1109860045804040003021824500003010a800000e0322080f00f08442c01032441003500c4c242180ca015841c0c0800c0b0000605602c0010b0302038000701548400008441a40c0e18003403100700b843e040607480c5035529080117084824080200e41c050f00020358104840342c40442c0e1603104603859111002841201e0301704010f9030407410b5048007450750f0f5480da81010354421006d84514500c900e201641071030710300141400c04c0d1960740302a0b600301d0404040071041601c5040e001c182c0700c1d03900080102d030381c401c14400007600c0c5010170001c4031890300082c00300748400840c1a40c0b04242c10b5504940f11040448220790324410342c440c01d0480b40b0180300344c50b26503607890011038001040348100c0e0b003091550b07281c3ca29030750304100200b5001d0a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 444334604 1250 444333354 444333413
    0xf03100e040c03060f111e0702030d09091104060203180102010e0a050708010b0306090a08033105010506060a0504140a0f0602031206030a0c0b0a210c03111602060c010603 75
    0x2141c0104c04100010740303018007a103d403406c800c6a040c0640c0c409409080c41030f000c41c102181c07020080e508041d0b00203003111025100c040d000f40c0790341680d0084140c0c082c00c241003888030380c0415045400311002c690045240c103001c0c81c1010300c481030b084401c904554840580500001040040c518041c1c02603000e010540d180135000b43c00c5800da2164140030f50004401c1181545001c0765503030300d0a800c590101d50300d80e00c00702031441000014400e424036503801c0001841c4030100c000441c0141d441000204035a0b101d080c204041401140001e2001500c104801e1018500003410171a00800c041d007a980c20343d45421220001d119550460801a44040f4034502d1805844501e190001800d40180240d00d907240c5034050781d001a8003a11005c5000003540d400150720450102c008500601d1016541c4000202000c000d44015800c1c0000203045c1400c0001038050241102c060390801c24180c540030110343d09001f8560030550b101d210039541c481c00040072849514010a894140d02c0301010000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 444335854 1250 444334604 444334613
    0x12052e03150b01030f0c0e09190908090f04112203050a050109030f210218030106170c0405011401030b06250209130c0e220f020a0b030c0f03100e040c03 67
    0x145c5060001c4100b40c1040c038549001760300014015840c04054a00400796540d4103403881001c0e240c9062958682c0c41c21100307809100741440a000e42910403140300704036101a100708403c0e1420300c94040a13980d4108552000310001081c2c480d9a6440414503500c000c3d66915814100001c0e4107042d500c0ea5141c0300c0010405034402c1c0648110003607402d10030b54240b41c100303800000018108005034030b560f000910f100c600d14201a0000d2000c0000c000303020303990f1130b5842d007810b2030311901c0a10500d1182404071000e500e024003406041c0d940b0300c0d4600340500310610044015100303414006030001e20402085100030882040c0e4900c0400301c0300450072202880c07040c022012001404041500060504100001e000309950801c8412212001c0040d03107540c00f61940d4070310546c19145441c00000382d403000300311802071500d03001070088800403246951504072100920080ba07441500d030070200800080412030f18040c1d500144061125140c860b105c09048210420a44040d02c030dc8400c140c0400c02c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 444337104 1250 444335854 444335861
    0xb04080702090c120705130e100e060103090510020906040e04110102072c0405071e050907030207030503010603050712090812090714060c160e0712052e03150b0103 72
    0x80303080c04081c64460b070540030804091002d0030b4541001b00024040c4001041032080c1c00c0034244000e8511900d0030103101c0311070103034403911851802c45080302c00924158028880c402d620343e0040702402c41e003200a0049002984000b0319103070320000030b00002c24101c0c0d546004da0300c034600c01c0d4207100540300b0000c000392a048060703112074480c400281e001054010154084017241c1c0075034000030b00380e4071140740c05410498a504001031100d861511b1400017036040d202141151015170703c0c4081900c890030102c00b6403050842c06804260100010403035940f00307500055120350145401450003103150500b506903180d1000175510468040340b0700c22901c04011403150450351980c020201c052a21000814084a0a04d004e1207003201042c0c880f0700e40014030500fa20400b500a5900700240c44070035041e0590010385030140000c001003900d13921341805100d07042c0648240458603270003103044a801d80284111604c0804899581e42c4c0010000c0d0201035903080461030b0401c0421a5210b0000041c110f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 444338354 1250 444337104 444337111
    0x60908030a1409010e0303271020010608120a0e1905060c010f020403050f06070903051002030c070c0f051c02090103030c03020f0a151113060e0a030b0408070209 71
    0x550410003044240c5074002542c0300300306000d070340301030b40b21864840181d44e1000841500e6404d4000080d00007800c030922600c0b902400030584803c0c200c0301d500e0303045c091541103206a980101c5d5001200e42038404003804207824100d0a840046126600c0c2c00b417140c101a000d030301d10800b031240410403025043e00701e4004207508000b44c41605410304000341400403282d8a1280303d014900000d02c41c500b03281c081d0420301215113100360a556503692840c200d03680b1292400c58a031030340503100109001e64401c10010040300c0d000001000f10202e0030407a44025840607101c6041d10004002c0000001c10008a40700148048000349101600c0c281c18000741000303003810307201c901802100b8200160b984007505c2d41529054600051a405107290a910305a080c161041440c07142200303c80030010a01107901c1e011408035014081c0450b01405007081d4080c43c3c468045490391031206103c0b49204c1e100d4110a440000c0601c440503a0f03c1d12482c0c00c90f1000e030303019030348610005001070075400d1034528180c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 444339604 1250 444338354 444338369
    0xa0b03010902030c090a090813060318080d3b0601080109050a082104050a150e0c012708010516050301050307290d09110a0b0d090602040b03100609 65
    0x89441a54000fa80b11a4140e40c414070400c40308010480c24402d96100d048129031184040e40e540c1032400107d00c100f13032035119900002c2e09101c025200e444818640c02d404031392040149080c103c81d00d80100c01303800c0d0800c15051159540c02944d05445100c0400041000a400e42d281d0400864a2290070440d05030002c004980c141181100000c10000e2040045900034800d84d8036000d604003501022126078003500600b11114041c0418000b000c154001001e2140b9030750b00c1401070360000ca000790391b821441c40f11140c010f0b20035a907083d4040d202c410301d803209410092056500c041c00c2c0b00c00510687d0440200d41e9540c0082086480c1c0d1030290388654519801c04905540c5004002981d55800e40548000300e82d0355400c40a5550107151042044142032000320340741d60240c1d01ca01e006200e80d4001340c070f070f10144101a41803030411104003010b5603200f1405070310707109040c0700040140c07030b8650b4200c1c0c0c461750820000510000d4000510f0007100915640c101452602a001701b0340c42072500100c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 444340854 1250 444339604 444339611
    0x109020706110f0a0306081f1a120715081504020306030c04021801020c0604081c0507060908280f050901020a0b01170607030b010804170d05010b04051201090803040308091f02030a0b0301 82
    0x243e00e404026441c072500811000027080d1400502845600c0092202c10180c210111100c8401e6040020502400b070751a0750b018680510003600007180d10a02c16504031420a4440301040306a08080e00110741c0140041d04640300704201201050890748884100000344106080c00002c640c2c1c144482508440d0455403541403604101c109603d40b003407001d02c0300c1524121400c0d20040c034010001c2d100c3c041d4102008000300000c40c145140b1a82c0492080440c1c1000480f010070741d6003e0540d0549200869520011307446031200094403107a01181d94079042d8400c1840b400c000903004400300317000c2c103681c3c1008421504a154038518114014022000b8581880104030007640e0103aa140c1d4000e4201c803501521041020090b901c0d03114660010612034240b60000c1040d44030f05006008076841038a10034000402000031754200c0ea500980102800010000300f030102c0d100e40015a0000351150648907000c0401c0e174080c100e03041412040380c40a4000c1304020100b001440341e000c0c40032041c1d0091 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 444342104 1250 444340854 444340873
    0x4090c08060f0d15091b1d070315030b042006121314251e2c01060c110f102102041811040e0109020706110f0a030608 52
    0xc12100e0a144624059440f21410034144014840428015a2140303400c102084d82428140d41a0102e05041c43e01144007990014100d0b4461040c035201c55001202c0c1c00482c0c6400104501900b44105c0301000314024040220125484480141c069481595103401280048030312600c0c0c034262440051140f0b20034007103010000d4a603c031041c1d01188610410030b03090071a00d400316075a01e1095000080d40b041c07101480348500448109040800c881014610069540051252000600b44c01c817078030102e249010803420781d055481951a40841a001c5107007401480d44056241c426405400007602009507107040c058000d08444c0d1485094420003002940600800c00c4070406c09200d0040080382c02c808011103004266001d40c0310344000c0305540d9a96a00f802042c19885003028620742031800300c0c41210100c0101c206c03004c903030b40030001c411240c2c40e00084800940040100703949054642450000c0d114042000745105d2400d582d2054480c0c6185000408685064000c07000d19400100907 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 444343354 1250 444342104 444342109
    0x2070e0c0708071e0b0703055a1f05060a0801050d0615080a05100c0e060a0302121e1501050d0207020a0305030301080703170901090504050c07021504090c0806 70
    0x319000c96820544d122448414444240f1803d1041c09000d003034030050b1002d010a1541c19080103004054450b012607501015201d81100750307400308960030205000c00d0b40740e0840c1c003012809001c1607c95010610a442c080b08034602c5111040310603140040c44407100050466407900d501d0701500c4152a400d003420000d440c042c007116410701505205024490018007008415007111030401c0c844041548115905c003016903954001d020200e415004001d02c013060303007032640702da5203044003155180142e84240b00280115607010040650400d9020040d802d00e00c40704840713003801440e21020b808a00350600000110890b0b0260400641004118004941e40c2c4c4c0001901c01c08030300f1880c0165140c00910005a42440b179900040c903900000c400094080320110b040d1080ba4000d01c1038812008844502040342e00c0340b02c0c20280810800c00c030900c46828141e01c5140d1104404c1a028078000082d00000c0f15908404070603001500005820b03c03400c0700c60f005000e0380300e8050400c2d1040c0d0902000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 444344604 1250 444343354 444343357
    0x12260105010c02040b1f0e0102010207110108090a0506190b030a0c05090a060317031006180e0a0f09050c01020c01020a02010c0b0601020c10080f1608180f070602070e0c0708 76
    0x199034100300b07080c0c1c0070b41d05560780d59003c4003925400800341008402d48a07042d1010300307a070521040104242c8500c83d2140d50043c0203c07500c0c0c540c0600c1030003040b4281001900c03082c8010b014420240304124242002550421002c0d0141449556903014100d080c0b5403c41030360113100303640d03020750824060000025240f0038544241ea904688030b02e01341da80c1038440c2000b00503030790000c1d01300c40d01150459044030101005500030b404004241c1d40580e140d40007030320b00b85404c01c0711540c0ca072141c0e00c1c2000f0480d0f0121500c0e800c642c45500116500ca0500c3c00c4509031800705a068030a82c020302034451540da010880b61020b06400c3c0090040e200880d000a016890019000b60000845d900000c0c401e82c428003002d45407442c010404502c1c0c40110030001c01c07424086494030688000e6001182d244125140964080052659040c10a030b0300c03072800030b80304010b40e859606184101c0040382d040400074400403000e07141c2540104042c614000040501110180c0354208480041051101180c000030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 444345854 1250 444344604 444344609
    0x1517032a03031e13080307030c031808040e10030807320c030706031e0b030109050d1107060203282a0b0a05090307080c031315020c0102060f01060c1509122601 70
    0x2340021141118881540503000c0d100044003040c02110343c072010407040e40d024000b600c000c8240c14469035600c500d031041c0032307006000181070365406101d8080010030702c903d41c0ca42d01c0c0e501217200915682113000394400415821020205410090341e0f148182800c000600c01800345290070301c0505001c11140d20801c02c030104400d5801e8450081d40a540c4007500300e19883c96104089030064107101100814800c868080030255000b080000a401031000054a9107589180107031005c1021542c103d802001c903402008040c04003000c502d10b01801e030818100b0709084201d04070094007410f80303403014643c04028410603440707103040305100d44404008159680300e5480704002d40d48a103220502c40c5507010b0822414500790aa41c0d001c181c040f00f1004c041c01400c850f400f1501c4100c101801640c03140021500d031980305000000400201d44a91130000c000ca000b004400d0085c21001d4514054560400e800d5480d88690221a4110342d8040c050310f00300d9031904102c024070782c60009244080201031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 444347104 1250 444345854 444345857
    0x301020a050d141b0d091208160507030503060f030a1202102007060507050c070807540914070b0a080a0506060408101517032a03031e13080307 63
    0x8603c2500540c0c1a501c0301e1501ba0f041444078115110f00f203001000395000b1100400b00340b1115038030180b99405203013501c2549a05840d400e082d962100240042d00c1c920a00c6e03030b68140315a02c210400b06d2620070a070f50544107594080c040c071180c00009d503004e8400d40029004e61106500502d04003100300400e4a0b009a4840d0b03000c1030907142d00d1801c864500801c4a490000d014120000845100000d000400c8500c01c40c2c031142c404c018245054240b190304025096460310004070000303c1c0c5c1e6044124805051a5a8002002004a0180300407a541042e0840b4101c00e0b0302040380e10075608114950040c011460058a4600f000e50010a00d00c13001c0c120030f00b01904c500101e0015502c030f00a490250007458111803808102d1a060360241c00104450403211141c07104c04503c0034090280302220140c1400118a0001c907216102c41002c84640584041c8500b10100c0030729403020300056014980010180c00807000c12400c000d0700d403201405045401c0f14940c2c0980008015200b5070b13511608a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 444348354 1250 444347104 444347107
    0x9010e0906040902100c03170f06010c02131d0705030a0f030c02030733030221041a0103051006080a1101030e1f020c060108070509010b030c090301020a050d141b 71
    0x1d00010074007824035080d009600411208100c0c040f258804054140315000350f50b10050221002003132111050181da405410400320300c001901ca5000e10082c1c01c0c111710240c0707804031701461158540100c0304079055010044140304600b00d0080000c00402d80681400c80c050400d24141c0e54a9400c0c02c981c0d03071402428800900748138015554280480c8000b085401800304004440c980c00b42420140c943e40041e2600401d14a044d42500c248251844c800c880003658560071107032807020342105001030040318000e000c2102c00c4c10302c04015452500844c407940007007030f5000300c40c2c1940c0143e80c040e820060b40c0da8040c0501d0404215122082c02c0c0c5401c083c00c0004203820201030247c10401c0c42e000305260300c85016452900b5100940c002e15003410090195001030340c842501039190081446440c0d4040f00041c014403144c6425070095400c5944403607400e140128a4022a09907000300c0c200e6404900301050001180340d0a02401401c0c0755600d11a030000d1610032141541a102d08460341d0501e41c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 444349604 1250 444348354 444348361
    0x721051e0405130222050f1207050607110112050f0a0b0d060c020d090e090a030f0203130f03021503040f03030b0f04051003020a0f0803090103051b0d06061409010e09 73
    0x1044401c55014200140044900e0b40d0305041e40c1010303500c0085c85001066801e44012800e04000e000034040d076038021304000e000348002080042106400050080724010703c6000102030b622213004200e244d1085c00c00ca90b403690180e001506031030501915490550401d0200251400d00c03880446d440390039038a00090309a05100410098104541c0c0201054a03080e4015030681d0005070000100c100c590b0f54031081a00d03200c001c868001c0c00e03200ea10007a40040d1041c4000b900581ca000b034082c51510460b807c0c11411804e00740c46140c6d80d80441c0c2261907040080c000d5040c400d604001c07141d0aa80030610314103099440344242d040306203003d800c040c0e0f201d400320300550381e00010710184400148140047c1c2807440204581002902c0224401c041d00d50001540d2000340c6803100c1110324480103581058042c0006502402c0f0080410050451207000030000300e00f5035008d03220300305c600440012a42d08041020309a00700000425190b24414442980b441c0c3e402484540c00300020f85080e080c2e80c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 444350854 1250 444349604 444349657
    0x8010f1e0503100504050c0a080c0f1c211d0904020a270b0d05030316050403120e0307050402040825080307030c1203180305090312030c072105 63
    0xc0103802070340e414003541092000701e22040c1c0000340114065400c0e106142d00780410407800114a20410388260841d142c8284540390180401d03000210281200282c008049040c40c1310b1500d030041100e40b20350403581584150740140815038200c1841c24502035409a0f0714800105041030101c151103403180342c1c001402c6482c2c4051200040c10700b03040351404014082030380c0007500302000d40c10540c98585164401036151401e40c4845071034016014502d50789032401006001e00010b07080c03106104007000000005003d80100e190314599640d98844c1100102d020035007811440d50003e44114014001889035600c013181c0050710b24103c407021100c01042c0b414060340741405c0d0703202d0b680500000c550b82c0b081c190400010249103100703d00895400144c0703c0241c01302c9886280f40491078604900c00c2c40060b00030300042c2182540182141c1001441c0303c40380c00309500444004a1914002c242c8804025908a2860f03030500b282d0014a0300c0c803109600100180520220096150600030030301c07541e00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 444352104 1250 444350854 444350909
    0x60d0f11040e070e0c04050d0b0a0e2d06040206030a0c0c0204020705010b0a06051207030c05070c080c0102191106131707170f1c1716020d08010f 64
    0x100080d1040c000401c1c003102d020f0301c0383c620344510311444c840400014150443c4504440542c0c5006000c03250303108181d2034030b0490070002881641d800b0381c4d40d500120110010008104a0303415010884100c0d4500004004400b481300c01c1111700354800400c0c0300040c1c1d50315050b607a2044070000002591170a00d0001c40d200407410034080c0d0014800500b40c4284081074102c0740c1100010fa030301414040ea148401c640622070010907462030b00ca20030100b010305100c0d41244800350403500c6c1590600c403003900c800900c14401d50043ca450351107450b88100c00c3d40c05100d9180709010b1281c0720340280d0095210708510441001c09544640000241c0031040e800701c82440d0060200d054480302102c07618680c050391164070b400380e401410788031105000e00300d40010300212032424480192408511084c80c0080c00c002c6100001e0074416140e40c03460a64031004038075403050846216010201c1251403000c4d0404d00301d0805030041018030703030050090306100308c1c2c0001268084c2a900341c40050704801c0c031120307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 444353354 1250 444352104 444352133
    0x409080403080301060813050a06022b09050601081b1011060705092110090606080f010207060e0303070206421005090120010e060408030f090105060d0f 67
    0x220a0218000c01402084000f541c140c41c82621102c2070758680600181d5140d03080c10000700180d0040d10114002001d0b45c02401d002d40c02d21550454120f6985c20030b07890482c1820408145135a181d00040038488108102d500400444020740035141c40c0d10049911234118040481c0185000d100261910344628031880440c0c10350b106407400f600305180001e000740c1c00407104903c60701140c44070503407008c00c8084d04200c242c218001040c44001140f4001e024201d1510300b56181551020002240c0905001042015824600059031130100b468080201c4181c00c0312191254003d05c1046042c6400084443d0002d0580400c81561012a4856000d00d0044100054030110540300f01000e62204504034400d03138021600441000d0001404640c0c900660a042c1c0c0004c1c000303049058a06104040300150183e2400080380001210b000c09240000035102190b000800008101c1e5410b1a081c680341c00c0188a07000740014148400010100c0d92603101c0030300382c1102140d031201086180c0401450 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 444354604 1250 444353354 444353363
    0xf0102070507080c09130b13060c030e15010302030a0f0609060c0305011715011403152a0a05030c031e01030803010504060603021c021b16210f020603060409 69
    0x550302041d00d040e41d00d480142c41044002e225010450a603440c0500c03c542c8111039400003120f0003511a200c4120721907002c1d0503403182280c81d109250124400e40101d80458101d07460105445001440440c6401c1e42c403021040c400c9428070040c070050740c0115840055907040700810400071000d0824400800544c0d8000f003656180c0703540380341d98070340540019040320032030600c0c0c00341d02440c480c0d01602c0318a90000e05c45d00d010188014041c008110b02c2c2209011401b4003180c0c80c0001411174229401c00070354001350b010681300c201418924200480c80c2c059664564001d041003000c0c4c030007030700c1400301078200350480d0b4000c40040c1c0800c1d1500c0007900c490b0706001255a040d40e41c0c0c202288039510030701925000e01d0601201040b80b6021340200c0d41e00f500d4410b0b0012003212180c80e594000c0d0000ca410164a00385010308104100d81045880d5650748400400645685044041d030410b41c0003268045035210b1703203022500401c0440e525054003130b0301526901d0b640d94803100080c0003801c92020042c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 444355854 1250 444354604 444354607
    0x402063004060b0f01020f100e0c0901080105011a13090525080103060b0315010e04021f02070815090607030905100e010f0b030a0f080f450a14030f0102 67
    0x30600105401c0a40e4079002503603444c4101201900481e03d85400e000d00f02c0382ca41c40003400146003c0142d11060311041250b0680381d81e220510000b5035640003e80c04014a070391500c00500c8406110b00b00c20012000c1c40700c1d6203162014458202d4600c1c80c1900ca958400c03665030000469800412546001c0850b50f00d4940c09110184200a000000300b03000560303c061a203200e0103a2408c1c0001c1000307050b8500d2500a10f00d80c88c101020700c0038030b00140100d030030440c1c0703810100014400401001480c5243e40142c0515403c00324643d1500a10300c505a009102503424040150404518150001303414500815007804d1402d2403481c1c401140d80b1a5401d6192000414048d007040d03109020a2595400c107000300c008000825950342180034020f0b01c000c0400644000140c0640002c0ca40303212101609420304a40106020166900341081c000341600210044d00450800038404100c080c08060800c2d270458180218900f058240204030195030003180042c0c036950208043c00f00c0300d2a40c00250b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 444357104 1250 444355854 444355861
    0x905100b0403050a05100513060207060e15151e10030b0603010902040609120305040e04141204060818060112032a0506070e010507060504030e0904050714060304020630 74
    0x41d6591042030742602c1c1405600216925046d41e401545e000300c8c102c0c3d1030348000554644500c0001d40c8049000c5038034641e9140031502420b0f0521031901c0841300b601241c00c40703141c42804800d24240b2010071505c0740d060110114001103804c10310426409060360f0019075804200c10660080c40807482d034550004000c000040d50000c0c680080c02583c0f155900c0d810426a100c004070740408912100070041901800103100c110040100c0c1c941c840c2c0900045500f10082010140c1056001c208405007030000260a00c40550080c04c030a8101a6200c0c3c4c1040310080415000e131940e2040c0584594540309d17040c420306040c480c400d240ba441961418008403a84404044800d1810700700048030240691000030b0074281c00340c503441d4502c03c03060b15a145801074a60b5954003d00c80180201c051140d40c4003891203d441d04085184039a1080e002000d04a003004019094403243c0c00c15940f0440c5d0070810880146c0b18441501c001d0012440d0740c41030750300c0411402c01001ca08123900700c00340c01000c081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 444358354 1250 444357104 444357113
    0x2511030d05090708120c1b222c15190e0601051c0f060b0409200102010e0a0c15091203020c090f07080f19110304020406050904020a0905100b0403 64
    0x4507411544103204441101c0f03102d200e107440c82c0c065514141c40d1900000ca0341a400303c6c0460503085145001001e01030800c00c12240d0701c005400c0003c1c2c0d188201c0d0380310040200062000068280e0024004103e41d2807885061442d55603014004e10424ac4c2e000b410114264001c0c442840c20762800300a001e20840081e1612a60754180911400b40301d04411034100c54405007105440100b160842d02c8010550066120003002d490114060780d00a0343c1c1c0c5240700b0214842d004103584a8500700201280b42a4200009007134402d0288072940582001882c1d02c0010010000842200c070801c8c01c1035980d000c013100c10341d20110719074010344a0180b0004040d040503804119850341322070449034007035107403a0803c245500341750840c4da99001c10783c1d860204405840115595600ca06200d04130460f03034075040480c5003036078440014800c6414000c802d0100310f1400d40a44c4028100548801c061880c040e0000b50000000d403049103081a55400801c4400006078104005840f951803a103560340d549140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 444359604 1250 444358354 444358363
    0x30f070303170618010909110a030317060a0f0311031507020f010e2a130c0509040501090c0509010c0f23100504050c010e01050702090901090302062511030d0509 71
    0x35410240321803030006019450103c640c1d0710b034141030040ca103009a00701110600245480501a600c8e1607030300360301e412140d403507040207005140310b07541e210b5140003800c102517600d21004d4980352080c10907070b40a022810401408a0407250051442c0a000e4904008682400000040f64140310204c0c402c0240031500003540c01000104000200070000c2401c0c88582c0711007804001d800c21a500128220842800b403120040c3c8101c0102548440795109143c00304a4044100e00720200d6000f02e000d007102e181c40c0c0700b20342c014284203a06202858860f50010310034802c41701414180300c0d084181400b403168075000c0c80030040d8020041c114070a039442d88000c10107284082c0243d64404c02c10002c44028890094500403644a4004c1104e4004c010055400f400381400342410010244481e1000d030380e03400b074824010281c46000240700c80c01d0f810002c0c01d2030700051070410180d0280e026091070440c035818800048565103031103003a0103248035a903800d41c071854901c41e8116003000c044c000c00d1000401e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 444360854 1250 444359604 444359627
    0x1404030c03021b01020d05070318081e1f1d0303040501020304020913120f021f1a010810180b0402030a0614010c020d15090c0b0d0c03020c030a0c02030f070303 70
    0x400716220014650b00c84210441142c6003c0d005030400844401110f004102400c6000d11030700b440a00590601802c60300c0750011750080c4251361280b02d00403006040d9203c03004410f680c507801390590034005444180c04c61040d040c0008080e40d203e04030109d40e418401f44000c02101c0c0b1098a42d60b00f45402c01034003030340090760240c1c41008580042455007034214241c1e0401d0758080307500e40090b400c0000070b603090304d41d6540000030341c02001c500100d550680020209030124103000041c2c603c2d01d8410180c0e002d882901d035581401070b0b44e0144051451007204e200103e8403d01742006181c2c044400c5180540001d8000b590085c0c004018008140f00d180c0081c01a600506020007903000c0e0080110f078000040744029405c9010702d1800008500d00c2400806416003507000482c07019042c2c3c1e1449007601c800d90180300c0403040402d80c000240c85c1c1d8004e20700c0300111031405504101100130000c1e00c920400c030001d000d010044c690310085403802d1160a051424070000c0e110f0b52540e0f030402802145500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 444362104 1250 444360854 444360857
    0x20a0212061f06020d1d12060406051006050d1107121d0102011a0904060905030a02060907090902150a02070b040b1308030a020303071d0904060c081003050c0d0201031404030c03 78
    0x740b40502c41c107118004a5000c8a035154010180f61800300010303282420611a100c0b85a01201d544400c00e44a4800400c03075440e40400401503843c090410400702d450107070404120004229041280980c40410394840c0c100034200040c901c5610240c1d43d1092007801c2006080785094154402600d8014042c2e117403103a041c400604880121000490803600c481440454482d45114107007000e091001741c8640c032601c1801e00158984042c0c464a16640110a08200580c000c100f0020b00306400e1041500928618005101050b255800a40000074920710f001520602092103103401e44200a00e2004158200603555500e44410b441c100e03a901c45099649180d1001d00001060320f400411240c03600241e50107903045858005040b00e00d0145080240842ea191081010540c2d070381c111058081d41c820800015601a19640031f8203a040c000d10844503c0064001000480d8004c45e020440c0081151003582c00c130158030050340101030582030b154038064104100420550080d5510544a01a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 444363354 1250 444362104 444362131
    0x31207110f010b03060106030f110c0f0706020a0b06090c090405010603021801022a0321090a06051e03060102030c0a0f0302061308180402300717060f01020a021206 72
    0x762a030509079040040e003d40c05520038001000b801d07100382e00180c000d91a07100c0100710303400b8901c1b152500350005c0013004082e070410b500ca4030340c800003044950700034080d0780054260740c0481d8a032400c3e10800105141c1c0600389200000e8039441c0010201c65408400410801603941c403090010000c0d000908102102203a0401110503580000f42c400146905488036040c90300c0040c036070400854110480d00d170075216003559500c00300d00840d038000d21411855551074849000d00c0411507050000d501143c01c0c094100082403c001c00d0048200409000708030540d5641c03100d4004034998480c0c503681c00118010b070b20450781005000d000882c60140682d08407031460326541010184c6000460380248801801c004142043d02d00300c0301c42900c80350050005040480c03601700000100c0514081515071201764034107403c03c0c2d2120304669040242c920340400c024003210004942d0281c0503100c07910508070314401542d20707031080140e072102c1580540420f01810340d04175525500c4905940c9241da0300d03d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 444364604 1250 444363354 444363373
    0x109150c09050607120e090f090c0d02102a0312050a0c05120a0b06041401120506010903060e1213090b01140301090f1d100e06060a1703120711 63
    0x30440800007550b400408040c07400c5113940e507418850b10400200c1040c8422003113070050300d5940c03115251003480000d845d4403107403409d00b00c0d00d800c04520510302446281c5805010b00543c6581c9142c031142189820a440603812241c0c4584c201c200d8144010400c0a00d81c0c4082e00b0954000300b20a2902d0603001d042c07100342ca0f40e11600003a00d016545a6000070402d00c4408090308010762840e4000e103c0c1c08000410b048450085496503200d500545c4256801011070005942d104a501d1745004041d1010041400e00e00002868001c041c80080c0900b500d84a03501100c000a00880c001c0019025846964112403000030122030454030485441503d44030301c4035840d50082401240c4070f42c60783d03110343c5141c4c00c041500000b00f030020480d0740341c01d50707420185480e400e098040c8285c05e04104000d22a4148239000402524048509410290000c0341070100c103807542c503100e2080d11791801051500100e041241440c6014028291403a00309280c05d000c019500032800c002001d042409440b101d60 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 444365854 1250 444364604 444364607
    0x706050603071703130f060e0613080601030c140f010909090602041d0105010f051317012c070f291908100510080a150503060108010b04051b030610030b030109150c 72
    0x25a881f03880d0202c1e80303108048115103000002041032080541000055507110b2810700d01c1e00000743c02c122602c0f00700000c1817001c1500c1e130701015405c42044030042b02c0419400002040a58284114001541c0310b00d007140400001c0c7c0c0584026000d01c4185d510051000c01540100c10028852a4007245000031802241c500c01d108984582c0703005c04151030303d00d2411755100607502d0341c0046001d095688181c1200c108a5800314000c240c500c200340a10007844111b000c1d410084180d12480490545002c01c000c4149441d410070306000c21081e401031031002c80c01480c4402e101d04e00b01c071020001c400d41101049a00510106e005102c28032441580c26118014425800c01c082901ca0200b4800d07800208008410f800c401122201242d145e09800c0da1003011a01e044000e030800c84c0d1507515034407041102c0c01e240c41480d41c81500c01c0325036403402c103d101c40e20b0143d20000c1c0016019580f4850f40004c858000c0d00b0806601601074020800ca40f03190400144010045c00d00d10710840c140a003418131079 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 444367104 1250 444365854 444365879
    0x3130b010503060f060105070c03290a0c1b02062104170c0318150703031a0409080712030b09010e0f070e0a120f0606060908070e0705070605060307170313 68
    0x10504801d20b4446902c440005480c48e07044480304407000f103440e10010000a02e480d02004000190020309100605910354040003030100a1805040c9480c103210522150345c42550304ad42e0410040d50600b5500c03160002c00c2d001d02c40c1c50707070400106440c030b03c01070f070680c1414580c2172080e40180e0340103148112000b212661480741601408240e401404080c6400c0e2030074400341015a0018440d07080242c0503c40c041140d0400c00003640404c0d520598000e5440850005c110f00780003c41d400c021140b03069840221038007074602c003d0503250075089080642c074003c0e800680e540c0720040240c1c5041d80c0d507005001101104880c0349002d207800704003080002e030240307003e0305c1c40000c000c0c0700c00605410403010302c41d5016924002e4410024000c0c500c8081f44440c85484080d2101d9558103108a0400d41d07564504402944070400a60001c402c01c203c840d8844240c45001c3d0f4458030201e41516007000007468003800d904030842071600c40600c0c101401c000070007071180c0011070000c0c2c10703459039501e940c1c3e00700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 444368354 1250 444367104 444367111
    0xc0601080d08150d05060901020a03050f040f080a03061809030215010312030e1207050c0109080d020607031e050f0709080a080313050a0b07020607111c030f09020603130b01050306 79
    0x205048a0102d00150407034039401e103603c04042c001d006003c0700f0b07485280c41c0c11025141072209960002c2c3d0300c164540d241c003410760f20001907121080541455607842c2c00c02d2107900d81c0500185000304101c0419031194001c50020f080c116192614004a1074a80005060261007100544516030400030241407664040b41241d421110b01080c80f00041d8040e0003030101d000d41e90046006000026541d956410003030644240100010004171001900241c100c9010fa0031690385503000401070135020790300203086a0f02008516010400780c605040c120003c04498000c062440d05080070001e050000b120068440d0010f0f9856000060703540c04100d454403010240500900700400024a001d0000b444d880d9550340725000b1128115483d455102c8520800c4d9062001608440144440b03c0da0103c213800b008000e110141881c08005a20840305000c1c03292400d0a05031582c0e41a01a21032660228070416009008640d6030b190036180d944d503e5000e2001101e5283c01d203400441c0ca400c000407014031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 444369604 1250 444368354 444368357
    0xa050303161d1f020304050a0803042d05221d010b27041a04030f02010b060c0c130f0212060321030a05060a0f06030203040209150312030a020f0f0c0601080d 69
    0x2150440043c1d2550304019541412007980700c20400002d00380c4aa00380341c4c0050001802070358440b41482c0104e504090300b00c1c1c0070b01001e0006540c55147c3d185e003061040c12100115003d4036900450059000c43c01001070340c850810b8a01103a01038400e568030010702d1100c40e004020024441c1480400900030070801846000c102400c1b405216140e0030fa4040e03070054041d00e40ea10010151820851440001322001c0340040d00340d0704035441d840c0d0240100ca0b4220000c840c40703400c044002c48805d82e1045480c034407034452440d45007001600c00300313580414000910751a0a5688425a0803c0d0b41d10361401e440b082e000348a038201c0103286d204403c41034070300700c490070f400350349103844080c0c19802414001d000b071940007041c5100020039121580441c0001c10301510096201d24043c01040000d01d4010950700c0c0c3c90240042c90203091f80e0105660900c0000c00440076280e40303401952070028025083c43c14200031001440e000c4c022a05005030001c88000421101c443e030302c58070180c1d26900207011410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 444370854 1250 444369604 444369619
    0x7110601060f1b240506010302070809090a140a0605031c0203030705030403090f0f170604050d0302160c14150c120705010b0d0c090c05090d140a050303161d 69
    0x502d072144001c400c0490450b091400b81c25000d071074641184005602280c0600c3e803007040340c00442400d0080c10b52045003400e00314103221440d20340c40740764490b03c0100d602c541c1e4550006800780841d64441408958450b40103a5540382c0b02103414001d11483c007039140b1910a000c14905001d41d580001111940d4940c0a1825a15210360546540e0800780046040c82610b8401040c05618050f07010000c143c0010000e48a0346400052214650701010310b03010391f005281000040f600006000460f003450380740c010b0755043d025803201290825140024081c0c260320000003a800c49034064105a230b0b008882e001070700e0b520444003900501c01c07910b9200072900301c2c15075609011911009010414020070011417444540c00010b914010b01d0001101c2942980344140105242c600c24580701540300d082003440c0c2003912002030100c2d10190401130030303082400f10308441d116040c1b0030100d804d940442100e841e0f041400042042d400308900303040024140b0340c0340f803592640c6072900440c0890064001c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 444372104 1250 444370854 444370877
    0x18040206070609020a0b0c07050a140a03030815040f020a020f0a030e2e020a0309090b01050f1605061302181306051b0d02180103090818040603060509060711060106 72
    0xb80098a83d402c4180c0c0e000110900000b0520200402003150580b031801a008590030102006032055440d081503100c00d800744540140d5455140c085004c0d01c1d01410810f405984450b60034500350100a0426001414101c0760003280c2c42540250100f180c564081d16280d20340740009564900c0f100740054005002414201c103541403031a420002526412502c00d51070382001103144056220841000050384807101203024035500130a01005480102020b006d003030001000240a40140210140381210005010590302c61410340c60441c5070740101500c5481c50090004c80e440b00c160310090340030302c8080a0710902030501d0801e0390312a400084404aa00691791912070050a008006c603040015107056014000201c41c003400c84084030007005640c404211105040b420390407901541851308020342503000401c04402d48403a00606402141e00c11180400200541295403001d862180750204ac088450004030700c551040c15151140c040304601c40400c41d0fa203c1d000d200f1040001e80c0ca5414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 444373354 1250 444372104 444372113
    0x25020a090905160608090f03031e090f070b1206040c08010b130f12060f050705041e0918140c060901050c010e0f061906030201050901030507180902091804020607 71
    0x52810745004500302ca0041d241000a844641c035250850404200030108020603507808112142202542c40051402c0d42000c40d019454404070945602c18001003200241011408104545400646804513200d840d502e10030001c190b4061806da00342100400c00242d0941014083c1c0c102c081295a19002c03107030710708032110400d900032072002c100b07802c0b929074005410100500b08a02070007404a4402d0b000c0d00b2403034960b0441348014000034269052204100b11590002c05640840301400200b40841946908050a03580d4a8114400345803070030140d5124000c0080c00c10040a00c00d001d0004500228050719a8031000d424203030381c5c050400c011003e855403040015150758101d41001064800511680a04204041d0a4589140d20403000c006d003080b40c0c0d54400e0722280240700100301250554000924901c82c800d15903051648401c0450700b0188110840c425221b0b5800b0609509a10380ea0084042d5114150f0703680b050194000004018003c1c100140c0282c0c0e00600c40d0345448000e985 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 444374604 1250 444373354 444373361
    0x260118060f15080d030b0a080d0e0303040b120114010206100513090804120c0f0f0b031b0304060902101b0b0603010908031e0c040501230903030703020325020a09 71
    0x41d8844540d48541240d05400740c240000d03000303014450b029181c41a54600010203c0340064499803003110028400c0019000208010990b112645044135405081c1c03c0824a0740c0714651080404e145c0000b4010128155180c00c46e0503981040941d8001c194590012030f40d811040e0341c143c11101c40c510003000a490b2400300700c4640400c1035030108924200b500c445e10150000d50140049801540604080019a0080801500e03c0c04081030f000c0f400c080002c40c18401d513001d80403001c00b0000c0414813407903200d81c1c11600c41d0886121507075280340900d0a90041c00040100300d000700d101680c0340e05440c1c06100712200c06418014a44c103080d1503a10740c0a590103000d00450341655a541142012910b03403001184181d040c1e00001d10403c800801e40c451542c0000c0402c403040c44e05010500440e030340615078001800c0c00c0d04030500c0090640c81900b0480c41005016685440000303018405c051700407020708400c46c41e4018007000c1c1200300351000f000380e1150f20002e40c005000403007442040c800f5032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 444375854 1250 444374604 444374621
    0x30e010c0803190608011e110406050a0e040b0a03110a08010b0d031d03030406080f060321030a0b1f020738120408030105090a1b110a080426011806 65
    0x20004220917581c0ca0400b82140d010490004c0051140c0c400058108514010703a07903030040302441c892a041c90f11000504d42c1c00340683c0642007002c81c01c010759065071142c101c040034000080c81603184598a01e4040c0e0f060303900880031400381d42c5192000822402c10b114180143c44098401d079258010381e681210107102680440380c840d0041100c0d003540752001c0002c4c101500340744e1a0b0110a0801020743d0f0803880d0010510740c420782c807206030f001d943c400c1c540c098208098403a08094890f140c05100c40007516210031443d40025042244206024440c040400c00200c01e4080e00c15080d01c800880042008030908240c90f01c00c4840e1021006403500c000302d040f01c0b500000c2500307044040b01d4240c806403040c0e0701624070b11000300c0103100c0d51800000c519040544068108034148034440c2040e4070803c2d40102c503041c000704401070581c8803c01d01c4034109481d48058860356440d260310307110203240741212443d00544109450610880814492009041c09000c1030700c050707012991f0359001030400074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 444377104 1250 444375854 444375901
    0x603060604151502030c0102180117010f03080711090406021c141b1308030d051e040602090a081002070318081209060d090506070206060a051318150504030e010c0803 73
    0x8000c6c40562281c02e1010300155079001c840da6404000e44e4000600c240d40499107070b88004400001044810010b0307400400b1071380d001c0e0b04141ca5003514208910b00041044030103400940c9942000204580e0f076000700710780203642280240c0240c6078100d4004448000c0c55a0004142031004240940f000e201e4520412603540b00262624240c5032900c03000309000d600c01c854690001c11142816650740c01003d6112070008401042c03004110401c04003032002071710240041354001515211038640151440103801d85000b2504022101036500000b58000e5009138002402c260403c140903507440e00040403242514000c0100b0400345400506a03801412510381c0034804000c81c80b42d1101c58082c0328603030b80c002c00280003d440c20000203428036400802052044030050400d01c040c0d40d640c5024450742c8541d4100080702400340c07102c61905220400d016000500b02220442045180e800c89807156200f956640b03945c408000040d100101d10010060001c8828000030f8808400d0801600f06621507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 444378354 1250 444377104 444377107
    0x60904050619080a030f0f050d0c0e060f040801060e060117060103061502031903020319090c12050703030f050f030f040309030c090f06050f0306010b03070504030c0905060306060415150203 83
    0x52040c02000e200140d8032070a000c1c0c00011181c02130640059181083c0b82480c186084140307c842070091007446140391180c180e03031380c07941a13076441740c80340e0025100300c203014000b1070341d40240034000c0c61240c006100703624403507080481c0131840c19540301c0c2d014014001a107032000c4441c01c403c0c61890b1500b004042a04040d07403075000040308202840010300507a0b00ea0051541c8900c160011280c0c0320349910601c051600410500c48a11545c074a11035030500b80040000304a0054600880a941581d1040400c00c1c0d0b9051f1400c2880004989034040305c2c46074990b006010640581505c070b038051006d50307209414060001829a0241102c000da0181c46032515011954403644d5010f401d10180e0055080f0940d2102c1d8100380b0704452190780b018000c1203034840074194007000000d6803100d05005420030b0705400301c08103034101e01034401d0b5000741d6032000003071030b41c00c0d221404030300184400c44019100b032040c1c2010603002c1c24240b003038113040402a241e04400506288441010503403100301c803002c5110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 444379604 1250 444378354 444378379
    0xb061305120f072301030c02070b07060615090815040f060c0c20010f0806060f0903190302060f13050606101202030907140102061603050c0412051005090c0609040506 73
    0x4040c061078001c0c041c3c00c400e0994059100d58001c000030110404c2a040c0351510001004443d00010034108541c0214a103655500c0146003203805000309510460010400710000d1200781e0300010940c00740c40e20002201c0c011541e80c1d03080380c003005094030040c1145550003062800300d551038003c6100413580c0e04089100c5401669030560032501203e00e054817041700c6650340099a40050030302c80070744c100c2c9001040d50a00f600041d00512031084da5495107100024400f49a0702c0520000800d4402c03c0d110741030018450a01035140c140456403119846654070007e001c20381c1e09030104010607000802408580c0c8c4060900c50b5040d400f924020074080d2071864400c0d42c2c5130714001544079018580c0604134051401e40001402d66402c200c4a055401100801011002c91809010743c040b852a0100c2d064951482c0a1040c0c421500112400c0080f00c5000d018000005900f90401d110614100460365848004680314900c2d00d00d11031b07010fa006c00062000d490a0f403c025008440141415503554 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 444380854 1250 444379604 444379633
    0x1902010c03091e03050d022e140403030903090b04120f02030c120a0506090c1305060d0606080102030f0601092108040e070c0b100f03080309070b0d0207060b06130512 73
    0x3200103040f00100c0d030324400e104111041c4091000101c480c0000c0000741d5035200840302428418601c0401080c400c40e611444044680140307400b03c102c42849082800c1a04000b03010380001d11081c2e01042c0002c02c002143c08250044a040320100340441084911668130154000d40c0745900766030502c00c3c800a036415039100c41002562030390340d2005000c0701d61540781c07980c1000c1c070040c0105241d81054011485640380c41d500c648610406040018240c1c2da01c20000d80542c00051002d0002450860041601c040540c011030080c102c1304103400c0d0030381e81c00e40115003183c200d008480e520480815806145500b258120090500c9281d419041948030000103480c00d1045600b0000150b8580c0c145050013071224006403c03621b00c841d13641d41d5500f08000d86850101511000300b11420000001d404e50768240f11a40240c50039200031a507c00309010144042d4000c10415941c691804d00410300901d00041155a41c0d0107049080d03411a19150810040c41090b218030802c1d8000c4225142d1640c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 444382104 1250 444380854 444380879
    0x6050705010f0c0504170705010e09090f06130201170702031c02190503010e010614071e02042a0518040504030909020304061505040c2705030a050705121902010c0309 73
    0xf4045a50f0180c80f06e01d840e151502c1e1102281611645030011001480566804003180005c0c10741910311801c191074010359a4905158005544818052001070103079a00d20840e1100c2060300036030300c81302c1401c80101050307003604003a9000710250703004200d0001d4451121907180b4050074548401403c3c88500102031448011131a00c1500155001006100388141402c1080c003502552030100404800300f01c0c0200b481c401c00c2401750048501c07c0c1100c9044400e1802d10400b1a0b01800510480740581d8043c00c00d500d82c400203154041c0654258080184580c0903a40000e0a000648281d49040410300000b8040a8020b4080142140020903100000d000031800f03107102e21000540d002c042291034072200c041c1d8001b98400d81c1443e054140c1140d004481810f5035580c0c1060700b10241c4003228501a00f61154807054041c060300a01034240140807130400210b40b01998003c0c2c941ca0b080300199210070400b1f1012661021400254025520800800c107a1501c00d00780481d0305a18cc014420b202c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 444383354 1250 444382104 444382121
    0xe070308070f0605090a0503090118031b210203060a09031407030905031006030803150105090301090b011a042414120702010b04020c03040b1303081218070605030106050705010f 78
    0x684600c10702d0b0100070701c600c6096071100c60300c3d0242410010a5465903261f08c100c000c41c904202c1e0b401503a117803c099210744000150391001d40811010454050048020b98038820800d080703903420100034402d801c1d966501002d56000b8090590766903000084401010558020703410041c0f11021121604078410062108900a440315800d0602c0d28040510b0440168802070101d410301c20b0070400944000d0030b898000c410121a0715407862a5001215140a04080e00d40d00d5801d1521400c1480f4061200701d050b20849108418034002041021009114600c2110070104030707109203a112801046802c1c025140700d107407582c5070104076640711106800100414500c01030b401d0034010b546409128003060000d0a031003d500344081c16a11588074007481c456080300060004008181c544400c9001c40915030102c60b003074035007504120041000700c04450511091a500181d8580d24800081c3c0c401121515902c0c0340c0f82d81c2c00d061080380c6070303003110b03400325015900e605504800c48800d000e242e05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 444384604 1250 444383354 444383363
    0x70206010807080a080d0b03010902150928172a091312110c040504050d14030f04031b020d05030d0c030509030306040c020f0a03050d0507021c030e07030807 69
    0x16505103085142414100e0744030043e9a482204c10704c00003195441500e12410781d40400007600345001012a001d4042040c1c02503001d03250071250714000c4d00500252080c0401035030f4841112200c4100c90f002031300303000122460031409880400c0160402104c415017108200142d80744c00301d0b50040d240c2c07044440807038865900308601d055907032410a01480c55102c60760b2070207084551540c0d21440320041182c462181004000045e445a01d01e04002c940b144440c0504100400e2070903041c0942c540360703c1c1090000240c04405003030004144601a6401445c25541e101c0040d11030b03681c1a03c4450030204010010041e160301e500151b55003c02005804c2e003e040a50b03a55840320080314101c4c1c7c0f410381c1645c14145010300b4040b2070f100000c144c0c0c0c0c3c4070b88182c030002100041c3d070005910342007c44640c460319104201c0c0800c00c05a014010b442300c8481c1c41402d0099032150f5000340d80b58003103294400c0c06880000b44000c55207110390021035011030f81a0540d0407441d103d031901405070380700203010740307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 444385854 1250 444384604 444384613
    0x1c0605040201140a080109150b040f0e09031c021c020d060e0a1413050111040f03120305061003050411030d08090c03010612260d0c02010b060f2a060702 67
    0x10541d6000012a0450b5410f81e810303924060002101070910313130041c0211200181c1c0e031640b6284040b128042d9201400c4030006041d2a543e40d451200e40c1c06800e8015074110300300e80b1000c6904400000142c8200c1c01c41400300000c40e00d41c211000000b07400401d00140d001c944d501c502c0040e814284014000140e9884010034100d040c03842d84200040040c1c0048105854140b40028807404080040d0b00140c07101c01d11300c07141460307041c018090581040e54480d07950000030005a45855007100c48112413181c440b00317034501055030007601210b208444481d04403d65101c10300500d4420345c8102d40c8144100304402c08000c00304003280c9401d08007032448002c50141d90512081840c01c0144000301c0e41c080f00203100584c249092280e620321520700003094502c00c400790a03543e800b54510300070117218a01d403107a229003103442c2c0035015100240401c4099440c020310403a06007401d1080316400919004103a00d0040b110b8012160301440c400c0480b825440c0c0a40c28000a07014070405008024035030040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 444387104 1250 444385854 444385861
    0x601020105060a050d0201050313020414090c01020106060537090e010e07020a140a0501090f0204050a1a01050a12110c0616020a03120b090903180f03070b07021c0605 73
    0xa800c403900944141d1080240311400c00030b954030380409000e550340c2840c1c00340e2207031281c89880103180c07081a402540311f401c050480040301816006c052003109400211030600c0c0312213005a0032a0365900a40000400410140002004180b6110002c83c110358103030241c22045070440303844604041201c4009001100d080144400080301e035405865546071520981c14601b1000c0e40c0c0d1400c0b440010300120034800e0303200440005018410580390010000c1c0280596031600d0580440754120880c41940b511000c1036240540d40309105503440183e0091924183c9a0015110358010b02481c00c100480d9080036008219103004004558002d000180e0316036100c446403a041040c02042200c0c001d10403203060080c02d500041012409415045c40d61a501e240e1880e000600000719081e9001300811782480208040003000380344454100500c513109898841c1000b0301c40041034180c6034103520000c0c007804240603150003040054030080001421f401c2c41d000c10035545d803c0701c0041d43c07500c2d81c803c1003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 444388354 1250 444387104 444387107
    0x9030703110a050f0603010909020a21170702090403080901020c0102130518100e04020a0b03070e010e0307030b0a0f140109020d2304060c110f0303040203070501050436060605030601 80
    0x2c10040d2204880703043e51019030b04085a1503000501c600038403151958515800c1d0340b1200340510142880019122014448048038480c43c604007504070f50080b00b8080c0e5210003d482e409503890350b40d0040004002e134503603440c00c4030b03c1140500000c806543c2008a0303000010244001c0029446410024445520305020843ca80843d0390110894940c0c80d010032419405841119050f180752208900c40f980712800820300505243d00b1200014000100f4410410380212600030701040c240ea441c16948400001c0c540c0360341052200400d101d8144002c0360101d0829008141400d018402c0003030074070100c0300e140d5a0003001380d000080040e400990a50448114003130440301c4111a00401c03842103502104103a40b8400600241510b0f6a4035002c0b11305c2d42c4120b03104000c41858000319a8008042001591240c0c02654100e100e403044101c001659402141964100c030380e0340f200c1d002c3c0c00746403140900d40514002520001412154600c2010740c0e514854400074000c150780e01501d91604800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 444389604 1250 444388354 444388369
    0x70209041e11031203190c0e0604080102090406090e070501110309031c0f0512070c110301050109060f081b10180f030b1b2502040e030304020a090b06071101050903070311 75
    0x1e04044c002001c0080080380d420406130758403c2da800060000e901403100b002101c0c0b19134104031031a4001c00000d4002824101500038042c0818119420006180c0d103c028004603001c00d18100499000103008002560140b800098951000d8003602d180000303c0c00003e040a00c002802e2103141c0c448084119100d6120491150790451424014688501c801c84151010b40041c4a181000301103000720703007080003000c0f00320f0741402c000d0001c7c4a02c0d40c6442442024002d03e016540d01e020000200045081000882c00b080200c41d0342000c580382c02c01010311029140b401d90310024418040110313504841141144001085070b0b0a85074003890451810032034003200902607035801d8044000356100c3d050400101d0b102c5d0000c0305a095010100b45006090f0440002da0280d4428a8800d0304081118044021403196100316044040789440300c1c012002c954052680780e4101109114800000d0350741c0880604008050404500b0041400006490a0400d40044074a000f003202c007005181010750 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 444390854 1250 444389604 444389623
    0xc16061d0607032009210102030105040c0207050f0111070330180501030e070f0306020c15010b0301090506010509130f0b0f0102030304120c02030a050601150302070206070209041e1103 81
    0x3d8107015a00c0701c40c02040700403649080c503143e09080000c50b03030b48581e501440750012443d071820501020b01d40c111a54000d420074400c90340124108161071554610100304030094072030041c140700d6034060350360044610007048066040c05115075000400420b40c64680030048141660030500c030520540030f4015104103840c40c62052101501c0701c850b00c1c0c44402900f80507901c0c00c2c40c0c000b40c20f04a85054524021071039210419500e80503901009004454004052248084007215681b4502003092070200b40709220b18030004e40180b006010b02400d54001907000041454224203250b001000141403940300600b1035056a502c280914002e880c0780644a020201100d02c0804d00980a002075264407004100410045400c0d903501d02c040d010b4542c0d0350340c40d034029046550202c4649440c65450b02c0a0003101e0102070b034007466240b030601c00d000b120892640600900e01700301c823070307424407000b64000b03041101ca40c4403400c03a5840d010300c400c2c081c0407080d004d08520000e101d110000d250a004a2a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 444392104 1250 444390854 444390857
    0x50a08090114030c0d1a0d050c030601080609100f110d09050c06030c0706091407060504061701050d020907230909010509060307050d03020a0510020a03180b0c16061d0607 75
    0xf0310421203040e4620040e5081d5401d841400302d074118640d0680a8049200e2a0182e80300d18082111320501100056001200100b43c0c1107403051390301c0d82000e0741d850000311180001513200300d0613804507180540040c8148000b13843d003c108140360310305082c1d2640009440c900c5460352000ca0354280501045a40f0f44804113560781480c44c24541400e03503ca00c501342c80544081d840b043d00400b00407104820b2400030001e4810f40329a41c0c1c6409008000b503115200d200002020009036200b08002c0d440050b04980300100700302010590b5034207000048500621401c14417540c0038880016983c04050700900c1c480390320480f50741c0c002660401600d1281a04034074041d801d0350b01002042d480015403002510340803035822000380102c1c58200c1c5044010b0304002c1150054500c01d20020449802409078405c0646051042025010a8000b03140d00c6000c0075000c8105200400c0950007070b04002c05071000754008042c42440d880d22000c0564030110083c503081c40d6480407650150740c050000700c1d00728030790303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 444393354 1250 444392104 444392107
    0x30d091505070f02030712030f1812031e03063221030c0a03080603030a02060403050f040503070b0904050c03040804150e041812020a150b0d050a08090114 68
    0x30046440366100d1404000c40a1040004001050140002079280b034254003c0491b41400d40340c10f09483d13905081300c8120042441e01d0002d04406003d1003404002c100c0700d54403080101e1400a42501488440b10190140510103032290200c1d00c2400c0d41043e581c0140e107010079413502c2d016500b0600e03040598010f4401c661003e0002905d17184001584410b107045030004003103801c1d014001440941c2550301c150512000034111f1038020b0200da4006054080c1d100c418043d030b2500241030300d0340720f4040c3d41001078105200080c0002d0040c0040c0c0303425110340101c0d40c2441e84941c0802d190050f10b41200700c90310781c08602c42c5c4040ca014010f142d880108000018210b003840ea0710000e01e03005900454609914090040301c01900c03a403140c02149d1001031050000660a1a0440c1110090041608d0703071800700150700ca060380002000c228a40c0d0000512405170a4504400c0c014400b07040d0355644503803094451004034038104007143c040e500500c4034554480100001414190302d001400c20710000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 444394604 1250 444393354 444393359
    0xc110709060f0902250b0f1e0604091e0825020a030f0503070605041202010b120a1118090f0c24070c0305030315040b0405040f0f0303110406030b030d09 67
    0x2600b12640c001c89985840c056183c450110005144007804d6000340d80031510400c0c11005d0101c0801c015000d68055503c4c162261501d88030300300c900f0320980744c3d80c0e66500c8400210742c2c0d03410203030f0180260301d0080e903029410500c06003902408c8030540100b80c0d580b01c400714150902650750020f4003c07500e90381011101c00103c55010a49119507488050019855440c02c0818072105004903451039500500c10042880c15181004200d0020a0503500640c80c18104600030f080c0b14080c28015141e500c014607000c621503494101c1643c1c0001615001030703000c80e04101000b132050440f4000c04a0302d02034015a095511081e04d002400315240d403003410341d1543c00c0c3c031007030301640c031200c800c4011681300b0307595042d60818110b2200036a10050051000204005514000604280314030074210303814014015924104400d80b10b007a14042d1003000c00440f6039000581e41e003200201648a420049004d03210003252034015003141d444a0040380e118160840c0600e030030302c41d6106130002403e00e07000160 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 444395854 1250 444394604 444394619
    0x50d030e010c05120d09060c020c1311070506091507050f042310030b01030606210b030f01050106032316030b0f0405131406070f0c03120c11070906 65
    0x204000300080c14005450340c10303810700c00e05001d4140d100d02904002a0340c2c2c841d10301404002d0000719000c0c0d52451a2022924410b440400c20600c0204000c02072503c0c00505a1040c00501e80189501144007040050200003801030010318491030f5000050300715100303100500086075100914000820100704010303980380705180103540640349042c3d446600d1042d4480c04040007881c1c144402c0d4410340100202e6500c1c0d5140c2c004140702c50083e601407008a6680c20b050b42c02d400301255280305182c1c031010410a004c01036009900e08640241100e40700c000030740085084650a82012000a80b121a40160041d000994540c2e00f07105e81d03070b03903900c6c1c1c9486c107400300160128200807800c2503200c00110400e550fa0754144001454000c1040010f810316042586030030f0b044030000c841000c80160f8080d00f221003c00c030940f1036030301616008250b40054400f145c202c1e850101c12014081c4a42e513060713010310141b11702030381c22003251155008420b1075490036141814039840b5104450414009203c40d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 444397104 1250 444395854 444395867
    0xb010c0b070305061c12030e01020c0a1115070b060312030c070b0601050408120309070f06080f0a060f0b0901030516020c0105090402041d04030f2307020d0503040816050d03 76
    0x1807441c60001038a454071800141c14106a89040c09078810940c2c0400c1840000c0b0702a040040c01500c0800c031404d14840c0e80c509034016080c0188143c1c10221081c0041110460480540200280000c000d05135440c00031903103400c0342c002070314001000ca003040003030f05040202400d09540d00c00450b042d490945800c44e01d500c582d190003844c4000d24808103070140d01600581d0040c083e210150381c1d10a5100d461010b06d03070000c0314588110300ca04c1a0025a104400200400b5120313290780d500a81d60310302c2d850704500e01c40502416001071f0b45244c0092400e07a00d49544002d41004240250b8a1240700d000505a88014003c801010007203417880808540000320354045050a00300180c4410203140010028003881d8080304048130300101100c100303e01d041a15101ba07209450320113001010580840d4121000c0b40c510840d0284560446003a45418002c1c0403210310040c00d001c2c250803940c2d50281550040d0380501510750001d02034460700201284480040c20b4141d540345050b240035140102038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 444398354 1250 444397104 444397111
    0xd0c0e34020114091605100503040b0c041a030105040b19060c02010225030312020c1024140f030312010b090105071208160e090408090d0204050112060b010c0b 70
    0x110544030803a500601d00030f4000072544003540c400a070b81d610304420301a8941c2060729182824400e46840410146000e40551050085a50b5403070304550320b075580c419803110050002c00c0d001100b0700c000a14101d1061003181042e40305d05555849502d040184416240300f0040c0c1e0384038555020b9410240401d070620801280c550f03151002c070740c0030140010307414043c1da075400030306144640c180254014650350b400000c4a1099071640c01071041c80a0a40480c0501c00b054401e07500845142c03c01801260000114640040008810f1007a0b410421181c014150702004e80180c0c6440c0083c400e140815095404140c290091460890806281c480380081400750b01980d00c000310300180c05921035800c4e40e50095114090780d09446141710058843c2d003088815841c04480c0c03a1300300c804d1a12549092007082c40103881c01045444550b6400c500b0340000b000745410100103404440540d03039600405000340301800983d01a8142c604004d426120701070010350501c0906c1700c00e800010b03c20f1000035031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 444399604 1250 444398354 444398431
    0x304050c040c12020d050708060d08070609110303030403030509160b030c0f04031b0e0610021e0111040905090c010201050f04150209130e0f060610050c0c0d0c0e 71
    0x30a00700450341603c90290241481115074030100d40c0c009200c1469212078081c002c1500c81e824180e88503006c10a004200400052055206001900c005005a0402040f40d0f01c00d816405040d43d81c1d4001ca40b450308200d03810350010742ca4209100c0600001d01c0540f0a03000f2195001c45130509000c029080c81c40098040300a00c400000c10070308002c1844255000383d58040885440400d01050302c1480c6d20b002d01811900c40ca16030085901898100840040350050750003070b01c20301400134601121130400c00008915550ac030041c0420000a030070081001d400e070f8000c002180c4c1403031184070346031503400342203281968506800d125446031501c11080c0d2003030f07000c03a00c07080a810348101c003806406252565a00903a41c07014500c445002d94001c60045401c41e0200c0d2080340100c0d0040e981e800068071190b030054041ca00700203c0910660050040d000710404440c0c9100124011034210300d01d4002c266154006117405011410000d0740e1942c00c40c0e8500345c003507482d644503031804400f010040100c55 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 444400854 1250 444399604 444399611
    0x140f061f0e060d1508010b040504020a26030a21020307050f0a0c06050f07120b060301050f180106020a0311121b0c0d0308011503050108030307050c0a0b01090603170304050c04 77
    0x75165030381d880807035408035080d030820700c4015400c1ca00044000c4550080a071359501301403040985040c984035091095400034000c1c0102c2d8540012800000200c1d40700003403410041d13960700700c844001c2009007503d40c200d60302d42000e41154030440e90403d9001003580c1c0194010020f020003168030000343c3d0b001c0f42a40716030b1030f547d0b01707a00f005443c000f100c40380c0100940e0a11040000ca5803914541a10403000340d101c0003802d22a80c42c203801140d561101007540450144014003160a10101402101d1300141c8914000c60303110319041e40040090340034400503070100144008040c3c1c0400410080d1600d00001c0480c8401ca0807001c149002e4200001654900d80708040c0c00d03d441009007600d0381c40d0250420448014a0800600d64482401200d0500501400003507050340310b03219003412144040081c40c11502c1c0c9140c111103d91142d1100561407041410b100301049a07010300c10700801220100041d13103844c1d403a0000015585841d07860340c0d114103100f004080762000c15008030900c0200d4000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 444402104 1250 444400854 444400877
    0xf0e041121091b1210020406030605060c0a03030209040b1e03150f0103080304151514060c07030209040804030c170c09070c150225020a080a08040b0a0c06140f061f 72
    0x91040c2000300111005172140d000350781214070059008000341c030100c0d54103000c010f440e203003071211900c202c0407903240710381c8085110300c0424865409050600001040801c1000c0c449001a002588501c4440b007010034001650016180800c071419805680c00780c103150610f801800756440d4401440302401c115000400901004040603009454080d030080801c50100c260f03003503882a00c09805a910030b1500c016040c0480d24004040d55828458100248221411039080c001444006442203404103418000400096600411540505403c002c180c10390300044000d24034110304002c00a0003803140700180002c29a008080c4603c03290019090400610703808503e000034407070544070104203c3c0e444032000710020111805c6071b8050085a1040320251681c0302d054944460030401018940c0800c81041544204006428400e400e41032401e6410b0660303c506040e0303104803070500b508680324010000c07207207642d13040c90345c12880644468142c0040240301c07160080c010780c00581844500f10a2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 444403354 1250 444402104 444402109
    0x6080d0305070c0230010e0d030209030307140607030f05062b0b130302010f020322030e1903211d0411041212030207080702010f0e041121091b 63
    0x29040aa0b90241810005d80103800c40e03014130008144207480c0c51103110340d144032140014080e1810000b41c2002405191001d44001da0007503000f00d03c181e400d804144020382c04216084451003d421001000e00362a243c04800202210020b86e410702d0b1480c640001d20420342c07030f45210000703407104410071a9030303810040c8200c0c09071b858140c0000304000e410200f00202e0400065824009034805d400074004071001c0500c00e0241d010031258010f0307896002e80700b841d00c40c85524101030300c64028140300b1003000701200801c0d40740301c80c012407000341d0503001805c0040110290a46108046c4801229071380c5601c800000c1c03090704440c100d144903608520152002c1d42d1160700c1200a442101d0003103a682e50f46026100c0da0029100082e2500c900011814015900900031214000c0d40002c980780f4094130b5500640704400903000030320800480c95402c0010780c459201e0301c1c1c01d0780d030b000c0b6285440749203800c4201c503110314804540484203202c00c10301c0382295001560403240c1c80320160000144460102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 444404604 1250 444403354 444403367
    0x20718020c101d0d020c01020d0207140d0c0b0c0102040302150c0d030e0c030106031203051f0b0a0e0d050114012102061e030408130f0501170705090406080615010306080d030507 78
    0x540800707009250300310781c0d003e17000521000c00d02d80c02e8081c2d42030f1000f40c0c00140e881380da4520132010900741424001001e0301e0032124810740544100c1c605100340e0340f00c4410355420b030008000d185080c0c2d0300040c1407081d49090008411120000c9100c24540481c429000303480341d483da42c015081c19218001c01549290600185221110140c020840a81c0d2414000c110b5101d0410140100b844c10020404842d42c050003913040c50b10740741c04260340718689035841da016808841110200501005400300a079600d100301c1c0342e40c900480000c0b9050b2090303c401e4041407010b0303015030940040c0c0306480d0007980005031126103064045070151340700d000288608592460b0340c044101109000000c00040100d41c00103072400b4505001001d1900c1d03290740700048480c21500440f1702086800d190400c0601074848216840b400616005086c000c6090216080e241076400502460b0840400c0009038402c9186e400f120b00d40c00d20742406000e141440c8035071100303060305402c0100343d25080000d0f0f080d40540e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 444405854 1250 444404604 444404651
    0x16030e190b0103110907090308030a0225030311090a0b0912010204031a0105030316080c0f1f110a140307090f1403010f0b03071202150406020718020c10 67
    0x5802840401940780030100d00009000071540f0f001041103018142c01c00c0320300d0b00d00c07490140c0c403401c01080c1140c483c04200c0e080180b00d05a016000c003d40c407a46450391040707501804028407003041c103884924021f0305554200440c0284241d007404540b009690346450f2404850740115000e94418042002c1081c0c0880c44400b0390403580006800010800083c070840c245002c00c003071320714140c0d03220401c0580f00c0c8188086109090040402e0300041070505004001c0a801c8104480c82501030b80811820030440d15038444495400300304c1008411000e004000c188401032000a1400301e44950203818180c00f94400c0040e41004400190440e0084a450002c2c100320000b03850100c0e40e901c240e25140780d10700005402075080c00c42d01211803045000f000090080107003e883c100d800c1014049400d14450b00a03a4825141c814622100c10414001c0026140a5015144850800c0a84103480f984554105144ca2040041522450001c0707000c0c00305000c010404140303c0e407600d4500b00d0010400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 444407104 1250 444405854 444405883
    0xb031b07080d0b032113080d020a050d09060f080a0f050c0d0605030f19031103030c040f05030309130c0905040504121103030f0c1605010213090c0509150915070308041a16030e 77
    0x3030528620241e00041c00040192040040b04c44cc1008802c085400705001e205070b1002c41c4483c10501a80e0b03000e0041603a000140d20307130014015031010640d0090741c0c0e0540b6502002c58000401400300040c078020031020b0041a0300403c2c214008900240c0c1e01c0c3c054159840030000c4d0a5508410984203181140e4080c03640403c4a869040100346130030641d0040c420b141040c421544009101e05010040d40d106a40c01003207600009100d1134040090066407084808008441802203001d070340d40e12a141c01503002e2480e4903220003003120041c041070204200700070702c2da109008200c50140200d10b01c0d03501010245d1000d865441e409051a801b42602030020103d50010a2079003100d03100d10078810844035405c1e024441d003010032a05034fc042c829074110729000b000c8500b824007180c82810007001c1d4041c0103001481500b10140c0a880301e0707041050120300240c010300501c82072019007450705819000c05100080d0a080080c0c4891154200002da00c00b031586829807111980814090000b100181 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 444408354 1250 444407104 444407113
    0x2030405010b15040609060906051c02191106010504060b0307030c0905060c0102031b0f0406050c120f0417060c0412050a0507090b09130c0b031b07080d0b03211308 72
    0x201e0043c03619a8000c2c0c003800000403401c910009565100341c408500b16041c980768a4600030b01d80581c540030504074100c007150140c00304240d180d11003281c10107007194041941c4000d007840720131400500f00300e0b040e40621b1003181054824010741c46440120f80c0c111409040003c2c0c2140303e442d09513080851a44020b602c0034000c0340103810308006400451042d00b050888610400718181041c950f4020800c5c10301400c40b050000b030243c14081d100514621103242c003140c0c0e001900c0d0181c0c0100d0f41c482920031000c500b01040c00c0120140240c03111118014001c0130300503230328045070442841d004d68490b000d020300b40c407074000e01800320501404100c0e580100a0310041c5440700c1c8464080d003e2100e0880c0102601c5001511459205a15181c166030164065422500e03000c0b66001d55040903110240350204c82e202190107816503c020720b05188142071458a4400703610b007510440745203980081c02504940c011010f02d00826030411605e0131500299601d6800d039818001c030011a640102900c1d10a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 444409604 1250 444408354 444408379
    0x901121e11040c11210c0a060c02070e15090c091509031b0d23010f060302151911010f0f061518060e010c0b040b010608090309060d02030405010b 64
    0x81d4005000a40d80080c1d800f4031448940c01000c442e08018002a80880d4010424000c0e90340e00f000b445003244100e070118942410f0349940202d04106a20a044842030340d80c3c034040c0da5094040c0721803402468111020300d510f10f0f100900171110650705841920039040c000000300c01042c0f00060300c11070180945a0012000821205151540031f0b0b00300911130700c80d40540c182c0110000d501e43c01c64043c050282410050503070380303c484001006032041c0e80528401180201c01c05d09101341c54000003402d4001c1052840c1d401404a4030724400c165079a0403100308000101607104040f00c0b001501c04d0710303104140a00c403424a070300600d060310440c031540742004c24400780900160840c401362048100c1004000b694550103841d80c0c503000078550381500341100308100d04da002c3ca81c5581320701f03010305046000703101555403810410002c581c100e40004030003005012a6a01c50511580100110025031a01e5400c000140c2d00d40146264118a80d400100180403c802034200c20520700000e0308401c0c100c076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 444410854 1250 444409604 444409613
    0x12050f070b04110a032103090203120d0506040603050a020f060f130302040f140109110409020a050a090807060e0f0414090a060e061605161202070911090901121e 71
    0x7010b0314240c4000f9604075035030485250007560311080fa07034050554242d11040014130307000d0100f61403410301810f079102c001c580581c506105001050341c4500311540e0728000080c03410221030700941168000e032b15004e8280000780300010205102a011100c0281c6421442d000818038411004900140358002c521030055103031140300a01540e01c03c54003407018801501005040f2050688114609600070340100310f40302c030580c0300b129a117250407075603481c041e00d40d10018113a0744000d40000005600080c0445403503030120b42140509410000381211600c1c140700180728000d5400c401d4403981c9607490442050f500d0754001c68001e407800411a0482c0f500117407294907a90250742c2511264200705100c2d80620700441c0c8e0500c910128024070004120584c4200d0f030913000280c0000c190b00881078084080750175070540751505c04c1141d000f0001a420300d43c42d1401d549842d05151403008050254074895620070300b40505413074502e201047e0b200704504003c0d0710588010000540e844c1e007000b0010a00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 444412104 1250 444410854 444410873
    0xc090b2712010b0103051521030405100504061d031e01060f08010b100c08030a18020901030c0f0504140f040305070b0705120114030a08030a060905090c041b02060412050f07 76
    0x50f4241c03000c004036962881c020300c1c18904917240c10f5010010b0115841c076808108802c00c6000b0b00f000c11a800c0c03079110030200d01c007120b503117210402084003c1410000d41e5444002141000c80742070080b540a504040802c0ea944640c00c540d070245142045210004002507102c04014401d00500e0340c4255661306c2202d0007000702c0900c250140c21805080441540141c0d03801c100c4980c0505198a5036540b8100100100110041e4200c10300c1c0d00201c2c907016a840000003030203140101e060708411844c10720400200003c55010900850a124100d054810070b003441c9036000c9030100384040145d4540c981196540724685008000c4040b2406128140790b21001070100d500406200700786030390725903000086c031541c109101035041d4000c000b50000100d8180103541c1005401d2004240f25440e00381c0141074910440c0d40c00019802140561058a414000c503806046080c0003414401c489000007500d854000300003420342503004440e11091889641290801121401c40f0b37500c403011031500c030261 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 444413354 1250 444412104 444412121
    0xf060d0f060503190305300a050108010b01082a070605010501021e1f0617060f0c0307020d0e061b0a140d121a0402070f05010c090b271201 61
    0x30203161400226403414001950010900d50030410782d00d0b10401d0785d044a4070b902ca036040e014000e9104e000d02d91400501c041c0d054448501d05280d44036403070560090411101c05a00001e15030381815154000c0c0d981114540390000d0b81d0741c20003040c01d4000c81d40c8903015091086a800a4400054a0030070b10003654440c1c0d0588200360700781d07000050004200c0700704144060704907076650090301c1c0c11542444142000c40840d07207030a0011803800d40d40c103160f05001502e0700509081d50820310420168852041c1055400010300d800c5d03a00758105000c0c000d40c1c45403c2130380d0314140060039000c030201c0d0765080306841d0300e042403868124003400303a0840701d5142d10300754504035082042c051104242010111b45002c1c0103140340d560100d05a4029407c1d006400c0b00f41c2180d109480440d00f500107511a4002400c09501404c48500049a60302d8503c1c21500c1c0c10070100c041242d410340034070145401c40200e0380408000007600a4019043e44001c00084056001603404032600160140299044d04070117030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 444414604 1250 444413354 444413381
    0x6120a0f0b010e0601052b0612060b0402030103050d050f09040c091d0c0d0f0605030a081b0607050315030c030f0f070915050d05120a1d061204110f060d 67
    0x1800c2c3d0741c1e106000781410040d541344e8086842030055403000080c0c8820f408810018110f8202c03400d224190210843da01c5410041c00310204403949418404180a910b038030001c2503800718030b103600d99110a61901c1e2600015020400001083c665004e07410041d00d050060042c400c000008001030090101140c85c4615601c0c001c5c1040304070030005403503940e28494980da290403031500c00a110301c0d8004001d000c0d512003002d55501030128003502d0401280042901c2a002203580e050401500c2466070302c001009041d991254007000882039120f030a5a41040701025466800c15503000024200075480900d240c26208090341d5480740840081c5242094034a2000c0c1c03600c450b00c8101c90019030302501d0301c2c041041c0e82c8120030020760070612500e507400b50140054555100406c0c0a0a0255225003196000148010402d80c01240d180c01006081c3d03500f00d984a2400407071400307928290100400217030903046807400701e00854445400302014064000e20305a55221201d010100501c000d0800c0756 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 444415854 1250 444414604 444414623
    0x7080f1312030807050703020d081305060103200607030c110f040504030f11010c08160201061a070201020c010806030d03050402040e1005220803130503040f090e0609030a0c020906120a0f 82
    0x44da0f590048084030b16043d019800390115000c05503091302e001c5005001603503070f00140d07142d900c045082030240c54040c600c1103040d2a1104d166140c45a25107100c505558880c10b4108855000a600031955110682d4400c0810420003008000580b0b94500140b282d90010706260412080552141411000e80544d880e0031000c0d0000000c000d0807500d9500620020407401c001003024800500000d08030007a4920021410039120442d02e041c00d000f07a600c00044c840c021070000300f1580c0600c454400d0540a190a826600d00500001e545034421060f020503d80c5d07a02c0450103544a1744c010850004054080750b50000b11400c52000401c0700b02c4442007050341e1248c86c001ca00903204003580000c2d0b00300c081d403400e40d2140d5015a4010182c8081204d0301d2004100c0001d648429100c908003d0040060004a500001c0c8446040a0340205440301a400801c0814040c1c0c3d08250060300d02a01600e01088070fa4400780440c0303170204094a28803051082510030000c208078044900141840f461800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 444417104 1250 444415854 444415861
    0x1d0a0915140f090307060218031606120225020a0b0a020c0103180c0b0a030207050a0c0314010605100e040204080118021507020f101701060305070215060607080f13120308 75
    0x5407a0b000d4a01c44800e4108002c148041042c81c3c001e010404200701e050840300360a4000240b8120b030010790a850559049030402100e40c01c000d110700c2c100e119070419898002035101e0b1810a0106200c00c061090b410720300d144c00d5446003000074001d4081c01020316503d02040001965a910440c2000d001900303000c02c5443c9107402c0c6212000d040c1c1e003c440d106406040c19620f800d00e800850101c020150b083c007551000c90010400052200e000d61002020799007942414502c0c0c000401103d44982e041c541c0821030380e154803000c014642640c0c0f40240310807411000107000f070710031544001229800c00301201780901c11241007000da43d100300c0342030480101d8512602d425004140d0042c0d8007506021040143d0300701040703441c0c90145c5602d042d504549000700c400c0d071040801c1cac2200380003c0c1e813101008038075070b0104650428016120030350900f40ca00240010100c2c071034030750020043c0c200030908140c5c05890b02d040e6031000038810401e50003039803201000072206400e0481500040c2d03152010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 444418354 1250 444417104 444417121
    0x606040e0a0803010501050915031314060402090f0a110c030d0605100909091a041103011d06040f0c0e041a010608010b19110d03061409011d0a091514 66
    0x140e581c0568000c49050030340e80307000e00564103500221102c40c2c004110210341c822544082e4000c0d48034600c4403054904510560510228000b011403e680041d4400d00611001d0b0ba500c3d40c000340d1180e21000d0041a5580e0300d400c150281c420195440d0414a020408404243c0d01002514032070540030b40c204600c603504e10420400503104080c08001c03c46416042c0315010154004a036501c0c0140d80c14a000141c415111048802c110b600b6210801c032511001c01c203160a00804a40d00c01a20300ca8500362203174042c0c56141c90000d00000c00000f06130700000c08104800748000000c00d8400c51868651420b4202681c000b1030003403141d61804500f1001190450160110b20b050782d0004584d14104100c000c00c0390f40b0b140086107818280f0407924403000b103052007049103100e0401c0c141d9003c039640e840c100b40d000342400462025482a100340c001071100c04c04044480c05441d00d0381e00c40300e9403a01c1c1c00d000a001040303043c801601805c028030380c1d58008005074008150781c0941950000550341c45032071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 444419604 1250 444418354 444418363
    0x303210609070f030e0132060a1805041406040c060f05040f090209311a060a080a11030f1608071b05010b0603132003030a0813060507020606040e 64
    0x2000404100c07403c1440721002e110740e000680380f2240200016620007004914211501c0311070700d0340f60b40182603400707001d52520f401c4984d070081d00c25201244624242840c12240c100009070318003c540d074a10000342400084145414054100310645140f8141814951070301681c0340102404901d0f04803051440034441d00071070b000c45e542480346444003070030a6142d202039440b802c4d07002e03400180428498811701c80c0701d02d11948140284210401104458002c40544582c071007000c90221001c00c4400c040d803034000440702c0d1000a031420440035900c3c4456000101013020809880c1280803003006840a40c0a06d81c2c0d000b4602d4651910600c1c5282504903070884046501500082d40c0423010f4022446802c840d07100c41307110300e00200d480044040403801c1c5400844041c0c0c03550030325014000520178021500c58948114602a400c11070b207601c0425624403c1580c004100b02c84280020540c0c1299410004c505603c45030512260914480c0256a004d0541c0c16910442c9048403186c9001300018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 444420854 1250 444419604 444419611
    0xd110606011b02060c0f010c200303070c140102041d0109051009020f0f2106011d090403170f10050f010c06020a0e0a0b030f011706060d08090303210609 67
    0xd4071401075207800d02003403242c91a0414200e070005001d2060189080d4148000b11540c0804400020442c102c0b15000b48040741c0c84000c0f40c040140819204042400401160f40c08512401d003280300d405245080850701800444241042d440403e010814504040c43c16858100700c540c41c07000350743c844201104a50b0142c03000d07004140c0c4240b040200c40583c1e0040c1410790245504c9a00f009015210919954050700c400da48e1400391000c0c451000c04055812a0814028a090101c40000070841c00c5000d040c610a24400c1241d8800542010302c6003c010200c0380d002c104903c814200381c865112400800e94482803010010791011401c1d05080b114020b0424059507406445040d40e180c4030000d50000e1407080c10050107030514112900c0e240c100034000e08505c480c0b50b50700c0c60004814061b1120680214800c2420340d40040c050000019900340c20120403586d0040318081468044814858650010741500000c10840c00510ba000114003000c4889030200400c0e60f034510411152070402c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 444422104 1250 444420854 444420857
    0xc0b1c0c021603050c03010e010b0a0605091309110310050c12060411070f05070605041d09010603170a0206090d020d0c0f020a09020405010315230a170d11060601 71
    0x42811508268168000550a40c001d005490380303001c5001061029181541081c0c0707440d40300c00551006800d091085240c82c01842c4020040300b906c0d00006010081184500380030030501292444842d507a4284140c00304d50320303507070400804400b80707403507104c9051703610358144640030700d01000285410f075000d0240310b00c1e810303080e0070314045580100d01f032104005001c1c0364015503218240f070301781c20000004210407401401d402c126440c86180c09440d101c0c0c40d40014040001c01d000c00c00c0424403810030004007488007803090045503039040310300c0d0040c4010380c0040c105c0c0e885d0b100840d0076000440f00130701e000382495090311460340c0c825866540e10700b0043c0000d8016800400e03c0000a481003020000c00c0d0310802c800c10321034605800040c10128075030050f001d103a41c00141008550b03094440c032040c0c05d0401c5405060030f03140081d10890394103451014918494086455030143e078845c1010009800c0c2c0242442c903102c6d0300c40086a4a2403512812000b090040c803003c0700e110400903a41d4803d4905 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 444423354 1250 444422104 444422137
    0x30e0706140f0c060f0402240702090a0b040c03060513050421051b030901030b031603140a14011407091413140411010816050f090604080303040803040c0b 68
    0x8207101040c41e03005011804003030030188103811114034144036507402000600401000d908180c01001100302016005044100010a103403e140c000b5001ba51b9640f43c045a002d041c2e540c500b0b40c40c0002d41802007610b6881441c00d982c140160390158095000c2e0341040d02d100d0300c0303490020314560880c1c00645000d4803004541180e00d0703007034504c440303810005442803503c0c81c00c19202d01210341d00c3e01c07508543c02030305800108001500f941e140c8074194180004600421120119510b94281d5107564000a884030400c07040780c43c80d40704104180d01c6019032100d01521595180d100b114001e140d00140d0303030041c0c14050042080580b2826030041a50712840f001c42e43c9482c103604120b0101c0307900c180d464480c0d88500e040812498a03010051041d030091621b0a030605d5480001030420000400101d0700710748400080306410361220560b0f00c070305491503140e036461021000048241c0142d50284400340300c004104020800901c0240d4020345c80b52440c056400d4841c0a1001d01d0301410034003070010f11030b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 444424460 1106 444423354 444423377
    0x12031e120507090b03060f0a0b07050708011508030a050304110405010305030d0b03010c1b140a050f060601030b15090409051204050102060f06180c0f0a03050403030e0706 75
    0x207151809420190410a1810702c42c00090322a9004041f03080c0050f405842e0050500e02400801307508680707605180c50b002d036480e0158080c01040e54200480301200f44c245004090070350340488095400e0030342024080f00c40c1c1d00014006e0f101c003c21010640055103551250300e01071400f42c1d001d9540e0f40c54020450054a420309841806a80340000c42c494156010312072410780c55056101c1d40244440c0e0515901c44d03064000e03490350f03c0c0104050034040000005036404081d111405555880e918078005504071080070720340d142c203d85003403411000c40c10954004d01e19001d0007800001c103030782c44d901c0c0c452400c03802032038201c4e10b0708001800740459030b01001810350011a04d98004214070b40540414144200c13140c41051114051000c614962055801c0e00e0202240d01c0c0b209481e0702d6080b070010003a000039035042d4040781c40d02282175a0b046011a00750300761501511046c22115 = true := by decide +kernel

theorem cover : BRFrame.Cov 444244604 444424460 := by
  have h0 := BRFrame.cov_init 444244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 444244604 ≤ n) (h2 : n < 444424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
