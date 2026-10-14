-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0799
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:52:10.470849+00:00
-- url     : https://prove2.me/submissions/3a0a7100-68bb-4da6-a916-48ced463e576

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 143525179 ≤ n < 143705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 143526429 1250 143525179 143525201
    0x9070303021b0109050913020a0e07020601060e0d0609020307080703260901120b1309030c02041103071b050307050d02060a0e0109030906051305090c0705011505090622 74
    0x10144405108140c0c04021401040041414000c403401d40d6400003091401c550041c41d028100003400b02d01c4d00b80f0302c051a4010564010f1110a4060b242c2030381c0c00f00300004441c040010b100d140000110f080c024901ea0080f80070180030580344000c02e41312140540034005080341c05209280c40080c450000703001090186220313000c0b80d15840500412446c00210041130306003154001c105500311a83c10002d414551460701c5000b041da8200100010035503c03841a003802400d01b059031440801da40711900c01c0c9400d00c01c49042044000080440c000742c08102c80329000300726000c0410202c1190840c1e0000982e2181c003c4a1500f446940e41c28140740e1320100305005a444802800011443c0d4001c0c580e0020412000300103c1510b624004c10000d1380784940401c3c00000a0b030b1401c108410700c00c0b28041c1c000a07116004509004074001c01d42e81c0030510641c0c0350752270992501c1c0e500d80d490301c40b0011075100411003091501c440b020444507080e290805140402d61a00d0031040701c1d042c1c05152550a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 143527679 1250 143526429 143526433
    0xa0b0a050c16050603180316030905011709064b07030c08130f0c0e0a0b120a1205160302060a0e0c090411040b090103111002121602150309 61
    0x700d2500810340b4003a020000d20000012180050140f602c43c40305880d44421707401c036480e01c18540064014110b00c511940c5a044603000115501072680103181042100d00a07a58104110058454010141c03030a451207001500030034082012128808200100101001e1007072504a01d0701ca46210265841070700501d03106001c0042e894542d404170706a0303038000c000381001e22501c10100c00080001200810313904a03403000c0510b09043c070048100c01320010380d00c20341000b081516203110780004041158101c4d160b509014244800b0301302010015100405d000052640c071483d82d80d40b42c41440300070440702c1004800c3c04241c4202450100d0110f00380d000e500940814249960b40c20162250580d0142e520740c00402d5042107515000025507105401200ca64104060080050080c0c80d0444000d50b001d0189800131003400032111140319407082c112410701580000c500160307140d4440000c102e055040074031000b01d00c00d42e07604005503c01c0c4002e00240c5500700c4e104045c085904140c44440f10b903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 143528929 1250 143527679 143527687
    0x30e030709090501060303030e0a0b01051905060304140c03010c020703120309050d0801150e031504020102030c0d0206011d040309060503100906031112010b0604120c0503190c0b040302010c110a0b0a05 88
    0x7c035030184269085001000d014207085003440c1c6804d10444810f11510b805481042d0304402c6640411001d00080c190081400c1d50f41e080c1420508201c91921454003003c2c05a016044a039140520410f072107a1001d4003d00a501d00d540c440400b41c42c00481c0c1c0b1000d05445a10f4600090014040342c00d00600e551076611790340d410700c120302445540503454070040c014600080c041c80d0ba00080c1e81c080c2c4001c0c849070742c0d50030795885c40101c5c218003643d49600c2542c419140021000341d0003242c0c00303050b50407004a046560b0601c12820080b840181c0d8040e01154040400303010042c8a10010b40c4d100040b40312180b19180d03542300704801c6540c654804e5416100380f400344c8200340740c00c0314916040310442c40244048410f03800011124821481408602d40324520b03000e0401c09808940f400500006081e18480402607a108507203101600d801c51f580000c00401040d10258030003030b14182c90301a5507441b160010369480030749074070b141d42001c3d6004403a0b51000071800e01c403600901030f00d51a41d0f0b4040d22 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 143530179 1250 143528929 143528933
    0x9020406080d0206011d04060b0f09090a03020f01020a0f110102040f060309060b040b030718140907030210050315060708070203071811070b06010e12240105010c03020a030e0307090905010603 84
    0x101041138001200c0150780000706100300c02d50760b03001c1d1f030050f41050000230398091640025002400c42201c1d90381085528080000010740070031348062944c000d4003900e501659450304a400c074405c09414201007108940c03142000c0d80f04103010041c0d40c01d1440014a41511549208041d00103540140c002a03210000e9504004260150442601064405000c1c260780f2000081d1114414000d034001000007002c0811380e480c1c82e40000c15200e00b40c3d0003200950a140c505039454241c180010b03401500a0f014002d81c051140003100d1154104403518010031f0a100d0030042d031a4080003055618110a201c0c00016035418010280144012140c0c1c204880716000440203880000240e406007950511130787e8045115060300b103034080300034a002d03421020104002000b0403072040034403800c3d01c149002c40f0b4012032014060076110102c22741c9617090340e986000445030201c00e001c0c000c0050b0440c003943c0000a000303008541d01202d005055a01403611450000200c484562044d81e0582d12150b040007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 143531429 1250 143530179 143530183
    0xa2c0f0a020d12020a052b05070c0902030a09081602030d171308040801020a02060106110106180b060f0d090c0e060f0103090602190210050f040b01150917061b040f0e090109020406080d02 82
    0x200c882c25040a81c00c00085480d00080c0700034ad482071a00c500c0c0c00200050120220b544108461a84002d80380d07121441c42608140920f0400381c01ca000b48541e0000e07038078060281400001003042e50303c042056603161103c052818402201c215503c00c000d01c4081500c00b802e00140070b03014050350080006600d00b241c010b1000d5480d0060311002d0b450b00c03c05000001e4054042204001040400b10b1b0459400010030b8a40c8202100e80001250100b00c5400011068000120f400e009d440741940468945003028090a0b003036400d56800010703982d042c0c01c554003d8019691081c020500107040c11140f41c81220041e16010442006800c0210712111450312031154640099849000e0030b01403501c1d80d550f4184d00c4e018001c1230381d10f04615034080c41c0d070340c4544184005080701e060300c2111603a04d9002c071a070740e03c1d05407500e80a0183d800c030030f9100c0c82c44480644e42104e41d03a44880d810146860144c0000000190a9a032255240e6940a0160f102c40c00303030328018007280f80242500300034240028 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 143532679 1250 143531429 143531503
    0x3190201270818010302091819050c090603060a24030b030d1d04060317070c0b04050f01110a08070609150e06150f0306040b0f0a05010f0504050a2c0f0a020d12020a05 73
    0x49d00c040c540024090403040c080c003074503e10101610195980e403103c0e40001c1c4906203662002c0c00d40307201c48020f290300303330400600c82d1030f80d00f0a914180800a906010180c5800c00d03000e2203c0003e144040881030000561942c080b10100a000029516101d0311545801c254481c100b6020040005618003000034100300c0000401c10341c0348040c185824800040e0003642c50640444c1005000c040d00b5003081c40511000c4180c541c0111459070301d29030791804030040d1142e1041a9440f01d40441582ea020f41c150040400468001010b0240ca45d10100807015420501101c59045143d818150282e41c40c20000140128040e5022044910305031108841d101c9000f890480f01c603081800401003903c4c941d504100b0340710102c8002c50329503241d0100c080100b0031356111100c032200501c07100105040e5583c041c0b2411201806643c2d01d0a17401180c0d55a556507d90025044a1241e0300300c0c0101e1426080594003450610655440c10103d490302c80c500320780e00940c0c4807010040d0301a18000070a9492030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 143533929 1250 143532679 143532721
    0xe0402040302030604030e060d02030109061a03073905010f05090a0c0504020f251103010b180a060e0c04050109050a060c0b0603031902012708180103020918 69
    0x150315050865000c00e0b180e40002d00b008051000c0030108280c50740d10b83e416141c0c810000e8070115225a5142880c1d006040039215803698055884a090200c0c00440200d80c40f815040c1c5806c0d6088541d0308030031340c6d007292954548200c88041c021407169400e1501414885074050800800c0340020801c0040480d41c0103001114583d10004803400001c030f40385050411140102c5005850f1500200789403a103104152058540b1040707841320801c4d003040f03003022684941c0120b1032455654203603410f25089810701d0156660180c4c0402c0340d4a02c1d48144200070b07501c4100b1400116840b95500a0101050f40517504801d0000700400c05100a59020a00500920084801200300740c500a000b84c07600e00c031207501805440c0c00340006a402c0d2020022100b00c0c41c05400200e031030100d010f800a008101280d82b03080d60032860028445925815100280440e42204c001407a1591840d07140c4503108000c1d00840c18560240401da181e40e40745c44400c60852081000d840d4540b40c0a008841e10302d54405076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 143535179 1250 143533929 143533931
    0x13090b041109010815010c020a061206080c0a03080f0d02070b011401020a1a041a07020a051c170a0605090a09140f1902031501081515010e010e060c060901050105010e04 74
    0x40b0003140ea03003c075202d034120b081c810b034134a40070100900407540101c0306d8030080d40081c2542400113a107030b409907c150038450020300070810252141030407074598101c140c902e60700a4040d03030203001051213030000b80540d903c80b11103103140030003186121060360044001a14080403490040003c8002400100e01c504402d1000d010000800d035150b2512141d030104502c0782d50f2014002074100003401202119601c4078480c08402803400e120003d681e80c802060403900390213482d803450f44003407449203d1403a2110075110180003071114441c0505407500204041e100d903844000009064455290185c020310b910702010420060909100303c0c40c5403800800081540f20040b9500301e803c0104122280b001003204146501d6054000240f41c40c6042c1610b8045400754000020569400101c03040c00c01a04241d1aa440d60750484458011881400090100b000d618144006611a584946904800529041c10400b00d98401450554120b46949590f9921801400705c2d680040f01e03194040d0003150 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 143536429 1250 143535179 143535187
    0xc0e220c06030207050c04090b0702010617030306040509031b01020415020c1e0406030b0a060608060d08040308030c21070810050f0d1e03030b0f01030204151413090b0411 75
    0x25908000c1419407081108056011403c2c00400c0700500c1481302503040207200744400340e46030800c4d8212180c01d07924400950b01c0c0541c00983c108488540c00c051040c0d040207035007036a40d46c80510000c1c1c0740091103036540e400200306410032000356070806002141460001a100e41c01e141242c3d662581b410101030541d404014205215070326454480c1c85a50018030304400d50700d100021074040c10443d08001e01005428007000b007038107a240c3c0705a08a442c559900046030304c4c0d190a012002c1c1d1504006003160380c04100510220303400000a54020305100902407800d6210280b40881083c4030040503c191b00d13070000d100d00f1503809607445400c00880030110079040c1c43c01001440f40b45802007082d00544010801105001c07104085041550300d4484010070340ea05403400030700030081441180e00c160701c0d223070401001d548244252801da901080102c0c010007040a01501c12110030101c21103c6d02c0104480580c000380005808001d00e144880410204600b9081100392601c8224180c0c4801c4148 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 143537679 1250 143536429 143536433
    0x1903090603270203191505010b040503122101060c1101031107031107050a080604050609011b0e030a080d020c010f1503080a110a0803041406040203120d090c0e22 71
    0x80b090103240c249070070034040000b0500c0442d09000ba042d4031415021000da0141c014003e40c2408891344101401d401c0016070f88654032401180240e000d400e030194003a200d0301020040c040d00610700350036400002c2180c0c100505a00041c0781e0260000000a60808051000c22282da04550382a400908082c41603090100100c000360040344009400c000c140c7c90014004141402403d01500c0c01403c4100683e03258000035070346003000e035421982c62142c14001014500c0c18400c1c01f020641c400d440800c44160a041191014090014240c1c54010001c0d440c0000d8807a800400c5c0041d0041005a19041e83c016410f0031140481980003016041223411000425102c1c482820b695110840315100c0401940444000442800700c070210f00c82c40c00c1020520440c0701c05140310782d21509201010881030aa0781e511008207a0f4000d4040d07001e0549030700f01c10102030260100e18490b00d80020500d40c0f81e15a4541103c9650122164034454000c0c4540d202c01091030714110341041800303250b603144076 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 143538929 1250 143537679 143537711
    0x2060316030e01050103050f071202060708030601200f0d02030304020927030403080712032d02250302070b030115080c0c01090b07121406040b121903090603 69
    0x380588800005284500c0c4030a00942c000e031081d4014100801142d0707120314045e83e84400d480c1010341103106e0080c00190004e0720007103c148050740601460b052102603550705407940c00240c2254180b22484d800d003070700c014888c21039650340e0800c2401807d418405c01c62a40c10003040300b80b180c085401c1003041002503140c030b032203194000748490122501e1030f031401d5a461030261041174070740c0c003800001030000903c00254041c100041c0141024007008034480816400c4440c801a0509900d00a442d1007102e0b5842c2d40299031081201080035103000d03646103060085074141880c025140661517941018580d040040c807002c1c080554105241d541044800c0029082801075003080001540c00540015101020f447e041c20642009100030186803800e84480034088950000080c1100c8110762039841c0d6005210885074049403c003a580c84400038040581500c544c001c2c4c0141c18031030400d002c143c0802038440d40c01c0000081c0b03c0100301d6854002d0400c4030326401841054203100100040c8601 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 143540179 1250 143538929 143538931
    0x1050a0608040b0a0e03030703051e0712092604030b010618121b08062e03020d060b0a0f0e060f0a1502012403030210050f01120515040305071e020603 66
    0xf1440400703070340c1e4619074428040c0800741da0000c400d0002000b884400c90701500030302e0140b480408002c08448140108c41d130310382402c4403101c0c0080d500700ca01c0e010b00c41003a40804043c50003003403500704254915500c0300705039005c0d040350380c1000f0300083c0800500c143c0e1080c490240c01189846e0000f5141d031014480c0c282042e00036034285d1a006d030702c1d130410410101d00b9801c04480103581c05000564031054241c440c8130031201c40d1810b006810540710191b146d000400c001600512452014a080d038007407080d00d0b00e83d060b007183e50a80c0e84140030380c2ca9a89075585001012540e090011090905442c8800b0541c00390178540900190480c0210545d9182000c00a81f5080d00c4085005406007000702d002d49503400303620002400c81c0300c81d410040c030282c401100b542d0080e000c0326829441810b0340c80840380100c5410206843c03070001445441e0f07034846800311640c0542d080301c5000f942001d480c17414000039103007103004c900005000c0d4200900d06c02c02c05440c00c07140e200c8060360740c4940c020843c0d500c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 143541429 1250 143540179 143540183
    0x90a0b01141803061602010e1614030703020301020c010507021006080607050c030706050703060f0e091b0604180f060503010c0f030e0a0501060f06020609030310060c02040212070c0b01050a060804 86
    0x750104403071a40b0108510610702c84407005049901c182000b100d802c80007400307841820019420500d241c0c2d0321003070000790200a080c00f1128044500d29243c900040c10402e40349081d4180614900040941d42c00d0016240b0416040e00024107420000000b07807602c04000701d01d2156030308050080001c02e03000f08049901540c3e45c100340d42c2e0303103880003605802c603c13400200511042c86e14081c8405140d2682c8801c0640da003206802d0200c0b03440e4411180d1201c0d04a540f01000d50066103100b0800c0510b130400c044844000e0019030900741c544920205901e009562610702681c0c540192254004034068640101010f900800400c0100540107140381100000d40c000d0548504500414000070840c0c5d4003c10b0300000200143e076126044101d0709240b030301c84c1c0b400500c20310340407078481d0364040704507030140030b406044081c80b91506e001510315150b401800c0e40d0003a4207102080d001e00070503407120f1103000f56541d0010900b0007840e0068405406130081350042000303040070700c030b00c54001c25080d0b08a6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 143542679 1250 143541429 143541467
    0x72a0303020702040609140105090a02091e0a080f160603020705030313030915081e0717040305040906090c09091a060d0b060c03070606050301140403030c0e04020c0c090a0b01 77
    0xb8000d0000c18040d10090b4084040c10b0304e4902030540250040744c40c1c5060310703801c464040c03840e00c03014a50000e80c00346000c003990005031080c24641e802400aa42d20350042c0241041050036510300c5400d041894500c9400f55603000f004002c1031103001c1c02e001c14050492801c0c21418440c4a440305d42c1d4a00000300030594010403403d0440a050081d40e468009080209107000300340e0707c0041c01041c0308401da8014005041c03182118034108140644944103c0341944e4017194014005800c0000300c101500c1030701881070030400821355074442d000c1d02c0041c04491401245200030b115008000014682c80040000d1800d6010303845614005c074500f12179107003160503584071480780b64114001c0180090085e44a14005004041d55001001a1400e240a200104080f65036042450b080c1d45040c055101010040e40000d40064001d0340f00000380c0d411890132200c1015010081422644072180d52034107640308030030381d1600d8034000104980c0840905428084220801c1c000380098032092903500501c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 143543929 1250 143542679 143542687
    0x406050d0203060f120106030506010e010302030c091f0e060118030c140f280e0103050604020d08070203070b0903010c0e0603180a0b15040605060c0c011101060807030b072a030302 79
    0x9a1300c078003141c0311858005203140c1e1481c0c40081c0c494001c0910f0310080350b090140c1c0c2c0001600e2102d1803070540c1281d4015010b40b81504071802044520040203145101c200340c156000c06d034071510b0a07001806000c50004401140c00d1410001d4a140c9112000d5403034103440340428800120781c20305100c101c1c0d680b13402c105603440031500094140e02c0152000758000000340300384103040c280414030204400b045100307101c1241e1519040b131220103090201070500e5000c4004038005003404035034032a007140201e91030381c2010035070f80c002410540c4c55803184028000c0415070398a14074081c030849415140c5400d280c0d86030800800030840602000b446100281441d40c0c03401b5400106010b82036015070320418402051a1240f4156091207010658900803864603502241c9410440d0460781c013400c2c06030081c020038a1640046511341840d801601c401d54803020f0000323070b1120400c1040c020314480d0500c92080d243c20440140542e00b03e06e0448070b22446020550f030500e00c2e502c90f4903c1c1d603401d0320b405652 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 143545179 1250 143543929 143543941
    0x2904050603071d0a0501080f0a0834060b0a0303080402090603120d021e07050c22020705010902100e060f0a0e0d1a0906071205181c0f050406050d0203 66
    0x81c0341e010f6001e8406a01241030b0308024503c0e405500344070340c2c403c902c200000e980301d0ba00c4c00e6481c6c00c0881d01120a92281c06081b022032001c0005e0030180103807040c2824606d801303201e503003280c1e0440d03004c0404040c20b40d01d5040402c11140a2106460800d031810030000d861610010311100c000f0300068091116640481d0081c0c50503c0b0222a009817004155910016000440d00962000b82c0351050b12601104000c41600141c0c11600c070a40c12030001c0541d4a91320003002200045002858158a856600007100c0c15160024141e1540110300006032220320340148201411848107200070002d240c001626540e90303070800d480c40403440002264542c0c071001401da9984450203003640d80008103804450401161201b060300394a81028801c2141d102c03980441e558103400d4a505c00450307195003081c1050005a0312040d8400c0700400340080100307101041d2820800d02c180c441424040040d0745040c0c2c0c03a00907403881184500ca18000b40307060b16120000300380e4007809401d01003054001005c03500d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 143546429 1250 143545179 143545183
    0x110901032705070f050d03080105061315021b04060b030f040501020403020405040c050310050714160b0a02121506030a0b0f0306160912150203091e0601092904050603 73
    0x603a001100211041141e031500708103544103910710804c00c110341452000300c0c050800c82143e00041e5810b48030030344140d0910301000929000b4280c007a4103940802c800003101c071030b00c0c020003041c042960003500d406e00f4480c40300000c281100c182d00d400f49042a00400190780d400701142d904c45215a008034003034a50f0b01d410780c0a03200b503a05c041c0d40135040100744418065500f4094040715811022600c004070030103800c1e07066410450b040b001050481300c000b6036144942d0001c202240078034a62600141140e075509504403001c0d55080c945a034045003e0144e1400e042c0d5030390b003054000d0240001810300400280e0a440020205c859441c0c0360f203e0542962034030b007010942c1c3e0384006c0580c0d00602e4107600c080d4800b0f1001d101d00002440424000a8855608454044c95504038611208402d2554031280c003a50006e89811094451481840c1602c003020740418000040100030b000036525001c10f40c0140d40c4030283d080103001d04401b40198075020a40b420180280075103001c5455a02d42001074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 143547679 1250 143546429 143546471
    0x8030601080711030f0901030b030c010e06091306090b010f0908060415090503070609030e0a0f090c02030c0a060c0806061204110109150309021002060c030c0d060f0e040302010c0311090103 83
    0x1c414400840c28200d0352821070060100301d034088e80d00b0032100c541c0030308040c3c0e100c4480b120036005c40d9042e01c0110440c14560000c000013800600b2810301e0300f40d454880c00407035015500115a143d03941a82500c150f1f400380220004000a280421946040078206038031608064002445030074010030040500903141c00082c00e8982110641c2d0712610203041610142c81e0400044002882d00461f1a6103440c1c40303521101905d030100c1109c40ea450520100d9401441206035020540c40b05115103a80f00e141001040c400c0e40c40f0301030100d0700240c07144016122203005000c04e80306e90824800741c0c880c40c6d05441226442038002400f191746102c03460042e1850820368015001003e02e00e04c01c121001d030150008180307244280c0b0380031110207441b0412a1240308c03c0d510070203aa801040822185034084001d00450400e00600248156981c505031000307118561105070710102c941e04020034560280304041611881c1e041c140211503180540b4001707807240003201c5042c59503401c0c01c1e40781082c0d014141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 143548929 1250 143547679 143547707
    0x90c0302041b1101020c0307031d0d15060803040b0d0c0e0a170f0a1a150319030201140408190e0604140312090d03110a1a01140607080306010807 64
    0x8004807034a050a0400c260040200000840c20f8030120040d0f8803014400c58070301c4140c06000c2d5061501e2550101d894103404070707a841e6070210610300c0301c60a1781e41a0880101134401d0040e40420082300301401d040d580594040401030b0000c0c4801c1004c1c80300e56085030f040a03c42040080d080c10201002c1e141440220201078000000c16804141800c00c038411000c1e0316842011141300900d03403121345548400040004110089032805041c002014500c600d40180e000514116480d80040210307181c40c4042c2185600c00c2c0310144500c3c141130702849420201e00440b421740ca05072400e80c4904a40e44201b81000c03084d03003541c0b40120286440781c0d4000507a0407000301020ba403190388016440c403000d00c2111045c46409003408881000d01d001003114400b4001030400e40d614000c0380c50a89013100d180840307200c54081c81c503091300043d44514003c9200c1c80d04180880c0e031541040038500790300a9000d420750003004100f1580000c56a1507083e00d600107000d1900c894903554410302111544042518 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 143550179 1250 143548929 143548931
    0x607080a02130e0702010b04020414040e0a080a08061e0306040b09010b040207050102070b060907090e070309050a0b01090501060203070317091f0902030c040b0916140c011a0d15090c030204 83
    0x40403c014074850503280c0280c3c40340d0b00a0020701c1c3c620b030802c804c9104620480300d000c030800c0382c1142603040c503130850880d0364242c1064403403000240d280c211195002c1c280040c00120700508000d10b034908420b42c91105c420f81e80203e64058a48000f19940d120003810180501c02008001036a0b81c00035080501c80000c050b10a54491100e481d0483c042c3d0050901214600d16000c0015030609185a0451151003a5a03d03202c0d250320b40810440d0798000544098205034444581c0b202041003000003860880c42844181e50640c9045c10031801c40d00180c2100702190802c01a0001003584040c0e03134000c41700c800c0059540c070f803a8002c3c0f0354502002c0001c0d6400407890050701301e442d602103520105040d4000d0b42603ca4094850303003003200725403903007810f10f5201d010040400d40100145491a04510507400c01400f02d401640d138101250f080810a4182d61391208462111001c201c0d001c00f6410700e003548d5980740943d051f0b42e0080c0c101c034100480c0b401c942d0b40d0804a800c1c0b007107400c03208004540142c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 143551429 1250 143550179 143550217
    0x10120f11120606090f070c0f05010605180a05060405130303020c0f0d09030501050c0313121710030203010608010c050702100e040f02030612070f06031e0e0703021002010903020607080a02 82
    0x60788540714501118814407400d100030014000b50080e00305280308081650f240000005656103141e8805140b2a054800359030314040032030141c45507a02c2d26108018022202c02e189020010740c8181c42d00100028001c6017070500344400099002281d00a003549820090b0701d41041d2201d00307140000c00c0c01c45503041e100341d100c00e100300d41d041001841581d00490081c065a50f60710303040790080c44255166205003031640c5080000c59001c111244a0801500d05170505501100c0342c0d8403040d50682e04010b06a80611007042185001d204580c000e10396440240803c030603044000d4402d019102002c0d019941c09104c0c0400700f4898401d0101c083c2d001082000303120684401c0200a40040314028010a030300398003548201400589070080340c148001402440d42031181c200c011307146186600700d088403400300204181c101c0d030240016101c00c01004121540c0f65004100f54200c2d5040a0415645428007032000700c1e40c04150964440710340e0500d0221502e444000308000c0c4a4044e10700c3c88144541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 143552679 1250 143551429 143551459
    0x51602040b06030a0e0d020d02030915090904030e030c0a030f080901111014070c0f080f040504021c0c050c15040f060509070501020c0105120612030f0c0c0910120f11 73
    0x58028405c01c1498011103da005400e00d00b40d9513440e02031000800b5034028071958640703141c20914442c1c40d8114143c014201035011000c1525080140c4007100854031010900380941420810074076402400c64030068654515114441010078108019101c0c8200058440403640540b561000c3c01c824881100c84204103608200001c08071020b01400c20340c421004100c1d80c5d403003480c0240300d00f60000c05d41e421022082e0b440c001c259010042e14034406000384400603007656140301a103109100000c0b010480400d8016240c202c03010818010140001031000c400070035000a80d60f200c6403080051203ca03a01c40d41484000140021300040041d41420300b0012500b20100d01c90040728820303001c4070151418440155403d000d8620001480e8104000103052490134082a40703202c1c11100969260034080450b21600c1d500c0b105a50146520000380700d0218204207451070392111001c6010b8841354104840c0703030001e46488201070040c0814410341c42c01e2140c0c2908031409500020f00d44140749800c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 143553929 1250 143552679 143552681
    0xa0c060305060312040503030307080a0b19030b10060203040612021308150a0c0c030810030b04030809060a02130605090f0604090605030f010614060a0306090c050903010c020d051602040b06030a 85
    0x40b100c2c0c5001c0d0150743c4a505250840070b003035805540c030082c00740d800e664600004036080c148c0100f070001031301c3d2a8694002140c8409400e0094a0f543c43c0b08031143d075086003440f490007080607000c405121004c1908100301d50780407050f6400d8441e1450900c805944070881ea10190241c00500c1585040e81d002c00120f901c030000d10340f82d10400c444455482070380d828000d0343c201e0704440d075410b02003810706a860300020304ca010a541d001400d0180790080c0740e140e0f01c0c2c0d00ca00c010216402c40204107400b082c465805801c0207500c0e41302c1d002000a5150032070700c1c2c8004085510901c01d000511401081030740150380c41c20040c1e0390509015000d50303112a603c0d000712015044ca441024020701501c0b0300700d02c0c04003040c092030381a1101c200850506006c10018880740d544268946401c0595910300440c0031089c6011340c8496220556400340c4426840040600b110f4800440c001503501441c28040e80c0c44d004020350f50ba6848010b89860480c0950005c100501088000c00d54444800010450b80d00c0389 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 143555179 1250 143553929 143553931
    0x10804031e09050306070905090a0b0607050a030e090c030405030414040e0d030c090905090a030e062808010b1905090319080703030612170306060d0e0607120c1b050a0c060305 77
    0x3c21400c56210341c803658002e82d040d000038018185c00019441c000380c00400d0f1a0403000a401c0c1c060311103072a020040e11b0b020300b00003c0407011030010704003058035400d0389461010240c011810103581c603d1070034a981d40c01e40c0ca100e2441281e0002101822110007a561940700c070035151405810340e240b240803008024000c001240005011030510b60002c11a0082403042903c202c0200d4000c1c41d0180c1a52410356001d1019059254841ca00300315031034002c3c2c000105215a4070002240c001603955180010700012416044141100c400340705080260000c1d902568010445d818844ea852070400c0209092600c0c001041a909459404d10410410321800500007640a942d0400c04103803140a06282c001030190090303c1c1c45081d1a0200d0010a488021604060f00405040c503107801030f03500c10141c03400a060308002e03800c030108101002d60442422a070101c0050400c0042c0302460742d0240812004030a44200c420042c80010304020b403c200074070b1215080007581e501965220402006484 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 143556429 1250 143555179 143555189
    0xc050f0f010507031116060b0a090c02010606080603030d05040c1703090a0503032701030603140309010e01090807062001020408031b030310090f060314030c0106051806010804031e09 80
    0xc680320019000f20711074420048420a0301c0780f0103240c0303030900c8410486c80c2c07000803065451640e2241407481c9690f803042c01c3ea0041c41900c00110341c23260b0646000e400c64110303a0101c0d05105203607080001c01c1d6000300440b15048010800041c1c0340c1c90300c0c00c002d050800c0315007020016011801d04092503850000160401440880e07000e0320440c2c40c1d07010306407a401407000b800b0f0101c41f00341c00c1c0d03020359036100200c0c55148810700d0f00084031540c82d128202020311000818010786c000040005141d40d0200c013806180c2002e0905d194064641920035a0796071f414440c84013004910102408009115074941206103074620007552511386414500d43c40c2d500c40304d42c0401d41940d590741c0005d001404001e40c0c0c8995503a0300311400c0d00340360288045c0500b0382c000c1c00d000441e94644c0084000b07121310810306c5000c0c0d0f10100450715905564032450131900c03150449480b8070803002c006082d40990680641c1c6c00030081ca4a1080b50300c0b28a01038409076031041d003030448904140c59034500c03658000302d00e0040300c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 143557679 1250 143556429 143556431
    0x30f0a020427120507060c050a030b04060302060f0c031c05090607090807090506010203070c0602240c0306012604031701170c010e06040b0d0e1501060c030806010c050f0f01 76
    0x10b214400030800d5007072405000030465022408403800310321410501c0300d01519600341907181003801d0340e40741d0072100074407c0503011803808070f00908007039418400d0a0555100b80c400b001001c3c1150006800b50281d1001010754030300c0020951200a401d005480404040c101c890301014414001040030380350403900041d4610500c40081c620318400c260701c10840b0390b0900580000f500f810100000740c04000d254a0562004214001c0000d0030400301000828060740a4034128440c2d41070900c0503001c0e50034040b0b0400c5030303505001100001100316600201e00f401c1c01040b85900c01c6218161512010708443d50610343c0c1d0801c414180c0286e0798600d00f82e8040c54103142a80c882c54075504042c0d226800c41c0c85075214440c40364665000714100440d017140206540d06040e5074042d2404e80d41c1c848841c10000d9a114602654212020410046080040d0740d04503140d6050072002024000b00303c6014040200e14004110f450f401091459a41a044002d07169044101e6454694812800821503001c4d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 143558929 1250 143557679 143557691
    0x1030204140c0304030c11130b01020d020f030d020d09050303010603062c04030c0804081b0a050d151e05071e0e0f0103050a0f0c0c030908010c0804020d060b030f0a0204 74
    0x101c00d50190148a500c02c202c555046032680d071012915812054821980302500b280707545603e44d21010244e19a01302240c4c049903c0080000084c2041d641109403c159803040c40300340e81e5514040151020120701900040e120f5030007221803009044142d9000c0e000d4000000041640d41d1701d900306006440d80450241d0595002ca031030304480f101c0d000d403421240d03511113005c9400207100d400040d58103409001c40b642001e13201d402650a10703c05860b0307442d007424220f20154a0b810481c1403003000f0801169051740080150f12051403164202207d0f0106075503940c881c3d000d21b100c1100090020164000402c040c0ca03140300b02602029a00c1001d040b28840c0102c0b8010701440303802001c0c103d1781702400c1c2c4121000341d900190081e2002501e0240c00a4172200700d0403106041c3d106850724214680d841009182141c2009800b40481390850220359040802030102c058205030b016401c07d505469061501c0b102e41000c0e401800e10a0520350306008580e41051960350028034509107038002c44081100d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 143560179 1250 143558929 143558951
    0x190c020f01050f010e0402010e0d0b010909021203030f0606130308030a022502030706110708060f0f090c01050f0901020120041502030403020d02010e190905010608072c031207060501030204 83
    0x203611402d100d03503e4045d40c100002001544901c0c04800e01d01406003610024000c01d564070790b003800098100c0c0c84035698450400307041d80b601000c2d954545001d04040e51640c1410564041442c1c030041c0b01e40d00440d800144123503184e001e6075800b002503411192243d221f0030050400d00181d84440d951400b225600000c000141c0400c0f110105860380c020000d044051034100251440310034005806018040d22000280c9000113001e020320403010b03c1c0701c1e42007038600f80d86020001c540c00350100003150b01004140b0502d036045012111200c4d04031a031307586c480c0e00020040f8058110680f0041502d90180702c6100c10b142c0303030300c05802502c1c0c044440e0b00e0790705030070a802c076503902540c0b0000c0d5119108006d00c00144d401404400301040700a0112403400c03c1e200c0441c6a6900242d1202c2d42003540c402c0100308003584007181c19000900d601d0007201c841c0119400042c410f0a680e510441005c1072100601d869508104c0014450041c0d1070041d02c50100e42000d00c0189001d1006038001c40c2042c1d0b85d415 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 143561429 1250 143560179 143560201
    0xd050306090a1b081503031b120c060c03101706010303110a0503031302041103040b09010b0a0e1f170114010801050103030c080f041d06040c09080a0b190c020f0105 72
    0x100e03a00f218212090124803401044815420191400c48002c0244948004545080c4001c00c03806558104004060040b6131070140b4040041c81d003650409004d00401d4000b40012801070317004080307000d801d504ca45a5030b01036804e03d11035030f000d6001701d4034a0a00c005003080108203103049074003940f19260403404101200c1d840c0d8090b280c1c0201640c004000044000c0d10101c428440e4500241002079014040c0c4080400c0380d00594082c0d8155140350200301c10580b090044a034005020703981c01101c60f240146004446034064103065912840280e100088601030302414000c28001301031310a20f00180f582d140c02056000c0700040c84080100c00860007800c140500d274100d940c96602c00003034a4107a191405243c10000940e964a242042700140691244003181c01441c00188034203500d0502c03a003000200c1d648186c0403001c1c0909004100007031000414980f048942101c40104140d8070050b55a4441c0d0624290005451901d02802010740c2e0000e81681081c08107402080f040d03c4480c00b0b48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 143562679 1250 143561429 143561441
    0xd1409060f10060c0609081201230f060307020c1c140309060307050d0b0a0303120c0e1e010309050601030602040602070b0c0d11030d060b13050607120f0507050d050306090a 76
    0x242c000802140400199108255400e0318500664000402c2c1440c1d950b600304941c0001c0c2d4843c52151328400512041c0114106422140142c1d90a480c480000c40041001042c0d00d80100384195404800101c0d40742c001c1c4054040c41c080140f0840100303550104074110180c1c202810780d104440f0640582c2c10340c070000116011614002c05950560342c076010100c0d2568000201c1002c80c0f601c8000d5604d56480340b4808030051031003500c58804108a40215a04903030781d0071400401c1000f42e01c07603c0c42a44866500105003c03005400c1c5103249424001a009008480c0c40100503100d82d100001c24407180703501800540d81e45900742c0d1022a0344512032100350041c18010201c03600460b0034101c0c074901448408988400510039203082401101d55502100c40c585e210921145002503101a10000180c649015003c01c8030410f007000b449894412242c0404003aa200740070085016003120760007074041e502c06550007400c4690106081100401e07a41080d9800c5000707110303050214010348182c0c083c0b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 143563929 1250 143562679 143562691
    0x1501050909180f1b10030212062704050a061506050d050403031d0f01110a090b0a091e06020c010903050303070f09050301140f0a0605031f020d1409060f 67
    0x8169032a42da012000030458015104218464400c5032145a0030034003060301500301052030b6030142405401400524801d48031319000309031041100c1c024041c41e0380300d42508894251000b00c40c0d1161030b0114240840c0003d02c000000811a080004104000072104007640c07050605001c03144175401c2a03507902008e8058040452410720015000001c2a88015031141c00303442c000c2004620800d0000f14418800200c8105400c68940d1140e00a000d001d0303682400e40b054219850614204001800d59a103401100c592120000301c02c0b00c180d00c5902480003074034914202c1c101c00e09200041559441c1584102409400740d142c507681a50b01401000c401c1b80c2e0490051491035644c428102c03402a1503200000c10b00c41a40408110303034a0900c28802d00268800c5c8089040c2080e01a003038607a10014010245030b4100f4405005c0780d20041581c28091640c81025008400d02c032403603001038002c00c0c0c8040980c07403406100500c0c5240c104001b90081d14604240c070019200c0c45a50040e41000307d0700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 143565179 1250 143563929 143563939
    0x6050a031703062d030f0616030b0310060f211a070c050708070323070b0f0906070b010611010c05220902070b090f1b010f110706050315010509 63
    0x40d082108240c000440d480a0000c21340306000281c00e10800e4180c00d030718010100d401d01e4610305003050904200786010410780400401e000e142803124401e000403600d900d10101600c076078940f44107841c100b00054020b0700b031910a00810740c643c454410303203885c240701d850244032690480c0300b918102244450300c22a00101c1030420034042400300895000701505000c2008280b84103040420420b00c181e0b40a44068009032656600e2b50405550f10b104120440400300d02c0000c1203032288000041c25002c88140e403642e962241d42c010400c00e61400390582d09030300280c00042c032800708681001d9881c140c0e132031303502c54072414202c1002003802c0b200d180c4600c0d00810f0040108c03a82c2489800070344812540034290800d00c00340c03140c040c4801c1c0e800c1800100c0e18480040b007030280800d02880400380142005000704401c2d81c800301c8848600e5000c901c0141130040c8040407040301d620448203e600d241031032044580c055034819005000e5407040329200c41d108048041f1040541c0320300304590401c800200b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 143566429 1250 143565179 143565203
    0xd0e06151504060e300607020d03060e010501080709090c05070b01080a02090105120f01020d0219020d020a1b0506071101030605011107090e0114130c06050403050312090705130b0406050a03 83
    0x5105c0c1c10f0f200015414101c20305442c1240040c00c0c210029552a1004400341200c1e007005100a494440d020000c03400740360500005000c4441081c0d04641100c80910f4100c0c0a501c61841c1507502415a1700041581402e08004054035a042002449024800c820030119a0703610340c10340d5241c030003c0300e0082d80490b041340100070919003005070031800c00c1c040c41038800001c0321039034003403c9902590040c2d0f400c0781c020580c1c1d40d50b0358281803020501d08650002e41212070785000c009440e9222400c0040100000c1e0341d1581142c0000315154024041c044d00d000c0d40d680c120308001c03c8117072040c1c507081c1c001790401c000481e81d0b51055000c0d0b1009030104004000940c14241c1c0c0101420300f22019070255035840303140400015800a070f4900605103151489001c54081c20020301d00c0f07041d500704500380310b07003003104100045000007183c41102c4d081c41044c2141d100c2c13015580c01c06280c1c1e4011540a1007100054403107105607400210180000c45040001a82e1350050000f51482440013400d01b0103104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 143567679 1250 143566429 143566457
    0xb0a050c0a14040b12100e06220902130e010614010e0105071a161e050301090b190602030c010b120303130804093206030c060d0e0615150406 62
    0x708403040310001441c85410551501c44000054002d007015805d800b03031940034041038810600d5190060110111011030030b1400b20045448901c1c10b0300301000200d10740c942d50b107001403103a10880c489640100107200e40307401000004c004d08a600e080080951074440300099044103803d0580180d24180c40390112800340c1001914076805c0564251031035880101800080180545c0b4a8400c1f4548420f20000189a000051031043c80c4c5040112030100d000300c03ea641a00941a41d0441d242c1600208136001000041002000f000c0c0b03c0b03820103002c045d004990250040003500c04695004000c10110860900300090503d0240010055400400100b218034001c003038050b40083c0545c18070f500d410b5580c040f080481381105102101c41000914001140c83c0c41e00c26011031800381440c0c1802410480002915100900e0300144038810014032412842038540100d1555100345040d10030501e800038111407103803400601c0f079124080380d4400540000b0074206590940d08550b071b920642046c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 143568929 1250 143567679 143567687
    0x230a051c0501110301030515011d0411060c010e0601081605240c030a020106030b0703150603020901111501140d030806060306040612060911120604020f010306080f06040b0a050c0a 79
    0x1184040d5074a54036042500e1105000900a40c0210710031401031011180700700740b001540406030003002203c041d04c0ea42c0c1d8200136007103608075003094121018080c0590340b600060310a118001c1c010000d54201145600003010104003207040380e5404041e5003100d20758411021114406000d101d5101200b440d05241d02c0712a50918503514042003021803512015020440c65904011a00c10060b91203102c00e20402000e032000c41c0c5c12016034141071042e040142c00c2d211440010f80a0f4004056000c00c0d0150107130709c200090350410405006403040c80188041103402c0030320074001d07500070b2080c2c481c0342121414111342075000c481e0140e8a020258844008000340d50380080c0c81c580d407160700d0b2040805c020300e20b1100c482d07049110b040001131102052a00c031030110001c58400d8410b40d84d0140b40c594449000c5013940c1c1c00b50b4103e85030048550302000507402803031290010460707403045c44c480141c540e00014906006501521b90154142e846034680000d998040398005040d05d4140480311080b409 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 143570179 1250 143568929 143568979
    0xc1507030309050604060903030f02030c160215040e0412050c0703030804081e09030606010e1c060e0d1d03061308031b0c011505040e0c0d0c0b04230a05 67
    0x440e1401140c02c00e8141c07501440c10105450940d035407544c4180420400d605403042e888500d4020101350308515104172851401c1c09907201c91200e015811940c03000319507445030044540090b0a191903240c0303460301d41001d0b12090483e000c8501521a03520a0192805102a40c2c40b1100700c200905540b820b44c0c0c6c00b01d403110800b51046895240c2446401038040302005d007501044135080344251a400003208161802c1006003102d4103224600c8888410380e1151f0100341054080f00c94035141483c045d10703100c40201029031440030a4015411004c1c0451307406650707600e40d11035003003114517501210002c058540074142c8200c2900d9400401e05400982e40c080519400796150030480414007928205000c3ca81c0801ea60944507551030100000b0900e0788101c0704060303c802d44007004010b0441c4d4900c2d50700d141000c03256214601180d090303001c0103526425500a07280c9400c082e074135595980c48100008032810300e0b4480020b21602d034982c450400265940450f00028002078090003000c0301c4a98141d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 143571429 1250 143570179 143570183
    0x3060b1804021c0f120807111c180303030b0a0b0c06070e06190905011b0c12020a090903030506090f190515120c0a0812091306030f0f0c080c1507 64
    0x42e0048801302d10120802d51080f03020352543d1001e5005280c005101e204000d0229040c00310003195840c0c541d03030001783c0000d058000e07441a1480010030b0415512071031070700d900c0b41352031412003008000c16178150400000404241c8003e2442c41c0c0b254003011040c0a4646102855030000740052081c51080407090103210303016200071714028050841074070003010300c0401d5000c41c40d400c104021550384400d00c0d0012126480f6034010300780880d0b842440b500034a00c83c07240e001e6120030200003035589140d059001441d694500b04407000301c41c90701502410080303889501c121621800605827041460b400da2003000d030703004d600894906144420000f044080d044650306410355200e102070340c480c1c80c4072608c04000310008040344210b1104001c1044420f0f0001c244642007800d0100b440d4190707205885800000300c801c2e102100100d49084018215a4005032880c2e15441c540424004403110b81302c02180145607000c60b2036281d2440f00c0e03550829000050308080340c038201c1c40010503203a014000c114 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 143572679 1250 143571429 143571469
    0xf0c02010c0204050a05010510020307080717090d031d0a030201020d140d0608010608061f0b03040503071203020309070f0617092e0b100503011e0f080703060b180402 73
    0x1c6078640116044400407540d07811020f039102c0c0148080d1812020701c0317080c0e4100d48011407038070340703565900c2099016101d0001c1211480098101c401070710902171300d102c404003800d0070340346c0340c59410300a08901c49401044002c2400c1c3c030300c104490406461182c2602c0e0181c00800180c120440103c0300522081210003540200b802014a001444d000b5100104115030003c41d05c903007002c510504218025100802e01100c0e8074403010300c034400d00e94410850702d9613200582caa41c0d0710f0a120b800c501c5501e200074088101030750035454650b0145d01650080035241c045a080c90703180d609406140d1801c3c0114400300d40240c0107604c0a5040d0950282c0c801986015540c0c0c10002d004401c60902c00c907240c2d1402c10b4205804040b80c41800c1c4504a00004120f80700c66601c243c0c540c4c0602188010701036072206402d80310010300d420380441d420000404809031171100d0607913208101525120300303010031200c140c00d1503400041d510706074600c0c5030408012910380c0d1140e00c0315401c101c42c800c0400c00301c000e11 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 143573929 1250 143572679 143572697
    0x7050d0603020a08070f050d0b040b15031911030d12090204020d06060507031206060e100e0904050f010c0801240c05060705090906041404030509010c02060301080d0e0603070f0c0201 80
    0x580f00c0314850b80040824000800300fa6042805040303050545800c4140111246c10b03020010546000d081134100d9000380d88902c1c16101c000707404030b844090045042d00b51281d21213102c8440802030709044031030b01940004100c2d62407901019156200d001c22a0b0020f040003540c0d61141c50294052495103100420051511400000782410346a499020342e000c01c4010400d101455041003c017216800100c4003013025038103085c00030f00030240419056000d0065003c4055595000da01514a441340081c10f00300a45060f00e802e80d51600784a507101403a508002d007690060b03000d4102181a140d0001c0a001c4410804020a00411001d0f0f030340d400f000050300c0c0c4800464403e0242c903002d5126a51580d42c0c840448003030028040004c3d000364010361400c0d94001040000313901c2180c00603490f1610942c2c03400c100c0c00403540d40c2e082240181d4041000000001d058500003840d02c40d004080c1c492004054900d000c0000e00d0008a6644011444000603083d500748641c54110070b03071384141010500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 143575179 1250 143573929 143573933
    0x2090f090603070504090803060901060207030503030a0b01140c0703140703110d030201060b0d0207050d05090d020103050c04091a130b0d08030a06090603080703030e070b040e04061d0607090f0b0307050d0603 91
    0x240c031b1007561306035503026000050110301e0800303400c45400741c4081d000402851f413031992020344e20310004200130070140e620f44000c3d42580c8902288041001d001c0103464503018020101921100c15100440700410300301e003003009901000c148401101d4001e030300000030741480c0c014010ba66800100480441d503941c10007203920661800070f41410070400b00c0c010f07101c143c2e52078507524020031030004c101401002d00c91420b02c0e540e803440c0071290540c20300e40803c0a4035042c1e100462030043d50018006641050030906003200500c04081c80460f04a404030219035801c641d40d4219104028000d4103d144c07503001001191044e8011a040400342d1030000b03009503160403160450305150011243d641000a895003810b90500a2003400c066940240c040e8170310300484021a84164130844860500810010702480302c80d51044840782402154012745051080610f600d601c030485032800410788080300444e070603d840c2d41400035903200e001018030311303190b4010a990682004041d07120541c0c6941000c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 143576429 1250 143575179 143575181
    0x9060c0a0b18010203150d060b030d03020a0e1e0d0305040f0f06020d0206010503190f0f080310140f12010905160812071a0c0d15090c020102090f090603070504 70
    0x880360140180392294182101031140740c104024001a482c1c2c01071050008021883d190015440e01c12220b036065102940350a20180510f94415a4180200080703100d225815400400a0084c603035528201c1800706810000100509a001c1c08881c0d00c6112070021400c00c496a011140e000e03007809410305581b1848500c02c01c0494005403503524a81c6020400203404005050581d65107001410043d81420042a0340f80b0740021200e03501034a601086042c0030f00c0c040300201c003a42203468160568418100401d140c3c0c010368007214408262000046d19096841d05080c01010040808003d0084603040050b00c480d070b95421241ba568500411001900130442c010b82c1040d185038240700340e8a41510b25003840070400d48600030040030441034000071006076504000c0c1c41c03442c000010701e80740c802d0703103611a0045c000d14490303462500701c0340580c01404800741c2c1c0488207030070340902035100c2000c0d040b0300b86c0c055160035640100035280880411b29200034100c0d4884809811210034544e41c00000d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 143577679 1250 143576429 143576443
    0x1f0213180204031203090218180102040b0912030301180f06080307050105060405070311070807060b150403050105280b03030f0d05040209070912080313080703020c090a0e07090209060c 81
    0xc001558001010000c0100d15051092441d25070300f0100566502030300415040c209004011005d54041000104000342d44a118400d2541e610021920341d500d03a0740c4c5055640c8415641e40c4070b03d82803001b54040405c00800ca0341640c0400700182c4c520021485040050001162000c4480e40c0381c802c041501d0508002424000d8000c1c0008a60b604054042c0011036030082d003013008040c1000e100d5160502c040c001c589101c2e502000c0304e45d840300c41e802c011004140a1410a501c40720700f816602c664000030000c3c0007520f0046c4000c0001703880d4203d18405070012021413564038840c5800000780020198099040341c6400b0703050b0ba00d8880c8003c0708050300d40c44164121202c41c1e44c0d00c240019400d210380c0135503000810b03042c6062441d06103207407030103d000120303401840e20b140000041c3c160003514501c144410760000820303850724040d1402030b4644c41c00001a030f008900c1c1000007a504210b500504010380d01c08805032046908252018019501c6403c14a0300302400b0007000c0d03440c0300108044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 143578929 1250 143577679 143577719
    0x804030b0a02030f0609010609031415070f0210140712090b0a06081e0606090702010b091003050c0a1a0703030b0a0308120109050411010c0f0c03140f1f0213 69
    0x43e942e242c0560910003004c0050281c5000300b50002c0140000e540140c041400d0b41d4020080384200500c4054072450110300800c40006030712404180840701c0d4000c0352400050034240c0a450251109200e62822134241c0e001e402801d41c81c82004c140c0c424040e020240e49000c00307200120b4245000e480391202140b0640316400010380d0350708104510f0006003c0d00010307000e6010800c1054440c0700e820759440c0e03006800d580c031a6600d1008114684d0003540103071440300020340b0540e82403402d0900c4000880c0588015600740c010607803101c03c20b160240c01c1d03500b540c0401400114141c003209003545a0b4020281c202d05140d6076611017007141d5600c440c0c0c0c4000f980320f000f502d1b507103803520400d80e440804180d0010034001d042c030043c030002948107682149590401e1800b02d00c508500d04190303600c910613407000340210f0007203030010050004000024600f004842c08440410080b201c1c0e165460340300e601d0802002010003445a24500290000c3c100300144000c101b032541d440b89842c00c042d10702c6810f1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 143580179 1250 143578929 143578931
    0x11010e0708070812070303020f0c0601180606031b08191a0102010605150d0b040f020a020f010e1f02031f080c090a021204030f140403060902031005220804030b0a 71
    0x10410028074204620409856004050a5980c000841600444c02030b044020141038011480c0d03084030b002002a50440049041200c1007940c0d101d0204030225a52040a0b00080c140b02001c20034034000e00651003496081c512024a01e034002c1422a0b00c0300000d40303540d86510144e0b502c4800780c03806000726401000321840140300254140000380c03c4800c3ca40c0481e000308020124022244804402d6906081c0fa1071408202000d651001400501e4041c04811b003252000c900074030000d0f40007602d026400200c0c0700030445640c0d100142ca55800d000c2744100c0454160740825944544d954010b903420440d4a0540c21118141031004958515030b034000445c584e100c14034455084c54107000068100c0f40c4244114a81080c11000d60040080180050144501001e09041c081c0c4110300c13070343d85a40b034201c41035103d503280d240070390241003142c0041e48648264a00002c584c50188203e60103000b04040100494032445400140001001003c1c1c2d0105014040003001c0f40340c0401043c4120702000e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 143581429 1250 143580179 143580193
    0xe0d08030a050117102304080c0106080721050708060702031306090b090603093d11040302190506030a0203010801150302060a0e0f030102070b0f0a02030f0408030711010e 75
    0x401d00044850503070110320360200d0708081d800c031200301003441440d01140385030118205011483c80f00003c105008481024240d9030100001d01007403402038020034038814000e000d010740c1d920359a0740d125018064030038030304030b25218040c00c07500302640b006041d441902950007280d5100205410003800303c0e05880541c1000a041e2600400004640702802803030600c02c55103418804092282d0080c0103030280140d200001140d2107090400842c502003812440c8514200c1c4102003280100c0c8044860f5001103018101c011596241400f601c0302d01c031007510300d1a040034616020070920a0011080e060901e040c0400402d0588506000f14490813203500003581e213514103c1d00c41e003102c41c00c11a04d5810b030036240040c401640e07060300f104d9100c1c0036490f010709810340d001d00042e90550070000300b07981036100103550000c000d02c101582d441102e903880b000d50541d80d10302040e426440101e072070040602c80c02d0000b400246010019642000f914503110744400780f400c0d00c460844410401110341684018 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 143582679 1250 143581429 143581441
    0xa08030c0c0c030a030e1002010c05030c03041e05070501020f0106031104050408040b1809011d0a0c051b010903020d0c0c050d060f1d0d030c090b160507031a0f070518010e0d0803 78
    0x2410700c0141000c0c600c00ac200107038200c40000e006010280001800c00d2001001c242840304042c3c0690005074510001843c0c40346500d009583c0e400c6900c02d1a01501440003000c0021b103041c071610040302d4104c0001c08250352080c00300002010000e00444a2900c1400042108003016014000d0a60750500038400c080c4d0400410101d040c059000c007000703024018050700b03080c3e4801c20503034006001241c0030a10848182e002d566901585a00014481148440344083e84054000590490080d02981e4400c00202000c49480d00340700e0000d000d4182c21070040000d41010f808640d2103a00481c40000c140c80c00c0001e41007a10740d505070b0880355060b03081e0104440501400320044100481c241003040542000c1d01a11261007842200902c01021414214559840512071001e662007001ea590160f207900d01401c59a4000115842c0d0042e0000020480c510131004c4c24001d1a083c0c507410708245000341811880c3c1c8c124440c0f54100040c1007460711a80c0ca0748045658000e2240801603102d2400e5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 143583929 1250 143582679 143582689
    0xe03070b1b0405030a0303050403030b030d0c110109080a12141206090c0c0c0f060c16090e010c140d0b04051005040b060406090e090a2f030a08030c0c0c030a030e 71
    0x512691508071820403082200b5900055009080380e81070038041010360751402c080d00180120b0f40780503090b018080340103204c0d9602c04402d01c1494450b0f034500c440034640000450750760415020340744d02e6030f00c614000001b05501080000c420100707881c240088800703604980d030550f040341c02012140c8501d8030a0110600d056180e80358070401016401d4145007400480d1548c1b00c1c1030b014554010250103040c070801c2d8030340b041220039052001040340d04428400004c0c00504042d44200c4460030b184c80081c00d00c40d241030007403002d4400b155a41d00384005240b200b4200561040da201c40701542d6441c280302140d1110b00401d8803d25401e070603c004240b411050109484925051501c102c90400080c03000c160449010010f540040d0440302c7d5980d00c059807a850b10000c0320b4060080c00342e50050440420000b2080700b0002d0300500500030080500c024940c0d501550030005200d00c0c42030001422642d440310290076400300510440301340d05034900c007003410b00101c00f84c264005144009806028244 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 143585179 1250 143583929 143583961
    0x260304140102011404081602040603060c080f07080f0f0720030a09050a030506180a08033103020c010806030102070b0108010515030609070510050c0d120507020304060207030f0201030e03070b 84
    0x110303c4d040b01d4240703065682d2461502c20703070040c00076100714090fa06040d500e50b544218055030f8080c13400c0214002c40b02d005800700d201140c1102100c09c5890014000c00d02c00e071941da00800000200d03540c141c8a524144200d058000c0c518000c00500041d01803102c1214a402d03100951600c001e5907549a800c000200400e00d543c021a02a400a0100b080020750000380c06500a844a6441e0b942c103083d020002e0a010b44050007500948020081c410307481c1906452651003d20a50599400c0742c41d42c07200c403980200d000c0c010b00543c01c4003120001a501660f90903901c11002400145803031600e40c4da50742c0d641020380050308070707070b5403101042801c40710300c026075200c00303001c070002d0400b464100b01c05903940c0c855000d241c0c01b0707082c07a080100080b80070700150b6500400c0350095404000c09120001c1040d400544001021424940441e02103400402150180c9130709034060090241107440d440100c0408640403410980d8070503c2c41c800c040184041c05000d44100b64202441c00c00301084000355907 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 143586429 1250 143585179 143585201
    0x2e03031b02060909100f080d0306060f0203180105130e0901050622020d02070c09090302060a0e121605030c03070309050316090b031f14130503030126030414010201 72
    0x41008440d00541d841d41c003940c0000b4021540d07826650b880d80301d8004e1030420f9070300520074401503013008118004041500751001c83c82e998200b00342c0d03039100b40865204031002c1400c070241c2c008000c2081d83c00e00402201000c083d06040c503e1034150450f15402a26013141d1040c0112850343c4184441202c00707005103a005001222202018030025201d20001001d808403980d500f41d0002e01d00080300c140d501035900c03c64000355132442e02955418008040c0404000842c0107014150001d12022000e100e00140c2446030350007041301c01d6059441c84e0302544001180000d1000e00041e000000d0303400c100510088041102450312100c507481e002d0042480340e042a4400d820500c403080280c18800c5040003102c0c040c0c840410001d0240000c07038240080038001424a00d502c4903501750850745030304140c03030140140c0305840241e03646001554602018800041003900100010002c071140705e15600e4005130030303000c12400348024800540c90365110ba40008081102e400c4890110740e0203110b000d400384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 143587679 1250 143586429 143586467
    0x16060612031e020a06140604050708041509060f0c030b01141c050a090b07080618060d030302031909121e12021c051005090601020a050d05032e0303 65
    0xc0e810750340541884024000d802c0c110784820b00c0c407160540b0820811200a401030b90410013020310b8151405845c2c81103131034900840c01e142c04684940e100d010124170698003c4031400641103010720701c01c06030030f15201c282d509035180c1490700122440c40c8680b030344c1e0482c5d5450000307030207551200141840d000d08000c00f001c0b100c00d210b041c6a05041c0040d01118039400540003c0c15650117180381c0040c009028007418a0700c082040240030b03034000070b003d40503000c2202c0003000005000c2e2034030200101151019040301e00700c1c61100019001390082c503080204d241c002c0c9040802d0400050465404841c140c406502080318a821242c000503c018000d07d41c81c42e4198110a0080141c40e041100f40ba080b4402d0f400154000c15050303114000307c0400000304c0030302103030801c0c4d881d0042890860154910401940c1301040140d8000607039410301c01e5100010b019a46400107040c0d80680006005444910203401e13000380084150002d5580500b05114240c106410348c1002400c04607010b401603490 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 143588929 1250 143587679 143587709
    0x4140403020312130b090d0908070f1206090206030906040b060915090a0e010609050405011b02071e0506040602060702010605010206060f130b03010612030f180b090a0506160606 78
    0x840ea0120483c2e80c0050503003001a416121400309038152241e55201421314142c1005014440e500072840c0c0511024681d1072600180c0c480b904145c4503400c901c00c1a81800341d81200300311406040403c002600d029000006100b00b2540210b191a4000c80d0894040d4210108100030041040001c581000086e0340040582c90030800c0c040c410258540d009102c0c00c0d04c1c40016080d5000364100b0a4001c1545000740b14066899081c040582008d5404070381c90b5003445260170141c001c0d02500103a04109500030704080e45012080403560b0960011448450282d40000c1650380314000208014285540144070718904408020b08440340c079003081741150400014440035585018200030b81ca00103d0780c2d24107803982c8200380c000600851500030703019400c100b800198001064401c0c1203190181e12007a080c1c0e42d203494100c0d1090304a8a000c551002500e006121032180c4e003016100d00440504110704141c0c50b000051040e403c10ba60794003090480003040c1c4100303c80d40c02000010a1a0a0700004c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 143590179 1250 143588929 143588933
    0xa021b0a0506130218040f050706030b090c0f030601050f04050406031109090d02100b03030c1c1403090604061e050103062c0a06050702070308040602010504120c050a0602031b0c060105041404 84
    0x4641c9503071401c541c03883c00d42e001c00c090200b003060140e450b0340e002c23045504040d502c2da0082e0190000700c080f10712510b00c20000440600588080b19214405001c09030700e5030b40c5400054030340b0b800500c1d40c241c1d690400d010208150b100c51184a000e1802811585c1488046c00c0406c00301c1d40d40140300b101181c10038a900c681451b000111002c085502c45800700d00b026010010038a9030081d6031000392030384030340802060b8801000070560541031083e82d48000001d403914103100c0b54801540c4814049d480074001034003084203903000700c2c109541e0200011082003003100e82016074400307800c2512040c0d9114042e00e07100000782281818920f01030300c44140c403002030f1107268503090440e102810081e21078000908552003070090301c0c00745a025006907261030301c980f0300038000c180403030b402c4400805d041c400908950007017103600c60071036201001380f180da50a5030310314000c0d4101074100c0c0291024001c156070204401000b0348694940c4d0300041c0701540c5404104000d0b980c0030100e40d03021188207024040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 143591429 1250 143590179 143590189
    0x110a050d030c0210032c0f07030308041b0905100f0501020a08040b0309031b010f060e01051c21230909040b07051216110303090d080a021b0a05061302 66
    0x110300f80c04450400038034014000035000790882004803e40e400c501d14055400d1464440a6640ea82003a401c480710380100919043e619951800041c0c0480c40c100b002600180111204401c07d40d100c020200c82559562151425604251600070340e08600500030f11814100400b8200284424401030506008c00c0e1a0814240316070300580022071400400034440160420403100001c004201c030714070990001150500a010f00d4002c0c48255040000000e0403000000e0b50905130b44008002004c0c11810413201c80d50707085207100032201000e08801400350002c655072412000040d549030045c0a2102d4400b60780900e40180d40da12600909025014075a100d00e07000d20b900c60b41c07055481c4504e444156040e251400b84940258a9046140401910200158a1881103a42d0381c8411034900111032015889000c12a8488030070703480310040b00c2c4442d00c03070b81c207554114801c440014502254081082000742e54107810302c040b41e201d43e40410403c40c08200f00b9620085c001c1050f0807000c5aa07002403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 143592679 1250 143591429 143591447
    0xc09090622020d0f05060103060f020403020a06110c04151a04060203040302011101090213020c1905030306060702040b090705030108120a02121809190c05030c03040221060103110a050d03 82
    0x180a490400000303070215201c03403c8500c40d40c2d030000c580b06496400e83c41c000b540e54200f400301b02d81036410710390100302082440c02030741c0c241d1380c1c010030a0454604059044507441850f401c0100248190b50340403916499a11428201c9021900c81c2019036041040d00d20502e109940294044d4904101c01c01419a0101c2030b941541c1d82440c041030035240c000907907800741c0300300b18019501c0b0307210015000b00010a64014184c0c000c84005440711041e10720300b200224900070300c001d00f07280c008200061141c5040001050006d200420004102084d4800310300c0c10304003200c020000c680c0020040c03100341c00c00c20850150039200d615041c90b0003900c042c02901d402c189c01c101c106000010801911034040e8540b0000040400f4041c018149015002803441040d28494103000c280b5040d4100c40382c510030b070122841181c08400300d52031516607609000503802043c018040301d440754003100040450a010040c0294012401c50b04020090410010340b03c0142e4011032003124000810b80000e50840d4500c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 143593929 1250 143592679 143592721
    0x11010e0904020a031113051f0e06151c050a140f040f0b0c1c0c03050108070b12040317070f0f0903150510090609050103050717060a02030702100e0c090906 68
    0x11500056202d40820706100c841041b001000c1e0400c000c104950300c0121502682c51802c46404000b80e9035076548911090341074480e150081d035000558054008004000c115108502007620790002ea905030000441e00c09881190006071518030818584415201094105140000385200c6082c9603884920764850b94400801c2c00d1002c0c0c001440ea2510001074600d080c401a292400c20b9840110000040444030840c4011070302e40400030803030300d20001d0454113403101010f45610b040c682c078041c40f24a20340200101c0810030100d840300b840c803407803040c40d501404c015101c3d421004000c2001a10412403101580100b002ca034a00f00040341c0c2d0100c608010080e403840008958807040305201881c9901d4110401d03d40c2000d2000500098030f901180c100d9009206031240b03981c86a2181062805800c5044407651042c0d002c20f203860702541c001c680017440c07070040f80c23042d066020820058078005640c1e440150460040c110b05801e08481e410303840b291242c09480580745c0150302c0c04080b111041e031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 143595179 1250 143593929 143593943
    0x6011809020d0b0c2101050d03030b0a031a1b0f03060409060e0f0d0306080f07060f05130f03050d020c0901170312010e070906050903120d0f060311010e0904020a03 72
    0x440c40542d103410707007840741d85504074801c1000ca16004000c000180d02000308520001802000c0b480206480003150741038440042155209954a4030210060032150344203a920049a00c40000000d14076500b0031400504100101c6c0c05242c0850b201103c500145014460560700308450089103040c071040b42d80c0300c07808483c001070340000c03402c0c0701c2700500c0a02c550310320921900714680794100d00055a1526079103140e07402d01c452500c40c04d0898541050255020746079002c56000c0c03202078002c207203090700c1c4030041ca801400c011090002c1c00b02c445203503004800e9110100f00c280240142809840380d020001e000a00542000102042c06440c0c14441d00c44003001490444074105424030071a03041201d0040203c02c0740d6182c04000c0c1c0320107026261100800c6449600243d031030b001c0c909a40950344014050003c01e0550005201b440d801040300c2e403020307a62100035000012040c4903100c060350203858285c4044a40300c002410700031041e24124442e902d00c03405c202c016030700c21410344140d0350b02c40300c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 143596429 1250 143595179 143595191
    0x705190f030b0c071202011d120d02030912030403121b120510030501090b010602150c07111309030309031d03030f0901050c030a1d06040b031b130e18060118 69
    0x83c60050040760802002030014490764881c91b80d054004004a44180c05000c015082c5d08550715940c45140762248046201030100b4003514039158051a8040040e00550303d440c68080403ea240340d0040710300f100803500700c080c488002030180c0b140d81c3c2c01e05440c003800d01800079064405801c002540c5260092280c0301c0c0000f4000100500c509001540c0c0034000740100742d41850100e103078480074041c00c0c005216030701110200165142c03c2c2406101d65000d050300d00020340c0c44102c0484005a91107810103a0744d00c910f1245883c0c1d12230086524020b0780c00080c49001c40c6802840300c101c0c0180f0855401d54140f075071020796000b1013142c10185000c9403895a40c2c0791040180ca4034080c0703686050b1a400003060b24005150000403141c114580e0b00c242011000001c0100301003801240500c07d02c510003400040c45100c0801c0031101c481501d07440711800c141e10a0900545444c8a0304000810b072005d4041c0300ca44082c2c9040304200c0281c040203001550305110341d800043da1681010b042c0f031a1602 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 143597679 1250 143596429 143596441
    0x30b0a0e060a09021306030f060b010804030f030504021c03031a0906030706110115030c09050603060c040e040309030501020a02071403010606020d0c030e040f0c2007171204080705190f030b 83
    0x2107941845d8400c241083c4100d40d0340303040151035520350a40581e03200c0c3c21320b6202d805544c4920788980c4181e5050f1108040458180403c80040c600101300f20b800c01c0c029111f00944503038a091084400e8480c0d40c0100701d1040e12041c1d03001501c12119824000d620f00c000780010ba950228401003500d0b407a1900a10380000340c060079001d00030880300740030420240700020040c803841c00e004c842a65401d110a0051380c48800030b042c0d550707c08075034160441c00d040c00103010300e2030076840254005004e40707400e81016480e51030b03507030880c0d02c005002c40140c1d100303403800c12189030400c040c003840240c202c00800c61746290031000ba44407d40350082c0010086100302c100105409039248800369080504100001b0b44500106001011807041e8100410b20030180007400300104802d480b2100c0f41100644a4185041c0760031421181c03441c502d80300e81c054104800010b00401014000421059004156032072030001031201403102c02011700d024190003031040c464800d0328019403084035400740d0340c00d0742c69680d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 143598929 1250 143597679 143597689
    0x111010506030706050f120903070b10030819230910020a020604060e21060109060e15010e0423011a040e190204090c0c0b06060a09030b04020105091009030b0a0e060a0902 75
    0x52112009901f1402c01d00084a40000c00744c0f0540e88948441002c0e51203030300c00305071209482d01c002002d4010030032038080140210700132100d80ca913075403c0c005404000c40402424504100704042100350700811040480d1030102c40c140c50103a00350000e048902c1c00d0b40c007c04d100d0721903802030105001d080c44015190751102a2011060422078030350002e480540303e44c043c1c0302c001c20f118a101242c1072030400301e00c04410024582c00340920a2151454a4005005442e0a452070004981c42503480480e0208403140c1c2103100e001d104081d20300006507050140c051002d001100e03030300c848030b0418031061207141440c106140c3c20040810b0b010004404200b640d1010707219035080360b841103050244202489800280710810b491280c606000c040d40e0f844c0903c070f058011000380d280041d143c0c034001c00110300080f0304203030454010325206180400c1000451205000c0c50158800501800000c009101540860039001000c015090105550b90b03113030540e80e194041c0401d21416643d03e0320310704560390 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 143600179 1250 143598929 143598937
    0xa060e040f0c0b0a0503010305010506060406020a03230c011d16061107030204090515062202030c0f040e070314011d0601020115090209031605011b1106180111010506030706050f 78
    0x40c08030f4142d40e41910400240550802c0c40200c0d41b560902c000306c0c1c400d01c0c091041c4ca042d2001c03a401414041c0d41d82e101110f80300740321582c1b0041d60207281004140b0541040c02050030b200c0c07440c0089044400d4100110800071042d4808440790030601116840700041c1c4502c0e01211800e1420401c208503004138541802e4990348002e42c020301c1c0c800c174401000400310340580c1211149841503055074403035091188440c030307400402d45500d80c000514045c840541d400b546c0c000d000a0201411702240c1104880c10750300c60f4200a0344540c202040000d01c3c0d0b814000c80e01e5200706030070160400e501d040e40c681003014141071403075403a0704a5000102c49034400d52006002d4500c3e0192501240d580d0040f900c0254001040b1030f010740a440d0150003440a0840300340300710382c030607951914409030300783d444160040f541c081124040d8146081c4440d80d074800010f0158a00c0d00015000a8000800013401400302c107180ba0000741d040104014040d074012034100c00725000d90a1190751101604400d00040c42 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 143601429 1250 143600179 143600189
    0x150f1e082a031014030a021f0203040b160510060308040b030702010b031005010f060801140d050307060603120806090f06090a090203071205010606020f07031106040815040204050a060e040f0c 84
    0x9004820041c510b0305503c00c8504486002114070460070345982403589841045001a4001d550070111501e20b1500d00c2c940081c0e80540d10580382000c0c2c0f40c2420040035407000c03201244000181d1250420f0010901c00301154a014400401581d4556940c152182c01188601d8565030030200010325041d000b9004032511000080950350222a86090344005107800c0c010401074030114074000c03521502030103034241652400c520440d00d540c561010400e242c80c402c0422a0540418002d0300b0000c0c009006803806107106440f1120101d4074683c00810080d002009140b00d188010184110300c548100c0e142d800c80707800c2d00d2140890b0389400d0298007800200000035014840c020000910401e50341c481d0305180d01c100000d0240550f19003080783d4803d24414200046c0e04004010800039202841d00d91607658064402c0c1c2c1425038038001903042440a0b15a0000f02e04980200011032510f84503899102503500800c201c80e500b030440a10750004014802401e0f02d050480c0b03a4144800c2d40504c0c0010a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 143602679 1250 143601429 143601511
    0xc180d0201050f070c090605060c06061018060f0201150e130201090f0308030402040b0102150c090a150513051f03180501110c06060307031e0606150f1e08 68
    0x40041d2070308051701800d522482604903d0b1900118191910100719039403050745000820440d101d881c00c100e00a8441110403007401142d03802000110002c001e0b020003020300e501c030060403041d86217019080d140900246c0d0f00030112000140a43d0200300f0b44103812040880040c0e031035000e0381c4016591880d59030800200c8030018003001040010b40e10086100354400d58091201c14559001aa50303124003000c66021000b105001580c1040b0010240140d00d20040001c2000c80e65007020000d040c5c1c001c1540800240001100d0b1030304203054007000b00611081d502e0348000e401001519100d01241d403e90020180c540c1840e801c10f00300300e4410f0811070b130001e000700039243e12a00383c0901c07907010032410f0b80700d4040c10300040c2d5289000704505044942044441c1c043c01c00c9108516172000341864102ca01c2c41c2d650f50041038510451f22100078000c240e444840f1186042070004c2d101245c04a104c0e40390400c40d01c610b401c03403a40200090303084142e013100158150040d0041075243e446e6034000d24802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 143603929 1250 143602679 143602687
    0x8060c0711012d17010b070201392a0b0904020705070602030307090f030206040e09011b0e211c12020a0504050406120506150a0308030f0406050c180d0201050f 70
    0x2000f0101c40c45602d042c090307107440f11844c100d05652004d118007482828801001801084055401051600c0c000000391601001410340b03500440c04010462400407003412042208804120b281900400030341940d000d00c5a800d038469455810159007801a500041004201041c00e038880f60103030741d0303640e6100040d619401e8440708001d5880e0412034440c030014000400004a10b001e0f03081082c19644c020389401d10303150805d80b000f604e00310050800030b803035984c0c2e452440c946018000441e0303200602e07035641c5018411003000c014446401c240700c422030390b80c2c048082c180d141d000601201390000303e80c4041c1a0030380120050310381c41100d00d035402800b0300003e84000c032a5031000c02081690401c44081180b141c032020703c55060443d0f0000180258401004140099134030f540038410358030000c00c0764000d55280d581e0304030740f600207a601408820120f400d00c005c00540b805500c2e44032000e03801450800003034001d40c3c140304070004e600a00031a0045641b6056921401c00c43d00e036450441200b0781d507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 143605179 1250 143603929 143603987
    0x80c0906010320041409010b0c0604030311040510080105041b1d01091e061b12080414122a07030b0c0f0703020a02090c0f040905060a0503011806050108060c071101 72
    0x1760800300002148204801c034004034060820000740c1303004814600c01405240c1d1540d074150010a01900904040c0205000009103684e0311640109002010340d80c021481d4903101c28481a10401c0c1c0619401480c1c203120692104c0d032184908101180058005407603081c441c0040c3c4290380940c1040c00e402300300390b90b00304a00c08100c0c0c400c0c0490f01c480c2d0b25401c1e109482504944c200c486a04000c100b210000305030a021f9104001240e007103400b62445441401000c5c629919185911046a19080000c140c034040d0b6903080c7e41c0102d175a101d00600740340c0442510728061301d80d491800010030185060021031948840c20081d60380b0092a0b150243d5148254200a0340d654845001203203d55000d00000e010302d02c1420030740d105030360300c0d008481c20175081442c800d002e080000c02032600002510f0002549607000d001e01000205026120ba940074445e04060050311816001004558004005e104040c1e18000880381030360b412440305000d81c0000c2c07004950700c2c208616980010603a580764514 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 143606429 1250 143605179 143605199
    0x61104080d1202070c0b071b0f052403070807030905060414101a010302090310050109061a030c18040b10030c02010609110412030c080d0b0a080c090601032004 70
    0x6295000e031240c0c0241044030100300b00764815010f008010001542007003100c0d00e8117102400b0114847c00c6207014607580c1c0442c451309156154070900300802c40318400c00c40b509014080d0140711805a20f05a0907a82540844c0300c03604c0b002d0044001c100c2000e0006120a11a41c49080c1d0a58000f0544000f41000d04000c00c009a90b4070318004180030341442d11015020521600742d50113034280c0b0540c15a07500e04010744c029008003290719010700030f0707007864041c8180714800c0324080d0000301e100246407420008081c002c01c04852601c000303400104148060111402c1c1070710022120120500840188c1d0004a8050a0807041c1150002c80c015200c0c0f02248e01030b0400110160700741d00030005140c0e030300b102500360344408a0149017104200428028034481c5110000041d0190038042031444280c1d580b540603503c0301d1081407559603103224103d02031421000c0c200c000c050402c010002d0380320740070001b21010000303042d241c141992180c0c03460b41300d0304018240714100700c1e1300605900c0e0750707031032150803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 143607679 1250 143606429 143606443
    0x3040303080f07020d0509060c070f140d0f060902040209040f0b041503020a0e0a0608060403090311040b1804050c040e0a05070b0301061d06040b04080c030105010e0903070f06110408 80
    0x60101e00c911000905036501c0c1c084092090060380d008180651513100d09079025403000d00066007240b000c0005001805040150300300400f0340003008500302d8a82070700101040b259a030060300c03941c90544078401048440040010181d003141000804a20a1000400920a01c5c020b141c2150403c90748a084c18015800301816460660b030a026013400130789400840500781c0402580145072b01e1042c060b10103907904181e80201005000030320705841e811900e00e414070031607040300005e102403028420002c0401c903140c06088150b90501900c400400045d60705a0205076055804020900003811f105042000c0d00c12002c000d0001c0090400b040c041c6602d81001304025140c40c800c2000010754513100c201100d049030182d60fa80c88500c11060802c55034500c80c480510b9009034284400700d00d0312001d400a200138001300c0000c1241d52440c105260035603405a104a041c3d08000080080c910004021901403a501c00c4010350806141c0c50003200520000c0112035400701c02083c0451080c000207104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 143608929 1250 143607679 143607683
    0x12091c0c1401110a050c0703061b0323130f0c17061312050c0a1509050d02010b03030f0901031806060305060f040201020a030e0102030909041203061a12060a1205030403 74
    0x60041c504080928241d0f600315103c00c0f050310302007103010704840c410400b4181351a070a4069400f070740e13981c2c0c07924401c0e80c407981e407100c07801c2c03445186140419402d0710640240b071221500d000041c3e000c01e01143c0160388020441450000e469005404004034022100c0050780d0201301070365800d0704d0340000700c00d80304550480c000500c100b40108805468222080b4400e95000090701c507580c4810320200d070650001000d40030240b08900d030f202e0016100d280300110348190340400142e018034a00313000c1d02d003002c04648103065904d06100b00318242c84c003100f214031901e44501281c3e0baa201c1d00f00100c0c010503400c1c2d49071404003070062280301003000c1500100100ca00802c11a03507580c0350000051281c010a4500a01582c0140011000a4003d803104e0390200030500507a8100f5244401080c01810126030845600c128845510030300307501807240c04003038100344991400340094036290368424481d1040c64181c840001e03001910944e6551514001f5007010350840880546070700e081c654a400034002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 143610179 1250 143608929 143608943
    0x70525080c0603060d1505010303021b040933111801051312080c0115050411040302030604060506030f1501051c0f120212131a07050312091c0c 63
    0x203180032000030310403a0362400616040c9942c480d802000038441816000321b03400342000300d10801154107440760320300841c0a50050056291254000c402c0c0ba0b2414540030711640c44c202809001c19158800203d0b07111200300710444900f8240f0801c400c100c101d4074072054081c104000070040d440080f018160020051040e0b403c10840300005490501680c4030000b84482c201c0ba0400821612203103540d02507005a01051500402c0080300e400d41c0d00108145420002840c401c200a083c9480f0302151401d000b64801d050a0850f80001d4031100040c00c0a030040351181d0205211307035020b10825241c002c02c03100310340300115003a050988919091044a00c01d540c1d020001c3c2e903401d4400900c0e007450758040400317840e07801d60340d5610103881d007000043d40851203070b0102d00c82400201c1c8000c0129461319201c0c402030900e002101004e4406415080c00d40b41010712403c1d0016200009071020700c0b2100046c80c200d555034403401c03403918512043c9500c02d42c05041ca0a00165000f45801d5545401091 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 143611429 1250 143610179 143610253
    0x2010c08220515030624090a0308090307080304060f11190309030510020403020d030809070306020d020d06080a03020303041211010c0906020c0d0302120702060702030607090e07180302010c02060705 87
    0x4080b0079400105d62298000d101910307001c80b40010f0a410503181a8003032001070400c03210101180741e0110b10b4008440544001400c00d0007440c00b000303103000505202c8011440c1604000740100131900c0f010343c60082c40003220041840c1300b414010103c0e02e0243c4014090300070b2207400c0c0105403601520090354070740140c8401d02130711404c034000c40c0c003501e4005c1e041004200c2d80c0d07038080301c005400800300001d50085003c040700249444c002480079545401001d0f0f00c03002c05000b07042c01c03507000c4e600c4032650f40c0c046035101c2c00103a004025240d00a40015040706500c001c0d8209880070007100248070301c5946412840c108a9400084d1042a2100c075404c981ca52a001820b20406d4280c40802601580c480e022484101210100070100a480508070900f0816964042841c0c24000e58446020600c820004d200ba40f02622000b0b80c80805880e2a01101e8410821030401610a000c06410451040c3c880780564645e0300c22140304a034047d0842c0c3c3c03c18007683d441d06403004400d0861803000c480e05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 143612679 1250 143611429 143611459
    0x504050c070b160206011a09090702010b041103060f060a0207080f1c08101505090604030b041a0c040504020d0912030c0923040b0a0b030c04050103110703080402010c082205 76
    0x1001503ca1410f031030b00100004e9080403e00010100000c000506140080003c4800b80d11078000d141e0040001c0e40012840315240c0707041000360395000e070030a50740680510130401c550390752141c031520010701901c3c519600e00e402ca00890501c51544c208500c14030880c154411740300c0c0c000494107100388818182c0c82500ba40400222840c08081e58a035503040b08107030301481058038060034035100d1100c2c0d0030103034030700040c91300030625a8000e5407003651515540340402041c441c2204c0307006007401020052604d00e10708807051404034051030082500071540070446c81d1180d6130743c0d03105113851034100b4124440401040702c000c025103107a8010703100141030440005040070300d8140d480e44202011291090700403440052000410030504240c0c1e0100b01224001446c003103500007540542ca80030a0980c2e603900340400581660070a03030450000f80e20030030010b004a54005400d50f00300d0342c2442c0c09080318080341007a010b03074000ca98000810743c1140c0141364000c10203c00c0002159415503036210080d0b441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 143613929 1250 143612679 143612701
    0xe0901050114130e07081002030f01060206010f0303050702030c090117010c021612020d020d03020d110a020f0d14030a090e0901090b07080405160909060b0a06050a03090c0504050c070b 81
    0x1000d1101c0c1c00080c01c208a801c0c5000d02d0b00081d244c8503d02c1300712a41d440c0d440012a240095003140202469030000c00d101c409100c8101c0103002d01414001080340303515000d0308040c0c1c400e03103100140400502041c02411940c0034885812440c6000307140800c0c55031605103044105c0d4017010019495881c0031b001c10405400415665a004441075030807418603c0d03c80011441c160790a01241d00004c21101130006907101040074041d14080c0e07006248101d4042c0018144900b41010098554002803642c401a51901490f80d20000c0c02c5e5040d400345045d500e49108642404402c80e2101d003c0810b11000603944219508101c800000401c9042d4030399480d0103088841001c0d010f0030a0502600203203041d402055807e410920860440f4040c824032840002c1e04400c1c2d4001e00055500c030034241e010b01031076001e4014111422109404000c1c40c1c0000588148610542c40c001d0648039441072060101d100c1d071440050102a00078426460304134100c18095204680c00c0350903511034408540c8036900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 143615179 1250 143613929 143613959
    0x1011210106080c070203010b04021b060c040308030106110c0d05030903100603080706020703050c0a0302060402090f09060a110904021204031b11010302032707050a170c10180e09010501 81
    0x225482c1c24a4948071090042c00e180d2010074160307003564803803800b40b40c143c031148018080001c003000300122424144900301c3c207002c009842126505020b10041c00440c0c100f00460341164240c1c280845690200310031103003848607a5000e20703440540c1c5850750041c8540800102800310084040d03d4070700d280c1c2c0740003404954880c00050075800081c8007550014501d54002d221050007810322034107000751980003624052400c0320480c010f80200c0c0500046050038445250000542ea2900c196441e0010025990b0140241250f0b809a11401901810003444040382c204540c00f9205560b03621303584410344607041c400da4003180018100141090202c1c000c40100a2075540086040d00855000c40110041c1d00090103c050301660000b0603030001e00340000303248400d0044000303064070f58504810003e040c1c0c16584200403220580c500d12664103400705070144000f00440780c06001400b00141180e0b07100c07460724801807a040c0340c4e20108503000c06641c00742c89603800304000e000703da80700d0003684091a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 143616429 1250 143615179 143615189
    0xa21140f070302040c030207080c0a030201140601020c150f0c0f1603020a060509040f060303030b100504050109030b041703070207230d030c150c120b090408040b030910112101 77
    0xc07140c024030061030b00e030708110030b401002c0c9005410030030251a4121654098000da030025402015010300705038081c020b03800f500c001040c1c4001c080ca8800d00203521043c110030020310514070301405000c81e81500040d40d020242428440351500784082100e0303969840c883d08081103100300b0b0004891200c20310b03450019a5030281590318064078100c800d8031250807110343c2c0c03a445500c0300b0011543d2040780c804d040045010303650100e010b021540034840780c8080b11141d101000400c00c002d1080380d810880303c20840364441c6100010342e860b8140701800707045110405140340c1c00003086c070a607950b00041c40b2040d80d4080380d40c0c054608030309a0b038901901040c03441ca0380008596040780c0110f0f001d800841c213280e008e9912160410b1012201c82c0486070f10005000105656000c1030340c06000e10300c59520502403e60701e002c004d00b05501c0e03203402070045208554510780f0020000d08040005e000b242100e6170041001d0142001d00c03010211117802031f4903130342c4954002e4a40b1038008103118503001d048074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 143617679 1250 143616429 143616433
    0x20c1608030a180305010207030507110108061e0103020702030106030b10080f060f09010b030601080d090503030f0405190906240f0e04020c151911040b09010c020a21140f 75
    0x2000740e0400d5a40300c29002411a595030351003000000305c0c40038001440101c1c403994540355110b44902c1e00d2000310b1042c1c0209410070184208000141c1c484c40c0d19400300e00040e42c802c030521401640100c02074407840800a4040d424000d00000708078449010b10300821809640d1070b03000d51140241d503950030905115070324503805080420344201050301c10640003074241001148100f0881e0109281440030380c4901c1c900e60040c4d4000b05050f80c4614180060b1600700c020b5494002d4003001d030201d80c0a10b00900c3d00c2841911441ba4400b080150b181d0000c0c840d5440c140b2131180d503200d03440306200b444401c1300804040e66102880b040e102e00360502d008071540c2c9982d2907007200101880000e4011001603030b030a01c61440c4500c90403032031703940040c030520000984402068a0b5240c100580b14100b0740c03a92808001d2006004c00c01c600c40566690302020300e00a034441c03151b400003038803035585a8800da41503002c91b580c00091500c00030310044800d000e05000210b07510a1101d00d6901c0b48419003080f115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 143618929 1250 143617679 143617687
    0x806070f0804021206150906060a020604110f031002030105010e04180f06060b040e0610080c121905010b0703021b010e011d09090d090506040b03041103011e020c160803 74
    0x145000741081a040340c0042c00c540898210420394134a0180207445c0c440d00400740c0700d8104000e207040750441da4825829110700c1c0c100f10400308081d5560b10054001441246115100c01c0c071134640c4000701e000004020111440507640ca00e0003c025442030040d01d0004000504510181c101170103007007480c884406001d0f82d0700c40242c032100c02c4440402e00803642c10b501c0350000210f000212002d84013901d0302d01c0104d045420513004101d4682e2400341c0000a20800700c00f00300c030300c111500030744122a8469040e20340c40c1e9100369210042c074065500c4241401d141c1000824444231a0018081051280d001c841003580042e00700c0e000764802e05601030000300111076010701544100413a0049048a90756060700250742c000085a1100844040c509588000240d0742c207283d00013410402020252815441c05060030b0700000c96110003000034142088000c2d507103029407000d50085c0301d01c0315400d50104141a21842400c080d50100c0c0752081c652084108002d403030304c500c081000440742068000d40c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 143620179 1250 143618929 143618957
    0x10804080a0309020d050115060912080306150c07090f0e010b09060d0606091103040201023c0a05010504030915030b060d0b031e07210c0302060d0b150a09080607 71
    0x541603e81d004c982100c00b10319075038000f450902801e1082d19103075908108041c200f07540100a40c4041e480046400366501e03240c0003090320230003140d4203ea025110b400c030160516000302141e20070b51044140b14401c018001030074000c19407003ca890605143d0602000001c00601c60903070780802d100740c2e4800060780120f400c0d440c161240210140c4203032804284190b5504480080b145070301000c0310001000002c00c030071503038140720110250300d50016407c841008044284918607000900010003007100d100940b0381d20040001c51502ca0b405002485185014a401003402c1d2203440740384214480d01800e6070780d16000b8002c984c50303820050003081c144124034040740e001d44900d550450301401036800050300c0700c08000c14407a802d04254010008140f41081d6000703071900d0703c411040405920b055500004051403e418112138040b031380607461741c00050010300107104120040380c0c401d1080c00304460004402000c2c080d9034605031990041d0590703c5d5155511020120344031800148040d5030201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 143621429 1250 143620179 143620181
    0x2e1a09090115030f020c010c0f0c050c0904060204030813050a1202030606060f042c070e031e07090606020f0c01030501061b03030f0c03150503030415080c07020307060f0e010804080a03 81
    0x461002c6180101d28010051800e608a034469117203800035944505a0055258010100c05003006030380ca8207161180304e945904c1d0700d642075a00d850b4070441403130300071405014803a019074010b1900b001c055503071201c030500388000307010b2540318850040c55401000110800f20350516404160040c020701065650801040056800049180e5002a06110104000c540c0c14090140085450000c981c0303040700407203e201154005046404003c2c0c12400b440e41c0e9200410f40140f04100380c21910180a01c0140700b904104498004140551819000082d83c5500240755034000790540d00b074a03821401d4800440030b0303403800d00400c40480c00c000205040c00d46540415210f40e8042d20740001c00344c0c00300c007804081c1c400c41054800003075201c140c0504143d00700b910300401007404400451405140014041038030074905924814002e5080004441c0c0b0030f200221240c60798000d058900da107072035130303405081261b200205100003400b00003000c0155004240c2c9600994010703040606044201000310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 143622679 1250 143621429 143621459
    0x3060c03190f020f120f0a020f070201030b0a1707030201080c030108070510020c09130605090106030b071101060302030a0b040308010e01060e09042303030702191a2e1a090901 77
    0x10304895003081200c14012124000d03052803c200520740c1186e08010103c1b0820020240c0780d21081c0b441080320760501c0d0480411580b003a6030a0802060000a180c0040c0d4814490303071140c1c14039103404012112001010a101d000d40f4400d0725a007901c0e803900018105030b400300340144001c0c0d6028403014441881c040d5100901d0224500c112043c100440b0040f034089070f819580c40944401760091082041a0340c007466500c1020314008000c000e15645500341d0300d0318041c20300301c18006146454408040c0071340181c40910380207002c4035481e040d9840c154880010071141600040d0482c0b0000c0340301170b80d0a0382c150403110507a4a802942e5144800c102c071040000e00219100b0848000f001104000c0c4030000720002c0003140559100c0c5092000603003020303006003010441282801c0700030001100c4246069030030762040010700b025070350080c0070440741181c0103801912110504421012480c0903404509a401144800c002d000944032110458040d40c007200398488800d6005001c5090b0002c600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 143623929 1250 143622679 143622701
    0x3050c01110f0111040501142a010917071a040803070302211303110102040e0a050604110c011a06030f190f15031a220524040203060c0319 61
    0xd036941c07035600c0c0d0700c41d82140c82c1020311020784c0310b020804000945c0c11659030f51541c0c0310307140550300c1d120781000440c0007407031100c1118041c0c105805240400001c254040b1074600c0d44000c1054501c800ea1001414680004500b2940c14210f0102d01e0350742c1040001c40c0380140e0348940c0c01400c0d5241d072442a0042e4000480400c110343c3c0720f0240c02c04c01020b25280754040c1103104550721040043c0c1c01e0041041c0210500c07511160300411080015000c0c008000385d0100300f65400203115103903100050050714814440200e00c1c0b10109001b801c2c0303413041d8040c01070b400340b85240c12084452a018801d03d40400c84010850301040c0c00040c8509501030039021070b1411091001407046a1020204105c07121aa00180c030042d4140c030078810030034989603c10200780308103890070817031502d03221000941500c6001d5040701c05640b001c0c642008020083c992140740950240b03503a500800380c415007429022a0181d02c00d201c1c10300031402101c4200212070103a0000560956140c180811100250042d5030321 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 143625179 1250 143623929 143623933
    0x50f030c090a030f05010e03040b040b09033315010f0c02150a170a090c030f1a1504050f040203033915070207060c1713032a03050c0111 60
    0x345490365040b081c0000740d03100f03814429412140e4200107003124858198888103500c100028030940206005840c1285c4803280b00580c1c0d100030740c02080c1080050030440100a4019040458130308588000d95080c007681501c1c010240d42c0e0300c12001c1b61010428406002c20280d00d601516148900c0010703814030300142c07902c031842d43e200e48080c0081c1c0c8258036410001d0512081d42201007080c0c140641c010001140070700409010b504e8811114a062100a0041700c611000b802008511a10b0703480c00c40714203054075810301d82000f0290070107858101143c4101c1c68400000d9104c0c610341c1c4802d00a5402500541c207007125080310791080f03020790150722200b8200c9820030b000b00c070040c00c0d03d240500700300002d080c50300c0301c0041c9079990210113082001550130140c814009594030103106803169811001484941e0500142d035405440b03117403034440c0c0c00101c1c0500441406546c441380d44800704042d4007140b8407681c041c000c0180400300c0c000109540c000300110b8086601c41c90104c2461130308481 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 143626429 1250 143625179 143625187
    0x30f0207020a140420041502070801050a02090f04290102031b0a02010201050c03161b02040e010b03190f0b04210306080d0915270303090317040501050f030c 69
    0x140d0b01601507800499500c800303680c89145401c0c1802050200c0c56408074411128400c41d2082c500c9000700d0080c5e80ba90055070f800c503c41d007882042803100510088000b00500c0c00c00d049464040d5004d42c43d12070144420019411007030030140308071626004d5820f0301ba041c80307103000582070654801c10b03092070452006211141e400d080590f542c3c04241b582c00010310107082030340b00281c00d4038001082450004c07002c0c4204200f1100b0403071040543c0245190a094003035800c82011100038082d2000780d00325150203000700d5120415030201143c03400c00c030308441a0b07003207629540c0d88450580c0310040c054807400c50710303900080601c44c5040d0010701c1060820017400306c25806111841e00500d1000000f0f4550804001710b9005100050020406240808045003040a243c150aa0009100041140f20b540c001e020384401128415082c2c02d41040c44000d41c0c1e0703420003c0c51045240001d503800c80c80c00d00700a00f2060034500b182e0813104180c65040c20080ca4401c01c001580005111783d2031498100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 143627679 1250 143626429 143626433
    0xa031505131a060f030118020c120304051509030c0115050d02040f060902070507060e01080402010801051012020409020a0305090a0b04030813060c0504090e0604050c21010606051c0c0f030f0207 85
    0x1c2d040035a01c0340104e988a41c503240c0210318901e0030a861003501d5104200541c4403c5010420f42c070401c2035402c0903566900d40b4a86a487e02b103d0910084422038224148155040040f00901801880c04001e114119040c807240425402c00d128560f4880700910103200181019007242000c120202030002e8901d03a1411160309a07440480d08548980000100340041a045400030003260001c0ca0b04980c2490075074000303040b500c2e040c001c041c8901e038014040c80e9001c0c440c40c915407903003041920039901c0e00da03941c8080010390002c4403800040f03820400040c50703441d400610030883ca60441044401038540d51019074440c54054154640102c0c2d001f03c1c40e0124929014a00220b100707641c0791076031103140015440454001441c0080c03150000c2c1c040c44081940040d1039036144a003112508503500c10240170744048030a06851417029420b08000096940d00f00000e03003c070700c48503609001c0a00d03220245000b120800c25083c0042850a680d01710190703c2070f03015040c4a80b01c0303440186010130603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 143628929 1250 143627679 143627689
    0x503010608030c06090d0c081804090507051011030304170d0c0c020906040506030a02011209051b0312040e0f06010e120105180d14030a06030f080a031505131a 70
    0x5401280d036030b5000142c1540c0440c4104607480d0b120041802604002c0c0d10142c00501034105546c01403c840d0f00414149032028240714601e00c4c04400401c03c03c031924842c50980e80704c800900c1194801c21462040c40b00d094090103c000c805000b45010f149590740f15502c41401704114070b45403400700000e01009007810803c5c07281c1003142c40c4640b210240c9090030320402c0a4a20001c4c05d4900890500007030024036140041d001c000d440c2d0900340303000300183c60410380e4028404050090a1446082820207850505e204c00c0f0401d00d0003501660121042d04611018174400d612514440000789400294440000420250400e00524202c0b0200401d100014406c0ca1044e1445650703075514018012210280080c98480c051010003030840f090003d4805840a100020410f5203002c0010014408a54542c4180701456004541c41c0355107103031341000d08140d00f11000804c0405c0c90148044012400114400304882000700070340030424280d042180034200d507000c80c0c0114214800e6441450340d40d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 143630179 1250 143628929 143628941
    0xa021f0e1309170c030a11190f060f020901090e070210060905180c060a0c02130603080408190f14010e0111130b0313140a08161203060e0718050301 65
    0xc07990301140b041c1041c20704011840b102000c44503444403c0004140744400841038a0204078142132a4940100020881d400c24650440490106114050507010403a03440d0425051038010071080040c0300102040104901c00c0210741d07030208444140811402c0100307011140d0007107091042d00c012205540e110b105450164010f1a011a2903d0412040c0407a0b02d9582d4007020040008043c05001c2101140c0703148161080101000001c0d8001d009540b030f071034804e40c080c114840081014907602d0802d03490b00d4205018507030b054050b080b0003420b50003180d5038860449401c9072801e60429510780c1c85c05a1400100b0f048c002c2552543c0019007003400a100750300417804500800c0e561a605a60303c0c2c006044150408450304070300707105010003d5040c1c0045030032140c2c06403c3ca00e0b0130b2032010401d8540f031a80030f001002040f000642c0b4442680c4540c00d0002c1030b22503d400300c034001c1180020750554509004040481c0441c07800203030801d00c22850584c6000c2d80c01900320360309440703201007802c1d910 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 143631429 1250 143630179 143630209
    0x19030807030e0108070801030b01140f0a150f05090a170f0115080f010207080307030c05040803030108010b04050901090f03030b12070807030b0106051201051003020909040c080607020a021f0e 84
    0x40b1503140000d42e50700316084035403140041c541020305604690f0742d138a1068041c06400040d001d4001c03610065214412280310003200101035542455030341c4103001603500c1040c6a84001003184246c4100b860050b0280c8402013002080c0c3c1013410b0808400c880c05010b900543d002c03030304c540070110403c03440070321880312019448404000114145141e8a240002d1040014040c0e841080503001080b549000da9170803000c1c0c0d2401145500c448841100c060085402003111400000000500c0180550280081d008155001e00156482c00d051600f00c0354080d01c0034140039180c1800d100000d20a9006003421507008214040308204000790034500300c1c09811004241c0c1c003065090090000111125004110500e402c40c0351060381e000c41003402c803061088500070492140000200d600a0701a201020b60103000e0341581d00d020305008003aa5964801d0411074010030300807130052071003c42d5034942541c002d003890380c403449104880c0210440c1c901310b1504005041d45850082d43c1c0308886003003003803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 143632679 1250 143631429 143631437
    0xc0807020103022503110f25050a06050d050a0c1d06040b13030605090a02030a120203070602270909030909090309030a0f150c0f050a11030d0609050f040f021903080703 74
    0x10301e000740029031b0106000f0301a03400141e401001100c0055141d08c07064102c0b01216040071030040c0f07014034880300c0c0c1100340d00c82d41c0c1040204500341d00c00090201d201e50410140050703221104420100c5001c203901d078000640381c00300000c24a0070b0200e61403030100c0181100380b0749a51484000640d4014100c0346001500c0114208103001c5e96008150708041c21001620003106150b00103a41c490403504010807000d00f242212005500900540b24016008601596070314101180310501880210f80040341c5070002031020094100404598890020003009614100d070320420440e00c040c00421650440c0b100b00a60100c0351801c0c0124039590f4410350088040036124640008004001014035128606e0206d800741d00591080f074903414031056003002ca580b05c40380c0c0b50440d000762005825010a00c40003c200c58002c03c0c607800002218035900f01001952603840219412010998000d00440c030000014005441c146614010f0b200f0000320300c2c10103a0f41ca80d82d0946d160003600e070940200e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 143633929 1250 143632679 143632747
    0x150c091710060f0f060c06020c06012402070b0a140c0307050a0309080109080d05060301141f0b031b0f19031d030c0a150e0f06070e030d0c080702010302 67
    0x2401c01d8051440034100c0c0c5281c00d0900d5041c41094100342900d44102c20400c10780240301c105100003541100c0071845070700300fa02c0c810740c1c41304500480c0c540d50086a5020121140003030640074400301d03200c02500d400c284200d261034140c0c001140d410708840e00c11041c00104000c90b0240c1308040001380500ba203d0030260095400500700036041c68030079804050243d040541000000b01c085044540c070040c0d0840021740e540b0b035032003c24010700d80f80c410321000d80f501c2c81c248040f4200c00344402c05500080072000c08060f403104290221b600083d00c004049046032242544070a1490002d0841984266440b030704104c5003107110842d4103516010704001c80e95174103507980c824808030f2200099000c040011071400b180b1101043e521130394580c01070030b88000c90b0406c0315440d031107411848003403480360216140b5000082580d600c5600c00e4420202245030706404040a00b00807980c10184111916141d0b5044010340315030060354070102080b030400da4201704241200c40380d402c0901ea0003c04401078415 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 143635179 1250 143633929 143633953
    0x20c1e0c0a032109060207060f0903060524030a0b0f070507120801050f04050403121a0307240c05150a180516060503011206020c2103070e010507150c0917 68
    0x10084400030040f0810402c01400d106143d0001841404c48042e440d00c1d2107500e42107041180d04500c180c00040c42981010180b1040d4a51100c01344103c1c059100078100303821214040698482c88144001d281c020603a000a25035596807a109502114904000e480d002d03030780e500c0302904d07020b500190010840020060100e401c102010784540203050780c003041a81469100900700209203a15030280c1e64684459450f084912809800c801001070201c66401c0c1d00d070004c812001005a40c40c4d94004954111144002d10542100070a2600714000d803440c04540c40f54080c0707250004020b104044d84880007203140081505000421601940c09401000090210b070300017003890b5071080c005c0203401c0c001840038850070401e00d400682c1c052001a580c1040b01d50103030603c0104050700c580040815000c0f50100d80303200042d407090a41c2e9851b44d44450444005690364000c6900180030b15402d509030441c403d2a03584000c0302c1140c00d0a0803d00700d82d80c2c0e26409804c1d60034520902e100e400446c54121 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 143636429 1250 143635179 143635223
    0x3091506090106050f03060d080408011a03190b040c0e0103030c050114010b09040e10090308040c062f0a0f050115061d190b160b0703020c1e0c0a03 65
    0x340220088401d54415403400c20020458001c60750060240b00380007011651540d075074aa03071594070341e02030603183e1142e40d1906558020440c01c2e90304c01c000d0300a0341d0a1000c038500484c003102c0c2d0390400141e500144005444c1c0744c8030200000c10407203034220300c43c0d400300308914403c0200380207603c2562030a00440c440e240c02c0d03096400807071416002142e124014000c42c0c1024065900c0510191400910907043c12100b40c40d00c0c0c3d100e0302d207440701413170001814241940301d10824401d44c01842031f15101c0750384035011141404240e0b900039070003101280022140f55104890b0210085030f00481d08642d405484000f0440782000b4200d406a40d5841c01c40c0d60000e402c1640c00c002e216a050004105d0b100d01c281c106108601e4124500c5807807210b4804249451030415440507001c040841c0e51a840d00f9a40790030345807014a025502d42c3d40903000507450074072074002c0720200c0040d10064040303542c8a000050301401e04410954860003040800e80454450010300402140100d036000d082c0020004001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 143637679 1250 143636429 143636431
    0x5090d0e010c0507030212070e160e01020a0803040201030911060c0c01110f100504050715111002030c07020d06020910030501050f0f1005090f040204080c010e06130303080606070206030915 83
    0x281c18490050240804180c022a03000c0440f07406441c02217150140946680c00c115064110000c2e03010004140f1080c18503214285240c4909615500c110005000059a81c2c524504008060050410004e00194840d0b0003e002c0f9512070000010061000c000181194202a0180e500340c0d00a40d02c0078640c1d03910241e00008106400003504001842885d140d4403441d0040404010503103403004102003003010090031000344170b80010031000400341c82e00103000071805003a411035445040642c501441c1580300300c0b40100c070b400c0340c42444c0008036401d0210b405039608090310025400e100014083d101c00700d00558100d12179038002004d40c1030604015100c030394162200d000364a11803680e1001c0d1240322018416204a0030301a03111000303000040c1444030300404450b002400420001821a00010f5103410b01c0401d880d400105912002840340d28010401d142034442900f0504101107806120841d411010250110345080401d40118815038070541e00d9072141d40c000459007918503d035240003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 143638929 1250 143637679 143637707
    0x17131713090f02120c0f041406070203061608010f0f4103120309060f040c0b040b030106020d0f0905041107080705030301030b090c130507050702040905010c1211040303030213030605090d 82
    0x5a42402955242c01b0254000d034040c9404084880001005a50b0740c1d0307003507640d1b181c1d00908403586898858000380b64400700717603018004a04540c0010580300300300040d41d02a910701036581c4c1041450030f51611032880e240d906500b00102003034000803410000303c035a051240902d1502c0c000d010b81000178940340034001c1809a1340c002060007070205880c404104190808079028486801d600e03a0308020400c200c0c680d000500183d17001800107589030003040658101d5a0075008d84a200c404a4810388140311041c2482d00001d4021a00344028949513100c1030344802224010b908006040d41c0c2d4243c5548020019111a0710200040040040005400b0b90104100c0f000d001080d4424010515002c1d450140c0039410b0f848030005420140300e2030907204840d0300200180241c103c13504000d4001d05031071000c04001001c0c0006e88180041d00d001c0c20310660100c040e514601451910b04900a402041850507a4880c248000012810074014180209840c9001c1c00c002045180040c29021203e524 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 143640179 1250 143638929 143638951
    0x20c010c0b0601080415050703270b010b0a030b040908041401020d09030602030411030615011b05060a0230061c0209040b0601050d020a17131713090f0212 68
    0x4040025000103000c940241c42800c1c45045505c40c0d00d01001b80b82d155050007000e16151208005076107901d070f04100c5600f2002e5400c12035060031407040309181031204402500e41040031004126041a1000502d4078146070314002401e04820800a01034a0400000340e03102400402c1c280140d0a4981c0d82d045814024001400c0c50440340001500c041d0582c4005402d1b60b902000040a0051550401e40f440d00014103a1f0001d1030b103035100703490044607102494001040c1507441c03040310801c0500f602410fa000002800316a54049901001c2d6100f201d015560751030710000c00b00348030070080205d20303000e95131058081c43c1e240c40c0090003a0b001010881841443c40c0c1c1d50640017588500c140300f03400580002c00d1058640c1c80ea40103030340c944034008088420920020728000400c1c1e20070080c0d50300d07000c3c9200e40079164503107103114142608411303000f42103c40682d07825043d000e10321005000118101415801c0c25513604c001400f211662090304604279000201c01d410b5004107038000303501030b4400700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 143641429 1250 143640179 143640197
    0xa030c091406030a06090807240c030204052d030d0207150c020d0f03020703080301120605010927051c0e0913030f0e060903030304030504171903050a110601090606020c01 75
    0xc0da2603494503405405c0300e54428807442880f040e04112200e207600f0030003920458444e0b090171840c400110381e504241c5483c1c0045600c900d4030074000c60f402c90300300801c00382003503540c03200d141103c2540240300c4c0c120702c580010002494a05001d0080203695640250440300e14000d00e07403c5214401284c4003c1000d03000c01203005070345d0982080f501c540c0081c0202c12420b05445e0980c40d10295401c0980841008400020780d140c04445241809202d00010b02c65a66250456000d0f100028140b44070307a01a01958200110407180c1c2580c00b0340690102c400c0c202e02105000600702c2089038010000711480c1b400710160401e080603d40154114a400790f00d007601e52002001e0174030911101d0308015aa20300c0921585d900000e850b000107008041d02e0b9607007010314004e0480c1d40240b06003142c1052002c0910500c01c8003191000c402030600b100c009811110303581c100c0b0755900c218031600c280722074500000e52444041050b140a0618400001403003800c004003e40b5140c07050001c0780c100b00036a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 143642679 1250 143641429 143641441
    0x402010203070f1505011e09090213200708040501030c050910120b130b0306060109030804180e0a0f02120d1e02120c0303041704030506040215090a030c0914 69
    0x7040341d01454200b403041c5116096894100c8160319000c02c1022503d04140002c1901c00460443d0986410000d00c0e00da50160341c2c3c0e8038281a46c040b8800030b507100c0020449004145255001049844000c0e8030001d50410300d0904003203960231407082647d1100c4003060911081d42c26215022002e001170500c54100700c1c03c840021026a0008225070412054100b48201c450080c2c001c035181c0d07a4014403849110304141c104030001d040d100c0c2054031038810341c000b14541e5401120042c00341c3c0c1d0800110f40c07078182400310348004181000440ca511a030f40d100d000000e01003c0c014842203500c29001300030a48443e0040100c0308040c8042428a0341013a41ca1a00c0540c04c426010030400968020810010700154282e0801908031906404080c0004d4440000f02e8007200540c41140300b000040458444030703002c0d4000d03000da40070081069101d48041340252410f84241124000c0a1400a00c1c210b00d4002107854580303954400c581d00008000300f4800440c050003842900d04000c01003205900d095 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 143643929 1250 143642679 143642683
    0x901050f06030a02041a060406020f15073f05060906040b010c0f0c0b0a08010911040f050f0a2301141303080c071a0304020f03010c081f030611030402031504020102 72
    0x8120b0007403240c0c1d501c00f02d12042c030841b22140c0000c1030006040d5030f1110303500d120107500d9103c2c40d80e4020160007800f1400001c0b0494034481130281109a0381d45c201014142c2084c442506040c0c02c2202203510b00c020800c084135640c403401e004008442000c9074605240040c0301c40b10101a2240f4441c40c20200314030001e99000350031034031554103c10a0803224105013402452001141c100111124002460802c1a5081140a412294030a0080001a40c1040e10418602440c0221586106800c504212a144c007012407140d900b00205580c80c101c0c1d407041040040310440141003008000100c100309030f0340e00407038420015810314804520749480c1074a100b4081d072480c00000c02004010654251a4070f041148601914112119007401b0740490b4500440350401c803400c910441003c40301500c1824180907401100185840e46079460700c651850701c1101500180b0700740c07154001400000401d02c54015800041c00e4500006d58038103113070061500305243c5103940421401c0d11014800184d0380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 143645179 1250 143643929 143643943
    0x907090b030a0917030a0516080103080a0509010315060810050f030c09091f05011406130b0a0e0613031110090306020d0905060702060108010518070306090302030708030406050901050f0603 83
    0x3041e04000f0389a02103203051044054800c00c0c0e0000324002104200841019030b010354020041300000d0041d41410150803070768194240002001c6030802d005e908800350042d0090040307240141008500b21b111040007050016203503020f031000030b410105003c404401070480101415090343c060003002035030800320303a82d05075440106000310001d2002650944003440622004c8010b43e001010101107560f0700b4024200a003d032141031107103000d503042645041c00072145d000030161a0051405d146c40c090a01075000b094410302800b01901600029581d04e10007000305128410010140b217042d4240442402d01c0051020300581d6443e00082c0d959422120300c3d0100e035803001d40540d542319001101000703888005001001c61050b4003c3c01405500401c1840c181e43c44440200580e0343d0f00319903081003483c0f00003441115044000305001048058101c1102d890103030044a1821032142e8038a4502d45c001c03103003509c0251381c6109010400b1402c0c091035070009001c0450b117403581005c00c0000c1e16256 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 143646429 1250 143645179 143645191
    0x14010311040e0c041a09010815010e010f110a080c10020a0203030a0c03140a020a020f0304050d02010c050a050d11070803040605040b070c05120c01020c0a060512040809040501030f020907090b03 85
    0x8600030008a18445074811100500b102c860300d0080c071084040c40c01403a80000c141b590109410900141c0307031000b42c2d150a056198140d40d0b03900c0341c0c034070700c001540c4407043c5141200802021500d04e60b6003403810803a44170030901c40c3e1903e580c0c40404004503420120355a07071030fa1649004204400e0500d90000589410058941000400e8030030481c09800500000500510700c0d0306403010414100e10942c05070101c02e44a4081da20a0303122528182c3d00d0707210302d0141ca507102200485131030143d446a054200e481d4070880403900c00d110641c8800c1d00e001004d50086000030401c0540ea010484d041c0a0440108200750080d0701341800c0400203003442c05a40110380b68070300041008400d02c0180c04598004110103010044a030110320441c584941d02c0003622030151007900e002c12628205025004216005540c54904245036428400042c68001d0025180050305200c440700a55462180c08d00030b5204540c1c10a81c18090300c107100c0b1100004110f0030600240c07680403c0301c00ca4100071254812 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 143647679 1250 143646429 143646449
    0xa03270e07020c031c030507140a140d140412090806010b0a1b05030301050414100e07121802040621060e0a05100e0613030203090112180303061401031104 68
    0xd40c4200040340343c40310220301680e241c42440c10403078024501c810041c910029035602407046654280068444038460214900c20904c200400302c04a8440d85c5290810f07a03002600c80e00d0920001040000d40b01e0910904a414400c10700340020000c4503c00e00d00302c00c00c50708180303510f1480d00705a03a4542c0f00500c18040c1f80356000a600b20440c2c400c2c050003000e21013034414240d864440c1d0030700a41e2134009000b118003492820156030413a41039880100c1c40b0f586c801904210070b5080010001d035050019121009200408000450341003560150340213091195003070b007801c004140100300588420341c3c050000181c44015410342d014031581c40b00c0034190480008580600d0241c0d5281c601042c1010281a0380503040e1a0809200d5a03045503030300b80402d50460701c02c3c0e15242c02d401c000c0d425030705005000d648100100f00d0154001c242d44c00c010b2200000c0003552004040401070089140c04048001a964400c203001840c00107031201a402c5007072804100c80c848482e180740680c03040303000c0d1031400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 143648929 1250 143647679 143647681
    0x80f01060309082101090b01032904090f050a06050c0a0f0f02100c03020408010609020f12090307020d0308040308180c0d050322030311120714010b120a03270e 70
    0x200851004139414110340c4071400000341c11580240159002c00e000c2c882c119800c08164091562090064403146001894000e83c00e04280c500d00820001c00c6e48886c0d00543c0300e030031100201e4600590360040b1384c0914090038014002d45410011100b00030004c01c2c80da90203200c0010010b45c081e02206003030711a401d203c075910b03620441c140e241224144101ea41c0d542092503204110364907130003920407203070701710024001c1640700e44203007003031380a4442c420964140500c11047d1802024040c603401071001d0003130300c2ca0204070742c0200e0203040c0b000c02c0030340101c0e1041082c0401c02da40455003a51144008072024002c5541014040d11105070b480b00c248144c01d00404101400302c1170040342d0806c0242403000c40e0301c2d03941c02c4500e0680d00c0d4512080c0c0110b176400000c0d82c9400404a421a468a81c90001c0ca103003c2495a17140441074840c4010a0a590381c1c200c01c04894540054108000e00d1030b20007007840100e18035008040c0d981c04072062007581004da20030750034400e40c10f01003419031300810812051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 143650179 1250 143648929 143648933
    0x1e0e04032105090106140a0815100e15090f04171305032407030216030311090301110c1006152303010e0a0e010e0a080d0603020916030c080f01060309 66
    0x2000c1c6040c80c001515403800d0244a94028154400b81c12200940781164000d01d5441c00c010050388a8442c42000c0c1d0130881e42205d0a001070202298030404840408205940303801c0703044112803085030740160b41c800000c0141e000b403901120386a44040000500329540c51300341c1d00e10081f8020a102d8055141e00407409500300b51036000310318040e242c05012162642020810b15203814030120380703180c0045e1a200856280380c464002c4608074034054590703240c50380c45603800324010154410f410880c031005000c0086150b4003030081c9810210302881881e00c03407089150351070900351403a920011913494400c0800c851152000f80703600c480c6030f41c00c2142c490600003480b0b40040a003090070800d900800000400c00214401ca024000c201c0c9000c10000405101c1c01e907401ca9005080c924240d40c0207030a0380300024003180007050709a10300360010841c00e9a0364003041241c001510303511040044401c220010561611440d600945549051403090814071144191030406014039810113461b002e034501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 143651429 1250 143650179 143650217
    0x1051009030516090b0f0d0b06061605150603060906060d0c0801290604180213050a0308031030050c0d0c030212010c05030103170f07060509070b0a09090209120a0503041e0e0403 78
    0x40d0403140911140c00c070bd140d620701251034120000000e4040c070b0151001c54118240041c034244100705040c010013440d00c40b403003000542c03142c5000445840d041500007088980e000e00503600d0501c2c002c20041003004850100d0301405070b500203503501681090004000c520b2042003041c020040c1400010382c2c0707442903404c20501803000d400c903c1c7c21444220000017004002030080d44079424210746e200500f51603522940d1049980721041e8203c034080c0c00d4003e1030a20302040042ca1902c51070031540c1c0310b548074010666016030700e801951942c103441010401e60501848810381550b03404020080200d228402802074001800040d080706510960248081624011103075440c00040c4625200c0c401440c103034010345011201890140210400041c084c50350100b42c8004000701e48583c0c4c403050508000000035003000030b00b250310611031031a00300340139414800760070164020310185540b5400c042061400211000c00304144096070740003040240c0341d194045801c1941450040a80303181200e90780 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 143652679 1250 143651429 143651437
    0x91b0f1704060b1018050604030803220611071b06050a050a0504031a012301051c0b0a0b0408070b16020409030512090705030708120301051009030516090b0f0d0b0606 73
    0x741c00440200300684110341001415078200317150f444884196454000740603640c0600d200041046074180081a80604040c10306003004000d410021010750701b07a11401c06880301180180c1192800151642c11b208a50b54480061040d00608a9003603240603402400c51080f41003200c2044000308102c02503a00c03840c00c071801150428801d0302d10b030401c1700e1422448402840340303001c40303410785045000f0b0390080802c41c155028161951030603c12513407402c60709070a070840c042c00580c0d600c1224840030340d41c50100402404940151a8a0f14108032001d840c1101ca504115108ac600348099050862032021042130f00f40d0540700400e800b10300703150507951409000c0e0b0b080d407a80c18180c200483c00030001540e40840e502142194041d0780d4808405441c0c40e03840a00c6030b009801040144050300b402d0b00424a2a0a1440c00c1c821441d600c0d1603040c01c18401401c3c0c002c07200340014040000e42404d004040070000d08807202e0100710911400208481100344000700100842c00000d016607031080c00391 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 143653929 1250 143652679 143652701
    0xa0e0f04080c070b09040e0604030f03020306030304050612040b0105031f15080f0c0108010f050f0f030a020d0b060a1403100c0e060c030c06180d1116091b0f170406 72
    0x40f40a56141e6a10407007076000302803501e0040f49000c864114840c00001e5007401660591035100a80b83c0c2d050f0110040e42c0002c140603010f100c05c00000070503881d03c1d001401c800c1c00b0a400d9100c541050b1070700020001040e0300c124404d60200b1390805000c0102c0d8010f40002040d84070003c0e0800b6502000303100c0e0030265010707801c00c1c02141d81900d642d44001c1016080020f00740d98101d505d0b82c0742c024450600396507000b501d070040c0b4081005101ca040c1a0403440c41d0344801000c40325203140320342c00108e051515400441e1500031402c02e000c1181018241c440150158840000700c1750110707800300f9603540c601411200c816885454a5004c6809017100e9580700741c01030b10140e41d4034185040d840c0d4039070021060034a180f00380070024001990500b08410445008401340c0b2700703504e0040c0c0031208101031280560290194040400c44840380b02007010041510120118901c00c4441701c036a81000f0a91880084c08801810448101c0d840000c01c1242010101410296142c5041400060000f62a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 143655179 1250 143653929 143653933
    0x20312010e040c230406031101080f09070902090402040f1806090507080c0a0905100302070c091a100513090b01020d0e10031a1203041a0403030c0b0601030f06090203150a0e0f04080c 80
    0x1000c030234001c3e0644501e0402c1805c2c1c8407080203880701c0c1c08411195900701d030140b166070022107043c401d1550319001458249001007001d404d140d140c40d200c810b107454680c0042243d692213034481060428034010500140480f130f504100d10b1814010103803500d00c0061500030101c0e40080e4401c2002d004e80c8162000d0308021b4500004141c4030140900254820700301501d80b03401001c4c0020f40d00c040b07401100895010507003a0f100c09074003d403d1000b40002403892806000050120349a441c001504460041c2241078020070148a188006810a0f00f14141e5104001c0c50404281d036a8945100403051075030a031400103602210001500041c1c2c1c0d8402000e60f101c1242070701d0380b00454002008e0400d890321490010b00c0301703016800e441120320a901c401800b01d10f40e0151700b00031454100155502483c107060200b042c001e6044c40b0001ca84541d0010341006a011041c44400c00c0c00705031009541c5015112000080d0a000344c01464041c0180142c0c0380d0030400b00001c08208850054480107a16001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 143656429 1250 143655179 143655191
    0x207140d05011e0b0a0f03230f070306181a07110604080d0501050102070e04030311070f0f060f0b03030304021c120f020c0a1401110f030a020312010e040c2304 70
    0x82c3e01040110010740120000e400c1841d01810b07072034021040c100f10789121410030034480c0f070f40c0c0d20920342e6090304840b2107983d4515050980008020b00081c048105001c018000e000e0640c90b12200303c0d001c3d4080c021140601c0c003040400161b01030703030004400c02e0440c94844c15550701401196080c00405000000740a2103080c4010800c00b80081e000c06040810180401e81c3c17a100126038440030352162035200e803a0940880d0109000e94454034461003505412803500590f41c6070700c000e04031003a0013215985402008030041c85410701c42c1045441c0c1300c0005010300b60080300003e03941d00000c5c001134491040303507500020b151107240e12030380b69503400088180014111140600392020380b40c80900580200b800f4000c00d032510a48030001c1da160581821240c1446200440310200070b401d80c0341c12407145105100d000711080003e0700860f001c95000b52b0b9640e1405905021070032040e072240301110159410f000000b000c81a18205644004a0000f4250040d8040f210030540c0343d40c2860300940b03845 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 143657679 1250 143656429 143656451
    0x80304030308041505130b040507030209010303110c01050c030702090a0b1215010501020109082508190e0301090507030b04080f030a02090301050f07020c0f06070b0708060a090c0207140d0501 84
    0x2465124074090360103807010074003807144042503400c02c5a002200e03042100186c80017517a01c11995800c14040e80466800d41e0300c1f540803614400b800e070007c0d000701b400d0113211b40e041c803401c000040d072404003031030100c0c180711803496103a5a83c042c40300028440c0c0f04540c000b51100340d2560000d1511140117101d802e102d00c00c00c60300c40c0c0300c8080c01c40144c1d50f89501c20000c2065401402001066507000c48410f29065083d01d06249042c0541c40c80b60681d420781038103c000c03e86640192510519100090b039002c160514040d04122500400c28003d9040000c04d80108901045907412aa048250071030590b680e450300414506c2030340d100c0e400010001c0280249046c00d680038102c01c45080d40204a1521110308401441d1012030340c450040e4480ca505a00c40d0030324981103025500302410603801c2602540d10800080b400301c541c3c2000440703c5080140301d140a08020700240400c02c0c04208030380388110003d45598a500a464009503107583d982c43c01c1e00c0d20210071040071381000c02085504490 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 143658929 1250 143657679 143657687
    0x14060a031509050c06030c0c0d02010203010518190c020c010201060f0b07030e01110d020607030b01170c180a090905070e09030a03020304020a080102030f070e030c090f040201030207330204180f060803040303 91
    0xc07951340d0040f4403603902190f89c0d07a0300500c2200c0c1661001491a07031010b4503020705c3d1600d040010040302c001c0040b041140e101e11000d00954241e1052500580b05e0484401d000a00712203aa074400581504030078410040341000108807410340d82c0610301040c400c1c4850006071045d1222290707801c10b91081003080300d400d66006c9107031030264403999003c1c81403216140044a4002d141d00f500000310600c2c40101d0351039110070700105545004100c2045114100c00001182c100c0c40d82d0010045944600c4a001007003418002e05001d445001d10704005410468905540c0e809a002c21f84180341c2d00102140c15540d0701b1f9200c0004245c0d690085d942da00c0c150f180c01c88014801e407051030228400c8844000f140c60b000c41d00842184015000d0445550b86030113002c18070002030000da0500d54204100380100f401583d11030322441604209925035403103808070004510740c01d200102c06034814802030100b5000c0c5500311403000620080482e45810b090b5042c4010b00c001d03031040001d4400014000209504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 143660179 1250 143658929 143658937
    0x228080619020a0e1207050a0314120a091401050d0e010b03010c0201021801051804090311100b0f0f0301060905011202121209060f0705070914060a031509050c06030c 73
    0x16040c1100007040c0c0001c0000507400b884100ea00850740c07541040c3e40341c0c00d0510042540542d04070490300c46942d140e011880c0c0680e10741003696411843c8449946040e401c10042c510380c170140b410a0b241980204000380b418110f80154190780c95000c500c066142c0c8540247c03100880a440d00b0052180400d040c64000c0456144c15406542051411015030b03006109030b90342c0814034001440c1c3d8600d59801101c0aa0202c24200c0d603e0a0307800100c1103a4131a40701d544862803103911050f0307142018800d100d00d08084030003000c03240e5080441c10100d5495803849003001d071000380d07007a06400543c840020701400b5a1303003104050703074a0900009031510004021207802070082d00c000c10301b103001240380c0c0d882e400c102190b090500030400c203170080c60030080020308001d605016141d041030416a28641412201c0e407201c1001e54454124811025220a4041c0c010008980a4140c90314507940e00240c040450310001e4060365800300301c428820700344405459500000c01c0d40369a40f034840491000d80d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 143661429 1250 143660179 143660191
    0x1170a09051002210601050315012303010e010f140105070f0515070f030509060f0c04031401090b06040903020604020402030604150e010f080f0a1e0203010203250c03050702280806 79
    0x44500c1503107660b500c1103c0185c3c09410107030b440c1440c5554213144c042d035034904000c0c000d0400489840703802c2e4083c07161542c241064420840c00d5581c0d490020607088030101a000036042d2401c0074400c106039400300c10b8a0f2880364003130900303030b807a03104500380b4001841000101415a020f00c5040d052030b0700404404c2c030710400d866103908070302101d8007200320304480c400c4500d070b2455403000c004070308081da040d103035543d020340d00a080340c1c6841e45a580d00303e0070300d04031b0030b009221ba134441140e001040301c199020360740040705980400800400d038500035030b25580600041c0c0915130000126410381c40d0b81e0400701ca4450080c400001441d5104041d0240c0c1000340b0a004403c03510b0302e00410a500d021804200c0030716444010321072000c02c0d440d005e2590001d100300304a40c1c441d58003e140181c07020b0001c1c6110301a207035012040915081462800c0840840c0320724100600e500804c00081e8004060310300a9406442081040700c8610070680b01e25107810002040000200d80050a2080010700600c030b20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 143662679 1250 143661429 143661457
    0x12020a240801140105090f0303040b0708040e1b030a0f0609090302070e090c0d03050f041d2509060c05030403021525030905060c10180308130201170a09051002 70
    0x1aa890440f032800c0c02c030200041d40015010411107a1902c1c2000010524074002001d6030302d001c1d030f90141814140d0100328201c51550000c034040201d07002c88a06290710800340c00c1c00741c60300100c466680c0c141e03200044c044914150f640700410382e415490360007100546000c0504024020580c01c01959494092044c54010803030743c07002986040c40810710042100026100c0300003110a5a0280c8072900589940b0100301c00c03e200000f40569100001c04e80c1c2221030414846170b081418040c036698080000c2c1c40e40c664512211107a03003075400307003885003140c03980e1811284c00c0c2c16038a012411446664070196004a201804103120b0400000a084204a001c00d51082c040500b200c100900d011920140100c0c4c54104200150b0800d0401031519903900415140028111286001181c3c9400685c0800420100300401010740284606c0e400c110704481c95680861142d0000303003544880140c0c1640743c0e4444001c2444c101240d081400c100d0f0344a4280c0b8011101204040c00035002040303800070700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 143663929 1250 143662679 143662681
    0x90e01090c050a08060408030a0f1b0f0801060905360f010e040b04060914010615020d090807050616050a08030f06010309020907080702070e04210203030106050412020a2408 76
    0x1074500f480007035044542c448080d080b15a65501e50241c640c10040071a18026115424240074024030302c41c007a0000010058189000f0002d107000f006203421a44440a110344034006020f01c5800400300c0040740c60490381c281c0d2540052003100c409110b4400a884401008004c0e031400f4503400201512866400d14000d8041ea6a2060403043c06802da50103464202e40802080105005401004c41030340180c00081c1902140314280c0e08480d503550082e5a1000072000c0d40b0780040d41441401c201e06114a030240c6410b0a0091080e10f41c1074a100d41ea00c5084002070700024400d01510300704019800c44180e038084502030400700640c1e84115480501c16440350700007500c40d1301034400c80340300c507802911903070003541c5e504015100b882d4064800c01c00d500c42c1503400500c80309961103052096200700c10142d441010600c0b81d240e01800b01904000f5504180700500c803065002c01910300300c40e114034206150302102e0012800300301c2103400c103140c98140400c0076049000c1d121400114103080d60707209652 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 143665179 1250 143663929 143663939
    0x9101d060108062d040b07050903030a030b030f01021312020118060f030b0109030b040318050a0305030c0d08070f080a0f0203040302011401052403092b230a080907090e01090c 77
    0x607404d41101180f038680c82c102080105114500c0180e0015483c1440c0786440004000686190405606000001d8031548005c2503801e05119024101d243d42c0001d60030000c1e21203c914804000d030046494600442c240442560300c6511840340e12074041850f40281e90b1540401010b508880308540e0100e4103000d1503089651090300d11804594102000c0c04c050b0301c03555001c8424061581d000a080402080080f44582d80d20151400540c4540c008543d51a403c048080c2001401440d02c0c0c10b00188908109040d604408003151803c882c1ca4100c2c401c0d40c1d41f116400c01000080801400981701004100800d90158040c1170640100c1041304450380c1e0f21401c00c030182200b42800000810125202c2c44945407840c003468000c001801510f010459010212402ca84054040e00c062921b401da10a0aa43c06c0114441c6401228140403100030740b02000040a00c0f80c1d0140b6401c01c0703440c4000079100760083c881100904100726080c4447c1d41c510f400e1501804500300c060f5000344c2e000d240020303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 143666429 1250 143665179 143665231
    0x1b15071b24051201050d0f02040c0f0909060302010503061207030b0c030106031a0a0909020f0d06090227070e031c02160503160909151803030501080609101d06010806 73
    0x140c050014110541e0fa030309140500030348600310b0104031140f4036801920700060f41d450049021085040d40c662202401c640001889941140c0c402c81c2c2042c50712500f0300150b68041d0032250710410075944ca02040d40c0c200d482070310348841940040d00d08014a400c1c0304820000500540c100e4490b03030350a0184a06120502c23401e00241c411465000b003491504000c5060713140c00459550307000804005017503002c100840c05800342c0c0e55080b580740303648003042030861a0407000c095400c600c0b00305051100307802d000d0844801101401550601400400040081c1e5080040c0e8071410031400160700d070040c0610340070707640d120f52840030081d0015282c030109440c2030001e0141c0350356500000b440039092815070030100401016030240c984a008801003801000365005c0c00c0c4984403207400c01c400f18012030800400711101038200300c01c190014811f00400c90400a48450700c603082c0f00380080d03041410b0141c0f0319000310200e800119400303400300002e051480868127a10500c800c2c0d03585400407070481001c0d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 143667679 1250 143666429 143666437
    0x4020f04050f0711100e06010302150a080403050d0f1b0f020114040803070306080703200612040219050d08180303090102150c070f080c1b15071b2405 66
    0x84000160b000028141d14071440e550441401c000081d41d100f2041000007006540d089103842540d40d20038001001141002d10a18039650141220141059620b181c01484110060300240400101007400001404254415101581e00c40c2d010403094845614250103c904801c2c07000208407080d0f10118807a0040c007030301540c09500b40401c41d0f03940e920390320303001c1070740020300350340d0070075946171404503044800300180c9020318004d40e01c1259454051a10021042d20214040e001d0300c0e090100301d0607000d0003802c0c281c2242d03041b80d100c20036004055520303035003140070303404035510414503100380d030a00c0f56560081104189080c60794a002c3c0e411024140e4a01c62610401d0041e400910f40404103141401665001010380480c070f4980300311901c2e1400c00d0065030341d0550b8641400980058144010010311120300300c0941c0e4240c48030003540c000303041814841ca41038980000040c5c0502049800a0302c148050740704403089420f5511064070442c4914010680c4142903451842c200306c05002e503081d9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 143668929 1250 143667679 143667691
    0x403180803030c0d0914012301150806040f150f03050705060f0703080a0612060501090518101a0a03050a02030f0114060411070b0c0a0f2c0a0b040801020304020f0405 73
    0x40c0c1c2c9800134448400c030003000c1d13045003034491103800038210041031802e02038400034681e1140141785601501c0320094100344180d02140c001d8101065550000c0d0f008100c141d4000821a800640c1590580110014040c41c0d00c4c03401034103022400c007083c1145889048419030f0701a908480019460f101441503a11840d8030805460500f4484940024840c19005a00408150020440701c0e600c41e111030b172402414004407169a150001400340c0d41c01842010341c032a50f04406405c04401c0181c1c0241c440c480c2c4400070303210039200c600e240d05500d100c0c0120b010180c0d024000d101070903070342d04090740c0700c40510074224802d0144030200c0d8200751050099504001b013800710021542c5440b010040104654a18410042020721585c2c000c24844620b240c850007422842ea0340c6e40104082c01804881001c0d10001449140e1243c0c510041031f4400481d082500c00c295102d140130020000741c3d01ca51741750f1048003d480c0c00500800d038100190041d501503071090301e10000740b41f121002c2100f51a03045600c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 143670179 1250 143668929 143668951
    0x30a1404080c04110705010e010506010e03160b0d020927010501050a0e0904020409060203041103120c071a0c100c0e0105091e1c061a0d031202070303060e040318080303 74
    0x8140028900f6922014070b1203003006441c0d203000c3c020741d03d0034295001d2007041c40c4165925010031a10756041a50200c00b520214054080c011440302c030ba1051840c98041c10044990100b918969001175178102c440943d001801e03800721032001e18030201d41c015440005200d00c1c1100f0000a22940190255485080c0399168481002040802d000070010000e000faa4041c1c1c903a03e4100c04a1603510045000f64060340c12224100d01751030074186440d54540410003007150400500710700d0000400c5010540b031032005991000860441b5092282c0940304c40d1541a00544109101c900c41d41da000c1c0da10070145d074a034520701009180055500d80554195550022658071400ca90000158100140058000c2c0154044005a04a0244100d150708200c84d1a46d65180d40f240c41400310741c001c2c05548088447c40d01ca2802da07075000381100c500d240d01c1d151103500400c070356003054040d0f00100040c1c0646188141c0360f103400e0400900e225071000a11140640c3d08034046008000442240e11845030011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 143671429 1250 143670179 143670193
    0x40b19150f1d01090b030f060306010e071704020a05030f033705030402010c0b161e02070312022e050a0c0203090d03050904060e0415050601090605030a09050708030a140408 76
    0x480c1d6015802d400c410305040104100010401e041001c0c081c600401c0c89030626a05440c1200604d89401c00607000f21070065940000c2005145e4003035541d443e8110249000015921a03201190041c2c4142d00100d62500603143c5000000302c0010251860b420301217080d1034424160701c94802440101c00c2c2003002080c220b840600403e0240000303640042c41803400040280c050384580b6448030081c0c44050071a0f0100b041b68204076400b900c0d00419505840b40764011460450029540d04e181e407000410070040c00229107031050007444001c7d4860038811101c0408008295121031f103045003113003e4880c618010100d09030580138484d02a000585400561605107124104516201e403890114100001044620001d40380d5005943c018035070180e41d03a0880c246490b0030342c100e90443d07642030070071841d103000c1104d40d80e8800380380c50845165041c1642d5a0300d4112409000d03118407080038096104003140091512400802000400919590408142d40e111844030b06486688034190071640000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 143672679 1250 143671429 143671457
    0x8060105030a020c100903052d04030b07110d0804120507020d030305090a05010906050405060f101a0d14041209030b011a1308010c140903031602040b19150f 69
    0x1d401460001d00c814100d038403046800d8090000d451b5100d0342140052400700b25401410104040f00a01118150b154404810030b0040c2a005024a100141c103241030f200220b07070b0f102d0040661030600154041a80c0346031092400181261405640844081c6041409820450b00c944d0a540c182ca90040a1000c4040aa1400c60140c04050710408050249452000000b4024840c481c0300b140700390303804030b01450142040c03414580010025111044401e04100c081d51507d4190401d031450311280312000c806150b0f042505026078150070a0081c61b05c07130030540442c205034030035108500c284420b030112480b0090844280c429480700815040c8180d006012441c1c2076004101c40304541d541160411054100b0000100202d40c0007021030b075500c0e62a0710985620201e0010b44c0ba01100c203043c5001c510f100440d55030b11515800c0342e0440d4034021000119039483e00300c0c4a000e00d004122082e038036101103420a00c02d10b548280452200c002602c114014002e081c9a8410b03403e0340c60f44004d0316044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 143673929 1250 143672679 143672681
    0x8030411190311190f030b040b070906171909051506030d092106020f0d05090a150b0d0803090706080f0f01210813060f030e060a0f060b0417070608060105030a 70
    0x510744c034100154089101060014217140480001c2d070081001112500301420180d03042c0c40040d083c00c00f00b103814102800040d410000e249071411040401d0f04069032080c0052001d01c141444042c200f609200c0071400340f01001906000c207801c40280426039460380420160784080091014021656145040286102c1e035091048048000310503c4000790465680300e04030f034001d00140c0100307480802d84100b01442e5228043d84001c68a000781500c1569441d140703460024000c407824516140c981c1c7e08540c0d01c56a0401c14219440468a070322400e2401080d601e440450140d100044d10101c00a03114614810800380556200418070140380d0801500d071008890441d480c01901c03111204d440c0000c0c0c00754008091a175003404200c0d4081e070038450024151021070503002e0815042105107250f81101180040d0001da800f00d001841240d18040d9401a150b5a17211078054400441d001403007204417000c03850446d07081f8098403185502d41030300307a900361415640a4006102400000c900e0040c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 143675179 1250 143673929 143673949
    0x901090f060b07050d0807170f060102030c010f0209030c04050c0d05060117130b0105062a010b030105040803180a080414130e0d3b060708030411190311 67
    0xc0c10205026450b9030140006a010800031201c69100084038400c05601428558001c00c0f10b1400c1c2c1c02c403441d0401803c50300c06000d00100c1504895034046000e5030300800446100b030b206040240480301c0300e070340000029006290885d01078061840c00d0080e034a001c3c459580300e00107100b1441e003042454a1a100101002016541803206143c030040741c030486606000d03c034404d415481c0c1c22000c10361411940c15803041e804180103950a204070100d00880c81e01813113181e5150110740c6480852201214054121142403a401d54600414801840702910045200303003c0007170500c460b81400107803640d070394900c00406003610300d05020511442e8150b400245000c3c0c001801d6030007001200c00e400c0300b250310308440c88200781c3c008542502401d81000422030702c03e0540d40e03240c00200c100801516078400b00e41d088201c11000f490321040a5071b074030055414613034010704540d4503407600e0f1805e940c1d04a55241000d10403010114000091072808908a06403a40251442c11820300c0600f400700e0804 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 143676429 1250 143675179 143675201
    0x250305040f09050915190b0f0d1515050604030b070302130e070f09080d050c160803070302010e0111040521100b04180b04030c05100c0c02040c0201060302090109 71
    0xc010008102150030900c4024002050b80001c0905101c13450342e281112040300d01084000000400040c010324145081e240100e088001c5064010100003d40b1107100c107260347e81c045880740a00c414026688003900714101c0c80719040012040c0201000240001c40c400c055210760b0810042c0f0002c0e00c04899560041581e041c09820405580d00c00000c440b0f05070043c00f400c4c0b46030000c0140e40b5900580840d150409418164205030504c3c00c043c2d10fa010039642403003402800070760344255990801003692a170742010b081a01d02d0791030700305a5840c1c0d404000c094005600705007004a05503010300c1201083c00403200da05d480c051400c01888249401c1c4060194444041e040c41d1180d14802e0100f48042c4000010000ba0840300d0300400084418075005100d006280c034402c00e00280303800060f160880d8241c2405010308100c1c0c504580380c10300e02c81d10b241c4500c0c1040c0750f000803290480c0701900075078401c4805010302c00c00398008a0803500c0910000e50b100310014010042e1074429405000030031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 143677679 1250 143676429 143676437
    0x605030c09011811070f0203160311040e0c03030307091a0a08060405041104050c091804020901031e141f020306031f0f1103040c0e0114040b010e09040501140c2503 72
    0x4c0208003810085400c41d401c26030301c2c40ca90840807400c5207810700802c200302004c00012a41c0e1030035610386a02c000e90312840d0078003d0382e5620013000c1440b8204220300100c8002403ca0703a480c940880000c141c800c0c1c2d403052103d503a403040d122503800c6404c48140e450210710b99a80d071480399030b01400c000c0648400b804c140c0e0491840c12984003507440b01c0c01035a00c20300507211025680c095440034040840340c500c4524855104040500c0010b95460507030504594200a820100362030011564491019220004100214030741d22156051400b080110142002407488424054600e20341710680c4002c50300741c3da0540062450301c03031002544903100300c001c0038600006420344005016100b1910344052400000b0004810042002060072a810140040d0100354070b03d940b40c041290040d001e4084c5040c85140c403210002c00c56407117469985900e10000b428082d6604080c09c02900912284400380031060032400040c015641c00c808840c5606095029041c040aa00c15041c0c08504d0140e400c034100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 143678929 1250 143677679 143677691
    0x909060708070c02090403031a0f03060c03220302010f1a0f12010608030d050402031014070503040609020402040923011505030a202203020f0618040c030207060605030c090118 77
    0x1584840105e94400c500c03c0e14009440c00000000041c1c1040c1d4a6605105446246c110441600d010403070356001218688115206d0f1114512a00c030501409082614015818a00c10070725905412100c01a41c00850400802c1d4a044070105405000c5904ca50030070845100d40340d6605081a100d81d0815404000080c6551110070060665000b08521540a526035081c04290314007071019070010100c1c541d04205501141d056009854002814203050000200c0020f045c401c2c5a00a201b0244d03000304115681c80e1a1030450000b84508400304628080e45480c000c421a5500e1111b8180c5901020151415041340411901640010002007a26850700b00c84e400d80803188030000f004400c0c003040f65498240d038000c1003040500e15103090b111010014420000358455441c1051883c805480f02d40d521884240d170542c01c1030b004000150400d162041e20100e9960540c042d0074403920482d001d204c0f0341ea80380c0c10150758001400450303900400382c82c01084542a115500c0c0c2e04540c41e92404294 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 143680179 1250 143678929 143678933
    0x80405010807170a140a06060206011205030f0310030b130203191406070801150519050d232d0a0209031903020d080609150609030a0813060e0909060708070c 69
    0x2c114000d88400544944603402d242400c260079070100d46c4038080c0d503001c00c040b40c030f441d00c000c0d41c50006105c0d540b43e4200455a94091140038001c8074400c081b01618985d6a080100000b806034a881c807068a1000518010070201c03000405407500b016002001032007050442d03420344003203070424041218906624410803882c2e00042c4000c92066181e612107400940c5451340c590030481a42c5405403c01c90304020b2052000c3c1207010074605810245400d544880030b001c4148000c5c20a12460a00303441803116002404d180000740c68403030360050703181c000051003030f5848010075408100e031a040380c885100011080710f2554060201300f14000e085036a81649070f9811024400102000d40041c0c02009102414a80280c1c02c075400074400c1e949440741e071420a428945d001702c4c0495081c840c420009001c03007555002c0103080520b503009548a6034030405000c0c050b001c40e500340b1030a008101c4040b070340c855070310385210070380d2141c26880090f00040c1d59034070080f680c019008101d4000d0000355140c01c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 143681429 1250 143680179 143680217
    0x7020d021c02030105151906090e0414030c0a1704030201200a1703070906080108061303020102040b0d14070e1c0302010207060e0f010b030f1b12010903081909080405010807 76
    0x20146c088100581c91000500b400c3c8901d080410103040f2555420280130443e040d44101c851040b200c9684540c680d6413100c0c40c000301c01d6044440310305458400851200712007000400c070450130714030030710208080181e6411680f92a0003184006404500c81c8540350208040c1403502d01e880098080a540050320b2540e502c04800a25518202074400d0100400100c160418000700c003809180c24102c54645c50400107a69500c4010801402040b4091000b002c01d07000f501510043c0c5038a42c015601c6a00444001006003d450b00313480c100000070010a99041c0925a03076011010040e000406416007110000c1c9905400b8804408640d0b0070800f030004203160340309211480c0c0202c400782610000b010b445034251200038101074400d070012001c1903541e00000600460803107070458281c21540b0010b000907100705100515480c0d550801d007071081050b6000042c944640c103071100d40c030101c0c91000603000484d2907404004164150800040c0402d60141e009507070301c0041450501420050800214 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 143682679 1250 143681429 143681431
    0x40506040305070614040f03030507031e051e0f03071803020d0303061502010c0806100315030c060f0e0307120213061e090b0603040215040801060b0405011407020d021c02030105 78
    0x81c5081d00f1107007051100035400340c1d1400d0300185003040da500b05420044007216816540c40010103010340020f1003000c15001d500c80381c11203901407040c520101c4031100003805542c042e08600075141120000d40c030004140005540740100401122815a40d4581f420780d0081c15400c4612050740104000200580d03c0f02058003503e07209a502003180c9140054608112034110750740c20070759040000b840c40d480e520030306076507100201f285c4030b4591810104064000301034071000327010444090310011043c89050402481150304598881e60080c07401e44003150102d0ba910320749507154004100c01c1100341041040741d40c1090000f46800c0e00a2041036501c412a41c281e0700c1440b01d42c2c21200001c82180a02c8240d100401e520f500602080c40c08500103613051000810003481604d90f0814030340d80705456015100a0003201000304410f540b1803038000e540c0e4015100d5180011204043c03003054150040985084507806003030750040c50070a9003044900c154035085e0030304094600d0324140140c0c1d400d00400b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 143683929 1250 143682679 143682683
    0x1c1e0201060f0509090a0b06040e01110a090503060f040303050a0b06070c03050d050a09030b070320090312070203031c0b1302040e0609040209070503040602091e0a1a1602060405060403 81
    0x1500d01d18000c0785005a02c1075520652295030100108410a4070100d01e520f170490f801a01c0f600660b40c3d0100080050800310a80c064545c0b03402629402d51207920010803030001c013500c8559605990340c0800d9501c00b002c076007000030340e030f544404103000900136000107821001d03000d004248103036060f0100d84950003603030050340e480c01022000c0081c8541801110000311403071515610700750b1000000740c603800c3c00d0303c0000d001c0c803c850005480248203521209101603e003180c98104c011004003095542c1010361103034440e001d480398405548011000700c480c880e6001d006942010491102214143c1040d03040079505500c4403101c8916590712200000914140c0b14016101da0134840c44512003c0000c00b240d005034007500601000d660340301c11050744442d281c074025a81b40c0c1c032450130780007134065a14503680002e03000184c036a440035244821007205c801a1041d1110b80d07501d600d2101803441d08003080c0c90803902000110322100300c4c10244001c00d07001070710440c81e00b559480072134803d0780144d2003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 143685179 1250 143683929 143683931
    0xb010507020d05030a0f1d2b140c01090515030703060305030406020a0501060801050402220906021206030d08040b13020604030c0306060510030902010e0424060306091104081c1e0201 80
    0x380c2c105c1e40c000c0500346c40300066282030080c030002e420300207062074103241c803482c4a09603c80810001d511a100d0020070305000c540d51072814600c0c0e10703102040700605001c10149001c1c2d4a181859544a441242c04942d030051041c1c019000301c00000041e948003811103020142c0719803010012580810051005040700e42c0144540d29030f50409900b150310603045a1001e03410f02d01030201503540d41031044404c40d038410608254880d1500c66100409000310700600183c00820080c002942d40c0c2c41c22407007000140c0640d0408a00000c2c22190324200f110010302e900c2c00d00d00400c104200074602005640d00c068040781c1307400c0e01d9480d00001c084141d4422074480307443d01424000c070b0030000385042c0340c1c1c02c644c1010302044072a0390029211064040748140030300d0380c0c1c400041c42c48c61206000022094010441c1c0700c1a5110070000b0b014020314010444c07690306002c542203024a600c421101107500c0c0601422686440c4043d201c02e6281c9601c3e80410810041209545d081540314000e41294190300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 143686429 1250 143685179 143685187
    0x10c051617010b0904080d11041206020901030509150c1309110405040b010c0302030a05030606090414060306070509060d0c2016051e1908010c0c0204110301080a03030b010507020d0503 81
    0x4002070a40f980446404e00a00341041071000141c05c85081d1901c0801e242804100c4840240e095500c2e801254440c02d5034003145194001031050030b5000f0034086000380d90030f20071a951002c005aa1b140900e0b00c41581e401210001004070042202910300300007540030109040780d40790b500c0030a56280000522000c000040c04200600d0944140d418603a803c2c02c1200c007a51162b00c002c2d40300d0180f00f11110912800000141c2a0303942c880407990035460040003003011120580b80000304550072542c8500030b01c528404103034840d000700d0684104200082a0310f1a1121004001000c1c00c0030a50032824400c0c2c220720070302520303903110484468000b150000c200304980040840080c0034143d2041c2e0155003600c0c082c001c420015411011400025603403d5a04804106802451511a40301450551a18055144180c0e1100350200c4e428001c030b80500501450082e40d100300c3c4000c0c03041040d0350388921801800203009030400c180c04101410b000d420180f058005c01da1f41488490201c0c1e081e08005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 143687679 1250 143686429 143686469
    0xb09040c050f040f180c020a260c0d03050a11091306091b030b0613030b090c0a060f08090c0306011809080a0507030809010c020d0c0503192a02030a02010c0516 70
    0x10305c0f40320a600341c0300b00511994030f500034041d45030315440002a003e0f001440c100f40c80813440703041d5003a030030324580d105907614020705e10566200d0041451560000b4201800b00b840e11140d0302031003117801000c2d40380300e1a058010040002140040900c0e90055803100c0e00001e4070181481031b0006220340056240c10448003480013070451381e40d103550520846040c00442c9a0f92100218a000d0741d500404c206a0740d110f60604900c2e09401c440c40340c5d800001042d0200c0c40c99800b400c41c0c007110306103481c0c400d020349405a9031034660741d01030340603500359105400400254006187d84410400300c0d83c4000755114080e00c8000c0c0340c0e40040c400a000c550002500d004066001e66082e40c00400710000700684021101c00030f445070001d007010300401c1076403020316080c49003e10494076100c142c80a00d41401e44202c001420014113a100c07208409500c0800c002d107000d544034103640c1c160307008002d05250303640c69006540c07a03103200d8025509481b03480780da1041c0031040010400904800b545a074122010300e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 143688929 1250 143687679 143687699
    0xc07032309091f050402090103020c0607020d2303070f12020c011517070e06060d05130210020303090d0302030703090602070b04022403150f0a0b030a0507090b09040c050f040f 77
    0x240c40200350031021010040e0710b25a1242c103c054070070454000d66201c1210740120003034096130310080c04a01800b01480106900041d1a50686580c0d88410107584100784a200d800560090303417140c1d1001c2080008d030342600c1004a01000903083c10540007150008800300b0884c0c1140348008038680d9075820a0b10810b40d400480f000500307011021111900c540010b15071910164880c5100c40d00e0400049110740e991181915031701015603c040000703142c08180041c1c20550720034164042c0741000103a20132188084212813003030420900500c00340f8004401207009502c002c01c040201941e070160300c00064058001094200d004485050032810140104125041d20154004006420300504110001c009082c0d80d4016414205a600641c920780814003500d810910281d102d0301b040e1020a00e503146601441c022021600b04100d25230791440705956540c034034003440c60245001c3c04139840c14030b01600036284801c0946072540c1409a4091403640c2c580041d001080c141000c40814842c80e408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 143690179 1250 143688929 143688931
    0x1203040308220303120902030c0409050307140d091e030f0303020318071a130e040804030b0601180311031006060c05010e0304030c030201110f10020913050f0c0703230909 75
    0xe5035039011a075491030b0780180803240c0d1720318542d441a44502d00300055580c1448445400034001d4818010340d881c0e0320b001e645942c04001c04544030400d8581030420708000003245420b4880540303075000010b0604941007410b42d109503136a149813003206004000079904404001903176202c2c0d02c0143c1c40b400c100144400e50300d002e82c03522110368494801000200025004c0c200da510401101e581d40e101503044402c1014081e412484240041d0400d0104010f441030080085030301841031860180c0f2480011651003d10360310703c08190511f0030741030000c40c9901c1d81ca5010704000070200d0b145c02d5101851072066031840c0c5d00c01c81c04034000310318240502c0402c5c082c003820520300d500030710b1416046545155251025000c081e040003008445407010080400804c69418080022503200443d40c2340710344080d500031144036008210034400302c128400b16020f030600cc1c040c4108100710640d682140c00409810000043c1d0800107220b88040c103810300b03641e0540c40c120700203040e1a0f944038420f05010071210 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 143691429 1250 143690179 143690227
    0x240708060108040206031f031a091009050601090f020714061e16140c0a150608010b090403180e04050d11030f030610050405041a120c010e06091203040308 68
    0x10320b00308000040c1e07500c00032254070495519000040b08000c20300c4594641c0380d078200406054007140540b00714508140050b11070608101100c0021681d400d800003070702c65401c0028123590045005100010340d0b900030084402d000b090060520840352107841d4207048000060006070003890034000307881448080d0f8004090055069040360a10315005039081034a095031004010b1058900c010542d10f40d0125180340284104407156085581804245070022403000c1128915004000500c110f0600600340c0c0400014020941e03550b8a880c00d6030900b56090b6030b0054031084910101c0c0f00d810381c13081e040c0154002d01c024090b40c00483c0c40545015030580d42000107034020f000b04c0301c504e240e4004a990240c000d44424011a031841019506070080c0d8104540c01824102211507500007020884034490702140c2805011808450590315100b048120f5030004610b030040c0e51160a02c0713001040544400341c401c84044c01020b01507403d5400c02e0f04115a004800a805001340c45038030350f6942044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 143692679 1250 143691429 143691437
    0x912020a0201020a020906010e06030f01090f06080307110a0b07081b0303041211150a0903030c0801082d0102040b0703020106140a06110c0306070207050114030f0f092407080601 78
    0x1402580010b136032110442d000074821200800000c1c0b169125003507424204402074030082d101d080c01c00c801d500600090141c2100280f403d880da14070005036015007021201d401020b03518299964480b101050b031410811500403404202c0052230346c1e540e40090180c42d0050141c00d40b035504200d0748121a40e0034000d80482039100340b0511020071100341e07010170a80d40d142809818002043d120604241c1c5014600a40341c85c858100494450710340c00611a95110b40d400700701c1031105180a4030908420b002c1d40c40194404a25075900041e21140c04c0c03620a40f24420070000c0441389195421390b40140c100015020010aa807c1003680902812002d055204050b410142480020440b24010b500c514000c001030003e201441000520dd42d00e11040e000d404d45006142c16400a540c0f407c00e482118000386045005d2448000345030262402200c10f5900d01480c0d4841d00e0074200c44190140502510307005031004509100021204a01c2c0425045001c0d003643c982048060318684c00101214140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 143693929 1250 143692679 143692693
    0x605060d0e1207021507110d0609031b03080601050a03090203010905011e0912030207020d05012a050c030a0c080c01050703050109050a020a0c021207170f0c061305042d091202 77
    0x10b03518200085440701116880740e48078105070038001f003100304a1038400c0d08802c00201d440d041c040030b0340240403654080d0f1102d052a42c0c01601c0c0704245030740c3c0c070f42c0580041c5800d40490003542c4207100a001015040c6400b040520081e0002404c4a0a948085881c0e0795205c2802d0036403281304441601d09100220200440344850720380c144e440f4840b15401c3c08166000509a08640d0340320030316960300d40c108000704582c1031a03040110f000c80f001000480385c540507048031480144150100c601880103000903605012a404081c0c80302d0910000c1241e040034240820290001c00f40303d00c5100d2419564081950351401d030502040310400f42c0108041c500400183c2c8901790040401481c49606030b6144000f01104407625003084159040194903040c08a155000440300054000072100c0c1d880a0f00e03020a421401c10819100f134541c841224501c0b56010859403805034010041021468841c4615544540201c04800051101e02600c107540d107040034180145400c8a13145415180010500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 143695179 1250 143693929 143693933
    0x10905030a0302030d02030408040801140f0a0605030703080706020418021809070507031d030307030809070815040311010f0507050c0706260a0e03030f04030212120f0a0605060d0e1207 81
    0x2248200c00c1702c0200340d0b0300040421b08020f07421017110b00a0004078020040310341c94401b0b0000002047e1441c42400081c0004107900c8482841013108461008004041c1030340345a44006564000381d0b82070711050350901c40010500d001c50050388080141c80001aa590f07270207001c01c1e0a58000b88003090158480310200404641c025080324800f64040c00c0c02e11455142e0003002400351654440712703405000201d405010513800051090040340e040081c5da103030585801032180d89100c020700440d4030004000118004c00d004864180c0b150360413100100c0c0664460110030103895003500d980c40015400074619030401410300c202c0300a0005850001d2000941c84558105105d44201000906c005007001c2410001243d001d000000c0101056984916040d115401104030440e0281c015004a0340045500c003000c0b4116107441c000380480581341c2e11800e042000c07284000303140424072681d41c0740200e142d170765607030240c0000c405a1391f01196010f00d80304428100284407040c01e02c0e10000380070b2940 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 143696429 1250 143695179 143695183
    0x1002070c0b0309010f0c0513050306070207051005041d06130506060f130e01030b010f06021207082218060b3a020d0204050f09070206070305090f01020c0c010905030a0302 75
    0x4111071840d4000c0703850b6100e56050074010811750391005200f91604003000b8900360001c000d40001342c440c500042013169034905054561030111600e0006070005d00d400e10551904c0c0080602100040c9007480c18683c035008001c0402e03850103030018200c03040c02c1c10041e441c078040c1c0d6018044d1400d000c05200c035062000100300d41e40544014228120408034901021b4a03146082d20001c150004d11400f06507500d00304001003480a0140e000203910400c0b0100d4000d00002d00c41c6940140e51004030f203403400d2901c900c04150000d001d48030403111810b90750000d01d0243c00c0c03e40003410b180210306015080304461030044a959501900d450541808800780280c440000341e100807100d0006141a10b551210030300c41c185124030701c00d100602c045900239a10342d883d40a0415608282c80c00c810b07041c1c2140c00c1044200c0100c1c1c808006074000000220854401c1d00110f400200c0c003c1142d01c044030045029003a600300184c20000c1d50b00c4000c8003103403913901000c99402808280c2c0a01042078054030025 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 143697679 1250 143696429 143696453
    0x12020f06070b0c0d020c0303100303020d140d1104090e010e0708070f032a030602041406090f0d031e0201020706060608010b0a030b030c12030304111e010c06110403050609100207 78
    0x7614030f460125041404000c950100c0341e039190060f081d0380e40c0303284c408011000c1d0300d81400141c00510800510041c0ca070700950350058601103410525041150344100c4801800080d14885d852070790510000824000500035240000b10440005c60480103452900381343c262154040c16640c0d01001e010010703444000d01d40d00a880c0c1050241112214400c41c41580d800995a50410050320800003c24403485034058403c1e80d810000c20b00b1210011010041c41d401561010b0758400410103a004282c946a10b1403220f083c070a09003544254003c0314040103020003a03d01c0f0004d070b500000c00000f08011885408050002030804800da541010f0311440345000e4002140c09056480706520030070b80c1c0400c412440e01c24010005c03032028120780c5829450780c005903011a144410746018040b10300e0301c1c1181c064013079541210001070341c00d110011529908890341c180c420940d034070307184d612034000040204080c500800c010300442c20402e010600c1c0c580f100f8441032845d40f0500c048000182008000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 143698929 1250 143697679 143697691
    0x60302030405330907061202130306050a060e0112050a02101812031106090318041409030403021809030406110313080c01030c020f3412020f06070b 65
    0x58899545207480d9240010302001043c0340c1c0c580441d84441c0180d1100d8401890245024082007900d400e203056076500010702540021400384a000918044143d0140601208075004241280d5407611072400300d6006448900480c0c0d2100e800307108a002984c0200d004100ca6803941250f095551150b544030030203990024070412000c00729242807403142c68203c226001c0d0a441c0c1048550b07034066410542c1d03416000301e01185000702c2192000700003240340d03849080d6500166181007080b40711003201403410504140d01681e940c5c1c0741129080c00142007846220303a10011a03556055004001340d40204c89481d840307131a880004c002c610034002c0107640840b501c500b08240300d4480c0010b0241140202103003075514020600000074240c1c400200700e03000510a803000c1001c400c200d001203032280e103c200c40b45440e5203c0300001c0d14010040700b03c074501562111082c540e007072604c20040f06111043c0d026916024a0300ca071102075107800c40c8040c0007420202d83d42071408010b80d6410301003503402890 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 143700179 1250 143698929 143698931
    0x1608011409060303040b0a0c0b09150130050f160f050402030411060a1e0509090135070504060e0420011e0809060a0507120504020a1502010f1a0a0603 66
    0x89002d5803010401d40b000781c0300300c0009136110303101540300034820b01030210f059032451000400701e404220041404140210b203030940b00301c04c0e824074405035280f0284208040038010389501002d890340315400e072100300c0f51007500030740001000110b40900d040c000c04501070031040341007410070000c6004409041100d0341a41c01686a9031030382050080c0c14520000707680c002c2d00002d88540c4895003c01ca28119642d4444928005101c10800311030078002e60000540005400c8010321001850502c1d40d400310740341911030500307051010000b038a00300c00a030b10250039500c40402841a45002d005450240642e000001c006141c00e031a0911112941020700910460520b14000203034800c003004111044d020003500038050444c24010700e100700c111001c402034050000490030311a040d010f1140641000d07907a10f81c1102035441d094005100142c0100d80c042d00e60540040c1880200300100344692007130f00006001048264104181e400d0507000d038106141c4004881800e82e944069201500c80e20310b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 143701429 1250 143700179 143700181
    0x30304170f0d090c0603021602010c02040e0a080d060b09011b0c0f0b04050f060c07061b0209010b03060102010e0d0f0e010e1806010f050705060103020d030c0c06081608011409 77
    0x51000001d00c80c68055041d00000040c1100049845412100110b485112442c9080e0780e152406c034102d024406808654440707084c100e0b0050f61040d0007840c0303441d0004000040c14405151090f10340581c03114200c50007a4041110040310341d07284991001803515401c03c83c03600c0101c900007441c107450712140d4000c01441d5102007052007107198207a40a0b00142d00714404141d1104500c0b4060b41092180301e11607042c14003241da01c0e0a12401340c0e020290300200812080d030030203100b50b419060501a40c244d007a0803494074030160381c40742400c600806103001001e03a68140b43c40020300350b40c01d03041200940c0d0303c42090f02c07858561003015001e060505181a04040307112034012142401ca0b54607940e0701a160f500e400c0e05583c0c268640074003c440980356114400068881030310640611000589590080b20040001d42404010010441d200c0d2070304650340b01c4c035951842041d9407107400c504000340c1804104030640d42c0c008640d44079032290b401d16400541c9000302101180e01040036450003201950 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 143702679 1250 143701429 143701463
    0x80304061d0a060605040e070302061605030d090b01030204050f0403080703021608041d0708010b041202010e0402030a06030b090304140d0602090312090406091e050702030405040c02070509010f08030304 89
    0x104481049881d00a803400d103595410326001502070b9000303607440b40f031400c64620800840000c94070308581e0302401c5141030001180696500c0c0a0400d02502c030b0740001c00090650036034511503110b03814070803a01034215504500500084a1000300403809202c04441880042900f114410b07511203014500541c0e2407034855004690504181402803402c03902080c01700f40c1800000c1175905007023240c3d0410510755038140040b0f40d01003007842662080d100c100300502c0040064684171140720b0040c10984e44000c0c498000c203003241d004407a1305402d942d50b1071041c01040411000303540c0104500c0015030416041400d1190003000c85040684203144103d603030700c200b000d69010b903800c2d058002d059030109500c1c10000340c1564000b001c00c07807107a40750281c00705240c82e0318441c1d080c0280c448884d5000390540300c1e8501004020141c007140c15440300348800145599203000c1c40a50701ca0983c040c0c1001c0b480c250900c1314441041e08254080c10800e24203000010000080e07136440358100a801c61042120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 143703929 1250 143702679 143702711
    0x50c040207320d091e030f0f0503070b090c040f0c1205190c110706091d070c120c060f0204080a020603040303020d0c050c0d0f020606010c05071211010206090a08030406 74
    0xc12040381203401480503c0011035004810242100c20b100070310210b6500c03607000071051107000d0100a00032800e9600a401107001c001c09489601d2064040340d24003d82911981c094410131204000d007503210400001260406000300700402e555003c1c20b00101c020079001510700300c0c010f5141c440701982c2c2c40c00140b103a034020038012050388040e41e041011040c01c180003041034903151500c20440c402c0b010002076551189505c04c0440d170b0b40b11595944501d01000011805401034414030401803504524002714004411010b0005425281d08201c031003c0e24241c82524031270403a0485452061004000092010603005d0001e581244c92660b682e41c2c919040c0c000f8010044002d0606240c07012540e01d05411000038070b520810001200c1c040001e0807400ca6000c04000003140060300100d0218485500030940d80c1031281c030643c295070419444d08940d0b407101c414203800b9501c000d480c0c0a9100c4958051000c25045055040540003105098568a4144c07001400041c0340565820050780d8800c05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 143705035 1106 143703929 143704013
    0x150b300702012c0a03111c030b012d0c030c060507030c08160e01050f0f0c030912061b210709030204060906060915020c0307060309050c040207 63
    0x4c0e660381103c007041c9600c0309040b64030418030500c1012854140d0501e02c2e040c280d42c0001d4040e12003000404800c141f071041c100310284400184000800d00004014031595802c02402026041c40c088448115040010340001d103002c081c0a841d59150304580c040945a40e100b00907a102d9416055001c0040600310380841c040c07090703078800d07540510041c1a02048040b0085e080101c01d1241a000b940b00e000005040d8000050415071340c0f6044c1d003200c07440580107004041b1803030007403d450300b042480700c0001c621180128550070b40c0c1d0038400015040c40b14002c0d0f9010b4a080102003d0320454543c001248250704008020804400b94440d103411180030359508a0007620740b07a01c06005800740d43c440c0c0d0442c010075a401c407003034808000b08001071103540d030001400c100768185a42003180788082c5034495401003001c070011981214a0308080414070000c0200c0030b6081d0001148d4100c = true := by decide +kernel

theorem cover : BRFrame.Cov 143525179 143705035 := by
  have h0 := BRFrame.cov_init 143525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 143525179 ≤ n) (h2 : n < 143705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
