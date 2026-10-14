-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3022
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:25:31.819975+00:00
-- url     : https://prove2.me/submissions/4c91bdca-4e6e-4583-91ed-20c758f71c56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 543345323 ≤ n < 543525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 543346573 1250 543345323 543345329
    0x40806010518070504150314040320010212010e04020d0c0303050310141f020709060f05030d020d080406020901110a0515060111281712010b0720060d0e01150b04050a 73
    0x380d8480e1002c0c03141c1b0100c00030802490b09140e101d2500c000e00041c164000784000a1044103a150135079208284482803c03403040d548003803080d10039400100180d0030002c401c00e40c0107001400c590110780c2c60b90340c5c080300c07003105400441c0464004820712000b203204071701c400c002d01b01c090b4040ba0740c0012100001c3d529580d00f0342e0102803408940724514054824001c0c40001d02c0041410b00c60282c990589e03801103101030155501a10030429440480d504c001070440c6036001d540c6500105444548489010394804110380e4103201c2c0c2d40c030000480c048100001d046039030050f0003a0a00e0308a010030b1180c50400641298100805103000c9110407101207030520603c407214a0580b00090700072084040c0c3d4000d060701501003610590f1729800100d80b40e00038036520401e4a84060f440e80c80f090308008602900102030950000d495071140b098040d00007020180e04020030300c5090115900c46031040d51003507407807003107140d44408140c51010034000e1210081c100580000c0e0a00d8140008241c1418040c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 543347823 1250 543346573 543346589
    0x2604020d15020f04050301140403090e04021801090c081803042c04080d0c020a0b0a020903010e1b030610032d08040e0f0604060b0f0a050906040806010518070504 71
    0xc0140d034100001c04601c20000c105141d01507440d1044007110100a8004c4c1c407502d17019500304255001402405d90b0001c0c070a44c3d0545540c00110308000c8000d001010040040360040752603982003105400d102500d0340209010903000c60800001d00d0002c204a0025005c2001c20380f990112a00d401004070654090354a6520800f210480c403180c880d224641030a0021075201d2107600b0701092045d000000c11141c80749600c1417040f143c0010040ba42e44900d1040038040908407400f0821140a80d00203102c5070707100800100343c4a010201305800d02c081142401012002c21281441074241802501d034004648218102190b2440c0c17503980c3c000081510640c03000b800416061124164101581c8083c1e07082441991900d81703032800001c08000075200b038103d211000c0001021840c141c015541644c103c59515414000600851980c42d0002d07103101041c49030a00c62640130344c5a5601610083c09140300034007440d458001446035000c88062500501001e96080000d04d41c1c20104407812120b200c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 543349073 1250 543347823 543347839
    0x90b030a060c0809060903032203020c030706110f120706050403140d1e0203060f06030901020d0504060902012c01080402010512040b0f06010e0904020d0609140d260402 74
    0x5540068200290004024403942c9060a82410345901101c2c0500ca4161241101d42980700ca210440d0740c0e0000702c910307c9580e844901d021400034070020b041c81e03a880c420300440e508802e4800010f810055113400a80000e496100b00390035407003040040e410100380e05005090028800506c130310300c0b4414008060141c0b03407079001240070540700350388058001c81045d621039114400ca640e0800546a600100419004072404544440c0c44500c01c8038003c1c0710043c00c030441240701505104854100411114440d5030a000b00120816580169403007a07110710b50000c0e94401910024041c0382c4580c4400e42110642c41d016028010741c00302c145440c0c8000d0808142d940d40310310040751144a485129900700c0504000d04c810002041c01c028090841d4602102003a0381c2d1500460300b007141140d00d540d005051a0214025040c000c02c10b11410707005800100e201ca084d0740f1402ca41d16a001c610182030340c040c0d2900c90004d0f03800201140340d000e21040410300f0f65155420041746542c00f07040070740300c1c6200f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 543350323 1250 543349073 543349091
    0xf0604090f1b141608070b0702011b1e230f1b030906030406180f06050601031109060d1e06030b040312020403020609100c02040f0b09011e27060f140f01080109 70
    0x70170401c1c0d80a0640c0b190903ca61032034800c000a000e000d0b403000400303101000402c000c10343c90058169545806e030040c8480e0450380c120b64111000d00111a200c43c101c1c40911200a140450000820000e031040442c40ea55089a8400078401c00300300c814008950418440c0a031103685500440c0d8126800030408502d0381c0e40071801c47e10341c1e09039a000500313500c25543c0f16010400241c110a1080600340c03800c10000c540e50b080707100750344112200325600107410400310110100c00d0b84440c440c5c807050000c280c001a100c407003181c04c941c0150401d07625502520100400c165210011004035407031480190b00346443c40d40400c0c01402a0350060b03100386030b0b455001c0c0006124070524810176070018401d000c070015045841d001068100791140c06202c0311400820302c0e00c2042000d00300640d120381141d07550b030720f0400c0341030f440a1842440c00c01c8401840c10703108030f03a003036001e51400f50032002410090a032804c1850000310b0140d04a00703004402504c8001c2c1c060380c100003807030704540b4812004208404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 543351573 1250 543350323 543350333
    0xf070f051f030b04150905090c011b0302011508062220131a010210110a1407080406020102090a05030a03090302060a0c0602070809030c0910050f0604090f1b1416 71
    0x200c4003c1190840e180409001d08084441844002c036161907100300507a0b161900f05544905204101a010800c02107404030840052058040954028800020824a6000103040c1d0394440d601200c01540000241302d6207d9001c429a80324801680072100e050040c1e07950b030603003030050008404521001e94410340300c544400011443c1d48007584801c207c0300c90401400102c0e0b02c1c0a00300710740140b1031100800308420151040e1008074203000300e002d040025006013112400c03036012700e0000940040c400000007a06840290019204079000941c460301100184024000c039640301a00c20f074030001c482d501280e0410b010205903901030307034056a42c07204c001c1c5c10b0390803442c41080100f54030b1001683e035007800302e2400075081d8100100d05444003031210404004c2c84c3c00e4183e542008151003d40100200e25005940207910b8a02034405800d060361609220122281d51304a466900c7d111a1140500e0403001984030170b00c1003d044c49800d01d41a0b41d2004c415001c1c04142e00419032004e00501d0501c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 543352823 1250 543351573 543351581
    0x8060411040e131202010c0c020d020103020f07050d020d0c150e071208090301060b0c070909030e0d060b0a0e1e0402030c04060308130e01060c080d0b030607020f070f051f03 76
    0x40010014255050080401d90300f03095888056a400c1055110031501600c10b000d90000603006039100d43c00c074061b6800300644c854408204a051550070480110002100e40103080480c1c019400303016a248000e80181c03d1202d4404031804000d2940c03003000014021149010100514060005e802c1c5000000742e0301d049040d810240001d8202c501090400c0721490050280b040182c0081c41400da991800c210640680c098069041c0c029440c2404020480d5016207621703402490b209070243c9441c808965858a0480305480003600c0b25081045402c0c80c514040c01442c2c1101c44100c1490f0442d103a10700720b540c45666039a0700c1c40c11001b00d029540c0412aa240304c60001700104942d580c2c03132808082d16401040c0e6444070041400b400224480201142da048402c15102c45140c20600c1d580c06100d54403580e2175142080c0e130b9141d110800c0c1c80400c02c241c0b184000d600244640180308002901c2c107003c550000011140c0381c1018402510742c400c070005140f4280b920209100200381c2c05a01034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 543354073 1250 543352823 543352829
    0xb07030b12060a020c01060e010510080712050f07030515011b2102151e010b0a03090c03060515030102210702070b0310050a05011e18090203010803030403110d0806041104 75
    0x60720518092007043e030859401840701120b00e50003000026911622580641303002d2058503880031078900311594207030091a890382d00400c80d150036038050801004c3e90301202c0003506c8040f401e000400412145d40e03014440d0355040384003030201d43d1214002000013000c5091415105070907421402100040041d450200612030190052080e40903c59842c02955000c05220035120b240000b4040b910000a001c0007400740e12141d4003c0c09142e01700304042006502c802c80d100c00301950b80042c1300204945110400181d031242d503010450341005800041c005801481e564030036441088010342080890030352602c0190000c0000101c1d80d10303120140e0400b02960300040000e58004100041c41c006080b00c801610801c0b200e0907001901d910044500b003c050700081d8a001c00500034000d1280501c122800c90074299294902c03040c0c90301c0384030061360020390120740c96078004030a101c100354011410955a111000091403680010000203061203405002c00b4040c1e5034940300085501d40c1c0c00115409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 543355323 1250 543354073 543354109
    0x3c06120b0403201b120d030b03061018050702030f0c060108100e031e0408070e151c031d0901121709011d03030409061706130b07030b 59
    0x42003400d04049000c01114200d00050312251210041034942101d4450020b40310000c0c000341c3c0c00c100310085102c040200d480d52052800310b00d070340980d40801240100d5422641c0108030301c04604245031802001420545c50920402010300014400c0d6a000084851803030001c00c1544a040f001c5c1d0452084441c00400b44400042820902030009180340c103d17100481240c504007543d010400469107800c4141c425a0400c00c00706810704150710300501464421400c9515281d0740da0307511498505a580b14840011100c0b08108072000013101d460001042238480354036041c1d9614403000e9003900030300c00400788071a40e01c0c4581c005208414a61202801400e00111561120f0048229088100045a100c5a0804201c6500d544c420903501400c40613110704083c00204190807983c514141d81e51509803005000018101070305008520082c0948490f80e604442f10b11212410144001c0c46564440070105940000442041e03041c0e6204809107800540b011300b04000411900075026203000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 543356573 1250 543355323 543355349
    0xf0702060705150901090c0302101808011d07030206091507020306131401151827020a0609080a080f1611040c140712020f07090605043c06 61
    0xc00000141180b070b440c484125840441e65483e10b0142a1134034020028500587c00008000509180d401080307480d4103070803c0c40d1000690310003101c02260581c400e40c00c070307910b81c0800d02110155406000140d1800405015040c2c115008507001d0310403109118000c600005c400f80410f80000e0580c2c9015038018203589950402c900c4000c07090702d403840c050351150042c00403090150014400d9070f6030895181c1d80a40441c0c5000d5507299542000c0c87e8a00f900c0b85c0300d80803010ad41034014103021102d020781d004070003001040d005000550341d45400040178404061414460800001000340045901c0881f55540d0b1071803100c960341c903014034948418440606000c0c0010051002e09890a000d0151000c101590280c0310480d41c0b00c80e40b810b0080462410428140490346903002100b502c3c80a004071440e040c05201e01c0b40c9003038000d0741704611159880c0f1040c0060301d028001d41c1c185e650b6403a200c4000080701c0b103071f4814024240072024100d260200310102d020045e900300720000d040c510304042c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 543357823 1250 543356573 543356587
    0x1c11100c02070608070c050c1507081b060c0408060105060a110d090612060e04020d06151509090b0303030a0b0111010f05190207050d11150c07060b03120706020f070206 74
    0x303942c40105001e82c0e0041581c180c001104507124601030311001d0303080300c01819032400030014410000d800d041c0701e21404400308205004241002c006010b071002d2070340c00a802e01d203554002420000c3c05000f0158041c070130003041224031000100c050540d00100d4000740c0e02e000420307003602c24030080175080c40d00780544494101130f241c0040d590802c41d40701d50cc2d20100000040c0100301151500d002e200b1403012040b0102d400360600a510592152041c9000200c49003690743ca00048001d032392100e0004001b100004540d43c0c3c1c0031511400814640c0400d00194140c0000680c07680001010a1b0040342e582c1030040311a03204503154208400350a00800128901c211540d01402c4c080798016a40c0c1d80c107501c0d15500c91014401c450340b00360041c01504115401040848a034540c9040c40115441407129040f400c0d00011b2516000d144c040d0262603581d4201e15027101a14000c01d4403611075000040020340c0e4000f5001103c0b12036510000060761002030300032910307441c00380f90f1019400040c045004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 543359073 1250 543357823 543357827
    0x301230a0603052401050a05030402151911070f0311150406020102040305160b04180609180209072102130801090303020703020f0c0a0909080702090705130501021c11100c 75
    0x1e503011304000e0700e810078070b5080890340412003200c1c4100c00c0d000400800041c0d04007881171015680041c80100780301e00b040004000715100b40c0103a04585540c1c0d41c82007900d11016082000c01540c4114507003d0a2914030305114044107400a120140c11510580620007903581d45d00d020b250040d1203404101d450b9916508024000c0d082804200d0b500d1140024200b0008410030488084404101c242c034501420320642c00ba2141c3d1480200c000562110030210b01003410307000300050900b980d41d00d004140345900400c040701e0005045a01400000c603501c400a00d4114100d0011242081d009070b038410402443e800080c5042e807101600c2d5203000c01007030400d81d1640040085070b029a0072103451f4410340441d179484040c12b106c01039011601c00402c01c5010000d8005450881c0204101030404e0241c1c2c0201e03082602c125074840004400081c41500254020345401c042c080a1000302110b0346410780c000c00c1e12074444800010b000c2581c60015030b40d1420411841c0e00009500c0c1072100b00d00320080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 543360323 1250 543359073 543359081
    0x101a091515070b160207080a0809040f090c0b0906070209090d14040b0703030f020f1605011503020315090109050f150106050f0a23130305071403030301230a0603 71
    0x29a610403851003440390401800350003070300c091540012001046440e20080b405841e0384c284040b07400e42c000d20b0400100014140010300c14075001c1d0f9402d03550343e00060208000c8840380d40920003041d01e400da244010810184081c000c1c0d4030700203002980d500110002400b140030b03018001350700541800401c44440e4010952603210001a22552150004010050340300d01076405103482210090201402080c0b280d0059400710741494401440c0840c5526900c00c66400b0ba0207030510342900040d04c1d02007010074484c01041d15464021034040a045900080d00c80c00310103a0203c607900000085501c101c000e502410751558044203c81c3c4500c1c00011403a15001d582c00c05100c1d1015130000018214041d00450b02c2003200d028101c2d00e000b100d14401d907400d1390b0301c1550110240350700031118031441900c0e0081051612500050301e83ca4035500e07201d850852150000101c83c0c00c00101e51005807400421380341076904940300c2c0c24958a0460181c890415200b500355407062540c80002005038150380 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 543361573 1250 543360323 543360361
    0xf110d0305101a0415020705180a0906020c06060f01030606020d0309020604150c110904150203090c040f241a1b03030403030209091503031e130b03010f060305040203101a09 76
    0x1340580d1601c8034505c09a840b04040d04c1440e800415404001e241102c4145030030b42c2c032940c0e61034001150b94864031524201d030003601088001d41e01200c1809504d01c0c0410182e500074800340781c24407140b81402030080d10b41081c04005014151103103090700440d9030b0360f819a806040c84808249211070100380c01815144104000e6814041582c9414031504001c0032041c402c07908242400d4462400c035807004001d600c0280700c02c1d405e000d010710403090380d646c900411035124580351010820b885000e102c0240071421826281c0300740414038042008410703888401d00c00c405400203c0303840e01d00c1d00140e54961542813080fa20a80000002c0104058159001e014600000d0b2180e4440d07645101a070982900400710041e410390017884012640d11452550000499901c2800781c240405540c00002e050100d4000c000d0319200440180401c840240300c900042009160504c528209500401d4072440718021101e503d9444130b0541d9000100d100020f0318a0001511400306860141d00c01c14080007455 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 543362823 1250 543361573 543361589
    0x1d0612040c170a1106070b0708090f06060a05150f030f0a05090c090406051806040b04030e0303130501082d0a06080f1005180a0b070f110d0305101a04 66
    0x103100840c2900490020301241c2d1409801000355030740a4682d00813080102c01e2840d070000e01003003054002103103044000d016600d01c0c0c455041904000744600d05201c42603114905a030700c80020400181e48a680b40021610181c9242c0d4004902c0c04140314540b1601d011181d48a00010600c65459405107082d4460f81c0100810000c3c6d84885000a41f0b4280d4000c90aa00c402001c01003000b0941d90b0b032009070090301681100d02e1186452803035a007400303402c40b400e4424a580c101048241600052031300c0000008901561030300719004180c100b0b18406010720303410020610005615601070195003412090b00b507410007a007400f00380741c900ca5807904840070235640d8104140010031010024849014100c050017601031030307002c4c1c00b81070300401d0001c2c4a0350807200390960240f0081000d0182c4402e0301d002c2c0c250542546056a0301415158403d20b1a03c200030603032698079074140c0040b07400301000c001442c01251607210204400000f0030070341c009440107040c0407812003000103040d002f07100700ca0040c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 543364073 1250 543362823 543362843
    0xd0e0f1801082811011202040f140f09010602060403050d0f020403050307060f0b0105040302040908120c0406030501050609010525051006030c0e06180403030212070906120606050a1d061204 83
    0x20300200010f02e0003051500381508503100c0350b00078440714083c40c0c0e0704070006042994902019045008a900009490211071052004d60511075440b900b1004165a050619454950000e43d01d450080014041000204000c5280e61081c0c03c0314000990b00380080d512140c403810300640320f0b4013407803003101c41515207110326810f0b28407806007582c100c505131038076814030b440c5800b40405072072080c1007114202001c03c0a204035030020080c103070088030840e504a0311641005405000c0f64010b07085188111001d111400c0141e07844412501e01c1ea02155402c0000c3d0b0200582c3d4500303440f035801c0107040307000300102d50151078080d601050449010301604c140305541e5842203483c070700050310f40f6900f000d14060f6101041c2401121940c12a10a01d001403034401c4403921030343c0081064880c0e000090705200d003009050ba1210b0031407400c00c1a408100100b5107480d1000e04188614454078080c0022060201028101020034900000010707115664400444c2c8500615030310803902142e1007414 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 543365323 1250 543364073 543364123
    0x60e1806060907110703020a0618082a18090d02071205030403020d02180405030301030c0b12041b051201020a08070c080909060f030307050f010e0d0e0f180108 70
    0xe1240d018400c00703824008103031601c4004031005165158202010300c6038107000001030f152035140000802003641d4a109800080719425281c0b03035290700880c41c9522119112922020040e015406103507960340c59020740c0409400f24014060524103902e821041000704140f101021032051070175400c9034242c42d051600d64400340720024800401401540c02840b09100500f415907075609141c3c001031028401d81c0b4a29002d001650040320112040d4101000410400c50440c058101411520022900f090f41c408000390030004000c2c0050b00c848822280720341c40080c04540c00010b06000b410549402c098011081e010b50f00c20600b40c03001882400004407414130418809503015401a422803400c0d1005041010080001e0400d41e804003040102c005070341d80820050174841d200e40080e01b01c20340501c5405003140c01810091400d030300045c0d400b4040c41d9000c1007400340c00700100d60125181c10f007080414140c180d1045d00405019850001003103405001807041000c550899001d410703800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 543366573 1250 543365323 543365371
    0xe010609060f0e0a0209090a0f0b0409030e0f061908040c050f010215101d0405070605040f061b0506040c0e2401051b010216030909060303020a080705030c01060e 71
    0x42601c90411510a410703001d21803000000f1103107401000084000d401c00c1452800201c1c0500b00396090302810f9034608030703500822068007078407a43c0403084038100140043c40d02c000d03104014400c0b50902ca0802001c02e01805d95130036080c1c4040003840c050003059814000006018903400b40e5040d10880340c0d03480c0001d25450f00c194801c01050f01030f40604603040701c0039a80303446424081c0407003500c69108440459410072803603440c00c908241100132103903030416081a9081c0203450b08807030304001c0108000d2001111507004402124041e103801c45000c804103402000c1c40079100c000810f14004e48041c0414018141c1251003034600b440381da1901621450643c0c00b005c0911400529a00e24100c010141980101c01030403101101040d4100c0c11400d0962243c22a4000c0a05004140d9840504400d141d400805040901060700c403c01c402c40c00d588010f50f135000f154800a00407200003a06904102d0180107469040125000074402030340c407200c01469100045500e060030401c0c01c06c0c4580c242d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 543367823 1250 543366573 543366581
    0x80601090213080f0312040c080d0c03030c0201091e1e05030a0f210c0c14060a11071709061207050703030b0f09070f05121006140304081c09050f010e010609 69
    0x750700c4ca8021480c010010401864001008105680d100760720f13035000500e060184501310000081d82e0b0342d65080407503454083d0480781c2010702c1e8400c580c034000e120f6002030441401d607800c84a1040d42c142d84140c50b85440002d4418030b15058400c01400d00c9a271040000010103130549983c2074603403000d1098130020444d5940740400007901c1100350b603800e6200030881940700d5218040c1300d141004c811015620f850313101c030300c0034038100c8015804507007000b42c035280720b1054111100b00d2020140c03410011303896503016518200381004608100040750701c07055a40f6000c68000c007021900800c11031502d400050444d130000324003031380440c0c1004001c880030315100300624055070b030003400444179460391070080381e080c0752108500060240401064480035400d028540c820b0350325135080c1404500385440104203d9941c0c2c010540b1032014400e110008030050144c031900100343e01a000750014895142e80600700303c20014000d40500304035101d143e0019046220750703104c54002400f9607507031100b16008072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 543369073 1250 543367823 543367843
    0x102030a140f0c0d0c2d08280801140f0607111c0b0103021309080a0f05040504090602071b06050d020d06030507080d14090a170708060109021308 64
    0x1034030742060481c04141d044050100340c01d00048840c00c2031200d0500920b044441c021070f0000c10350170069002002000c6075186282201c00084200d580c1c0c100c95004031100ca030240040c4140408104510844000390b90b00c0600380c0350303103030914140c0d07110b01c0040d003460400c0c011070002d200250340e1b4503510300780308490007003002c0003400349443c100c2651640c2c0500680400025802040600840300000302020020710981c060159101c041d45107104001c2c240301280c00c8021130b9070802c00c0c0c2801040300102510118143c50602103186070005104031030368801c03500a1a0700a250000b18030034011203034080c040091240d07030b401c1c0c91a40581a41ca840c40c03050b204500000d88100f0041034580c0540d000b42041d0640550b02180301502d07642d402d420641c043d08400780301d41c083d4600340c071f050307074882601c0080c18000c11840e0301e403101c2140420141200c2c3e01640c00005c5003601d110340c842c0c20800c402c1000740004015038455584800384c84000c0d51002c040c1e41a140c612050201d102c460103c4c41c0350403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 543370323 1250 543369073 543369077
    0x250f080c030114060c0709020d0614090f0f151906031a060f0901030e030711090a15030305031905180106082404020d1a1009090320031e180102030a 65
    0x410600e40800541c0c0d0300031004400c0e51b0060f1a0700052207200c03400501401d200d43d00000c6507050610601495000d0220080303031003024418240103540d6040a100f540148031103c0580d016a43e1400c09041c5582d82040282c002a00c403000d140d098038142e42e003000307481d1569003c0c481020243d840d40510480480ca1a600220400c241c2c1ca2168108004000e034900c10306003c00c81ca0510304d54a8190740001c0410b55030001c00c000210303064980328002d1a804040b42e00d040090300d0107074000c40a01f034601d00000301400000004104100d1061803003400004c1c0c1c4c41414400740c50f048003207088942c00301c44080c1c0150708010000c40c0c1204085009050381c4240d0f43e00c00088054001c80781e0001d84060801d907000350300b108080c80032400511200900d2501e106082d181d07801c0c400c0080301c4010701540994030790351400d0945400607600204020000c0400380921803d206400d205a05504c80c07229042d08000d0202c0070b0517036000c0d6050180001510704071481444000d804016a100d00ca24661100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 543371573 1250 543370323 543370349
    0xe090c09071d060c010c0e1203120403030e030d0605150f1c09050f07061803030203030f04050c180103020916020a030c0807020a0b07060f0b0d020108250f080c0301 72
    0x7429a102e0b0032050440780c00119101800100507020070302c40d41c0041c000d910280d44616000c031a0710b030050f1031040030400c02c3d02c4510781c40030070504654581c081e010062440303a2401010405052082c0c110245503000401a641c0d112000380c000c00090189208550080c0608000b80342daa800385400d0780da40700d59020b5a240307172143c56100c0a003404c8005030441c1f6540e41d241418000304404010050740400c0d10001040d110f800c065000c0c20250310300300131083d020012a42800000d03400f20a9a800060000d01d21a1945035882c0240c1080c05a81c10700da0000e4200c1d14019046100f00308242c1240e000b41d0703000c00b07691104401911419481021240941d1240039900c0c0001c0c4100500030401d4010b003885814149583c1c00075221100a501c107109564010a4420a02040d0700c50702806403c0c502c2d08100c4118000042002d9001c14030002e810f104040c0c0000d090701c030010406840d80c80d1300041c9160b00440c00c89020302196200c08032000050305480004040381d500e502286d05803003000400c59 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 543372823 1250 543371573 543371581
    0x51b0403140f0f060108012a030c090e090d11010219110307170403050d02010c0f110a0c0602030319200304080909040321020f030406050c1b070e090c09 67
    0x101d94404912010301c1c1500c54080b00c0104400280070801c0d0881205000c1c0c074295150500f0307030342901c021f4081105100700020142d00c40d44165003042141c03070101d0401255208802c08143c1d480c1b4800d0b40410000002d01d07003084150341d40860300c250303e4101900da00c0c03400b611a01e2914205c1c05006042912400070407030b8202c0107801280d5800e0f041e6030070022685056100d91b02c0500761540e000480000303d4012900384108001032120795503184180c402000341c640362400007892844030b44d0746842442080c0f4450700030108240600810a42c00c50940e54880e90b643ca8000e649600444001030080005d19180004060b28082c08c01012070760160a50380c142c40da92034440e15480580100c4001c4010011640d072512902c0100784503a00a80741c03180c211810400080d24103140030001e041c103d20400010b0650004ca0080d01d0300319400400000e500e83e1b5507126443c0d24460402c21a488220754050380003a00000500c100583e8a1a06c10701003a8139450b2000d40c2e500e203561945a480440d020001e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 543374073 1250 543372823 543372833
    0x6090310151211040b0d05010c0201051801140105012102070f0611030f15040e0a0b040b0c121305120f18120c010c020118030f0605010f0f15020c060c0d03051b0403 72
    0x1c00c041440c02030002c0003214859a40c01c8c02c44890703d0898016035121800c0041d001400c105c10f1132414140c030004d104a54249d030700426603141c1401082d0601802200202041c6010040b0011032800950119600c1c809414980500004020125156405c2c888900b040038801030030b0306c0c00b548458001030101c0c1c079405101d808015005030080e17006681c954030b41e4110704d400c000f03c28000c1e001e00d41704020341c2818244203e000b00c00a0003000c0406c1d04125400c3c03983e00700c0c1d1141e5800000714202c40b0000420785802c6d030400900310090400e03444003080040f0146c120500502264800c0d6440543d4104210203000232982c0c091104c802c0d54110b01072500495001e02404031106205140c055500740c68410102c00380c0140d500282c400e0701500b0301c0442041501c0c0318040c00f60005032819103c240c80c00030703c030414050307900030102d01c0c9402c500302411a50003040070b1001804020301c0d507a21440c180c52010b80e200d842c2894480003900b4040072840d916070490381808802840617010b49003904540311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 543375323 1250 543374073 543374081
    0x40509010905070e060406121a030a020609040f0e1e0111222105010b0405040c12030203040f1701150b0d110c01020726040608150609031015121104 65
    0x103d0350610400c1c1d03030004120764803c00200068001a21031500f131030100c4180d50103c5500814000109507580307003640300e65400103056800264111903d5560f40461400316000c1c052074401d010b81527040070301d200c3ca10f1801180c0e50290010b906500080345149646c41401e070f880c034034104207000404002c1a616850212441c50081c0394800c540101140e94524603950a18581100c002101c05441c40d103042001c00c0c041e138106542c00b00e40c240141e09007900d0b1403003560303001d10400110071f01100c00c2604241c001d06c195001003000b50901c0e554540d403107825400900c1e82c40b440d0f10b0254a0b200210340021850211a0b05840000002c18140140c0c0d03d1132400074200b1419002c201c440c140310b284018a07090008004061040e524022000b18000c00400c580790104c0361020502414882400f8440e402450554811a2402c00440940414020440a2240048841c0c1500613a00e0407050072032950028882c5c1c84600c070015403129a074400d23980024600e01c0c0000c01c600c20546100c0ca0502d41500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 543376573 1250 543375323 543375331
    0x360504090201030902090408030a15140909240402130c0f031503050601170f0a030815040b0d03091e030503071712011203120b061e09040606090504050a02040509010905 74
    0x100052555405e40000d0741e6113500b203404580e1b2000c0081007166081e00f5010340340350072441004504041e41010b6021800e03400b1118000c0c011056400054282c0360100980c1007240040740102c0d40541e68003804004019045074142d01030075503d48045559045442020046985d070382c1d8a24250714254401c03030140050782008000045881408000310380184103060081940c40c01c0c0365608581c800085062603c4130200186a801601403000403e40000426030700c00f00c5119059054119031000170002c0000340042500300c040603118804142c2c022860800361100c684103401740d03028440d0104052840381c0402856604107000c10000144c52160180240c2c13080340d41c0360706003107000407401c0d0400806d80c0410341c888016030541c0e060681014040d940d611184900b8040c0c15140400700d800d500c6141d501c046800140c003903d6061468100650340c5403c001007043c00040c0da01c080003005030115028141c4520315202c0071888045051080341c003140c0000d811080507030b1900409900820b4020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 543377823 1250 543376573 543376577
    0x1e0c07031106030720011b02010204090605010c0201020d180b07080c010608060c070b04150e07180c0c1e0524130c0605250b04031701051302070201110d360504090201 73
    0x6400207108400791410303108940c0e01f5500040c0c0721440c0c03013203000c196400e65020906208801c4414400350740d0104241c0701c0c425940c28906400b1680456030585041c0c654451440350340042034407070411005070010700d40d40088500034402680c42d00300e426252039099130000c80065040010740005040e200c0c0c0a90f100740070350900448800c000d400e51040c1e8504110540c2c1607000f0320350074002d9051030300d031500c4060181c500c20407c040a104000e0505c13045407074050700d40c80d01c821110502000c1b0248111b40c665014050b100200c41f01d00007022102c84200740c6064800d400030004180c050018080e840264101601741c150a1901d40d0a0b6000e41c0031640501400d81c894520300a501001e50060049610a0810988070710385070074014614400c00900c00301104082004010a41e01e0b001c4250b100000c0701001a515086440107803450342d42880c10349003038010003d03514445c50b0014141003a00f82c0104001580d86ca1040150440e040b498402c00580c1c204103030244260f040070b91003100600d1040c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 543379073 1250 543377823 543377831
    0xf06011203020a020a0f03020907091a0c0c040f0506030106080f190318030819030203070c060b040b041401050f09190507050408010207050d0221030406021e0c0703110603072001 78
    0x1c0d00414020306140c6c00102054a400754100114100100b000b6480241e07840d0070000d0170308120510003c1240506581c42e40384000c100c581460b07006024180d44030300010010400c08d84640408030107071000b02d41c501d11951814000003110b40010898007a01900a40a41006c0c1c0150030b15054401d41a0341c254100300708100800180104480c5960245000c2d0403215120441c00c00d4201c01c81007400985410140180300340a10150071503030000c03026034403100202d028012140820000c200030011180d1050070036503151a4110b0900486040c2ea20503202d0700b0044216805001c415002640d10041000d4850408000c01c4400d50109812042502d81540350a60b903e40c0c4d0f030700303903080070f1801e84050700701c00420031021342c04101c4c1581c00010b081035074010411170060115103010042001d0489900094016a9203032802684110f0b1125415035540300c0d03e100f28203542d101240d00040310649425800740c6011300d4040280d03031160710307030b50b44000f60031140941364000c0f05160741410301ca0b9074803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 543380323 1250 543379073 543379093
    0x201021602120142030b06040911130905190c09020a0c0609030323090a17040312021015050901170c06030901140a06080309060f190302030609090f0601120302 70
    0x1c52080e028540039140c210380003407406804c071002c00c540841e06507070104040c1841000012a155a1030b54460411200055080101e00b09104110015201c4903800780760901c6d805804042588402089401003048400c00d51b000c04100b0341000800e000a0003030501d00303000b003186080729001015040024500028040349950b18402611007400c012070200e070320fa07420b42116410401001501001c44d2118a0060401c8004151513119401c0041e0496240030b110040000300c040444004551111407600c281d028414004c0d11100c04a216201041c107014a03014031420420110080c0c2c1c0008151200c10303440d041d0703c0240b101019440c0c4400e801a5580e4840a544800146202d43d904a00106041031103504c91180d0000c001c0c50100c24605d00441401460000029120b010b5410740700c0e96920000000211414010b2100c0d036615149480c1003980c00d5649900030b180243d07801d4602000c01e40711600b98603251030130a907500e041c0d0b52102004101c045818586a410980a8016940400b103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 543381573 1250 543380323 543380351
    0x61c17120103060b0a06121d0d08071107081b04090f080d06080105090304120302120403050d0306090b37081c05070f0b04170307080603010c02010216021201 69
    0x40e15140c00c151001800401c144501e501861800490445a41d130f045810a20054180500c0c4068000341d20b035034200c2d04443c0950480e0b941184103950040792015403000200400c000d1080702c01c00b00050343c020300807079240c2000401006440d50b00b4058900d00031642c0c004582600c260580039841510f071210200420200d04541006a0252100720750b9100301130350520903115241c0c840102e5031314060410200100100030389083da0305010f00f04450030300c42c0c10102c0c5000d6800c264490540c200003000400c00c08001118880c51800d510140000783d0703201d21480c100e4540001c030b150131000d0441d1095202110001304030741d40a0f109403502264019131040144042a43c105601030341c04200400b140702070040310098000403c0c506645011042c0c5e07190091000c05180080580b4a250702003401c02581d044004001c0490910130b0b40c4034a4191001001d1070b10a03100706001354138080f00202064410f00845001045c03400705514440c050341d081c4440b011021100110956861404150800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 543382823 1250 543381573 543381577
    0xa240909020a02010b0907020a17130506120103020306010605090127080307050f0622030f0c0602030f1008030406090e0a0b030106080d17101e080d020a031403061c17 73
    0x420310f680000f8041c4440018441c1080d405003040c4107541c450705406000030f0b40740400ca00c245402c0b110190b1158100d818059034141c054012a40c0001c003c19140f00200c900071486040780d0003101105c401d0b907a40c00c400d83e41031050a2189001a820100d225800a0a05c111041060364031110518044c0c1d984141c5003141c004040881c0c3e550011642103070701240800c1419040000b1000201308071f02c81d14401c039914402558000c0a11518003404001c0c24001c80d42c181e801d80e08000b0a564a207481c10303014a420340e00711841c141030042c200c0c0214403603000105071000d42d040e903100c541040b8144a000070308000014122284652a11050388451700c0038040c600007007040d007000348810402c0010260115a454205800c00c058000401440c1c026800d01c200c00c45489400f80b651480e144070355640d0b000a06e4102000512030b50088141240c3e0028030704401030700035601d0b04020174110304d00c0f0100b4030094580c0c030b40c001c619007540441c1d425200d010501c094443c5085c4a100080b203043c401c419 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 543384073 1250 543382823 543382837
    0x80604150e0c0a120b010504050114040e1608070f0206180307020d060c02061e010e0402040b031b13050f01051005130b041703031902030a060b030c0307020c0a24090902 74
    0x80041078a60083d80c0000c912226010700701c1040c000112040c3c0020164061482a60b0410000c11a00802c003a008c0c4100c0d40640394540f85485a4580981c03d5680c500e02e4054030b10010f0301ca06d00241004d48200405143c14009a01410a644031220b0030f6051030030b98403d500145c002001107400503030f204100d12030001e10400020504000c249400303810110300420a003102c3c15410000340b290700c80252842d0540d58000014015602c440c00454002c181c8a03034403d4241c8a003060717803545200074204140c1c1e1644229158135071188000c1c4a00161a401d0303900440032380c4010b0040c4060f240c40a25100c3d11402403500604016a510b0303c600d4022560748100709400c000501441405e00f6200401c0301c102242004501d182044401d40305012141e0501c80946a4040701280c81802c031500110000d043c1e40740c480c0e0312401c0080d01001d05a1059030190054401d00c140500a801c01c0200a0100e034000d5801512201d2002c06032134601078001012002c02108103008905012280302811070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 543385323 1250 543384073 543384091
    0x509030c16080105011205120d0b1e0f01030e03160f05150103050c06040e0612010e012309011407030b1c030f090f050a060c0204060b031e07050a080604150e 69
    0x5a10b000021403c50b18103030414242c0304507060810000c5003002032001d20b030862601c011517440b5040c002c10b40c020620840f1440d07101003007100e8240c1d900503803441051943d40844120380919010030040d0304490710728002d2031080c1c009104840b0180c2c0b40400024085e80a08807486140f041540d40e0380c204422601c9a6036a0150380c40180b050007010400c5101a10058540b1890582405555070b401e15008240901c00d00105101e22200c0b0300a40201c60a6a0364100a0010440408078000301c07583c031946403503503281308034005003818005015869248820300c40c0f498003030315080b2044000e40380c402d0310660010388485100c5200351038584000b0901c1d010350f40e00d21024290100060003a61103078060180c40645000c140090b5442170b000400300c5443e428500c20244d5140b010034040e1007a540051001107010040203003003200da4404098265004280c40c0d8142d4400034103035410f0003400c002600041c5004000340e5075040951100101250b23488403814055502d00312941c0003041122a00c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 543386573 1250 543385323 543385363
    0x10807090b01020c06180d052413020d1b08191101090302010206012601050708101d040209090f1e01150e13140708070311041e0509030c 60
    0xc4219801d20406400700c40900c0600006450000000c0c4c071030080200d080c1700203034528500c0318580d9a58140c503043d04c0e440b1042d1040b0600194000d110900003840c20410a00300c0f400203001d240700c0309920341090350300510302c5001e0146511030038241c22004003100380701e001000380418141810440d08208410200c00880000c5580c0f0b041c401a05900809906100c030a130000e00050707030003007841419104040421210701c00401d001c0d003e0706c0209000b410865192030248900140d100c0841807041c0385007891040381a0b44c2d91002102c40d807002c0c01f0640c40a1114001c07c00600d0680b02842d044138042088035460b02200c1d070120304044250b600340313501100c510241c81e030500084c0100140b40003031003100203205203880b0030000c0f10340000789a4a04841c91054000412030301e4003c0079038000611003107c40706603c0b0300c0c0059071a030f01804150340041e50b8400c42d80403860716010b001d0706000040e1800d0003c00d6141c44a5010741800351140245010501c2940c00f075072820044a281c0b6000032031501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 543387823 1250 543386573 543386579
    0x8091c120e180601140d1b080105030303090d0c171309060b18092205070501120501180c030605042a020f030307050a020a1e11120c06030a0603020405010807 69
    0x50040d5010105480c01050207220500b4482c0e00007458941c015820b00380619031203518006400c3da48a011101114030b80390442c00c0199454010340084012000d480714107061342c031402016a139000854940125501005800001c24841c1c01e000403118444e0412407500c0340c461070846500d80020f07a86d4401500080020020111540200d5009040880c04246468910b000f09040030319100340d8a800b84070154049601c8020480f50341d0b0b41c600c500b10030700c841809640b418a4403181c4501ca20783c00500c0034245010301c00c415118540c121825507190b40e410300800701c880b02c090a03240040310103241d0f848000040e252550702400d200d03144c0c91084404412890500100710005240b82c0381c04640c082c07190013030811400002c036a00661f01e41001d94079140501d9089140418509008004000786041100420203c143c10450345100386074480000900d24140891010306140d001882d13171180d50503d205041142c0115080b03400040d010408a4807500450140e40d8282e000c2c48550780020010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 543389073 1250 543387823 543387827
    0x19050307030b040e03041a07080c030301081c1b021206010b0d0614030d1206030c090f1b0801091505060c030406110a0218070302091023120408091c12 66
    0x30b20010004a070108030004403003c10a94030f0045000f0078010701e035050b810103082ca40203003d54002c2c2d6803040380c0d566540700b4042d1041c0c59400a00c41c00226100380d489694241c00c040d80d880c034000780350781d0b10040403004a085201501403e202e0a0740c0001c8013241c00b902285081c00960b0107440000c401c00d07618a00310442e6011108998000f804141d0f100c81d405446030390210311040d0350404c0703207010300f110101001c601000384415800244190007502002610050b10f4002100c000e06080003040207082d11211040c0001e000d0b900e030300016280c80014800f030302c070503402080720603000404001c0745620790300403400c80d6000150301d100540c0086420801c150b8008002c0000e496861f0281c80909a198081907441c150300003403014125810001404042c42941a50401a001416810389540c030405c044e28000b0014108210400000c900180c0d2038180b030f045a15180d454900d1b999180d5070360311850401e400c40c5106039804191030f94451010000484060030441c06042c1402c9540c0b840040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 543390323 1250 543389073 543389081
    0x30606090409051f2003060a0b03090d09170604030f050d2a11030a030b0d0213090606120f0b090703080a020303010609060e0d1104060f03060213090b0d0f03051905030703 75
    0x10588028205008002010120b83c0c00380c0ca091005c2c4002c689944815001030200369090b0001d0345c3e1440d000c420000900c0b0001010511845580c4605144c0d0b0344840c00402d0815a4206142d2258404800b00d00041d2180c0304203221025541340050901c03005034200426105146a03802d070054104070220b40c59a410040c60405004034182102e94002c4c00b1b8403075440c2e024100441090558a8a4441460b203440694000761640100907480042290441100410358280c0903208180342480100b40c600105010803a0380303030056541402e11055640b10850024001d00704001e81c0100e5074000001501c00e40034140d801c0194024645075030410302d0007071080751030307911100410466200324400d98a07012500c03d0070541001e514040303008000c000c280035100799800400c2c4228440f4000041c09810750103800011420b0a5650105564000901c1660450461654000c0c403224007103001440c0f2060502c0c01a200b8100f46080440034100d0003044949140b016000c9100081000440c41e81445 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 543391573 1250 543390323 543390373
    0x20d0204023a0e0a03080402031c030c0914030a1704030b240d0f020d050c06030a09030801050a05090c0a021c08090c0312190912030e1801080d030203060609040905 72
    0x700318043d50f100740300c0d942e10503110f00903052101580c00720b001d40d00c5c203010214030b5142020f0011108964002e00400510b000241e58000844400c0086003a201030041c0c60f02014000b0001d1001e01d0040d110700c5040e07111a5104030349241c00304400800600f01604603803290821040d002240a480710314104003401040e0f005100c2c40c01c1d004007200007485121200021901500c82008468103480d00c00d1400f060704603056440306020007044800b22581c0c1144400382c2c13081e9201045a40c0c0e40d01401505c80040c007420740c0c070900c0d120025a51400c8a8090101c000291040b995140c0c88200d001e0150140119840c0001e1508010031100503420800203a91007800e4004000804103e16213000c2c0b0f0203a103590900100700301204900031441405c07000c001d409038102c07221860300310345400340c807068003010300c0d0303002e2f0810b244201c9940141083c40d50481d1a814043c2616a2290504600950000b0700b072542c00802030242d143d094403180705128140c4d104100901c0d1981c2044182003c4800c040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 543392823 1250 543391573 543391687
    0xc0c070f03121b0c09111216021b030c01140409050712050903120f06040902060c0105040303110c21210a06080a03090e130b04082d0304020d020402 65
    0x1c8010004d90011480b02c100da481c103100250b05803424112000601c207082c1c4003084841d42d5030500202100d240c001074600b8030700e6021941000c040b200c52401e03588584543c075502d0b80100c0304448035075004100798028a00c100c0360071880c0039224480f000c02c4030810740b001400905080060800704040e071040380d801c42c444800a5003401514080d114031500300134004030039a503003100481e07180d032165080341c01c075142c6c01082507031640300001c0040c1c02010116002ea00080c02c01d500000384540083c101c1e0b280d1041d050180440c008000341c800040c0a00260300c154580c000c0203100d0b11085090200c2450760040c5030040580c0c1041c1c00501c0540d07c80e500800e80c641c00c40c003031210004c0c1d00181040100c41109540c0785040d40d0b50780d80b070740030201e580c0c3c406444511400b00700010013000b000204801c1d41010004482c5011050760248402d844000f1204085401c00208015150110f509199035100030809807030010b02ca40c0b00c00c80f1400c8015542081c02e01001040b8076560002c0842030925000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 543394073 1250 543392823 543392867
    0x170f1b0111040305031b0f010e0102190f08010608151002010903080a1e180f03080702071508010b031902130810020702030705010f18030b090f060f0c0c070f0312 71
    0x545030742d5220300c90041040103980c0c1c02101b440c2050424890750001640e0340000300503c00b05488514040d500c91141c440d00541c001c0b062402c02400380c01490103026080c1e84254440e03080840c1912020030140000503030325041c07004c0742e4160313807103000948500e8040d6000dc640074285140140241c04043d045070011410442d007002001010b00c002c40c070805c00f01d040400c0c01c50851740038000ca204008000f500f010343c004010300c103141e0001131460040c281507085030029950754092000800003140300c0000a000c80b401004103036040310295810102c200d441500d829030f0703909043d00300d91003984c0c140103800703404038100b0120b00306100c180ca800c8881003040d450000c240c2d001039110f01c40350180e50b05100700c3c02d000c2c804040c441c000707420010100f00409100c894032404d200c103071180c0031a603048161040c3c0380421440c00c0c1c081001800f4010141044c0c0d130948641a040510fa080302e4800072180c4101d0900050701c0081e107102c04001e43c0034619880c2c407084078020060004a00e4034003400a043c203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 543395323 1250 543394073 543394079
    0x41a0108090c060a031a0d03030603020306011413020307020f070e0702011413081606020310050f0607122307110a060c030e0105090d06020a020705040e1603170f1b011104 75
    0x142c581144c0c1d0740f016501d40014040e424140315413104071020f500702c0c1c02c04030010804082580541c441070039240201c04070303815a81e0b103031001001c8111552103141c0080e5002849104e01d2883d801454000c1c1d2140180c407903508029061074904440e941c003d940da8040c8509008400342c081c425490f040c0c141003842c0da5140303401010b0f081030102011000340394002c001460781403020b22031250b448066103c81c09660340c0c01c0000d52041c0c0843c0c2e0703000d514801e618403070111070a8a800c4048911050780410740c0c1201e501429810f60f602030201c00c401d10703c4585910069440c6034100010207a0f1441080d40500ca000480107020883d0140d80042c0280700c940070702000804d40010540d41c5807942480c5c543e41d110f510b000450000090404010f00c500e0000c04c034000c2041e000b00700242624020743d010010905030918107941c074810f110406001c00603030441400807601b10590038000300d00b240001c41c030b40100c10844010b140d010b030000d1400c0d11007800c002c521b039100a0081c80841a0101d805906080c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 543396573 1250 543395323 543395329
    0x10f1a0109120303060b031f0e1909171308250b18040c0f0e0603160c050f060f150a030809130906020f0a080907060c12030b041a0108090c 61
    0x104030701455405165007032402d8101880780c0c100d10094051180c49036107030b0505c02116800100c50300d04110340c104090b4008603011005680c1c15100f134900c00c00000c0c0b11285100d8950040c0190541519600d25080030500005810390041c002128150744ca60401c61910302c0c5141003141e00f101d910600c5807065107010104541003020820b803200300021720340c0d40d401c20104031310003040704507000c0c0c020b4100000e001d9820b400c0b4945c0c8009034030755201c0c03619070f12015007001360a1200311aa400300010400050050034820055140214454021511145200201e662070014200d445409000d0303903204010050320b000341200c6c5c0c0954151090780b00705003180d980c5070b0180110154980540d440c605007081032041da0f0032080307078550010421943c9840c541c060401c40d0340b2100741c0c8004201a480440c100d0200025030804941141c6c0e60000100307001da68045401c0328004800007055164410313444c09a03114403036071059001000266241c080c0c140e002402201c0010000802c0d50490114500355031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 543397823 1250 543396573 543396587
    0x405130204050f1306080d0914040c0516050a060e1c080c030a0b030a1202030a090b04030c030809060d050a02040e07030e15060a0b0309010501091803020309150c03030405010f1a01 79
    0x30404c840c0b08603500c0010048070000c0805910525a40c41295880c92840d5049408001641d0000c0700c108503803c903003028002a118000c004500248082001002600c005041b0000c01440342d8296002c850103902c03503505032140c0000d071290b141c000740f209540d030303610010382c46000d13030340341e0a0503603113440e00044061541c00010300401d11503482e5810806a540d00317000c4c1000c1d184d0700c64940c1c402d03502c082d04025641e800a025000101e0800d04004c0345400408041d00d080365803103007031030760a181140d0704c1c40142d03049815840e4001c182030082602d004041e02946128030400100141c0300c40c98008280c0240001411400070f1514010078481a0390001c100c01071100c07072002a0300103540742d14020549485040d800034550013008805d1140092042d00110704860114105020079500c103118508012042c14008000d680200280f12403410300d0784640200180c008030550408681400c1c0e40e04650046031700301c0e950b955515140c5c0c0c1c1000c06210341c116504044018060000741140080c00003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 543399073 1250 543397823 543397849
    0xf0115080a0816330b031f0e01020910020c13050f130516030308090d030c0f030c050702130c030e0708030d05040c05100507171215040f050c040513020405 68
    0x14058400000305121210540d01d04840d03090901c00c0b8480b480040211464a0800040c074100317040900c0c4c90100e280002e0f0721511074200340d01030386118a01400d006d00403c003550340304607695024002000f5030f540381c0554070a460b84680150049500391010048030030003459003001240c0c608428080040c00340c41e411540700e1500c0d0100030510034641005442c008414001c03030b446201240c408020107500a06690040c015041121202070304503800354103540c1003c00c807000003001c040d05418102d2003074000d442c00c1a00b9040051a0940d16000301340d061142401080c100b68030340c5403102032907603d031050004081d03c10003e00030082c14000e4040e2280310320410309490f10707112030200e414018000c0d4550001c05000381f0540c000440088050b0294014440581389040c90140c1d40b80780ca501801202ca000807500c8111841c0c3e40e82039050261031000c007400c06d400c15034850802a08111601c9040d00031111607007456160b5142904002d01e0240700411012581d00502c8108420f4071020820780794 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 543400323 1250 543399073 543399097
    0x3090305090108090c0a080c130e06160e0a14030c03070f1203050f0412050f0a0203070b0d09060617161206090f06050f180a03020a03110309030f0115080a08 69
    0x4152504c850b0b481c030b000c40c01560f041d400400c80310700040c8003000140c2c180011a00783c9800f440d014811418004a07600030040c200907820800004800c00c41540d00d450f0b07904c0407802c01607480d0000c140480d030448110341018001d50490817416605180400209240c81002c4004002c840e040612044420515109d6520404121600001094001c1c000d40d0788000103082c41da615540c2d110741100e0541d407032880c2507589001740c1e5406100502d010400c581e60701c0d000307002002e01c0781c909161000e1980c0810802c1079215a075490030000a03010b4000c10005105042035030590b02c5c4001d204509200807441840099201c1c01c00c100300f50740820140c801c400390081d10002e44403c0f10304005941c250b0144e402001d0510742020800d0740d0940340303420b42c0280c6104244400140f180740c3c000380e0f210b081e040042c01691010950b800003074801d40500350410b20b514241d90510164034003007841c241010165140a0b511030700207140d120203244c0c41c00c00800c007407030040c01040318a4540702c00c14464140c004078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 543401573 1250 543400323 543400337
    0x70f03020901120e0709060e010e0615091f110d090e090f0a2009010b0d09020f0a030503041a120114010219030503090609060c0901081503060906090706030903050901 73
    0xa4140e018003e001c0904100c0042030190a402c40340ca01c2d100c2030300340540c3e0f4410b0325040e03020a0303a18204039800c1c10ba94101c800780d6407544407901000b2060800e21160306001108120215840e102c201d0ba0b1174401300340d20110144017600c0840980380300c44030288000c1d00c0c0e100480c00312140394403031968412214920454a002d49403d40740904108a0584400322442034440b4001041600c807407507100e00c454006e65407095181c3e1000c10910741d03c04e12503513071108803c1c4050191003034a54800c21360035100074005501603140001140f98240030368010ba41c80d41000c0703820005184820310042183c3c51003a000d5191000380f0f00500c0044506004003440406045010b803080c0e40200505000c01a0304010b562902d03200e0f18004040d0751044854080d40d000301da001c2448030100242c1d25029402054446045c035815800444001100500000140200340030900c400e8405100c1180107425100180c500d61605103441c518009141d80130380109442c01a19501003503000c01038419184007403070306003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 543402823 1250 543401573 543401587
    0x50105120d2319140a1706041410050405060621070c0615090b0103050603031e0403080c0a03020706080702030304060905160f08010f05060d02210a0c05090f070f0302 73
    0x11045861094454085410000d901e1200f03801100c50382d000c0540540d100b00303c085501c00c00b100d541c002c1d80481da020407884034903420788030210f5a150354040005400050301c0c25250800907681b00041e5420409a1750b074040900c21803c140c080c4a621134015189249000078103ca4201b111740395484030110781922070f0201c1d010600c43c00744060950b8000c0c40a2220b100c100c0c5074040403054501c80c4e561114941004c290095010340901440307000001e000c2c5040403c815017000c4800d0360440840c0b00782030100f1001c000502c1103c06007000300c1000004010401c081d141c003918001140e00300b00309101049003049902a40001129401588010003140000e0b03141b9103030380340810311603a000f90400c060b000421038407001450642240c1603900280b00307245c0200300745030403180700f42d41603600800030742d130450050b04000005401490390344806da58048400e131170702410006500e4080380c1c41c28802e4410400c500c2c0c5071703001030307013101070780100142506003110b01a10705004a11804241600440d1003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 543404073 1250 543402823 543402857
    0x10060308180a0b040924060806090123010f030b030a080918041106090f09070c030801061b121403070309120908030306010305040c0f0303020f011505031510031a0604050105120d 78
    0x50300310746d1a8440c01ca00541c0e103030306c2d0103420284100c0340030b40290038a000020b21500300a50343c03440c0551110401d4544204400115010350050000c00e05054132150a103000362800c11100415030701621040e82c0b9a045002041003041070403000c00e0300072800c2c03020300c0081482d03228401304000f0300b01c82c03003030b0341c1c1511002182c20150343c0c0d031185500c412054200250180c01030080541c1a2080d44c4020690fa02c0c1c000070740707e2001016180004800403041040020f05000044480055600380344460004034500c06495900444e40000000d44a403421800c00c0101d071a09205c2580b00c3c00e141e910541042001592804001c0c0f44504058980000c034041c00041204c16014007007041c881b006884d141e0802170354840d90800780c11155841d0501040f0f60080b141c0d01081130301c100801401800c0102c8040140200c00501340d243c0080010303100000244c24203c1040c0401010642440107181650400c001c03250140e00442c0900d41205800031140d1010403140c1d9404240c1c01d00900d042d1914042c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 543405323 1250 543404073 543404111
    0x40506040b070611041d06030708070e040215030115090902070218190f140f0403080103080c1606030902030c013204090203040503130602030a09090e10060308180a0b0409 75
    0x4481380010001401140c046ca20011490132610303001510402c42c0c41d0502071642d82d1180d8450031495410090040c00322803020201950050f0005001041111703c2d08045481030f4804c0c2c0c0076440717006002c2c1c49050850340149400c4020410b0400842c103089403074001c18003030544850540b0000100d140020200002c02107081c000030008641040201d004400c040c000b01003440e2032080a03200540025420006d21070943d21540d8941e03075601859286907075001440c1c00c0080840d1250050000031940400c3d804110030081030780d50750101d1030f46240d005042c01e06a940341c001d4108034842d265074240600f914412198040d1034616101d012003202c54907a103901450f0030030f04080e40000140030a120001001d4040b20101440200c5910755800080c2e1343d07840f40742c00c09000701e44100010060701025600910202400c00161a200000c2c0e9038a030b400c440a98100315403c0a020803d005002c080220f29524844266515400f0a04000c1c0c42c00050281381300310301c5142d40f1039000d10512070780e20340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 543406573 1250 543405323 543405341
    0x30507060e0c0f040902130c111c030c02060603280f06150501080103150216081303140309031902180a0501150c030507380a0c0203040506040b0706 65
    0x4007000503668040815860700103112040748038140b4005030302402d2400b84103120116a0090908012044041018000e0a4031240810a0041240f1030041801041c448103070707006e014048000e000c1019007006001c40d00341c01c8070001154001801c100c41a100001e1960503003e6000d907580c40c80c449400a5074056540400044c007200c01e103030041c01081656000f24580c003001801c00b05900b5120380c011142003100340700140078404404280003030004280d0003041c03000c1c0d020a0b40062968151501e5190f81c0c01303c200206c43c070744d1120081062050b503848071035445141c3d8001d5480d00403164006aa690740d0300490030503144000300e070503003155508500c002e04c040c29034458034107a03d1300c1c0030106c3c0180001d110b074000c59440c030103402041a1241000280c5150316881c0d503818000e0b140c6444404d81d030407450040901c04c01420040c1d1100500c030b000070030324120301b5505e0301070b241001d00041070b0b42408400209550081c4014496582c0b40001d850075070b6810380210352140b90508048010380800a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 543407823 1250 543406573 543406583
    0x9060819020408070e04021206060907030e0c0a03051507140a1110091a07020c0d1e051b011107080a15061a3007030905161e090218010507030507 64
    0x4540005c084194901091196008450949825204000140e102c070012141030703038001c03210000039406034000c0d0300003584007000c00116032041041101092841c04c1c40d41054605510004051419808900c034107680102c8034901001c805818210211182c042c1d0b505c5c4c00b0904c00041c050a81a04041065241021240310244084080c9080840c9001041c04a040b04002c0041c0003401039400092209100c10303000d031018002e40300030f448861400c0c9900c00006080c010b502081c2c1c0c0490410801e40c04c0d08681d580561942c082c4607000034000d02c0c00e00b840c250700358210703002c200000300003c08c4652005400202d00315074801c100c0c0940006101680045911131074402ea6082c9811982001e0400007010303030f0500c082d10302901c0a8580d20701c0c4c000030300c00101400500061040384207800c08564640700b181200c1500c0100d9021164881c01500644500b207c0d1403080031500784154200c1c001089c128804625005c60407031241d04500b40b03240303d11b050044c001811002c0510031070885040340c2d001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 543409073 1250 543407823 543407833
    0x50702010e0306130302100b130c11070f1d010503191a0c0304060609021c0c09090608030d140c0702010e01121401080c040e03091504030c03030206070f09060819020408 74
    0x41002d407901c940c0500426001032185012505c80e03035015201d0b1408c3c92500800c65580300d0611410040603011410440c002c105400c00c0e9410b290f00d0030401c00d0042c00f59882001107803420304422130a12080400200d440400d880010046510041034102c164000248412441501400c0c46a06607108400813082000e5040801202c4008040035501072445100c0901030540d03102c1041007607006001c8071300c0301c9102c201c5803002000b40c0d07680643c0701d40a5500b000c404256951b1402003c60f6403540c424805504000350b10304100c5503920481d81e01c1d50784482600c4650034003459450490084141c02410f00c5035400ca03100b05603026969041000c960b1180900415207510b0a1400340b413006e1242a20500c2941480842031519006062150600d00011030038449030808001400c007a00c00d01c0d0f12241b50400c00840440e109010842c040c0d4000e800419843c01e00e584028002e4040c038200c10100301491005000080e0300540c144c1c1c001d4107040c000d40c5210101c0c00c141000f40b285e40d014445d41e1240b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 543410323 1250 543409073 543409081
    0xd0e0a0902130e13020112060305030910141c050708190908040510020f010e070b120a0f1103102c090f06070f0909060e01170a050307110909010e0d050702010e0306 72
    0x2620107007020085c801e0780c46600340801080341205844a40c00001c040c0e0304188100060750500300c94017002e1402034507028040d00000d5101e2107450340175203040405080c81075411246d802050142d0b0740c200b042460010341920301060000181c9110ba160300c10300303640f00c0945d82c05006180c010b5401810340144851102c00703489001175075903012248062030550074a0141c46610801140c1502220080320919181c11507070122100d80900044c51003140c80d035107034241c00b94070000b4410100b0051044d160b4980c1ca04180e00801c0b9102c0c081d80c4244031a0318004a04141d5015200c5010624198011440c0551b100c406201f0705002004030003506510640c010082415846120a00d580381c0b41c4d00c07603220b501d0312001c020381aa00317180107a502032842c002c0104040040842112980200c0c90207450501c400341d9107190440cad100c210140d03903040e442400704c0310380c0c50901442038019010a0080014150100c07116849025a50160090107004030710081035900610740f180c1d00c010003c007600c03158a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 543411573 1250 543410323 543410341
    0x12190513051509040c1707030b01020f030c0a03080108010902060405011b021905130e06040209040c0801020d020901030f290a051804171303022202030a0e0d0e0a0902130e 75
    0x1280f8014442d07401d00385100b02c060300945218178049000d140203035266454041c29006000c80340381040c11882454800c0c0b0340208280094603060745408090004802d403410001c21284042c0c000200c0c1c0e0349800054070040c2e8480049404649081c00c2c4030079090b46a5a001000404540d0060341100394015a40c0180c00301100e800103617001294070100b0f40d0524080d26080b030f80c4034030040e1444d41c450780104e0003502e401c4214a0381309209070103038a40715403071301d50712400c0e03030050301c000c01080b41c001c100c1c00d020390303050300a034103a004541c4400c21a03640342034003001d0440300341020f840000b0b8514090030900d8590800f01c1002d00300181c2100d42e5250445c0800c042c40344215003e8031b5850500241c1c08420f801141111751000b1892074210032541941c0030050103103016240340451083c034004811000d06903001561207044080000140d04002100040c100224414688100400044a50010340d603c1d801142652120000141c0369459000070b01030380d081c55000044d40103200f00801003640c2d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 543412823 1250 543411573 543411577
    0x3140c0d0201330b0d02280801051c032d0c0203070b030f040611090904060b010905150414120a050a060b060403080d090f0b100602121905130515 64
    0xe0001020032600200b07a01014000b83c0f0b000c0e0a029481c0038a841c1000101d508101a260043e0110001407428482c4150000041606510007400032650012001100c0c0c002d4200340c0180f6054484e0904402522580003030569003841c02828040c801d030000308800001d081c002d40d0090283c2003101c910f0024100a00750071b0072020200e200740b20b0070001181c140c0c54002580d008280d80c01e8841c0b06030300c3d1a503588001c0d02c2005c4034800c400e0350500050b0841c2d43c400c56101e001d6405501c0014004103000001000c1c034046400407030080828101c0d4808140e400070403607003105d50314003c3c581207042010004100310442400b5003d9071003050341c68010f02a001c201c110b2030320b21070344041240352001e4041c882c2074055803001600d4141c0501041c0680c42840c0c1110102a2064084009500e0380342d840c080b1282c016907405000c0c860079501407104da5010403180d024445026030050510021003aa9105032400b140d000c8100403010803003450510140c40c00ca009043d0040c00303000204401501403c1d03a0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 543414073 1250 543412823 543412841
    0x3100503060a2f0a0c0314190e09150409050c06070804061b0210050703030e0114090c01110604141f0b0109050d05070306020322060b0306071b03140c0d0201 69
    0x101c4409001d40846200002d984412049405095030808004e40415114101200d0059051000f15594810150600802444d81c58032025484c03c00000e40071004041e00d01d40319003a4003589090087c0540f40340520150358102da07048401003000c5801d0318000c3d041c071079240862a003107a00032a40c0c104104c0000b0242c02904c01a0f85d510040c41e02d500c24424400494500294218a05020340d00a19205030001c003031ba40e0081c140428a40d1211114908598100028001e603040030018403002103401c0c858806940824a4800301482016811030307103a80001e080200b00c08680c507001500000305015008a500800b01c03003030314400c6521580c0d00030305516144140001d9118801003150300e0100300083c411500800101001d03401c5660742d04c0254409048106035405860200003040700d41c48284c03807250f01c1001e0114950070b1702e10605103444400303090322043c07082410300082803000b070503140e80721150940b070841d9801103500050f2000b0301c80c0301c24200a40c0a160183c0d5006901500600b00c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 543415323 1250 543414073 543414101
    0x5010906090b0606040608010e0a02190206040c17030306120f070e0405070906140405040302030904020a050405091012110402040510081b0a021f0612030c060f0506060f03100503060a 80
    0x100c0c0c0d1510301300203003407041e409007401240d4180700500c050101c10180c59402500386a0040c07501c441e03101800072101140c2c0c001c4006071300c2081004100840052020010100181c50b001c004a080300840c1e07ca00000703201c14050301d18101e07d00c405600410052114101c2a01038855891b242d030200491f8800442c2c0a0320284141c40e000224003125110780002c460150400090000da004100400341c40003130030503004c41c8814850015540d82d91300c010203031942152181607643d0300c0d2400344040403100420200c910741400104001c00c941e104034103015244c0c42902001c8100c02c2c10b0004000340a6900704640160500e84021011500840e40078000d1a004240303d1003640c01c03603440d0443d1b1040599820050f0403880f0a103110368105000c5038114101030f600800c04544803805448480f24030907054000522114211051142c07174820140341c03072041d01060105184c1180407038014418000e0600314500c0000010f8110a001c0c86a100540802810740d240c40c2841c801e40741c0036151020301400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 543416573 1250 543415323 543415343
    0x5041202010515012705130f0617070e19051303030b1e010e0604171c0801060c0b04020d050a110f040902100c140a06021e0a0c021203070501090609 65
    0x740d0f644014840010160141d48070081c11a00131440000c4061440ca0040c10450103039010680360380310b501d921030040000c3c0000981100d506184801e40b82c1d9a07000321850751a015101c0070102d0049820300946810542005540d00c034070080310036407420b004561380c5251516003408150042c1e0b41000050314020381d0b081c8140520301003089008020310f0391814400c80d0101600703140d54010f1124040c802c1c1c1c0140401d08056548030b00103030f4a03080146001300c0d900600b4000071240c2d41048100b040e248140303412403070366042c404040e2001c0100a07010304880c2107140002c00715500c80225400f484d5000b03058800c48403603032502c014005403d80107540708038003500c00341c0e03054203041c86a15046038005002c0e2881c825902d5040d503018a96030025100c40b0f8034101e131820144002c0041c501100e224440042e81c0d0f003000e801c030303c101d4440c8180da004c80a004002103604694841c00c42111550101d621291441078120407601d50700c15030200511a500b007210340814001a503000039501c03801290980 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 543417823 1250 543416573 543416581
    0x714030c0403110316090516030b0306240910030519171b0a1b1a071401020912030a170f07030c0207090f060314030901021b0a03170a02070b090607060e0c04050412020105 75
    0x42c0a82b40381e001100c0d0558800d40002c0d18444003181010540880054401b410015500100310807840446811a510564030010410801d08000d00340c0b080700002d669000d0300c0515692070b27101e490600c040385100c01003c01c02c0390600702c82c48000e04030803e20408407400c200c05441c11000010060380c2c4030350540304040c4000340f12a5810302c641c042103072184550f440c0940079a1140103800b01071128003402d65083c4030041d4940c4940d4032a40071140c002008585410051f80010b006603000b1707505c1000c500b0b51100b88000040c0b841c01040d00003250b424007040e10012100b00300d00c1c0c02881e9201106d5281030000d201c014000650000b0b0a0b280981c002e0401846140500c80e41c2c0d100b030030b03c83c900684c0071030741011505140c1c80c100c4c5d41d14040200340000c01d075502c1c0c81e818521030007450314403800c00c00080d00c0101a5010020400100b544602c1107041c141c0b1680054070a01aa603406404a519a11660500324080c0f00101d40c0d484003c108111a091600f0042d003800c0084103920050f41c07030719000c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 543419073 1250 543417823 543417827
    0x305041e1a091c03180c0612150e040305070f0c060507150212041403070b0114090601110304060f0306090e07030510020f04030f110d0501050714030c0403110316090516 74
    0x300422014011a802c41d03200c141004400a0003a0170700d20000140302c40011000446c0300313071020020300c1c550382c50b0301c400c0b40050b4079203007120005160013a041000da4010840c1003c001450750b48542c2500342551503007814106903040000d666401031007490841e2001c00c40540110143c880c050040b00f07907445115407400840d04a1150032f203448110020040003a0010f051070544501910102007581c1c00c1042696441c41040c8003a0411443c0b00303004058400542001483c3c241d000700700f46441601456a0a5140c0d100d20031406150100413852010004613406500441b00030003240f1800c010307100070310311015240c000341d0000310703100e000d004c009000113050b500a079003a1002e48200c0918151440d5103d940e03220441d00304a4802d09070340daa0b440765646003000c0c0c00303959001d000041218038000200078070019040702d00001810060084c40005401242500c0980340d01289580440c0155400a0b20f0807002001040c130420501c48089041d40058000358000d00480241e070029043c48031341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 543420323 1250 543419073 543419083
    0x120f0c0210020c03031503030403080315130221090102070209130210020610120204060302090a090b07030221042102100c050c0d210603060203060f040203160305041e1a09 75
    0x4441840d5000b03202046c03410303400941e9403803844801022640740503502c0c0d40e445a503420881d51400c1ca85041004030302c40d810290701c4581003501c0203030114503240082d10340c90300500a0581c045040000c0c0800500f10078800d604a8014a400600128070b625005104c5040a42600d04c00c84c081c0d81c0e54002c406c01f0303038000280b0501400309590869036050a0003c82900044901010382c1e00c01d4407403600001584800c00094010f42e11400c0109413104181440520744001814501c10180304204011408000802102e20114581d81040311a01c0d00c0c03e00c80c0401c21224010803859442c0590b410345a80c00051400792261011418016002101000d56003801421414011031304650400903d6074494040d85404504065030884070f03542301902e00040b02d029800803280c060340082400014a400c0301c29003c0b10300304945c103510798a00303d80d113090301c01050600c0703500b4961035a01083c1000710000940b00c6075402c000040641c1185410503000d00a180442c1002094605000c5101d140000c58 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 543421573 1250 543420323 543420337
    0xc130b0109060e0a0306020406020f07060509180a020712050a02190b1f090c05090a0b0403020d0818150a030b09010305030a0f050f0a03092a05010e01120f0c021002 72
    0x10303803007081032400505403040e241d0030350780960205203c440400080c0440c80600003800041d07005140501c1507030b048510f89079180e0810024440180302c0d80020f6075071044400080d070003038a0850007548504c014600a0700030f20f14005e290040d50384114150035802009030030765006a6003102c03c0000d600f88411100d0b1f400e008003900440038903001801c0d130302e540049001d140b00c0c0500c100034419501c050f10000c0b03e10650351040014070010b00901c29182c40d41c1800042e1000420030340c03a0501d180c1c00541e1003440b5410050000702c0200b040341d002e95400080040e600800745c83c10103c5000c5001c0001113500420062012910f40b945110f82400c0221036581a6503101009524003022a102543c2c546540390800081143c200102c04c40c003915a400740048211f0750b00d0101300f1900c6032a00e64504013003c090310107090340480081851028420604040359002c2c20302088180782003004031200c170f0000c54000100c500f801c2c3d50300050b448580c0000200d072115800c1d41d01c49161612000c3c10703441114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 543422823 1250 543421573 543421577
    0xf060c150c02010207022403070509060702101101110309031902030c01090605041208040f06020c01060b1b06180a02060d020706020304050703050f16031403130602030c100e06070815030f0c130b01 86
    0x2300002d515540aa0018810180700400342360802c1d0542d400038034405030020a060000720080d440c20700b031142c01d024100d08188030070303852820340c41c11015041d52070040c1c211010040c00712161131880d4034028070803201e00d404010700038001c0e21400e040000180c501541d0440e4a17807459007480700124032910149000f558000f0603148031794110f8807410003a4001021180c125580d404001603c2440e820089c81c1c20110341d0b10f0076042200c8401d0813401d0a40003040c40c2d12030110b2042c113182000c00490030704850b42d81102c0140e1a0548268550700074012140000c041c80d00c0001400305000000030384c2402c8034803c004441c0900f40c5041a01e03210100c14000964003020300c0004e20001d4a80e00d019884c024403001100e060681c901c0400542807080e6019101681000070205800c1c40103000e0440c4c103140001d82480000106001c0580c4e441c00284840b0420042a0200c2c441213118549050035180c001c0480e030702c3c800210725160b20b6000c1e0a042510403207101c14000c0700c00d2103030300036100c4101050b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 543424073 1250 543422823 543422827
    0x10050d03051b1f0518060f13080d0507030207110f1c021f18060c030903030f210c03060905090a020d050325050f070f060c150c020102070224 62
    0x8401d0703100c1d09815844510b42e280550b1184a100f0300c1c40880c850507034502c204003ca610309214a0b40f14012014078207100e880c0e0010010042031554400c100c030b400c441000e0300c3c001121140d0521181c2c5016a141462110742840c0902105a41c140c02405030b4500403070300b07c035101c030f80c030000c2040103521002c0b05600f16141c840c240317413044681101c0924250010300b480301c0704150030218660403400e04070010007055101c1142c90010003c454580d02a09090929015082c404c0c0c40140c809201c5100c02400c000d4282503901100d03114581c0b8003024118941c00c02c0000140f50f1185000d0180403d000380001d03e0b00344000b42c1c03207100e0300030140203c044c100905000b5066409010001c80d0701079042d10f0034401003000c07018201d02c601c1e440b075040b000000402c90007000d600d001d07400d0200c0d00380048140d0f031101e078090040c040078910000c110303580e906010a1a000b80d2501041b6458815200814a442c0c9020303000d8054041d0000c03c1d03141c0c8229020740c03240d6000c0144828003040c2c5000035080c1541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 543425323 1250 543424073 543424087
    0x10c1d0402090d050a0602031602030c060402060304020d23101e02160c1806080a020306161407050309100f0503070e01050d0f0605120c150a090e0c0310050d0305 71
    0x4654010070b01808042c2c22084100c4958840920f443d1060004640e002d80c000200100c4840801020104d00c40c98400f80d454a04102e81d82551038101402c00703841428000045021940c920b01d104c00741c02d070f1000c035280e10040400d480f1149801c9102c0310010601600340800e034142c42901c07a18213007085e22104402c40010080c0103a00075040012000102e03203400700d120020902d0995000001d0108007041e5200383c504c418141c003900e0f5664008a0160701c24151440183c3d00841c6095100449441402c958001003808850705492600141001080050b940d8103202c1c001c0020a1140c80a80300c0c00500000c00504840e510002c50040000401c1800030400841c411004001c07400d0051400c01d0600342d080e07444c002100c050790405049a40e44500801c01d50400030001c0074103c081e203020380031601c040701c0403500c8620301c030240b000d2440b40042c03802e0740301d4050b00c0c4e21000f0781300e06095007035541740c6810303014003907402903135209200c0e0fa4071100082c1604d070146800c00b00030790564400b410040c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 543426573 1250 543425323 543425329
    0x803090625050d1829160f051005010303120e120a020a05011532270705091c050a08160507080d0f03020d06090c0207060e090105060f250308010305010c1d 68
    0x2514117001d240c0040000700c130718048001c2c00783c901c14021907205030710a1840c502a850000c0d001004503019040c1001080401d402c80d1894080d006d041102160881000754000e0602c00d414142c01418180820800416680081d0031900b10780b00e20020032000705550240e0000d15443d01c9a90210b50040c00a004029255803803030800c240b2a21074038841e0300220b000220341454240c0300c0b2842c400c1020080800c3c02510b484c0c1a04101c0a0070224600300c1e018003c0380380704070207601c00c000d03030b4032141440003c00908028108241d900207c80343d8855000342106810f082174402e095074144268103005c00d800720041a80100c410494581e611001d41d90742083c0d01940202003101151030b598840081c1d40c100380d020310408504564090000b507400c0400240040b98040b0070b0a004648441c010b01c801d03165881111424002000100c0d2502d500c0b06c1c41d08001051418120141c81030b4420303003004c03d900300589606aa200f00001d1050f052605000c4070045010555840d15002942840086003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 543427823 1250 543426573 543426629
    0xe0a05220b034e0a0f0c03120b060f0d02040303020601090509030301210c03080406111507200a03020c01030c020604021f09031b031b0803090625050d18 67
    0x1c0004101c1900780c1050302c440c0080012140302100da20740c03000030111084c0354004039490601d803442c00d060701001c0c0710b81c8000f4048032030750601000791a521442d40416903103440a50300003076601951680c0d030782d5001c40b500010b900107100440142c80303100300200e4805000e000e107620a8846100071400c5a1804201d404d0719020700c0c0c4401c1d80307042c10a0000300810f80410802c0050b501690310f20b9502c51030000e004001c3d00c1154518400c3e50482000403940d00d28907444150048114a02401d4244004240745c009441443c04e1045e0b51082945134010540c02103842510680e00743c07410059000e100c10300780d1320f48208030b90081d0310224424510038000c04400031480b002c00b0302e103031035190140c80343e0744c84548c21907044c41805c120318281020400c000c0359a003013a104082d440740740f40b8507900d01485180d807805154042031059a011684000f0203803858041040d07041200041c03003100d813503810055140c0c10880d00540006101004800c10506141074040488100c0f0045004c0f00c400180e0f80d030b0f640 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 543429073 1250 543427823 543427903
    0x109050a0e1612330f14010e0a30082a011805100e12091311030a2d0f150e0f090d0e010e0a05220b03 45
    0x400003010f51210100c0c4a4420780a0030142079201c070030309034090300e44590484016855070304803061070036045c000302c48003030304210071a0070841000c46c481890b500161b41e04100c200505402c83c140307142c00689104103c0045140c800c0740880d0b000c1c1d5a0340301807c0d5050400b00d00340038120b00d8003000428040803542d00744450743c0c880101506100d25003500600d00795094025542524181c0e0001c41040c00420301c24110140381c600010003020000c0c80070962245810003a01c18030300350105200c0b41d103031100080070803070b00308280040145260400c91071402e81c109642c0d65101602c1c1401c100280e0070980c141c1c42c490b00d0072060328106c1088070780592001e0100100340f11103158481440600e01d50680b0351000103841c400d0030444076442c1c825405880100700509801036540982d40f50903045820543e488000b410a01e400d00d041540c0502090300c02e001030340001c0e00446107180c2d0240c48502c0040c00a41c080488206000d20314440c004c0654594842c035001ea440141980c1444041d1a180c50900789 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 543430323 1250 543429073 543429077
    0x406051801210e01050c03040203070608070c0b1608060d03080a0207060605030f01020715060f0b16050d030f0f0605150c1c02030a030518060a1d01020403050c0109050a0e16 76
    0x600d6406102d0300c0b40180b141d46a020303040792166100d400c0c031070003802055072080081c0d21260840c43c00e034001a60b1045988234040030300402c10042400310744038021083c00950060310b158254104802114090003822a008000070004004102c140c500440b880b038166806607903103600b51b00c40e06200c1d00250302040781120300300d603109000a200e8405101045d0707002d640d03000060316840d242c140740044000c10284a50440d20b0120240403041c00c1003040400d840da01030480e51940c0c0b440c0d1540701e0300300c20803801809500c180720f006640700e40c0c0343d0000c0c2c8094410f0740d4140413410702c0f001b41c034041e01e03420f00030b01d9404080c1c0614101100e6403040981000e09201c803c5841018004544c0c0940c04400c0103c10b005800000b582c00c00c140e014080c0d55044050061001403c0c2c500c0e00005855103400307800b1f8084030381c80c0c1d15103084141c8503a16114600000c0c20003103549980d03d1400d15034400b014200302d400310700e02c10b0000070340c0e02d01041c07414100c0d035082e43c0c6582d055a40301c0500c100b05200c0d0004c1d1003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 543431573 1250 543430323 543430337
    0x303070510110d1a041d070909030c05060f01150203210403050405091f0506120f15041109120c15090402070f061d120a0806030f0d050711060406051801 67
    0x140b480c403138040e4250810815219020001c484024001514000c10302480455401517141d5202d00000a070031089a94801c40040c035001103103811229000b0201003d41544903000c103000b0003000c04075125040b40ca6880850b0800c80300e40310244d8403405030000b50718984603800740803036010070000a5a54018402d2800e149070944440c0010300384001595942c07041b4100c1c1e43d99005801d2551000c1000e031100721041d50078030703850101c041225080108200c00724001c0402041c04010100426007a517500104244081d0908206190340b603000302d442913106641d14500003102d141c000ca58011900d00151620407140d008140c3d0591a40c030285e03410f07411a0342082040007141d000c05084600c02c0c0300c1c081c08911f5107190308042015000c1c2e0000c80e045500070302e21141030202000c080f104030000c03900301080c2d40e44d07603000040d00b480e03030561420f44540508122848a103900070000c2007201e2056400c1096003180c117052210714001e50080402140d4100700d003d42d02000b4188080e801e041c140b6090ba = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 543432823 1250 543431573 543431587
    0x30b030a08030115080907120201120e030417100209030a030c0f0503030a050a0c0216140f0603011203020709061d0a0e071e0e100b031e09070f05030307051011 70
    0x1016442607012800039410085040310b041e80c0012451b400c00b49000003010902e0801c4c1c058203500500100c028144004040d14070301c8000341c0d40150304a41011015030b074485071307a818205030400c140b000521321802141d0a5501c4030342c00b8425035480d404064020a0035400c195010b4410540100c01640d0141031503486000140302000103611800580c01c011986c1e0400c81c15210540e05014414402d54002c4100c41c07a58545544d406401c41d000361500e628000b2680f030123b0a0b6208030344d00076402c6030340000040340c01c4a51500444100d0301c02e508603429582e4580790401294600d00460380d400c081000d040b40c902d403061182e582c200c1c003445c20001d034502840c00c0d0325103407411030760150405500d00c50f040340c00940118101d4002f04000c048038500d519000040c1a2a50910302a0003542c04020000c0b81c01031450310b0890b03015611a2440b0b11950030070306a0345a60790b0f01445004241e8640d8040841e40741004000c1e81e82c42503216008181c007a0b1021003000241890240c0006000401d009d81 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 543434073 1250 543432823 543432833
    0x180b1207270c09060801230427060b010e0a06170406140f0f0a06060504050402070f1e170c0604060902030c100356061801080114010f030b030a 63
    0x2d000c0016054441c080c1c01864841c001d8030458059202c03d95140c401c15410404003028612805284c400700c4000804403010f00c0781b98001c0c040541d4080c407000b0b0b890301c0c160403c500e85d4003400c081042621080f508440c00d00400a0003201d50148100140280c0840100c000a1552840d0807912171200814040720f01988400851301c2180c41000f80344018050011202c0388101c1c40307821480244017071003142d05104000d0305134843ca00c2801c0c000c030780c00182d01c82030042e03890f88243d0b00d6911101e90001e01c410306030001d1055451807016580010031202141a280990040b49c40252400000d00000c1d038541d10b600303004100842081e601800b0380d03d031805e4141e581c0250320b51014038944002411031460180000d0849090744400e810849101d00c003252858101d8510524417117100030302d150140b804807a0000460f4110f4010781010340856030303480130050000c00c0010002d081e0303112001c581e40d401050b15080243d0f1a001d01140c044200005200c0c40b036000007500c800040d04540081d149541c1d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 543435323 1250 543434073 543434081
    0xc0f0309100c082502100f020a0b1003080412170909011403070e0703020c0f07050303030f04030905040c0e010e0109030809151204061d060108150a090c180b120727 72
    0x40c6140c8140d125813118118500b5140d181e40940f140d10388031040364401d000c0079560710b90f50075000d0544140140010f5074116191441009141d004039071540340e5565103c0c40204c2c1c2002282220441c000c40d82145500500806407100544000e00c680c406910b0b003070102151041b1607030706070b80500441c000440c50301580c4034005d00502c05a60016074603903440301d40b503090480904034100c1707540107600e081049a030000180c036000328030500c4911081d00c3d2441e06a5017803400380e20990700710307051607004c14060b6003007980d40000c04000e0326440d074107105840044903440b505010003003001e0f4081c0f049014a0a2904c0c1e483d1740c1d10504115580b40c843c0039280803090329000c450072940e060f120f49120070207011458620401e885a14000d114550500d18184e8135a03614142403454058a600060030002190700200b54598001c0140d1b000c007034450560002ea460407100140282e42082941c40040c02d0049400e10072200420281480c0c5041102180d000d60001650056101c1e0419601c81c40000502c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 543436573 1250 543435323 543435367
    0x1202070803011202190803030114040b091f0f0f061e020a080904140f01211203090c05130e0106061409060903010b09010e0405100b012709020a03020c0f0309100c08 72
    0x110307142e600d0440107a42b1144d0b000602402a410b024104090703031180d200e410380025031691150040c8078105115407410503543d00c187d0600242c4032000400440050210b01607a02603982c1354420304a0042c840d08601c15880c02500592003250b410740860320510151800c40401171011480031000111200e49100543e00c01d885803c031500100081500340c5000001c4c808001701007107012146860b00303202000311070b401c1824541c440319104200310943c888170000c0c0100503c90350f49091007001c0d000040c410300010724265803a244010401d24007960400120b032490705119480d14019005014040c0c008046007a0199255000c10100d81c1e00c8800e03160190245015090301c529113428034918001d4281d1000d03d81900d0000a01034a036840b00e025114a4040306583e081681f91700640004180c00341e111500c1c4902c045203103042d0750b0b81a001400100562012648240c5503022071640f28450700710035030f90005032051445003240c09600b000405901a890f00c508043d00043c0d940c2d40f00e4900f40d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 543437823 1250 543436573 543436589
    0x5040b180301060603150306020d060506070812100b070201050c0709091a011e0509090a140c0f06191209020a0b0304290705090f041b120207080301120219 68
    0x80000301040c1000d100f404010f007102e2800b80405600c10541d000c041c0b880d4040504942d4000a03041201e4041d60032000003001c0c0a041c4580c1c0e24400e042600c41034100b000d006010050402c0880c030f00c00c103480a10000d42d01545903051400800761300544080e0300c00003e5608074060804002181400d81c4117111155001d064240e8001c4400e0201025501c01600404003000e9084a01c0142046044590702034800c01d4030364403800d4450180042c0f501322145801805400f008101203172030030b800700310742d082e0400c150380c0509030402550811a0314001e480c01182d40b6100d441c101c0e602544644162010110126000a6000c176542c01041e00f0003c290002d6203c00c20020901c1708001c0d00002c0e014948010300501071950303c04511144c10341c440a0710601c20040d0215441a51b5a62106c9404005a00074020019056482c01040c401d951550040c00402d250018000d541070450080f0b0304d11580c4180c500d80f45071b0904003c82506003148800341c7c0c10040c4d0f07088226084814030030f1030001d05102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 543439073 1250 543437823 543437857
    0x11e1a040f061106070c1103060c18090402100f200303010e07020a26043219052205040b011802040506030f04020f0d15050f0112030e0105040b 63
    0x100c8000044aa40d102c042007000740d03400032015000c0800c1c00c0350480b499103040b054144183c00c02045406d281c445072641400b0760b80a10a80316070342c000401641b11b608120400b81006e1804001e07100b80215000303500001020001c0e1202c51140e50b0010000c145400c2070b02d11070802881e401180300e010000120140c4c000001030001c01d1041c10000e502c00020b00c01403514a0301c1d0380e20764045074a030141c81814200207070b80d11000c103046001550058400d90441011031048404041c05602c999160138000b903684c002600b01ea07090003001943e440c004511450305151500d01440b94080b50301e5803030f1844d04540750460010101c1801905d000702d0007841340b824154101040c0c00c0705040e001d4880c0840c00d1042004000a0b1200401d5030ba101046003415101c6542758000710f4820361002c00e00c207510890b0040194104030260b0503ca00301c0351001000c00096031946800040c400c020300900756102142000d050001e40304500e500002031044c5061801c00381d41e0f01d03900e819900001a204020061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 543440323 1250 543439073 543439079
    0xc021203061206012706080a030c0804090207050a140106050109141f02060402011e090b0d020c0f24190504060902040501091409011b230a0e040b030105060108011e1a04 74
    0x5e840454414002800200021803802154540d5506400c0e8014103004200d68064140200b040071f6074001e265148095603584850b1408035100c42e15000200c4007100300c00700300041840305110386010340340306846000c11030b401c1c04440000101e0303424440b60b2224503451207a000900900001072130160980041206041510025220307100c210101000d22070501c0390403651651091b1400300b1600350740d103a01d94550500b401d401c0030707124100920303040380308000f90104086000101e20361140e0320b8000d1082210314500c00c10394003070000e0f0388809030071640c4003400115041c02c2e40a1754006108040c0043c455080f5808203064607026400790b500d0070350300c0d00028421001042e010781c0c000182c074020801d9044c01c5690b2060340c0f100845107010484014816480511340401811590200794000ca45401121038003d05003011010320502507410042070502e14101401128050031058480085680c01c1100300c102d010842482e070300044212603000110a007d004034400541041c0c0607095407141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 543441573 1250 543440323 543440369
    0x1209061d010506010809030d0905011d061e150f010302070f120318020d0308040201020f0102041e061110020f12041109090304061e031b210c02120306120601 69
    0x41c2c010401410700003a24204012188088100d915a03105408005040740321760800c030b40105125020321030014141001203503e1000022704034443d42804204bd011000e98611002c80010207031415100c90702e40025483c0c031071402060203c0c410038107140050030308040b07031207441841d03100000a446460041900c0c1d03100c5985030095940003003068480d00107180c2654046001010006800381c2000251000318007161710070f00400764103410080003503442d20b0b00d40802c03070654403550003080301c1d041c03450100281d000d0041d0030400c26061b01002410f08120280021000b0703502211341e406002c4020006030748542e49040f41680a83c0c0550407014444d005807042c041300d000090f03e42c11140c1c2c41803008000055004083e44c44021134545491100481c0c080e041e0702600c44078941c240b0038114030044d0300c00d060b401228421b10628456400c41502d0456541c1c4045941040e101750050300306043d20f06415a10000071a00b08270041c00c07620082d80403014041c00c190303080c0c10052100c80340c806035035007241c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 543442823 1250 543441573 543441581
    0x9020103180819170405010b010f0908031207030f02070309030209010504020f1804110309010b0108160e1207030204020a181a030406050414010e0a0204060914010302011209061d01 79
    0x1d0301012807030100099455022060081d103180c000c51040c0c840403601c0440c814140400c42d00000700440d00c541c00c0c145806400703045810440d900040c1400b0700c80032858440c03280501240c4e04100510710b80100c02004d48941e80000301440207040d1555504840a503180c4003d122480c000d41e075410307100e0306502c100110300741c040c0c0c0124840c030300506ca800e2070b1034418000c46200c12071080415902c405400c0105000d1b04200c0040c0c0c00154003c0108003400e80c1c190003a0741c44c0d842c26a102d048944d2410340c054503800c3c22402c10340010f40c2c1c6a89a071340f241044000003221700449411142c146e0f94a500040a991003410b40d040080c010003110b5403c2d0480381200009007003184481c0303c00c0b03903440345c0c44841800010310103001203071541d0205051007142c1c4c1440b10101c1d40c64000b400089800082c0c143d443c82441da040340120f103007284c0011994514802c0c04100040c4900d00c013031907441c640044852a0f810750400d0070056031502a0300015903e4890036980100e030489031000c0c802005001400c403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 543444073 1250 543442823 543442841
    0xc010c080903361309030210090309120219060504080708010b01020606040203061906110d0801150f0210150f0506070302070314030403020603010b09030d1106010e071103030a09020103 81
    0x40c1c2c810701c0000c0038912071500307a403607880658041a008400840c080382401c460506001c0d0009020a20391130b0000098008203c1c6500903002c4502c00b80022440d04210f4000c600302400140c0c05a10074071203003050001c025103a40c0014408039045000c8210390318042d13075641c4030f000803540025080010351010300200d0002d00c40600200890720300400045d49682000300854800c80d40080060640e41c3d4010740c481c50300c403452000700c1109031281000780030380081c507500700014403030f440000341c61900c00d0207030f98180c44125100c502040d202e101c05445541e14034600009500460740104818a40d51242c4201c001202000d40c840341e00d4031148014010340c9801240c001d01040001c2804280c000811000301ea5000002000300e03d4020303103d40c03c50099410080d0701000010000030301012000c080c0405132003c034103640000c002c8034020380700030300c0f0b44092000341c0e00490010000e80890f150b202d6413001d1181040c00d00443c120400d5821030740304941e500219991502c084080d56030510600240b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 543445323 1250 543444073 543444091
    0x307020f01051e13081e06060406051507080705030a091401081608070203091005071727040b04060e0f071b060f1b09080f0a02062505030c010c08 64
    0x70348084030140400b20007070071010f8240058001004945545540d12101c014040070741034921421100c4140c0701482001035000015104800109031549010320401d400c032000100b42c140441c43d204107054542e00010703000e40c0c60348002d008a2010400500041480203000e0740c48141442c24294020521203010303078280d041004903c100410701d003100c002d16104c00380c0ca0400075081d503500503040703140d80310701c00307a15030890520070303a46000c5a04000034150ba18400d907250300f048810100940254044d0f640d83c0c076011000c0320b00b100002d1383d10806003946d107640648045501060303240890b05407002076102408a8001030100582e0a003c441c1c02d60308244d00b464001031f1003080440c0070907000c009104c084c02c49a17444000d1001c0702480e600014074000324051221032035003140c0019000d6629072003611241e01404041041e541c0d4042100000b030740d80204100c0c244224400f0142c1d40607206d0810492210b40d854a0801241003040540b020321440d000100d40b44201c203c000f451841d0280c041c0c20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 543446573 1250 543445323 543445327
    0x6031a0a18020f0307030231090c0302190e010e010501020f0601050a0605221e06050f0a03020711030f010209040e0609060703020703090b030c0a260114010306090e0307020f0105 78
    0x18441d42960400c0c20059011100d101ca004100310009080a02e2603100075440880d5284040c1240b43c0300743c0046462001e14045003440c7c4c20324030640251030b4009401800561011410301c01441c0c841060900380c3d458020004156885980c14542004280c0200c0700c04034145004001940c2c0c1000506010002a000303808a5450040841c003448541d01a20091020205a2101c81000340d814100215811031070003c4103507545180b403080c050902044211402c22003008903629000380100c562403202c1c0c0300c2051500c084003030220000d401c000c6c800c40d0202c04504420070a603908000900c140d2820100060752074240703008000c01c540d501c10512429402c0321080191340400400c045511040c60704025035160180c1c40c0c100e950350419000110818008020311540f0b2020304003401c00c41c8603980740d41700700c0151104424401e500c4000288020b9082100521188000c00c0c81d40324035403018180441c4103521180b2010913583e00002c529425400811001c06500d800c0c2804881d640c404c2c00d1440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 543447823 1250 543446573 543446591
    0x7050d06030521120601081b070b010524090103050c04080a0c0e130507090f15030f030906110a03030c05040f09021c140a0c0c121d0108070c1502070606031a0a 70
    0x512414005c1a2a0501c02d900c0000343d1400d0308030b6601c001c4d01c07400e1050150780740b034a49003800030701c40c0038041d05000c0c0c2510644180b82003002d15010401c011406c030031604251040e40114040d01d00100409480241480b00103051181048480152840385e40e255056070304148003d00f86410041400c0045030061540001042c0c021a100e01640ca00800110350302181007005805001d99004000031558030f0840001400409411144181d00c25621901d50641d904070484240305d0240503848950000074620000074003035404130507492040d0800c3c0341130643d90b41c00e00444a240b0b81c0901051a0001501c1241d10500d0380740010b64004031004018081ea0b00110940d2018001c05900546a03289440600356015a90300c0440640c801d0280748000407100d0000e05141c108401a16890700f0039a07040c0c03103503000c0e5254a00c41c49581e0740c0c4e041c40b800f141d15507c50300d60905440d41c2c00c06900300003940c0800e80500402c40a540106007403200c401c2c4201820701c0b11030b002441d141c0e1052400d000c02e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 543449073 1250 543447823 543447847
    0xa0c0e010909090602251209030b15180109061a1e0f250501140603190809030106150219030917010b120f01060501020c0307090507050d06030521 64
    0x700050312101c2c58001100001498098000c1c86050300b00004812008a51440503401c0320b2040e20703031440b4079508109032000c407909554942803404004d01c101002030018850390620301102601d080c0080a2107507503891603085454414080e0008421a501e62078240000c0d40310100203e44040740c10740c011314161008407403102c8406000320303114003020300081d01011070202c1e41c299200034601100881c6903481019212042460003e8111400d50801c9404501030352889806803140d44064050321180100b4103500703c00d0440100100c1e41c100701400284c0007070700e09210b040f0203465901004520441071013800391501246904000d20b00805510b031100096108a0240c111000c0340604580f403104082c4181c05080c00d51803103500130116640b07030f40d020100001c1010303421040800070850291501c1c012601d80101c502590b07010341c402c150410803034141e0350081c1d81c0300c005407811500300300b150b56000b829101c6aa0040d6020fa011004a50401511040020140d0f14801407a40f61500c0b010751 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 543450323 1250 543449073 543449087
    0xf01080408040608090f0f012003131b1d09060f090703110a03020409060603110a05010e060c19030c030f0e0f010807020115120b0601050f25060f050a0c0e01 69
    0x340000300b0050340701140180780708100c030046403da11401e5640c440749200b8414001c0032704c501c04890001d4503080101000e0403c0c011070380203031254104031921365039984880100320030040464080c050a50030020342806041c80e103400c45540b141e40301f0114100700000a1404002034202e9110084070000e018081c2c400182010032254410044a190a081e200040c928074142e07001940150510303899204200e166446241500c0c490a0b846440d042c2680501c42c0e0303200359010b01e60110320030711101c100b0b07480d00c14050315034010071008a4000f00c282184038803039140d040300d045000c15000c152502c201038001c2208003402c0b00c24500146410005000540d039801c6100c00141802001004515203600c01c0d04520924404412522101a654492100e1104c044038082e0b403510700070804107084d503101d48121b851403171a00110342e040071010002000415500c1542e0b803601070351640715000007500c40c00f81c00540c5401a4000681e850020421030a07610789401c000c0810403480c3d54403481d40c0c2c025403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 543451573 1250 543450323 543450329
    0x2120f070215010612150603020a090b0306010c0201030e0a050d050a09120b04141c020d080c03040c03150f0f020c061315150b0f091008040803040209041a090c0f0108040804 76
    0x41d12198400c040305185e40104031030792015203900b001c420b01040e07540e0076800030907401100395075000c500f41da94903900c610350005403440c0307000a0264840901544c882d030442c1140c0300d54078054034590b558a03a2128a40000210080041400441c0c0704540c00e401c50b54000040c003001c400012810300d69a0b03172128501d070041008000460f144012a001441081404500d87d02d4a00c244031b13892050402942d200c10302108940098100000280c90848480582e40a264402280b90700c10382141c0e2001c400c13540c4501c214050780d075a20b01e42902c04019000ba65840e00212000598604151202c43d04000d4020083c140392400c403262180010081407403003050703401742c00313000a43c2c04d40c44890455a41c12940080d00c01400820a0040e06500c00f0050051420032600503454062014041d50a49401c5a011308a550107200060150400d00380540e4010711410b1000d01c2d4505000c205c05541c80240c0e18408036501144a80d00107041208020b60301900034286903480346000c0d07643e40402d2180340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 543452823 1250 543451573 543451577
    0x2030301120f05060118060b0c0705040c17150f0904240b060c0f0105160903030810030206070506070305010902270a05030604150605040219031e02120f0702150106 72
    0x20041e0414440803400b058481507001003580d5031540e584103104904001c8050168001b4030304800002d402c6003800846001d1203080003d0000a4034010420000300700c034446020070b000e02e03c81c5100d9108007605066110fa0201c0d41c0400906480500388062581c00f00388d81e500582c4580c3c20b1001080c1e2000030389500d00c144180b00100001144046000341002d5203015402c00c1d00400d4103444198041404501c000884008015a43c2c440c00d0480c04c00400b45100c03004280300c50390500c0801d10841060343d00c03203552100604415500c2e404100141c0c8411307000d8032160050300c14003489035410301480d80100301c03041041d030a2641c6503116a00e18042e0207110318003100c25040707540054840c1000c140c01408020195030a500c0c0606010040140c00340c04c441340c0c149020404941da16241c8291010421000030040c425149610305030001d10b101280000c1c03000c6120b07459080d8103c2d41c001011583d07200c4030365501074104880040d205544c0941040c0c255040307240102800545002c946046606d64 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 543454073 1250 543452823 543452849
    0x10f0813061d0f06070806010519032009151317010f05040807170406080c030a0603080f0702011b02032e06140f040501032109090204090c1e02030301 66
    0x140382900040500800807001c802d641c4000d401c0721040880c040341e6002d5079070169143c80c0c0d01c0748802c42d04050100e850b01e0200b04c00344030500012914040e944011440b03810001410b400c1101c600080c80c580e55441a02c113600000c0c00020741c201000e040c480b03c2c44030001c903407c1c00c8245c5003104480106000d031515101d0050501307400054250070040e50074070f030342908118500b024280390155a11015056482c181c0c1c04160145400ca00d02c1100c0403100307070350399031200c41e210178041b0089940082c00043d000c0703480d09000300215006400924105a074103104d59903841c5c3c18400074211020400d20740c800706c481d05810300b002d038034007254110f00442044030349171030744050380301c800c605041c90f80d17192250b1480d200b4007003810b000d40d61624180c10030480c1c01380700c1041584104000d990f003d000041500d142c513218480030144907400c2d058071118078180003410a8841b1140000c0740c0144c2e000001c1c4686400078120341130742060803000903a43d00f50385981c6c0c00015440280d07803032006110748519100e42e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 543455323 1250 543454073 543454111
    0x1509060f0c0602130902041e030f1217270c060706091b0f0306060e07020a03030507230d05130f08070c09090308090f030a091e081515010f08 62
    0x1043d4111610600c8036004900c0359911404401c0081d003250040415035100c2d88441035070b8801d40c48180044a502400b904d889902d640d0b01e0900040c055010502802200034041c500b00030700e60081d80c071811005401c082c1d4520604040003004169400503800c680200100c0030294036984112913030542c0140c004a2680321500d1700510004e0101c03c1d24824000309000414444044c240301011640644000c1c89020344802103aa4060402e8a1220150b4400d0440c540001e001e50409940b1203494240045d0142c80001400e1441a0312540c54890100020f00100084601e2044c07581001c42c1507046209541944c0d1103100702092000007070124200490608100290034141802400d018132040c81a00020301d4042c0c0002003d4940040c07078001c040140702c5070440081a01d0003880340340e80d4401030340d20304110301644c08075410010050001801011400c544108214000d00f000c034610507649241c920180039220012854043c10030030b08110b0651069030102d082034008512142d141c05140b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 543456573 1250 543455323 543455333
    0x40e0d231605160305071401030b06030417040801020c03070501060f0609030303110409090605090c01180b09120d2001060e070e01110d090f0803031605031503070b041509060f0c 78
    0xc0c801c0700000c0c01070143e0401000f044000f2030130760300b01c0740480e206001c0f4030080c400540c01e0b52000039034107800007004c2c40028041402c0c2d00c04c00d01106c2c11464001e10740b5488100310b509a031f0215000415036800002d08504105003441840c0c010541400214200d5083c0080106011000d110140030552a40c1d107074680102c008044500400300003208002d0001145841000780034103c0d56000d03070740181420300707049500551840111601c80d41c00c50001e5401c2c00d0407a8010b4020b1145250403404181e81030f129000c04002c00724904250780c0303903090907007400b644004501d07140d0644000701d40d041040403c10720389080001c0e50051280d00303010003c0c1c5407070750040f00c0030022440c0c40e084a00c030f00702d00b41c40760350341266580040c1c61030758465540c1c090b2204c0809980e84000e03200d00244680d001440e1401510134005141c0203202c080e080520416401d0002e032510005070400c044000c0c0010302000f400080f0610b01010241c24180a52800d19102000d48407d61081d040c1091200d41100e00007040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 543457823 1250 543456573 543456583
    0x30d020c011224150807120f060512010b0306150307050d0206070c14040c09081203101d0703051f03080a050705060c042610090809040e0d231605 64
    0x7944000f10500300c060000120354002c1e0700d80b15482c038440c41d14201c4d441d21882403503403600c42c1d125600e80002c00c101020001004200000e0303e0100c40d0ba80d254082083e959103010f64261440300e07030020960145c2c01007010304104010700749103101e482c000c020311415240820680c0460b5011102d030005040d0a00224850f0701c2442c4000f0503c0050300008500c8068200115110031000e640812500e44000f0081d00c020b03c0364042c1501940c89607246840c2d1002c0c4000a59000b46201d680c00c860302d507034011500d818800b2101d0200c0b200d1a803800c01440720341c1846103d5000c45103038550010020210700c2840a00e02501019003408800140102010300590445031070329070241c211950352030070303a005140c40e4101d800390080082880d1085c2c4180355050700707825684a00d05001e071106502e840d684800403c00001c0441d5406070611040030591b032148143e0301f280c0c04c0312000c1c0250b000d1908000b0880700c480610246140202c824080045031107005552822011903982c0c0b004c00881c1c1000d915103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 543459073 1250 543457823 543457841
    0x150f04030e0d06050103050c0109030203030f03060402041e06021501050d030c03050912010b031603033011070c1502030909250f03051012030e0411030106050c0c030d020c0112 77
    0x402104520901002902da2013241268025025501816010801100d41c0350369444065030583c000e20410203400010030045400010040006203899a0759200b14501d5803072001030110303414890010040d0700d07014407038911215241881c0c0140c0750704042c001886030300e40350005820071032204003c1d010540103c080700d96601c4014900640c504101c0b41e018040c00c5030343c260b54003a025965403070144101183c00d460560380d01d91604640c0d041c4018540c8500d9644030b03550307c5000300207040c02e1032034051482600c60b0300100700305403541d82034207090420000c850795101c3d15015101d416812026a0b000c415111802411030310384c0395540f240b28a540030101c4890103140c3c11814400401c40d400d8010b0002c104040e82c0ba1800c0c0000d039030325038284c40d0307818881c03241640c08280e121001380083d11820303d4480e07040e8000c2c000034a0321007400084103940c10903008200803880c001a8400400410844070381c11f00c0048005180840c0031000003500c0d090310791300c8181030190309400c590341801d941d0443c001c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 543460323 1250 543459073 543459079
    0x90f0f020316030e010902010e120a0803040c230105030c0a031d061902091804080c0f0c0f0d0f03050306060c0f0c01080a14010e07110307050c090603150f04030e 71
    0x100d0920b500408504442108480e01180c90030201007107401040c003401c004140c050311103480d103081d0310080c071031300c1c1950b040c0c4107034203001d00040c1c0000950080007031030055006550242c2c200e8100402401d08000900350240c505440e02400340c05a0b900200f100d0b0f10003a50f50840380c42d4076188900346c000d480001500c0040046025514090540005400c0e2045035000e05071800314400410b000102d1040e0014160000007a80021083d611a0f01c002d5800900c241421450107111071105030400016401140858201c5882c00d081c2d8501840b000020110840e80c0c9015400e56645a01c044e80d28290000c09021021001450f280d13190400c1d249501340100950f0251000010703440e0702d0f9160451441d01044941010444140b002e218190076010240303521200c1d64201541c54070035040042410041040307000011219a6052004e4601d07503104000420040c2658820802c001a0040501c2c0c080e600582038003c444441c2c3c411143c0180c2c2c042d18158194450b41002c59644041d91111a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 543461573 1250 543460323 543460327
    0x3060a0605180414041106040b040608060d12021b100203042d060509090a02090108040f020406081e07080102090d0f0f0f0305031504020a0c110420030106030606031104090f0f02 78
    0xea400e80074030619201d14840d42001c1b20704044032041001a018030b00a01004480c14081444224000c409103500144010a41c65400040e5070306c0036000c4c02080c0704640160418144948004039142560b80161000c8884805c404030b0540020b55a0007140706601c2c4c00307402c0e1800e02200030300d40c51200f54807028100760300260649441000c0c00c20307408000341038041c0340c5681c0090351041c45403086c0c03810142c050f9a0341d40c603a05e45443d020350001d042003003a43e001d139a079440025020410440c914628400c00c990306840c0c0e00e404606400c0114a50110b580c60340104944485541c4100c11100e9042e400301100b40110010300f031146806421034001051201150103000515422130084c6229a600c0c0354400ca80303003001e07800d0005901413140d101011404202c41c00c40010805039001002000180c00022040c0b01c00b51541803803041d211040304403140c0000107021380c55046c02250094100b509062107221104007078581d00303104a118022100303607103008140c50b040e500c1d00055120341427000d00355 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 543462823 1250 543461573 543461591
    0xc031908121008060105030111030601080601140310031703041106130f0f150e102102070b06130b010f1d0307080106082a12070306050c0d0b0603060a06051804 70
    0x102c0036100d2801890001d00c6070000000d1540303814013505400c0d0414208040c00c40c6ca510005403450803002d00520305018046500c15507920a503405140304012078000064002d103181071000d8030003103860252181075801c00400010a2081101124494007a5003490f03079480540c0091800c0402900310041c0c1d01851440020701c0d404d60200070080d00c001041c035968000c0100b00a4030112020043c3c190440300c0e420900756030302d0090030b1034102c0040007000c852030004c1785100035049034082001216200810818402d0604024000201c2914001c0302044011100e01c0040c0541c01d9101c1307076108011800f040c4078494850f81c07a80b1050018090200c812003900c1e10311080c0a02840d00400b10b4038440c11010a4519002c0300004008140303510200c1202d50380d060a02c1150024158100401d2040700b40c004001a40351191512503510941c041d03440b0f0f1100b6400310309a4500d900ca032445940b0074018400340d640c0c0ca200e007004540c6903017800c07a80c2c0d40000042c03007802d1001e081c5155000f4070380380320303c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 543464073 1250 543462823 543462841
    0x8030103051c05071101180906080a0c05090705030c0d0b030610170304060903140a0503030c07150c0e0d060b0d030203030406140c07170403020603090a020307080c03190812 76
    0x251080401d0b80d5a030850b501c5011908850300e0203401c02c0034084080c4440b1510055015030110b03620840d913003c03003a114545480e1580c00b903031640e61002c14164403140c0389070306220200788450080d100481d803103891800d011b90001e000c1d000103850303404840c1c4001202c0c1d101c251385500400c503864019090f035156280140030542017044a01c41c02d802c034100541c3c4e01e00c0390360001c8102c0b410ba80441d00d0b0074a1442c1961542e840f1030f0021120515244507602381c21003c41e0080000d184a1410030719000c0c2e94110364a002c052071890040c48814103414205520119a0400314617502c1220564890f121042c070741c2070000141000c1540317550440c035800ea0304001d2683c08030003980700301c0c01803506000600810319041c08441080740d0b40110740c8400d00c1510001030342203c2c1201e0085440b92402e003055240d0b000030392030b54400d9410156071b900501d0304c502141012721585004040b60700143c40c4216604020130740f1841c440034940081c03083c00c2001020450508192035280d81341041ca190302d85060040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 543465323 1250 543464073 543464083
    0xb0a180e090f0601210203030d290a06080406050a060b2a0c0114030403020c0405131a010b04090b010504080105040303020406110d050a050d0e0d030c0f0801300803010305 75
    0xc036901500942c9074155081100040290403030f41103200b000e428800e130071890310654108400890380750008021030a002c464038010701803410410300300401d540d078903500340c6902402d4002000f400741e4000c0a0401006030000e421a40c00360f0400f9004c03035030f0b80c3c461040c0002440c03035810541c003160001c603450080c0320b00d42d00d001c40002030140d507a82e0300001d0411559914600451a940001c200014540d0b01d4440c01d000341d03801500c0381c0110359519164030001800d4420880b10f179014002d20594060034020301c466544031131042c9000c3c6040340e50400089812900c203074000d44840320b0b02c0e146a00003e03441842110000e114100c020081d80c1081d240080c007961082c800d080c00180d4450070404400c5012810b40c0038402c030758540d00d01c1c0c41d814100c1074416410080341c03030800c0b5035035000d68500300006000450700500b0a5a000420b00301143d8060b100c401609010020411144010300168010104031700491941c610b11059012020175021400154070303c009118510120000081200c0050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 543466573 1250 543465323 543465331
    0x807290706050a0b150c19051e0c040c0e0a0306020a0e0a090f150b07110f0607030201140c18041107020a1e05100e0d0507170627070b0a180e 62
    0x220300030910524420141c0c00d0051969006c1160032000d8841d4801814400c01503070325104006070707090b850903034034200001540c814807100140c0144c0342110b035a24192242c0b400c141414104181c84400180128100b00040d00000701801d81c002545407600c0c1c0944568810100000c0607074030141e0702c2b4082240034000900c200d0030420309088090035203410f10707410315080c1c0f02d502c02d94030b0500866849007401c07034104600720754210708080301038000c54550038010848203020b80c0001ca103480c11681401e425110007002516821018010515401042c520701c0b11208000c80b804160703c0021010101c01f44141c042c001d5020303441210010300f00c0180d04403040040404501c07003202a5440080c04003d4891030f04100000360f9104030020f10b4500b83d400d081d8614080c00444583c981c41d100760300c40818a103190f110107036005600300500404071146058648681052802024014041550741d07001c09004940b600440419683c4000d48100244803a84540691400c4815a103440542000805035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 543467823 1250 543466573 543466579
    0xf0f0c0a05060708160f0206070303240b0406030518060702150108010203010b07060515121516020a17130e01262119080609010807290706050a0b 64
    0x14000103010725007070b003c3e5881e0a030080e918600c2d101c903094060b60f100322584800c4900410311503040c0d0150b1506006404200e00ca920005607030000d907000550190380c0100310618101844a091191204600a40f0200c4a20b401d001c1a5a01c2c0c4c030b8003100e21098a070b6050f000a121704000c00c91f82a81c0010704058120601c1400700a90f6200d000300303820307448240515403110404118080020751564001988403c40d100c440c1691020308001400e50f04103d1203001641e8001d0703c1540322052011445030700031140c071440701c1514100500c041d441d00c90540c4040c040c20307040242e07041030b40728500458807000c26080b100c000040e11070350070400c81102805401d182244814810344c0403200c682c4807207211542c400081c180304440c0c00c441c01d10f20140801030b4494a8051224044814a002411154a006031980141c615008003403000c00d10341640a01c440303502c840c0f000c100364010300c0e0100820f038109031180e40c9a000c0218020f00d4a00c00c400d0002d01043c60101080b0007111258040e9500b900b0031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 543469073 1250 543467823 543467839
    0x6031205120f090c06090f09010b0315030309030d0309050a0f03050403031b0c1a0d05040501020307171303030504020a051314070309050613020a050a03060c020d0903051b030f0f0c 79
    0x5151480520314003100d9809040c4c0c4005a6081e00703103000005000003950082c01c000e46582c0d1640490a010303002c1e400710340c41560200900a18850340d10410741a01c00a4004500304101040006c0d980c20200f541c075030501d66240d0380882401004e101031035080d50403e031606045581854010b00c158081e100641c000703002100c0060146003d04004204650450050008242003015003010460b9044081d44620401c20002021134110f014691107503025000058892519140203000034500700a1f6200c01095401080600940710a040d86800e42600e0009069a11803020640d09007041c1c01c450303807021148481035088141070300b2000c1e02c501d01488020340d40d298000c05906980306580d00a10a8224100042084a9007100203500070300040c403103612507640f9030200d07103400044d4200381c500540b03502c0007180c4030350104800840e0320003528121000340d2560300c81c940c8549a210504104001c91204401d1540d010001d5040d100c0001c42903031a1030504041040d956400404240d00070b142c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 543470323 1250 543469073 543469081
    0xf0c0b0a0c1e080706150816030506060303130e04020121090606060806010903032102040f140f18062b0b010510090b160c03030f030f06031709040603120512 69
    0x15428400c02c0d4164004212404c00400756540c401034400005040701c055140200050043e00420003815a9030112061b16000e0741141400c5050110040621b8003030340c01081001c1d0a20b00071020758044443c461a4040300e92241d00c0120340102d03580c1c442420700c45058004002454080e84071288086c414103040019598520040d50754880440f0700c940031948401d010008280503903414620380d400c90b440c2c07003040281142c0b00c0040760000c0e0000641c4103080300c014480c0802e680c41c1e0b141e0741041180c0e8101054082d0b0000b680c03121500d20140240003a030400314105841c2e4541c00310a0404120b01450010110103000d524810f0081e81a18046281c4000160b0303070600b40002080b484039640d445515a050803035410140c0d0042d28115005000c40d841e04020a1241d03110b003019610a6881141005160760000c0540d580d00d404400050300e4550304000141940030b07020a02901e4142e60360b112000f0780300080081000f07900280801922000c2034196603072000041042c2c8895044c211102d0319 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 543471573 1250 543470323 543470363
    0x304271103061c0c03050109030207081b2b2103050f161e090e061f031d06011418090a030c02061c05040507060c0506040f0c0b0a0c 58
    0x140400c1984004810404120300c3d007424a11807140140804203040703201c07501c0c1c2e1121100d0140f03500c1912180d644003101401c05d0b41c1401800020301c503600040074072004218016006618801c84070348140445a010700c0b1904a820000c0c03100186a42d41000014031424009005107019460b02002042605890300540c0640702d804d003e2030000d0f50403801d40c1c0e01d01e0000380c4107c450f502e442060010019055003070303407460000c450034081a65a40520503140c440301ca240d00384c024014031300c41e440021031040030400e01c02e5020b070710004500c3c010440c25145e120f20b8804040a08441116001d00b00c004203e804019036061152202a200f1000d00c2d45c5510004c05031070401c3d80c882525800106000c80424410848a66510300003032080d40b81ca444000d001c10a02c1c80c1c0a181007525444000700000e204080c00384070010007040c01c04941e8656207549040d101c0400603c001d01c0f8490856603503090020185651019000710410b165684496060290600320115412202c2c800e00c0003403264201 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 543472823 1250 543471573 543471581
    0x1031b0c0b04170d0b0a05060301082d12030105030c01051201090209041d01141b0a12060b03040507030c05040908090d051501180510060801031e05030427 68
    0x1151640c5540c5442610303030703900300706100140041e111801a200c05044081c4810010130303140702d0100740003e00b1450442400004003507688800e11600081c001002681c002013070000f64582c40480f8103041c04010501d9000181d003040e1000014880e24100310001c40781007000394180d0394110100e50800d0248401114580310380080c1030344204a500040029405a8014180c8242c000344042511481d00c0c1040030819075100213000d440c0e46400c4400d480b02109510a9000480c7c586d8a803244640c0c00c86c41c0281340300b03803204e100c100a40401168680c0d5810f81c080340140070564130030380e031328249810003d6444010740400e980d5442c16402c0003440e850a4811030300a2940721806500b000d254108120b4908a084001d0b14036001b2004044000880300103000d0180c100307050180c82c0f041d110020007040f01c10040250384440d4400b6003d00c90103400c200c000341182c0d40845c00320039081400206a9030740e0008800140284030100c1c0c08640c0d003800b10500c42891001c0c5035110450104504100103036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 543474073 1250 543472823 543472871
    0x50f0d0903030f032304060c0c050601060c11040e0c1318060b040b100801140607020a0b030c0d021603030b06030402180a020c070902090a0807030314180d060b0103 72
    0x11528803201000007a0054080074031001c030303500b40019900140c1c00c0d8400728100591621203294001c000304401c10005d071180400040091418038a0006d07199921a640c40060195005102c5000310b001d041089820f03005e641000d000e0018800101c0814189507104c052024462180b13541c0c000e01c4401011910070152106203030071846040c00b69070307100e010040210010303490b045511800d1f08810780e2038141d0300701454899640c0e100040e40c5000c031646100740f03100c8485440b4480c10030020b00136071740303102800b41600c12400241c1c0e40e94880501c100c0b2988900024200a1400412550400080c04200c0700e50a0300944060103541042e80c02c0000303511049070001d51060600b0911540521009540340d404103001c00b00510b410b03002c2200c0c80c6000c10a50102269503000a0318050a04007581d5120092200100810341c00b420b556010704000480609480002c40100c3c1e0011000700e81400d2410b061006023410340c1d1001d0350300b0001c0c06401c502107864046800c0c640c1e0400362144180d400c9941d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 543475323 1250 543474073 543474077
    0x10c030203180402160b1f03080306060307031824050405150c0c030c0105010f09140f220f2f01050702030c0303030c070b090d1e020a0c08010603050f0d 67
    0x103001c12100a400e9a68520700c401600291300340011040c0d4008000c1d0899250b001c0e03009105039181000c48644d07a0024081148a007020000080000515000030f0300e405c0201103403043e03240e9444000c120000c2c105d0503619102040e0511f940400c0c0490700c5290b901601c05d1240680a445510042c40c0545200383c0300109203038030049030111541c03002c40d40139801005a000c4140350001d50300c5076601d1034100781c1748981165520b9004115180c54900a0b90044c56000d005102d40705514254940000004240b4440c0d2080d4a0008144055810a55080f02e50401440e10400e203181001c66291103610000c845a58030380b9245425104200007017115941b203000510b0008c1d22400c01110103400810049816229031001410140d8040c000396101e51509035600d5290070305030600100400001c0c040d01c4442d08445541d80c0c5e4547e1103001c5841451410801d03403c030f030060203c01c03481d1140701140030b450281c10690200b080304040d04070340c08a84c00349044914550350041156291099030280f100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 543476573 1250 543475323 543475327
    0x3050723010e0102120301231503060108040c030f060501030302010e070806071103130b27100309080921010b0a050a031410060803070b15090a020d060b0c0a11010c030203 75
    0x4441d841070340c0701440c0c440103105540203c2240d0294a0701c0e0341003038024180d03803084060001c0d003111400002040e044070446040c0e641d5032140320b0612040c440035021904005001700081c0c2807202d046801c2000359807040c0c084400d500715060080041000303020480065007046640480340030006130321002d850001c805000a611080c0d000d4487d03001c10034403201c0700c0c003060182d0307110f4007440c550321401800a80c0401303590710f000c00e1880e0742d08154900d120007001c580c0851100c0d50340740c0d000000648003450030005070048030350800400a0040402e5249c0c451a0f502d2000094a8409a12101c88407000001d0200382489420842140410b000d481c1e00545d004078100f0201c0c4017071107a01507803c8440d05071501e08001181803820354080303400842096000150040030003c042d0b01c4158007e44410b5580b6955400c04001110860b0161040c3c081d69008203d0009807202a4030080090002000703203541c0f4011310b0072594441e4103011043e10242030800d404103455004440007004150700d980a18 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 543477823 1250 543476573 543476639
    0x27061710090b040b040513030e18070c0609060c12110408060610180b0703090b0c1b011b1b09021c0203040515130506091207110312070804030507 64
    0x18004282d04000d0396481a25040303000c0c1507850714401c403402030315400d00701c000c2040700e41409010030080003041402a403a4041e0070007030300316224080e50000035500c3d00001d001403d003064000740c12041c1c0c01034282444c0c81a511015a0032200051480149200a025002a141e1042914055403190f00741980101c00090307441d18185031402c500c2034060906d0f400007004510203c409040c690000e905202c2c2c0000c0c0c100616402290660003094050a40c0c0d14003103801c0d47c1907443d9040044165031007503041d00d04008580c00303121102d00e8494010320040078250241004510748038901403400d24140c1e04500800e036400a8022101001002a80c1c01c01100d01800404025032000f4419900b40c050f2040c40c1000c8001c07920310303034003170f5420f2000a2185111811304c2420310380060f0003009658400c0500c8984552a4000e8809242d0407802c04456444800082410f00340710074070034030741c1c980c00040134000c000b1184098019280240201d50003a5160036080501c04143c003c01da952038cc0300741c221 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 543479073 1250 543477823 543477839
    0xc020a0f08040b0a021f05130305070f080d060617040201020a150b1806040b041424030307051e03030717070c140606040e070302100f27061710 63
    0x58000ca00c03400074149001e944000210107034000340000c00050f0007501c01014140511068078040c1444140e08111a09025a0640d51402410b8005042c4003000c0340303000510295500303081d0000e800c80d245c96500c10a02c00a50000c00282c02408040740b00c50401c5900c5210103143d203445140e040c0c0090564042c146c452000000c0e100780d121350095110b848501054880f0070000c3c2609900c00c1c1c981d64603090600070001031704d074056036103030003a03107000180f06401201801141e005121080e10581c18104030b070320700c0005507000c04040c1d003601c00001d43c1d00c1004400900310340f112070400c040748001c0c81d8900d482a203038801690365070009101c8040d03c8495420035881150410300c5030905000004090381c400d8600242d000c4200ca660300400200003c604050250100b44038a1501420960307042d80d000888486041500c4c1040210030000c40c028240111146610000491002c95a10460f919214006c070018090748001881c52945000c0743c40080026070300031403c0e4140050068240600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 543480323 1250 543479073 543479093
    0x708060a080f072702040807050a0b070b070f0201140108030a03050903181003090f03081503070605032e0b0307021506030c090c1b03040e06010c0b040b1e0a0b0109090c020a 76
    0x7009810b04036007a40c51213070304075031008100030b0070581d02078282c41d031070081008801c0300c43e94030620703281c4030030481c1d200018a4144400e50081e400c0c00c00c40e405d4035041c0412401491503c44d102d500611113000410005800400f030040311083d80d03018802076030341c2e11056449008040b04044841c840445e50032207864070300c03030201115142e85000240d410390b50b01e03121000840c0140503804a410081808481480c059008a001a096000f03011091034000000c0251100408018190b0b49450713448000702080e140c41400500c0300e503c80081651115440c801c2a03109440c0b41b805031003060741400c2c1c10140b800b031071440f41740014060400851001c0c00d00c201d0410023013100641e0042044118007104001520144a00c1b1000095850754104030400002820180c1014107114405861900054419440c15071040c0c0c4288190ba103601c50169001d11010215408500e29a58104201c0840041d074000d85001009903540840c4c140d4505c40070013140d50303403c800001600704d55400300c00310b018004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 543481573 1250 543480323 543480359
    0x1081306140a020d060b030c09210105010e1e0105060910031b020d08090105100302100201110a0c11100906030b030f0708010e150603030304060b04020c060708060a080f07 75
    0x84003049400c503403106259044400c440b1803111030340c0440ca05540d400706100c0c44000d005100e501c54a1400d000820305018081d1171861441076104030031902d10090b40019078090715241d80005d0206503103d01c020311600000f2601c21004800d0540071010300c51001c0d4045040f40c0c409840c440c0741084040070300100c0b00c481381c40034080c140c480c0700d044a52000c14a6070640140f00c1e074044c0c29017039485440104402005040c40940f40e04000901000c4101d1950701c4088a90450754032500c200c0c1c030202a8050108134260000c03a0402141030140d407900a20394150640c400c9211803c1d114600e410062112005007130040003808440c1c00b03004250003540138004d4020300608850b820b4081e0617280d1700d800103a8100d03440300e0351120b00400301a4002c01100c4e11084403248405c0d5646480c1020903900e000040c4080e000907141d40041c003c035103075681100d8010658209582591a103000085d004110603501036005400760301002804000114031300250a041030050001945000c51070345032144109 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 543482823 1250 543481573 543481583
    0x703050d09050f030405180f061221070605060108090c060309010b03030417070f06020d1d04050f18011505040b0f1206070207150f0f141201150e010813 67
    0x1403603102041c403c1010900d141406801181d9603410801801840c003078182404004c42004018003950507580707803120303a010f003041d01d04007400c1104455052400c8900701d4929108910206140e10541d0844014601e0500441c000d214503100d403001140c0010044941107529080800d0042e40c5190101c0210340000d2001d0010a5454940380000e00f10343c003c0d8005088001c250449500c0034401340300100003042e420074600b12052403c580079485014885222080142c00a803103001034560060302c88801402030410000d900c1c01c109900d070061407e42e144c200c2000500240d03000c0c0d081c1401195a035102c07142002030900d00d010240000f4084245e0308981c4003150100d045190740301c0c0a44d2010030302070300000704114200900082e061210540200200d41d44500c1d016408540014600d5222940382c5400c030303050711550340c0481e04000404c3d0f00071448070f000034502107000000c455142c11b0320021102a85022078003d03041d01c01ba00703010403081c0450502000100e41414100782104000c0c010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 543484073 1250 543482823 543482831
    0x304020405100f0b03040b06030c13050705120703020702030c06040f1a070602220e0105210a02060d0b010216080601030b1e0a0614041413081902070608090a080703050d 74
    0xe18400c1a1044a0360030084284c0700c04820842030007980b1b0781c4641c03c010250090101400c048000c1040807900d00c40c0c42103c16182c0b40401c440038850300845030f048501020ba69290b0405001c000c002e5031150384142e110344141d1a4188091400d40c08540c1141d82d9002c81020300f41c03620050444100140c5510806094148a40710204100b070000341180c41107065205410041035103103500806443d00900d289814803001407101e80c443c103039040c42c010070b020700912030381e5a102c4c603440c5000d14a090094000c0408159034030a02c0107904442110502602070311328408030300c000c809003003034140702c0c02020341d01000c01000401d82c003000c116000300c140b20000003041031288441c1c14890041ea03104651071356070b10f420400000c4184207610301c01d008650500070000862650a0212310103001d401000c9101511581001410412a0485003403012103e01c60405220007a448080f2440ba183c003198044000500314200800d80e4090307d41d1211710b00b401c01056440407102600000402e04c1d4075952 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 543485323 1250 543484073 543484079
    0x1506090619080d0503090d0305090a061d100606110c0d0830070305070315030303050603070306050c0915040f1404020c060a0b010e030d02070e0c070b010807090c0c020303030402040510 81
    0x80c810000c1681554580c50f175030703041407618a40782401c0e8178060001c15142006100411001240442c07600342c100e40042107018525402c40380120000501d8545482440d066010794107003900040112616a101c9a5513007040a02c000e854182d1300315442d51202148803103c000030300b12005849101103000c2104801c5030000c9000010001500101e640d100c2c1e040c080180c2c181d410b0290035404040351500b8042e180d1041d403da5102c0c90a40801000e0503101c100040305034804000d410300a5400c003000b4000b41c00e203140000641d61200074401c0c002c40d088840f070b0b512280c0300704c121030885168000881c40c0318a400154040c3e442c500540307540c441c0e02000100550790b02000003034014410707400b0000701180d002001519181400707040d64000d400c6a02c043d80304a8002c10350008442d0060700b0501980e03030754a94610584614503008000065100021842c0c1d54005891415112600c03c20040b0040c2d0383c81c00e846151901c4c9000754554010800200182080e0300a1074100100381d01d410741041c0c0b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 543486573 1250 543485323 543485339
    0xc0b1b040602011401060507110f060c100204030c062309010207122901050f12010905030301380a0e0102010b04020315130212130f0f0f051506090619 66
    0x200c29800030340140c1d1294031038105020f507a6405801001c2c1410068602449952912500001c040c3c2d0a4410720b201d010708907250310350000b00c40342c030300813001503d001064915449009400038082601c0424600c030b4089013043c01041741200c500c540030a440c20003240c1b0141c039000323a801886030314118041d070100051140595030784c6002d0180715185a0106620f405c40002c0e00595000341d6401d8400103200410040c0c54010510080d0381c405d46101e000020005c0310a03001d0992180700034004e1000000000350088405c0d000d25011000303070328410340c07000d09141e010041c5001d050001000c15040140c184002c3c001c800c100441c00c018000480c010550500140c102c1e0011600d0351460101954100494688482c03201020003454404600f072417024800c1c141c035104000c0c03c0ca601e00070310340002418030515914000507581c2c4051044c072640518945109400c5100b20b00b140c1ca8482c2c4171403800f10808800301203204000217030a5600c1c2d56503501c200040d8030415a01a11b854166040c0443d000c1c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 543487823 1250 543486573 543486577
    0x1d210c01140708070807081501050c0109080d06030c06020307030909050603251502031c0b0d05010501060507142e27050d0203070f02090c0d1d0f0d0c0b1b 68
    0x80090300c43e41c50358540a40003a10030040103150000f04504882000b001c0b005005000d00d10b103800b0f281054558944000007070040880c85009409400d011688004031401500500140e9108807005000f159035101d00b40e940740903140008010400c0c02d03905001c05100f03580008d92000c0020100d880d940c016584054046801002c201600644440c06003c0a8452554034400074a188004c2d40703032680a0300c0013a0311200c015100140c2c152500c00c0300798983d0f41c0d1481511940e810500070040c650b50b0320300c003900c05c0d84510000c03646c400c501c0c5030303040200d00c0110700d40500d01203241d00e40c80311341c09400c15200720b0108070b6508400746980d100d80c410100000c05c00c0788440164224218400700d0103003041c0e46010700285240341103600402151001948600c40500307069415542041e85d0780b1604504401e60140e40b40800300d140c500400140c4081c030303203002000001820025504242c4e505030710607440707030141643c000210ba150700c66a8001030b040c901d120750011100d0420b800c11503414000c1d0301e0300c1e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 543489073 1250 543487823 543487831
    0x302040e1b01020d09150903120c02010315030209070e1c26031014040621260a0e0f100f080f2202030f07091d210c0114 53
    0x9510841690140d0003039407824480a80d002d0009040070b41c8003200060100300e090141e41c0c1c0d08121551a90b5181d40903c402e00c001c0c503408071250790200d81c1c01d2401408001012000e030300003420916900052440310890780144c0790003820ba9103103559551030560310400100c810980140000366015400304240550380c12152044141005c4102c1e244455502c00104040a10401c2401c0050000c0445110345075003c44135858654440012844005402044650b000344014041103100600d40184034840305c00c1f00740f148107002d404e1082007241024038056041c0300450365400308001d4000070b010302030704606448001d040c07003041240c04001c26120709000c0c4040000c04e21a480c1100c40d10780214000d0790154408034500014a898440142d5503a082c0641c28001d0440600d510199102030042895801d001d0003207425032981c40000200030940e614510300e00c40710480c2004460300c00850481c01120000f0142442d492030118a10032030780c000491411190b503036000310013460151105803841 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 543490323 1250 543489073 543489101
    0xf030e010f0c02191a074b081809070309050309191802121302100c032006060f060f0306040e0f0604110a12020108010b130906031101020106060f1b020604030204 71
    0x29500b4510b000341c107040f414010400b03032001c0303c501150508045011f000c00c07002c0c03403505242d1490342031102d0b0b0300d40358030301c240500500000100700616000748240e0a08441d002c3d00c0c40c402603078400e64114225072050700014903540041003920b410707103007200704480040003050761a20560354803521f8800c0300030044805c155541c0c010900000c10510703070410303a9100b500190701c04104901d65002501e040760080c070700342c1405112865641418450000078120342c8000c07010001865002e00101c1da1010202d40040c07050031b04031420480380c10504151440008242c1d0103a04680b52602000042c011114102143c3d100d441c00c285491002006064041d134080c4444803810000d103010300ca900610f541043c040005461b0409c40140d81c40000d90781110b0035415843c0c2c0303c80e200b48000002201c0b9911461842c3d04000010083c0702e02030302ea64514010036002001415910b180540e140707004004100c02107079949000c0030210010501a0955520040036940303440c0d00c1e6400901290402408822 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 543491573 1250 543490323 543490327
    0x60605032506080a0b190810151202040b06030c04030209060604030302210c0f34060302070203031e0304060b1f050c07030f0f030e010f0c02191a 64
    0x2046040600c001c01e50341040040000c2003802089040c16800710074898401000160300014580c05860f0380b00070f0310214004d0a030101e104500e800031070b0748441c03401048910302030140c050302d17104030fa13104480200c455001004812880c0040007416a2009001680c000f40ca0355810881e540e585070085104500d5108042e44581c15030050000409000348210700410040105001185d00000d800860041c924024821900003545060390750203118100600c82c1708065180700140000b0841070068030030340c802031181f040200c40220b000c020240700302c1c80004031850107128a034865001081c4150020703044a03e850b07900c520030341c280009105000303041c0e8008024041085101d01234040c00407800c890f6040d4401c180c0311a040c881005e221002e041c403900007954a0000c1090196100560304812491420007080c102503400300c030550070407400628442c0320520698001c43c07030041484550b0317071132032809290f42c0d0074408864154507000e60085002c1ca4006294540c003c0b200ca152820181126 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 543492823 1250 543491573 543491579
    0xa05010c0f0b1f090603080409051e090a03030e0d0806130608070f1d0702120d0b0a0311010f0c0308010501030911030708071505120a11040305010e06100602060f0a050a0b0d0606 78
    0x1001081031a0004c07620281451401c1000c2040c10041c0d4083d110004400141da440b0f240d40b4030403028900640b4601d0b00500d50421102c14804034600041038000d40302480342c4a14500d1741500c40381c1e00084040410070100100c0c180c0c0c1080c040d05610365078000800120161180201071600c2081d600003080444074010501c4502c80082e40c00c0c201240184402c50b1a0500c40e101940303888024011404820000c00c0d00080b0b49115040844010740150101015549a05014800210041c101800701d030400c076001401c42c0c4200d4440691940540d00e1005903420320b00114098400da202c10756503d0608071701514146d070b0501c0858010701e00700c0014181207140110b00d0382e0415411807050107001c010310200d0741e190400448594824410030f00081e13404204510011907003c1d64101405561800c0700a100d00f1078001b400902078001e1401c1c00348540e5803070384105e9542c88211640e5103824222004a401008a6089a40c000c2c0b40c000d404208100310201241c5410440345047d038109486131020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 543494073 1250 543492823 543492871
    0x50109020f010221090102150420090408090904060f0c080115231608070b0907090e0d0305180a03050d1109010504140102010f02121b090a05010c0f0b 66
    0x1c4032079039020700280800e5803c041400762880c10f00340d04065842c00004420501d07030710a0042c52510552074031401628101400c280041d00c0004103069102e6001d0034480c41c4600d8400341c6680b041c4d50090341c0ba4a0001010140507140d0400741c0201d4486868440381c3e240d00800d80074207061024230f035503509204c0d0315200e0104400710035041c0342c05c03d00c8886440b9655900c07162210341181200c2101143e65000041c81d0361128042c01c0a0203050140c0106650701042507010030140150f4003601121240c40c0c480d10448200c480040015007554803500c45100347e036000c0d4000c10f43c4440700002c0d03925084000c41c42c05090801c040012400a4030025a15a41605911603131800581d512542403c0200f0800003801c50302c501d01542ca21581c0d2a0400b03103071a80b003508400d4040c60103030425900c8102c5d58101c1c0704041c0c3706482840d0100280d004c40c020344640d0006030380011703034010030001d02a45000019550300b038840034150303507110407851180f000c10030301d00c031550044580b140c0381c448045021202d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 543495323 1250 543494073 543494089
    0x11071e02010e2b021302030106020304061403070f030e0f0f0115090b2107080d050702040f09020f0409020a09020708070209070503011a0d0207060606030e010f050c04150c0f05010902 80
    0x1014401d140c0602c0c0b00c41c01d005070000401e040c0c221010f04415100d914000580142152405003c0c2c0034000400410b45541c040701070421151a0385482d90800c2940710811124002150b00c10000b55041e44003003040c0c3d100b504900c1030b01c5070355415103810280881801d418052030b4225007980345c0d1a429881801c00120179000001d00f80f401080082c00a00b100003041400c4c000344400098110080940414006114940c020220030046801404401c180980160000d01040c0d114514040402203c0c030b28034000c00445540c003e04241180413504208401413160b42c105036084012020003150340c0f000c5d4402041d055000702c100c2502d4a5081c41044000304004000d0001c1000c184010402d1803040400205481508100c098548020140402c020700032500090040d600f4104005000e41c0c2503407040c1c00c0b001c44400240712100c45140100e040c0d41041c1d60f8050101c20800080103032208421490a2441d002e01e45004c1d00c0d0501e45409002d194035280a603845d0359214489821441c000b81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 543496573 1250 543495323 543495347
    0x910030519060e04030e0a150c0b09010e0703061a030105190c1d100c0b280605010e0904020316030506160806210f071e080f1011071e0201 61
    0x4014440c00f4101001c1140ca60b0300500300409000091184100903030b40c0800c103c000d00000c000340d240e0703011804001490310282c02816030303080350020007107150004103000d01800101204028203241b40703141d803180000c110f4040070340300702a50750584070f595907800c0c05428042c4181c4412040d10344c40e11b406850840c0c1b44802c039076040c442d900c034201040c800100c01c4004402400c0b42c0340b45c1d0001c807081003039442044e00007006002188400410070300780c89116200031200f280004a4085040b40d440d80350848000d4003403940400c940701240a1103280100103564800d10150030340d140048900682c07500300805400407541c6030029020007162084142c0180f01020359481c2502090070f100c4007181d00307030071906c003030340b11600409040c0340014408001c2503440c841c5903012220b049507513040102c40020b074090f5007400f02d0f417026800a9074900c0013410190320508a40609803c506940d65600101205840b100e01d000041c03002102080c0c6103d0707a03c086039a0200115110300a41c4001090b03250806 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 543497823 1250 543496573 543496621
    0x90c050a060909020705010225120201060819050f06090f0118080906031b0307020a1e05070e2d010501020d1701050d05012903150c030f040809100305 66
    0x90000c0292641c0082ca041c212501e10b40010390750440703030810a02910a00c54401d0b6100040c1488001c04540c1500f601151401001382c02c050381007031300089080c1d420600c1951469485803201c135990b003101c0540705280c0d9100350102c581c44c0c180d89500d1414001d0882e41501e140e01b21a221840fa80020700501802281a05050300c00c0d078401d03a1000a0f900034105424011140440050003459191281d45440c0e0300000c2c100c3d440345031412000750341d801850411191803000e201450802d5612121103000941e22a001d0020305080170340042200c200142854003c0030340360810300c410710554022071184a0740304003070003440d030400d40060311b8000304001c0c090401172649016084640c94030011410740c1c000301c4040c041411182022400340a14240e40302d4107542403c0711588991b0800034030703100914160165a81e461001c10185200501151110405541080000c5d441420701c2081a4030030301c0342a00d14242003402010404031400d09840e1408a03680340e040c04030001c01c208458480c20249 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 543499073 1250 543497823 543497839
    0x513140c06071403070218060a0f120305090307180f1d0d05160212060403030c080708040308130f0b0a0629031e0a0b18040b1b0f0d090c05 61
    0x40c404616944103142015000c07003040b0b01c55490300081803046401d0141c0050401c0342c090038800401c10340c1c1c2c42c00d44601d0720540d0b403c80d002601070250b080c1c0b0340c101d0b00c82038001c40d01c402031518196443c1e071003400c84c0c41d858021600e010601640002a502c0c1301e01d40e000c03000840b600000f9043c011504500c482e003080030950f5010b2542602c2c009029420a06031703140c0103890310714540b1003103d4807111100017584481e60741c9202004100c0021000d00c518041d41d4184a40c09090300151132101041d0341c0000000d84240000300800c2c0541d0607036030030190581e0942c050b03508030303120201c00000c6910121201100001800200c44207030044101814040b0b0006c40348c59419800f03000e0282c6640c02c0103c0304180030000a48659024100008a5031104a15000351400683c0c00740246001c0c80340c54030400e1141991520044140c03c0180301c0c0e54092a60940c0e070300e4038640c500b00418906802c0d000800c040080802510002014002500020350301044035000751404003500710460300014080e0b0702c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 543500323 1250 543499073 543499093
    0x5011106060d0606090617060c0301030f080c0a08030f060f12100b0d060c05070507060309020a0e1302040e0a0506010806070e01201911090609072001051314 69
    0x1064054000740704440c2d0008203505454940054130181e8804240180741040000300b1003141d40f07503041e2410700e075402e540c1156203030109403500303000a0101400f5100f074501042e00040c0c400700280400315241080368a0300c0303e80d030740300000e42e17004845c80e121801c0c2da60140401c80c1000c14814200140817614550001c6d024190303981d82e000c082c106001c145072110b1005145403245c00c01680340e07a4010200340201100341d000504158440e21045929100c0c0990002e640d501c0b91007406940c3e40e0081c956181e1524003688c1c4c82d00100c02401e403101c1e0b0b8405041540050381c0320300c134090f640022000a040d801032541040d5040c041c0503401a11160481c03000c1000103540100b4124045000742080e81c050000420340070344484a00c03890000a1050b4040103d05035480c0c403820001302d1083c080c0c1f400006041c400e0100c01e84003503c2c5280c008130740c040402c2d2101d01603025403810254501c0000320f00b41744500306c6400d40e03006496034050b040c28510510103004682841030040d0340c081c0020920600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 543501573 1250 543500323 543500357
    0x60302120708190212100204031505010b09040f0f09150c02160509040c09061805090d0801030809150d06150504030b150d1b0501120b0a0b0c01060e070201090506010501 74
    0x41c0c512000d61110b1810740f910441d038440f150014461400000c0b81d103071040c1201800001c2d4084c0c0415180500d8503526081d40d0382c07240c0512410f84101d000d4250414503c00705002c007900100741d1a4810a03100d074104c02ca44c6507940306007200c00b4040e6403d030000201090902c001c80312088410000c42d001072414865107034240420800f03c48064070302106542d02d50070b2050145426400c0a041c0b28108070000503030340000c8400f40102800358004010a4588401041d07444003400030035808503800d10700400102d41c48401030180164060310010302e10000a01410807580302c900d0300c501d1a9510a0240910810031000d80b4228080c0d08009180c64110744500c6451840204400400461403603521826100d0030171007103c4990103000e05c4080d44940c0c6000181d410103000d00b900051041c00042d2081001e802940c135044000360034941c44d14140000d0300c1844d0b01100001c6502d42d242d000c00281500e6081c0881d100b450994000035030541c2c04d0cc1c100b0b00f8400d069125504000c0d0465004400d41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 543502823 1250 543501573 543501583
    0xf05090c070303020405130504030318020907080702120f0c0d0c0c150e09012301090b0a031808070f060b150405130609151e06090b07030e040f060302120708 69
    0x4041110041e440391410314080f0041d12440d0050b903040030101031266005a40b41c0c1015014901c25202408258108840410b58205018000e54001c0029000c5072255011303045241c1c10828601c1980c803044070034589600240e02c0240d14400451000607010507c0740c0510800b0000b4a542c50300d00201c100c00e0300e40e81000d0803140605100207540e1440c548016000b4645100d0054019089481c113681da2141800d540001204005040705d042042812641c858070441050b540c3c03103640f180c209680041c0c01ca0092401c035840302c404c281c0b03c0011001044017070001e0b0140d240301781594011403201c0d143c90302c00d03115000f00c411b0003400008081111440301009507010303100300755260500d05080940c1d007400f03086954803c01c0c03103910b00400708201d40900f50065081ea003c049088099160b45050400c540806100e000d000a50000c0107002107210031004141c000c0c0039242115055581c0c0b40003c08071040c18030b00c00703d810b9490310100f003142000c000d640551403640b0090000d192504818603210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 543504073 1250 543502823 543502831
    0xd08041d0a090c051c06050109062c0711101d0708120901080a0f050a020a020d170402060310090c0216050f010818030d020309030a0306120312020a110303100504060f0509 75
    0x380d140c0b41d105018800e492022404c17030940055052006503035135400b600007445140110525902c210403004203d00390800404401007241010605079546c1600c102e03520001d0150050341400360b07894001d40390800e401180c89022420107000c54914284088900d014441d074403001458110003400701500301e0305402d035a9401401e092182c010740c0e4070280c0b10b00416071904803e8805207030105200d030104869024200c400c406800f1141c50a481c4041990400c40412504000900c951b00240c0113080510203903400180d4941665589611441e440065540d0240e5002c01640206480380c100302498501e54000c050564a20b2100b10916000902d001402007120340e42008030040c0712030a0100300122a10000d100a04648038104001c2a544079030204410304002401c010007c1002d0462100c8a042d01c1e5054940840d0040c00502c201c0c0a508144807070800e001010100316003241c01071004501c9040041c0001c030a0030b05050411080f507049401c07220314410300200910442d22001503990304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 543505323 1250 543504073 543504079
    0x20d020d05010e040c140621160903020f060a02010e0f24041208090f0d0e0f040501120605101212020f010c0207180b0a03081e1c02090d08041d0a090c05 67
    0x50b21000d0106081c2c0c0300c0c3d00309084105052880e0700c500207501d4100c8e60b004104064624140406080c0708903003c040034000603500881001140c021440c4c5407000302043d055a0002041c0e9207490b0302e85a040c0b40c1800903200d40f50304955a4601d40255001e60780c1c0c481c040005031030055041984502d2a03048103105000103100903040440c0c00c4800c108410313000712203d10101e648a810003a0024100d00c111144240625a80080710510345054020700d41610071440e01c04044600a88400016000140c00900700c00074079100810a00c60340c01c0c80340103c60280c184001540c5812800903c0e1080215050701203034036203114164041c2d4049050401c076007400000154032006002244010202c07124515802001030b000001000500d60103003c03040c07205440f500c1220070f01c0d140c410241c0b08203032040a282d11950301c000302c4a01203902406001401512070004403450b995203103055030143e041100280b070428105204030080c6002c0c0c580c0103a090000344814800c60742d071803441d40c40900030307584 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 543506573 1250 543505323 543505349
    0x30516080702070f0915080d230408030f180103060f15021212041e0203100e0c0405010303110f0c030a03081b07030c1205090f090a060504020d020d05010e040c 70
    0xa41e1030310812810002e080c0030284140129900c08480000340185d80340404100014000059004800f0030703900d0148080f0f4581c95541d010114000c1c0c00c019507000d01c203402120601c0301046829003080940100d00115070482d43d503525615140e0a03003411404841d04141c1031072814030039000d0b0203c84a00302d80800304114040c0c00006016411300400401030b00001c400421030710b481088008049000741d024900d9582001880e14048a14000006011707400d64081001c41c0014802135100790810f0710303120250b80e401c00c40f010000c1d003552020b91055000680d150500790383c0c1002400b0b005040128040200b0440300d8280229485400c8820040d0901c061000016110000007401803090300078032040c5030342c03508145005409c0b4010154141c0b0790b600040900180c0c00c3c040c00444040700e80c014140b640420341e200410900c0e4400400205800707860b1400020f036503d5900203008982c0006101685605c4c0550100d422510b050307100120801e031000520001c1005260030380300307031400a5a041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 543507823 1250 543506573 543506581
    0x70603020a050d090b07091a0306060304030302580e0f1e01050c0405031f0b040c0c0605090109031e09050d051b04200309010603080f0c070603051608 66
    0x14580f4028010140700807420107080c0404c1200c00035501d446901280c5030940034030748444070f05003d003506409004511200308003050a901e4040003540d0301034401e2802514181c01000807c10f0750756400103500217044644a500f041e081005590300300c2c802e480f141d030403881100c50748038036840001151a030343c425900d4991016480d414008806100c2d500b9003100d00e400c0c40854a4912a6808056011203500e0100801e9080c48540308803800c035500100108030301241340100c81120040302c1d601013412a070381c200c40391564407a0b000d5900c020542e070715110744000c0c450400000391039005000d05801e0f494010503100003504140311000c001c0b4800b08505203014117010540c1c248038950841944440c41265520400200159003407200011031340f08101c600118040c44161a5164504101c0c0d44003112601490484013010b140c0c001007140011a5170b558a84498042d980000e06407009040700103481c42d8412010807640c0014011482c0400c844d00c1c0919001d044c034010440390070f0801072180041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 543509073 1250 543507823 543507827
    0x120412020d051f0c0c17090111060a09031704030f1d06070b1911030c0a0201020409150e09030a1209030c021234030b060a090204031220070603020a 65
    0x500c0d500780e0301408840c1c0401e54207404080d0202c10f01d0401018504180c2c0120710144144044211079500000341c030840c02004201650030340103001d00e54100021078030300d540c24a80422000b40543d00d102c40000b80e26116040091107445d00420b0680d4481c0381c0c1041c40002980f00c01c140d510612585080000b4160780c40c2094410504a50516030120001c14814148551540c80034000e042460707903802030584400000c0252803c1500c4000c80440a00002e00d0044188000340b216030340074400103107071948030301e05482100c1c00c0201c552807007103120f079060113840b05400c801c030707008004100114100700d10004020700c4803e94107954140c140e2540380200416004003001000c07660300a2450321500d61f480251a44c44c0c401e0081000441142440c0c500e10300d441d51011309035602103500408200b420b42d110000c081e40058129a0000304210001a1900031031000c0e1014511030b0b16408125114071100034030403005000d80b40404408040342c4002c0810004601d8100c0710702e403d0158581c103619a013 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 543510323 1250 543509073 543509089
    0x10810030813180515090925030215030c041404090605070c0b0106050a0512070e090f10060504050303070b0411061c060b03060303031527061212041202 67
    0x9121540c040ba59042e101e2000c1c80c0c01c01070b101c2020100054400c61003024040d243c0580e407100c84100102603010340c9042590a0b1a44407403800e040701d004582240344140140c00715140900142d0200c2018030451820b07040c0794039101c41c00402c0d01c0c107504007255003054911507445940d9110701c40c6100c0c000305031500c0c1c104088640e003000d03040145240c009800340614405030400c0300c0c540c0d41d420000c03a803030707004d1002c2e00d101c0b03115542c0e803a0030b0076445514500001e501402c0e40c810b0040010712501c040d9900ca101078420b0b680641e0b420745c0e608001c44208140310280d045031007400000d0006100c29100002651050b0381c00c0012101ca58846040c80e034201800b401c08107801c20000600f8800f01900209410b2032864080c4c020400300b540e990701c0d06991f000640304c0560541040001c00e01c0342d02c51440d9403821020082807000603503040d10004050b401c00740400c1d01e20021a8040000618004046a08042c500c034050b048119403600d41c40b00c0e52045005038030702700540040850039074541001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 543511573 1250 543510323 543510329
    0x317090a031e170f041806030624060801030f0321020408070e1e0f092a120a021513031502070c09200306040b0a17070509090c010810 59
    0x2c40c0c4112011510350280b0b16081c064416950410b0081080d05600d1a0200301c0e010389104910786414903081c18056540003408410001c03100d52507200100102d0309600c030b9903240c606914259042010400162454495540c2c048001d04c0300100040002c85c1c46140d807400120307414540b0324002015131030201410307103a0082c90560f05101003804501144001500d1051b656140e1b900000d83d900d05000c402d0201ca0010075036503800c2110040f403100e49040031025007115540f41a5508044a44400210014040d0710000302c0300070555484043e040082e0412a02e000c05406006100c007150003140e03294903030400054072075400051181c141410042c030040a1648144884550300d0b1251440c0080d40000405840300000c0721000a0320001611841104908500c003c80f401c2641440201c00341d003000304003a40141c0c41c2c0b0040c0d1455540e190040001d80200c0e40e80c0c003110104803100394034021281d00304c07500901001c401c0c000040000200200344150900c1c212100b40c0d14103000240740c11441e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 543512823 1250 543511573 543511583
    0x50112020d1b0818010203061309022d090a020a0c080901020c0303030408040e091603030806010c060e0604060f0908040302100c080c01140c120609061c03020a02030105060306010317090a03 83
    0x910220a065400b03003140d400b03034080300b04c00c414a40350703009201d080344800d8500300d51114800c0100200c11a442c0c01500096000402c007011aa0001040d01152400c0c002418144048101c0900081c600f004408d501314151980442c02c0c101c80180c0600000d100d404003401c040c0000c208001035a00c00c110301828000040c058130345078142440c1c40e84064000740070b5503c1800341280000c030203000001e40d2601218108120007800c81c076640f41a500d040001d8891410069105d8801001c1a041c1c010200000040801232006107030504251007110110f915698101e800d2291240108803194142d8080d240c040314000405508044140d50050f00c01d8030042c028030010815082054040d845000050811142e210165803101c2d42413815108503d46c80049040c3c5601144150504810a540c4400e001d4214282c1d0b0511131032034510007200c8481140160700650301c0c001103041c00c0c0503243e0491802d030000c0407a0b504554410b8442c001c02c40d2448615007001c204448160b5496110400450300303e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 543514073 1250 543512823 543512861
    0x3052a0a0f02030c040c05030a0e03090405010b0a140a1d040216081b0606090406020c0a0213091104050c0403030c081909080d09032003010204030510060e0c04050112020d 75
    0x28504120098426881a8803034010384d2910f1000e0b09003800348501005070b40e42d81c42e28594501302800001c1007800c2403640c80d8401400241840d071268441d21b40a050411074160300c1c1d1203c404020500d400409504040e9041441600d0115030024803941c1006020920072080b14000c102240080c000c00803029090035820586105010115004210040c50f0291480c1d9040c800002c1c00c2d0f0301c44082c0c1b01c2c0340d0402c007070740000b90102c0d49582c00f07008565000c60030340d4800051600003414021000101d41d68660303855a12030101310f00b1000c4400c0024041e1800c2c00303540380522105545001d51301c4003505000c4458072031010401040100c85850640f40404180000e001100070030710304050040050700c0c8103402c400c0140c0c0d4040d03601902126407044502e0b4698078050810840100030300c81039038041d902848040005042402103841318100800001016883c00050b0b51081e034024000000c0302c0400c020034030260341e01011170402c0d00c1c11000050b036180511003c020081150390740001d030003000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 543515323 1250 543514073 543514093
    0xc390f10030b10020105040b06010e0301140403020d03060609052103070f110a0509101406070213020c0d0c0b06010804150507030605040c030e0601030f0c15030902040c090303052a 79
    0x5502040600b40140c85241d00041d840500364200c65040d1380140c0000c40c00000500702c0e42c401d01c0c0b501c415040181c0041030300c52106000103c1a05c0c1641c1c00c9000d6000b10008035070503a410b10400d00100300034909200c0b000c0c90030011a4007401c080c802c800214a04289071101c00780200125a42103910004d002440d44281c103049520210000d4200e00c00c2c001940000b4041c50807962030703406210f5901228a0f02840d0048000085200d1040550080380600092000d03039140311aa00c041d0740006800350b44c1d805c112040c1401e00090000f08801e010140c40c04001081141d03500744d0340310600f800e07c12110340302d030f09214040b0f14cd2403000540040c1018100b09100c0e03459000b4000700d44064805000c040e2000c40103400f591008030844e45140d000f04010030103d0313200f044503083c2e1406100c1c0c410450351a50f10144031002d0207444040071a460360401e00031400c2502c01c1c0250601c4034500303460500d08503a40103011b0301c2074001452100000451105041d018220000000607080c0110303064109 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 543516573 1250 543515323 543515327
    0x60513150819020a0f180e240108060f040f0809011404060c0c0b0f27040e0d0206161e12050109091a0c070807030c0c03080c390f10 58
    0x12070803000f02d000309590000003812040c58603542090722400c0006606580c5210b43d80d1000307000c800541c0586101d0020310803001100c804c0580e9440d040401c140101e981400921071400750080c00c0e00d0003030301141c41000701180500400c500f1542d0300a03d00c6569901c820012607450345108030341c1003e8840060000f0321103400000b4454080d1091280004032a0b5070541104103000f250aa414102130411a40c201e9400c0d0042410407004d880c000038146445102c0407804444082c1c2c0420f01583c04203c0710200290104540caa001030110501c0d0b42d41c04404200034040d56040f29881c243e2031841d40002140c50050030300004c018407044003080190780d00c0009401a08081500380c501c8003580d580d40c1c1604030048129486401c0c80d09003607180030340568802c485688103540c15000c000345034560200040d4000e00c502c00950240c0c05042e00c903041400550f0803c942e40340182810b800d6007000c1c910060b02d42da142ca412201c43c4201803401f00104001c500c5030714012405d19841601e881a10203425 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 543517823 1250 543516573 543516613
    0x702070e01060f181a0f1b030702180702030901032309030a18030f1e050106080309041803080411190902030a2d05040606030501090b0906060102010605131508 70
    0x50f510380d40c0c1c49829044507048110000a0b001e104808003d840b001c1e40070800c058000c010b078100e42c40f400f5160148134416501d11200004a15201c0d800c00510308080d4600001b81310360003940d118401d01c1c18103060030041d54900c52016944d042c1600c2e0b012030b0501c66a4058616034009c40c07410044a10b00d000702101d0384076440300340e880002c950700951400c564104404080c0941e544800400c84000e807a44814a40c0701280303103405000d04410740d4490000d0002c0c000c80004103c844000d54072031120300c00b0841911580c178210860244014a1f420109074861111500150000c00181c0307a14407000104114030000d0310001030301d42c0e50503c0000c0304440380d402107210741c00d640703010444a4a0b880c0502c8510444800300c200f000b85000b01c800444402d54003003034000744a07100004035155250759041c2900d80c0d00c0000ea40517821002001036907001441107aa10903001d200800005007850000360ba03c606030340c0d004d0500c560f1041c00021056042c007402019121090441d0801041c08604880346 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 543519073 1250 543517823 543517847
    0xa0905030c0114010605070f0b09030c0d0201020409050f091506040b04020c0c122d01060306090807020a09150b070204090b040b04061a0f01121b09081b010f080702070e0106 76
    0x3c401c510f00010340070b4412025203581641c89514404c1c00c2c6556203c010154202a101d10f416000400c0040c0d0702c400200075480d040b454a400240e1101d03d0300d440030003104c1004140c041001912010400f8824011489031322b2454111020f46a54070b40710007042c005c2400e00c01c00382c2c0080c0b00192b840c20304000021418a038240c11110b801c40c40000ca280d4640b01c0d400140030b490001207000040c4640d854107064201c00d01d03044000000c40c00e580761281001d03910945026554040002069025030a2040d16140074250140c824007062110203a0003400710058421600d0a04000c0782240440d9142d4000620f41d83e000380481d0340904103400c0102c08588140d8040364841e00c2d2103400f0241550183e00050720700002021003060803200c00c015501000c131414a685d90f00e6070f80da60800080b550034990307499861103036a644422420f0207100c6d0301d40700100212615450000d90340b00380c00d071392050103148070211920301030703080340c0319014145c0c03800b9299080044900202000032980783d5014031102c5007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 543520323 1250 543519073 543519101
    0x60e0903090312070b1311100306061d0604090b0105070b0109141602121c110306040e070f0611070b04141c110103021806071211120904050a0905030c01 67
    0x1c643d540032040d4200c0d2041c070b00300030280308140c00050382c24981e0b45110692580103a040c5081d0b0f07282c803400650401503000340c80010030758a00c420f21507940c0c085c000803d20714035004455520b0034200300041c03c0380914441c2042142e201e1620900340d9218034141da40303455102c16001d6040d41c56113503180180911090394540e5400b40c9000850100300b4410040c0c0224550b0040d041c80c0c40d8880d080706040e4849807101c0ba40e081c044c8106500b04046100e1410411101d01080352a81003000802042c0c0e202251411280c0c0c0c4070310800d10a11401840101c00c840f07603401c00011030b00d041c1081134204061548070700c0e0041000301c0c0004841c40740b02815541694110b40c480b1030300000d10500035079045480c1010340300f00081c00c910649940250300510a0034042c491040c0700303034880d82c006180d0341c3c0115400c503503c41c100c004121180b900404031b03469000c80c0318040d01003002e00c001d00700390394005c3c0321001d4412600c800c04200c010002e80c2c0070809036500807007641d50703d011640c901400b0b00460608481 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 543521573 1250 543520323 543520333
    0x311040803300f040201030b03030a180506120c07020a030b040f151e1d0f1e01141506040306050f160905130e0705090106021501210312060e09030903 66
    0x28103640078811207501c02c1045a00080039101e14400c0024490010012410b042c0d80c0e200c4480b050340c08101810800902e55502079095181240d06031120180354041c2e0300400040c08500c00d60302119040c00c1c0d010ba4019001c0b92038840302d0000514080181d8409000c170b01d80e6000307100a11074000d0600f40403a0146680c40e0340c03489180301420454103045080403207402e483c596100355060070380020744c800303802101ea01c001210003031003039040c6050b8440c030300c199512101881d0416881c0724104110122244d000700b1200702c07400203e00c180103008100c00b410490144007540c1b0342e50741600303490146800040800c8070f0300c0c1139040140c1d02441500c045403d07100041d070f100701d6a840742400c1015200040c02c01d440d00c281ea00d4603c2c0250610500100355809614804039058030781c0e1003168000d10345640109029024050b1421031120706030000d000300d840742c80c00d5001c0910041c1080c3d00c46035042c0b50031013503815043c0c2002d00074803e40c2c00144c0c81c1c00700d40091144050001000d000244030480c2078038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 543522823 1250 543521573 543521617
    0x30a03050603120a05070213110c0105090703031b080403060507030f0e010501080d0c0501020403021315060903020a03240501060207051017010b070c03061427100506010311040803 79
    0x5640d50704a41003c0c81410010825480014421300c06400c1662000d001403518098403007800003654402a9030316056880170070848c50529007400741940103098107010300381c92825900c0051034900d03064840c200c00700940100c0020410341c5000c6400550f00100104514284010010301505441500401040c00e201c04002549410302c039040c100c0d6050b90003000d8000d0700c90030580d041c0310b12070020354055500303120000168032088400280c2c0443d545000500c076400400c0864482440c1c1c01c403100300503001c4030a00060720345060507000c0e203400541da16110000400d01c2002c0701180707401d030f0501c141418000200143c00103000d405590341194207c20158241404440036842c80c145030411601080040210b000348030b0080029038091840842d041d81c880d1140c0054541c4544813100c030001013401c2180b003002541400864200100e95480292903030a0761568070407403512203440ca599030344080b0f016a0701070340c00560040d070396881503500c5a030b4511200d0b071217401c502c8603050110b002c51104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 543524073 1250 543522823 543522829
    0x60f0a0e0601181e020a031d1002070c0504091103010c03020f030103060c0203130e1005010c08270d0c03051005060604060807050d050a150e060a050409110d05030a030506 75
    0x120180c210040016a01c0d0140d20054001004180c0f82443d1355030390700c4013000110741c1080308202070101d40940da03600b443c1c030010121283c0103943c1244265141044c03c40880114101e44a01c00002000d40c4030001824400100360b0168040f907449840c20712140b00f003007205184401e503824114001c00c1491030300031091341644248008440c0c551410030042c80019400d5014144640070703441141d003041c5011106061130006904002ca50380b1044042082c051100ca03064405441c080ca4807034184081c99032032454600a1140480e030011817841501c03120030034015100ca02001c01030451090b00c0c014100450303801010300094641d40200e5040c41e801c0c1009010340b90003544007500c80c03450645040c0e0304851010000c1d004d11304014082100d09298849400707564083d8550520000700d082c0b680c04800408032203940319000d01000001040400e40d00d403526282110402d840208010940740b900c00704c220304809889a101f20407a001c18288900080907010303046403524204443d450300010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 543525179 1106 543524073 543524081
    0xb0f0f030106050d060b070201210e032205101b060f050106030605240f0a05041703030718080d030f021b06070314060f1c050609060f0a 60
    0x4003c0ca804c4c82e0f88100c45c020080941094948202075001070b05500d400038601c0704120410301000188002a00701c03e030083c1d404402e1b26038801e4940455580144074100c403050044030b00002042c1030401961001c2441c0f05038603003411032011034101080c0d50b00083c804450061704c2d26441c42400055000f0180640000d450215420707050070184049291080445ca040d045001060400d4400c000100c96850b01440d1107d41d950300188802d17141882254003000e040081c004060018190210107540110711076541c0d03c080d12490340d022000e40c40107005002c1a9000101901100f5009a000604d025416071001d400c10081e44811400386040b00742c0100c0e0798002e0b0041110f520b9052140c8581800b80c0d1114854034101407003c200502d000d03000640c00b5142c16800100c002592400e08055281c0c4442229200e2410800094883c0710a42d0f007900c2c889440e4000c103000c4120b50003 = true := by decide +kernel

theorem cover : BRFrame.Cov 543345323 543525179 := by
  have h0 := BRFrame.cov_init 543345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 543345323 ≤ n) (h2 : n < 543525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
