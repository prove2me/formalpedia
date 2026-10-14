-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1085
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:10:36.045577+00:00
-- url     : https://prove2.me/submissions/0330e176-a905-4965-b314-a6adcece6c5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 194964028 ≤ n < 195143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 194965278 1250 194964028 194964047
    0x6090504150317070213140f071b031716090905040203030904020304140c040213030b0c0d02040e07080903120f04030309050607030218030604050c0d0c030c0b030a0b01030e1f0b060406 81
    0x2481407411b1080d4099009441c031400c0c0c030300c81500ca2454416100c10300103010911008000390208102c034944100013810400366080350700d10a8458074030308000b103121180e00150003030580a450845040000300a98404e0201c81101c02c0980000b403261120b00209045100d8607002d150080d000109020410012034844006040000290382da4000c0d8142080203a208010305104c0701c2a42c2ca41c01d0002c02d00030a061034202141e40e5002d40f030049c6041680d0284d070865030140900c0e00c4010200560f030f6030041c040a80c80280c0714042c520340506803001000505c009040140701c1d500e10360000d802c143c000d91240d030010f90050111203562900c81c4c4018040d5104107950b868000740b10805611508002407642c0c01141d10101406162034440b00740f24042603885401e40d580e195203403000010503610a1003e02410b41d0382c04403540c914046036601c060380c1e94205600d041514064030141c28007008240c80d08407402e02050b0405081c21500702801074120405120b0f4000c1c4005000036181c1d8102e003410703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 194966528 1250 194965278 194965283
    0x5030d12142502070302190602060c0304020d3801061803120302070510020d0b010801050306070806011404030c0b070b0c03010311270405060105010305100609050415031707 76
    0x1800100c1d079001c10080e203450140c03568412a2160103003003000c0d1410164040c03031050b0b148112511555660000782031164405005900840c01c0c1c5824420181d061108136845040407500a00d0740c24180e0110b914030b030000001405655131801001d080c4541c1c000009010380c0201c01c209243d01020301613001d841b400f07100e8280032400460248010720003a48010f4100c036049500e10b5518590184190301a40c8043c03002c0703135036004541e0600391800e82480035000c003160f008000100003901c400050840c84040e040b1903c244d1040c010000705179400303911268070000030701c0c0103540901c1c465404104c0380074940004081c040e03540d202041c00501c0101a0101602804280d440d41d2031307542c0311007020f21081c0000b410f0062450a4140710742003d94085100300b000250545da2002e20403080240404281d508030b403240c001e030004010540e450301619803c2500c00001c21080d900d8490301a00f0170100e807182d00d00840c0c9074059464401c1e044000c8038019600240c1590408098881e918119072150404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 194967778 1250 194966528 194966531
    0x31006091a010e09070314090a110d050309192706060f050304030c030504050a0602011b08070905010c05120309030c0709090206030402041d07060c061d030f030c0405030d12 76
    0x507220040c07840709903070415070040c0c5820031084030550500c10300b1840102100c050648803e021040070b010b0300d031800d00c41c2c0c80b20805051281c550f03290001c64820441103881c4180fa80744000d001044c00030049504140d01220001c10360120f04400840c500d02c6940058030000144070080c502c043c0c444007010501507410b504001d1261181c0f0103444035500d41e048100000c00520000340001c0c001c0c0c40c00c2080c64028184182440e030386600040440105411100050b51600402400003004490070310030a60f40d13083c00da06914011030010300d00004e82c802c8a0422608404500138080c1c2804010006100007403016a80d00d0001005583c950010390b0310030ba140f04806001401c4441c1d44030b45034199500070010b40ca1501c0741d400700310103400d0740c04c601c400203118888000038902040250300d00910b555100d05959200509202d4101ca030289103170301c8070100d10070300c0000841012084132500861207100e242caa89501420b0720603030040d50030007609032140180c0d0305041c6030404094414454136010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 194969028 1250 194967778 194967791
    0x160221010617162108070818040e0303070e04020d020a020706080a140106030908130905012102210a0c0b04150e10120b090a0f18170a030b03100609 65
    0x40460341c441001d607089040b07201c428824028611300e01c494180ca004118183c0049012685450000d0b13800b1140c101e81c001d0300002c0b1103e0020100b02d9a10310311000f01c60800507040c69980382500ca100c0284450100445500040740382d030740c0ca030f0640340e80d01491142103460361101d07000a52798017500d02a4202090440c80010b0084041e4000c02c01002201040b480c0c1a910f400d00035005401000012a00b140c0140170300c18803800c032903503c40d00400040b503011034594980301c2c3d515013005905c440ba54698500a001d08050389903c40d01d110003d8000800b0601e119003850001d09225a01d10010f09400d818400011515804001340c000e03215441140c040100d8503032000d8031002c2079900540d82240c20209841d1485000f50b00750701c4440c01100700440c00d0014280054946a800c840710896566031301034610710488244903101040b80d1600c809405000700792a0400349081e103a280c41185a000104980042d120350015011410050215070412401000ca0000703440640a03140040b072400c80d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 194970278 1250 194969028 194969069
    0x117011202040e06130f0c03020909062e0b0904021c0227011e05040801110408120c100f18051005160f082203020a0c0f0b1602210106 59
    0x34111340607988002c2e445c800e0800c141d858201a0b4050501594165a42c3c04008090f0b02e8043c0340d2413140c1d07907100290140d13180403100c540303000900121382c0000384a41d80080780c0750121280400d040d1001007006503110000c80c40010040e206405080d90004a02d0250034005900d6401030a81c1442c1c01101c040845040d206004808155420042c001500340d00d0040c007110f80d81c0082d28030224140342c83e500d09521011024252798035400001e0b84160300180410003540b041c4003034108100a04112407400307100c204910b5032000041d0280f1300e003681c4c9a40300d1941002e550b100d0031101c1c0c80c0031083c900c2c502c82c41c2820b584482c00300800604842c18080016006810b4004503c4207000d0354036601109105c04204480b40c2c14010442002040501211107540490054060566100380d00a105120b424600030200035402d500100405034041c1042c8011505541a00e0305030000c0d000c8102c84400500006110070412000c2e602824140c20070400c0389031064120005490700441e5000f002034450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 194971528 1250 194970278 194970283
    0x110c0607030809061b030610030b040c0f0905060c0606150c010908030403030e06190207050c1c0c1406090d08070c0611070611030d05060307350118110117011202040e 73
    0x1417000c034000e07520820000319649862000880614801e140000d0405444c10104049400010b2103002040360642c80e00b0030140c1c801500d4000c0c0200740c0d103040c01c003500659215a200b4024110714402c0d0014041c0360128640710013500d05000e441d400034042c0100506001005070700039075040c1c4c002410480c501068450004040b4021030f0581c20780314164091f10021002500411070444503401100181400d40d940c0c0804c2081503898100718040d01c8403a4070b400b11581403542d00c1981e81802e00e0b500740d4000c0e40c2d0070068031303074a5030280c6a0a2010f074161500c0031147c4681e0800030910b4142840101d4820b500c4400389140c44403140c201c81d45961100c0d0150352004407490281e085600402c8420002d9525400c010f1300001c024040742c41d440d4940d6150440c80c81d140c1851111546000078440804005401071400507980700c0082041a400003c1c04014195030301010b4940e0584880315009640b0660b101d0002c06c0202410450650311081002a03d410a03201607101e103040c402019918a4003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 194972778 1250 194971528 194971561
    0x50103150504240e070e1207060507170a0201060501030c02070503120d090b09060601090905010513090c0b0d0e070b03240301060302040f0f0507090510110c060703080906 75
    0x100840c20103460300e04010072018000102e030540200c40300e910700c02840190b082c8903030054800034004030a689001c00005114400108071903100369142040e810f100c1e100030034504281c3e800c91408943c2e401d29400c0c44016203245515500c00002c0025800182e65410f50150301903036026030702840359089003502260340d0041409000d504d9046444208102111040103002040b000440840c1605580d2249210300c2030071226100d407500704408001141da0300140075000760201040400040d4101004584144480664019007941d208070080502030380703c0400c0e00a121100240e070b65921455240c0015003004460034506200d940c0d00800c0c00c86541003501e100304240c19920190080c05041030071898150b1845541655a502d8088050b032114021a000b000382600c0100b001c00c4815819011107400804540c104909410248405d41d60081d0802030858145480c0840d200600249414184203001983c1e00c002c0000d070303101c00c00d40c120200705d105003564015122541d50b00c103204101c7c50700c3c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 194974028 1250 194972778 194972801
    0x80303090d1206050d050a0b0c0a09060c02040615120e060601050717070203030f04030506060a06120b0f1807020613020d0204020304240b12010b0d060506130c0e0a050103 75
    0x10201206140d07100d0b0408601550203020046140d9035902e01203100c00c690501e098070340d80c022401034410300021502c600c0c0c0041c820001646081c617904001000d81c004c2e80915810802402c0c998030540d0396030b403c800080c1c025041d081101c440740c51400381c2401404a1450125130902412903001c80c070204c0d0b640d1040b80103841d1185020364654549801d421720000e03440d43e0440910104c409078404001414501d8042c1c01c580b80d0341c5041d42450b40c0381070b600410140c820354030300100340812644250007901c400142c04003c07541c50420000682d110082c1d0203200d0b000254141c0f06405000e4200c03881d4090310b000e809440543d15843e5203026903400d42103000e074000c050750704400010b0509a008580c444d000703114001010b120300d41e030401524001c032481c41106840320700c10005c52030500105410480c07450000c0010143c01c2011a18060445a02a040c031350b07180005a50398994410001905440c030301c04215a00701210043c204a0400078150f000d0040c031003020602c1e50003071041507010b64 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 194975278 1250 194974028 194974033
    0x15030209010608090f0d020a1103010c14030a1404050309040b0a0614070303020d150503060a020405011d0a05031212011203120f0e030d0608010c0507080d0e031209061008030309 78
    0x20b0806900303481180d000b500421503846442800c102139041440304200704885039000d000000090b0906900451207600b80a101340d1608001080b019004260b11640c0d400451403503440e81c0c0d80c44454030040c2403071035070201500c1c0888200300401901000034400c01e203003141c0400c100c036240f0041c8444020725001d034102003a00c002d41030203000f41e070f0b04c0600901482494058600501394070388109581001d401a40803a030001000d0110b4501880078550104203c170045083c107142200080c45ca41c5240c910450041030000e0071040340d12100d182c0400b428001d000c0ba168100c450314030344004d510038411300e84504180400460090000b6040201c01901983c50324460a81c4200d828000c0c61008401643c1c6959010607084095083c40540000700e20708070001081840c0c00e01150035500c40e0495031041000c10001a000100c0180686c0c0d9045100480002c440401c40b1072a45107101d144803e20b8070150500c20425410400159184201e06020b141400c0ca0740c3d49100541c0d902081c1c0f00c1c3c400d01d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 194976528 1250 194975278 194975281
    0x90e0a080d050c1e07020a06110307030513081204180b01080a05060a031e03030e07060906110a081201050f0316060e010207030210110d090e010501050703031b09060315030209 77
    0x6200d030700a01d4002030705118080ca80b03e0740741d44c690000340c1254101e25082030b01041120951070a010828002d000c2c60510f0441805070070131250301c0c0e1040e140010305020780810000c1d0380030100402a4040d114002c2207600301e002040f00c8262980042c4100b00040552020413802e0b1b070098041c508000c841a103030b0200589680c14034002801000b04042c0c0c0144101d03200002183c040c2403580d60390722524400c04c1900d03070542802810f58002600c00c14865118a0003042403030350110f24441101ca0038903103c0303036210003403c0c003c0c2001c0710721001400710807022880e0400300ca010261641240c00460307000162441981c207040e1280e464041c0c070080310f0f003400001c0201d00d0080d00100040601481565011626640021b07143c00d4110801d10000d505e19448203a2140e003001020b4481e141414803000d241c0c580841c03961205414003585040050100c0c1d050700b05400794000c500d40189900403a00d14100c0c0c01c0c40141824010710400001a0415014007180c0c14801449425070b41c001c0e2140032107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 194977778 1250 194976528 194976547
    0x602010b0307031e0501050a0b2806080702030409060305010b12010b090c0d2c070602032d1c0c02070b0915030606251101091503110c0304030309090e0a08 68
    0x10642c0000032205a12810401d0004101f840342d03910035084180d002035100c200700b040c010007000c801d102544441081e074000c2c072040e064980b40e1048502615144d5100d07a242c540486c10760050f54405a0740c42d003010b401000f04101904800c5110030240d40340080441c824520342d0a0300c06081040b5007200c042d1010500700d03d842030041401e07400310b15000c503110750b1024500c0146500700d015000300c0a0020400300c08400107101c01c80c01001644015070070701010104014015400c54030b0303080500b03040c07852415041d00c203a003030310050320418521000005041c420b210241207002640001030140210108600ba0164151a40000050700501d441c00c417441c0384425a601c080c0120b648084180420715011880c44600b50f42c0070740901200d44000c26603d41960004540540c480c1072002a2109200001001c0310b0f800c583c8400c1d2601007000000d168036500740388141e84c017480705800300080220906420090000031688400000c00042c860256241c0d183c03004008000e184c11010001a01da = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 194979028 1250 194977778 194977793
    0x5090601030b011e0e03160b1c11040b0d0b0303040803040e0c1308030d0b04050f071b0209070504050f040b0135010f0518100b0a12020c030301030c0602010b030703 72
    0xc4510181030401a442c0849482c00ea8120140c4c900000030b1140c40030a04d060405000350003005400e4405890b542d800e22018104500401c0c01007210094005c2c000b4004200e183c01a0001044a138011580c840d11507810101703903800603c00340d43c1242032030424925401c0002c03c407402c80e01781402641c00d00e030510300d0005645030003070141005842d0600c045809454440442d8001b061510021a41d03144aa4600015541007443c0e140c400c2c0e2614040100c260a11700800e944409507190410380d02c4052402207034180c4860344040c1d0401d500e0820419100e40280090064503000c03524504425190700070041540c0f4038041140c0003410078060300307503540c06200c1c41c1c48009181c98a950590702020a01c4025100243c0c440550f0650750007042019003051301408200c0c20a2024802c0c4500d003410f24030b110b0190303910403485a00300004401549d03074812048050211503454041d9a548040390703005649030000c1c00150b400d4000c54000103013090051241da400d10b50007402801e0a640785490701b10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 194980278 1250 194979028 194979041
    0x1303082809080f030a24140603071b0503130803041d060109030f0b04021005090a0509090c0406080a1e0302060a02031306020309061f05010207050f01020309030d0c1b0509060103 78
    0x84000500f800300c03d14940c50746018601c198406000064a0484250310b1030350f52002c00102d035a0148083d60030300075034408240010b030300e5406450550b92503c860404a41140071001052044640b1030f15500c01c000340880140b180c440749a1072070801c3d0747c5070600aa05c0740702c1c41c4242c0d2000740580e81902c5028121031981c2d640042c05040c2051101d54a403a414004032245408a0309100b0a078208000c51901c1c016220407041035280c40c03810301070f996020403407100079030048601c01d400c0d00d0009010540d04104899009070701030424060540c2d6103415584da0b03c29080212000d4807454400c0c0542c0054030b00c00310380180c25500420440d01c403000c10000941c40904070a04070450390000d2000b06032680002e40c0181c000318010542803078180300c0c0c0d1f04000300704c81c80d0240c2d0070b0503200100500d03a070025846013070b038004481e20041c1500e4170006034039510420044607018020749074914080d41c0c04c078015400340740c06000c84002840390103107031407403035a028020141e2154100001c1080c0b544641d0221 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 194981528 1250 194980278 194980283
    0x70302120a0b1203030f0106030c1422120818090402060d0e030706021b0d030c1d0604050307030c03030314160806191e05150f18091303082809 63
    0x2081240d283c074a03900e003194401c4030750030610310483c00100405071f4513203d8030700501018604082d5000c00100b10303001500c1100f8040002c000005000301202c900d401d08000184001e01001e016141d02d440c104c012a041120000900e0050281e41400c504024a009228a40c000e2078103150000044e5000300800461111080700c0c0710a021101c0066840e00c02092215043e0f10701c41c0c3c203402e0b01c1040b14501030b5164401420141405140100301d41c12003091050400b468100120480d1043e0201c0d006004951020354144103081d400410720003d0410032099900940c0c09003c0101060403a18010405682e40301c0117034032214580010034880e64615402c450000c04403440103545d079142000700f00142e040090300c5909069280c04100d08a0214001410240c4800b0707401c4448291801040c040d41c0300c200034881c40020703441d910881c200200c100c2c0c1800103120140703906000d4070012000031036080803000319200c0c3d808141003214419007805030495821188500822031341e0140b01511000608 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 194982778 1250 194981528 194981539
    0x2060706090b1503010b12071502030f0a09050306011d0609060126100927140d05031008010e07090e0304050d050303070807170a1e050f010e070302120a0b 68
    0x7040021600c039071060180582c02c40203810f6003001e038101802c50b620320b4402441a028450b0008050b440822a0012201d8520b001401d100161400380d04510616408043c08140024240304031134101a00006803802a000ca84103070fa2140300004041e5101d030009140c8171801400584286000300045910800c1850110003c95488180410b48440c080c0c0d004010019030040054030410020444010518000203000c4243ca00d40144c20700c0355500e0f171001607400300200b01d03424400d20084c054a40380700402103c541320515500104070782c20940e03101d48101c0c12170100240402050180e003176080401005412864a840c0d0381348011722104c0601c081a01040c4000182d566030760000c0d408460088015503900d260004004081603401010b10081c010b091104440c6800c1a03050345901c501c244c0c00c0040c01d511002141a00d084440486209180c204010444c403146c6c07600040b8100e50048000000c161186042607080c0e001b940340008000c010900010340e01e0015400020060501810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 194984028 1250 194982778 194982791
    0x308071506090e15060d0b040b0c13031b09020702181017010504060e0304030b0f0709030c0801411306060b0703020c01020106060503011e09020a0908070e011202060706 74
    0x2a8102a03d4110750182c81e1a0000d610141007019211103480c0d000ca4103c64200c203e506d65139521109410107032014000800f40070004a140e0018012200921401c11440c03003219980e00d45148582580c0380c00490340f280244c0300103518901c1d0b0080d505003d50041c00183d03040c01c05106030311034040003441e00d5000404040300085c0305000f58100040d91010000100b094582410070405441c919145010207500400c020800700b9803002c4c0c183c0d002550700c02040310365100c00b102200c1c004000e07040900000c141c100c00280304101548104d130440c004048908041c8801d054a0304861a03041c07020800d80000095504150640114554030036403440400c480301c0d14545480e001c544181c0c1008454400007c0e8103401c0c96010401481140c40034030080c4542418940028124001031190010080525800303040400003a0080030203000c80b40300440d101c0560103002002c824140c80790401c14054140d000c43e404102560280c140d1f000c43e403042c1c00e1000b5550901050f940030b2141510460381e640d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 194985278 1250 194984028 194984039
    0x608030405090c0a30050f040b0402060c010e0601090c0e01030e070603090f050d0c02150c070e0601030209030109080d0c02120a0f020f060f0103110d020904020f010e0a091d070308071506 82
    0x1054200c0c1e810004684060b605005d119030f4101c902c060121400940004200300000e0040410b9660083d41900d603140c0f50385d000d03885140544031042e05034000d40100c200100300e0807601d40c404607000502d580c61010289141d801076046035084503204e01c5540000000b804410b02a03040032800e28441c10a01d52030301c2561302d644d802c0080d0548241c0c005031010303003024190720b81b0141c40c0410044116650b40f070060300805943c0d4802051084501b003585c00800908982c4c06a41940c0110501a000348249d481614241c4903d92141d03000141c0307503103807a1904010038400034504079074402c02c0700f19503d02000e6074001d07141c440010780c2c0f160071480382d040c0c40c1810400a0200358000d40803480d0400c119411031034603003440d10309496818000c040c50100c02016a03194200103411a40540d43d00000002d82e00040b02c1e40b030001c030500e6801c12440e4000186000a940c0301600404030400c090a0050500075501d0311884244400381904405000003404103590408030b10b0b015182000000e21980d465 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 194986528 1250 194985278 194985317
    0x130302040b03030d0e06010608180a02040c12050a0b0907030606021203061f080a0f0b09070e0a050301060e0402040c020a0201020a060f1b020c040e06010b1e070204050f0a0608030405090c0a 83
    0x3005c000454101e80f00400c451a006100349403ca030224491302c020700b2542400d01d5883d210408081c1c400c03074482d51110340b8940140304094410a1260081c0140d1420344d04a0b0042c0003030140c503074041c00141c000500c10342c4c403a221f0074081d00d9299016280d803401080003c22240c002820155000504061155810344500864205550603450f140054038001d8521012902c1e85480380d003102d400d2a10044950342c4060300740741d01c0320190030003248082242000c03401c004820303000150190320b0302d080406ca003042c0030505032040b40b08440130301040031500070881c0c44401c44440240542e01044211000030a50b812115001030810b000003002c0100161200b030b01e1100039510009a00462100d034481c2c14036001e138101045880c4010465545040c0b20f50605208809400403c61a0b085100230b0f060015401c81d07510760b800038420f02032801d02c0c00c1c1c5030747c1c104420788003507159030f14104001426481c0031084d2001c645001b0802060b076510218000640c2d442203c480c0204a450501e01140c507405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 194987778 1250 194986528 194986541
    0x10603030c1203051e09120a0c1e02030601121401330506090402090103020c030d0b0307150503240d0b0106021203040f110d1e0314130302040b03030d 66
    0xc1e50711000ca0300114103201061400102c0c4240070981842c04104c01c0b403615010642c190814070750b40341600da484010301410606d00c9011040711404c001100194180c1c00046103c9050007100c03080a0020f807400996441c01e10400000c3d0940c200390700402008004002044490b03001d000040c0c48104502a62401c544075602e121100c50301c5a140d07240310070412000310325116030614600b002d4034140f00009585005400129104540006429945034400d0301030f165041440403c0701d4484a80500340070161000100040c040c1c03007000b40028400f8650880200070740b006489070380c0b45440311903107030100099003d124140940b80c40303d0510701791034241251601030300900d42c4454a504194000707007020011510321803008005e00600010c0b5404070180004140d00254081c070030300414010500d0014488e40c054160050340e800840300350341d090307001d40d036041c860750340c01c1000b0222107000c0300240502035080b100f00c4c030204824001800d0682c040c2550145c02002c0700e081044030040fa8060311381 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 194989028 1250 194987778 194987783
    0x9041e0804060e041419060906150e09070914220504060e0703050705041a060a050d0b0418060b0a09020a020703050105010e01060f0302030a0b0d050d020d110c13020903010603 77
    0xc0050108041075110a441c984010126800c4c42090b980305810241042c0241c055800c1818004540b4005040c1d64064801024240c0092100c103a94450300180c1801503a401e0010683c054103910152a0400345c03a44500820b0701c0e1944464240400e442e0681061190345412000343c244400082a00d1111040340c090119808102490946010700c15101c1c10485400384ea40b10380030030310015030045509401d07154151800110399400c1c109465070320488030800c0d500030780002401940c160f07101000300031640341c9807028014504044280401c481c0084078040074554a2500c60700011402d820004030564014620300d10140c07281c0028040307134000448400580c0c0b21450030001c0001c03e00509005015083c603c0400d90300d800d1018000715123070820710003019800800565140d542e64407003406080043c02c03a254210032440c00d25a070303441c460010f0003d8804c401114891911900c3c103088001c00c02c0e40038084031250301e42404252030580180101d0389800303100e503000075242403003000021030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 194990278 1250 194989028 194989043
    0x120a050a0b100507111f0206040c140604090207060b04020d0e0c04050c07081308030301030602030906090a0228120f020a0b07021f0c050109081305010201150509041e 73
    0x1041a92001128500500750340204600c000089006030030806031043d09070455062094041104c0000d501c000303009040f94818051600130240385070340000c050b41b06170710071582460255165070008081d44407540005902150421042c4400e80050f000b03810703028400c4002040380803241d80003c0681c4c201440c10711000c3d9480742210502103080001140100c400d6804210a040c44024814188a800000b6103a0700000a44851810050000c01c000340300000c1900e440e96140d140074800f940c02996062903520440d000715000e5070380401c3c1c0001450b8000c1840070941d03201d0700c1079480242070540000104850000c002403d408418200341c4942c412060320300482002c0c8104040309419801400030400b05100c81c0d40141c840448000e048454044d80751202001110304494200d445107005140c0c3d4240341c03030001001a0200500030440c0d280d240300403100c0e1070b680124221065100c200c3c4011080725000c000d9400d00000941d00140a0b1070301d40c0150b44185124030b000101e031b200c102c4920 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 194991528 1250 194990278 194990281
    0x50f010b01020c0103020913020c031303060c030515030c09090c04060306090c0605040e01050d15020a02060108011a0a090510031b050102060c070503031b09030a140d0801080706030b0402120a05 85
    0x1980e040c02154074080f004d003000c42c180102a0b01140000c000c03e54039162050380056423004950301001920403154112408111094580c68400e01400d05089444046410200421111000004500d0b02d10902600070680e0b0b40711001040000400903045012a02400f05140e000d91a1405444003660141001003841401c0c2d1a001e18658881c0d40080d04005e020301040c001580340841c610304440c0201e510209451050400704e02040204554240b07140c03000071800c503400c0e00854203a0484a801001300007604016421016150301c54500c1540011204814414020603601098001c1c400d028512001a1266034491410452211810401038910410006982d042250f40e1f4001e014a0001e41424040c0e50307069524007002c0c3c040d48001c6051901003060500c8070040d11031540001b8100c5003c0e4600303041c40b84195042401c411858010004070760b810303a00941d59075040320410030003003080a151034000c40091145e803801d40c0e0700980030010313011000c86a88030580614041c06000886 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 194992778 1250 194991528 194991551
    0x80f0a02270a09020405010816020c220501060f020c090907080a050610080307020d11030c1f02010b03010c1e020a060218030606120d0f0315080102070b0901020313120c050f01 77
    0x4860b41d40085035082c010031061055903807080e0125000071010f2055555014480003c6c1c2c1020b19041d14903400a07081d40c0089404d205290843d0f0100d100c070041004140d032a010100c854102c428041c2026a012a02c41c28050421032001c0d1790010f8120107444105840e901c04030704080021406482c10b40c00b08041c0b2031950313840c208030f000030003d110045103003805a901043c51000c1009001d08004551352503802592814402c14031221001803d162000300c1000d4034008503140d0b05010801076103041e4020941d400d0502c50b0720340760107260321a00350b48a05c003441c44022615600030308003140505100d550009940e0f00150950003420f10051030350a000071306144c9402e84c01480180320b07503440003881c8003d4502140a48950710079181c580003040382c1003c1a0301801040d14003a910070560700002a46480c190301034940c05109124094043d200c07400c1c05402d0307000c10307604240c01147c0c11407070100240d072100c2d95070100351490a21058402054030381d20704240c2c481d00c0d0001c059440f040f502c0b02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 194994028 1250 194992778 194992789
    0x3030c080a0e0601090e01021c0213060507020d12050705030307090e070e180a06080307080301030b01331b050609070b0708190c0f060b0f0405010501080f0a0227 71
    0x500a208100402c0040944041d15079a04018481c1003c0c035540c45800030021442034049401480964000c4207020801c41c020318025800030849044100c20640e010524130700c82c0341241c98158004000c02288031281d00c990f880000c00c3c0301ca030428401d00300602d03c00168140003a512480894a4005559141005030308040d04d0091801040090700c4200090b07a903900a00c065000040e444440e20565034182034400402030341d00480410303c00414444c0030041e000000714142c80c420007142c40c030341e665019078030050f01c00c520303090040c88000e62600207400da1313503190105580700c03a00e810580450f00c9501e841003002641d4056603540c000b60304007d031a034410030000d0003d100781d80750107291401f41e0729940b02c0344c0a0001030407403619980c18001c02d03441c03040c82115005c40c0c04c01072031300032a00c01d40b038904020035007800302a000d1200008400301c54039242c400d050480d04185c440340001c1d0750704004a001104010804c080180d401d010084010260030030644100441a54204540666404118 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 194995278 1250 194994028 194994031
    0x30c05060c060a0504020a1214011d030a0c1106070b0a14070c11030708010606090609050307030308010e040f0c060f0e092229161107061407060903030c08 68
    0x240a03080c104410904030034002501d6a00410b1980006025140c610019003044603aa014080017000d405c40725091000b4407100c200748640240007084140340c4a038112080e1414842149041e41040c4400a881e40c041d010401041d8450100545141030540c001001904503820aa40c240502c20801420041d01c0c461314040c0c0c40f0303100d2001924901803c000700302c48000310700244621000d00903605140c03410400380300034210b444000e110703071503c80c18020213000c40c0d80700d4000090100341002501c0d040c003203807030f03400c1e680c06548034401682020b1070341185d050050401c64885d01105213040c003040964100700040c0149985070b603000003003840020900b61440100c10b2151140c1000d101c0140c41c0142d2404550207000071840c1006164107001c000c04440911072100e04060040c070a444115041100c0e224410040054165048038282192112815822021a548076400a00c400d601585454010480d00080d0b507280000d1541c1c1e42c4140c9010107002c8020940350f00c00e00f4a56600144030300d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 194996528 1250 194995278 194995289
    0x218010806090115030603050a05062d07050a051b03030106120515010f02031201030501060510032d09050718060510020d120b03010903020c130e0c04020f090a0906030c 74
    0x800d5051907000200c10701010310803449080340c3c407040f602110b40a45c019200440e042416261541400e090140e03c4032021502120f1201c80643e40f20b00c01004550802810198441c0d2440c007030307544041c15180c80d4002158802800814056003e100c100c04524052141c2d0380000382d9282c2d454000040c00006002d8000e006807420402004011070224900c519421000d01c0d144100030304003c803e03070441c803841581554a0030080d0001c07040c81015001842280c0382901ca95002c1c8458200c1201141c81c20310071404198a2001040304080a14600c047c01840600000459540302d907141c1d440d08486900c104d800c4009404501070840b001d200c5e9200421080e13a00a541c00c081c40f000944446220100800344010100060440c0c49942e001e00f02502c03014000b040510390030304000e07644d0500100742e28400c1000760a074052000080c010001004140c2008200c04050700c0104001380d00b00f182100f10a010602000b88641d0f41c410351603006241c2420001211401c41c00d04075107070402500719 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 194997778 1250 194996528 194996537
    0xa150215010501260601171006020607030504020f04200423030c060301060f0302070b0708040b1014060715060f1d0403050a0302030907050301050916090603051507170a021801 77
    0x1300001d00d8900f0844804c0d410304458200010380c2c90800580309000c02d5002008508902e0041241e084881d444940941e8040c0e000c403002035460340340407401d0326401c0703e00942048122103250034a05098000c2400148018004881503504c2148880240c00580c0244088201000511183c4540204a1803115010340c09000c01c42d400c0f00200b040c502c03041c4180e108000c024a28210007030f100f0f9040c0c4101d168400d091307800702e040980300148403210903a0240c461074110000708151400d200c802da8100d6481002a0b04081a150100403044d000000d0640301500401c081c22440781c541c1c485c2c00d000e072003260221950039003000c80408241c640c0d904651000c810050902c800f1913008000d071400380d0b0302894096905d640d501043c41c24001554071043c0c0642c00d1a05002c11500042800f460f081085050188459518bd8141c0183c071954440038100c1c0d040480030415a030092042c10f40d200041d42810701c030310070f06079086541c8010111200e00445a0102c0c524810728001464090300b66402d103031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 194999028 1250 194997778 194997797
    0x3091a010522060308070c1401080f01060c0302160312020f030708030a020d0f0606081803130306020304050f1c0f0e090106051809100504151203030207020a150215010501 75
    0x1082d14140c1c402c0e02c240603004102c2904095142c9500548080d40d845503525898001c00e180803000070085000364010004110710070a010351190451300d00c00c108584606000c0c0e407130306078203480708003045006500710701030948107a011149500780d1400441c464160040c03000c04609000341400d001c00e0800440d07800400c010000308000348280c83d002900341100683d0f80265149002c000e00e0300202080c81c0b1410544002001c940001c1c8091203645111420b07500750a041d00d0181d140c1c842d603201c42c800e4403a0510113001080315940079650082c412021109065034003841c89140451040b58444420f89004071804803e600610000003281a42000306040c1c01490000b200420140130f40c0c02000004240c0c6c0d61080c01500316481c2c4450094084c07001d40c103041d03a0070344005001d809494020b50510312045602c9a2900700b140850f002c2c5802072407900b04e84d5408070081c0d80944000c2e1f034410103116002c61407480d62607020302c200c040c64000b00300d10501004043c2c980d2038164000c9052124425 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 195000278 1250 194999028 194999039
    0x15051201050918100f0605010e1c111804020102010b09041208090709020406181a07060e031308010c0305060109050d0201051c05090304080f2a0a0302030d03091a01 72
    0x911903055500403500380e9000d9440d030400480060300040400d01600c03c0b43c09107003c82c1000d03405440e01003001c07001803041039255001554a401420001b64100d119206021408003840701541080b910a1400c1850390760386800080303240c040c110004c6060040e43c014001150303024883d20102c80e409541410321880d290325045641c41e16200c44005000b1450001542c0390340038050100607160b0080215144c0e611490020a0022030f94000c0d0035a210540020441007041072021028101d8421800d1400902c3c0d9254401b6000120742e900b010b04c170074048031100300e00d2040c4102c0606070741000000d0f0b5141d04031005094031070240c21981400000f07001031006403141c0b8040f01c3d0464082c01c2c0699180116014460f017035010110112582e450101071140000700440144111a201d00860b40340c0c88015003142c0d04c5500c0c04060041080c045d018409041c3e01180c4007440001e80200020100c0b0f6590300824204004007118600003039681002e8800c020074020400000703c40390700d1018480d13043c503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 195001528 1250 195000278 195000307
    0x709060e010b04090e0c04150e060a0806010b070302030d05041a1e07031a0a03080715020a0504140301020d0603080c1e0a0b040f050d09030b0c03091e070e0405071505 73
    0x4d0042c04101521080040b50182c0100103c0d01e100c40d01400401c186003482d4000009607810f8060403d4110280001c9111840c000420750103549010300a00160303460011100407650001204170158042480240c0811030f030780c82100d1003540a48002000c16015103480300c400d00d0002e0110150302525000501c90000c02c0071f81c240d05c4016800d00080540000c0310020440401d4000150f1121640b24080100302044014008062182c102910b8148490000ca000da02500c6640c000080040c001040101030b4009028203c01020700010324204d0380c03201090560310709400c00d03200310000241c841c101510410583c6030f051500398000503505102e50a9984800492001400707900780c0c1004241031109030451000200c0d4868100d03511468400c10140001140d440203640550b10240021040034440c0110791044802c0e401910a081740d1061102541000000c103110a20a1a1011441c4041c429913540111300481c005d01c180e5140c980f45982d070000f0b00c9440000c10406200241010980 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 195002778 1250 195001528 195001537
    0x4090c0314070e010c061104031b0e0c03130501020c16050406060206040f051c030902090105011403040605070e03010f0605090901110f0f0f0d0207020a1e030605130203030c0709060e010b 82
    0x40c0c2c50000010f0050400480d20720052400146c4010b252088400030544440c001740126482403510054500324858090040100c5104001c0b0041e1841c0001e5803001c0c14800569120044400000030756034a6100d507401ca03000080e00d0810b5902804000c0a5210130380200001080120b40070b120680c03c200000f03440c0c06000d007000b4031030400b407845041000000d0090180548081c0001035012036202d40060181001c210306a01541c8204000300326940720b1659400b00c1480e0070300d06865a146d5039169002014020b00003001c10241c3d014440541d5000c1c090752481c121407440c04500142480c040082081d0301411800b81a858003500402080d01314058400398103404541035240c031410310038400c562140c07410241c240325000541e00055040307030f406801d03064025240841c1d10394694000c0107d0640304151202107115240d01000000c0302a08141d9000d500c1003910780c00c10200c2c0d4040381c9103401c030902801081e0402c0d0814000c2d9243c0d40b0070000100740761046c00003a5454090100c000d44079 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 195004028 1250 195002778 195002791
    0x608100f0b1206030a0f0308010e0906040b040201080405070e070c05060f090c0616051609140103021c05010902030d020d140306060f0304030507020909011a03030c03031614030a0204090c0314 84
    0x14100c000411907074085c8050000305800540c001401180ca01d8000d00860302401410100c20340c00c804104541000a1414865a8080d40a990546460b0010340d90100e004000311158030903040c0200c0c000c3c00042c100c9004000c291a408684481c510b000350602000a050071207502030202002180d000000d2004140c03078040e600c00d6504c4c020381c1c210b21010780701c2c0c0b0f0780945a132203080b060341e182d032101441d00012035146010800000e500050701144141d020312010303500411800b44080d1440541c200c200007107118100003d0344c43d615502090404c400c0c009944056001a00200680c0b40c0050201d0002051995010f24500d0300c2070024606000b01030080d44045400700c00602050b000300704035052542c008294000c545002c401e118041c00880401350944d80b0909100d800a06002042d500c84905041c091801c50303650010b04a90040f80e107020f2010090030020360100c0c3c003117035801980108500840075903500c0c20400c1c101c00380c8124222a1081601d0300241103400d0288a200707a42014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 195005278 1250 195004028 195004057
    0x1050702010c05010608030307030b0603040f031202160602090f010207030f32010b0114070807020d050c0d05070f0b070203060414070b0d0b101115040213060608100f0b 74
    0x11580d0004030380310222480001c1042d86000350200b05818000b01461040300c01790307402d01252500b2002d10001d804292002428401075020a00000340600c201d0355041364010001402e01440e041c01020403003200707005480301603000540059070b0401040c90382c28240c0c01e000500382c07149540c1e20040c9040d0f143e0005000128400d100c1d8204000807014000740d071030000c0041c400c0c6403a1031072041c000c000b07140d401404200101d540a24008161003500c07581038002c18002d08148068080c05070921280e0300c216441d001d11151080d40f40c0c0e52810401c0494051001482910b0529401200c04a01030700300c06010442807211000507540020401c0c0d0099001c007151f600b80240d10184c62806103642c115982c0f406021524025140540c2c2c010380e02d0820440701c9039859034203143c00ba43d00454441c520f9546400c64513405da1074003400065181c000e4400f410500c0b901030940c4150046034a2600540c00180080040c0a40250290001c0d405000900184145c2619050400e440d07481250a0b500d90310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 195006528 1250 195005278 195005287
    0x20406031415070905010e0f042304120c0807060c110709090c09050112080f042303060a0b03071e0e040602042108070627140c01020a050c0105 63
    0x151115049040155803100781c001512000c0040151521441501c1250800c0714500050100748141e043c04200c0324183c5400c424076030800e0a0045094400152580003625407140102c8041c0c41100da00a145800c0c072030400300c2c14586010b5190390708800248007005005114400494807000844101562003d00020703841c02990081d1806800120310141c80d00808a000030308020303640002e0407541c864016807088548521113801101c03028052002000001d6103090002902c890007000d0945031000254240359481000e001011000c140300f444555055481a100b41000c1101d50380003805008103001020320304002c45d50ba58400d2080404010070441c88207251542189160041d22180000c5240c40c0307458104000654400d100e00d4130301040100b405410ba001a00c84001d91a5100840c43d16201058403101c0c0600409041020000c8080c9000d154880c10300c0020b600c0148503240141c290a07099051905201c10b000c0c2d124155080401310b200002d4005c174a00100141c2400c015444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 195007778 1250 195006528 195006533
    0xb0711010b15030604060e0c07081c060f06031109090c09010c050f03070507060906080a11040503030a090603110c100504060b060703020a12031415060f041e0e010302060f07 76
    0x1410280d400e45401c518900180d030410b00004005620071182994180300b03456846011b6200501c01b15410380701294148500f0000410440c001e0180e0f28246ca54139984601c040070045c1181d01aa001c0300e0401280001044596010f00480004010b40601a03042504039004074800000050a0b803030408400142e041c4207a0141400d281900d4205040303841001d03001008944c0c82d1b00000301940d15101781704002854520801c20801a030b00c542c1d0f00c0b4002074941043c414042e007031020070f46a40510920000c24151030410160100b80102c0d581c2d040a14034010000d0110303003980c0b038100061141081a0030561900088640042e248101e00107515076440c24058001d00e41c0d0401c00f5032040c40001c1c207005050b400500001c025008460b2100b402500903402e07130440e00031442d43e40c003008010b000910000341b41c41c0c8a01441c10702510740c52403c0d03040e4406442650081e0000301081c014076a8044841582c15024000351403410003030400c55041da00043d4403030041d00c0215a60000000f81c0307208 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 195009028 1250 195007778 195007781
    0x6020408030a08090c0604031208060f060a180503280f020a18061d040b2502030406110106050f06030411040501090203070e0406150f021203090c011107030b071101 72
    0x14044001941c0e26099140c0d002094039106a48489443c032172081903001074a410000c42d403c8130b0f40004a940110708a450039070300c4060080c050340d031112011444440c2e03900e0358401860300c40d07540c2d56145603018030382c284039048140507044107006e0f0f4484023400c010108a40018941d1100300c1403c1c2d0005c0b01e4501d080190090a2400250080350f95580060424010b4041c034880e030341e9440083c032206440300d82c2d1a00c03011076840c11030b5000c0d5000021901080c044c80003503070030950140860b009840d280000f61b00c415102c0409100690001800304003080d0b110800c0702c0304104143c020702400b840d2000240c2c00503400c0d29041d2107011b000000c1020444490b1020000c0701d80500f05108a40c3d44800c408020b41040b01e9240200d000100d00000380d14092180c003064a001104404182056010456120159400304015403107888144003840c0240d501441c030807041180140500a01d40340018280c0303114041c040c0880d840908141f00040c026859954000800d18022410240341c0c2c0c034050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 195010278 1250 195009028 195009037
    0xc0f01031a030a060207020a140a141f020303011a1215120f0109021309020307030303020a032a0906050307080f040201030621060501051009050f1f05030609010f051c0602 75
    0x80c2e00d4400d088000d4200314280c1c014145032802120740080407a076030031000300c020388030301d051590218142000380842c0d22040c42d0007500d180007501d114003a0134105409030030742003501c410030003590000c00104a2800020488048000c0c0c914509091440d426000010b0f29009401090300c00e05140c8200c83c00d4880c2140000301c108034004a9080c10b0346503885600070302d207103081a4060076402e091003100020500485080f994042e00908032180317140c908500a40102c2682000c164440301c82c01d500c83d0000c081c1280a0a9268400034415080ba002500311000d030380c442e0091103400d04c200182160003032955680080c0c0c01d01c916500b035a0f1480100e005112903086061b0110b5604403001e9100e40c108070301044140b06403810403040c2d89610030441c0111450068000203907844a0034003503400c100c05190301550016204070000401072a12107000441c150404c0c0026101000700507192801d880010b006280d40764085c4a99800c201c08607000200d00008001022a000d40c08020044682d0454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 195011528 1250 195010278 195010331
    0x30090102160905071205150409170d060f170304030b04030c02100e15090d080904110c102301030206090a0b030907051806010207050904061506050316020c0f0103 71
    0x1200e0054480b540000103000a9940c1000100c4001c04d006044820340724140c00303101004005010042e03542c0402010302403081c400c50700d02103030008c403014840540c0d01901007003910a001207403d50030102482c440c0c1c6030310b90103000f04c03021903520460640400710440f0141c0350090700e03007c80390740c0b2401c042c0e41118014000039003255034481032807841548404c0d40700840e141169540380e00720301c40c0d8482d01c0368000c0c49103203580050404075007070000c0c185134003c118132030307000d40081500d003204003503051540c000394038216480e00401c6d226000d200203481024900c50311810f800c0c2d00042c0c0c0c2403282424031414000240075000004000c402c0d6503071710201200600c01100300642e80c0c0750604003a80c880025204031801103010401088030081c03030700110707441204107078000c2000910b0300382000b0704260040d0058035840d0340c031140700400c0001e41e60000054011521a182e076070800303481c05540c51310070080700411904024080c4000e95140c11001a41c44001d103008980c7c150b0714062613401e00d0010000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 195012778 1250 195011528 195011563
    0x40f1109150103051006051b1006030303060e010605030103051c0507050609010c1106040b060f010903060204060e090f07020a0201110705041508160e060d0602090d06060830090102 79
    0x8004429561000c01011000c0a980c10300645d120340c3c0c15104601120700a00e000300703c040c8600b41003828000c01c042030a109120484030000b5480380c140081702d0940d00240c2c00680c032102c090001081c403040050040c18280b0345039140d9855511a01d80382d04800907110144100c000c00c00d80c9451040f415035000c280c000c415118941800e2035118024040052480c1c0820310400c09409203d5004c81c1081c401c82d04010407001da590795030100f15800c5640c100c1c0d0b078184503480b00c0200200d8031a101a001401060b111720b503506045808010754180010720001a013200101084681940454012051369081c20320780b10030b96074440b074542403402540100d03402602d04011210203c00700c1a904085600e0102691410b886c0d0f0200c0c1c071800e000c98014000ea10140c031010604074103151030301c0001c0c0c501508005003800802d0000516014603090103844054071400e0901c600c0c2c0051100001d0380d110f4000309d0030344144040e0b07162400700441d035503001c60150100d52203100d64001d000c49209a201080c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 195014028 1250 195012778 195012781
    0x70e1005041e09180302070506120612030408030d02030f061e0d030e13020d05071106150103060e0a05040201110c030709020c03042c0a05010f12060b09012c0f040f1109 74
    0x3040e40c0113402c0070940040c4520400040c0504065040b03a0540c3d1046000c040c0c00d0760341d0b1040c080e55504141c0b0040a40c0700411000a550385d040c03018040c462910340c400b50341d03410f004507030403006070014100e1032090030040c0c0c20340e96404000700c1503402a1000d440b00030511189040c103136045030030340b0805038104004114288486c90035500a0050182100b8108083d880f809002c032a03150881c82c0001c0f8543c0080007048160210040c2c0340042030052401241c03181d200c14400c00e004400340c0e09006c000b9207034800c0c00b04544c2c00c030742482c0c40d025034240200f411845e40742c006580c540051042d120f406a000424064540c3c0910444018040c108102c0041100005103074040d515040704140c40f005030f0070080b13407030707000180590341c125060a40707003218003410503200030590b100d42c070f00c00c0b0f40d55075907030014146588541030308030300800d800e2200c0e44000c0030b15044410802e000340c42035510606400100080302c03200003680c58100303400c252200d1511201d40b810f1441c031684000c0ca10b500541800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 195015278 1250 195014028 195014051
    0x19110d0603030305010f0b0406080901020c01090c080f1605100905100207180911011119030207260a08070c180b0f010309050a06051b03010905070e1005041e09 70
    0xc1140040303030b2281c0d030100505c0c0c0c1d850707000c070015240501404110b068208030400200c0d110340c1003ea0000c0242000510700784c00e5441c058215600d41c241100c1c400002c01042058880070705c200c10146030b840d00a0442c101c80c0c44004040e1210500419219100d00f0006580c41031003007102c0e0000c1c10000d0480d141e1500400006507880307100b8410f0750100c500382c0020001c2442e06005900c0001c0e031284c4400100042000103507081204048080d40c0f510074103041d110742c8203002c91800940c50290300508017890601d00d0000b00100101d089495040f1382400260288400084001ca9079400000142e100d80341e43c03515641c8004030358020300010300e214050226122081e4001190b904003211116013400f101001501500d21076000500709801800306040480d607160000340c5e118401ca944080a02068003094607c1c0d0400c3c0c000406440d503c0003004881c540007500c5880e50042190141002c004d00d540043c554400c1c1c1c000d11003016042044641031180b1781d50810702a11002c0d070140100d0038001d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 195016528 1250 195015278 195015281
    0x6030c0e0a03050c040c0f08040b070309050303070c050c010e1e01140406030501050406120308070e0f0a0b13080a080307050a02030f0c010906050105010f090308030603190b1803030f19110d 83
    0x81c0c4c41c244a240350010810b28940140d1042c48410000c0d190021165a562110164070030700900700d0040c56110000000001d03400d05c02103101b51010b48684001348058103000786008038019010307041c800e110303c503140d440d0703030300d0702c7e80c405140301080c8070700d50b50140600407911a9030b0b0012002c40c1e6140841d0200701d035070301a000207042e2a8159010041e490303a0b4012200c0c580128074024002c55440c0000c108094401c1c0c03421121010041d1049824003660400b0440361901944110704882000c14920380c81c03000980400014100030380100500c0019844000c141c0c400902513005001000075000308641c000c0c01510a0011840180364850a039a04998043c010904084503407a152900125039580681040b101c0903041e6942c518040c1c2c150b13603c500b803d900242030941d143c81a40c58241042c4600c022240c0d80c14401e0040039000c1c20700340c0f005038894100450600140c1c00c10b2081002e504001450240e01480d04044242003405001c0050700038450301c00b809259031000144140707400161f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 195017778 1250 195016528 195016543
    0x9010b0d2412030e010810090c0e03070f0302120105070f260c07021011031b01020903010c050c06070201090803160c0203120c07080c100c021914010f020606010906030c0e0a0305 78
    0x2e4481c0e400e20000c070001161409007c030b8402c000c4000800301070103462151303071000a884416040141d06240202e0000f40b030310005600c240301d02d007039010003070046040c015510600074000d00001e2049003003c05d03002e0711080d484207050042100d5009841d8040c40c0e04404003000030303038404c80340c48641030008051310b855110000581c01800090510101c1c0781c0b24a910f0711550706442e01a50800100e0b2114a00384200550000d60b01c0d07409101c55025903800303209010241810380c488581e81c107003010015080000041000c1c01b564580041d81000c11840c1d4201c0c0c1c0c0c800708075142c200d44241c000009a42c0143c10081c0a5010300c600010300401a50740b00051042e10406800c0f00e5100b951500032661310600c140c0c40c1038110000c0901406140d010b2226100d401d440140344003044100c40004121282255109261a01c410b1080c0201560030038079810181030740d03201030070b468600907001908492252103480300309692200c40121061185500c030840b800010001c00c04280c0e00e0030070543d0b6248 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 195019028 1250 195017778 195017783
    0x807090b0102060f04080c070308030a090201031d0a0b0a0906020304120e03012f040b07050705090109020322080f18100c0201140901020a020d05030307090509010b0d2412 75
    0x544035480c480ca40c000109684030703880d2000f00310950307507456940320304075004050301408038455054044001148400a0b51050b29400c0000412030380b02c0c00010149d403c1c1911880010345010014201c06501050003164590812007018040c2c583c14003003802024164000f4200170700c044180b004100010040c401e10051540d03c2c61140c0484004250072214440c1c41c0c0c240070316903500c4001c5000460051400610b280403c11400d241c2d4854480e00740b94402c940c11240da800210060015141c00c62641c1e001d00300551045085240080d1140d0995030300c2090311000764030000002c810400c00b801200e090a029180483c0c4a400041081e107807200e080c1802c41c400d040c07081c2400c1500384207500c225a816016541d0000d0720110b54040d442c1644130f400301030304500501d071900c2c0161b180d0350360641d1002d101d140215640c0c17030302501c010408101740d08010b02c0317080801d0042180e040b00d101642e2101107094000a0000c01086240d21001000c11600c01c4a1041d80000108000710f043c1d003190a50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 195020278 1250 195019028 195019031
    0x120c0f0b01080c0108010902160b0a0204080d11100b0607020f040605060f09090c070302341d09070609050411130e0108060c091c0302031614010c1409040c18080709 72
    0x9072540451f80690090001c8204a40c140322200008110205660398200c0d403400e400525280c0c03181c40d918140907401c0c604802148084180140f4038404000c3c03407c44428407a01000304440034070009110384039402d400b1303200354000c42807a291aa52641300d01c005100081c400c2d0b035200100100e2a5242c0c1111400f984505030700c200045019044070100c546481d40741d400303407111615000c00e80b000000560001016072001d58602018070300c1c5203441101400c078444030011000444807080c03001000c01088606113421980040100c41d40001c02c41c0150381c01143d010490b901310528140c513078040c0d07020492001c2e82400000881c0d0350030511340d606031485402925903541d2180c103104018400c44070080c1e003002d00611255041480e01c4400403c840c03091050f62b00d8100c5020306424002254070060310b85400401c000780481800744200d969182007424103002e4016a9203288404c0d026610320140566103400e14440003512552118502141d154000d1402545846005554400c0d41c0105104203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 195021528 1250 195020278 195020281
    0x1c11010e0f1b030703170421110409151d0a11100c030516060605090a0501050a050f03030f09040624021612380f01090504120c0f0b01080c0108 63
    0x401140882404454001d80100300b0f0070b2070340e960325202c0c1c5406031001040400c141f0020035074015a1250032405130090b01104440c0c4418100407440f90740207141c0c03d126038a40045140002c0140141e01000c82c41c800002030001c004d40040c540b0142d810740d80401a010308400c51040168a0039985001d150a49602c00c007012100350948080000f2070002c0e020402c14844514010459a1a03500c042c2c0300d0400460300700e03990000700e40c64100c00d8619003119030329000180401c3c108a03504800420080710404c6032601014080b9440b403040303200068006000043c03450b40e43d12150080d0004082140c800c5108030301d455100004019200720348030042c09040c00030707845442072210768030682e504440910701324091940d0716805002041400300c0c6102c6001d01006205887c0c0c48110036000d40c1c5024001c4501c0c00900e10802c1d680c0c140c02c0b1448007840e00b0180720204101481ca00a80041400c0104040e04c03103013443c0c240c00441107401408100e40c0c40010840020100306511010000e03214228507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 195022778 1250 195021528 195021553
    0x2120106051203030a0f05010803040909080d060b0309010e01020306060d02180a17010c050414060307020703060f1e05102106050a02040816061d150c0309011106091c11010e0f 77
    0x6847d001c0c8541c1002c0c0c3c1c41848107100b41c017180e07070210000ca88260140e03850000218811402c0e42c607194805140001e0103c1000341904080c0100001081c400e8001c62940c9062000070b031403405a8001001441c0e400300b40350f5120009290901802200201600c2940e640c80e0815101c480720200421659402c01d040c801425008105840c02d6407408180200000b00800611880b50002081482184034440e000404a49144075040c4964141480030602142140341c100c410000e20170480300c240d181c02e017084034034542c00c00114166040d00080044200300c0340740c03a0724100248040038100074a0301041c400e82a600da80104100c0754014107888042819050360313103404845104034004a41030a00c480844004013011240f05a001071103844400c0080c0544500764002400c029034aa10019000301c096030090b60410154a1510040c840b40c0341030140d0350b44030000300c110f40d00485011840100c8040c040d4940b50b0075a074402e002040701100d41c10b940303561030080300d0f0404028040c4141542c0f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 195024028 1250 195022778 195022781
    0xf0304020a1403060606030a02131806060527031509010b040b2e030e01090b0f0c030c070b04060209030303130b1609050d1e0501020901091d0402120106051203030a0f 73
    0x304244000c0113084a5a145814001035034001802c0d140001d80c20041a4244001038000d02c1c0a03007801c0002c280f0140141c1501400c94460b81c0041003801020701030705400e881c1c03a01e010140303010707810281c510ba1142500480e1a100052408590780c52141382000200c000540c0107488840c0102d0f800c5c029449040c00b40700d80201d0b14010036020100004048000000080c0182c45030b0529244c000f800001c06140d40e400c4500d140340031280c600b884802d0100805003444c0303036900000c40c00f10040ca1802d00d840b5903016442034040040407868100c0024007480055410340d080014081d0549a59180c42d052803a2051032a0008554410300c51010a00716030800b500964070b41000d483c0e1100c05d0703007400304214000c6190307181195001c804801c98008003000e0f210010f5104d102e00000344c0caa01c1c0da04009410359000380c000004204400c0b440d401c840322650616500542c0541d00407180013202100c1d107000d4074813a04021b40164401d44001c1140c04000011071290030032040c100b2100800400480 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 195025278 1250 195024028 195024059
    0x9051f060e0d0219030317011e0e04080403081207201509031b15090c0f0d150501081005060306040b010501180f090e010e0606091308070203030f0304020a 68
    0x800040188500385500e042190801250500007002883c3c44d8216200480c2441e900b030704203c1c0000d0724034540700c904e511821881c50160640610004c84c0040c01c04440b48040300d9446a880341d41c12800c04078043c0500b41041714017450f081614196610400c2d5405460380d131041e5a92000254903079001c6981c04002c0c003903200341c1504e6801500c5210208074440c4450300024082450074041084041032a103034003904400000134000191400144690801001d080c0050410160f600b00c440000d4503036840c601e20b88002101200c0e000d95035011414400002c0c100c07c00100e40351403a240c008103902d00005010701d4242c030705610a11103959807005046c0c42d080d080d00d000f4050359124005000c00d600940714104c0301000800d080c0c0b14143d4403481344100850300e0340040303c015a9404001e005c880280198400c20403000000d154a04041d000b1880111000b882410203107407401203241080041c000b181c080a4004044940b1001006511252a44240c03000c82c828402000d00180384c100290440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 195026528 1250 195025278 195025289
    0x121115030c0a05040510020106061707120c02160b03160903150b15070c031e03081b0408060c090f0d0302030906090607140a0c0b0405060304020609060705060109051f 73
    0x581540c44080c40014142c00c031030381e0002844400d000109403501c910341081d4581c43c0c01d41c000300e481403402c00050100110181400c1404000c0800c001030140c111170005101c1440312800500c40c1c4491900300d081c10030816007420740e1004080005a81c4010a02441c0140c0100010b0b0062013804401641c6540c1e480c4001407000021207540b0849110aa000c10080c000142034041100c2c81200704030039913403002004440c091000c100c28018420740101e082510304603146503828150807501c0240010714014121a44d0040314910702c1254118401a90004c1901c8400c60300c1d94240024401d000c1e4024902580c001ca030840640c80c52403400403419503080350136801552030501031109100701a4422a09250041800c10241f00040c80340940c0040903034000c40500b000c142503161a440c010352940c8010710301a0700340014851955141e00b260703007095040b40c03d90b5440c0540b00103d100c0780902c84002d03040703004d46000000c451603250807841c82003032aa1182c580000b54002641c84209050085 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 195027778 1250 195026528 195026569
    0x3070507030b0702190606080111362d04020f0406050711180f06010206162015040501060902030c0a050309011b030b0109050a080604030807181211 65
    0x7040410320303100800350868168816989500c040c0f4440d81801e240102c0704480550f50b0f0401040038490a01c1030303140e10707243c501c4154a0315185484840d10b030301401d40384a15510000c104030751000f03203400254220390b4006c0c000d0320000c10451840c5a10303807115408289900c5d03010b0305900071403405200300e0382c80c204950401400c280c28443d0455650b0000c500445102d9401003008206544c0c2e007071008810040e9852500041c60301101996030f542000c0c00941c103550024051201441e01209002c08503802454044584030070321030220a0020005407001d49401161401d002d900d4003001ca03e4071450082000740402561003024108910048449115a43c3d003484040d0200f48584011908965401c001050003100740690a440341180c01024010960b98801e80c44556003151440000303080888441203070381d14143e559516200c0c000e200604015010300052502c034014600c40001152800b03141c8406a1078191402c00b521081c030090307902c1510300100b2401c510704400c080c3c2030328600220 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 195029028 1250 195027778 195027793
    0x10020d060e07081f05150913060320031c030b0909070f2102130507031805030904020703020a0b1003020909010e0a120207080124050a0303020c01051e0a02011d030705 73
    0x2000100d02212805500e0409801c200018959440640b0b0001b0300b403801480946d0f4800c2036003004100b41641c0b0003640701d24201502003020504a00043e03c20300b20b6901e05c01e080c400b140001a08200805510b040c41c40c1c0394044204060f0791560110b0500074058a0402c040c2e15414085a0748244074480d0401c0400c0030749042c003110750b01c540b082d50484c0394401030140b9200d8550000e03495070a80707c27000d03414998910402a0310780e0f05025460841012821212800d070441d10f56076242e05c1381c00d5556001d40d40008000041620820801c0030150b00b1840610040c14004451100343d00c2034070003a031040780c203080400e0021300b040c45a003100e030207030b180204201141582c91103107040d03034092034a055004054000480503002e0162400b02e4550820450000c440109000c1c5284051b810490040705202814030020b034000a4901c04610b090901c00d403103400640ca0542003084d8031041040c25803020500c2841c858054012021000b405e200c89403184840f004250340c0c074080c5000240c1144d00192 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 195030278 1250 195029028 195029041
    0x30c0c040c12050f0a0506060f0f070305070804150e04020c0a1403040906181a030303071404030213020703020105071107091113031a01092c0f10020d060e0708 70
    0x30320040410031035003400d4608000c0740300070500b101c1d82169a2440c02041c1d400b004001e0940e88100381d81710008644050801c0707080c00c00800c0901071001c2b080070480b40002c003a010726018805950301c26600c080495038454940180c103102548201c4014041044200525500c3c41c2900a031401c074400c2030003c2c5860482604d07411038500005040d1a0280020000816191020302582c80035043e618904007202000f1100c48044a4291a02c0076291456540c030200d03d40e00071080301d4124960f03141c800120b1382c00742c503400001d1055500c001d60021151f01144070101c1d4a402520215020380c00802540c0d6441105803190074403a9141903030b0790006201403158551984c0040848925003040c0c40c10161650101400340205030020780c0c000442206500c2d400c6120f0300d1690140800140901007000c482e01e40044400a541071072220310b030340d0360501c5d640c0d2404114041281c030b881000c540c1b00b08583c0080c04003e40c80000c9120501e800c0101c0482c0407412401254002c541d10380d5800f100b075460700e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 195031528 1250 195030278 195030281
    0xd11131503180618050601082103070e0d0c05041b08060316061407051213090b01020a06090f0f11040c0c050607030c09080303010f0f0905040213020a051b070512030c0c04 75
    0x20241340c0302c841411400c2c0700100700204551030291514030001c1594650003126240d00313542c694402038916401b0420004043d034004000c803107907078043d00d0820340346c5d40e1031404058509850b04400c1d0043d141112000c50580d0284158090300341c1a12800425164142030544900c0c40010350003d402100b01e0400429100700c4404084035080080503003803841a681302070600c21015035002c02e504012a00707015007038850102000800a01001b000301120300c20001c0c0d181e485001029100d00c0c2e84007820b0040c8403035040e034440445e610100500c0c00030118503004c0308030079074011042c3c06585841c950340810ba00481200c2c00c43c5400c60001d1803143e4480c4000c0b000f8002400d440020003400c00720014101c02c00704040e41c06400044120000740c2e0030601d18030200d2000760b0140d4021030404040c08051b8448010720200900100400b40c0d072883c440100f031b90079100d00581d040028a161454400303494000c14201d00b0344404403400c4000f29070f01152030f03030f503402003811880141d00405200c811a1806 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 195032778 1250 195031528 195031541
    0x10f030b1005030c0d021b01150815130b10090e0309090103150902030304060c020f04090f02040f0e030a0302071101032a020703080f0304050708030a02120d111315031806 75
    0x1201301292501007140800400e903005500c1080c01c00082c0051980b035460203015200c01e105003202940e40c1207240031905603890640701d1003400c01d81c0f190030110f140b991201e02c0c0c403591150000c0b006601c0d8100006c0126950f441e9110b425080791401c01c40c940300ca00040300b02c0d40c4a04004001014a908644030780764400180c07401303410f50aa07180110001a201840607000408140c1c42e0300c0500c1c00103006211401c0300714406c1510a924000c08000003c0c0a60080e00b100c0d901542c00140001030600440c0050810b241400141d00c40498040120381d07250700208119440f50103031700d428190000041d42070701d02d00c2541582c04102c8680701806606a1018404002c0342c40c41245e01040d038981b0b414940703601c03801005190580c00400c00040c004108000001404c080004502e070034074451009444107640900030075189000a005d00b4940c07843e03000130030341c0100009203030b543c2c180000d244046511a4070a96040a0f00441c0e6110308070b020744242098600c0040740c0501035030180d507c840c0246103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 195034028 1250 195032778 195032791
    0x618021b01090f0b090307020a12060f1b02070911030106051e0a090e1602030a050705160f080f0c0609090402130e160909020a0e0c0412030e010f030b100503 69
    0x808100380580320100340221140d00e4050320000000344070b9400d041035611001041c04401c3d0b402040207038010307114040711100f0ac0303850705c40090103c40580f8040003d04156141d0103066410201780c840c1d07560300e40707444100d6500745800720b8509940c0ea031445001c1d6541c41c0014100e2441c01d00041042c240903000400c141c01c0c56a0740030b071104852540c0781c00581c02c10600c00d000a800c4e14414403c01070903400c416004050182c0c4103449403400d84c2c00239030f01d00c5034804a80402030040785080410504200c035011100e40c54441d180910780302c4401304d0000c42184101c8600d8800c1034416008103801050034010301c1b1024015520346020741040c0040041c0181003240c0006400702d00343e14551240c0b06503590b0005040240c90700420482e00511a0b0307040c0e0704191030045c0740075801c00050752220010300840340908061901941c0385d0340913550901446e03100803c9440015405c1080503030004080c01619000d0b240c40860190001b4101c0c100c4002107030743c0b504a03041c0100e00341d804d801800a182c1c03058 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 195035278 1250 195034028 195034057
    0x1302060919091d0c0a03150b030601090203040302210a0309140109030216051801030609020d050f03090102241504060f030506010e0c031b090f0901060c03090603061802 74
    0x981c0324016101400d41d03111002003a0788114290040000d0940300d12040c030700384024860880010002503204599100c003c0803503803911030480c080c9006e0380000704c80290060658043d580d40d041541d01035401241c08074010b00034852070403100010407103a46440540c1c180d10504111186409a008081040d006c0d2203111000080d034a50f041c0c2405064011031203070313018000710021031090103580410394011030700c265080382c0c1003642032200c20203840c112900002c1c08141d1400600110702ca489189401808134095402450013500000000b4160190301303a08550110100d0b010641c901e852254460304041c103514082003200302c441c2000c40440d4001000001c04507540d1481d010910b509500440e1a03130098401001151001c04400d5031000344044020f1840c0780407402c281d40f1b110460041d5091000110710030801da02c48080003501a840940215200d58450001030504400701600700c00060083c80c01150092080c082c1c503040350350800301039a40f0302d1200d110300040d4000752458061803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 195036528 1250 195035278 195035299
    0x50d0b040c0503070f1233050f060d0b0604030803011d0c0306010c03020c03062d0103051c02070e0f06030613050c210105070e0a0b0901050406141603020c01020d0813020609 76
    0x10f00031449400e40d0044240c280000082c0d1400300c521011503d4181e50b045c1f012400c0d4100320544865944075413485085515503a80d40c10a10380000510410000a4018001150101c108030307c2c20002d50517240082c0498070000f05444104452060482d8021944103040c0045401540600319504504e44039005a42e00b48203944d001c6880e0050440b0201c4401080890141c070b0043c0780c650000361098409141800ca60464a5542c1e480f10f180301940048201d0f085910203e030300c28421240030f042d0805000a403030030036141c100c80507042920101e100340070301d002140304e882d2007601c0b80340510341c0710780542032944820302000f00c040071103080fa010200410a210b02171035002e100303545c801e91068a803a40d407000c03204140400f02c512034001031a0f0b02e400b0403087d6000c0c2c0c2c0007800c1c1c07011280343e0b1900505410904203250010b000e5000300318601e030355070141c2c0010140c02203104040f01400380c3c2214508030413841e040b9500701c070a0b16404141380c42a400d01025050050080107100030182845044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 195037778 1250 195036528 195036557
    0x5040302030403111f030c120b031203040c09050403030b040e0c0a05120118080315030a0309090b120a12080a0612081b06040f0521160507050a06050d0b040c0503070f 73
    0x941e072000550400091f9101514008aa000600201c070341c41440070400c4180300715400f00b039881a1f44802004642c20100c0045c0421140e000f00d00050700480b0400c2c4014181440c01174007611468440512403800d00d2606403440703030f00280c190081c04000b00229000f500c3c040c14040c1003204c80210300042d5403200b000c8427000c00d0480e62070341d03174502c1166003a0781c0e46401c6a082c46100c4616405a10039003100c42d6640110b94803403200010b4482e81c6400281c60041000012101145184c4d031400754080d074800d8809218030030341c04980d450020b40380d80006640c8d000419040701d656010360314440800c10070300800b05044002420120003c00a909d14081c004822245006000c0f82c1c21150b85200351859405c02600f844240d003070400a144440102d8486505c3d49401d014561050b400160481c00c00d00510008204600061001070034001f109038843d84014241c0e44451031848445007011010368440c101403080340e4010455940e61411511100c004403442850f0000203c20080e240021051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 195039028 1250 195037778 195037819
    0x5120322140a0b09010e03040503060f060a0e041b0b0c030a0c06020d050c07060605040504020a0e06240d11040f0b0a03020f13050415050a120201050c100b0109090504030203040311 79
    0x1601e078000c0030f03001c0b01c501e0b29115243c01c0d140880e080c011a50002c0c0010481524006089604030034032801420243e81d954000c2050500c03264001d4034450114414401480744000d40d5085001000f81080b0034a0b845601c204410300c104040d15646620070410020440c0c0310b0903c120480c0d200c4c080151406054507081c4040d104145c031810748030000003900320108035043c841c01c1c00600c416a0b0078004c0385002c3e0009402d04c803003407182c035010f4245107002070481d0303403009000c4580c40c240e803c0700204070a01b690701c00c40796004a50041d8000386440341c07200c000b40158040c2d50403114440501c540542c2000e0418143e5000102418117058007448a0440c0c0b00701c12001e000707140f44900c00f840031245003001300302c20703115242c100040022810b03805022644603240302c5030545207210b807010070307006151004840d01d00c071312400e0300c449014644416403610746036040100c9142003641c1d41541c3c0c944510061701112000e9800402591041008000262005254107440d040c001c0403020902c640000e8040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 195040278 1250 195039028 195039043
    0x3070e0102060a06120b1e070203090f011b111f1206060c0b07051c050a0b09010b0c03040e060d05030a0e040513030905060906041a070512032214 64
    0x4011418885102005503410440c8030fa00495605060020034904905c9210005000c203014044061b503000040848030174041384031928812144a003034a1919100c000d449030002642c05100307a81d041c140303035920344c40b80614905c0145618100c003440200d5580f030007540c4026111864000d02c1a00b16920190142220207021186c161940c0d0183c41101141c1421201c0e550455024410340c1610500842d0b400c0b5441da074001e000d070500302d40d52134040e61441c0d140780700484404500350900c0108501e068040c0c000c1c2c0c0520700280c42014003640c0300c840221a500400b201201e00703034020321040007180708545000c0e42203070b00070b48071210864175178030b4650441e44071790325080c00300c2c084144d46ca882d41020708c40d207030348000c1c9442101d083d03004641d80281100800e00c200b511070207000c42c1d694030035030381c00d8100ca0062221807402504e1102040440b001c41e0002503042c0c40c107008901140400e02c13506800c503845900c14031204841c4a183d140c0111a00e049814103864100c4a0300c400890418104541e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 195041528 1250 195040278 195040291
    0x51512011b1e0e03011e060302040507030b03030a08040305130306020c0714010f140f120403021006030c0e090f01020c01020702030c06070506220501050a09110907050301090906060b03 81
    0x105100c1809812204600c604418aa0401202405040402028410a00b6094a6890022600b000c1d030f200203405040400e9041c2901c40d0701d0740b030b0000d20100c594810030807a48203803802e00c0f0740d07620b88a0a50031035a04002e015050f400801040c1e01091180542c0d992040c40390901074101000800c050035070f0301d00c0350800c946190f40020050038406040004500611010001e10035513100c00000904422524400805004e07506c0e402a000040740702c00da0f41d242c00c14161040d01d42301400b04810003041c00340c400f50050702500031840d400411501440d010b407a0001c20900445203440d500004412000308402c0c81b500507200480780b181400e000500b003030503102c1c0000d41c6442d101d00401d81020800410503118000c104005000500042200c940c031688204c01d0748045400090705078103c4514400c0101194601020042111002d40c070200c211405003d00c0350119040e6020701c66526070964034003000c40c04c00e00040000100c0c0b508030684042c42083d001c136006a4507002c800140e041038840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 195042778 1250 195041528 195041531
    0x11030115030f05150102010b0f130c1b050a030810050f0906040f09050610060503010e0c07081306050a03050f27070e09060106020111161b0b03041103010518060a05151201 75
    0x3941310b03030340c1d0901030b00c070282e50201d0b08080150303401000512280003540092040c035448190020525000d020013401c420b110b0181c07604941c6c0d0a00e01180c407690340300b80407000310781000045010030f0304c0001c90406540d006071062494685220400c44805c000400c0c03664099229665030001940038020b02e418940b0810003041103081000c2c100f6485c0b41c01da04031100b004410b0004108506041c1c03080b54101c02002c0440d560303a203660800415510820382e0b1034541c0e5801040c0041c400f54081d004082e610000d0794104410384682104203014038060381c2110140300342c13002c20101c151880d8043c804138842e010403107d845a640b1144580400c04440c46001347d0010401080103d8082c001c8906000d0044115441c1c080341c01c8111202c2141050094101c1a512104100c000d02c0b580c40200a00031f20112541c680c6068502070214000d40c140c658025401d0402180c1c01001c0b0b880085540e44072032020b400b6503607a40f0740d001d0050078028100303044081c2c030811043d025140c400c22440740803400d0f0700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 195044028 1250 195042778 195042811
    0x4090b0f2e030c020c0405040503040b07110906040e0312060103152301021908090301020706290a0b0d020f04050a061215050612040c0503010c02010903030b0411030115030f05 77
    0x80c1514410421222074040c1403d22654026007a40400c8080e118a01102d00242949542c1041c92a60040340c00c2204e1045001401c44140000c504c2c26480c02c0c0c0c1e08940b406107568031081170106590f48001807004651040c4414401c080080d81030540c044410f240000f1586a4003100c8184040c9540c04410101d042140b40760030740016200034400400c081c0000c0400382d0300b03244002c0241c403050a0182266101150003469540c0a4046070b412030342104040c0080fa20300d07540d5034034800e103120141100e600452405141410502074050031140c1a05800c0c1c200703040008000d01941c00380015218581042001182d1a514041c09801402460b03407003850a1001003845030884030780c0c50603c2c11001141d10200aa81d848a04940410b80c0c180404440c41e100e43c9080d1446080c9900035581c95400c092400d2030f0540c5c150700c8452014000d0381c0034040e540d80401808212841641550407954041006014441684081841d544068030703002806a00c08051031040310230a89592407007061185 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 195045278 1250 195044028 195044089
    0x10e031303112704050c03100b030c092401120903030212090705030c120f0d020313140901050409030507150911041407030c0324030b070206040804090b0f 68
    0x42d800300311000d003590700281d42d101e8034440c0030304080300f010390340100c2c1c2905001500f00542401801c4603040003504032414408038199003000740004031440c6000e8072030303035942c00c2d518136260a0072400f418190041603040c00e0550f0000702800d2052903035905000c0c9003104494904550710840c04441c2c0269401600c600005040913441c04002d0040005944401d00500c05030740d01085145884508071528116060101002400e00018180c0480c1038010f144030012016000300081c030060320301400c041c590540b6105620000840448210307000462080103215500703050b07003c40e290900a0a005003801240d0340c650f07d659240e00d4104070700c00d4403210804200030103420b81c1381c160300d000ca4050180e600e04034070501e00c6050040001c4109500e6410002001e4001d500c400d514141c801c2c00c0c1500105001190312582d08a4482120034000010028a082d4804070301d481c00755620210540c034141c43c202807031002c0c1049081c401d030300170108a0841e00f55917034145800311540050036014440740e480d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 195046528 1250 195045278 195045293
    0x603070e010b0c190c120f12020f0c060c06130302010e0607090305010f0207050a03080c0c070803070209010504060302010801091e0c124a0109050f010c0e060a0e03010e031303 77
    0x30004020071004c0f4040620020300d000310003005880c014240c0816444540c2003040c5c0f45c06171481c000d840c01300c441c6911650a40c0c003081c01d00e0f80000c2001251010103601041c002d1504c40c80a0360313040c54203d403010039070f44010502c40c01051340c064130000c0b0f0110324441d14541417035000d42e0b540300801d028000810030840300380120403440341031000071800c0c001d954540580310411000e0003410080d00000255808500000760f031410507003101202d03909038460b80c42c69502e40c04004264446d010001c000500713460503000b2070b01a00e41c1a951588117074030341840700d4040c01c020120680c0340e00b150f14205203c28070504c2610460441c0755144940d00c5a010a203000700c07881c1030180c504000c080c611030550703412400c54036580b1001d11403450b030303041210281c5014040c0401c03800005075401d00208809110001803d010340d1300460000300301d40c0004182c2a6003012a5004803a003201e000d2090142041c00340610018190001d030020820072580d4001c541581d000e54056801812101c02c10700034003026 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 195047778 1250 195046528 195046543
    0x90627010305212218020909090601120305160218061207142e17070e030a0303180f03030213051203070210140d050f16090302090603070e010b0c 64
    0x1985200c2010500f80c400c1c100441c800d0003200c40e04c000c0200c6030541418001c0d02c4000051000307024003a14040d41103038170000383d8030120b40701c0d10448070800403510b42c00c4041080c0c1d040380d03000042054100440c1d40d0582e41d035085403111a0070400c0311510140940ca801d451091a008a002c1c1da680340e240c14403c1004254140c08008185e510004040c030099486003440d850058040341d42c420b010089200e142e101c6040090307000300d1007210210041e001e54122507802c0717a45400301c0100c58a0754540c8000c07500e04600701040c0350b143d8070225001012a000ea400f80040c0c0c101a040b281c0c0321031442d144d00000302004402200007aa000809500800002c03041074054801200d0300100d1000300c0c89101e035240078195004e4031078000e050b0107455079400741c40c02c0350f6440180c000c101c0c0c448e80d800c00e01c10024007040340c0344002003010600265611012000c0a0301d450f006499515050341140c003030068130310f401400343c0e406105104001c103080c03c41c1d00845009040a444941e43e90748145445400c1801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 195049028 1250 195047778 195047803
    0x7020d03050a14060f0310020c01090c05030d121d0303130302010e0a05071505090319110402070312111b0303040606050d021003050702030712080403020106050901050f090627010305 80
    0x141480ca084080c41144606822100880e03010a0b00c0e41401300007810700d40081c421104248c800910160b0928041d005810546d0250280c8007032166182c041c03540710304281000100081141c0d86054005006070301400b40101c1d45542c020540441003681840e6520030341d0454148880d04111000301582402403052a000900c0a080701c4486542e9269a46103d8041d80502d900f150141200c0e02d07102d5801c1e1400350300c00030100d03602001a600c55110a840c60103060f0341041c2d60f008040e50301d0030a0b00132100c44683c181d483d05130404405034828001c0070954280c44114404203c0c44400e611142c188103c000803d001440c0d40e070078580f03000700032070f1310315804980140c1d10307141f103000540c0da01050000d0300026418089107540d01d41104034118810080b00401850341c5140c09100b1a5020490510852082c0c0080080035221710400001c014240701d102d41c01800400b064230542082e03507059410040140404410340c0c6c0d103c8525072000072440c400e4000301c0200d40100240300040215051401c0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 195050278 1250 195049028 195049031
    0x9030901021b030a02101112040509040f1407060e0406080f032706040303080a2f070204140a020319050c0301060c0f1a0106031d070e061807020d03050a 67
    0x55420000c0e460722003544070300200c0d6010345031900c0d060b01c0602288680680c0202412441c1800391405032240e401e40303002001500c24a003090201400d62400c80c0c003130340c80c02840c107500781e42c440d03458070100e5441710401c4584030a80c1c900307020320110410a483c007626264032482d0940409205020441d1040d03480840654840403e03030304844000705c1100c00404600c440c84915102d0000b80072841d00c258038010b0f4201b500000c0020a25a21a1000e80590700001d01404080104000c000380701c14005113041c11003449988661150048000a02d031092010b000403034460746810f80001e041c0011034080f0b1a440d000400c00001e401c0744541c1c0380c001d4806500030490350400540c4401c09000500404007030288400303809003808840b0034a8800640c1c403040b03001c2501c03c0da6103c122000020320031880460f0810000006c485940d006802c418540c0e40010040e8514011100e0800310300600116004001d140304d6802182e640031101c0d114a5003600201982072100c400141100c0f0000c201e8080107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 195051528 1250 195050278 195050287
    0x302071a1e0c04050105090d080a020d030f05091e07051201090b09030304030918060509040c050102010b03031c02030a110706020309060f040f020103090311070e090c01050a090b0d060513050a050903 87
    0x10342c910040e5001d0300c2d020b2070700503154503c0d9008180d007602c0c0303202c0103004103401040320340c011980041e581c070100344a039405000c60307100440d503201a6035044d504006d0613001840118107000311820f144030007602c420100c0314540e9031480800c902c3c290703045080d045a51900b0303003882413200b008119500185000b00540c0b8600e0161001000150140960034001507481c0d696503601006c0d0b00703c00007400d00142001c0346402e1518140100c04002d108442c0035500f080f0030b0f16003519010080d40c9040901514586682030a00b101c08001c1d8802001060a40d50f5008a044420b565501902c41e291041000590383d09000c42c0c12440c02200070501c169040160080000003484166680441c940c207090200b1303240514503080d1449141801100194800c007900029010740c10403a5501400e880d13016540b6031220900110346910680686d980071070315003c07081000c01602c00080884041190000a001c1d456030f0005000c1200040111840c94403417041c07110205240c4036494204801c507000f0b500e032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 195052778 1250 195051528 195051541
    0xc021e06090a0f08041a0c07051c0b34030e010203010510030504031413140409080406080c0702030d0e01031b020d120b0402030f01031703091c0302071a1e 68
    0x118241220001c00d5000380780f95042c00c0003448415140980211142c0d00744079031900394405034a40103a80800036910a51100142504100c402d5078429410112180c3e6400304d143c80d1480f9605000d051000d60781408501244500300c092440c10040c00000c3da00131202030b16041c01000d0302c4c01c1181815441c1d20400041255980304071450303a40d142d02d1305000c11280d4583c10190b4401d15081a1803880b01c4c400140300d011100c40c070440400b5141c1c030300c2031600ca008844050200300ca80c1441c00034182c01d020030080c41200d009481080d0301c2105081050b02d082601e0303021034244803024407108017080f5000210001c1d0341e00b60254490035400078480401070400c0c460029541c1e416003034803e09105800d000c10745840d0568001c602c18100292040d5600d06180404c819002c40920040c1cad5400c540c0215060284010000c0781e0107011908020b0400041410b405072100010426040500d5801c0110780000ba83c031000340d0b0f658005c0c0c64030107103503441d0001d400321158207a40402103061100100300002c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 195054028 1250 195052778 195052783
    0x100e0d17070e062a210703030e1f020a0207090612020f0a080a1a01050306071e030e0109080706060611070b0f09091303080c041a0d090c08012007020d0311010b040c021e0609 76
    0x406c6500352502080c3c10200c696102d00f0582c1d8000d26495242800c6101121080103030001c0032460001da003210001c0390743c0c034012002c0301e1450180060301085408007202501c2d086522240c3c2c0320b802081131248030390ba10000741c9410028401201e0850a9044003001010801080c0e80185000d0b80904014500388500424965856601c00f035200200da00354501d003442603000c8544c40e940e03040204a02d4103207040840303464101030021100d503428054007042c3d1502c103100350b40c90385141000408040e810500c20005a4011079054403003250284010328403944c0b21502240a034030040c0440420108a0500030a8000002c2c0052408082080108120301c078038a141e5000e03000200070152280300b01c000c041d000e0708032010054000d800c06000801c1c81e40d41075200c0160b1880408030814940c1b4804803541701c900801501a501146042c0500082405034501210014016000040c0c0140c13440c0060206c880c2444140d005a00ca14a1258402c401c0c4402d600003540e9400204501d181c0a0001035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 195055278 1250 195054028 195054037
    0xa15080c04050405011104080625050d180602040b0306030c030d09030f02030c040e07080607170708060d0c080705010201150806041e05100e0d17070e062a21 69
    0x2406656110000f8007480310079804040300da400e08030703595075580c0c3e00d00c03c459961800b5903008020400c908a03074190a10030211a50409159484c3c0a0030b00d40451520f00041c03030480c0c038101e000c3c100c8503240c00005085100400181030100c2116450f4204001494684100e5189080c00303540030780c252020b1140c01c1008481201d5002015008441140c4046801e04c070640d5015a04242403c4c00c01d008924003040250a44840c02c0c01c07600030b6a550301088880c11100540c280c6201c20003000f00e14114440c050540e40b0900281c00d21407040001c0d0380301e85108009a02408094219041c103008669082c014041845408012008cd0a0500640c1c1d034551001034801041954103a45400401c0020504860b03070039080b0059441000e43d58446001406d01c103105030710680600310b200c12140f4081d86140e5026108000d014440d03941d120b200340d4140013003107c2180c1c03204c5c06000c03018048404207146115040e600400041200700c01083d107103005050409011a0082c0b1240341003c034010b0f40035207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 195056528 1250 195055278 195055303
    0x8190309030912031707020322050109090c0c020d060506030c09040503030a0b0112020a0201091a27030702090a09020f0d0f0b060604081b130c0210020f0909040b0a1508 74
    0x420f000509441c069428021910f072040112050100700301072590080040d107480d030f50004940c45002d1800040396998050b500840e4080307200000c0074800e1003010780c4612074228283c2099005607403640c000801104070000d04464a50b168010400c903401d0902450074200b805880c0d4201500b00f580e19103449000040110400540c0c500d100441a8440c100e0b501c0c00240c003000840d034030707120361f800240640304a030025034a901a10200d03189488141c520b01d48520040e103590203a4050b2205180040e480394080818548000c0c1300ea9400b5956904045024080f4418005001c1c078480c8103014070071004c204050300c2150824044404a0110509000b42961081c28041c441e51000700050240c00385410030712040c0304048006460354261b10350a40c0b91f02003100c0394900d0040d00301c490000c2d11000c003101801038024200b91007004206802405010380d02408041c200040400415841102102c05030340e4072214100b032040010151181c000f1400840356143d89840c1000c043c1c907034460244105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 195057778 1250 195056528 195056549
    0x603051b0105040e04060501090606050a05070314090301020a03060816050a0b0d0612050a020103240b03041a0f150118051215091510051005030903090904081903090309 74
    0x480300d15a00c03030402c64014080910420005062504210000744002d005166200e441d05401050082c050f9040e42d4140456646040c0341401311385e0111802c8880740300c100b040c00d0040c804130050350740a0014000032026990300064041c030340110b542c603185240d40b114a0340100480c0600c001d894030010082600c1d10941c2c015a03400c600741c01345000f0055540128814000c0800e0301b02041808100b46403014002d99080c80340c004501c0000002840c440049141308100310001c200011000d005183d0180c012891014003c00490114480c404101c074500c18400407241003021030107003001c0b12009002c0030700e000206480250070002c0740030f03898020584146100c41401d5145c54040100305400c040016081503542400301885a90704612030040100c80c03c1103001500c0b503801091070307000b1108000c0c080d0062426003102690241e1001d401381c03c2a0104003c0040d032500e0358241c0c14087c0d442181a203075150f0305e18000c00310032822081c902c01010300741440103010a81c0141c0290948001c03026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 195059028 1250 195057778 195057823
    0x3040e0907050409060507022a0d0321051e040b060d020d060c05030105010e1503060f0102031306022b0e040e01090c0906030209100b191407050d12060305 68
    0x8454680580356101643c800d0620074290300700036454100c540101c0c86ca40071542c0d00880f5001c01c41d95151601c0003d401d04101c104003110b54a468601150254000e0411100d544030300031124a86c2d061045070101c202e5110340511403031b40d507906001d80c1004075641c818103c50510f56150611202c01801c0b092145091760800d0741950b0f254601d204240790302c0042082140301c842000380207908244640c070701041c800b01110b00903041c0b070061f00c0e1041040204c25403460340c8050405c480c1d0800800b065045200c180440ca002d010720b50141030290140d50010003a60324003001d2084900c281c13485a0007074410140e03000b003580e0307040a020305800600700d40201c1c40f40c2001401500400d80030f600a030965100200010b00c0c1c54503035014000b601e0007035415030855a01d07981400c0d03180a00341b054031283e881c1007005203400d8402002e0b0404140c5146403d9210320341c51100e8a00c00d800850381030350f0940181c1d40708004103412010fa40d5105654400910860745136403151900c071005035142111181106c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 195060278 1250 195059028 195059041
    0x307020a021905030a050607030c02152409070203070b071b030c0312020a030b03070801020f0a05180409080903010624051b030309100f020909010504091113020a09050f0303040e 78
    0x80d02c10140030042c00700c990004030340c10401d07500e18040d41c205011a10380360030342c546a8404a41000b403960101c0714182c2d541c5681102d080400c1034020f180300300c0c0300d01c200700788001e1707035141c7e0841e000381845d83c000e50300c5008a003003459a403000503189006012803480400c81c2040006281411503070907090462031850f860806a643c03060030f02d64011014030019a55841c26059800000381030410340460303250a49031032180703080388205e001002d42c600e002d1290304900c42c1f20b20000c05951403404c2105c007500d0708290205e0b0568002c0c0e41c080f100c6060106811200c1c2c2000d1203580000c1045081407280e40c0e0700d600d0140010078034101660100880000c902d00307892103c0d44114000c0c020901105d0b500e2901d420340c00e880d100c001c8003801c1c41d181040c0c5254600a45030003503980404000b025005207900e0041040000c02480500304d40741c180d00d45032f4103490b0344c2d5040216560300c4008800742e1740744441640200400800d8100e01d1141074950328255181c3c40010943e4203a031151021f076203035602e640 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 195061528 1250 195060278 195060319
    0x1a030405330a140702150f0103030801050909070e010311040b0f100f3f0506010f050a230c07050a1802090d0c030c090f020711010f1403090a030905060307020a02 71
    0x6041500d07000c3c440030f050080c004d50003e0080f50b900e041509030a0591031b15058404a0b9400b07200283c00601290014040391400a17a0307036820070081c1d070860381c3c0c6968842c0040c10400c400d034001d032280344110f40c0c0440d141c103080c01a070000c82c0040b40c40301701d103c002d080068029404140c1c8082000a1170400d001d14600900081a4003a0305101102044107030442c001500b404042e01444400c5070318081000e03203556802618000d11050315060003000c41103408580d0b5420084110040103484c5039503160180c400c20304000103e54607149240d070780580e81d4000f8540b005a40c02907009035100601003220b4403164141d02e14910040c500580d441d4080c0c00051034030f40c000c1c0c02c043c0510385488000010850b41d0042c4000315050101c003406070b0442c0007101da0882c000d87e24080d082d144d964202c4501d07503104103548000d0711241c0c104101555000e1080000a4104450070141e640c030600004c0141078208480341c0043c101264858598a00b0400007500c1c0c07001400d000f40140384000e184402220503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 195062778 1250 195061528 195061541
    0x801060e01031107060b010f0908120a0512100602010c0203040503120306030c030709020306090609010302011704080c07030c091b052205120d031103090d0e06041a030405330a 77
    0x107010000d40c55200c517013041401040310a00e010b000c02e0b41c0d080030914141c09107640c42d0031a44400007611500b009000180120b9002c0c0890b08100002000b20707184c1030b41c4400c5d4450080d50f070142d04421003424a0380c0a404c403049060140c1c10355100b40700801c41c555000800d0342d0b290240d0302d02503440c0d8a40c1e40120345000c00345140941d0600803e24042a01c1e19543d0295200ea51308a4011980740c6508090102100080c000070b40012440c421640c594140b2524468000d03104007001c502d45100114040d003081041c1d00f0440711000410020402c664603806034400c4100961000c0f16100d00121000d0300d02d118000381c15800d0b84041000078141c20b0a081c22800038070020381f01c036803c1640d1825960302c8050f61210072002c43c4c40e101398164031168100c141c0348140001c10042548119110050314400a0803d034207520140401c40400c007011034000c4030104441c0f000c0f01d0780c0c40f41400d280c083d00381400c8200d05070195070400c510864404c105d4100a4025604902421050f112819900c018028 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 195064028 1250 195062778 195062801
    0x7080403051915050121020109174903060506030705040810060305031c06030206161202011104050d3002010b01020c030a060e1f06180b010801060e0103 67
    0x15482d01022001c5091014000c4070311541c00c240c0c004030500f52490071100300b802802030a03c56070251721120f20f041503500030010b00505141d1045039841e0111001e0440c461024003050f00091001c4c4003000d6003145610500c1000003803030701141141a91200b4601007501d110340349845600c80601c445000303900c84409400e000d803000f5502c0c98446409840382d8094825030010380318000c0058600026403180100340c0b58458055454000b440090706506099146050580c83e501c0c0c000100581e5072800412080494001c04121151a410603a20595031100c5160079a4104205890400654001c0300e056400031500403107800b00c07605103400c800e281d04010254201c0002c031a0100d0319940c81d502d90441c003c0394000d0013081189001240c80e4194034a190350941d00c2825140000740036500300c001d80c4a8001c0458000320503200716269012030450b808210560341d1002840300d12500c50700c00412184004050041c8009400003d05003601481440200091080d90b607009030b10940101c040d000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 195065278 1250 195064028 195064033
    0x228020f010c0f150225021806040608150f1308030423030c0a0209071809020c0a050303070e0415260c1003150f031509061b0206060f040501080d03020708040305 71
    0x4038800caa80298800c5496194030548841401b003040e003500004110300c1d60160460040b092404402c01071008041e0205502c0741d22210045410407080004403230303240300800e1300d03096410607100703800c075908018119200c0040c0b031040040101700c0383c104482d00f20f07500c1920441c01c2d000c140e04240c0c0c013604001039481580030000d010310680e000015440411030080b5440c400503200c801c4113690202041c2c5081c440c03050021420015007200d5805401081d4120080c0d0340c1e0100c1560703580741140d0085651030b0100e00c1c2a80144090f08081c03141c1c807038455034442404030301400c000300350b40b96a4501d190501a07099109001110480030b00482c42d00c02c0d030103402040003450907240900504000150015500003101c000a100d4821010304001c4070781150340c046074240702c0d84420000d0300b070100302980d1864441d10380a1100c0c180c0c502081018030f05034090011410000208131b41c0609841035680307d94141001840305480100369505100d0b9507080041e5203011502c0d041c05036000d41d500281c803d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 195066528 1250 195065278 195065303
    0x3110609360f180d02070513150b0d050901180f050705030d0302070b31081309060806090c090a0915021b07060c050c0405040206090a060228020f010c0f 67
    0x3059100c0b401d80207880614000c081d0f110a0340c0090f035075999195800c001039001450400403401c010f6240007150401000110740e0340e0a1207581c0031984850391110494100000c8c00f50180390840c824960410100301c003e0000d000082c2502c10710b103202000107824400c40007000d1040040402c245001000041c0660780c0049049001400075000200e0654400c2c0c1d08000280020050710311b4a03850b036103081c00310396105000c0820030b030000829500840b9014020002c00c5400d61a011a440091154402c003040c40d0741410659810703c80090014030460744460091a115a81c02200c0d6501000c1c640001803080428204007211109110210000741d10014641d9110103070b200b043c1c5415603100701101c05a51ba64042140d4051200a010301690040d00e81c00710307d454660002604940005c0055051180c1c42001419210440e440100568012001050312500c8081f405610311502040c40d140b058058000c200b01c85008407001e41040040041401004481032180243c00c4d000320030706411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 195067778 1250 195066528 195066541
    0x906120403030c030608010504080307050723030405100e01200705190608090304181508030d0c020105130506040f03020a0b0a060602100e0c0405150301090c0311060936 74
    0x300001c0f060880002e040840108034184140555802182d0000b030951a65a0703158086800b80c0081000712040c922000058207070321144e221906603207443d84082d6584034034180800058499810050082c0704014503050500d0781c01c0030003014101c40625080240720703c0031691034182021078001c554070950050300960b000d1700c0d5420300c0c002d0704d44070b444800d25030300e0f101603442d501d020f148905005002801e09090740d0f482c0541004001ca045210080e40a540b0350001c43d0641c1c0042d00c184810580e10b00c2148049542402140e130440000d41d840300302100c071511040e0f15082c00038405410320a08035095002c0502c02c0240b04c011542101d0120094203041d0754080290041e4841c10340144119040710030150074a100d019100d1400b2002071036034010040a00014020007000c0003981152528050310a403420b004005045110300817000e5a142181380c600d2108181d24143d0380241c8007840350340c0c0552100b051450b61024075000782503440b111705101c0070040d032000c038106031500d5096052181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 195069028 1250 195067778 195067781
    0x10315080109030c14010203041e062a08071b02010311040f170714090103060e0c040203010b090a170a260f120711070b092106070f02060c0f090612040303 68
    0x4c1248070300b05145101070214101e41c00d070b003c1510090b00144050120000000c41e5010784445e4520a400205940f401e11400740d91895a8000c104801a40c12200c80c20345644400c00da580031a0038201000091688106481c1590724241d000381810f82d2581c915400005c100d0135240280100b043d10f614054a42444000103480b42c441c82003130384280c02001c0b941c0d0002d44200300c101100a000380c6a56803071070301d941010f40104c0000308102d018002455815031100d00082d8080c18001103030f00d03035400e0307020f050001c08242903115040b82d80814129000c515408584445200e0308060b034004c16100fa155130340d9001c00b030109507900001300040c1414000d2003000180c00c0c0440c03898540380a956038054103032500301d10700c00c455030035410030722042c4442d15070710000d050035039000361680c8105544408282c00a0204201c014801d42c0301000b080b101c40d9211042c100441014400350115003010034001c43c20340100b070400410f010020543c0003480d2500000e0b00c13501c0c012405044180d0516080103030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 195070278 1250 195069028 195069047
    0x801020a02160522020c1509151303050307050c07030c0501030f0b030d0f0512100312020307050601060819020d090b10050114250b1009110901031508010903 69
    0x14007600440405420052500c2480c20883d03801420040320035061000e200b081d40c0e25400d44a191030790a02018240500410200c41d50300d000704a203c01034240010841c0c900807039410301c500c0c0e01c2e48101c1040600d40c105500c1c50340e203030f5140c206280c503500c810700250f0705070140c202441c09510840c040001400303202c41102c002c0710b900781c0701000303c4260210002c0079200300c0d0403416050380c00440018201c1e0310414130311010409604c0c240d401c020400c42c004119444c103540322000c00c01070040602c2441140e502c002440005800194500303402660341c25110001403241c402030260340c0c0b000030340240402080c114084c9200c0f40c11940d07580301c4c2002000602c44410705442c00346641000454182d040410401503400503118070709199401c4001100550250444c1d038055204000c01c64801500120840b54007480b400d240079151511442c90a00d04800e0b600c00c0c100c072030800b034003400307009480c00454120010038623001c203003000e001080880c8a86c0700c2d8411003c540c43e1001040c14158044e600d031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 195071528 1250 195070278 195070297
    0x70204060e0c07111c02090601050f04080a12080403120507180b0c06060f03030702061b030f0712170c09010c050f01020d0b0a06080601081305061303020d03060b03060409030203090a080102 83
    0x100c4d503269a0300070b10840355641c42c03024140400c000d4144006d850040d007010fa001d0710516229160040018280380d05030015400310809a010703551030000c000d940131006062840c1c0d450135203030310314060701c3c024000c688071078505d4203013030ba1600480c400342d104c1c806c801c50740d40410001100389550f503020884507074000e5484401c14050074000c281703245400101d4800c101ca0003801913080580303d4082207120390206c03150054601e82d500040c058001d01b0300180c002e512582c04000d80300c10041c01c082c00711074000c0c0540b04c10449044642c2c1902d400c18030020ba0040320a290554886007020016100340e010400094414462001d9030084031005400134003443c001901e0a100c00e049090510440c090b0324000d113800b007100500083d000d544944000b0390311403c440101c1c1d04600b07d030789505050441c2603a14540c01203045480400f4581c0403c040c1140d01258502040180c2c03070702001ca0068040034001c640704640380c0388071f8408e0500c20130680700d240c1001498440703100c0d80c4902082c008d52108205 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 195072778 1250 195071528 195071543
    0x30111040302011b0b01140607120c033b03191101090906180c02150a091a060a060305190501120b0f010b0f0a09030807110a0920070204060e0c07 64
    0x14940c0c40d0035134200003080306500440d01d0710907900b400c0c140c1c0c150904140c1980d0b006001031090f030022a031400c9982406550584820320003980c83d083c024040824240e01c9070900c45071004180001170410455049600105072040c0e0344042000024140081e24005007080c401c1c102c804002c0c4001d00066450526098a400e1011542d9011003000d50351a072003081e808005c6140b40102c494420303085240750030001e2058070701902c802e11013469032010a440d18079500d0381e0340855004015803c0030752a6809c0c4c5401d04c072141450204002040c1d00e2907030044d0020103848501040843d0708404050740c912203014424000743d81c41e2410a1300981c44d504081c0c0310784200201080d031451420780918161410135501518100301100c11403100d500603950101008408080000811144c1c005450fa1074800e00e621120203580b40f0030444158002d420100c01280740030f82c0203100900d20f8000e4107110b010012140d44804807800014001c0c649680840180a04003040050179101e1000034000c45215880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 195074028 1250 195072778 195072797
    0xf27060f12100902060424030b040b0904060c0e06160b06090f01121505010e060a0b04080705040504021206040f03030c020a02090601200d03020c12071109041103011104030201 77
    0x1001030310150181218a80c2d045018404280c60481d0404030b003c500140c83d00d40341a560720b4828400c00101e04c10040c880002c80303c400300baa68180246544164111000e03c000c058500028081e0440500018040ba40c4e41300c2840800f40240c2214000b0100180120f031107048121010341d010182030001c6500450b5000061401d19180c060300e4000d01001d210b0064583c00d00764120002121090190f5410a00380c40e407166048071802510b001c1c09003c441b4090038240441401195030701604182c4d103200c0184018401004005415004c40d40100e4010403683c8490000c605110325400c01d00304640251030802c070601c8188c0b014150030398429a8200f04680c80c00808071303114021032070000c1d4401e00542c003041580d880b0742d82114080c0c6880c1049004c0c0358804c4802c516100607200c00300c000c01d4001c54181c0500074140007440c403200200003214900689540c0d40d0b0070a11a001c0c480303105150a074007003014454606040f102d0b49002030001c010152aa64100b00e40350000d210490000c0c1000b030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 195075278 1250 195074028 195074059
    0xc060e010c23061308071509151407021b0d030e030f0604020a0f0614070303140702070503010606050405030613030c0b040b040c0503011e390305091603020f2706 71
    0x400f0713403000e560028803081c00e0210940da9101c0c050030b910604d601e0302c3d443d803000d44045001044520300c40c94010f0f20016890800c0075940d408048010860b00039504a2001c0d0885001c03094240940207808440090303400c0742c0c034901601d2040c0b07056050b5070544201d0140e0713241c5803000164180201e00850300d458407161380b05001d20704a4454003445001441c803100f0301100c0709030301c0041c0100754400d0601060356030746171038070090285049a0381e038010f07070180000b009541428440c0038040c1c00203140170351a05081101003540d400700503140740586900c0f070a10b6001d0511501c1c5100406038891303d41c1420b41000e06114100308000e84054550451f001400103003481c0510450302100c1e810041010183e80454842c4014140349041840711a49010001810362440c0a1821040c500340c0b0594544c1c1e00e1610010110703040180001160342c080540102003a050900e1b520440364119090906000c1802c081805a0b03100b16100340e180b0011280f5403014030100c101c15209082c140c031031401c0041c400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 195076528 1250 195075278 195075301
    0x210c07090605010206011a0405090a091a0f0c160209100312020f01111912020409020c100509010915110409020a03020903100501062001020903030307110d09030c060e010c2306 77
    0xc407007d1401c07a0b0100000c00586c2001c02c0d0541e4840312a110010781c80c440717600d5944041d8074110f05901160181c0003080900108002010303004180b643c1d40504191011280b03241618041601910903078602e80024550b002e00d0b02d1210196500a1420742409015200a0f54840103954080000d500700250b00f42200c10800964103950340c03e401c099900c0c888010b054030020709954030b4130035540d0200000325500c26140010039031682490002c040d8032030384031525412203102030310f119000e90501c016100862a00103581b041200c00c4140000d24082140d1404558803c41d846005040c2c000320785680240d40660181c01c00010941c241ca810003500351902007194800d00590b0003058051b031412400141c192042c0d40b40702120000145800c0451002910707503042140e2000000b46d9000c10b407038954505019101da81101410056400343c2580e5580c120340b0031900504041241c284000c3c440342e0304c109404c0b03000f603070841c0c40b03c0c0d003030100c81d02030b0510400181c000c2d0a00e0b209110116201c1e205d407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 195077778 1250 195076528 195076559
    0x10608010b0310060c020114160204050105040506090714071209050102010e120d0b040603020306100f080d050307120902090106030e07050105130605030403091e0521210c0709060501020601 83
    0xc0c842800d90034201362041c1e070700f0148484181c1c100070302501b20f000b00c000100c00400300310f801d500c0e04190b0401c403441000262041600302d140200d00301400e0100c6616607614503134110b9200d05003044060381401c0300c500107010b0344c003020780084403d00b00c0640184c0c01500c2001581c00a034003d00100b101d440303410b6034074504986500055070040041c00c2d00300c100c0394080040c100b0000d0001c600d0030380d40d40001386069020380c0c0c40401c940c11441708000b41c2d0480410b407001048410041c001c0300c4c49480000d4090b0000801550038801d1800b00304141c02801c1e4001e0b034000e540240b1280995840380d0303005009107400448656070340704503c808115580248160340002c84c00107940b203031850034000100c4050b04081d0044007409030150300032511008107100d4400164801100c2c075035282c58401040740f00703401000029400d140300c00305c3d920040f40c04100c0c1500d6000c1268004160780d10303817415165510804940e41658007400101087d00706990304501d080700d00036402c41d41b00b41d1700d0329140b5041d09103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 195079028 1250 195077778 195077791
    0xd08030a200d02030f1515030604060306060b03160809070506090a08030706090b07030b030a2303030403020f070f0b030a0903020304091103100b040602062e031101090603020f0d09020607020301020c06010608010b03 94
    0xe8a41f40a00d03a0400b8001980e010034007070004207130300c1c0d66940c07104150760b03254000c07a00030302c00881049442121003525180c01d20040c600314106042c000ca14035100c60305809110302510000444094507114800b1100042806104407503690210303041c10801011071190486503c21844080796031640309014030708440d02c0c014042c000178885135440c0d42d001170040c101c803240112911803409000c103051024620031402500903000f04034803521140d040030510b40103114800c02844060141c1c02d2400c0540760b00504000f0001092230940c142a40f450103554043c004003814140031a5458010384069400303002290005038401e6282c8500d411103000c1c034060b0000580c0300c01c5c001245c001aa0381d280d0011407100ca12040458690720004540c05125042550411080d0049d0190703941d103d0340b0319000f0540c500d0110704080f000100c0149a12034200009401522501980159030b154000c03558150f038010021550b8502502c90280c843e80244200c0380404c85241c0001642100d10080701d20400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 195080278 1250 195079028 195079039
    0x4020103060503061e0a090c0308030702010e0111040501030b01020a0c170601080a03080f040f0b070801061b050c01050903010f05040b100b07050706030c020f060106030e0c0d08030a200d02030f15 86
    0x18000f05c0902e81c150010102091030b6101d400c68800324114a0a04000d54003035903a00c0e54030b1a03c210080c2c00d403505015500400d0f032400c1e018408a603450700c146d80a94409190108025880c031004034503048141e031001d080c1e400d20301c02c001130681c69041071940502401003560140da07030302c4400c507407a000c07280c401a020507803030000680030301e4403d580554064490500c00c603240d6040d13260070b00ca8020481c0c00c0c40c00700c3c0d50f85005110641e00100280318144c3c1c1c46116690308085075543c0c075242d80d1032040d220706100300032032003900559080d046810b00c21805074040000d4a4681048010311006841248140d00001004a80340f20303203100b1182c2098000e00101100d6151100072002000101180c40450207198051303428250f00f848148d008281d80e81c3c02254a1004001c843e0070000f015074120f1195002d03103d56000501a0019030b58081201e5000151110a034280ea1071035240160ba00341c00000c0005100303005090b00e5000e140203030042d60407410580d90b800640801501415170700c681c003e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 195081528 1250 195080278 195080311
    0x10c02041d010c0f0c1115300108010e150903040e13110307032f0301050a0c1409010c0602090d050f160e06090a0905190c08120f16030201110309060402010306050306 73
    0x1400c0900c807034010752103c810071fa407610303130b0b0414281d4082c00c036540b10240340e02042c4d070b00b01c0e4918411707032586024105e000001c00c848907805111542d10401400c00c01c3e020300120001030350000b000d0050714000e100c100b8000c3e00ca40340c502c40b0394000941c4240125600064081005001d00f030004031507003980d0784070b01c148815284024018408882d8040319140010074551007441903103080c001c10380551035821001c60f401c50302060207041805400101d416100e001e00040260f03aa002488455980e00a01c0c016070b10201400480e55030380110601604510601001004481000601d451812481105044207035100d81c1c86000030300059130141c0d072012104022071004440703548581c201c5485007003201c05030285807585220005d0140340940703810920b1801000389880506c581030314a82c0111007245400708181700400d09016101050703070505190a000c04c2090300035484081441840b0380940e032285003c080e00c41d034404e01194100d00003420b000d40012141000182e0178004d15803a00c4100384e5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 195082778 1250 195081528 195081563
    0x504090207170d090b01090c020a0206031e090d09060f0c120903061b080906060916170c031f031203020a090902070f1a040b0402010c02041d010c0f0c 66
    0x20750410081a2005038410318184030b0100040700800010401e01000708040e40c1600380074000c61816070200f42c2480c1000800125298042082c030089507040390015120385881030716042000d50091800b148a4800b02404620040014014441d05c41d075030b00c0c401916184c0301c1c1120701084503965140801e45d252018000960b079114881000b015600d4221081303a1307241c0343c2c1000c0d02c80d0120011009404241c90102890740041090b5110452400400c0d86040c42800308500341d034014042815400c84483c00100c040c410700c1c40002c0342111950800c80e0f814011204541c50781f069800c2d004450900d040d5070400101e0408181c1101d81082d001d121111910109070003960120810108120110f800402c51381100d2001e003e103107009400200000d06a0720305002c111541d0002c050340082c60008010000c2c4a1940c11680141d0a28112a088403d8804030300582121012048945084c0451901d18801507000008508540c0c2e03a20043e05103004060b40c11907648640540385014107003e0402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 195084028 1250 195082778 195082781
    0x6070e060703050c01140a060501020f060f1503031c0606030b0d0308040b06120a05010f06170a20030d11061008071721030f16080414030436050106050409 68
    0x421301d82c0710000308580c0c0c420340b83c086d14228200c0302000c2c074950f070304000c2c480c0c1d507810890751007074102c01401040e06041158075400340010040050740d00c2141c0c0310440e0166241402a01e9001c81c1343c8d500d0b06111080700c8204405049240210340000b440c00034540058545818564240d43d01074071010860740700c603207901c640502d0040800f508502d98000202e8254404c210001c00c0c14085c500000300604c6075a210810765849500060803030080c0002c1582600c4049a043d01166100c0e46000720200f965410362100c1d02034881003135150040140a07003025811560f1a0310400110f000d03115141d40b800ca40c3c0c40a00407500034644a42d000c0c6006110513210a0032440c0000041c60031111841e40700045019607013215544440189000f00c00e000c21110481d10103604410843c0c0d140e0303125096010000c02c3c0400007040078080b0460a07000a140310780900c00c58000e800c13070303840410807000c6090703151052598001d90b0300da2490b4203a00708900039209110352070507140c080e0354061826181980742030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 195085278 1250 195084028 195084037
    0x305030402040b120a0515010b2b0f051807060311040603090203150903040807090209100315050a080307020909010203012913091b0309020a060c1703010b0c06070e06070305 76
    0x1138001e4a032071200c4440c10410030040485512441c01400702c2c282c200300e003c4007010113074025901e56105100200300003031205211201050705c025014105219622000c001d00240c08135015214a45001d12248404081044208680d08800c80da1085d41d0752504401b201d8084242c2c82d000541840b052001c288280c221b0300c60765000408031844003108100c0c1d4108240c00f580c0c80030250780300080400030110180b05030401080316030411410045404089107480c0d44203208102003580e01c034144102c0d00380140c0c00381d0107000090400d02e202611501c0956403513001510980c490301032003001410180050007264181c91001b039a8551503a5a000c4803440910415141e640307a00c41400141e0300700000480b0400200780010b03011455003500d02448046150b407040c00c40800d4244510100540c45503520b03507044ac0c07814508106092201d081140c500458001d40d0303003583e400080000b0b22914054050300c11822440c0c140c0364136032a80441a2283c001100c119074000c1801d10030640403070701900140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 195086528 1250 195085278 195085301
    0x9130219050916120525080c04030b27010608010b0a03021c08070b0f01060801080d09150207050a090b0f0307081f06050d03090812091f0903020d03050c19030503040204 74
    0x40700d50728100f03401320140c8408544040300e9000a00d0352400c9500307212251685001a41002110740c200503494100a10413400091b10046101000c1464680d03221070b15145075040964044812605008032806050300c1c1c81907003680d40c217001c1d40201910302003800c402100d900a00000d80e012002c40c4a03203105400b080140c946181c240400404510f0070540c0314820b5115502c0704031190304200c0c002c0c1110b001070300100c10903031100c4d04402206030480040d0003520050300345058010001d00c0d0891400300b01d5040700c0d420000301c500000d81f00c1c040f07421000384407404a52120b826400304c014150703074108034410a201a84103034265507002e0220704445540801c0000041852030301c4001240661a404070220009051018104031180301071000f00440d402101c102d070300d0722006900042c3c881000348415510b03903002941c4408558020b21004005540c05004032104600509010300580c004525110980c021031205010803404c0021550380c030341d07054a84608580382c6809000007007903042d014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 195087778 1250 195086528 195086537
    0x12090d03181203032a08041106040602070807050607020d031b0f0f0302100513170c07060f0207080307080a08040212010f091a070206010608040c0509130219050916 72
    0x10019858a0510304038080c2078038214203080301c1e16620f00201210085580c0440c42c0d042d0180d4040365400803400c60311200e4040c03500045a4482d03042400d0a002c03514407150744160005800030f821307a00425800116103220040d01c00c259030315001e1007813078410a03800a501004110740c80380042c2c050200c00d100e521b2804c00c410325030800c1e07985514030448607a000f581e0180d070b01000d81c1d04240c0d0402c0304205c0f121440f0014880783c113251248034001280300740c00610800007c86200e2b1b000d215401921448526842203d4002c2d039100b90160600c480d045c0110012300820b80041109070001041f102d01039400200c403454054100c7d81100c03401400380c400c99100c480c0e031900c80710481c801d002d080c01c2003491440006e1080300c5441d083c4200303007482c02c10400c0080040b04000080e9000704103181111050308151802c0d5603245442c0c5510035890300225031219400b010f0001c1c1841601015520520988210654a0f494000e41d071208400744610ba62103410700001600c400c0c0f0b5216102e8140400341070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 195089028 1250 195087778 195087797
    0x2301061206031a06040b1f030b03030904060306230103080a1d0306010801060f08150604050c0d053c010306020a0504080709140f0c0a05090a0b0d15050312090d03 71
    0x1074100001484511031502003071000c0c18400130346020320490030a803004071200302005401c00c108403840c1c901c686003101810b5440c00401165241403080b45c10862000300704004d03168480c40c12030000d04100803100070581c03040414007d480d00501949060300e40141c1d2242c24000300303503400c6840d8030b0507400b00e460031001035500b916161800c008881c003a103243e00003c101d80741841607250144607107602000c100d80c86101e041d0802042003050581042041d1004249039903403900410241c4030354540c1081031458403042115072501400c0c022451030b07000c440f0002c10b4100c501d03803060103001c070b49201c24505020401040003801a0b0300422134401d250074402d080c0b0380c0d103050301420201503902c2030520f1a100e49048004030400611503500001c54084c106050510426111482c013406003404144480002c084410399108284800140304409030355035508403d40307644c006001800b254003589230542c84013040c0751034085000c0c1d000f440240d039100c0c03c0000700c8003007242c0402c010000f80c007440080e80e0f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 195090278 1250 195089028 195089033
    0xd1104020a030b0f0d32100506100804031706010909020a020102030a0b15030a09021c0516080105070e06030414030301030f0b090c090c0a090b0c0a020301230106120603 74
    0x1d04030a02450b20009003694500c01880140d141c0203000900c240340305881c010020300508101000500c80c03001d503600e4078010350b0641908080ca00c441c4030040c819002a6422002a03800103072040c101a5401021280c51140a590010b402e681c02404541040b030281c100314802070525922440500d0a6881d06035115404812684031a441c0c00041c0d4001042250700221401020900700702034840c40401100c0f400506c00030701001d00700d06011034441020000307541d994204014030701c0d24511403400014a41c0741c030603620848444842c2c1e0f001c05800000402c0d02042c46964030855080d203c00d040441e80c9000c00c40c1a0340000d2084980780f040d45c49403e0a44410009036000c1c0d0300c6003c3c600c0000d1028141380b0030f910001004ea900542c808840403071192030b021542904151113803140c6448090b042820390300303c0429040769204900101e02c001890900041103420300c0e000f54020004000e8142c140c0800e01c000f407078910340c036030340300302c0100500c07482142480349140f501d0500083c26510796 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 195091528 1250 195090278 195090281
    0x190503090a0b07110705030307050705120f06010609050906040c09050d03050408070303020f070b13030609060e062a3c1201031e05151e1003030212030f060d1104 71
    0x55440f0000141e403c250403480c1e400402c4940040e01c8110000c40c103148056840c180d642413903004041c010f000c07000120080f2b83d070411a0f032582d40d13854000c1e11041d40e100c90300203042c20501d100301e070312400c07404010a0590810b8414030303035084802d64032801514145000c0c88a80150310f001201000403c01000600c464140004000f9602c240d01902651414860710303441c0145c40e41060a00000c10481081070105070400081103981c0a400451600c00a05180c0020440d000c0f0500c42e5018680402c072903181050350540b4442d152500d40d40785a5598861030300203010f0000001d0f0340e01e5286e9080702c49409500c0480e1100c01c940e5078940345900f00d1000c458a0f5400107804400c42440840050041041c0103800503007814070400d042482e012261151030303440070248a2480000074504c0450001c5181e00728060038419500303007003541801c00c0c00f1102d1a1030742c00d100690042c051070b0002c0c4030607070740003003180d00403c03030828040c9050310703407904200c008c111034002201e0302d801072440d40d007250711039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 195092778 1250 195091528 195091531
    0x6150f0f06020f030c0c130912020d35041403070b0a0b010f02031b011b090905061c29090a020109050a12080306060706020f071205190503090a0b 64
    0xe29014408500e0004040c0c60700301d070b000c50030109420500c14203540910004a8614181c411103038642d261000c10780b420b0081200b00009405070b20790000030b4081540001d400d4641121580d20b002c004c01004002000761021010002d01c06584401403000c403c0044041c160824041c1d9140e102100300007465a02e036a2007031000712480103150b010000c0029452081016070003082c01d000c017482100240082d180c1c407032403240e4400015090200b0101030301c02d41c0a0781100044100040040790400000b80c1109800c0c484e520516060500050040c2040b00c6003414407102e03003096066a8560307582e40060f07220034114100b680c2881ca101507408402e03d030429402208560050002d0202a000051400c64581c104600803d0704100030802c00101405000200d030b08198499180d8640500240d5148900c0c1006040c60340049440541c99000034001d0070194407070600c4070803e40c100e6200f07560314014800140d000c1110004181c1b907150041c0d0003168003c0b02c01c010b8814100031540c400c03501030720 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 195094028 1250 195092778 195092789
    0x30e03210a0b031203070c23070305010f0c090b0d020d060e220b06040903030b060406030203090610050609060306030c041103180307081b0703120201020a0807180306150f 75
    0x1140d400344880400544500c05070060168003604007034901034620314040c0b01c064460801c02050903410400c1c0402c018002480c01c0c18908801164040841c04682d99001c50009030307000c0d440c16048403030807202c0d40300b04043c81d1100c1d21095501d80c41c0261022441d0804a5010819030302002030031103006a07449005c0150074031007100f248034105221000d1152100052441d090391080d006100464101207e481c2d04c005c084502042091003131400300d015114510394142c200d0800310300412000d8168001d548245890812990565520318902c01c2c0c0030518490030360008010860360165061110007940d02c1000034084405084060006c030742140e0500c03031031240c6c81c000070040c01207900d4841021354154154074005c508000c40c3e0384401103988605001d403003440000009070f130b10f14001841032400a58010070389400c0c0e01d00c13900002e4003030740c01040c0800000303025a0018201d41c3c003444014017601c0d240b100881c3c42ca03056a99190043c8201d04022164044039500021038414104842d8007901 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 195095278 1250 195094028 195094087
    0xa030b090a080301081c020f2104080609060403171605071a04030306080106150e040b040b030607050415050301081f020d021602040506040506090a0c0c020402040603050f0c0c0d030e03 81
    0x3200642d240940c100541c2d4070302c21500b005011407241940003500200c0303d00c2d4011031101d55015004294541c1c0700c1cad071380014014060b000811812603408980103101e18000d8507100b400f00c4030780311400c41243c03044454689400f40a00c40301101c40c8144090001c081c40340310308041c00300a100200e1903070b00c0200d404400280d00c2e0f8809102450f0213002d41c00040c240883c10340310700307050b245010b013800b0901c0c2000d50086503178601d01800b80e51507030004000d180002c1c00ba1600d608209000618903481402058244541e0b80ca2003036101d489002100e0488500101a0050441d850b003241084070045c0c0740f45d0300a94086c0914201d48078103100402180700d408100c845025141d106100523560000c081d607110301d00d4182000031544459038150b41c821640756001a55841502d010303a0203886400000e90000d1000c1408281c0301e0b01548464015040c01820040310b0340c039215000b0300c2d41701c1c0011000d641d803c144128080c00e40207400240d020600482601c2c1442e004202244480804040100202c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 195096528 1250 195095278 195095293
    0x70203011413021008010501020a0609060f06030c0312020627010605190f090608190821010303030b04090201020d0e01211506020307030206040f02120a0c090c020a020a030b090a08030108 82
    0x44c5014802c0341400001420302054035890300380040d44500e40d1043c060b10050f113810520003040029480b000c40400c548008001058603800c0c501010842c50004488400b03070300324102e4586000144c1c0c248509241014418118070040d21132003e05034144c24000950341790500800d160751070201414404800303d803120803003454032040560b440c2c1c45500c109034444c5095401c0c4031004010654112040e11181e00200c012030b9880c1c44880f510442900845c42c40710301c082c180e0041e0350988080d0489009540500020700c2031010801143c1d00c1c50f80003030141c0d0009502c2600c0c1e50041510849040050400396860700700c00c4c03021070000b004150302c5508295681a14480724500403040006401c40d4030046050821641d0003a42d0b0b103001500140600d0304d01141b0004558813020580301c4000d400c010ba940001c0b20703190401d10140c0f18021000072030302f0130000308d110520004a9031a0144c0041801510500d103407540e40e106e21014040001c07030300414844502085041c4000d6009110903802401c10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 195097778 1250 195096528 195096533
    0x10c03020903160f0b2203050706080a1a1504030206070804050a1e0306181a0402030d180510030b090f091011120705090301090303061707060212070203011413 70
    0x34000070075103540b8000200c0070f082c0300740e0701c1284018080c1c84c05407014a5841018920010ba8070500c00401c00710502e4000001c4100180403440b003084810a44880c8660b03203606500c0300583c0c03111380e00f089602c640510381c1400c0d86804003614400c0600f500c905403074280c4030317004a4810740c00f0500954082400103010000d504240c2000c8005212000341c111440342c1c50040441001207a03c406010507031105000c00f1654049100c003400036510000540810304c120715401d07040344003100c09030710030b0081e00711892019024a800000314481e8044400c5e100b81040e0800c04200342194010b01056030b601001c0c1d10320b880c0c0c410032501400b40f0b104400142d1a00700000d80c0780a0020100f600c110f41803540d814050941281178840422001884011540d18442c0468040c003c400a060b8035600300710044040c1a0160b0104041e0392880009094240d00d03040708a0b69541640300f944010ba10120202c80d0140300b00e80039088a6200400101c0c0c80510203082d9040b83d0310a588030703444c0241c4001c29508 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 195099028 1250 195097778 195097783
    0x300612080309070b030f040b04021903030c0303060e0c0f0d110c1605060a0e0d0f0503031005130c0504030f06060803040b18010806010f0c0203120301060e0a0902040b030103080705030c010c03020903 87
    0x10116108450316628241c00c2045011b0300250000b000d80c0100e40110b821942c0f0201c800c446801c6511410b05550341d80d0a00a200c5c0c4044001035021038038210b03000c21281603159074a031042c400000c80501d0311080034101e410550242001080550ba510441070b1a0000e110040ca07045203000010042802d402c10f02404d411406d40c41913120703c2c4100850000250480b100761190001140c40a0340040c1504109c50208000000100340d4080002000041144005003006071001541d520303003400701d101d40ba94211480400c0800104905201c20000a5840e003d2241520301c62075010074601d40c4d82ca07900d4036581080c3c001c0c14031050040f030012078560150303010908280003441c0155580c10100d0020344010043c0701e11000300841441078500f50f460800c000042040e6500c410350313507581d64100c0180046944420103105049500001402c80010700946069a03050302400d880c5900c3c5941d050848da00c100d8084445e80818820304564400a1088403a14080c5841c096519840d0008150 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 195100278 1250 195099028 195099043
    0x40204080304050108070903020a15020a0b07030507030b0f06070809150d0903030b010e150d020909040f030e1e0904110d110910120816051912300612080309 69
    0x6c081002c4510108050782e01e00440c00116500304040c4125802030410481c01d010348101e000c3d100e150050148244c0d01d80c554000e502c1104965020003022255108011501c581a10740b141d0185c824458080480c0f00341001b070418070b100815002d05640c00b045c00e14090740146008902842c0d6802842d0305060705401200400c02c424a411802ea41e1a07400148089011003c0c000503484041101080e07100540c2c100d078600070000313001e01001d2410745044040c402d01840c0840004a60400d511803030b041c4134001c25040004403143d40949401d40051007a5410000c0c000d94130421250564081516103103803006125000f074601442011005003071121120707010740b40d800f00380c1c4160020480841d0014140f03000590060301e031a652007080c0d01010400c3c01d2500c01529038041c407810710070340c41004d50070a071400b4819000d0110650b15004152303080e000390b20501c00c52200f260710071f004007041c0d0030b050717944841444000907a141d01ea5020b410414082442160300550000600140034020010312 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 195101528 1250 195100278 195100291
    0x7030c06080c09100807030b2e05030705070f02030a0c0e07140a1b02060d0507050a110a0b010e1f060306050a17030a0804080d02070f1a01030c15020c040204080304050108 75
    0x118900f10003080450a021004500001000030420104500a1282e0410304414200070154208580110742a681c4501900034241c40300080301400d5214900400070359110f203e0a0302d40a041c045680c6810b0348200400340300701d03407500072200c007200007a404040200240100d038084070b425140030400506440700850620180c60010311000c51100d511078121940c44083e19140b1101e0006480441d865000b01d20301c000c4918107100c00c100c0e0059100e006800110074075903440c800511040c080a46650b45040040c0020b280c043c010b000d840591400c81750004003004a442c55130740401c08a02c0d14007a1600002e0000f52a42810400e500d02014098054081d0486041c4000401504c00f179036407091940804c140700301900020244401c04054810500d40741000b55500c5040c1e02e080c84400c2d1200d40100d80c128030b00480141400c10011065050329401402c210729181486e01500b122007881c2c802100f180b20310f503205081600c580c0060b2000313005100066031180e0038000090403214004104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 195102778 1250 195101528 195101551
    0x50d0905090a0f0902041a01080c120609040f0b01080f0c0103140f040206040b07120908030705070504022d030403141312030e03030711030601050607030206151207030c0608 76
    0x144020355a001e45076410441c00e00000a85510006032240a41650a0040d41c45890010b01a801380b2a16000d0118518242d80300805036441ca9041c4d402c42c01510508218155004000340407030a00001c8690401e015000308084c00e9816a60030f8502c5500b6081440c03107401c03e46920403444000c00c54a03420308400d003010300820102581740d29503418002c0003121103201e4200407d0540d11210111030180c241d1034411036403020706080400300900040c00800001c0d56a56000a8074031000c416610750300d03405806041840d1820081001030f401904490240f4100700100c4000c28203289000c00248848008143d101d00e05810060f0802070203d81e96030569a0800c55204800305200d00d05e410f0366160340156000440c6401c0031550800c003901c130b05030548000180c040c280405107198a0b030b08201181142c01070b03a210700c14003a282c041e40f107000380940d120b1408980003081c0c006016010315005001d103441900015032951802080754815034031018145800c3c000c031680208001c0d80040c1c40780305d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 195104028 1250 195102778 195102797
    0x903171e0c164a090102040e07090b1c1803120c030507020718061502030702040e0c0310020c0c040501270b01050304120e04320105060f0c070503030a030504050d 71
    0x16242428070f5480c8504410820a4500c007a00b40d9000340500c441111000d40000c2d40c1c601191028001c0d4401c2c0905410b10141c0303000180458498151682074890800c0c145003030510b2003203001c0440e0b090095521003617486007030400035000c2001d5600021030103076540c0d92212141c03214400072234030030000780710030142000c00300105550001985411504508501920003803031610210041c08960880820f0b015142d41408034558004054140c0ea4000c07181042541746c00c181141d603c49200c901c0030340540002d5200641315a00c2c1d40a4002000040144c030030f451246000101120400d8105004618405414001d107421280f41e282c406d203140d680811625030362200281003030000405c000c03c006803840c04107400c503106c4e9011214840022f03005100703500d450600e40c0d00d510075403960000b1100985103421806800303044001e049420150003285030103515078114040d036005012600251245c1c040001d9240c0b01000206600e103e9540c00280310b00b0545059420700c11254001002c100030901d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 195105278 1250 195104028 195104069
    0x3081e0f0d05180a02060309030702030a0b090c19060f0c2a0b0a0e060a050d0504210503131407030b070c11010c0201021b0114030906160903171e0c16 66
    0x20441070880c2c04841700c03074aa548d40c401c800e16610402000135054042d03041d222003004805038803540107420314000d441c15a5a00b1062101040b012202c41c0484100000104882c901078051814641d8842c6425003c400c03007502c44c041154480404904603518002c00800c4a80d1204070740c402074640c0c1102c82d8585400c8490050682c200010050711031400010880a01400303001150014030540c0c8043c002c3c1d00d010f0a01d8465079541144d2802e020050503551861244110b048900c0764800801d80e4900a49a40703811002c80c2d4515258130140c403c80c2c20200202d031070b48944503c50741440c2ea40d060310820a00c0d21a000da02c4989181e81400350800354130b00140e8000c00c0f00d0381484402c0e40201c0a4050450040310080140102e1401d29200001445850940032a440340f20301814550b10041c8000420112803050365071102400080d08603010003030000074071005005038661071164000c203222240700c00c50b13652b00c44001c41540b1fa000c01c1982c2d2142007218005002408403445068038034410741e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 195106528 1250 195105278 195105283
    0x12080a0e0a081b06040e180105060315010311041d0304060201060b0c06040b04060204050402040306090c05090106050301030b04030e0907030e0606060f22091506020f0a03050403081e0f0d0518 84
    0x409030f104140d50303000c6000340c0d1315904281c078001c2501180107880c40c18002c49203981410340601d402840c0d400c002c0000e43e00d0900003030140254401588143c0036a1030344d100c1311509107800f0703101d0794040d0321000c000041c0320703c02c00039100814640700607564075881d255005e800c550060780300418201c0207101904000030b0100b041e55015400ca0308a1040d0394852820300c00030301c1140c1045601c03502c00704010052018550162101a1180f8044882c880d191003c0104d214024424103000480030401400014100c8030700c190801e11a08040c1e4801c0d80c020001a410702e422106c10002070350312032404115004c104103d5411040c1601c54903d001451204410548103041c04800d035903c1d5500ea9012000900308a680104064941046131004100302182a07440300c2c03107480010711504071030380c80d48100070568610859058561610301071071170b0355581e0381c0e070030040c4038490300e19910104a09904443d002041804200c0c04030555841030a58541c08560b4041c00022148415116080716075400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 195107778 1250 195106528 195106543
    0x20a181a090108070905091f0b0408030307050a0530100b091e060301060309120f05070b06040e060406020c07060905150304080d060e160f021b010912080a0e0a08 71
    0xa00e03103d002680d49080c1900c0c004250f90015400c44500010848001140321041c4c0618400b031100c00c55165403526910614020b50103004c040b6001000810300881c01100182007a0415040a50510002e15070381083c2042c82464508121124803020007490031000030315030f02006032500c0c80e00785c90900701c40c58403038010542d1060103880d85001ea90184201103000301d003840401401107950350386423134004015100d681411a14a40c80c1c40000c02a10300503140044008900e9454904140b155204e4420361000508140d400c07942e070f03241109c0041c0e02445100d100e240150300140e038030030012230101d1400301030794010310410800420901290b40c2d141410300c0700600141080d510390f12541440ca40368480c05184c50b600c01d2034940b00082020321881018440c1c1c01e003070142c214a40c80c800c03098032198422101800107030020305840341d40a0407180042c184c81d20624110f200f130360300c40c042d40955030100e00090340c00c60f07008520049030303035400b5010720304050054401c454010325010702c0c156241d02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 195109028 1250 195107778 195107797
    0x30a050601031a191802130609150c08070506040f110427060e030705011401090908090d14100219020715110123040b0a0605030c01051b01020a181a 65
    0x403c08501d0b41c60300c0c180310038030014003480c81c40c0c5080488807440482c000c0d40401e014644d1040c0040c40088c032907000395820400c94240d1000010803041c205011103c0b051002030480e5030840c10700410000c02c1e02001140e1080307104050309502c404441c203041c040e9901da03160300c91007a8100041144c505e003540100030400080c00c00f000203c01c00701c3c5401806003660503003c003d184400306445041c800150440d030009601c0700c40d40303031860740ca40c690035098801c048406000c0300e41c1046000382e41d0810040540110703024880e80794000902c840041e00300080c84410204158003c10b22882103481054000b50001c803d0004207196450300681000c0c03804034881d000103106200d0032105a03200e081d0400c5882040c2c0700c40d84041a074024280051284003990705903044100480010000f0002d4400c2109640f40140140400b03030100c1c0045820b907004c070340c0c070036840d50f056405200303240340900160038407843c43d40b5204010a4071030007140c1d0050203070f44100c0c110640541ca018510070000200c0b5003890 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 195110278 1250 195109028 195109039
    0xe030702040e0109140304061707080105060d0902220608062203110a030807120504021302090f0439090e0c070f1202100b09070e0a030c0902030a050601031a 69
    0x160b503400345a00400b402800909620789180d02c80b012120b0203c000c00c140d8420380c40701c510640b080c03e281040400d0417135143c004140410f0040c4001d28003000900490551480c1c0800e41040550100c0c600050548107030038054681000002607824500a00c4040c12820009008501d424040180b00810761400c450100d0380282041040c9882407921301610070351002101c846d001e8618000300034a00c12950a4006004c0242051000c0744601485000300c2e0002e00304110081d0201c1c580c0c009600001d07100e03901210105000d5459162800788140e4030321000c45404032200411802030b804a400002c1d11203c0c1a4003600c034a000390031803072a82c1581c1c124644003855507641c02068a4503c5641e00207401ca0152000b0b1034204901c041160310340300c0090b8280d80b03401e0000c0050b04251000d40107080e0b07001400d00c2c0003030003280c801c880350f4a040d803005010161603681c03a1115400710782c0c640c12802c40345400104000510b4100e0142541002080c6410071281000300c0d09080803a00000398070340b041c6e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 195111528 1250 195110278 195110291
    0x304050906060c030c0a02090105040b010f0809010e0a0f0506070804170708040e0a050106020106120804300809040c0e0f0405072a02030c01050c030d150f030305030703050108010e03070204 83
    0x2902c0320360030b55030240020340c212540d40c103040c00e0403030b40c5c1d0b1450b0008a100384403a0001184a08041c042d190a46206031030700360003559880000e54419100511030300842d0340c7d46624024624041003c80d46c0e0501503514000112010b04141741440401840801405071309014800000d643c03446200c140185900055290170b03461030441c885118691160030554585002e0002001551740b05604842c6650005c004c0190b4640a60740d0b00030303050340050000c1c102804104003010081c0142035088074620510f00d9030f103800707000c20318a1042c0b0369415104810086000e0145003418402c4d00c1c403103502400c100c001e58400310002026582c120120a005546403400b0a610324000c69684a401901004c1802c607800c1c2440c2050140c2c0544205901c0b0340b0403020540d8465006000311002998054003942ca01040041168040e101180701450304481050340098840c1844807800040e52007951903a58904054500a0590304180c20000803031340b400c203809004c2c401c004112400d030369042e107010808 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 195112778 1250 195111528 195111541
    0x6050a030b060301031b0f05060a05070516060f08061903030309061409010c1706010f0c080f0a03050a290d030905120102040303170112080f1306050d110c03040509 72
    0x2500401c03000e2074012001000200400c18a01c140d000c0e502251800386442c29910f01541000240f02c0c41201e8220100308404444c20748900000c00c103050064086513800c07100c030410140316801c240c0c440800100d2506401440541c8103926640060048035014900481d0100d035210398a490b01c001411706550710015020408a500980401e0307424035452103e0b413519121082c080c2c0388485921002842c0c000000302c2d144042c4884c1c40c0a0503069403804460300341d01070282c40c40000d241046d5600d40c028068030040b11b60b000c000317109100c41560085414140000380c0f0342610100e0403000301d00d078824a450205c1c84902100c85c041d0150440d220800c1c03298608085e60b0030340303058005640000007190540c00600c4150000e1040b60b203e503132110b041c2007440d00c4220010400f80581510040101c80d00004200510301070314070101038180091801c031100700c1007401c07900c0340e07070120010441c00300d0810094500d61152000c2c2c03aa00e034188918140d00340400da9284c1c4524010244181c8031500404c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 195114028 1250 195112778 195112781
    0xf0f0712020f1e0301060b0c01060602060417130305010216020414040302300d140105010c0b01050d02012001141b040e04051905071a0a0518030115120501060e0c0406050a03 76
    0x20030703c000380082060f2901e94a94000b1540700900c1500b1960a040b40064014030000e181c0b0f201d90342295017030310000340301d000b181519485100d01300607241d04c2c64000700114500b032000f42007050b65800e254031284628814042030790400010f070805405020f0400011a8011520481d00c1d030000300700041881c002e024036054040e07545003d94001102060540c008260755028546840043ca03241c5e0540c0e070703102c004581e441072003000103156a40c043c0c010005400c1c01d03854a40014414140744240703803c0c101489419078410240e81072503a450300c03400e01108180080c810b0304103103200603a802003e00389680c50410f02c254419034003c02a80c40014051000074090903a030f02400383d042074a00000c0342001e40e955041406020151240c4d81c04601c11121640120348404545840d403906148112141c0f03286071109103042030b010b54031003028200c1a50300d091006c01400b074a11814401103070b107040403801c5400030781003150102160760034040107010b81000d035070450f80e4916110703654031040c131011130 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 195115278 1250 195114028 195114079
    0x30e16080105040605100501020d03020c0114040609030806031b010c05030708040609080d2a02040b03031902100203100308031b030c030601020d140301050f0f030f0f0712020f 77
    0xa220405124000c80d0006040d081207018a00036a0705000c9074490790b4107858403040381c0c0b0036603000d82d21600c00b192110780250041c200000070040001907150303000e404c201d2500421101280c0e003540d06e0051004040c0c2241c01070350441419001001340301e0580c0b07580407000940d64043c5062080c12050681046010011208206d42c004146a00c85681d1800074110030404c1c05200864001c0080072500d440c030922490302c0d00a05030b0000c64200c031030348001c0c1c59424002c20040e07810544448025096403820402042002e11581e03003038001e0401034900904040083c804004e40780e00400c140100c1401c0074640e4002e403034200040b40d40c0c07502c8600310749010701000b000d0703d50403020220400039002680300280d8400c0600384c00380c94100c104c2843c21511003910382c05140540354240014815401d14074012941c4100203450000700e445c20723100207464504420403019003544003890000c81c071078042c0800c10082482003280701c00c90000b41c4c000340f042940704084501440b01d00c401021603036816442392 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 195116528 1250 195115278 195115303
    0x8190f090b0c0c1003140112020604090c05091905150306030d05210717011e06050901030b1203030402040e0a0b0a09021c1a10240203090a230402040302010c03030e 72
    0x9013074402d10ba02029000d014404403981c040840302c0d0001920b004901100a01c3d103034001e000034a01410490b02c1001002c507002040104007060003511410f407646030700450300340f04948010300c216140c41e0410102e200d00e00000d0b000e01c0428000d10540e6200081c07500d1114244c1d0401c5501d03000e0844500c0380b0f5140828000c070b80a0890000d015030036420103075440700c1c911600308108041c0e880b906403c3c10000582400c00a408440004105942c41000078208402d014075020070f41c640a130001031144040350b0207850064000109100452929104400d041d02c410406004401c0302c0c0e441d0041c1e03030000180903220745601c0b05108811035894400c104560f968892141030b10040a04080107500d480034401c0074844906000b0490808854064504071482c030400c0c00c00000e90315034140080d840c00d206040540c03100b8000d5044903600d101841001e043d0203814202d09812903400c0d00020584612003034050b80c07040200b4400350341e0203401a0303850742d0141404510308400505052a040c0000e158 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 195117778 1250 195116528 195116539
    0x120c020607080408070e0705091504080703050303090c0d021e010c0609081b03090d0f0f081204110105090a090b030a200307050a120f03170408190f090b0c0c 69
    0x5080800550201600c00d07550b40100b112178843e150603403602951011f4940c14003044040c8030540c3d0500d0010a0070941d44466001d4500b402d176251185072400d15103030405c440680001c82003040c100710030414248800c00c00c8a8502d0b2505598003c1602e02440c0c56600242002440018903030f81d00076100010302d40d41c170030020460b0340c031641088443c50f0058104003424041e800c818515051001040c1c41040308010a102c28100760360741d451641040e01e8608030b580300a1500034502142184010b86251245031149003400d241c20326086041c1c01041200c0c9041c09400e01001d4150b40382d4402c2c0c0030551312249c0c000101c0b42e141000103407074250728190040a4070b40c1c000708261413040d18a0380b951001c07826070454610300c1e00c074001c00c80c070801d80d40244c552400c4a940410045104407041068050190800c100001d0b22210754200000c400c032816100e4010000b10030000c440c10100034800c4586514040180309480c40c402003a40d6071910489030329030300c081140f0306109024041143c400b24000d00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 195119028 1250 195117778 195117787
    0xa020a020d030504140f0901092003040308040215040b0d0b1804080406121a0d03090e0f04210903080c12130e0f07020a030c030903150905010605040204080a120c0206 73
    0xb4001c04550081c0034035915080300c8861300c2910300302401040c15200b00145903a08aa013044001c500804500000388030984079a87e032110490f0080d8001d50086d4026500c1443c5032405005020341010740081d407820080e4100300400c80c1344580015504420b888450200e40740b9402c42c00140c102c44003154910515041030140000c200e5900c1c0180101c8407980c6038000845c3e15202c21100f2103100a07800c00d40b403084401c030710303640d403604031074515078680b090506002c4541c45d4150f80720010821030303541541002070010300091008074204c0c28460f0309100341d00220a0070003d001171800e106803000610780c08000c500d0400c1d0000c1806101c011102811029480700d4201c003010540032032600c0390011221600300421543d1180640c0680301c1e80c0250010a00d0946d41e9404441d00c02440c00164100f10010901000050319640b50904456203000c01054200c00d81c14024210380541d400b02c0e01c2a0710402c01041195008611605056045803045001d8124507106544e100c05071031000354030210020307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 195120278 1250 195119028 195119033
    0x20405250e040b0102010605030303010306091407080d0206060405041a04031e0801090c0801060c03050f131707080601060e0603091203010f0e01090c120203180d0906020c0d0b0c0a020a020d 83
    0x18605007540c0d50449061016904030001a400c85040c0d006240e0550010030060001ca2401e0708070340e03074081c8645508188025600d122506240780b5410030b0784582c0201d00d149104641c10008a90480c034200c9007041181081d07554607905444801d070380c098002c0c4c2040014140350140c03984910300300d89910415840001c9030300040504c0400d00501f65003510f403c804a060910031101241610392030380300d034184441c0755141a503d50b080b6900001c003c41d0204201d404807219096004014800c002c03201c00074140d800420744c01c0c4141c1e60010341640c0d004e200104a95a801602080503900540b200d9030759864081d100e50410325907002c40180b81c00d0000002402030222201c8004443c1d289003002e58690b00d41404100760f43c803201540c80001d03110f60b410016102c9903401903400a1008040640840d08102e1240c1000c002d01c0d04403000c0740d2903100411200d60188a007122841e000c85079525108001d5a81d02c034201c07405000400c0720800403034903812440c02001014081600102817080d6055140f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 195121528 1250 195120278 195120287
    0x2010f0216080a020a2c1005040f050a18120f1101050c0406020f071811070c0b09100207230109080f070f05030309130b0301090b04081e070f02040525 66
    0x2840c201d005066131710001403820441030003032002003081c0d11600c02c04000302082291a890150218007916030301800083c2c0740d65030b80f050701d281e030420140c082002e140005010040710394075040304254000d660b103071000260410038143c07400300c810b0130541184419184225020520ba03401c00c50706620f80720601501c10504000b600844502da4222620704240e404125141d8030f147c401c10031614010340d241060030384030f900501d8140900800700c9042c00f815841d80505c1c1021584880400c01d0006450051803c0c8101c44401200d00d60000346000c5190001c1d003035101002500901a07000c1c03200b140b207866841415031034014240c0004a032000411071300f8064580b03000b8418415003469084000032075090201c00d54172401301c010310380704c99031503c400d40d100a4610105584d606558581d4440006a82070400c1c6000f24010b045564880d40d09507459913920b50044801c44c40d00e403061044000003184034090b103068136811b9070040713499158800165a01a50b0059071812071111040898106511 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 195122778 1250 195121528 195121543
    0x150e0118060b030304060e01080601110d0905100309020904080d061a030f06010c0b1801110a03060503060604090b010b07082104260f09030307080c060106030f0203010e0402010f021608 81
    0x200001c1180180c200e08250f928416442001b021031749120050030590300500301c0c1036002906041800b0a8964080351038140800220001e010402c104818400da017000c800328100082641010000c1c5840c40c3c001964241009200074809800020742c00280180e9800a20007442003034040d11000c0e900c24000d000c2e94104840d42107d01000c0400a00c6ca584564507624001e604194500c00e0358513089040d0308440755524644900790b403684000c1d0700d48146200109400002c980e00041c3c09800e00381054281003014001920607820204540042243c0c5001e00781110845900d2959400c0180b80c542c603d400b841c0004020700344000340c0c13084100ca980b140c0b58412442400c074214aa038180d5034031080a029108001020041441326040e0310f034084d002002c8980005044074101044e03665500800d51040f08a0891500100010813001c0c0e01b5009481d0a940801d80039030940d03060101c00400038400820290400c070303110540b5070034503000740541d041d12500d1004208000ea21424600d5980e10b1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 195124028 1250 195122778 195122783
    0xc1314040c06120207120c140717011505031c14030103320c011b1712010602010504030e01051c0614010e0f0d02040e0f010603030206071d0904150e0118 67
    0x125800030501900c0303072003105d900a612191201021440580840d90520904401c45011006030b2500c40b0062081104100600800301030720740c407902c440e1041e4250703240d2042030716003200c6082c1f05000c140d40c04070300800300d480d5682d003154172418090411038400000481c0c0ea50741d94400030000c003e00c500d01040780c000044600c80e0000007800b044401c020300c003e407038041945410410450703000e588078030a00c008140c0c0e14038a498025080e6140e403414454945150704007070b40300160708180e050300c50071600e0040c04180004c0101d446d01d6103018003030700c00e11058a81005000111440781d0300182401000410003200100881c0d9200c00500041d510350080c403e01113000350980703a01501e0980021601c1e10005040758100d104640c0c20700004c1e08032054a10224050403c0d8148411024030604000303502135801000e4070306028501a2142d131121001230701c81c0382020007403080b94840d05100c075003255000c00f060500315480004403004100d000c807005059401d003414000584c13204640c4203001130 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 195125278 1250 195124028 195124037
    0x1c020c16060206040b010611072606070c0b010902030403050d0903020a21170405010905060c03011d0402060307120b060d090c0f0f06030b0d080a03090b16020c1314040c06 75
    0x29122207060340c1c1c0c0d88084800901450b800300040c480c0b1440744940c0e541305550901141e2000c1d4440c0103070407402c1200c5407040f220766a0002c010401035410007000da0844607506240b05000890346405818000500911900c1741c0c0000c007103400c042c890411100790320340d125010000c00c0c032186402529100742000550f40700130842c40040405007002400c0c9030b01d09540d21f968a80c810000b2403000140c01c0140140c032a13561701c00c0b54101256090024600c108402006941e03070390f0412880360120100e0408250130034040c0c208200050f10381204980e008403403403c04203c06030b00d54100c13a01802d0003c10031030304803c2c045902007450186130403d02d8050300c03c0c2011081a522440c204003800c0766440350188001150300c01f004054001d900070090510081c140300711604003a15865499488250410b002a0741c07048184288800c0c044540e8000c000141c449401d003d50510081d642d04485d000d4034401c540c1c14060043c1001154003e04601c01204014440b6140a00700f1000b034500f03074032601c40403d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 195126528 1250 195125278 195125323
    0x30f0209060a0e0303161a0906131b180617010c17090c06160b061503011424030108100c0210090201030f060b0c0c010314010b1c020c 59
    0x11a00030385140250141c005400d000c900c060031941c0014030492030340c05000400218101c0d5244a010041080c0200c9074041c1d41c0d01d40503600502104003e0410001d80c00107424885118185919207006907003014804201c1d0017851400030900135140d0041580303e0561301d0341c40e0318142540140c001c5490b42c0d6141614003a6800d01d1780e0a85104400d0040040c8040c0c621095070004605150303006001c81040f42e84240182c0301140c200c2d80404540102c0d510440321460402a03086810356000e0000c0d10300d5002c007407217814000914001801003010385a0041c0010b046521a24000600d401d0309010001011818841c68078060f8400e028210f146e00440d40030450340c1d20a80078413100840c06034018520813210b00c04040051180c050100c0c101601c3e222107040710740c000d01442d00944541090a40c3c2c418403450303080c0c500700d1381c1180d0078180f41c10081015204503215110030304550060f40308541e0f5a40c0c64011080d5140c89443c80400340c1e1003c1164000b1260019400200100b52011610103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 195127778 1250 195126528 195126551
    0x20d0201061d1602031e040f05041a15161b060516080a2001050106030513021302030903121f0f0b0a0e010306090c02010221010f210215090103 63
    0x540030b89060051481d06400110304141e078030320011048405940706036401d10760800031005850214090f842c0781407a0129050001ca5a01d109104c014081102c0401c031290900c0c1c0403001d6184e1881c441440340700f80062407941002a0404c4074a04101107d00c0c2042c00b01e0b030f2400060f00348a000449a041e4000300340030030050f004001302c8a03101e922016000720a0100d0751540f00c268412005a81000314240c148954a6114615000b88410303000001c541c0f176051000090444400420000c800c03c080103182c409030712030408001d0041201180580e407603075a00103052561180c0c501c51410184441c0400481049540a208482e8035080442071f030251355580304c0341d10702c016000b4240810000c1000c150b0250003040b40c03505a59041c10041045641c46107440700711042c40c4100310150f500083c003141d0b0382c02e20800d10b80d048a1281d5800101d94109680c3c50011451409504c00c48017107645100444000e641170400b203035500500e100307800411105c603a2445d801ca00d007a01d01103030078880c0c0c3d40765 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 195129028 1250 195127778 195127799
    0xa120306082407050901080c03070201060f06051902010203061011011104230103050c040e15060f04180207050c010c140d0903060b04050105010f0507030302040f1e0603020c0304030212010e010c020d020106 90
    0x30301c017005039203050b415154000071001540c030140441096640e2440001880c1c1000003410300202003944030036403a6a5105007803e01e80c5400001c820441e4030400411280d07641e1007101c12003540a62a20760300c252240180c00b8010300c80d01c560f00c0c1041b2004a0300052649840740100051b480014400603000c0025005400b5204195040101254280414810004074281d025442400104203c075083c94910200300b9560149401d40048100020305201c2d03500710300e905180d00080380c10304600d4082103496080c1c41e503994a03101410400c80c500c0c0c45040c09540d148000a80c03070204d050b01c0285400e02e002510b0301945202c1225810f0170a10100359614103881014125401070319400380d080c0c000030040342c0551141000b02c0c10306500303110114054034914004406007a15280300100a281001c201800d00d109030301c940b0406004101000e0b07610004001da0f012030742d041d100c4010322a003d80605003d485c0e003220701c440540c40c14005c1164240d0001d050540090150001c0000d240c4884a550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 195130278 1250 195129028 195129037
    0xa0806060d02100302090d0c080c0f0a03030311040803040b07032a030e0d060e0a03020f0a0c060e0a0e09070501090b090102060402090c04030b0c12010609080a12030608240705 77
    0xa074001412180100542400300c00708001c0405454010710780040c06001500584010009031156043e80c10140801c060030000030030365120442e0002c03c03e04031840000e07500700b95030000504054035a480700c90412080001e0701c5c044c11122095940311a00c47e803007440e4a821500045c4c000504c840303044541d03110841b481d0080032170100140841c0c2080b41c4c80c15140c1c031441c68442900044840203e002050003446502c50721160300014190001c03641c10300034540404101900c8940d0000240794000442a02d41e200844076103042c00c503a00c0110030001851542290b0000408024090401003860008504081070300d4091700c07500711a5440e040207000601503090141c0c0540d1024001c02c02500d00720100715030015030524803070710381a12503840108a5109860003141e02e01c02007816400300c42c07090500e40c058046403801e08440b41c501409140d440348005000382c40c4464a50408082c0c46c400e40129003d040c2c82e10850b260a2450101d0b110201c00700c07100042111400e5021981481c801d10855 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 195131528 1250 195130278 195130291
    0x40b0c03090c010c15020c0307050f0133050907030509011116030507020a080a0f050111030f040f0f12090807091406120a02131a0a03080d020c010608060103050703020a0806 76
    0x4014050b0103000540743da006600f426103800d07480e10184030030086680000d08016460030040c6440f036080b854118588041c0c9444164035074140700c084842c4070f980521401040900d003c8a91080b0352044000380b4040c010b03040785400910450820540301e805800541c01404268000c000c5a18124641c410302d0007400701c01542c2e03800f500d4410780801d10130b2015003001d43c0010180030340721b907171100c07407510b805400c0ca0116503d1101f60000c5c018081e0070f101d05803208500034152482c510301581500d21000d00184028819900e030402030b003e011150340c0801081c2d60242901d0704911240b44041c0518049114074001442182e00c04181c5502c2805440407400a2901194040d201d5108100034000b801c14600307014810b000422025030358942d01c0386c00042c000d510002d220349000d0021a240c00c40504280c0c003d20580d0400c00009a0728002c0321884252400c0040e11250001f844a004d0031090b48244070340d1182d64008024001c01140d080100c81c801c0301d848080b15a80c580c080d0301d855044400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 195132778 1250 195131528 195131533
    0xb090c01021f02130906030c080709050103110105070501020c0706030b1201060e06120f070308030703060503030c070905100f0e01170615130603020919050601020a080706020d140a0203040b0c0309 86
    0xc2e0301c5910203d4025262a82081c2c0001c03420a132242c40000440c2c005500c15504494203540401201c441804000058112040306000a605546802906560395140141040400514503040c0718080d41540c142e040c07035800b0303034001c180c0e03600c0700038090f1032401011845803000809800c0c02e0340c81403081d00101c0d101d03d420920155500c03000c2000d80c01c0309400e080d05038028489255030184090140501a5101d00b06072a200d0800480003012202c01e034201601952042068440c40d40c030014003001100d50304040451250341d80404502c0856465201c802c020302c060750045414006c015800c0d0580340d06d40d1079080c0004208400031b40d50076045d62004c010200c442c40c02495402d0501c00b42444954560010560b9642c03680882c10140c0d0840e484560394225a00800181c0f601e40034076a0002c3c42480100200e00c030301c0d1160400d070b2141e00401845140c0c0007561036030610494000300c941d100b00c400144241d29096651902030360085030115910503104002400a00c81101660b02490b0800700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 195134028 1250 195132778 195132823
    0xc0f0513030f050727060f080a11010e0406030302250f140105190305040c15090509060a1a0705010507021203070804060b061908150105031b040801090b090c0102 71
    0x100c9070809000054290f5003401380090102c0e601a601c1d0042a4003c1c024030b81c54021114002000e00f26032041e00205120340c9240010014090b0000745031411513002140f0380820302c40d000c010b0b0762a140300e02c441c40c0c00030304100000041c1500420300401002c0348c2d440031480010138a05401000107a80208580e1107035442080c0700c2005a0341a0410100d01810300e146800d40080102d1009526541a03e0001ba1180100700030000310082000090200f4103409042100512000d803504420740182405110785030002121995400103880041400941a100e5a48030800b0058aa8840d0070280c941d5800e00c004910028400240e4560040030031a01604645981004652500b40600252090380c0c0342e01c0404d445903500c80040899800c1520313414524103148001034a0554018403d41c2c030f81013055011501d0380d800c0000c6940c86580100080c12131020108e40d00391034001d6801c00390003507103040550010030514801003801059004200c54640103500012a034a071b1300d5044100c0280350005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 195135278 1250 195134028 195134033
    0x302040b0909151f260d050d0c020313080105040317071205040f200109140d060b01170408070b0a0b010f030e1203090a0b07080408040b1c0207060c0f051303 69
    0x212035a030418a8401144440131840028101102e26074026a2511502c1e14000755020801050103c8400c00c5002a10602c029504003602a010315800c036014291503008590015100348103c0d038420901095110140752518180381c001c081c21502140818004058070104101d0301d94100e1040450b0f61b10a40c9070760b00404000068100540101d4811f404222034500050b0101c059441d40c0180c05081044180404001000702e50b081e8028940e44401b980c030203100e074407070f00740d00400550000e1001c117034008810b0040b1202404100b01a42e080720150501003006000300003482a14090b403010105520b9103080f030800c61f1903030309505012410404003403280d54043d4000c03021083c43c0d04282e8007089a00800001a40d00895566005400c0000c40c0b41c2000a14142940c01034140d18001c0c00f18074081e500c2426500c40c0c3e0248141010010446014941104141c0c144200103c1d40954540c110b915000c00034084a210240124074074840c50801140b01d842a0ba5100f0782c000d4040b10b4861454 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 195136528 1250 195135278 195135313
    0x211c020f0307031209082b0c090e060102030708040618050402030108030901180807060302090405130f0f1110030b04061a0717070206070308010306060806040b0115020c03160302040b0909 82
    0xa00c4d031000341c2c039115107100d000310340100040c2219911144a507100b09006110704040e00c0d6002400d1300540c1e00e41080d000d21648d2248460056800e24480169651210001030345580100302d03004144440004010415591149082000056007650440d4a03500d034000c0000f0f0780001d001e400d10aa206002494580d881012541341d03680c104188006000e80764604641420126045800070a800080760710b51030506214550780f01c00c1000c103041030310200e40d0f1030340c021600400c405402c001036024444e040c000c1010f50076904c054001c001c01c20446e44420040c001c0c00100805510541c9401c10000b14000060f6100b4034240004150780d1501400d40c1ea1180081c581c5500d41948500900003040140c8502c0014000a806500c0b640c030550314510380301b0142c8031550011006a0080028400050301304c0c0c6405041d10b02070301c002d4a0310600c96108a1404a0f84003c041d4184071700460000100050904442a80e00985042c00014082001d1110090f01512440d05030b500ad40307540c08116145 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 195137778 1250 195136528 195136547
    0x61e0203030714280c021809031b1005070f030c0e090c07031b081e07020603070503070c051507030f02071505130b04151b0801090506211c020f030703 66
    0x600014003600d0301d148045903c03101000800012170800b08207401545440c5440d003400c00e0101c540c1d42524904006560703201e0042c07400346500102504507008d1040310900c184035121100400812243c03400f0798008241340043c9902501291616480c4414940310b64011520008090145a040e48039023840b10080d44c041a4182c0800c230b4182180300c1c4812003c0741712131000c0c1c01036140c90f0b202c10311003c0c030f464224442c0405541d0480c04221103c01615100b055a0b407107030030390800ca0b40381e946d640403c0d03900d80e6036000000c0940c00740c0482482440390314440390b4040d911541c0c003009001280301d070b07071000c0348030700b0384083d02c10740403060f02c0c1000380d2641c0c122541c080810700082ea0907c0711569107400204c0e0a9400320f0308403540188422407a0004e201d0007005001c51140300c081300170400307406400c5000c10b010b9641c45031344950000f031050b122203c00c0b5190f0f05d685d8502e0f410711000f0942e1316031600e000201c1106408a203280040005100143d982c01745080700000e980740c01020f540a03a600c141 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 195139028 1250 195137778 195137797
    0x509060708070215270d140304060b03010509010f1b0206040210090506031e06040204050d060902151611011106010b0d1d0c1503100303030b060c0304061e0203030714 73
    0x1500004001c4860860052170080030a00e0811482d1881805c0300350007425090411540781c0e00000d21203070156885000d40c681070000300e0000795a5140c0342400d070064011110070a40540c00d040605c03041c2c400543c408191880003440400c1155101249510340c0c0d0404c2029000603840398000c1000f618220031001c4096a82d82480e1000c10380d02d0010808c25082180e00110b000c445908215003001c07030031201ea41c0200f0403241140742908040008803007403115200607103003696411180b41151101d01408800300c0b0782e030350035940f00c401c9101501815118800f00701c646000801045123170307502981c1303105161400d600203889141e00703021441c6000c1e0445031070000301e00d8076441d15409024a21a0002009905c9005800140200c1c0180540600c806050a40c440300820400103501101d40f1001c00303403a41864049814405000028000d02915003101240e000000300001d10070f40000940c5014035121640c2540e04d941803e080ea100d003c22507103030020890000c03c2c4010784035034200034058802c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 195140278 1250 195139028 195139033
    0xc0312060d0204060602070303230d0c090b0f091c0b04020105071106040e0a0513120c05030702040203010f0806130803010e1e010303080907050a030f0209060a270e0105090607080702 80
    0x25260300040c00343c4079191701c1800540c00c0542e00340141544402e40e0120010701081901044003c081c0c09170b540e00c0352403510100c3c141c0d03400700030b04601d1040442e00c0080400c01b601944400c1c49211140042d03010700c01e170b80c1c465503070710100c1e03191031001240b0720440a030000600030f01c40c0e40b00d40041d201503200402c12251245000511000c5035a081c0c06000a00301400f00d0821078540035135024203c1c6c401401462501c0310452081c00020480c00244103e1131852519400b4602c507031a05c9072960046401c000c3d40a030001c4001300c1e00380b80088424040360802c0302103030210303100c00c80c1000044d8950a009001c00c4000c10040c4803900b030b04030b540d07034108011707881c3c20a610911254452242100f80c00c1180000d070309005200e030003007007000381101600d412a45010388924550f618111404d18840080c01580780170000f03001c40c1d481d0b0300d00c10014051000303100c01146208440340c441d20325400030b24800a1074142c0020003284148030701072080d109071004201c1c90702c1c1c0ca00b041d5400c1100426070000c52 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 195141528 1250 195140278 195140299
    0x60a0911040803030a090309120b0a0c031118030105010e0106121e02070f020102060c1c0c2313090506130906230103120203070b01090207020a0320010e060c031206 72
    0x10b450402c000d40c4130700356090f0b0000b00c00c09140350081240016910a584101c240d41000020581010b00c20340c208001c11000102c0703099584055000d8000e008a150301d61201040b1140201c0c80c180241500d00c0e03045000300b18583e01c415020039030000030f0107558001040402041085040e07940110580000d8814450b1540b0382c0c10000010b0303900080c0c0403968080d885038010f0031941c0401072240c00110124089050012058035082c80003061403500140c10f8031650003980f00c81c0503407a041030300c02e1100c4050a500840810f9807220b64001d9241c110100e1128800083c82c80140c4142070041030010f10101584560000c05e10140c0255001900c499599410440d0010300c16a20981901011001d400241d851400e0120300580e400c030414003990030421078000000c030158036441c10750703640342c40058503610140081294002e054100034580500602444840e00d60035540e6104a00240d8030708455400100030b0016600925100395880e03403013400300304401d082c0031900660020001e081c60844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 195142778 1250 195141528 195141539
    0x81c02030c190302031e0a0e15010305060a0903320408070504060b070203071a04031b0905060427080702040c0302070b090a020d0b0405340e060a091104 67
    0x40340d20558003900d403078000080044801980c034000303450510150078114110301d0581002106003020300400d060b0011000001850700685a20440e10403903c0310464110082503071110010743c80a010a48080c40784c1d800142400d0f49030300a0306172940e85651034640146040b02d030b81c03640400780c00d25020610f07018045a00d850541401400040500c44003c02121b440c10081c80210391885c0c000061503a0100310b0000561000661402254a8135201e09100038254007005424040d03070f0001080000c007159208612040c105808003a1241e12030100300e0f9459540c01c0000325600c0c0c2039440350541d0b40ca521420303028003a07804890000d0140d08070310b140c1071817640001e048031501500000403030390101d08003050008107085503a2080c41d190043c0040c04551f00041e007005050f040c01080110003500103010024184200c091001c529a1004800d044a1003180b011400f00c03540b9807070180500200084100108990901070700c4090b00c2a480c0c0c508290800d400f400000007010350114041100003031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 195143884 1106 195142778 195142781
    0x20f03012c0c040302270411010212070501090b0106090f140d060903020616030623061908071b050d0e031908190912081c 54
    0x1035052049060410001d0800c40c1248078103420000d1142d84440d0700060400d0301d03c2200c0b6184400c04100c180d5098541c200820f94540d54440c0c08039010509801501548603010710664500c11b01d103001c04a0b640d4041c01e001c4034182e5450700654103100300f20110320b014204034a80b00403001d1400450075a03030705a40c003403614111700303e520200e840e5030b0710100340d00c01d1980028148081c91290501075155281101c214000c0040c07108401e540074480e00c0b40006885004010b100120440c10000b190704a02190309900030008116041121166044500300500c9587d030300c0388180382c10803004001041c0501011400303c0c00c0c3c0c400e40700203800481c800050080f02d2920603d001c81c40700000b4504407244204140c0800008542024411013200404141e04100513070201c0c03081e81e42c8210341c901c0c864410700715088049020a400182007000511112034100c004860f4031000200220 = true := by decide +kernel

theorem cover : BRFrame.Cov 194964028 195143884 := by
  have h0 := BRFrame.cov_init 194964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 194964028 ≤ n) (h2 : n < 195143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
