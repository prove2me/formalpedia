-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0499
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:07:15.561455+00:00
-- url     : https://prove2.me/submissions/989b8837-86d5-4e90-a51d-ff981bd772be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 89568346 ≤ n < 89748202 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 89569596 1250 89568346 89568377
    0x308070b1008060f1e0405160915150c020d0c03110907051c020c0304080c090c03060307060804060b0a0e04111516050109020307030c0e0c070f08070c05090c0406 71
    0x25403004440c000c0000f083c0d19201d014001d0790742074000d0311441c070f425040c05c846002e100c2e07144106805a442031000b00b002c00c04c800594603032460150082c5941d6030801c5040b00c8040048032000303080e54840c121166604100342c1007a168007080c810300a4001442d40d04420602100c05506c20403203010f8030481c0f00d014042c10402038904022140980414818402080c0401000c203000c00300381c4a91a00600c2c00021701c4203a451600507921020895104c0d2032100c005040000441d03030070666881d003080c103504025001030344880740790080c6410000f0400014050280c25042040025409407004540f940c503002000c141150484040c2ca2400b841c400c00700007810f0502c2c7c1a40d27a50118000b132414007890004454000710810415907003507480c2c406482c0941d07400d0005000640c421761a9280d554075180408600c4100180310482d511024820000030560100d544040203a0101c1c640780d55030382500c1c01801041e480d40205800030308280400c0340ca000290010b0054130407a0f200e01c507001c0d51500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 89570846 1250 89569596 89569621
    0xe0a1505160518190b0c0c0307080d0f0e0901030f060c0f050d0b030705030102030a14090a150902060c010c0525050c10050d050702060612011418070905010308070b 72
    0x90300001d0b1080006100360a0600a10b90f034034940240b00d0f240000e040c02c4080c040031840c2d04001200c0d4800200560400810040c40061000a1f000b50640ca45850711880d11a460720400d10140041503261100140c030490307841120b0000148800740f11350f105d05100103031943d11a41254518035196071006901c0c01041c9540c400550b0340c1c3c480b45407082d1005020b01400c0e000d09855054810050b0104182c0e50a00103584290458000000e5245d00d10005096070100500707031400c150820700c6040045424100011404441e41d00d000c103140e40701d4800703d03c0c584507003441020b041d480c04446500300769202d00200401d00145001d105a80b4491650700b0070324030300306c0c8010b0842e880300742c448105081500341405200803600b00b4604080003c100c1000740c070012174404005802207800c0010340e2800d03580595402031401b008101a0314000c455900807140682000d41a55400d56503241d108800c2040201400da400c405101d5540e6030f00d00110b035030b0060641110003504100000d40603d000b1f1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 89572096 1250 89570846 89570881
    0xe07020114160207270b01050301030305040317090d030c0308100f03020405180d0f090609062003040503030f0702040f020f040306020307091505090a090c05070311010e0a1505 77
    0x88038a208107071035082400607640b41c80d04518082d4025070301c00045c0c0c41040e50b801c1c03440c4138240800301c00203802005c03030104896442040c14103100041c0b005001080d4030000781c40136213030300c5030654640c80c2e9902802029805041c2502d64028a248848410150312400c1240403502c00d44400d40a82c45441081014001902992020f41040c80c0108058a001e800c07151700800c60442d03500f0001c8850f8456400d0869580c443c2000c540c007100c1d50503a49601c00f400b10000e1202e480c01d004140c5c1072800061200358a4400308820803807245040300900414422a00103050083c1142c2d0756065080d80c42e8600d030132100d4182d215514100b46c0c09907401c81c900031501441c00100c02035180c85d0569131588003d40003e006902002208900807508440007002d0304a0740080307480701511030b5245c000300035198070103410894030329081055007046140c0000684413415490b06103440c4400c901c4210714014070f494006c0103102d02c2820603850600600c01d4815804205c03110050200d542c0e003092040c0700c03a848 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 89573346 1250 89572096 89572121
    0x31b020f0f1c0302090d300206061804021f09080c030c0105160303020c03030a050a0e0c03190303110a08100807050d02060c030d0501140319020603161b0c0e070201 72
    0x246001002c0d200740d00508500800800c002032075002901c92081e1001484060b51509181301030010890542c483c045540010345d10091405141020100782402c05c0440394540740d2040724041340441d81c5071894003200c0e40422041c254078070302e1090028020402803285000502801040084070305001c0b68a96003084183c641600e0405950610f403881c0302c20340020b408051b07091141c604d1024080c00158042d501604001c0740c3d505000d144a002c50b80b102440078800d034016401014a91804a0510100f545c2e400030300c8090041420241d0190034140c1d071303c2154800c00600c0495607500540d8840c002e003500300b1a400040e032980642c032f84d60803003402466448071641185000501c0c10340020726880b4003080940c1c0c100809180e121044c1d400c09e03040760b00420340b013060340141410204403c440804008090a685501c1d64000ca0f015110190107600c49010080031000321900684409034486403201081c01d10241078281601600e181d030151a00303140c92100401d0b0120300c140140760385680c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 89574596 1250 89573346 89573383
    0x203071403060916140f2a060a021602061201080f0d02071203030f140105120d1202070807051b040609050f06010c02010201060506041d06031c03050403031b020f0f 72
    0x44006501e00000080441d00081288003001c50000044400280211b40040c404d00e549803619100c000f51010030140490000f0108801303405802c4030005100b81d00103500030001a42c0365080441000c100b4800c01d4040d40000c40014801000120f444c0b160b412102250151030f0400311000784140c68800b0a940d1f41c0060380011000c5c84503107034880d6070342c0c00b162080c1400107400303040809210903940c0601e542e86011801000400040c28102c03071460303104000c680601284484010003030b244044086c60b40350b44541c046400001c1203402e04c11500d24517005070860300c3e8402d408401c209242140c1c0020fa00840c00d11030700083d1510301e40600c41c020030b001c0c0601103507039449400440d6114803400090b4115900d40310005556112100148080c0811495841c0451250b08108160013005403c4034040d0740410780c4400303c582c00150520f07034840103280124071900d59040c01c4000e4a08000300c142c18040f10140410034680000304c05d5002d01c006000c1e51519a4aa0034968540c0b0440761b80b61511075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 89575846 1250 89574596 89574601
    0xa021902060f12340806030307120e01020606040e0703030e0a0906080303151021060902030108030403061d030307230a0804050d030e1e011404030c0519031704020303091302030714030609 82
    0x10300031743c2d1791580b180010f0120780c00e0a4007030301d4540c3c607290b0361450080801c10040401100b07507418446c084d4840700984040c0120362600405983d40d208611001c0c04102c450064410305550342002480181f0034100e0074800030344c4990301651a40e0090720b03880cad9200c05a112070354079814a02e070500044046038441030883c030301070440c3c14580401400d1004119036185c0000c54016400e10245010b0502c0a0003181c58a00354546801140d4405012402d043c20302036540382111000011260f00000501e08900110380c400194081a60b080310000d28111020a20741d400750740c040c81151046000708201d812007071b1004815812225052900d240ba5048040828801200054840c1d61014410000517600c00220280c55160388246c404074000b81c106001e0109001c0d0070094621145148514100c04e01c00d26034000e001c0d02c0300d4121810320100c242c4000b5003035503428815a00700c0c1d8805010010f40041807000d42d0f000798822039490000c50b2903010034442d00400c010aa0340700c1d410280c2082c2c04c03034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 89577096 1250 89575846 89575951
    0x4080706110703031b050a030905100201020403080d0c05070501020406020309041b0903231f0e1209190513090b0a09050309090603010b150409050c0a021902060f12 72
    0x210070718241085055041d101c400005181017200c0702c7d0050080d40d40c500710908080c04c03c040142122640320443e0300611045c000301d010102102c00a0809010000e07032000c039074100b9901c47c01200740c007829a501c0400c00242071a00800202a2800100d90030014512001b454815480907013440500141030b02006000080d500c1411a0041c21110b09000003045200c101c80c0c6841c1e41e1f4980110098052103091002d21024022a406d840807400038144100105007001c04038007800102501c10803012002c00305656510109002030040a0707d0b500e4000b8400c1c0c0e0860181907a000221030240d225030000300703040760610640c0d925a070b000380610310b4401400c0404c100c00e00d001c0d0000e5415503030344046000581c0c030f1010000d83c5000c40f010494403103242881d01421030700024404114028100f01c04460315901245185020180b407406070324803007881c0041407060080c1c0d1045001c042c00065003003280c5150303001c3d05214600d0107c80b0b5652003a004c40b00c0c00c0d0a2500d2100c011048030122006524 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 89578346 1250 89577096 89577107
    0x8010f0e210f0403080c01050a02030f040321020d02030403020705010305070914120f100e070303080708041104060b0702030105010504090b060d0809090a020702040e07030b15011808030408070611070303 89
    0x1000c1d03000011030a00b035146001031200d50066100311180000007a000d01c15800c207008450380302000010460440c6411b00c4a1440840000c200404022180c0e0405000c01d072598000c02100010010071911500348202080003940195002d8002d0f214224000681350322034000d05d4480c1f441d03a40c402840d40c0c41c106010015a60402e105580021100764082d03403c6020880100940305400003407081200c600300d042c0c1100c131480c1040070390743c200e440f051000c030f90410b4103580c104030186042c10032580c641c20042c02d1f50030b0303a004403940f05041c000c000607508181c10262044a00031030013001240d0740e4000700001c4941d00380c802014a1200400181285400d5545241003030203020b080d40740408000018178840421102040c19070307030105e03015066040c54424101c603500400f004104407400c54541c4e0884e410018001da039408022001114664482d80d0102001c0710701214032208a03031104541034482e0480c2c010112303d0310a8400020b41d1a02c18252803024003a0322000d0400d841c02c54400712007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 89579596 1250 89578346 89578393
    0xd050718081f0209030102030c130e070804080304020f0a0b03060a09050f070e0a031a0103060506090601080a0e0a0b040818030a0305070206160f0b01050112091509050a0b04030908010f0e 82
    0xb4641e6091080c00b160b900c1c2070006520a1900e03000d41581d0740601d0780310403c1010150011140b5210901c2002401c0381c1224805400c80d821588142e00c82c1e80728070001c0c020001c0603850503005080ea9400062502c20f05000e90b014601c02c44d062a101500c900c401411030740c003107a00c8544001d2020108403a140500d02400410a0203801141c810f41c07a600d036900b081c1d10015603070160305030b07007401041030016900c81c9079041002151885080c0c1021030000305a1b040190651001135603400c04610540c02c10460180c5681e80118148907070b1034a4107120300d2a0b000b984000421020417840a00c00d4500400c0c49540310342d040c0c86080c1420655020f0290b070343c01021200b00b0b0f00c1034190205021610498045140504c60710410f5004e40c107020004065403001c00035001d6041c101000340000030042200c03856446c80c0c0700d6000070380a0369400c00d00d2914000c0c0d20003400d000f05803001e11081c50382c419421170a5030005002440783d40d90200c5440b0485040580290403a0415510349543c038000800082 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 89580846 1250 89579596 89579653
    0xe06070c15140f0304260901030e012c070509220503040f1211010201060b0f0d060506030907140102030304030504140a08102007081b120d05071808 65
    0x2201c04a0102000460b403082c203651480102c048100030400c542501c46d071581141c2e90004801070907000105407554040c101070715040c9601c0b00b07184131600009601204411509240c540d081e0300d01100f8140e400300c00130f1980301c0503000784c140200e07003403c0074540640a0403c008420408189c200300301c6101d08509441200c640c0400c00c00000c01ca01d0240911000c1c050a140081c1007809625160740d0399194034240d03e042d641801d0b010445907940000350f8500d80780c043c1c0c1d100c0d641d489590490340100300580203540d01110100c1030040e601c000140040944200d5007440c0c1d51201207100690781c17404100c070f0081c0010700800c41803081d1361036188050300f10a070241c8180100350300d23280c0c040d00b002c10051140004a550340980d2041003a40040c7c2500c0d810340500852030407005480301c5c2120301c107000c0c00c0503070341400c4081c0c88103400303081182100c00b00031140059121440000321234058001511030a0004074640902e4040c02c2484081108031401e03407008140380d284032582650302440b032002c0803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 89582096 1250 89580846 89580857
    0x310605250201022d01140a0507030b010e060f090301090803010e010b0403110105301902040503100c0c060f0b0f061207031109090103050c10090303050306010c020f06190e06070c15 79
    0x1442402406a4558400102400b01007807421f450b04100325038004280604150420000d412684d80100c3c500614000941e0b005554101c11071100300213100f608042605586405038078018440705c81c0c041c40c160766034000c031012280d9844850507a640503c0c040a0510450082122565030041c0d00134082214040710300020712083d8003a010046601d08400d081e080003280c1008401d9070340221304d11003d080300604500701030405002c41c0e9103107080842480140d560380c011440325400344116000941d03000c0004c0c05204c22212014001d060015041d40c0070b0881072001c0001441c200c1c003920102415045103101c81d559a4100300d010341201c6034a00300c940c004204800c1e00e5103400380f8041c060340c00b1308018100d0410039014403c1d0341c41c0f4001890104400d0080c18000a50b00504603a0001024030700744800c91340d50b000241c50007403648541d5a100c40c0000d41d00400070131158030300204001588840c0244003c0000344a0710384100c12000702061200d6000f072000c0c0e2048201c603280078150b40f901 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 89583346 1250 89582096 89582173
    0x303170a0e0613031e0c12030b06070302030702040b040603020d0204050604060801020f09030d08070903060b0307050d11040c0908070b07060f020301120b060a060531060525020102 79
    0xa03030a0000c140c031804004281c00702030b1418542c0242d00003071203007030305a1803010b4014045c0c0c00070030420f07800000a0014100a403072010300d61107a04010603400c4000c2c00156200411714010b0343e2584130311401c0740a1030601c66480443e28140c0300310000c50b43c014001614105190707003080010100200000da02595603400403540c01400d101600b10014402d6007035559502550030103146c070000c0e0803107100308142c410421001a5004040800700e0303500c9440441c09490310340002e030400540390031890308042c2d080d0032001402030481052312a52425070b0104110903281000316401030403070140c03c4040d03004013410404000c0600003030a44500038a80081c41c403400700790041c143d034004c0e4030107040f0b400ca081030281031200d040310903900200f048402810301c520700354026100d40103021022150700400c5581400100d255000542003240c803481c02070104d80c0b2408080c0850b0090038444501803a45051000104448010404400c1d0140c004002e110610400c0f410307404450340c075442079099288074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 89584596 1250 89583346 89583371
    0x90608030406051b0a0b130605060d0206301018050421050702040e0a0203100e07050d020f0d0302030c0706030e0709020f040312020106030b0906160807090f0b03010f0e010303170a 79
    0x4995000e0000c0741000d2147c001d0b82d00304101911000341155100d945880500303001a038030f42044072408000e24403e180807280d1303001c040590507003044030800441060420485440510f51030304003902c0ba000f208140c4100c44200950071030310200c9000700003418200160340c2401e641c540a9034540c2052030014034144540e0301141c20340390190f440f05050350004a0304011132500340405682d9a4034403000304004207541c0320013561032416101e440d0003000c2c6010100195220001c4000c449400505141000031507450003d54980c85414504401d005114011481c54428020344001c1c480110007040e0326814036222030029030140100b010f40440070000003001030711444210900d240d82c0d400010b401c07072440c2041600c2c205d0080000040d90040410003284030310440d81600c058280e031070a0505d80c0d079110000d0f6041c03000c94000c0441482d8856000603000c031501c00550603210800040040c9555404040b60258000c3c04002c0200300c5a50308103034862401034580341e0000d00361102241c644010017 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 89585846 1250 89584596 89584613
    0x2190f0e09100f08160e0c0301050409020d141005060d0201080a0507050403150c0f0503040b0f150d050a0212010c050301120f080d021305061c0906020c1501090608030406051b0a 78
    0x1804131003d0340042c5d040045020a441c010700090030002d0240c0014030780740c1c1c80300f181031105004e001d115541d00c401e4101035407241c5148000481d4884000001c081d4614581703a9281d580d0403103001000e0400300058480e0614105603034080b5810784030321760903484103580d00014040003000700f4100801031200001081100d0b060b4282c07a12400000104404100002480313441244000000c0c03003c104144000101c600290962201c541d090211250711810701542c1c500c40b502030529440341d802e48807107092290208448540920880e0410301c0b0002800c0c170f0a00340c1e2001e04400022443c188010440c00030034801c0d500c0446d01c2032080c44a0703051545c0e503040c025041306402e1032100d035020550000079200041140003030601115814141201e4011841c00c25182c00c4210b0707100c0d41c81d0004901040141e4040e950710b4841e2509032075220a40200034003140500b40700e03801d4140c3c20624000340f0b10501004940595045170f0b60b551500d40c241281f081118002062a003962103071003000f030040380c0c084 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 89587096 1250 89585846 89585849
    0x51b10030f20070308011505040e1009051819020901050d080c010c0305010602010f15090902150a030902030d0504030c06080601021608010b010e1206070e06190302190f0e09100f 78
    0x2c580030303071550302074100100f4100b0160000444035441032544002540c110007503a0840b40850604540c0703a0343c0b4040f01190758007503844801c1045c280803d000308154040c044020266580b0100d070180d07c0d00c00c0c16480362000c03c2401130340190040d0018080760030108041441c49000d204064505400e54080608591082c05d00c0c10010355518014003156a0a000303030f85d0302c040c2e0a00188480d02d0000040c035a10066441030446043d40d60242a0840d00d6400c2c2d0031400900c003a446039140c0c10004000b8016006d071b00412886030250a260400d02d600502c10384041d42d40000d83d403520300382015070640b070b04a40a0701490640c800c0d04000c510203048240c40c60b02401c8600000700301c4410400014180c030080b030001d14071602100002c4403416800091032a80501d05142031075100d103403000441d45600c10f081035854095410b412052003950150020403041240c5219007142c80707060607080740c8580b10398144400141c80040940c40c689820514641c00058000380c10081e155928503006a5a40d02d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 89588346 1250 89587096 89587151
    0x4050f030309070518091e1204150e090115050d020d020a020708061003051b010e0d030306060e041a01030e03042106060806010e04120905090a0504051b10030f 70
    0x5103010701c6242410f019100d117203031543d0030000b460b007850307488181c41c0c1da07003c101c90000d443e02080d0514040c0d400c12001d65003a5a0b0744c446641e4603202d01c10400007000880d094400310b0b0450900691600b09945039a0480b00c1c414202c4c119150703080c0f81250641e02095801003010303000d1201c4164044288010f0401c2035554005104a9141c414003504186000700511a204030240d4101701050000c03600280035580c0b40007132100c11300c2d0724006850848002d40200e400c40041114202010b405900c4041613841d42d032900301000f450b4104000503508000c98145084e503d00810302c0095000f03401040b004881e180550b42403030303140d81c209a4220860205440c0c2c204040c10954203000c80d500ca17000c003410b0744201034450713581050040706c01c3c06c0005d80700034031041e12058480c0d8124843c0100ca00686002402084182032624512001d414161802d4a0500960000442c0f45050500c810350500c005401c0326000c0003140000d0340180001c1c0400c0c20410f07180d9507501113a081d109564082c6118 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 89589596 1250 89588346 89588353
    0x11031201091a0609030304050909030409050702060f09010b0604030209070c08030903090f0a030f17040305010f0c0f1706010c0203011e05180f0c0603150a0305010b010e19090504050f030309 83
    0x4801c2d40018442c1c0d000b1507240d0080740100240c0a00b40c0300481158182c0b40c003650700500d03946500344201e00d58860759011180e0580707440d06200d10240d000c524a800356030031000105181e00c5602c15542200c5541070181c0c3d00400801080005082c00e04555600080c81e080c0040b104440d6140c1040380c0c0d0084403640401e030070000b0f9884441c685451220201c0c082a600d210b000c40c110341d030700c1c0455882c031000984a00c01c9610407a20644254045401a691100092043e54425004031010b001c81c4030700007021544102c0301da61300510509800c007104005c0f58001f001c81d102d40c3c0040d6490000032006a80654a6000304207402100c00110701c1e03030f80c2c2c45d1030300000c0916000000e84d01c41210718030340c0300d05908500d21854061000042907030400c0c40031141c41d5a2626581c4500f91107192030203130306400003200803002050000640c080024070000703888000c0d4000346074081103040d0081c6220072014070080030051000700d610764001c0c1da0003403040d03044540441040b503c207880c5810032164401981d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 89590846 1250 89589596 89589611
    0x12020a0e040602131d190207120807020d1d041e0606090e06120c09060310020708090405010509090a060507050d0e06011a040b180a051c050c01030c0e04090c1505030a0509070302030d1103120109 85
    0x83d0b042011004087c537500d0039029500d14072601307850800c940725403281b00e01e49644010209007100c4400115204c40d0800070000b00e59140c0c0003500340d001c41d00c40e40d44070851040004210b824540d100c0da00414122004d0b00807803400c0010880881c00280c1111703010301ca0782c40c1140d0a44100c2c4014072840c1d01400b480c544407401c800801050b0b41050300028042c154640600c8054900003444005440d40103502180b45e13550040210340314003c9000308400705091022a8800340d00214505069031030700b021101c0414036003554075102d0710451040e8400b103c410825500607041c0b040d00300d0441c0000920160b01e0310f0351a0b00160b0000c1405085103924402e0030000010440100001001c202c800c0c01c0502c0000140136029185001201c500ca00031a11413216101700400700c003082d4068141c41d09401f00b211003a840060440d001290115581d070f01d000d000c41d8002c140040e00705c0c1240e45c010010b080091030054101c0c1c08403000612081a44011b00503082c94100c00b2002d10b01078000d00d000002c5c81b5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 89592096 1250 89590846 89590861
    0x803010f0b0c030a05030705070209240301050610080a0f0516110703020f06070c031502180a03021c080d050411010e1912020a0e040602131d1902071208 67
    0x160103a0710600300c0d07071002c000900c1030580100a40300e2101e00703824915241e44d2403420543d264030400b000298010051402c206640f1800f01e11103258060100310780c01280e00d41070501d800c95009462060b40440e00461100150b440350b0b80c199441000b51074045a0610010145401d40e1000e0f55141902a070340302501e20b03401d9020b000740008070700c40e078014400c243c590b4012079849118035140c14020b40c03001481d04180069100c6100080d98404a0051468038030220302000307411100c04841c448030b5407403201007189400e11000341036a400508222100c503800203007440c142c801090484181e0001d00903150703000c10314483c0d0b5202c0c50040300b0707800d00c541c1302c0c2000416141007184d550348160710341042150030142071007114003034403005507201c03185001900000305070503aa6800042034510500400040020a0300036200d40c2d100c003e803054036561035007450740c86c50b030355104e220124268100006213822644a00c0c0c2109440640c40103240c00e80944a002040ea00302c04a81d000c0f0304c0303910900c07460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 89593346 1250 89592096 89592119
    0x180d030e12010501060905010e0f182202090a021606111306030c0e15120a09110d11062506050106020d02030f07020607050c0909060403080714070b070e040207080301 73
    0x407a1500c002003107590704000c400740c00308049020305070400440011226442e01ca0a0006c4407040b4000c1c8000040441401250240c0c40107d820404641c0d00311507480162808813410b5005a034010a4280c0566070304400200940044400f10304031400036240304081900d80c0305840002c540c00340542c1e92003140342c11807d001e560756403080c1d0406250224050b041c82d48003902c1c04030410304039044010340e813031901002c80c03034002c503800c0718119200c400520109500d950300101c1c4061240600c032249540700030170061341100b81080070b030281c50303817000e10380c00352901e0700003410144500c6c070359800080e05009181c0740b0115040401c60315182e4403001031011039010406000d130510184001c40c64058042c0c1140d0060050350710007030081d240030480008102e01401500c940d10000b0f41100d0891425403210765131240d054609a0102d442417001c90484d6128000440c0c00c19440d0708001c0c5000620b03a920402d00030001d02c0c00003007107034110307910344203035907034002000d9a40c01403c0342c40c1c030b035410008000c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 89594596 1250 89593346 89593369
    0x9080a030605150307080f04030207080304180606020a03092c0703090303050f100909060f09080d050c03060922080a0903030212040501170703020d060e04031b08030606180d030e 78
    0x101c3e1507080c02002620ba604c51010303a441581440d821105440d685000e0740342090079003041045010100d0041414540f08803031801121001d03005000c01580d50100b43d8659001802c041c0005680d203105020140303000c58403848290b03120203c0038100640113580b0500074403d540103400252142d003901c0a140e40750045640003036230052619410305000400750340710101031080e1412161200d1601c024084298881d483c146212907080c08904100e1401d6000d130361100d40d4050721946050702060700c44441505691091002a00301c0215881d60760950b0041c9840019000050028200f6000090100405081c8200e81620307988202825480e001c0d090020140a81d1007182003400100a541e0f80910802e54240d0581851701a64907150790440c06449a010b81320704a43c10301078005a492600700c3c40500c9180284e5a0040022070009100d4211199a1014026550900100f421352401340001c01c0034010b040440c41046069502240d80b244801c030081d00030036143c8100b03500a0070300192004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 89595846 1250 89594596 89594629
    0xf0509010506010909151d18060903090616050703030801090605010e09070309021207030c150e030705040b030705120d02330c07050307120e0307030203060109050a09080a030605 78
    0x216514000000a118070300901c90381c0a4039441b0b0011014599881c0100707400341a03c009000c0b025070032410400f4107440e0645002298948030300900c5889000444c4281c00341d40700307002035440d0251305410404190418000c03030b02c41e01c003003101c03901c0014000c00c8071100651007a1603ca107150b140c982e0502c2101d00b5548202d0500191007042c0c5c0481d40e44644d8141d102d503850a000402040c1d500115005285085503024240309002011051100980b6603108407542030801e807013044007040c3d08683c0100400c0019805901c4a4014401032070140c0144070b414401804484801d5074450005000c2d400031001007606070031804110059a03814450342860300500f800784032501115205c03100019518403182c002c1042c500c0040340c05e41c44541c040740c9100b40c02004607500c8510500b001714417400f000c001700c408544501c02e50a054100070440c0d100304c0350020040c000d079030f107041c4050020703110050a92403d01d54501d00d08000031220409014100b10a0b0740c0014214101014440e2000b0340c1d40c5c408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 89597096 1250 89595846 89595851
    0x7050102150103020402070c150302091c0213050c0d02310b0304080a0519050a0815030a03080c0405040c02070e130f12020c371a0a020a050604060f050901 68
    0x10400301d010104040d04480d0305480c010b039540d21a040c0071a807450341c0c0d000b00400290b00317203541030603039810340203080307142c900300c6120000641d04039004082070818a0001d410026426404420702043d41c006075025480b81d040764a4090005041c8040368000181ba0861102405900810000024254250045000f40d003041c40b403c02640c480c039400300520003026950700050304010280309505542d4140015400010000d007451800380041e003002c90b2010000300030744000f80f40d41184443d501d40089010740940038681864400300c80503140146410b0f041c030010000021161100c0c0300c0c0c44103403001580501040350a00100741a0901d010f0a2100303203880c005001400308040040d001c0c040c40d407100100d501541041016410710044281c03d6074800036468030246003589908003a99904400f40e400c0309019142090351007004545c0c06800e030b84084044c3d1980325480b07040010b0846603d140111580c1190a558075440c3c06000c49040320f00b1500d402c041900031071140180707500144a40c000303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 89598346 1250 89597096 89597113
    0x7090e100b03040807030e0a0b040e091f0e1507020105070206010b03070f0507021909020405010906050f0405010c080c100b010813052109040905030304170403172b0b0307050102 78
    0x61850750101500c06001503000184082c1010700484001c100814080c2912070880e42e261070000c034940140c8513144481c0001d2000460030200850350813400e00760424501d42a9800403224002006000381c080070034441c15015000002004100c0c41c800e2a04c0d80c004035051504003c0207003401070681c04031940d0501441801081d60304005540140143c80c0b80c01a11800e06000240d9402d020f80b00b1411600340c484030218100340907800810960b0400c0e00c071150900e685030000c40d164842c00e03076450743c005001c1c030082c81150310407180544c4890096000600303042040304c0361800c01d050380200c182242d680740c030780070700c1c55802040c0b40350302c6850100d03c8945145603860781070b180c441e0f50001086e00c0d1f40403103d40408841e0b110a82d418001c002c0c208004014080c60003542c1c0341e00580302511013803d500811004241110129820790350b000034078000888203008210b44681041079400e01541750070303051401c80c541f0f2400f2010320f4008490b0100d0744038010003c0c141040c4541c0c2200381150000d641 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 89599596 1250 89598346 89598359
    0xf27150e060a0e1e060c0a03060e090a030206011d06040c0c15020408240703050702010f090b011e120803040302031605060708010e0727050a060215060d020a140a030b07090e10 77
    0x2c0c0140c6c400d808042e40d0741d85240e1088220f00a1003240c20000f044401601404011540000d02e030301201c0c4241c0803281c1c0c60f41c8800004280d004181c40741d62004c0031941c001445410b01d40c104860b03008403420000d52490321690781c01c440c00b41021a1500d001ea001c0b0341042484e0f0704111400711140e5528544007415805800e010400400a00d60028180c03510003084c1050310035441703141200503000d0304004070880742c9000da441c401300307100e90000c04490104d15040401c680c50968103c40103c120f0f074100450b03503500c1d0307107554200810075000c0d4001441552100000d9031204150144074402030003031890411000f030b282c030714181c100c4c0203044d041804120f00c86400003100d05898403040c0014195500c0005407070044412604101d810081006002a100c3e030002012400314680c40980c0c03000d681d84070240112031080981c042e42c0411512010040803280240c6856400400381c1000f00c000e84a40300e4002030f64042d0341103000110020820040750307074020748440e0004003071406103400600c0c295 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 89600846 1250 89599596 89599603
    0x60c060510030b040b0402030c1009030c0503070602070510020304030b040f060509060402090106031e0c080f1602060408030604091406070e1206070e03030c0601090f27150e060a0e1e 80
    0x7440203200e001d40c05e01040940d5010440300c2090a0010045200c0856040e00145002c6a43c4011101c2c0e50301d064012079075180105600003507c040345c4c01045060701c0d0401300640d02d21020410403d6000c204408030205d50003140203481540110101040c1c1c100501d0326804462008042c91025003056081c00300503039401c4900d038110741041ca008612100d00c214950304424045098400c00d03450000b90421068008800912507480b03001d100d015a510341064681560b20940c41800603009080010002407082d4090740d007149029000040b555031507550301603080a501c01e14010f543c000c100300208160312003661050b440b000d41e8120341c00f0401d0b03000c10ba5036103000b03807802040c00782542800b2000c0d03c08005842148140b00c0c200c842d1941e40f60030038401000b04d180c81040540c101520340c2201d42a601203400045601a00f094681d40140c44d0307840d2034800c00d0038001c1425202d80030a0a00d031420031000e8080c403600100081e10407020015241b40ca801039200004200801c08186102180170 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 89602096 1250 89600846 89600851
    0x2130b070f06110f0c010c0f0804050d050a0c05010c03140a020c0a0b06031213050102070501170604111e0d0506091012060605090405030901020f1902010302070206070507060c060510030b 82
    0xc0800c002455800314200ba0003120040c140344c040c081001210120305400400100c1c20985440000f8111080c0450341c220084401411540c401d2018911043c0301d1401400364040c0d9181c03201d4908099664507094486d00071354540065140c0c40030700c3e884600f501100f504614210000c62500d841c1011144d140c001d070030b0015040044000000d415a1801d000c9c07460b5449642440e181d07914032280e0018400300075401143d005110f403d40210307455000f000031242123595074440030340395581c2e01d0400026001d04a0130b00310000c001d112000142150901460b4202007210010b82c4407085c1c0040c420491301c0040410b889000990103102000100001c5582595072058001c960020f80d03007400c6000c0e10a130352015030031600c00d20410040c018040050241c1c020b09900740c9488140840341d01d40c0c1d0340b00711650510701c61005024a00190f0080c2d000b0700000c0d1002c0e180310304000c215111309080440c40e62008003c502e802c805c0100304541c1c1c1c070a0641c4010b03000a60b580d29815a101e4046c0702400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 89603346 1250 89602096 89602103
    0x6250207030602070206070b0103051e15340f1e0503010302090c0c0303010f05040c08250c080a08070f020a05060402090c090a0b090103060602010b060d09080c030d02130b070f 77
    0x3c540066481c0c2900b147c54494000d40820504e5a40340f44c403e030382e44074440c0042d114484068022200e8a00410101f00ca00c4e05080c15400300e854010039407100d410445190b0100003412440c07440780c9502a44518141e0078991142504011070318005001c2148040b20b4108039411f5511700f0340e5294101060b60305594041d5501c244659030148980003611801c40443d59500c000b000000301c114002d15100141c5100791401c0c080003103035000964503c0410368904c0d0b00c0c0354410a01e001482c1c082008041c0001007450708040d805850348561111340d100302d0038500043c000d0070820070000d030801104480d04a6900c0100140c1c00e5a4403030740d88546001d00001c0c0700305568008501d103110550151111290000d00c40d0700f4a03980c0da170380040154000350743e040c082400c1c440700144840c0181720311441c901c005803140f468206070506010041c1110b14048444030406d0084600740c0f03408001420ba01c4405010042c1d540362502d00c544140210750f4800d444d00d8008200003000640c070030b1001c0540c280e2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 89604596 1250 89603346 89603351
    0x1006051002031309180f06020a090e04110f040f0204080604050d08041713241803050604020904050102120106091a090303091021061409060303030705091908062502070306 75
    0x244a806000390700c50424021b010188444030010a00020750700400310210551250098103603075141c41500040704880c090b0502100b400c209555043c101140442d01d00b00900006090007410106412600203800c51f01055100f481003208221040192902015803030409600078509951038809004104030340c0c2581c3d4a0101e01c2441e10201030401101404550b01040c3c000901c140e002c845441130038110b40001032816504801c10b000c1d100000341a2078001000e442d0640d035039028400030500c0a4011a80b6650802c100354181c5a2151000d0280140c0d80da910045498021608004014014044c064040030400812a2354001049a910308001e8820502e0680c12071426581030034440b40741241411004032001e01e00029030b003e081690a40c00394030427885038500034030441d01c10480d03449030564020000b01c0e11450046000d0014580c0040002c00d91507026802c540c0007e100b0b40c003041550b4400024880c061212a01006103040080000d80d041040f044c0300a5449100e440702920070355 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 89605846 1250 89604596 89604611
    0xf19090b09060d060b0f0603160f0e01020a0308130203030309030c1006051c0201020f0d0509130507230403020307090524090c0706060509010b0909010806070507020907020f1006051002031309 84
    0x312281c941c46c04014004061640368a0030048241ca180f40000e1100d00041464140c903c07501c1c01441c20840111042c0d0040c40d1b0440d071641c09886031000940702d0020000c40344610401030344c1c1000114810120403020f5900d51403070b4034941e403070b00703405104010b400c47c02d011050103c0d40b11880003811044012048040001c114001070382440c0c4001c0407104103000307240081420075004001814460030941c4c1d1080740380c840d5a0008200c44040d60000e0014101c600501e142030140d000025084464529061810356241d0009242441c2640010b80c590703281d108001d080458590140301400100078000660400780f07001a1000c0c000905040400314003040240511007164010030160001401c00059540c40e040c0d2441c450f0044103a031072044010b10f002003440c0f4404034003140501080d494031801c0c8081c607820011200720040144003103105801a040008404210340c00d03111480036000100d440c00c0105008010081d140d414040d5807040040300001400342c25004203c42c3d51880014109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 89607096 1250 89605846 89605849
    0x2003030319090f0c0f090203090c060309030d0606080604060806040308060907030b030a11030d110703020d1703041103010b04020403020102060c070c0e16020105010504050106050d09020f19090b09060d060b 90
    0x1480203002c081e102d801d20050071000c01402d0300450050342e1510381034020b0720303517144030300002c1c1e100c00c80e80da0440d9000105101c009042c00c1024640003c40d038004e49040c04c00288140c0d08035484c1c0d6200b035000480c081c09103c1c00342094130aa030050841600a41801c0c0b409490280c0303001c1d0050242401080d820340000d041034400d5108442c2d290b07008042e50500940d60a00c030050308405404a44030b8014211800c4850f4040c030101c3c50304c840c002d40a800e06038655000c04c50540714900701950209a004480348480031b110b001140b107284242064803441560109150031144e84e01682805a80704200500260307800052003039009811a041580e02c130700e686807032050070300b040d44901c160717807103101c02d004e5a085519582500300c45c941d80200b001da03988108000c151030080c45182e02280c410072072003400c2e80301500070300c1a050000e4400003050100070081032907481e040d01d010400140d5584103002200060284000d40d02089800e0300207801e040c0f000800c0c02c5106800100320a580f418641940d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 89608346 1250 89607096 89607101
    0x3070b041410091407150e04090b0702010c020c03030a1b050f01140414120702040c1110090201030e010c1715040207060603050118080a05090a030503162003030319 72
    0x201c00e24182030380e145144505000025121103e800c83d043c2c000b20140074070b18003000601104039a205500811811030065080d1204030000c5600b94000b61920140c4000c604105142d5000d208140d0002910440c0c00b14020b06000d5100c14040c42900100500c1819650007410210605400740303024569000300c1c0ba0603071502005140b0340d0515420002c48090842c0c49280b01031085020341c0c4c001d84400d0407620700c3e5444080e9003814854120040c021000541003680c0018a40b92203801d0003401e446070105840c0c509410ba5003420425510341044c0f000b1560b040c000e290840a03403000909c0f514000c0040a0080101000100c203c4011040060440031641321004010300010704115620754460600c82d001c1e0440340000c5c1e42940c06c280311000c1c8450310344540420207802100550030724402460445499100064956000103960408000704006000800c040710514910f9040780509282507800f1004a054250f1010049118035005440102c11a035010b480903160004802181c0c054100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 89609596 1250 89608346 89608373
    0x308180a050901030503070308091204090b0103090215030702121833040f050906031015080619152106110c1612020303040905040804120b0a05060a050303070b04 71
    0x602c00301c200d0000051001c0800105001c81c042e0751000c03e00d030b4841c00300c550303280d5600304115220070341004100885400356010b200101d0b4149004160140300e50002007282c0b0b5404055a0100000414000e03000d0b01000f007c20343c0c41070f41290030300385900002c81e910810444160540510340c20000c4002c013040006030380c1108035030f842e41d00103801c0705600b28603003139000342c003d000c507038000171801240c2440c101084a02c503c0009004058000015500402030070b50a140f000c180780c135202000c107100d0740501203c0d2080201e00c1c00d040302c201220040c04103035142901d21042c86c4885078000d103c1401d46004448400482c4128030f452440c20b071500c01d004280b244406413503048040b0304100b1940c404a91a5501041d0041c071142403a120440040c0716001c110f0000c0d4540d0080204102c2d5000c0d030b422035584107020381c41075030070035135078400c4001d51114010048411500100c01c1101d900c1e002d00c1070641041d0142c403c2c02c6041c0c14507000c02c1d603d1040740d201415444071140050200050101d0109 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 89610846 1250 89609596 89609599
    0x10140306010201020c0f07060f03091e02130c0806090f1b0705030d0903170108073002040c0c031b20191203030b091005010c082205030d0201060308180a05 68
    0x707400d4040546615245c4d091740c09003000088501c0052500c0d04cac800e0043c012501e4010800e40540c04c051030120910020303100003240c00c06080c10003844000650310402d100003505440318031652408404100300d851b00200945140d503000001e010101e4075100c001e80384d80c2c2241c924660f0710001420a10300d14024180c403410003505120348030080580c00003000315100507209014980b44d0300d40c5101ca8484025000d0701c0a500040078a03c0c2e5150520010104400d81d41803102c68103040360313004602501c0c1c0907000360340442c0c180900002015804000d40d1700704503a22560002a0505a6441c07404040100301081300d003850b013441749469564000701c11400019034a4103501c49036100040d2510341d10b21107040e808640381c9a210350050034030f003032481c3c07040204812240d000c03403d12006440f017a088440035140441c0030301680700c86850858030120159800080b418072203141004142c80e08003010311483c216410b0420400000b074044090760880c000ca404412484110310380424800703c4583d0059 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 89612096 1250 89610846 89610853
    0x607080a0207020d080403031806050a1202090409030801030c1403120309010e060103050609010e03040f03030c1502070609170a090608070c05060f07020111040612090606090203160e10140306010201020c 89
    0x1031041010003001030040324880c0d21400c441d1804a009c003214180c1034880d08010031020091f00c080b0511800c542c00d00c0f032940100041c03d100c450800303e001c407500308404602080c1710f00010b006021003950f0000040c07070f0b1036200ca0f104143c1d41c00407a803184044c1f6842c0f80d59100201c0803c44c130740002e400074402c1c03403001c2d400c072582c80da903a00f0000e0781c505041c3c0d20301000f546000803480000e5408011641610108005641610700d15a421036131f0a44d01e600c1900c05c88800954101403800d28001099400e02452020400b0341440c18141004440206040301c41082007100150740ca4200001c80102d0b0014108600c0564030090142e500303442c4004014030501503041004038078210161003e009182d6903000b0003020f2242490081d40340b06601070f03100401c00200035000011341c150001c6e180341d8800c10021840d40e42e175010480680e041134564200c90008819030641d22079008010748003105049400480c40103d1003400342105080c101294401240040000e00c3c5034000d40480d840c030f1860744100d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 89613346 1250 89612096 89612119
    0xa020702031b010f020a02010c0807110d06091b030b04061d01021c05060a0605040e1302040e0d0807030203060d0f0f0c0f15170c0702030c120a03080115020607080a020702 75
    0x51091010080c62080c0442d04010960136a0340c03000409051059042c0c65003114180f55444a224640088208461510902622400c15151003002000244c071600c0b010421081a203001c001c0361074942c48400d40d000602c1c40410105402400d0030b908950005400552000f040c0c00b1480301ca02000b907044065800055851000c001581e200c5c6001e20074642d0401140c0c03103410402041122610035940003030028002071081100080e2001d402240e101c0c0c02c2c00401c507059010406844c28654010441e0300a840c0c20858182c00c102d21030391001c12468110301e10324011002a4000c404d051000d0101c8007c800e4060400184002e403482c8190829005415282d841c5110b014680540c05031460404e41c85001d054000d0003117a0600e050140e4600282e8a03030364108100f20540c024500680e458401d50100603069200c40400078648072181c80500304101807400c02400d14071044c5d01c0704800e100c5520140000307584c04101c089d0400694a00020a40c64005c000c5003c1e001daa0000382d0702000302010f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 89614596 1250 89613346 89613373
    0x190504020a090f05040603050c1c1e0b13150b0102030405060309030c0714030a030e03190605010503071d010308031308031905070806030627010e0106090b0303071205030a02070203 79
    0x411000c641450000000407074a410603c01519443d07c070051181c0e10161003200d49103403030510400740d5442c082c600d00f03414104e6292000851041200000403080e01003e03031080c080e070500d00c181c1c02540044590307000b150b142e4400c041300c0c3c02c14004854140da900500007042e842442110024038000700030948074104543d04640ba03901401c00d0809501c20481c00185840c0042111390701c2104c010090580c3c482d03a6101591501580420aa41130050221400c01c02c006040f8222046008000c00981c7d0740c100b90906203051490f40103007803000c240981c400b0780c014010b844541540e9001600b241c4130348401211200304c0c120000700410209010080004414022400701a4580c0d6a2014080c6032a02c200540701040143d0f031481d0542c00032400600360491030140203614180b040c440619a910003d4250b00b111200f603000509a510b0710303001c118202036170003611092030003240a186421120313078a450f1050301c1c04000c82e05204010002400031b40296044e1205c0390f40150542d240003c0d002d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 89615846 1250 89614596 89614607
    0x4030f022d0705030d09030803060111060f01080105060307080a11010e10050c060708060306040609030e03010c0201060f09140f06010306050d05060a050c03090304060e06160b040b07031a190504020a 87
    0x5108038648102d04000a032450000b034011a420401e4032500112410341c0c0710010035900040969061000301c4201442c40034081100c0d0344a400590a0300780d081d410b00700a2400c0d039901a110170702c079511508081c0724031b41000c42c025002e035a0003444001841210001611a40c0710003600d41d40c40b0031111410b5001c00c0c2c2050052060b03507040d034155030251f6140b003416140d10b02d090755000d0b015030200b17000800180031540001040390280c1442581001c610300003a0a403039541f201040141d4581d0010480050080b04d00d2001e092900d03824420030a10028842c503484005000c4251900c0700c2000c0b9240364001c1d8054000381002524110b42c400c943e0412994035503043d20100c24062038100040c105000c0c0301c06503400f50100308081c618040c9440c02c210b400504904246510090410090301d1403446030b685665498421070f50141c161425042c910107100d03000302400c0070705040200f000c0131801d0155203102280ea08403120304281180c2d4807110748040241d007089130880d01c0050b03000d24464100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 89617096 1250 89615846 89615923
    0x614030402150403030807090902040f1205010605061c05090303130b07140721020c0310020d021b211303021005070b0a0f230703110708070f03200604030f02 69
    0x1a252100002d030340b2700f44c190403032241e40704204211108003014004e504810300e0301c1103014080d20002c699035449000148295000070030340f401c40369188030b54401c40400c90240642c401940800781d8114641117406902880501c50000e00490403a40010b505500854429040d4000c0e40e4030251504140d15140050b09458142c481107008031036040454184002000404040054042c1900c038005507888000303504403c505d021030036001d0102c14050441c08810040000c88500105241c00c0a400020304010714800c4001d0125010011000c13040200a0f180d41100ea0594504000c1106401300310341500440c03c009004413001c0f000d005180c02690412810002d03007003410006d002d41d20500040f501d80c403d0400f0700140405c00007a1002e4069403083c5026003001202c50b1512841da074904440341d10100c022601c8194900c009814940e0080c0c8001c054802c0641c0c00d884541c011414a0340c5110061009041045121741000344074802d10010400c00c040c0d6109070149091144005c42c8203105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 89618346 1250 89617096 89617111
    0x209010504031b0303031a030d0e03190503030106030612050309011214040b07080702012315030a030302030a060e0601050316050c0a0b160207050105040b070c0509040b06040c030606140304021504030308 89
    0x103025041c1945ca40e90800b070480d00b00b0040c01400202c274024402c5d01d405080c600c04076894040c507100c9050984820b07030f009070f00500ca0b8025681d298100720000d030480e441500b02c810b0b085414168400007230000000c41d9070500c004d080c6949207030043c001100142803082c01c800d9000e4407500c140001c0005412109014600584441a187c1c1d900300c0100e080b1400b0740361407040c081c182c50001112000c120010740e04403d520142c0e050502d51800403074584401c410048001a074000700f0080080d038030784181c4003e0b08102810240a0915070f0000b0101d00015145901007611801e0445c0300c4c0780540c04545c840900c4070190740719030145040c0b01c80e0414080716020f034803860b60b0429000481c40403403008166901612058100b0b420032141036040e0b00300e14011105035410705404149035541c86d24840c400c5200d41c60803041840c241050005550695031000140740c2000018440c032600228003048c407030420403090f030303c0340e4a0740000340342c119030b00403001044140001c002c020325a100701c000c0e105087c2c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 89619596 1250 89618346 89618351
    0x100f14030609030f0a11120c1501060e0108010902160c06030903030e010204050109031b21060c08040b0112020619081012030e040c050c070b09040b03010203190209010504031b030303 80
    0xb80c2c8030036561648100b600d104079108040040d110034601a103481c40225030084100c1782d60f500048075200c03283d80301c010440c139641e02810000a200c0700140c0060f024201519081034400082c0c40064000c0406010b0008a10f401007840d80c071408284420340100c03500710102c0c0b5025a9143c201500a0255281c15400070381006690b0b038900c03905000722030490b08107944d29060a883c64035000e024030594401000682601400056001c05c100f030780b030030b504210320112110340240345044001c40e221034a800c0d081c05014010032003c0354071007500714110f40440614011040061000901c01e104038903d010240c0000079031090803992004034584646007502155250507150481c031468103004400017800117407100b0765100d06052a81119001155a043c140d08208032041d88a00300601d64001ca10b846a0100e146802880e05002d0309000794801c2d00214070394100b42c80c00011022104910f107c500340c0001c0d00c1181c6234481c03c101c030003e6401031307001c5860300c0d44441c0e0707100b8032807851205800090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 89620846 1250 89619596 89619601
    0x150a0201140603072d09061805040c050103050a020f0309030a080108030408060601050738182808030703050405070603060b070b040501110703050309060903030105060a0305100f140306 81
    0x80c50700c146640a40d00c020300820080d49050204075030015840000102c031140e1760600e1001c00d0301c9006a202400402030042078050a060010b0002c250042811604c24140f00602c00071600d0340058400740c440a10700403074240e90f1a40050b000e403007156102c40d514940002041a4a0310200c09020049110303525020143daa80800560743d00680c01009116003094010030344543c02440182081d45c8a0302052040805003ca0100c010031142c1d44000c100e41c0703001540d03d0315a0000e49940c0e1165181102c40b013003c0c101316003160744e41c001d1208281100f58100d102e840000d858150008110751107441e2036903030300d40307110005d010b014203480440e03031480b40311070200c2c205004e80121015a41401d81c11400c20010351034400240d10007031b20a1f500e0b03540e2074500e5403060325074100800800380a0b403500b42c1d032070408220041c03400d10000c000410581080c4010702050781e40780c0c00c46903256102d01e404170310b13900d4000c510031000f0703510391000445401083c0005140c8400d0405203c181004800780c0305280d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 89622096 1250 89620846 89620871
    0x7050c070801020c0c040e031917090c0103051602070e100321090803070803041509080301140a0f0311091504090f0203010b0109030c05040228030b0901080309090f0a0902150a0201 79
    0xa81101000741f41d650800d100d90542c0c000c49440d00460141e040c608803e002e1426004140e8486040c1c9400b100e507040403500c5150342d40c260240e15042007c401c04040c07080c1d04003074001d40b102d046000320500c48046101040c052219080c008000d540c00c03101c0c0105d0002c045240c5081410803041c1e41000c0780f88440b0008a90782e011042e1088a0780010146180d070b81d40c2d80d51898012200407810902a582c0c4030f211002c41e00c0c1d42d000d140031308803510a05540032440070400189032803c0e481f00c0b41424000b9001d20008000c6550700d00e202e1003c0c0c80e41c2c0403079241c0d101a200150880554146c01a01d1301e068401804207007a0307000d901703900942c000c00045108100450780310f0200c4c0406800b19001203c200210709040d030041004100c240c0031101c02c0ba400640c0035040960316000030300000d4481303019160500c0c0808e0082e004010f0540154a40f4100801240c50316000038101c040c0d55100c3c40015200f4a0942c01000c0705542c02064109040611055007520f0341020b200c40c030056280001d1101c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 89623346 1250 89622096 89622101
    0xf0708070b040f15030e01110426030403110319050723031c020a0611030916080a0602090103110c070e010b0a09050d06090206030115021504031707050c070801020c0c04 74
    0x9441082c620540f60720300380b4001040032a00d64900ca410140c0c3c13651002001c0d007082c4a99400130001d55040b582c0d4038680202080024114040070303440380b04002441e00000e500000b12401c81b80d200c400c0c040c08403892400203040c2a080c2480300462911401e1303000402030040b460006032101c81081105031000c1d9841241050700c045d41964060340300c2d014442116905070480301340c1c0e0b0700324030440310040d00556965081d22080b601e249a400000b10520841000c01d001c0080034402d802e1018140742c0ca400602550b13181c4540003d44000d50010b00c101d5980d220780c1105031104c2d5540d0201e60b0715214000001d03a00e100500c1480d044041071800421510140c1003100c480101a51314200704500f0001002003694441e44100c1c1c83e15640e8040c00d005840311005940200001100d8021041c80c1400180c10100a000360560404140042100294111a010700380303180d21600303408a5a1031301025a424811101e010440d4414141c001444c110b054004159820714102699144041e15090006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 89624596 1250 89623346 89623349
    0x3050c030405060f0a270c0b0c061306090c08030304051b03251e0306050c0a080c0a020708011109040b060403051e03073810060e120f0708070b04 64
    0x115421000100d1100d041440c4a15008080c1002c00611b00c45042d41d510602492012058080c122219404040c01a61030107000140213808445207840168214940c40311001024120f90030000280482881001d904c0f030741c3d00584c8018082061600c030000a80c0e00d03041100e08550074845c0414890b1a0070b0804142008848c1c0540204902200411030051464404104009800806000083c81c5010b4517040c20441a1091050500c03030541c20b0100c1514001460900c800d1030801c1600821380c3e11084295202e011800300f541c0751b03100d40ca012403c0060950103008258200030181c88101c00c0e44000b480100011601001400384400501009008070700c00540103400804441c80f00580950014a00108a100b80c0b840c187c80c90b40c034000c40c020502040c03040210081c0100701441c100c01e00c94401c02940c4801d08a80d0700c1d060790240d6450120b40205401c006501d10140116118410308004040c8400280c40c0c504071500c1c0c4080e03440d20300340700d1a40940b19405000401041e284200ca0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 89625846 1250 89624596 89624603
    0x9010b0a0501030b0d050114010e091207080703021609021c0902130b19060201090b010501181404060902040305010902031c05030a0504020f19090506040c1b03050c0708060703050c0304 81
    0x110001e00e0540158001c02c82048507a13040306000d590100064402e20840014840661030b10340254140b4014001d0500004d240080ea81e010302144203041001800340ca06650748120400c0e41d452407858204c0c10140b07000d840610300c1c41800004110b00e20780340c02406200b040b014111206448403181c1e601540e050b00ca002e5002061001c6480c1210b410b600b0210349000080c2c110304411344800080c0842d0b9080c0d42c40140141d540d00020710820003044511401031500b40791040740800861031010204c0020302c1000003c034072920320441c60b03803295080301c2d00501d0341900031500d40b5070703c0c10007038086c0802110882c4a030240d5060703c1c045041100840e110079220769a0b00e42182d4a0100183c000c25000e00243c0c0d03c145180c81540c810340e121010f44040c0700d812540c0d1305001e03280203400000d48102403d110322031814030046612060b40000303071042c61740d00c0c3c10100c0c002074858141a9082d04c141121000540034102d40810035410004400340510340a0745c00b041560703219004010180000c0c1c0e03004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 89627096 1250 89625846 89625859
    0xe07050901051e0d03120b0a05030303060409031103070305090310020f0d050a02040b0d0f0b0f030a0308060604030203010204030305040303020c09060d0609020f270906010e0c0a030f050406050f09010b 88
    0x611181c145a403010031562101d20f1591080703101e080004d401081207881c105d0004090522001046d42c66004e988505041642c50410850521780000d440f0301005084d82c3c0204da65284e80303400d052050301c841d04c00d0104c8500b6260340e20404e0400521580c4281c1c1f0b00d9000c2e00c5a0200010071007070034400c4900030030140203070b0303030078040b03100400f2000d0300780980210141c40e002c0c44046012008a4014a1400d4902500107480e40199040c442540d450809240c400d0b050380740301c090251408522203002c29418075145a40e5911100080e11b1802680c1010303403d50710205002c402c041c0c000000b0700c2500d000c1e408440e000d8078008100f04604001702c4090390400e05002d032400008001d600b1060720f0034401411114000c02140100b08962640e541190211202030134441042004045c001e03006071035200070709125814002130181000d800f600c2065480d500191340b40c0000d104c2c0c0d0241c3c1d0208100700c8180882d017811300b800000740c40281d441008804100b00821040340b41445a0032401d03501a180 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 89628346 1250 89627096 89627099
    0x50312120615070c0f1d010812090307030f030819090309031203020702040f021e2107020a060203160f02010e1c0903050a05101407080c070309030b07120e07050901 72
    0x1448004114011280d00e00b5409200000000d424004440064561808090070785e0340f502c184c400d040c1c0c0000c140e0100c0d01301c2940c01070180d00c0003c504900c04040e2004415a25404440428504105603001820080c0c200f410007040603800b4900701c2c0189520442c1c043c0070712442200400b25500190010042002c07888204009500d802d404000070400f030a0050804280340c0100341622010b44c00071382c0e190b07800036003811201c201302c00c01100001c6900d403d60904c4400000900804100e0b01402c50500d4008000740341c0510030000e0000712603002ca0259183d0501e86030300c00940151502c480c0100311943c44410006205200764041548058001c160114140a00b2203101c1044074510f0204880403c1c08008035400304440c5400b203108000030075003210815010400c454030b0038588140f10500500b404100703548000242e800048440c2410750300e802903e401d88941d0651350000f0300c140b034003004000390b4a4005941b422645c00441c42402084c5034220007076110071280c021154001d981100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 89629596 1250 89628346 89628349
    0x2190303051b160501050c0406080c0c03041a0309010b01050304030f18050301090804031506050d030e1807031d030a090e1e09030301031a04030c030f0314010b040503121206 76
    0x10442d004030b8504030000b003060344110030310390941c0203940341040020440224010080244503441e4810403156040b8201414200700a00f0041c010300706900040c0042961007251600344110790080241101c403d8281654801da840c0c0f540003211168010752810059101c954058003c41f4891540747e41d0340f00d03a81805110545019807a1018a4490141a000030509481c24030490341200d000d140f2103070312a403851038950f10000304202d14429013801c02c0c030204081d0701c8132111004100c0c1d160500c40030318032451000c544007000c405030184810140a05210655425512901d00744030003440c66101c0c92050000702d542c0b0710800140e0000a00c1201c0308100c503030311215096401c0000c001d81d8450000b291150f00010300350541d8850074540000004204000315811078501040440178580c14500e0991000380104810400c083d080c00140e008040c2014441d500200c0c07801c08411a034096540c45001000c003940043c02054000d206030b410305010f1456131003d403401f007400700d001215103568460 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 89630846 1250 89629596 89629601
    0x61009080712060b030304030c150e0d2d0c1401020304081002040602070f0e071b050a03020706020111030405060402190f181b12110409020f0703020d02190303 70
    0x4410404100410001051110040c4580d030024151401850300c84071060904500711800400402e100c0d41c402c100070400500d01106010884000d810386140c001c06010f8142c0d05283c070b080c01c196002011140a20820407074650480014500d44181c101c1c080000d120f56003a140c0504000e4491181c3c0e103810450003980c0071201418030f006205481c00c1c1542c5144030b61520085603e41c2c5c0c03403d600464240003481e0b0402032800146041d0201081182c1b45ca100420207402c054814002c005040030102d9a656441500080080c1e01c41c0442e210020076040080d00c41c805401002e0055081462881820b031031f000689005a8210700508480d846917401c2040a040d01c0170569040b20b00d103800042d10748000880307800140b540c5940e100c0003115002e031800c100d81e000b20702211315000c80f40d41803042d103034440c80100d10300455543c0040d10702155420a04d50f4020f560000d80024000211124030704101030252030300c54400d03022951059590a0240c2c1c540b801d00741c0d4090f8a40714002201d01107031098 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 89632096 1250 89630846 89630869
    0x30b06040c120c05040e0f04020301150f150e0d030e030120040b0307020f07080a1506080606090727140906032503020d0809180714070c1e1a07080306 66
    0x1c2c1402032406960b403901c0914203a003243c5142040c207daa00300015402d0a0040d0300042103200710700c2c00210304240011500b08450300824001c41105442d44072074500640304440700c00002021351810464a1600800c501c1c44503020600a50914081705065003030f0030501c904c0689004852400d1505001d5180f01d00d400c003c243d1400c5125206004102140600c1200c0192241a000d0503022240707003085030303901c0c1a10f00364504603494000b003002118800b041041c3c01007411200303000980c03940c41045400010b00641c200801c00c4d06140b0242e11301d2001102c004039071030380700a030644038046e004100e4414000c0710360580640100d145403c0d00104103c4c11103468400c16012002c00d07460b034010030501c00e4052000c841c1c051000a000e00c03949044812650382a060030500003484c644404020729030b2010b902c9811021001061500411041200c04405401c0c041086807030042c810781900c88000c1c0c01d1007030a054001c0e116014207403182420848034217607081a41c5c9891900c4490601038020300701c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 89633346 1250 89632096 89632121
    0x9050111190f050105010501021b0f1807020102120901110a120207051b04150303021903170c03071e020c1512010602010506041a13020c030f13030b06040c12 69
    0x1e66400710104584041600000c50003a0220030b000c545034504103003100d0042c1c000034107540c818511180c610201e508070a0a1120680b03005082c0d8500f6404034801c200c00c400e03054440c81400040000e10303a415400781c01c2c172102d00c00c00e40e00203480300a10350342251944440f10100150403c03024141d94062040c004250824520051410740d083d200c140c240000c200354540340d20240440c000642ca02405a01500e90448a4440050b841d603500603544075402001110b03070003491031024090501550740d806030716409452180c603500d0001c05612159104850100124034000c110190410f02ca18101c480b2005503002449031510007001c01055000d159241a420101042282051144201524000d081071340002c1490304211042200340d60400d0f44c14210306d915078019140c9640e27a9030038010000c500020060782c64140b9242103041d031203410500d001c040c02c00a40c00b5105c90112900f6802c490240400304000c0d210301c400c2005641c6020301c1e901c0007658203940d4244020307842d406072030703007042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 89634596 1250 89633346 89633353
    0x6050603070b0c0105010501031d06010911090402130e070809030a08040c0302040c08010f0b160f0305090a0807050103050f062202190305010503060f07020604110f06191404050109050111 82
    0x58802d1551180d0340715000c103106694403000108115605402180c0b55014000c0321036840110850040350f45a00501c1264004e41e110099020b0803011203040f52002d40000c3c20035540d401c01e031558404020840d106003154003400c7c40c0003511151090301614003400d0742c500910b1900d172002030102c03084003026109444c00140001d0010046c1d84500c036500940300e031901c80e68510744c5401c1c020801681c0c150300c06110110100701d190110862611503c1c251540162503044010baa81000c4509000f804540d6070041031a400101e580c01c00040c0705c0d811240c0982e01444a035680b4140c40038a0b0390140c995035082102d2000240141960360300d035028046c0d00c00030041c14071865000f070911040904820380c011960b200c00500140c1800c0c0076190b0702c4405c00e140b001c014140341000a6407030b0001000548601c10180140307000382c0e1a51f600d4040d5000007880f558503100586102c084100032012500b000c290f640860b44503200b40d000944049440584422101e0b5281000544480152403407a040714017 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 89635846 1250 89634596 89634599
    0x90e06060d0308010e07021c02060619050a050105031003020405101a040f050d0501110d200408070b070f06020d0b03150114100908060a0903090b041410030221060a0509130605060307 80
    0xb5402c1c448c951603460180d00804450811009121385840b0304040b0f80020084503030107000c140c6412000c04200c0704d007071800650f00e95445020800740f044503000294414105020f100702460500800415601a0070240341000710700741e5414468481e0b4803030410b610600160400c1a86040c807a04494540030780f00201c0c0132101c400c0381d18615440030b94002c4a10baa508148109140c5015001d0780720b4200d4403413a4640b03030402094990720484d40c4914588e0800029a040030880e8523403030080950f80c012825901c07211030601d182c002e0600004200e00911a40381883c8641d40c2118038503040700d0318400c1e408009590841400302c07084000d0601014000e00c1d000020b10800c0400c0060310410310180c00040c164410b19006140005991011806c44014001400000d050f02804030000608072074002940700303490000e402038080d5a52031187ca488102d6400c2003000c0e001d184d1880303038a0031104054500d494004008038101c0c03c0c2d480020350702120400c0000117004d94130030741d00480700804940520703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 89637096 1250 89635846 89635873
    0xc09020c0f0616020c0105031504090804080304081e0d0f110c0306010b1e03010b030105060a03090f1406090316021c020a12030e120d03090c0b04090e06060d0308010e0702 75
    0xa00e06480d070500c00302010f110111200d5040c40304a00c0d105007440c12030700e1400c184030381e0f11050000e10302e4284583e6540d402c00d010400d412044400500e0316005503600c65a4403c002e944494080d600384a0300402d0301e40c1e2000031103010814002041c200e0301d4404500300c03206400c43d1903044050540d030051140c2e2151408035542007112034024280350f5003581e070700c4114038030010320301c003165030728a000c110144018420070305890240d0303055031070968220744c844032013140480141c03210010280c45011580c0080c0d06118100100d52400c031a010201c441c281c45161005990b84551060020343e40c01c1920588018580f406607400c5041d1368030302c0c415025117550000b960780051030388500b46421141e0389280405412501549040c481107800c421110482d104a03506c40e03000445d080304155503035070348804000e07142c805c802c058040003540039115501d0303190403c0280840d401555040c8119000141a40b03051a039080b80d955250b0344404150b4a420701e4022540006400c0100b50300a01c01c446010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 89638346 1250 89637096 89637103
    0x4080c03070b010311010c0201021504050a06020c0303040c0f06020d030e01110a050a080a0506010905130e061305060a05011a07080f13030311070609060516051b100c0c09020c0f 78
    0x406001d21400500b0354558504040c01100d4400310505001003400784001603070700810b501c0c03a002816845400d0b01d130b49519026052000114000307240e00c0c0b0109003217550490000183d4480c5101d15900700610382c40e41d030041143c20f2503204000041c1d2200081b850054840e0300150501c800080c004104d80a24102c01c100c1a007100748400001180071528180081e4040c1c2c44a41210f2004810044d42c02d2440000b08140214011180070360000040507104102c2580300d003021101c8039050f10341c1800c081c00c50301d0310000340c000240d65034810200440c17034440007031148504941c1898100c45022301c1c03010081485400000e419210b903001070009048011544004140d240890400a82002d046140c050440000c41c00c032000d00e580226030510446400080c040d00b5600c042c105281c8444c94820304040c1c03034030000340061441c001d01407184c55000300e82034002c500303010489070b260b64000c138894100e0710625062005880a00ea401c810003c2254582c001e000c02001c00c42510b0607803180007005842c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 89639596 1250 89638346 89638357
    0x6120207080c2503020303091507061401080f0c310603030903060606030b09180109170c1504050a0809040908190306050607030206160e0a08030a03060504021c0504080c03 75
    0xa2581043c503080b0043d10550b05607076001090061140003560441e00820758901039641c1850065988004002c1c420800380305079800c0c035074011014000022540b4414000c2c420070310a1041c0c43c82220302c00c503214030004c0307080e96607804041d002d05500c810141000f18100240b5040d1081224038003c045c03540c075040c2c011100654081e40700d9011551641c9811400c0300d000e9800501010324011001c59244d80c0c8090141d0002c0354080141512800302249a0040440b902c000703041034080c88903410150240c102601d480b02800094038902c4000c0c000e83c1982078000c0754028680c0c0c200441d8140040e642802600c04041e001e003000403a0301241e950010103a109030480c0e2024002e0702d81c0712900316414026607026080c00d8070118202882139402940d07668001d0305403699040c81c0300442d85a10302c11002014441c100801c41030b00f50f40d69400f400d880740d00c1a00c0400010341000700c0070500c1c0c140b600031103815903106000c11f80c0d460703042c00700000201009001182d440d00100000e44900008201818 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 89640846 1250 89639596 89639617
    0x140304060222080c060705101a04021c140c0f0307021204030f020a0501020c0a0311040905060c030f06090103030c030807030912051206120607210911030f0708070612020708 76
    0x1031085042c10745003840d1004c181c0460303103c1c0c03030301b0460303500018000704000c441002c1d0300d8404110603480c102c08980c1b041c0f400366801e405c10310225076040b882480100089010841401c100660503507054000042e1104a40300849503004000c298441400d5500444d4044600c1c4155040d0041c9044814141e038820b9100fa202481a0000d090951510425400081000b4002052850b9800c1b010404c040725520010700750405d013030b45001080c0c44070307005882c0c060740c0002601d515261040500690f40c02c1034540f00c020495220019103d030815612281c181c80c0c16072100241680c0c10350b02124a880c00038054820075803550040d000003521902d40b0b07038407040f098807150780b96104035900e40c0d11000010600ba10481c001e06944903029008607405800103410300c1c10072005100150f569540c129100d8069402e149420714800030710151075101c003040e0b5821425100c0c03965180c1c001c030740d44005e14060013082d030f0450b80080291034000c1603598004072400c140581001155110702c44d540d0071841002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 89642096 1250 89640846 89640907
    0xb030105040e06090c12010b03010c05190c030e091314010c120b130e2104031203090201021b030703020310050a0b0109030c03060504030c0b0a060302010206161403040602 75
    0x148464035290182010900c98203004120614000c4e2000e80c2c2c600b2103203200c5000d1000210390710840402074005111244000c2e0080c031212208000042207684400d407400d40704082c00c82c944154030321a400c0d00032a203130555580b1101207111010808900e5001d403540e01480103602c49640042c01501030860080c03009800003e50042c10000a0056000215030403007072894420f03880c1003680c4030110039003051a00500042d6021742469014078041e4100654400e4044224013003143c21002c1000340156482002c0031240101e860109400741d03401800e000703015800c084840d1120061424080085080040407100f81030390b03035004281412207104d40b400b0015190000c0180b189098010040f840300c003071a100740307103d00d543c4646072100028000100841e45410114007458480c030010740a8903000440030045042401d100d00c001d2409110403805030042c00005a0940c0010282d141004030780c0c3c13a602c2445070b110441008650000300115000c5500b4000610740c442010380001051210b101103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 89643346 1250 89642096 89642099
    0x909060911121207050c09090a0326062b030203090a050d02150a0c080a261009020d0e0a030906020f2a0103140c070b1003030203070b0c070c0b0301 65
    0x340c1010308108501e02801c0d04001c0c0c0000c2030b0001510494160800c141c06440c1c80740d07807074480d0410106040c41c0c0e9102e000c00061207030100002c80c003580482e00c2921031046803600381d250042c4003038401c0350a040d5200d0100014165080510340c0380c00c440d0308040c0c008540405042d0101c028118038a0542c010386c40400c00c2545410f207080d810f00600411501790943c1701141c0d0000b00180c001c402c0070000c0c19000300e5142c0d24039006440c1c400344258850b48058942410b504001c016850003000484020340c40d0001e001c00d200e90315141401114a5482d490b003882c2803085090107075000316101410b144e0388007013000c55021b0502031903c8007803107a071340c0c0303882d00303240c00341c0240f800b441c801d0101d0068106504404c042c3d403000801035a148074031040d00040d00301400c016401000408030441110311400300300040303541e4140c020075049124440c201c100c0d4460301744540c044c0915000040141c1c0c010800540810b28021185901052002d801890100165a92403030700700302c2d074011241510003100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 89644596 1250 89643346 89643353
    0x302041a0a1202180609073005070f1110410f0c0d0e15040506010501020d02031608031803040f030b2202061605032701090303020a02061309090609 65
    0x2100300e55220f00034201d0540741400170000e030f4484000b82c051800d1044c1940f0351003030020841d50070a40c0115603079070020210040740c034410242204450780c800060050a09110f258094202d500c2181d5025005014000500714079200901e04e104400d107a06480f016554a074403508241018168004000f1084900c51301242110600c0094002104500c1d94002c004084c04004103a6203020070a0502003421000f080c0818103011070a04c6800030540f0325020041070100024416049031000c4c2e0807150226801081203840c1d009840880e03500510180140c03000c20001c00195802042c40d03039a19040c5801d0540051455205a01501c086c00600d1410800d01c51683e042551100c58503642e2500c04094030341203038400440c0c8200900c6000085448141c0720746a02101900a5010040b680c0d95203030104064020180c0c07014401c802c4d10040400c6240b54454401c52045aa15030024030844000340d003000440d41040d10070107481c0800c0d00c4001783c20401e41c0110300040f805403000140500031400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 89645846 1250 89644596 89644609
    0x1030602190203030c030a09150e0a03020f070f0e070e0d050604020102060c040b0306090403051309090b060a03150f0b0402040e100503120702010309020d060e1c09050a0302041a0a1202 81
    0x6490042d03400c01d004101c0d54202410482c0e03444a8103810025880300c0c2c925142c4d00620890700c1d84240380e07103008048504201c0009682900a000c0e408445030300d82c154001c2540c071417150007460a0101e20300802c110142c847d404468018066040001c200906080401e2a40030300c2c120544259105906100c15960140886608003004800c0c80389064140305080801c0e100241585010f60192800281814411740c15203079000000900c0d02d00c025941c85400300a003c2c0c1c0340701580c1134045040800c119141c18501041229440340400c611421590b1499004100703210103a10340584640c1d00000755680c0780b009001600e00c018440340c8500380820b454041032569006240658440d0680202c5140ca00042d122116824a0f021540d4545440861034040c0b1003580200150b090203885c082c0400c0c0843c03400d1030040c1407000b49100b6103220030210364000951003038940020425100303201600f05904001c1c00c0381c05074052a8642d200003030128034400316036440a00112540440241145042c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 89647096 1250 89645846 89645887
    0xc0106121211030f040b0a09050405100302150a08040b0907260f1519090507030c0611010b0904080d02070b01060908010c081006050313080304030224043801030602 72
    0x82c00110300340203103001108000d110398010302c0d1298802003645080c1a200706401d1010b844090300a00203410a8a1446641d00ca6800128400c0c000350300d9505410180c8410740e07144c11456918100c0a40b1151940900c104020704414901d0050300000f10301001c81c4110720b85040080302d070030091044000040c40c201440382c240c038240798000e03074409100c80ccc20b18101160004028090002c002d84c02c002d070400205070b1000010050700800c54000140140c49108070701300d41454603051545404d0382c0d0030352308a610400c80f4542c06002c003004640858100ca014203103601a14900501d48507407a2034189281000740c8c08100010a29002440728460078090740040c0e03259030410b0400e40c2058000181054000d0040104010001c030004942c5112500e0107466950800103180c0d6a0a207130500a49600340508030140d06012200001d45070f681002c8003610858100c224040101007400061280c0c2c40220301c48103048070000c1d0352801c2814400d40c090b0003588140ca0050b0380d1a2154003100303026081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 89648346 1250 89647096 89647127
    0x305040312020c030a06020f07020a150306211106091804021201110417070b0403082802030a0f03060906081c02061003060c0203070606061101140c0706020c01061212 73
    0x3d0300240d10001011561a6413103440503843c0c8951850b00c000c140148a8003a41c001c9104034000707a150a0160f8411204041380e9003400255100c18006070402c2c6110b400045540250301e40c48085144031003030320700d071000c020011407400c02c06400003500c10407102c482800c007541c044148011441c0440030070007499081c200034045a49410340c41c00305800b0758843d0b079240950700001403d06c3c1c030041c04100090056810199103c0383c8030b0a0200f00ca4000d1100610701800d64100340200c082c10b4015041c441a45038002e615011030000c089540812402e910000d040d00c070309002c600010180152000352040100400b0004c01e0718280d0150745000c10302c0d100540d00b100cae05014800c800420300c407040c0c0c0d4016002040c10804840202e20b148502034019199030300e484004118258441011660030158000900c20064041700e90207000f03200352075034100032008006100c005100c50b0003400c0ca615440c0000034000c0da03201d0309040290700908044a408001c0a180c816003604400058901080b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 89649596 1250 89648346 89648353
    0x103050d170705070209040227160201060f1806050a080f1b01140c070905010e0105120105070e040e07081902090a05010e0105011d040606020706230403060c0912030504031202 77
    0x41c0914003411a1013504401307402014000d0005083d07450301450100c400388000c413144070b4004c2148407200301980070303200c0040f803818960014039035500c14080e03c010358600700c10824800d450502c80074100401040d080f4026502d03100b000038580e444145480040c6220409400d41c003500302c4072503003070440b8511540c104016094049138181d920106454904500f01070701640c0f80c141c07845a070702c0d001f0990300200120f401c9c0b2002140c446400c158090490f00142c4102d00d024070002c15080c00e841046910380000741d00c20703085c00c1d42c034038103078100c95845507080040d201802d48481ca03043c10300354403201c0000461042d014040031418044025944041e44040400255040048c5d1000002045c45014104024044941c805026460501c514034a000300108200c6035248406901d0700c6841c4180404a96100c20f40034800b0207001c0465000741003070030241c0c41e1900310380e0741c00000c05048510000300029240d011404005000d80786070708070f019881e0f4648482c03962070710f0000035035101e440e2000c541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 89650846 1250 89649596 89649601
    0x3050901090f0b0910110703050307020a06020a09030b06040e060f060d211e080109150905100501090603060b031807030b0a060819030509040b01020111070c031101210f0908030103050d17 82
    0x86d813031000c0e1f5800780c0d8907182903590b90f01c40c400c003240340c114014005801c0d54400a01c080741e41e80c019100c41d08592144800904981d03030802000110342e038401305003065812440c006841c05200103841540314070006d2204000c081c1544446014034070400c0900c0d60b281d0091440c0308000e03001209411114052501194002c1210800400b4501c0600c00d1030b0340c05480c0c0b40300c06110340a001c0fa01014204105080007640741944442914106911840340410b6903e540031030010301ca4003920081d15107403403440d841c40c0c81d0715010354034803402c100e02c074481d078000c0d41c4000c000200382c08a034901400707030030030007280c1d080c10807034020304281c2c000ba47c040b4003004011142c2c0000360413034143d03a9002402c1720002101068480142d0141603852107194100e000007031003400300b0a60721540d10540340114004000f45440b10015183ea00d510101d01102242060107000f40b16000c2c1c002000f1040d2040c0040b45803001943e8030b0b40b035504282c2048079241c01c0034202642075681f1440da404100c029403240440350 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 89652096 1250 89650846 89650871
    0x501080d0c1104060302040c03021207050301210c0b16050705010306150503100b0309150a09020f060a02071a0408060f0105062205060316180503060703050901090f0b0910 75
    0xa000000b0042e6000448100065880e40c1c403980007150040d00501109048000050086d80003172456041c56040300301080620748103a0540381603400303c106074250004130550170012400c903000c0498280c0d2000901058944a0502800c02900000c29400c01c0c80140d1811a040201ea0303040706040510f000c90803c140c03c00000b82c100c0903001401e02d540d980c0c039507517a50100750031203400000da02d81c4008280114144001a1007045403111411a06592940303400501a02c250300006540304c3c0da07104004a03186801c4005000315900e074012a00016500c03001001d03503110030180759145040c00300d000c200c008410301c02950305c0042d81502220035814038000803458026007041a10740501030340c000c680f0803d48006034001e0301008045a0700c0b458480d0070103550003c900d9025001407415803010241443c150403c0d81039550083c00f500c00756451403004c40040000412840c402c1d07495540c5036000c070310350b4202e01004078000c500b100101c2c80e06a80300c51400440318083c2ca9001c0c40d02c034881c401d9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 89653346 1250 89652096 89652107
    0x70c03080601050a0e1f26062b08090916120f0618020702030f0a240914070303090501110a0807060618090b0f090604030c020604081204090501080d 65
    0x55400d00b405516400b4040003102e8006840100c5500001481b56240f2500010748290184511a56541c0b004030703400c0188960041c00d1421001c80d8003071660201c0c52070300d07000c042d10361601c0001d083c0b20310026200d14011007905500005a69501d00000c080302241440310515900490006142e0140c0c49100d000a2204942c22402140c01d5990382000c01f150069411610051106ca400c148501200031260402588100c2089101c0c1c49400c1448988601c04544039081130b420500090300d101c0f0300038000f00546200ea403443c8115a40303c0c4142d000543d600d505805041e40c000084c048a42140744c05025284c1750b0b0003c2c0c1c1806040d84101c3c0c3c0c410b000180d034036819540140004e0b00e6920703614012000e0b0905422508898440001d40e0740401301c9540403114050188504603001e4803880c094600d1035200b40c1d800d56050300024006404280901d0031441003520180034546803540c1c0c4c09003d418105911440001244001410402100d050003028094090b01c1c005e4070f08a003484101170903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 89654596 1250 89653346 89653351
    0x7050403032001021e030105120619050a0219030519050c160812090d020c0a14040923030403050105090d0c0b0a020c10020307080a0603050c010507050a0203030d090b070c0308 77
    0x240c0e00d000502d4800381402901501c0c404c109562065035003a0032101c955a0a41090107040d019600e540b8440f0b442d541d00081c0c95000d440c00506485814154084c02d0700502030040003400d038240c007046117003009565000300d028011000d540004050521106a42c50003000d11500404541800c092100c13240728501103072400000f40c011503000c03000500c0c0480c518050782c076100801400400c1000301520011481c00b809c02d000b9420313a49a00c200b0010812048100d010b00b006081e040d000400d041c0c00c081e44810002c50040102d0700100340d03480c400c1701d41d00c4100c00d065145600007080070000c0001c240603207030300206120058410500442d034000c00d9800800e402030a402d0000c0c0108800764110b0703048442d2800710070142c400d00f441c566580c001a40c07040e1540f1300051501d4000803100b141620034030081e290f2000c06008400c800c0d40044496802010003910140605041c00e00141d408000414041c20340345400f081c9820207040403026550000d151600707120b94501b9400010b907000c44640da = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 89655846 1250 89654596 89654627
    0x70e1903060b0d03020c0111070f0602070f0602030c070612140709050f01020c1c020a081207231b0105210402040e030a09120c0b0a0e090709120b0c1615050705040303 73
    0x49003950380c2041c1d00e01c3d084680d4030a14421001e18002f0804135070119000041e10802d00246581c240e8401040384d80307201c3c202070b40000b0b802c094001e01145106100510070000720020200703035064600d1940300d01c4042030318454080743c4041020407490500100d40c01400b44240040c0018164000c0410184107400031007003120740200c8041c074215503c03d002c104c094004c1c0740842d400260054294841a1302504007501d101003103054010782d0440c14240301420800c0c2c80007504000f0403400030560a0440080b00c2418000305004050309015080300030345030442c01d03100306021428140140021202421080503813500200300c1b200d2901e0700701d20650221580b9844045118006003010b001000c8140c1001000300d500095244142e50301400801c02e04800301e0310790840d43c4860303109551614280c41001035a43c400110304020941960300d0b90342c07080c07046403100e19151504444d0031031540e00810440f1114441202405c0c6400d417403091680c40600b0b420803a282504544011307100d5008645201c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 89657096 1250 89655846 89655857
    0xf040204060e01030302031c0902030a061508010903031d07030206031302010e04090305070b09241b0408100b06040b041215060807030317041a070e1903060b0d03020c01 74
    0x1011922180c0c0000010100701e00c062600d03586034500251203503c4501800041005140780f01200380c1c081c418407403d298003c005046640560740c40301d014200c031884a00742c00340040707000140c1c03480a0007000f06583c402d0b0390001d24440490504112420000d103ca00d00394424034082c00142c0b6010304480c0c100c0e03a10913007804203604510040303030183c0070108129003081c1850404010182c02c4009412036500c00c2d00b20b62125603448005503920100b06e6500d00c401c03c0042000c8032030002c941c04090300302d03010307060007600401030350b246060740d6105074020121588000d2218083c0402d503c1008426003040700e41e103150901d0718450b406140154022800c0e601c60000c90042009000030000c85103950440c010300242d55a42c0384143c48410300c0c171041e000300b140c04110307040c0c45014041b060301c11503009030360041d452041007554070700740030040c903c0d803d00110840e401c04681e14156015008000150300200140c2949002026541d026911600501c0300092220003e81c0104000410f00b2003803071310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 89658346 1250 89657096 89657101
    0x114010c08040518040614040203120a0e0603070f0206010b031b0f0d1b031d0304030609150911010f0507022d04020304081801020f0c100c050d020105090f070605030f 73
    0x10703072440c85075a00a960000c00f01001c5409000079000080c80769003e00d10070022144545134168462000703d0f03000354580c0004506200c03843e2044040c001e4194140f5000450500300400f0071420b41c415070340d0201203070142d200e150100340d04201c40c90162a41001690075400c18194003022500e000c2c98407040001d01051100a1440c1013040e40d07030350f010306001800705481407103254040c1c6104088400c0040d0a01c0010915649150342e455400c05028000b1840c4c1859912400c00800e040002160301d4102c0400003c40010180100d1040d14080c11880c6071081e21400094810f425107040c0005016041c801e07500903a456014014859140c0300707802c203550080c690b00310b0f500d02100901690180c80071045c0402d0000e0302014281c1c141020140003201c0303484400580c1c1c0c0d00c0c004155010a90301581070b0800d982481003804a2700c42c10340c18a401c07000c85c2c6e0798495040c548074400210060395618104a100c400c01c00c01480b0324882c0f40c018091803410020024030b64480142031707450300c1c07a50001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 89659596 1250 89658346 89658353
    0xa050c041d010207060b120304060c120207030206190207050906030d12180c140405010b04090b010309150c020d090f090203060612090a060b0306100510090305010c11060f0114010c 79
    0x104507149001c0e4a000310341d10f800310301e005002450800d500302c2c01f0300c85c0000c000000c1d0500104440599280d610b41c42030240340c40d5650008550641405070440c01400030001c0181c84203405844000144801400c4481d0045d10081c03508000f40c3c402486841442d05000094502245d4402c4503070107854050701662124507501d0183c8085d0001030082e11003859044180f2a50304000310584020000d001c3c10900d44104100580d00d0a020322590032030200030800c5003e802c0da20001c41e034172040c107000c2070304034072a101c05180e02c800100f0001d030079490701140c1074040d605201041c940002c9040c085501400d03c0031800310304400b40101c080d410360002c0480c613241d8510f000d90701c852000c41d1060203140f90620015441d08070094040300c5c9a410012000320520300440c0a130310070380c901115000018605003c06c110008507880c5c0e941840130040000c80490360a008010b203078052500d96400903036022915a2421100a0418446841e20401441000310381030310f0700394016003441c2143e03100c940c0d0b04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 89660846 1250 89659596 89659631
    0x12030903170615030a0c090f1d0a11120109050a09030806011404050d03030617010605220b100201021c05040f0210090e0f060406080f150a020408150a0c020a050c04 72
    0x80d80e50803c3c1d00040100b2442c805a50440110251299141d00145503140070b04e0504411a00a25400050300b80516005d074985404055002040e0440490549202e06074030005911200404d0702c0402842e006014428140c020b2941010a4410030008041e00f40c0f070041c190040900715504102140e40302510502000741500c0280000030142c2c860aa510710700500280110b11841114201a00400d165480103101d040304540c0c02418941c1340400e01100b41c14041040c0700404645c0e541e6104040068807070460154260205400040c0d6136100310071801d00b445e848404083c40c03e800d0008020005401d0203508000c0d030740c19164804448251746069900400c0c0360040d00c0c0c01a111401c2000c01c0786101c84881c0140340079034080040c3e503140c04403641c486511181107032160b4041c8036107414011208000a03804211448018107103601c500c1d20038208a00340009892059200040c170811105610407034044a419000500c3c22548030381d145030319540c0520800e48240c3e0740f200d80e20600541c22 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 89662096 1250 89660846 89660869
    0x30b130203061e0906070504090c1e030f1d1009020f0315040c09020a0e01080406020c150a0b030a0312020c100606081e13020f03030403020901030f120309031706 71
    0x40aa441d0303032030708a031140704078154640040c0f020301061000c01c0e8405400310b00c40c0e02031011640c030603182606203480b070030151148004401c208503075203c1940d008440d0107100d400020050390040745400891b904c5009035061050000d8849028130381501ca002000202c09200c00003d901c0403d00c43d05030300000d40443c140a03409074060080b00f40054500420360403d600c16403148a6401d066602c1d403071007200320700410141c031010501502d0410760351340c003421540354004c4c0b0480001d80743c075984900c0355041c1150b8840007800c00081d0014043d04c40860f00400481070300560060451540340c0d207006111445442c81203642ca0350000314035001e01802d0080f91070700c43c00e916003841080d030b45082c0103040030411107050b9103245042030b02d0740c10a140c01d01d45034019140c1c208140f2290400da003c01404c480c034000d805a2522040000000513103072506a035008500886010200207800d052116000101c4a0300701d04243c6405202c600080d04000e075403031400301082044002c4d94841001c00c1800c00c40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 89663346 1250 89662096 89662099
    0x309010c050a02180f070509091f0302061912020901090302010f11061305100e0d11030408011404051002031b030a1d0f0c0306010515030717010303030614010e0a030b1302 75
    0x50748a083c0207070000b0340194014a185d81400c0103554404204580a0040e107841d581e00c1420b420100d98110400030040380304946801403405100da42c2e9000234041d501040c1c1c0840816220450244215046200c1844000b20305105514001d003c400082041e079940c000207051140715121003403180e01c40c034207000201011070119070260a1060003801c4086407414111054801c04442d16000d100b580100700d4110710702c000420304101c00500c251144d105080c80c001181c4001d0200184600c024020700b2070710380e0304c01d40403940d030300b01800d145040400c070007122904540108203014100d914003860703210b00081c1090860716a1241110040500401071a42300782c0500310504601d00d40e40401e01180110fd448121049040040c06140d12107109200302d035842035000d5003501c40401140b00441e80100709240c8880790015421180340409001c3e04141d0001c0d0b03aa950500094081c4040c2049140d401d00f840048415080005076112100b4000202241d4810001c04e50b003d181c1000e45030600e50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 89664596 1250 89663346 89663359
    0xe030d09030203130605120f0714070605010501180e01120201050d0f05010f090b010c0809010c1a07022b0f0e0301140402031011070b15090112031701080309010c050a02 74
    0x1680c10001d43e03940091082c0d80f80e640744c42c100010240e00a008941d00401b1028561800380e564071030340300f002c42004104c503003030060710f050000d90155010010428544a010000341a504100005201c044c050046050344103020b01c05000070a0030303060040c112510b281d0840e884c00a86d2004a50902916280f400b03c68106242007403640b8140e0402070681d050150400c180c5555204a10180c85010102030f0101e4501c45d02c0740c0c00301d0640030040c100483c040c105866040c5155072100340c20006002140301242110050000495061200c0c2d5604d00c004490380c501141045008040c02a24041040601c100650310240c0e4600403e084401004018002c00c400384038004070034034201c4211012403090140607600907004100e8030500d1450b038042a10942010980d030354003110080050b0a02c66900c4504900750416a21032f051107020304102e4903081e80d20b070003602c0c0240288400c4014406410034000061014680000c10364200c0282480c1818440900b800c18078248034202c1406900450f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 89665846 1250 89664596 89664611
    0x3040b030103111002030901050d02090d08041503050a02093105151f020624090a0902120d050d0f0e011d0f1504060207150f0615020a05030703030e030d 67
    0x3d42407010b4240a1058500e555030a5222000301e13140d10a501401d400b02d1014001c00140035640d50117486c81e076802a01200aa9180741c551090a800030b5020221038002c2002c404000755160244a4208550040a6040c500d00e4400100800d071515000d090151960000020000c2e22400075840c41804680821081c00d0184540c0b00d01117031910700358040e03c0e0030300038090f010700d698070a45810145607000e0000c40e2280300b50070803c6a181b0000300c145405207500c4071360729610202e485015074035001d00082c10741c01601c103110800351580b540241c00c0c0c1244103030481d41170f0031000322021a09810800101e13007825500c410024007070500003404561a1003030001c8401100c42c054414440410121a0039100000d0900d55403c294520181c880ba03483d00070500083c4160054905103204080803240302460706051012910281c10031141183ca40908100201d00070780d14610f250420700c050809002a034585590784c0c03040180007410996111000d00d03650f081072080d0f40380211640710611008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 89667096 1250 89665846 89665853
    0xf0b09010305070609050105040e070302161403030703050c120403080709090905030a0801080304061b060618240320011b03030504030e0402070f0b04031808030d0e0d050d0b0303040b030103 83
    0x880c640e0040f03c010645d00100444d65600840948040b00c48680d403810990341c415004401a4122424042d49041129001d8000a07241e402c0c1940480384440116168540444010700f82c039806064000000010000c03800310311850b84880d81d100d5050b007070924268444c00740407622540b0940c00b415040c2c3ca8034100f079003000f41c040001c280c210304a41d1030f406141d885000b0075480340318600c151400304040c6010050030700040300034030b03121a009001c005915a92001c03400c45d4001c2d2a850000b425548540000021141d541c0300d00f4000742d0000c00144003030079540c45110810301400c2194095080c1c80d400c0c0038682c802c040032046a0000803c00003904641c0c41d0182c06401c050f20210301159110500c10f455042904c00e6440441d080103203042100c0c0b9984070485449006002a000c00c943c2e103403488203c1c1c8400d442d00c4014400c0c0d600543e03172a6014148401181d651074006085074004610310104a80e205054488444204c9030004611040e140024034610586d4844564000040f0001083c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 89668346 1250 89667096 89667103
    0x80d02030309010c08091b0414011202040c030c02100e2103070e030a08040302120c060a090302090a050c04051c0203060a05010e1303091e0b0c0109170313060f0b09010305 75
    0x10b40081e50090203915030521040d51000b80845441110f41d1201a00350f01c1444410008003c5034400f500005003501891842c0c1e990172003d03044001c44121200300041103041034403c200400340e1500d020004080d290701c0094980400011a01100e034031041a01544038003403200e081c4c2400c2401188a03242c43c0481d0410071030b0011103510010400104480301c2d0b90402042c41c80c1c80342d038048049480c107030440e400c2001a81c103043e0782e12668132070040200e45030703182c501c010800c482043e00e40c610400d04c1e500c10442c0100d402000340315983d00346418840f4a13030407502600e06583c012600381c1d0103510520745100045000740d8003e035040c441e40d01032001c0c08000d0340c40301c2d050303645103507014840d0b40d1051111240c1d0703080940024000342204204001e144516000038a8880c072800141031229900c500e43c1000f50088221f041d01e5956a500c160100030301007030041020b1003041d8005007145071403e03c3c0c007041d00f8000c030003420a9860300c80c080a000d0059000304281080113011000558590501980c0e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 89669596 1250 89668346 89668351
    0x4050603040303140114060406050714070e18030c19150501031505010909030e060c0111030a06140d0f020922060b01021b130b01110d0201050a050105040c08071404080d020303 77
    0x602c80044001191b03000301c544403540e0304000036140900d0a8984a0112029407000c402030b03a40380030791412401d4150003401400018150080642c041d400d04500000040340c01c480342e004503074410800b1640c004400b20b031802d00741c4001002e200d00b603881800d040351059404030520107245c1c0b0b401c001104000814540344010b144003441003040b681c0312800d400c101c58454102802282d902817a81c01d5a1800c0c4000b41aa68443c100100d00e911a419085016800584905141c0340d150002030004400c0c15010503c01c242c119a00f0750710a02c143c644880c40d80c0b0204002e8015607544001410301c40c0c143c51106011507600d1903d24000a0a091000003020f60111003801800ba11004c1301fa141e030700e2844480c08040007000c0c0030344040700b070040c071005150701c40501d4180710340c40410f03041d68001848000c00103165500013007803a26241c0e1543e000c030346058004501c41c514058a81034265400801c450780803170f0508181d80308a5042c0d2540c0c3c03883c0180e078420441d9109140444088542c048080d50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 89670846 1250 89669596 89669621
    0x80307020a050c0406031505040206041203020a0510200706110a0203090306010902031905040c09110307110d1d03120c0a03091d04021017130209060306090303010b0a0504050603040303 81
    0x1124400483c0030030090702e0451101801c80005003000e00001d1910758805500548014841454103584101011041d1105c1d81d05401580082969500307100051045c0c140110110710200500300201030001d200c1c5e0102a0030415204002c140b1204001050340080c00441da00003030203480342d02076075000f940e9a00805910f4020b000741400012005828004c0c2c90142000c14110090418421040d00040c00024000c1e140031a55100000748a00d451140340b21018403100c610340c1da4541503c4c0500001300c00a0341c3d0382e01c2d0303028803684e41500d9806180010700d800116000b0030052010000030340b41c0384500110080c01d420004030000289d000003841e00742e40c2e00c00d0b11405030042d62002c50741001301d0600d010030605825000010014905240b045807181003900702203500c40601e0366940c503142000ca91008100c3e41d81c0c0e2201041d45450b018051748602c04400034403541c506040110740341d010601c034001d146900418a000b840740a9000d48018242c0500a41e41380e240a00740103000e01070111480f07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 89672096 1250 89670846 89670853
    0x30105010f0b18040617011514010e0117040609021504060c080c010b1302040812090a03030e0102071701090308090c01020706030b0307050301050a060e0c0a02030a0804080d020315040e0c0109050906010c080307020a05 95
    0x55100b080341c00411801c0350b010311400c44030f009c0351000641c0c403444048141410840003210341d21010344000d4180d0f00490243c000041c018a50b40b06004e400b0000010450a4600900040020651040300d038510268440141611a0807005c001c41c0902004042d09a02528580c540d1544c04041d038003501c00c40d24668100d070038451100000c2050341c46040060707900040c0411050000c01d0284003001c88984061048801c001d80d00c41010341092810320703140741c40e81d441c0c2d02c58206160340031403007641100d02e48010340403501c00b100c000303547c800c6113110310003d243d22000d80b4405a582402050002c08002d00244014a454600000208010700840c03040d04034503004601e40182c04010b440305c0d0190b5400940c9850300710002030b20700c105d0080044905010411081c492003a403030000c0e42c080d240c040001d1a502d03241804000c180d69441780000020b034401e0400211b140c1e4806440006c0313800903100c94159440b6100105c650b035008001c090075065001050180c940ea00007220400d050184058 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 89673346 1250 89672096 89672111
    0x6040b0109031104050903040510050a03230f04030201060b1303120203070203071404020702100c030801090509100504021206100f050a0e010e0a0e16060806030105010f0b1804061701 80
    0x15250710115000182c00604108020543d5041aa224130380082e4814126800c10b030b0b5a0000a4054460194102c00100085111a00c4d540c25001d4910315551000461175a14003110418891a100820707101160f4017060200e0b00f0b00d0300031b503c100301400503100826501d0100480d66043c04a1511045801b22502e10001e03001600c0803082d10003003603009010b0071480b4502400c401c0c840c403000c4061075100e58200f00c01001031303650f105021041407039600c80ca8151109802c1c0501441e10503400902401e060400300030714001c1c0454110070002030f4590001d0b036a111400820a031101840700e1a01d1442130700107205ca00d440d2000c6c0442100c0d040d00c140306410f0f80711801d02005a5143c41030002191001005001194039941100c0d4000541940004c120440b170b103000c1d01d064200b041885007025801818801c4c50f50010005600c410198002c0c0150f52401c0c007101294040361140b510380480109049080d200130050700c8a603240000c1c014010300e80c03501004499992181c0b100c001940c43c000a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 89674596 1250 89673346 89673349
    0x61005090a0501050d020d110a0611060f0108120706090807080726030f1815010603060902040305030f07020a0f0b0a0f0c02010f0f11030c0a17030f0406090602090301020d0506040b 79
    0xb528140c030b00c05080b4000000080e424420101d00b645000c94107001c030b051000d90a51642041440280241e90301c0d0761264580c0710070700e0309020000d00380d10b22800c01c10005100c80300300001c5c06903218004038822a034504980c104800205244900100340c00d100146803000c0c000c4000103800c01178040ca650007203810100e5508a2011850b516a0100c0b81c000e0002526070300c04507140079071009410311009003c82184030a00d04282e8000000c90610051100500007a030f818413942001e4580803404614107421500c485659000b4070140340c0b5004030020303a00d070841d151002a84014203205e621040d20380c2e00d40030003c1980e00003004160005901050b42000b1034440c208a08031960107841d00c1c0d6a000c000c078000ca600008800701082884030440a515160500300000c01c0ca072400d04002d0000c1501c03c1c0b80c4224890420761220841401c01e100744044800c403881c0345504158020342c00909440d8510b00200a801440c2c822689035101041a202c0e450b455000203100e031600722010420000c07800c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 89675846 1250 89674596 89674601
    0x6030606050a0f0e0a0609151e0b0f030702070503070806010602010b010503040803040308091e01090b0c0a0504060f03090f050610080706050703030e1005100807061d040c11061005090a 81
    0x3c903100380d030016040c0810010802604a58000c150400c010514a864403036030705c1500c400308240d42c0f45a41c204001c002c8908200c454502e88005000c08402c802c0c50070001100c01c2c0100c01701040345800000204940074001c000b00300041401505840100da40c071242640c44560034400e040c059401c2c080d031b60b82550301c00d0b030450340f1884d40321204a041d51a0360328102c40d1000c0080880b441032140d0341d030a000300204100c0116281142d1000481d0500241c0740820320300303001504200f0040c2d0300b03010041141e40c012041c0c0d0251401c500c1c04811440f035000e0128050030803101c016044980d40b5500300140305000c2682881850080e002c0052550f46503486559a03400d40724100019800740306c40c10029109400c0500000d01c040304580344040182d00c21012110255140411520716150030841c00c03c00b0701c03040c0700405440c101420038030041485002c00044c2000d03154400c560f40d2003a0b82e1414020481c1c0b1104c1d00507401200c2035172030001d1900c083c906503400713414410245540007404212050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 89677096 1250 89675846 89675849
    0x6020d0210020702010c0b07210603022107061b120314090d09060c0812070e090c03060312031e0f0601090b07020307030609080408030a180501020f0c010f020309120106030606050a 79
    0x186d480c24107140545e1101c500c1240c020f440c0c1020040c0102d141000c1070002d40388200180c840e281c00003103452451040241d04855800f000b682c280100440041d40400030079010102c40d8982482e50a4601e583c6100f400e13070410900041141403c003240c070303010a0340b50340004c4141040103031134500c544601c11529540c1c200e110f0707035a000981404050040e0f503c42e460003068644107688183c1080310392842002140800c40f483c100003166104e01e4040c074034000c214141c100d20915403180c5076080a0000c29100c180c40d9804145292001010544100b084986c00c07009510303155030100b240c10070031408820403a080e134519000410f03565001c660b540002c0c0454a002d0f40c0100205941841e41d0340d40c10184c04081803d54502400744000a000700c0d061000300000300707490392440351076161b03015a0304607c0c0399a04624115800406100b8401038005482215000f007420104903542e10010300300e107184141c0704103580241d203404401202c20303415049002903034800d142c240001901c91091024030b2025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 89678346 1250 89677096 89677099
    0x1a0c0306090711010f06150305010f030b040b190c0206060901050307140d0809150904060e04020102060708040c080a0f021e10030e03040911090901050a080c010e0d0c06020d0210020702 81
    0x1c4402003000580903c221844224000c0d0000c903400c10345003403040840310280d000752908010300c281e40c0c8140d41d06200b40c3d40940b00a0517030301c030301d00e0551700c1e505020341004200030404006c500c0803416001030718124690b1490b1261052101c03062894000351079403030a548141c011070000001103414038020900e6001c3c1c803041503d01360100c94007800c1020800403000d00340c80c0581f0401c42104152141a50f016040a428a1065850545800b840200e4505038024070070201c0710018040180c5e07021840c0380c0c02c600d451406901545075428108078480050b03100b076030948503500342c0500f0018a00c0500000500803940714290140305000c420f8602c11800c0d440e940002403400c0c035070125000307138454a80c90301c800049908140c0c0307906582c8111440000c11100704440454003000c249000018503000d4030080c3c42808509290080d280da03030300c0000314498140098160104200e44420310794000d8150080110080d00ea9200d038060340317640e02c2c05078060060103822401480704180b4002c8a480760350 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 89679596 1250 89678346 89678359
    0x60c0c09010605360303030108060f0c0403020d060b011416170a0206131401050f0108160b0405010e0f1507030906230d020c0a030f11070f120c030f1a0c0306 69
    0x648546004038041c01503840700070b91400c0b0760802c941c0c5c40801c00781d401382018800414507800d110409a200910007490000307c114200030510050301e03180c80e0a0301250b40400089100e92120005942c038008a5010440c602d5001c18403c0401c5a600c807403083c03150090784420401d803900c0042600d030f40f040c0c02510001d42d00000200d00c0c51401c0c980c0503855280100826080841c107060b00714203451040c0c543e0000d15402c01e0041c4800070341400b0a5803a400c03182d003e03080092034418011240d010758440c03581070002090650010b07466400d02c054400c1001040c009280c4292642c0800e0342c1c010100541c0020400318003c0703450360050008200074046070a90b0380040c620f581d6602c10070b90140f0100c9000340c2c3c0a001c0310300504001c001ca02c0c5098826240c0d192024a50744000b80044468000c01c1c2c01c5611103c1d00300401280301c0d00900c195040702c0301700080c4443d6800d014248104542c0000c1c004c550b004522802d110450400507101100ca2010030020303100e204040c0138601042e10207652000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 89680846 1250 89679596 89679637
    0xa0e0d0807140f060112030e031f05060321070b0f0103050703020d030e0d150509160b09041401090609140403020c0f031c11160f060e010e060c0c09010605 68
    0x190300c0358400540181001c03c071182c2c00c50720450207003064001e91010440d5240141c11034205a0805516044017005400910566007800d0000c3d0b200301501c1c5106111607070310b201050310b644091011510f9503403140d0a20051100014540c0c00c1503200000c10359641c0341030804a280101000e0400381201d410400400300c06046400700241c50624001c11804d2103140d0b00900b05039122481a03180e07007409200480c0381200000c00e82c00c140e88000301407010702e80168a10310b00c0c00402c038000d07e09580c0044c050980ba28210000b06000f841030b15108008088007500015160b01d00d071700008242c038441c4605100d11015580288040581527034001c0250300f00b0325a0044a00303200d100041c06610040840700038491210b142280381c200e1881004c00a40100c284c1d1482410810001d540e55001000508405241c840001a030106c4c6010300781c204503160800100c541e100310588000602c00520f03182c0d0307500f001864075075140d0100040502500c450000000c8160040042ea03d0f4017042034242c0304044e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 89682096 1250 89680846 89680853
    0x504050f04111806070b040b09060a0b1c0503132c0f0408070c0509010b090909060c0301050d140601090f0b03010b090604020d0905190209010b0403080a0f120906020a0e0d0807 77
    0x560222400ba03400003400d0041c05c010901c9403100d5400f41d07010703180101d21030a100004030308002e0002c001141040c1002c00381050354403120441007165104441c80e4003228060304e8641d0a500c50b4818510072034480e1600440c25414410801103407100c00d01c481e501141c071604810000354000c03a501e04104239041e00184c04208690300a2030003a00c0b0340e40e07501003140c8810010f01481c2007a04404141c02020070260100e040071098190010101c00080c0054a401101c9640c248014012a4010032203450b0b00c0b000c00884081070541a5a1304064440a40c2c48041180c01001729000144040d1300704214480e0a040621075040a030380054442e805540d501c1c41404007a501c07100e070401e030850362004a4408202d0600c20f58407689035206481040111900404c075103002e06802c1181d0424080001300b00190307072801180d103110b141d8101000070448640b0152240d8444149614017203080070911010054207500410804005450f071080002c40c410911076034000340540285214810020b25020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 89683346 1250 89682096 89682127
    0xf160f0e040902030f06160e0f0306010302040e0a0f030c0201090b09090114030703050a080403020a0e0f06101115010e0a060501021207050120030907060c0f03030b0604080a030504050f0411 83
    0xa45001800710317100800700c0050146010021500c04850b5104e002e0b0744018543d022005130001ca4084030300510782c410b2040088e46580d01031000074892030740c844c1840c4903800144200040542c0042401c6421326081c20701034199001140701300e0009a4203000841d032001644140e40d0841c070b02601240190b82008030b510300415407000503540c58030401d00e0020005000b0000e2200c070760312900740d1a4171540b0f184180b092440c03054106814061220382081424100c0581d8a035000e60225080c07102c05400c04000d4402d6882400d0008031400396070010f140c450740600407541243c5c0b110040900550703800043c80c04076251400341900580180b82d035210301e80540006002024081d200004611403902c0c1410100000020000002d05010042044081c001c0c0401c01c010b11250912001150540c4d481d00c080d8bd00429005041c103545a21001c1a500d81c0d0f01580d024000d10012285194041d06020705150402c0c0f140d244144808186050541414029411000300d00c505d11820040110781603a103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 89684596 1250 89683346 89683361
    0xf0315061b0213020d02190302030412050f070b0c220b0d09060b060a0207030c050f13020c1f0605091b030c0309010912031b2f0f01050f160f0e04 64
    0x380320b5a0343d119a0a00c0c1c0080c0b00903c0b60000c00c000c0181e940d40b980410b00c0d01090180300400c05d0501c1841000302142aa04595102c0071a515156984200d0b20f000145c10340214240070340303018045802c00428400d514024025110b21680d0301a804006007016030354044503005018106e00c05211005062400e9088a10150311811340403411090400c00f140035600034040c0d000040c1d000030010400c1c1b020b50141180503040650b019654050407502203554000c08854025096034000740ca0324207001c091107080c040500c110728140da0b0280d0000d20704040e0040b40111032143c0d103124041050419000404500712403005180d50030b540c0c074001810712940000308002d13103954880c2c10500020300d0b9600801c01103c2c26403800100088420030700300740c1c81d00424106003401400950b2545c000c0b0122903005001d2400c42441740d51040c1c4d0b019050420040740f52200c800d6003028140605201030038110703441108070428511000c1d4199008540b420b241814000c04200f12204910860400340c100c0b81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 89685846 1250 89684596 89684599
    0x50111010b0f01030e070e04030c03170906010506070204020d060608060a0b040305150601090b070b01060311091f02010f050406020a030c0c0c09050606160b090705060a0215040614070f0315061b02 86
    0x40c045960f5440e00310b81c7c0c0004032401c400090140c0340041c00c00d0303040a20500b0b800034996042c2e4580ca01605186d0b42c0344010300541303200d600041040340c219592901200c40d1004104070a0220316078540000d0300c1d842045d40c10302d10501016030049440e00c031000c2518201d9030004000c2100c40c2040d08103500300d1101610987c10008401d80200d00302e6001401844214070075001601030b50324192000f42216510040c0309000103040244c0d0545030340e201c81d29003260042d41c94151109001d490b081e401403c100c08020142e0382008100000c1c00503d43c0a0300743c4502988040c010310b165001c08552804010000503d4401803103024030a011721075214a90100780904080d01e000d2071051242542110144115403540344401009211941409200000c0c201030f01d50074103040301080007948a02100806080c034000840004040c043c95800c0400040131403e10784000e0b0a0290000300300c500609a4480400c2c14a41d040642c1e40030190240201c90480c0e8031500300a40042100c80344602004d0282d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 89687096 1250 89685846 89685853
    0x60f03010308091f0c021806060d05190c020102070b10060801030803061c0506040201020c270c09060a080a05070804121d3715050c0709020301030606050111010b0f01030e 75
    0x44030b00880a11400d00300c0c50142e11586101ca05c40c1c03040000442c82d11946228603000300c41800700e5512140c007a81d00c0145040b001080954a034507042d00412195089088003604104506000f150194004e1920702d0007a0740c030308c00f9a514851a403482d64010301c80c481c00121448010000f05508001541d080100188482980e0310203900140b81140320640954542c1c01c01e1013400704660301003150013824a001c1d14031a000040910705a01c60b016a103210020550a00c4001124403090074100d80c40d10308010711064840c1141c14000b0a580000c94900c6071042c034000c08100418080e0364014800c650014820340145a0600308031202c2218120303070032062240c0048015a980c8140f07030f400110090146101d0300721451907513441480100c480742c0ea010662810180071f032400b503948585e210b47e50b07420f0030b564038104801e03c103142c084194044665544084008000c03c0015040241111000d81e240d0038440100c904040c2211880c1607001d50060f201081954154000d81003000840e80403c1035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 89688346 1250 89687096 89687119
    0x10603050307081903200d0e07080715090321020a060518011404050705010f1b0503040509070516030f0c08070f0501050c041215230103030e060f0301030809 69
    0x4440c81d64001900441d070038000400c011403411003d0010303811910b86858180100c03003216034040c003075480700040d03000307410070008442d00210844e800074948550458101c0c0c181580d1030701195202e11807401f4641188200d16005081c540c070500b0120b041e02e0f0003019100c0791b01c1507580449400c107881d0340e0500960168000c0e200104001c2d01c986445494550010031480c02e001090508580d04051420345102d0f0700c400348004110300003026401d946007070a00040c5403e16140903038500e90b10741194a208030070704034624200314020010304100c4105560000003070301d0310041a01c10380a0515640d21051046c5080c00c0400d110301014001101141001c085540ca561510191580540030984041c44907040b1201000400d11a03a540070203a50001c40c100b0f410890b0032200c52021040c05041d104682c14418074545495010301c80c0c401c8d0b108000b04226045204c02122402e092105801150880c0d007004500e083c1401144c00303103202c036041945141e09698908100d030300002840340d04a02101c64 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 89689596 1250 89688346 89688353
    0xc020c190b0d1d0c091b040b16051b0f01110d0f110f01150b04050607030305060303120405010507020601080d090b03041518060f090305070b0a0f050705041e080705060c010603 77
    0x2c40c11a102c83d07407406066142010000d011000c100640354400e4424202c11715a95805840155403e46024107400c0307039944504510b0703102030980c12002901601800740708174080e14001640c40d60b054803d03100c00501c248110015191080c00d000300301c8203604190804011103102c0c00000c00f0100450030300700160329903040c00038030b00070040342c02540f80d07075407400e041d40d414820075594002002c0b07900c0300524250030000460900c0c084c00d00010107168441011900e6170380c0900c169000800b10b44880755103882d2904005019140a54603100980600070000c100e048000c6186d2941034045e03220142c801d4078021072410f1130b5100400666041e1144060b260f00511580194458816503802006140d0702e82e0030908100c580da2203e103a1a145822448800641c02c001506d200e07a0b00030341441c0170350780e0710010031015020500d80c1c0c15010380780104202c03036550080060400e8460b40382c00c500e00b14490640700c1e55a07000c030740500225603004100400c0189080380051050480b60b00000c11126503964 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 89690846 1250 89689596 89689631
    0xa030905060a090b0109050403053411010806010c020a1203090504020c030c1c0906030b0f0405190e0304051e0a030507060201091406070e01030b0a0f090c020c190b0d 73
    0x301c0b25444652554000014013121028040c090940000c1c20009402c041e98043c21a1003100407080c20040e50384240e0101c000741015403403001e91400c030a1000000b061425542c14181410300c64045121100440c269511509a0072032540d805440903c0c01410484403000d05001c44100b202009000c8101042d40e46a07070000d448442d87c0c20340216201c408240a407030030301122115503140302481c0d2103420309542c0c0c0900c1e2841210320358100028015004400b103064171000d4402c031b41c0c202c0d0402d42031219034000c1450300344061040784801c0180800328004180c072407145200e0641d01c902d03c030b20040002890902072813001c400082290040301d5807680c440b81401e4990f80401c025075903030001c1c80180b1102c0c02d40610001080c1d00074044518290b40c02070000e56a0b100601d04060744c8016140090310b4015100016045400d80820160783d51050080940040044d030001405120740d01003803410001785801850212101c0d84e040b950070104080603a4122000d601491604e51950349042a0501c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 89692096 1250 89690846 89690851
    0xf0405150304020a17100c030b04020705060702060a09200301020c0709051b04081c0315290313030e0414070804030201061406070201050d0b0a2315030c0a03090506 72
    0x35010261a45020300401400340d482d82d016202070072020f20030390100d032004503ca03203015013102d00002e0600f0036420110010021139a040303400c68400a48a03061260008040744108159401c54410b580c1c3e4060150030798150300e1000f030807030004080180023416801024000000050001810300400200c000d103804481e0740129400350b5202c3c1441a001d0711020060416044102c9540c505494200e40c41c0d034030351864100d0f1141c414407044801c88244207800c0b408610101038030350a003140d228010400d14030701c8424034001d00c280307882c00c8804030300d01c4200783c0380b042c038041c01000351b40130b01c42c2c5041e5207000c0e1449100d9480f0707039145c000d2040d44140c0c240c0c03103010342d80a5850141d03030b2034549400790031260141c2003440c2003901900c0f54003982e0f4403e000c81d041640c0c286407a0352680701324111840500400f01c041584a03451500200d1003031080c4c03060940d2020103100a0400980030004e0118061600d40c0d2110804010000641403050501c010400c0e6500c07454000780c40c804613140c81e4140743d000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 89693346 1250 89692096 89692129
    0x30c15030109050603030702011b020a0302090718050d0201080c030a0204090c05121e0105010c060636020f0403020409050c040504060b0a06090e010e090f0703050109020108011202150f0405 83
    0x10006110460031407041c3c070742c4000306800071450141300380c00192114240030316801c1d4902010104032308545907400b5180080da4054a0301540c0d040120f805030140c010b109460401d0f41091400081c523240600c268006180c0603160403040c0e440b001c40c2910154002054110000d408100c0016403100a1140300c2a04085075902078031183c0201c33528402c800040c240260a209001d42400b5117004100603a0444d83d00342050002c01c7c069103440400303011035900910030300c400300011034607a000900c1d0f076603402e240040d80440d828034003180580803402146040500c0c0d0f00c080c0b10500041c205584144659800b480031500d040c854500082c040d41c0e0100d404913940380d01ca2100b4400750400c0380043c006000b1600b01511001c0c20003081c2451040144604101c81c00b1400110b40303175150138030890585903403907130503107950a4803030134114007900442608034001880840002400162106040070342e590040c84007041180a041c50891a00a240c88101110003000001126500c0c2485448000340703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 89694596 1250 89693346 89693389
    0x304080d030b0105090a0b030615070c050307080607020601060302031008011a0f03030406020a0b042a030b0c030127020d060612050a020901080408180a030803161404050f030c 77
    0x40c120802819510762500c91814003406200d9900c150b034400300110300b42c0e4102c2d400725850340d4074038000540804880391b4425401d1030004a01c014030442c0f85480f02507610980446225540d20f00c00c0c90355800c000c50f2490b0060b0040401132054510a80085810204007204482126104d0140c1c1d42120580d0095a02c403c2ea40e802174540350803c90600d800300c0714110b010b107040c50302d4002c0182d04c915004030b00404039854900094100400b41e051611000c42c5124900369902d461a050f100012203400140c0e0b2040012000851104640c030889040c0c0f800c005c0d001d044141c41410b0b2610b81d0784c1c084102d040e095000c4c80308400700652440b90000900803a0b565840c2000050034403021070741f010303000990003401000301000303a90300029090340040c1d000000030b560781c0c91444404084e6040c2d00ba444d600107030501000040c062041c000d1400341c089104038128041c29628185c6801100881c1311000b0300381440100568901400c601d5000b42c07004d0140c50701c40840c1d01c0041d01062440a0b003a84208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 89695846 1250 89694596 89694613
    0x30c02011e0e032a06130902070803040501141618150e1f0c02090901020c03030109021215010f050a0e0306010603061806121101170a02250206030403030c050c030408 73
    0x14080200320b16144031107544206903e81c8002c4008110013606442e8098003000607030407400c1001c001d40b400104005d940c215190b01242c1f90041d481e6200741c40039107a80d807d060b010380380d80100401250103040816010f1321941e409090540b84c413003089428604003c5000b000050320b07041c1003008200c510729950b84401488140080118070030800700210503414445400c080900d81201c410b02d072464045614021950324220050b019224076900c1415070301000c000001c104032580c0283c04105051060b09003160b85001d00d01603640c0c910018507001503982094000d01301d02550042030300c00e5492030858084803068003c2490200203920041c0026601c00c010007046425410100c100c850002d0244001440c050000f60923030201d15016114201040c100a0a40c0c02019040803446c054078480c4400e25280d0703d444029044007108074542c000c80d000c50b0300344030210f16028100c103500421141c20754480d61011001040c600c3d2880381446010040d01c0b9181c841040940020300301c0100604591 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 89697096 1250 89695846 89695849
    0x1727120a061b17070809030705010f050106121802190504050c040305070807140f0d330b2107050d05030705010b04060b1204080d11030603070608090a030c02011e0e 72
    0x2810982c90754030402101c20b001c0c54010100c60812500940c3d10b1a241c4030544440c0b03816410f610842d08010460362805483d02e580900700d8004034122400750700c6580703040b68003d90260035108000681d400c801d151204400c01454002d100c1c031682c0c0c5000800749450f64560f0301282c1111001d40e0700541d013060204041040102c10081a40a03124100250802e641751014480a0480c611380c1c0b035104452010b10301d0603030345a0034150381070700d600039000140013603a40b81003103091181100c1540c00140040d81d0164802d6560240c190f0750b150280641050725076200101e201c004400b400a5030700c0c010a01c00042a40c0d03844110f5101a0194000d107680345402d2601c02e0844040360f181900a609055080000045400a42d107103000b01d00c24a0070a03594030702c1d0041c0b851003410380401d0094a0324040030390710030b1502c020f1072103441c2c20340445503010b0711080d00365100f810813150f18106074002442140000d20a40d80038000314810b06128404d050940c0c19241040d02c0b0441140004441c8140903005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 89698346 1250 89697096 89697131
    0x120e030f1c030e0706050313150207060c020c06040b03090a08121e040314070303060503160806010905060a150e04090305070614071202160501020f071727120a06 71
    0x103107908082220100d11250607450341d100b4807800c07003801000b000140041614420381e0003410f500800210603e9400401d041c025081100305642840c9002038042501d070000400e007910b4400141210b04007441c10035203600c0791b40010320202c1c0d107000d042104800521410050255080003901160f09442c0c015104202400342c0001e2038010250361050201083d04058031070391080000801581e203050034207040e0302030030156005580501c40e641c242c5140c640c84000d880213803507012041d110103998500d06141565426508150300c040054000c02049014094a01c1e1358070341420503007240f00c142c00011781180c605010903800b00301e002031820300300000f6104030a060141c500300e0300b02905050500904005400f00c8141c0d4195002403046505000e030701f54400842e0340100250f41d02c801a0014000a400c000401c46120702e5800740c03016006203c0c003e40d00c03038040c1d030300c1c3d500d00c2c42c3c0e580d803026425050f4441519401c5030341544200d18070791040c00800d24990188001041d0494148110202d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 89699596 1250 89698346 89698393
    0x9010303023009010e120d020d11030c07120c08060f1006020d0e04021e0301080f01061a0702060901031e0504020906041e09140303090609010b010c0f120e030f 70
    0x32120041c60b10941610080099030780c02e5000380792110b945d0302210045181480c22443c100010b1141c2440c07034461550004000e078910041e5940d8102a009040005a80380648140c2111f0398100e4041440181c144049840341c0e14010b921442c4242d58540e10a414200b040d00c82c0483c042020b810049582d11031038244000f00890303c0140626416044003d0003000c004404610980d000203080d100d08540100500004071a144426903d5030341e0309003181e45950400b40220300707500740600090740c801402040c642d91818950224034080907903081100d03e90100c4440b1713043c160340354019201c82000c50300248881c01402000140c0c1c0c103140c01000444280240810b108501701080b5031904001510109840d40c82e000000c110100c00c2d18241c507103155017141101142c400841000742c0810b000071b1985c0101d495500800c050700720040111a07040800b100a441142160380c440c1c0025030b8203018001100281c50814425142080001c1c10410b051542d111258800842155201e03481d618109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 89700846 1250 89699596 89699653
    0x411030a051e06090a050c0c07080c040b090c12190504060c03110301050105040302040e0a0f0b01030c0b19050913060b041e05031c030f06091a0a08120703030b0901030302 75
    0x520030319040c0000b5138610b400a020000e91030b141c4021442c201403034001d640843c440b500a460f403254640d2209540c0e6891302d14100c1c403990074141c035414130b814802c0b405401006110038440c80c1c0340321010b00d401c1d0b00c0b1001d0075001c00c1d00a48500500d03c840a44140e03409988180004240d03405c01a2000301a104441040e600c00c540400c01081a603801c0021a411254152000f150740c0d2580d049035810b10042c010003070300c1e0f02401843e12003000468000391b4181c070710034005200c18503100c00c07200f0b48500034401d080e40001e1a05841112050003640035009018000340240104c01e1900305030020788100d0352041e140030202080c14408905071110035000554484103a269252070440000d5440703201500d1405054070702030a040c0c0e514441c2d0011500d07061614801d02c10a0f0752001c0703001c010a44140d40349019207483c02404402c2c0751080208013250040b00040948680d12200c10b00c06521043e8100c00b49030f030310a0100302c241c070b8940986000394020b8025000c0f0754402130003900302691015402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 89702096 1250 89700846 89700901
    0x1501090f0507050301120201090b0a0e030601170309011d0d031e051603080717010e010302040c0e011218020306010b0a08090307080a0804150e010b1c0b0f04020411030a05 75
    0x2d80f984182581d046071640c21401d19001c00e41c3c00144c4038032507a41c112208040740012100c84294000c0354840c00c1400580c2150b048c2e0307a0351f0b102610030903204d520344205a00708002c68049980310320f07499803220b505001024102800e07000002c401440f907a0702207000c1011b43c1411481841c4200d03403948001d9403070174402d103030109c9070300d05800c01111001c00405118003030740410902d03407141d03903201c40c10074403ca4448029610307000c09040080003440200e10035428200c0001c0c141d0310a003d03000780114181c450103141e900d07000ba0207014142c40781c07264100300092514038016035400c110b0305000b080c9003401c0c5030755000f011744000e240c4a8001c1205169038820000d0340006178800301160340d50701c0285030401454880b490407007145c40d00d0110707488116003007a0079038100f043c040d800003560400440c2c134100b000358203210341d20314000c1c07071003000c0c0881078008001050301800442c0190701030f100420003d404030a03020031102d0350300709451038890380387c0d54810841c4e4551142d604031080c0c076492011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 89703346 1250 89702096 89702101
    0x1030c05070210050903030c1015050d0b0a0e0111070c08060105011d040b060d0203190510181401030b01030b0106020304181d0111090a0b030103030207060f111501090f05 75
    0x340440c4500e0000034000c014030f03101c000c800303485202525900070004060380d0380c40340e548250540c0d4030400050b19008c4c5240000c0000c020f0504039040d41201c1d4050301c2d611441403240c44041c00300e40c004041c4600c50b504c5118403404100e0030310500481c07919072402e0315250341885c242a80341110503040424260711480040c001d90303801118101c013240c10321407d051020303541c40105004d040c80018040c0c2006010400c50242803051300554818081e1b0505070030800b00c101034030300540710269000c0403800c00310380050002c100d2110182020301a5441d010481c42c0c2d0440d884042020245e00c01e5420342d400a00510170444080c05450040000d03200442c1454280b44203240d45600c084009019256140084013015000c00d082e04a52080c60008120342e050140791101e0551042034020311803c010480410300c1103881c81524143da03010f9005002072420038100365201040c42607020305201030490319a25a0100700301113054060303403010108080d45032841170010b980c0c6030003410001074100802c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 89704596 1250 89703346 89703371
    0x924141e041412030109050106080916051207030c08031201090912030507020f01050a0f0b030f0303060607170d0219020109050d051b030c03040510090f06050906040e0405011a0103 79
    0xc010341040c0c001081c080310205040031140b41843d10b4042d41d40841c2c01000014030845141e015a040f00e0881e2911740d003941e03d0110700368803092107070011201d400e9690424001d90500e41d03039141e603032018502100c046588a8440300308038490303a44041702c2035200161540c0700302c1c0320b0302d0641c0c01807004400a01401145030b80301c06010b1448440c01040581e01c20001d4031092081261203802101203000308580e09002074000094012800122980c1e400c1c03103203011080c100054003682181c200e5001c0e40c01c5450302c000b00091507001070019074076042503001281d039000c0b030720000b0310411000000040e510703503e10181d80040500f114110702903915041411000c5600440d82100c44042445c281d6a01e0500b2407540c0c0d8141c10800d014400e51001040c2e4400f00c500003c000d000340c41c42140c0e81c1040c40c501c8101103030241000d000b40c400c480d04110081021900130000b0b4814803030000d28070fa003059110160b45c0201700b0210f400b500c46a45075030740550700030b000c1c60a24407501e81c00e2a0602c0110540301c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 89705846 1250 89704596 89704651
    0x207060b0a0605180f0907030c0201050c0f040911040b0c07050a06050304020607060507021207111f12050403050412051005060402250609020a06050307020d0f0e0103092414 76
    0x989080c10f0644060342c00200d55107803000300e0a41300c00203240386d0312804c080d1001002001c60707442e804095031900c40070a040151800684510103924514180340c14100382d0258050b01c010400d5420b4101c0900010510f2117080c80074107a01140d038001018101e1810080020402c129800319003485010801d00c00961184011203640725044400403031543c403010012442c102c10406010001706001c1b44800801c4036244099141d60781c00c0b01e003002040070607203010310740143d942c10aa02044d00b01c084000d0b01c00850304030766840740c003a007000350400f80e0725040303041500f550000464072504564280040c598140c072899410100690b1304505115844c20340301100040741e480003406440513100e440c10420150829072005502500e2030030710583e85d00000d440c3e90007c0d1a02e20250203480112400b4900c905400807203c1d000d07564540384e10001d05d00640041081c400140d401810300c601e08501d01c51004a0340080104542e0009039040c8603030081e0003002c0014000c2c0002e01040c424054013011500c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 89707096 1250 89705846 89705857
    0x80403050919030605010801060315020a0215041514090607140405191535010b0703051908060a08030c0d14071e0b01050315040b0c0903010f0207060b0a0605 69
    0x690307202c805511250b0b214658800541c0c030050949007003e0012815075010b40080c42101d2007001007210141d00401d90406a0083c41c1c00480168030805849002181014400790014010132200130054440c05142080d14484085e0095a0004806200010008100c0c0070b6100100e850001408085012440070700c1c030503030bc05c092203800071070410105d0340380c10b10144004100594001381116000c03400070b00000c0c200c00c0c180c51407a441000414001942803600c540003201042610300580c01c2107200c05458010303000c1a000c210040c402c41c1d0401840c018604929401510f665034503240c03850070010000740710742200c0c08642040c0410f101d507800000d05141c8103240c500b00580c0b0001280350078a980d0040d004080d000d50221440060003091032245c031245140548001461aa200c80030b26a448a1113980c1d411449101000503020821403070a2942200c4441d01ea1881c0552003070019007500c00300682400c40c9680082d49508010651140b1400c0590a440b016039181c41d003103002c1c2450082 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 89708346 1250 89707096 89707099
    0x91a0609042415080601080c06070b060915030d020a05070503070b0d0f0b0a0f0e0115020a0b060f031b030115060903060209060f0703030b0f0103021c021308070b0c0d0804030509 78
    0xb000301c40c031070705a02c80d0001d1200c0d00007041c49007403950b602d50300b50761703150300a10030380c1214050210480c2c1c090800c1421140302e2034020022203115220f038820f00c074104030010b001d58010b000d0511036800c1035805103d0800c01150310b03801002050401d040a46c00c00140e03a008074800e90010301d0400001c2e038250280c50440c1603100c00080c0151503400104050700c80582c0071035000752140008600d07902500e111500b41c0f10401c0303c518180ea218550343c01d2403005040d1000240e03014161a80000345010600c070317403041024103080e6280d00c5860200e40341140c002da41e0300c423b4020040e5540c450400f48a0314a10a01c460a4505070f00c0c0780c000301078154a114040980060740004100510b500d0388030885a081f140150025618411420700030700800f204071584d031141500c400d54068540c46802039507111000d2a031206048032080e0710840082d800000c030030707490658013840040d20010922095004101c4440b01c1586d440814440a04045000c9614014000048180000700b54440c0c10745040480 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 89709596 1250 89708346 89708393
    0x503090a0e370501260c010804110109091b0e030318010c0507031e1a010b04090b04090203030d020703170c0304080705010b130b0102010e12070b04080d091a060904 72
    0x201ea0207941c0045880040c02c0841d03c1c1000000036410301e040021a01030300740880f08040c42c20103411391035110444560b64900041d07030240400c003c075a401c83c41c0220500141400824503030348145c2c600c00c0e2105034441207500c207041c0c80e40540954000d0f800e0303615070f58220003030351502d95245007006402c41000240c90400c081c2080c0401080030810807031010f150400b1f10001960908092041c8608a80030704484410300008522040c8038246c40242c165100510041c1c281814004e443c4001d1522908095002d612201600090b0300e003071008002c20710788501c1c0923075240181d00300607240904400301040d1a071912810007540203400002d89410550214800e40d413650b41e410400c0c054440e03502e009502c4000b00014080c4e08001d41d1040c0b600c200c003030b00248600149024503d0700c548585844580500b020000440095020400aa803113485041401d0424680240050032504c0160084031804071741c841d1418201111008181e108600b2101c0b942c0c1c13858543e90b1b098203900c0142007a004d405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 89710846 1250 89709596 89709661
    0xa0f0306020a0c0f0606180903090902210108060604050105121506040b03010e0f0706020705010206130512030f060301110721091d15040509120f040506070503090a0e 73
    0x240f00c1c0580810041c3c00003032604446900d804c1000081c019441390040052088402c400c4c0d00207a805000c0c034280d059100d50050604d803940c0d038006907104880c2e00301ca07000956101c141c40c0c41c0105565010303040384001000d0914160b001d1200700c0e001a044148682c1c0ca020000e0399005000400c14010003da004411440d01c580011501508e1030b4503a40364154200407a08100c104000780d11008801c6820840e60034a6aa8100341d0301d91490b40145130041e000f450000c0c086094605200080320310840031107c80b20b050200500a94005403192440381d035810701401920300d03007405814000880032014a26020700c030703610154141c2d19914500286503040c600e46213254051980c841c01004510310b01803036210790300302400000d4012600d02c02002403411901d003044c1451f20400c0c0c4100801d4005011070755042c41460090340001b0045070f07415800700004143c640301c9802a00300b4900c640011611810f2101c100440d01488d50840032122400b5010481201c000d6080c48085580d181c01c10300042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 89712096 1250 89710846 89710867
    0xf0d090809040f05040201120b010e0114041703030727030b0415060602010902040f09030905120309030703030c03030b030604030915020307121e140f09190605090f0a0f030602 77
    0x3801642400355100d0700d40f40c038116102e9415000148100c3c806d9070707805070628102c83c103003044812074181203001840e58038941c072455000d0b09a18039445401c004590606075500c41d014080b003910032443c21141c202105020380c49400c2441001d0104000500d015803100a0b40c030369590604600c00a000910888080790500400d0340b00041560480441401000e03107918001e4085c02440d0320480c000da191129070746030707442e01e40704103c06030f40d06680d0a40000d10302010403840040400602e40d9a000800000e04160340030071a10009510a4680b48504062420003804441c090300b29140603420580402c400030f2341c841c40210954040b00e010300444200c400b8124554018a031005010000e4481c0c18404c050b00441c2e12003202c1142802d11010a107083c0c5d00b124010000d1480c8007034414103104041d201c81030480902918135001d80300071307078005080f45042c03034112240d808000030a0000600008900746240200700c00701040d00e0548089151044c40c00300e0302020312002d000142e005c500d04014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 89713346 1250 89712096 89712113
    0x30a0b0306010b03180a1a0c13180f0209091b040803040e1f03050604030c020f0303070c060207050d021c020d0219091a1c051e01050105040f020f0d09 66
    0x15101500711070390796031038803075420b1a83e000f5a80120ba81000840780028600c0016180e090554011350b2039541d00c6080030300340290100503014028141c1d007400594a25030010903640300070407230b5640c80600744040c01c941c4022a100115145200c0e40100301c1d210040d03c071111216045205070100c81c02d070400d0044906294040d98005076000e01002034000303042d40d00311820078007814984540c03d0311049a000403000000844c40010825080700d000280407a01070111201151700240c2070a040082100001e0300716400800304689282380040180724590b4108201c02c0a00001c1c0c0740d1000300034140d00040c0310548150302664070380381606200421501c40940d0081103942c082e00f100000020048402e000e05224041c001080c3e250018a041706650301c07443c03920b01c0b80080c141d2540900c0f4484103c1c0c081000d0042038400c1d2052000c01420100e95505181d90324001c0400020b00e03504081c20001559141408500d10600510185131490680400c45000070300881c800658000039217080c03d107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 89714596 1250 89713346 89713361
    0x10e03070f0605071101020d0c0b091c170108010506010c06050a06050312070611030f040f0c030b09072c1f050303191b050712020f03060a0e1005010b0d02030a 70
    0xa1059062000240c643d40140180200314416004036080324120341c01269181c0c00c00c2d00c00b00015020201d00380c0417034802c020b141d81205d00c200c00e584008140e942c017031030440c0504603d280010900249038006021401d1040e0142003124000e200d682000c00c0001c2c0350500c00680070f0005543c1c3d80c0441c070400d18a43c45000284400b0381035442e010010b02c0d40c1c031510b421180041d20601e0401146002801c04013003164450000702200ca40c0e1511580c558540e11020b1000498200016400100208007a004440d10811444008007115424411000305901c2c2030004036440750a0102d01d040d0398240c9140003984540300d0311342c03444011600c50050004080301c0c1c0c007180c1c15003c00a0031a42c03c0000d510442d011040d55212521514030100034588450400b00c0c015180b80c101e04424404221814a0040343c18001020350317411610000001c0e0403c40180e92041c400d1340d40c0c0c1009008103500740410080034801003410020713507241408000c098400c0c1404c4103281030323001001820400d4680d00020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 89715846 1250 89714596 89714609
    0xf0105130e0304050901080f100203070233010b0415020703050309060915040303030525021b060d0e010f0608031201030f02120a242003061212030403030c05030f06010e0307 76
    0x13440d503507c884c0c054503100e41d040c000c0014014100d4044504e045030007102c0c00351085030700400501003013070010060322800e2801d030b0445407019a4024040c0310301281d4103010f0414201e41030f40d82c0346002110095504607103c07581c00e54124107400c1001c00c20200039288142d006803101542e548076034001900e100d400440007800464045800b0041c16455400288103114190403a0061010340240110f0349039030802d01030045e40502c880210000c0d0800506035081d8002d0441d13401c00040c0c58601c010750f0003d1050031010381d0b542260445410f0140520801400d080c005540b50003c20401004030140500000e801e10040700603030811512603213003c540711003691060300c02e54240ea1602d45030a080700d62525440102d100200d41c0101064800d00225081c1d1003600b42d112201e1401c030310807079040240020351201c1d145003110810002840000c510010344122a81e51f86400c1c5000342c12a000325495108004060040003c4610600205900082c09091241c820b9150a0001c6c0c07820b24140c0044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 89717096 1250 89715846 89715859
    0x1080a150e160e0d12121d25030206070605060a030b090109060507020303060a03060b130c0c0309091406010309051c0f0210050405030307050c0304050301020f040303080f0105130e030405 82
    0x100b0a44080d4060b8010b06031a950358201521902c0d0400ca04646502c030058100348404e020440303404d010740034030701000ca100c0c00f001c103020f0032060180da051451480c0ca91003541041c64503000d8940201855131803010302c83e80d404012410340d00030601c6030041c0e0100074507541d510300210701240c2e01d040500e002181d0107540c0b0003440c075001e1102c6029009441c8121111030a04002ca8031035400802501d2040801a042c84003541c9941c44030005040c1001850750007601d151421f0072081142e009142e03a900c86a20f811400915070318000f41091815401610130034500801c2500c1240c1c0c0402558000b0340920300894a0421418640c0c00c00101d6800d000303581410684880c4030301d2f0002040d903031101403a000d4802446003400950141d81084400074103a800400000e280507010340050160b25010034116806c2a449001081c2240e0120450012407000800e08004040e0b00c082035070350194503a00c6954055141402280030210320b1402011413548400440512040c00c1044e50000c00005005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 89718346 1250 89717096 89717101
    0x18060801020c1e16031406090c1302130b03041b060c080706050603100501150e04110306100207080105010305160b120403050322120807020604031704060608011a04061401080a150e 79
    0x440041c0c1150408440d0324043d000000f08d54100200c1c5200f83ca00e00500240b0f50041e0902c0f60030025402414800060900d142d40401d814180801840c07113903201d141d40b002d90500c03040c1c0d104d000e50709503406502040054036010000602d40400e8900069200802094540700c0701d0004e420300115260780c80406181400000718080f0944140c5010703504e81d04d52988502600003030000b610401003420032040c1007040800d9480c140085407590f000941c0c81505d0741640c50701310942c2500c5080e4000d480700e500481c03241d00c07811005080703a4010700283c10142d01c1e1070f17a880ca01056501e00100081e041c0100803001600604c400d079840602000d1000c184201008030f40303888201c1c100031264200c0050310338800240e0541c00010704601a54041c2c9500c03e4284a0079011480e004000340101c2d141500c40a0015802109024000c1440050341c80c00c0c01c003155400a002c1207071a40d90014046040da201219201e036004800320350804803040c0041528903c020030105503400c1d0782d1158050300001c404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 89719596 1250 89718346 89718353
    0xa030b0915040c0302040b0711030307050d030603060c05030603060f0604061503050108010501050a0315020306011202040e09151501030e0a05061f05090c03010b031305010618060801020c1e1603 85
    0x400c0220040d0840d0104540100403100b10101d00a40c001c1d50748201d0708011150100c0c000552710910540e00808036441c2400c0c55642904188804c0c4044001c203490701d600780b08100450241840d070100500d0424254074013a00065659080580400d500040c101c1c0070403141e444075009540079003a181d03d10100c0e55140300c00180205000d01c0380d00069403130070001050600e0540b00300c01c11240c21415a0f611354141d480307c45d00039800500014140144440120307401480340c00030f00010300c40840001040d00c0c1584205090901c0e801c10003000424060421659181400242e40d031f42000f0f20740082d981100c82d500502e40182c0f01005045481160100103018450340d00c0c140341c10347c60b1969000d1980c0e4a1040c03002c2440203884e081142072081c0018007800c035a45001c1c69000d0000714090085103000c2c0c0380d00f400c6030360f07075040100e44041d110062007003c00103001e920000c21160000310b00e041d01a05290342c44a0420b1184e01ca00000d00082d101219010410b00c98002601c4d900050365035030707034507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 89720846 1250 89719596 89719621
    0x2090115200a0b0a0b0d080405040b040e030301210615050a06020106080a031b0209090d112a010512070306030c0501081e0a0f0f020a03060509010305120a030b09 71
    0x518400050121a0034580e114808070046140030020000707041000c02651111a020402401d12400301c0e5113998030107055641c40080c11070306000e0105d10340d07964104002d12043d508108401805075051400d0100260070020840e41119a030403407040140311030305070500e8100b050320409042a4101548403000601c00c94000e01181e008481000d001c903503507117059099810521807100c03076410540c03140010a002e1680301c03044040d6006182c01d5208d981d80081c22101007600d080e45260f03c40e11000b044640c00015071442684144010300700c3d01c0540030541703140d0b052860854004d54124a580305039034045c2041d5581c005e105044882c1307501c1c21020090040c01c4920090302c03040d00755040014103500507003a041c01340e845800c00d160510138669003400000809003c0d100a165161080e6018881501c55880456503500000d0796071031500304000d040d10240d8003c90300c24500040100700055001401e05000b9808543c015100d191715902900104103036400c5da031300000c0c6541001403054098 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 89722096 1250 89720846 89720879
    0xd050105010801050901150302090d05010c0c0b0a02040509010b070812090f2b180b12010e180307030c060f06030b0907140616050309210607050307050702010c050703020901 76
    0xaa849542e9030b030362a010400305100a200d10361146801303145450346a1302c00d4004200c5010090110050145aaa1440e08440d01040b00c5000111114502c0080002d4100b50940111040900350f013002e0904000440840b010301c50781d5801c03040060314074204012802503941c90064110705820615101100c242c4407200301342103042e0342c091140103d18015031124000d240401c0c0007201c1d0b000a403083d600303a41d0054500344100d02c07404c48031000204201044028032682c0004004040e0039450301c41d104c1082c280241a5003028080441802100c6800000361000349815140a846000c09818410300030500c0c40910032800341000c2c07011080c0b0408000c00c034000c03560b04d4201d500d4259121b280c022102840900300741c0c006000c000388804010001d005140d028090026686006050000100d07060038810518844000b48166440244018000340e0342c0b103121420701c0e03440d5151240c4020102d200340d500003030601c07500d080200c06001003001620b02450b4007402d442d1655071203013010440e0b1341c0e02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 89723346 1250 89722096 89722099
    0x609050f0106171312020708010e01020406230a080403110601090b010e040b01020d050c0f0d0c0c06050c120d020d050c0904061403150405100609020a030b060307080103080d020f0d050105 82
    0x1455108541c5400c0f9240b41031003000000c101d840d89041a41d5501101441e280724201103202e0400c0218203003200b88220480741d141b401c00184c1d240d2820201411085c1004101c28005001c04260300400d074a0000f25042d401075841c0c00020780d9210714065070b030501c090303280e00c5a62182c0e00011400c5a826232028041c60f000341c0383d100441a000c070401040e18803100015005070881070100340d0307a900500143c1001c003c0013094601140c29401c0d80341c41e000b28a04494001040a920b00052003842ca0158000d810030789007040c60049032164080e376820194004407041c1030002240240010554191519103078104414841c50504649a0f030194100c40816803040d0703e030040006515400b14002c9450b45409806084602c055607804440613100400c282c4982c01a80711440c01c669840c4100d8025207a03123840180c403102240c20090031500301e1b01d5180d000c0c040400500032407640000303e0504403035101c45026641c10ba03808405010340140035485041c8240451448605849900124107981c070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 89724596 1250 89723346 89723357
    0x140c0d09180b030a120e0d0605070806060c190f05100519020903060f18070b070501150b030613020d06030602031b0301031e030903080d090501050108010e0709050a0609050f0106 78
    0x1616400402212040d034007040e41540132031490780028089007a2501c608403d0305256461134882c8020550910580d08100c0c0c51580e0b810420a282d50031050721a0486400d44c1d030582005200c80c1d209a58214000c1070101c2e440322000c1d417008020070064070800d91603108080d1101c0d0500288860047d200c241d0b1000c0c02d0307180703070081450160703064420307103080c8200140140010345032500d14100c0c504020300302d1842c0a10703045c030158034040200010320080989411b110703520b01290416500b124828500780301005401c001c1005000840e001b666000b034422650700c1400241c080f0207000901c25611000c103620b0800d40300105000155024500c00c00c1c0c03507441c410f00184191044a59480700b400000e241c5203c44000081e800050210081014840c0c10080045070700c03900d038800140c001d011403c403110388910b1004104039003030141038010803045000340500b142c8040810f444000d18018842030b650f4600c0010070010042e081034008000c400001c004908159001c2c0107441000d025001c049607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 89725846 1250 89724596 89724629
    0xe07090902090609010311190f0f0201050f070503061306170111070503120a0b060403140f0106050a09020c030d0509010b0a0e010302060405041112150319050607140c0d09 75
    0x604900880382c00300c1c002032031540b0302030112005500520b8400c60385106000d090100c442c4505103041090a9448a5100c0300c0390b4008403036004211100c000f4070311003164101418003200420b01d00c0e09a1b003104441c00d0441e2265554000b00344003a02c08541030b4451b500705030b40083c4502240e8042158502540000d0041c80d0940d14402c02070b11800c00c008280c3e50080141619881c175400c041c54015119080c045103114581e00052104d401c00e400c180d03000a558540700e0041c140420a103080074520b88002d011a900c2d250001700f4510151042c3c47c0310340e4002840c444211424003c40c1d54005200c1000c02042c01c0480d0822b000382030880343c071401070802d048042210340401a050707040f6035000301414606070501043c00f01400300540e00000e50002404452007814015000754440e0300303425a00e011905420081500d0910f004c0c1c0e50178032074901001144049140824144d40c800d81c2c40c100040b10408004411015124900c0100707128055140584107203070344003020001302c80128440d20243c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 89727096 1250 89725846 89725859
    0x307170d0c0b070f02030d021218011406040b0f0904050d03050c0c0601090c09121b05040b060d051803040b03010e0709050d0201030f0f060b0309070806040f140a020a0e0709 76
    0x50160001415982c2c00400181109204207180900c010003441aa8103000001044c54140d801441401c0c5001b01c40f202005441d9003824031413803a04134080c0007404201408246a10150300241c00c141c021911401c0d000c2d0b0039150740b0254904910080e05690792483c00f41040c9890300102c0240740c00103070601c00404c048114281c143d400091384007014101c96443c10b034811005001454503041881980080020041112500d007000c0600510381e020b9518070404050240d10540c1c2c004074800c61074400800030544070102914030001034140001002d89a5440d258104101400300007068800040c000c0792a114000146040300d4140910382440c0d210100150340d406801d0050a801940641851001d98071070b4000e450001c2c0b410344001829140b203096a4161a1590824000080c000061010f550003c019a1008001003006040903003020b42d2040429201024081d06052000303181c80070a0105210800701e643d4020032510409940c0c90001c5000941100c15002150f09843c0000341e2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 89728346 1250 89727096 89727107
    0xa0b01050f04020307140705070b0d0c11030412080702130501080a03090f120609061b0201090c0b040e0612010204150804110d080d0f020c073c17010207020307170d 72
    0x4845c140c840b11203014451940035500c0d0400b090540d054410704000103041070200c4003e020214420801213110410500e014009043c400201e0206600401081045040c00c080d010303220341c0d103d141507650350054000038450032160702c041400759260100015001c00d00048440b2900e12907110032240780e40d2a80250686c003c1c1e84680b01808200607440000155103501181009108010010b11100c10b14100005110700352904000b5079929180d10090049211070700d4010318408000d00e16180c2412030500c0c3c2c019000e4806e900548001c065003107142402e4040d20301500c000030000d02e480404443c0100714003c03d49098030001c6170b03c14245004e00b408007500c04074641141e1000d1401d142054450020541c3e15565412250b091107072514420307007846000001c2510a404500c94282001e40d07400f101030f4440c84e6600b10a81407654800c08115981410031191707500c150402103007102d0042406441a648001c0d858044c3c040042061781200e155042840d94003011a560054000800e842c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 89729596 1250 89728346 89728351
    0x402090f0402090a0b060c06010b030601121a01030c111207022d0603100305100c0f180308130308031f050d0803010e101802040e07030605010e0409060e0a0b01050f040203 75
    0x410884000005202d510250800000170fa40a003045151101141131103040450a80005100036030000510031a50fa01490003c1900c4441e1000c00c0018880101c001e80300b400c41411a040c99280d29a03c2c10f618014214540e43d0b03801c00e01a10000c1b490b210b9224034039130052004a1040c484c0c904a0f2400300100180c0307070146a03404010841c3c800c413420030040c56400c001d061000f010f20108000c00015018444000010414800803c54402c02400604010756644001080055580088440c0070300f52003020201e03900544081e949010100d21800d8010203078101820b251400414042404041104441c003a8284044110620f45810401c1007200c1c45500c0034001e03500a0005004282d0508000c642226155a507070f40c1c07043e43c1c0c500e44800c4a0030005003044080d4041001c010201001807040e6100c40d07285000c200c0a4203100c0013812907111601d100c2e000350341d00c0342a84200189a8013894900b0380410491b60030603800d2502c0300c8410000d004980c0209241003110005050038001e070b90 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 89730846 1250 89729596 89729599
    0xf06020d031a04020a0804051015030f05030f0313020f01050414041e09200604060c030f1130090d030503130209070c02011701031709031c05030402090f0402 69
    0x14140280300401c070060040603515482c2c2000c2402e06031640d940d10710003440486510b48401000703103403900302142070202600c0300042c0301d420301e80340b001011350441e81c04066990040c800381c1c101110307080982c918014020112144c282c00010f2100446502c0d85c0c0d05111407017210a14000e084a100445032030255105401610442128184440c609500981c0360300c2941c5046203084145000e58030241c5000000a56000c3c00c8404a4240c03030003081303c41801e00205560080c17826280c508010700c48a034480c0090b0801600a0001e07030b1039440384c04030806c0d0340d000000b203030b58107201180c441095144000d02116010140d03190401c60342c600c0d00940d105504000c0040314030301ca99441c00d41c0c0d00d078401000801015820700340900180e59040c4102d001b511141e44820000402d4070003d0328040c0c02030f82010810403400e00410016161000d181d04084102d2030280d02d6450b0700300401d00c0e00380d44020b0504a02501d480c0c006c003ca502030041c600c590b008607606081c544070070344020f0042c442650040e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 89732096 1250 89730846 89730853
    0x50d1403060f03010902031905060a140601111501060504060201141e10170105100806060f1c02030a06050a1d060a020f071b14010504080c090402030a080d090c0f0602 73
    0x10304180b4065080d80015032014002182c0090580e00080c241100740d030750071417613204101d8407100303004040080325070000303070100308019180d0322841604044000520090402c50b44140e0640180d10078070403004081480800030110303503140d5078003900a80140c02008019807034908428510801160303024040c0c3d040440c003280b0b07000081006129042c004041f205514444100050152059950704010103880f000001c0c0c44c0c28040c614100d007030200d40c058400f645c855018000c1640d6020314a41fa060401c803902402104030b44494442d6920b00b1074040c2d07240c085c1c05405c85c2441110b40003039200b440444006c216a042204101040a0100354038080c154840e03800521500065401050000b203000d510a042c10019a40c00e40d5001801c907600864510400301084a080703402c2c02e26501d2542401e00c0c604140c18028160b640f40701d8050154404c013004000701d41991004e101c2d1002094000345481e0b41d5041222007207024100c0c0302000c465442c440c2c0000204442c0082e450000e84140d80d002c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 89733346 1250 89732096 89732101
    0xe01090804090504030302040834030b06090a0e01091b1e03030807021603080915032406130f0e070201020703050d0506030c04050108010b09010b09010203090105160b01060c050d1403 80
    0x44000800f0000e004900f0301d42d08000c04912041c0030012000020085d040009070341a0404803030219803070814002900040001060000440385a401644072800362501003803503842c1c5503584003416280d4850f20350342d443c0150990600000e80030140031242c40030429041c130f90781c0f00b0ba0f4040c1c880e458030710002c00030042d800c140700080c880c3c40b0b03203500446a4030441d40348203a140303000311046045502c01c460301c0c0000519450241028892420480c00114100382189094020710506201c02c0c4c0502d00142d20b604a0f0003400e54802041e110f41c00d079818052510740c2e40300c5190384440310070307801103d0b031040070074002459813031050003143c0c1e40a9242e03488074204543c094164014020291050398140128000860035440703c0c4a021f000304032031400858a034025174103001c46010182c00c000d46280d070404c0003c450b641c000013180e04a200c20b02e00540d03110a280f00109145081c40d00c02072000002c6000000c1441c1e2160703048152600980943e09105a2003c05842094144450b00c9540d0020f000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 89734596 1250 89733346 89733359
    0x71713020919060f0f0e090a080d021c150e0c0a0f080c0c010c050307030c0504080d080711030c100b0906030a17041d0907060f1b0606090c0804060e01090804 69
    0x20807100c01c40b214400442c4064a8610b00c0c03440d58807036041030710140c240348820440e100d00810026048694000034042035207d6445c6d110340ca2150304c8801c003080f900080c0c0d644a2880d100071040708030f14800005c20042d61002040c0f185008144207041307184043c0c50200e00305100a0040f586002c1e4183c65240c1d0218011400f5603a0010081c282d544030301060096030b10108080c040c0c00025402540c5070380e924944000041c040300d5100c88400c04201043c0014001c212001451211a01081c209110319a5030000200d4008801005001080c00702040c4581e070074000243d54072002c0e249000038490344034a40140300041030222007a5a16a11071041e000c0810469891020108118250b09251544807031050385032500303c40420f00214142c0c010043e0304442070011002804482c074014007200748840e402005540c4d10f1080e2203085a40c81c450104204403640408010044400c0170b1010080009000d0210b00045409031000380c105007400d00c1d640410b1083e000d04551041070a07043c10b04002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 89735846 1250 89734596 89734621
    0xf0b030a05130f0609020120120309070b0a120b01143403080613020c030f130f030f0c08070f09020304020d0b010305070f0605090901050105070510050717130209 71
    0x2d2403000e81c06664482c08002ca1015403408103c03d006000c08250b40d011440010541c0f4030706415410030b10900d1985a184200102d034003c600e14414200d55100e0303c9000c24907040a41c02d6000c0406c00e4400107150f040d480c0c010044007028007024104210401b014001500e40c840c00070b00b1203854240402c40410940440066a6100107069070f030200c03012404042416140f0392184290041142c40b0304101c01d510b00714008070840c0160f00803c0d405c0200400c03c940d50f80c003548040e4400501d0200e4400c101001c1042640d0040070098050078519540b4282265800458001901d8101210f0300118400030000388540850b03041800310f802d6140340103000c80080d00003400032a071007000461020085101c41c82294044c5025101510440f4502003c0c03013514031703003540000700348441807141d0b1809560702200070741115020f00380b495545c0c1041c0742c042e0820f03010480f000851403400041c001420361285004880b55504080010981c9461407142403001807640029440300303561000458030001071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 89737096 1250 89735846 89735851
    0x110402030405100f090c1a1603020c09010609050f0f0915040b0d030e180f0106080703090c0b030a0c020106031e05030c1911041407031e05090a0302070f0b030a05 71
    0x10b00558504800d910410419107029a04001070139440d01441c030140080d601400700244900c58065502626039009484039024007214183c2042d9401220b07001c0c98000e2094141c900d1000b49154515030f16010701802001241c050b95000f03904002d041080b03402c02062a051f182c4004118103560344d5402454910885c0400381540c204c3c0d251500718131300b9290806504c008521a407120400000e880060003140d10480720500210031608050100c0b000f260602c0340d0644480d0b25004800e87c1c1e650b0000e84c050080e03034800900d0104a00b800080c0f144140d409540581c4412000707100f076510410089013654118003000c0e2030381c1228100940c5100340b00b0006d0451511500c2600c1c00d1049100a1604005060400d840d0001d81c50400104201203c200030462540484040190304007904000400c05001042c00003456aaa50301d4424a820240851501c0d44990000d00c031518109041e5070311580c204000b10054891600007285003074020f118041501c0a500041c0e055540d003206480242001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 89738346 1250 89737096 89737103
    0x1080f09070503030403050705090601080f0705030a140f0105011b0c1401140c010f0501090c1b081b150106050903030a050d060b0318070806010803181c0c080105010803071104020304 80
    0x41403030000740b80d102031002e08001c5005a01030541c231403078002800320310600102007504011884040200080c400000d1035000f500500d01552039643e40000320307004050b51058000c00c00311107000c00811005040c1c242c1e058031000c2c1c2c1e038030b207059101140b261200c0c000802c3c010700324003240405124002c00c1644400007400149403a03080801000d00c910840c0e40070f400b092109944032108201d510b081c40c0141c50040803100d03010081c80400d010018404c0c0e24198500070800c24160748001030040c40d00540c0d0403c01d4441111074061000846242d03180b040252141700c00d9410b0000185080c01202075450b0124090059850032106901c100c40c144d002d0501258440c0d507420300824074006000c080c52281340002c03101c00f440d05481d41c1a924140c0c160344044840e40c02503005028601022050b1244d00862103036a011110a0380b000407119450f00006400d04503e403a035000510540719809001c070350380c11008000e41c0c1d0701e0b5180c01d03840344107040000d03105683d000d0781c162945c20b045e030055620a01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 89739596 1250 89738346 89738353
    0x30b0108091905160f0e061e091306020a0306082b051605030d020c1b01020709020702030111180109090e0604020d030e0d20010804021e0d0f0305030a0b01020c01080f09 74
    0x10340c4504c0302c511072150700540c4113081105014032420b852003040a0308280e00300c8070a0b00094000004d00341181c03c01580e1406982340708040354400b0130010180181c0c030f9202170159103d54490310000c00610082c400c0ca0418460a1998800c0c050b10080c525a194196008a0300c100842e40040d07403141e0016445d007140511840c15a00400c205101401c143c003002d000141c1c4d551003103904280340100b10220300e011144420003102450780c0000e0401d00702c03100c404026894441c20b00000740100401d903045c0c0301c0d00d00b00088504600c140000c456804110981302c1d00d406580f110440d00403240c006030340c01140c3e4081004107002d0f24000824160451013458664000350f8500c1c00f0074030460f00c80b8030803a207a80b94000490108031049040c0d003070380d090a29000016241070340004080314140e500c4ca5030544d50b8070503042c0050b1110b000e1015041c1c0c0010100304c1001191500610550045442e0b4030343c14500400b55070250701c0402c00c0158001305944420003600c4141e100c0d41c659001400c0001c4511 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 89740846 1250 89739596 89739613
    0xa2102180f0f010915060e040f020d090606150905010e130e0a03030c050903100c02010b15041d0c030f100f0e0f060901060c12050d05040f03030b0108091905 69
    0xc032002106031142a801c001070205041030000c1101801040c1c1003105054144084840c2e81d00c1c2081042d81140d1043c90086001061200482c00400c00556104616400007400884407002030308118a8180710356810001d00745e4620040098440310346044001484400c401c00c010b61080021840c204c20041805400a00e0084002e08440301da1602d460150000303e4480c00340b640600c1000c030301a41d01d0500e541350824400010b07446240003401903e405541303003035103100e4074801d621841d00050301419040b000d0144204d8002140c01c984151030020070120f0b0ba2085420040c00106c0c010a000403d40f81580ca034880a007192074401030640e42d01c1c0c42591000215205200e4181c401000c038103003102c03450304220f8001d00d21030100810a9000320b003244010072100340d100e45107440640d040044244514108401100e0520800c89081d0969081c80180304c24000b03128001a02e281c80794908010b1a9100b8006482081086510104036080464020500d460388415a0111886072042d00c0003107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 89742096 1250 89740846 89740879
    0x60a05040218030d02160b0f120c03040606050406030201050d0f15090218040b0303190e06030703020a080a090804090e03040306020c0a0209090a0203100e010e0a03020c010306050a2102 81
    0x30307004800307200d02e106510485a00075060030320012601c1100f600c0500500841035141681c0c2d04424801d1401c2440b0016900c0d0b441a0072106481c040700c2080320f62502c80c10100301020840d041510182d42d018a00325001540b4070307241c07107400308032903040c1c6826081c0003256007024010015910005501c1d03460303e40c042a1001554070b0440a07020110006845840c1000c1840c0844103010201740124500384c200c0145940000a9030315000f240b001450003d002c0d90b004558440102200c1c9410000c080248001d01750940c000e030201410554800d4844d60b5400016019252f01600240078110104001d110f8811541c0043e503401e13002c40100c920342075403030380c64004903071015141c109150054960b940031454910555500704c0445001401030000d0350b000207858803407a0f00c0f00a91035a075401e000841010a40112a44050420544038411001c0c10080e40b1032070f14004250000385000c001041074649000510103482e10034080402d1481006d01000302e100701c0050680cad010304050b0458a08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 89743346 1250 89742096 89742101
    0x307020a06091701060803070b0c1204080703030c1b03030f020408060f04020a0503070b030f0a0603120809071a0906031e040503040f061d10110d020309130207021503060a0504 77
    0x401c015a184104145451111030000c00031041165013a410040b040041c5940001694002074000c4030591168491610039102c9108201e100b4905c0005482080180710200700074000e040e0080e10705200640140808640c0400040e0340a0a54845040e1000200b807084d400f02d122075801040c010320b8076450b006020701d019011101c0d0041100c544003000114149000d1008c010001070b001003d1590400c81445038a00000704984140c040c1c4d00002001c026480d0010300003980c02c0a4441d010800c0c4900c024141c2400f20745800c030b580304d00c89001405030114600b9040c0d0021611005090072140ea0800c401d07940050054444140184100b010352028410320340d008522502c000d581c2c45161030743d0300b200e90040d54440820302112031040f1200191007a0200300383e440860b180c580700105850305a40b40d50328140c085c0c800744070b03003003140030356135000802804050400c0304e24128500c0000802c4060f0302c1000b20003500032122100c0515002d16420203590001e100134070300701040d81c903080813604 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 89744596 1250 89743346 89743349
    0x6092a040f090c0207060210051b0304050105041103190f0602041e0603050601050708070f020310020d06030203010614150a030f0c051c1a011d0301020706060314030325020307020a 79
    0x4180d0080c1c0400c002c1d2151a10450003075082e10300142031802c1c034141c00a511340d80d07522030401e1065140c00000300307604104641c610000e42079074a003035100c0c2440d080c400d0082074210350803180c01a2101001049143c0064481c004d03c2d01049550030381401607582c40444c00c00008100c6410382c00780404620b01c5c2c1c1d40c150b8840082100015a152140340c10002402e46602402c018140b1900300203100c00b180c0d20008135540c81c0d4110031644640e803000d01c0802c0c5410415080d001c4400d20108540d0f0b508203054000e0740860780218028403210392213203d001003c140d0000d0166100c1c1905078042c08450910000c0d040e5204642400500c0e0340440c0b0f160810b49640380d061400084c800075803c141030800403040e05c80d412400d80100704190100060305130a03000225020305000c10603040115490800c004910701c01c202070000d5403a45114501000940b50386e000403034034000c90705100942070800106403032081d901d03640040001e040300d51216420380003505140c004c6010802044000d0b0300c07030300c82250 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 89745846 1250 89744596 89744609
    0x501030503031e010e06150c0d03020c070803030c0d090c0e0403050304030908030a0c02010e0301020f1809010602030c030307030908300c1303060515030f011a060306092a04 76
    0x42c2c0d2031a014044911190404601500b21140ba200500c03111301400b030140d074801020350f9400c0ca4030242c002654014010801c90003001d104054841d4811581900540052600e0008552002e82c6482800f520b0703020803615402414424820521004915000300c071405015600e808181c548441030080102003c88003074010480010a2100b0540e110507100001c01120700a1820702e800c1044c01071006250010190411001c00c881c545a50381c203604880c40c421000d080c996480504c0c0b06216190b003880050b061040080c1000054208e0012084400ca140c0c11405545180c0d500c1c10160020314400303100f90341240342403103441e400d00721403106203100c602c514000e0030305481c0c139512401700c030700c0001d0000d00f0701102800560500f02c41e00c480042583e52001c004101a0354092404208450580d18a035040c80380c1400300600c0328041d40130803081c1c21031f41c100b581c01200180c1070142c244402e40c3d40c40d40040c500f1000600d0034200b01c0030101c014460401002c42c1d0505444039070340d180c1151b000310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 89747096 1250 89745846 89745853
    0x2010b240d06080d02061005010809210d0905010e0c03060601080a090f06020c030d0b011407030e04020c0d0c0b010906030c050f0f0613050a0512070513060801111c0630050105010305 80
    0x3000d40d01c07c03c1254801000b0920f0407226034034206804c1a181c1040004542c903a880341902c0015151042081d69140c010f43c200400c1400b40a0620a000c0c000c50f00b0348542a0140c60b96070045800c0205445124840684401c141c544441c43d0050050a54401c10340d1104054850100000c40c180010284444148020f41d11500d0b4407a04008554146000c0da060101903503c1a2007882c1107000e841c071458050030f0001021407040c0100c1c0180c850f9038070100c414022441411101c0b50061b0781c1070410350041c540d035901681c84800f50380031910075000180c100354202008015900e4180030896449101425402000d0750400202e0440d4100480e040021314000106102c0e038100900300b43e0040000315618034413900031810146e00c03149280129030242071803800001040c1100d070030a03401440084020130001d040c01401c1070303440e04041c088040e6040450300308103114185005100a071103c0303148100c0c030b01180320340c0b003072420b224a8190078102c00c00e0b20341c41c00490001e1058900035405100038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 89748202 1106 89747096 89747101
    0xf0a1401030c18080102120106030b0a030803042a061b020603060f010504030807110901061d01120b09010308030a0e0a050d12020705011b02010b240d06080d0206 71
    0x5050110f600c1400014102205500400040c5080c1c150041241d0702c902e000c6060340c0d2020103c03544100d40d082c0034404600140300840d00280300750181152103152100080065920160481c520303107818070200b0000d6001200060a10001c2461403a0140c065000a0342400040d060a01441c0314000219699000d441100c0142d600090b0a07a00d460062401c09401c01c20a007515014100f11000004c65500440c102025010703808030005000d240e0310011a0311021113900c00d0601030711546d0408058844420540c080c2d07000d80201941c1f8900b2040d0401601c1510140e10710640c01003561402080e8003051441521080e49800d070114800030a03d1006806440c0c005081b07540f03052614401000103035003000c1c0000c1241c000703010001114007000006200420031000b0742c58002000d902010401c0b0050003e8400c0500018241d0b4903500d15500d40b544c6218460b0142c0d01c407409 = true := by decide +kernel

theorem cover : BRFrame.Cov 89568346 89748202 := by
  have h0 := BRFrame.cov_init 89568346
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89568346 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 89568346 ≤ n) (h2 : n < 89748202) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
