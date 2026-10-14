-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1087
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:10:56.741154+00:00
-- url     : https://prove2.me/submissions/7a481a74-574a-4acf-99a3-7b2691531b19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 195323741 ≤ n < 195503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 195324991 1250 195323741 195323753
    0xb01020705014d03070c090f140703020a12020c0601120503040305070e0403030e01060503060a0b1c0f030f0206040213020f0c10020406020d0509060405041107060c090e070512180a0203070909 84
    0x120100a4030019405c0c03035210b480c0c0e10b15541d06842401913660303403981c0304403800303141e0f4200e0010203aa000302600301e85000c0001030082e500840184001840000c180a940d207014801d80f00348050000007451660f003841149504d21078041d0041d1840e02c410300000001420401c8288081c0c000da0003804407908151402405072a900004821180d040c41d9007030145482c0016a075502104004020031651011804a428030603e280340308031060072110000244039415000e4103905210ba602c4a61001e411030007261a40c1c2d068400030341c05112200d05017458095500078068605010046a14220f0709640306132402000b000c941e50a10780100f020401e40b601800034003601f600c94140246440256000148203104d5030103802d02c0350395103c00031052031207140c0507a0440b590200003040003d210560152004070181b04041144401e1300018058510031004c0d1909881c0f01621400542c03120f1140d010041100c0e14800524800c4180c0d05000d41c0e01041113000910400000285010701c500307241d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 195326241 1250 195324991 195325127
    0x60609050a080303090c040b0a0306050411011b0506040602031009050f010e0c040506031b0c0304030305090306150f0d0212120c070902030606070f020a03080705010b0a090b0102070501 81
    0x15510f42050003000744006002c50341000500781100c001031010001c40000e28400321076040601124640010042040214008030203411400d80701e941d4482c81d4615102c8080700180b1008000d45c00801c0420005406c6030082c5410100844548040580303d0002d0812200c049442c0303c006200785004010079604400d0f646e8100811480913450641818007040d164800600030301c00c20403804040b00c2103522604240c030b03110100c50081da99100c0d642d0030b00404582042072510b02c42d000d0180494080d9030410910615680007a0080003441c810404001100a14101c142d802040000001d031010b503042c0040b45a0015a440c205c0e11076140410407850140c141d00082c1a00c1e01c100148190341d560b01e425114290743c003e8145c031a51040380301168115200303a20052211700045000c0c400c00ca0190802e80c5826015140400c000c2d075500703000b8043da03007000070003805138015650078402540710b806103141d100c000480c401d601d4480703810361408050070705107584c480100035400c40c04243c0e074a0001e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 195327491 1250 195326241 195326249
    0xc080f070f060510140105370e01030606080f04050106030c080f0c040903140c07090f0b040b0d03140a0509030f06180f10020903010e01110a0e0604030f03050a0210060609050a 77
    0xd4506000d045c4802c03900088000407059040c060007085001000501480c21002202c107a0010751491b44017801c079640c240b80000c1d408002c02e0b81c40c41803164551080c030913142111503980e00c1a00c01d031200180143c5142c0701074015103903075486403000302c045288403200c98000d0030343c0c800030704500c11200c045030b00701628009a05d01ca0303400e10311048042548500400f08404e0b06844203075480c400d20340e50a02d03014036a405114943e08100703d00340c1c5000b540c0d000320ba10756025a001c0c4510100c2c00f0400c80d400111000081c01f10301c600c1080c50703408042c40d010345040001810807620f801c03100c00c006460041c00a0307400865a200310f0400644074084061840e500c60704400501003805000c00c030a884071030305191080203d80c0030480003150b035000d420002da00110300000b086071024130303200846140e000b04d01c608003003a03c90000001d0360400804407404c0380d0f08002c0e000e8541185a4080b01c4551018025a0840c031a1480c0c1501090180c85203800419460b01c951805a1621060020240c01540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 195328741 1250 195327491 195327511
    0xd0f05090a0822080a0b0703360b190605030601151805060a02070f061b0b100b031009060509040b0a0c020f030d02040e010807050a060c080f070f0605 66
    0x52000c1160005265080d4a52100ba01601c480d001c00002410084000c06403883c9000603000280703150012801c0400385001c2d2134003402d01c2d034440c00e0a4080d20726400038100c00350354042008030016015403484d1410303c50306040c8c4010403a2615a0240c160313055071070180b140701c00c90540f042031110344580790003003d0136806131400d0340c50218400b5406080700b0070001880002000042800800385241d8040d100040c581c0c2d07102d104501000b982c602090164500c24507102201280d403a01411089485240c5032070030729012000d65a460340b2402015000c01d2440700d8500c00450b481c09800050f41c0304048989840d170080b03140010100560340c0c0e50b448a8001d1100d5000d003c042145c20030303440c2e80304031050404075403020203c0007245041d0222495180300d000c0858000300d5054241c00400484a58441d80212031741c9400b840e60301c910b03080c13180c030b6403203064058101300c0c85029494a003402405892f0803030a04070301070b130b40c81c070554031042049985044420302c420070802c0030320901e50400c3c2e140e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 195329991 1250 195328741 195328751
    0x106020c010806090414011b110c0a06080f040203190b0f09070f03020424180b2b0c0510050d0e120318030d0c0309200f0f040216060504120819020a03020706060b0d0f 73
    0x5080500042c070091302d0b07500c41035202c3b00002c4c04d64030300308814511078000c801411240003540c00c221201000c203640048900d00d1100118803510b400081d104151002d41201c0301c0e180c0d00d56400c12008219100d410300c1d44106241c2d42284414809000600604000b02c1c00340055080110200444074038010642c49000e2021545202c11481d09070b50004000030600c491742d4040b1401d1800010b10320ba400715501031413500910f80c41c540d110f40070308240c007056502880303d0710f002c0c103415803a03030745eaa03402c1c2c1f0009005000255078559900e550000507403400c001c1e28500f403110760b020825109040a0503000c251540d03103581c1000030005010001401050040c2c0c1c1d1112140b0002d9401c0030349000c014401e040d07000f8158419074855044911180520082d003080e0041032500034084d107021a41903c140000004d41000c0c0c44c0207034040e520400c41a2103100c20b00c01e4040d040380094010161a0042560030f08c04100012064801c6202074101d908616803131b000128001819a419020088000c605103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 195331241 1250 195329991 195329999
    0x1528090305061e06100c020d08190c08191b05010912030c09090203070302131403010b01021209150c010914010e030705030d02030c0f04030b0106020c010806090414011b110c0a 77
    0xd0019a0000c07001c4031110315030170306448103e40c4a5485000698030144840c1d111040007800b100600308012106440e60031085181002d4944950301c5001400304001004403043d00000409141e07000001801d0201400c1000c8221017102e03c11642e088400c1c0c0c0d5103000003c01d0110740403600b00031107000c2c03905021111041c0e0f4001c2042c4001c1c0708040d00340750040041002980a60140c07288865a54042c0520564404c090f155104a00500038000c0d460309010103403551010a14000030403403807101d07d03d1300b0208010302c560742d0708928550b4205a001c0c05440001003089c020240d01d00e0040000b10300c0182c21001841c21a2140001e800c13899004100c00f00002e4804401e0b9200e41c0074030b043c01600c0360f81d495403c0141d031007070000c2c85850100c00607010003048142e03801c0034140c401c158221007100c20781c10015600f0182c02e480d40c1d03900c0000c19000400080c8090806049043c0c00d000104511003621082d0a00320507100c3c15034003203260301300d2040002c501045405a00c59003221122001864 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 195332491 1250 195331241 195331291
    0x40807171e150a0e010e01020d050109020a080c07030207090c0e03120a09031704050a03031101060504050f24060c0718061421030f07030e04050105152809030506 71
    0x240c8141c804002e20040014003803034121362010450900407002400f25500c005070b254001d50044110540c502d28100011524400ca0f10944852041c142ca8568254959086001d0507800c40c1e00c0440c1180704001c0c000c038a1110030300540c3c400700360544507152000100702c1050304010443c0032f0300010300d609000d0741c41403a601910003011640c0081c40003503592008010304046109c0e5801c015041720300200008200341e4429503103a01105200d0003000305503255020001503031030996864680000e0f4030b002ca00841022a030f105d1800c2220565200c81b2020340b0003007006a00304d000c2c0e161254100000400402c00048054040b46040341000c0046034240200d00100019101507103002c1d0341ca04100f0440880107112600408410750308407915580c4101c1229126441464200d0024418001440c400d050a0103624183d03600100020307006607800346954110b81108100708041c240d2025a5010002d910300810103112142d6543c806042c05c1d03080072890f14002400503182601481d04049105e01c0d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 195333741 1250 195332491 195332503
    0x120516031a092d0a0c080303071206060f0302091c0c080c01110706031d010905060601120c08010b210c030603010b010c03020714011101020d0e0d090305030304020d08040807171e 78
    0x6640f001c07140d0f1040d490000a880c00031300c06001010740c0170324036012030034201c0040070318400c0c0c00716580da03400c0380036059240094428501c10342011400001d048043c0707034041d8001d04101400686400601d00c9100300420140500b40f40c19198000702c03c40a102d4404180142000305000b070824a0700c126903000070aa41707142a02c00c0d00d041542c1d600094852261a03061001c040d002e0700d00900030322030a400d090751030f40c00c103440590108203113006e03464002c6228041c1c2c0b102456070361144441c1e60b05e09425120543d0005058800700500d12810804100340c0d41c132039038020107a91424903142e14104050500f1195101d03c6241405803006150001943c009501d1081e1482c013034600e0341c0001c1010050710004028407083d03145500100700d00000610301d911902403041c0c0c40044920031a0500700c1a00d0a01c80d501001c1d006820400004000d4140b1600c1111640d1003142c1103841c0070359504e05281801d0301500b00740c891990886030490b90381001c0100f00145185038003041c484084005285030340310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 195334991 1250 195333741 195333793
    0xc2a061820030a080307050408060f042a17100506010309020a0b0702030c040c020d20031b07030f26031501030b03010902040c230a09120516031a09 65
    0x344030704200d401510140080a207480c0d2011034543c8906107401d0103000c54210b40100d009600c02d110000f09182c01d45412640140d81261010407070b5500c0098149100c0100034075041e0300302c00b1841c000384020841c1c00300042906910301a1910300554503100b410354201402c5e041c10142400303000c1015946101000307084450303079150300e03035640118800721707081840c0c0c40c40031903100c2d01d042d4041128907000301f0103c00da0344466507405580303032080d0084419441d01c8003210005910074409559030341c00f0f05000c040c0b1000c0d10421100714035540c0d56a4154404810b604031030f607005007426400c030303405010800407200c42c00315580e074218600040f25504214050719002d041646400010010341c80a62041c80f9498001d4818407426403012009810380401c242d6225000084462380b031040c2940005440e00c010440e0b03540800d00d4036020144045644540e0265454003940b0360704180c0381d0600c0385110003035101d4500c1c2034200c00404030801e00c10000510400c0980c00541c545a81c402021054100c40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 195336241 1250 195334991 195335033
    0x1082205071d010f24021f020c0c1509010309080405032407020c030d080a0e0d05032d0103020907090e010f06030f0510050603180f06060301050612030901030c2a0618 73
    0x110b00c846100700e1070258011801f0946607034110350202549031640081c0384541101088407086441c0c0c0342400300f07031510004217400d0b1030006d001400256100343c000e842c0d01c3d4003445c941c509003900c400c0040c0c01c10310592001444090215400c1107080c00b008440e0b680202076001801004031403101007602d9021503446002001403500028154141070b82c0510031854180b03048945076a141072014100ba031080c0c3c1d105c04180c0d80d010f40c00b035100c6203502e6506100d0510522105159183d5404d1144070f504c040c00300d10501c5111000400c0881c6400ca105000302081c41c92070200c24030b403200c0502140d00072030b040340007a41007100b00600000c2041d81d80c0100c69041d01c19a0b07590b81c80c2039142c1040e400031500e500141c0246640000e254000148540c0039840480c000c20498840070204070248010f03e8010982e50000d1004130030700d602aa000c910f107800d281c04c0c00d2080242000540e845801c0c084401d050107101c541c42c01e000e0010b03038841c02600e80e91850301a110b0003103d0302c640300c202c82454006a10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 195337491 1250 195336241 195336299
    0x50303160b0a0e1005060a05061e030903070206070c03030e060733090c090e01020c0706050307050d05130302011a030307080c070506030f09100204030201082205071d010f 75
    0x7550029407001c050300f10f08000f512140c1510083c10b034083c1000352074451240c0213a500101c0ca030701d8144121850b50a50300510f80d4a8400400446203507000200b25200f00d00082c0038403800f503251200100314051044418180c007605500c0c0c0a051070004075807035409668203000160004070440c00010340c15030400b640d100d10000284080e00700c841108130010549040450401c2005107216042095801101041c00b46000d8498420700306d00481d060b4411903031090004210180c0503130015a001803c0340740036445c160f505c1e5070300001e030381c000e90740344520010908151080c99420b01c900491808210383c2c200c007400418001998034080e510b00034090b85070000d070058454400b00080801801c02810380b98a03032402ca403000c1080e00c8110340d545894080d1b07622001c10140c440c800c8030242d81d4161200d180b16120031a09615100080100c820f040e0900146040404d00811240c80202810414904040c2001480c2054000181e200c0c1420480c20002880010000100d82501c40003401d04900c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 195338741 1250 195337491 195337501
    0x801091211120d0605090604020a022802100f08060306010303020601051c1403041d010f0320090a020a032a180e010f0510020d080109020c070801020d0c0306050303160b 74
    0x400c0c02100b04802c1c2100c0310006481802c2c0f115504500100d8104860f2910aa40c0d544140030a920440d80079038010f802545006070141c44600107034000c546840c86205240c505035002c14801c3c0c0481c01c0302d201140f06018009401c5034000c000c0380d84200c058000d400d0552655401035924030060041c03d2207910b101100b0400380c04443c00140006800564484030209081e00c840d460b94440c0c014807c040c0b042040c0400c0070105061214100c13110b01c0c00b80c0280c0352035600d60744240e810404848403c1d05c842189418507680e0075030b4450044400d110010390301d07426914058103c9090480c090401010030005100941c400d890034001c0103002d05000c1408904410180341401054006103900c0244400103d450420b000c1550141c581c2518040076042000c84140e90324515a05070703000240340b18006101d810200c0d0060f002c0c0380c2443d012a0085601d0303c0c1c60320300b6600320600d40f0305115560f5400200b04c45c0e243c082c800040400381c000e14039100f1403141c000d1021980c1c0c03401400c01c03055000850 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 195339991 1250 195338741 195338743
    0x30609130b06130f0504060c020c0109030804120212150a1d060c07062004080114010803091e210c0409021c2d030905150405011101090807050f070801091211 69
    0xc0c02c1340345543e0003000107140510b070510003491521007841c018410906103112030b501648034502505e400510321341c20b1602d00400780310680020a0101d0f004554922ba190005800b049141040800400705461501d89160a00c0c00c9034256100320a8821488410074100c1c00042101a000947c0e1300229503650198188040a091880d00036061070b034100110400000312500640160f8040c03138001d220810341d018003a807040c0c07020f020320580c40c0c008000e4903a075440c107080384000c0c5010810480001c6095a000204001e071044807280c4110060000a100d00c40240404040c4102c101ca0400c0040100e8000c510610410640000b5840030390b0700e030b20144840310009131b05600c5000801c007280005410782d0281d280030a103045011604220010407545046003040f0b0304c0016038802603040910700001140d000300c41c0880e02a15541e2802010003040a090040c826036005000a04084164221003031508226070311210059240a182c8000101c075000031102e019014079080d0500010301c440c1d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 195341241 1250 195339991 195340001
    0x9010504061b120f0e0d021509040f020316090e16050304060b06071101030f0b13021e0c010606021c0801050402280e01170f040b13060f02030609130b0613 68
    0x1034002200f000b9903034801648441c00418107081955144c0700001c040e01800007602001500941c0408084070300c2680c1c030324400103000c560f200100301241c0e04500816070022030b8410340e0401c0e80b4194616410741906e4000c0706070700040021040c040e40515000103409800143c0715010810040b000000c582445880c0d003217000d0309800148a9542c42e402c0f80f030309680001070b03000e150f4080b905000404107000c91380d104210081501402e07000000e08a07001400007580216050700101840c400c2c48103400040340c010300480b023100d10002404a040040c00b0340b4000e481294003540004041c654018158000aa2070444d0380640340941c40d11310b0140c08880680ea149007150191003403440c074101d01544003104c1181031100381c80b0708200da0f0b084c800c0071107a848111200d03200102004041400500200d42107688400d94031510f804c694070503901c14003950450801700c11915001710520042e4a8849106604294a010701002c140300d195640707a01048000e100354400c0040c000e0074900f00340c00da082 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 195342491 1250 195341241 195341243
    0x108060c03040302160f032f04021b060408031008030a0e040207030e13090b0c04050d021207150f08010509060f040b0402130f1a090904060e0307080307080f060609010504061b 77
    0x40b04810351103c8080c811030300c840c8016902188119001410a4102c81160308c16202013800d040c10002c0b00c2c414000a0340c001a441e501c1d02c00c00c102100d40b40c80091054a0040f4841d0000c40e95905207161149525881d64001e28819001040710200507500305110449084d420b444c0982c444485080c20340d51030741c058141d03542104d200c0d41d40c0250581d140d031152074100d00c00c2020702c600351078030250500d190107280901d94014905038010005440c20050243da0020071a084074040390312581e414020380c0b1a48450000314500300e280ca0722860b00401261302512050703581480030310b0014000380088481c1610740303010700d136154070b113640580740d6404480c61000040c5881c1caa441c1c0d1000300c00d00800640c410f4094408440d514210381a200404840400380c0041031071841c0e85868603014020010140c070803005120030044200080e06140265102d000300303454601d4546400b4a0302034600d00004d200b20b110700300401000c10540c0c0c1102c00e8a05440840c6041c000c4ac0085214100c401508020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 195343741 1250 195342491 195342523
    0xc1e030510061229040f0e0d05221508060409080a110709180c09140c03090a0219060f09060225090e01091b03020307050913061406030c0105030108060c03040302 71
    0x155041800583c0ca21190381d07004e4804204412a82c6c075944100d0b0743e003110006041d0403000340210310754400e10140c07035a003040c0021040c4d08035141001080040c89980300c220b913400c024120044442d0048030703007a401801074070b007130189a01d140d0303c4550b10310510344000305002a141d20041400c00400908014084c040c00070011010726200070070039058103080440303c1c09034010b0003280001031806a0085410744105403035540e241c0383d8108405400050100b0800c0c41005c56401c00350385c03000d0807041c00b01103800501070f406040081c0200441c0c0100021400d00424034001c100c000e90019030f910007440c000802d8030319a5540d084600c0e5900b00d03070780101401424450507804114040d4005182180300700e09000c084100400380151101c4284006581504140303070410807400e001038039a038010300c50109005020019540c250071100c04120003060b00c000342c0c0821075182410000050301d0502400d0150941d07240c00502951614000d0000b9090711300800414100b5001704402c0d418018560 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 195344991 1250 195343741 195343781
    0x5013c111b060118020c03040311060f03010608060406080c01120b1c050114090703030f050a03180501090c08030f0415050403020a03110f0402070b070c14010c1e0305100612 76
    0xd50507560b1000b8050124140c1c40700f400d8903044000391088482050706031006d50b06140c40c5488206411039880c0100360002c00c100102c400e003184002c000c5018001989803ca03050500320280000c5441a41010f0303140e600c52550b80c036a507a045001080318030941c8802040b01200340c5c0c007060034140c001c403000c0416034015441104005040d0081c503001d4000c041c480b0110b5650342070103980d03514507102c042c0100d0074008841c1c3d0800d229400903c104030b054100070807220b00304143d00f0451a145141502c0da039540c0d00e820400c200c505008440242910b4000358101022422210840c2c8200c1c46143c1040c06241484104180503000b5140250780003040c040c03810381e0f6400c00d0180a444904518400c19550301c1e00d00d1035281a2080d10702c0c00e504031002c511150f03103008058603d01705000d015500000c0480740041c0c0c0d00c109016803c4041d019659454803080d0224850001c038403103202c50400e00d03050400b0804422080c5007004121600d03450000c2d0b44d11200c04400707000705421145c00000200340c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 195346241 1250 195344991 195345037
    0xa05040c080a0c020706090e04210f0e0603060f0d0204060b030f0106260a0e0c03011b030506090f040b0a240303122c0f030705013c11 59
    0x84075071503102c1c001e02e160900003000240c0c0101d8130f8200c240110360218410b102c050020b0403801e48102d81c402e100d805010030384d01d03010f0610b5050b83d0303041120600082043c00100980c0380c1c04201035a403500300b501c00c5411420003000207610304200e40400c60007440a01010000d5641d01e412102c01440c203401300903941d043c042e4407903090890900822002c03407000c03541192002042c0c0c0000340c001d021280c14103420341f102c0c41000003402c81044580c0d843e11480e80001010307030302031251f0b90320000c0c540742041460601e00005003e86100800081c4a200c507501001034a175640001c40d640076030b010740403408070368490129000038003000e81140710700e0000c1c04c00c000c2c001001c15841c00640c1d01130745441c1c20302c01020003200140c420064800d500c141c0c0d80c42c44030780641040e01c40c43c50001c0c0c503101039414024003c001d0f507181d134003d40c0060782d86a4407001c91031709800e0342c0e40d171032200d00825002c0020380007101e600110b443c12160074901d603495a03580301e82110010408c29103021004c01103809001c0103003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 195347491 1250 195346241 195346247
    0xa020915030d02070503060a0504051507030204090605120d0516060203010b120a090317070203220509100602030a0e0a09051008060c0a020a081605190c05060403050316020a05040c 79
    0x4a00295020b0701c2100520301d2024000105541165001401440f01d640c4900e400009048041c000710307a50300c07407080a48651480422210312072041660016107803881c00500a00762040c40c0e00442c0508202806031a4040010070002c0d4520b00c0303828035a54840f4101d19080d20881a11006002035102000129004211800800000a18140100e0f06440760120b01d0b0172038901680040c08035a60100c0d0b50306038064100066801459401940d051240c4140b1003803500a507410401c00040030f441060140d49000e0480503000501590600003040c10f0103800f968070b11880d903010060141004802060303550385050784010f040080010701c02c6042000324040e0181d581e0080126074040c070f00006260018640030303204400c260f03500400904034591150540b44e400107007002c0c04c000404502c40c0204000700107125110080742c60400c000c407018101016080195046240700e14000c1100f08049031000003903a41c40a070003e04120106036510000d512800d456000a030080e040c5082e4142c2250 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 195348741 1250 195347491 195347521
    0x120c1a0406030606050301350a0b0108120f030a021315050d06060e0a0501140f2709011a0d0905010e0d0e0316260a0b071709030405010c050a0209 64
    0x5a440070f0218076122001540c40340800d00401714130307080c503000c1e00c40369180d004900c001010700c03100503011050020807910700f01040e0180030346d88000d0b04801045041c4040202c2a0074071000a9424248023414000319140d00c0b0140694103026004900108044a00d2008000500c03501d600c500c4420f5500b24094400e030010860101014078100002940074010384000b281d082004021a022030704240042d40c61f14501c040a0441c02d8050040100b045184030041c000c68881070410700c0f141d04440d040b031a4103584175103024003c0e800040100704114210040c50301c00288018002d454030f0404080304020929a20085d00719030030f01c46025002c40020a984a46105550714070700140703101c03070a05594000c3c1e0b841c2d413103440342c8107001040005501a080d00a8002083c0000d1030180b00c0c22019103000441ca1041c2c8100c10220103120071a40c2000c69084006124290384243d40380c4202d00703a0f01c07801144219814440d206a80c801044421710614209640c01480004c250414111501c8241 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 195349991 1250 195348741 195348749
    0x10507080705151e0601032f040306021b120901020304121119061d0f010e06040b030103230f0706180807080610080303040b15210105040b0105010e0a120c1a04 70
    0x6030b11004160340c0d511034001d91b03003140c404540051610346040800b02d980b41d234036548150400002c1c0700c0400050f0990004000e07203c025804d41c20100c541d040001e04000423901c940107908030411881c0b4480c1d8010060302e048500341c4041501081c160b04000745400f0a0348182c0d50306c40051142c0240070404c45c1800f005071005a55032840064002c0d00c0561000c281946060307109001c1228240158840e0581c0513000001030401c604059884085c80d08641080c1c0040311842c0054a503110501080060104410a007100030715202d20a1404291181918000d075000c00c08800483c0718480f041401b20380c0104680421502d0a0799a060301c20740706e910980d40440c01e44071102000507c0c07000003080d00d00a1341c00024103031b89602c682070a15a01c8007041a140d400081902e50f0f0100694007681c1039605d812484008503c1d03140c03d2030591040301c0140c10642c14441c0040305d60b01c00703446a2003144282c070000629042c1d402118201184842d5203544020b0176040400b150210340a0380741c7c0900122 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 195351241 1250 195349991 195350041
    0x3060f0e01051006170903091203031e0f06010e032a090106020a03050d0b450c04140402090a12060c080c0901030f1b230901050708070515 61
    0x3900e5115a0f511114000e20841d40040c0400994209004000c0080ca03005500401182d1030140c952010030711002c0c00c1e03905c44019800200800004004600c81d00c1e4043d1418110a0380503d000d24600207030000150415041145000d00c95031f035a2001c02c04580b100a07103080f01c0104c0036200e03681c0b01e9501030000c01b07107005008980000a26500000740032808552640300c503810704030f103980754034010025011000d0303008000c40c004103004903d22800040040c84030550200b0621401e0400c000301207580c240f48402c800000030010002160400d0303070309a6144443c0f02000115040019002e4002c400c0b000d90302280047d03001a840040c1d40c03000d45075a214640510040e03c010800b560810380403940451098010010160309620030f9020302c00c011483e28000a410183c651b008950001000d81180450202a240a6038207012075a00c2c203020207001e00140b82c503034140002800c07809820381c002c0000c400400d100c02084420300140104403004034008940d860300c0c060b06c1c0c40d06198011803001c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 195352491 1250 195351241 195351251
    0x1020106140906010809160617100e01060e0f13060614030f0c0306030a051204081510060e03100203040812070f0e09071404080309040b09040b010306051003060f0e01 73
    0x58100070040c0000d150002400a1101d40e104001502e421400420711101d6001b0407000701c1001700224000405032501e076071140c0c507041303171000c0300880c1c400e0260050811034131141c4100041034000721218156009454000c1d80401d4050104040c14828020968051107400f90442240d45680c8054103c800d540e9035428003540a1341d040d5a944070a50b80440988582c1c800200394003906001142c00c00e6019003110115a99500c0701d40c01d00d0400d085522221a00103010400071700208100c08120503808020b018506100c1c034403c220840900c02e0200340800c0d820700043c030707136018400d1140180c80e02c48195624a13040c43c0c00e00b04c56000c41c0560401c6040d00c40446c94180c420380350084026034540704d54034050324550400c0420303c0001c4c18101040b070b502d42e28122140e0400d010784001c040d200005c680760907002d01008251010701d20a903009078509402c010124a48001c801d04494200b0000601500d9100ea620703c0c001d40d07500060304c00f0307045c0241006101c2c27040c5d001e18000c44c1c0401c002c0003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 195353741 1250 195352491 195352499
    0x220f11120703061d0103020d0f0f0302010b0102250e0c0f041e090203160c0c05031e100203070f050c190807020f040c0f0513081603050106080102030717090705150901020106 76
    0x100070207886510a40104c42c014801801c1190703038840030500030240b0503101a150365a24070040c81c9403d04400507511b405291030309580400010b000781920180340d10050000b801045d2026480744102e4840b240000041561040088112407400b036685070015a00c94607a4a00c1c40700c3c408604203100b11402c1818001200c030014400c0c1c0b406102038207246201b10000084c1165020b440d5542503900810385600000e160350200040f01c50800c076403240a2072611040c41c0f060909840d2202884081d004000300041554000282c6815003d9418502c0e2078020200e506072518901d500011610b0140c25252414000c90300060f00f030142c42180c2400c24401c1d900244019180c1081586010803088045000e600340501d0181c410302c060156080c081c0c1c1d5441e407036646040c402410500080750181d5051040c00710a000307c401420204000f94a14105603a0003403a48070f580d0082c1c49031040e490049601801c06018480003070000402211080044140d6000a0b5200d4040303180035601e0540009 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 195354991 1250 195353741 195353759
    0x317010b0f07020105090a0b040909050118170a02030409061205100903120b030a0b0a0203090708120901030e0313081b010201050c0f09011e020705040b220f1112070306 74
    0x1c0c0041042060141008a581d0056565030007000d0225445102c86034003183e02d0240700c003e00000d018840001c030300d544040c01d0941c2150a00c0c000000311102d544140c0e404a81c800480b40c0c2400044000c0695510b00c0d028201e04600a5400c00403080f4201640080d01c0350040908040d414090403d8810110344684a0011a6401c4000401046c0071600306204411560f1000d034100c880a02030301d5002015984650311000101d8403a004103138040140003603010200044006800072500507c101c10307082082c0e0300710340a00e07001c2e24105512240c00c00c0c0340d258280255042076408801e20145075440320400d944031800b0504840c0f42c421600d024a00c136610500585000f900314104940c9840c140b840f00144070340c444060503041c08000104e0003901c603e4180c0b001c0c7c40781c505601034070890f4105000c00050b40d00318003045100d0100c1c078044820784011400d003d180d420a210340055035281c1c2e008683d0142455a0002070090000308510388031103140708880b40700d102a5901044045c2d1110858 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 195356241 1250 195354991 195354997
    0x26040308060409120809010605030604080307140705060f0604060306151712040311010203090603010e04020a06030207020319051c05030f0619180204050a090b0f01020c0f0d0807020d0317010b 84
    0x82d244410a588002c2190f01509542d41c020036210000300c0d48e00d442d80d01082c54a5001c0c1c8084410000000410070a0b42e845240b1078019003c02e6a4185001c01c4e07901d801d50b5484028026000880c480c0d000304160755910350004000b903520110500500403481d48091180e041032082d1440b2103030841801e90f40c1407000c100706000942e038090035420715080d0f48510000411b008251415440200807150240c0d4414010710b0080000044000d424a01441070040720f01040d80300d401418014401d40c00140ea0120780303aa0b03001080f41925400321421300b00149404d8120f5030304404910910030720361000c1c0d44030703000390310800c12102000d000341c8a007814801c1a05000790034010b142c40c00c0c282800b9000c000070001600146104015083c01e0325440010201003040c0d00c070b055882d80e40c2e8500e075107030b04140403071a0703140e13000b40050040303a25070001241034400041c12140c03044a20328800410083e4940590b8601c58028207011940e000c640340c0030703021440074915950120866800029601009012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 195357491 1250 195356241 195356243
    0x6160308060411031611070306050c030106020d02120403080c0709020301080321010b03040f080c010203190b0103090804050d150c0f110f1b01020a140303070e060408030901050a26040308060409 85
    0x58505c01e4840000c048885d00d040c0c1003e00441d000744440003010490500a107401114031078505039032540f4042c0c004c1c2c0f600d110711140000303641280020200f200d00c11341c10350341100c0d00400c0850359050020302550038030f00e80341c000b2b01078544044008103a088002000c5c00c450a4191030810032500d1500240051040c240b0901e24040403c10024ac0083c0b0f40f03501c65a85244140e6545040807000d042d0b6a003603800072900f038006801c01c101801c2274001503000749040c0480c01c0c20100098034440e1241300b0302c0d10a80c011980220840c100600402c0115010b41c203086d01110b008100140422078010003d80044201000054549400074640000424001d0210702198010225002d00c03104441d240340d803403031480d410350140b0b031920800b0641510600b18100701001c05940e486c60502d20140500e4402071505000d118240000c0c13050400010450300030a40c00d00b003040c1c903005000e104865200d09109801c1c040c030595403000e0380d20130340c0441007402117100303454080155444100340b00441d618904 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 195358741 1250 195357491 195357511
    0x604030c030602160b13020103051e0c09010c06020714070503030a0203070f020a030f03090825050402030a2c1b031509100e0610050109030807110616030806041103 72
    0x204100007031040e0f00528010100d040300c800c04400940340c41c04d80310011680301520020110004c1c1c11582d151241e280c4c03000f020f804001c480c403606032049000b00c000520703049100c0d10000d10b000241c2c2c0610710303040a140d031180d415075498100f841e20325035000003010104018850420080360300c1c90b001c07003501c0584202c0e0340110f00306034160712466100c40904006980220454001202190007107640714007150080c2c64105103585011111841c0024040301041c00b000d5114900d0380d0102103200801c102c800440d030150b1aa01c0e4411081c0040c0b0311040340d20b03c80c00c1c081544101c407160900c12054484010400c3e19000105109054540400d400e801307a4150082140004d0010103143c1d090381187c00d00044800060910004104545514406140700d51000042005030035840400300064142031905108051075566481d03014001d2040c014029591555509004d4071031409a44200e1000d43d00551204420f08028000100941d511401142880072040034598050201e07409501800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 195359991 1250 195358741 195358763
    0x703050604080d02040302060a0f110105070207030605091c090906120221010b03030a0207090b0628020c0a0608040203010f1e0f090807030e100305010b04060804050c2d060403 77
    0x40c0d561501a40300440c4120142d07030174400403000d611a0300c0a001003020945a2040480d00003c02030304146021080018680c180010413181c5607010540c40c0c2100e83c03000003c1a40c0d2210400c0d14140280400400000c3c4031035a03070b1a0440b940050b1000403200e158004110054031442c1969540480d4400a0f421001042c031024503c600c4980030300c1c5c54202440005004a18480002d0555001080d41001a0300604062214060b54400e00110510444500d03107008040041e100d421602c0040405088030740c04150b040c003500a01001500010085c00761112075250580a0b14500c1c091b1020380c005d602e800140381c5090494070035040c681c181c1912203110810103882c48006803007200324025485466040394000658224040c1c41c0c0301d07109483e4603220b10040c42c140080c80c4098141d50f800c040c1403100401030300003080c088a0030348003d40781013200365985041c41ca00d0440d901441a030060b0740f14510f64010404154196410002455481c038003217000c50412055008078000a002d0803002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 195361241 1250 195359991 195359993
    0x3080f06010c11060705060a0e010f0209100e18040c0e01090213141504030807023a23010b010f11100203130c030506040302161413020d0e0318030703050604 69
    0x1802c2010390f000148060b1900085669103410010180c854802d120389994a01200311002c0c001c0c100c2202030050114105043c4900043c2900100300700030061140d00c084441050300d400a840400ea04140030f18192810285000c40c2d960b1000d11030042e1200500c00049041c420324001c490f0341f10300c00310740152440c0c01c2401c2d41354441407035419680d005007090000c1c04000010301c0508002d50050072141c0e00c0d01c0d6140188060034442c0b424030002e0b03001d141c800c850700d484d281c080c01244503015060b400c0e4000309440c20f1a000d60120903001c0d541c03401c1c5a010388201d40305411171011400280d031121043c0c4660a419201d00f089c101c01043d1540000400d502c05100e1b030b03800b40d9800201114000c0c090a8a40c4424824603041c1e04181c409800002c100814150104204000c2d140230104520000d480c11399585c2ca51a07820b2041d6114543d48030303034a030703018440d40c06a6003d440e216508101031141d1554850f6690300c020701a040740c60007140f45014a00d004111902100e400402501440d619 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 195362491 1250 195361241 195361253
    0x503061518040201020d0f23120105030307031205040f0602190e1f2114010305070605040f060305070c060501060f0219050c0d050123071b020f12030c0d050703080f06010c 75
    0x5000901010026140c8c1d0381903507046410582580d00305040055561610714042100a90344140c00c000c1c041c0c6e100704003001c0029400380071010700325984480040e4030b8945c2d2030705029454001402618070f40c00495004000700e01c1d1600182160060789803c62400d074034200380a64205483d8044c28440350104ca21070313090b4020846400c10f1104142811484150918210125101c40b01c0000c2008000001801008020010030002c3d10719070801c0e40c18240b50400c83c0704070460fa8096a01050344030004644040d0240d5070304415140c0c0001c05214560b140c0800030f00050401071904011709c07030030740c480d0414000382c03410008142e08140a400445102c1e0240858400b40c401c00f01c98966a07914072000c0e05034040d800040c0801201152080d03400d01201c000c2409001138105420100316038480401691382a905002c5800183c40c0c200000450350442400c50091007541191401042e824031a6503500800902d03c5601c81c0d143c010894444850070710209604403035080c0450f40c01c03003040002c00e07e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 195363741 1250 195362491 195362507
    0xb0c1902010e0f031204030c18020c1024080105070e0105070b0f0408041e090e0f0c011413181d070e040609080d0f0e0c0f040f060503061518040201020d 67
    0x2409400c1700c0070001094030009040e441a481628480c02031a01485603c582c00303c030320050600c03140154240946604444d455100d000c0090340d641c0e968903030a2990100382c0e0910300030300031401522800c1507541c5800c580a0070b4101c1f450400070f800707003c1c0803165600840548080942111401103a940c801128490441e03020303205072060101031000082401e880740d0040c3c4c010154010717802c081c61a02e00c40c6403e4031406c460314441078000d8003030102a618000b4950014150910f02542c050030001e40300103c03481445c00c1400304100b003009c0032032181003400c000340c40f500302d402042080041141107290504201d004c42d001039004100100501a48011860b0f0400d004440009103810303035548405d4158004000301d00c41e15124440005c02984500c80c112145510070301a120b00102c0d0070000707510401c030944032840b072984d5202c0060052040d92240024001c060121f0325181000045007004400c1800c01c0c1788525090910703c1050141c0d00816402140d040c0c0040040100c1d100040d1039500f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 195364991 1250 195363741 195363769
    0x7080a02120d0606021b030a060506130e011b030501030f030804020114030f0f09010606020d0c0c0807120b0105060a0c021e04180203162603040f0b0c1902010e 70
    0xc46071411880800e101c0d03000400b841d030001d0a00250b00c81c503008010382000c203010310402c92504d44210300441382d10b001c5510070310198807050000301a42c4030b1000400c82e1234441c0403e92140d240c000404100801580100c0e001080006404015100d84604a060318401d000c0140b52028140303801c00000e000e841c02d6034202d84141003c2d500c2d04114007101800d03400488170090320a212109110078800310850454210311224028440503081c01d2001e551071140302803907000c2008240214080c892003664281c0500000c0085e1009150386010610b01a40160019140c0080c0700c00001018500f441c01c407001102035031204244207081e9020000c810305e217100e1550548d16160558a01e0303a070390f449229082c007400082d0030b11011603801070500d0300000c42914036606400d40404d10220021541c0d001031142c90402000b04500e2854045046010b25031100090801910000c90001d40d40d1010380450400f54040b202889003040102801070f034100d40c080d0200c3d220b200c1120301801c01c005d84400c85 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 195366241 1250 195364991 195364993
    0x80a0306030204020d021801080c18030c0603041b0b040e010e0a1d03030106020c0303071e0c03120201020405010e1c0219050d060207020405060306040b0a1a09150f1507080a02 77
    0x35650781c000c10142e0340204e10344c2da1a107074005072080c074200101da010080d601c420701e801c0c0740350b10344410651414450a0100b0760407038103018804105507020010305414580280036642c8a0a162814491441c1107420b4282d541c0c236112030208120541106440807112580080c05290346048241303c00400c0c00b41050744950b8654607010b00c641c618545010714034a801d801140d50b5031420200074140100046268403942041141d000818005180441c00c1c075445d9034242000080e03850158520b1405520013809503c0c17240340082015010b40c040c00072204280c80300d045114003501000f0849050350840400000c1d02000e11015040202e24100000c0503090300c4641c09481e24000342082402100403945035400146840c2142071134014903411910a9006000f50b0525079103910a0b00c0000300050035050f900c201c03304a5105018210070201c2e400790440d41d1a00300300700400300d40000102854000c41020400046905000740b0003502180c4100b40c135820204d05980d00042036109003a44821 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 195367491 1250 195366241 195366251
    0x60a0c05040302030a0f0b0705040b03060603090c091513090302031801050d02040807030c08030a0f0e01020c150c15010b1804020c0303070c0b0604020a1b0302070f06021e0303060a03080a03 83
    0x60f1400c100c0c174858107018092154080c0140d15041e024402c0041020041050901042000c0c0100800380e98200d001150360325126038800108030301d015010611190710401c010207102070240e014954041d8000c0035030342c0300039001a0030006015a142d0311002001039004000d00421500c010543c508207402c140b40c018500108402d0001c2a600190061141038102040030020004072080c07101c0180004805142005041c007005041569889030000074800e5003020410280c0c802d210b411000740000748544408246d0300d95a613850340000202c0c841520604400210800c00c250001d8100c070680070745a4030708003012b0210702c06010002c0071035802c15001e014180401d0001c0c00034601c40d0320765a41e500e202c242542400c8804000203000c850240d4410070001c2d0205602c250401900d07680b46110350900b522030f2400b2803414005921201141880d124086101c55000c00c1160b02401000442643c00c3d1030355203090f0f2644402d4072481d030b1120402c001000000c3c0041c010b807046507564100016 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 195368741 1250 195367491 195367493
    0x30f180d0204150608010f03030e06030c041a0301030b151e0402040e010e0628030602070206090409030302031f0b090910090204030f020405160c0b0c0d020c0102041d09060a0c050403 80
    0x162483e5481d0410b030000b01c400c0c107002c0c10354003082e42030041150501260b4214515200134112510f400486030040000000040c0540f07a500100d40007081d440b11003002000c3c01130041020f5400030f000407223000c40400040789101083d44a007002080c002400d150016140d2203208240301c8030204043c1d0096000c5c080060345010700c0e4000740c0240500700d0040d020345480000c02c6040c0303103440a00c24501c3d030071403c14101c1041c24081c0708180c951000006035941102d0001400501035411001c0d8040c0c00d080c0c05904140c0d054002c3c40c001d1000340c814010010030020340300d8164410f0701030392421311414804400e140c50030302101a08502c0269049280c06e031109214401d0740d00641095600c0031000c40700340c04505061007041d0b13002c403071420802d44544006100824201c2003036400b42c6414809000304842d094494100e400d41c1d421003c08641c0d0706000c0410034045d410611403056001c1c0405064804601040b182d54418421b150180016a0366a030581008060034007541080040600c0080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 195369991 1250 195368741 195368749
    0x6092a11030d06050102120a02030306011202070f030c020909030a02030f07031b03090828020d05120403060e19030f03020307020705060406050309010506120c01030207110a03140d02030f180d02 85
    0x40391a8003180b010414a040000180c40c00301d07400b04d84850060204603000006034040180c0b50003020074a40204440d13620f4900708064010190003401441c8070030391034410150130020507070480348240c0309d800150362810362454590241205c4800543c00420694440c026071500403c01148241091141d081e40d01c14644104848004100c1c08240e254905000e1003004107d0b05c1c905001c0aa005810754611100483c07889105050090280a00507902c1040090038401b6804a002d00900316444075904c1c02e1050242c002d00d60702d40030f18041c062074040c0300550056028892070f01622481c00f00c40315808100e000f03501c020024011405a0480490f150303541c90000c00080c4900d6803444e4913820804140c0b030031180060310f41842038106200040e180100031038400192075090030016110450341c03c1440e20b5801200116900003d80440407080118000100090143c050103c404040d52401709a980e4415080383c8058070f030b03007030103e0705905a6404941034994405421081071b100e05038003107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 195371241 1250 195369991 195369997
    0x218130609181b031a0415020c0a061803020c0909030403050703080711040b10050f0903030307020109050d0302040f05210a05010c021b090412051e07030306092a1103 73
    0x2c8800881041a01c0d400e00c2440103100308450b600940704a10903207580e6070040c1001e04607001800f00f0b00840005030a12801c0000c04450f5482c85000750354800d0f6500251761503440c00c1ea07080780c1c1c69142c000c0c1400441d1880c009005040c1c0d1540040c404039444400b0810302580051a640c500d220030030000c80004c50502802d0000c1d445902d40310b4440f29246080100303025a000e51900442c5418500720003a41c1d008405641c5500c40c0c00c0042e641c805058003184148144080c1a0701880700001b4080322507415440050640c0c0104191159051107507021016407285200701c1c803c14070610418052031034010b0581c01180310030000b698042c60880c15050600c2005c0800b9981039549800c0d007056a0380500070070b111130300c0a190304400f800da0540012422403001d000a4072082c031034049940454003c004440550302c01c0501012946096100e80515500c0b902c0100c001074285840021b010445e03015110603e2890003020910007e0701c29400361079100301824608002c540355014402d04024070003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 195372491 1250 195371241 195371261
    0x705010e0a21171309050907050a0e090610060e010509060c19200102150912030c04150306051e01200106050a0b070305070335060f0102010218130609 66
    0x55007200303074050600311020f102c801c1982c582c07803108001800e140c81c5411030000541d084540000f03071a440da4155249032040d5900a240c10000343c0401040000c007805042e44141e29080844500c0c3d6108440602e02d00c2140c40b8540c0030690411034046e1542c0504050510070002614181c2000058204139160200b0310340c01d13081c80642601d50000784082540d81d42c0c841c2c1081c5030444c0400d404240000e65503609194010329007880713200030644001301440310320300792602c07549429240d0504251901241c1d000d881111154105504000201070080c0203080480744010f0001111b03085065206860021039000c013410081c11002d41050610903101e0b070300703800c0c2d4078000014050741440c0c2804400c90607900a43d0140c0003d004950000c0e51280483d440346a140c07404501242107080400e06400001851a0480500341c2498a2641e4407460081c23042c20200d030318526048001c2c005901304d218003c408400b0031402c2d0700b034000300d080004612000c68000100051a181e5840c10035003102c4000d40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 195373741 1250 195372491 195372539
    0x3040323090f01030b150f07050319020c04051501050a02070e070f022812090b0a080603010b090f0109020c1603081c020909040f0f1b05130204080705010e0a 69
    0x80c8a411509082d00072441610080c202006040c841c4000511071030303107a0600a03450440019000d01c0111700000b0340c0c0d40958445c040700c0d160303210300007202505002c20040c2e100510441158035468075007401814000e20500f40102c10304403140740112015485a179042d0250b02c1910000070b1702040f0a010140305006070780c2c43c501c05220074580281001218007641d403c6800c6c0d00f050001d0b84d40307008510a540c9500c640ca40140d4055410700350748208441c0d21110000300003040f00c07414590000f45080c0314060840c001c101c2d03400350108102031424181da19440f5180114014002804180c0c010a051141e0004840310b000d00c250946c600355072560001c07a43c046010446014001404a1080c00207002d00f07020347c2840041004034240e640c004002400703001c44c50b03404106204a002020340c0d860703003194044c00000016007504032809140d224036406003201400c81c13602c2205500c01d84d42a100c030a00a05a0203182030011aa40b40e5100e0541f580300d00075801c0014409402c00801c01240a440d07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 195374991 1250 195373741 195373747
    0xd0b0a0303050a030c02010e03090d0309120813050306090d050a030603140a03030506060403031b0206071505070801050d05100e0c030d080a06060306051f0905030102120906060415030803040323 85
    0x340f0007010b540c1e0200000c81503a0400341c189002c1c4002200365a00b500098841401c085035034103003200c0c42203a942c4403020079680d0f407c400080c001c0c107000810324031983d40030045130399540d0b0061540c1c03800200d91800da02d40140301c0c001c915900c0781000b40b0103030445107800704456440340c9484480b00c075a0500c0c0606540481002c50401d5054003c459000800b280c0b007604152940c1c40180c810025940c51200465204824204554a0744261192030340c001076412038442c9031050303001c020038007030300c01c0f40101da509000040d803450080d075999415603110000e400256402c000885c0036000018002000c0d00800f000390720035481c10405061580515550f102c0c050800703c2000040320400c5e04840c04250405106102d5606c8480038040700c2010030300300544180c00803008489564160300915859400055105445080c0d0000e1703034004d4100c0415120740b500c402041104035585565501c00210302c03400b0070004107a80d80051a403103030281c10100961045c06441811050021100b48003183c404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 195376241 1250 195374991 195375007
    0x1103040209091207121206090e0c0603010614070512130e070507030c110d050f07320618090f010e0703110409021e0d02030f0f04020f060d0b0a030305 66
    0x40c241d141c1c2000552001c2c18a54415400c51001c0f4401c4401c05069441c0d01441c441c0228455244840107050225007000010744508050014013207002e120007041c400c031801d28000345000c008036030480c1e180b41c64080c0118140c2150741051b4105a40a0f1102e004420780480e005410350024111032a4030003003044021b0403e03808020140010340600f04008003805003400094000c00c16042e00c5805c202990042c0c0c2d41c030030015410079504c1e8802480c0b4050070218410203203000803400c0650b1401010211020f070100c0100030740080301c0e209004201d0310315440182c5810907000404d4400c100c0b00c145555401c0d614041141b8440c00e5552156044d4490700400000051032055a0002c0c1245814040000306070014000c50003140079410900343e000500d03085006034148a0703001f542200c8051038450a148100100941040321040014520040064901c0b0f05481c01d541c0306660040c07c540e01d6400c2a4188682c5801c0700e008400e02c46e54800e442d4100741d44441141c0c0003148070b40d440daa43e503804 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 195377491 1250 195376241 195376249
    0xc060a0204080622170d0c21020c1204030c030303060b1305040b060913021306020f0a080708040e090705011107060801050f01050f0c0106030201230307030f020d11030402 75
    0x4050520092040c0320074403080c1004640d95800800310805251035a40b0f9040381d4101c5100c0c441c00074203503141c21800301d2968600c140949004c014600e8108498032041c00140d41402c903085007010303d40501d0101226400311540500007582d241021210b0b40000c186d201505a400707600280d07000103400c0c2081042541c1401240058011411003074108003008025820005050203694415902c503209190141c40306400c1d03e400010051880354544075881201000b98008000300340321241c01003020410320b00004444242440440080c0040c0c800c0f030700c0e2440c254000c0700302101c008408210018400c212218120301904405010f0442c5500e010000751451344604048c1003150400007040042d0b03600305107a10b04640e0195030007600741c1c003441d0049545100e207a1110008440114040344510f00551000058a200307807900b030035400b40b002000c14903007403001c41c00040c480c0030070018480d98401d410900c030300d1070044005800e01c445009808260740b40d403500c41d004644044200320039494 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 195378741 1250 195377491 195377503
    0x8121903020406200c060726070807170403060f0c030b0f06040603090501020702121e06150105070c0302090a020901030605060901020705100207030c1d0702150604150510050c 77
    0x1940d0a007145402e18294000c1c045644a00700713601c41c9480302c0c008000070b03d030074003040b11210401000140d840d5880d1a003c0140d0b0b403200403020100701040d00182d40551801e084440407500500c0c01801c00c11075540313104c01c00c0e0058040c0d42d10b00400f80f00010010708280503414954a500001050130501450b0040c01c849583d1242403060040d2244155240c031b8000448003514001d1a022811040c50b04280740a0312134a14000d401607042c1c6010074002c80041401040011801e110088200000038002d503240320513070322040a00101d42c0310015641c0120b00511440e480750030301906013690b0703400050701c0320f5040300d42070480c03600042c41150f00d6070b0601c2031801910048030b106062401d0080000d50b01d40c00c038054103000b00c0c400001940744074000c22800d0025071340074030881038454451003002c8030403030b0061070001e00340820f001103110540041071f800011000d02000300243d0f44c880c81008013038502224203803074500041c0030100c0ca07030b00c0c0c0040c02c0b01075482c07507200ea50313a0700200c5200d149026 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 195379991 1250 195378741 195378787
    0x3030709060e0f0f01050702060906070c0612020f0306010804030e0a030c06031d060a02030408040e0a021206030a050a03120609050f01050f0d0f06091716020306070c030c0b0403090812 81
    0x3c821444422140d6454450181d9952030a180840e01c6d00c0032480410464494035010075400640807400b0400c00c82888011019141240d0700c3c1e4545400300c01011003030b4014000d0000703d405003031000074440d500c9000c085500c140a4600707a00203000000104400441c190416a034100d0008000d10583e90140190325050810070380680300c2c140e285070600c0d107406015040d01e0340c50f0b0300080818180540c14050790040d2222440e2140e260415140fa00003e500480101c200d5011a2000440030324000c01e400c658140c01034041d06c140340507903034101c031804000107003800b8056a07041c0c04510031806200d4244505221308a14030154100005c018602c690301441520441c0ea8400940c009001e80c0c1c4002c4074540d1180d4080784003060351500d100c00d86428440314207a0880403a900c1c1e107804000c0e11103642d030b900035400e40300c0c107443c0c44400b11528480200094041500c1d08100000610705243c1d0039480f41c000d10f0140601616695540d04120b8200e851130101314020402c500c110300504462070100d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 195381241 1250 195379991 195379999
    0x13020d0f0e01060f0e04110d02030d0905030601052209021c0f0b0105091e06040b060a080a0617070303110109171c06150f02100c110106051806060a1103030709060e 72
    0xc1c54945205d81c56030380200010820081180d00c4903903500c404000c414540e6006050703901c00703034101790300404c0c04045215181c0700e48118030001980b418482241c5130f101c5292664100100551a400009481c1c110012a000b2010002a030840c400100b0000da6030f80c4030340040440c1c58904d040c427004200042c0c020301d200744102c40a1082c2c080000d1144100080300c6520182d641d564600003c2c024070101c80020307000300c000500030078065030018656120b420a000304001c03581c0c80325442d0a942041e9200642c282d4011034081c80400e000c1c881c0300c000003141c0000461900c511741e5071510741504c00010303a0091600481d101042ca51000640000c41c0c8104e1020080d003460184103114141c1c4509204003402007885010043c0d0f4030130b0110720f414044100003441400703140030b8000c03c03203041e088140c03081d03501e01140481d06180c40500500f4959050524030a00c0d11614100190b5600000100c024031400d200b0300c9408540c140b024622444154480490700c030700d400e4000d030100c01b100c0c5e030b02c0d481 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 195382491 1250 195381241 195381269
    0x60c0c0b18061501050417030c030d020c011a06180f150304021203120f2707050a0501090815190608030304021806090c0a05090303040306021b07030f0213020d0f0e0106 74
    0xf151341d103d816641101d40061640c0d0030a8203401c202401c41c0304d4151040c10764040001c0c00c214005c0b6a40003081c2c0b5001010081046079620005010b4468007000603035030000c02042680c001c012045044240610b0007401c3c80c0410b81004002209038100d04c5244181481c0030003007000354540003109994866101c0069440c0110700d180075039060000034100310308044000b000c034220220700714848a4102940e001454142d1059181e61f41e105494482c9030720544d005200400e4951143c840901154812001015001085080e5005004004000d0a02c0c58294007020110a80d2401408000c1540e203003c0c554a0429005003c91014603083c8290900001c030180405511054000ca40c0309820780b41e01a1900442c2104407064800d20040f50360512010034044107001d0154020400c1030011402086d0703141040c494143c80c2e21581c4406051281079218540160400751a203410b0864440d400500c1c1580d4103a030031007107540041e60414032950b50b113280f444100091042d04058801c0c10745000c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 195383741 1250 195382491 195382531
    0x15021510081b10180302040f0b04020a02070f08150117030906070807060609060e04110a05030111030a0e060105011409030a060f1508071a16050a1a0609070c060c0c0b1806 75
    0x50745134601c1c4030080c0904e0303680180c0c413081f241d95407050009800040c4117564542081100959819050191070040d040b02013000074411000103e4045a0400404100e8160b1800405070302d081c2c4403030f803501d125000030400030b20b00740da41300000d1205521401e2440c1e21040c103403d001088074002d030000e49000c0e16046082c0503a00b800c010144d482607015000a00c41521103021a20f40e1100ea40301c07607055030801e2180103217035607020055845006090001c001c06050035625980d2410203100e402d002c0b0f132982d001c07040d10610800062042400103021103031084140d076104012182c0b0b40900c00211695070100b26401c210b1075030410000d1400da402007890324103200c0040c940032282c4804000e20700c0e00043c120940d00125040704091500f090a172540014a82000c018074092191080c401c6200b101c009107442ca0102007080c05004c0d0b9030b9920441e0100340c0c2e1614000d1050548004c01d100020b41d4270b80000e00c4c0d00c41140d206803028512180b4801e4100a05480e00401501103015008100890300c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 195384991 1250 195383741 195383777
    0x40216020d1401020c01020a030f15180e030d0b041a030c040915061706011a0301060c0515010303200102030609060d14030307080f0115021510081b10 66
    0x11140540403100c26084079840e1030040e082d40c1c0081000c900c6540080307a1940400c0c419405081d01c10001d07203085c06114480045241151215040c2c110809038540c2c09000d02220002d06c0001d4500c40440003940851920302a480d540180007c91000e548400d07000e030704d41c2040e0050b001c0500001219214844040703002030740310401480900c0c00346e079035681c801c0288480b11400342c00b000c1c1086010040c254441721090500390306455601c0041c4900c1000244420590400040c0d500c00b15640b10b04503428000d0466903464840f2003520f05d48150b110407995154030711062402036100ba00ca0700284100d480d29541408a22050250302c3c2c1d1050082050580700c508141c1c2c1d2000040b140c1c8074036454249080f5104010b0500c071080f092001004200341c0c82e0704090041c0c0901c0d05c6001d04020f981c0e85070034806221042c11382c0e60005800c110b0800344180c40c551202c9400c11239200f031131000943c448400c3c0f0325001310700d030301b200c1e0541800415a09070306000036244513400c61485c06030140d07800c2e283c3c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 195386241 1250 195384991 195385027
    0x30f10080f10050615030a0917040e15040902180108060106030b030303010b0705071203050c0c060403051b01030b101e0203070515040501021608090102070608070c030e1801180b0402 80
    0x190b100c10380c0350f10000d40c1907035542c03000c1d82000c071a41011a803139040101000d801840d1042d82240c40001440d01c400c80502071030255011103140003103100c0240c0d1102c2c0f080809105da03600854015885540c0b00c00180c1d10000074804886944110141d21362500d038100d85803940c1a48080d040c58036014603a6a03903100401140e05558804d520343da980e031424648030385007940a50241d50107000381d03e50241007590020003003c01c05c401004039078100e8089000c100301d910a520008080307a0249600289520300081d001000d8203050400140041c150b41c00300e00e00500540034040060441010070104202a2040c1c0110050910041d402c100c02c0b91b4406994046040c1700b50680e02e4088000b03020494250100c48501c00c4409420048200d03074030b480105500034203400740c054002c501010822a22610701540f08074260740d11a1000d0072561419204101c20661443c0c0050703d14030030301c8481d0700da0f0081c1c074001d1040d40010143c1e9401d40c1482000c07500c801c04c089208a004201c01c1420010744220 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 195387491 1250 195386241 195386263
    0x1e060b040612080c150705070309050a12030e130f0b01110705010c0b041e060c0f021506060a0c0506040b04050f0d0903240f06060e01030207150509030f030f10080f 72
    0x240d04e40d40c950341c00045245c0318803051010340c50041c0508200c0c2082c0e001c00902201d031710a8840b604410784643c1001131840e900e01501070074551300e80340c46000c20310407188d001d07a284028002c04842c0d04820301c52425203101e2404903c13001e0712128120303090b590001201000c01203c030050881d50303080c040024506c600656001d02a00000c4001c42c042c0211302800d180203220300c56444156200901c2c01c20058030160b542c02c0c02044401d2041008280003203140c80030026100d030345c1a0703583d46080c01c00803650064403880701001103010b19540003c2040041d40c0c0070364020880300400d031a1a243c00c5c2d01d4003001c1a120040c94020845600360140c000428405583c0d000e143e084c00b4019001401090600425411905504180c003040d40d4007542d80c8100192001662462400c581120064080e445500002428041103000a043c0c6100e01d6105680024403c0c054030314000442081c8200d542041d680704255890f40c4091010740503003480550300501e1a50701400c000384003c84400d444a150006c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 195388741 1250 195387491 195387503
    0x306060904030c080408150403080f060a180b03010f09050d020307030f120e0a061e060f15030603150c0e120a0b10230405060f13090305071e060b040612 67
    0x1882c2c0d400c100b2600e080c1d402411070601201e4111041f000c182c084680c05480640100d450600411482035404012504c942400341c19561284d06e040c9501c1c0b13003006443d00c4100d006d41e4800d982d00490b5002e00402c01c0050604c1c801103030030710050408604041c840c01007082958400c1200c00c0000c1e4101d580103094464070f0030400328100244203a0310103008640c00100e440c0c050040480100a081da000102c404840b01c846c5604980b84441241142c0e105e00424515061442c4204031403221406c1a0611503107902e00803d502d40d07250b0380c0e440600e0790003841d030071071a84804503032075590f9011a401d03078003013000c403030020186070002c002540703841c140704001d840d11850800140781e408600400b1001408003241e8000c3c0c2c41d940300701c00416400da203121075101c3d07820038021810a01d006501001440c8008104080044100b60b00308000c250050084051100038003d903000700f80103007800128000e0400014071241c0c0030386040c008903280c08861600c11032801030f080c002200c4140d081c00007942d0242d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 195389991 1250 195388741 195388757
    0xe0108071209080f0a120c1b080409020301060c1b03020a030204050a0b10022107030801180603020d080d0b01110303010b16050f0c12010603080d0c050d0e0c010905030606090403 78
    0x120103070140c60184000b0700124000038081c03c40c683d131a0700600c1c5a82c9282d441003041c41c1d41d03e020605844101e5082070000b99510950a041520441101c0140c0c0c42844490f180940da00c1c0680140d030001d0707001401080c0303400981c0f003e00000840511500195413250000e003805d60340010520416404003a006550f14000140c0317568a6034804040102e0041c04000c814600010095071110608550401d00341c000c0c0d0700121500700007054030308560b40340e111001c0c0c0da030034a04d100f50249001e05106505a4032204000003503240c41f03568202c0103015079507013540c03030390744c14008803d407030340840005e0402c50102c165423401d45c4040f05680c1504c41c100d202594481001904040c10724107141c0140140c01580c0c3c190f001203400050180b050b1100703480700e4002e140010401400c035038840c440601300103c20807684e04144859400007880c000305081c02c50801c1501c9a0705421a094032801940380e91007085060389940e00212000c0c000c00003103001380460310302400400c101c02d40240000302404285 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 195391241 1250 195389991 195390017
    0x18110310110903070920031f06030606030b091605160b09010204030b060613030204050c19080105040f090c300303020307030b0901080d080604200403060b010e010807 73
    0x34816165008019101488a05070074845400700741c0c030001c000d6100c4c1c411040002003052950059010100314011614106000580400543d500041c04850b83c80e124501c00321600d00c003040d200d009081c0682d80040c02a00f40350016048501226031a03104054540402040d84280741c4220011009460103584407030a940710314180500c0c00d5001014020740741d02b0403401e01c9055010f0001c8a000e0148480316031111401d201091080c10092050b101e09802d0500142c01d01e50401303500601020a00d900d030442000ca520318a4000204ac40001540f4900401c4203140c030740158000e401c41d0039010041002d86995220080344113100d04e9030091000d48182e8800141d203c4c80700d100000c2c50049440d81c0c00320303250040081d48212503d60101e494005100994100307641c81d14141d820040007000c482020a00644004000902240e07120351a0f1858845841640c200d04202a1411150644913810362038100156448907034054100000301400e070001c1c6c0c1c0c1c04a900da030024920f003850444603607c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 195392491 1250 195391241 195391243
    0x1b050d0309230a050705040903080c071109091b030706050a110106090e03040806100e2716050f06030408270901060c0615050102030f0c0102040503070303020619181103 74
    0x10280d04040e440306215007481c0400c0103c2580d100d0300039600080d4403001000121092980083d00091480001500c07842441c0b00400526000300401441d44042d040010900c0404071507020041d084003855064000200c0c0140854034021005801e100741449001071580c00341c103407842c0405c0001e8a5400411000707520100140c0481e000a00002c85c4590358223907258403610415400340700351400100e44220050a84040e5080d450701d44002d5100e04400102451800303000410602140e03075176071801c04007000306035002c540304440e040102c0d18110401445400404107140101d10400802002a810b80c08941000d9400740300d020700c87c002058503002042901012541200c0100b0011500a82095816115030306c0b50609105601d1040720004262580c2c0c803840f4096442405580900e5041d00c0c060405c00d1040d400050510b56a900000e140100300c1c0d100751701681100c428081082500d03c00f5005c408104403003403000208176100401c01c104007400c0a003c081840c0720741006650 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 195393741 1250 195392491 195392513
    0x903150906090b0c120907080a062c0606030f060f07110f07090b0f01030b0a0b160507030c05014509020307080a0e0c06030c1b0708010c1b050d0309 65
    0x3e002550f0014902e0240b80c0e500351984842448014521410700164101c800040d00310b09843e0400c3c06400c000b1500c1d500d0344041c1c40741c0c0c0f9268180703000400d0416019060501e0421191400d00006c1400e4100f1034140b506000710b901c81180f4603001042000a401e0f05048501c0e00030f040c0e4585901049140a0007500f4110700b83d0009440b401880c0000842400e01d4000603800d110855074600a40d0f6007c0054044607004c122082d04541050020410400d000d0081e107204240003520b1140c001d0680d40755800c0040b590800c8640300d4800034107201950340110040340c49240720119044103800e010002e01d16004e850326083c0e00c9021703031404505912020014200030414010f0039905d0b03080c109406004000100da0000718a4546030b650141e101000520441d0004064801450354458680702030507944041d041c01108011401c5a056240302000b0060003809082c0000501441c1504004d11021400c1c6016110b04c0038040c001000c15808102c0041d068541e003800141c1c844c0c5450502981c0c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 195394991 1250 195393741 195393743
    0x5010f061b020a120506040c2c0910020a05040e07031509110f0403061d1f0f11030f0403031103070e0609030715020313090203010605190c052b090315090609 69
    0x4059848481000300000d0340c80c0c00389202d482c0c6541c11545270494040c8880c0c900d96254141010781940a0102110142e2203820415081c150341c6051110440382c1d0a81c0d010070303c03c000003200042e04000e0301c0c201c1400b45402c003040c0d00e801c0c03141c2e402c4040c1072092034003c0c0c010100e03466954020b108404881c0422176040f81d01509040f41c60703a950741031610040164104d50801503030903a4070881c040340c011944404186050307150316500100008000010000100003902c0c182d5104c0035040c0c1940030340090b5101d200040c0d034403505850207140040c162090540d0b802100e036002c1c001d1104894101c0c1c811034000b102a10403a4440c1c00b80c600203494903616520540446006400300c0d903203113a0103c010314090700c0441c1c508011960307a51807241288070074401c03400003c0c001c0c4651800300d140c1c1302450342c981c0061f02d4000410300c07141e141c59040110540b1074054985010000550000d8211100c0c86201c42038140f48101c00e140d41c030b5084080407217202c91607c80b0380d95801d0008000c1164080d50740300d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 195396241 1250 195394991 195395009
    0x32102070b0c0702040b01020c01050d0e07050325060c02030a0602090d0609080a0f02070e070c02010212040e19021318090807121b050a03050f120a060905010f061b020a 74
    0x2d080000200380d69a02541c010790003a820190300e00c0030340d40000b400d2a402c1030306a4500e031030101c10800d1240109942c0082c0e81241c002c540001a2980d41000300c040061000c0c11003002000420383d0000842d202036201e1000e004402da031820169601003042000150001000350f40d920781600019418800c1003c01841e640ca000f903040e040c04408405401840010340340c03088256240001669246003511901440e140c0c1540041d45540c400c81e4007a8100f031042c012074015910716117904807550020f4100013941c8c0c1100c0100000e0304031a001a03403c54605a0045140c0410701c070075681c10401c3e90141d0900d0740000382d070303412490748181d07c03048006411007112500c0e40ea00c0e14042000c4403c00d03804400264048000d10740c0007001001d0f40b825158010024030450380c040e541940c1641101c80c0460000748184880c050030301c0c0b101c560521688510b940001e00034207140400003140c5040c0c01185902005c0b10040c00001d8202034262122200088101e0000c0386920004a00441c03a03041200c503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 195397491 1250 195396241 195396263
    0x10050c07021e0f0f09060f0d1208060a0501090315050709080f070321020a03120f0e060a050c0a02071802070210350403080601020708030c1e030703210207 68
    0x211410320080c0c07200840040301c91981c0a8100020040b40ca0113072010a6400349202c4081602c0c0d00d80b404002d000076030080c21a803204601078423040c442484251003200880c0003541002807078078101e441d1201074142400c0800700282162102a00004080700d106234040d0b81310302149905002d40d09444c01000c000003140d240f4400081c5040e25030b046072004031003010507082d0181082d140d250a409103640c090b4014141d00e01e00d500c00b210501d00d000211061241d50350ba1900004000c1c1c042c881e11140d00a0040c8081e040100c210821520001c1060b8221402400b82c00e04c19039006c81d4030303c2240c0101141c002c55180c0201c60314001d118940b03000b54000d0440d03041c04003d13501f0580c60071404507200c80340303124400400d9000340d01c112980055040b000c0d00354000380000f801481c038290864018070444900c1501c400030b640c61035000040e10304c05a4000340f01640c3d940c240002180c20002e0104c051414209141c0e4080c107180511200c40204100058140c0102c0e00c1c1541500d482542000303019907 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 195398741 1250 195397491 195397519
    0x81b0a050d0e03160602030a051b06150f0409030806010e0118061e0903050705010809101e060f080a0f0302100c0f1403070e041107140c0a061110050c0702 68
    0x107052001c2c4900034002c0801d0070301600220281e0104803000f50700a503141c01c0c0f0a000440d07156101c02d21440700b50406005c0030100d8079040000501c644494042c0c41c4007448d11804000c400403805160520075403c0140000000f5070104100d03811030400e090041c0c0031989003005072500c41c00030300d09840721840310800203031103a0f0001d644800d03580840b8208007910b06412048070034500714040541190b105170800c0000b54480c442190784045200141c840307500340c0003052001c0d200400802004110b82c81303008174100c1a24440c24009004100c1e41d4010b092900040c940c8a200ca12000f80c10703100601504000e1500a02c80c2d001ca1a0840108011000f6511030282c4410b001e0180000020101031006440a402070b003100e0003011541c030b0303140ca070000f210104000781081c03180415a02500b03210703940020307200900440d2440300e2040a00700c125910300500c802d901071a0f2041080200c030f499041c084400c045a481e0892694000100e0903503190500c1782c0b440e220b40c0c100250032807041601c0321 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 195399991 1250 195398741 195398747
    0x70c060e040b0303030f1b040e0f10050904030207030c080d091505090909101401240212070602040518010506030408090d021302070501050a0b010e040b0411030906010e010909081b0a050d 82
    0x180c072500c800a0700c011500b1118007080c84138012341c0038040e0142ca840d004a44c100d0400103060740e011003c0404a86140e0700d5001117010741d0802e640460161340000b90034000c204c208000100508034080042c040000781c2170300180700500b01d100700002810740e42d140c4801c031803003042280c8103910003601345604c500344075111b01e5540050196100046d40b500c02540103505910030018100c4030905852803200203002c0d241340b0321101f4043c0d203a041d0700c81d86ca5034981038013684020706009805400c005854034900020b0048030348104a90462510b598001407009a480000740c03500280c001c60780c1368881c50320102007002c0c030780b000e400a0b500c01c900c803030f4401e60002d080d001021114454002400180c880002d1481510100d0000d13a02040c000c7d1651101c50509038808503c51302c0092021821740c02c120804100c83d84260345000603078010400600c4584040340500b4010211280b0400c9280e5050300d50f40001d0060042943c43c0c03403c106040e05010720308015030240582c000c0203444000c46c880c5005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 195401241 1250 195399991 195400021
    0x90303080a090b0f060a08010e01021b0c0d170d02070f0201020c030a0b0a021c061502241504021b0c030c0f03032a070e0a05010902070c060e040b030303 67
    0x1200000c4100002031914901406400d0031250301401c20b41e920380b1814502d038040d03003000340000e4011000301d10000c1d806009000320070020000703100059072584010b2058a4a80500c0301e5200c495000c0c0403e96031a0700d07500000c420040d000007042c00c5489070034404403040d11030000079030103460000c100c04092094180d000b4401c0c5100740c080703030301490141041c1501e503800000f000c0d20003108040016400071442c0c004140040250107a5110508020a4141103c0203500a41d5480741c850b4050010140c0412071300c6404107040c00d60a5812169040041309220000c04043c40695080120800394655405450081242c24040078403d1043e503d41943c42d00380440a038480e00c40c0341b025082a0070100201c40103110090081e41ca40801c04624000c8080b40c1442081c0034083c02c0e03c1000005800d00c0b50310090000d041034070041e4245166150305507501078200c05000c0d4410021040001c90740b5280908840d07150401100304032401c400600205440303110f007074150000100300450410f4081c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 195402491 1250 195401241 195401243
    0xb040b0105040b0418021507020301090c080f061623070318060f021009030e061605010515030c0d06020f0c0a0b01120c120203101b09090b1302030c040503010c0903 72
    0x2000701c0310903c81080207851807209220140941002c0c000e016050603d40300e20b44803070600c50140f8102c9540c1c0800d084510480c81075800141d110070074400c104080c4008210315041c9001807040c0d041440510070b02c182c2d49051034003488403580c50b1020b92030110034004030850b90882c020351501c0309414040d04a80b001022080c8005c08174802040c1503000700f00300411603019900600b250404410000d00a2054543c15030512017400242041950b80600409501c2c02d80c15011021084600d012400d40300060322003c046070622900c200300c0d032400203526645040480b41c08107001610b0404600a2145007000001c05100103061030104000181c5081040c0c0305403003001a82c0c0c1d071a590b88102c45004180244052021a410880c0c03504080c04402d40a00050564290100b0902c241e011a50141c40508101c120420340c3c105080c2c02013840001082d01c3c03901403194001c0480010300e20246c203814543d16580c00300c040340c03424038620291006071402070002c104080001101604440ca5480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 195403741 1250 195402491 195402499
    0x507050109170c0d1e120f1b0e0f090610090f060f1103031e07050c031903200a120b0d050309280b09040b03061017070b0a0305060d0b040b0105 63
    0x60f400b440d100d170031158044e14070075100100340024440f04860b450403d0f119051102c2d2a4140c900100c5200c0c480e2042002480508040c0ca000d00741001c2c140300c061f141068451180281c10880c1754a610703d0a550041c0126241415103c680000341d07100011a00710980d140340c0e0400100b039043c2c10411003407520702103403514080406a40d204607603911049405040f422a10321240000c51411076500f07400c00342034100030703007441c4842c01d0580c516001064000c0380d094030b00c01c1c1c00c58850340612a140120311400c0310101c510444020a0269104100480703041241808001072880d0700380c0c0c0a01c04103200107003024180e841c1402c000c1d989811004183d80b0411601401580549040e010010704001c42c808848c2014501101c40300c444d004104d00e540c015456590480310359800b802020710414090f914100091f00307000b01098082d8030032a84444030351200d40d040c0400890750064650944d0145400b048980c0c0b40380c0442c5d018000c01400074441103401040c4010021113408460503254192 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 195404991 1250 195403741 195403753
    0x50403020c130b0a090207080412030306050a151403130506040b010305120403030e010e0f0904051005090c030606090705070c06050a02191208150303041403150907060507050109170c 80
    0xc0c00c042220703110b0030b800f03512503081c8004110301c0c0c605e038001d08000342c003949000d0300707240d44c1e013011440c030003410003003180001da94200c203004074a0041003030303000b07400680c60344038000c01c0002000d0511032001c0084072000b41c01000282400022414070016240d010003510500e09061400182c41c11082c04110b48600400754a8000021900242ca0451b03070155500c844a424440064802d401a000140c0c3c0100d0660a201d08680315002903900583c810001400b65443e541d2200003110409408084c807508280c00000c4a030303038001203103500041d0407a2600095102c103c4192400e100384100188034482428000802c41e4000e006803401c00c440b5000d4503035021000180c1d48145850032002080b2003a141c03500300880784200c0742e4580c00044900080542000302c00000d01c0c58000b07600000301140b11a6143c0c1c51420705016248202c0e000140080306c41c00c115032801d865a500c5d025010401c580840c04400740202500490445500013020a0f80c00c1194040e003d101e0b8010214800340344522 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 195406241 1250 195404991 195405019
    0x90601210f1a0f06031614030c0a0f020c0d0b060d1b03060501050114040303030e01060b04080703050c06030405030301030f03030207060614011704030e01051b06011d0112050628050403020c 83
    0x214483c1d8042d088000d12403840c59883c046480707801d0315280f000004000c00160305060b6140e030a00194000d42c3c43c5c2d244030f41c0f50f18004400500601d0240101411500700c0040030300e0a8488440058034aa070009000c812a981c410215104944006002e007402240d0540c290f5208580006841582e0007030206202d2aa02c6000640c1d00000c4031039800d500d903008100400103e03100c5d60080300910205400400c00c40d40e5050000b6140d002500b1811a540000d01e081003005410400740041b0341041d2445800c51401d6124507803280414480500b005000f540d240701014403a81c1240c0c0139907070040c41040055260800e8208050544000070701040401410b03002010000d0300f000d201340d6244d030700e0292500e0038000456898100100315034004580e403290046008061000c14064044071b0700c0400c2148120707003582059181a88001c1c05d0000311180070001c50404110503501407150003061400300c1c0c1c2c1090a581e140103111000d440c0c1460f14040c03004240e03000c03850944808003220940904200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 195407491 1250 195406241 195406249
    0x9020310060c080a1101090b16030e07050f0607030c0b09100b030615040b0a05060c2b050301050d0c0905090f010c0f2102040b0409060501031802090601210f1a 70
    0x1042024004207401c0c04a4400340d482400c042c0d103c01217610000c0307142c10941c0d5803c90f00b140c05842020030340241141c20482ca0340d041c49200309890020000b80281c91600002c50f48410003006030303500442c400503101c01807601441c00400c030139a0001c035130307060345c03911001141d100c013060610f008100341004840000d030310340015581e01541544005400b64004a020000105401e20410b43c11035000100002e95603904805020f4844829000d05040e2140d4154415561440400c0030fa0601c1c1140075089659484404e0b83c1c1960420303601c1d2015004c071410310349001c00c0b407940518003c1e0300b003504001c9131540c085001c41c524071841d00244180c00d04540705403031401200000c480014564280882c0c1d00008003210407110041100040ca000c0d100c1c09202c8aa50068000e03041880e150300003005030356414840c2c001d05200801a0322820f003e40d0307000401c80c49000c0c1145042000411481000c00d40742c684000c144081003008201e401c1c0000c029001809400f038200191400d01e486109444c18 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 195408741 1250 195407491 195407507
    0x60c010209091302130b1c0305030f010b031902030901020d021b1006142e1d09280605040e07030c080106030c1e080105100e1008070501030c050c070902031006 70
    0x3900902440150744090010f40040000400e502d0f444003407d090100c107408404080c4501030f01030b41d039035540d03803418454201928106911044a2100c100200442203040c103030001030b032041c050400742c1d81c3d484200100d40a4010580f05052040c400609001d110441110300784010120754280d8450648200440c0125409880740c02c805101c9840c10080e58502a03a04002201c0e01d614105400b4600707010781d9040b08107120851011900200c9031804151202810010303c0384100e81403061850a4280c82c05103d0b0b41c8038001c089207500c0c65140718643d0803074225030040e00e40548200069210860069030b5170015100a94201c02130400c041784042c810300804054070342002c0c054016a00e01804c1402c440100340851050707000048000c00d83c18001e005a50040d4880050411010300700100c0711403049025000b008007200718107040080c13450201d80582262800d00340040c4d409075030031060f01e42d441104103074042409403120110702e40c0629400f4501480000c03601010716a1940001c0e240d40c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 195409991 1250 195408741 195408743
    0xe01030501060909090c0e0c070312020c0307030e0d14060a0b0a030506010e18100b01120509060c0c01060308041203030605010203031308070c03060c030507181202060703020c060c0102090913 84
    0x411a403802d202d500710035000750451910800c2046d46840c0d0361100940020307800d030360320103542d00002840300501d039110001207590b00d0049004c61800540301c80040c2c1e00d1081d03100042c148040b01040b40d40d96920200c0b1201095009000c0d111640c0708801c5064980204540340010107140c113403a80b840342000119039003941d91080c02010709900382551400f0b800b100902030003610880b02c8034580e0071001440102d42840f0b5a500204459909200150a00d0240013030190320910b018104915103000046a58000c580890780e660b507200007441450140c03509030009400a400040c0014041c500040d01c4d40c1214080d507010460030351188e004907100c3c4825180c80d00c41c0354641403030002045c0c04a0040201c1c2e0712070418450a2692550740d082a1107001007020b012980e40c804014207690406115100070304013004450003d1f0408200120110043c00d020780613840c0841c2040c03c25000304441c40f9086802404580c42e0001100c115002c1d5010075549409032000c0c0010410713600302d800d042140c0c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 195411241 1250 195409991 195409997
    0x80a0f0b330402070816050601050414070c030203090d0506090f03040806070f03061205010b150a02030d02030c070c08070315021318060308040620060108060c0a2601060e0103050106 80
    0x19034440255540150a081c0981c072550801c005030000340d03068000c00032020390400f0007940314490b080c203600f080c005030f000b10f0040b402c0c8022811454070109001c0d0b4810030382e041c00c201050803420100c0c0355010701c00190b43c02040e889021020311000107030300341c400d5202d0403c44000322003041013541c41e03014600c940d0101c0e60142000c00c854a009000303100340c11806242c0015082c2da50100481c503031680b0101a1002d1355079240c00309403418a840000440d81d100342e400d51034002c040500960b60300c10070740c01c4001c0c2940403012030840d111020480b0200742d08200201c1e41c4070b49428019440342498130044a800d40e1102001d034500d403c50080d12880c100804490302d0591601919810038554440d0310400c49a0714000840007900c5500030703001070700c003d40c0e507184a01b100b050000c6a0120450a200080d4000c400400c01c03c00001929030b840340d800e401c0c00d0f44941c1c2d000819222907220a502000d69900354400700e620300143c0644904035000c50b607406041040c084010740031140203001d00000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 195412491 1250 195411241 195411301
    0xe04060f0504180809091801140f071806121805010c0206090a0c05060304030315090b030c031606030915060605070209060103090302060105330403020901051c02040510080a0f0b 78
    0x1080c648506c00592003c512013800005035600000300b421910a12400022060030340b080c00a10020240350315030100c05070403e9640301070008418030400a10788940f004001142e0400003031066942c005625a0141200e001d540070002e24246002e04030301c02030940140f02d8500000d01001c00000c40c40801504800941500c81c10304042c0041540003c1081d0141a200e820030002e050034040c42c10001e00d00316800180000d030f01d43c10141840100045e480c840c0d8402c080300d580396001e81080d00100c0744141800034064842d443e005400d10225141c0d0030440786490313400102d2540001c01081c480d8400c071600e030790720ba80b1800117408548a035040900180e011000601044c140f0100e03003003803504500702d04000c1c64103100c106110480c5c0e4003816004880045800c00440c10001c0b9814050001101e802c0301c10041c80c0320441002880072000707031003031751520049414000201500c5d0081c2001a09590041010f8240400040701d401011a018a40300300011114001c030b414058042200841f8406 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 195413741 1250 195412491 195412507
    0x2210f03130b04050a0c080102040e0c0d0603080a0201050703061d0604050601020c150d140f041106070b0c070512040b0a03150b0714010c140d0c0e04060f05041808 72
    0x40240c100a020200c0d22111014203408035a2050003144140e2181e40103007401012460325400502c200d034020110760703005000c04d1205d010710540703e591092001d01941c0d107503104c0000c02c5000d000d0651028040b6103002813400807003581900b00902c10400b80c0c805102e401e65407941034042e0403a200d001c06000640398041102e0b40341c6908041d4101c44148115034880200400180740c0c0c0503031501c82d81200c8000075400b075080c401c900484507240013282803150280b52082c44468550390040009280c0454034112080d07550b1810306030740343c1c180c103c075881c1054074004103044403640c001e00c4151014031034144001c0144050318222401c0da0091b02040c0e007040a1b02c0c42c20381c003414800031040080a002c42010a1602c01c01002c2e00e1050700482d964644240e035a00d125007101e00594040c0200102241c0154010001c201220403540381c45100180401000c84102c80420903c0201d036401400c0c01303000100030401141d400c00b130701c400f00d800f0404d00d6410340100c403001d05e10041c014101001404200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 195414991 1250 195413741 195413767
    0xe010f03150b0301090b0f0406060206011a07080d0203010929040e0307020603090618070510080a1409010c09060512060609150f0d061409271204060221 67
    0x5240001200d41580c04240c82c1c40024032281c009030000e180481c0c2e182410040c52921840b1204141d80684081100c10f052540094403520140601c42c00c000e0b00303032800b250020f159411a09010340fc142100e03100c030328207100d040180d8420302c41c01c44074a00b07040c01e2902c0ca01081064200aa800031581c054000041c811704c0702508220781050402e0105214900260312100025841680c044000e403242c2d24001c800007403481c50407814160644d1202c1001d211175101c140402203008600e08198200c0c0e44da0500000203014ad01c0c092016030030240e0244031064105400c2440041c1242d181d0640f0f1a44401007164140108081c06104601b4900400e0541c240100103003032010b030181039410381d603142103240005688590070075003588100103044000b842e4548240c02c09064400140031410050000043c1710b50005448034200707212807035030400c03801d10707404101a035031241d5019a594130071800d00994454200d81302e1080540140b604500401c074120002180c8001d151117454200a008c07034883c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 195416241 1250 195414991 195415001
    0x20108090f100f0212040605070816050d110405100e0102060c0c280804030c1d04020609011d0a090906060603020c0709020c1e0a050c03010203060a050409050a0209160f0e010f03 78
    0x140100135801c010000d010b2010180a0b131269000755000300e01801c1810004000010090544a0f614011026000040d82c410201e50303011004180201e440814041a4680c91117070380e1000d41d010402c502c1100c40150042d95a06c0b40a4090702610082c8c1d407070118080240c411000703081a107811042680da04850780200003500c042e502103400c800700c003840d030fa485865403007500166820703000310104014810303900b0f055606034444041d10950904240d804190a4041c507100207041c0034401001d01500c080b03420500c4120b500c020015900207590b0b030038420081595a000f40c0340107051074404154140a40201c85010341e0341001003c1462410f1641d20007504000d8102d03480d8003c150a440302088140d504004084c04c000280201c0440c0e40341c01441d08219211007400780e4018020022550b803846c00c18402c071181920045502011072500908040b255000290310202c020140f200c0071009581100c1c100c1c10399110b4602046402c1000c0c1e5942400f0081c2500207485107103410f10061098101d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 195417491 1250 195416241 195416261
    0x120b09060f0613080d05030a0f0b09070c15020f0904180203030a0c03110102030a060603053711071b060804050715030905010c020d090905060303070f02010c14060103020108090f10 79
    0x1003100c050716104028140003007400d201700018004000c3c07184010580c4610a106d9038401c008000c4221400b0112b00041d000422010610844580c11030900190010305441d84661620855440ca0f15030f070460701a402c8005128001c514201c40403240c84414039901602940041c010341c24000c2d00700b01220001e00c8a5001c0f02044100960641e400e04240040c41c0128013001020800d2803c082005044075402406100c00a42d0801000e10380201c040c03515034560304005841d03109190198000c4003070080d40c0402045600001881e00c00c0c0201510392505095400c000018490b603124803c840d41c080c02d0f60080e04c0d54001e003404111040c0c9000da01e1071081d99500b00030540c06441c3c1c0ba0103003103c590201c60300c05a0090074600a0b03642c6d010468001030014001c04025a081038004241c0c1ca0044078001440c01b02003050110075680600c0c0c10750309080d400038103070545c206202042500c07200c00b844100e001c9640c140210724454404900c42e4035a261600082403801c080e08140030240080340700c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 195418741 1250 195417491 195417517
    0xb07080d060803070b15010f11011104030609021908060606030a0e06071205070c050705060c010207020d05010b150c03181f03020309120408060f041b06120b09060f06 73
    0xc02680d11140d01038280189400005141c80720000e0800c40b41004d80204419100740b02d02c0b00c1c007034080e81c002817404001222442d045417441e6003504103038011b03e488800141c0000012600204000d582c1c0c001c0d03140c0d0381c42036030003010612210b864603800d00c0b203900a036006900150000348190a0100242d540040ba9079400315030003200c1612141002e506884520000300c54840d190100c6641e4050a50800030030300e00010144410b40b100c03600e80c0341b030f402018490304002075000d000b60003d40683d24000d40040202580c00e85c1d520740f0314000d0202044039401201d02e403980003a40b009540507030302d4401410001d1813429596510301c082c56001c100440754440042c1d54102850350840c030041e00c00e40104d4400503560b0900d13800c440c3c5099085096510442410401404007110104089803c01c801120382003441d2150b1a041001301514152485120f02d0450009070041d44060b2000c1c0c100e03000c2c2020484000c001701402980070301200c03219006a03419480003094100380004013074400100f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 195419991 1250 195418741 195418747
    0x150807110102090a080d1d060901030f020919060201060608060d060f2702011707200a0f030504030201080f010e060f041d01060f0602070e1503030d0f0c1205100b0708 73
    0x2100240103208607030440c10305070384104078949900b1f4001d402d110902c8503034100386c840070b80302000182c0b49200d5007528504158892040b0b140b400d41c0c58054841c1648020300701030010b00009841c2c01c1e151050300c03481c001076090074400510300d40699100c900451002d49803529190701a1525000380c0101290448035982d41ca403840e04144102c00c0300310b90072209118040c41000b0500004010b850144031520b01803034004103201035950416101901105c245442d0058140b01c0c4071107a0038080b01c91009414004024040401c0540c0b0400410903240300f601c0743c4402d622011461100d110b024000c0d02c03854030780040460004e141c45040404c1d44000100042080d0107150f14a4040080341c00349400181c1d15014240005080030030008082c018034401080103e1601205991010019000042818104120010945042c8100d54101f081c0002c00d03c40070072120820402828083c1c050000070380c0d041c0310341c64007104030b0041501440b52140c018040d1030030440100b1050f40b0040040740ca1000070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 195421241 1250 195419991 195420007
    0x120b06090d03050319050126070e0f0117010b01020c010e04150b04050906010c05030d0b0d0b091f14060f0103020915090f121b03070807080c0a150807110102 69
    0x14241d500c01aa200c0c0c2d0342e03140c03203040c02100e01c40d08031080c22070300d80d8617030802d00144500c9485003949400c5240c00000400400004101c05081012a0b04000c1031417118000304450200c628949904a46426824011075112039402c175003280c6541c03615500581010412a00030340c41445031805620009000244150605003640843d074440d0303001050024022404021901d0404821030348880d00b030920140c0240303075907103140d107900c0b45000c0d0304000c46d55043d90007c1c0c3d44510581049495210101920394201240c030242e56400e0400005542d0b07074107407461030031042240103103440140c601103880c50399216101007144031484007a41074100b681c20304c07556046a440644000c1c0d24034103c1e0b00141d541c91072a05002004011030b420030300815000300c07540343e02c05d00041d920899095420204000074084400603041180b0366100d0f41903881780980c04103100b50040345410481c581100c000d1007083d1740d44e0a00c0708900383c280c8110003090101c07001925850003614030305014480503000500c4d00c0b4003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 195422491 1250 195421241 195421249
    0x30c0b060616050610050a030323041203020f06150603040609050c09040308160207060c0611072f040b090402010309050c040c021b0d120809030c16090e07030203070b0d06081203061e01120b0609 85
    0x2c44ccca01900168400240ca0981160a11081e0382007080318595028641100700815200c2c030010b07000901c01595000158240002403144c0300f0348082c02061941d00b82014140145060016220282c220303924861425516000154000c201c900949400d60b415016894140c000e0901ca50344801c1e0142c10403004000500c1018412414003171a8184410a9071441d108001d104146038018001ca103810a80500f65031400c0081d07500560902e0040342145130b610f8294101110b01d000340360014104a0f459401c80d8020807034200c1d24080a01c0c4400080350328007007007000f00c60b802001c0c101c10610164180e525200e01481680729a000301140c0c40d011070440b00303526180c900c0100561034103095109001c040c1542c041c020003114018020404541582c00207174442138039100704224060005680301c0c0d651066000380340180340c400160381c80401403c094a0503030340100c50b0140b040300c0e01160001c0f516100c02100480392810303501c50003801010b00c40c1d08018801000144d500c54001d108494090362 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 195423741 1250 195422491 195422519
    0x10509030f1006030309140a0e0a020702090103060b040b06090a030314070b071d03031c020a0306050a0e0603190506060f042405011b030c0b060616050610050a03032304 74
    0x5100010420304d5030800602402d900c0d00b100d4011551803803615801c1e90f0340c0700c101007655000124840982ca0300b0803140002e1050704402500103c1003c000002e02040b544001580c00b02a1814003210306003104001141c441e61303010980c4404c4940003480401d10070180a4004ca4a00080c03919020640d10340b0280b4202c00c96000c1c00051820a08401e00c0502101140c07040c3c10980c02141001c00d0702c0c0c0a0803200400b0b908a880c0d565010a020342e00d24441d4005c807000700380140428a40c19250203040200c0030040740d03518028418002e00f030000a0041c13501d0b0080e160401c002d40340d03588500c0108005c0c2549042081ea120380c480104c0d644243c0301709100420110120104054207240a002501c014540b002e2200000c0c0d11100d03076000302c5c0e04007034070881072544052032215a684007800142e13031f4041c034029195080c0c0442058010014009840303406500407540c54400e4640e11b408220b0059424040280000c000c5944d0719044580b80e06142500441090400e0a140d1a80c0f404030740c41c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 195424991 1250 195423741 195423763
    0x4020312030a0b03070b0715150909050106030203011416050d230403110304060e130f0207050312010f060504090902031024151b08070602030c0c0c030c0906010509030f 74
    0x5561a07403d03206601e401c000c40c5009201001c045828212581c503240d440c0c4000044082c4410303190110100882d02e14102207000c0c008080d01040200c0140c00c2c03aa00071f02c02400203d002e03600c0d24a5100740020b0681000d8403580160b0042503c07100e5801040314190003109c1c0b80943c007901e030003d40c004000156820092000d212000003003515040c07d00030410000c2c0c018500581e042001305100c0c0d154010b5142c0c000b02c00640b00030a840c12100c2ca00ea004051140000c0d088130320120b24201040700210081c07882400f8641c10f01401c1e43ca80344541d12281c0c0510500012500030002000080303415001480400c3c0024140c80700203018110400a94070049071034208034030b03010702c03200050741600c4013100502140c81250090b00c42d2104042c3c100c00c0740301401c1131104040c1040c03404110709076040350101e5a0004040d500d9050008518000780c21580c200e00003170007913204058441c00c00084e0381c2d9049100818a50082c4c540710010344181d03000361001c0c0c0e05130003020310403201e51508001c020116 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 195426241 1250 195424991 195425011
    0x4031502040b0d02180910060e06070605011512110d05060d0b04030207151b0201050309030c030f030412020604150e07050303070506090c010801080d18080d09050109080106031a0402031203 83
    0x40caa00c40281c14410540c0e9803514810040842840447c0030080240c030300740c81490130079100d012108400107035a400303200030040a071420600040340248280104080044641e202d03108140514010101540c080c4007801d541c04405125040c04080c1a4200a800101c080c20007000c500940c0c0f40c022130302604682c15005030303003c2d030f1040207442420f04494080c0e2400d4a401056191074400e640207401074100080d042100200201c0d04200e014800c440c0784801400480b0390782c0120741d40c5818940c1003144c0589108030b030313a80d0012034103002045051180f42d221071100c2800010165040040580c0003588050f0301c20203001080302d44040004040c0c460141006116920342080b4642c1390108580d4090704100390303030004000040d40000c04028510242c01c12014401c503880080180c4d4256038000f40303841c8500480081001d4203c41d02d5025036a00b81d9682000d02c5d01c840d0070b0383c01c2c2e6000f07100c001c01604c082c0b80324000308401030a40c1500705100030250b80025070315840c000c0a680040d6856058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 195427491 1250 195426241 195426247
    0x1b05060103020108061507020402030411060301030c14091e070e1201090c05180a0f090209070f03050c0309070b0c0c0a0605030901061211040f090b0117010506040203040804031502040b0d02 83
    0x20b40d80c1203550607900c0340e811907000d8260401e980e010100d0303000d0004024002c680101c0881d042080c60800240741d00d80181280c0c1d22580c1d03c2c01d02441c007407401e10841c0c490283d103d00c081103504186514a02c00c83d0807141000c1c440d042c4984c800c4007410300502c044100442509102c19651f226409103030084c11220020031000140d0a140300024500d6010f1413248072440442a144904071340b540c0d5002907503940015204003003010302c0c405061a0b100003035002e80d61a00700081207400002e00c49118400365000c10050342e901e400252684402c1c0c403401100c1d84103400800074400128000c181e48006c01c0c0550b2816900e83d40401c501c0180c1d5003101003c100e011003001170391034003441408000c00704001003003004c01d0141c49100001300c1052006001d07503181c1800451221440e000100d8099008405241c11340e07403121100380c401d100c20160021035080a0200d6080c3c0b5060090300e001e540c02c0800d01c0d10f031078a1696815184140707a01012a01d0b03030203010014401040304007034032408d0311030350015a07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 195428741 1250 195427491 195427493
    0xc0503031c05130b07180509041a1509010519030606080105070f02070501171e04140c0f060313050709050108070f05031504080c07030b0c0a080105030d0c11011b05060103 75
    0xc1da44020040e039058211501104040313000141040c0d081156414030f66103006088000442022040d008131344c03c007e07110b00f40020021428070410b000c1c41103078200e140300e031a8a00004080603400180315403000b080d078018000d030b1400b172140181c86103800440003603859403681c0d182c0580e4241c1d404144141d55440421440b642c001030b29200d0030726103201412029040000103400c0110200380601c0380d810303a40008002031080140c0008904d00d42075101d81600e41480e0030300b5400300c02821682c1d1070140c205102c001d41820744000740c0c0420000c0c45a41035644110000c0461a00248280da291241c2c1500103156085840ba0b50701800c1c4081c0507108240c10510301c00c42c9a00d0760b42c0620b00035070040366103201a042540103250020707480540b985d9958266249613280925940000d00120008014041c0c10300d007041c01802d03d00c3d0162540781e21a070384d440406440d020b0801d50900410a0207140f5000510840d80c8030050b1070b0141008401c03c4039001604050400c8440102d0300369000c1c0340144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 195429991 1250 195428741 195428797
    0xc0c110909012306120607050301090c030f020c0c0a05060708031b040e0106020a170a05091509060a050405040b121506031617150106050d0b131103041709010e0d0c050303 75
    0x8140f40f480d1710300815441c1426040100130340300c140318009a8590b2640058000b920030742000004180c4017000f035444030344c0380000a868280d91503040303104144c2510001658208070060b6a0a0b50f0007030603290031076994445400f005080700f02d020342c0a560410000c6000607410321801d001e0601c81e0b009000c80710281c60425884a408400e0304000c0b0030030301080e62015489404c075100920700b9a00c0c1e40c003042c10403546402a0044510040d80501c010400b020f51941c4140a03108039030b0225001e10800d0140c0080c0707c8050305103544030501790041240c1d1000c410903000841d8100501030211520203020448409405002d40c0250300200c8501c5000b06243d442000310040c44030840d00d505459514145024106205001604000d10740340d04040b00320b6960030305010800e1010390b2052140c9007110304000f07001c0d442118112503501c25009100180f46d6001d06844160006031070707604da1041d00ca02000850400303100c044030070007900000400c0907141031010301404224440e480c803190607558504 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 195431241 1250 195429991 195430009
    0x20112060515270904030c02040f05091609110703050f0f03010909050606030105010b310303090510030902061209010b03160812130311190f090c0c110909012306 71
    0x303e42d0385518040044080d03520301403c190019490308000000301c545102040c05004076a000c045120329120400031211808606426100f20031000c0303029064582804000320790707130145d0b800d18405c42400f2240009028400900759034840000316420301c4060281d02801c2c0d030007600020180c0f40c403502d68400700017040241d20b4000c101100280910f6042464418883c0038059080c442543e0b40241850404035406409600e9500606103100458881c100a00001c8540c480c441c0500f40007400d072680980700b40f0400013a2940100f9081c50450840c412942c28035010380241010755130b07000555441d0780c0810504440000c2d80c4001d56266160400d50f90802c0703400c140c0c0c411a000108031508a8031601d00c3d002055130341c8002c80d030400f490184003003001c0e80f032041c10704e1045034101500484c0d101d085a40d440d045824000082c0060340002c841100c01d0a0182e00c02455069000c941c06010710b42010760310b41c840505000091170700700f140c0d034860007030b100300c03101c0c0902602020134015a802c2030001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 195432491 1250 195431241 195431287
    0x20414040516141b010504080909090714221409010b0a030812070314010303020703120905030c040f02091c140105041a07120905010c0e0f01050403020112060515 71
    0x1a000d01d0310354400b8041c06030461245950341020b00001c00143c24040c0c060626014000b01c402003007586401e241042041e441001014030891000c00098a001340010b507020544e40c403008401c0ca0109641d042c800041340c80c008030003551224142c4c540701410907118200010b00241d0542c042d5080c0055054212100c1c446018065809600e040c800320300c3c02d6003140c007003400c1c41003845a60341d10349404800030014011100c0d01040700c1d400000034107600003280001e80340110b44052410740b407280c00303803004200381c414250582c00680003c4510b14181d442044400303086600136262056120000b01c000162560018403542c062007e4024400604682662100020001c01544c2003d440720184c4180301140405c0c41003100d0000741c1c0e00c40c49601d504c4501c88540d00248505111458664081c1c4140544034000950608030500145402c1c00300c03006510060311031910702030440c0c00444100360002113000070b56440c0c440c0010349032204104c00c246984e00141e070a44844076500c9206032074007a003030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 195433741 1250 195432491 195432511
    0x10905060921031b061005090f01030206030a110d0e0105060603010f1509050306070c02010825051608040305060601080c0f0a121407031e15140111010204140405 71
    0x800e250158a036502d001040384086040e82400307500000401c0c1c40d51240551070300910b41c88900c900303c1d4010015a180c0139050305010703d113005803180144411180200d8032000c080441000410160411034025a00654032a20202e4817a500c02211801944100001d400c15960740751441c20842d42803040d20782002e0100d070014550751402492000c013107054080c441030140020f081d04066070040c0c84400080c03c014095600910342014042c0503401500e03001d901186111000415001074024074180c01c551440c003000c1c1ca900c907100300312425003001132140080c040c00306a100208041300c003e08000c500c038100400c16490040001000104050960103440c0c1043c04501100c00f210010349581c05250701d080b0150030300070f224072005007107150f0210031074408100910070110ba05402c0f040ca0555088003a60081d420022001b00700d072080c410b601040030618400f8401007421004106003100140740c03030b0240400c903295032800c80c3d02550100c41285040b401d24812070600c1d019990703201603199 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 195434991 1250 195433741 195433747
    0x100518190c0504091814010e1506010e0d0b01080c03030f0706051e090c090612060f070507080a020114130317040303060f090b041b090608040201140a0e01090506 71
    0x120260300e100c00c8261120240d103445001e004141d41c030403010b4500505410505002c610303034906802c55503c00e4244150340c0d054052092081440781400341440c0300f24900c00421240c40c1512400400c1200030f011103040242c00600b03600a65100860680c06901400545042d940340540b042d103003140c402d45650080d0424170601d081484000c0942e8a465042a804130b0150348400286003000c102c074074030540c949400401e2103003c10b400611801c90600640c1c2107489900c2e0003007000204298144c441c40340354003140001d0400800000385540001903802c0050500259a441d60584e070030086500006079540e13000f0b100f0005d03a4003401504040000c807020401c52246d14014050b441c2e00b41440d03000841080460201881380d03015200074000030010105079600d41c0e4000e0060a100451140b0660030000c0140d10214100d50481e480c0c2c0c8075845580d40c091400c002580c6070f1100901c00d030b051003400443c0b050030300030040c010098052184d8032900d444a000002600c1e0081c0c9400c0103000d41028 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 195436241 1250 195434991 195435001
    0x3060306091609050403030b0a0611060c04050d23030304050f060c031b09120f0c0108010f0503150c120106030b1903032a08040602071a1801030c020a020306100518 72
    0x20341e404000f0f580c0050004200c3ea9218102600600407035100d440e000700d92036800041d42540018042401c88090094981c240c81c1c030312558090740070b00c2c01082d520039081200140005c0203c40c0302e0000b8269401d610104904c210074450858100b04c0b03080e1125000004c1086041c20180015035021b00340200700c40c11400c0c00c6030380800109480146e040310000020700d2002541d5115401e84510b202101126030801070350710f402c0c2d00c80b006c0f02c6040d40852040000843c1151940c0c0760001a110046c009240074403440001c1902c96030040c007040385071041044400240407001945901802c3c6580b00070401d0340750081032200d07441c07408858221045000f0300a00000750700c0783c0c840103c04075902e40010741c58405050401d4004210030014080080010005a441d801141c032108407280e108600c804100701070b80024442c0306090818400d64007071400c00d030071507010364001c0711412260b10407141c0c1101e00d5030110f45410002d42c0d80c01c0c50003003500c0c002c0199241c1000011103502c0343c038012550a041c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 195437491 1250 195436241 195436273
    0x12160509091f080d020c0603011508041b0e010e150d1b0909050d02010506100c170c100b030c030114060906180703020c070605040501020307030e03210306030609 71
    0x1036030303844500c60010400400c000440ca03a6154040c21503852403500350581d201541950350510504c450058010500381101d540790000640b8125a4031021401311a80301120803503082800901c1100d00207001c201c20501c5a8032004181c01411140902c4012035041c040c000b020560300030112103101210707c26068017074643c038800130241a44090342104c3c5c45c0864190b000451281d03081003441e1480e05800c6410720200280646466103150002c10254a482d0144000c2451943c0d00e180400ca000f203a440015141100f01c8011030b403018006801c0c08084803145060480300d10880031250717140d00104106240a1100c05807030030382180208061018135a0800c40028014661407046519100052954070744401c50381d0000700e00101c60707141d0314000e10301034004e41100e10510307618801c0c031402259082c00365040b2426224140c0085050020f00ea070100d400c08030b030309116905805049109180c0c48006000140d01101410070191213240c00803c1c50328202004001d04102e51000f0341820031114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 195438741 1250 195437491 195437497
    0x120f2105120c0c030d05011a0703050f0c030403060c0206070e040216030c0203010b03010203040c2904090507020715051c020f03041b030b040c0503150603030922020a05121605 77
    0xc40015229050303803694582c00c001d0050f81c100602600002441c0300725401c8a5100768103030360015044080519481e1907600c614041c0c110f00901090003041030000204181000c1e0140b2010f020441c0d18050f1207940d100d00f40d811510038400564031403c10700c0343c2c1c5904a20f01e0014564203441c2181890802c1c040c00c2d800000781d0801030188a0352084007004d54a0030341015005002c054002d55490405140a6074540e9041c1b16600042d281c008502013000d000b50300300c5113039030742292280b801c15007894021802810007034074030f10070351144040c0042d0440c40d80040302c40a06441e02c9680d114100054821088045080c0a5803071510400580a0500280c0c2c2900d800507003110f9070551074560304030140324040040d0000b41002c50b10600700800c1040c50312024098400075000e441184050140b41c101c00701d0b00f59401c0303034150420312200907107040c1802c1030810340300c00c20038050b4044180202c08c81241d02c0f01c08402d00051000516a4560160b40b6402d90404c084c55490f6070901003a600c01041d81c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 195439991 1250 195438741 195438757
    0x180a1203030b0f100e1512070f14040522090311070b04050603010e13060905010524010e0907031d06040507050d050a20090906060f0102071419120f2105 67
    0x400f04000d115146d0f210314151050b00f00c4082c13a1155158084146411280400c840000008070001d040c08072041c403500081d02070401451640d420a4104000c200c0b03010b07580364110310001070304406215208001c0c00384182c400d0007501e039403601400850390b09040c00340e10f420001e41000100010041c1303854003003c49045800d2404421466101c0981c8007101c80c1c407a070406441242414680c8040c8101035200034050320b2031800b101701803501c48040c107024041c1e503010180425098200b0f0102800c0c0340b9802e0b6030040c01440c1c001110080c0808068009030030101110841d4403072404c00c07007004404c0000b08090101241d444040d00926500c031580c0b005c1700b000080c0144045480403081c2503c00e050241d0405005003011514903000440554440045541c1d5101d440c81e0a2140103650000c201c03003080c2c95400901c070042500803001d00120641d1311503888420011040d0001c0e4015440e003070b010001c0d22452880c01c41014a0400034951101c40f044000c40d0301142080400803070b00312040301c1c080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 195441241 1250 195439991 195439997
    0x50a140901020705030312150108090a120e03070f03050601080312010b0c010b09041a010e19050c0405100906020d020d0806040b011814030105090304031205180a1203030b0f10 77
    0x90403003000403814144154400c60b094440440c030105242c00b40200c00344606111203000c0d2044107800d004544400040e01e0021087c6c0100c5050b00c045080c0042c550000640d40c1000001c0300360210110b0714010180d0301c882180c201c04a0b084c401c0040c1441154010048a0021811b0400344900c3c026a494188a5018494000506914074410a410071940280010a03100c250f00e03060400c040540204050641144411400412030145e115149401040242840042260300e1f4103400001c09001e401c081c0320f12014040004d5540d280190220030507110307950f8028281c50920301a00e016503640c1810299006000c20b0f409a590045c44581d01800c2110b002c50006440001611040b69020086c104401e110901013500a00368040001c500e80c146c000300240c0d82c0e030b8007a00392039000e030f40001402a400700a82e80380b200d110300094884101c070000c1d107510070686800000c691861030b51280c0c0b106a040c0d4403000074150103114100c030b0000150b0348090349032180000100d15020f40d20f0040c0c28 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 195442491 1250 195441241 195441247
    0x90b030609030405012307140606030a210e12010219020307200402130801020c0f12070f02030f0105070309061802030c040c050d090f0203010b180c0d02070812010602010c050a14 78
    0x1030600b1145000e280c007003115046c039030b4485040c1801d00c550205403900000340c0c40342c0c0c0045941303400c00045040c071440d08401c2c0040c002120303052403018420100040010440440c0d000c01315a07a803141d00c41c21103140f01c400140e0740e403c0c010090410302c64070039008096400a000a07000b1a10740204804926402e194807220f0a01d100700140081c041c0245045101c46d030004040750000056004202d0341c41401c003211004d50035100310690b00c01c00c140801e04583c0f004d20545000414400c100581c070391004040d100e061000310041421103008640c0500081e464200b140c0a0002a00c50840e86a8980000e8a0040644d0700869629210808014041c03a42c6d8a80300580c3d9100d682900c80442c46c400c000d00204119007090640403181c41c030241e10075403030301c040b41d0b00a20302941b89081481124107221007980e5018820799881e0040c0b00403031784064080203180c0005003400014a0706070002102c0200035410190000c2c2107400030207180c01809000c011180c07902d03400010002210300002109a9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 195443741 1250 195442491 195442517
    0xc03160204022703060105151801020316050318090105090402120106081f0f02090a03080f09090a14070212121015051903090c0302060d060e010b04090b03060903040501 74
    0x81c411041881c02190307070f0344100951180540005010340e802103044400c641d8803581040308a00d48041041000c130b80800060132051110038002c1d000d1901401030380d060008901800011245003102200d031a00b0010360707403804254030400107020120588083c205581450b001c2102104e000d8406482081040810b40c0c50325025044080603044c0402a591011340b46480700032103003440b0401c0000710b4144051001c15a009100359110180d0047c000007040c0d00d03588840d000d07a070100b0600c100003807040140e58066150081042d0044450041c000352500302910110f44807440a010316085400c18906c6d071206401402c192081e060794450000015240c030f12144c1c41d00c40030f41e400100508441c510071002c094100d0090004800814590041409039910407022110540402400401c3d8140b003407001d414194050702920a0344078001a043d030b02c440751502c200300240e010840c150000075050282c0d513180c0c01540c60000090780181124100030392100e4032030055015481c100321101c1c110b20703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 195444991 1250 195443741 195443749
    0x8031308041202040b060a1407060204150503040201110d020d180f0815090d08070804050c12030d060506040b090d020303040312050a1403070c0803070e120616050c031602 75
    0x44406984000034a80e00d03561074040e00d580050122050748124541403480c40c00307041020450f080901196180c0c004e1100080d10b802003604040c40c2501c459a0034800070038842225000301e860455941c450b01c0e200d2500703100041c40301c40d44004c1d800d8103801c82d0309807003c41c030303000680240300c0700b41401d05100c1c6100707100c0003011a0302c2d1503001e03d00e0845078000010318404040b40024070611000006180c0350707034a069150351151715800b64400110300d280010b0140e03119042e00741c0c002d4422820f607210300027000b000030750074442c03045104d66a400000303440c0f0401c400c9204d950300400781a20310606141c43c1c6101d0031035900a002600e4001c9411803844011550140210707000f441c2c0c00201e01d0700030b00c1d03500700041103174002e0f0000030b01040e0290003a2020f02e1211040d0303482808030356504101c1000740c0d80d40c44030907000581100217200b44c8100c1d01c03503903680b41601f08140484090040003070f417422000440aa82891408105021381044406010300010049941000002d43c5086190f00548042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 195446241 1250 195444991 195445021
    0x50c09070c020d0b01140307030302030a03020304140d1107090b0d1e0512030a050109050c03070c0606080d020a050105060d0c150207090f0b010f02010b030c12070806010b0a031a0d0803 81
    0x398070403440107102003000309403001319041c2c0f00d40d9601c1500811000c8180340e55072155000140241e0300a002c4043c145119400543e48644541d45026200f0030560200f4030740108811a00d01042c266544002e04c22005c0080740001c141441081c45501c0b80000410018455414040c4c400380350710718000703282180316548001e000d6016080781d10f090f1160711180c040b034005807110080e40d82060000503a20740a4021240a081d41c1140b041c91030301d50701410346852074884001c03641c4544422001908030004d00001061046c0c9802400e400c1209160541c2182c0d802013100f4816140e0416100101d107070700c2c0300c0e40705a0340400c400b0f034039a8590f80000d0749854601d5008190b40b90a00a00c80482c2c030060700f000403402021380351681c6c040391401d010783c203030f6544400540d05075010020300c0d8454500f2000040382d003088541602c82858840a0460411400b604503401ba402d0000c0caa40c00c9642c180320380041429003803c0e442c58402000c1c00681d04421500014100b10004004101001c0440c080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 195447491 1250 195446241 195446243
    0xb0a0305010f050610091715101a12060909010b090a1d071d100915031e03230706090602070218040503040b0a030b0a090509071e030305160605040303090210020307050c09070c 77
    0x80c034003051909c0c0e0120381d45207886014100314008245007060110082c20151010100b00020b03000e00341e9180d0301800b000d44001401d4016030341d2200301c80809070700c1d40c00f28980210180e650102d81f508500c074402112030300380f002006199201180c100300c441c000701805510421b000040915903101c2550210800540d0b0304104401072030701d40e0850300d075811200008102da20a5101c01a01d209d01c910030300352461940000f4001c20001d402e098615042810707078074411950750155500b01800d9480b140d04907140c0030800c80e0440c1c1d0014094081d440c1c03d05500004450844072030000d49055954a6220b00441c13152070030b030100100700748a0301c500a03081082d40c3d00000c5c1c2003910a41d80c900c0c402010300350984040030f503401103000c007003100405883c008507110303640040c400103c0e01c2c684e02141c2540c001920184d4411024180000140280c020580a00c1c040d03a404a00c0400c24010003004030210900141950300800c103074800505c002c01c0d160b0040b60100c81e8460b0780d44c3c4140040d00d004425403c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 195448741 1250 195447491 195447523
    0x4080d03091b060e04060b0901020601090f0608061306061505070209070c0203030328020705031905090a030609020315040b060d24141e0c09040b0a0305010f0506100917 74
    0x680410b0341513100c1500038100b03100716002c2c00b0071681c0e48890441445041042801030b041140144000180354010004424000c0740c0090803555503d0720b01c0c100007042c7c88200c0000035207008074081c0090760103200c0c003828201c5c0032501002c08165003e4018818460024000d021500000d1074440c02a82083d001c1900170301a2545e03480c000e00c019080c804c101050100c41c040d6190040d00c0e40e41c40f842a00c040940c4800207615003d590030140c00d0459040c101c0c10100304017000003101640710402c0d40c070029031003000d021504008030710406041038061140b44a4450b00081004045202800c030240c0103401038690120101550801d00760025202d4550280380c801e09001c00d5001000fa840440014040e00c8040215241c03241d0903032541405102d00380e411502100480c80b141849001003a07000001080060b0710015070700450885000c8d41d2098403a039554000d2149a18454041e8a61001c401c461201c001e110000c80070b4004280c5000d28215031002000c4400060010800d02089001d07041c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 195449991 1250 195448741 195448793
    0x60207171c020d09060e03151009090312060608071e0201060801020f0a08060a0308031f09110301260d05090612010e1608070203030f0403021009151104080d0309 71
    0x10000ba558103d181c040800082445030000f070250711614200542050040c094480b07541d105851030182c10014040c001c5050300e0020000364120715100f003105441c4a40c8400d40004005a40081100c0740c540c07254092019100801c8000c9502014410451030b250394145e0191011300f04c224014185038200a0340e07580b002801d8206640c0d031201810000e602a90f8000c042c3c0d680d0b806203d46640d03144801404640b050022070010300f411461703400146220055506825507403600402a95a07000740e285000c2e000000511051242e04100d0209101d0000381340a60b501c0c2044250b035a00c0f5481c0080100315001c039489075550f44540407610900c010a03078805088d61030f0303040d01c4c060050541d00401c0d04420002c00c0104030340a02d0359980329071160f8000e5425541c49034000c441e5444002e00480031400b440545181881c0f072485900d94640c019844c3c0072542c607024100c001214003a460100c10400140404c215941c0002146074001025141c00310f0321540c54070700400e20f402001004a2043c11710 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 195451241 1250 195449991 195450043
    0x110a0803060f0312070b04020d1209030b0a05090d030b0a0f0807050102011d060714070f060e07060201090c1401031107150507090806151f2706020717 66
    0x25005107004620803260b2a1200300e004040580e1658051a0181604004c0c0030b03490101c0c040442081c1c0c45800900351600c514025511000c5404040c0a444082030140704c2c10300034020a1900a940f01c0e03041d29003000282000c0250300d5a62540a00f1300c0b0815444040b40149074444e14080c1c00104a0050329a18107521070309090303282e4041b0b003e000d0040d80ba03d8081e034038400b0000006042c11030114094121915031500845948075038807800d00a226042003100000b600d241f400f444c41c940183d0001074407102d0341080c103040c150b160740070302c08581c1401c010b0004030f15690010021100301ba01e1200415800070016000351001c0c3d1291104003070049501e038141724000803183c1218051003030401ca2a030340d001082d5181c10040c00b4449040e0b1064001406440c20a5a490b214280081444240304200e190b10613404010041c0c02c000105540342e10342d190003c0c0d07007030352084135602d004c2146024101503000755141c4844c0324021304510003140d0060881c0741031103218484400340d034840440003a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 195452491 1250 195451241 195451253
    0x90510050712020c060f0d02040e1501140c1b0d120f030c0c0b011512050106110c121f0b060d2405030d0c050c040c021f06060509040c110a 61
    0xc0c040c2030741c61941c41051855024808140e1900d0b0300c1c40184021b06058003816900010b410040c400341c40c4960800010075111118205184142c150300745241080e88140700050080300d050800042d449001c0c09040c6042038040352602e42d49110580125031650110000360249450f04009003401c1e00c0c06880c40c0c01550b10883c407001c5c0041d141c030140821801c05004480800444501034001c2c841d60005000d403503100d007203403140c80c14203141075120402800c445500300d1b4020307031243d40881c2d001e41101c01a04410b110000800c030301150089050661480000d4603050600d00d000e4110300d8010105000c107145078040c0f04802c4018007110341b02c051f150b9464004000003040000c4440d400e001c04094880c10b03421000a464004c2e011386600740d043c2000781c0e2244400c200c01c96480c0642480b002c1240c035a0303c5040f0014545a00414072443c0c0c3d10404101c0c0e0a0400d4858029420800c040c001c2d0358000003214100401a0790024152640e1042160340d1040b800003400c050143d64a41e0040c091 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 195453741 1250 195452491 195452497
    0x19020f060307030c090b041a071a0108061009090b0a050402150d0213050d02010e0103020a050d14040b2d040305041e1a040f03080c01140702030705010c030c020c09040309051005 78
    0x121a01c403c85c11988842920341c07507004921070714090a0380c681b400704241c1c2c1c0764800f0f886200d205009101c03c0001c81031740c1c001d964500760031452a551110081020b2401c03000f0700341c00203000c4401c08000142450316948101503000300106911501c1d580403800b15101d107084c4100712011010116102c1014601800103580640c0c1c400640100d800030108203460848140b00c03c140d4161591001c10b50500c005401030340112007a0000d1100c140300140d603403241c0d4000c0300901c0f819100c0800b4545000d180c5500ea0031000742c000b40607494000752120b0140c000d00600c0e140d10301c4c110004040740e619481e00316003902c615003005c29460224496440403070803041800040c0da99604405151014035140c03c59030303000c0c6200f0940c1d03042071907004002150301c1038000c0c869102da680021403c2c0b003036045210380d01d003415101c140061f40002982c00500901784121600d6007030382e10b0180320000c010304009540e4980c40301c180340300e4548a80410101800380c1d00c5900100030142051203103102010018003a90 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 195454991 1250 195453741 195453761
    0x726060f180a1524090b0c0c15041505030c07140109050d050307210b1906081f0608130507080d110706050304031b0c090b0f0103050919020f06030703 66
    0x6081c00c0a40644414540c80d0905460800070b042520655054540b641d0300c074107400c0d007414480000408143c04409074000c0c1f00382c04181e0010001407100b4000c6c8080c1c0302c00c00146288000c4c05000610180110307084105000380c041c46d10702e80342d40340d604800b4418410102c00074206004c0200c0c4040c10503040d00714002550180023a1803140442910550740e611003261428000b0b181420720042d843d2290b00420714400ca14600062400444030119112090005c0418a0011122007c00255901581e420f50003802e00a004203d1410100078104440da030380980e07401d104c4c141d030000f4500c1200c1800302c005290003500310380c52680d803000b22a49602950003441c0c005180941d00ca00030b0300c8000b4030f81c001c8540a940b2203185640f1500d04440b041d01e04412001122502c1030300f000403c415495820107414418000549441e02c001045607501003040c1c4d142c140f6007000200b010600000c215420f400c42c6a08201c4d0744c401451002400c89400c00e802240d0024022040c0103100d981980104128 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 195456241 1250 195454991 195455011
    0x801050601140301060f021e0c0a0f1a070206070b0a1d0601121e140d0908013b06040623040503090103110f0316080726060f18 56
    0x291a03490046034103071040406000d01c0b00c0304100402035103200d0b8072070704e4802c40d180c4140e0301c4240c0303804947c0240a90f40f205a0755280d05c51510341a40d4600300041030010200c0c50500700c103103490901c1c40e0803516510301341944001e80101c0c044007907464080846041581c0000315404920b44102c00b00000e100c404084503800d5180c000c1d103074020400141c214103982c045540b4015003401642d0b030041124800741c2c0c8416040b07100b08500b0000f80c0040184e4a00400c00e00035205500c1d00b484020203543c42940a0309880c0c1c14505040d240451904000b5046041039000f1049500181400c0c12140d428000002d4103214a400700024085643c0c80700e4040c00381d1403100301250a401d01070012469081d178018006030020000402c89601a60040c2c4440d95108030b0b6030300708000f4050008246e0011a149455880c44d40c0701400c80d01c0d48100240d5000c0c0c1030341041c540c4054560880b02707401480241d5031201240c4003003c01c0e81640c50142d4038031a0701c5c000345808844014031070284e05000040d00c40801d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 195457491 1250 195456241 195456251
    0x5070807030824180601020c030318100309030e010c050f100506040605220203041b030503070c0e19020f0c0a031101050703020313020105090f062d072402040509100801 74
    0x7011204002802c0c490714010207410a1407162036130300c080100d000c0c0400d4150711030000410841d032000d002400070101c0280c010340c9a05031540c1481940400b0a40b4101018a4a8800000a50000030a40f0002030038600000890b000d49482840c160865801c103d0501c5a40302903c000f9031907804c03142c442c810035030701407055550350410312405101e00c0c41061000c81002c01d95541c81c0b031942c0e02665100f80a00d001c00d2201c11002c0c90408616100e07042525030350400103031082400000968a00200082d28a541481c07810310190b0b28080c1c00e40c03841d031100e5600060810004c0342c40c24103980040e404401982d204030554980501203201051840029500b00000113203440d00910940e1f00c81e010401d01c0300001000e55004640c03c0d03100329900360f400398802d00c62901079200c0d400a08844040456500d00c003683c050400f0303031003215480c2c107401c04d071008001d182c00080031510480c040790b10001c12604044074091003070019000b55001140c120041904100045c0c00b0004c7c000100c0c0da800d4002c020b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 195458741 1250 195457491 195457531
    0xf1a01090608011821030912030203040209060a051f050705010c03050124020a03050306030f0604080a020c0f0315040510020c0718020a080105061606021209060f0103030f050901050708070308 84
    0x1c00d02d000740c040600080d202c030417001e413040494916082c60024914002519032840c3e51001c40314103030350500000007076003c0100300450514100c4550080b1044036040400e03490000001d00780c1d507a00d41d24410f402021501d0029003030150058910b4154000c0090091406524008008050074415091600c00300a4480c0034052117504040010715541e014040c0c43c61252001e41c1d1540c40a40a9038151054080d40a0520b2007480b400d80514410f030302d40d035540c00a000000349031211046e240380c4143c4140c1070542e5650350024400241c0b01c9400c844400503a55810820b040c031140400499020b03000003268019003401041141c10368000362580040310f071511807414202c2c0910311408000c9103a01d00103001c2d5180650142c80c40020700322108040d003003955981e00503a04014840140d60305800d090040042090121560104403030140113095031454500400f5085190703070200c280100021101c0301c0d80d1207a0b0413124119040389001c1c0d682e03030301450010700c0024200c81e2410f08070391201d080f40b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 195459991 1250 195458741 195458771
    0x203090423160801091505040219090f21020a050907020f070e1302010e04020904090807060e0c030d0507030314010608151e0f030a17030405010b011b0f1a0109060801 73
    0x20314801c102d60f445407043c1e0b081c800400010140d240141140180c00700c0e00080c1c2c5c2c2e8460005004424002030140c40c02c1c0c04640000d000e050442d0402104020007a50901030a03504a0b01401000e42c0030b455455407400600100f80b5940083c0c002c1500103811804010000380c00003011562a0500d804880c40c090761410b480d1b4400705c09441040b00c4564014050303002d9803140c0319010500c40c00034001450300345004001070850b00840d07811502118007080380030038803103184105440034000001901d03002c80c80000180e00e400070b04c00030340b060240c0030807901c003030501c207034003402001508c0d032138424a55031a01c4001c4c0c15140300701c91110040b0209069200c080c1400520540400a00c2000c1c01003c40104104100300000728007090301841000721410110b203e010f2003041d9074001c11012540e90906c1e0070102d094810050a26040c01102c149180c17840c40d51003100024260449404500d03107807245440309503003000c01c2c0005d04000406001040002c020303402041210050301c002c01070399000d00c101e8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 195461241 1250 195459991 195460021
    0x308190c030c020105281d0d0201020d180b1809100302060307260106110706050304030c12050c06100f0608040c210f110f0d02030d0e010203090423 65
    0x30300242e0076010300300040d400f50001d888880e0f007103030340e01c41d05008150764521011010b5014400041c145e110810b040c00e140000c60740724240c2660740012070302c040e80006c0d41d01c85141014030100004001c0c503034028844100c540c000341c0741000741540d5504202181840c220003540d0a1841000442e0100740414181407660044030b50180c951360442ea41c5500940e0404100b1100f204101d4245170340180510301c0101c2d8070b010f00b01984031402811414012a0700d080803541140092047c100140800710703401c61450003465074420f03007801c006094610300b01d070306001d0542da00900d27109200520134840080c405101c00d4400d240d02200d403041d51010229020003003a1405400c1c0b444420f010b1202e18100328040815484540205034040d000344c0c0c80c0c851807189014292a12144144450100e103041408042040c5049604000309201500003030b44442d50f013041c03c01400310008070080c0d541d0090040d107988080c020003c105082c004c0400c41201c0c00344602d400c4000030210005484643ca81ca82 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 195462491 1250 195461241 195461243
    0x60509041a0d030f020106090e0f0d09060905060a1101140a1109090a05090106030f03081005091e040203100f02040e070804030503180a061d0709020a020307150f060308190c 76
    0x6100782c039840c50f201955005049400c1104554850001042e610218000c44040c12044802032945c2c0e0345060040e403d01c6003040341c800c1004461320301042041d90040d445410765004a652a07910302b06008191440d881407044042c844d42071030306640e41c1c00441249e0f1071264800f600b050003410b184900002d010700c50740c01d42c0d40d405020900031036481001c90303105a50080068000254060312501c50207008c1c00500381c11800030b590082000480c440c950300c008014103058480f14024107002c0894180c00da802038418074156a010001010b5603010011041484410201006107070b02c00c1c2d200b24041d6005004034400305010341e000c030301340c68030a4504520407034155941505688580c0501341c00420490428101da204080780d83c8040b62031841581401102203100c80120707503902030914180300c4258415032800c0c2c41408410501500401190764040d4895400701c0900e000030403000040c00501c10140800c2c0c5001c0d004410040303111300401e8203000c484100102c003a8000d030111420b00cc8030310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 195463741 1250 195462491 195462499
    0x606060a0302090301090807150c0e221e090614010b2d03070302040801050f0103051b0102031b0a0b0a0e0a0f050118030e0f1905010503070203070804060509041a 71
    0x114244200d8401d9000d072030b00040080021407150281c1d10344404580140700c0654641c44064200c501440c5031344121580069641031090103c200000001d55582c00b1030f05c0005840c0000d2482e0705043c0c003540c882220840035900d0030003031044505458008102948049550600c0d01100d1020b40050042850490f0540311519242485142141c9d480058505001d0024a640380e10000440c030f840f00618851407042ea00140c0b41c52901940f2825640c0c05001c03181c03a0341c60800140042800804e0800e200801c0003c441144040071004074590701c2030b141c25620058200c241d80305240f02c08910703035009602500c0e60b59096200c1c0703201c14040368400410074601e03500c50041800011081c01415a032603009500001c0c00120004801c0c2c2c50102580c000c40c0000d00d03110010203245080c0d03c10001e1448191800380701801c9060481034005040d000d464140240880080c5206108100f00d4164031750151210751a20746d82c90000c2e18980080140d58401c50400051a00b91002d5201841030400020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 195464991 1250 195463741 195463747
    0x60806010210021204061509050106032702010804030302091804051621060c030603020d1b080c2d030a080a0e040e03030f060a12030818161502100e0c010f02060606 72
    0x40d40b4100140b03400d0301100c5a07c3d504441c0041c2c001400c0c8501c5008000f940c4000c103508040f4140541c400d241585582c0d01c01c0170070140e00b00580d91001d852036200d58141401a500c5003c1d0000511665251800071054131150341001708105020440e40c40149808818a094688607010303e8141196425a424465007082d0702101107a0541c0006005840c582800520b81780c680e000710b1a1050140b405440440c01e4194080c0500014881c6400802c021400740010710b0100b80001c11020781daa02600e160061102405641480c03001008191000101100e150074013a1515582d0f940006811501241070b8035003121903410725008000e480c00c0100c024600c0d5956842100d001420082d08894019610304804102c40c60388440c01c0c40c0c83d9000752124440c0d40b905842c80d040902c01c0c800010240d80000d00d42011241c0c2000f46401a14221580300c0d2400742900001c038505841c01c00200324640c100014501c0c1598080341d144900b000a989071740040036040c000740c2e03440005403400340d0080010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 195466241 1250 195464991 195464993
    0x11b140d0203040c0504060909030206090c0a26010c0914060405130e011e14060f0a0303110a1a1806040308011502030904060807061209030206010b091306060806010210021204 77
    0x7640259842440b40c0528445261945c000c181141c40603000f072100c843da141011001d25404000d40360780889401d004005201d485008130792508641c3c4509580a803843c03a90480245480b4026501460914002c121a40b01108010312000c020b12445088907510701e8403e0550402d00101c0e000c0da14082c1844105e0324007526040d00402d01c842006c940303556500740501340b2103c410240080350b0241003000c10b00349503105481506800c094145841022038a4691503584c8420106408494041c10a00303401c0000b182081d09084514800400309050b045d00c001c074034542000c1d00c9020707401c030694000c9940d81002006907626030903500980807682030001000410129880255404070700e04c190f9040001d80000315003178540030303004168240c02054060144c160f200b5400000f10071042e1040c820031100303440194035a0410f01681c2d031409400981d40c02e8948984100d214542e80c0035008204140d075070030005245000039121540140160000a6521812030080c0c8644c080c00c207142e80040d40711 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 195467491 1250 195466241 195466267
    0x90303030708042109091107120c03091a030a050c0c07091d06010e090115060c02040903050f030a1d03120c1b06150a15020d080a0b0a0602011b14 64
    0x100700312658183c2c6001d40c20380040760f103065113000d407a94981c0c0c0c0701c082c100441c42d415240d030b440c1e6060700c0344d006200d880c0103d44240c0c44040d041c011070070040e04988203400c0840d000c070495005100c0108116142459070002100214403895400704208082d40394031800b03080500c81c2c2d1507191505c2e4421030301072082c00f590354010741e013040c101840b00740d80e642ca0500362410520242d00241070b0b21124420403a5519003030003210651900343e00060415400c000d405000c500c09c030400030b4061a0340740d0100c0e04040c080c5044560303402810701d000e51680fa01984100160010541e0f2101188521044080101000080e00c0111013074595015460741da00078101000d4000343c4900e0340c2421840d4000c2008102404050701441103030750821034021700c4800380075482c1e0140e444941846c40061610648684c0442c0390302401c1140d140600060311004146405090365804e8264419400b40001a80d940c056004000003004c0f250900c04031200c1110030382c0c014021001c106099031003004254100d0344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 195468741 1250 195467491 195467507
    0x402040f0b0d080301090506010e0108070305060105070804030b0907060306051503060301020d14041e080d0c0903050d0e0109140612070908010903170a1e180203060a0b0a08030903030307 82
    0x20303103a000050050354100003a0a20102000c01c2d6400280000140030010752801400e521032400c4c201004114a030ad40020562400100100201595040440c0103a84910210b40d14035410641e00d640392603c90524400c4a241034900e20700300c0c0300f1000c00080e458081d000b0780d4111000200005825079002c00314030f2035588024004c2c1c1c1c2c1950f0030880d0072010040c0e8031400e0316828104006180610381460030340450307144900100c035003840b96401000050018005c440026000d000041100010b40400b83d400701220381005203075000324500310300382c194000c1201e8541c4400340c0c2c3da4070f00c09654004034580c1408030310740e49810140800200e43e0740b8104444180c1c00c407040b4940003150960b40d40304d09007180c2c044c02c400c0f000a900402c006107003d84541c940e5030007040d00c440c2007018000321180c04841d50b011241d841350080d250504404013460010341707035030320302e402500b9039040b07181580c51400207042d1040150b20551001d1404a000680001500c00850000c0c1c000e6180da01d685070700792b0300d003e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 195469991 1250 195468741 195468761
    0x60c081006141e040306090213180f02031005070f020c0103060b070206072a0510052a100e07081203040b01050904021201090f0501050a0e19140d0e041a09040204 71
    0x101c0c05900b41001ca0f08807100610040d0700802000418000d584100b105800e040c0e21a100e003181046084283c2280f9080c031480180e0340701650403464070041c07000c03d04210036000c001105c60b1600c0b0400c13811540003000401070500c43e50035104642640350054080300c1841c025132800c0f02052001c6001414050300030000140240500c2c1e110f020345401284000014410308504262414410040b5081041100c0b60301c84541c207017141040000350b0314024298a0f00c100c4e841d502e14044041140010a1110101d140300d068414440540340100039995103a1500c01c150461240740582d03204400e205055038003c1d50f02050054a070791a00702017041d404e070098011b90744842003202e41d6600c1c050912400006070f12480019a4000460030080d01719a0020905580203003012400c2070b04000228100089942403140e0306d21941c2030b0304140005030541d81c0c8000f041c3c400c0d0540d1038503403a00051081046103003100c2c2489039240c080b6080000045000c50650041c100750003107001840c02e83c11a403c0c207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 195471241 1250 195469991 195470017
    0x2270103080d02090a090615050c03031303030f0c090e060901180908270f040204060c0f06060e01080619020a05041401140a09080c0904050604021c05030304060c08100614 75
    0x4540c1d000e001510b000055442080e41547d210020002c542c0d016801d0700d103a514038241642415503000c03c00b501e9100082403115400301214000342014040c0e4000340c1400080707a810400d511031890054065082e5009012604c24020005401403400d0325149068817611440f184408512921450180801c0007080361900424022040c1100f00f41c0080085141c03501d170300c035442c2960f0f030043c085008010700320980034500422003849281e4006080e0b03107800703500c02020300c2c190616061100c010320312900850340183d20704000044944000800d1401b800014503000d410565404220080b48102d030303c00340100700d050008024004221210602c125010306110b01481401122001f01c3d900c040200400700e0f41109052010b0101086005070205054607880142d00742507c0d20382e6150704c0104020302c546011814000f024940e500416140c59210b02100d80301e050901e42000509983c40f130300800290040d001407048404041400111800c0781c03105c07150310001010001c1c0380c0e80290b80384413130 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 195472491 1250 195471241 195471247
    0xc0c0913021509094006050c19020a0b01050f19060f110601031a18030a02031c0b10080a0e0f030c120301030c05100e03030c0a02270103080d02 63
    0x15071a00c01400c42c80725803103001195504503800400c029824050304801c00c41001c4070311031000001c002c0b0311801c800c0d15522001c401c1202c004030b80c2c21502030600000c100e14200010301000e005203801800c3c1d408141d04ea600460410312000300d0303503006002d0300074001174420b200420080c104003d0045480e00c0252041c0a011085510075020303002660050f40042c81708001070211701d50100001c0d04c4515607070094200c070351450315500900d11380491742e071080c201e103200410709800c0448455109040c0c40801e0741c0d100e090000d07002e5282d400100103840034210071b030245c078016421849402015400142040c0240345525400c845003c8000c02c02110b40d0b0f59400004c003108400c2009000c400c3d0081300451755200e00025031400e08080445800200d04140014000030324406044001d0301c1c81541ca940b079140420300122113291080d42d42ea03805000004495100c407802165121720300340203844080c9081f81da10012001417407070100000e014022980180000751500005040701d1400c0d00300581 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 195473741 1250 195472491 195472493
    0x203070309020916080a020c030f0a02010e070e01090516211514030f010b010909020a1701030b0f01171905150c120f01030c140a0b130801050109020c0c0913 69
    0x10f00000199450850700e11031061552050b98058081680701ca05083d0660a02100c43c41c066503034000c1d03c450110303422010680c0704005200354001024007261504440090b070341c440356118a48028060f16501a04190002780070388041c010740711165002e5501c05146034280807020900302841e1113040203890b200c00441c03d01107850500b410103490120003501c0307040441e100700351400c10140210091030341401c40703c59041c0e03005101c0c4000c441e03641a02695603075035010b0446140038850740300ca1f020041100080213000d02c40550500c07070b14944e4003161b11a6221000d404501c4070440c4009441c0d40031440b15003500c505100104040c500c100211803441c9613210904440c40000c403030b03c07117020102048403120301d800d85803807541204100080396200d50568440b16040409402550320a14001e101d007560741c1c4510389150010301004400544400b92840001001d030603034802c8604030b40c207200004c071749000e0a1080301c0440382900003c150041c0c4030800e000c110600184070120404440310800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 195474991 1250 195473741 195473749
    0x4060b03010602030d0e0604020d1e06051003060b01140406050c070914093307020f1b040c0302030c0711060409230708060a031106070206070c05010e01080c0d020307030902 76
    0x5406040c4680285841e41c02204008045400120100c11191f10140600015071150ba56038005160801090b2448440c0c607e0400d40b00400420014003407490001000500003900d00c1c801d0a80f4803c013030a20018104000441c1d561070701c0318008240d5031017041704101d41405140100841824201501d01ca96a0380303012804490303001c801c1503454890a010001685024000c3e00b205140009602e1506081c500c5140200c04c0c030742c0844102015410080b0f032071540200b140350395600d5220111071341d070403c1d40c2c0c02498061150080a01072820801440e801c98000e0003942d21480520640c2400c18403542c03141c045000580c0801500706000700400301d134259450241011040128485081c83ca40c20140c1856281000b040304042004480920025a071140e4019080325000301004c10000d13503400008030742e0310440000942c00400000c7e20410080b80c0100031040365402d81764244001c500e9401940c84c010122a815103491041001d117240303492580c0956017264a40c0f0300003600c21060781c081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 195476241 1250 195474991 195474997
    0x80a020c0703150605010e060429070b041a1501120b0f10090323150619031b0807030503070312150902130b0a050d050c09030a140f15070e04060b 64
    0x2d0080c4c840400f031145507008441c0d6014500151007052801d480c00714401003020001e41c10801d001201030075100c41d075a001c400d42d40c001d9000081d40760780b402c140c900403220a0f50708000042d005500741c0003440005507100d402c1c25529040e162915480e00d68201c140003407230f4100c8444d602940d070001c020f5098581c012400401c82407515040760240c01c2d130901c5407100700134003646142d418030501070552604000c1030240300740b0030003540d000391515100b0000e00c4a8002d2103404020301101e0b6000000e0041840001c03d2602000022203261a103c000003a1078646501001d8044e83c820028000028030a082d00d034001701c0d001c2d00010300c07942c01c00138403026100305502c8008125004141c402c000e1101d00d82807401801400301c44c5151006100001d4980d000782c0d42c4000724250741d407001890050600e0304a0b9044440103080d5651110a46400b41c24242d0201000d01c1c584520031000703030b02030700004080911605440d2180000c0e91030b541c1c100c0300b41c0c0a8a000b150031503120540025113001110203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 195477491 1250 195476241 195476273
    0x40b0f091008030a0f110102040b090904170a0e040e15070503040503190905102307020d05060a0905060108030721050c010c02060106020129040506012a0b0115080a020c0703 76
    0x12011745800181c002400700c0b22150660180b40d10400c4100040e802031800ca0707840001c1660f80040c10303a05c508000c0d000a078410a5104020307000903224281a920034840803241c00c080381c04102801508549940e1084000c0103000200ea403540800c4207540500d01665003d4820822649001c0d1858480003000f1007440d4240081104154280001d203400c402c0f00f200030f4024076002c815110110340b10200c803c030480c440091010009400c2c419900d45404001120750400e00321042e07820510b140c0c82c024061402c0039070f85400350000100d030040b000701c2103034071403608040307102c0d60040a4840c0c02c0e400070750a0425000d000041010800385d100c00c5c0200c40500440743c02401c1c4640c0741c6000a402d40d4102c66481e4101da8030400c280c61400d50342a10f88100d424159000034076a610400180c448542d5417280b50482185162003481c601d002d8410980f010b8480c0c802c141c00341e6a0351031005c05481c00e0714118404146902c0020b4074a02c410750250400c0030b841c10845548540d2601c942d2003035820640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 195478741 1250 195477491 195477497
    0x80a0c1b080c010f1701060e03010902060f090f01050a0e040513120801061209020604090c0302071a0103030311030c0d0e1207060506040b120304120201091701050a0b040b0f091008030a 81
    0x414080b096030000d0711480c018040d0b040ca076410b04c210345040740440b94140100360501100b03441605650300c1c2540840103d5034044c251503901c8680180703c040d2500030581c0030744038080042e4680859403240096a0f40b50a441e110521580e0003502000043e000084c41c28082c0518800c001e404107156030010304040c0300d651520304555051010060010082c446450821814801d2010050b254802210216545110006034002d50010114041c3c030990b14090081c03c40a40481d000d00c40030703c140d904803403190310b04000d080b007a085640414001181c1c0d5140c4840c05004010140e10182c01201014001400340c441522100341d200d04107402230001558115507030343c1006454205407042f9204010121250300707401c807841103010750320320582c050704412101640601e07045901070300743c0c100603203200101c100d0000e0001e0030690081c0411a4208100385c240034004105003424070a05d0503022002d0304840c40004400144119039001606c0f4410100450200160882061000d021f50b01c4d000c0d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 195479991 1250 195478741 195478753
    0x5030d050109020a0806040501260c0d1a2805060f120703020906060c0727020f0304060f06030203060a020c0f0609010606081b03060904080d050109050121080a0c1b08 73
    0x11401080307110b00031b000c01c3c0031354940001071045e000c46003524804004a100d100084c103401c2c1c8201801e110405080d5901700f10985119820043c4001c0300000d00c42007082004070b60f540320001c41c8070381841c9031081540342c01c0110b0a6160802c00350840341d4001ca010f00b0072491f105c0f10303002090402c120140712500e41e8000010600451a1564410790030040498420341040d505d01c1c851a100c07030451081d01e142500c05504100c55500600480200c0c0d1440c000c00c540702c43c3c0c0040a001d013a4821941102c0e0765180080481c0100824400d0606070382d00a0000e003100c0e82c4e0b8a890b000254080b4400440503c281c0810810b0b4203003c00001344134a15210021454503d000030240400d41e01620b0401c0d248034440b100718140440a0580e80d002e00c04079016100d58031a41003040e03041c8609040249114102000800e2a555641140f4100d5280c0700082000303d1100c1c01c03c07560360100c0f000c000e141080c02c02644428a00c948501900703640240c640164160000a40c0001011141d0007008107400c24 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 195481241 1250 195479991 195480007
    0xf0f31090606030504050c0f150d060306050906100b0c0a0807110108010e070807200a0b07020601060309052104050d0308270c0d0501021e09120a1e05030d05010902 72
    0x1e01894008203401d003000e00840c1856521039440c0c1c03c81041d110301030b50b1400d50030083da40d0341607115441031081801159840b03880700551400f901a50205a5002d4100404980c0c0d1020001d0758911500300388000304211400d01c1880c000d01d51051035070380c015108000044022500200081c0105489802c0350802d038400340d40090407040059028400c5d007184042007001940e00090401d130f101ca1203140000811074a8400d030444540c02c04456966803080c81840020807600c80701d040e01404654080311703d181c0e41c80504074283c51040100510507085015491030010020343d40b800c0c403440400d9101d04054941000c42c17100d42d801001078000581d00003d000001c20070b0140c903140c2c006943c03281c40c800100721201580c0c0c1ca04184196009590203000f6005221081d0305982c1004005202d0440302101100301c11325542110340d0b0548a0360000031509460b1400184c3c200b080d640c17200c40c0344003001c1800c00b09403195070000401d03610350208105000c101c220721b1061074060920841c0050300e40d030301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 195482491 1250 195481241 195481259
    0x8070506030105060d05061c050c01030e122212030c030e0a0515030a140a0624081f081f0b040504081804060801050c0703080901020f0f31 61
    0x42948528011241040140800c0d156042140e0b003c80d03000c8404655600c0e9000030503040c040ca2015110180140b01040e02001070100b05c003050100260713018400503d4001e04140c070f8595072040540c03140000c00c039603214240022801c0c5040c0d0100c2044806840d40d903002500700f000d14000031800220ba03038584108054110b034a00500010a4884c411980d040c0004540c114041d8135800211a04c08000030b0703505050703500f001203207850068a9646e1410191001006170415001c0e1728050300d0009a00745800516502c140e0002c1101e031b65116084d00d80100c00c000d0150b60f03c1e4090040b10f800340001c6903600c020450f02140c1c9c0d240d0b85008079001022001c0c0000c403051808a18480d60802045c8404074189109840e00c0003143d0f003c40103a100078200240090504da800045a542804208106c3c003110102900c0c40d58004d0700d4901761980ca10b44c3c81400c0b88281040c3e5414040300380540e003550300c0138001a1040311000100181800440c012011a00207000c0780e00402140030324040c441044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 195483741 1250 195482491 195482503
    0x90a0c11030309120702030309041d0708010207081603020a060608070501030b0301020c0a031412090102030103060b0315281404050705041404080d090b0106050304020306010f06050703080c130b0408 87
    0x103524055401c5003080c0d04616100c8a0b40c03e10b0224030900400d0340c10540d603081c0115403455600400401031074016009040080c2e6988085003014080d180700092050018002c42d680300e6400200c4520704030103454101c2002600f001c0580031403144001072030000d18144035400c003410410000b8200c1a25100005096502c0c00350414003917401441250904200081c101900540c035050414201c071034802d0b0342d6080d00460001c6a0760800c5602800707000742c4190b00641c1070301d005131000c0c4924070500d401e041e6603078040c10070003484200e041c0018540e860840e040350041105401070440075100c100d07202054031031075600c00c00040a09800d01041001c01c03c019001010103075070500141403d00600c0e4221000204081c0608ac0d00040141484085070b101d443c105901400c8900a540c4500004080c0d40086404900a10620001042682c0c1144640c01100c07016a60f0302e103869003c0ea8103c4a0701e00107486585140d800b407182a0200c007000c8501c00141954886540c1c071103103010300715842c1c41c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 195484991 1250 195483741 195483767
    0xd06020c2b05040e0412140a0305090111040305060115030f051f0603051005060f04050306010b040608010915060e0a23040f0b0303031b0412140c01020d0527090a0c 72
    0x704010486407104c80e2080d0303803141c0c003c0801c0307001488240e41980c043c902ca41805400c400700080ca0b0002c203030141d2103180610004002045000c0031070b40c81901500c21800054501e80c4502c004200e4280000c030a000150070625011481d0040e400380d1005542c0d045e69070400c14090074201c840e030038501445580003003082d45003e2029042107948501c0d0940030340a518000c1da0000b6071018003001000c2118002e11010381120a19079449200140d0b80e002802010002110303800005643c6189000c2d8051482d4661014546a494060300343c8030030f00400d442d2900320111080004400000c00241c0104455130380030102580c0c4031200304400c0312203c0201300e082c2860004084400d46000017a2a40040801c021a0a070004148890310724001c1d6402005d1243c0c0c5100f040d03007080540000d585070f84420000702c507404074100006a8440d990032080300e00048081c4000c01c11641c0260000d00a02229000d40c400340b000c0c080418007c110807204c4429864450f00b480504652000c0028050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 195486241 1250 195484991 195484997
    0x90f060c120b0f1903020a06080f071409040926040924060804030207083915030604090c03111807120207060e0a11030f07060804020d06020c2b 63
    0x140e030302c000910004007002c0c0c554094180c0301d01c00b14401401207512400b0f140c0041240c4141540c2d40c1d80202100002c40d11017070603419220228003064040d1405004008070300741d440d410110780302d0502006120020042e600b00321900c950a110700d4440102400f078080951079295154140171089050782c00316200d44a40d8030304031104a03030809800c5600307019101c06140c078880c5a21141402c07854158103800480083c05000e03c0d1508400306c550007011070079404515250210440e0b01c40408041c2c00107070380d50308148000e0060441868040045038007030780080000401c11582e4943c40c080d840560400c82e070070170034101e5100c043d03e0120f5075184072404920520110389089a00140750380400088050360340d8000c0340c05030401050b9046541102611000c403410180c050502005540c80086018024000e244210115060109403201621803030f1f110f03050039442c0c13542401426154884141c07009039081c001307885a450140140c40507184484003000000038076a1a00e011040c03d40488024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 195487491 1250 195486241 195486251
    0x60801051b161109010e01060e090702061b0f0d0504020406090612030f02030d1b030f06080d180509010b0d0b03061506130506031906050d020d15090f060c12 69
    0x4592007800484414506440152211504516140072001c55204045034040303100e000119400c44000205c80c12035569940c0c8000c0d220b140000d0080545060341c0711030060f000b07040010300e102d103d080500c054440c1040e04501d41410041c00740c40750742001444c0504140c0f55010f001c1586094000c00f00504601e43c001c010041c0b40211030a01400444002414410704140d00c84542d0b0003407003a2844080c20b44018030200d10314080c4980064050a96540464548804081d5014145c8a03180035520700000030a007903a60164160b0304000c41c0c1407007000045002501052540b5103001a90003011000b581540f10901c840c83c3e001510303031000100c0d004c2d42c4101c04201000200d0760500401c0f80c42502c4507a540d08402c8414604502d0301d800c0340b900014000144000c20450030103d1201640404d002c000c10741c1c54800b04040b0020b4440081d5002c00c0e80100030b00401c0420b40340d074101c80d1483c3c4001400840726507510550345400703042581e003d0391710050030051981140c041d6900240c41c0a04000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 195488741 1250 195487491 195487531
    0x206150306070c0c0e040807030f081b09060403060e030301150311070303050a09060e030c0d020f0705040e100504030c030e040c170a021c06060e030a0308010605090a0b070606080105 80
    0x10341c40ca001040c05040003c2003000c0028452403800c10b9003e0256140500b6162034176042c42180b80d441402d0440c0000d00b0804140c454610880d059802141017088081402c108413412000d13541050300c2c280e501203010003002001a109104c0c1340940c550301c901440c1c60b076240401c034051441c11000400d0605003084096160032440c00200c419082d4941400203454651802e948000c0c00410801480c480c5090448142d003040040904240a9001d0407500c43c0350300b2090881e12a00c00c083e81640300d03440140c050003140341c281c119001c113081c907904840c2104003001e640820b5590070364042c0d01041ca0704000009040c0d010946400d05c00d000d0383d091100300c83d00c220061041010005031030390401d4800110302d0192041c2c0480d0105040507180c1c9180607802c920300b00091117103200762008900d2080c03482d0002e060100f5200803003034040e120349029178039190040e9042e03800140d5003036015084085c04164000c011018090190185100140c00d03810400805c1c02c40f20060030001d082ca0b003606d4010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 195489991 1250 195488741 195488743
    0x905010f09050118080609010504110f2209020904140607050a050a0f140703050c01050f0c2205060a02030d0f180206160803040f050c0f0a0e130b10050102061503 71
    0x1c049410a181800d2100203845041056481c0b43e04940700178041c09040c00150581504a2401240a03541070340c2c42d11905001c201d034010b81c5095040c3c2020103180507030f1048034503145121021000c0e0030045480c00c0c1660010b04010f8088038104e4590101036030b030020b0440b0410810703a00007240c0c1456031a10180300c81c05040d42c0541c2c418401003090314116100003074850900e504418603101c4d925600e40006250280250700014148007543d0b00c3c000009091540c0c21035000d0080380141c00051500d40b6400000c14140000102c080c5a1401041d0000301070300e0301001050902c41650185271145401124002580c0d90001003864460402200b4140076404207480c0340440e50440e445550380800c1a414000c429500d200901506e00100800c000d1001844002a909224400340c51032401a03600f000800440e822441350001d0500205000e80c24854544613000800d0a41d005c0b03c1802983e40ca0200100882c1d00900e0544024420401e550701001010780101c1d8500011400103031500102e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 195491241 1250 195489991 195490007
    0x91a07020703121716170a0902040b060301030c0e150a090504060b01020705030d120f0c0c050f010c080402100e13020c0708070b0a05031008010905060f0f0405150901020f0c06070905010f 82
    0x40c000941c020400d0355083e02442805030f10045a14148045140107000c047c024003c07200260b00603801d18000b200c262400300b007101e050369030049598903680c0c2403c41c1c03a10081e200034503c02c42000c1188850106030f0310511f901004010048020983b8585840c2480a03200c11600302415540404428400e85e079020801c04442140e5240c0880340000514404c8054500640c485604c5440c00110711801ca41c405540c01c2600d005108a800700500c0400e020b081b12240f00f600c5000452040c04030f0018a03004103a03c0c241c0d00036152442d01c164100c40000ea07102142100a5220303503000895400311a010f1091000502060028055291410801e81c5441c03140010540800600100050010030040508005400c8050003000002480d180c0183d46180507142e4084056008000039904004050610300ca2540007016000017070a02c2200800310740301906000e503d540134071441c0030745500e500c045c0402c01c03100c0004203581c0c18641c0000e00b9014854200504224000400b605200d400c0000303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 195492491 1250 195491241 195491251
    0xb040b031b220504080405010f0207140f060405040f1b090302060d020a032c0111180108042306011d06060304030e03030922050603030913091a070207031217 69
    0x6650381c4800c0c0302c00c20411140429059008807032a050500042c00000009403050301c00a890f8540d041e110340005030303a118114440c40e000120340c102e036500b450420200f40c4001d460081c2049090644880018051f0b80d12442c0000f00d41c0d41e01c003103154004a20041418209240b07040840070181146c0114032140304440507414200c0c2c0002c1d540140074031981c004c80e842d007500f04000100710f56000c4001511501141100c03401c3d0f0929419050801c000412034044848003403148040040c03100041d500550020001d44088500c3e00d0382e15000402e00d80d00c2c410f0f42880e5805400a0360600306400b0030b000b2041c00340b05041c1c5d2501c4c101b20068941504490300140c150410384451041640040c0c40c511a06c2030942d0403000441e400344007028500414003c043c2200c0050040fa507980e81410303a00e01880031101d41c05040c0a8030402003400c203a00c00d40c01180204015010b102924980d11152001551048016840024100b042c41100300100d4620f200c07030f00c0e04c03560202440c500040464400381c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 195493741 1250 195492491 195492499
    0x6050405061e070b040b1006050405090711120403020111010b0f060d020c010c0909050601080603071a0c01060e1b130308090d020307060818010915020a090b07060b040b031b 76
    0x406a41d090120501c0c841d80303441030510b0a40d1414140790201d0203080c00e84044408441803404501e440710300c04515401e45a0550f5128289840d020810000a80c00fa00b100c041c000c5201410015044c244400e40c50a5003004005036168550b00c00181301c1401001002d00c0359140001c1004555601280c640201d1022a140340e1542041c071700d040000d05c6211b03003d014941c6403d080a82007038005803100200ea252810412856548a005403109042120301135499000724106001001001e005070b400e0002e0700c004241010038a91201e400c4851a40000001d10704402c200a0040604482c0c1140c1e08045030350f55003040c038900101d056150807800000c0c420b000104840c2c5c50794075003d041d020801d400030200c0380345554560001d080c0c501c0941d181c4210319420340b14151542014080c1151459004100704070711038000c1160313402900221b04003001c104503a0380004e4400089006440114090355001440c0850f000412003211200030360f0301d0007500108038060180704106114810501c040d5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 195494991 1250 195493741 195493747
    0x2092523070218190506030a0b06040c170c041a04080a17160605040b01051002070302040507020a140601060e040b0d0b100f0305030301081504050a08210106080610090605040506 78
    0x880001e81100c103255040b41d10301c0f40c0c1d00820100808001a0422a81c482c401c10401500c466060548a100c145805440300d1520b00106800341440e038001101c040d8145451441c0511240e82081050029910000d810030045014041c02c43c0449400084d0021140800c0c81c183c0b42a1041c1d4480b24014006064541511034040c1144100011500e000f00001401440211240740c40d40083c6400c6e1400d603055181d080000c6030a05001e5480e12258000c0d070024401149943d08003c00b403e0300411440460143c0782c4800300084000483c43c0d9070a000d8406040c0035810103200a0015101e88546403046080144030701d615201d454034a50495080110300e006c90303481040100b40320859912a056405036079100000340507011001c2d5050760100025554081e042e1040461800e5081d038000e03016400808148000501e02d4004090010418901c082a486d90010000342c94809a0182000c00d8440c010030050b4589031000c1500c40342281440e021907424040d008090f40614010309001b00000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 195496241 1250 195494991 195494993
    0x9070b0f090904050102191809020304080c010c05030406111207080619090b0108010f0e0c0c01090c0f080f070305100c050d0f0209130504080a03050408070209252307 73
    0x1101c8400c00c000d4403040280c10185001d6000f944111001603980d04003020300003600e8452060b122401e0800d50035420481d0508013008003d40c0054000c03070303100d641007200720840c501c28017400702c0250441c1c4401da1a8541410301e00e0a903a00500c011064540801c61031840d0402d007440160003600601d0714992a40d03c101c00f103074109005c3e15900c660182100b030000350104284d0017103008000b0a0381e8659460342d0b01d0310414003044090041006582e0000000b0b030100328650081c001900300d0800100d29107105454034100303000242c01008242d240741d502444410070400000d03041421842c02018041d1464940c40e489140302d90a10401390b0712110307070b414454450402d032010304019100410652006003d000e0003540022003041c0074500b00c3c1628441c0131394502c162031013079800010061074110342c48022070007000001c004940040c0240f14150240c4c560401031741c030030b001c211050300c0310218812003458142d281c04002d00400608140c4803a90040000c45011481002c00c1007544580c89 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 195497491 1250 195496241 195496267
    0xc080c09010c170c011503020d0204180f2003241305100c0e0a0e010e04020d080c070305061609031103010615020601061202030601020303130c120605040507080609070b 74
    0x9040a400c03810243c01120700b00c04401c0040007500a003c00130050072074420030704003d4000c1c41c07002035030001c0c001c2c2c040009401c040e008907180c11202c034840c3c0c2a034080c0750b0324103001e90914001030715041940820000302c074074448050707a501a81100104000090003c02e101c2000102b0051a17100020f5408104034454080d008219107501c84152890140024040300081004a9099001a03084a0184002e0900ca61032034103544140141d0a41c607800c02c00024142040a00f041b0b030043d00388034200c40850381c284041c110340f00b25140985080c9141d4184245004006400e51101d00e25101081d095160821465400c42ea40000d1030140c4200700c032300083c0107028070382c404e141181c1107085644030b49030301090b00c5050781d1041d166416808943c1e10890100c1c0011079105026034020000710392224000a98000300e80c0c494019080c9041e201d01001c1e200d024042400c0310b429071980d040c4001c010303081c44054040d1119000509043c070b0000c0c0420b80d80e80325446000f404513000a00c40e40360300c007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 195498741 1250 195497491 195497507
    0xa140114091b0415020f010506060c0303150a030812060f01080910050c070c030f15090c050f03071701090b010b0304020a0b030403050d14040201020f0c101209021503010e0a0c080c0901 81
    0x826030844d404104280400603444070b40c02401c44545510745000120b0764540102503403900c64040d40194107585d2000403101e61a0001c90106074050300c180b07800030015070507030020404000c825042d805a03081c0181402140007207580860f050040f20720800420031400102c1c841d00c0301006001184a0300c0d028a00c03080f40c420100040c020302d507a8100030041c00100c284101e0414850141100d2411030100c00504459a20ac0003c00c0c05503050010801c5103814804501c21a50042c1079410321340d520b2141d41d02e9110b80b40e02d480203503515510f940b4140102843d2150040c9070300c451440c5145000c0e80003600f01c03000c2e0f004242d000e6030080085024948a04251421105010400c1001007280d921000c464a0211341c128010f10803004098030414020965440c0703105d0203000e0501550848130b06565800d481d00c00200c442e50f60700044000359035000d141d00350002c4620f00260707403135060100050302e0302e00040c86a0203290521640001c4c1941c800042d07580060012105034552a001d80101c030101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 195499991 1250 195498741 195498749
    0x909361b1507020118090b0907030b010504091d0d090609050d08030601031104030803010f090b0402190e01020f100603060c0504080a020103020d02090907110601090603020a031202150a140114091b04 87
    0x220985c04080b4280d540d170380c04680000781c101c4044800c0c4d5641041101a6000d0408d0036000a4080c0400c1008110640040010428500f510402030180c100c640d85050702c1c0100d03101c00102d00d03030780400c22a0f810014203005800241c03840c6a50380742940714000580b0000c0c00560415a69011444607800d07440260380166038003480941d92135a4030b040080c0a0704d200d004040c0010b14101940c403842c40c280c401c48104e080b00c0001d03158400d601d210f0507507800c4d000c0000b5606601070130501004100090119803010440c0400010b011821420310b00207d03440102000107100702004240103440000a51102c1613a09180160380c4000c0b8150401c043d014802c500b507000b0408400340410560449030040c6460501070840f151603a0f1940100103841c0c651001940011201c00244041000c41c80310041340315807030040f500b00d8000c2207442a20804200d413041c803401e541c0c01c00c602160011100060040050355506044400042d000501c060006001c114103002110801c1500c4a09401910010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 195501241 1250 195499991 195500027
    0x90c07170d021b0c0a0609030b040f032601030b06100909110d061404050619090b0414040c06080a050f06060a0908100b13050c0909361b15070201 64
    0x194030f100c20296550707407003900b00e521442c60b005000c9000c1e41b0030602903040340e03080030416079141c440751079000003840300680640822200454444841c1500f075050380840038130b0040c85607190300d1400e010802e904060300c2c0c544664002d9513000f4981d035004110405031503900200252203120f0f849a40032074802c4d00410848503050020000b03440d80089118103020005035030a2280b6500c06040141d2404950b48156108122441c281303c1d0b140e0700d0340030042940b00900b0000d56040c07601340e41e1100f000210790403900610a00000e03c41143d00031062600003124510a010506050303c41017040c80c0d0042c59280111740208281009500c00c00d44440244150b10503582c0300d04240f40c0c40409410364040050080400e00c910f104017601c00e10980707100c2c10b1240d00442c1485c0100080100c0719034064580800d0a15280c034441e1900302504070380b10800328081404100c02d9441d032030740e818014900d400990f012100c801c1c004054071800b00995031365054410060361006d1500c01a500306404285503141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 195502491 1250 195501241 195501277
    0xe15040e0c0d0e0f070b0d0e01020408011b05031303050918070815010513050409020d0501051303090602010e0a0201050310091a19030f080a030f0911090c07170d02 72
    0x1a207041c00800c01126070b10014890714011411043d521180b500c4001c855501a80c800c1051611800c083c0c203c00480d2100481c03415101d58140e0b0a9807c0b5800c00c0103d659502c2603140ba601011031000f421a489044c002e04514150b80080d0300d01c40145400341c00d000d4006101c40840da580e8400800e241c05400b100521030804450003010350808580403985076034401d101d007034258094420303140b403244180c402d0701241d410201400302811499000b260890f4094210710000703030380ae010303a61203100d106403440d41c03221440c1001024891150720607819649408285000e081002c0313080003603e9020300709a941c035150444030404102c0143c1c010205103150402c814007503031862071461500d10382102d400307814014444c07031108208800d00c0000c10000350380d20800002045a406080c0c1c100440c20005203010610000ca0b041c0c0381680c10032a43e20b003e07030700c0011491800c800c2180d040300c0c1c031403100e50070300c1000c1d43d464508150003540310940ac03a0100d82150104001d40407100c55500031003610034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 195503597 1106 195502491 195502501
    0x4030519050a02060a030906050c0f0d0b0f04060803030a0f050108100f0605060f091009051e030f030c070609060309080d02090a090e0a030207080a030e15040e 70
    0x80d9030240c40b2185015a50341000f0307061440c075a4a02080c0b1140b07907e0b1003001c0347d5000b800605418070034481c0001824481041d1109042400c400007170b007000460004201c0200d09100c42e9225040283c00f007001c01d400700185008421070703002070002a0084500c00243c070424064100d0701c1c0e003d482641158201c9403c0b94007645110000002e160741c4410200d405a40140c485d50801940000c1c0058141030440c038a201c214601d240841000741018001031900e031501d51100710b130111141444034142e40a101030482c01c0a11411240d84400b030701e030740640707a20445c801c84011900380c0d40300052841c024095014940c1d48600054a80342050351184000e40102210603040b00c00c1e8000030070a81d40c1403144d48003814040c0c0040010030b038207203402850040e180c0c00c10805900902464400240c119803003e007941d03811140a414000b050541d01140d009560101c500c83c0d0310401800 = true := by decide +kernel

theorem cover : BRFrame.Cov 195323741 195503597 := by
  have h0 := BRFrame.cov_init 195323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 195323741 ≤ n) (h2 : n < 195503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
