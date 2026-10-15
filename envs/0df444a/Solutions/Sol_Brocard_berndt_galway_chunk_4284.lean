-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4284
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:07:24.125755+00:00
-- url     : https://prove2.me/submissions/1556c57e-5d3f-4558-9b7e-df6f7a17fccc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 770323741 ≤ n < 770503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 770324991 1250 770323741 770323753
    0x1805220e0115060912080316030e150105120708071703160503030f060108040b0c031914070e10300513140706050403080702012c03010f050c070f03050c 67
    0x40401d01000e0503901c0f6880c0001d03000380000807690780204109120541201009285590340c0d504140c0030300030340c1144070802d6502ca400215824090101010355540c1c0704480c0060352400041001950540c0304030001c680040300c04102d00007000800208490804000c1d0140741094008281140111304445207980c0945203000f040050200c01180305007c069503209807034540800458032040100c4d402080d841c0e903071001c03030441010400a140c0c000c0c2c408060207507081d040c014440a50345d85108000258030b0550501030026001044840c00c603038155010041c1c9a400000280f40e80c0c0140840315500c00c04001400d180d082c0c8000420170740d00081340c140320038101010f000280c400101c3c41940e00e130001030319800014101081480803920556501420b01742507484800351544a1802241070294080500d8128126005a0401c0c14100350a581d01014640207060070360b2528078044030050320b40401c03c01e2040814ac103035928190010784240c000103103880c0a840034440d60b447d00b0341c54403485c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 770326241 1250 770324991 770325011
    0x1e0f0a050f0d0611030109140703050106020a02011103040512070e0a020f1905120403020c100f140f09090405060403020606010302120106050702040e030d0f111e18060304060c1805220e01 82
    0x758004281008c8108003000d40e070f9407515401ca040355420301400006800440c00c00340590b100c1c01b110540d1a643c2c1c000d5a00e06642d80000500c10003c8060511540e00301c0b42e030401c08400c0034480710341c0c0f08c1d0101c1c0b8154070700f010103007460550340700725055010600d071054803456006201d42e0544002c0c400902e009441c4d4142410069aa0301d2400c103070074440d51000b03210110581c81400000c198200c10b0f02d4468900d101500c3e0000c0542190110304402c800c00e000c00324255031445805030060780100c0180100e0300301410300a04146005040321306041c0100301d558501005425450304513113070b9103000e079140c0440b0b20002d03024111607000381810340301c080b507034000703100641c0d00c560401c098030201081040ca0568402e00d250080e02100c8010a210841c1d040350800c0900c010502c06411045004040581e000003e0f2541c005075405c0e50b284d50354103074030425190081d406041681d100813507844200d00c0c4c01b00103484015034686442a072148044d9090346c0343c0440e0442c100704a4030200a00080c00c039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 770327491 1250 770326241 770326259
    0x8040305010506010e1e010c021f120501030b0c1b07090c1101090506010b07080c070609030c0803070209190f0912080f0708070309111e0f0a050f0d06110301 69
    0x2804203461552a100114805600503400c1004086000d008a070280342c80c410640107522400c402c1034180481d82901100503138409070710000c8a40d2000c00103030951141d20f0024180061828003140031803810b001400450705071252154801030803101140c0d52202544034042c44815108489a1031241120100700c0e806590851404ea60a03903603481ca595440d000c850b801c0e101044000340072a04140c00610055030071380020308580c1d0007001d03181c0c6044040d4119510300032040d03003c40f0004841400900401c5041211400241007000003181480c05a0700000c00d440030262080031a9030380c0310014201041d07a034100c80072a00400c2d00400c076945140c28441c6011a12602c56000250f4482c0090b021801a8801e6405002540e5808070f0326503924900780c0c0141804681650808080e0584400c1a900c070f04510004c441100200401d4401c1c04090280c1d06907100c85981c85905222801d224030346910705061170b100700444d0502d05000403420044000c0c90710b00d0344000c242100100105449403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 770328741 1250 770327491 770327497
    0x9181303020d05070b061c02030714010305160f030c030b030a030507060f09030207030308130c0605090f04020415140d090b040b0601030b010c0204021309020a02070303090e04082a0a08 81
    0x101079001d881d002800010202d0b00c3c0d10400074010811024140403d1081c01c000510415003248100308940d014000d40019182100a0f0302481074400b0b68282c510031940d01d4041c0c640c1000304820703840d41c3d01c0c40342c0320302400218014078100b040584e9000c00040d03140c4a46c00102c49a400541611080c04950074000e0496214910035a040340c1004120440b803001c07841359810458040c2c0c0a000d9441c15603808032013100e030241c020340c3c011100444001c045a941c29240303000b840240c907400d96504d03104082c8a4005001e00640748101d02c107000401461031030b076458a10150b01c51811080d610800040e800315801684010f000191504241c282003200d000c01d0180994091417009005913204001102500d100b044c50a00261304520681c00508045d0042d110a450928858141913100d1180390120b030054085000143d21a240420a00d078210740c8032005401c01141c0d03034015140580341e1031240e10503043c07040240e44407000101c01502d0a901e08900f000120300c02e03205100c01c0d034100480030350 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 770329991 1250 770328741 770328743
    0x60e07060801051e061b0601091a0d0804051203070602160215090a0509040201020109050d0221191803050d03050a0b090702100b040b030a0f0308010e010605090402091813 75
    0x7503420001240c6481c20b400d8000d03640c4c0404202c046011543c00030702c415508030007090812250300c2c1d51000b02040082c0702c0240078102d4800e0008043d42c090028802c1e807401e40d6102400744c02c030003c0d98404150344c14203e030161071081d01c036013050b142040c4241d071541c450781d0700c045c08891011402200807403807081c0f0384202d035000701c680740f2000c4090f1700e20400503c0741d4901e456124000c2141041207081031080c4a500030b005000000d44250b0580360b050505000c862110011f80104003205000302007041202c007401d086040050401084a62007240980c00507a0302040c000307400142e0881040050040003d1607001003a2500c06480c804054068881134401d8181d060500c1c0f030705640e50400c408858400d00050703000b41240301c000070142006120000006401903240c0c0c1c102c0c1c082d81c404101c0c41305540c0c410442441c0d21000c80c280203151401c180c01490410511030010007845501c941621420441202c1c0140d680d040d0f00001201e2225035800c05c0c015441e80030400c0410f800510b107001d082 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 770331241 1250 770329991 770329997
    0x12151305040b2a040501030903050c060f06100c0506010b07020a0b13051f0f2d02031902150115090f170106090618020c0a061803020d091a03060a03060e0706 69
    0x43c402007006640c100c002030320b8000b0300b001888100200e40c030a4000440711400703810028903005000d48010700b091400c031030031a04510101306003d00c070304248010401040c01850120f840c88140c2da21141c50300c0e0188581d13159a040400c031700c4250356031800305000514180c800705a6514900362103c2422505114140c1f04d00b400585004030054211802090041240c0d192103040200034425540800316103500d0094203035903c448000c81e5040c1585074092641500150749540211404c0c1410b041c8440d9080b0854001e401028516280e55039100d05540c80601e252580d1007840a049030300c10060b600c516182015580000396680c404500d500100350790708000e1000b41d44446000065841c684544841045d115043c040b20043c103a0191070200e00c0c03601a0f94290801e6214102038a82c0c0c40e5141c800d611030140302104042e01041070030150142420444840c41c03800c0c1c112035031078901c203090102c40e090001c0021010b0381c840103c2e502031a884001041041c800101190b60352856004803008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 770332491 1250 770331241 770331271
    0x703080705012c1c0912061b03021305030a03021e0a05120405040e011a040b011806110f1216020d0b010602071d10030206091503040b040b060612151305040b 69
    0x2060000d8840a8000900e464080e056458404d048441403400706051f508159117a0740c590381d404048071840300d0121070f981d01588401181c801032101e80c0d40b5521151180d444000e048000a40101e40c2c80b2588441c1082c83c06545c0810015600700400e06100a060380240080941d25802504c0039106440c4159001c101c9082c1c00c0c0b516a00301c0310000b40c2c1d5468201070011300b104c18070300741e00b1410040406160002c00820fa0a8460320704d040943c110a000c103038281c460700416041008940c88070700c0140300504054030a02040111407080b413030b915920101d810340100030b5448030015a1072503a4040c00d410283e695a150080d00c40c0501d014003e00c5103008200c40006020016031180142c8100c2200403429146a0030001c2550200b00e038650480703031030311980d1f8503c002440554403690048801d411149402c0c40c041c0840e41000340740310721608040c0020030400c1c000c1c0d451154050400c0d542d46118018000000c2c03a00e83c0c910181a40e003d041c40104010071000002c900e014182441c840c41c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 770333741 1250 770332491 770332513
    0x70f11060a0c020907030906020301080606040e0303070507020d0f0210021510050901170106081c0f080c07240903020a020f0105160303020a051612090509090703080705012c 76
    0x549100740090500042e00444002001d803414040c2d02c0d40214041c1000102440a540d5440598100340c1c071091068005004128440c01c00340201e0001c00080c00196103075103000140606240a01d45003e40540034000d40b0104000780807844620042d0014040303c45501c03400002940e80510b242140000c4211501203032922503075008030000e07140020420906a070030440b00943c8011060b860100399901c521000035007c5e0309000c89a50806250ba800c480c80d40040d0000e05200050f142e0b100c1000f00f00002c2080b50344400041d103a001d5072009001650516000302e1412001c0e02d070b5651011107203821803201c1055000103407444198030941710344010354011001507c86024a44403103c8a004011090300001d22079401404c00303100504003142440000c40d00444041e102302000c881183c40308003101581a003000c0000010103003211181c481c2c3c50035800b00340c0c6035400e91100400c440c10108000041203820341018071035900d0540c9815580040c40c1c20f100a500070300380c82034800d004a1006031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 770334991 1250 770333741 770333749
    0x809010e03030c030405151608041d0c04060f0c060c350c0a11030a030509150402100f090302091e0f0705180607021008070f05340503070f11 62
    0x3c3c00c100c075440180d42002d1511040c45034220034101c000c1c3c0702e01010845004141c2d034900c10550000e000d1a140da84581c01e214880c0c2c403990901500e1548602c1410030840d21850f4101160207840052806a01a000d0b44d407003500d500c21a031100502441c01d0001d14504183e02a1016844050b50420703079440301c0c003d00b800b001d0a50614052024104040d001407960b06100c00105001701240c6090842c242d9010b280b00d0a40c4c004000800020342c42d9014860303030140800154401541501c514451402c0c00d50002d00d08070508200c8100348040144908001c0e030060054400440d00a0135a0000c0d00d8002c05410500381c40c403603e140740c16110004941c00440201c01207200342c01588445140c003819081d01d540007050f01c069160300c10010400d960041c2c990902155883e00c1c2ea84581c5881c1c181440003509014002c0610001c112080c060000304000c03055501c2c8000900c41114540c01c0782c1002030501c04103600c800600f46201c005000d2081003105604101880c0c0070301001c4540c09510001c00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 770336241 1250 770334991 770334997
    0x20115090e0c04020c1b031002030103060903202a0d0812091605060d020705030a030c02060c1c0507020120030603010c03020705031e1b0a05370204180809010e0303 72
    0x46140c40c0d120325001001b45041600b250744e42c0344020203d41c0c5038141c003c02102682d000b6007040380e5454648805c0350416801c0402500503002c46143e80d4048400007954603034458a030840c42d00c10428458920041c5201c100301c0030003448010700600e802115900301003106a0010410041002c0a070340002d0542e40040703505003690000080c03075134129180504206883e080b01d414010084d50070841c000000d20104020902201c0d5901c001c00da24031039180c06410b25900801d05842c00c003041141c1c00c0c2142e0340030b01d02c0506e0024898009101d444040040740103001601c2202c1e100030404100c9200c481c85903001e1803081070114000c1c0410303034032110101c09038087d03000014240c2d4030500c03480c8000e0080e40e15901d88000058907080c03c05441c0d0f1003c0f8043d05c68014600e00980141c030044040c0a0140301380d2803503140035501420103204072441c100800d09a51048002c00341104000011035540d81c21803d00d244c40b0a5881c19441460f00701820b144c0e1040100c0c0b4046402030302403941c10f01f070100c25 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 770337491 1250 770336241 770336257
    0xb063c0a0206070c1104240b09010c0b0907030b041b06180501030c210608010f0b01080402010c05101a03010b0a0b160606050613150219030f020115090e0c0402 70
    0x1408883c1c030746400555110329a0300080340c8500740015080e0b010340760303841603180e00e5100f0200751142c0c144401c02d9602070f41581e080301c3c0303a8000400603695666002035145c80500d50014007400c041d92010b001d0350806103640c100400c0d0b9640801484280550002c3e503682c280940b0261407241c617580c04042d600c907880946850504103034610208440d6003e0340c0b0095121f920f41c141100e43d0015800110144040740c8081d06010369240c1d420702000900348070b59a00507455000030441103411000103002204000d00083c104807815040c0c00c10800d0904c0840403803010402e0a100b94400c000d1544659041132140c6404ae40c6000301d6110f49180007020b6408450b000e8140903c1c0182500d5041e00304c00c2c034610142d6401d510781200240702e17205c000c020110100c928950740c01c1d2609100c01d03201c80d501403180140c115130050180d081c01d500402d04140125505003070484a074900b040702a0b0140c0440004d004c07428201500c001b480740d0803500082d1400d0003a900f074039108058607040204074042c0b81c2c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 770338741 1250 770337491 770337493
    0x9050d08060d0303092a06090602031804050709080307110f032409012304050105060117060405071403070e030d09030305121e0403050706060909050309040b063c0a02 73
    0xb0250100e4020b501600e1341c24004e801034840b402c0400c440702040131001d01000901c2140c03160030003000d90301002c100d002d016113102842c603051380003d0717424501d542124110320461303890002c00c11480c004e42e04035000300011001d0700d0311014a8240340740340440c0d000b0030a004000301100507072280760110345080d0412003809003c90055103641e1101e5149401009606250741ea581100c0b19800c030078200c1020104108103950281c07034985022801c1d254007510300d81c14030140e0148454070305400e140d410340c444000c0c0c03400662a516003404550f011700c6441d40342c07084140041840211b0380d000c808a000710009900b1662610b04814044882170540e12000d800076105220045100001449840e01302c2840c40041004201100a118940b07005550480c0455400a28101008024018140100302d540c03800c00142406465003070b113a20134102c000d03101340c0d42e803056000340390740b502c00381c7d001d44800c0c6071564030704424203145070101ca03a14186c1d00744e030a07004440c0c0d8001c0d8504608684034090b880c1c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 770339991 1250 770338741 770338759
    0x30c090c021b01110f010614010305131218090906110a050d0e0c040608150903040311010c0320010f0e07051c14100507110105010806011a090a0909050d0806 69
    0x5801c00704002e502d0403402d04000001180002e040c0041020380e0a5074002030000440345e24180c211a0f04610401c01b01d8141401d207803c000a80c2103451942c02d030b8680084400e4100e00c00c8280440303803203102175000414922900c2d400300d07a6526170f0b03016485040c46180200610428080c0c2000310f0b000c0c0b071f003090000401c10810301200020f5500080203440303044d0211340e0000e2420000806941c92034101080c02d51009072011814410112006d0b0800506009907181c241151514455110b06043d0b460601003c00c2d001c00405200385c00010003151820141480074101d0b0b14624007900006806510581c14011000c92803034000c28000d0468000070101d030f011580d411200c52108140000c1a0340c41d82c203444204402c40002d00c1121102407030520b00040c03e141030100588240c66070342e0101840d0f071400b801805103250001d81107065505548109401c410780d6083e002c414800e104403070750019002400007411001c503411040c000e602c04d03820f4a8080c11040d10807901140c0c101c41e1a5400305080f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 770341241 1250 770339991 770340013
    0xd1203050f040215130509070206040201090e0108030406051b1509070e010503030a0e01050d1406090f09210405060f0307110d1b02012c010f09080a06150e040606030c090c02 76
    0xb05004003d00171054803074216455941d000144030040449017500940c20132401c1004640c1d01803e90340c0540703503d220840d4107505155401d03540c0e001c0c034090ba0051040010764641c816407240d0b0101c031242d1100c012109103c511680c074404a9006aa08210321321a0f110040b03540c00304030b1421416210060015818443d140400311520010000c81c03d051080800c480c401d0101580608400080c11309a410001d0910f24244000800001c000624000045003030091250b8045803004a00e42104285006800010b40c081800c1c07040307030310072580a400001c5518040202101030341c450180740d124440c000c030069040c6505c5501842c1c400f400255511803012a892000703080d001c1081c018905111742001e40700c9100d49042d028800020081c5041d20030070748660740207a501254454514081c19090315054a036541e818032410018a030980381c1c0c450a41425020420390014005440048140e0401c1d00b041001489640400e44260001490100710003503030307000c1d100c800078942d80207000384801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 770342491 1250 770341241 770341279
    0x40207051203070e0d05010209010e0f0d030c150c03051006020706050f0a091d06090907210510182607020906040912110114090a020d030e0d1203050f0402 68
    0x1d01402c04d022503580131648603202c1080090000c0e01c02d000059892075a40009818200c0d0301183ea0310610b4034400210a5842e00b00701c440d030f659814100718000102a141902844104034058600d0505c0e1030343c0c401c4d10740d9041d00540d00480b01905401d07440e9031190300480c1c0f169000d000d4400810300402180401000c0c4130010189510b045c035003c001c0d07039101c01c2ca4448103080e1160104005030b034807040c40843c0c43e21015041d0480c88041c02013950034a4a50170072450f40e920806000c8040844414509218040c80711800403011103004100028030407201c1101e445020405a4100801c07c41000c409003049a0303000c90840303008081342c20b1003003550800c041201c00030860f640060b00d44662000240c40002da100c01107146443d45280c03c1081d4200070f00b15025180c070400d0f00b24002051148032503020514076107298041c0c1d6040b0626290b0705003038400c540010011500303e000484042d0074400550355444800d206079a041c445522958400c0807848029103002e50300c0446003c0d0603a40b40c034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 770343741 1250 770342491 770342497
    0xd18022805030102130302041401150309020607051005010609061d060307030b090c030711071412030408060f010317190e0f040908040e090715121d010603030801050402070512 77
    0x1550800c00380c8425100c40100782603802c2403104450242168100740110f250500400d1000000031b0746111041d07152010b05000488040c0c605000d040e61113942c2c20030740d02c03140d0803681000d0b049000c0301c1d4000c02c0d0021450040c41c09201c2c180005815075004212113110302c0014003404c070309603812120b41540c41e00b005041d0784042c0120042c965109101c4903561262403c262040c50212102034032881c001c8409419490100e082403d950080041030005406003d00780012020503a0f04401e985106002a40f5510494101e4002c0d48100c1040160316600401880d041e00d00c11000d542400d4081c642c484014020941c00411950f282110303150300c0c40c420903031683d100500410300d140f08403440b808901101d21040301503800c0c9400060621144440c0d84140c1e0704805500014401c242c6860251000914160120010030008105000348000c0a80201d03094a40c007030a907040301070f0f4810041c0d00803da1444101c020032020000001e607850b1034803c1d44ca0654200e405080b100c034410055205c00c4d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 770344991 1250 770343741 770343799
    0x1008030c0325050f0c030132131718010504032103020d0c08090c010c0302060705030405070513091a130f05161205151015031e020d1802 60
    0x5070342d001d50038001c12070402c0409055440a400f40c4001da94280034035007503402c0500113806403148020078000c01c5c60f220840d1090b12800724980003041c0c0300e42086a47c1201414005080c064040b811f01030040d01c4ad400400042505080b1507000101280041d01e03107000300e201c00307040d5506206486000c1d170304080800c0700486003454014039050050008104580c965003e90303000520200c20081da4402c20080008891001d0901814074801d581c1c00030340c0c1d110018601e00c100b110100100303080184c20030032031000d0400108145494907520260034010250442c1c00d45680c1201a070441c591200106094000c00f1040d03051541072040f51211510300b0701d010404c5400c1c1c401c50000c04444c803150103448001e0124400310000304181b600305141b0340303000f0001d85110701010b201400b092441041c82d0307600700c408148071911040300c28a01600244185626104c1e8040c24460310241c080301a4010401c83e5021881004403501034001046500320000000390040302800d00c8410b2220503e071180890 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 770346241 1250 770344991 770345047
    0x6040501080a0b061611030111091009030f060504021914011b061113060509030a120309060f0e0f0106051003091e0f1707050c06030603241008030c03 66
    0x83d040b8404192954001c0c3c0c055609030700510100c2e400c000240310000c0303045004030024402906e800036150204d1040502e2a840344400380038901d46a40030f280e001d0011500002a0b980c042c015003421000340004480c00c81c400c8001007040440592010b2041e02942c41c1098980309265500c401510544031403203e814089004000c541c0009401b4040c0e0100540602038080c1c40729580011940c002520350840000d014060058907a551030001d2194089504061020406110140250020046040b02600c00c03410841c0106800c6c0d51030b04031081f41400d2104072078201070301e440014200e40c07050140503480343c1400c03803070f4520705d201780c004140c0d80380908003807201303e8101d00f0a02880400150104d91080c83d205480060203055620b082250305c2040c0414980412591070365151010002450302c0f43c82c000c00400c03110340f030401a030303003500d02c0b84107184d42c00400d010340e4191640f0f01202c40d92414003082e0000b04a010004c02650038444000740154106404005039403005c0c00134030020002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 770347491 1250 770346241 770346251
    0x40c0909050c19021c05030606070506150a140109170313060c02010f030516030e10020f070b07030c0c2004050f0f0c09210102090607030503011404050606040501080a 73
    0x3000c59218107409450200042a650300f40400a010408410740d005001d54000504d085003d007040100c030380c141030162500360341d25501c4000158a500440034044e007207115550802051000d40050181119000c982400c405590341c00075888203040e840340a40020703031546040210a5505a15407911012801520708000140c2c0c0540c0901134141e01081c0013900118958080d960020742c0461615070320b24041c0111300d072190702140a1081c4942e60000c141e901c1c800c03540216410721074004c20300c00c20340040d5a0f50020050003185900100d01c142d82da12600c8c0c01007500203009100f0400343c0c2c1c40c3d0b07441d518040ea03110b4645030b2070124100c8880c1091510354620b042c05a40d0b038401c0e18854400c4200f031500900300304010315041030000300109500402080760040c555200ca0100f00340e000b544404140d00300d6000000c0d40603001d0f0b03001c2c154101101140c0401050340010203103050720550401404041101402c0000351401a207406402804c00c01c818442035100f2032080b907000b030501c035000c50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 770348741 1250 770347491 770347499
    0xd080a0c0b1008070603021b0607260606030f041b06020c011e1b060902030d0507050d090303021911100801030b0906010506072a1520060105041e020a02071502031305040c09 76
    0x41080c034100c51b9980010b05002d01c002d54bc01c8103c404601d44000d1b015811034501d0428086545ca201c05000005408080b1000804107c400440c1c90303202c14080100400d06692504041c0da129040c4890714041081e100c11103035550442c0009250b5941e869660031b080c03840c14a030702040d075804020207692540d1a01d0400e005030b2410041a90421050340d90a07540c0c2503036040036420509802150010414480e0007040803960000380140c00e40741c40d000f45046e09440d80f17025a0110701e41044250002550a0f0700d02c2500d0b041242c190480307001d8201c081c101d6032942c2d410740c0c40369424080c01d941b2503803d0104030301098440d400208840b000d100e4070074070428a4000000a1041d581c421080d410142a41400d01503015012081d90f000f0808004119044006201e4481105026280c0100c3d80c0b2903400d401c504190b090100c0c0000007550866a828040c0e1001351240c0c600d0080d014031040003000741e10094400001c940811619110074200c02d81003c0402000e440d20543d00020802c02c50070200e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 770349991 1250 770348741 770348743
    0x3060d0605010b1c091a060d050f0618060103080f0307120504060b0112060501090302060c1207030c1106040e0708060301021b0a0c0f1a090d080a0c0b1008070603021b 73
    0x2400307848410401a202c851041314864600c2149035201600350a040921000482c07000403030303071001d13841c8203c075107640c0d109000b04200d480c1510b0054503922480c2135203881034502050050040c6041c0c11100350350740311548510340c0c80c0303c00c7c440100680d01c20496651180c41e07400165805c4481450400f1220225180c03520966000361800d84e40603036142c54481c4e5540c0c00034204002061a20400c0c00410725110001e00310000620010307001e49400610001d40b500144500c40c060040080e038281c4501c00740c180100010b221010440d05000010300ca4089440c000058600301c58102544c155150303a400f00032191508080d10b079507007564080c4101c051001c0001d070729400d03040481000b09081b501c6410003080b0070100d81e00019450020541c18003032045140e888103400d01031001081e64403c480c90114a03883c0c2441000351212401140032000d542e840b80e0b03070340b501134040c04815003681c55402c03810200e08014807400007140d001c150100700c128000e4000c2d00107804258448104030b04010292 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 770351241 1250 770349991 770350001
    0x70308041401261006320c0d0c0c080a0b04080c07050a0b0c06010b03010b040303110a0f0f1415130c0b0d0204050102070f052202090406060905010f08040f030503060d06 74
    0x2c040f000842100300f216040792042260002e01086c0b5002e400614022410008140c06461000503841c102203603c2d1400407510850304128426400c6030384448184d0001040307410420000c44202c0c008000015116030009198052a0b4010030304011503200e03035403008070075071000002050078040c01c4000079130765603103070070000082801c09140ea5544110044079814010142c01414010340700f44010311800c0f8404040e901a40c0e8107042c00c40d208500009020f207080c0d04150010304158401c0000c008101484241c00b22140c401c3d54841d8001d0101d0202940300d041e1415001d24100c0c02400190300d503819072160030f00050080b07444000391900c2c1c18107a51a6400003e0104c141030b00058100519681000054010215814000301403820440042c07000c450002e4000041c82c0f5100143c4001d81480d4103d5207034540003032042000d1030f031303070700c3c0107001311038248a2a0f0114512004000e141409001d46078443d6a01c00c0500794070794500e90f0243d030981c0000d0708250300326900c80030400003d5203e00c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 770352491 1250 770351241 770351297
    0x90f030a03051903140105091b0d0609050906061813060504050303180601060206241804020a05010c0203100f020c060405060f1605030f06030f1005040b09070308041401 74
    0x502651038240d11a6000441e541e0f080c490700305890240040a1309103294050f6042d00c3d800c940e201e1443d1911f4480202c40c7c41804103c003021300700010060481c01d501d500250486125140500c039580d14850340903124030b0201c40254010500340c412040c99109a04501d43c060704904403580c2c08001d80d19000c0407260708403000c0303405500000030311010705000d41c0f40d40d0840354014010300b407540c10070744000e489100103441560303a82d44040005201002c1c1811036030200c5000b400e0300050140125850b200c5103001d80e000c1c6e008450380d20020416511940c408070342c180d000340013002c995940008841c014409101d90421040c0d00f8400c1040c881030a0180700d01460052004041c541014171600c810b8100103002c134072030401d88000d545405038201c001e80f98400c03250b5001100356030b603507408030b030030046071a00c0c2d031038140600c0600281d5025140d21141c01a400358041d1a040d5485501480d651101408080c081e02d20078401040785c1484d103058129a10418074080700565654070b00740040c0c22601e12 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 770353741 1250 770352491 770352497
    0x80c070f021f051209060403211e09140d140702040b180106030b030312070e031e070602010e0304080c06030a0b0405040c03030305070e090610020a051c0f0306081002090f030a03 78
    0x502400c150004981040c0c104907010058080d03803c042e60b000d01040c007900326120701e00c6103c0c027904d0f04040403544244000790102c09010704c001041c00d0301800800c20904100c91a5001103a885040f0400042101903a0032944881c1900005010918031540004008983c400e4075450111001e45841640c12860680072415142315410018042c041d104052110b078042d0780b00748000c03c144609620700c0d64101c41070f802c10703540764030104021074200134540040a1541c41c400b0346c85100d94000060020448545a008000c003450700c1c0050390312803140c0c1c8903080300d90384601a46065031400000940c1c00484407a0005100c81040000c0340944104035420b454502003510b0400601d0b4050040c43e600446516100034282c4400340046c588601c06031007203020704203d48600e103000d4000c01403040c0c07031900300b0111840202085480035100009004420008100303039401011207000b4018041551f40c03c1c8082c00e404029425064000e410a00506a00c0f880445034030780a910300b03116210009001365 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 770354991 1250 770353741 770353747
    0x1011100506060a0c051f06050901290f070605090f0705010c050307110607060c0201020a0906030213030605091509010c020f030c1002130e15091605030f071713060c080c070f021f05 79
    0x23002c000240700141e0128448801e2407560581051400b001b541c241941301443c0c50303d9411850840e061030283d440300415251402c024085180b600048800e902411042180c07d80c03503d0b4030044034071104400c00280140c0c0706004a100082c1c6518120b00200e0001e0040d03810709110b43c444a060718000c3c0341c5100580d50024240150030390215a1601804481c01c0a514100321207911b0a582c00b207030f00c0301500850340c0d400464000b4105100c1d0103405484040140c0407030400c07518140c02422288444405445030810342401c0c2140030054032038002c64040a001172415005d00d6030b000c0e6003c1d890b07150418000d002c004c1071050400032058007030b02103101c01c408001400c4083c0703d4080d101911151182000c0c400c079520351070b400b6040380ea2005046da04060651903451058a05401e120b00d183c545118220400c0b8104016500d90b01c01c0340d010303103070a0040e03110f002030a0312008429211000c1210f4100024000710704194a50254507102a0491a44801a1107100c4000c803a0f450900c7c0020400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 770356241 1250 770354991 770354999
    0xb0703021c2304030207120804090b040c1d0f04090302060702060a11161b0b0a120501030b0402221503020325170c1011100506060a0c051f06 62
    0x500300300848030001c1c00421080281060410700015030b0011802c401900c00c002504041c42800300c03e0007410642c5c400400207030f440c6028102e82d00305010b80303501c0300d1070854600000c0c6001d00843d220500c8a0b29204001c800f0142c0e103000c440702044209801003420031074010981c40b9440303602d04460003a800b500340e9040c4040300174240000600011501804d090a01501c0c007145030869000e00e030032144544084080349072540c1581841a001903401d00d2040b000501020300038001c1002c2001580c40d0801c940021101e4401c0b01c40a000181030003594200040040c00c14000448156031404c810222100b120903156003969480ea1025004890130340c410011820100108942c1134040e002c07140252201090301c4c1c1c0800e0613446403012110b52049014814003040c03001c010f100502500504941e8980c42d400350421441e00c2e0158028800e00b4a51035614903140300c0d0b54012200280303064a024840702c3c0446028500480c251454001c030002c1c02c40034800480c1400e014142c85c403001c0740c447c0c98 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 770357491 1250 770356241 770356267
    0x9060d06180c0f0e010f110c0406030311120315091503010c180911160f080c0a0c0518010b030702030d05010e0105120303010f03021c290610080c03070c0b070302 71
    0x4280c0104007130000c03001840c820342c1e030001070003002c076901450041c4c0d0b20b68036401650300d400341c1c0703084090f001490b2240120901d5800700700e03019400e1905044400700302c41c60004480c64402240e55a0302c1d1350750410101111310300f001d80c03180c1003511402e10640d40982140001e084802d00b42c410404074500811258000d003a000d00d4200814a6010800c00c0d00310740c4e410100d452103040e64070402a84000404020000201244250190401007083d01e035014001080d036241c099003020760714020010000903852034031414040c10880c0c0041c082c250384e4645020f450322500080c02070029400288803241803010244601743c001e0107203070981880c0b940341800780084920408042e80a40e001000140f001c8407682100e03004580c1d0644403c2c6142d03680e0781420300c2000d51100002c000055006560050001c411051106010003407050344094641d80704203d200e0404029040200745000c2c0000c8c0b185010a020303503400201420045024402541c42040c582c0f070860341c0c80c0c0440c0d40401e00c9458108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 770358741 1250 770357491 770357507
    0xd0c15021903060506070f060903020313080606011206080316171611030105012301020328020d090518090106050405040f0605061801170705090a1406040b0609060d06180c 75
    0x3d5450300d140001a80701d02488030b80c47c0001400c55070700c51240710109031003003049800f507424405c030040c01d50381c5803914a6160034003511494005600c1454110324292288030300d000b1070300704100461900701807041ca00c0d540e1001020540da94154800c9245501c0c91201c020016a611403445e074450304614038080070103203104803a442c02a0301d131034014408407a00300c003010000c5c0b08000422002a2104004034a10b21401070b0300141c080d503e1508a12440f000701d80c605010038030750240e401e041c0380a01e0807140b514961049961000c0802090001140d00000403900081501c00100b81c0c0d503101c00105060300e03801c0d1400c0380d002ca4820040380c180003803441080e030494421215045c4801c06000f42c0b6103000410700603508194440c01010002450400090000386000340c43c0104500e840952a00240b050b4070708020103090440000d241e038509403060b01d5084100401c450309000070300d4240440f43e000800718504440e41c50401060b40110740c000b01003910501840414154009134005180c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 770359991 1250 770358741 770358749
    0x70f080708120c030a1229100f0207140105161109011e17010b030604150e150c0c0f070e1806042f13091101050c0d0c1502190306 57
    0x500c280f100e82c2c002c000200443e0903980c1e030382c540a1801c0f840c44941d0402031035203142c544100304510008083c001003080079001e070b0a60845406529003417954040c1c0b031803c0c100d885040140c0042209200e03540f10700e40302243c1544185400b41c100f20f0800301e50144111041400c1d600066135500d954091f2a211f920310307015010010281100c95464840f600b03290643d405441e80801c22407542a4964409500c10550450018101d50245c01c00b8107101c0000001d88440300c0700e650518040b005034010000310800b1441280600c2c490965910110a03119080595034030101d0040240c1e182d4115001c115010103000c94240494260a03e4a14500074218200120070550800700811020502d070f44005c4500104102c08410081c1c51100b0104205044055507540526540c00c52030585c0103581c40051481d02c20f010b0200140c200c1401941c941c001d60f10108099800102c045810f10320510031045407030301c1902c41e00e404440d212504002d03a0882500d0021040400d90207542e56903041c002d0304010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 770361241 1250 770359991 770360023
    0x90105010614040308031510080703151208030711060924070e09040519031206290c03040902040311100513050603040213051008010c020303011d09070f080708 70
    0x1514040c040e640b25000c1c52101400001d004000600c0c03464052903164101200104091007101250300c003d4010402a00c40c580002c0c130700000520791640c9581c4000541d0350121890354021010350f00c40405600080c80a800c00250800c20080c5041c10440c01d0b0140c45400060060080c00c020742c0145900090200404c504004040c000c8098100400440c3c03c0300c1510b2007566651365061140c036100300c0c038242c0303103200f10f094002e1014141c0c403c0d840b1004441068040c040300b651018184c104109000e502200c0d42580c0d40141c0901204c0d40c010b010342240001a02e0030b2960301c0c59180c1c101e0304598402c2d628400800b22079981441d1080015800d0700842c10054140711044064100441c6d0314041d85004100c0040480d06556503402d04000440c10608203214504c0e1800341154181080d204044966080c03104401e0030500100950b0705982801000840c0d40c001402d001840b06409400760700b0502461101084000303801c5100400791040500900c0c0c208e1038604c030360380b90103100d6100307040e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 770362491 1250 770361241 770361257
    0xf061902060712060614160804080709060b030c12100515090916020d0302130f060504030b0a020c061323061501050423060d0e07051203030f1b04080f060901050106 72
    0x101e810281341b03541c84621411440e21001c400c441d034007140500401c01307000094045000500d0b1240000e001e0282c40002a09000e000d41c1c031144d034202804180c07880d583c00c6d0030502015208860046401f98490040c400d084541d03541c8a010401505410718000b03000e02d00040c1d40c1301c281c2400f074000342d08030f4408010f081d06c410072030200a40f5035010204480815400040c0c8407003000341c03c1d000700c000d40034030b021002c11036603503400c003a200b03038803a10080302d00746011000100c03121824402d841e40500d43c28054a01540c6403150201c40440000b01100c0c01c4586002d009201186d501c50a078010341c0c174500a000c0d80c11b1140606c0e440a20b641485410000200410700100f2000700301050644240c030325102003000034800240e05801940da84c40300c035034984500d21b480030b80002000011117105071020140754400701031184e224401210b0791000d400315400407840100c6d02c01d00b078070001810403444070306280c1c0ba42e0321241041c0c51220316414662004060000b03000d0284192030042105041602c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 770363741 1250 770362491 770362499
    0x1c2409050628270203090303090706021209040b181342021e09091303080f091c091d04020d031d06071b0e090c0f06190206071206 57
    0x1141e03000c680640800c28507107103242e00074890f40c8401d0b0070301c40c043c4180654681c80c003072515a60383c1d042203404020078401c15100107100c86c000326101229520390903100d4a444988018000941741d9410083d420080c120580d0b01d054064452840c05254000140189044142442d0500714180f00c4405074150501048030b454440c1c007014443d1034480711003201c12100006400400070300899411500901400d81d803520800c00043c01880c080a00b00d5540c05e160301c0302c200d162001c00b410100100400d14500100d681c503030000311550342c0881114104d441e10150f22a00b00401424800c0040120394180014854000c00c11110b10424151003003010b62840e150300000c4100c880620044c0620640c01d03681c10400e4207000070b041603124082e04091303030f80c5030910300580304451b000c41d400040144103401140c85452101064020280a00204a0f403542e4a007003100c20400c00c078070168001070802400c1e016410040c0c85890b042c58a80107800240b8004101500060922100d13800c500c0c80c140085c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 770364991 1250 770363741 770363809
    0x2070303110a090315091e051b090402010c020a0306230c3603240601020606030c040c12110a09120b040f150f020d060b1c24090506 58
    0x42c08507030300100c0302c100001c05d014111005201800b030141612000c5054901c000e00c0c0c0340786018030148034408659100d24080d004110110701241c1c4503600c11500008a030140d07201e0b64040100ca4001003001c48450383d06d41e2200115003110803140d402c0c0c18401c001c0a6a051000301803a44954550501c40c5480045a240d200720490880c042d0640000c0c039071440e0315500c0e151200b81210300c3c05009c9400481004420031003002c080c24143d02400e00d001c00159107075101103291405003030302400400c020001a410800500740502c40801041002043d10024800f60300408103504c0380e20a6541d942d60a120f40240000801e4002c0d1101141c03030030901001484140655500c81c0e0004212180030300c1e1450040c88203220040e9010700f46003041e1a070f0955a149500130b1a00e01c009043c100700a03a643c124481690140b1018040c40e01c500118205600c2c0080e008003d005840e00040810b202c80d0654520303490b201d82c0c1102c255107513507a04100f114104600b01c6145040402550f42c2e2107274030070341c0c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 770366241 1250 770364991 770365007
    0x306080606041509020f030631020a050d05101523030a0f0f0522020109090f150815060609091302151b0705060c030307080c0d0f02070303110a 63
    0x14900480e03a614801070f10001c50041180504078004041d076483d800012207206540054501034400c045c0080001c080c3c4004990702d240040260401c0c00c0e03404904500e12000750420040c01c0c09000082150f4040d600451042d03500c030b41c0c0300000b40b0401c075040c10f62198580d60081c842e04180400c0914540f0360b582101d481c5007a803c041e000c1203550b65a01d1090101420130080440302a07070410011995603070094200502c03c00760b1480c400c00e0070107240c03045440e030141180080c0c0420f1620100340400000b50304049032005607c580802d41e07403003164581c2d004800c00e9101c5e12041d0800740140700c00d01407103031020b50000d5007160700c3c03420b18400f180000e512803800741c60075904000312865807085460385515603142c80110441030381c5419000c40a6008080c4014190035240543d0101050910301203040d101d8201d081c10041d030a6581d1140b060b5041d0314058002d180b051030a10042941e000c140c080c030414404188005600c80f40c0a01d009020360b44216141c0280c11800c1c0402c052944d480604 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 770367491 1250 770366241 770366251
    0xf0c0908010f020a200304051c021023070204092411130b03090a0602220801050708010320092e060e150f03090d0810140603040516060f090603060806 66
    0xb0010080b0171181c51680745100d50342c400b80e046030400e000e82007241100d0803902c2c0a24000d45494015a5846404076074082e070343c644140402051002d01d41507285044050702001d0710181000031307095002c0c1c0300c040040280c0c5d40c229070f403501c1d989107050804146000d00e030f5911401da050641083c1222800054046480c011844d0002001c00055041981081403810b000d401c840110341d41c4030300b00c203020b1910401036504012035400340e5001030764960504c01c4034424842942c2d09081a4215500c0c2090031034445a805405210f81e105500b0035600d402d503da01581d0740c1010b51700d5031044081c0c0290440b18075640d0708421034801008000144d0048015100c050b0b04882060214102414081d040d0244510344003541c45d010040183c0702d41c0010740d10441901649652840f60b0310721000e040e0802260050440903200040c00b03650300e0a108000c1d44d0071920400030307102442d680113040e0320060101c0d03100c50f00290a00000151540c0c101c08960301030020b500d81845081e0405020964031000a42 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 770368741 1250 770367491 770367527
    0x1201020705100e0304030204111308030a090b0412060207021203191b0302060a15080111070201020c09160c15020706090b0603032a030c12030a0b0405040209190f0c0908010f020a 78
    0x401d4000e4690714005c480ac0c400341103034141407107611404034640e03030b400c0881910007094031501d001c680f507403444064808481100490790300600403075807000041c2d0400301c000c0341c000341c400b48056203c0c0300074000f410b20b8240074004646078420002000b8600e0035070f0021120601d09910b2001c0c01700303a010400d5940b1040410300464111521030220741010115030080415510f0141c040188035000c0c00106140c0d4000d07422203106203014010032201110603926a150360b055184001162409041407401c03081c050a081403011641c60100030690303004000031030703406580b003041a040084400c1001d0304010300b41e0007541840456078010311400c10030590184590004940c40e01032803000c104440348603031401d081d20000071198490070f50039001501c8036003850f401c00f42d449040741450b1140c10320803500100024201d44406441c6440c0089458000300201e407520049035541d90741c0d01030130142940e180d4581845900d420384150864014000380e1080c50700404c408107a440d4829003404501c0c070951 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 770369991 1250 770368741 770368751
    0xe010c030e060d02031e0c07170403060e0f250603050c1603080a0b0f06190e0301020433020d050d060801140a0c08090712050c1201020705100e0304030204 68
    0x800d003500c40e440c1240059610600000e4400b0081a05401031800703007100348a494851000e200000702c1011044800711201d41050114002107140c000116080300082140745280c039860751681c81c251070147d904000340340c0c0000100001c0c0c4130104000811000040c20810000500062561380c0105610903182015154004108108205012504419081e00c1020585015890007800d0108100e07004880c8034031f0300b80c010380242041d500e0100c0440004145074548090f02080c010540341c3c03204800108140310504210360b440c2440104042e02d9030200c06100504001c41000054100301087c0c100420a10a00455503800203402140c0d034065040071343d1200441055000280720070f074420550340d0308004501030b50384200e4129500514a190050048200514055800303401c1a104040164410003040060341b60714007803982c4945c410300070348025900c490006960350742101540b64150354005501070800808005003102e083e84403400344107000705901801d0b183d008a10019010b95210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 770371241 1250 770369991 770369993
    0x6090b3103020f1c08090d08012709050718060302090601111c0f0806010c1a0601020a0c090507090e1005130227090106050f180406030b01060305090d090302010e010c 73
    0xc1c040f803040020801d04594064001070822804c034242e0742501c0003c10754240120750b50345c101083e54520480709071a00c501d541d180000080c0b1450b01c0704030041001c0b8000c180801c9075805401003401d1107003e0001040128200668049081d405450004003a450101c007000141c80d02c401ea1944003d0908001410303500b0b100c405420800a03034441d403400580002c00250903030304079440ca240c4020540d0b8054050351010b005440d500b101c040d01528103108181120b003001c032601d261507848101031059a901c01c1e503c0c1e44082c402c0410340c0007101800d842d4410400320980c01000c01006001c03440e02c1ea8050300b04404224902d107080d004d00c0d40079002c50002810f0006298044500c0310410508889161031b810401c0b04c04080f1248405100d000e0380d00c000100d591164040e42d1400141034407013840d102840380b00d60550002106400d40190f101c00300003010030200300388d4034000c0000d600e02064519294101d03d04181034040d4060500010740780920250342e200a10000159003820689102041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 770372491 1250 770371241 770371243
    0x1020901090504180f1b0626040309090204061110110f03070507020d05060604050c0a021902040f151401020a03121a12010902191d041e06090b310302 66
    0x6840c07005d03043d183c0c3c1030604404c009940389501c2501d10040c04104400ea10345200b2144c442c82c102c000310406c079640180c07440c004d101d1400d07560024440e06000001a58842056060740c00c954411804141e6802d114001a10103201c034105c1c286440e001080380085001e845603e07405541039507031900e42c000c000a070829024074120b480c0740f5001800254000b01c1d0346030565903002c044034100c1c0110f0070840850510103403c02500c0040d40c0ba6000f0b80207903400c1d440d810f0419010000c007a81e0003a110881150781c3d4410348901090304541424074044242030040700b007451b44044003030a0441d48600b0560340880d600031000e07071a0314202e940120360300407000d80c907140c02c1450340d02e42503212018105544e19280c0c1513202461a91080d9141010403420221040c1004424030440300150b1814001000c881e008040d02079206210b4508132140e000d0b040f41c103241700c00d200c4004440c070aa48116410900032000302030355100310b110811507045481c00344911000d2a10014129014002020b0b000070540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 770373741 1250 770372491 770372531
    0x80f0d06030203030d0642020a0b0405150c04030305090d0f06060b1308060c1b07030605070f090905060d020111010b040920060406080c13080f0d090801020901090504 73
    0x5001411281c48207501d0300c05030001d0506d80f2071828a182145814081e2249600c0041c5c000c3d070004415031412200307040400300103041e0090890850207001c0246001600f24100035000300d018400402040c0c04d4000f5807494100302030901002000180400c00000b9800003c0b11501c1d01d0541d003030728580441e4a040c1004680245000741b4060409101003480d080e060042c003048185100c600300e060786c0d64130718240c54107420394100d00348000405c201004d818050309200700116041c0d044904160f580c1d241c20003112410f485900002d500001d03547c18540d40484240041c000c08031040113a400d000000540701c00c110301d4028103101d4581d044045c070a030298080b01d250080a44144940781251400c007501808114812102c142500c50310b200500f8000243d9040d1481500c45003600c1e01d03030b120854100d0b0040d44071001a0403041001041105080c08140c1103154a04c00030030205c0501003018100300b0260b00f007001280e01c10300c280c58250781d001d1801e808803441900c000a00e20130050b03010825030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 770374991 1250 770373741 770373743
    0xf030102120907120b0408070807050d0c0501510f030210030603051921030207020301060911040e0a060b0a05070c120b040b130b0c1e07080f0d0603 65
    0x548045000d00d01c00c500528510b204000c03034010f460050b9181c501c100222560034102401d6100040001000651030784000c049903400b40440780e0919119a80d8203207011080441c00c8001a060018181000003d02901040306501039114903400320501002000d502c44c10074000c07811207044040000390355003080c1024292451900030590f185c0b66079006040d1012844120b0040b030340c06505281c00c922038400c4d6000d0780da0000c00f407e40080e0f08800c01400e18500a002d81c0c1f25120b242c50111162007643d22604103003115140940c40d441907004140c01c4030540d6025000309810411215a03001d80c0404490035968020151505070702c95450110041105422155240e0000261200c03a13640100c081d114241c41100200d010320380321700000462070080080100a00c41c4440030400058080e03040360b078020f6001c1040d00000c041da80794110b8120081d20410702c40d079000100c840441880c200182d104482607201d2072725111041c0c0e580c00c498410004d00c00030945002c90343e00500340058002c04019 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 770376241 1250 770374991 770374993
    0x30b0d080d0606020c0d080301170c03190b060306041e050c0901031b140d06020706140a150e0f0c07050a0804030b1801090c0b03060a182003040b150f03 67
    0x1494080541c4008003980d01450015204401c140c100519050680510b03079030380039500a0469181c1050350354005015101070a850161180400c400e48081184207000c49400c240300120f150f2608010645080141c1031318042c0d00f007407042201080f18001c6803901d020090a00c0c2058401c10f0801f1400e200f24000e0060340000314000000c14800c0d901c180200310701d4550808030301140c4c1c42111643c00301001d120641c02185074042d40011403d07507401f0303064080c01481d01041c0203078001400700c0d0101044903021046030f07503091140384600703114ac0b1403009010b2601c04040d841c01c0130090080c9404d0001c00800c08031000045903020060180071100401d036000e50400d46564903882c21241c62501120080c1c20000014403180b02c2c40014015811039642025008190030700b80740722070707000e82c0c801491070341c10039508100001e03860448060140000e030f07a5580000c280a00010201100d943d5400c07014503110f080c41400040f0b032000c0d0003188c002c03000c00d0380e214107160b0142c042010380903010281c540c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 770377491 1250 770376241 770376247
    0x225030206040e0a0b0a06080615040e0703050a0c11071715040602270112090606080f0c03160302090f091516080907230301020705011b080708060d03030b0d08 70
    0x4401400003402c0e015584100081c0104038485c4148501e444003441603070005002c0710b012800500f0501d001030f5009400c2200341e41b410b83c071603462101c003410175144c03500002d84c1c0e8403c10085104500c90783ca203803106868002403040910010703594031071032809040d0f2813154515031600d0402c4100f00ca01c03c0401c010401f41214a030500b0050025003119a2003084e01d0511a203819400b032107109030301d0a00c2c030140c480c00c0300e8024a0617400d0007040b03500e004503896644c0d5400811190810011403d240c4500c100411080007410181400d20340d60000c6088020000c12040c0010390340c050141d5440452a41800b41560340ca488180c40e2850b00244501503949002c1801003818007000c40718201200c80e11001c2203a01c90024803542c4000520406084507951203442c0c5c82c080c440a024600c84000400140c00c120058a6880c01c442e0101c242c030300075030441c040048500e900100050352000ea1810a82400e1030320002051030340d05912001002c16540f0400200d069030fa001d0286030b940e0b00f1080f6113031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 770378741 1250 770377491 770377499
    0x40e030a0e0f041b08090309010f0f020a21030e030f1b120a03050132060a1107080d12060305030711030316080405010e121510030b100f080d022503020604 68
    0x44c1a01503400000010013400c00244200c20000480300a4281a943c0880d5081714803c2142c504103884154000c50254107106804900001500000382e54042c03204903000388042d9018048442d444429900c5802c00d00540c0300402d40c80b000c1d15904040e2060700c8100c80c0300d9504680c107003a0140e01c1440219400328184042692645c007403416607034880c25501c602ca042c036014040c490284005504000d0310003485040c18100b0101505c0c42c8850360070722241070045c2410b402e091488a81183c0402d500c4540c882d50b80700d521000340001d10780104010081c2c9030031364403030544920800c0d0303001d0f08400f6070ba860321210340c4007001210303400110281030001c6400700e494481100c0d440392003402d0004503840000b000500d016040300342488500002032800600060100d003540c039006010b94a065003014000010a40754032039140304800241080810b50708022038180c0000e07840d000340705150300424940b116590000781c030b01d20302103a400c14210500080c0f00d01c819442c0c001d8000035041070001c58005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 770379991 1250 770378741 770378771
    0x90103022b0c140f091303031a09090d020c0d05101508100606080703181205121f0b091305090f0a0b040b010e0417070627020906040e030a0e0f04 64
    0x14800c11802c6a100c59940e4134a0108400700794191240ba03101c201c8403a43d04c0c000380c00f81d030000d64803464411801315148001400100d42150454801101e9088080328401a950500003a1104041181e40c41241c4105455003961502c0030b1458210b1199220b0648800180810400700204540800c48041401380304000002d42010312801c404500480d001c968054082c0c0580402c000c0d0b940a6a0441001a1100c1d41c0602d8400400d00c1400070400c0344510311614544210707c210300c04080d481c00300000c000b004c5c0c000149a404850a60014010f00d0702c0b5944071480d2041410740b104021625844005105080102003241e4050318858010000c0422035520021072041740555804070480c0c1c3e0b11006401c0c0600201c400604000c95181300e0180b9802c4c04028000980c00b0b1140043d91080c456044102c06070002901c5103642a10310120701145807802e24150b0114007650141f143d16040701d00503950380100e031900000d000c2508040b0140b51031f44c019030004d03101c00900502c10004c007800d81c0b17 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 770381241 1250 770379991 770380019
    0xc06050414060702070602030901201203010f15050d02070212030c070810050106051219060b090f010c0b27010c03020a12020903070e0c0706050c09030c090103022b0c 73
    0x741089000e0940003c0e0424004a85003044950303c0c2c000e54603000f440c600444a042500f1000714603451489941800301c50208600702000890000c940d590f541041015a4440c16941c00b6540311009290255103003a03000d804d40b580207a540c4005615040d640c40040c0740109000b42d80e514030f2102044240800f0b0001034203900702c1d001003080c2c403000440794403400d00740c0b0300c24051280414000c201c4120211182d1048942c081284080008641c60307442a030400e881c072940c00304c0c0b0090004640ca00b03840c64000c0d10305035940000d08085244c207025030346d00602c9103402062247c3ca010705000705207a085050501c200e0f0401040001c00c12004100ba010f00203421000300700d0b001030a151001003002001c0d2007200c5200c41c0083c02400b1a501c0d000030440220402400c0c404060020700122001402601445006040c02e0319000d0b02c41c04010103041c54402c034462902d1242d00300743d0042000d81c583c10507200c44c0c1ca2824000a01c900c1c45610081403400f103680d00201040c3d40c49800044202d043c04070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 770382491 1250 770381241 770381273
    0x190f0b090307320f0a03050304140601080c0f01170a051e090312010806190c05091f020111040e0103080315090f1f0b09040f060b0c01051f06120c0c060504 68
    0x405408090003003005664a140d00364001e011781c4002110000b180c0154051035220784910146a408605500c0040c100034080c2d200322420340c0540040c0d90b42c5d1a0016038500c920307000786000c1d185000741010104048102501c40940d40c3e540704041501e0b00c0d00352601e80300d4002c4580440e00e0728107210441a5036070b03004480ca041c0000128001044003200030030081e015800940100c1d4503803032410020f5005000f801c0452060240400c00d0f0601ca85440d50301c07000c1285429140401948d0424000c0d0a4404c1c0e01160303409090100000e11040c4018a1070342d0540307030800003582e12503a80c4806502607920800350282c3c05250305040014401a0205584c072908410b100d120700c2d4016501302110044050040500100003402881c2e8070781499808212150845074011403101c2e03a46160b040342d90b202905150441e5103d400704548030b0a84e403a46071141059072080310f1154a805401419207c1061403070b100161643c6044003200c0c031031201c141c070040d04240100004d0616181c980302e0341c64a504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 770383741 1250 770382491 770382563
    0x19090303020f1c0608030c1b040902180a060623090402070c0b070309050103090b13031211090406050a030209010b0a050f030106050702011706091b0c030301060f02190f0b090307 78
    0x380440d01781004004c1c0c86401c2d400710b00600000e000d012601000c8402c003070021350420b80d11101d040141c1c0d039103480c041d100c1f01900f503203a50ba03003030a80800c0c0941d07001e40c00080a0040d000c0220320800c80351085038001c181c400d420b1319280c1d881c520000700a40302c0e40728003030602c1181c1e403804940300f0441c4005100c054443c1d21540000380d070340d00054040e500c0a40001c2c29030702c1c030000001c1c040c400c160b8032048181d20a00d400b00e21700b408003032800115441810800305400011030b4000160070540f0030180a024100c0d4034064403403a550025440d407030140a0480c01c1d12000c0b8108008501440a40d8190760404482c2d030385a40e120b03403005159801104040c2d002a941d03000418640c100040150301954018043e03689642d9601000c02a545004550300028501000203074007500b822b10103940602000ea0702d800c2002031014000b03107030608042d000e24414001c44100c80001300e5a003007040720640c1c41210b0480941d01c2c030342500d09501840f1800350280740d046005450000e001050020b00c019610 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 770384991 1250 770383741 770383751
    0x703180b06011409060d3e0306012001050603070509060d08160602070b060a0909050c100c0c1401110303011508040212010c0c030818030d1a1e01021519090303020f1c 73
    0x80350283c6846442c7c211101a001e0f5581d104170200004540c03110040c10401da607030f903010486100003000c440d10b444082c0d5403102445030a00d410b01c40c0000a060840390040e850800c200011054906610700828250001420110481040340c18440311500300004644400c05070600d0181004125030fa0f502c543c1800001040354030f070a2152005982e080b0000b40348050b40c44007803141002d80040c4040c1444a101d00ca00e0000d03000307030b424a0103401c1c0706c420124080200400540b1844080701e4030007054200b480148184620800340c10150030703081c6008031068039a4001304030684800c2103070300c0303065007012070301c2c1c0c52150007809066855109980e43c00465030340451903c45110410035189854004002a0742c820560303030401241c814041c0308500300310303442c0000150104289500c2d00c0f80b8a03c030003188019581c050100c1c207418107598849100c54944803c5000c004840403c04a1030281e9502d0f2070305c207052107036060780d00e100d14406441e5130b81c6042044142140040184540e0014108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 770386241 1250 770384991 770385041
    0xf0f0c061704084f0e041520030f090d02030a140906090402040f181a221802041113030803040f0203150703180b06011409060d 56
    0x58106503200b95040401641061013400044000c000651041d10300401c03000d82c01e030700b080500e080300304602050310000c144644006a40848114096002c80d41e41c001c0b8004210206905040c001c101e0070345030700c0c006840b0740c440719078540f0138100704200120110040300f0001d2003402140480e00404001c82100c002418000049940e84150345080c000140340c070001e840a0b008400107810550030090045003000090800b203400c03a0400e60201c510028000010082e030a0b00701d510034640d860f07400c428861049542800104841103101d1603001d0200340049042c40c070445601002d10f50305a920900c030117140600c4010002d000f03000280d100b24540781d60280d1800c1450211800807540003512101c07280745449140c1190801082030710303950080100724005a40500201c00320b1012038031030100c14207040380700a08580d0702607250044c0c1658564a04003040020864980c01002460a040c0344130350315240300c03101e00403034000c00d8110700040303107200d4a41d0094000d84d038034142d002442c0c00b4003800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 770387491 1250 770386241 770386277
    0xc0d020f16060e0d021e12130e010b07050619391d0d0c09020d1509021201090509190c080609060c030106030f18030c1401110f070f0f0c06 61
    0x641c0d40304c400359020000a10050b600c07481c0d03501c190340740c010544d440c0341c601036100310003a030000140e04490111064107201140000e840c040c0076010070b0001070300300b22407a601e2513903460028103129945110340d40c2d144110400e603008003e0f01c04540400e118200d80404485039540c1c4070a0740148440c0005101190762881070f500d0004160340c40e8065800c603004202804038400c158402924041070310680401c5d40e0200340000c01c129405400c1c0005d00c505c100381c0241070502250454454540100240c82815036015002030550342d00031000107054030f51281003490045480001c0c0e1141f6101280502400350a1100c0022940980c0c00d0710007030340c3c0315610710341c035244100d0311200418003d10052003514402e500c4489883c40084000410002d0000b5502d40311aa81c40c0407800034440c0c0782c11808200c8100b1540c3c0d046081e0200900218810a4012503071b4000c0c111001c82250010a04000b1b0200d8000c08200c01d9401122258281185041c0f11036884000d02030f0002150901a8140800503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 770388741 1250 770387491 770387503
    0x1c0c0302060a0509070e010303050306010207140d020f0a09090308011701090302190501020d020f030916050a0b130e0915011d010302190e0a0b03060603150c0d020f16060e 75
    0x251640c05422030307945001416000f401c020302143c2480c400e0600201d801c0020480c00c41c0658002e80300c4540700e14140000910701940d50700042480000c4424008079501c5100c070a407107966045880c68115035140003c1108880e07554418900d90303041a1704801416080004681039401003820b002411102600c000d00b41c409400000700140c0c0242d5a60899180e01c03410300180c18410b40016140070301081201d41660030074005e4004224000050002104082223030000190720520003684480c54103000606600e40da10940b000840c0003d185040c42400306560000381002e508620032900f04648401e035070300e280c408428005580f450010400341c10181d0720021416804541007041ea084d0303403d000449041d0042308480f02d089001c0032817612080005a44030340c4081d500014241d221404140c83c02902070f00c018002e80100f0304108041c8da45c0c0c0c54a80d44020344407005580c0302c2e000c00c00c4000034450700301c060709215004214281500c070805202048e89026a00604c42802140d880c1900e80e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 770389991 1250 770388741 770388743
    0x7120c0203040f0627060c020f091b0703031410240203090f0a05030d030b130e0718021207020642010c05011112060306060d02012715020d110a08180409051c0c 70
    0x2c0324000c8020bd070f0420042410324864607020808209100080c4e01050007070f58015a81040300e2024441080000b035200244424107400c0a021101d200c806900d0744030f510001c0b40181c01032004802680c80e801000d00051502030b00315580000011001401040c51790481072143e90f00344803040150010307002c0c00011861440141035002e01d0441c9c4412030400d440340c0d1502c9580c0a20405c0302d0001d000318400c3c825007094000d0503491074084252550030f4507808a1540e5000e0f0761290b2603441101d10007410b001000840324100c41d400d80030040c0c030310412509000340550b0a105003c24249101d202801d04042204025003107a12050101070b140c2034104c031540d40007460000071a016600c038958804902041400030503590300c0010782c43d01201600d030420100c500109207034515055040125450448407890000e000544007181039440340d115910192004101041c01c030501c200100c02000d584100130002c00c603000262070030369181c80d068403d02243c42c0903c1c0076403013035900440b01d0184603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 770391241 1250 770389991 770390011
    0x7080706050904050a0e01050a1d0102210a150b0703021b030a0f0809030304090207020f04060b04090c2a0606090c1704081207120c0203040f0627060c020f09 69
    0x445610028000107103002002003110706d48555103149441020310940703001d024101000b14021700585842c110401d4500448505a8410098444460b42a100c0c01254044200318500140c84109526001c1c10840c90042c142034010f190010324a1855001008002d221f42c0941c0c1d800005500072809550400c1c480b0380c0c00d60424582c00380012503100214021510825290b414908a0b4001c6071450b0032580100801c554000f07200740552802c9055940040d408a80900500d8240001c7c540c06015a102d188461926010042d00c0d1901529840104207480e1817407508105080c00b81a24141940c1016100903141c05c201080c801c0140c02070400c20b0711541c80d0700c80c15120050480100342d20040050310a044140300c0510414010751050780076001658900441180a040c03000c1181c80c407541c070000f90b5008010800401c01a90b8544003110a0307030a00ca03245402144235940d40c0d200421101105110362000400c02a421808401000340280c80030302c01c440021050011804081d5410703000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 770392491 1250 770391241 770391247
    0x90607050708390d17060109030b100306050c04051009061409060408010f02270906060702031510150309082514010b131803080702070b030a0e0708070605 68
    0x1240038042c0501a034003590000d1440f9028608204030304582c4510728845242c1001c00c0b014220380e03010705140445c50f02800d01e0035003401c183d00041c2903070350316210043c24686e000c400551401044000f4100858104105000d50b02d0a40e42101807580203006e143e2055051030108c8503c20f100308588006d803090340d180c024103131032494005015a0071039182c49510020410020581903020b000f0070000e0b000d4441e01580340e0000d800041d861480300800c1e0600784240e28040d40300d968481c0000f41c0c0040081c0d600c10ba17100302a00201c0d04040c0e080110b44912100320090020511040214400f11034427482c0704c04000940340005c80503038414000141802005018640104c9821481242e41c4202c0c007411140d100807613070742d40d19503031500142010070765503030240c6482904019800c0d101c080d403048e500304101d601e110311035400c140b480c40f400f80811820500154a0b01d008001060282c281c844480340c0720b10707007225000f01410050f003006026000c0c182c0b001a0030040054a00c041e070f07c1070f032100d0382 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 770393741 1250 770392491 770392507
    0x150c0f011b030b152b151707031704050a0626060409020d0311010b0f030c0909030c0d09150c03050d0c02030d1406040608030306151e07030c03090e15011202070c0806090607050708 79
    0x14081400c03011512003401508c00000010701e41c00300355056080c0080b52140c4036480e08080180301342499102205001e001035a8990b080240410500c00c00300402800030a62684c001180c024a00484001d4000701c900b40c24105060f0048800c07400b42c41e40c0e8009004048c0740105001543c4100030302103401d5032014800010924145000c0c0740d2101d00d01c0226410b25100020041c0341c52000709003100814059101846400000b060000500e011801e0820965440c1d6500a1882c4205280780d07508035030307030680e60410620070300c2141d074940c0d1401c0c0706201c480c030001c0064080030800e540051041c0e240400c0007a038200040705980c0b00e0800209001c25504200d0304006041d448005008640c4891051009a5032101030280030914020758503040320008a140280c0b2103941504002a8008a4400c10150047c9404903c00305082880c00d0184901c80c034800c07802034041c82900400501c1034901c08a412540052070744e01c600589800c0302d1007a02c480405481c0303440384038400360940d142004507071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 770394991 1250 770393741 770393759
    0x1e06070803060d0209010e09121206041e02031005131b0f11070b0d0b09310b090105101406040302040c0e150c0f011b030b152b15 57
    0x59440400600748088440c0c044c4d00003612040300b604209484098401072089100c020000b000758024809552440d100e901001003420090090407030748a5600d540c0862032007031400e002c2d11a08104113605648900700a80e1b9a0110300042c024280910817030034480e00218494007564801d04001c80400a554640e0300c400c84500076980c41d904240501c808510b403901d0010030103400184092070321581c40e5541d0646900a440e04092050302c0360140c0424080102d614020500032400358a901c0e2004194120180c28254842070300076191519120400c07420080c103401451061a1808802c0426034940c000840d10007030a541c0117404c02400d000900040c1425802501c50103a24144506801207240c00550307042c01c440500719079850003103802501d2103070806c220b80003464807170003e01501c80300c1d00c41c0020325512032514400b09502c4e150f10303d200b0348401100c0d039041c51300d50310225550000d584140d06840f0368500c41c0d0203c4030f055100310a0100d0680310740780c1508461030340007111f985403c0002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 770396241 1250 770394991 770394997
    0x40c051203040f0303030207030f020d1202180a0909020906060307090306112205030105151e0d050a05060103330903050c10050415140a0e030d050103111e060708 71
    0x6489148001c00022600f02401c5000e04010742c40f99074056035841140c68000c1400300540807030002c2d035010198425003941c12a221003000d148104006840e030a046020100c4003841e0142c0d240c011201c98008900401e882d0071085071a4001c0c0d429420300d442c9d44051004074402100c07108005410608103100040aa400c003c2400c0400056a42884031140380900844401c501060309003840402c01c000d581003e0185580c070003151700381c0180022030400483c81c41c011104101c0c603802d9001c002803005545070400c501540c2d410104480714481c0d42e10b8040e64983c0c0a0000ba14003186a107a18451802c244619000702c509088240710b400d0303180e00881000e00f00b03480c800c07014080244020b401e02030080041c4103400010748800324050500d41806611302900c10310a000d40da04029070046103444029400b40c0041e000100020f000340e8955003036045000703845521070614201000001405501101c08210404c121121601e4482400c946208246040390440c0c0001c0c0500507100410002d41c09 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 770397491 1250 770396241 770396269
    0x50c04120318030816050105060306190207060e190b010b0a120c090333050c0316020f010f0f051302031c170c030106140c0a02100c14010605031005040c05 68
    0x3106103025207075a41c4c92000e030062a046801900e41102500a2003424041c903604034009901400060400c0c0c0310302081c2401440c0c1c400b03050780c3c001480d0400c00c41030381d00222140c3e5141041e03c884030302544c07000e800351100301c405880c510210000810600e03054004c40e40f52819070b403540c0f81d101444132400c20190440c4180c080600078061400004940e8000d0080416000c8110a941c40324501d59242c50201180100b210450301d444200302c2d000740c0300811260080310b40c0120706102b01c51194202e00d400383d020074a6a0369400c006060024450580204a4070a210b400a10681d552404111800b05a60350b0195260f44002401d250004001e41c259401c2c80b03003454442004410b80c0f400c08240c0c1c006456081c00404004010001c03141d100210032006400360782d03603d242c80050158a965941041c0002e0322440124141411490040d0400b01d19182e000c1a10728441155000c021700a09280c801c85001e40039030b1245107581c1032140f0031144901e6220018034151800c0206000550381c40c036070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 770398741 1250 770397491 770397527
    0x130b07170601120e011d070815130f0614070905090402091902040b040f050a0b0c070e1518010303020d21020307170411010e04020406020c010c05010f060f030501050c041203 76
    0x3200011310b800380180c02111070401c81a922000384609000e10301002517010003001d4105440a4a4041d4001c0480d034110f40e2285040c20742c5e0796181030000103280384400013003440d441d01c590b00c0c41d2a1111106184102100d03260400010354980a00007180000c0320025844404403002890b6804196503500c200b403409000103042944940384c14038160b02c075801100f00000f0300c8000308028a024800e04d4094002c990000c3c1c2080105115295914150702882140d0400240000c00460000182104c0054003c00c03803609070400e4030103503038804000e000c150018081d0b0f000b00a4424000ea404a030320b100c00719140ca044048500300c1d00001e40000d05041d00300f12401207880c0403041765101d003078001e0707000d544500e0f081210b1100151020080f01003481c0158014801000015000310304003142d04001e09080000344c082d45841401041d4807001e065025241040124000043d900d840d02542e115030001c10403515000c0480f14580110301c90f4000c00f004611003c80085d11030350046040242d184 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 770399991 1250 770398741 770398751
    0xa0c020c150c1c05040b0705011104090e071a220806010303111917030a06030606180e0106151110060e0411010c03090501110a02030303130b0717060112 67
    0xe9001c9016414501c07220002182208030000180014504909442868080e04400560140076070245101d05240c0c80000300700802840400e400c03100c1781c00442000503540703a8075844454000d04031030801c206503205841010a044a02c4410442080306030304055041001180008501c0903411604004040240200103054141000b40034083c511030388031001031800b0766102e580b40c00c281e040e9601c00b40080303d100301c1c04240e0680d035030300540800c14070850352030366412046000b420580c0c0c80141141c1c0b07400c4000580396040c81465055603142c450a2000500c1401030609998850150010044040300c044100c14040c5c11891081d04040c403c0d04c5040415411074001c840342d60b40401501303003110040008218440c40701d68000d84003424055400d200c20b071030003003200c00c5a000301c0d814810710300746080540e81d04101d03102009070f006048a0b6240f0308120643c21082d903000084030070500f18000302c0c12060140c860103000f0301035494010074555070900111a40010800e510611954032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 770401241 1250 770399991 770400013
    0x50309040e0706020d18092d0e010609060f06030209030a140c0925030c11190c080a050a0204050a0b2107140a031214070c03061109090a0c02 62
    0x5015184074800c400d4040c0400b207152075000303820310380740901c0302080201c9500d058180401c2410010141e031031100000030b120701a802d04013100708104c0c555254295021500d0750740100150080741000c00c03407900074420250b503803000b801540c003140640c0c00080b1032030f0414400d2070f11a0b0301a080016000741140c0c1100d2180c1c441c488460102c000f40780b4a50072041c03990764070382014800207802400c0d0300780740020558508081c0c00c50092071441e50302050b4413081c03400344403480355003054000c0d1911015903001c212004042c1c15100c0788200104c610048510001402401c04500f4000d0030f50414094030004140751f080000404c03000f8581c00d26642d0380c0000f800c3c541c07240c141c402683d20f01c40c908000d6020648841c9440c004141d0f1141c4c654510807000e00e05903445043c0c00c0011682c1c40142c05188403101030042c1c440d1960201003420384040851000144a5003240150440c0d00660301000b10b011580c1031440c0038400c0c40c40d5140c1040c00300c40460b1200c980d40e8490f402e04901e82c0b040d80e10907860 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 770402491 1250 770401241 770401249
    0xd0b0702030708131a0703051e0408030d1401060207030c0b301905090a0809060d0507020a03030b031b2202030916080c0f01140412060915150b07050309 67
    0x1032800c441c0a03101c083c07030600c01c0c170300c3c480300c0e80506241102841d4285009a50020007500c20000511040300b4803e00071240403403010107850142c03042c0c0042e80d40b107a4030300300400003e001014421490001c02800042c50f10700100d40642940e0700450782a545604003881189254001d80e40e0544040d0b00e400891040302444030311018030007401d070001e5282c0c10301402e81119803170501c514590702450001802000c9000242156809921820441c1c65495a0000800134010039500520701070810040000c0c0680c00705050880138070030b07101000030070049403c0c1590703406804c0c08061400101c0c1190b8406140051008007034407001c09220f8209504c10b003000f0240c0c0c1060755510784650189100e1032461103054521300c0030f4038218004040440c224000109220b03600901c40d070520002e070321030420f0180d590048070050500c00c128074804440d00d1070b002005200d20f04007030380c4c05440c1e28416070303103400e450003100306002070540301c0c2180030300f05070b035000d00790303100c017400311400d210402c0012001c1d12 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 770403741 1250 770402491 770402497
    0x60f050d0606050408061e070318080a090e010e0f0a0b0301090204060323030c03090d02030a060501062607080703111309020403020a121a13050f1605030c0d0b0702030708 75
    0xb4550b900e01d5103aa10309021189441c4000c0c02480c40d01c3c0da03441c208805052220304840e84407801d440c0209071804c560780d00000c01e1403901b0016081050025101428a4100c84802c0481c3c1c40d149585226a0381c9810075428141c090394011110b10644c404901502c1c842d400c40c003010f07140100009406502c0303500003401c48006030703c1101c10005e10442004401303000d00210034001c60314000755240c8154104626100d01c550045c582c4100d404108201c01d6440404c00c1c00404e88e4010313001c1205585a90340a0800c0c1c80071000c0000b4101110020681c07084001042d500903455031319910081d1715440e2040c0c01410140c00e5810030180c040c0051034500c0e100c812a0402000703d01c1c001a904ca0550043c450149910b40001c080f00100c800d103040020281515000c50701c0c81382c40e0a803c10740303816400f0802c0d00c00380b402c06041d42c4510014010b0704200800c690410440304040c0d0001d603135480051644440c2c2a01e01c8640c412920301c52400032031920a070243d408140340c81034a15107801640c60b810340350 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 770404991 1250 770403741 770403749
    0x90611191a0a0c0e040e030337050108010f020405031504170a080a0e0106080a1b030f1202011a030a0b1806040c06090b070b0c0702030a1212140105010207060f050d06 73
    0xd8030b801c010002d19070403884203098444140c0c0d0600411b80028101c540c0c078031008e8100305c103000d1625098090345050824070307951010486c48011030001c0c0110443c0c0906000e0244916a5103000208010250644200c0f001c40b030002d40a09403141070019070a000180003013050b500c0c6401c2c1c0011902030017010000f0000081e150f01c0300c40c8a410300c00486021101c1c1a614507495a00d000014881660700042c404030303156110000380f4490510301c00807149010f0560006003400c03174120003001000900100003c0178030280d4000c00190f0307090309a081e90803105481d40744c1c0540240500e2008a13020303400c0c035079000782494103645450105405407850100f00710f80a9074180e29240c402e000c0c079540550041c0042c02c00b25240740c1842d01c90b407500400428003a042654000c00080d0080454809018400c502ca4002c040c0600000031824080d2062003c80c0300915030903d05031501c8140140c60002d907040c0c03401a402814050304003041940d9548500c080c0381c00784081445a48031611311409294090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 770406241 1250 770404991 770405011
    0x9050708070303122d0f060b120a09020112110723070605030c0414010e1e040608030408121b0601180c020a170d02040b0f040303090611191a 62
    0x20300d50f0400426101d8a0102030354500d00300a1040e510340e0110a003a600800340700c441d078413009680d00c580c1e8002c03d82100c114505c682000340c0003e0701d0182c04050030344001c4000711040260380e00d048100c00c448420078004c1c003041c0207980d60600864550700842c00c01207450341a178680341d0b00342c4400906410b503290103590030004c0104894440000c1c00079000400c0a414034074214149501244201d000301c0c007032094601740340600071405070301c0f80404010300720020308200e00e452054451040042c1c003201d18180560700305400050449000000c8404444890010b420004200034101501f94001c401813060840500007042007640140001030081100c03100098054550f200e401e01910080030022043d50020400300020681c04103c940340c0228a0380005d030b81d845040c116000901403500041c1808c2004195000a022000010b0007030320f0003602d5103100c990b6070741c0c0c0842d28048038458072103083d0007110012065102d1007401d50380480c0b0441c4140100525909100d000c0038040790001c020b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 770407491 1250 770406241 770406253
    0x4060f0501020d021c0c030521041130010209150c010f11030601080901180f0b0c160f1a04050c040e030c0d1b06060605070b1311060a0309050708 64
    0xe0750380400808070480d146001402d52000f44040188038140c400c00d0030f4041c402080a504c0406124404480050006080c02d084105244602c000c013008115000c03101900d01c050000d2844c544000780001c03000120100401c3c07840071310381000c0382c2c4881c0c4a41c0002ca41d024003002e04955108204086100b040c104960b440d0300c02c6100305030a44010150214400d4540700241814a0703024007141d40c00b890a081603030481d151960035900400d00140b18540da9080944030b8801c02c00c007191036054180c040c41403500943c5900410f4142840b0b80032102c4d80854040e40010009100c1c02c48110450b4059007202d22103528080d00130503211811142202c01d43c01c000c3c03141040c2d14091140c078801d440b00030001c50821940d01c0b207a95640d84d203200c203442408200d580c4080b00082e800d4034200c0da5544032034180101c42d81d410f409860740d04a00c2c411602040007000103688207403074070120003500fa084041c46058903492001d200703541e88400d89001c01c1540b5100c920700407910800080d00202a424020b04c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 770408741 1250 770407491 770407499
    0x8030c074b0b0a080402061308011104090e010b0a1e0302061b150121050a020d0602190206271015080f0c03031806040f0609060f0f020718090204060f 66
    0x48507907442e0021200030206009040070150701c580d041c1da1007507040d46c0103561b503040d40017140c11482c480d42c0900901e6003000e80a221500005010303100710b80c40f5140a00848482a2030b00e07007a501080751154101c03541000070082c0304044100000301400c0048000342c1d07540c494020503030304c2e0b0207481c0e0000303070482d1100c5c68041030a04011581c45c5418034018100c00d0350401c6888041a4889a4960143c0703910001d04010b0010901c050756401e5401825420308541ca4038004001e07400c894000914076035803003490500d650002c80d465104040a4080b01c00c1c03003500011046502c101403540d020302c0d200c0d0b0302010b40d00e14490300c0755800301d18109000c0e1191919221459191030b055050342d05d040c0c0c106081b40245520004151049444102c12400004220602203481400f41e98040030b0b142810700350000d038190b0052003900c103031803083c3d6a103d800410a84240c0e01c40c0c07034400040c00103a110340700410601c0c841c584484440c01098502142950007600010140c550b90b4020400840d00600100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 770409991 1250 770408741 770408879
    0x21080d14070905010e1e06040b03011508070c1205071502030414011107030903060b04180b0603060c04032a18050a0c080907030809010c0c060305070908030c07 70
    0x500808007403810104400c0308034081030290382040e0380481106c6842030300384900e540741010303500645001c0045607100e6a4414000620b45681034003000820120310100e480fa52203a4a0310f902c0c83e802281510403a103805004a030190b202c43c4042d078622001c02514031000d030f6180003c500460080d81c0401052042403015421a81c0103034000107009805c000030400a500140c10380100da4020600190703241a140200d000703480d6021900001c440e0560f00726081081c104691400b0740707401c0d01240e03010f507100d1a000501d44254000a451040d05400c4201480f0541a6280e141e1003c0400c3c40d04007036481c14510700e0040304001d4510116191700c104200102c07144140401e0510746e01e041c0c20181004200661120500e000250604d0740001d03141195034090080003619031307030000e8507810455442e440100241001d543c0080010300c3c0900003d050302c000025659203c01d00c070b0240ca4481d00e0140b42e032a0022105490070088200620441e000d0320707991550901100c01c4d0b03000030241002c1c1107109 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 770411241 1250 770409991 770410007
    0x8090915130b22150611010510060c0204090201021509070e060a1428030c050405090d08070c020d05070303050a09060c050a06020a0c0f03030f110421080d1407 70
    0x41620701c0e041c00c202d100e548214101c462204550f01294152002110001c0981039201c400440000c48031070001d496540040303030706a0712082800070816074a1301d1009124585c1c09108690003c3c54088070140503143c03550252030511302c140101d4080340c2e1002680c1e0708150040b02c070308520390000001040445016003487d94094412100828070707a043c650302c10781e00034030100c0b981e014814409070380c1c0c004003019815141c0e100e070010b03c041045070342e03180042c0000c3c05402031501440c00d200209a901e107000494a51070394072605d640d11303142e0711450201c1e40044078a0080c0e074001c03c09170031039010480600201c00030754040c1d03a840381c1c7c034030031210054801c05055000d0f000700b0141e4070745c0d507010500105090420f507a2001000d070355460102c400b00c80380c040c2c8050103094200d0782c0542071700301900342c2d002d5007004131420014000035055010002e8680918410001d01d8044414a4140d40c042c500610480ba07101f020424181100040c45108031899608034184a100d5941484800d0b500000c0c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 770412491 1250 770411241 770411269
    0x4020f272d01030209013c060306080303070c020405060112021306031b120b01110f0a0c09090f26070b0f1308090f0a08030a090302093108090915 64
    0x40c01c200d030b51440e408a02d442505201c1c000b0f8000d81c040100048000e0100700c1c4081c01e02035850003545007062052809041203070f00c41d0b407001c20b14210001990b004013006803440307540151200c00b86055103030240400f906c0002c20141c10481c108909009064141c8041c0044091444220020b2410a803000d42166000360b08917006000e040d80d50894540e000b0941059460880e0022a12100741d6006890302036007a4800b030b4080c000d00783c1e0041d034604000386042c4c1c054014886402c0d929035032800102120498030b03000e02407144016180010a86420031107500704440c0c0f800f07c0d5420340e8484010040c0d00508030032103100d10b000d0113126170001c0003200260001c070000c50a82403601c49a86031100c6104400c1c00e1805020000b500c104c0079500c0300c075540e00400c0c02c40d040d070303a03651413808008125400780d000c12841140c203980801e01c680300c50000380308440301501e040c0c4081b0601c0c20460f61500101c83d000c48158004002004483d2a0004064099141e490a10582d00b1090007000102020440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 770413741 1250 770412491 770412571
    0x1412072321030a0e0f15070c0b0a30060f080c010f0e012f010f060f0501020303010b03180304141807140a030e061f090504020f27 57
    0x39100501d1101000315000300149007400f420302c10341c1c0307000b04103098401c0d00320756840065a07100800c41e440720b0000b00703481e5102c0d80ca80300b601078841500040c540101c000a40002d484030b801c84010350503441d220701c1e1046100e4100c210122010128009890590b000f4241c0391007501010002c400c0d04101c2c113003105409007440c240c0c0f1841c01100810619480403698104045050600511070503e00b825034241c080c5200c1005150030150703094040e200c014524040549400c00000301b1000c0c4041c40401d5800c160b0145181d0391074000e02000680025212034200c10202c1c90640400000308002c000078900e910200401c6c0e0091010070012411500e054900340455000304001e082d03022103102c0b01004c203601080d88500104004a0007400c4590800b00180324210030b100302c240c52100d1881c400c0c0e91400d02e0403145078841c948107054850a4500030b41281c944000c81040b0b19100038000310b59081c0c850b00c5c14804c008007030f400f100315509a403810300e940d030030440b4070346400c01c04203000300d04c0741501d2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 770414991 1250 770413741 770413789
    0x801051305100b010c08032707050a05011403041b120f06052d09010e0307111906080a020708090916090f0b16020a0510020d0801060914120723 63
    0xb80c240117a452000300500c0000000580d02c00004001e0051281d410b021040303100074400c00c141e524002070082071710a607000d17803000880b584541c0b054280004005941070641d11580e8516006d4400b01d4400c030f442406007503001c10082c08510251a4007405450315146450460600004480c0058462482c0340c3d0500d40040141541259901c6c1e00b90315804c0200256807401c40090044c00c4000807011140400262041407041e45600b011025600b11002104000c91003402d241550561245201043c80803000800744006507014000e01c03402481e0b514984054640010b00949086425005140c051032400c81d2055000e40984083c00144046601440c00d00e05809064000c400c03010717615a801c1d544007001c548410b00d070103004000c003070040c040341c80000320041d45136011045050001442100005102d07886108100200e03154801c0842c1440a41400c2c01041101848161400d11600800041c401100c00369000601a90b50440142c50305401c20070107005281286e0140120380c1c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 770416241 1250 770414991 770415011
    0x715060b07020f0f060f0412020f0f100c080d05010608192f1b030307030e010207020108011503140c0a09090e070e090f0a060903030e0a0803010b13080105130510 71
    0x3002901400c031080311302407105091400040c0d007911646848004943d030200c3c0010f0780144401403205114030865160f40008105024401610b454400e1076611400302214814910701411010b98102e010ba80000d15000c103d1000c41d003500c0e02a40a0344c0000d06440c208000c034141c00700070b54510801c010b41072107200c034099461030902c000ca543c040c01d06982e040080725a07400d406c085590f844042d4000c50501c1000b0410282c50360001c444d8480484d04200c48807070851410301c00c84030115416111091141d00f459640c040340f1141c0400c0806042d1349030b00f5504100c22544c000d52040c00d40101682d038400140d42c1c002d04204080e4003079841c1d03a050030410040b4a402103080c0b42a6a03148480c00659a55541103615200c6194100705a85c0942e20205080c0b101542001101c1c030b0007a141400310039104020340c0d60354541a117015002c440c0510040c02410101801003082211003183c4141175601c5030760301070841d2419201c1b0320003890307000c0320711041110030300c00d02e41e07100f440f80c5080100e07201d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 770417491 1250 770416241 770416249
    0x306060d080406030b060c011b0f081b0c100e1b1504050909160608040c050906100807110f25060507030c030909020a12050901090201170901110715060b0702 69
    0x2d14094101459215000c640c0d541d1500001d468202441c00b000303000020600e11402c404c6c40e034000e003110002d4203103000d040016008110360ba0044c40c004246191502c01c46002e41c100381c1010944d90103500504010b012168402c2c025070501c0d5207250040c000c0315a0f00a4584d0031031404501c1c090113085d21210b80305844d962541600e00f210301c1520503483c1c0c1c6d82c45d6104141009c00f40c881e42d1500203034800780072840d035a1241990780301d94411292581c410ba00d078002c1002420303080300c401d42e1042440303c001d20014403d40c0c0c0300d6000906400d100600049464076641820544a0b0f0018182e22142826003031110f4640d4488000040f142c9002c603050404070700130081e209611010313091121003050441091b02c1030207200020301c0e014008548500c1482002011099046000122581814041400319206219451800354161103031050308131100b0300100d913600010504c0c11036540e91035100303007203e580d4801440014854414058180081e040d400d04449180d004100102c00c00d220030801030312 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 770418741 1250 770417491 770417497
    0xd0e0c10141206180907050307061e0e040b0303280c030c08030705040b030c03070908060105030309040506030c0307081c0c1109091c030e010e1506060309010605150304020306060d08 80
    0x10240c44040c0941e030301c9020503015a1028101d881004d0076604002c500301d8041103007015648100e0550782c0095940d14200c0d42e0078200d80340c41081041c10110b400b9040d0045201c4150705001400c0454904c0203207001038110340055101504035003140c07040c803400c075070301456400d45c0c8041402e142c06e001c400b54030002c0c000544024001c2185400001203031180d070089066400074420940396540d40e00e0000c405189a400544000e004103400000209904e00702040c440d040c0e0f80050300a6060101000400020b0000600b85580600071203001000b29101880445c020b40780280003040d414403050b115100c941c030700c1a950fa0820501c0304041c030020350b164030301030000003040300c0303034a400d03201c419185043c0b028020400b00e40505404402203056010b41004103400c2103400200200101e54071b501c0d80320842c21100ea0000350002002038114941000a190007041c0940000791040e149c8000c90340c16088030504020081c0c0200411003103250810559902c8503054a2012500450366642a8940 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 770419991 1250 770418741 770418757
    0x6090b1804080f03090c0604090b0f041a10031103040302070512030306030d032a020c0102150c0708310905010b07030f0f02010e2a01090311090c0d0e0c1014 69
    0x740c000400300d2507134002040000c00e0100001d0449580e20791b00e04140b40101310f807207011800b4a80020481cbc0c4145000e200f6a0101011640c038903a10708880b0003040f805070078000540e001d06564403004100030780c004010b107101da80719400500507141400104050b040b04018845910360040041003c140c6010880c1c040400311404c1c085004800341c0b0800301c990000c03110f0b40c114900c10341e1804407039a5000030001c500300002e80179204504080450b241360844d0813100422080c008010320720000d11004000c0980c110652580319198032200c240c50311421100d040c0c1541d00740309010504c1190b2003880f62500400c3c201080c43d107003603010f54014102d04d482c068003009202d080104100214001e41100341c02da803100080d501e055081c00348444003903a0000d08100f0682d0700c503000c0c4440794090007105007629000705c030440303903105034030200034040d8402800a03500c40c0003400304416942c3d40d4007407a50b44020450207412051004824882c501c081c0120540c20070014500302d10383c1c81010002c4981c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 770421241 1250 770419991 770420017
    0x140a0c020913081303060c090e010314150702100b090601020a0303090501180812070e06040b281d030c011d0a03080c070f06050406080a1d0106090b180408 68
    0x2a5602c2d08003041c6815250740240c0041400906a8228007400d80340006492141c441046482c1c5001001c5400f0140c03405060f062418141c01800462400d81721588400a80c0c401c8500050905a00c45440d21081d00c502e000350740b0481b45c40030610120b0080c0c000d0081c1c15601c140c40c0d8a05480001c1d552400b999010303080c5582c842c030400c24042d0039040360039490300e9844103183c0c1000030b2405517990f81c06005801600131002c070102e20446c1c800d504000700d0384c400511107402d050034403001c1841a40101c40161400c2070051560464945000215102038110389500606104c5280c00542038210180311034031907040042041820380c1c11081407a10307841074244c080180c01c10b09000c20780885003500080c09004c1d0110301401c0d05213000406009036800c210502c522950341e800c0964450050740034100c046548a00013501c182100d6001070300f8090701c070300750b40202e00c001480e41d800c5442c0340d088403501540b110004800b50405000109204c00c40710f002d0001444d080e12220402d009080b81c0d4512 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 770422491 1250 770421241 770421259
    0xd11040b0d02040c050d0b0d0c03020105030919140607090506180102072607060822061503080c010605010c0c0e0417040e24240705030309060106140a0c02 68
    0x5607100c640101162550140040001c900c00c8907024100390003002d1400d94903818500101242d00381501d005000c5588003a02c4030340141568010348240d0802000260035106295078000500c0c0140b00118216001e50b10004185540580072402c209004102000303100044038100243e03110602210b80b0b4010310060038410080040040381000e485500810f003c012200310003c80a6200c100c010a00b012441110103031541c41005452022080f1243c3c440880221184100b0080100840c100c07a481903800264140e03c410410030007040e43d4105a84c5900c001c151914200d500b4070034140600780074201000300321044e076943c15031200b150040740d102c21480000b090130080420f0b14071400750b030420107480c0c403140c581d03d0840405408a80d200b180c1c14009000c1c201c0020500c810400201c00503010040240f00000ca201d44841c0d110750307400c0001d0701000541c01160017400030350700461004028100651501038000c0c80a00e4080c40d80300d41c0c1100700007005030150062203641c070841e4181c1e14044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 770423741 1250 770422491 770422511
    0x501050f04080f0f0114040b0402090402121b120106030b19180f05120f0327010903020606030f030901051c020d020f0a17090307141023060d1104 64
    0x140a41e03840b10701184500341d1a40316024012a403941440705540007001000f00480c06e034050324100b520054840702d006000f0a000d810900e004603803083c000f5009213582d0010302505c03403400001c0c1c030f04c008654a01d0011985145000241d403800b541e102d20017030001e1810754543d40d12113000500b035541481720701c0340980b410b40804c4d044200001d041d6000b5650102031070a14440045011408503014081c45070000e44a4205038281c49400c51760042050460707903801d03e281317161745205070480315141d9454042c45015109000b0f2102142c4a9409403010b4100320b03080c545040c65001d01c03801d0540042c8109041c41c0d0b4802d09a99141d4030001c00352684580001307808000b03224a54015541e00e00005203000740c100c05000800e004481a42e0b8012400c0440500b00d440031000d860490031038004120b01303400f20342c8100708514000c1140c010b0786c1400c00d82c44029400c0350010113000d60008107a14028a0450b0716665081e0700c004242c4034040380b00a10b5895141c07a42c0808001032142d561a55070034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 770424991 1250 770423741 770423767
    0x3051f06120f090f03020a030908011812020106051c0218010608040b1f2402010905251806061116050907050705070608090c0d0b040b060d1205120c07020a050105 71
    0x340600d0707000049a44c80460b6802d000b500d83d0032200050740443c0d800c1500051109052045001e201c1da1203101e019405d2640da281e6440304000d040290440d0b480b0782c0081140d50b9041c61820030fa006242c1e500c0c00340c03c4a03205105610022000100f01643d01100410615401032021644207a1180250440b0b69a40b4044c0f12000002c403450080d604c100c52001c40c1c06c81c038a0055103a600ba5425001a02400042c4101e00380c40241c20000c1c269045100d6141210320310300102626580c2d01a0185802510303003c02c40140c0c01407010f9461003a4032740b00100602900803500600b00c010120260207a40440c4982e246101114803032140107001660008026520640940318599809403d0b80c810075510b040040030f9600580c4c3c4000e19000c0c0300b4000c01c0510f0710010211415501101480c281d649a0b1511820100003c0403d50080042031691000601c2c9680c1ea2082103081e4442545400c040201c05c1c01142e401009030b48100004c0000801503690b500118088940c03d1a0040d680c1003041c000d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 770426241 1250 770424991 770425001
    0x606040605160c0e1e1611030903060a0906140c160606050909070312110a11040e0a030903120309020d12050c070f0e06060316180b040603051f06120f 66
    0xe005810803500c00721354442002c80480c010508070100b2407542d1200a5000701e100000e031000804040e0840040b506580a0f119082005021a0540c5e0810b50181d0200e42003d000302d03849035926950702240400c0004a03c104210b1104c00307600c03050103107010070411105119454041c03500c20101280241084640e03004040070b00310207001c644c51410324030003040ea030310f6460108503850303c90107000c0b1040c1842031120140701c0751000014a03001c8a527032585103554280d085a103030490b8075403510001e000d04c1040f41000e038a101c2da842d2401c40c0e107141440484101001c42c040101800d2401110243c3d071f2f550200e4440c0c94000c03001c1c80d80b10302034500c299094071980d22417441e18080c4400020f0380303035900c1941404070f0300a010b503940381da5102020080b10b403000305d80d11060b201004124012492240102c03089030380c580030304000052340300c04525680da0000c1e030001000980f5182082294103003604000d14540f0152050700e842d90820201902420180703418219080c0d80c4c1070f0180c611010f50b001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 770427491 1250 770426241 770426243
    0x10b070213060b120a05090a200d080307110d050f0d2a0e0907091a040302030109080a0219031b11060301081e0721020315090d030c0305060604060516 66
    0x401c00c070443d0707652441c4029400440b000443d1003218000550800c0791801442e2245100c240a031030000340e01d90350030200711031a40000e0300c3c0c01e14001d80302e130141e12104070150049004060f0103449142420004082980d00400c82c2c40d2070b0418240342e00415001030035034404c0512030700c2440d00e51584100d0440200700803400c1c9070345041c820321580d2042024400c0030f01c40350803a965900b6100300c04000d2100807801602c00c0400100d0f4410b040180010020000150420700e1403001e00d0325590f034000030b094231884141034400400c0003c00e0701406d074040080c0c0c150040240409403038180386072405000c050000514400c0c03050b0b40001c039004c2101326400d12141d05001490280c803540c640d4035259540250343c600c1030003045441510a01104002113042c120340c070040200384c0311690003030600100c200900d0304030380601c42c2c0d4440010f04000082600e100300403810040c403a4a002c00c2c402400c0c4d80216400c5401d1501d072000b444240d440d10400c840c01d803409401c0840d0b030348048003c620b50321030039228 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 770428741 1250 770427491 770427529
    0xc061d010912030b1c0609030c0b09031b06041502030603101d06011d0115120f050621060c0304050304050612010f170a1209090e0f100b0603010b0702 66
    0x3040e50100320001e60300720701000b00356404000d00c2d56004207210036549440d00522000000c12124400145103400101d0b45520038602134130480780319504e0550a900c1a1244c114640010400d030390599034122201543d0905040202000c0c1095110003c81c41c0740108030400d150780000000ea0140c40800c551046500c5ca00000c0100003014200054112540c01d8040005d00840c800042c1c40c440001c000104004203a004d0000742c0d00e4424044410b04c00300301c07080103016090649c50302e4080c1500c5045c0300030906071004a2107140c00c1c3c04101c01030881ca6240030481505007643da41071a000551664020500c0030ba8560b80d032075904000c2d25500890703200d1540910002140b50601000d00b40b9581243d2055201036101c40e02d0f0040d51002e030100004801c1150702c0000c89c0c0d004034400f0140f03941c0f058020300f050344250361103c14070130681d04ca2543d6030b040d03031348001c010520301c05040202e81d58482d00d40301d00708000d4290000083d09031106100c0e0f04000d05010400c1b6055544051219036030401e1a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 770429991 1250 770428741 770428751
    0x5070f0b03040b07020601051507030c06020c0609010f02180f030703080c030c070b2b0f0c0903110a0f1206150e15030604030f0c0f171b0106060c061d01 67
    0x34404039035104880880308100d40101250356140001400c074144d80d0020204072003c030104468020a4004540540070012842080303c007251940c4028800c944440001d00018030305605042d081d54820418071b0350040c81000340ca01401e40f69200b206e20004200c1d034101800021400003407400d0036030380001d840078000103140401d1500000042044640ca14151904c0c1d55840b2410a440d01692415414540c101c810404082440b4411040e20003602c0ca4001000002040c048049030047c00d500c801041d0a03110a01c14400803144854003c402141c50101a07810301010142210485c4550640d8005400d403102c100651900001d401c004d04400c2000101d80d03170b04012558a90948055840745092506003c00d03050115059102e580c040d26004003041d4458411164918054003c1d101445c02042040010354808803042500f561800349a0302e80d04409203460501e00d4000f14072100b68584881000b840d50000d0f5007103603a41c0c101c0800900111240348100e03003100c00e0942c02c00e155180c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 770431241 1250 770429991 770429999
    0x40e0a1e02030706020703170903010e15060f060315040b01140a02060612031e090d0203071401031409060f0604020c0f0d0f0302040f230303040e01030b0705070b070c05070f 76
    0x103142240d80c001c6085805042d66208166100c2400740000f500301501d00d480f03a00d5081141c0700a0580d1fa00140000503e00199940e15003800d2013459000b10f618200004d04c4903500d00340d00200a8400c046410318914100010003100c030071000c103000d500603902c0302e038082c203d03a018401d5075840401e50050503a6420b19204000d444070710442c0e801d481044140031800e0980e6000044d03400350003031282e0499083c0741c0c1c0b800344401500002d4025501425045401780143c4091090300000c010b100a0a10030030013050015003130700c002424441044e007420040001c0c2400014400d40c0001c00750710040c1d01501d40802040180c80381c00e01200d000d20984d480c50b4100000094140d07441d03100c0da9510029640310000c11030992285110700081003a6142c0c0501c060440740360800791111080100c0300c0d42c96011400309003140c00503801585256203000041040c080160309a0f030f07000c192071500c1132811400d0341e0b5811101c0380c0900001d080004545001d0100003007005500050b180c0203000900c1c0c07581e1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 770432491 1250 770431241 770431283
    0x1205040b16060c0c030c11060912070e0601020f06131a01061709010c14130f060518060a0c0303150e01080c01020c042304170f0d0c020d0e040e0a 64
    0x100000310b80040c40c20703c0c1d806802d4810000c0c20340c0a64945c0ea04511034072542c880290702088403041035071159041060800c15a2400b1410740d0009142000d0721045141103069002000020942e50554001110701d0b001100d0208106d64480002048010040a0390502e40c45070803100f480c903100240c4120011031180e4008904a00900c04140c0c1d00003550344003090942a210b0f800d19a4010407a041c00c44030b44501d414000d1304204509200c045545541c03a000300c1c41040d40c5a0040c4040b0308001544440d0700d90b0a816007109a030180c03106440c100c0c0030783e0020b081e030350031a20140405649040e40e0b901450030581c031000415450001c80e0903561601d000e2600c0d801e40700d00450240c401e040c94421541002d0107201415003041055800303404c0309040d44c04281c04014400c0b9101e0030201c81d84801e2084410152000d140c24000d0180c8a5960a42c3c44003102d07054041002503500040300c201810342d21040d80030024000f030307901242c8100403017100761034108100c0b0300818500c1c08804444032a00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 770433741 1250 770432491 770432527
    0x307050d090311101a12150a090c0b0c0d03020a0210050703051515030a0b0a1205030706140f04061d060114180c0703081302030d0207150e010504031205040b 69
    0x40c05076004504e0f50340c4030b030382245e01e810702e10141c4000d4000d0700c128500d00700040b240001212001e507a080c4003105031038080d0344011100c606041c1e5840003000180407039403240c08007402140c1000713072a00980b0744d0080d65483d0740ca000704040640015600e00d28500c04c1c03014100f07030142c00d030007444075081c0043d011780906812501e04100d504642e140c60920b1510070080340c4210040400149151a001086009041d2400304290000415040090303152080803982a1290042000c0c60b2502480d1070041e007550303441d0620b10481001c0c5070a004c0c2100d599039886070810340c002c5c80000c00555100078440c80120b401500d4895000b0580000b900c401d6411030746040020485480385405980710040540303000c180c0b0f049055400038403030200000c0c050314405d6082560f0441d410081509580040c0c6003045009446005800503201002550840081c01e443e40c015400e1501e030400e100340000340640240d22001d040f003810207030801031082c01a02140c020b00852002d040c0e983d100c07024a464542 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 770434991 1250 770433741 770433767
    0x3120622051b040b0d020a180303030c020c0a03020f0904140f03040302040b090c030f15040e0c0a06090b0f03040c05060705031b07050f041505060c0a020414010503120307050d0903 79
    0x1402d2881a0024680100c5080da00e007210300609024940940c84000e411184607007023446030400308560080e542d00e401000851007950041078040070000d00a040440d1641c8260065080600510060b9150103452243c80390540708540d00d907865041103240000e9070007a0040c2d13802045e04070459030710040000c0c02524001d0702e09006070303210141030105051080700e07849141041070000c070b04505828408242c00031000358800900d119540005021610a2804144a6401844404031034104814200000c060504040f51142d01d4640354103128850f043c00c80f0f424020000002d0300300a0201101000340101030203c83e01c5441c4c41c640141c1d0b85c0e014100c40e81c0900150950708c0b5a81038002030384402d076440038120080303c28900c4240405001c40c03815a4603114110071001c01c0e651124006018504140b000a003464491401808100c0b04001211012000c40c03038018001030314002480c4070403041c80d00103a59a1341c2c039100300701e43c02c0c0a00080e9501c8a0308042218080c181c1c020a011411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 770436241 1250 770434991 770435011
    0xb07050a120306080f0d090b0d11030f0402011e0912020a08250e190e0309030d030f0e03090f0d02190602101113030204020c070905010905160f020312062205 69
    0x1140c2d0301117080c0c0d503420f4180514000405d0040f040c070000074110080c0c800600c10410208012840100380d2056030812034007081164016400c00003903603842800c0b204032855100c03e10043c4401c0c40c500800710400f9001d440c01c0003828410b01d1045464000e0410000c1c10600300755583c0c01128585451801000f03040880810103514000c13418a09a006c0c030b90245d5402a00000041a40b1004501821500b12182d02c0b41c00184484500d40c2c40c00c2c80a00d00100160381c00090307103030b2011400b03805c42c0e401c01e505040300c4d030007445204496216a110344503801c104580200141e085803001555401c0c421140c81010204003a0001e41c0c50303000200c2c05107080c0201018070035019454001c00b007500400c01c0d132304c01c0c103000d00c482000036042c81e50080044000440c01d50702d05e1526248101d098600a90103540364907910401c1211419402440b030704c1c0c2048518000034403a6203510025940d01910131150080280034000c1030349541c480304034514401d58901403192905820000308003e1804031000080b0f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 770437491 1250 770436241 770436253
    0x81501090e0303010f1e0b0a210b010203030406090602090a080114130203060601121b180801020313060c020c04050903070b070504050310022514070605040f0b07050a12030608 77
    0x1007001000b07880c140d44619043c100418a405405454180b8030200b01d20804100075011500e039946000500407404c4a483e046205244030010614030701e001d02420100c5854003d084401780ea02104482d00f02c1e4001300d012030003a0300707070403d000280b00d02d5074010360220340c0d881c0c00900e003401904011114141045000403d47d41c00381d9140401ea01c0400003581034100310005812507004100c221107004903600c0c0081c0349a11941540d5403049a001c11102103411190407041c1c0c0f80480d4041005004060025411424003201e0341d103800800d10401040340c0e0311003500401c014401c20000d510031030000c2c410302c16410300009054a07030703001003000e40781194007000281402c0c1c000c030102c804451014004024595004900e84002e400200d8494903920500340c1e180314000f41c809041600342d019801528150700b44c840884c0c42c250701c9500c00001e11609210420449400100b650120749c16091016621070281c40c00340c1c18400d407404003d0000c49050041ca44107585940080140d4171204101d9803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 770438741 1250 770437491 770437511
    0x307080d120c05030c0705160815010b120118180b241c050c0303070501020c1510060509041d01020a030c030e0615010216031a010605070c050906060408150109 70
    0xb51954007016002180d01007011a030b0b075402c8072006101d074600420983d039003a034401201140c40601d0303a102880710741c401c1c040560341388801c034030640c0100b8568030050325041d99868905030481051090000c600c490104800d503910a5400804403e001c41c509003c10b00e03810301d48400031090a4070240d28064000030080401c941c8059842c9248400130040c002036200200c1c0d105480400c000221224050000d046100c1d840401c05402c090388103a0000d40c444072902c419a282019100450b00601404000c0c81804500c15403410207540c41840c0140d518070542d000b203800717400c20030a030040040310030038020120b84e07065000c0c0005000c2554288110b0851501c11001c1e25010318400c07800742c0000003c22196505094822400381040c0140e51184021480fa0240d514040e4000d4a40c81c2204011240d09081040e8540c05000309040182c10b00289446501c40c0c0f10b49030141038014241580898125500c01095034002c104070b04c04c40d9a0304080800d1918103441c00e04c107054540b800c0c0a0120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 770439991 1250 770438741 770438777
    0x9390102010509061b071505060306090a0b0105132903010c02120405060304110d11040c0807021b130f09051605090a09061b02150c0a170408090307080d 67
    0x43e01548048009010076210607082d440c08500317002d803c1c08112420800d1400243c6038500321a107003400c9000c0015149000c3e814513007400401805071005800c203104400c0041c202d5070b5000c0c156a0140e60203020140300003090f40007084181c120490310600344c00c028201004410080310b85d550194024441e80645180599903254010140240760b4010311007800319007450805158031a00400000380000e0400003c41c0380120380b0f0f003041c0d580100030000c028007400c00d4000c40000300701300d1500c29020310301004025210307040b000304e00006521005040070305907201c251040190412820800c12150704071023004c001c1140c6401101c060103990680c403c1c042018044104603000a000200513a842030186001404d15070800c0300d98981d11443c001024151140602008500390010031100754510901e100d2944000c260260181e81080303200d0209902450000070800940d03a0900d05499514014030603002c0e9044494151080090008400070005007030280386c401504c2c3c024105078184903070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 770441241 1250 770439991 770440001
    0xc11010207050d1101171306090c050901030c080c0a030b07050d200414060306010c020108040c1a0306130c0e0120030a18090b030705090408071709131808030939010201 74
    0x801100c1c031887ca030300c801103a00b50b0000c6804038410700d0a40c54103a1600c0020700c1210081e08152001c841c0c008040c01200b17010010320002100454211024519650754913000c0c4400804e10740411901090702c0340d40314051b402120314581d070300412090485480d460301455801038800d203032054440c00315040540c20220210ba01410041e900c8081c145410340066400384000b510803030300c0210f404000541005084160418800f0300300c451a80ca00300002000b90203241c20050841f6146403420211540b5002045541c0c6081c1c207080007d1010782000081d1241c040400e82c41400e40000107041030003070f91000c0e14201d50700300c204480c00101d854003420000c071041a811590180c2c0038880c14015482c1103c030b610f51091080b400300d46800160340d10040741043c0300d94050f40f0300340c02040881d850700d4840142c515101842008020320190303103100d01805501e500019003514000004551548418000340703407960a10549204400d4000380e2081d685c80000306808010241c6490b000b0440d8818020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 770442491 1250 770441241 770441251
    0xa20030901030e1015180b0a05130b130501090c020312010b0f1b01050402030706110c0f0114040816060906020c0111010f1e0e01050103030c11010207050d110117 71
    0x8608010324600154000c1c43c240c0d540304001d20410702000c040c5480303406896888280c603501880c01c1441d000d0042005101c51140c00c003018100703516542641c4a0070224401c442c2e04403440800d02c031160040f0700c02040e03500e50464000c0c2515001038040038540d04824100c8017000800c2100c0098a1800c9850b405901081031085507880c4c0104111000c00007e44140e402c00c4503410b01d845407900c4503200d10307006015030500f56512203081006614007400b0b03410040002d4200900d07010103c8038407546569480300b24511500c60074400500c41d910480080111203e8492034658aa40722440700765502c92403510003100b6a080c54010569030b114030f01034403c841141e0000c3c880b400d212801512803490300050b43c0d4266694060000100c004d500410700340350042d040503862100b900032400c0a0303070000220f40800d6814000100000fa40c40409043e43c00e402068104801c06aa00100d0400140c0d41c4283e40c02075544001c1000d106003c0c51080070240240c035035403c0c464040f40c458400340c10482e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 770443741 1250 770442491 770442493
    0x22110303071103070914070e011b050a03030f02031003031407020603011d070309030e0909150115080a020a0207060c03030b13051602070509060f010201140c041e030809151e0a20 78
    0x100c0c070142c2c0107000001423000c050418404054810800d040e0000000e00c080d0b415511200302c1c0c80c145601882201e01450724400290715510780800310b0b04640d02140b1008081021303a0036620102c100140a031100340794003c00707103650307540d4500304440041d5420f140e0341080c1d090000030480c028003c1c400c0c0c0d0751003985074032042100f403c118100409190000c05011007402900040c44110282a6180d400384c03d2030440c0c184d2403440c0010090000d20024800c0482030700c108501c46441d078001820404440143c54800101d1440c1d140440240c4500c41d14640c00041c0c2e60b2000030314140d2508201d2140c4010b05451440c500504c8041342d030380381d162007516088040381d8042a580d0500010311144040c0600010071814110102d80541200c1210842c0042001003010702803000c0d25480840503106581c18140d94606644510030544940d8120500c50303042c02c1c580340034000700c0c0c100b1703950f03410b00e041004042c0301803003103860120790700c40001c0e0f10001e007000c220400104031850110040d410144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 770444991 1250 770443741 770443781
    0x50630040804081515091305010c05030a0605150301210f0501050402010e0103022109030c0a050c100c05120307030b03011a010306150c1b081c0314221103030711030709 74
    0x14040c0100a50042c2010a19100020b40680813238005d00687c002900e442d500d00e82d60b481c20703a004200300e9400c3c1d0001b40c0b003a980c01059180f45804036043e80e041d0b071502d41e500d20000d4506141003030310a01c0c6480090000d180300400c41c3c04e01070194001d604c594004e890b82c06211440341d004504034414076103140000140d00400544010000d040c442c0e2000c8041e040301c0c070308048040b20924007140c0740b000322111791040101b035096080010300400503c040b82014800001d003551000e41351105504032441190000c000500614847c0d0407071290314801134000c003d40c00c2c2007000c802031074484200c0c42e4003003801c0480c0010901a20550402c020380c2c280d0354420040e81c02c1d6108565a8489440120010450307030000c40c1c501e10601020f505240c0996075103c0700380d003911029007550303120307408942404000317010858801d2510034120f115404842c44190145d05038500745416010071406150180310105614080103400310405c80e00802c00c90842d404030740d03a40810815658158089100441c2038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 770446241 1250 770444991 770445031
    0x4230319052104181a06040308030406060605070b0718090501170c1509060304060219020303040501050603150402060c07081207050c04050403140d1b0e040f05010506300408040815 79
    0x194005003102d205c000e03480d80c10203e540c0009025800075042611030440004c1403208020692007008020151803c01a042080369100c40c019084020400014090105c4050780000122065007014080000040182c1d5031503806040211141043c150729900c02c00005402625020704803807070300c451001c411441c1c64032003018000d980c1c001030001c81c0c4141c0c080c80566040070701e1403040c03113100d15283d0003952070f4900b500b822402d461001c0c01c0720380a0f40140340181c40c03240610144d030394401d8041d101e1941e18900640e1403032408003290700c101807a0080160713840030010a0001003001e98007540445050280b00713400c00c401c40304196001808541010341c441892660f11000d0b01000342981c0c00007a61014142c510003181140d0101e610005083c05854551450706102d0b01d240c86a5010082290350b0409011030b01c01d00c1840c0021309a021200c2c03600544002400c54003400055102140e00281003501c0d1000041c0c10600609805019000a8a00c0c11109120a91043c06000c0d6107804280076 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 770447491 1250 770446241 770446289
    0x506130506160504080a2604030503070b0601050c0a050f25060c020d0c0602060f09010b010c02040e2128050708133804230319052104 59
    0x101c0c08910900000340030010384c54200380300701b100306070055901c0d00d101c40481001240204d103042190040035028801400401c03000019602e0207544210551f43d6a200ca1006803614010702c40b1000c203a120b1540480d04100c408956004004040b0003200d51340440100da4044105401c0d01c0d80215042011003040154864824507170441c0c006040a1643c402d66290759404ca8004d8000501503444042440503241500d800c095200314554002c007c0c2188401c00285401040d45000c0d1141ea2650144001104188007814407082d0315039601e0020140e0410f01308643d00300b1404000003c80782d045580c0c01c44580403c0709051705140e030700c05283c40305660359503440c0c0e0015103034807520501c42072003c11080c80c0302c03180c80364a4211800c0c40d0305403009440071001641c5482d0000c0340c494801d000c108904848c0c5070741c2203075000414212200080c100c40200c1e16104909402c03c0d42c006000610209115000c2001c3d0200070007020a54052042210006882d22036880303006d100d207a4504c1002c0750307010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 770448741 1250 770447491 770447521
    0xf0c081b0915010905090408130605400602060a0e03030403140a030f020c0606030c01110c0402160812040b0a1e0509070f08100e010c091215180506130506 68
    0x141030050f01340d5140d80100c5d81708070044500b00c0b042c107400900741d030240301c2020400008040c0e91500c00c0c60b11202030080006550b550490440c40000961012040c0a40c04003140b000b0416100c000c40060391404001c1da0b90300d00340c076101c210925003040c0c00c17005840070085030b03c03590705900c03422618a8408607c5e403c9900c0481300e103041603039030100c107221990540001c0800c600c3c42401001030b824440201410400280105818400d220241032461000842c441c2000c0c801280d0060301c49440740100410703518141c100400d90b132b50000703100c8030703a00e40110318a0155000c2e80c082507103a55000c0c1010102c488400c0b00b60300e1403203038061aa02c81a2180c01942d804400c1a051300c080d00c1e0740c0c0741c403036072001d259402a403145d801900c1900504003a034800d03185190741c0f00e4000d01c5500317842d05003d0a20000c41c0900541403004000030024000100b129018411980e0010013581e05914880c4082c0d0300c0140c000c0742ca50142001081100d40c2e182c00718003520744c118001e460700d915582040041c8035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 770449991 1250 770448741 770448781
    0x6030b060d2619090503060a0606140d062d0f1421070605031e011202120a0b0411100c0b16030908031f060207060e0f04090f0c081b09 59
    0x26000c12901444103401183c4800440b100d40b200098681800201400d1100083c034080c10a4a840001c11400354401210003483e604500d42a5982c04131000c0e000c0507003807603005040c0c509003800c5141c01c2c80ea10030721841d011140c0140d0b040803a5803101c0f0444004401849002210921041c1420451a01400c04521103003071413a80c00c0302c2c0c0860a01e13a41070000344e50100011174004070420807480d403508d0450142c958900044084c1d503040280c00200000040c1003e400b415011102c1030f1540802c0141051058020150a2142c17401d032030a80510880040b10f203009800c0e51403e074081d01d0080068040c0c040d4025075040c06599005080c1840c40c01442d2244105603d80030400c000c5080c45000798041c0c440c03800d01c00b80c1907940d60160704800307505a0050b021584004402c110090788880c0043c02c01703104036203800640001400150207880501400b404894820351104108820b9002d45d40c225040941981c6c3e2032101038440e0f032607003400050310b0740d0003040d240002010702404542115001d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 770451241 1250 770449991 770450063
    0x1603150207060e070305011107021c29090c0916140412030c120e0307030b09161d0601021614060f1603090e0601051902011e06030b060d 60
    0x1100c402c1c1c0b11042990200103040b41c89401c028400c1c07043c05000e02801130000c00c07011200d464004940d01086d03048020303c01c080204103104c1220740820518105010b50900038440070b9402c00207550039501510b1b03003912014014410306068240c2400c2c0151103500c0794008114003030502030360010a03101042082d0000844080410020416484180e42b03184010301070fa560b403112045615003024001105801b20060007600b1030100502d9030000f41c0344094030342c0f01c0d00101480e00c502a00d107140070302c20307140192482e00808010440c507805a842c0084500110070f01d402c90f840307c0005a88500001480300c0b100e94512109000200030504004580c40c005021146007000301142d840942d00000d9000d2000011007040340c01780341d48000c140700a1702829031079028608040b030019106114680c182801d0390001c4520580f840d00032341c00625030018070003291559541480c24900104071601040b80e04503001b00c0840d034141017044542000692108a41c40d5890078015010514a42035060b41e0a03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 770452491 1250 770451241 770451247
    0xe0610062c0f0a030c1d0604060b03010510050d110a031b270906140901080c0306040b150307030501020c010e0304050a17100213240e041104171501060216031502 71
    0x9a100345d948402008040d051205c07168454a0b09280d03a18003030946441507040a0060011000f50412681102c0701190864140040b50b0000e446501070591a042c0f40ca00d001034a00090000c50001d003000c03555035800304030340032400e0072070040a0101902034000927148203880c00f140c00e103035859400e030700c00c040200e51a803940d41200030203840058000801143c016040078801d030030410009805000c10344060003401c034649021940e00c80c0005c0c8081d010328095030110354141040c515002a524016040d641c0458a034107005000c0c0d4041440342c40707590320704468030400560200a0300c040e00e03030051a82e9946803a040c040400c0c0c04000200c1011030150a030529000032840c8001e0582c90481a0240c0c000b500d0690601001450040160b03890940400c8800309a1750010200500c50003c0310009038412901300551980d024980000c1a11068903810725050940083d003100341c5c01821407514001d80c0c0f5641d00b240c0351b052104503e440340300c0c07040c8240001a0034644a20791451180c1c4010300f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 770453741 1250 770452491 770452493
    0x3091113021b01021827150d0f0507090b0a0506030c16051b0a0308120709080d0503010e070c0b010b090d0204240605040f0303050309010e0610062c0f0a03 68
    0x54800d18040d9021490b980010126a4201403007400e842c40181102e400c00645d1100303a206400624444840c04a1403030400002c1d00b0614400030042882d80c06000003e414550317107008401030300009e03825600f42c071425200148151141c06801c0400350003900c0d9170a42c0d413400c401e11600c0d81010305035003614401401b0310384400c50340080380c0740907502403402848c2c0c840034000c0103149420300c2010940a5800d941040c80418500030441c0e00c140f9200400072426503407400111003400c1280c00090690082104a0b80f00030740c40400b40d810b85600405452098458900c1540c903007a0010000b00704429a00c01000144032100241c0102c03600a020900709510941c00201204d54036041d02c070700c202115600c0b1401c00f10401840c0c0241160b4141300746424182010b240b8062598400101003010000020f0781a14007904002c441d1424402210403e08050300c0303400480354a0301034040050020701780c8a1012144038113520880703448001500c50b0140da8014018805403888501c0d4002d640944000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 770454991 1250 770453741 770453767
    0x30a0207051903080c030c1b0f030a030e1002070b0708091f1a0a0f090c020a0c030f140309010c0b0705070b0702060105030706170a020a110d08070e010309111302 71
    0x2e00001d46421924a849142d45006001d004c070242640902d20418810004000c4908003101c20076024440680304100d0820144c034a00410083c0740041400081080d05449405401c03002548541d082034501c6603242c5040042280100b00c809402c0080d80c03404907040d00c0c0251015500310304064242c0c0c0c07001903005502d80215807007401d00341806688800c0c0c80740d4ac1201d6600440307a4441101c0c140303282c500d400810103032003400c0c0c069200400c2e52800c000800500800a1317031078080c0d00c41041c4c10b10725501d050000d003e00039840b0990b06e90300c0d14540500706210100c00c03101c05c1c1d44161a440703164021505e5855282d14000d010500740982081103501184684a50a2003480164002c00e030941c144410b150414405901940c28009010080c1c0c801c001d0140003154000284207005803540450101201d2519018848450340c5c007c41c031403080900c0d48003034114031800d901d440307a6080392840e800450440d042c1c0e0902401d9242604d04400540c6402e100f4402400e40100e005820030b9400030300c3d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 770456241 1250 770454991 770455003
    0xa08070503030f01080a02010801050120070f080d0503010f21060203090601081b092a1216210b040e0d03061502120a080901020f121f1802030a020705 66
    0x1036880364000310802440021500c0300030302411012001c1d124200c195400a001400e040c0607039410701203c03840c0c00c1ca80e59000c0c4602031210000104075116a6507400c0250313007240d214000c00500e030042c20704519189000e28100c13812110070490380140b40f0f20384480c03000031280c501d6210004088043c1080c01084050000d075000b2800d54000d0951549445401840d1400701c411503c500388809280d18002d1f601c901205d5031018207410b07002140039006109002c80803407540071030341e040c4000ca11038500d0105d80e0034031ba11a076140c0070360400030415480180d0302500c4040a1000380d10400700d42800900a503005080d0050014001007082034070130785c5030b6080240c0482800d00080d0b8400d02004840041400101850070500140415074408a10301042e0b10410f50742c4010300105001140b40920300358122a20349407075141d01d6445003848a554078441390156103100704060142001c446801c02e0390442003c4071240005a154200160300030f5003e500000c1035010540c2e0b0a001042c0459002d01070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 770457491 1250 770456241 770456243
    0x3031c0506040c02060606070803150303070507152f0c130c2307140a0f030e01030c03110a1b0f080301051e090f060d06060e06010306140906060c0a0807 67
    0x129841c90a40c0c280800c07100404510b0302154810401c0c80050b4444804072603420780c004d0620395032a038030110180c01200465824070b4042c0b0002030399005004002c40d01400f17991421842c02101c1800e18011501c1c011003c9020310360030081d44000c40c540440d100c6144164071100b05540644900c20f000036498410b804540c580700d52903072200c0c00003a601c150300c0c82416180054940502c503d0410b06201800743c1440180310f002c40c20b80302003400c8010400c41d15491b41c0a08280441c008518000b0412041c0746441c60110303060000070500a4002d001d2842c2c0001403415a90405081e813400319103102e075070741c04d058a121020318450301040080980001c00c90080c0c104c9662545000b05101c02005603a50030f003c80c84001d50803000541c0c82000b20707500706411b4014445183c560704001f440f4032140d41c00040c140c41c6094030015007840390000382445a1001d803820024a03030380d11000c451660b070b0804456805902c071000143d1600d48040078000441300d20084400c05540c90340d66501d41d910840e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 770458741 1250 770457491 770457547
    0x108071d120f0705061e03040c6e040609050103031b0f0b04032a050f030711100e120703060501090605060a1d0d0c1502030310140303 59
    0x410b6100c0c101c41000440001c06090710040d1a2107140388007601048034440a00c0034620b8000042030522000700e82c42030140844511104440c000d0110005c0c44142d4410421403a000e000249000d00d4000000d55047c4200701c080644610110554041c0d891070305080200c002c5550520356260340c4075445030001424188500150a504509010b400700400551506034102c0c0030504c08000780c410b6410440195200c4040000742e1698942911404041182c040114078540802c0d81c802840e014164006da004506544000c5040202c1503128850110094046100c10360b9200b0f1609190041c00250710051400072180150880011012510860740340095404034030b050041c00b242d41300d928010144042c08100c07561400740031800c507000d0705c03140c41c01380843c05d5015018103035420708000c00c0560003070071444180c030302d40340001010415004075542604580340d1000403a0000003100c0c0603900c1000703401096407600103100b10780200320409540501081c4001464011a0b400010308807a4900d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 770459991 1250 770458741 770458753
    0x3050a11040f0905090a0201020706080c0f0309010207030e1009032901031406060607030c030c02040b130e010f050402150703031401170d090e1b0909070206060a0f03020108071d12 79
    0xf200564801401910f05034120f21840f030300507078001644504545440c04c064400390758000914100f40a9036882d5481502d00000300038040074194010445a8440d481d041c4401c20542c0074403407100c5600080001080d06020309002003408005030999070030540842010035820001e1710386008000381d00c2260741c1c001854454011100078800b565014005682d42401e2410a0318020407489038024040d081c0710030496010159210740c0c00400310100003070318407101c0c03580c0400c1d140300420265098010552801d82d01c003241001074095580103036001400e01482c00000441000f080e03014040840c18550b84080405c070840d0741c20700e0180201441d00d45491407240c0805c2280c20400d05d00c1c40d0b0010031035124401e2100035851502c5540000440b01850750700c2c0d010020f80e21a510a501d4444cbe80024031318108000c107940001c200f0b105000075611914101d40d0350071030301c400d82d519010090100e0520b41c00968003d10545c12450710300b05011022180c910707a003000c54442d000c1c0402c07852160f0019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 770461241 1250 770459991 770459999
    0xe0106300210021e06063001140702010614180702151006090816290d02030601030b0d0f020919091b0b180f060903150a0b01030204120303050a11040f 66
    0x3258240390b0f00d1035a0b8000d00071505c1e0560001f00d10505a0b484400c0702e84010400000400b810658030400242c168002c011120038103961414018044480d03100560a10303102081c9000c01103032b40c00d95040c000c0e02d500e48060313840303490035113101e0002c0c00300341180f2440f604129208110a0402e000e44500202074100d10b061200c0100001c880c2d800c90071203030340032850040c44030101d04240d03c01c0307070240150f958450b503d8000b414000d9101c1e0305545501d80000c01c0f00314103109958000e5000710400d803170170014204004c0c00c0c40614030001e10058294400382802c01c016060113640c156000e02c0964030361089681100805040310540d800903070760031200c44d0704101045540300d8040041d0403080b0640382080d8040f0b01d0344680700302030b613203d901450710822141102c0d00e82c0c03400e03100300a400509a035500160043d1221481c98201c07801a607880c00c06c02e140d14203501902c00c40d415620090000c403a105910f0b14254041c10020741010419652005801324081020b00604058170b07001c2d2200c1921490 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 770462491 1250 770461241 770461273
    0x90307090902240c0d08010e090f0d0c0c03210807030203100b0903070801050c0331033009020301050123010f1701090e010e010630021002 61
    0x10681080c50980c0c03900e44218096030342c500032000d440380c800100940a000b808191a002d0241c0301043ca00e52162201c0044042d4012201d24141c501c00d80a5a01d599224510282d88001c0040c00c460070f42c102c990b02d40b000511541d00300500d94000c03c9080540d0b90741741c0e220815903104080da244a11108185142441c1c1c0c009061504409203240540c110704002001040341003c620940310b0031400040d0b0000261810700c01d0000a24000f0000c011902d0151260301240d40112028103002d891201c0d001008442480640ea000c5092880c140c20143c0d6603070196902c00001911059020354039400c150100303440c01c0c0704074540400b0040841e41100c00c0c4107050a40f041a045501104d080c05820f0f50340d040081204000c15500346002c05011610380c2056134806280109214070385031000c00824180d020782c005941c2c40c407403800200002c80c02c0c60103003400c90b2a580506d0804110096526504c0c502e051506011401d040b440f20581040c5035000030f4060700310a01c40c10250700b124004001c0081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 770463741 1250 770462491 770462503
    0x30305060102150c092412060901080115060f0519020123250908010e0c1018050f030f25121208100503030304140610080705060d1509020903 62
    0x440c20b250340143c2840100d88250340505108503008001100800402c140304070f42152a21a0001039161f403102182110f0000782c00884045008040c00c05c00050398500c14880c0341c0700c2000890405412600f4035108a030030b05020740f0007004004051141c001c1e49202c62040c000280e41c1900001114010001c0520341030851000034819180008200400180d9110000e819940c0040307201d11501e115000540d0204010b0b00b004000c2c4d844d0144801d200c241c0020001122241240c1316002c0148546044440c007401c0c070500d03068203100400800890508451905400100609403a001e0080850300351a1400c600302e06984450400035100f03404040050801c094000b81c1c0400d0304415080d00c80072003200d94810207800b00205000020561042404024080d101c02001d4994034145824840d0413488071120900c460700400b004180442c0b080224141103a80910140c043d880c40c0204006858000d42c032025845904c49880c0303800082d0301c00c420406811803140041e119603041084c549898 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 770464991 1250 770463741 770463763
    0xf0a031a011103030f0c13030c0501020c1c02092d0423031c020f0304030e030127060e030f0a0f0e06130e2e0302092d070516030305060102 61
    0x850303a0030388035440c0c2c00401120b500c01c05650314100d0589840010728201e00c00d4441d0154005107940c00402082241d40d440c00444000b40c0c215048140390408000013052054642104030b12100300305e80050520b0038460b50720015141d103018480c00b5031030400155080c103009030103a00310807030108010052054040b000f114040c0c03407070500a00034425620398078881d826079020364400e40d07001100e408445404a079a00c3e101c1c168019102d040c1441e002d0240c04c1c2045070680710f5428001d64280214511132074286110642c00081c40c03480b0742e0303201c11004241c213507451051800300300078862010b207030740c4d000300741c0080340b561113040203070075610010300007004c03010744610a8504018494412040802c4038003500d85d640040242030700c54080c40c10300180d0030103046440259001542e2007071100c0e403008d402140d009448202081e980c00084051281d88200403400203200d000c80c0a20740c5480a400e03507800f200a0500350710301602c8040f207074200d00402d1000c40000f0385074002c1180c9540c0c14004400c0d14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 770466241 1250 770464991 770464997
    0xf1401030b09070c1b0f0506030a1e0203151203030c070f140f060109050108030904020a0210060e0a060b040305030726121509060102151e0907090c11031602060f0a031a01 75
    0x5042c9006e1400080c9136101c3d0911070304012000c00d18561321607001c014203040400c600585680711940d0200030307400c2160708424544284051802e10b0509a926044441040d0069851030713558446085060f0001d1800760780034505c83d0544c0001425199445e010f010019004107610070200440d149403100c140c1280a0407030602004005182d800000e0310b40d9040102c3d000340e00c41c00000340803480c118200c42450f0400d030510300b00140180b1a100700c5801900260000d00140362141e560740464461880014010b5100b005801c0200c3c4400c440d80076400e01110340303181901c05050350380c1c1158012100388818141d0000921a480e04243c681160030b51041d2981c541d80c1c49d100001075100c0f02100d80d990400803080001502c0c00c5080d041c650705201c0000803c1650381002510b941c5c0c1c1d00d1440c018220480c4c036000451031054061007400040d811204015468909114a44140c03c03602010881c1c10500610191210800403005400030700013a650000c0d200000c0d00001281d42d10358050076040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 770467491 1250 770466241 770466293
    0x180611130807080f0a0f0b0403051c0902130b01120902031e01020a020616020339010912030612150209060a03020c070f05030a060b030c120d180f1401030b09070c 71
    0xa902c280d101a989400c41c5070f880181d07590f8127040d22584146a40c60880000d1000c074290701540651040e65818002c4c0c9146d00c80502203084002203800b05880c0f18046490842141d615090070b401030411030303102400344d1700040d00c400305d80510040c10005010882e50042a078420081d4104400c0b0b9006c0301c6145c190128a90b2840e029450f480340c001385894005001d003404441c00b070020480580207500c00a4901082494010342c8d00822090b501210401d0007120610800c030311078002c000039584c800c560840f04280399551500c080040c4110000c0d503640a01c40c0b00c081d6640c16018169112694a000d170b51000308024882c2041e05a800110803404840c0b07003803000e030710002181e03000c1542c05100061501e418400092030130302d00700800703544165105164180d00d00082925403608040751505909285000c1070103510200354000c0700c40780c0e282081c0411402411008420411506050000b000e240200c08100400411200c8101203510000a401000000100720102c08145002c483e9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 770468741 1250 770467491 770467493
    0x909030403030e06090901060507020f100509150c030a0c03090f060c0b0622020705072c0c0a020a03030b0f0901091a09090d21050a050a050109180611130807080f0a 72
    0x9086e020600480c0100100820204119240c428150b002c0e89401020000a401d07401c3e8000d2550b0b1100781410f00503100002016051500c10b81503400c184080301c00b55041c00c0b07820100b11003000046600f6001c01044003800507003288500910005400c480d92550071450305410814a0208044e01a03401a5070008801419408103003240d540070381c000c1c1000d0780e00d20701ca007007840c80c068043c1c01c4070000340e00d8001041c09400040b100c00b4145a6880c0c0b00c0b1129a0b01c10b00207039500d019511600000d0307048500b50a0001e07101368016142040000c1c150700a0100390404110700001c00d070010350440395542001c401000f0f603500d60900e1075408880c5840035140514a00d61120b01d410b1440040c070420b444c1d101c021501d04616544030740404641040039141c41c04801016120666210401c03618150002c182c249480c007510381240c0891000582222040e07030b0320001031500ca0b4140582403804c0c0708002500c000201c404004100003030084c43c0c0c55062400b454200004041c00d1030141c1d1014100c84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 770469991 1250 770468741 770468749
    0x70b01080d17160810030b01120c120803040209250306030314040f0b0c03040b0f090f01082802090604030606090506010e0907030e0c0a081509030c0c040b060403020909030403030e0609 81
    0x70260b0514134181c1c50580301c074250005503080d96000208404541c1d000491100083c2c070b29032503140c1c00785010b601c2240c5e4500e107003541402e44840140841e542000040e0240c200a104280c10411104081e81507100c400140c60001071040c10540000b40c4030300d01082491b5101d581d00ea40018901103241c600751604224081091081c440e00710440310129404d46880802d10a80c0c000b803540c04d0103195141c8415084142a0f400042c2d40303032040d40043c100b6a07241d44100b120b2449040303499800313481e44160140c0703214100d8165403443c080c1a020801410682c8518001e030000750300c620302c085502c03400c0001c00c4c0c0941c0e400400103410070240c800003904940d03410228075041801401c0024008481490107030400600440e21600001c0b40c12000038111400079003020301e442c40342c000d0311107a2545012240c0740d20861403614002c0e4494458242c0a281640c400f00d418480206420701d016904d13404181b0114086801101c4c941001c5002c00500d034105010503d0050116100c62902c09260002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 770471241 1250 770469991 770470021
    0xa020f0c0a1206060305030714010c02070e0f061906020d08090a020a170102070803010308070b07020a0804051c0c1e06030e030418020c0a080306190302150a0203070b01080d17 77
    0x4040010b280b080070001c3c0400c0ea807000000c1c43d040002e0300d45d10b481c42c2c2000c01c9200d4000065099039840c2040d80d00500d403022070000c01b542d14080d0850000c0d1200c40c5140c4000d413001e0310060344942d401403002d52043d4100310b1403000302820340141c4076450584d040585000b8005062030b000347c22000c89000180c2d0344544001c16200001e920a60180030042c20500a00801100800c1580000b001000b0304c070142025041c0b1074820850001c865480e068202e0311500155402482190700348014812071403e041c080b00c22003428414800c000301962601e01410390540d104407031148440941411007188039000e00c1c013034016400d0500a9903103502d401d690f00c3c4100e21030b4021000d410820a18420401d030100c2d070501c054042194400f1070b081c1400401940700362452482004c0d0a0201c05202c8107488581e022207070010008060031003040303076504096000500303610841c00308004101c0026507070428140600103c50061040130b3301c565006d816803003e11022110401c0b20001c20000341e40d64205 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 770472491 1250 770471241 770471249
    0xc010905030a23010c120e15010e06010302090316050301151217070510060603052d1503060f060f060f0d2007060207110904030207060815150a020f0c0a 67
    0x1d01510307544240c801185840b00382c3c0b10250a5424100040f448036130007840c0325004039280008212900c0300b01610b5a4594880b50f0721000c5028031401003000468a216190b40002e060501610700400e8000207030501500e45080f030291402210184160300b402d02c0b81e01c07082151481020740320741c01e090f218245101c11000042c0555040058040a51030140c1a80c1100742d0000444501071003104445001d0701a030700071480024079050000c0d01181d0034800c1e03200e1046290519540c1000401c40f0f05d100080b009028100c0800ca403040d2030f0390d689041104500c504d0764840e091a0600b0b20303408100381d450b406d618540c81007005000c25140e42160100f22466222030f224000340f695840b1014050b00041c2d04410058000b001c2810402e002c0260010a503031480344411071088400e00d020018800350654024006031f00503001404201c0c000c6009580250800e0b6840d201c10050000140700d5005507600d107105180c000c540c2208582e01003080904003002400504002840d0002180043c601885 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 770473741 1250 770472491 770472503
    0xa1d0f060d09020a0b0d1d06010f03030c050114131403070206090f0a0810060602160e010b03100504060b071a04020f060a03061a07030f050f0306131409010e0c010905030a 75
    0x89500840d51078204c1d1303800900300b140d034454461036294020070080c40b0302e01019448403007a002220500202041c1c00b81030f03072031641840a1042c1551000c0300c111000d04804c032850740da80d55041c8072048800c2241442409041c411148400442c5072685c8084985920002140c0c0244014030050ba24082601c410b01025510b409a1111100004980b014a503011742000c2c01414049605840d4a030452029201683c084400041c03119503090308101c280d214040ba0300150b8001800000d50900007550007180450121b0410b070344500c0080c044400d117920440d138140d4002442410000d5050f11014203070303920f01030801c0600d09074001c00d0070301c004125224410880080c40c508254003e500c49005880101e1b1040c129101a441042c4540d0010740c00798007140c960782001600074400c04c21034420720000704001781903071281030901404400d40300c503141c0591703110084032102010250401e0703c2041e01d04004140d028040d0030f05410000002d007120704100c1510350502464400103007406013142e03c90 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 770474991 1250 770473741 770473751
    0x6050a080a02122e090210030c09080703200303040b12040215070f020621090c12070f051314070e1c021807050c0d09030308150d030e04060b0a1d0f060d 67
    0x4204c00020706000b03200a41c0208028079100c0c2e0540d261b0b02c04001207905803200c60301d00382c56003071140d40c030045d42c17000a10b030400301c8502002c00d00c1c50006045404a001d421281007903201c06181e00075412808141800308288001c0000f54a08124103480324026000c220703140911686070698404503034840070340900d0340000d8490501041040c007900c234110144420070740742400703001c06845400c3d44440c58071506030740b918507520050116402c402c50b5080010f00c02078034981014001c00c040701d10072a500040d500c540e41100c10901d020310620650f00d41c0c3ea01020076001c0e00030041000840040e0a01030588400c8071030041e1640100e080e100900309080f4070441c0e40d80c0324121124428025685050301900c0740103410a900050150141d0744252108080740e65440d030300300103070f010b103c00d25a8000301e407204120100c0e00580c00071411310405040401d80d10f0b15144102003c0e4400d10b040310001d0364042804640c0064110845074900b01100c1c9508042542c000080390f40c01410f40c1c150300c03a0354074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 770476241 1250 770474991 770475073
    0x605180118090f0b01080601020d0806030a02040218040c03060f0909082802061e01060e01031506020706020c06460509040c02070819030306050a080a0212 68
    0x404100c900000300d020811502501c80715184041c0210a00f0124802d0801d0309129080d0b000780019441000117134000c00703003500d98101c11074000700050300f01901401600e00482c05601da074001001003004526140e210407101c1018082104c91144c0c20702c04251910340c0611540110700826800c407030704004042910032a0b814040e02a00c1004104000602e4000d600300c92011640240d4000d012079409803405542e811044c16107020b84080300100c22645c0c0c4c001844194090b06451100c1c01042c500010000c41c03a441403071030a00190080400769000b500104861a410130840c4812a0305603040b80c04d10704120464640c03600f800c0605070400c4001108203201e941d10455000504034420118010080c00b04c0c0007811a5218164041c05103052104640c125800001c1880803181c008004202c0c0d031b60000c2c1d0003000044c0c0340300114101a121140001d084e83d80e8038840d2f0150000ca0060700d0071f03203503e10400c0000243c0c0900002141c200d4010390400c081103003441c49010007100d01c2c1210050300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 770477491 1250 770476241 770476247
    0x51c0915030204050a06020f070609030f0201031d0d080613020c0d08040203100c030903080c03060d08030c0412051c021209040c1403040309050918060c0705070e0108061f06051801 79
    0x149801860700710565050015800d0b81c00242048d418210710140c1d0f040e03540341e40f4212803a800500000c3e186c4079101c602c0c8001075101e0f07409442c590304202c48200604020302c0059040060703090340340c00000d0070b0006218080c0f400d000f24000482d082a8114942441100903a468040140400040c00f51040018055440600250031420381c020b0042103a1b502030f06016005080c000000d400080100c00010032050b4000f007140d000d0316000303050266500480d40c4400c0e05910081c800311104d0024400028000d00d100c0000700101e21620240030050100040100c81071a03d407030300c100b19403000c082c404c0c20481510032240c48038002d440200341c80401110681d6011081e25012064600000c204014540c0c8003441100762003045605114a4488250350b80c0e200d0340d80004d00249402940c0440e65a03003161000300411486003041e124043c0d41e4140240c01200b09922010541c0c01c150104980c2c201c0d8010000505a810300414092303605141c0010018001c1c140174111a0201510000c8a0b81c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 770478741 1250 770477491 770477497
    0xe0d1e170c03010f0b04081506040e03070305040e0f0403080f04030309080f03061206010b09010309140703030c050c090c04050d1511040806090a08030402060f0d050c0403051c09150302 81
    0x103546400e039441d0030440d280e0042035009109036128040c0700e07a00800d00c203210004650844003240c0003041003209010640143d0030001e440950701c41c2d640c1d0390b60881d4000510181a8150290b252151982d20b01140c4000e0080c0c020066141f4880e14400c0000207a0040001e5400100102e42c40072281d5540c41e00340d0080c215410084d200c000c0101d034007074a100f11903000b03500c110815201d01d00803481c0202540d07501d850a02030000c3d651401d0162000030351107544000c644d18028108000c41c407103180c2d22542001d40c0b03508250005032b02c2400c080d09002c41000402a00300c0f0507a194411460000280c1c1458000c83c003c0303074804c44a59001c001031200b103c0c40102c2031740c4040000c000940c601c10701c4420075400303449031018600030074000840ea4080490586400f6402c44a8180342d640c44c0c2d0700f08151030b880169840f164440921100c000072450780b09051080044280895449044d41030003032030507201100742d212000070b44d182e1080701c59003c0c81040840c3c0024105880030801e401099000e80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 770479991 1250 770478741 770478767
    0x170c0309030303100303120c02030a0e0a090f020703080c0f09010e0f03060c090a0b12060607020112051518061e040b1801090b01230a031811040e0d1e 66
    0x44004000c4c810500411580401121310a84a110741400c1c46000d0b4420b4401c0310345178a02503002442004050360144e90340f000b183c4002852128a00d448807803480490300560316401c031882d40425040304040e002062160024039044400c0d061814061500280d072250850050400444264445203600c8200c05002051002001d41c1c1e8985010010300001ba0400c05400b0301c90740e12440300284c00541038048407400c8080324000c500b20358903c401c1c04007690107401d0480c100400c00817a070011102c1d42c420703503005144555114020510b51000c000001d2004454480d40301c08000034040c45a8400c140c110001c01010700d803194420380000042d00401e8104c05168204113010f0120001c1c2d120304089505035003003218104001030300e40d40110b4004021085904801c600440000c01e42d1402201424a003807041c5000f0600c10100704842031000c00040c0f01321044001c4c4541411546854001d0f00c202c0811400100451050320034008c01000411620745c40c1c10050101102290744202c8400d03403c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 770481241 1250 770479991 770479993
    0xe010e1b240d05070e0a0518090f151609060806090604110a260903040303050c1f0911040209011b06060e091c0903030503010e070c240f09170c030903 66
    0x50300409024002400f42141c1400000710210103203440c500d82080a1010350300c0141440381c08114115010b10603403006400040d01d4801c0f9400844106001c11442c00700d603c3e02e000c0983c4a0400f140315030202c80c00750410304284134000c07205204c081d82c041403e0303511400c01c8465500d15190040400c0086c024443d00504103500040d4400760550000119110302c5a60f0700c00340007403480c00c04031400c000000e4800704a103401c20041040401e00c180c0c003804070326000c4010f48410250340110001c0e80c048413441082141e40303e5205000348030249a80b80d042c0c1009030fa0561805c644034000174011042c00b039440308001802d042110a1104076800701000d40b102e03070b900502d581441ea9090350790700001800003240184202449848500c500e01d510b08072a85a19900d046900340380c903062604100500c1d0400b003045c002014001300d00020340031003280302c00368075448020204032501802d469544060103015424412818001003883d10010981122104210b031900c0d440c049441c110701c00c4060050749 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 770482491 1250 770481241 770481247
    0x702040b062d07031b030e180a050f01050f04180203070311090a0915020a0c1a011811070305160b0103050312090105152209060e010e1b24 61
    0x1d080407422415010400462059002d0042c01900c02c42030b200d2103100074005114841281140103810111881192003030421115844614020650618004034580c0a09441070f050040034400d5229054112400380c0d41d004196040001140c1020b42108526004130340c0c0d000c01000c080c000c1c0380c00101c40760b801016030b800030b0703501d0600c1141c24405154407841b0300030510200d200c08405120700c40c0e9540c0c0c8100051415002c14041d00020b4104442110511030081d4032032001600074031481724400400d00b0b0b80d00c4a0f5040100c5070301c10260000d5001030841c03406030034915801c650000e40c1e00d03107585450219a20b80a10703c030b03010500f80410700200060291400401042404006017001c28010100c407d6141d980c45441c500b030321002d45400d00c0700515003200d5100350401c440004903107150100340b00c6504c030404e9161021101d0022040e80d085503182c03110b5908040c00c4c0285c00034665813030001d004102c0d01c000f0340010f00003e043c0d0301d881020001d0303103084000b0300d24885c6410504030186980e2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 770483741 1250 770482491 770482507
    0x9030c08070305011107050a06111c0f060603090312020a090e070f02010f020405010806040506040b06161407030803070f02010603021c050105010e1006050d091b0608060301050f0601050702040b06 86
    0x95104200d0104540039401c1421890042c2d11840c10341b40341503000401091186450b8903000d004011503808502d00c2c42d005c00c1011080b074084190204c2a01d02e0200c0003460345c0540000004640c41238010804150400d0030f800c000c2503000d4880c1000c02141d4200503601c0380c00e00d000340d680036000d070b03c1369803444041c0c410817541070340241d1010900c0c07013240c000307000018002170190101d10481c0103d9000c40d94510102d031300c40c10b09a0150b0b0780042c0c003400028650040c0350000c1c20903001091a52550002c0c5a4400104044a1481001d54080c00001c011890031a5648c08007804020244010070500341c0320b05003112310035000303400250380203014021010407903140140750b20748007a0199107542c242400000d1080e844000b01e4810388074040f031040201e003000341c01c4503140c0c4444d01942690ba250310464003c0b0382070402040c00c030294090761070340c4e2524182c40500000f20050009110364901070400c8030b00500c04892580c405c10900c4c00355071b0380c0740c1440010002c0009070180c6401400c0811805 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 770484991 1250 770483741 770483743
    0xe06070606150221030c1c2903060c07020d0302070302150408061305030a030b01050f18100c1a04050a050a05030c1009050a080307090806040b0105010e0609011e09030c08 75
    0x140c50b00c503801d4a0014001d240e014111030303000c0943d107542c0102000040c00d50038254014008121040c20602e0080c4d04440c070407400d5905141c00704050070703065550b468a42c0034a40480403000c4080d000ba020b24540411002c000c0c0c01108000b074040e001c110700407800c00d0710900c03200f00070355801001c2000010a51111b0500358100380201c501d0752003040c0104c0e1103c81581d03001c030700c10366000b00214502031501a08501401e00003c40030f05103d018840d40c0c1c000c1c2c49000185c200b2124003041072803000403c204200007075580680010601c0303038141032900400d80007265095100c40c00d120300d201540f2185400c80c0741448420300030340940074003107489081100101c0100f0900d5282c3d0101d50450a542960b403084030b07c0740100030902d501000342100001c08003c0034550102990900701141540c8584143c20140b040340d04440405000005200c15a0840e01000d00a0000e540c11410003101000113028a0b018111030a0941e200ca0710340f201c071621034240b0f6800f45034070014091159640e0079040d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 770486241 1250 770484991 770485019
    0x30415110c09070302130506031302010207050a0b0702040c0e0405180f150a0b012303060102060f010e0612030d180c060809070b03270d0314070507030e06070606 71
    0x68005403202401150310440001e90314000071004000078065140d000007078000b0340c400211488100b404c11800203803aa260030140d07101d0400d08000103408402c501c002401d000b01908403610520201758140401c0203000c00703903440258192400101e604a08100343c61180f2441c1c1c1c5070768800d05100400c03000e01d00b07110b9184d51440c0b04900300e43d030a844426016032540c00001c6541d001c1c04a400c00203c140d400b603007080a9840041c1440040c0000d245650f0004003c6070070f9050481c030000042c00410750741004050352184c0c04150740800743d410003100030b185400141803030344a14440e45601c840508244102c3e070305801c030f00d00704019912000034000b10b02803001109440c0301c3c2250f880041c5a6016096180c41a0143c20290000c1c0f41018441c0000703030005000c80c102d080403044e665880e00b04040c46903007004180001092408161003006043c2c50711000042810f40006040c4000103400c0f1080d100640d600d400c0c1030b484490340b0f00109503e402a0540600a18208070303000030480150168 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 770487491 1250 770486241 770486279
    0x5040f060e0105060303161415180604120305040203010b04020c15010b0a0504170c0a0b0c01050901110412080c060c0c0d0305010f060c021918061a03041103030c0304 73
    0xc01e0007402100d4103260300f2540e007101c005401d50020000031a58101455041c40380c04e06c40e012000d00d141c40d080a0728649035406082c4004d54050000380242c04c40320400d14180ca00040307004240c5c5291035034980d80c0720302c1080500014180c49070003241c11550300b03400c19501c110015008549030b60884010b20380d503014a41c5034000b1801c00340004a044444141200c6080205854885c500b038a05140d110380c940e115110703a4010302507034980f20803c1d5640e03162140200760039240a51a840441c1056003100e10150202d10581e1524440c0e440003d070100a540c1103849030801301036030100e0b6047c500280e20a02680c1201c41c0114020030140041c84409000e40024440849010b4903d181c429011103100303005e8401c0b40107040100700941d6102d00001c4541a201a000d018483c1016000c034080355000c1d0000700c0404080440b0a201d84401c0c490300300180781c06030145030348036000400e44180c1c1c40042d201604800d5900b010a455071403c0085a0b110201c3c00102d0b95501c0d84d030694840c140d00d000d21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 770488741 1250 770487491 770487503
    0x9010b011403060a050d0c0b0f0306011e020a06020c030d0908041e0305031e0c0d0e131505120304150302033421110306041407051c02040905040f 64
    0x541ca10607051081e0550784079100c080c0415003401d08050400c04405c600342001c694102c00c00318042440100c0c08050191841d02d031040580301d061000c0090807281901205500c04181981d10641c801e41c0056100313401500080c0040c0d4401c00003460b54114418000d511000c5c1e4140551042004541c4008004035841d101c03081c2c0c0308030900b80f4001c081409902c005045544280003450b03411010f003034801000e140c0d0860040ca8900320060031401c00d000443e260000c292440254240e070308000f1080c40d00c03203454401c2001100780404412804510354000c45000e00c07480300d80d004041c0c004104aa014100d115901043d80c01714500c010080e51003140d072810780502c00c860400103a08909040b0b2040c91841f400c5140c04600b004088510700ca202c42d904031480800e006001101c10b11344100c030413400406100d07555a11700282800155101c15131030803041c00d5010b040000260340142640c00000f942e081c1d840314005000e1200c406400303981c00210505183c81c003030004000c00090681d00c00c40c4101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 770489991 1250 770488741 770488757
    0x303050409110f0403110103060512010b01090e1e041502030423070614090109180e1e0c010f0c1a0a0b040b010504060e030703060c0201050702061b09011d0909010b01 73
    0x14009403403405440b00220080c0804c0c8000e00000314a160310130141c4c5818900000e080d41e0740c40001d009200f51707800b11242e0343d6407150380e4055968400010409030082c07100c00941401d00246514008a8000070a01c0440403200468100b00c60030303007500c01440c001e04003036449061a003004038030384018044540760b2036514003070455030785070118000c2c080761020f482e440c0c20001c0146000b0100d43c40f945c007190402c4a000808501064000710962255917000d800103640d440080c01c9518040820210ba246016500411114002c0c0052450390400302807030300c0841c103001e11501303845898840c0f10007002c00300c02440d08010340c0030a0855510917240d0003808c1c441000c16100b07200884d0100f5514900140040006200c0300f40034000d694603500d400f4048400c4c00342d0340d40f1008200c46c4010008070040c0d45403802d101c4281d034100017040c0c020040c5070702c04480540342c1c1c140c002c6902c2150030050600c28170050080c903054410b8604a100f200103071502030a8030302070200034001c1c01c00d11039850100320342c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 770491241 1250 770489991 770490011
    0x1308011b0807180e18010603081c0207020306070c03110109031e080f060105130b0403060203040227010302010323100e090c090105040b0301020903030f07060c05070206070201120e070303050409 85
    0x1410070203610381409060540c115040403400a413042c00107200c120a0360311504800f050740e000344282402503028082c1c1e551141c0d544d07924036000308003d0001e148902d00600c4840d01590340403d000c0d070042d559080c1005a01c1e00c9190580e8a4004401c3e20030b12035103480600d42c10305400005450720b80b00180b008800d02c602c07a000595003030340181d03410304211112100244280d40100c1c014149501c9103600c05d80c0d070503903c00c2a184681c0c8680c00865010760007005101c21400d101030040f100c15031251070410010500c0b101c0440440051101904058036010449100c3d1800c1028600030b0007888006074103442c1c9481d030118103028500c505840307003030141c000581d214000b04030300c540003074000d104490603441c0c40200000b408008025035459542080311141c61f0b5000c000a24030041d1410b142500d07501c0e01d08045e002c0b00c541011080c1408020001c583c0180d075190200c1c1d604560900709100c96144a0204500034074000c0c501c01e001d442000c0020080c550490080c10446100301c1d4107100c41110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 770492491 1250 770491241 770491247
    0x3030e04090503180613080312130305030a1a0409060c020d030606021e070e0709060f0305040c030308091002160506100608042d08040801050703090c05061308011b0807 74
    0x86920080c002d904240081d061140c401c1d60001180c6500810f09420844541d08140900d40580d118880503440003070003121107110394980d0384e072180c012022211441d5003503d015016100c0145400e400d60b545e20907101c1c075200c00481d149540c0708041c0c0108425916480c2103402000e159007004090310400c001992614440d0140d04203031030003079001d0079100b500450602841440c0e00c00410181c0a079142c0811003a142c042d14521880c2d03903644d1920900e28007600507200700a46103401081604110401c0041400c0c240130000312a07061910100641d18039100a08245c402408044410300018141003200b021030007101619010700190350700760726010400000070384284948800308410304001008181600200a41c40030340801800c460394070180450501d2402a8040380c0f03818000c10140b200003c00d00c82d150b8402058281044040c050341c4076001151020311800380704410004584105288445402004080b00f000074803250b0303000c001d00494035561602c9100081c0059000859241c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 770493741 1250 770492491 770492501
    0x43602030f1308180609190314070b0a0e04230109060902070c09110c070f06120506030705040c0513030605011a071203180203030d09111e040c0c1b03030e04 69
    0x6480586203240102e071071880138038900c4001c40c00e94824400d00c0383c811103840740d43c5a04d80c03007820052200745580c110b01e8180c041c0458030b40d0745c80c403d6004030801e200c20b2080804480c0c1c03040860400044291078140006c0242540d5104240c4043c104419440880708004040d81628041041400104c2e10303840030754101d010b0b07840094007540840504011000341d650264010004030b20b502c41c541603040c19180c0c44c2c03082d6584680040c00c202c001c00c102d03007a40000c221804040340c520501c0f641c10700c0c40006c0e40e034030550700030a446a0758502e089103800f4000c100301c5c2d440c0d03100f480d0b21480896a90810304001c200910818034078803240140c0902140d80c100c201c96407241d1004040303141d04110b01040b0b00800704144070b0030115039943c03006400340c1c1d800c101802400e48807601c0803e442441d85048184c1894100803640100d107010f95044842d0745280c00ea100081081d00c00040d0209000310840e03020101c200c01030082181003006200001c0103500c940252402503c0380c030156140341040c401214 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 770494991 1250 770493741 770493743
    0x70309291c050a0b1f0c0c03050a110a05010e0906130c0305150307050105220f12060606321e0a230405040216320c0303043602030f13 59
    0x42541c036610344507a05c1d062842400300351070b25200d420b00b18240d07074a048044568000b65070075808182c01e80c00b0881ca2024040c92138074143ca80008803468580080d04411100000511441d04140000c05541340c020b00030600c01c84c4400d0a000c12450b1400c041c005090075240782940044007a80d80e03d140c14001003000c201c41040e5a85860301c0d40b4405101c02075040d000807040400c0ca2110005103a81105013801c001c1c1040b240c00410990340c2c0d00d00300c0c0440e08540d00c410140000380001c0c5240702032120780051140240d0b0054400c0400c0b249400040d8411064030b0801c8149000341e8603403641d04000a4044075106844411340b01007181540759011003191039900c00b45500700424021820290041c20f146100340c08101082c545581d00c04c0f03040200c00f514038140004041cad1103105500c5070035682800100e00da014011340b482600c0800d1300c902c940c2c066503119441e2088090308000c4148000d42c680c0b841c411010341d0708280c0c04a040c019520a5901c500000001d030041260300e0704d40310301c52002c5c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 770496241 1250 770494991 770494999
    0x1209050a0e010b16060204090912080a200906070f1101140c030708070503070c0e06040f0603080a03020a09080303040606060e01020c01020c041e02070507051005070309291c050a0b 79
    0x45034460981e001090504da04c121405a002d000000d4130152502074208402c1c41800ba01203030005018000300b0004008084096a078140301440b004034404510405211001c100381d142d8800803040440e03072603ca2041d0040c0040803c0c81c4038010300142d071404a824540990b034900d0456841c100c1e0800d030b805518a00d240315001004582c00280c00301d4001c00905104030103480c1028002e03291604269825400f908004140c0010002680b4061168a040c800e40080070854182183c41c0e00c101401640f4100b018180e000500c1c441003401031081c80014281c24081380d82d64a003900c3c10304040e021510440000c10303902e003c1e00b10035600104a0342d107070800c1030307000b000000920780402c00900f601110350200d01e0081a118040392204e4001810042c0c0201d00a1031228078103030a2118440c008000383c0b080005c1403101000080c0d12000c82021203984a0508180001c01c2264002e45c90540340c5041c40c1900009140d107900000085008000882c05001c20265661403103100654100010003a44 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 770497491 1250 770496241 770496247
    0x7080f011202012c030c0307030507050609151b0d0318060c0905060a0c0506090303041a070306050d26030c0403080c010b040c090f0f0518131209050a0e010b 69
    0x9101c003807081c0551400e0051418a0029400601840c0c141028010501141845090841444c14100070003041c0303641c1680240140c40c5103031a0586c603003540d0700a043c8a1800001c0d0040356590b503c0d0301100c3c80c8080c50400380d90301a405c001140d040c2c15240c10380e002e40101205204801d000744210141013003200560200001913a540b90018a03d11a4007018040880d00c0454184c0740d00b8040c092480541d12119010b515600300640b5142005080246c01e82c810010000028800849600b0084c10750004117038a8455141c1a03000d02070503001181c0004d4414118018000780040180d15948034030b40416400e401003174141d0503440b0407151114418410001000001d0300c0c81c0090840e904800000642c42d00c3c41710008055071050040c0c9000164400000d020003030000815000400e52054040040c070302d0a004201410414820b9506c480501d05c0041d900b50001d1200c411910390211106d000c48081e010b0103010803c150290b24061019020f01051705032001c484a810380324020035081c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 770498741 1250 770497491 770497499
    0xd0e0a110f0d0602220b09090f06011b060b0d0609060b01080105030c270403020d11210f1605031806070b04021504170105160c0f1203090206030a020d0507080f01 71
    0x1c1e5000005841d8032860300110792880b40b82400170700010340318903d007461351444214200024408007410008064082e402032000316070f08004c180c02c0e14127210030301850440240c141070f80185840700c0d00d01c0d000a0941000b2040112560108580d2480b0b10001c0185800010045400070000d00802d6050b50100d5032940d414035000000d4070007805240010309920440009880146000b43c1e003c6015138010301403044080e402030b540f9072071404401c2c02000968880169800d40e0300408000440d1000f001969071140800407049070310005046d101e0700e4061681e4138000d552b039070002d10440340246882c0e02e080c400745040702c1151031035038018040c4009034855400b04441ca01d004046d09480703140810000842040b07203000c5488444600d000011180340c4a41c0c2c050b41d4000d801ca841d401c00c504042a24005106202c1d060300598022418031002c6050032401c3c0c00034080603c010354059000b0080000317481854005228850600c0070038001e6858109056441c0c04081d80e50451384920b080c0140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 770499991 1250 770498741 770498753
    0x80d080c1605120a080f04080a080403090819111e060901020f0f030304110f090403081009090b101403070e0603031b0a020108160e060f0d0e0a110f0d 66
    0xc01c1088100350492980d0744076a49107854000102900c00c14910042842910369420410903503012810401140040c83d00e6a141409441044018001d105000010a080c5449990700c10701070031020f000c82d1040340c2c545607402401c0b42006003c40b08000f40481c201c080d0b05140550068034010f90801d4290745914904004194200c40403007130442c031030408440754614040001840034205000075503601d00b00b5080451800c107078405480e018107400d8031244026183c040c0304507807054143c9095600e544540048400d1428541e00004003103007010200d000703101c406082d05004402c0003080703000c6180d803100f28040500c02d100c001603054110ba001081000c1c048032200c0e5115000400340c0385017070070000c5440300141c920601e19103a540710b803500f10308550304403080c0341d04108061805004a19030700c0b8010003038058030858501031200800d041c84400c8419050f0307402c20840a40511012030f914004695030f070810a001d0b6141c00c012040c02543d400e2001050140b00b50250104a103003086448203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 770501241 1250 770499991 770499997
    0x60609020a02030a261e0708010b0904051314102703080702070902030411030f0c0306163c031103040201030903050c0a20060310050f0307090f0203010f080d080c 71
    0x282104040717207200303040c6254059001e0702c54075101c400902000145184c0c1c60341030320014001d40a002c001d000501114051a003650311180302280c0226407961160a80c403141409900300800d040300c071035840c071100c0c45c010403904072a141110381088811443c8800200c000b00120385031242c1804684a00c002c288600d0500b0351104031401114481559515078104070f0b801142d054814040844851110f85010701c0200007511410f4001c3ca010745810001a48411010341a23900c00c51405081001640c003656072102d0710a52640501018002c50b105a5030107880202c0308003015448a950060150003403180140c07000101041e2820350b622940150000c0280580607414030106000c0f07040103d604000301030a403031080d07420855202c0c028114804103a841e00c031040c80341c10144208070780b241003070402004903030040310f1034225140700d40c001c00d09000c030580050342c1301c50804ca03100e6030640c05600154125541050891255940d9a0381d2135180d0440c41c020b0000103400002151060841c03c0103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 770502491 1250 770501241 770501267
    0x60c12040812010909060b010507150b0f1207150531080f100b060c03030c0a0c1a012111090705041706040c0b041a0a09030204090f060609020a02030a 66
    0x540e803900401602d19204003a007640444091034840044030b080205e2402145000031007828254144041d0b80e55110341040b01c000c43c00449e82e035681406d8095912000d41d801c0403900038040400420085410a0700d80620340240c0c2c03176070040005803006c6140b08808480131815040400d110410300c001c4460a140c3d0340324140481001c4510300891814801d0000b004a45100d1005110044199220350240c81d100035102d48142030a110048000300c0120441b40c0c401500580c841d518101c0e1070050f29601c1c82240007a22110740d55011110620030034035614141c80e0700701c510354034108905198140f04001420020301d88460400541c0c1d1030308020345025000089800c203241001e85940e4410f2002d2011031100340301d5842541400248120300c28020040e02c401200145002e0504520880040c00c12500c070781665000902010710a00c42e50544024580c020014040811a07080c1488a40c000300000d0350814501107002600345007a108070380086495401440c144071552005a07070004058030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 770503597 1106 770502491 770502503
    0x5011401050d0f170301080604031106060117060f1020011104030209070c0209010306060e0612070506090d12032f04090e1c030c0e0102060c1204 64
    0x940400901c0c0c1102d000f403080015440c03c04070244034543d551600302004000030072043e40120b81d0781c1c0158000d0303403880340503488844480d0700d602d015200a808101c1c07800580a05818140c40e03142e01a00003007007030301012079a1000c502150001c401c180b0004030000107054010484003038004080303890900070054206480c41c54a014401d41c04003034441c010700b10000c2e0265106007120306540790b0161a07003c040d44c2d2403400c41c2c040c3c030840c066506402011030028540f17040c015100d00d2641c02c0ca030700501b45a4505001e101041e07012130f032600d41012105407010b01180802c43c2090440700b0036030f0001441601d5548040038100800390b014030f0b01070344d20542801800c2610540d070990b5a6150001603540c41c0c0c911242c58001d04241c080b03d9074010782c008081164055014070320b0140240c03658140341ca641c1c001203865a004a441d0070b0850301c01d220003250340031054465a80144185 = true := by decide +kernel

theorem cover : BRFrame.Cov 770323741 770503597 := by
  have h0 := BRFrame.cov_init 770323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 770323741 ≤ n) (h2 : n < 770503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
