-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1781
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:39:09.323858+00:00
-- url     : https://prove2.me/submissions/20607a2b-e4dd-41a4-84b3-ce6d3d3fc5d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 320143884 ≤ n < 320323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 320145134 1250 320143884 320143891
    0x120513030b04021f020f0c0306060303030a0213030507151b0c03150f0f1505060418090f0209090a02091f1703041e080d171303050418140705040e 64
    0x1001d1589650300c3c4005100078519941c0315040455020028030b6071540060b4651000c41c1e10f0089564139091501010355034003048442c180d1560080002034161000c640150429078000701a90007503e0300c039035681e1704107050351300041c5c6180b41c03440e031107000350360f0081c003003102d854542212030020b8840e51600d0301e402c4400d00001d009410104c460f44181101c590102181b61149981001590f0126000c01c002d002c00c0340440c008201c0b032520204842c549001268100e030840c400204015050804040142407203100a86030180388403049809038407507221052045ca4040c001c3e000e82d00c01c52040000460340901142015442c285040800b1200040c0402c10f48003900348001d040604442c082c0d240d032080b600002524a4442145003000b5080000c4a0646102000f940c000d40700302242143c00705004203844941816040c0072841d00446d9040540b0310358013a20b4a1031070152900c0c1c5415001903401408003050b55210108048500110015500052507142c440d207458078080300c3d01c041e554083e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 320146384 1250 320145134 320145143
    0xa05130b04110a080c120105070818070e19060b0c0a110d050f0a14031801051c020a0c060e06040f032109031e090e0c0c0c090a0912051303 61
    0x601040c144040c070036440b81d4020b0300612011102d900c072200152500410084540104070010b65070302c0b41d8a041c0249442000326035690610b03595001742d018007603105c0c0d4451340d205000b800400b04000c500c0c658064070900f01004071ba042e5080007a044021036140c2d82c85010400418010b00084090100c3c8180d2003641144695038080c4008000900120960000415034401c050341000c40701d070b000c50080101801104050400007284080a45a00c03412041d4524104201d81c00c00c41c2c0d601840107082882282d012483d80c0181d552160000c0b85d02003200f14000c81c280008070820008a8000c501c441c04a400242015080036070b00d40c2c4400503103490080c140300c80c03854113102d1400200c0d400242c02c10059014054420b0714140a4403403d03c0440c0d550000d0740155000030054016618481291012070101d0510364a9440a6040750003a030341000da54080c035444d9440c2ea030350f2805014010f09000400050340d034403926110f05661403004200c02444414008a254980004400401c50303401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 320147634 1250 320146384 320146403
    0x3030906180819020108130807082a1e2a03100f06050f090402010807080910060803091008070f0309032f0706090806060d060e240a0513 60
    0x81200c1c01003070300d01680042c856807040d01c0b00040221801294040340728002c0c0c075a103080e5241c0d8411002402d42c01c50024040c0340c2d08000f85000124160000c100d600d10280940884610002ca11680c2001d60b20150b059640701402d1100000d540d014403420a02607400101142c0c06010100c28040300700c3d03900002d100722035420b8900b260318280845082c101007010300308004060203856000500140c040c0b140500130045c03085081e814107030300150003a034058441c1c1031503a0700c0705c50842e4807041c010b201030103a008110b2801420f147e03a00400303000c0c280560142d5141c90442040c000b20748000c0b0005030422518605000c54690000701910a484080c50301140c1080350b8107007070301c20003141280e028440d81e1041c80c40603a229000d0b90741000700b03115001c1d1351146503914011030300850380340200e483e1a00104003180301807808440108120344107100100710aa0003013001414a40702e0803d00750072540e001315140d80b0000c40e0303a009501075102ea200b04064145070555183c201d03401c00006161101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 320148884 1250 320147634 320147657
    0x20c07090c020c13020a08151c0309050310060503192a15180906050a090b0406050301020c0f0f24070e04050c0a020f0604021f03020702040908030103140703030906 72
    0x400d203d4840c09100c0900181980c141c10000340d0001d6028504c01c0d4005000038004c07511940c003214400342240d50007800e0308103e114003000c81e2030340c84031172008401740f04005100040a44003440348401d040d40144000582c40c0c44c2c0004d0504065020160b504201041101c241c00100d9182800d40400036880900003415013000c0800310b110000e800645140c0e400c000d120940d1507008540000c1d6241c025003c20616070b43d1016181915801c0c060182c2c041c07101ca40c20b10940d400c950042050322001040454199030320b401003070882e4000755401c90990015050600305060802002e12034410450040080441e1444c140b2616103001c058560444c64038008240c07a00e01c02e0b00b90100b02400180208203c0c14500344100055129941c4800580205a0114900900030950521860300648a0898482014558880c6180482030342d824181c2c00e10024001d41c0b40d5108546002c0c0c40707005107a55a5040d030804c0c6980c1c200403001d180d26a8003014082c00003d60041e091401c6540a0526039802c89 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 320150134 1250 320148884 320148887
    0x20406031805332502120d1a0607051e070f063f060b03090604030e03100504060b040e0f0d1101140c0d14072a1a090f01020c07090c 58
    0x3e1501c080c6003c4060b1000500c128610040b225004100400e00c55200504101105903107807111003048141c0c88209020b0500e0030076081e04036074800092942c004186110038400902c0903000b00005441e254006000c1822025079034071801e401420310001071446a00e0301c00c60002e44132060003208200190000b4601070383c80d6a425140d6400e85803c0610455201140b00081808140200349400d904011000420012240c1140e005007000c1c40074141664880d1410740b01260074140407a01403140e520300420000984c4030b200d0203140300d03460104041c82100100800d031140d140c1001c01c2d50700011036403e45403000040d420044045420f20b8078074060008545030040050382c500c016142100b0b401c000104180c03000400c100020280304000003944c0d4903030000000c104940500c003044681207080b002c80301404404006912409020b85420015511405517a9103a9807402241d030b40300e002e1064101c41444085d0b009902c080007141080c0014116071b544070200d11452840c80e9442c0041007055 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 320151384 1250 320150134 320150203
    0x809010f11030a080601141314030a120e0f0a05060702010c020303130909060f0905070902131a0c0d081b0903010209040e03031f0b070b06030c0a0801020406031805 72
    0x9070802401e80c2c3d250888424003904080d411910640001d003009081300c8220110005c0c2d4a802401c000c06034034079814184100c041d060728884540e8144156030405000560042400000c01087d5641980c0a800d180510030280360300304910384640710546003405692540800c0e68016902441d22511410203400070078258071500306902005400c80030086801c20698018008040c401d1130308000790282c595001046852140d0020210342103104208042c80e070a401a1001d582c2141e8144400c030303a05e242e070714030840000c480b000c2d10180100300525007003018010003270360390b40c1828980c2540c41c180c000461100081c036003241d000040428442c402d41c07425419102c00d010094801c11992159140315952174000311a001040070350b650a400c460b5880001000881c2c4440003982d060102c0d40d44e0314412000020269600740c420448141d001e569580f00604c01010140e00040e42c8505003078006045e60b9448016042412107005001e0008000141c1d101d034442c1c8442607440040240c10311501d91 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 320152634 1250 320151384 320151407
    0x1180f0b04020a051803030c03040e04030509090115031406010912080405190f0b070f020f04140403030e010c0804050a110307090e0303010e1302031507020a0215250809010f 76
    0x5480401c6803050301d5005801802e44800424017121820001c0081503624400c1145d00c0300c098000b44400c10800005844907a0010300c82d0821a0034040be0802080130040b00341d100045100180c550401415054821008072202541621855292910010b010001c1d03d04c0b440c0e50754400480c110045c8024002990b001d00802411200000c104a08038081d00c1d8460144200010b80c0714000501c0500080c00c03140c1c1c550780138841034404540c0d40c08109146500080480c0c115446907901070744c1342038622805102e103120341c0740040d054014880060071291014010800d00013190140000700c0ea0000d0385242d8103500c10484019258030380c010034200b007003d81c0308000030fa041528007e803143c40400a0350503248804844540b0780da030f02d2034601021242d464040d405820010040107040b105205565110550b40103c5144881c40d601207902903111300c60550b800c00c00071421000314680c101a42010b0b003250409007030340c02c42c1c2d0b413203141d0340344501e00907203040c000302504c4140f80b18040e402007000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 320153884 1250 320152634 320152639
    0xb0c0a050709200a020a0b04020a0302030f0f010e0a020f0d0303020906040306201c05181b040b01090308030703182a0611030414210d020708010501180f0b 68
    0x51299882c1c0e90000500314072180d4111000c55001c19004440c000d01c00c2e60f0760416917074018804901c25840700031960002a006a801c91824180840540c9040050b003810078212030081050b00030b411000303400c5655651403400e8980214524001603540d040c240e41d045e8008a0700f034212070105150503402445002c442c1d0341c011201045c00001c0c044135a000700c210400e08009802c034803080390020307541c5100340300c40e03c00d05c00c980c3c2000050110050788050380c0540348014081020b40200340203440c00c0c9a81d18580e0501c091b6a0b461103282c1414018080c40788004c2c2029120141155160103260000800d40d000301682d628403803013851109441100d0164200c40200f43d032801c1c0340400d04204c00707256941090b0b00007031000040c00d14459580155880f040c80080c508040c00d088140c4074900c618520740341d1054500001194003160001840c031004c00c030500500d40c0000f0758501038240340c5a5401500b4a03450100100034482c400e501044000d121804002003980d0b2120207840100000780b64180c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 320155134 1250 320153884 320153893
    0x120801170c011d0d0c18020301150e01030905010f090c09050c070b1f12030e0d0203030a0e0d0206040801021b012a051204050706091212081902030708040b07030c090b0c0a05 76
    0x82481040c0003a0410396200050401200807210046e400742d100a1180144100c4214101c04003184684449950b0540503d40480c030021242c0b9410b081d503030b8100e954201c0c1035403901880b0401c40600e0f2000020201c07150144400e00e030005058045000c0c3c1080503040c0302c1c841c0000380300041d070180085260555021146905610780031a048640340055080b03020803840c444c48143c91914080160400d51300900840c54002e80d000c048a41c0c03e40072003c660031040807054500143d0342e01011b040502510000107850300d181501c01105103407480d10b08209645072684c030130782d207400d86c03d0011241c003040c80f0108100400107504480501c2403e0b43c0d0134400d0b014500380802c0140100e400411103059650f203009175519a8040305103050214001030032844100c1d8405c0c106800f515010364404084080714052180b0400d0140a0b68011541c0301300040b071075401c100401202d42291a0082080e107002c000c103255240c03003d40103a0303041c0a5003c61120104845040c1c0c2402c0051a003001c0d409420307603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 320156384 1250 320155134 320155159
    0x50c07030b01060c0b06040b030715110a12030606050f040b09061204030c02030d022406061614010f1a0d050f0106030b0402120102031608070e040603120801170c011d 73
    0x1058000a002d017201d042c0100000306d072040c40d190184045080005001d4101c852800b21080202c0880354011014443c81981c0340b2000f40080c08194000d034001e0710f29080c00300001030001d04590a80d0080e8040c400144060b01001c40c2440aa6043e030304d42c0c800403075440f140800054541d0040e9844d100c010200b0604000c02c05602c0100030300c09501c29012220046850841661501164490649400000c100860700710034590740b81904107101a000b54030307003000d822902920b00d203140c4090350f0210021041c004445801d22410101d5201c44804004600d24007540c0803540c1d28840303e407032140d101a401541802380520a002880c40740c40000c104040c0d81c1d03d4490056a0225016441001f031700c0305100e2555010f00803603201c0c5c950105500c0620303e0054003a1040700001d000c100170007107410855082c0c3e4486100b14800b840c081c12800b100a00c20b040d00419505058000c0700c41d43d01c039001242109070002810000c0584242070085500e005080602200b07910404003660048a041c0d04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 320157634 1250 320156384 320156387
    0xd0e070504022107080c121e0421091d04030201290406140607170f04060905030d0e0a050d030c0615050108150906062b0218090606040303050c07030b0106 68
    0xc07041c4030360f10b140c005807603560b60313040c243d81c02c990803540c401850300100513004000b4405015191f02182c0d11540000c050560401d140c00e040d011103027111141210190b0b40c8401e05240d840c40c10b01c6810346041510242000103203122403410004260443d1811001b041c1054001e410121180f020180c00e0031040340c0d401c00e00300f0030256041500380120710f41100404c50003941c1d50f000b80022400f40800d0310304265a52100008142c0b10220640d034103052110304e20809000b4001d00007000155210030515091070101820038039004035040501035a048404c400761a070700c0d0710f201214421a4010411545070a041d902748190b83e100414280c0751804c2940c00703005000e4450140c40c020b81c0c4500e80c640c2d4121030300041200c019003071944105146c00040c12850050020700c11281c403804001b40080c1401c1807000e002805002c9511111740204210042e414035031201000325001f107a200c420b50424a001c50740c1c5d88103601015042140014000c98206000c0140c80f0007160311003007000566a54040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 320158884 1250 320157634 320157667
    0x30e0d0309090e03040302181312090e010e060a0603020d0902041b020c0d080906030402010e040e061b04140d05010212070225050102030912010f15150201110d0e07050402 75
    0x40c01100516080040c0c50803d0700206031801d0720341c05801d0000420b5548600d0030320381c078001c010103290001e0a07900d000091624142c1c040400c030a80380c80310454103002c0c0000c1c4201d07058001c4155003d506041080703981c1c90342450003c5401900300181d44c0c03150200000c02034000400c0294009003448007000c0e10076030744000c54100201903400e64008846400401407410882e98018010110501540c0d21034604a001550468414144000d1800508000c10309581c401d800c00041a00403004003d8440c001d181c10500b01c50050306d080340303001e0402c50142c14501d416100640181c560320030040030060254119003140c400a03801003960f1500302c400030340d918204102c51481c6001d1001c202450341403420318005844058015605042c1c903041072101c0e0440740310050350a5034941ca02d40b1640821842503920203041c0c020520342190400181102400f144041542168503100c07485052501c031a0550701c0381078034400045000c2e09880d2501d407a00c4026040b0035406480000c00000f450b030040d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 320160134 1250 320158884 320158889
    0xa020f3112170702030706050d0204360c0210090221030307090503152202150c0105340207030c06030c17090726010f0b1e010c0f030e0d0309 62
    0x142d158981546454180c9032070b00540c1e50003074140c1d10009050114600a4000e02810300c94a42c005080950328070320304c0000d80343c1240750a4101ca200000c031000c1042d0509074000071481e12020700c8001000c00300255141c40840c425000156561030b640300315969166201d070301590304000e6114481d51410130070745a50081d1090004242c4c800c40000d0581004228800160011408060580d840c840712056994403041c00d80c1a0310307215a00341d0016a908080d84180103d442d0020b520344406103c05400c40c0d0b805000401d00c4c2268203a0b0003500c0054229030354140d9180c1172000000c46c80810300384e02c1d207074031600024000030f100d02003c0f480d60303410780c483c0070348100c5a9600350111040c1f080143d2061401c2c0d800c415070383c0002c031052080404501013030707449400c088140c09040c00c0c42200f05085402c001600300a0644403000d90046240520b5407108440301410f00c45020400807001806030f01d9031800041c420441c0b414a00207044c043c10390300c00c40540140c40d02c0080e00d41c0e494002c00407000c50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 320161384 1250 320160134 320160143
    0x30a02030301051f09030605060d05012906030c04140612011d01171b030f0f030d050105030f15060607050114070909020a050f1b07030b040b0a020f3112 67
    0xa600900300d101c07200e90021414040e546440a171182103403500805014014a240d400c80301d2100d0202c0040d000340b044c01e00800740d0740c0325841540d40645000c01d11212088100784107180c02d000b44400c81c840401140c00f02c0f0004601010b03824418400300da154052044410340182481c000058403180d940c010302c0f0346014014900c030082e03884160390895024882c4880e04180d024014040c2c080481c40070250090600804035401000000d070240d07c0c0c01d1481c82600216080130030411a40009401410301401e8110064a070701c01040109550b26401c510750420800110ba0201e00c1036151032007100d8425410000a0010102070000582e400905552210008520200004a0000920a60700e1004d01c1c1d540e100c1c5000580145056140c200c440091304084812005008111003044880f0045224420500c01885c290500092202e40200081c003101d00410101c18560030b00c90880725a148000c0500307402943e0041c24640001000c442c4000d40002084089507501c20001c0b28105c20b8801c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 320162634 1250 320161384 320161399
    0xf0906070f02090a0207021528020f0f012a020d0c1b06020607120203150d15060806010315020703090605030907090c0c061a0120011404030f03051005010915050c030a0203030105 78
    0xb500050b0503c0c46800104c0849841c27807494074030a00c0c8415504242e104040c8104c407801d520106031141040e21902244003140e55804a418460404000c00b015007a0301c8604403000041001000e91910880f0300800c0c2042203905510040003058040760b94110810307485d2410264607040b02a654200507546080442c00101e1b003d48032a1050084903c03601c401102510100030070018000780b1203e101044680d109182c00c0d14040500c184541c400420401001709110351441c1490420060034412031000c242c010480c0c000800c3c1c001440314201e81303480c030f40556203546034914142051340f9078000008140c104014007040c0c036804594040c0c2680186001c210383e4081c141c0d8500389941000c1580d011501e0310601c400a440804032200c0e030901d10b039002050341c1d04003400031050294104c4040b800324404010046280f5418454603910170580c08100e084541050000703002d0410364801d412098900328005c0080324800c0d015100760044901c112a1191540d100180d140d0f0001d02415001c2d440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 320163884 1250 320162634 320162659
    0x20a0b070c290414310f020708070501060501110703050d0e180108010507110102130302040e07210b0903030603101509020403080c0c01090b0d0902041407020706090b0f0906070f02090a020702 84
    0x202c1714211543c22800c0e0007080780100c9030480580160550ba010a0301242d420712143c80402e10500061031140d1050000266103400c14001400d50380d12840c4160003640510414000901c000a0300395080c1d10900702a8000e15030440000c649460490f04200d00315a16800010000d005400860041c42d103916030b40c000380c6015684071300301d0045035000754164005050403c0942071951142110000c05420307a1170440c0c035448030143c00c00e000c0b11449501c20800581c00c0502c0000703601585c010105901a40c0745040c00000260340d60b211030b81121110b41c0d00c60241c401074002201c10380040001c50820364a031940e90912044139084094650b003580500e829810f0706612600a03403007500d0401041600740070000070318400810544100b04d03001a5203d03843c1003004400c189985c414440d5030300034035140c0d05102d0005c105e8085c651110800c1c0b0790078894100010305280c00d49401280959505d9100d607403904204080213a44070010790403c5441c0240035030154583c0081080b00d0090b20814000035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 320165134 1250 320163884 320163919
    0x9050a0209090f0619030b070e101710081501140607030206041b18020c0f0d05070821090a060605030304060804150b0405090109020a0b070c290414 65
    0x10031505034561041c1010700091141c580d030b0b40d089800c080003410010504160a85d0070354000358541054030501604c4c81000102c079401084219070b1801236640409585a00070702a0030ad5010410380308101d1201d6000441202a03003180342c0092240c0003c9600d0007048040c8010040c0081c00b4541041110b48001401070915000b1200e90300d03415401001e507956240c86126108030440d084c10140f1000c25000203078001c0307107a101c014440d500c0e40010381ea001921142c92400300c2040558246400c80c00b864100ea54001d0161140c0581100c142a0744200400d09407072460b0019083c1e00c4040500001c1c00041ca00006400031928401c3c6000c120b42d90311582003660345c0c065072103400c0000360b0fa4400500001d00240310201340301841603011440c981810001001d85100300e83d41001a0f5540001d0015031425900703500c0105400e60f412490310005458000d04c400c082d0041407845e03480e40c80d03a04060081d02036411150000685402c0c7c9554a661220102100c50f03107905100d82501c0000143d501c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 320166384 1250 320165134 320165137
    0x313030b1602030313080d05070815090c31030b1605031311042c2a06070215040816080d091406040f0f080f0d020c01031a040f0609050a02 61
    0x407074458005600395510507951111a20003420b0840b80e010040c403241c3c1c2c1e0014280244c6000700e0050702c4144881ca042e02c0c2d01e412541035404642d210705095424840040848811183d5403184003c4180f04004c0d800c81140740032145425111090480c46800002c0c848502003241c0190400d90750061841c00966003282c2d90300041c1e8200c80500909082c0304005200424035210081c005000422210f801003408015035044000018140c3c5900d8601c84443d2028045040c4180e0a001100501c425144614040821545186004040002d4100f0a554901c64200801a1a0700311140d0700c03a00d0b103080c0382d1550703004100725420400e03482d030101303100303802094140000074565902c08a56242c1800c03400800e40d40d01c60113802000801002c9004042c0f4060b44010b407034426080a916440c003040185480e14011100d45590000020078445990118164000d86000d10b13000c140c5661031415100e0b405101035100b54440d1402c45c4404268040b038100070708540a42900300b21540d140c0d032425042c5d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 320167634 1250 320166384 320166421
    0xb01020a1e140f06060406050a0b1602040207052b03050f04021306180e06070207050d060c02010b060a03050a110c0304170f07032f0d030e01110313030b 67
    0x2512584508944451100062441260052110188071454075001e50f0030450600c1d000315958200008001542c00d10340288030090034181c0301810210b14040706108180120544120048002c085241c19942c036601610b03071061300036050b40d10040e01c0340140e11755508500b121128828982041d820903500a104151062100000404183e6071303550030411081001407084501c95558080468403c1c207402c0305110842e4407040010340e0962081416103020070042c418811580700d80030a00140d1140d55810031415400000070891501c03440341a80503014074640140c04c00e202140000318550301d81c0140f8040e013610401000754000d10f44e41d5910f20f224035111a111a0710400c003c121072240c18070f211000030301c0042aa065407401180e22410b02c01d0582c002e445100d51050324403009030788101c002040c100c5401035880004117050100d07100c004000d40150611141c0e5412101690040e51401c0f55146840140c0740d03103840c03404802c01c00d03051034081a22030001843c00541c0703a40020720800403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 320168884 1250 320167634 320167643
    0x30b030316080702041506050408060a0608120c01060e0a05060907080103030206150111030d061d1b0c010b180106030e1b19030c0303020105240901150c0f0c030203010b01020a 77
    0x44404258942c551141c0c40a07000300e030003550311074501000203950950180600920703900d8039581e51400221511b0f01c60302a00008260b4a0203c040144e00c1340085c00002d402d40c4101903d4660100c1f04200b030041c071003030707000905a598074000c0110200c02c6510041c401c00e0101c2d00d040454176202400c4400f07032824000100540d1015000c0340d5008200d50100d141c0800525055101c103a8420125085421028401000e141c80d107030180950388410990789081c48114142c03400d03d1038201c1c1d254640100c4000000e100110002d08400381002c02c3d04038403911140684030070300e2210b522000a950303490900c901030000b45401d420440200c00407078043d917104888034414203c4011a001c02440c0c10b00005103483c2c4200c500c00000000742c074400403030015402a000010146010007200100070003007401090b83c02400c0114880c90b60382e8401c810f05640003480d10503600d80d498101a1040d0b415018050032055101c00e0344000c200500303001c1d0040e030b40b0070383c024058184c003000160b0343d4120b411070041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 320170134 1250 320168884 320168917
    0xf02120403121d06060a06021605090a112a07060c0b150d06020a0f0906020d08060102010b1503010816180b011b06050603070f0f1721030403030b0303 66
    0x200442d2040000441c000324240001424884041c0d6180078802c0c6102c0359440b5400940c100b15040c545a0042c00092401d80041d000300c0d201c4000080401d0810300034144500e040c00c0105040c2002980022482200c0078000f030f640c1c40d4407080322104a031101180c112040b0410402e010b9503040456580111072480c3c6503c0c0b4481074554690340385620003408070040004034412300d40141c0d19013001100c042d018090060392120001c0005080e114042000b0302030201c1d115007000200d0f400603281c0c100103403902e4803d000303848880c0100d01400c0422000bd0f4018890400ca400c8201d8a00045048940c11401c444950044041c0607100b01c4071071042c2c2080c91103601052010a00b0b6800611280d50149803c032410140040d900048030340c40c01003501c00a90f02c0302008402d003020891100a0000c1074850310301c4078038014040c0c9030b401e01801f80c051111941810b8007401c41381003000b80d004a9403ca040c68807203a032098081983e80003210154006828820000c10301d007008012103160700250701030705 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 320171384 1250 320170134 320170141
    0x909011a0409091a04140c0307030201050a030504060e07060f0e0f0d0213091a010501120509060a0e0a0c06031509020405060406030528020307020d03050105030c0108060a0b031302040f0212 83
    0x300502d1001029201d02c522500c1c004d205945408005110714800e60740c13800d070340001c144400d24008400810501a038030142c428030143c0e800c401a43c401e040640390220b00d5607611714114002d0700446000ca42d8501c22140d01255082d0000d1000401241d607030350310080500d80c0020001600400c0807943e42102d0f4400ba140094108030480484d080d00b10000803440000580d601c90140e030071407100274080040100144400c1d82c2c41002411210708210040c08a4104140039580f40d1401038805040d030f82c1d5580010034490800d00030200e613180c2004078007150343c2d690b02c030280c080c09140010307003500c0000c03032004510185140309540545001900300c6003030171700b003170f0082e0700500303010740070700141180ca41c896050104000509003140289000140e124100380c5806481c000b101505a03050500b440c0040c45540c40020351000180000d291441c0f2548821000c26810241d540290050040c00020840a510b0000e12080300b248290307010420055111080400c078010b0a209015401d05034012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 320172634 1250 320171384 320171399
    0xa0b07030509030418021e030f310b010e0907031709040f0905070311010e030c09071b0f0b070c030f08060307090f1401080106080d12061a0909011a04 66
    0xc6511086039000c6a01c0c064460418022401000038a8100a500011108450510319400030303c4190f1f548a460b0031420301900099480328000c0c00039007c0317800110014003500351105101003e1810f14580100c40c2c5950600000f070003801d000e07601c00c2110341c4012074400000043c1410440350418950300318298410f0101c1010740c030010030b286d801a2a6039400c456407600d44240008188070744010f0000c949185406d0101407542c42ca164103104c0c1505100b412500d000c03414074054942220885415070300c010301901d0034280d0380020254907542101101c1000410b0403100744560148040c8110703540c4052040342c0000203140010001840211221340d00b60082d10903903004100101078420702a150b0703440504840d16550031a01c0030b40c940c10403d624418010f03c160140c411000240002c0b03082c45503a9613260b800f1200d4500b0806581d0807901c800da8158001800f900c0c1d117250000e4400c14000b0004529008040010701c04c081d008000210034050750500d04501400c0f107002070400385030809 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 320173884 1250 320172634 320172641
    0xb060d02120108061b181c060b1002070e0604090b010305160e040201050702040e0a05060a06140604050d0201180503030703030501061b03020d050a032403170702010c060e0c0a060305180a0b0703 85
    0x48075100c10b01100130041c1c6d5039650410800351240c1c031203000402c41d4100e04151094840051141e8000c509445d0851400d1f0350118004040d00d80440101140f920307520003280041068510140540e1803010022080080200e140303917032917041c281100b550305d071185101403400b001950000e0114804201741001810940c1100c0203070301c00c08080c0c070303842106500c030107080c050100c0f0302000b003580c4d910041c001c1940030b41c0d505030300c0344058038440d041034103110116000c0000c900713020341400f5500c482003d62100c00d030040b00103480081c0542c1c2e2506010703c0c018000d49030a0103201c0204074500303207040c40c44058041240c0e800740c060f4001c01009a80c0c0c40e09581590001101c182016224174500c1e44035500300c4401c0045145e20348110702c416107582041c400c43d1101010b8003103120001c1062401507030b841144001c046070070010014440c0aa410a00d2908110340c0f00d85421100c101000902c00b074040d03020341c4c8102800103101c8811281d21a6840c2c6410511600805140140d00400d003201d00c00d50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 320175134 1250 320173884 320173897
    0x50301050d1a070e0a0611060f180714040b010503100b1605061503070515030a0203071106090c1c0803040602130e09060405121911010b060d02120108061b 68
    0xc44030100702102e00003a1891400455101000c01e2508803140c0b41420b0904099000344014501074040070840c0140700e40311349024080c1c43d04813142001103070191000302c02d00811101030804070303510655981c120300e00ca107540500c0c46100e40c1ca400118041c0e94083d100310b07032048901d001400c05907410407115440356040341c280107000240d00c0144200281c8100003540c080c1c40c02c1c144421256440b1403c00d071414000780c0000b4090564039200c5401d4080c030f081581d1b000301c2300741d801503281d65070303244101c0b201408400c485810380f05c1c2c1800d2200e012400301e41e00c19644400e4801082d01480310075007040e01e1000c500010041701c0204001804510300e94060721286070134504860420f41e60351070410f41420251400c0702d441c1c00c01070074007040000403c0503400c0c1001c4040401c0c10036a00c00c00c060011428145084203010080c594402181020740c06414101401484591180c250810f0017000350000c40c08610381d40a0600007003600036000515501c1000c040c000203540300400400c0c91690340107031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 320176384 1250 320175134 320175143
    0xf03020c120703060b181302010e091608150303070609150905060106030c0c020904120c17091c0c06050c03040503060f040204180312110d0507090501120606050301050d 74
    0x11802034541d212003070304041da0507520041510600b1030410300304440d40480204d00c02e264020000030b1640c0c0d00c0c002c1035800400449000030004187c0016507050494900725617204146c00e08003c292500e031440c1c00c400301c40c0c60f6205900d0350364024400c1500309040c100c0aa00d80d00074401000021080d8000200d40d41c40784840040b600e107110007920a640e50301e0011242d80c2c010300010f022960341032290450114851400352070402042d000716414a8010700082e003d504920311848043d03008200490340c480d0712810103810414007014500d00ca0b0420501c1d580303c0c16403284010001c2040b401034400c1582c1000b06da20780c5624207002658154030095003669980400d00000441d9a8180003141c85181406491022890140b04210455030359407414804100842ca0702e8011036400032420004160502c0005003605d06501d44142c24026001542c3c4924181801c0100c001d504c8a80d10007202c8080c4c844400100c4007050800c00d81f00e1034081d1070001142400104194544813000c0840300303004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 320177634 1250 320176384 320176393
    0x170a0e0a020301020d0c080f041a060609030d020c032401060302090a080607020a0201030b0402070b06010503070c05070b0d1424010509100806100504050f06030601022407020c0402090105070f0302 86
    0x541d002c00d0aa8100030750a0740700342d544070340344020960042011a4030000e44d5415018070315040e41e9100003a01c0306442c2e41c044101c440c0c0054095100c0908641027048007c040310041034549500070b54070365080001c00c1c0130340141d00d4184041e036009400400010302006079410715a003040b40031130083d0400011968403003c4240e00080c9940c007803109a00031660b55018001402c3c580c0009010744020401960166104009610101d00700913086a0800700901c0c081d543c0380c49a035800c80700121003980240050090303400000d104250000248400385035104e0910040e4400901c00d8001c0804a64001144038000b403080950510b032404061310780b00506003181001110404202d001d81e5041d20400800c030803000348643d80c68155040c4441c11f40b20318140d8a0941084080b078200749420302c00b140210004404503031302c1d81c000c5c8442c0004203441c000b01e2002220f80480024144019035800c009401818107200090900d07008450b180a0180c45480c0380454981e1411202d50501c502901140074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 320178884 1250 320177634 320177653
    0x503040b070c081206011d0904030c030e030f06090105092b031d0c03100e0c040e030409090506150301060b070206031b030a0b04060b070f1209030b10031101170a0e 72
    0x11424040c4c0003000c04103508030960305d415070014100491460751001302c118010358140c01e0342d507290600703648164103207081100c8403018601a600c030010260b0b903d82c14000e8100110070400001012440b0700201c50090040343c0f280e0380320644811880c01c00d10540640d540100300d01a4681c4110301b0100214a4005001c1100300b0700280441c828105081441e00000342d500030600e020015a0702c5800f080104000b180030810101c1e0740d546c15090501e01498030b5207000542c841060007640c0c02070400302014000c02989140040c0c40d5202111140325090b0021000240c03401d0500c120320540c3c00d5120f403280340210513020021907401c000d1103102000d04141400040780d4804000d1409114001c2c404110081d83c40c040009031303015900003440c10030090207007002261118000d62941d9400c00c3c0c0d0304a045000c01e508668164140d007015020450307880030f00c11440e50218803603085074001c00c06503029016410045540e640c9000c86011501d01c81404202d4405030b550250218869a40c01c8406801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 320180134 1250 320178884 320178893
    0x70303051e07110c18010302180f13110406030807030810080709020f071a06042f130f0b031603140c031f080102131a0a03020d060302040905010b100c030503040b070c 73
    0x80b01d01c040c0c645c0100e2400100118203201401e80c010440030b00040d012480c00885c80007859000a2003c00e002a82665140512a5070146100b035440041e0091012645908211a50340d10903d422400209600c00068900046c850ba44050ba4605006840c4041c5801e94001c060b410000094074484410041c1348002015400c0c400c1901c1c07401000349583d40741031410003080b0b400305604221000e4003044000e0780d02403030308450410850103140d12621001d421000215040c0540c01249115818540120b402c202e0724003d117126407010501c0450014070b405d0210165089980d085d5880d05200c0c0c0400c421101c0300700510340c40b0003c0a039003888001801c05100600c4200c0d40448580d9500049504483d003c83e42c2c4503001d4541804d0002c1e0000c4442c8c600c402074456841101d08056001c10998030303040c02c941114000395001001400000d14504005000380a40504030f8843c82003041c01d004268001c0d0b080c0d810003500b58a0792401c59803161605000c1e020018010820485180f14800028 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 320181384 1250 320180134 320180149
    0x40807050f13180327030b0912030903070c0603111c18030e0301150810050432010b0102010b0a050f030f12120c04050a060509030f030a05070303051e07110c 69
    0x83c4503030b29102c40042c62401c0140c0400041c81d19802d4035421200c0e0080c080e9051031803030040301e902141c010599620440e1407800d208240c095030045000000038440301d00400405000194058210301c00c0c400c1c1d6503481602110002c5168818110045c0661414000e01400d5203070f40662041d0042141e99500c0c0c0450354201c88000c0440106004082c5000c3e1400c4c00d1180c144181d00c0d000740460b115080401e40750351941c0000c990071280303485100007020440c2c981c6800c014103416011070f0802d541942c40300c100001e5102c00d03401d80d039071800b03080c800e442d0f02c1400f401d514080003078005100d2604000a00110713001008559802d4400c1903c1070490030700401800d000e000c00c5064540e291242c011903448040401b8125000001051009012a903112401c0e1021504d40e81007169135100b02402003814254840801c0300b00740400300e4031541054201d8020007c0741d1190b6001c02040e81d0700e10000d5101c0c002150302d110107020200015000300d024044921140c011a011100006607040009021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 320182634 1250 320181384 320181401
    0x9061d060c011a0f090606031509100602011b14090a1a0712020708061303110607080a060b040315020319061203030c1d0f0a030b0405061b040807050f13 67
    0x59a6407041d10303800b0b0880e003c0c60300901040c21180f11014005280009124031400380c8094814100000826081580300d50400c03405000a030a000c520b1400c0c010040075040c543c4106000742d42040c0800d02c000d1000322841000c204252a0006240d1070b40e440d1000540000000540003686280d002c903035000f400551124020b140c0a40c5507641d249441c00d0180007441c1c0c025041550300416043c4209038020850692004001c2c9032242900c01904040f20501c0001c43c01282070b0042c178050240c900d40c032000300d500c00c03000c860042c0080c60355103507c3c03040f6204a00c805055007440781000c4a4030140398004541010448001075000409100c101c811642160320128094040b441c0b41810140c0500038802e0b80e07952400c1001c0090700050001d4441c540c1690854480c0c1d542d101140302d280c0d26420054007541e000314102d02d4034640751802a44d40c000540e24121061501e0049400300e4100108031400e56812038082c080051a04040c0256030210010f0303c1e1380085091407038000030816200745820f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 320183884 1250 320182634 320182657
    0xc11040f020408070503011b02060403030906090b19060f0b09040c11100e160617190c020a11060306030a081c020a0c0b060a05060a0e030f16170601030309061d06 71
    0x5006217408109400c45040d041c0154003181c10740d80505010ba0041140e03a405901410040b400c64103a04e003d2004041009000740007100c54014420f220075900d204820b2164828000c0098a440e0444808011018460a46100ca04201d46d00c4181460340010510140d14140fa050551200c4101d50900c00717090482d424556481207a56000d01c0e081149020984010547c00a5613003844001841510343c2020011810040340200d00c407003072802d4600e06d0300c4a181000304104100884025110b810000081d501443e020088050901e0281c088a014590080003010311582d6955103202d10780102441c4810400c50400852048815000a1010703014075994400010348a02e03202110f0710010b070109014100e681e00900041d1200c3d011602401a18104428401ca02c64002032800308841901d40346405040d00d241c00d03035810603620784103a4915020310b06425442101c17203640c40100344170240024402500400801c1e00402101c0d451a03a06000c0c940d4010500000c54810b5000701510301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 320185134 1250 320183884 320183893
    0xf11180403030c0f0e190b0406091410080f15130501150315060c02220207121803060903020c03070609080705040902060d0b01110706030207021e010c11040f020408 72
    0x4200759051050506808050515407001c0c100b4820040400e0103010140c0d005220300001c1c12064109040240010100b50010f01d64482e1509d000a100046520580c914185c607480c05203028600030300c0f068841002070780c581c481a6900031500f00100000782408406a000c2c0300900c0181d218140c4084208903d0140400e15501d8400c80440000e1030108046c00c00d03140001003154442c9074600c1311b044030074610300b44c0d20590b8907000041c410500501200c2180c2600d944045c04c440a540103044810b00400040b034003100c2d052420f40740d180d0102900759620406440600006640b84c1c4941507183c02841102c000345409400b09103040c0e00790700038001080f8003600030490281e003000340f48090305050300c2c18000c840c0305a000c40c066001e101e02080000d52290001d200c1ca9120b20381480c000c10060003100c130401e590fa9070140c025402900168001e21001c0a5064440011000000d1b03440d01a520300d280d00c45540c40300d10b01d030000c2442d0f50b50f005803250040d603131010550010b440234100f40b40150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 320186384 1250 320185134 320185141
    0xc090c0c010e010b090105120d050f0f0c0106030605070f05090d031407110301150302010c11040b10080601030b0105030402220b030a30020303010902160c06050a1404080a0f1118 78
    0x40100c40b170581c0018070030400310a041d52a000c001c10380c8903c1880d642062610340241d070582d4030290181d200703144000740780440c4031900e9100c150060f10032a800707450100026180e00408580810040c00c051021900400180c1c4c1c0034185107001c1d01c00d00780280745c4040120038460300340d20303203500c03182c0c040e15600c1a05980b001302d80380a125200340e12075200d0b10900c1030b5103140c2c0040c2c00288003810143c030607115404140200e8942d50488002d1940080100144a0616602401c030180c203982450000e481e003801c1490035401203088a000781d4009080300381800c08102164001d0981140d01c84010391590059a020b442c01c000b07807035085200f00d8541409142c60f1080c41c1503e102c0c4202140b600f1a840b0070190000e4011040300d0541d0802c000140ea518031501190082144000700188420340c005030020f00d4560040141062141b2982c600703007901c1322401c60480c540214099a03400740c00c03c4802d000092209121350300075510071141400008406000112401154409000314200b10400c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 320187634 1250 320186384 320186389
    0x8070812150301061409250804061803120c031d03040501080609060a0611161502060a1b0f0c020a0603020405100207060c02060c011d07170a050c090c0c010e010b 71
    0x711500041500200412490145100641891000014061855800420340800c1c04140d80c0c2224440c2101d642c02c84036030301100130441c1c00111000e40e204d81c41d010700c4008082d641d0600091140e0141c0d01c60304d19034540102c0000921011078000b09040d03484c0350050018032562840c5d011003a05c0c401854aa0303240030300140a0a40060226204004610030080079555201e107010a40e03c0302d241c60400c101307800710803a00d841c0346204041030b44441414002260840000b0745046681c82e6406e07504c554807040c4140060b150030300096000040c4074046a0307445403080760034800074200c6141500054180c3d80100d0400f000036086040040c2c0c00103030520450800741c004583e401143c0c4000d201c00c45c5062402081c1d402c03c083c009101e02400624414030440075040620400b08044504406130350f100f40265070b40c54148500c10744006599600083c0d018046035080718580c00c040500020007030340c010002d0307070380000b4030b1300d200c0003c14170a080490f002440b9848141072104000a01c0d008040708 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 320188884 1250 320187634 320187661
    0x6041101110102070b040809120109050610050603040f08090604050627091e0c120901090b0a09050c06070c08030a020a030e041e0c09150216090c0801060c08070812 72
    0x204108283e004100e20b60000d514440c5503540203070800c415a84504008000502d400d08002c1d8810042d801d004401007400004603101d402082031600c02d001040d501c6c402e0258502086402030a8148074080380004982c00c03500510719100c005107000d24013070700d5000041c0c1c0b54001189030886035001052010510092011000308540200d03220b01c60751418070401448180185040c0800c5042e29001c1103040304034009440e000314100920740304500d00242281d00801004509031000003085012500301c0109104107100c1c1900280a041c1160b1200c0c2401540d40c82401c0c12180b80c2044031000509220920141c05104886e03030140001d0206070030000e104000404010703104600d00b0050140c2080310508052440f0840c0304003052101d058003068070203810a501200820150040f0040042d03030100d074880d0084000e0f44c010301041c1d01d4200007400c0300d13900d08a0f6804200000014811240200940848248901255171038052076a960344103e420442e804024581c01006016281c0d00c01c03507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 320190134 1250 320188884 320188907
    0x170f0706050705130b1309050103050c0901060311180303040506030702061506160f1a0109021b030a1403041401060b03090120030118062303070e0403021f0e06041101 73
    0x6000e44c240303980382c650f92844034030342e100700034110000150441002c0800d6549a004140b01e840c100099a52404c0c00340d203e04604c00d40030310940c0340000210b903d80c021b1003480c0300b89085c070f007055040810120252006805e0990695854442440300240030740d40d10004601c1141c0c9030b400f03040d00741030991040b0043e5012240051041c5428018030701c050100f2556601203580000020041c5840c0d4140f4400182c60f00101d62100707002c0500200381d1001540042000ba964007407009503032081d01c1e040a07201d000702118007000813204040115500f0108015580042c0525510390b04180184904da00f100d451760302000d010340002c030811650344401c4c850341440079007017103142d80441c400b03e00b85061880705004001d02c880036180780d8400340d5010303803003c0060b003e1100785840e02c104500380d0000c010640151944288034255000c904e902c7c0c22407003d13000d994140c0007000000c42455130001d100740e20809030090b0540c2d50100705031505c070801c60b01d80518020701d02c0d080100c076032f000014030840303003034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 320191384 1250 320190134 320190137
    0xc10020303060612060d050a060c140c070e09100510150f0e010f120603050a060608030a050a03092f1201060810020f19030515010c030c0b04170f07060507 68
    0x6108100a60321403d040300c5a103021041008403590b035000008544a40003040680715105664400b8204241903000540b070b50360300c0e1034910a0100365401d500b21486011070003200c6030014102085803190030341c8115004407010054500110803025800d08803030701190b40c42d0051035140800c02440c0740c42c0031503001382c040310724000718410050100a0451000c00038003604202c8401c061480203417049228120450016005200a6036281051603480802030019107244e4a0140c00041201e0000b0441c0c018082c2a1100c90030210b0080c800c0e001418210002e481160308250310000c0c5800344400c2d02d0000d6041c250f11103285400700e05000ca401030545500615070701d1700c0070504c5000000111162408824800569903031004140c1e4482d502507042000440080f441b1f100001d960543c210b0713845092510610105420454011640903a201001501144200401201060078201e10f540d1247c05a91802d1b1814068071202c2110b80c0000c0042c21401004034198080200c180640c9412a509 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 320192634 1250 320191384 320191387
    0xb07050d030b0603040b18070515040e07050405090c0f0f040e0a0f05070207181103010f06030b060909070815061602010813020901050111101b02060a110d020a0c140c100203 76
    0x1035445070031b07508020340b0f1450b88200400c20344a0f001d45c1040000040c0c4000f5050802003d03100e04122a0b9801034000c2d405658151000a1640c034031802c1034a08403600100783d011541c48051103609154040818152a1041000513076408080c010090005042c2d8900e4100c1c3c514200202d0b0701100c4851009041d0a400d040078040c10903400a0366a094821903882c8c80c403d00078503401100181203442d82d0307240950b404000020140c810524000460b1104e880a002104529080000e18803a0190099001c8405808140d400d0f1281041d070b81d00038105840400c201c12040001000c94115000c0d240f65407038441003403421541c1c40704034641c00102c1d40003902c91000300d6a0000303401980c1402007a0401441d80c0c0f1280d041c03141002902c8001c1c1c041101000308001140c00c80f8900c40c2040e4407080584a054049130313170030009100d80306031200240201c9040c80a419400d170042d5103c55050010001c08807100e00110306041012030343c050b00000241004000740047c007086146076403181095400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 320193884 1250 320192634 320192641
    0x1f0f0e150a0b09011b0609140607030603030f081306060906062c060901050d093c02040b13050a06090c08090c10090803120a0e0c0f0f01090b07050d030b0603 69
    0x1416080e252a1070003420180341007840703011742c000400303103140d00078040c2810422880140044600400502c8810405485032540d45820503005d48003540b1004002844600740c0c40e101d81d106002d40f640048a5030f905540c42c400a4442400342d40131a0821919560386080804ca46500045183e010500140c81c542c140091f000024820a140c90320350f0303004120004195403203078895002c0b81c0c405d1040f04010080410542000c1c02006d8099440010740403224500e500c500700d100042c0400c1e1000380031001112542d981c244005408020300690300801c40f140d01881810342070003002c0c803c0c203501030000b50b29441c0840e403074266204041a941031022003001c3c40074010b40480d941206581c140c071006496100c01504882c2c1e031800780d0107540c6a000c0070480c2c0000c00075003481c0f680903d2004909124031201d00d104282c450044c0c0d206079500c00386101100d903140c20050300840e40c0000504018080f0b0340d403a8410072640e031049908903003a80050300c010607000c2d01845000c40343c0006840c0c0a00f94034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 320195134 1250 320193884 320193899
    0x100e0601030f11030d020d03050a05092d030a030911010c170f0405060307020606030d09050d02090910020c10050901090b0a0213051f0212121f0f0e150a 67
    0x4040c04058407050074101d0002c240580004880309510010b4102d503144141c0340707030080d00d41d582000420006400c0c10017140100045005080c091500380020301060781010151010400c2011408040346035400c241e114261414030103860f000340142c4010030740f24a5441c00d030700c50340390320307425141440142c0c403401c400303e0885c41800030581500049150b40d03103071000e813195050203694440c5501c07100c00401c00a0080d4042031480c0030f0700090782252450b100001c01079900d09260300405030408140c1c100c441c090300e030541c00030742c01c020100f09031140b00a0020500c1c050341d200382c010101540c082c0c640884000c80521803581d02a00b500000c00ca01d035059510426060f0020f0440d220306900030500b04031401d20624540c0040c42c0050178410583c0b4001d41131400d100c240c4000348050b0180d140d01c403072107204480c1280c2114680d440641c0c0141c0c0d40b290610404d00360448442d09401c03400002054420b0326030b84510250140b21400031483c03924145030b04480c0d400340b40d02401002e80b940f0800140303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 320196384 1250 320195134 320195143
    0x61c241505030c1e0708041403070503190c0f080303041a0c071104020918011707050916022514010309021f0c170705012003070f050903011d100e 64
    0x1141c8808660742c985100580048041c0c0039464012084c4000440c001004200d10041040700e196850300c2d6198007907481090f4440303a42d0b20600b601900300e040d0803041d02c0888050030714402c1c030450701c103c9240d4990b10181035024081e0811200d65000006120030b00c04810811108900303143c0c10148689008000420103004000000b401c0d80020b8003904400c2e035490301600c0d041c2c00b003d400280300e4a15002c40c00380408082c03040c60300c1c410404070111440032004c02c1c900e095070005001d408554441c080221208000100c1510440c0141400800b0000035043c40140d841d0700c01807804800c1c1e09040034034101e0341140d103500e0b050501e852031403001600c903964082e680081165080100405110003941d9484a00390700800c0f954440040591002440e000381c1b07a1680948000c1207408440041c520340c040424441081001007800091111132107000708003007038105031418504103c465804242918042c05c0e8403044210121407000d007482080181e1000361050720310500074151188881ea849 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 320197634 1250 320196384 320196391
    0x20c0721050c0621070903120f0503060904021c030e040c031a01030c02120a030e06010e060901140307091a090c030601050708030919050708060c040e06061c24150503 73
    0x42e400441c281d038400301074440c902c0c4540c00d5414244078618112000511201a80c0801c0b11a407281c0c24840044c1c0d80b0031a00642000e01c1d685039285992202c0cc00c102c80020010000c80e40442540840c4002c405080e2815242d071384651540700048030841c0411098401013001b02c020076103070004c182c503010f007058100d200e606000e003000181a490b4070012410802c0260b190a112039000030241d1078154035071702456480e1480780a6450726600e0b0001010030102c1951034607402100c0c1c10040c041c1400079405442c01707000003421100d03800d42e02c0100e02c0c240c4010130149070300041491051001d03410305405082d40300c101200c0c1e41d032651901c6400a81580540000501070000220000344225000c02180c0b100702c20f04800b456000425260041c0d85550a01407c41c084c0540340104260b00100403d81c0c055450000241965a494606105c0190030051050548045000e101c090081c1c0b18410814101d41d409103ca0100f60a555011400d0900e54058086040b40031550100a940142a42d40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 320198884 1250 320197634 320197639
    0x3250b010312030e0f030405120c01211401030b010314010e030d1503020312191e050f0d0905010506040b06070b040b0903070501060f230114030604020409020c0721050c 74
    0x500345418003c80c02452040589125849000740101c0800c6002000c2c2045801c125914000380c0f001034122515249191026030110304030240b625403900d404004800c60140101001803103510301319040446400c2a03100740d612250b401c005105203c46007245a04415802000384030407464041215640e11410f00308142c0e00d0380d030b18040c0e095441134690045c011034008003101c030760303100b5954945800c2d44102058200500183d030b60004050103082c54401020444140804926160704241ea06a11000e590304500c181000302c0f0400498030710901c0750150060000088074900b00080c00111920151098480c460a026000020b001086410790040c0e00180b062000d8460784903607840d5019400009219509010010825156030f217030340c0713080703640c4c4602070509107460890b080c00b0413000b1340310b080c00a20105100c1e01801c0580000359080300000e44018a81603071100c4c01801c9030800d2030050902e40281c070382088100444034644000059003100003041c59001d40c0c81990352064107510a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 320200134 1250 320198884 320198903
    0xe010e03010e010e01050a0e120d09030e030109030c02031b060409020f21040501150506030a0e030d06080a02040b010513090e010902040203091f02030907090902060c0f03250b0103 79
    0x4000d44080d0000040c0414620090012001c041242406048120b54003504203250409a0a01590019840042c2c46040581c140b0344010850948081c3c900300c80c007901030191119030741401ba1001d1040d85034450180d074940714544182c2c41014246595407906202400d040d8200020341e5a540f42140d040303940d0300c0c50060f528003504c040e2031082d0140c0c01049188244034040140b0901c42d031b07841070b44640e00c9035000700410080c20585c0d40310101c2c64001c16030407003414400540c22000710b912140002050508590030311500190b018103694080d080030700075811905220303045081c580107003100d00c40b0034240709080110702c1452040c020f04502c507400d600b50301d5110f84a01c6d044207521104455402400c00d641d6880c2c031041d01070ba0f0b5005501750340413400c2501c820040c1c1808a01c00e880c050750b8041d001c0c01c542ca14256107a00644001032003643d003e1410441a04075880400c1007000b080040005940c40f030400c4411b1201015803024070048545800459900040c80c002101e030640c1da00c40fa060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 320201384 1250 320200134 320200157
    0x5030a02010e1b1909020403080403110603070834120b06030411130908070804030302190c090b01020f0106060305012c06010503071205010902091009050901062d050a1e0e01 76
    0x78a5410ba075806100402c6c40000c0100501440d000140142c0c2d0140b07072001c030100404401d000d0940300c03c60361680002c4180011508401d0b80c2d450b8442e2040100108245220020390510b41c0480c07030081d42004644615289410350506001e4811001421030b1064250b01d056100c54203000562481580b1840f40c8450802044005a00c040b0800b508502c406803550f8175460150011f5200d400141c000d07224100d2108549031105500701c42d955401004545421700c4c010100000d002525151815400754141304035002400344144001020a590081003035450003a11258064049030182d0a109055103004002e04200302951340010303081c6402580c0780d90b00074084608080704071200c07803582e041000004804c0e625401030a01750700101c0756203001c13448001c0c00360303171010719441600c0c5c02c4480711004014240c021100d603001c4400d80d100c003121141000c07000f00c0c03c1b00920325000300401c202050440c401c139400380714a544485859641d01c4031841025016011540c8080182d0401403140d04a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 320202634 1250 320201384 320201419
    0x3030304060905031611011416020907140d0b1906020607121107030c02031e070e060f18010311010f1d010201270b0916090b030c0d05030a02010e1b 65
    0x5c917403031420003650691a8082500e000342144040380103490001d5525201d203a580c10550003111012060b800481070104815824054540d41c0180548244001a4035401b40b2400d1301000304041e40b0714050000303107a03000c081045210035140e00c10308200d00d400401444441e80010749030390810864104941c4404d0001c0020016003000f070326402c642c0c500070a00c441090380080c80300d0700b464401c406075008080764680c90340c041202c01d101c00401d584005002c206440703c0421494214034082d100c3ca444841100118102c07090040c0303480390106030a001041842014003a92260400c2481c01d00c51000c40c5090090a0b10215272104e48600c1d101054559907138000d600601005d1008014100750114580095a10307451994007a1002001070001610811010850441c140c00c40c00c600c40c805801e02c00f1402c010319180070340603007602c0b0744d00400b003941e6242d40c2011801841000107643d21041008001e00391200d00700d09114070b9100760762400c011142c1c00300119035100d094415003e034400d010316 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 320203884 1250 320202634 320202637
    0x130f020a050a03060c0305010803030c0403080d1107080a08010b2718190608010c08070c0602070516050102370c0e0c0a110a02090a09060e0106080303070e0109050303030406090503 79
    0x407560040d40712000104100c019004040311034516141000385a17a180212901d03840120340d01180f03104200028800100c0342006090380e0895284000342c030b0012802020b00c0e9501ca2030059810302c00c003041071400181d002682c03070b001d01280384005050640b503c64101c40d030489a0342c26803134104040181d24481d10340d4141d403600c1c000d0401404040d81094104140e100ca01c010508c00900d04121001c102558140111100c54105543d8030505941f1030504a03000555008200c400c075408020300c60114804020040300300e03200000300c403126460103001901d81407505980c01d800c0000d00c64104941400761413030807601d4803150807000d0150503d14040940065940194082642d0481481554a115130280c10461580e4580e440d650180da41c04590320384805900070340c098800c0002504506680d00050f40d2544100400300721210306440c01400d48407941c100005d154008800c0258955000038070072140c10003820042c2c0c01c2420703c03021945a100003030003d0005600c1c0c2401d282001000c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 320205134 1250 320203884 320203889
    0x40204240207180903020c1e0103060f3516050a0e040f0b130c030501050916030c0b07020d02060a030b011209020a091104030b090a2306060f030f07030803011d130f020a 74
    0x42406205244231180b0280e20381035030f840c403400039280003c0030496055280d02001514100b0681443c1e8403081e240b80700c5001c0e4210359427212f01100c440289400b0004000d0a05200c0b800031040c80f0f140c2c18501401900149a400f10b006040341c0745c18000070640707081c3d0000c00c41c3c2d0403030002d02c4c9039601c0100c1c181111840c40402001d03142020400018002d0650015005d00701607000e0311900c0d180c00c1c240f00742c59034075801f010b01041c42d682070400c20582e016000304205413019061303207084655500040e01a0b001070300da4402294807500300b4566980c5c450183c00001507100010060030340d154010450707010319070050f54400783c4d80340c18500c0000c1003102034070000d5610078200701d484c0c544603070829150940c0c200c0172243c80004640d43c440c45420341c14258821080c01c0b0080c8400c1e52120100700e4842c0400c03903020b416000301c11000e100c4d01000c1c40003c02941c0906580c0b40d503135161050054451400c010000d46030710301c0c001030000302c02982a0421080d60840d581045810560001441d054400d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 320206384 1250 320205134 320205139
    0x1302240c100518031b0a0f0501020909071107030f020d171809071d0d05060a0b12010c05030408070501020c0304030f1412040b0a0905040204240207180903020c 70
    0xc10403140028001503401c00d40004108280040d4607620f01c2c48052a20007000e002c100e410500c5a03104039802022a28140c04090303080782c5400405480d14085030241110544da542d4002803014901d040000504e03402000c180340107031803412030404c56034442d171850200501e50b0411307402a07025943c0e071044a00086421a018201c40c032101944241c103507000b201041c135072280c80c0030001c0948c44c000a036640319000036290108480751350400b41c0500011504495401100e03c000c5001003001000700b503115060520300003805481e100d003000307914180500b03405020fa06110b091101954400c050341d8100d0b91001c241521150545860f60190144081c0d5100c1440b01040c0042404a0502d40c0b2400794003c40488003011000000c0c40d44408030a4800300301110100070410003c031801004142c060004d103850b481440e103d00020703040e6400f65101c0500740c64202c40401e002c0107107010500031500030b4001444150f20f0a9004115207500c00706410b0702d555610841400d25009020710419131500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 320207634 1250 320206384 320206387
    0x100e030f070b03060a0605040b0a0e0d0b090d110a120f020a0503030702010b01080a051e0a09061533030f090b071706060a020a0209100509010806011409130224 70
    0x2200b0a8a805400848690340315012031000002d85034000c0c0b08603402e0384c044503002450100125801c0d2607030800441c0d1550413200b194180d0001c1a001c40308640140014805424442680d12000740b004441c03940e0402c0340d8110780f0015002410341c28010180d0050f5043c031110f0020100000da080c01060b02d0003030118000041000203540d4107502401c0342203806d80f41c51000382c4480101404950701200c0c0300800d060300c102d40740000c820750350400d9848402213102050131070303a41e640c4c0c1c402c1d103100400c040031000346032206100074501c10720301c00304404c0d183e032814402000c0c0440100d1141142103c034424155030b500828800865500700c0c0c510a50000180c5800b42440d010003403411100400012441c2c6019000c52a286020400c41d4001300c2c45078010b01042c4296000c002c20301202406481c217440781e40c440054147c0b51009101c7c02000c131000500520362500402000443d100103880303104442140400502821561403c04c510b0b030140c0e041010410488160007150800401c01e4101440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 320208884 1250 320207634 320207639
    0x5100803040f0609120b0a09080d0e06090f03090a0e07181806080706020a031d030607120b030703031b051e010b0102010e01020703390303060305061302100e030f07 72
    0x3020840c1107651a580b1110742e01d645046030910201e10728401043c00d400c5001040440d1f03940c2e00700440603401503011510b040b05051010046810b00c02403401260086010481840c10a1200841e900081790285280800071800070b40281031501440741001c1c25034000c030b2a002c1c81900c0803070182c0500c10b1005c19003522402c401001020054490039920700b0403034041143c07200440c0980c211480d54005045419070790b54140d030312524168000d0100804800d84c2030083c0e0301042010b0050f115071701c41d001758810f5000408182c0715440c8009009501445003000080c4d0700582c80500044800c12410301300506d85015400d06800c030004030500100c01542c002d4090f410351144d641600c00360001c0180b900907090b07107802d034058440050003042403c2c1d42c00c0102030703104400340c013204000b9000038510040890804204040c5d0302c01a00005d42c1d40d9018010010100301043c0c0201658290034002101742c0d00080d0b29240000c0d1900400040d84c3e051415520304001d0b4074201c1a00c501580c5121382c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 320210134 1250 320208884 320208899
    0x6030c0904050f19150506070201020a021309170301030302030403140c0907200c090403050a02070e0a23060d030f0e0913030906050f0a1b0b160915120510080304 71
    0x2002c2d1803510f9000304c074a040100800b910704c0703498605585c4041c00704206140c1810001c0340d8001c00340c01d90540c00380f8074107400140e688006050862503000000120a031040c144094400c0c00800c03185204141000140040307900003051b1421264000207514448104015035400e0172412221035411400b1401070140f4103800510308100c0360701c402011104d03018606001c6a6900701118407540100b04080404c01003845a4000d190f21506401240d0016980d080c004a10303800446a1120180c1d81d88d0101120304031421000d00f0104400114643c2c5041c4900050a6092102c0c001418040035003844085907021b083c1951130200c00070701000310b40c82d00f103011005045814000300c0001d49846404200d42e8002e000350750300c10780d4041c070490a00685080984a119404903400c03c00300e0f84200443c0018104004070344916441c00c00c4000824142401070300c1030140790884101c40103214101c00040780e01c05481c610108103000089602d0b100c9030000000c2042a810464050100140104e042c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 320211384 1250 320210134 320210161
    0x406080d020a050d032d09050607030504050c0109050918010e03071a0a0507080f19020304060c030e0102091315150906110c060d020c070918031b050c06030c090405 72
    0x82d0095095030840d4041d440e088040f5030141142c90386800c43c0b61903001c3c6240c00d42600180c4504180300000d504819520b239a494404115240d0002a84070001c104c1006030070f0041c0d00c4d00c05001c0c240000043d04080020b00903120040c000a4000002c1070925081c0a00b5000200030340c0f40002506c0d078444060030003800e85c03030002c074901049030080b0300451200e11940c40380700d1042c901c6540304c9900d03484400c0303501401395015184581d00b030f10160011a00d44c00d01e20055005501c14400001c10083d10030300601650308020f040d0311241d1050105c00000d442e2000401041160341038001501e00004007a0036070b4903460b42040c101042540c0e24401100d030014210310a031001743c0c0f51484642e0301c0c02c241d031b070740c070790b400401540c0005e018486c01d1402641500074008814000c0e0607101540d4542c030004088400401c01e032011410398103290070915401000c502c14038820782d180c1081c000428ac0700c440d550360316001d50341e0203204000001444100c8100c1503818100c0020014070560400c0014408039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 320212634 1250 320211384 320211403
    0x130605060d0c09140f060705070e012c071d1507030c02030f01020a0f0c1103100f0f021303080901090f0b040603050f060f121608060f0c0c0c09060406080d02 69
    0x866803030750010440b134811000c981451040204000c0c012102c080c14403000d1740203404115918400e40d940861a81e003c3c101440c00f80280100c48032034115802c640810740c03030440c0b103403083c01205001800106607018021280a082143d5041c4070240804082076003900108403032248404003080f110100742c0d02444142e121402242196101c50744404012b080707220f03200501002c80c1414006545440c003400700012014080c00b190310706c100d840d001080c04c00b180c48181540c015601c2025000c5890740344202e41e0050f090f100c0c01c5041903505d00701e141c1c440e249400003610b6040c011031151003980c8240444070144c2200b0b0b01440802d9034541c00ba80382c64211f8055000860300300000034501c200b50230a0640700c0c4800408040c150340f01002480050b501c11141d200320f90140801b10230703021422840c4d901c001c0610400910507490301044003002d50350042d01c01c03a05400c0401c20032040341d400040740440e010044600100c0c0792922000103004010950003030b2202d02900c0c505040c95a0081001d051 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 320213884 1250 320212634 320212637
    0x8180610090605060c0d081003051c030509070e06150f0f18060307051206040e0d050c01200a030c02010603060e030d060b0f040b03041a0f0103052109130605060d0c 72
    0x100c2e58841d02040110702030000c2403141c3c0e80c40500c01c1c2c134115200e0307100140c100c40c1000032807a00540b6525103a09100d02d11aa106080814004000c3c0c1203a01d840380f01e80c4809501c0103410901e0801c0b1119150600c0a00864441c581c0548400149101c01046682d80c020103901c050703981030340444000307598110102d4032880da451000c01034081c3c105034013180d205039440d9442510f0401c10703e03100038440034050160b9401ca80c3d0760405060082080240b03400760085e5450b00c5440d07055086045095940b242c140c0105210b041c0780700080400d007030b03080d43d5040c2c400e801c0200b80404680d808030f00502d166440544020b050034042100404088004c0241010070700040c4029a2100403d104a101e4072070b0b40c103460181040308010441e0220041c5801a1240c00c50795244804038441c04034000c0240c8900c001104940010010010100b0600b50010101e541004440d00546082c248a0007824a500d000d600f10b4107008510790351640c04500070700002411583c841102c10000401482e00d0000d400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 320215134 1250 320213884 320213891
    0x50f04050f0c0d150e01020a030e0c15031602012d0c030e03040b0a030b060c0c10140304140c0901080f010b0a0308091014030f06011704050d0818061009 67
    0x2000d00001042003400c00b40c014258100d5840c444e514a0300d000340320000d4010040c0e03100c5450818010078001400c5548940e03401040d4802803500003400d01c007030800524030410805218140c0b110b00c40013075aa00500d4400100c03044400444140d014119034030700c018040000207c401002e0380940008800c19501d0942040706203100001503048540100f24940151b02c20b2108000841d8614020107400302c1c3c0b803401044030b1150602249154001800c8002d240d0030022300007000b410498050b05010000d0319000d1601d0054045a905510000d440500030b50304896107494104410014001d201001034425000c0b503a5802286444042000a0140301c0d424001d10080f0787c1b07001012502a00d40059419103004c8401042099100e40f0240440c00c2c411120101000148003801840c421a03641903601c0c070900c2e000d00010100c50030414503110001e0100d0900001c62000a20128040300b982004075080e120000c104c1441350209651208501c105000c0116a001921412088a05d51070052 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 320216384 1250 320215134 320215153
    0x91f0f080703090308041205040e040c08011b0915050909310201021b1212030405071215090203010e0109050f101b0806060d09060917030c070602030402060409050f0405 74
    0x8070b0580d024800081e0000380e0302c5000c100822206400c86004080d1810170300c0ca40f9581e030505500c0b00300e0454094420040b6400b00b0003120345c081c019010882144c00740d44041b4000004041d125450340d00511072a220035078414804107010714100c8544410040005040d1f00d00891001504120303181c8903107902710000b4000c550764825120011a1643c140c0151164250b94545070200d984800d102d03580c0305001d503400000002051083c04003500500d4007403907030303803405082881c90080107511410100c01194240004140100d400a02d8078030a01c0010468402500000e4050010694510301079481d00c011003041210010f620840d40b6424410b454041c980c1ea0040022034a400d42c421560001581000d00400d102d1003010350702c0080104106c0c1811b600c0141d26048440f903150860728181d80b43c030348c2d070244503100908010590f2000700e910b15603e0016581d0806000c0c1c103000501d61030b00880441c00310358954054401411a0401c100002c2c680044d400e4403202c4281d501765458090503030203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 320217634 1250 320216384 320216387
    0x130c1b06050414010b01200c090f041202030703200709020d1505040506090610090b0307090e060d030509010309080c010905030304120e030615030102130b09040f020903070b091f0f0807 81
    0x101761740a24161202c80007081c40041c804001c001050344003000c0c0c010005560459a01c5002c10b9015210308400300065107011b00d03104201c002046c0205055500c140810780000f640140c603410a0b2503040219039078215000e540900c1e00f406038122680003070010440b1035948a45502c03034418079800d0800210419650001d00044038001e5a41c0e503081041d0304006401401d0228216620020500c3d000070111382d02c1d0580c0c92160429100d8400040d41003104004080320700000c0307900003c2c22602c0d250280e103aa40c0240861080e00b4036641410345486061080c081088150351030450040000d01141c646e9280c1203403a03038811141203c030078a440c1c540d907150921881e5400000d0f00090001d004e543c03500d03e480036038040c00e10912581503408008006510711404002c40c014100420f109842d0801c40e010001640e0582000c49500c0b8030510802c840b640d00054000c08840b5000c050640d00c10854000c0f48801c0d070741021040c207450a68038035a00303196106030484959031003640c4610480d21030280 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 320218884 1250 320217634 320217641
    0x2309010c030b090c070f02130e0606010905010509031507111902240406120f0e061005040915051003170909010911030403111903050705060c09130c1b0605041401 71
    0x284416131507404e000050000d0700c0115510265400189551002003101d220202507401020080115800c5181031010381d581080c400e8001e40f400f4204541010a0400460303a01c810341c4e0f06c000f10b6880038801090f1100e01400d030788102e20500c642a074201c1200980c2c400003084104504074080c4181c0c014200d0003480c3c9225100d860400262403034907161601408983d406503500846001303540d0341d5900c4100c00f4151040b5880100181e0182c00c0600c0d000c1d6040c030721400f4a0703102034010b9042072821000601c11044000c41c51188541c00912a01ca0345e44200d00d05a05410040c64240d0840d00c0c5d100d1084008060714101e42c003203c28284036a02e078036030b2400f42c400010031655100c0342840880c000074014000c200c5203410180894904c48403032001d81c0f0a0100c80d08013903020807800035030702042c450148080c42d44580b030400301c0382c0b034200b9035804180300407074516104000301e41c2d070740340c2c4451140b18008401c40001d003c0d52100351110b02c0c5c1403c00080406850854880e81c4983c3c007a1070002c810301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 320220134 1250 320218884 320218891
    0x6191205060c040609120203150103140106060509060901031503060501030311010c050f040504050601270302010806030708191a0f091605093c0712110d2309010c030b09 74
    0x698104021b0b241c0f03021404030010815040ba85802400340c001c1c03801c01190103440c001cbd4000c07620200c41c80d107012091402c6501ca03030401010804c0030004034040e511230310100ca410000c01e01c2c0004e80414141c0d0640001d6881da080101020705181c00001407690208445604c4845000204800303420310606a80a108043c1003491041d0b083c0410002c40c505039000503848034060401508030804100094aa503c8881011854000c89242032041d5680803402c1e5034001c00580040c00c480b07040200d07055030f44030b80b0181040b0649204960b002000001540a000031022911105440c10411418072060034103c850350302038404d11554041121140f101401100c030003508003c05ca88910000c1003800e1721010100d00130f5100526090041d13044200c03040c522248140c0c00300041c2c00e1040d0000e2090408c0c80e4100b901c141030040042911100d00c08039410400c1c0c031180080c000149078000e0f19132524511580103640d07004c9081000c50307041034005240c800c6050340c08000d03c10320001045201203054 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 320221384 1250 320220134 320220137
    0xf02030a080411010507052b03050906060d0311010507021c0c0b0a0e0703052505060a020304050d0c03021801061103040f1701060503060a0204090b040e1506191205060c0406 76
    0xe01c04680800c2040c110101c5111041c549145000c4003921a649030038608000f2050540c25030070203c3c000400c0303200780064080189024040c60400444913962800003620452140d200d5481c0c1004050048600c001800c1c0260000d000c5460910030281d120714038a2081c03079a145640c804440103d100d001c1d11003402e030344806900e1460b2030b001502002808041d8101000d8454101e010000ca401000251002c54000220609003140748072106c00842d4a0742c40345002340d40a02500c03d4241d008801c1e41c0944105031074400c04ca4605052208100481d070748040c0d00b082108100e4407803860700a0020341614002e841e48800f0b078001c402500d07501d100c0ca2081c80e90b55010703101e00384002511000a07100c0c3c4110b8400105840b038481d0002410200207490b1402d107640d00241c10042e17820a809a10503003a42140c040000c0200800526103842c9440401003114005100042143e5501c2d00110000450001d14060a07a01d5021a8000d84040c18064400340b03c0d50000076a110320b020100c50a88046 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 320222634 1250 320221384 320221397
    0x10e09040f120207050312040503160305120708070804150e1c02060906190207031208010b0f0c0a080a0c26071b09090c150216051207050402030c0a0f02030a 69
    0x641c2c0b80c0c0c0907802040c00485003180241d03000000d06680400903516010034400c981c980d9213150504062602950101d480c1c1c4a10404200b08040781d03000c00c0e0451009060280c0c0c0c2d54840880c98400c900b4494160700805e01840814081910070600c1c0c40c0d240002c80a8403402a05410b4008110a50005826001c0c0c0410000444001410900f0103008620405421141801c0d0b20039405280f03aa2140301c03100043c1e0024008000b84001000c00b0b07254a05241421911075040100342402480b0388030740236584650008903d02c0c03030702c81080800b1000743c000b240c40f900c0320f200c0840100032440b0f250050b00ca131404d0307243c0070131006042d07030303a1443c01071081040515240140c0d95a82d003642c491111034603c641c000000161503000e90003102c00c4130b4071545040c445103051404c8040034181e858183c1c0210340c40422410000c04010f032a2005482d401c4a0035501c01824030206441c000040d080302c0c0d0046e0020041c0a81c0c0c410400281190304120348550540310071541c012a40c902402c01c41c800007c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 320223884 1250 320222634 320222663
    0x3150603060621010501091401091b0302220f0603291c0609110108150a050f2d150a1b210f03110f25140303010302010e0904 55
    0x81c842400301400000c070f030070180320001480d600c40c00c5940c2644210a00343d02c0712880c158035144002304502500300c0000410182c4110850f11184858014141050590002d240d5254100702c51294480f03c80200407002c24075100e186c0074580310250b00c9207402007410a244100e14101d005070780f04030054180203500d000b20b00d0b0030800003102c40e004004042c0261003115075010540f2406005e80e01c50240350f220511000c0d9600041c1880802054001da02e200745402e24070f250f840c0301880c811198200c648111841c40c00002420000c1c0c030510880c0420100c54200c0031480e82252113001e0706008a0b0329602880d890754031440203201c0c00383c1c2030000402c2075020b8581241c5400603000c1d00350194054940c403000802440d1300408484d2034110105500302d160501c0584e05000e0072010008070000e00f030800e10b0f000903031085801040301700201040000050aa0030310210424200d06806c4110f04008425841881c0d0b1241d20a001c164001080d0b40d401246c00d0825003001401598410700c600c100e4035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 320225134 1250 320223884 320223889
    0xa08010209090c03070e060a0f020d030b031506010519080621100e030d06080303060901060912150b032505030a0b1302030a05010509070602010e0d050304030f140a08010302031506030606 82
    0x2130004080350103101006e96005c001d03072aa580038004812321a04c41000020010342c020340b030400901906410141014410700203602c000c0307054070303680d070107113810b0311650b260040141c5840c090802c0001e181c50b0080f00c0315841e01d510011041c020364041e80c0742c43c0c10b08041940c00d5810031000071500902c1d0301280341020783c00990b51007010404001010b40c0d0a09412846a50983c0c002e503100c3d01c00c2e580044140801841c1080d0103600406a6081c03c81202d460400c080300d403103408190141c2100301ca03054141d5111980e030009205ca070002400c0e110100341e08030802a00003101c2112040d01c49055002055508001803000111908030400441d03541c8d03040c105020b070010600c8200c0c1c06008018a40c00003400c02d00a40b130003941a800070b44503079810544000e00311200d0007540415507200346507032240560002c0440360440c0d018501380b680d104032080151880300d004510381140c1280054507180e181d5000b51110306a074821801c1e601d40c0b5115564800c4849402d0f02d4080e816004030001c00e4261 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 320226384 1250 320225134 320225137
    0x3270326040605070f050d051c1a04230c04180c020c120c0a03060203011806140103020306010c08070605040311060402181003080f03010e160c030c0201050417010b0a08010209090c 79
    0x11740328204180840e00142c0e119030030b1050401240d4040341001c0340d001605da0082d0030161003101c0410b01040106000840000540090360469000c0d40d03413440c603101800c2c920070f00c020442d007408007810428184100d80030361551003440b510501c1c0c4000081c004c000410380c064540c00e5443c5600601e1400f204404002401c060a0380d106481c0c400c140c20780400b5264070309801d0081d4010700c030050700e940c506410010320036104140f0390b08540c81c1c030f941403096180140045041203401c0c40c005840390345050042c0d1b603045002401500c08080417a10f2400c104054004a224038402e55514240c072034441d07005950303060240ea00a40c8107440d8150040325030129500c80303074480803030130203c50455526110707091f10f035204080070b81c03c85800000610854840001c0660000410140c145400010180041400501000080170002c400e00b4143c29603110b1800c2d40c001d051051000902094142d800c42d00802c9100b050070301132807158500140001040c030035505c0c10040a0030385805962400001401c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 320227634 1250 320226384 320226397
    0x1205070302210408010f0506010e0102150a0203100e010b1c051e04050304050604080a05120906030112170a0f0207050603090a0b09011d0604110604050f0103020703270326040605 78
    0x141c0b07000e1100040d18102406010020048000c00084a050050004109072403100d9070505550040c00404844503a035007910f0b0342b206102c3c000684a40300c03040f030076240d000c1c0e07548051900b0032080b001140040404006042c150b188184041070489809404e10070b80384c0454201980c4012605419808030888641591080c89441541c0c0b401d605d820006069411a8001d02007503440850350328100582000754840600640c51384609100350500002e14600c0f050045080001d2501c011030f0411030010414000d912800760800c1c0c60740c0001d81d004011004415403107005101d00a800125800e1003403c5074064001d0f04003900e80c080c0c45443d2410040000303000d400180d90f0312500d90b4005195811000f20f5688680d010740340758202401c103500401c07000400d6904c960f200704402c01056a1302c030840980d4100038200945c0712511401d09403002000380c40240c2d40703184010040c042c6005003200c3c140030303248100c03048030040703581c82d115105072800d03000242c0e20640b08120512441e030040014105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 320228884 1250 320227634 320227693
    0x13020903010912050c010e0105060306040807030c12030f0c08010810090f020a060801030302072c0405030702040509072303032b140f01060c050607050d060305010212041205070302 79
    0x1d00b03040d02e80d16100320400103100301000030b8010502c06070343c02c000e01401c005007513030300021312490900c03c0020707848880c01f41c80200400e82c001604010180110035403156603411213002054034250307200203005450610b902d42c0d0503500d0b011b00100418020b020703070ba05885001d0000e0a000d103101020400030702c0b0301e0348103030360742141d00549034010b0303880e02e54400280c4455607518000707505d5403070301a25000458110496982071a0304500c1500300341804800d868400011103912901c0d0350500c02d0440c401c0110194200341454100300400c0702c00502242102c155801000301109500141c42e140080c0000c0c1da41e06810800401300c80740303040d058020610100e9603642c54440f40c00c03e01c1c00b0031070f031668401e4101200184108822990001409401480c841c140b400c0024090341c0c506031103c03001002a0180700380031071002c6844039141e0203003002d158010002c564a230000458240d0321001114122134036681044500c1c0c056114100351440583c2c181c000300310b100080790000044c084540c0c001d86 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 320230134 1250 320228884 320228891
    0x30c1b1806060f070f060e0f060c120403091809020f01051303020405090304081023010803070b090304090c0306090b150409020a05070b01090c0f0206010f0501030b12010519060e061302090301 84
    0x1011a005116184680340b04a000084031187c030b414450514521000603403d50b0005020440c140400908485070031031010140c0d04207030f440b8501540c4224103a00151154699111102c0100015a01159406000715034804400d01d40400440e8a445010085800348164000800041c142a0401a00a038404080c1c900305600c5030b10140c5440e0040d0b460000700d540300c4003030604011002070305031040d4042d200249810340c1884611a5280714464005101119400000380b40c0e400c01d00949010b02408081440191001c24004000e421140140c7c640e072031038841c0c07035983c600d040d0540d03002d83e00403c2150f60a01d40381890b000c009410640c0c0150500a00f0011100000d40c0c410200d806083d55030760004888a42c0c8800600c180310800d090001e6501c082c0c0107000a0a2028403d0100d4209103800300350303840500d010942d02c1a120445800960138a024401040598003d201059601d50f40070003102d541c80382c84030f0700110b085c3c403030baa005281144001c4078056544c00401c80c048002e030011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 320231384 1250 320230134 320230147
    0xf030d02070c080d080a060503060f070804061d07060801120210080c07021309060b010206090613050c0a06020c100c02010e0907170c0c0d03020702100e01020f030c1b1806060f 77
    0x11410031044508004c0021002c078104000013080d4447d45000c0c080c140c0050056151082d0400758070807018040c0424813a2040014040080503081810705040e00800810301c1c0482a008981c0c0f25024000e0740c0105003440d0002c01d02c807900d0720201c4d842075002450f420055901c14801d941e10940500b00350f200070300410405004d601d5095148220409003080000c0c4c203400e6050000407216504100342c1150058000e201d070f03609000900c0340d00800d4128a20b60b1007919440c00925080c0b46004050300596500d40c00102e10303402081d03110041c90165a69100c10080c45011038000048403c0240825070003580a000e505000038240e50042c030a0801005c1c40c003800107070401c5001d00b1a01d00414074800500d20b00600c0d01070010641c01101420154203180c816030024030182010480b080400013500600c002c04da100300020700340122000152030b5103071010700c80355417258840c00004e2070300961041e2a580d14104103249581c0c1c00b070b0b401e1030031003036454910130480d42c1d40c4200346548581d981446036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 320232634 1250 320231384 320231399
    0xd0606142b2a0b0d0c0305070c080901030207150203011a030405060c16021c0302010f060e0402040f140406091a09030d0c03020c07080705040615020307080307120608030d0e0f030d02070c 82
    0x210050942c9080254452400003501380c291200c2920b118105070602c0d061244442c1c0008500080640c0031111540755000f03440100d00038010050050098100d2015149821580d07500540c16100044606095240001c001c0c1601e4070056070020101c0d4044c00000d03a00c2520791019241014980101b8400304c2c0c900c1e0001400700550600150f030b1000203104400415409204101846008000501c40700d490702c3c042485d91800140040d003e00e880b580407180031040b07a0712640b102c41d201d00e151341703c9003446c4c1441e40c0140000034040b41d44400f002c1c01c0818281c00d5213804d07803003400d254008515200c0070390f5000001d0603030244101c0a15070240721298400788203000ac080a0010b16005000e141d1500d030410058801540c4009030b0409041800c640703070b540c0842201d051070f03089407000d40d40f0b031103808040360984541c030b40400c2514640200031901d448080020540c801d24800b06000645040129035201c0c04202025196903000300000b252082540d0058605580209080102c0c19985ca11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 320233884 1250 320232634 320232713
    0xb0907020102030f06010905030d11010f0501080f0c04111602010918022a030301120c0810021b0d0801181e020403021311180d0606142b 60
    0x220240540d4000c003c00114480e0703519000da006000b444e124600520304008240c480756101c40c40b10030000084001100c10350300350840060010350020400c00796a580210684901e8000c51101c0180500125a200c6207058050140a00350422000c0e1030241700b244a64503403060706100700c0c1031040880002840b88605a80b000c03507204508400b42e9180c5100f00348111080c11304491031110000319a1195903410000144c0381541c4103800c8080c0c0b0b14046081901c19020305e50310070307456841400031101c9041d25030b40140c003d022502d200c1d440d41101048a04d17484012146402d000549188010003410604859183c81e02405e13800020315203102000050f0f03165007004a0340742c0070f600001d0410031070402c1c0c01c00b80865440c1510400403504400c841c075007188101140748047c104024a0104a0303500d8510291440b54004010040a540c40d83d4000d51641c944010611400c1490b0541081959141d1000040c000703141131300281441a030b0b51911000341910074081005019800c044000d4000074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 320235134 1250 320233884 320233891
    0xa050901090501050a0213080708061503030d060b04030606050f10030f02090603100f05010518010c1e0302100b0411040b072a0e1506030610020c0a0303030b03060c03090d0806040b09 80
    0x5a914007c82c01c520440c81d009901411f050340c00101d0410041c03034082501c54116000e01d803220f113a4003030200041e1450203100c0040c5c4209103048000142c8228000003001200d20900060200561f41d0017008201484c51481079004003940e8a1040001e201ea030004c00c010f134030a4001410403840c40c01155480d0812203c01c280076000301c40601100c055071210170028031003403030400d240c02d8403000d104908000380c0c0c881d6414010b100c1504400c00c511544491161500030384c0e194051001810000c2d82c0d03040e11000d803a80c01e4070b08036801403c0d04050040360710b0b0f8200b09014902e401d1802e005200e4550210105076801c104a04051500780350840c0c0d000480d608010180701d4071070034005007000800c0080c00078000d805800010548903110f030415240e1002045441c015144101c81c03003a0304145035512002d0b401165507001200301501030f0300404e0114015000c07200c1650f14070107007810510090304e40d40d03820b50001c007080038020310402441e60712040282020440000c0032010543d001c41c1507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 320236384 1250 320235134 320235151
    0x50703060f030803190b01020706080603120703080624220801050106110105070f09151205180111040605071716080703020f0d05040612140c0712030908030a05090109050105 76
    0x14410f9210449181c00000f1900d2a8201b10380d0280c000081d40d07410540c4074070014000d410300016480ea509021950041801d035100d0355652019240041c400c11084036410b104100307076001c00c0001c05640b0b107040f08610195100c5440c207a40840c01d28110b004011500b040c5d42c88180d804114124207000b000d00801440c0c46080c0102c0000c0d400b1400d603100106401d0400121403040e600703869000801c0310403169884a40c2205c034151000441300b1074502c0e244100038500303090038081e0400d4413141c041d48040d034900003002003c14180c00319109102da4890140052001c4c4071250100314100c80748110f00702d09160241c900602c0384100d0701c011840c00300948a035000892150b013895014449a156030030810090075030614110b0303014100c1d02590248004000b58807000911885481d40a14070344621884403901c00d1406044121741540150300c100c40e007440103001800c115020303010303400042d640040140e003141d1b10069031400418000700310b489159221541e46c80030440a03c200c50169144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 320237634 1250 320236384 320236387
    0x141902150d060f091e020c07140111150907050105030f0c0c16030b0a0608031207051303020d050c0102070e0108030d181b03050f03070b0c030603010b060a230c10050703060f0308 78
    0x81d00a000c40c00c0200d4040c0e0b00c14240100b2044007c2c403000b007040d100f503c00c80105044e040c1c44150040316508800308880045104070140c08810b0000704400c10300c1076010f82d040300c140341c4d256001111540015942e402680c00c0081c042110388104601031301c0c1040d00e09049424007050003007041586101548143c541801d45028400300903114028400606120310086203020340c4042d982e1009503008001504100e80468290340c00c01222010800442d0000c0004405118504002c1c0c0c503010300d02d03100340c0540304003c400a12050000140c031b041300c880402950070510010044d10140460540c94041c12110b107488400041090007016461020f840d00030320254150f1401514050142d806c100d050307402484848001040040c40603803112034408115181e8807410013184c0500f0030441441c0d44940c02243d1403102c998080c040058800190b04111424080100039250a01c42c008900e03140c0c2c1c00540000181c0d0186402064110815141c005102e075a01d1001d0b440880090b0030807038a4000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 320238884 1250 320237634 320237651
    0xa05030f040501020d0f0e01140d0204090605040f091e06090b010b130b0310170a21090906030b06040504260a020c060301120b100b07141902150d060f09 67
    0x3410080000300340705c2801d201860164480015001c0b6031095075603810803c8114503212141031000580d810202c1c206001d43d151a00c0708807000240c031890140a01551a01240321b030040150300580350002d0300800c000440ca101e9510401024100c4202940c11030b46601107000090b00026003a8020100110460780310700e00043c0e6190740345481d03072025242c00020f0040c4401000107103561011a280310340c88580c2510414491b42c00c0112501000c0c2c5440501000840c18040005100340c0c5400a56a00c02045440305101c004440f06400b024210f440c1030400110a13040903408150868043c20698541e41d040c002201d00300d01d0046d0040d00d1282001c6002844550100021901c20004031040d0341150f0400d50800440900d0540c043c01c1491044d022a084184182c2d8a40140421130340c050b076038000710706108610050410044280340310f041d6521462a680d0035170b000ca259402804850200c0c01680596a81d400c4400c103030b031500e6610900060300007400c0340e0940041820b1480821a40c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 320240134 1250 320238884 320238887
    0xc1309050f060a060806040b01120513030909090503040909031b03020705030706080c09040b060c03041d0924060a08060103050a03080108030f0d051506070b01080d26090a05030f040501 81
    0x10380280c42503020f10000001800025040b101d030039480142564006481c03102040100c42c0c00c40641c2c1c20049013481d00007441001074100c03c01048250003510750005ca560707221810003c550003060301800e140c005000a001a00c0340b41c101295880c0203242080900c0405401403c03000d800304012405079001e02d108021324141409100010516810b0900b410710303114034a41218400d20540c0d51055a03540d00c0035209544d00d4054034184810902141c0e1500e445500102c50030b0b804d0711420850229410024802d490700040c103055003041800901c4a607428916202d0500401418050b40b080e907680b008110010b080000c00e000310301400042c42481000c0c2030140c103da5042e00601c040d03804c1008504043c4c82a00101c82c002c10f501603000542d80c1d5000035915105c04030304146503214400007440700500103001d1003581a43c0a502c1650400b41d2481c9007503501c80565103c4103840794001c4100c1c550024245285a48601580c2c00e03a0844900340d0b40d06401c5034003c0c2c3c07090000c094003080038001035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 320241384 1250 320240134 320240161
    0x3110f0303130e0c0c06040f0219060f170105010215040c080f01020310050d05120a030f020c0d0210180206030c0f120106140406090b180a06120f06031a0c130905 71
    0x400804e95440c01d0140d510644c0c070b484008001414080180b40c5180c119121581c00703241403030301d50070415405a240e0f04018446011402e4480004004403801c03094202580861412200140c0062405507403000602c649000010802d60303880389907510002c1c0080062203482d81c80405080010717903d25121008007640f1103990400d41c05070705031102400000f00c0000c1d070054400c2244520686407140414210042d0840f142041c04890000c0b8608081c042c001800318106030711a000c0c0e03080c1a00b41001d9800316040410582d021075603900380d207800350802900850b0820f18107590075203012514070103895654001418211402c030b1000041004a501c4503d480700c065000e441545401d180c180004d050761440e0003a210b000000280101040d280080c00600382c000c050b0075528069502d00000e00a6940c0301146051141000703845c0c18050040e10400f0305580c9d0110903600140080a00d01d51908002440c40806c5002000181d008010808006000f4001000041110b162505030100c03103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 320242634 1250 320241384 320241391
    0x20406020c04180b06091f1205060a050c0a0309030905191d06010518031519060608010b16080403140a12050c0c1002070f030614100b0403110f0303130e 67
    0x3c1d0b00d04092001c000405101440307070892070480e10b4078082d844107a0100000b1601c900e8404002c442c5800004411001c940745005080c001c90995505640c0c0021140a54100301c0e00c0c2b140e045020420305010314060b5100c40800c5000741b0344000305a032940c022841182e6011000c2c96011b8050700d04010880c2644001e40028100410814940c10300c000040c2841c000c00344c0d481c10b494110071840d4a00d46041000d0410360020709001c00050a0036202e00c8003450203a51031038030300c41c20804045141130103042501d0480d81d12903801850001c0101c211042030303c1a20089a11010401c00000400d1400102851120419000d4030b001400c034a03000b001284541600014400144142da9034000c0c041040041441e0035112060700c400071400032410310f051a004035000c1c5141070000f20a0110b40c1c1e000741007030703d80c8500450198860388200c6680161720710070740f111f040b810001400090095004d004007580c01910494a00ca68000001c0c215001841c4a14544200550030015202541d0fa40f030741 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 320243884 1250 320242634 320242661
    0xa060e19171b0606030f3d020304060e0706020a020901030b07140d06060e04090b0a05040204061d090d0504050d1407030204020706150f14120a0519030801051927020406020c04 77
    0x903440105400d550340601c9103000c800036041010b030211f0b105100307900c403070150030750120215540e00e090701d0080300070f14101d484206075124200e004550180005811040c05800900c080200da103180ea51071008a00149428104200c4078003000d0461100c001929015840a402140c0380c1e04000c1c000700101c028468851042d828152500080740e0302c0410650020423014021803195150b001240107450f00364031003d5042e001403c45402800c1c1601d03c2400351307500c0030569040c40410b0342c00b1222406036000f034551080c11500d4240004107500b0080d000d90b0403090644590507569000034003207070850241510ba254640340c0b600c059001300c2107001c01130405200d01045035030a109000b0708031100400014058201081d024010034000c114505203254072208440a8030142d0711900c5010350307060401c5000c00c003258008111840d01810702030030049903100f030111080c41e04c41c442542c500382d0200314201c20003508149034036640da0700080010700320075001041d1240000050004036820f6090340030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 320245134 1250 320243884 320243893
    0x7080d05040b030a0e1f09110904110910030506040f0b1305101a041a01020607110c150c100213050a0f09150909050a060e19171b0606030f 61
    0x4420514094a13008601e8050000b8444d041c005800d181004100c4d060211b8040450f60342c1c0c041c001604140c0701a07101e242401c510702c07000d40a10000c80c00580b0000e0170b400c65503005046608014074038940c030600d28450012a580d580d2030b81d900300305040e00d050b18010000c5c20b100041c01910746803550070400305003101e03903e00d0143c1c48150321003d521201060560300c6209230003a80a00020000c00800005c2040200000b01081240700e41c040e40c50603030141c0108400164920b02a10300d2500c4980103101400000c4070840030042c1403a2f001800071800c4405101c1122136070001c0122048905501d940142e49202890303150342584180c0d07001234401d0021250034041e0004000391282114100d81e00841c000e185e0b184a1100d81c5401e8020f0103c17545444807240c14004000307868041c0c1070244604001900400f4055600c0e06000f1061700480301c03100600300d000407804040b40036079900c6c80203030a0070441034a003505040b44100c40014050380c001401e1080703d00e400c0c81118402e5100c0d00c0240f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 320246384 1250 320245134 320245139
    0x7020d03180b0c0d0225121d10090b1c0e030a0c1b0518060a060806060a120f020c06090d050310090b0609090405060a15050d14010f0c0207080d0504 65
    0xc444802c801803d103402c912010580e0038005103075030141c03400c03200316441c2c840c9030340b8000000d02c00c000c200c01c90985d1108100041d080d2154042c030000300e42200400b002c0d20010340048207201110402040c8942085a42d10b0300240c403801034070207030015208801036400003800c682803440c01d80f01c019510300c800d03400802582c460b5a42001120300140e41c018040080d8611104604011800989c030042e0000b0610784041e48164980c01c1091144808464541d5629200c01c0f040b951181d04840d0942c001e1010014150b00c03134000c0000b0021a6040c01000c13a04012100b0310f4001d0384c0000d004031300d4a6103d0303c1844040346050180d400c03100507900c0d016043d8500740c1400d449603801442212841aa2400120443e460f031008484030594080c00449241c2001e1401785c1c0e955a046540c0305026107003401103801455103000c41001ca601c01465484498400e8642c101521924500e41d0041e640c1ca08803409040c40d5070282090030103694019051262500385007a0812504118420070020108400d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 320247634 1250 320246384 320246393
    0x80a181e0905091b030f07030503030f0a0b150d0924051e0105010809030f03070503061215010b09180702010212070903030801120303020c01061e06030911060304170307020d0318 78
    0x80d15a0b14a4000013110003081002c08681080694015007980f03010310400070041c444000b0003540514400146541c096561038026030860f503031800171540c0500341c03803550403194000c080513117100d4515030700005003a00f166070384000302c0b55010040000010040d0034400b5510641c454982e2011050045401004150a1240310140140980740c107001e8890041a040c01d03003003054030300107400354950303903500d040601020300325400803100648600040e0304841400c45001c00d85588074005002c001d0b2030b83e401d005100a0503000981201e4021990000d101c410b201081c12503130103a440c50700016903c84010800e18031020006110b54140a42c0010800001707031b00001080c11180c415011551086151404401a21540c18030241c190309203030300818601d060900e611840251590340414840c1d403550140d0685000d01e20103000c280200d038050034107007401ca0045601c103100d0590721840450450100c56603070010345080740180c7c0f0160001c01c0440d00742c801c50600949840c106c0f100301460765078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 320248884 1250 320247634 320247643
    0x5151005031015110f100e0312040b0c090d120f0c0510021602090f010f05040c1209031e0527100c02030c0a0305060406050c0a0c080a181e090509 64
    0x14290b903070003041ca42e000e10134410340000f00c41000510a80b005000301e03802140c0d88070070807444800140d190042c00e00b91074000004640000c2c507910b620042c81d945984650321040300040c5001d415040c1000b03495813541e940512140520320034071480c01030340485000188175204e40d407850340074071081c2020b44c40450030005020342d50b100c00803000340ea1036030308504044410b109110025081082e4405210780c0680c1c408050313041e200e4090100303400554500800c4180d80010400300049440d44400113028000398001400c2da0340a403c4c803074001c0c91a41408501032119003c90b0340054000f145240542400352015060390152207801800d100a0030001500306503610806820b1080e040035860442d1014850500a444001c3c04803414503074a042040d10b85804403030446c2c405241c0030004951042d044291044802d540d40c80d1801c02030b6650311144694446400b45007807001c91518020780c100d001d0100b602500180f0f0b081c0310000c2101010301c80b40700311504075089490500b020813000344070014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 320250134 1250 320248884 320248889
    0x601150c0809010e040f05180102030c30090318150d0c0905041802030c09011512060807090f0b030d050306010e0406050a090c17010b0406030915051510050310 70
    0x4030840d0b407401004016561400d42c01070aa400a0400480312409190f640c0054030030035103900360300030081d03d112140d4200c0c4011101c03044044000e0190300c410310803070404419008034000035416440c000580d49020b2140c03c07140c59100360320000d6222070040c0600c80e103800c3c2c81030640b4062111042d80060010701e000350082444070540e02d0302007010b1103100305603450007002d02400400118428000341c41501d40814070590103403060010704411030901800da14104c0300c1507002d0f01f01c09181e1007401c40b854440704040520081c0c0311940490b030024148404401005445030024046500c0d04809043ea0512058544217030400c1030303c254a160407004980d4010030901e003040000311510f000500410503900540e0300032001103070100340e800041c1e110514401c440d49440d41309c900b25040342164803009020300c5100140900c4200540b6029402c5108518030880c140c0d03402000e0461041c0c211801240c608880e4ac1d4030109205003420710041d03030314000c1c0d05880c0107403071845c007170310392260034422031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 320251384 1250 320250134 320250143
    0x608070201090606060201051005060f090913120906111501050f0301110d14130c03030f030e06090604031812150e0303010902070b06040207020d030c1b0b04080601150c 74
    0x40005098910030360001c42c00310741c09402000220b44a520090081804407102c001c0345501020100b21403500b00141c0f03031050f006913019481c00440d04140044030f4405052000c0c0760054042c050001030b040081154450010758a5520a503e030a100501138501c071034020000307402c6107404400329610101d07100d0550f4010756600d0005849000803e0050580860200d220b001c0030441c83c00090315a04a03121000320a000b510300c513168903162580c84411044024030b5085000d0701000040d0045035200214205401e000440c015a80205030404408440324040f0303402c20000c000405070001081d100001400c18407150700f43c20841080e440d1580c01002a1042004400048400d07845410520350b1a42020a80c0e031603595481d50b8030041d41150000720348a000042c009401030801e482940c410b00e40060280e10740070324649041c3c034030941e405001d4986040705103a0940c582c45e41d5458400800e61040c80c1555140b5003614a818104d06800506901c800580601e0005074030609001c540c0c6c4c1c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 320252634 1250 320251384 320251397
    0x30706090201140a09150509030a0b07090504020403110102010507020d0c0b090319020d120213031511160507080c01091503021309091a010f09020f0f0304111207060906 74
    0x3180016142c21aa500c1451401c020010700d500c1400c0d84100c00d84d00b02c50002440d45482d5100c144107941c2400381c002e08542607804410b5a8003c290b0a1910705d40140050514801c2c2036212400704081c0e921642040e0782c81d0b942c0710b5a984155a091146940c010f0080c4040c0c440403004000081c0910b0240d20083d0040400e100880c40440e411320845a4180380540c60004180e070144010307407134500e005c1030a4003140214041140d5040b607030084600c2d251262601c1c41103541913640d4420016500c2c0b10b600c800e17660f94000b0184180629000304000840d10000942c401100d140851a21101e90080c90741034101c6880546a0b980180c6100705480e2080030030706002d0514031044009000703041301c190781020004400642501c00d6401100c0c0c403401018040104c07800c000d04a41040760030700c2070704480c603005402004010925030203030141c1888100420316081d01040c40501a8006a0341964428074240e04903146181c070300f18181210b000308028200c1103207000d80103003000b001489000140000b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 320253884 1250 320252634 320252651
    0x50907090f120812270703080a080a0b18060f0a030b0402040b0d0501050705210601020c130b180105040b01020f0c010309030311070f0b010b160204020703181502060f0405030706 78
    0x404415502c4d10100d21014074038510300000d581601300740c0104100d18581038441d2401c00a10085007444c00ea90300000c0d02c40c5003e0728060211a4204000e140444180e6581c4020072a07a0702c8081c500c084440d001c812144074240b0004010000c00c802400700c0c402c1d6958201040001d015060315a4040c0d01103074006420072045004c82e002e242d00721320041c030551900301080b5260b600140038003c4040812101d6001480c004c41c1803901a6003940c003d8056840f0b0103500700c0d6072070266400341240c00d05081c0030800f1084180801e1030440c04030007040070a040c22006204901300782c4100079905400344000e01d4945101071010f030310703100104c00b194101511002d0a0003458000d8112405041d0400d815590b207101c2424203140409a144080b10302c100d00030000120350030b03040c05a5050f90808418460042120340c05c00c0001c1d400f40d2421400d01c0640d903810118013a605c5441c5008002010110390200720442d0000e04041d8000c1011004509080500c80400e20000940d117003542c4c011000506041c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 320255134 1250 320253884 320253893
    0x207030f0611120406020301140d0f0b0a1e0207021003090317041b0e0412020106050a051e0a03081803070f050f0d0803090102071b0e070513090207060204050907090f12 74
    0x860442e680f582c2c076103504140010000300b540190f0488040784100074800e080c590800c601d420072076034040c0c8608802d0b0030304070204402070080c2c1d4020244120004481540b0321182e0000c070840c0100e061030940c0400d0840039410701079084c1c2524036140c681081040c1459038060026418040c0c02901007109600240c10407a0340c0c41c0c940110140700c501e21a106e03642c0e045103000c580e0b088408440640310b1001d1418482c1c0140240019100d0083ca00c41d050381c2000c0500803c14103110311603102440715440e2210300e445240b40300300514000c490703950303a85045010304840804003149141c025801104108108440303805808169078040340d50403103c80032540003c806011030a8003400d04880003081c00300410055006203c1d4900c1045000c011060108040a42040c14491000c00c0341c15640040c0300188158000c00c60200b08220200303a540d06d40c08618201e0300101c40485800d0b60001d07040c00585400414140e12080601e000c60f061801d02d01d94084048261041d0740070130a00450700320820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 320256384 1250 320255134 320255137
    0x10602060c0f0c07090504031d03061303090518040209010f1208070201051201230102030c061303110a050a03140306030d080a02091c0215211e0a0b030d0207030f0611 73
    0x42000e601210040e45c1c403070200c03200a04042e00e0450104103440d00c0816030b444000418903110030014007501c0207039240c103981c0f0041640020105c04108500a003c21181e650180d440c0714268100c0c010b00c0300340703002c0c8148114550181c102000c10b00940008000388400f03921401032180d840790000c1d481e14042d100688007401520905a0942400350010a041005a40131031030040070103907488c8400c403210016a164030400041e80d0752508040006840c0070085887d01e01403600c0ba141c240b82c2951428040c1382020307102c50045800c1e400c2400c3c60414190301c4030928100c070742000c2c0b05601d541003090010b9542c184040d0200f00b81324900c0000f4450611750340c1038481c903890150001c2228910721003c91141004c0040403445000002c000b040c107100504166216941e04c01c080c40012003407207c0c910341c0e03004020010180304a0b200064031841301440469402500c2c4001c010070005025803c0604101c9510012011980300d2007007040810303501c4040d016015080100020700300007003c4406c245e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 320257634 1250 320256384 320256397
    0x50d020408010e0c0301180b04020d050703080d0e01060e0106080610030b0d110a15170a0b150c070b03070f051309020c0604030f03021606050901090c0f0f05040203010602060c0f 78
    0x703946003500b014404000811089640c001c114001c10541b40e003240440c5c18031300c010101500f04038410340064010304101101040c0c50740100c0407100d010755690f07140c2045500411a1a03403041c0c8841e482c06a03c00240143c001401510282000540c100b82004280d801c004041c6d511403a058004449244d000b540320005100000d410001107003650f05016118101d150031241c00342c00c0c0030b5000580c010701d1aa004541e0740456803134040320700c04803800704405207001d4a00c5422541e03074003030000d25941d100c113902070b802c08600c000741d1200d490010792410500142c0c82606415001c104101d4000da00410604041e42142041901d840c145009032408000c160400e0003203910014550014070b0000500c6071050b44030341d03a66000700d00d118104806034044c1c0404100c00b095101001c03800140d80b42c01059014419900000780a0442c0e11020644074455000060b220301c0c4480501c00382d070700c2071689400350000340d130150700e50b51500304001e41c0c44400500b00198414040f500d00c0d011b03503004d030880c0c50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 320258884 1250 320257634 320257649
    0x130206030411040e0f07170a035304080a0f031b110709020c100c0509180915040206070b1015090e0105010c0b15120a061b02070f06050d0204 62
    0x80d440d0711030401940c4502d01000c203030317003842549000115091010244c0c1004012030001d8011045a554151114103000d4102e031300c004514190110307000b4203e140e00d507045c00300c0c142000c412401400c001d03240300c41c00e0f00005151440e9200708004114820700b113030000300661610f01c001d034900c014120001d19114a403510310081c00c80b90040540e41c0724000c2c0900011030002d603181255201d402c1e034100d204401842d8501c0d040a80d0381c9214620507486440620002d040c1585400103030f6000980158000c440103214225074004d2101813501084501902188a1103011131410180c002071540c0c054520010a00035071440010700280210071140d00a00300c080420454030107045010b00a003802c0c2c080c00501d0031400d07000041070744c81607a00381407081c0c00c0f0b00c808482d2307191501d5101d80401c600300d009401440c185a01d0111250410908241c540943d500042261400d1a0104c2a000181c1c0c840c0455002100501a4021440444045078400c0c00d0a035074403500204034401070301941d0300010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 320260134 1250 320258884 320258891
    0x60e0601021209180c070209180c010c11090a0903020601051c0b1e040609030314060d060b0604050a12050c0402120f0a1803030e0c060f2b020f070b0109020313020603041104 76
    0x421700709100050421288200c07180e00907035a40c0c0b400303e018010b0038903c03203407a580150141052540620350f41114240101340310042c00c5c0010003c41c04140c1e0586409020990b542c4001c41416818800d850143c01c0031146909000011440c000d60802141c90190000c000c01d07001c02c942e1310f070580c058510f001c0c00c3c1100454600d001d0414500030200280e0942c042418179000fa0342032151420200d114680c01040c0350455600d40d103650006100c01004a600088100404980d80e0b0350154041d00030b14400500303903125111841c0050510800449090080c2e00500c01c0226031515403c4055100c03003d00c2c80d220345070791784100c2140900400c0782581c480505807406403040c107500d60031111300b2028143c00c8500b118114410300140d4414030900c001034100501c04590f140b40e0f0a202050304200030244941c1c0707100580889400c03688402d40d060000000000c1c80801c200c01c91100b140102900b550460440c0b0303081c10811040785000d18000d1044c08008002820042901d0f80d217281e0042c060000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 320261384 1250 320260134 320260141
    0x40e0f0103120c0b0a0f11040801230114011d09040812150109060f0212040602030a02060c0a020303010b03040f06060e0105030c0d020a050d0f06020307050d060e060102120918 77
    0x4418646081c007042c2c4218a4858401520074000c1a04040c029031240034005155121100b000090a15840140706141c82e070384240000511000900b0140010700000120b44c0f0301d050034060416031491807801813034030000c01013088054402a44225103403e0030100b1100004904c84003109084620080e80b001a00b41413009128900c07000d0040708041d030320301c0791864132070150a000b0020001200c900098075504184445071061161180003130a074012902005403000c00708110743c10a402010050b071010480d82005e5604101f010741101044003001d140c64440e89009403284414003072600300c1030001003c1001c10107140c003588520741e0840010030485440c0d00045044600070b11400c0c0c840d200d2004104601d02c1c1c4190801d004075402410400c5480c03408040c801c6039200580c080d03514180766902074020480ca8002144074003440d82c0c41583e1a517080180000300c551a411885a003041c4000708480c50360001004400c12079500252600c1c0c03084030780064010402100f44001c200d0b00c543c01d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 320262634 1250 320261384 320261401
    0x402092e1e060230120a0c08060604181d011b03060f1809050c190f060c030f0c0c09110306120102190806031005130212010605010f1202040e 62
    0x4103251180036a01d401a070b507194000c0340c0d115035462115015410309041c8034a0704481c203485010607441820120704215408000c0110640200d410301c4200c2d84603220041caa40d404982c041e805402102c01e20706007400d0504607160b2990b0100080c0d03485544800030030a00c07110040c620425403411009201c000021042501404a64040c410110b4140030000c150721108107a5902503d500b007000d54818031100c1c012401030899080140da00d8001e24070510440e4580d0513a14003441100e501803c03555240c2800214007941d607501c04400c00c100b9010b0100043d51080030111401121719010441c442d8a0508040401031644240e01440c40c0c4550301c071500ea020b2001e544501c6080b540094030008603240c1078240c1c421001c01c484032441011030024190300039503200d80c010700302600310b440140329044804200c40c400e455061121b20110641021480c026540700d0080b071030396001384800d41c40c080010b0500c1c1e16140c0c00405024454004016451803581036500a0a00a004a1840c10702400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 320263884 1250 320262634 320262659
    0x2010b0607120809060702030f131706040c0812090d051222090c080609041a0a0b03011a0906100c08130f0602010e030f0706021306180801050402092e 66
    0x100b0750120745040002801c4034004a18144a5151ba402451821200506011280d4090100424030031903503400800d00010f40142c02c2c204038100340041038507081900700740714425103d600500d242d074007281551031304a001340c3c10360342d445034203884c07044100307016290a0341001c03040b0702ea044200c0400700e035958402d00d091042e2400b210b100d170070319005e041c1c41c0d034604802d44090101c403c01203010f15010699500784103090580c45030059000c1b44c202200052034440c0780130196110003809855081c5000d56203400c0c4184071702118644910340010001c4004981c40b090000c5c601c41c4100b11041c0c0350700089000399001188664003407170880d9190000054109402850701a8524103804c03c040031410a0051007030503420401c0200450400101c418010016071100c0d10440d41d841d001c1c420503103452503c844c080d0140c002c644901407509181080c00c101c0031100d5002005907070420040c03002603140c0310306041c7c105007100380d01d1000b25445d14180c8581c0100022910b5585041803000981442414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 320265134 1250 320263884 320263913
    0x9040b01060f18030b091c02060601081503060c0a11190c1d010b03070c0206120604050a020a0c020910030f110102060c040627120c03110301060e0a0c02010b0607 71
    0x1220b81842c1d010740303042210803c000489903454001c0d4a94184003146840b84801c0e4840a50b40449008405885402e04e03512920341c035080142e8004030610030b8540c0c004582d61382c483c480441801d600240300340020340d1100c006d01604001000000c0d4001e0581c80b0311148a030814580d4100e0b00300c180c542e2100715000c00052001d4819146210000c03e691440d40d546591300c8002805081e41030342441d0f900a010390018014600380200454464016114440a4600d4000d0454a401c080c40c1c64000d00c000e039007000b040d09442e54410001d44515503080014490120340680f5110074950300d2042d2507090150700d070005042254000d00c0002000805032100d65048800c0c0e00350b80245e241c002180340c02c0c0c002d80c0228800328016100c090400a80e1000000205000c0c0031030791a06513407809491840f07103030f11406030b98906815509005010584240502180c0c2c15402009a00d00d0550f0705401c1d442e020b085403001d1a06ca00e03407002800c2c401d4008401003034008040c295100c5440c50704d984078010b500e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 320266384 1250 320265134 320265137
    0x70b07140c0603130b073b0102010c020a06050a0f09080d0b0904030c12031d010f0b03211b01020a17090703050303010b071407030503040303140a0509120a0209040b0106 74
    0x411520701d681c140001a24010021004240003c1501c0e580d040b81c0b07028028901001c11165003203000314201042840d001d40d007a290015205040c14408504045003c401d88a065a040032000d003801c90b400540409140d03001140040c0780c0c2c07a0b41100c4000361060500d089040d60030720844c3c40c14041240010414400d4400c010025400440203001c040c050888015010801c0400c0c8440861015455400b20082500d00000c0d654040c141c0f60b40b11009012710402d80341e5403584449076281103441021002c81c8202d0040401500d42d42d030311800101070f50030364005d01b50040383e010148002d401c1c0004074110807034001d540720700382ca540003010000100c038024100c1c5000c0c03000c60458000840c07050140d94021001d14a1a030070010081d100fa881000d04075105070301c00031203410100d41440070760055441007000e1517031549542001008142d00c1d050944440b40c041001d000d1040e000821603400e00c0302501d0552322500d9500105007448100c0c6006500250108100401c2180c181400c1d8180d6646 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 320267634 1250 320266384 320266393
    0xd0c0e0d050f0706111f0b2d12030d0207030207091107020109050915010e010921050706020f251e0f06030207020d060e0c1003020a0f11100905070b0714 67
    0x29400200d41150001c8210a17140c1c009500c414000c45405d00c194074902012100850f40e8032241010500c200303241c4006501c40300c8074030a003500011a0b00d20b21644030008450102c40301c0341c13998903942c07248242d16450085983c0000c0002c01c140c024072403100140700c081010080d464030080403000685c010030f412400100038800103d02454501000da00031081c0a5070368030181821001901c0048000c000e61b030600c020b044001a01e40c90594100852460102c1e1100101c0d00714a440f9141c2078036a00038030159000b00700658550380000174441c100c01680d61003040024000306040300400300f2500300c01d440c04851801c52981c481c00c660100c0c11110171141040000d039403150110102e000382c0300000d6018007422801c6010071400e80000c0622501d51080c1c803030210f020b400040c9905582d86040300801d8003ca104041203070403250b800c0c0c00c40b0007401c10340360040c10912002d440c3c01d13142188250b4a9503030352000090017010410078028001500e941a982c80c00c40c103041201380300c0108060003506c40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 320268884 1250 320267634 320267639
    0x3090906041407080406021312020306090304270207140115050306060a12020f0405071106150603010b0307020c09010f0503060112020904151b121409030d0c0e0d050f07 74
    0x1401c2c4500d550018880300c0b4801d2603110364008540b4034001901c10307280c1382d800f4008141504034582500c00105042c13500c0882d00885032040c5400c000009002c100c080e0020300c400c0002c081f80c1114201c0510004907540301c8ca5040101c10340c0240198003000d0000c42c440701c01d40b4000301c0150710060b1205191300d2011505517984d0b040554030b000844540707402c0250718504200c807921700652910041c6c07000344041c4a48013a4000308003103030021200b000020300341c00c1d4001d034050418805030340c000200781582025162402d01103045072006226021100c84000f0000d42600e10902400075503100007010310007996512030048049a03c0d90107100c0c8030703000d007000004612440d0a006600b51798040c2c1207200d959520f855a4914981e13000c00c44842d503031107804910300d180740e6101200c2c4000041e19040c0c5040030ba558008102d070041007420703190303244420500c920810300000340c43d01d00c907854101042d104035a020440300c801244000b150001c80b41040d401c01c100c0c0c0460740642e548110340c1103444180c2e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 320270134 1250 320268884 320268889
    0x50f240906011503021e0c010c09080615090c0c01050f01080106140a03030e1c0c0e06090f0f090a0209010b030114031b0108151e0a05060c03120402120d0203090906 72
    0x5001c0c401c0d038000d0580520907990040c0242c0103006d0020403a1040c42c24010340070004c06041d84001c40707007052a50354155030100300380c200c0c081c50302600340c0ca0b0003401540303004c0070010844007070300140078416180ea4000544140d01c40c0200c4a101050b90300920036410140c50b01362a43c3c0302809110700d15400c0000c00314620320000362035034203290020282d003011407546d02d091f944000c8a9103c01d41182078006804032008030540540c1a0b580b0518000c80900d282c0980300c0540310000e802d05228880c45000d02c84100161505141c1040c80518a03071003a80300c8860141c0381a07038444000390015500b40c000070b08080d40700013540c100c0b000c041010110040b840101501e0701503d0351200032412080300d000141e54400c6015070790101c00c240b11003008194003000166a02142e8245900c0f694070340805c0c40040c2040c9090400900003507074038078100407100c0c00e0542c490084411181c900c072050030004095503546046200090f5086042c0c403003803400c80d00001d48a9000100050007400c58001040490 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 320271384 1250 320270134 320270143
    0x50c0301020c1c03060f080c1e0f0910090903021606090302010512040804170d090801020306010c021e040219030c08040308070f020106171005010f0311010c050f2409 73
    0x82c841406007002040001140b58600322821140c1c04042d968040031a0300d40c0c150901c403000d0009030300103200580703582c400c1008580d501903140c000205070540b40c1c5500c4d11988440744481c0310884000e1f80da6030b034000d00d8403081e00d5140c0c4000810f03030a043c483d505060300810032401310410a83c1d0301905a03203408054800c1c0c001840000d0002e9010012001102143c82079150024410540b442c5095590001000d01032048070000d092034020000c00c00340260414039400c001d104240c020750962500ca4000303025000306601c064011580e4060010301c1c9a84940364100d1900f004208545810907200f0040c42c1c45004501403020070310303210030710700d0950044840512455041d555441d0303550b284441252400c25200020b41959201c02c4080b4002e04d680002070200b030202d400410305000714039501e4003911010780c800400099070310400d1000c1001001c40f841820390070308210b4418181403411514000703103108a84001e0041502018203e5001820214914003500c9607800944600f00d440e03480303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 320272634 1250 320271384 320271397
    0x4170406120615020a12111b130c1b08120c041e03022b0f05030c070906050303040501030c05160f1101050a02070320030106030b0603010606182702070609050c030102 73
    0x540d00003400400094403a6410310725002103483c0442000303424a420314640b01d03423507084030070701100c5485142c3d56040070b082e0030386526203032601400303807491001e00540711900071825015072000440240007030142d40421070b442e401c0f100900252074039001c40030852981148c0500c00424140c800c0005020764030780145001d6980003001d00c0c0d4000030084054045817030f1700001da600003241c2aa00c01c003007a002d400c104c65840c0540091540d841551010700d0801071741c3d40207250050725040040c480c0b5100003042d202900c10a0800242d0207400c200266a45e00400c41d406140c5201c1290071010800c000100c0520340384103c61201001d168031005482900680c0b41c5c0360300581c05a0010030204000100c0c00c50b03030707450380d071108c0710b03200c1210010034203480e102d07001692480031707010601803107040c00d2240070010149841c012880c1d459924440c40100c1003449030b10380000c90915460501c100314540f90b4180c00c0003d03000c664031a039518000740905540d0000b80e41c01d01500c00c0c010810f05042c000c4428 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 320273884 1250 320272634 320272637
    0x80303040c06051315110d032a090b04030606060f0e0f04150503030a180803030103030c031101021c360609060b0d0f050c06040b040b0304170406120615 67
    0x90542054012a115081300602d400d00350b10440b800101c85402d00d8540e410540300d40e480c4c0c41d0a1280588482ca07100107100710000301403520074a07540c0854015050344004440d280f114584141010040315009050b4020344501d1400150000801003543c1c0440120345054441552030b41e04110f040e1102c070250300481d03401180e01c951440301482d2940c81160b13070b140f415445541c0c42c1d40307420100f07142d40c22100e0420040780b6042d8401c191441c5081e049001022500000c1d89590304646c1d00030000c2030301240c0102484603403200d00f87c18803c2034055400140c00300c145020180310300320b115070280c5010547c0100d58031410202c5084c043c0e80c00395a0302c0d4004800e00c0040070b00c290b50342e0302004100200c0182c443d2075660291344055074405005643d01c0d030142d1091905450340e810b02754180714030b0512880c400c1d2404c010130000200340a0940b022501050900343c4c6941c1c0c0d070b040c48a4900044032031145a03038000600032038555044031581c0c00c0e429400d0020070481c0c1d12400d80010b4000c42149090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 320275134 1250 320273884 320273903
    0x1180f1104063e0c0301050702120711060f07031106010f12030c02040501120b1302090f071b0605070311070203031614010c020d08250e010507170405040608030304 72
    0x100c46401143c54a001e80c2240326041c3d21504080707080b0390408000c000000448442c003404520540d0108105100c2c0702c800c800800031420b00c1c3c0300195403508209028200c86401007005002e101070701c0301101c03039200043d2219644281028100303079250300030042180802d2282c54800e06000c00020041d050301d00d020020007509042c001d0056030003140d050100e04008a044050780181c986019080c001c212400b20308400643c03a252041042c1130060030300c48000740d07441c600300143e943d40503d103401c0881151802d03290381340e086040710000d00341400c000a0220350f08010007000368650002d442902d407660304000417100c00d01e500003203100d1024081c3d030552060102003002100c5540c85132403e0712922105403206100450182500c1c0c0070001c050140c2c0020090001c0303190400350282e400040070b03480d40700c55842d503180c2088801561101c007040105841c40d85c0c038164010801c48851076003021942032401150304002e00c0c2d41e4818081c0300d0142e0b0424034002044003001042d00d01469000f2002c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 320276384 1250 320275134 320275139
    0xf07080102130e160315080a0c0302030d0f0c0b060607051501030203060c0705061503030412060903020712051b130204030f0507150f0f03090b0a0f050105060903030418021201180f1104 81
    0x11000f0304002c451b22891121990000580c016040261180f5548107004107503080f891401014100340d580500d000c00c1c8803a02d02c0b01800c0035030118000b0f0500740d0000b040302003500c03240041038440c090408001c125120740c500311140c40422a1400781201c0c822811102c185c0e91380f881c1d8410030f005801000b011644038030007050010000204010000f000641120700342640c42140f1a1903030900c40060781c4582d9600e50340c4062503410701c10301021f854805084040d080d11540e030b45548188040400090703c10940086410f5078a4403418004955150404c2d134a0702d4890502c0000c4080203041110544185000000d00d000c09240c001029469621011003a1b04410b0056032120201e44002003015035411a03903001840000f241400f40c8503400740000ca1002d821840000c4a806070491442040d013031040a10350f43e0000201ea06490700d8400c40c01e60503c040d082a4041d000d5005125090621940040303090140c0749407016103442c1200c801c1c0080013400030100c04035909c19091610121042005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 320277634 1250 320276384 320276387
    0xe160501051804090b07091d06060d0e0a060f0e1506010f08070507080a120b041103060d030c12080712050103051c0512010e1b030f0a0e0f07080102130e16 68
    0xb04564802810109150140742e40f4891800c0080360054049142040c0a000ca01d80c406040740c2c9040c241b604030880c1d8200f0794002040b50144600260049807503d8901c04414018003400140c564008010f028114950764000702800b1402c02104403440780034091140003000d814024050305060312804445804004211501f1030014800350500c0801c02c0705400040004004107180314003951407041d90400640e42d401566070408449105508142c0740e141c42444480450360400822a64200740901c14501601c1010f00c00c1e40141020070300c48030805d56150056003540c0f0508050751800074408000c0c84080807900280001380c6240d2221a284155032510301c0381032400f40460404a082c103030380d00c1c1d00b0404170078241c1040c2406000034049c05139020782072203c2e4104810a1826908525080c240c00307203901001440c41d10b07050746504808610f90002d00444040d44045003d8034032944d1100d44040c040e6001481040407803000100014942c3c07d09500c1c0c5002d005030000c4a200d00f21861300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 320278884 1250 320277634 320277667
    0x27050705091e0d02090405030c030307050901090803090a27020f071211060a0f020c0f1e0f0c1005070503030c130f030f03080402010e0a030b040204050a02131a1c0e16050105 76
    0x100b147c2c4c51008101c400c148440030400703540300b032165650351650740e0301e90800106400040d50000d142a130003800500f40e01d6464902c50015243c8004030440180300d00503043c05513940411004074054400110303140c20500010050013401c3c0142d2500707440f11558001200c10320340f440380326102e6420036008103840d0f4a840e0410070012000c41c8015080050b840d03270441c02d0100d0981101c0c00d82d802401d1030100b400984110307076070020f40d80c40944090307140d90200300c0d2a20031119146100742601c16001c024140544103440d02590440112500c81ca45542c154201d40c0c401050441850034158002a483d514000c1520540390b000180c05052120355809030343c98540a8003c074140aa10100820282c89607041c3c140214002c00102c130130b5007031500601c82119805003407008114010091320a1180301078071401c0c01c8403003040706040030440b960b810204c180603007083c00d898065040b401403041407180e00100440d032a00016500c041a9150881c19154040d00c81c85010a00c10322603030012110821 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 320280134 1250 320278884 320278891
    0x305070314120313020f04050c040314100e061801020a0e010503040224040e0a0e1f11030112030e1905010e03030412060e190c27050705091e0d0209 65
    0x100712850865040c001d0b0401c1e42040b1000341921030605450029458a42581101030b64181c9007040b4509040144a000e44100d010140403049560b034076044682c410050012807a90208040040c1d0420818184d00c98000b652280281100e030076003400c5090061003103468079422515407070400c01101d001074400e07800051050f0b9008030703840454400807180ca002091f002c001e0074062503a8904000c420300341c031031002e400300c0b00051615403c00c42c215000568400320810700107000304500d00021107040079090080301d80099800c080000601703440904400200307540300761180400000240184640e034440007110008030390246070100100d5000e00d80550072101e01805803841d240d21000060f1952080c642c04440c0c95580307022480c20f440043c40781040c0340b103040f01c9005040005407600303406907603140181c0307a115100041d491a12034804034060900c0b00c4040c0140110b151040c0301800c50f410600c00c090141104c00384d0b490118040c601c0d460003a8200418502c83c0030b0503034081c001d1404005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 320281384 1250 320280134 320280173
    0x903060b0102011d24010b0301051507051617010509060109020a0c02030a20060c0303040b131a07080c090307090902010e030709230601020d030c020c100305010e010602030403050703 80
    0xf11030b6100008881454040d044c11210018180c400000c0c501040c4400001e49040d41104103000601c100070145003281c2c116441115a042010040703941c1c046244074101004001d81701d0941a04080c54240308401c003101c08070b01411403200309000c4900c0c00da500498915150360000c10050001052603400340110050f1860000b0707402c1250b901291038541400d2066854400026984100311500600014038200c26500380781071000c45000541c0d0381c04042c0006004480e040300281d01410007260f5030142541280f00070707085c11105003500020446c113640001c00036030030b5030014049100000c226500030b180600200682407074241c03440000c00002030304904201030140768941d641c0e41003005002604404600160810b4074050440030310240028000c80d0140c1c100804c9626038000c545c51840040a0802140c4581080d84c101d0410500007600c42d0300480801142c940c007681907215505950b961103144902c0d0342c031380c034060340e80b80510303c0000c1180e4800f5405000050b060000002910180e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 320282634 1250 320281384 320281391
    0xd14011e05040c050901080405120706020910030c05040e0c090604060f0f0318080304020a0803030c030a06060207030201080a1a040c0201020a1b0c060c030e030d050c06060406061e020708060f0601110c010903060b010201 96
    0x20100d02a540d004030bc003601d60039004101d00c41c40d071401010707070040a4401d04003080200d03c0b0042c0542540560320502e10a242c0520004a50142d8841140d0503800c008024030340d2692603480c05401d40700740301950030020703082c50000a902030281c8100480c070000310543d1f5003a242c141d030320104182c0c0021700481c0c20419559000039102810400345002d0120707503072102d07124940301000c032007100c0456005c002107621005080002d82d030004a200e420800820000c201c0d4041c580c815400d4001c0100c845030003901c2c103401407201d698194007400d03001c0a50307036885282c500920700d0300c101c1d0340d000312001c4d088941090b0b04010190003000629a502e100e42000a9103516110000c0d04000190041c1000f007000007030140c42021050201542c800d03422103081114600700080107103c822118070003900341c0c8040c080c8880d40d9000708602c800920500048401d1403030f00089100d0909810303150b850104480d000401d000c81c0d00810002070300740042e034030500442d01e15101d840c01303010031034142810340d5603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 320283884 1250 320282634 320282653
    0x9050a1a041d06010602070312020307150507030e0d020c1503060916020a0615060908010c080601110f012a090b0a0c1e051b0303070f080d14011e05040c050901080405 73
    0x7043c40501e00070a495009040305502e1820100480c4418603620000c5400400002c1e001940340c8c1040741343c6240c07540d00000c1d10341c0ca99900382e0041c02c6102850500c0d10030144210030140d40003a04a461a2051320150b000402064921000740401e64280e60b209080c08001034071022404040c0640200d00d2045500d082a40d03102c690444404010301803940b0807101080c00040d822100110041c50207100070000902840d800030001d20025000b1810008540035040e24008100042001c00200b40002c1009140f130040c180990351030a880b000b050031004444803844da00841c0342c0d07400c89000300c001c540b03485c6507104219400700150310701f120740259148000c05854103455620f000e21b4400d1008003210420700c0300e402c00743c1038100308091107a4401c1013a040060021084e50084030f0b480584140c40308a10f0196101400c3c0c22580b10720340c418144000a1020110b40045100d9490a00b00e04810758079002484280d42401d4a0304022032010407a0082e20b510601c04994054003074416500d4544 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 320285134 1250 320283884 320283941
    0x20402160f1a090a02010c0c081f06050103090503030406050603070b0a0e030c0f220e0a2102061b031519091802090c13030f0c09050a1a04 61
    0x15100080c0c0700d6034051041d410402000300c08101c03401140b4401440b10349031021480d5035070182290001d041004c046042e03000c2007028224103018104407016162240c1c1c084156032449026001d00586070342c20300500140a50081c42401191a00302c00a585190343c4c544a9601410b005031420350148184200010303464080f1024040110840d81e6055500d0301900c10545414039202005120700c2040e110302c10f040e52000c045801c4100b0200c00e6039a000041d85c80000100b00780074001945d4000c0c400510b0030000c0042510320790384031954040d00b060704070078012030381d9010403500201c403c2c180c00c441880c40d180c0c06025550007070700c0783c03a9000b58911000c04030321600d038190600c119042040c0e5003800f58a0043c010b81e88020a884d43c0403e5081c95270700014503115014101c94041c05c00000d219075999641540c0c000590b406c502c0114401900e4a00006c2545992040540c840c1c5014041a4200401d02490501000802020510040241c108001000c0b0f5080101450f044200c0504410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 320286384 1250 320285134 320285167
    0x30503180a0b3309130206041d100e0702120d020d06180606140702060c16061e03021c0507030b0a1401030c05030709150903050105091c02070e0f04020402 68
    0x3e004074401c40d49064000c103020b07030140895168902c041100c0c81c10551441e150108a2640602d4490070250151050300101d00188644e402401035030b03485082a140300c101c01c000aa00a0031001c1c20241c5107642c6140d01c03410020140c80c94030041c0c00040340498840c0d0f54602515001c00e50b4500189048181c2800500303d442940c051b03903a03c2c0d40ca820800f10b40109100c2c50340140f4050900c0420b625241d005828984140340c0c2c02840b03583d0124000c3c4e007222041000c289503903121040f411605465100c040d080080c00710180080c014500c001c044018480d0003070344e40f08002c541e084582d81ca0540d6161000d400000c200b1401c0642e40c00010343c80d075a40c511000010a9400c5481d103a4594403c0010700b503803030704804a01403103401c006000c3c0655001085000302c60442c94040901e000c0040e04036040d048588c13010f0255820b06052103040107002c5100301c5251400c00c0a104000c3c02c849044c1d80740d0200c0d204020f610320299001446007058120300b142e200744014001440c10f4614010176024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 320287634 1250 320286384 320286391
    0x30e0d0c081b0a0f06020c0409080f030103050c1c03020c09070e040f090204050a05220f061b0809060702030a050306060d061514070209072105090d1803030503180a0b 73
    0x9014560a81d140c8030f04103500d4600142c400c10b05488192414000040d545102e110345070390259680f00c1405050180785415900800781c1011615a00d580d203080c00c1d40d5440c4602400c034840c40020a0340d03181d0b10325400540c03001c0caa050300030300071f259000c03010040c548400400c0d000600c400c9140d00651035889205d600c01114018038006200c0d0071500600007281e90050505c07100c1c91500090000c042c0617002800e1420f004c60442e0140e101607482d14100500348035800030441400d00350000c4105c810701940310b440700074030303a04c1140603520586229641d407000c2e114400580c00801c000c00a4038403410045500900280080c0e1800e0b03107003003900046513240d91141001081c1850703410840c3d6804481089800340850b4105c1c00c1101640025241c000c0240404e0288602610700400c001012102c0c46206448290b041100e0714107460700755150f52400e141c540008004081464407080010402401c1e41c1d0141d13502820769869500300206690040c1c01c42d180391117280c00140c0002c00090740c3d24070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 320288884 1250 320287634 320287663
    0x50a020f011805060c0408030f0a050c120d0c08040809100903120f090e150d0510050406050604060806090604060c090902030a2a0c03050a031806090201110a030e0d0c08 74
    0x1c6081035080030380c204070001e03040340c142120806c003c005d8500000306807004c6c0e01c0c074030101940c0d40e4080c3c1010b0300d180c810741401e8000785c050802c1744241032a684014010020150006000d4080880c004442e1840101c3e00200741c008180103105040c00d08840040c06202d040c1081562251243c540c10b004001005d0401c0c0018201780720f40e00d1240c0c0c0001c0081c010550303610400100d041c184102d02c54144440c001e41d02a6038007440300c10606c80f0030000f003085441942d400300f085051609240d000b90000721000fa02a5041a4001600da08001003130b40c814600074010340a10744841c0d46580c090b0984503603640421a14817808610a1224401180242c40c032810001c0c1003034160000144800000301071450355070280c03000c4140c4daa08040d03500002070381450201d9a0702c04000e030560081c20f008003448a4500120740c440300300026640030512a60003600c6d2100a0341401d940507680c2e5081c1038006002516035800b042e000d0804840140c00305102d9000303480f0326038881003034034a00318051482d2007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 320290134 1250 320288884 320288921
    0xc1e0613090506010f0f080a02030c040b0c010b010801080a030504180b13050103020901061b121808062707121703040f120906050f091912060b03070e0106050a020f01 73
    0x40250303004070035082d00170140e0926603014103a80d0409410101d0090215013110780000002c2d09207004902120003030061507001f00d40702c681200d40e59000304013080c140307408511404008920303c6000503100740c003968155155480e00c0c0c20a18440c0c80c074604044014130141d01d800040e22580c1e42c20116170880d00340c9031070004e415031460041020f1386c04c040e8401c4042c840c0d4030442c0042560011202e070103154100c1d5002070780700f03d002e10403644042a081d00c400100114280440c02e0080410564007034115801c600d4449110401e004814002c900800101940400e808000003015600d01154050166040d00c0d003030390981000c40d405070f004980403154a08010844c0381044985584040480c4007450301320606401e0800c0a0500d100d03e541c45810248042160460f43c0d80703a2140341500340da2a030080d100d5aa590451820003c802c10003120941c0c0cc0140f4060300b03003030001d5520111760000c98009030310391038100300740c840d5400050b4180c21801382410603254101d00b400303420074420402c112034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 320291384 1250 320290134 320290141
    0x3031b0c0e0f07050906090405060a080d050d0506040b0d021e0a0f060f080f06120a050d090e0a1401030b0a0e070608010612021e0a020a0c080109060e0c1e06130905 72
    0xb14070002d00e10740503c4030901254030300d5118401a5000c100c82510300041a0b00c4a80020700b640c4080e42c0240c0780ca2103104008540346a10030041e12003048a002c00781b001d51141c604020a0302c0c403c1c00341c0e07174124102400b1600945002004059425a20602070603520382074800301c1c905403141d0304075511410710310380200203403036000c11851007142d4945408180c0d4107004500c007501090281034103214070314084c0001c013410014850440c200c0d610400721054446211400303884400140f0510030303000310500c00103034642c040340180070000604480104150f8219541d81c10b008001508032030b07403641e850000c092030707803000c10448029181986a6181c1503240c244c2c02007810084c102c0352803102e401449048810b5030316848201e00c1601504000382c803032111301012803400381d0042024141540018000503506010b46c019500d050241e01d003400000ca8046a507a99201d054031580c0d0040c0c0c101eaa0140324810100c13508240c407200034007140ca04101c03a81e12200c1c0d413540750000085640c2e5001071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 320292634 1250 320291384 320291401
    0x7020f03160b03090c03031b0601061b030807110114220f060c111917030c03070f03110706020909150901060305270c1008090703031b0c0e 61
    0x904851050460040c489001e40c01c4000024801034401e018000b40d0210100f20001c8003441303000103a8030301808580c2c80304000003024011154001111809004031000030605502c550001d205541d400009080a00c0c0160b03811100103e00418000c10405000000302c0760300c070203026071010546140200805803d210042d0030050313585104195019035145400c100080d0390300c2541002d01e41062001610701034910003030721000c0c2c0800400322203000301042203031804140040c0c0c810180c058003143d43c1381100c03090b500071244030a54541185240910000340e540d4440d1000d46401c0ca070340d00e008645040700c64420041e54200071400c82c1c2c0103402007419101828203220303c2d94070000030f02280070f600030b0f4003021a050001c1802800101031b1580000340c88042003003803944007030700c09a9200305140703000600346840b03d101401903403048900b014560a290312a0382182d0007120b40c00054210031746165001c0c1e03030b004401c058250b410300001801e01c0c04502e40d20a804001c0001007103284a80c50184003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 320293884 1250 320292634 320292649
    0x120303050a0c031a010e0a05040603051006060f0e040c0215180c03010c0c03050703030219080906070c020a0b090d080c0705011103030705040605160506151905310507050702 76
    0x1c1c0030b04152400e858400303040c5580d007800f601883d080c00c003046446895008904035200035084960442d0070b1400c00002c00400103a2140303404116901006140d071202d0b0116060f440015405001501019003075040d4a0030303500000c2021180c4c0101c402d15a021488240908403c58030031285190312410250071000c140808940901c048008009440d240400902004102c200144c1042004503070300c1c0c01c0601950481b044004000e01815a00d18030306001401d01c10200c82048107030003140086076019010300549500298000c000d40400c50a100d2084403541024040039442601c81c8600d1010554400040800e544004044c2000c01c1c1040d00144c06ca9480603251a5950b004004101c00c0c0340e80a0142d4003a51444e2034680d0f560410a03d814070130070a102c2010705140246410b00212580409803a14801c0c0305032464446a101090600c402c1300c035610441760084180207a40e01c101c981e8a0001902c4080d00b014003d061081c09006412941c2c212080408030300001400020761401e4403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 320295134 1250 320293884 320293901
    0x140403050a090b0f0d05071115100504140a050c0f0313020a0501080106120f1b0221070b0406020a050c0a0506060103150b070f0309150503060a0e130308040c120303050a 74
    0x10b001d150450001161415101399017802d21080d55800104401d01c0c4100d604030301c18201c0004030381400c2d042103005030000700160303000c0156014500300048ca9044c20300610400e4413100700c0c0d400807940c48101c0030001d080e0080c01c200072020704000c8140c001c0390710005940640d100c0311040018001c0ca206000c041402500300c24144000e0a0040224a50040e0083da10188000000c1000450340141002910001400e000300c900140d1252851980c0042c40c40170050901d400c4c52084400000704003907600c9602000382802c20450000b0780450520313001813149580c94074041c0d10303042400306510f0522500c101d08456a8211005000c40c07507915016105214101d00104601c403450600300d0341c0e1030300c56414010650f12907210180c0c2454061146030000f030062224204441e9070000001b4402d60048800d28442c800c1d500740403c04464148801d07100300300d40074000315102c44e07940301583d11100c000c10865108050010120301d1410074030700340c40318074460384001c40c140c105140340500707952408 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 320296384 1250 320295134 320295149
    0x903200106180212090c030723060409021c0c09120c05060301080609010e032803140a02070c080a050309012102041205010c030903020601090f0b0402130e1f09020c01140403050a09 79
    0x40b8046e03140c0e000309045003240c0c5001c1e001003022107280400e800d100d400030a07883d0701400115000420401c580c0017440317907603010b072843c030840801144843e0490b407010034a00c0008401c1101400b102c481c00c00302980f8140100c0005038100d540b00006503895200741c22040c06500402c0078010909000d018003a02c0c1d00c1c1c1000a181065201c41d0440c0e0b0f040300d0440400c8411458450808006000e54803038040a0400c00c2aa48203250241c07000c4003a61024004450502c43c2c1d0800190f100c03400300d038480aa0368004051032511000c0c00c01140c94a15082552040d80d4401c095412441054401400102030385259058601110708200d421114130042d00700c24076082141c500c1c00650f0208000c4d041d5138007001c0000d0101880780b50700c03005080d0054a103410a20004045503c5a6608902c00450301928840403040c1d030394403540040a840203003001107c2d80144c109108424460f0042c0c000301383e400000140300040681c400b030300140182c9042c0d021030000034072419078981c4140e40d4000762505 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 320297634 1250 320296384 320296393
    0x5030703020309190312031109040e0d0e01030905030f0913020706050708090a0c03060203072303061f1b02040908070c090522080306041808030f0703090320010618021209 75
    0x85d6220b501c0c085061051850800d036954a60025803a4a6005e40d000384002410400c00d0f100708980882e940c0d0aa041c803800442c0d1486003180047d0311a00840c1e0500b40e0000c061800c1c9401d2080c50062608200400313940300020304c26074020620780f4030180c0724440c0540c0e00232440341440080500b402002408608582e001205c2000125014100c907600b00e03540242d005a60f5a203540e0b04a55580441080703840c7c07034520381000341c0e0202800c006940200000c41d500ba682501c140c09500b240d1200c060400c02045540542d40c11481c3d4010580c08054000f0f0b00200b00082d19568207030b050b50107100102c9210003034480074024807007107209107540305006843e001004030181c04561120700017810010081000080050403a071103c2d04480c52403900c0d01d060806001440c608495030f5041103c201d060300e0144000606080d05c00e00440003c6a0561203c158912103e610103402e4a80450030741c600d50749500e40068111030403118042882c1d480180180c40304070441032404054800b03068000903502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 320298884 1250 320297634 320297639
    0xa0b130b0607020127060201020d0b1c0b0406021b0d0e040203091e03040b161101090312050705072706080601270b0603040b060f0a0e180a0503070302030919 69
    0x120311088032425a02400c14103050004410b240c0501791a81c031281e80138155015002580340d0301500600804268980b00317000104c00003042c481ca50759580811074000d40d01c1513085001c603104000c941c0e0014011440540740043e040e4842c40020000390b00450309602160309a00b889600140d420345100d000c0760158a141031208825661350020030400404400c00e1448150303c54040048400404180d01100e4450178006448036405450207000e0b6144c242c03108455400d58841d04e811402c0e2544840680101466854121110b400c002000ca415119010020a0b03d44159800b440c03401c5c00740f40418060409148401c054811580c4503400030f510160042c0420344000c25000700303402c0c3c4800e00d0821200c2c0c131000720016024505070260401400000c4c4002d00c0144103030103126950941d01004141000c00c184560340481c2d11030742c4590003140b80894600d6442c0d084120044498804484c40030781c25440e0142958417018044025920000b03803a422070030070341e8032502a00a6075003510031052 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 320300134 1250 320298884 320298889
    0x60c0f0a2102012a12060905041401090314072307050a080c0901050613030602130f08030705100f06030203060c070b0702030406120b211e16030b060303120a0b130b 72
    0xb003241c0030b5050501018015607504e446803900042040a1040c180002d90ba6642a68018402514141c80e0480b0f242103584044105004e0034914503415a9510808508401002d8141e00050030440c1c00c2d09441c3c10003c1960501d40c0b00040041c00c000140500d68980020001400019800341c074180e04440c00c0100c0c25520880310a044071815225140c0e00c8100300c1d0380074002c016581000f0300051000ca0201c00c49200310700714906441d004220189010303203070a800345d9280034050b8001d1081e8090581000d1541d0341e07822122490040800204100d41c69500103400c00d181201d03020100d034000708a0005200c03501e00300c9d941042c09400610310b00b50030440002d21800301200305080c001e45a501040158a0700d00e60242d1071444c4203c1403926852180c4001d8550926419500c40c03101d40584101c1c10750380224041485065192588148600e10ba40320380c02584000c0c0380e40d6150000b400441542107119829070707c10404130300300003006001581001020300040c0c00300b01c0f1191034250995000d8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 320301384 1250 320300134 320300171
    0x206240d020604031406090c0d0f03032417010c08010602030a050c101e0507030c09090b06043f0c0311030a060e07050a090e0a02060c0f0a210201 64
    0x4802514018030284150000c10520f01c01c9610040c0100451003512541c0040464018000d8a4000582c0d8210030387c041040703001541c0a40c081d200702c20092542d030000f8025030004040640c054214614110701c1c1c0b01c1d9024115142d88203900c50000d03200f0b500c108400038400c01c0401d46060038805415410031100070740c1da02841200c501030144c00034030305c0d500d0b8100304110150114004018002c0500712144502060030f000d190503011410300c4003058096000713028042102100f940c1c0c1d22206440d00c403407000500940b400041c0c112800304004506102507040b1b4130007951825544907204284001d09071229402c603071044050b08081042d80000030032a903a00300480380c0082e16120845100360002e4100030400c02d000b85420b00e050720302403001360045424000c07594101c4d410402d8507510100c0b14195203405407504a1908140107080041c0b9000d0b0150480c0707040c4c1c0049a40d801840a01d842c03825424074400c2d280b80b104401c01c480344500c8011000c400d60300910003886840351f04c1c1d0000121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 320302634 1250 320301384 320301451
    0x118051602150a09200405180c0607030e03030304060b130b06030408070615080601080d2303040f06020f03010e0147030406020301050301060519030602030c0706050f070206 76
    0xc2502c80020a14029540c0c02c00c86525402044020480480c0008041c5200d582030809005504103000502e0118078104020a41d106c0d0001500c52121101c0400200f03500510013142400021904122240c400b00061403045204041c0024080c100f5010404141040c1740d89070051030070700c5e0b02951180c4660040c0d80e0010303401b132009500c0306114030340080a026205000d0300c140c00b1610000988074800500641200c2c40c800a407568038200e103000b00c60084940c00507940719501e810200410300f02c801c0095900a004a14000001c0d101c1e03559582a60301914116242c250701000621480000d4065103006200d8140c0004801d03003d180d01c4904094150402080000c0001440207003002020110fa402e6840526041c0e0b640742c01e14103034009402c2801440d0007503203003490224441c24003400d958034000041181d0b0541a05d035070340711406544003c09800001c10184044c1c8000b40c458000c0d14001e0301d044044080a142c80100240751881c01801c442402440c0142455014040c0080081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 320303884 1250 320302634 320302663
    0x4061d03040b1804050a0f06060e0102070312030b090a02090a0b1c050a02040512010608010b0609090f092b030b0609060708250506100b0a050a1b0b0118051602 70
    0x100c030f80c0c0b091800224000e2004103560014108010003022007500d03400340030b11074a2000200203007500e0341000c64400c005200c401e805640310500a101081012020054034042e6160100c4c030211100f0216194007004c2d43c0e515100f6401083d110f01c140791055956002d0907014481d9030a1421000d180c000c0046145145052941d070b80000c550141204d80440703015201c040d14207420a8070480c01540204180e05c0750001a500c0e0000d43c2e1814079082044500c110390050208043c0e4483d1202d442c036400d0054112030f5144503240b4004588416110071042d2404c0c28019403030450310911000d41594000030010f03110314410400c0140f26036689081d00c1c10240c000c81101d40b16501c90300b404440c450521201024540010501000c001001030907904ca00c101c00326910000e40e440d080103889004414681010440a12070034030002d10034501384420010007480c0a1358600b090715504442c810030380040d41e13042d00c00555040c10703581d80c2c003071031b40c01603e000351110994108807802922024005043e62 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 320305134 1250 320303884 320303887
    0x1080d0f0c03030b0913060b1e090a0e0d03020a171902070203150c09030f010513110f0d080a020f030c0a020114040902130302011209050a120c1a04061d03040b 70
    0x400c1c94425070140c01c01800145c0303040d980707007020801400c41c0320800008580c003070306004109030103003014840c10450180040b035010010394042d0411504003030080c022100a9607030b40c44200750607070401150400404a450046c0e545904182c020801070050400c0d401a801c0842404400715a5103009000030b6055000180c540c40f2900c0005e040004030300e03020034a500c0340300a1205511110b4010940c0141c201c0454000c503400601090070780e02c0880303841f0f11844d0a6410100840c401e00b6000c207400300003c01070401d022a1800203241c503004014299501c02c0013040e8038407210b404001c0311020924400040d41445645015141e031428100c5009042104c120010b401120101064030054611074000b59200c100e4000344409151507071006a000520352a0440400080c610030000c1e42500300b80a08032901903a160b4804000e261041c0104000403503003100f0200704c040b2107040d01c8428040001708181040e00b40a0142c903005182d1304480000c00641ca1a0210004110382c203c0b0114804035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 320306384 1250 320305134 320305157
    0x9050a0312021209030c060108061509070c060c020a031b05030d0e010b15120609010806040308060111070303080105210d080a0908030a0f2004050f0415030f060501080d0f 75
    0x140030b406410003d180c0f0340c00b51001c0c01441c000120240c400b02110701e0464072141e07641d000140d5a04000d8604c0030100712070b10015403660400c0b001e25a44074003d4102000e0206040d80c81e002111010082c110058000c0c201460416a000c0d210040d49600f5141d01040b6001c0c0703131a69500d0703206003c2005503007030381c6d00c00786904404290003408a443c40240301c00c88100d4003560300806a0b02060307012205861040001d0418544408014140e81003000184010340e079960301541e00300d80103040303241070007103c40c8040600301040040c80007452080e9545600d6514042c240240c80c0344400286030007982c8541c1030045e01000103029816401585401c601c142c0303c065020004103800d00b005407040344004100300315299140c00035518161002c1003009002048003803086180c07101c0c4c0e103a980c440020842009503190801c010009440c00800c0054545580300c80881c112401d039004641c1d4040c12810001804000e2048600400c4424050080d404a203400100000c445103020302c180070020351034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 320307634 1250 320306384 320306417
    0x1403060106020c180a15080303090d050f0a08100315060602072426010608090d020c09060d1403040306050412020f0606010c0503132403021602090c0c0703060b090a09050a03 76
    0x104506c0305281721590100e03848804803516907204880b405070910554040d8800b8900c80c0c0304a40100e400350f070100d4240b410001044501c0c0c1c0700a0300c5500100b242000200c04100c0b100003541150b603140c1400103200e803402c8406070411005a0180c8004800301c41d44840c0324401c0725255240c031940d45080d041502c000c1e00c1785103040b41041035218401a685002013406a0829001030080804000b1a00c4684110600301d0780c0d02c89020409401114003004241c850030500c90084d00c19124690f4194803915010280e499074100307a01c01e5400540701c03014032041c80500e41100d030702840a8070140881c64030145070240d84060207000981080902c107401000c0c0001401a2a4171811a01400c200b07150b460b0000e008842c2c064a0300301c00134442420000f2098064402c5038007a00c0d21144075010b0b01c1381d68080006d04080200131191141e010084031140e19014020381d80518403d02001074202d07040b070240b0180590042c0b61034101e900e800a0b44001c04d00000307008240030750500c1d049100c00c520009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 320308884 1250 320307634 320307641
    0x100207140f13020f03010302040b060c12030703180f0317041a0a1107060501210c0e090c0a0605030703140705030f041b0602030d2004060f090e011403060106020c180a 73
    0x40c40500603c003055443d940b2580304000d504a90085400b8002d000581080040c0c610501e521402d069010061514541c0120800b07541d100c3e2150400064460507004000350035501c08000700c0311091174403036400070980c11804404008903d0307404900c03a03107010f6541c0342410f415107494908207a070030000603940380741503042101c081c50207a006903103440c0c540c54451b0161a0a0052041156606003542182d00c0c1c08102d4100040c0c0180c0d628000c18a0200007504012000d8010040c600500c0c09402040d214800c60300300501e030a40d91260703249000034008084428801c02480e05e60365250a01c00700325072000c00c0c3c0c0d4100303901402910303e98903649407003007904811080c5040f420304071460018a094000c00a0301d00341c0482c1d54184070003106020000d000004c0640c00301100c1e80140014070034184580c03a01183e1003580d080180d42551200f4401c3c0902d43c090344150580610102c40c2052800c003841140c7c0100400d00003418642139038400200c0745075400260381e503040304e15400a10480c200c0e42 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 320310134 1250 320308884 320308909
    0x812090607060f0902090108010e212a010b0103060e06130f180b180703080d0f02130501020d020d050d020f070209040f050706080c0306270106050405100207140f 71
    0xb0401034101c0c2e1030095000761558080a0344524001e0000041420041c0103040d0589000400b8092000c0d101401c00b8640c07408840c2040f001c4024442c070000e10510210881886d540c2403003100d0030b4080b480d44642518040ca928504050030074000300b14800401c6080c5070011000c803062407c101c4d0020031100103100d101400906142003901c4420701c01420030007410703a02c1c0961a0340107160765504141000b02c0c0000240c41140d80841c40030004035030b080e0050032207483c405902051008140c00d042c4240d03000861103001f6120b000100f0411980c04002e801e404030018000761500e082c0003200504107010789401800241d800041515110a0110440c2c81c040d0f8001c2c0381124504060410340341000f90500c0c21105840b4590000c81c0090091038198811002012624919650b00040c408509a9007400100d4a00d481000c07041d00340c0404125406803910b43e07122502c403807510f00bc20254010044e00c100954000c41810320410300c10706109800e014003500c02d480203265002c0412076400006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 320311384 1250 320310134 320310143
    0xd050406050f16140705010c05070506070827130903080109050a0605061815070b0415140411040501090209010c0611070210080412050c100e01110c0a0506070201060812090607 77
    0x250035030800c000d05180413803404074076032040f20702d00350701e600054a00c01340e8048041c1c0b06912145040000c1d00c0c00d54020100644107240381c9050008021401003402d140311a402421201ca03040201281407a4005c0c254410b46594107020380c90164801038105c0c103040c0582001e00e03840b100060030070409a00b0000080c40c02401242d40d904210514006403610102e40c00c1c8128142c00c03104400c0034065090703400c0c1035004115060341d03448036661040b91a0b402c01c8014038040d2100c0079088203030100c00035640306600a00c090110701898004010441c2c40503004415417030310600c1407a400d80d901c48068102030790322090010350030303003152040c205600841c00001e5002d40c01c0c42040c004203a01a04c003a00940c45a868004550b0b4260010307540d5001d2500400019880000803420501e41a000234510030000c0000060813803480d0940329265000340c3c49040c255100480c0d0100b009420000f65612401600c020003081d400d040c2a030303031540d003a201404240c0071301207044901c0b940c3c2c0c0b400f00d0300c3c0136610 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 320312634 1250 320311384 320311417
    0xf09040f14070b030117010903021c0e060a03020306121b0609030f03193216020406090e0601051203040506070507080118050d0206071b1106030702030c07080d050406050f 75
    0x4070f102c4561151300034010041d0350b031410170042c94089070500445043e1703940754000d810385254034281c180d0410038101d44082007101301c280c11034203511046c0017841100c0c2d55940241c0d5a152200502024962054088402e40e010341c80d0300b0380850101d01011040d410031252180d071a410800001c0c13800ca11041c005015000009018002500d02c07920b044040a440d141c0344080015032074416003800b0840740c8840038608001d6050b0380900313810b00403d603e0070b41740c104032075410050700440d00320f40f0541c0142c620310b95101d028035115182080040e00512044a514112800400c0c99039142d0065100789405403401282d0002080401e00502014003803080013000044054003907940030000080c1c0a440a0180070301000e141440805c6540c414038007510b8443c0c014040e04d8007013080b41e070000310070344460f030107120490b2490b03890300003d50040c010f44d401140c5540c1076240310b07410101c030303644680350b030f5072000c03260122840c0c002e000d0350200c803003d044c015201e0510f800b6004544c418980d01d035818941c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 320313884 1250 320312634 320312639
    0x24111c030b040c0e0a060f0e01050708070614060f0409050d111005070801061205091c02030d090c03061116020d140303090a030e030706200a1a150f09040f1407 70
    0x14090710181036013104480701d08a150b40c5640613258655020400c000084201a0000719940200010301c4410300c9810154074001c0162240421280640025000d904203401401000d15080318601100030040760308000c40319555444540c1d4000000c1c9600610816556a0105540c2880a08056609060700b44110714103464011b110308002d00800e00401c02c10603540c1ca08401c5407244900c5600300754000c0001d43d8118003c40740b445111040c800441c4810480950303148018010131004510803000c41f14403d04526040c42501c248a000544021040c48804086110400310360402d503015900c20200d10b20a041c01528000e035100c004203280310010600207502400668484c0c8d07540240e1354102d806425034100342e00d41e5024411440060001c00510b110340804841c0d5a411110800444d90060b450382d0340c12800c100d42c40b0719901d04050301c90401400540484c104205100100e07114000c41100308000381a00c0805800601140300030751250080000000d048045082d420341110751090303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 320315134 1250 320313884 320313887
    0x50c13060f02061014010e0a090c030912030b15090a0312120c180302011218121112030f1320011106010302091909020a24111c030b040c 60
    0xca090900e4014420200022403044607601300500341c4444e055105041c6600350011103990b50b0b2108a5036000c4007803140090070340302c58071420000c05005c2c1c402142103a09403c011380c26101d06950a402d042c05d00c0380c9100c003035440d84180d5030007044c1d0100040e100c030b5004012480c4241036800080c00668200c4200b4105500b00c3c0140c1401225048180146001d880702255403030004400c107121290480e03c203100540c05203201c0d4600006103c030014001d81d1103608000122401642500c1711071000e1103504a503907000c1c04070202c0711111001044602080300c8240090702c401061400d400c240c203004a075030649824035010200d9040154542000c0d501c040d524603950b12512424042490039681554140010817440d040380d8000b03010030782d00d66888042030b01c0e024012084015890740c40c4d210000699800005001801c480c500303510040c510b0460034000c0488a0320364009010516103808140b1000117030700e10825000d242001100b114642c0258042d10f29031903219481802c100c822403016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 320316384 1250 320315134 320315147
    0x6030516090f150b0703261b090310111c1d0c0d030c050f0a0b04031407200103060b04093206010305040309030b041a100803030604050c1306 62
    0x15901c62004018865041c0c40d280c1c115031151202c510140c9030802e0400640252202801095000e82403801c0c1c1d146100c240382800110003001601c81c148048103103d1a259942000f0900c0032044c1c5215141c008041e0009988640e202861940c4c81c3d182d81000c91751032044420380c3c40441141000040701c0d480c02070004043c068400841e4562200b8603440d0030403010008104014a102500c0c00403a2016501d0854813030000c3c0360180e036144035042d0f044000d140100142d8481c1d90060780140520b040178a4000c0401491030135034020000b0900c242408a900301d1461403091f16529a14901200d81c2d900580140002d0741c0301200041d00070900043c100201c1d0080100714a8400380c2104008541000100301040328130032000c0b01c0d94900c000b8420b54001d03480141c00c1402030a2004105030340750303148403042d84125070841d020000c444030145950004c04c01c0a030886038410f0200c0e04942041d096581c0c90100030415882541c072503021612711041e0004441400401c0b401c40d03240151a0f20740901403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 320317634 1250 320316384 320316389
    0x1e030204030b0f060f0301150918050307050a120804030e010f02010e12070c290f0702040f0c1e02030706051816080d080f01052403091e070602190606030516 69
    0x4034170600900341145018890500d002d164840464401070400c080c030310042911803a8509100c03c10340c0e81002003207081019241d07481c8910010b10f2600b00310b01d8024a0107a2462042050000002c2480000b0f40c0010003c6110b007820f2a141948110380d00c0104e0241140351425059400303000c03031000001c0007101c02002d034503000c0c11060300710582da91003044c1007804d42c0070b8a25101d0441a400042c00240c1d00082c030103641403094242c00c000f2240c001404440c40503501c1425180d4581280f02c900341c2240380318609800c1c4100420008141071000703034481c13003480b000403e8503581c5c0002400202084010300d405440140880b00e0801400050800440081c014440140700d80003012141038801c0460304d114084210030451280d280030180f007020b03400b004d07140700384580c151015451415000e02035440781000300000c007402559600c07100fa1000311400300013080c4e0030a0005200558001404445501010800e080900998204400200085c4d000101240515940340c80203501486105d000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 320318884 1250 320317634 320317639
    0xe090a0209090309090408071119081603051e0f0703031713051e010b13060906090e0304051212040906170f150a0f02030405100b010207061e030204030b0f06 69
    0xd20748a090b103a5550b406141c100740d6011012000150024000e03c001d050145d109964800829540c180022804000e031039200304400107031007040021070410840911244100c070710340142c45003561a1681c44410615144401c4181b825054810040c104208102c4003001000d640301961640380003865500c002d400045603262500c04562070b020030b4500e117031849501100500542603829030384048407083c4190f402c0155a1850080d025880e54914007190141071070000600a041c21111411a003454022040b914035001c2c01c03c458010020840c0c054920880380d070000303110a404030902d8091a440c100042c410089030004550300f081d00000283c617014180c44503039410542045944060880c10b443e120f0b1701580400c954103c44404850f04010794a1003c20350000c18001002a83d0060310110b900d50f110740c1074070749401c2e4148507454505100744040c1500900e0700c070f0018a421421074071a4003281c5046500d100481c06641141c000755404202c460217481c0c0b01104104212080341c0c00350 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 320320134 1250 320318884 320318899
    0x807020901060215070f2007031e0201120b0301020c03120604060e06060a12150609091409060a05060d1a2512090609051c09051504030f03090e090a02 66
    0x41e040d40045459401c0b02185032400b40c041d5500031048420180d20b86d103040c1402491071a4191000383d8101d4800e9114440c8010f0088a1561070400044080030718220000b0380340100d4900141e91054800f034089400010110b20303d1104400640288130f0401c0b54041e500c000291284a00c000304c1903144542c4044908208a40d51001c80040040085507820ba11003c00c002002c1554012160944a0512110b000070350b0301d681050201c0c0e2401ca5003005001c18440c1c1c400300100ca000b4021200d03960200d9041100500306541c5c02c50f62000060150350519441740001581c544a00360000c4800303030014402216010518041d50901d501500c04400707000c005820445240291a0705107181070b241d0fa00c00d0280c07081002010010404a03e04503074441e1101d4409021610400441c21403401e808038803075262503640c0d00a440c0707182580c040d034081c0c500c429100380844241000d50341100d801c03042c028128015403a04440346503198121040b1a490305046c081c070000c0c0000c214103114400c0e558074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 320321384 1250 320320134 320320139
    0x3120711070b0903070b0a1d060412080703090305060c0c01110906040b0307030b180403120c0e310c080a090302100902011808210c3f180105070b0f0c07050a0807020901 74
    0x11227244202d000b51420404941d802000051181c4000d110342c07400b034900101120380703942c0c03400c1c00c2910646203803003003050200d00000050802c2c822912142e9810007800e20f400d0900c000305071903000b80d2082e00d828900100010b0038060103600814044c2c0e41c01450919070b080b00600f05031840b00b05031401d070300003101c810b860324001280e4419280365054580300c804251501008000c150356501c103e03103410580c140c804045405500045002d044c08002c4040707005022041c1c0241600c5000f45aa0811400c0080d5500802c1e00400c000b001100750407004955403440d030005941369040002c0202c004009018002050325000c64140300b0044e542409a600702c51040c4018003a0280042c900800d80141e603d011818440984050038840c0400c3d2484002c40c240340401040f0f8a003101a02410780009a004061003440d000c0c008614000d007411410310354036407201c0c040307034000409045041543c00045004401c409040c4d0b00301c950301170100d4109610516000174107805c00c490880c06070a154001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 320322634 1250 320321384 320321389
    0x61a030708011401021905071a040f0b030a110d0b01021e1f09050303090d0206060901180c0203090a0603140105041413020f0405010803120711070b0903070b0a1d 71
    0x86038020381496460020503401c0c10f050780300c501800000c03e0305500c1800580600c03d00c08541d503201c8a40100080c0040350b01c0c09460480c04107580e40c02403135101d010801404022055021503040d1800d4a88a030388030351300c0b040d03140000e25441074081c1ca00400441c001d1200d045940102108910030380c02d54142112404050740c045003240061050b070b401c41da09041c0022822601072540700d203440b20109900129031075107420350381b06480c600d0131608051340d01d09015404000058100b14156401c01d80c5600d0210310303004850301100c542c4011603c501c684001c6a1080094840c03480c40109603082c61a61144007034010082c800211800181c40c40001a8528151250030460700928005001c02e5403449517000701c092007554126400b00c16035400e12000d8480c2e10480340602010801035076900483c8901c01840c0800409150810140c0030009158044c049a8007089501c810011a02ca00000c00002d0030495160030940340b0f0400032030481041c82c0d010303079003903103481c2122811060100050705 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 320323741 1107 320322634 320322637
    0xb060906031801061a0a0e0117070f080117151e0f0f0a0603050c10050408010507021e19030c080c01090605092404021909090303061a 59
    0x500030030510007442054041d2040e0024403c030410021000d45e83c61041c01c410000704001c000108032164000d24034214217203c030300010101d80c80c6c01c2c48001c00c41c1c078418400d800020304200c0009000744104190700c243d1150301c4040c080c04c00c0025442c0584450140216200003500305510f04e4031035840d41c075903021702d5046180114904090206c460b81c41d0303001e09070b507404503e071030f2003080018000100300d4550302c2c0c01c2c0c41400c0d100e035807003106585500655000c8800f030f500340420480900c0d4003080ca075021a64042d202098481e000c1030896856004560401168100c82090400b082c021901e9100c0503100380340451924220401d601d003522681e00003207403160b0710785040c001e045209004240f414025120340c40001ea1807155680c1e01c000c8040c1c03019008500f85082201500c40070b0003098043c10b9220018441d4050a190007030040140b03201d45070b91420300a00c07003a0b17030103038000 = true := by decide +kernel

theorem cover : BRFrame.Cov 320143884 320323741 := by
  have h0 := BRFrame.cov_init 320143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 320143884 ≤ n) (h2 : n < 320323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
