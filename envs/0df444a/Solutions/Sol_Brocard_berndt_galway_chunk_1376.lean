-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1376
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:39:32.27635+00:00
-- url     : https://prove2.me/submissions/73cd2db9-d5e1-4837-b14e-a32f80be18ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 247302158 ≤ n < 247482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 247303408 1250 247302158 247302229
    0x9022b18081308100c08060a1d130803040606050a05010203040806040803070c120201060315050f13031b0b0f0108120f030403140403150e0105070504060e030309150403052406 77
    0x2090f0141e4610748582074a0740c996442104990487d0007100c0c00c1c03546910b8100c08101000c600100b2804103a000b01c00125030900303c034202c81c81d8a40000049960b403400c2c0c80e000e0010240c1d80641407143c2c903c2c080c04500342d4800001d4600360b40c40c1c64020203007500e842d100c950060b0401082d00c410010401da5000c0000c07000e500c82007030200180c002081c405d095207015016a41440054000d0a252104000c01d071900039a0f100c2c1c000030800707407400815445003812511052600754520402e003a540744d5608000b11040110312400500c0800748150342c0312034220351944000c02e0051170b8140e040c000042c88115035801550420311078241500ca00442c0d81600d41c942c2c005520170707103003144646170f0704024038420300481c144c2c0040d090007017015140c8800054820300550195a0811818003004409500c0130422980030380e000602c1d07060140700394003144c19942c0c001d010441d6240035019001c03a002c60403c1210390200a4000e800d015903440c074050064a03200c40f080e0001c084034007405254503040a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 247304658 1250 247303408 247303423
    0xc020d05071805010605031303030e0a08031512010203071e09030f06050906130209010b13050a080102030601020f06060a15021c020304050301110f030403110709022b18081308 77
    0x214405202d14220744428408075a0160b1055052150400400c1302c892002080315541e140d050600041e02c0044580c0245014072038540104900d10010074040c05009003034400d4540380007103801e801d0001071916000d091b4001510b82c0408a400c1840309103642c502c42803081c410304032501e001000c0c541c0e00c0c0c40c0e040100c04003d1068940c95900c0c014454260740621000b0b0f030291164000820705590b0342d0114441000512403002c1544005c141d500040381450300c8640100b10041c80c3e5801c954913114054001d44c0192105405031040301c207c00030700080070840d80d1143c4401043c0f59521071400e2130042c42107102e4850311003140a058145400c0a107075501030892100240c0c01152514107210600d03084401c1700302c10500d02ca03400d000e0400d0503000401120791281d45480c0184100350103078034140c42e0a50783d410819400c0e002044142c40c1110b5404021019030041c01e107900b240c14440c0300d40d421182ca00398107903041501280d072780001c101d1340d000608c1100401202c219aa5030348d41e810310f0400c100b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 247305908 1250 247304658 247304669
    0x60b0403020d031e05030402090903030402010c140f1006050306011a031603020c030712301a130203041106070b040f0c05190314150a180c121a09030702010c020d0507 73
    0x106c11f000a5080c041c0016920404a0005525505042d00003030300030301c180000180f04484e406807184400005026501030f0301480c008850007243c404054602070309450003070074001e1042d040002401c9e1003542104030b804040c0180305285440c2c04030b0081261806142c0d07541072680030442800060300c20001020f03201d02840b400e400c00740710507400074140d0000001180d544103109003200182801c1d40000114486030b00300c00180c0103462005030101c5401d58070100d50141c1008509030340d21035660010b600c514852020091495040c000300221030181d0300c009804140d2190000d40012084526400c41034059000407101654620014410750700c04c82c50b0b10707068080c1540c1042040440900e4980000d40d203c0949542042104944a031800080c81d050407a91145544442501c1c1c0c40c0001110640196091010301e80311412607500c3e56001c0c00445000703041017070109059420002890049840340d001c2e5140c8141d0380c00444410603001e4007a41d21809070b0103094000b91080101000924 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 247307158 1250 247305908 247305917
    0x15150b12041a070203220f0602060109110a0801090903090e07020a0302100216120504080102190f0305010602100218030604050c01080114150c0f100b1201060b0403020d031e 76
    0x361a00d41090301d1900300c2c62240079a00d050080c0700c01281c02109646596104200c01c1d04c0340c8005250021800700141c0c0b20320720200041d48049049603010502d1070603a695624240302c03801018115011500ca0078403410f0000c1c040d04014004d21425030840c440c194003902c2c000340c1035900d51105c05c44000d4180c078000b0250340816a5a400c01d13406000300700d1541100780c001c60909501484019200d60035042c014100911242c2038806d550003070341542d000d050720000854486224843c003107404a00d0010020214800414100c403031031182c01054180c600e1540a009159455140240070350400c1c50145100000503501c0101034a081100600c11806040204503020041c0009041610180c00884500c0c0440c01200015281d030104200c11040305007505950341c0f0000d011600704805ca115080c024012080710020992058008000545045840b0203014200c5d0741c04d87e080380c003140301704014101c040c8020005440c00358016000705004c1c3c20038103001a10240350100d203528440508021030f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 247308408 1250 247307158 247307161
    0x809160f050f150306040209060d0501030302011a191a04082d0304060906180e070c02030610140f1f05071208060102102a02030d0b030a15150b12 64
    0x1c0c581914880c0b112801078400800903040401c0091040c03000803d00d07401543c0024945915889190403640469410b080420042d40c4a18000740601000102703602c1e5021020401c601c20703e81080c0700c0d0703030380500c00c412192414501b071356410301c0100e00040121044824400025001c0c0113100f01f901d809481c160203004080f0540548642c0c1d031504455001c2c0380c1c400e010030701c6015008148002500c0303450034174405c1c3d0715102080c41700300c204a800c04622108808140300c60140c00c030441018152085080d03030004c1d56014100e80910035184039004603428040c0106d02c9030b0412049440401001501c5c03004c450744440c00c455000c041101201c03001034400210384d400e020601d070801b803250846d4a400b500506203100001d564102000f1000e5038a680d4040c644098810801868440c01d1400a00c501c500c1200d0300180d121b400942d003071607040341040700c180124a00840d0f1546220b512044501035101b00c6a0356000620382140f41088803100f0550110300212010041c00804ac540c0da4404204d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 247309658 1250 247308408 247308419
    0xc0d0207060605100203090d03080402040f0905011a0306060a181b110f070b1b07050a0b0703020f01060614030405162315090d170f09030d0203040302030d0809160f 72
    0x2050780c44c81c005007150024041c0002582c0c84403807903030603160545001c0d0703d07070b88482c00000c005040c40b0320703038001c031a142c41d0720241004410b421401d610f0503101d5100d241020705000349a1504422154250301018000b014803a03886200c80080311080d4100700011080081c00e011001503421581503000300e100a048600d0842e0104100c00b100a1100c2c06041010300e04039140b08035004001e040b11040d421801e21341d0080104020400c02001c00034103158003079130f45034141d4a8a074092442900103010754030340100941c805010724003ca0b1207650750007040019072154104e5940004d04119030078041c0c0180703604030044490364000542031894810031711941403a550780117000300041c414000c9000d01244900c44110f4425500707a0202600e40d075024038554a082c2001c43d01c0200b0760300c03d400c4089403621303401c26500050180701c5416800c039039041c559114181d1b0f590003188402941988840c05e815241481614100c2c0c12104400854014265000e00d064540e4059046003c099000e028108034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 247310908 1250 247309658 247309669
    0x3090a062a170705150c1803010b1e0118081f05130201030b01020a0501050a050402031e030d020a0e030d020d0207050a0501090e0403090f15080109180201080c0d0207060605 76
    0x640384480c004070216007425a5600300c0c00d4002a038911002c481c042919803c0c00018049440714807810003103040307145000d00c9480703520f400c0011071209030100d071803d5080c54241485003054800c80200303109271079040c014050300b20a40c02c03004d407810001c250055a160804020402000c0e01c1c2c0500581010b982d2116408842c6080343c04038031001d03007070070180224400c2c4c20030352408a075028030307000c03c801c0c20100060349004d0034000010142d40ca42000c124a1034071035405236000b40d100f04c05443e0300e50038500b230031140c0d01e6841c5404800d035001040844034900031503000701304c00003071400c010591000100001303040c44040f90640015810404001024079410300c11540507160031101084250f04040c0000e0080800e4014100c071440c0c0c03900070030141030003414010020100c00688142e0117403103c141a50511240041e031001c14400d10002c40c003941c860290384015442c1051715030752040c61b6001140c414a010b01100c21000b0100310105507000a400209100c500629010030440d191909000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 247312158 1250 247310908 247310957
    0x108010504050d0507030c030f031506020a050d080f0a0e010b040e0604050114100b030406020c030f040602190b0c0304060e010e0c21070e100b07150b0d0506071103090a06 75
    0x301304142009500000780e041040900f0503a05440c010810703684041060b0020310341c0040303100301c0c600640f10005402c2d0740010a49011803080003903900c00000048141c60000d81920340d55461642d040c00240c0300c50311a0300250302140054008640820341d5004182121089010b0007840c1e04828204410300c02c0900560408061100b1744010740c0ca8440c62003609900e141c040c1d4030030702e080040031500b885803540689461015090640340d45602c0c02400340c013075074483d00c40c40001d4081c440d588030b220b43e004a4012012b50b080720b038150f100c0c0d0380e03144440400d0740000d0088808550310880283c417140c0c00d1203415032f01c400020092007050718920420001755480044580690002d030340d0b8544007100481c00500705d0740f044410500b261034491220381446441e81296a60010204485050048030400e007144000b9000040060030300342401c0c8814a4a6210b0250503544030f0f10119215910401d9003000112403501581d0410036844001101580107030302a10008410f20744c800450b82c4000b8400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 247313408 1250 247312158 247312183
    0x51e0c0f030a09031710090c030e070e01030b01081633030209190312050a02122d030403170c1605030417030a0905012610090c051206040203060a03020603010801050405 74
    0x204086c3c60001c40355a03100010b40900c64203a6183d2605502550098009090090180d400d07541c1030383e1a9003110041038001d1205490030b044850000580c1480882d0124001c030141c42002c22180c00c29510040e0071300040403200743c8c81040b90340020241040d085176221040140e401503500c011040401c03000d03030420203000b00403802e156000c00c0000c00c0d140546110083c5410059110002708400380e00f8850b500050000c1c500000a4600450300381584162400d0b80881c2c654040702400401001f0038001101d009001c102d00021018014401e911000d0b4840304803000c3c50b02d0403807843c8004450005a10701207400d035002250503c803404c103d10b0110000e4141310300450510b401400024140125880b03800c0c18001d0000144e030b442c0c8044000703541c070112044510381c0c05d0f040c60405007000000720300c10011103c0c1341021814000b4812401c0300d0510382c811500740b009440e400100f01c02036001400266000c200404000300603200e2802a42c000e11040000140c41d14150910340c0c101a018041d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 247314658 1250 247313408 247313447
    0x606020c063001170105070804020607020d1511040510141b07090507020a050c030c2b050a03050414190306050603161413051e0c0f030a0903 62
    0x90300350a8851005503001050342a0804807510745070108844401e60b0441d00742540d0441c00000310300e0b0090780714040381d841c0044000b001070360b890310300884d41d000c1c8c191070081d80400100560405407800b036a0241201e0701076550044603011080380c006c1203440f20380481d050074030045820021807a00991011100100e800c201403c000361010300311032481110a007080d407a03030700d42510015807003c01c501d01c00f4101c681010041c1c0d082409029542d103c440e8800c544c00e10689030702c040e8a003408509412168409446a2800309020252000008861011882c01c030420320006010903030401010704458043e40320b0b25600c034100b034044001d00c1c1c0940d404030300513844080400181b40400000b4001c0781c0e0410000203558a81d500000c0c04c0c01c1900c1c010103240250000c1c0440c0d424184200204610300440d14041403006403808a81914012a014901040c3c0110560fa0b255001c00c00702e588100d01c1c0800a01d4101d0403a96044160403d413030805420365030700c1703101c400c05402c003410346c801c1940f1008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 247315908 1250 247314658 247314673
    0x310050601080408070c0e0420010c021e01021501120b13032c0406030b060a06030e07150203070609060605090702030c0a110a090204090c0206130302071e0b0310050301060602 77
    0x6420800d010340010301c448000100b17682480300085640000c1c00d81c0c1041c8024a040c58141507001602010b036010944200d00c5084c0c2180d80a03403812030080b64081d0040100103901d864a100c4407034540c0ca0305055005515060340001c011010060217082c81a103d8030080c0c0960074018001540104083c0e519008170383c0000200e0741040d190000c0c82e400d007881040078400701103080403d203004441a80c01900b055804410050b860b0720b4607202d000103540418150360f58081c00c4040c0c544403401c20a00b5000700300b09221814a0a008802500f403a004407031038841c8940d40c22085034510101031f80c9142d0748480900c0ac0d45000780c61150040100e10041d82000d0f004007601d500d90b441d68600038a4503400040c4000c2c643c0300c10f5003c0004001d140400c54071103a4038070840c005001443e0709000103000d90340005241c50301020741621040c1c1c141c0d0051800c0c900b03050452511040701d0600c07542d0900d403003000284403018480107500c01c12035240d02c80b500514003030925081d102c80b43c1002c3d082d03400007070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 247317158 1250 247315908 247315921
    0x19090b070609030504080610080c0114090d03020102091e010f08010b1b0f01150801110c0703031202071202010e10020a05250206071a130f0f0c150905031005 69
    0x40560303042540000300080c551070503140590f41485242e000420034000c4508010000c1340d8021540101c80540d416512a10005001103598013225509808261400d20403000386081103d181b403400d030320900006241c6250200003c4041c013500807a9001c14070300c183d20105035603002280d400310105e01d052044582d414007400740300c28001c008280644403035021100041c54400c110908000a20030002c0061800256846e12844480d0058403455030030072b080a42c1e842c00310000c65108440c8040581507150450758202c442c041040c140c0c801e1180c013401800301050071559043c5244810341c000044441018100a0070b0031b4542c2081c0c0300240c814001d030720b0155000000c0760300c480011094208580105450141645440d2101a41049000c2000743c10841d0300c04410f04c5900000d04004020b84e42d1203c030000c140130409004190350300380f000c2c22000a855020102c80c1078852185181000d4503801009111210340c45000000b84410b4400c010701d08050205c1c050000a001c010300881c0f4001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 247318408 1250 247317158 247317179
    0x506030c0a03061809060e0703050309010f02070504180b0f06010f0e010c1502031801180837180e0f0403050c030d020406090501030203100e100305070b1909 69
    0xd084414041001409110441c800c1d031043c80980301400b140000301d400d00351114001c0104080407111903107810106007203680b00050440449a029006502c2e01c2564001164421503080d0100190702c00c0c540049000da56901404204480d4042040308210081c20105e100000240542c0300c0701600e0420300100e640d0002610111003558141000e40700ea046004803a19a821070010b41608004243d2030202181d580055004000e002c0703400030018a9a81810308a0b00c81020340c50303d403044103291800103545034010709000003103500003420720451501c400f98960922607011441c400032140f41d003545d030340103424040b000420345905820542040c2c165529040c02519481c0d210402c04001800c05106401321209000c0304000e40783c54290211803140607400034010080407680d031500c0400c85502c20301c03d480c441c00c00310503019441071610244082c20500178240100c405224200480450310420884000f040c0c01003906a4070b1812002003180e00c511490a501001842c450400003440340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 247319658 1250 247318408 247318411
    0x6051f03060b0d0f0b060906060c101509092103020c0c060c0102070f0c1401210e0319080f010b070b160201140103210e01020a030e13020301180c0207050603 69
    0x440350000c2c00100c03540c0060022200600000e0501100e8100d800401c0441c50310580a04002d60b0508096140c1c4401c00416000d0076213401c0d042e6000f40c2001407400d00641103a4002c50342c2245665601d0703203406000050b03421620098903215030348203180b503440350300c0d0048110360a024075045040ca04400341c00350b100c0d0100c50701c461103080c0100305130203807280a5040b20b102035400001502003807004e26100740c440d04a882280c5060b40507804021095000c4c070090340051401c02444a5140c01a4614a009000900e141600c1d44011b1200000c0f11041059201203070b0042d40380d091803841d00011600304400e0503041038000340d43c240201000501c01e1b08409070004090004039a091841c03010490060a4907101c4000140300040004103000311068415540240400c0c02e03801701420007015615100403001c401c3c0180d112010000109105001407000f0300320041035580800000c02441050760020f8110003001285060240a10f180a104646240342c950020f04135441c41d103400112603000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 247320908 1250 247319658 247319663
    0x31201240e04020405040203100905070810030f0c0305030d0b0405160918020d0f0b01030c02010c0e10020f060a020406180302030a020616060e030310080105100303051e0a0c06051f03 80
    0x42001c420051a0b8450b010784e8050a000740c801c40d00c80c80c1010345a0110100b071702c608124140b400020903084c6202c5c0950a00c501c0414090794412481d5507101340421107864016542c41e000c07628081700294091004100c140c1d41044086030200910b801c0004844018201010402d400303200c5030609500884800100c07924548180551107135120900040e03c5004c0328502c01614080b00d01741140c900347c1c0420800102a82c0400603204541d0090342201c2428004001007018030a100ce96440c0c40c00e48070030003007010b205030780c40342c0c0d2412112890403405440740001180c0124082c400c980e030200541c0e1110031644d007464000d51542d0040394991141c40e00c068081e48002900410380d8190205148000383d11040400818080010300d5032641c0055508020340b50500e14009401001401010300810000d074210070b65914565050f1a00c0d442803a040e081096281c0c034411400c107145001d08a100e41945a140c4548620303c1c1003000c841005260303514000800c0c556101001c40182d4001c1a0f0341d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 247322158 1250 247320908 247320917
    0x30a110f12090307080a06020307030f090c0902030c28140a08010501051602120705090604020a0e0d02031e0304030c09021213050705030d110106080a0f0b0a14070203120124 76
    0x7560b00e02207801c101c503e8020068600c0754106d000f00300141075004600c00ca1450340c042004c0c801c681c1d20360701036402407030000c0c0085040742ca0600c401c403000d900640c1c0001c0c01244091030102e50f421000005081405902c05d03400c802c0103036091650300301038103c140303100480100e803900d5243e03640540080410301032581008008151000c56882d6540303a07000315a0020f007420b00f040001416280d03110342e41c1c081c06000d4480b400c00315800e81842c1c0283c5041034480d0b210300030140d85005c00d200581d880c0c1c040c00ea07410f12070b08505001412440304030004003010140990303566419424481c0d5140515804000d42070303c1003000c80c002509071207019400502c03061160341107140c207040039842c040c155000644c5c103008074000d0100d17640d00107220003154032105009014259491110944a500400f805084007207403440c142c000580312010305502007505d410024100040d0f01c0f413540840012107810002d0392002400010110b00d0402c1070b40105085800b08000c3c4c5110603400321020000c861810501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 247323408 1250 247322158 247322167
    0xa05060f060f0903010608031e0304080904060b03040b0702031e090307090501060203041809080702060f0d060b0c0c0909032a010f060302090a09020604050d110909030a110f12 77
    0x2903a0304001450005401040503807601092031044030598080c0020710b209620301280010503140102c01c0e9403004402c051040c1000320740d25001c60750f580c0f0003481140c0154040180c1c100c2d990343c512425000e802d050740000e0701ca20f880c3ca44600303400c2000d8180000c0d9401440070080301100700705820a07586504621a0b1501c0b62000440c2c81c00865400c583d07100c9042c100042405540000900212040e000132000d482904004c00d108660458002500e9024208110700260401500502c0344d104120340091501008004400484049411461105100007281d440b2100304022a02d8000d0301101c1c0d41142c2d041c1b140c3c80c55500d1103070000b146030000c50203010080c03041c600118040c6940c1c06400a000d03004000802c40300a00e000d010807842544050b005c5a001203603032044203500c550180106140504003001c1100056a200d003c544a46c4401801500c1d42c80300f041441c0951200d000071070701c500d040c203130103003110448460284450b0300010450600090010780000c00c143c103450843d43c0e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 247324658 1250 247323408 247323421
    0x606010f0c0501050f100f1d25020d030b03010c020607030c0c3008071b020a051c02040e010c17220803010e060603011d0718030503090a050f01080a05 66
    0x1814450311000e070941d440c04d000c00c840071040122203480384501d4000c46036400d84a08803005850880d001703501400c030000c00d049401110140c0c0454200360341e604a80d1701e01c1c05804425140d0088809890016080740a01c10241ca42500840102000440082c000410b107003000940c0d922008206c40f0805494481d2118480d006003010141903401941a40e001103035031708041032202040002000400031210842070284c484d040c114003c01e01030f510b4041840200e08068800700400200b071f41d10009000b00012145c1e03424461089a2a140e242840803100600402007209d80300c810034070480e4117140586082581c040c1c0003011125840421485580f40c040c0c1c0c100c1500a031407000c0c450212034141c44014400018043d5041f00c0d85280c1004299480700288016808207100d5810074101c0c022101c0049100704010aa00011615162410380040c1c43c068241d00604c0c0d0060306e00c0e420001d420f100a04003000c0d1031016100944000781c4042610300020103440e002482c00e0031459032400440c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 247325908 1250 247324658 247324667
    0x40602040b04090501180501050a03080c10020313020102010c020106050315150d0503030a1b0905060a0e100c0209060307030f02060708040504050c0405101707030218040c02030301150801080606010f 87
    0x2414a00301c0e020b881d662181a01c1d070062030207000e500200b401c13000014072928610b000c0c03a8141c520181c1540c140501c0d40d55181c41c950000422011680102d422a090149050ac00b9503c990b0030100100030148031740c00060b08640181070084116418100b090020742c5001131a402d02a0044021621a9407040c0d14444c0c40740c80c620000f0b9200c242062001309100d8000003447c01050040401c020360f400c0c501e19500040c1542c1844030100d03000020170000c030328000000c2d1032440081d0501041502c003e40001c2c00c0c0710790b016030000c0480c21039902602507040000056502c09415402455182e09640398590f0043d03503c04000c3c492100010720030100300860003030301c0c02882c0150050015003000074046000390024001c40c4e02944d4004100c2c1d03500c03842681031110f1020090010401d5488142d8103d010b9405024119401e400116142c44152103520415580d01c241e40e000d180c42c3e5050948082c0c03032008003c9136200b00580342d030041c0203415000c81d61303503041002400d1115103000c034000c094a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 247327158 1250 247325908 247325917
    0x1030207020315100803191b0501091b1d0a0b0319030503161704060213030807050303070801081f021c1418010e03190e030a111009150305040602 64
    0x2d405009401d4400401400c1c50f0450f0301034010102500e80d1541c54180c801e035207000e89011041e83e0440c08441d54900c0d800745400141410413982d26030a0183d281e100c5a0a46e044000c0840c0c0e289040607001c6001c40c07001c902000548040b11705040d56110b0007200c01c1c1100800341c000060a40d645911318890340c0e040244030468088100042290215400c001d402e5070030890b0300540c203a41c56040442154070078200c80c2020016a4a00c91a98440c2d4560fa00250024210781800e5030b05058007002140d0800090103649104800035941c0b4540060010030460040c0d11180566000f4510043c0d000907410440d9600ca00c030600050301c0d070107544401299010090f24403050039140450000d81d1140380250381d071154400e10503e8015032400c1480c0340c01c8440d28125004180c00600c8040c42d8250400103101000d203880c500280c0c0510003800290034442d04003003ca0f03451450030241c684504001240f000c0040030380c1040e0381498a000c0036450300034010f01c8040d08141d662400a010030440f5070584 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 247328408 1250 247327158 247327163
    0x712020f1813061a030d08040c05060706020c010c0e0a0b03070210090503090a0b0a090e2508160509060304031101150b070203010f0b0a0515090315071b110d0201030207 74
    0x802060901064007001c440d581c01040d28003604090000e007094880138000800c105010f00103081d082500c4d1001c480c00b040280040700d44807140c00000945035a48c00c080d242c0d0500a2340c005036128044c0e001c55085a55001b145010702060540c19021a500d00448400b103800010030981e503540c07400c808900349060f01801d40005840e00035142e0034480000060a06a1400d4450b01d03d0143c480b4542040c034000c01c3c44110000d00c0e00c603c10b10050444072750560300300c8880038240310600d11200c3c0203005034a80c00890030025104000700501400c01c034010304000c00050070454580f43c00c4070003003101480300801c0034041c03111076210b40d041000c0950020500d070307501d1009984074a44401c04824942c0c42039606030300c203600381199400241080d01c20400c07140001000c11130380c0b0703142c642404404200011103414040041c032508106403024040039514000340501090f240c40d0501c2c0281502c5a000003140303c5003014030380040001d03040010005860b80c11100c8140c501610b1004070064880c0d603400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 247329658 1250 247328408 247328449
    0x140d1b031103100605030304090b030a0204020a05090910031208070c141b0405010f03240f05064b0d080904060501050f030609070318050c09090712020f 67
    0x2400748182440310500c0303084094a1042441a48250a0382c0b00e5014559058004110401802009500803515210043d065803c00c0f1100d8000031704a070401c002100c00304900217000071503031400001c156804241c2041c5000e80754110341300c10000403101008082400f07222000320341850300035195541c1003644090300b0b9021025410106480e41010f95010f003003842e40d00314502c9203240038007030710341a80c514801d111030040c515250f03620f04603c05000c8041c15007141000f0241c0c0051801820020300c00d40c180481d550924005014200114001680c3e00d0400c69000c02641e200d0341c01d200780c40e09030002899040c03c2ca20031085505150000780b0135800810800c00f001000201409892240001c5404211007552040152000c2c81501c5d45c0b000303162400c00026400c1d03e00202e072071750000118500010180c00d110702c3d83e83e5803090b00b8400c1d52964805850701600340342100c80c0680c4101500d01a0000c14600800454020b905901c0207102c2c0c21000400ca4264403202c2c511305400d00701041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 247330908 1250 247329658 247329713
    0x7080f030c2b06150c080a05090a08030901080c0f0d050403030b03010c08040c0e0c03041e0f060203060907030b0627041b09060f17100902041518140d 66
    0x85190710b00c0400c1502d03001450034038100240c0c5110004090b039850394162607501702c2c9051650b510100b6809001d525052000c188000340341a29114480001380c1b1003032005598030004de00014020800042510300100c000308540d255181c03281e03080e0380c4c50312030980c4042500c2d1114901600a40a03100e140c0d50903601e00a05a02e507194042e18042c0694001d00140310b00310340300d2100019002e0100c07520315581c02e0070004100000c44e5004d0000d0108090f9102c500340c85c01507a00c2840c1c0041e0b4420699601da004000c1c498a8030340700703604c0d5800110f5800e0421988101c000810102d00610000e1007074003038000c581d07500040c15000210544000180200440141c803003180110000d0901e4000014148841c04200725005411080c0305400c15121043c00c0c440700c07030820703101d034070001d00801c01400144000120001940080c0000d095405121041c54480d010300901800d0040782524040c0c0e541d0704100044450a510010700103030a0b205606904014140103105100c000000c0d85811186003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 247332158 1250 247330908 247330957
    0x605060d090627110901060c030507030c0503040b0304030e01023f120f0a0905060a0914010e0f0c010314161815110f0d05031305070b0406021207080f030c 68
    0x400100b243e80c8030701401d078000d2110300c050200c1000c0c01d000c1e0700041400c1007030901c003081c064009009958824501640c0300741d0165640760440c2c110f03900c03884c0000004401e020030550490100382c5504404c0c0300a03c0d618400d04100f00000e40603078907040d0101d901040387c2101415441a01d11140038014580f40d035800c480300380300051141110701132951040c400216981000c00e000301c0500c1c5400c80002c0450b41c440100d000002c0001880888002c80d01d498001640c090a0044d03509003450308000d044c01403503100c0c1860421203a1a1b10314105840c1010421508801902007a001402c0b00314406100e00144800d95100b443c0003100e24528a6056000985207060031044d40c16a103d80d40d0b40032041207250342295074140808107070b05690403100500e0420343c480c101565000b10840c00d00c10000c11075844190130040c55401c22911148000b806215443e01003150594050511182e1032a02c1059261041e044c01400314002c03550754008081b600e0156a8000e43e0701120ba1200144164400d26 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 247333408 1250 247332158 247332221
    0x20111010e010204031b08300702030607080603122106030313080d03060f031a0603280b0f0912070204110a020c1905061b030408160602010f0605060d0906 68
    0x1908a1880f0484403034011030348a0020841305104084c1d80d4081d904500c0c0c0c840e60112141c0040c02c9048c0e8040140001c0002da981004824000c803010348405845040480c01d140c14441903420a8000b200c00f0050280544110509410ba00c4c885110720b150a450756000079003117104401c900036081c01640400318206501003074110403240c15840c100006c0e035458900d904400000d100103405540684140c0c0107500045c00c40c4c3d64450801001d40703d608c00303a120b22202088280443c20b080c101c1c0321440c0000c00c8514000305810019100c0508542d20f0100c012aa82d58441c00340f810303006d040411481e045459541100782d207242501c00c0203403118080c5200a68a9010240c06880b486060042954121484507005c09941e0302510381450848200c0703251920050070079800c18075200800000500c80b4060010381540d03458000c3e42c400d41881c08030000d0940b2540f20700d0440091408104001a6480a0450700096a0003001040c40445030401c0c40080c4050301d6801c2c1e40001e200d143d07070080c441a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 247334658 1250 247333408 247333433
    0x201120b0d0b01080105010509060a050907090b0426150714070b01091424040b120a050f25030b04030c05151f0b040302010e150a03020d0b030118020111010e01020403 73
    0x1134000c00c2940e03641d804004031000c080e02c100f500201d500c2c038140b01505010000503030141d00c2d400c5c020141d07542c1344c00801d1290311035444443d140b2011040f001032440c40912106100054070004d112039041c150aa045400000d400c0c082804858041400c840180100b56801c864010894500541c2d6074100302010b400c02901c414460440000064154902c000c0b10241c6c150012074003d00850340c000030301005240b6254040d510800da079190305881c04042041c681d0440c400d0001e045589180c0c08842d103401c0301c42c0c0c010310500304030b0101030301c22800044ac003c1c1120382041c1520429180d07400c00350f51001004c030300580b0758010030750100302c42c0e81e08d07801039409401103c2007007041c504444206040c194190003482801042000104095132040e2491908540000c2c200c41105024445a80c10380d44606202d801298010170b00c8800b410281c400c8220344e0100790002e01417002c0c0500b644148080c03052009041c4042c207400114046c1c4254000c00fa80e04d203c1008640d980d84a0411407441c115 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 247335908 1250 247334658 247334669
    0x703030b060c060c03131713120b040f0303240311030d1d0103110d0506090a050906040f4103040f0303030b060f04171011070201120b0d0b01 62
    0x20080c21940d9801c22a040312102c000c0d02c0090306980c1c50b0640030290b80d80c8080d11250304510803d0201000c61104e031146114894030b800c0c3d540e614081c2e081d081c29241c42e154001344003034210a0a00e030204441c044a6a40581c0c080183d0400580c0d620b01500289108014200402d15900c005111588054104000d490181e44840d0281281c4810196075041c101164030000700d003a41d240074000c40e8044088a02041410041010f83d420740c980710958011090012425844006100b441d09114103456003105250005110342d01c3c20f00500c1ea911803000d80010030181d54250310000b4842d40c00c0c0d4190715450710f40b070141e4070303604290b10400c0c1d00c1c41011058035948000940303c000d600ca002085504480905200c41110352440d1800c0d0001c01c4616100c640260040000d032107461250030003030018104000d0b0301c0100550081e1818074100b1600c000d020b440e0b26002114954070b8105007076070000303a030910b8003000080b0b10f0702c04807010304081d07480076401c0007201030301008121600340710300e040e641c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 247337158 1250 247335908 247335911
    0x70306022101080d020c120d0e03030d0507020706080601020d080708150405010801140604061505070503120a050a1802010905120703050114090d02070501050316030b0d12110304050906090403110a030203070303 92
    0x410403410040d0500c450b2a0035203e80e0301c40c0d141c0c035030307214009c180d02e8002d2080281503c2c10558041100c00a541c0308030f07030140040c2c001a00500049811280240d001202880100011001c0c8078018041daa009443d400611401000040c0032a5035040a40181000608103110b1543d440c05000d0283c8404005014401e510000041c8039042c203114080448030441c024141c4030f5941801620709a11150f01650907000410148130460780c0d1800a0340078904107180058245442d056605c100d80c101000b8104600f1001800c4c009070380e001d803810081d01e40032070351503040500010181e85002884e5000034500e5007010b40d81921003040c210028400c01e6084113480c101807818000300d07214070450250501082c070500101e44401419901d0051502c420704000800c0402a0006030f150b1075506400c0b40d0a100b000c10704540c2031703401000410041c408000442c1401c1c180b42c00140f1340500141114011058840080c040c180700d40201c503083c84580c02941c0094a0504000b034a03540301d00320903070110f03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 247338408 1250 247337158 247337173
    0xc3702010608011103040c09020a110313030b071805040b0f0909033114060702030a0b07111501050f1906030603020a0b0c030703030c2a1b0602070306022101080d02 72
    0x3118040840f0301c06e5910402924025081c8010000250041d58814040100064292131000790410040240615502c450b002507403035441c1ca800843d2004155000b0051503014030040e1405c540100000d455046801141495180001c2900c1c4a400d4142980c8075059500340039454801200a020500301c2c400900704100440050f0400c6040f503041c0e25050200082080050140c684050141c110b0b000f054907142a072035400091401e40c40606c01c3da40c0769004400d020819401481901a0060001c05403c0c2c1241c2c04040c450035070414410140105603031405a4070341e030344490b80c4030707290500b1075500000f054669074004c2c01812240000c90152034070400c007145032404502070340d80c00a1800c0083d80f030000d007550201c0103819011480780900680380c015004805046a05010003911010900200b110605290680440e40c0985000480f00c0e00001e0001540c08521756041e6a000007000d07a403030640042000c1e443e03540e0101103401413541400402c0c060b9001c914882c050115a0031203403071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 247339658 1250 247338408 247338431
    0x71b060b0415030c121a0108060610090821040b0c100e0703020a03080715060927080301030b090f0a080405040b03150118020c0109060b030706080c370201060801 71
    0x31080c00b015040c039684c1c1e030080001c00800340851418503c2a02e074a5441c0c4145865000914420381044540f60044001c101c2076050441906548403070901e000b105007842e010300035460301120302240c021020501004901c92000c50100c50041c074160b020a980e90000b00395460300e42c2c0e42c00305242d110f09d0600d0a0445602c10019807082900d800030400243c0d185107079110072581d48186000c440c41c1c0c0c5c490041c800c903101d0500c90f076001000d200701c002c50052640b0b524104c440c0303104800030380301010441903200402c080d4400d49040d03035071241c0c18004607218031a20928011050000a08500c01c43d144202041458405042100c81c01c0e1000e100701c103640c000f09620740004066124100c0246001000200a066180ca21215048000605d04195204070500b0740340e010500707590305501c86003c81c81034101013103254024a12031500c0e41c03086c10311410443d003610840720314401050007004415008045003280004821518501b5601c10842507008ae01810b02403007841f285500e0946003481 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 247340908 1250 247339658 247339691
    0x20f0604030f0c111008061201060f06050a0c1704050a080f1209010315030b0906070f1d0a08060702071e06020304150c080304150b01050918071b060b04 67
    0x5180e0544410300b01c00001c500840b44100c030351a003941d902c11260360b511003603100d150701c50100440c5540c2d60001032901d40706105001c20340c0c000f2101103a01d00882080100728901410b03043d28128a08907595028051044030010520800035110028181080c1d010030070140040080b1401501e034648a82d40d030307180103919071043c50b4542986411640d0000e114802200080c9814032301410009100e04000c0c83c0a5101055030f00203c1d512080e0f801840805901042b086510460300c0ca01407041e802e074104024492010340b501290348801040d0a1501303641c40324684809080c060741210030354685000000d65400c0144110707004a142e14140f00314400f6100101d04c1a1901d50300150f1034545003501058100712817004103010480d01c0301010780020710307c0c0001c40c0a140604801114441101020340449070b41c17403819410f03c41c1c01c004003000760b219800d5038141d1403032001900c032403680c0e0003400b9a08490040c24000c01c92844040440c1040410303841211030b2038051720200100860480d2040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 247342158 1250 247340908 247340911
    0x70b0709050915010216140406050603040f030309050712030309021003050c1209010b060705030a02060106020d09030209130204020c070e010e010f0b0307030209060d0f0f0504120e010c0507120201020f06 89
    0x150800c0c120302c0051002c006084240840707007418811942c0d0409010f0300c2100340718042e00402d40360207001861400610340f501540f4050103048801510b181800c1d903402c0c406064001000301403540b07400c0c00d0811700c00103000c08401481103030203446030301045180090007080300100407489511040e640c0007449110344540340c403400344840c2d524609100c0006629001d40000d042c0105503481d0b840069064807048050030341c69100d44000c54864164006c042c0c20010142c029800b1036001d201c050041030342c00807140040b03d03019900c403021501d440401c2c3c031340408584c40294016000040020364540009900d1044584e100d0000d81183d0b2101042c190b43d007000c0c480c100f0b9950400c0d105200101a0400468100304c3c1410010720344074039400441c000340c114842c000c08003a980c49a200c004459809120300003280c030300080040d0310b091307a164a04800031210010800c0416030a8038141c1c0d01528295410700e40010441e0252562401c8908020302b403180c089005014500411000c2d103000034070276 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 247343408 1250 247342158 247342169
    0x9020102060c070f0203010603080c0709050f0601030c020307061104091404080a03022d040f050303030402030a03050a03200304050106080313060e060405060c0706080c130909020103060e0c070b0709 87
    0x78a85a01d9a000840c0b0540040c00b05032800c102001c0180c00681e0244202402180b180400e1a11810b54208040c2041199440500d12506000c02c01c1018101070402560194003400d000852520448080303141d0b004000c00107145920700208924092002c0340a4001c40700040300601402d103d10303103228848170f4143c500800c3c8120a011043c0105d0180d00900f40d0341403208001010204104064104200d0f207031400041f41100080c1880413140c0803000030042c2405400540ca9401c003075020980d41d165031400a001c105000c205107101c01d21941100c00654150100c11002c4468000803e8041d0300540702120190f10b042c10000701c0703c001000741c800140e1044020000c140c540309040e01c4060035003912690146003044042195681c00028041030b06850740284403036403c0c5040607241c10720203031010340354050901240022031413090580c02034450741c81d4085010768a03072005a015120680041c0384404c0e00b2402c01000c24035a03070261640d00d0080c5500c100340d03201c4004c1590411400c1c0180e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 247344658 1250 247343408 247343413
    0x1091104060e060904080909040b0402130903200106050a06111009020a0e0601020a080a170603070b0a030216050a08030405071406040608070e03010c26280f05161209020102 76
    0x42c42858035206195001b40202c003804e181045604c00155158000c480445100d48a00107000c25410301f0505800442c00c206800c00c80011251409401503800940c091421f40005290100000e429006a1b005101c0035010b05150b0b600c940c0c1c041c0094045081c680540c0c03140c450114501c1c920303800b070f5039980c940140641310f0690520201c00b8481a000b0140390552245c10014000070b00030100806440c0100d07603451050182c013450110544901800807446684408003d02890a041003121a10074503403c0040e65021060b1085254001c0b4030006400c40c0518034004c414010007100461041c0d105001380d52689031035190310340c0f41ca1600c1609a070840c0080c4001d110072409078001035080724803030820546141900c00020700b5281c41c4004140050341c08601625641c5d845800720307100d101c2035189458203107401001e002e4032400c40d200398001e656241482c01034042e999806036030114810701052200d442e01c10744104c08914840232200015810890f032a0300c0fa0318034402c00309540c3c6e05a01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 247345908 1250 247344658 247344661
    0x1e03050d0f03051b030c18190315060b0307050705070506162f0108060121020a0e1c030c081b01020307080112050606150f03010f03030201050603190f06020706020c01091104060e 78
    0x25901b00300c1d08003030a000d1048102ea8010704807503444040020214241e91a000621030841c942072000100c0c1000b5440c465083c034070280021065201600d601119514140b900c6122500b00340b49010a183e01c01138110724001b52a140201c0b10000102c09107010f44200703807027482082c103c010b203441040348642c640060504039007a15846003080300d0b00404145408005000401410385001c03200c1c1c0b0451107042d50000d10014000e8103c07000801d03402e800c94040c1259089072418111440c20580010104100b101c2c0b40380400544005403540e594402d210340050210340b9a00714001d40c000c7d180c81d03020400c144000a01385203250045000301c0c0c1d0003030180045403039060078030008000c1080040e90a1801b8000020494042000340d802801d800051807003a603d1030401908454001d0f01c080d020b5003008240c6500c0844c0c42081000e25607010881805803009800c1c40002401808070052201d400000c0f040d101820540003002910b0044010141c2080e0150400c02111018031401502000150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 247347158 1250 247345908 247345921
    0x5060a060908061314060711100605060706090f050f0c0406120312320f01050904170d0209090a0b1003020a020705011103040504051303030e010b0603011e03050d0f03051b03 76
    0x15444003180d10a10001070b0740f03d02038817118208031080b541d01001851103004610189401c000d02010346040c02d80402806040001042044c0b041c01405051306484031820382c1000404501d80c02c00a41040585100f02d8100c4045c0741c030341300c6a450380c510403401e20780c01240c0b009814080541d0940d068650310200c1508124410180c00000c1c0c0007010031b03001d100c2e411805c0e0092000c20301040f681e403000c26154a00803020001065040e08581d01806031041040300089910051414601030111680d49440110010401038440d03190101d4004011200740a20421150030198180f5403c80c0c0d004012a00014124200e0050031151310040e48849820002940171744211a07941d60084141c03407401c0d4661000ca015640f0030313181d003181c0910041803102415810f110308001c44192030024004d00c1201e00018105002c18041d450030040340300c85200c2524050441e400082d40e009040da1030100e107250010301081442c80c20072000c2420300001640750080d009180c115810482031060954842c079 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 247348408 1250 247347158 247347181
    0x4030518090106121526011404390e0106020f0d08071407021002160f060c02011209060905030a020c09040f03050304020111010612060c030903090506090a0b0d05060a06090806 77
    0x321862a030070030403000c00c000b40b0b004414469400c4c1c001b000b0482d042070303408072401c40c0d030b05c0e018004c507091424040c00300040c403496a8a08452076202460340c2c559845500c0740c41070092405900d07412000d041c1c0051200b1891207034030304039801343d000d80d0450b0740c00982c2280c4070075a101e01a000500010005500f80e0300a0091380c801d1031071004014104299035000c110b2284680200c031015a21a42000d411494180b072018060a250002002c1d258a0f0480c09442d03900000b0b00241408588a0241c4c0302c0752480d482388a0040d0080c1050240780c1e5a030404030b44a030711005a000044c0100c090089082c24641084e6000e258082603076a400c5000341c0b03080f03480e90400351080781044490001155514030900549d030103460312440020403540d01d071610340110380d03403130094009040c00c040f0f480303011a411070f0b10403046071130603951281cad1441c41c0d04c0000c15400d0141c016180780e034004607000410080943c4024819501598001512030302c4610540f0002e243d0b200fa44101da1001e800110040c108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 247349658 1250 247348408 247348421
    0x3121f0306020d0e010c0c0b0103060c1101151a0c1905030906030a0e0c010314070f030f110301050a05030616050a020304050406080d1710170c03060403051809010612 73
    0x5010591404580300c1c0e0760641030741d00448803a002603459000010340880203100700e10f03c411180c240382210250b50795038001c000758144809840c050340c80403a021902d0003115403940c0098558000c1200e00705017030003000c503444a4090b003805071503100080c000608188040b1490490400010102e000c10a071256080200d1440b04890b940400d0207020780e2901c410001d0750040c407601401142c80144032000f5441c0170b200d548980d040604019441d02140c00d80d402040c2c10580300d1622050a54880200340c0240105250100c180c0f403828000d0300140380d0840103141698000c0380d609030f11075521800c15030b03281c3c002c1c0c54182030030340100d4071080d5581c00340c401852513242c6401500e040590f140006412950070754845ca440340c05c2900d078401e5069124401e6240c40c00c8241220f515800c005201c041e404489008600008208010441c0e000d40100000c06042500a0844507503190516005020b50404248604400b12215460b2079a01c0c26410490507100d40c0c1c0e45000004401c0910705e000f4241 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 247350908 1250 247349658 247349701
    0xb01120b06060a0203041a120414060c03060f010c2f010806100215040f0b0103080417010c1e02070b180a090c0518180114010e090103081e040b22080312 67
    0x10802248e10710100302c14074903100ba4010790b02000550911445a824080000d1000301c401703c0400801c40b4940e070740b4400c8044d148080c13030324805003c240d1801591300406041c20410005001014052070304c51041564031451003030303a4142c2c0e01c0c0c80710002d100c408501d83c1d541401581040141d504004101211958424001c4038a6000300c40c450b215010083d50a0b0015a41c0040009041c0020250a65540c2c1072044140c020485032449410080c6140306050350198088011010700390140c2c420415070001d007a98404055640e61b1032080e03042c0c2d003080e0503c1c0b54041e4400f5403000680030880e101c0c50072601843c0e160240380031141e0100c000d07803401c01c140c07441d8000e55440d1801c071072000f030324609030103060400d440300104030010380050f0101070030f8030f04540308610310700061001071003c0f0181c54420a00251041d00b101540d07801070f01500458006064100c40841c0d039060700070720102444203603440c0c0000b100200b5101c455164480c0705d01e00c0f10410480e10107000c50314614400c05000b803a1803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 247352158 1250 247350908 247350959
    0x10812160b06150409270c050f01030902060c0606010e0618011b060f050105040506040e100e072403051005012012070305180406050d08090307030b01120b06060a020304 74
    0x1c12000d49203541017504110f07a425034402c120003600015061300101103210003d814100e50140c2c1e5400350384030481c00340078014840c024021030300c1d9020740c000340c0103290300030a510b03200d442c0c01c40700c1a80c078a011500503000900560440c566070a010b01165100381105030102c4503806500015140f00010400c5c03d001c4103000da041001007156171252410011000c070002c00d2551424040105944e0051700c821f205529280100008080000c0c00440c3c8440400020480000340c00044e414075102d6400b1840c4180e007008400d00c0f0842020503400c810603d514200b040f0f4864501007944840c15000e06404180c50300d00407071b13800c00c0322111402d000214204032840e030740d181d420100603504020402c402203180486c020008810081c00c0306c0d020300b81500c04001e102d18000000c0c00504c01d0302406800703201c0014031b014190b181441120003942d08086003008550b50354000c01c2016141d210240c8100b02c0e05004140e080c500101100c0c002c0b0540d83c0103606060038041c807901c500c540c0d14170485060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 247353408 1250 247352158 247352179
    0x308121f060c08070b240109140114091009031703040c0314011e0e010e010c0807050d020f12040308090609070b0a09081209090f0403091401030e0f06010812160b06 72
    0x10340c031120030a1082c9140b000385104444225060001d001e0f00709400d07814044088c42c144203e41ca81c1d400c1d14075140091030050300c01ca00e48000941e01d40f00e80c140301c50700910403801c00400107400c0310f043c3d000c4901c2000350394208040381c0781c8040e890005031401408000722a80030000b290785000c03100c003501c0c8440000910310440041003409199040440b0f001503458a0355516046002e12802c1000d150aa000303000c440a4598010440680280314038103014000c43c00700002c40e901d5054815110403c02940c5d03840b43d03032100d04889440b085408a00003118103000640912000c2080390240300c01500030019541481c3d4042000e4000120007010000c0c610340000b4000c008102031344900c4801700b240e40d80ca059031010b02069107402040c6502404030323a03040c400003039804503038402110f040700c080020915002c401200070b00240c8103202c82c80c1c07040302c074030050303280002c21003604950445040350846103840b00c4c0f0420300d0140600b07030fa900442087c12100860744c000c080f00d0303010000404801c080c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 247354658 1250 247353408 247353413
    0x4091d01050406200f09040908160602090405011203020a0308070e04090b090f120f0a030f0c0e0a091a040203041106030408030405060705070f030c0510060308121f060c0807 76
    0xc55204440c1642c1450301d65604c074002004211580000031038a60125141c1400e01031910254821481003038051070740e0f080100d043c0030080342980d00009101c03c01816071a41800e214001e50401965644501d00d080300021b0b401011180c0c201e1103d605401612400025880966102c900240008103001c58040c414025541d0351050800c0c1500c507029a0109040c0303c04198035020304121551401d510010748081e50340042c03403d0743c0b100c100c40f600250341d4009100c2d088000e00840156800c007035080200d1510000e0b040100d6880d003c1c07058800b0f0980d140d030358402c0d40654186000b1040800c0c0c000440d44003c0c20b00781c0041d90320500490340e44140b040442d02140445e4001c4405a6003044e012086c4810001c0078440d44d508000c1030f18000e401c12020351226881700301036240050505c040318509108000080c0059030720340080100400c0025030700d09050725903a0012200080c00382501c1e00040241a030200b201191403002c445000d2018203001c001d903005a4105800c5d0b03507024023800709000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 247355908 1250 247354658 247354661
    0xe010302041d01170d1b02031e0a0201120b0f010e060c0a050f011407050306040c0e04060801020a110607090b03100b030a0603060e0c06030a18060c05040e0f0c04091d01 74
    0x50304142c0c02d81d090860340c90711504241c1a5201d03000e0280c1c41c0c0001400d1841c003940460510380c440b80b065460002c0c00c5180c07002a181140c4541405804000b2050741c00f003ca0011075041c2c0c52900030380b09e986250320301aa4080c1181d040c400340d80c0c3d0015000e698242a5481001405003910018042d80c2c0381880d04410b15240c6018900c1c21500c990085400660301002805243c041422100008806040980000d02240402444540555a60903d04004074440c0454009015020300204102500c0300244c81c040c1d84454040d1020821170441c00500c0f07039000601c140b24030303410796525490908183c007400541d8000b8001074403c000080020038903a980400a500401802c6800526035103540340443c16196603110003d00d5130032100d8040b28940310780b42201e60100030080e002a1103428424206164031001c44080e140781c0c6001c05a09580d6000710052055401b08041804646d50b0140b0040c1303119001c5580580c04107041c0420061940c0c0c0d9007103588032a0340904c042c40c070110030064590 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 247357158 1250 247355908 247355939
    0xc1106011401110a0b0103110103150b0a1706061803070e070e10020318090720100e1606080a02120f0421170907050607031206050a03120e01030204 65
    0x742424400c2801c1c0741503800503000482020078401070a00c0044907102e0a002d41d40510003e8089818070f03903083e0310390384694480c52030703404420444030b0b209488404143e426048080041d0100c0c0c80c500403420880030b01038003140305841c001c0400c1d00d090503040f079030082503d51101d1a600741c8a449800301c1c00f4128258206d110b0340c640e40e104210a4800740c02c02c1000c10035201c0400c10740d0010800c688820300c0041c1c80c1d8a04500076542030030243c80700c0000f1034041c8070340261000000c04100074000140720200e070051203e03441d100305114940180108035260b66401550305801101d110081102c0c0d4000d125250b03000006540040c105004078119020350841250010308081c042c0c400c11081000880c1c1220070030211007941030b585241c4a4018181034070400c03951551244540001d039540c0000c108200c080c00340a0440c0d61148414500a05014550301100f4445414100f01050b94101074080008480c0c00c0604101500d4a4903400e440d40402e84407a20b0415400700008140151281c030f881 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 247358408 1250 247357158 247357169
    0x705120c0f0f0a020313140f041a0a090e0d110706080403181412010510180b061b0d0c02010507060506040608010c0f030609090b1801020706140103150608060a0c110601 74
    0x440d9908140220780b5000e02894100d503001303042d402e5202e6642d40b0748e1803000c03203256010788000602691050440b1031000224210719031101c1c06200c08955035140e9040403000789018412501c001c060300000f59440c0e0044540c840e02c540c0469801c010062203109680c2e0014000d05107920400d8103070380e00368403c0307a198010600380c4001c0e60407460303181012102c82c1105e00a0a000b0012070600c0c2032440f0140c540d0344111041c50880441080b00e03810294000200028020441580c650841c038054000300c030105600b507074a00a1030840c1e46202d0090880394200ba505a542c03a01d4062030395101d200500001d00055040791351000041401c1c907013440b40d0010000d00b0f8032440300f90842480d00600380c40d4a03810110806040c18400d100050581401d83c0d00503144410300d69500c0d0b10b24448500900416201400a5080071100990034900801041c140d074014440e501d46ca1002403000e8040d43d003284180d0750243d02030300004030054080d6100c0074070301c1003e2402c2e50024410031803140c6425000c0c0c002c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 247359658 1250 247358408 247358413
    0x1003120503010e0a111813050f04020901060504030b180a14030c250e07020a06061d0702010207030f1805040501230d080d090c05060c07060201050705120c0f0f0a02 72
    0x60000103c0c060f2055840104200c0503c51601c5045080e0902e01612150320711020300c0c11000006555106134200700344070181e0b01041030f031529642018442e407003a00c0581c00b440f2490000b0503028130031000c8405880d0866240c1b90203885450496000e0b0683e116442c81c68002e5400e1200060301d525210740184140c0e00003140c8451007c007201c1c5c03c142c00841e52441c07031030216000c4110b044044007010200c0300b68490410040e90358400503402c205500000508507032400d180480c441c4c80002034820180c0f1107210000f2951385580b8240d00301d11170f41ca00a000f050801d040c1964061090521520344048a00b10540e0a0341e141c02103401e8510030381209044c0d03e50410140440082c01881e00f003400403c481b5140602c1c40e0b51103094a070f100380000184056100c001075418030010106140c02000c01405c665902c103416078032592a51010b000d03a900650800703000c2100390344100256410000c02d920f54031a9500e411030b08a0855000112150090350b0600102818402001c06050468280e030003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 247360908 1250 247359658 247359661
    0x6030f07020d110a02150405060409060f0504090b1f091107140a0c03030f02011e050a05070e0f0d02130c0c140706050d0c0c0803130c17030306091003120503 69
    0x1020381804482c1080b1070410203100c0d00e40c2d0104800181c000c0c2159015183d90701c08609003500c40c205442070360400d542003403000900003680d03400b40d40618201d0b140600f210b00340d1600e8008001c15180160300180000701d41d81d000c41c1c078068170315041d01d8100c1c1610b211a01c099030780f82040d505490a604444614110104d0900701b4802042c402150300c1000201802c03103150310ba903604140030040e00015041020191070214018002d522500721100d50740021825101882400c2e405020101e540700a90380c280b02c0405d8445014060a0107064002400c40310160303048414000c0041c0d550005983c09903840b415514602680d10410300d178040701c0d82e148034405082d401d01800c0400c45001401903a44810f40400c1116440001c0d20078080c400f8001040c01003500070100c03503a22004030054010100041132002d030708442080c2041c200d20400102c01720701d0383c035030707602c0542e0f0075001c2d0841c901d410800c0062280d00c2d044000c10f5000350004070840045440e41c5401040031042c2c6a80c1012400000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 247362158 1250 247360908 247360921
    0x5130203060108070503120a03090b0a090302151501110c0d050309030d080915060d05070b04060914030303070f1b0303090605090303040201020705060a111f140f1b040506030f 77
    0x22109001d0250680104a994680760110703580b84103180d422021360102180b4040fa15101e80c0100900540202d8a5142f9040c502c0404c0c0082400f41403c801600c500001c07420311918a80380244109108140c5004540150700150b56032607221042d03940300d00403a10f503800c850342c1301c2590407080b6001d000107648a0028200b418541103480e8070210034031550100700444002e0018015000c2c00200041890640300c0d8808507074228910074004043d4002e101c0086012030f4408040c0040350401d03620010311980e11031081861000c2841e2498240d0420400506014011440740300791001500d0275a50149000b801c059441070301c0d0344102c00003500c4801030000e0050b54080c041e04102070501031469820b06030b00203556041680302e03130f43c0209004a02001424003401c01a00c100301d030102a19003c03000012810b100642140d4009070080c035140d4000d12003444000d90300d200b440c0030107645801d0348540401800c3d03c20200948401c8800c2048003150700d4880501075405000425410b009908096 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 247363408 1250 247362158 247362163
    0x60e090c090c030f13020d02032a0607050709020901050c030a0e0120060a0c020309040c0c0b0a060f090222090c090512030a0c020f0a0303021c020102030106120f090605130203 77
    0x141c042e65084500b4400d100340c021215040c03a800120040c02d08039800050320205459011060010750705001d03413081c0001000c100c5540d482a4000c101e804002c1600c52003c20080f80038001c0046d0243e48903900503c041c0303c0b80d40c010110410141856400d00c0c2c80c0d0000f00b482c650203c00b01000050700e1721454551035800006240c44c1c031994240100c014841d241004c0e640380b00c005d092040303c6407030300c0b80004541c2c024030032102c1c8843c003d0010f0191042880021340420346d2003100b1541402e8020008240040510984050301c03501c040d06684140307002502e0020390440002c4052116a80c2030308400d403d140680f881c0240714004c00410072400d46072002c0c0ac0039569a00c12401091040c00490011704003008031025400c246c2016042c2009a00100d0020a0f0396440b5071b800010746a0040241500001c0048190030480501d5003a8040d40740205d00740c0c0001e10641000c1480094040c1d003085203600311411040c0d0118000444215949648040c0c0300c0681e80804000610780300301040d41000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 247364658 1250 247363408 247363411
    0x21f090501020d140a141303020a0503010c020c1210060e061009050906010f140c070816050a05152a0c0108061008040c080604080d1a10030c0201060e090c09 69
    0x90000d401100701d40e550250a40c4a1074004104d0100009020400103016080500749a10982c1c1e406440d92142d03421429104d02601041e440b0b42c4414000003094601400b6642600c4032a0703002d0902000110107100d1140003024000900e4000e068802c0100041391241000800a0036101c05c10b034207102013030004c3c000b8240504420041c40280a01c101d454104810343c00110a03c1d2200803000e070a40100c8140c841c00003080150344e00020100c00000300040d540060351040c43c00d03150149288010710400da03242d4402c8941103032141c4000c200c0c9180101d480008941682c014a10340300400303000592030409005428210314100312512503041c0c0411980c5013050382070a01400714100007000401c0c150f40e50200000300030116000604004e00100c141004201c00e008a031000e041601c0c110000e508034116924443d071070034950307200d011040a030f000c1c0000400307007000b03807011803460045018080300010b05040d507485a40000700f1036449200b461040180c03002a01d0044610000c121759841c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 247365908 1250 247364658 247364669
    0x2180906180c01080711030d0608010e06100e0c0306220c0e030a030512060301090804080a06180b04030305100519180b090c0a030603020414060301050a110d051003021f09 75
    0x11041002c2c0c0e43c0242d0303a2a00013003d4100580f004015809207891481100c00307103030f9001e08001c800100114150050075505040700240d48241d55660450a60180320744902c01045500801140e4855042c078019070700300101400c65400a408038814805841d8210402c1d904681e0311840f405215031b00c0944a00c43c5403048002d09084a2a51801042e50044110f40104408032101040850b6025130001d02c4c482d0380010100d88a40c0c2c1c0d0001c45403030341c00780c00c4143c030f0050910001d0f00b600c9000003030607400e072a40913003041402c2d25030f91003c0300185001047c0d01c4040102e038802180c90390701e084420000d4035850242c103000500307002005140c1a5403041e40324040d03040045a01150395030620f03107039100c0a040c849a807150b900305011405021940c0c8041e420a14160180c5501590110f541d403040c031040c0c0c020b101d0ba46a5085002c01c0b195214010500f099040c000c80c111107013a50041034010500d292065030031a140c1d000581d51601c009140c0200d0f60125400c0703c0d02c1d5810502000c000c11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 247367158 1250 247365908 247365913
    0x30c010203161b0f0f08100c080112021210020a020f0a0c0302011202040f0b030121022d04020a0e090f04020105040302012f01020a03150308160218090618 68
    0x946000c0e02e0000064040001845034000a41c00150055080d110030000c014500701ca05a690f902e0841d0115101180102d12003030141010404180102e07000718407160209944512086e072030085800340b61200d001e022a03001d803000c000820f1244040025004401e450080141d503400504030191034071510340d41d540d0380b50b00205000004111001211401c07250282000c0030b8491003d000040244540d810241c800103c0f00307000310701c0e800341d1005941a80d0702e51703640d06040340c141030300400c00c500040d038002c1d4000c4001ca191110b00c110054040e800c0703d010104c40c455583d0f810300007004c0e600310b65034101c00601c0c211403020b802e24000400e6508640d148504128508198000030a1840340d404040d0512082000e001d80140e81e070500341c006450306481070501c0c600788080941c040e500c52110440001e0030170440603010084402c1e100200c0c3d0380300189c2407070400140403580d101c3d1042041a40e001c02d40069104208080f810254402c217036441c068880707460720740002000c10484444490b4a40d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 247368408 1250 247367158 247367167
    0x1b070902180f03030706050606070803010807050f01020a050d11010b030f10110c1209131406040c09180e010b100503040c0b0703020d03150b1308010c230901020106051e030c010203 79
    0x60b01e0210841746680c1e084103001c101d59a0b0200802c030140300c0c031507000b040070100000000d000f020105249056038001c41d80008111124001240d564a409801900581004800741c036160b014141c07004403c0300c0c0b480080f9040461300300180c20001841000c402c1d50300296480c04503c0790300d1141c00b0103486605d401904001072800d25580d10a5042c0d44000a010300103400c0e4a190355840308890450300d07184003440714045a40701820a0b000c1640d03030380d0041c2d080241c60f42e102e03801072120300c2c140c0b1071100101d00e80511184105019090581015206540c3c9054501c00303502c41419080e80c080b030a440720b60b900d05140c81c0c1300b0020500b0f0b900604883e070b000c0c0030f40d03000640d0103d4143c0f1008090310700851848041c0c2144815200b6507404144402c1e0700017403000c04008a0709041c011500640004c1059102003042038038000c5909800686045014822100300e10100740506100e81c0d040c40001081d40e00c40b404206c900007a03c0b402d895510300c0e1a003c40315413070100401d00d4407820a01c06103003031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 247369658 1250 247368408 247368439
    0xf15061c0804030b0c04090c0f0807020c0319021305010b0304030e040204030308040602130e130302070e06060405060a0207090501090905010b0109060e0d0609080d02040602070e070203040b1b07090218 88
    0x1d81c0114000100001581310100d03d00300c2840d001d03540a800f10800c108000811800c0190207102e0f8000000082902c0e41c0010b6421800801c54551613013015000d08208100c14200601080900e0790490b0700440391045400d4800d090300c11140600151100b85a60b420181400740034440d04a00d0144501c1c010042400042e90103803480d60826071140000d40c8403541891607604c2000290041001d4044c66010003240f41180d218602074140030303800f9540800d80721101501d43d40c00444030550800740801c020040350070a0401000230908510640f074840d03445030720b5130040c1d42007a40140d2055464142460511100b071162016030142400c0c8000001e00d042c1e4090312505070701843c5c0341b08030784440380c0406010311078101c59411503020815070350750f0780c40302410300007504603016081c0103120b0003001181000d52040d80901885240d0010b500341850500300d0403103540405000d8030543c8814426008030302c000c1107004041c103148000580c44401c686068482c1d2440d411050b03204900d1141540c51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 247370908 1250 247369658 247369673
    0xc0c09021306080601051b100b030316030e120607080103020406060302030f0a1503050307060501030b071d2704060c0206060105091503040f0b040818060306010e0f01020f15061c 78
    0x12500c860a0070b403400d9403100016206e82c007800201704e4985105804c0014280b10100340304108220b07000c41005440401d206040d500d004003280c010003c0066000040824080e10040c405824001c0004541103401038a03e803d24900365241d501140880e001407085240a000d070f040070303080e030380b030210300358641428002070003180039160a12045c1c8d144449080300d60840c00d200040c50304103040b02d0340c60001d45007890040c03800344815240700300c0010101d2718281c8115440b40700303d090404241601403095040000420040480052a070310555a07d01c80401328480d10344681d010307983c0011210700c2e4610181c14818020502810000100014142981e809440d07140704008000d0164499980f89088061120141405481056507008000c10040d00000504846403150b200385500c89400040c802c0c18001a202c09000c1091b0030400c3e000703828031082040034500144112110b40c0e200d4200d85e400c001c0d20710f802014000c1e180d42002a1030800161003110000c141c1d01440320019927454410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 247372158 1250 247370908 247370947
    0x905190b010e0d03090b0a08161407060b041404050a151509150519080d030603020108041101020a061e050903040501020303041401060503010f0609050a1406010f140a0c0c0902 77
    0x901c03d503070300400c210034113116503540f078083c0a040b89195650484039901502c00f203000c5900b50204040d0703140c1800c94500c03c0e1000301600042c901590b0800082d0380d20040a00303071204c41e142d0841d90341e40701054000b05200300c06004034016000f80520f003885051840303201c81c000307410200301410104422030450100e8520b0080760130802c0001020b000c1001c0341c80c51400d0540c007440d030101b0140c54203552034110080710300480300c500703080701c0c00d0504454040d000c1c0c0d002c600c40a808148010000b40c00700740040801c07294014148183d03803881d000759032204200c4440380c60301c21512072a4102c03013031001c4091041c650041e80e900025800c10307181000003956844001c000405800c40c10001d0065090309401c08009018010020700003142c075071517072600802444c4581c0005134148804106208090720400891640c00a98604156962401501e0400029416008001000346c40380c00184030032000d04a0381443e41c1c0e40070181c0b000c500f00106a0300d1590460747c10248100300300c0d070016090142c801c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 247373408 1250 247372158 247372187
    0x303140f07110a05010c0905120105010e310c05040b040501030f02010c020a150c110418021026040b0711030403030c031205040b010f15090302041d070905190b01 71
    0x41030b080300802080d00b0042c0860700100190300740a031030154590080b00354425601e064880f01640ca12460241d4241eaa00b88075030700303440e0940e40c04120411078500c1034040100d846080e40741d9017913071540f404c074041c00d44040641d10954804004d1010340b034580603451025004403401d0049504584908c1102d40000740000c1c10302c441603184a0464961294200040c00e541c00b0105402c0c03400c05004e01403c00424040391040e04008040c1c0701854a48110007804e070b00c04181c1000d15055500344001800f60314080c000740708441c01030582e00e2601d20303140b6581001c00f03038a03862681031600c0c2482014101038403010900c01c81c52003541d0070450001c2aa000c803500340c9005010f0003281d050541f0711028142c0d00802c2d05040108000a0002003444d03a0304031404040c08a4509540795030218000e6243c0600c10001078070164208090314240d0030101c1080751104050f00c2600003103001501c1c20f61290321036600142c8507010410314107034900c0d4820072444081000d00156400d000000c24891010115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 247374658 1250 247373408 247373417
    0x12052a0714010e130605030a0318050d08030720010c0302070b100605030c070812090c01140a0210020f160308040501060b03011d0403030b03010213030b01050a1401120e0102160303140f07 82
    0x140c224015168005c00c0c014000601500d03003102e0142001031030782c81d499503c800546001070f00010f6900b45084520701071a0001030540c01c545800a0480e081c2c2071850245508104010b81c0c0c42d810307003080c80741c20000303501d03a1001a9030702054076180c1e0705500010114510608564000c001080e0030038200d1754445200000103607074220030714050445000d80803007610112100030410040f4200090303140040c1d030090702c803c104510901500c2c0b89522500f1b81100c010b130044039800f40949111740103464003903204001c00341000344041604050060600054002078144e80030300040c03000038030a000c098012486110301c1d5604148800f002d0148260103210364100740c00003e81494402d83c030498106e11300400070341d513070362100c111030407145c801c0e00041d26884400ca000066600d00740301110102d50301d510300e501c40c01c001c5c000191501440480031583c034548500701880b0510007032004149008644030741448002d55820010101d8074115210784590791380b402400301c41d00314518a10f0348142035180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 247375908 1250 247374658 247374679
    0x30c061b04030f0c0320030f0c0f010507020f0d21030501050307050d0f0c0b09030706020604230a050a0305130830070605040f03140a0c12052a0714010e 67
    0x14215136803140380d4009405994984240320500a00c1c501d40ba01d08401101241c0d11903950040d8151150800c94801c0c4e40002e04034062405c42d405400581811350000b40306014040854012615105403504100d0707810100745001040c581455865040303028039440c04021543c1000c1c04a075032030180e030040ca4483e2900508241c00c101c01c2d51003080445910600450a030380e40c0340080c134102d402c40e100b603a20a0086c0c040120750070348001913013482079803c405481c410010001c02c0300c0006944041c0d80d005070080d803070b501d40400e400300220360507203200e40d403071a80e00c202d1201141c0d0b000721075801c0300e01190420b10103001402c4820341c0920450550005950850800300e200052912841c1c00043c0003509200403c818088c00204503410217000780c480c1e829900640c61035180302e2042c0c05801c03010400317911000d00881c070400708a5940c148682062441c0c15001c51546c8160600c0d24400050701200144484481c0004c0c00550006d10400c81418540100c80f40064507a08982da00580034154900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 247377158 1250 247375908 247375913
    0x30b0c0d021b07030b0108011e052e09151d09031606061511031204020616060b030706051905250b2409010509090c1002030c061b04030f 60
    0x9040710b010062818040c1c2c40201d80e816019260305082c1300a94500c0701110001500180601400700d54a01c1c2228500120352001500c100400015101804403010342c000039211000790492240d2810f4815038200009191540352002e440054002408070042d0380d0003000000913038041003181500c03901080c4002c0c2c0c0c030303800c1651440c000d81269036440421705546400b449100d41c0000b055488121440c1c0700150045000e545000b481503121a09034401c06c1229000319030b41c0c0c1c100d50850300c000c2c08913180c8be416503240e5182d842d1401080d1101d5542d406017502a1908014950080480d42423484c02c00c0b806180301030441e00c03440541c0d01801340c005801e42e0031815180380030f1940c2c1400b4101c0300c0802d850782000110b0001c105d4507500388100c1152080d5010071103419a24a6002c01010142e203a070a00b0148010654060030324041c91141890004699446d40b0a5008402441c2d00642d00c81c901204007514081c0e02a008800c80802080d605903140d01d16000c0f1070a032900100f01401140c12407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 247378408 1250 247377158 247377161
    0x100c0f02030d12060905010302010203070308040309031a0a0b0d0809040b0d02090414210304150b03060906270703030c081207050702040f020a0c0308060303090a120201080907030b0c0d 81
    0x224001d506002d000e140500341d0340c000900c2038048480c108104407054480220707404854081c00302a016910a224070000607105200e041e0b8083d11070b142502c03400d41e40e9134541d2110700001c00110906902d0804002041081e4402d019901000700c80e11b046421603525168503d02c90301036020701071625104501d03241d0b22036003404080180d028140a80c28541800d214406000102522b5814000c030303d90405800d1461a000015860281515140d6100c60355074a180241440702070b01d626458500d00d019035501448454400d03090140078200031718145420000c0400680360700540d41440490807a40070400080308425aa403504001c40b600c2d00138105140c0c0303401381c2c500130b1070340c0f5005600304840c00380d011001e415118400e98040c0f2240102494180c10790241041240005007484c5804012a1040202d250442e00207402c2d00e29060805000c641d1402040e0000903110342c4c40100101156404180da960012040307002c0c0a102c1e0842c0d40301c4400c3d01010b1f00c240c500c42008200b1a0180055 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 247379658 1250 247378408 247378433
    0xc0b06010318050f0606220513060c120c03021611030a02030f15070305190906020c1002040f050f0603070503070203040509130203060906010b091e063402100c 70
    0x11050594203800d001e19006580f903c118101c0021801041c000c03071b1850404000b1564400c00b6502154600202111200d0043c0b10040140810703428005842011814501c1011041701042c0c1c4c0350307083e46108402d0402596401c1c542c0508040c8100100480c0381034885c0d019011992003500300900a00b20000245020042c84011390f25000341004810171440000d40400703003800f241503c026941e61100c05a0440c0e80454105200001c00c0c3c10b080c0f01015241d005140d51840390f080141042d8091885500c0c00c080ba0074004412940082d003401060190301021000702400c0b10010300f900300764030210750a804050312650a01c100030010444050091040d01c010309400b900c4607042e1f1415640460ba8a03a01e11421b9000b4020b10001c5064800b002c54440d0503900c511076041c0c90201d22900348100780f40520070005126520b1103644109903110f41c0280070010200700c002d0b4403000c040703641180b0307206100e1042d0004203002107940016101e0600c1d48503004071508186420103080c0c101407000c90030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 247380908 1250 247379658 247379681
    0xc03030412020d150e0d110c09040201030c14030a151a0717090402070f120903030905060903071503060513090507090209031603050d0306080a02150c030f030103030f1e0c0b060103 79
    0x1c2000b01440305d50005204210b24000390b490a0b064584d5580309510303880c071100c5c1c454108020000140155010360801c401c200c0c00b52508101c008501c00a440740303508151236a0018a03220700d40007000d00c03806040b650240904030a03c0c0c620346e041080f00d0038148a184801080b85c0f25a5034110040d110700b0080c1c1e0801400608103660311a180e290a5002e40000d0f02d048a01505107403c48450600c66000d0030107483e415110100352508040800c202030b00311002d43c40e40741c401c0c242c001c58070803403082e0b220b180c004540e24003041950a1408204243c00040c11080f1428030f050195004502c000503408215441000010313601c88104e00031905012800d24030005200100310000104100001c01a070003102d00e903030804c104e68840c40d003a41c80e0600000069404a0707880c0b81e070200101904020054404c410045070300e0300c10b802c5a01e19868200341e000b600130804084a900d1915004102d41020110b0700d04103c068031809280601a40c50038800940b400505400282650740a030384403290240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 247382158 1250 247380908 247380911
    0x190509061b0a060e0604020a1d0a0b040f06080d0e030d051806160b18160e090304030b1e1602100f020f0706091401020309060a2706020703020c03030412020d15 70
    0x12001104c1c59501c0c0c9017a03070301f03c0c0180143d20000822300740142401c2c1d0100006505000d090300e07101e10342c001500451000a9000c0c0d6a41c0b81c00360b00e56014445d48000303009440251500d40b4110030041e04980100c1c0b070f0780f40a07030003ea0700e0300038050307022088030850a0780392440840c00030580041a4140288030889001c1c0c100303482c01c1030030700c0207021a05101d0712601e031052043c224040300305c9407900c40070f0340d10805503d949041440035007aa400e4080c1e01840070b00859052656070740702c0d0700d0702030810f8809071100001402059000f124914019602120803072041000308141800295507442d4001d166000540e0354501e8041c260035038040300d0410b0301020ba5551035003601d0030180c0c000d0034614070444a40c491400d8400d469201070080d07030300c110281000303444281d8411015101030501c076170840c028101c1c0300721020300d00942c0c941781040310381c003907000180c07103000380c3c94041c0c0381015044006100754010b00080100808100c1e0132402290306480c4400423082601d01b04c2d14400caa400026800c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 247383408 1250 247382158 247382171
    0x9091f091112240409020d052a1804080d06080607050c07090c0c030c0c0504050c2101080309060f0d05090a051002120c2d190509061b0a06 61
    0x1000c1c21000b420440030039000015043d00c41550b050160002041d600e503801c01a0f820207070544c40e06038420180d00380081c1c40111500c5059451307506003141780f80d0b041403100c102070f2002216240d1004d11403c0040565210207140840c0041090b0980d00502c02447c0e81c4001800301050b40454000340c00a20010080f54054209510701904580020010b40e503144901c4800158070304881c06a003600070026218401c4c0d10302c140c0c904845402001ca002c0d03942040070f10b400100d9807506d1048910502d0324502140d01c1c0c000e0a001d81c114503548541052024107240c0040c800c030380300030046605031801102c489030740e10b01c018010b180a010b443c0c0301e50f040c1e915003401c01c942d5103004501c0e0008280304506440c400c4009510003800c90042039188d42c0040e500b8030000303182ca8810402030507410f041c0728031095040c0061002e0901d08440d0454650264000b20321360032075000303180d1078a04013a603c1c1000f500304003c2c6e50124101d802407005466415400c2100c0030513181702031101c0c100d46900314801f030025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 247384658 1250 247383408 247383431
    0x1b0706050705160b1605040b040e0c040803040608010906050f1f020c03070807030302160609060e040b030a1b05030f06040b2703030403020c01030204060c0b36010f0209091f09 77
    0x4c00e88100d40382000061070b440c010b400e0a210310704070ba0a56041003607050405052403019050303801d000344041c8a5860410010070503c5c1c04102500080c08169a0038a042d81030190000503074280c0d0f8440b40c020641907002c200e040d640c45000d0184032420140e07001002f01d0004049150030261451581c2600407180e001c51401400300d64a400e1ba0302940031119800900031101003441032610500340003940342e00c400c1c004140f180d4410b60400e48001e0010410014200000b424030708403e8084903042c075018001240e0b80b1414400710011f00d0110050b1681050101141d03880c0d440040c402091900c0d01000928071241c10390860741000c4d401300c0c030540341c0031410000503600d43c0142c1d010b030007520401c3d000040c10340c82402198203070303540395403402499140c5d0341c0c508108003006030004ca84d080c55a0340b10099589086030422200348a204200d2003459412903040c01c445100307032032a0301e00f0b00403c20103131681c540404141d00720803001031000011075407540b10186440701d80c012428035070802d40c00200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 247385908 1250 247384658 247384673
    0x50a230f0606091c02180a05041b0501020a03030209030a08030112110a15030e0f1b0a08030304020603040f050111071a07080105101407081605061b070605070516 71
    0x810301800c042603180d61500020008107010740880d4540c0700d00c6955844040840410380ba41411744080c000a11003006690303988010386c001c071911080c0e40c0e61501080700348112040e0140080031401d48402c9000c0c00c003c0000e480d02694040501850340004001c481620100200b44610742c11425031900c95031203800011144041c202c0546048901c2401e00d03009141401c202030844230030f5580388244105100081c1c0240c08181001c080d14010b819142000e02014064071014041034841401c6d03d00c0000c0400c00c0d20070454000388007540c4240100801600c1c0c44044030b400ca60080350110380c60301946001405405040b5848000d984003080351000c120040c5088058111018000f0f541540d40c103404030382d00002480381c1507001c5d41c50003c0d403141d1805001e042e948011000185490b000f034030b4880c1c0784c0aa0050800c9200704404080d050184402400016041000213191030490a0141e4001c441c3d802075200151841b5502c402082040703005d1030494404005e6401c82e11035155040c00c1016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 247387158 1250 247385908 247385911
    0xf091e0717070e101211030102070501110c070617041b0b1c050f070c03110c060c030408060c030403090618030b1509072c06040305030301080c0f04140604050a23 71
    0x8480d10b00810101360011240351521056490240608a00e1205600c441c0c98040440204903003556003007082801184007802108544208096102c1c0d45d1088254241d2500816500540030000681f9108110000d4a00d200d900a900514142031864070903080714191150780d40844001000050450300002c40c00880002400c1910030400641d9a010402074000c80f0031101600003425400b04180000e0280b100301d604c2e140010202c9501a00001c045500c561001c82015031552000c9020082400200413b03940010900401803c40c01e19560151040401c2c2c004c500034001108014450384507a41c24960003941c015118241500b414086091071050f150402401001520001040940500503000751222003050b0348000c94142c180c00c940441c07a514595a008100300300000c0070940c1000a140605008405050640901401c110641c8005501640250b0500721003180d60502c00c000c2c1d5901960956010886968003a02600103080080c00f04082c00f20502e00c0c0c58040c00401e0075107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 247388408 1250 247387158 247387169
    0x2101050a09020f09090a0b06040603050a051810020304050328030b031b060c1005040c06020c0306010b040308030601020c1005040e0a020f0910020a06091103060f091e071707 76
    0x10008141c480d88038a082e8803e0a1050001d1030080040100302d00b82440c43d0f69002240c80e02c0003400712400343c000b0350140d019500c0711002a40ba4800e10641c00d54074032840f0b8102569900012080f10400200c40d20342040068004045034048009000e0040078800c0301d04406030001c10f15034030440754071100c0340c02d40781000650029240c8403000015040002d402c401c90b201101f081d80141d000741040000350761000c3d00da1481c60049604040340304426008182c011442601d04050081c101807009107031a403810038441c880d40c4a40c0041080034084022101600e40040818aea04e0741c6400040c1c0c600b01d90101c0081c2c01100300a9401403142d40318002d0402e40e4141020001d45841c1c02104806074010440320245042007008040c5540c81c0103d07000307401703551034010b0744d49102081d12010b00301d541c80c64086d6843d00243d08184168a424015164085406003407803031181010405e00b50b41382100b02400e540885841040e0b40c07000010040c26005054074014400680e4007205410344500741403245 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 247389658 1250 247388408 247388419
    0x2130212010f06180f050402070503040f0605090909030306010503040605040f052508030c03040603021615050a050c1303060507020304030209160f020a0809040b0109090510031101030c0c0b0a02210105 88
    0x409404e98811041c201220541030440e028203090204010080d4448242102c0c18132003000001102c0c80f0046003480100041e0703e9407603c0d94050000d104400c000104800e03a10b4008004000c40760b0b80020507242c00982118002070241e58914011201044146001d07056208002c0b0b0a80031801c0b8500031030306002c81d82101c42d1820380d41d83da000c3e80c03806103100d40030141c0c10078441441028403c2d40585140d03401d46c081b28201e01c40b117481d05d000c0c108035401d4900003103031070394200100070084e40030342e0307030400c072890f0b0007a00e42400512108920165030100808030b6403100003240d0384501c2002603034082e5400400040b0642000e4540301003003581d00456201042440b1031183d8164004203140301600d402c61495454243c0d01c408010003010078445007030521040c90b00c00314007100c483c41600c1c031905403450400305650a50034522403048033302d80850f0401d400c06150400e1582e200d00d40c0300710f49503c026030000c00d4803200c0c1100c010b8011800c01052113043c94140c3d80102d809040502e04031001601c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 247390908 1250 247389658 247389677
    0x2180702010e190b0405070509090325031d01032301030b010e0603070603050a09060603031206230105090301090605091c0c081206040b03060c07030908071202130212010f06 76
    0x200f030b02e400e038903401c1d154119490800f540204410081044d8064410f400742c501240d200e1002a51810090354149540d88c03012516119560a81c5542c095002142090040c42c210300e84e0020950168000e504107107489003c80490b41ea4002e1700f10b852505540344201c042c0302007078980400140000d00c810344054904a00010360140101d083c580281000f0b030243c2041c40c00c00f2019001703484040c00030300303c95507a03001c00d5020401030b204400245111b82d84a0217030b84900e03105041901c0702d0390030000c80403140c1c1008101e58066110881101c031001e09000d0307211002c040000340103060f0900040c0000d4100070810035030000204981005116000600018120116080b03e01107112036005001c03000c20025600c03408a80e600e401c1d48180020404540d07405200c01280c01c0c900151019100c04034042201c030105a08036074182c000e040904020310420746040308188861400c0903000e4058204074904240300c8089404039235840480192000495a60f5062001d0004480c400c0c000099004807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 247392158 1250 247390908 247390931
    0x3030d090501141308180d030c0506072c0103090c030c060207080c03030405041e0f0b31020a140403030e01030b040203060108010e07030f11030105190f030b0c070218070201 76
    0x558240600207081c1603051a030758685d2000015800790390b86c070a404c0800c483d01901039603030350400442c1c2c0d8800c0d41e803412614907914100b440e12f02d001d40003200b17109032000c3d103442c080d25141d255100450840030024032000d4240040e80142103501000e4142210200c0220600807940c03034070000c40310075601b01e481044e030768080f5a44600310315804940c5600200010059441d0036004240f036181003800300004025203d03110811101550074503402a0f403607503d010307035a00c2d00c1d1a18249400600403841d11100c000281c44490441c21100d00081907400300e6807030105446010304811420b60f0083e55940c8076103d003005400c0030300c3d84500c2800a814100c40361007a0902c3d00035203018110603110000164249021400303100c0c0000d1012027050b50f20b0209062016460040f031142d02d00c82d814082d620b5041805000449200f401d50002030101c6400801285a592440408480c0c008065410b00d4a9a00c0040c61078400d621001c2d501c484448001c03441020b58410080c041c2e43e25400070442118140e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 247393408 1250 247392158 247392191
    0x13020a0608070c0b070516060504120e03100509191a0a0b090403082815050a080d03020906120a1401090c020d0c0c03020301050702031e1c0b04060503030d090501 71
    0x1c4504400051400300e01c0c500240142480315041703001c50900506095001d24400140b42c01000103551007915001400140503610b042c5018040304c0345040f0310009225004250368514840d80c0507182552038000580500041c0421040d0000c0004081001d5045082c409445640350001410030400000421960549885112401d031000b60154030a82d036581c5041c1ca0b0000020001c07100b0071607446108102c1001c0550466210705124000120100f19030748420b207801303440e04040d014900840c421b0041001c00039070b0031884107091070f0148e13403100e8110120341c260241c2e040c0300e48103000c00d00034003240041d00c1d001382d55a034003c0e0042513103ea9807014510300f81c2d00303c51404009a0852400001c88a20440d02e00e000b40303005001d010541a602d5010074210703041240c001e40180c00100307112080048400390380c030140c104ca0101e54100001440115030038440a82406e5006981d01c18840c0e0301d44031a005000181802000d683e02c5003040c524403406040e50307003030850f425440d01300c1e42205d11032103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 247394658 1250 247393408 247393411
    0x3090a120c0b0c0a30110d0f0506030705091b03010e01062c01180b0301080312090106050f0607060e1002090a0e010f09020705151f2102091008010513020a0608 70
    0x25622031242170b004440d20b801e00c182c03403044851000c40030207008038400814010803c0388110b604400b680c2e602858208011155000f00104c040c5040600382b0580b564001900b80c00c1c0c45048500192940b9512900386c2c0c000144058488818400310000410048452450b41280c0c0b070f030340b110f015071111542c1d8005600d0f11070054483d030541401c07006809510880840044020490002d800703261076005a03076254000f41e10042d481c0e440040c5105e80410200034494100405500a00290342072000003802c43c0480e0400c140039046c041146024000c10780c20241c101070403082511840312103481c00402950041e51041e02504403001c00041880b41882d6040c1240e030710045400c00c881c01c020b6480c01a50001806582c14450012020fa07400f5100300224010850035000d1071081d0100c0c807042400c1b5046900201c042c800c0400340100701c1d0590a03403d002160304442c12207095455035461070000c11160880c4c05198070f480d0820030303904001c240c500130301402150942c0b14965580c0044429540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 247395908 1250 247394658 247394677
    0x11d03070b040b09010b03030c030a0306051507060c0c12030525081b07173f090f0d0206090f0c030d0c02060708030705070c0905011a03090a120c0b0c 66
    0x952400a0b0105150f00d40031600300c2014800800c41a224000091441c1c0000000c1c201c6900001051610a500b6120303c10080c942910034500c1c0047d90b11019030b4500401034091b01d50f50f2946d4404680920604e04449029030003101c0a0b0070500c2848010002c0900312020203150700110341441401000000340360841754141e5907289680d464145494041040d410300c0d920105060155500069185016286810385046455201d000150010482c0d080980c1002100c038011076912462900401d4440100003010400d030081380c41d000c0783c180c82c10b0031180d603941203030145800f44050030f64042440b6001d04089400c442080210782c02e0252079080102925905a00c070072400344106004101c40304090707000401081c02e1039041c0d21941101c0e807048481c5400a100090310000704070351003203040090404520100855810810700040800c20346100b40030303200c00403000030318a0320200a40000294000032608040c0b100c42c90103089500e09140c116038510f456800104014040c030b051b50b5410700b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 247397158 1250 247395908 247395923
    0x608031c1a120f030c0d0f0302040518061f020a050c030f060609040501020409060e180d02061f1a07140c060d0c02010b0a0609080111070818060d0c02011d0307 70
    0x30414080002d0b07500310281a00d82c1c3e026900e9220750040301030001d045035803404400781c030715480c41020050012400e944400d051502c103000501580d26942c00001f00c0c049801110f2841c2d454150008690302c181c00080c00c4d158011440c3d41027266404614040702a1298040740d03a4003114604040c1c851040603e00102984088001209440c0c1000815000303802480014a0680c4070701082c4203444c81c90b04034078602040c10080c848072410300401110282031007006040100103807803000791686809080b202080c1e10010b0886131003004408080003c106080e00030040e544801c0000c01c00d0340000400740c1d810004521840381d4144080385442c0c501c60001c12546c0b03440c05000c6080000e01100b40d00208565a07152052070f691119409407014100c0c41d02c49800103442c001100d403c0d50401c05501c05a240c0a0007603c0000e000d6005a9041410000d803496070078a903040403610901481400d800300b00c0c1061421a040c54040d0722525101109044000c030308900306015a0b501c0c401d684001f0480d9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 247398408 1250 247397158 247397201
    0x60603060105093d031406040e0c0901030b0a051e0a051302122a010e06090105130905011d0103020d02091512070e0a0605030a030c0302030d0608031c 66
    0x20342c4518001c1c810020024401c20090201000344410f10322030800521041004564810075184000004038042e03031245418170001d0a0800034502c61540034148501680c1c40d0b40000200d294280860b44070558050421000713580d69080241d032040f8203441c801c0c02c8a1514011400e040c6070910803092490385400520b0040e00d03003400720700042c00000c00080c040500301d00884010380d102144400c12902e20710080034402c40340c0d02c0d00400100900d80c41000318609000150090342c0207222100808401c454058a403118140180c640b8402c103001c0e6000d03641010702c08a13800041e0361115060741e010794403e840900a0b034030740048602c004c2c0000380d40460140071100040c5410306000d0f91007184209000310002c20000420884081440be803801c6070402c036801d1001080e02d051260340b201c103861301800001d151001290711414070590250800480b06140403d26000b003003155020107030504204020340d95600ca481d02e030b400c04d20020400717900c40d195482890219001b442c508081d801c0c984101d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 247399658 1250 247398408 247398421
    0x15080a0c1407120309140d0f05090f0d0807060507020307051c05040b03060a03120e0306090a03080105060d020f0703050901031b1b0c05060708030603070e1603020901031d01021c0203060603 83
    0x80580c4140000200340d141d070201070010324450f24500401561b04000d02c03040c009518090481c01d00e13601a54100031090244640584d80d0030440c0705000c2d819106034007103a00c40d0030b1820403441640d0020305607605000500003219800801800c5d0700d801001500d51007800d18110684540c0b840c201e80000a405002c284003105414005680016008014010303041d602d645032410b02200032500320105000c1410200f00d801c0c01d004455000030840060140010159009400000d060141d0b600901c40400d07070540c190001c1d4100c460b0800b40c801101d84405442c81c00070103035400600d0b9940001d05021848450700341c7c0100b41304c0101000e8070356050011345180d007101e07142100102a500302c60042c0c030004864551030010f059503030050144955178641700080c54680728541c0d0000321a2040c1e8410800312036a5203050018500340c5240259581c600750300120064207002c0c1c50030b081034100e1a0903a0042c40154018401c42000400048d001c003045901d08007280800c031065078000c003080002400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 247400908 1250 247399658 247399673
    0x31a16031e14010f0909020303160c03060501080307060f021633060f0501020a080a03020a0306050603180105090102180402030604090f0b15060903030901140415080a0c1407 76
    0x1211141d03555501100c8086103010781c1651055107445a071241c00c14010700c0501c0f0b09201e4039020705103484081c0139160300342d80469501d1090500109c0b080901d0810701c1e04000c3c00f50300c15401507400c008280f0495845507030882d126482030400300c503443d10b0050300c131065841a0090300c541d42084030119820b0001030311201420207428a541001031420308056071100912180585401c0b0700d06d000040c454140705070822041ca040c0c101c01e065500001c40500040c1ca04400c8451990b00ca01c0c0c0540c43d01002e20040d0043e001070b8003c5a4045c102200b00120801c40342e0308003000040d404c009001035111a25003908030312810300c1d40003284007181001c2866082c1031300195000480948002004400c40c1c44008241d01c50000407503100b40c011040c000c01c80c00600307440071003440403540d030362401e441c03d40080daa81c812400001d040c040094950020040c0b03205c02e4400800040113800040003003088001d0202c0e4048a000e2042031030304d5510107003244950710151f1160020092545469015220800e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 247402158 1250 247400908 247400921
    0x80604030807030f180c0803040b0d0207020d12030903090e100b03041b061e02280204110c0a021504030807150f0f14060111060a09080702030313031a1603 68
    0xf41030301c400c1e4280e4000228030030044607140740d4125181c18010741c40d080d006144c15600c610820390003800140074540401c1c1c201d0309011300501d001a038131841407004c17842e0000030402c050900d0940144004401e034054220020003446035480c206285d0b2650b0465030035113820740741e0452090040c0018004490325400640c1c1183c02104501c01c1e4070784140c2c00e4040c2030403582046000540e04c00303c004402d03900100384246101d240c005841d90003500041c3c01e0302c110741604c1c0d0215424610143c43d0654a4550180c1078010300c0444840d507032440a15000c0d5100c000040c202e00600b440b94402c068101540240c2c0d00340c03548083e9007031400c070186e1217000c11036284140b01d0084507039480c50030a02100b1442803011030304496034041401b800c018004e004103480202414140302403554640354491011812544c0600325210001d4510828105101107029402c4002c0d058400003c00c04480c6c14085d042d80304807403080041c5419441494000802848180c0b0503582d15003942c14010003a6000e0782106 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 247403408 1250 247402158 247402171
    0x6090b0a0501081e0304030b010f030302070801020f07120c06111b07140609120a03120b090907090c0905060409050109060b0a02071202121f0605030a0f0b0403031b081e010806040308 80
    0x8134103060300c1c0e2300c07003900c07001c800c0c0d0201c043c0d50300c841010000c158060003840700400c5034000840c14000308104010302d500c01c011000304410100c8030005034490080300b441c110740c0e400210800c80f0f00d070425181410750740440006116903402080207851401f0000d000703016105201d1042011072502c0052087c0d0740c0154039040d902c0001d0714802d028203a8100310880e0f040b4001d503200044010301e62001801c40700c0c040340d1036008208010401801c904c0000740c0e2030071600c800f440060701c2c03050200122044060380d00915444480001c0010300040c0359044641a909078081c00c000d030680d151060b1100e0b214941000300540c2000004110380c900008100e0320150002c0e111115800392a44c4890400008401c00c102407000c00c400222141c1c010312405010384410b40080040000b20b403070b8031402c070813480b00007021400c0300c070001810180b0940000030303440440319540503031060900018100391011075100d0304101011010903014285550083c1c12a0400c0c00501200c0d116a04c0417500010020b142 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 247404658 1250 247403408 247403413
    0x818030a020d05100c0f0c0f03050c010204081e01020702010914030109080a0804060b240f07081b010b06040f05060c0c0603130203070f0605030c0a030902030a06090b0a0501081e 78
    0x8940258031880003030b0706a42d2044019000303e134000c0310710034111a1002c4020040000501c0c10300d0f0019041216201e03819000b1640da8034201c100d00d01140c081c0301d402808011940003150020b038110002440c014800750510700c8904625840102078201e0052240107800100c1050082040310380340b002c800d03080e003000380002c50455029190070342103500200380c82c0c0011703200c0c608004c20300103944140014403000b00d5a2107901c80710602c4484002826080c400610f1000188070518900c1644c102c481003580700010396210444100007454102c031440000301c0039424800e800d0035a103800c10407107065451100c003052a190403d01449800d4100c0200c195403803283c20712010300c96842c02c018521503c80c000c11039910765a91310603d410004291300001480d08100018000710781c001d415294450b80f000150764a480341c04400b2009070240342c4c8042d40500444408500b840300940040100c4d502132402464a5101c4810038022030308244038008058101098070b80340005441b078041c9500c92041d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 247405908 1250 247404658 247404673
    0x30a180801060308030405010c230a0215010e012405040311040f061517090d11031b010c0e0d030e3001020301050405180a0305161209060219081803 65
    0x1103003400c44046400a503016003011042104100d42405101014907261420040d40c00b2900000711801c0f19482c08645903601c0407a1401d2020710070001e02010500c46024000c2950f55240c0400c039803a0280500e00c140c4940d442540722600700c42005204945003681d61620b03007861602c5402400c41c041c8003065100c1c0d19201000d100d5045405100090022408031301c015449403130016003803594481705958841d20000070094500804940030004240b14145031a010100b1494107040d4810707096000c50f4081101003014420350154425a5400c8950700d44003200d110090800400740e250b003c008001401e52540009a4240140c0c030120300d24500804000340701095454200c1d1650413282c1c0a440d07940031004200e54500740c0074043d00101c0150ba51000124982034103601c0321801c890207070900c04001040c0c40a90610040c0099641d0480c54118422091100007499030390386118020041c070880803000390300c0c00791401040d4281d82c00740700c040c6402071007003130901940b240c41c1040f98140034461 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 247407158 1250 247405908 247405919
    0x504060b06073903020f01020c090a09060501060507021f0207090e010203060310060e1b09061813020c070e060f270121060f0e01060f03050601080d02030a18 69
    0x8098581d40303100c0c98605116074036000001c03c0d00707103890314102d580441d02455502803030f60005800c01642c0c2c0590307a4610007010780c00140c1c41c0c0030481759026084642c0d04200940c411469012a1042d440b0f203005102e41d03640d0300c0c4100d0b201e0181e040081d40c0844294024021001ca14030039808041840c01a21000c642c0c0e04228022a14084262420740e500007003001142e103401d000b0700c03420000344041000100c1c1000105400010700400c1e50402e501c441448803529001c000035039040c038400500480c0d84c3da1104112100030001031000314007031508440c41e0b000c10340060084c0ea40c2c1020840051613182c0c0340c521848108080540032682001c100000c890007034035403210f12503004030000982c007401307404180c0c003400c280c2c0140c0c4600d460403c4580703116070413040000380c03050041e00070300e01040d1410488074500c002c015174000c1d00300325840c1c00c5d4001386915a1840e10303000ca0f40560183c074a41d070f80e01c03c001c40e180c0402d08020001a0000c10540300c64601400825200c0044081c4422410b519113 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 247408408 1250 247407158 247407169
    0xf07020703120504030b0108011b140405041e0b01031b0309080c0105040602370507111e031005061503040c21110f1503090a06060312090807030503030a0504060b 71
    0x6a01010000d00c0c00141881070000c0c103d551b500404004001b00301000e4a1644041e001c8050301d060400c0101c0d04520010141c98101650301828000b4000c0110b04d0115240c50825503c1c40014064076052101c004072541c080d1086035008003006201c004c600181c030340228000c0540c004201c480007070a000f0710404110920440c3d105070302c9881d006a0300c80d40040c00708900c0508815070a0005c40320026900d01070414070003408684a14200ba549030101d91400054080c0003140140d002240100c1d502ca103032018118142c41e0300826000c0d41e0794440b6480e0604159a022503026402580321000b1021100720b01e002550f000f801605089041e0391109101c0348981300c4900300180b00e10700074800100344a003190201c080c40078210380c03940740e4034151070224104c1c0b441d005000d0780f400b0001c00060a60f400505c580c42031158005000c101050300e070701c0e00c509080c00d4210488006403401c44081044030300020404103498000c3c0c01141142e030b540e2001d80240c00e008100b125859220310701d44943d034494 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 247409658 1250 247408408 247408433
    0x8090402040b07081206100203120a020f131419030b0402040207050303101a04060807030c0504050d060501030605100b040e07090302040e0a0203280809180f01030b1308030f07020703 80
    0x2910704079590700400b44c000c0000105c0905080e00c05e412407c0d1254042d42c0010480d04c0700780c4913403001d01440c0e0b60240c540000f03016500303422800d480001130181003ca42030f40c5500a540c0308103c0d85590642801c1401b01d0505001190a00d81c0f07440c40e41400443c03200c002c40ca40c81840140302500e410b455030b0b6280e0071504166041c144d0071894403010b001100703000007580400040c603d10181400c0c900f242c000c05003070024041c42c0505941c1e40604110b188594210f802030700010345031400450643c07034054001c003004d100c00e0380c5407840c00b0049100c24001051400848140c05c0c010303810282001c0010360a810054954170920003001e000000580300c5020300000d010a50020780308045050050604015440c42c100109201d014901d90000145084468115810810054803980c0c0c900100d84c0851000705803002d482c0c032000400c40c45004007020103060300e2080340040441d4441c20300b003a881d0301802030b0040100406000084041c42040c40b482d85c40095441161045c80d907a81362000c0c41d0a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 247410908 1250 247409658 247409663
    0x213050603191b081e0f070c050304080706031802010c02060a0302040e070908010b09070206070c06020c01150501140306090604050c09130c0e300f071d13020d08090402040b07 77
    0x303003c10070b241141c0c00c1182c413603200c220000c0d030807591491100c1d01c00607190b0007000c8181da800600085402c0360320440310b141200b0b910a081725620b640300c2c070351203070340c0c1e0320710310071840000d050100031183e40150000f21800d15a0684511042620560030041d8580100e003554040560910000501c183d80548590081c0d00c0c5441d000718003802c1907042ca0a4881500e0303aa4014500c08042c488541d40c00244240d00140514291001030414038000c0c010b4411a0003584582d804d00c0d280c034229105804070b400844009885006084030304084c5810140021900e981d8444079440001c0d4007410719802c5036a104002c1950245030800c41000950380e4140512103140260b61120800031a58000c17180643d0280201c5003048140c4041e0000e10b42c4179485249014144801c0744000c6211104210030054140c040041e11200d03903c9a042d94a10071002c000454905860000b00b8184821420100c0362540c000c0c08045003040c2c0d03504ca10016520003500c0607003003582000f000410020b400050102c652 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 247412158 1250 247410908 247410941
    0x81308120f070c15020912031210050904030806100309081602150c0304091d0609060703050703020301060e010e0316120204060f060c06150b220801021305060319 71
    0x40c00071450700c00c01c10091044040c08040c03204140494110f14001c0b00303d00a054004d81c2d100140c3d0003040300b007407000042407490305c00402c045102600c000481c030300c9492040e464401d1555a1810001c0400080c0d0300500420071030404908282845120307821304807450309011500c00030968484005920a0a654030307043e50355081c24003180b40c00344d402403003058800021800c5c8040510b03003d0301d901c2a8418030800e1980c1d208441c4203000110240c04124900300103840a0740340a41c6c006407510001c0303e520001038070b01800680d000b0700078400d81e4180c840a94400e85202d00100c019903007061201d800702da00d03108112020604143d10008c0c1400381c1000f4501c802170bd1024814001550907036008103141c003007120400d00c1095401510301003216003115000c12040c2811010031084015900204120800018004405000da4281c208044412060b012400355908010b5080740180140110300512004c0f0800051401e0b001954110004400500311800d004d12464222500030031191580c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 247413408 1250 247412158 247412161
    0x702010b0102011b2c030307120f08040c05060705011103070c061401050f090c0d0c17090a122102040303030615030903170411030d030e0f07051008130812 68
    0x156428084c04010030071000d4084058400101d001e060702074840030319000c40041240a13240094464441c1600c608042c00b81c03507891402d400c0401c4c2c05580521030034040303006a030380202c40b14442c0d08964890b81d040701515121314102410000903034420002640c86640395140c488081d01c650000f140203500070344540060744101d24065050b50f0f002040c0041008401c0010001038444406040c01810205c03003443c220746c3c1b0311808162030f0080500340c008961803c1c2a10a000381c00034100250745441141c40002c0784d9600892304d07690036000c03000414500c030500041585902030b6800b4104082d960490000040140c0614000c0f60007580c025800a030b00c500c020424050400605501c0403d14502070040006685000d07052281c0016034403840440c280c0001d040c800c464041030944035005060b956080c50f26840200540327074090081546000e00c0200c100d07072000000300c6204451001e8405001c10300c0d1139070113850954008200040020342c8420103400514090010214650384502210b0716 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 247414658 1250 247413408 247413431
    0x60a0507181a1308070303020303041505040f0204110405120303040303140c0906070204090602210901020711041802090a020a120b060d151809020909031c15030209070201 75
    0x46480102030030340700195081c050000041d80902d4611000c600001c05641e521901c10180480d0856030180e503142c0916840801010390210040d40180c0c010501c511a403404844107004507070082d00c00030f0840c0340800340e4100504064000030000442840082d05047d5030303001003040d0821903568a9070b550400010841003540510500e0a80d42e00d44914a2071460308596594081c420203c42a2040030007080301011552a81c01006000d944500c040d906c0c0e04003074010762800c0304d40e059050b0a03862440002150341c8014801d41c1e00281d0445420305e803144101b4280802408060328010220403540001c101503210899001d0181007208801030340d034045240000d000700c4045030b00485050514075003e24a69611050300d080008400c8000703429030401c880100068190340c4880780c11000c0c0e05104200e00541e0b407005ea02d1600a0b280841c06a40c1c41d40c0044d160f12441c3c0466180c0d10358105045600255179108101c2c0340d030031582c0c150249489400050711004202c800340c005039100c0c0204e42c070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 247415908 1250 247414658 247414667
    0x5030f060405010c02031603050706060312030f38040e0d05070c0906030809060c160b07020312070308041b1a040915082a0409080a0f05030f0a020304030e03060a0507 73
    0x4130070680380f000c2c40c180005074140d02c0e03180382c44d101c014007008000301d0180309000884e40114011503001e05016600056602c2c040c003d4414a60030780300041c40c3c10340005440c82c50f82d4150304c10200d42e021544400c00d0740882d0101e0680018120740e0840d0313031120b121580c0007041102002643d8940c03249600d4161500d840c1c103403c4219001750302042d0900c8810170009a501c001e64881d00c0d4101d4500d501e585c4910b0115161202d080c0300c00758606004540000c000c1c2c0040001c1224500a030282c440c4a04400d208030600d200700640100010740440c00117000c1b80401c07a1064081030b0031710010300f072141e60b01d1581c5000c4540007285016888001030070080940c592050080154018905099191420307000f903441e60340290410031450540c640685404081c000c0e900c07192031005004010400740b0f42418400c903000300f000c200105006000000540e402402941d110300c180300d414900590301c41c82c50501940024008a00748100c111005c038141e50140a120721034006034400040e035261440f0002d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 247417158 1250 247415908 247415921
    0x702090a020a05070f0f1a0105040c021507050a12140f0702010524030705130203090607021606120f021b01060909020a1707030c0603060e180c040b060405030f06040501 74
    0x8800d10310402541e030407160080300351303400c0303030b4000c11813440300d00090610301720301d08020b4002840201325000390b0800c401e981c6141c03810f0390002c0d20704001c60300f40030009985d0b524207010540725540d00500094042c070710800080c8800d440500d4042810804041300c1c10581e40710740380e00383c814548541084000302e039412102d0707441030080c4000c1c004c6d41040b00c028006d10700e89010b0fa5103101568142d45542d40c80c200140c40040001804d648640b188502250000350000d6401100318001c18021402803440020349000140005074941c1d2141c0c82d04206890304000681082c41264440c4001000c02540c1e10281482035280c0c030403a004103a1601c260b5003102c0743c503003040301042c0ca0311242d080940c540c0311504013501c24080f400049441080c6102c0d1400045900c001c2000d1a02040810b4580d4190003003421180b402e000c1910301d85460040380c01401031041114100e034401c40c4011114603082c0c1110040c5031000d059146025280d00119050456804601540c2e5000e0024001005030034481c60 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 247418408 1250 247417158 247417171
    0xd020411120402032e0f0b100201050907060e060a03020703120207080702030708011e1805010e030d0614090a15080f03070b180703020108180d110c0301050108190609050307030203070209 82
    0x898403610011741d120020500395080c1c2081d9940110229600456010040c60300f001000c0342c1d4040340500c0c0003406841e040b5548140750184113800280540600c201c0018040c1c0244924200b0000500450081d0030101d42a0100080e48800e50521141440200815402504155507400280c018036140100365404520141c0c509044507a1001000d0100b18801c05448008500d001806030103040500002e800034040c3d52801800c3e40da0414004000c220140b06ea181c2844201c0d5903d140c1400c6002d0f01e04c0090300183c00d13a0004801045a50082c3e05006240580140f4036489040451603e442d00300c2c403e095500c0020103c0500002003005a07102480710401c0001200b6403a2460300c6d8801440024107010424020815104000d200c003070700b1423500411107000203000340000341441d00b4022801c40c94092050000b240b4141030048034140c58842e0000d0101c80002c0058031101400b406081d60050f075100c40420008130240014040d050081c0d0007103840b11114010003000c1000078005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 247419658 1250 247418408 247418443
    0xd150c0509180702030f160209070e15070f15090f15060906050310020c0a080c01060609050301140f07020c0406030b0108160f0e1009020307111c0804020d02041112040203 75
    0x10071204550000880e5140c449070041992501d00d44ea80580c845072004a00275400680c030390800c000c05600190308100c0301401c40d00b41d03400c00844c440c0d880552203503000252205100700311b04004242d41c1c06014200f501501d00000324880143c80720141142d074603004071000307400d89080410010140c06120b014000800f003c01000d487c00300002c0d80c444150780503000064010444d004c00c0c203001e0000624a5400590807552032211190740ca009120500441c404100c2c42c1d07201040d00e041c1442620201c0d003040001d01e1680c2c8a4070343c1e50032803500003800d507002c61145180410b440c1d00e60380034a000641c070500000b03ca55040c69542800c08074080e42900b03920010100030030a54041c1c010721f004958410186101030740315064045104100da8005074440c5000000744680a60300c92a40c408038030114041c1e03200c0e006512404405106008403034800214061b01090240c500003440110310340c4020400144081c00004050007500041190174010005404010941c1024011070700031601c0030130b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 247420908 1250 247419658 247419661
    0x10050406050612100f060207031b050d06050603190302070801060e100303050d11040b0304020906010504050a090f0b0406080a2a060e01200a110f01080103020d150c050918 75
    0x811481d01a50444020090001c0041110352944d081040c01030501d088880c8115a11440041e6894040b0704c8101d4081403041258500000f4038866907040d0b600003041300d044e01c0b0843c0c9444000e0400139100e075031325018034031000c240402c0711284c0249591094024040042c507000e4401e0858103980c2c415040c40b00d03540104821005680000414aca6060030100c0e155001062000024403204850707003c00f0305c00060105091441801444c880d074800c854510942c0d13200d2004407a98000d034441c20760000c1602300184a910361542040a2460040c1e0340082c407002c031000004c05540407580491600e0300000c105000b030086402c149400790500100101044441c2540340030f01d21454401d0300100290705590000582c8254070300d41c0280d05503045054600d00000107240c0f1031042c1c12003214035078480211080541007200c94410300c0c0070140c440018a0b880c6809016141d880c3c86001c0f10030711480700002494000e1441001124180c554031541c64481240038070545a50055071b03800c1040e4010f0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 247422158 1250 247420908 247420919
    0x60306090e0f0309061809180c030106031e030c0b0406020c070602033f090304050f01170a15170a030305070e0904140f0105010b03151903062703020610050406 70
    0x13200d010107801c0d10036596039105440280d1260b0b1041104503404490b103014440c03880c001001444041d160002130f1030591019200b09422600b13284001000d202d10682c041c00030311050200032500c5070081c1001c2200700c0ca01d40d114240a141114111000c5901003221071517a80c04202910242000303000a615205000c2e002c54801003120070034090705000d45500310350341480e80c0c20106030320070f400c48101c181d41401c90200d42c50f80c010b8041c2c076010340d0115217030305941e603c070780c021032001c90200d0b5441096172207900003e000741209201ca0100d03078411407000124402108046159aa54a4064003400256190003016180003400c8102000b0001c80d088145941749190541c01c030303510100d100c020040e22400d880c00c00c81242114610380d460040001440090480150f2103581860f5004440c40c5980e800c02000c0341d03c0b010350a0109034140300900010345c0650069107004040c40c280351101085150544001c0c080c0d110440058001006000348032280381041c9010b400c00b190144461030924 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 247423408 1250 247422158 247422163
    0xf030b0c0a031812110703030c080f09030f010507020c01080105030d080a230405070501180605090316060518040c0f0302070204020c0613151401051003060906060306090e0f 76
    0x40c04482014100040e6554000d0003980310751280d0042000c814800882c0d420706000c040c1d0200400030102d40783c82d17107200c401171021800c0b1064036172503181c680b49104513807680022604102c11945810404200c07201f159982007140d100041c855034000316a80c5006080241031000a100143c1448582c500501103541e02244510801400d8071b00070403a5a030741d802083c042c26120000c500072110680b210700f80226508403880c131440c0501d003104c004642e56001140c040064005460030f181454201340020f609c00e80003440c113840e0081c2225000c03943c0400d041191200c80d802100400c0e00010042583d56100098400114040720100001d4201100c0a000c680d9a0b101110405a0004500085590b1581944c48a00ca40c034215520b078030300412940004201410b080d9820341040540510190700b9010b4100030900400c0198056480c0c5414000050f01c01c1005405054031094040b690110f01c1c03182d24003d144954002c61054a00b000c94011203448030781e4108583c202f040d0504851000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 247424658 1250 247423408 247423411
    0x151203031512060504022b11030f07030209070c080301170615011d0105040806070c02011710050f06120a0f0e06010b16020616032f0d050c0c040509160f030b 69
    0xf201000c10380759181d10010301c100304600409441103220740c6100701d504415407000d08a0314070a01d4846121070006041507074403440d07040480180d40c0524400d2005003464031031140c204a860034000860b15465407461929082608040d0241c00d201c18a40940030b400c10910350481c22030711400b5115028500004e1407607000901c007500c0d0180c80b0248410b40c0e40329100700e8000300b00c5482510140d0508040c0200940b0b550740c0e0036030000c1e9003080b540540350500151a8040d0201c280d907114800d1400e0184a05440c0c0d00d0001c0d40c0c000d00a000f40c0650320784e2520420f224034a940400070340030040002400c00c6840044035029076602041c014850208403a00729a100703960503c12039990741d8144002a072070710a030020880001c910b210300c1c0d02015045100c0035003c4903c510741c5148d101401c0f241d101c4405d009114050b90f42c0c040c0c0c0005061070700400052050030104010366405119182c04241a10f00696158005500003004505076038081c010303040c090403031840a980301525680315210031100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 247425908 1250 247424658 247424663
    0x4031403073c120f110109050c01080f13150b060307020d23030c090406030519110f0f090c130e180606010203030c18090408070c0603020903190501151203031512 71
    0x100c240060502641780141d03441c010f00024880c20f4507626101c0d8840810540f8613011581038004500300c0c40ca00c000c554492444844400040459034607104100c8485a1454180c00d645095071038040c0c480000451188680da00201030800010b0401080130101000346034901110200b013055456440017100e8100c4507001142c2d0319020948001401804180c0c4000c1051041c0680c0740200d41941800e414060301445d4a08a00003000050004110f900f401c1a6070020030084800f0040ca046040603410541c0441035a0074040165000783d007401031500a40c00855490702040488685400c0081c1c0201e1401701070092410140b0020350303603002c040d044c50542031001c9450050b61003c00381e8010300d6000140a000c02d820a828081e440b6808044203950343c09203440045940b038081e0007201c0e07034540064000d15492000c10301940100906820860b5155241c07045100114081030f4254090480b05802d815000700710f00c0e0281c121010911070120f005540c0ca010416440c20907003000710700744c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 247427158 1250 247425908 247425917
    0x9090905030c0102040e0a0e0c01090501030f110a1713030804030809160608180a030203040504110d0228020a02010503070503070318060605190b04031403073c12 71
    0x108186492800d42c0200751160b211907202060004e03491300711402e07050181e907801904001351070701e1160f510388038194644c58501013050b502c420072080d4803030b601c00d103c43c001d02800081c0e188040c450041040d440850b42c1c50004140c0e0030b25079040b4001111240d084520110400c40e00c0f1a19603001d00450b100810113070601001c1c00019404240c107008111041c054404000c0c042c031389582002d000e240f001d9900d0300071a21f400003265802440051151003a0350036400645c10245880d0401016100344101680081c6040c00280345074809070002d440240c01e440e50341e0202803030504101c0035207070a0004820456000342001030150360002d00300c81e007202c4c151610b59640e81e14508240e0140034407148040c80d8210020140c81401003680c815403e0746c03804c81d031500038407d95100d20030a100309405000c2000000300020400038048842d00403184e0004019a07080449581f80c6280c100f101804610020f4001c20404007047e1200001c401e806000102100c408010340d211000d00b141080c600c01c0c00d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 247428408 1250 247427158 247427171
    0x1e050702030f190b0901090c1505070605090c0111030f03041e0f140d170a090f1b0815070804060e01180f1a06130b010504120506040c0501050a0909 65
    0x40d00d082c0002e08442402000719002001501c41690ba5600460002e40f004070031440410000401070140c101201d17000303600c000c105424015010324030550b5440d90414030004126400005d007440c01490722400400c0042d210480c11036001604404242c50141d480741c100f0402d0b80902000032041e20341082d0000d00b040032000f0b1321429264492800d0f0000b074031181ca6143c4006c200151004500440310740841503c541404405055400c201001c0080e44082c0000b000205080803036032000e407881c3e0081050000450060b11b506c126a4503580e0940072489008000344102c19003082000d400910f9410445224074059100801090700604000c0c402a10303030494441c5500709420000384d154021140c0391308031a00b880c10700c020101d13130003084490640d4180307040c00309144841c20a1007200054003000480240381c1000004001160043e41032050901020480c0415170694840003441080103240600709401d01751160781040e800380e410080104032a400d5294400007410449080c6031380030802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 247429658 1250 247428408 247428413
    0x6050a0b03060d1509021806011b051501150f0e060406200601120b060901050105120a0e0307060204091a060d020a050c0105160801060c050619090c0e070f1e0507 71
    0x2610301100c1e018140314418440c062602c0301542c01102114400c1fa000c2400071411488030607050011100c050118009480040701411003000e050326040c403c100b030b2046c0360b980d111524403500c0c00381c000c0c0c480d42c40d51109001382c854004000c0c051040c21410075182d215031200025086d84140d0084000b0084c842441406903c02124032403411a40c18059505540e12055005015442070406940c40c42034500450105c0c1484100e4034140c03003060759002e20340f5099001c40203009030080c00b401e81040d038880c100c00000805102520344240f14400141c1e0761860915040c0688a00d02d8ac502407a044020b5840d60329a03e59048420030b0540d040b02503255030080c2c1d03003a1103502402030500c505500704410810400d400c2d1140c4024542035440e00241d80c3d803601d00c200d986543d90500181203502c0b1001098200801e004a5070068560403008a580791a0769110081c0f18000d5021400bc10200400d0102c1280c01160883c825070172071800c0c83c1004826050311907501c0940310880180000010001c0c103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 247430908 1250 247429658 247429669
    0xc0510030e0105040602090a0b03130803090f0d0c020a080d0e0111010e07031a0f0408160c150f03050c070f15240602010606030c051918030b06120106050a0b0306 71
    0x580c1c82800020055880c19007400800382d400111803610075280c4440209041000505a03805a04544600c1d41b92a849507a407a000ea400541407030220300c64a51a5018644100003554408640340c0d20030305070900c1e52041c054400c803079800c0811140c10bc02d03940619290312042e440c1d5500004d1804800e1703041c4c031034100c0d80140b507084103410740c6c0d014072140030003481200694819078044541400e0708642d10004903003030034030b0140c80c001e1905608000e4030070401554060154440d00070384e0106501507440d1a0a4443d410310304035100070928203030864100325090b11a0a5000f01941640b41c40e02045035035040301007215072401480d00c20a520810742e0340c0304540c020060f54800d40700800d808201c280019100220a1040d2801982002d0012429900c02d001d001c1201019031509400d040c0303004a848640e008040c103450422080e1006a420721a61501110045008452010b841d040c1b450034010820304000c3c61080301c0c0e04000081000340c0303030005402d00721448409020b440e44c40e0f010000341d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 247432158 1250 247430908 247430921
    0x60c0d080c04081615020609030f090406050a061d10050a030905070e070203040911040f0e0601171008010b0a06020d0810120b09011d0c060a0302090a0906210c051003 73
    0x41d0213104010100c62400c14031583e4405a070022080d400680c0d12202080b44e4a00701260401c450b0740080c402461068246409001307444802800891920344880c0421000441035100500042103403440314000040807902144145050f10215581d0341b0b2082c2c0540103126150881c410940e596503000306102d4240001e0000c0e100150040d0700a040081e0300030350320b4010740a0792002034a840380145170442841c4c121421036065580404c003451900c1d0804c801e02200a151a05100400c801169017074101c082171813207031000e40c40020032076007400b02c45821262800d80d214000c1c1102e0000b8404240c0008810800629031715041e0140d40c0c0d0340000b00c164403080d5010f9a00114800c0e0940108000204590f2080d09060001c01106410f050090705007190000c0350105a0400704805806041c524000c0080b205141405860912440c020a0404010307030b200d040c0c020358400c004e0240d0144072584040e22891a500b0102c40041600d480c588a103007445514458038100341e200300c1041c020381044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 247433408 1250 247432158 247432169
    0x81803030409150602071e03030c050a0c0626040b130c0305030a17091902010503090c090a020714150a0b130e0c01021c02060f041b0303050403050606060c0d080c04 72
    0x6118180e0a5601460340f40102d008041c0580108000411000e10564102d42c1a85410080440542c41c544003914600014032302528540150700c6407001044120404000501e082da49100140342401843e2040d610802851050080403506200100340c00c2d8422940000b4000d035540403442c1c0b6131500811003200c40e0300081550201040c00c9105940040c1001000108107945582d280d031440000d5440303403908407a900d201c095409510740554454005190310580d114100d03100e40c140240042c4088100f1956090403940000d0b04d4010425004940b8848243e4200145800c540501214040c6c16004281c40c81c07480e80c2d0740c2c071880780f0b40d43c0284103240c0054040301001081c14450074151203000840d07400d17004d0710800ea071540c07130710b0504826141a01890360240180d80c4404081010444002d00f060324107540702c000c00c512010030809005e009600c00c0d03d40c0c5980d94650301d00175003400c1c0000c0203140b0660041c07003400122940420b56680c111180c0c50083c0c22692400d90072040b5010b9074005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 247434658 1250 247433408 247433411
    0x150c0903070b070b1003051c02011e0608010b030a020904060203060114070b0604052a0906071707051006030809040b0111010513140303161809050a061809081803030409 74
    0x144803030102c00a011160140390340c024190765145c44110054a144001803041c2d010080c07882c12550540705004980c407031480085035808000c10321080403420500e03424a1243e9404003040250300c244514155082d0540c0607020f10320158001464014008201401d26500000041c1e6607a1003200d08078244505c124119071140c5848c14103036403424088400d180240c0c54200468418403c4103540e2403117151202004000030f00890480c5215044100456000f141c244a00d40002c1c0d004204007601406120704c094480b426810004d103050900200d0034503540c5008400d00200f00f0900031074090507416030300800d6401c08400101ea210038030310780e500241e51034003040c4105c47c0f0300d0300c2da0500114004d0307001d40c01440610340c60740d89910080d00d0f4021000740600040f20f8660107440305000318101c292100b00c885998030300c007006440b41210113000301d55460b01c050019845a61003155030045220003003002922940c0c40810360320842004146d4400e1010b1996441e65081044502078461400c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 247435908 1250 247434658 247434673
    0x1703090303070f110a0528030507082401050102030904022109010618020906030a0b030304080a0803060406170606060904020702040f020a0f0807140702010521040201030c0c05150c0903 81
    0x52032040301c1007a2000303c60b81089051050107919048201105480009140f0002c3c140c0042c3c7c2101d440036550311010204018010000114600384000c000070910140642074071001d800c80001346540b01007511200e034030540f0050220380d034000181c400245c2d09690040c1c4c1c40d030340205030424000144880100c200194070404c24009019040030701100d218020721919608560103610913401806001900044c09000055500d4255000310380d41c0c0c00050203880c945a2502650744c1803d0004a003507440071000070170b11059090500c220380041c404089042011584044440e032158000b0f007403244600030200300f815495446074100e0300015070040003000309801c2d66090202031b402980041c3d0114041c540b4210205000c0e4154078401d0f003040c2c2da00800e000b031400250b1019000300f18245e041140038001c03118105d112410002001e140e48441700c00c207160910005003629003055a003010000c0c1d602e01e00c00024000601c2d104e0340210b880403a10513540720307400d5802d14068032010a525100c1c007074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 247437158 1250 247435908 247435913
    0x80d0e0c1003140f0a0905030c012301080303151906030509010c140f0a05070c14030f01020f0405061c090b04060b040504030e37061707020601170309030307 69
    0x8800003814415510400180c1260809604607440150324080c903085000018440c5801c0310401617102140e19000100c180f541e407110340c41e54020640c030001e1603566401c182d07010000d440c4e180090031031000c0400e005605100180c0e8681c08041c00d074404c100e4074102c4da031b150f55a5850041158101c0f002e01400700b507507070b02d0f40140035100a54901c1c01552030f00c85481e080034460000701240c1c0300b901003800d242150302000c0c07400070740c040081c8004200041c800360b8000b503d21031034000101041044000594120340c201800d0202c40040300000b60720401c1082d140c048420103480c125002281e90940325000202c00060000720780c0d10040c1400e1500b00005c00300860403540d1402940682e00400070080e00009000440d041602c004d40410b007040c4202c0728505c3c000201c2011001c1e40c0030745580c52249940700c2000040301a074450010700b050320b4284080c0d64004244080201a80726541d03207424a4030029480b81410b000300c0c2d51305e02d0303078541601f4105002c00440b401c0c0d04011b811030b5a00e180c1070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 247438408 1250 247437158 247437163
    0x50d050c06280e010e101d01020702280e010e01090f09150b0a120803010e090705240c0a03031d0115030809030319030525020706051602030f0a03030e06041e080d0e 72
    0x200c0360302100d441510f003221f01c1020f0510a49414076400381034043d9000c11080c1c0b405002d800a00043c014010041c0c002c80c511031481601402041803000320211075040c02804015a0031b541c0402d82c16500e407040e0740c004120f46250862003078800481c00691242c0c4040400c1e1641001e030000c3c0ca92103402e83c2003204000041700118100d440c4025001c0f01c64850401c2c40351101154428560b003c09010442011182e03800c0740780c141a00344070185840c0c911008030841c20712030103110170f40109589512400c0d1113107040c101038440e81c1c541d01c000c20154845102018180305180800341484001103211212601e003001103426840103203880018000403940001d011304070840b403003003028003480d410304021030301d10307000340b0b030b4940c4d01d07001740c0079850401004840c81d801040c42044000c080074520800b6881c24440010500641c50241c801d00c0301c0d90501409603980d03c01040b029900030400c0002083c05000840d000396880d50085821030303c42d041240d0345014640800c2c90303043c901400c03484021b000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 247439658 1250 247438408 247438421
    0xf0304030215090706180816030201030b0105070b0f180a050601140103050c27041e060b0a02060f060102010207060c170f0c071b03050d050c06280e010e10 68
    0x941c201c0b42002c80460b04070102240644583e06580d20200051000ca07010349100244040e0515200da070603a5200046450b1090040074501400c0c40c0450a00565915020b203248001c02820031074a440600c1ea20710010250082403a00040c5251010aa01181c80e0b0740b43d02115250078110380d0041400d050942d1103150a12501020140000d00c00d00994064062103205800c00b06405050040c00c9032107100030000301071320010031401994103042550312807062246040c2c15222274540c40b1007454074030f0b00f01c80703054100546550046c085070107a15070000b41190710412080111000c2d440c4e10700140e0181c000c09000414590400d00d100304001d43c80351020062201e2513703100b03069100c85280c4040c4841c00d456100000c80c0400400000c6030048038046080d01850014401743c1d070b503c0c0c44d80f5051041d0126030000213880040c40c204031403c10011150843c1220541d41816290400d040b80e40442d402c0103e0342664423211310102c038440a5006444480d014019600b061050002650047c0803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 247440908 1250 247439658 247439663
    0x6010801140609130f061a010318020328120305090c100f0e01170112050d0302030610110c030706080a1a0a03020904150204062303040b01031104090204020f0304 71
    0xc1d0202203003801c0c503040141c5000d6440034010003140d03103604081884151413800c00340e49113401c00c001180016418480c0c0c80701250510009051841550001401e40346070300400b01000703c92030959030241ea00400d0b0703151036060700307100795801440192541d1820740c002107002d001c40c940900105902a0160041071060301d0500c250781d603440044081205039807141c4100340005030f04124800210380110000c801c80101410402c80c030815103414a083c21200343c22400c8511191030401c400c21000700f05120b20001c00741015811441c001c0041092089446400c00812101d00716031054258140b010b40e4140e1009800d60b00d800c0e40310f04c005004c1010a0f101c8862851424001d6003030322000701d04038402c17800020300b44040e00b0701e03640820440e190b024006a43d0010b6100450700d0b407400c030788018130040c41c5d59100d420f2610b51035028040c1011101d140b000e5000d00c100200000105011142410740e036000340b1048544c420703140410010540500000e401074030000b00c0103100350045c000b9600c00c61 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 247442158 1250 247440908 247440911
    0x20c0c0a0608090d2307060e0f030f09010c0212431202040b0a0312080c0306030a060e01110403080d050a0207200118090f05060103020a231b06010801 66
    0x560394201203030007203011a40050b05800030b0a849944031705c144521803010401181840c5010707100750340c040303041e40291070031030307410750348621a40b01c4801c00e102420800a07840051802c0c0124202e0a488500c0b8a0707a60a04100c4030400003400c555414485040c0c3d0358192084a03420ba0700307207451111a1b01082d13080d04c04c42c01440c0e0864443d00e007503200103070046521a0360081e86803524000c5208490048412640f2546030000502c1984400c0b000c1402180034620840804420b020040d0500390049c1c601b10014008008000c460f440c0001d4400009512040c0090150120000a4014001650381000101001030000148905c660161500100c040c10821040c0c803030141c070b1002c91065210041c000751900861880d404050001040806010704045c5001d84201d20b441040301d0040c0c1103100500e0b91404082ca440c030305e900c500e0340d002d6400e003800c5161000c1c011010780001ca0101000c1861201c4811038500904040d088d07030700d8040040c0040075186441e0300c410352200424018041c096 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 247443408 1250 247442158 247442179
    0xd08040519031809020c070506030a0603240c030203010e220507060203041806080a0b0406060b030f04063e040506030a020705060906010e0402040903021504110102010608150c031009020c0c 83
    0x441e0140301b264812641000100740c824544014040c0603000200218100341c0c1c4c405000010503519a12061000240307800380e911400218051803ca80d03000e42406d04241c818801802110075195840d600598031068500c03003540301203500c8501880c140c40c010031a0240e443c00150f46a00007001d00150b5021070a154500101d5031400d504403034441c0b0034040942c1c0151643d101040701a04503a07001070250f400850b040f41c540720401407c0c0d00c00d03507070445020f0080c0c00300800d0125501c03490440224248098041c400640101c41c00c4440120709146023000b1811a003500b900c5010466000b032001a19058481c90012150340c020f403c8404142d03464000c200002c1d03001c95002c40d00764182d40032204100b072152100d13000d020080203c000120203500c00c59484e40400c44819000c144680d01c107003c03103c600800b190009094a82541c8015801d0344078a00c15241154003580d0180c0c05641c0c0c00409480303030b0f5080d082d1500040c565020001e251700c00210014480c60109902c001c0381415111a80752 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 247444658 1250 247443408 247443419
    0x60c031308071511060c070201180602030417010e0d14070c0305060405070609063212010302030c04060b070803070c020a030b0f0f011d0403030204091a1203030601020d080405190318 80
    0x40c41018140c2c0c8005070041000500352054006c0500f82d290b00614003645080d01c0d11401e2162a0340c1c42e0084800340c0d1001c14100b218420145c2a0407a6580b410000c3c030041c0c11710003046a940000074032500034086507000540d1420100b00c241c03400c05070000e170382e041030990341c0c14034546550082d101a07526025a900c00b161040c060780e421000c03961159100c1c2c00244145070382c070158400916219a43c01200a00210801203d9000e80801100c030a204140c80d4503503c101890111880c2c2c1c220300a038204201004520351000c2525035250700441c000e9a80d941c2c240c4201c17090b40c902c00000750b03c600341c00004001c0c031002141e42c520810039000c1e44503541d214220340d01d076091024071901ca00b00485103403081c0e48000781d85c0c015070054401e0901505150322000c0000544280c22180b10f80800d01d0343d03485a00740f915191000140c02260081c5107107041480000751078071500210b241c248074203800402d041100030404104e1013034103045141c40401540c5401410b00c0160820b0940d03000b141c1d54041803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 247445908 1250 247444658 247444667
    0x1210061e0e0c030c0d0501080c010207060f120b04064a07120b1005070204060f030201090e04050c060a0906030b09070918020f0403080c060a061202060c0313080715 72
    0x644040c1e840d4494035689101004409510050120b07100c00e50038011380316004124005c0f203000e40740300720190600d00900c0f00024649080b59104c1420490003e40c00719440390040704d09480f80c1420300c00802c5042d1402c0205000e03007a5036120b20809101030300d10301014810301da8a000d042d641190640e03006401000c241d5903070b844910840c1482590400402c1d0300c0e900071078410140303000c4010045800b410354000141d0303e107102c0c6c0c20003011031800500b0400f1460684102030182c98400c03e41c0b0342071400c2d900000c0407640740c0d008840c0d103c0302c00000b14061100400c040088004006c00a40e07840c3c41926006151150511600b00400c0c2441003400051030300740c11840c450300141c3e4890440c1460700404244115071450004211a0301b08048040d80656000902c083c5000c0c400c142e64032004407042500d40f14006048130100707490600140041c0034030707000a1000503012100320b0784420b0380415042c1544100c201003c0ba801c1e038440006145240411405c0441d4444a44030540f00045071042d036 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 247447158 1250 247445908 247445969
    0x1c051612170702120f0607030e0106140f0d200406050402030702060a02130f0305030c1504081806041d0709050f032a100513060c0201020a11121006 65
    0x34500c0500100ea001c04a01c0300340a04205070008080c0d071072401080c002541012000110703800076402ca0010417203050b804d801000003d4000100801120340307403c282c0150352480302d03d49849004280c205d621140d68809000400c2604401c040300620001c44400340001282600039024500b00799001902e840c00784285c030300c2801a0780141801d661100000c0000f5071280c0d0940c010b503104200c01080d00c4552442d404065032007600156680e64051308103038944444150325191481920040100090b40003040d03508005000c4005e141050180d000100c0600443e0010141d01c000032140704052494405500d008003926118080d0740703a1600140465412902c1c1406d4056200390004810350554008500c14520715044440c4002c0e00304c00080c8503040218507040001e00c2c00700d507202c0f240711480007280c01000903081000101c00030360f0010707440c0c070395607040900003081c0007100420f01d442c2c3c08000c11803114030380c068030440344440d440c02d4020285405a60b0003001529900000d1804840c65403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 247448408 1250 247447158 247447163
    0xf060f1309020a030b1c0b041506060302030f0115201018020f060412021309020405040b04030324030809030a12020a1a0618150303071a060409030f0e1c051612 70
    0x1441b5001c16407900c1c0020700300a44102c400d5090746107041307c03070b20080c4201c2000e4903ca9902607901d06050110f4203e02d041038001c203031501e0f001d40c068008503800280140c0640b0040c051118441d60030003074942007140c1c0c0e00940c820181001c1d000010b1050400301751030202c0c4200c0d0341c80c001c0b20f45c00040c00800c0c051401411240c0180d00144c00c05032404e00101811111100000700f00314000f5400703c1c081d14825a130840f040100e00d0144802c01d03806004020004800d001d20300307645080c08160700d003203040d1407201800e034401c0090807107420388040c003540d0310b00354001c03401100c00301490f80020342d2540100025149481900122100c404102c1c1031540540e10050604071006207911958003108405480000010410b00c1808200e4400307002422015019846c0c2d0501d4820005050b58000360041a040c800c910b4a01c80a0000c0e0700045a5031040710249800c0842c001d1a0300865041c02d8201c4241406504a201d401c00708000040c00710b0fa03a6007140310701904590b444241222a54404400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 247449658 1250 247448408 247448449
    0x804120807050307210c09080708011109120c0a0b1305060405030304030624030b0106030605041b110a050319020f120d0203040602041d01050f010c020f060f1309020a030b 75
    0x210b250b2034803940e0441100055908a01701d0701500b001c40c1000c40720b210708400040f0760520320400c1221024031462004001c2e260003440008240c0440100074454071001c54440e0303c00e60800001c1110070032202d100400050864902d540d00e52102d8003580d00000d010784514001240c0c0418542414410390b41102c01c05070085027401d0a59842d200507092020400e11828201045500300ca2014bc0c079850085001c0c075000246941000c6002b410340303015070800c81c02203041c50004216800e45c00c0204094810301d00c3c1c0b80c110803003504a101d080c0352310303074101074805c0c8000714104401b8003c519100800032865021107446040e102c80c03a54880e0005603091402c0c607018052100c104000750003c65000307104140041c506034036030601f00100d44041c01410040d07a031010050040d42401e41110308404000d00713001c207010040380c1c00501300c1050520110300030135000c10401c082c58002000d03621600303001d01801700210317250050000250001402d01e400a8180560741c11203003040210400c41800050a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 247450908 1250 247449658 247449661
    0x30905070e07020c150d050f2502120c0313140604030813050d030302030403143c191209031713020910090e010b100c080c010c08041208070503 63
    0x9904950000034000c070309601903900c690031941c3c0c90f0010500702911244e0340d262903a07542021b500c200c0300e00800004001d5042d00901c20051000400d298481041e41c090400c4014918030890404c2d070407a0072100881404110507404004c08000340c01e21706204519980b80d2956484030040c0e101e000a501a04038008110510120700100002c1241000301c5620b640400c2d070300c0c0003240b07020982c40c0d07080c1c00180d8040248403c069001c00e82c2c00f80413410060613030901c1c2040010514181c44000820321405201e450040f022050140d11030442020380300c100d407600c61f41341918145d001840c6508000030348848800e64690140e10400d440305030075607134031121f004500341500c1b843c10010b404c0940c8c0080344010300e401641c501600074410003861400084292900c24010143d4840449492442e410020700703020075100d080a00b407440c0d40e50b00d030080042d040743c141180d0b80c0c8510380d5440c0d029420500c41007142600009a540110b20820302c0362a00d15201c0c00441c0d01940656034240021300810 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 247452158 1250 247450908 247450919
    0x5090601151b1e05060a05010302060a1b06180b0f0412030b060c0d020f0f1c0c0c090903050414060712110f0106080604020a05030708060408030c0702030d021c03090507 74
    0x442c0e501140c05400700a91a000b46071149241c2601a00c21940c0c602005549103007005030500507181c10900c008018001541180c1c001070b11400f42d44154820802060700d5004015400c7c81d051000d0707504450100305c5000c280c4428850040d42d41c1050359140d0701e80340495201d450000c0a43d20842d04209001e0f0780401c031540880240155101c090340c4480140104040c43d038062204440c2001103800800b581900701001c01d091107000c1d4040390164205030086003104602c29090310180000b442d000c0400403942c81c10001c90300841c0c02154825160580c0300040540200007002550170014117482401d03510b0003004618442c209000b407219081d011000101341c000c650700c5446010300810b40b400c8004182800d800c441941d840b036041c5603c40c034284419800e01c08610409030070b0507806400c40300d06246a09994070384c0508004e00004000002507803080300031060301c10041e40181610a0301030b4100d0025540c14002259204000c0d581d40307080706050107849030a4003607510402511107185801c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 247453408 1250 247452158 247452167
    0x31704031713081009030306050f03060a0c020f030703020714040203060f0112021b07030c1706010b070303060e13230a080f160308070201060b030c0910030f1e0509060115 75
    0x11014642c010182500400c1c81d02051046884d60060b035000080c004066003002000e5800c564041c502403800c1113800c0106440c041580c65124030150741c041017401e84103c080749003a449404203801400041514020590702040c039804607092265802928007501c4100400c0b03101c03c0c0c604540c00342805a0120743d950140c00002d0150600103401828084000c03131804441d43c92408a141c3c1d500107210510400130495030034405802c03890000c03400590000241a43c480c07041c041e99828a8000c0f0b446000c0612030b42006e00501074102c9089050b0609421100c021589a001111402c50130040006500d201c840380303580c6103052800420402e0b803079440d0409c59500c100810807901008020014044204451856000d48a40e9481b2030a1510740350080c21a149074000500d056010402d100c040705221090303070b44c240001c84400d2200040320742c055000f0801c0d0f10f0b9445140b4145042c001072076101c20401414942900d10611151380d60f92081d5498142c01d0280700100d144c091170725680140b04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 247454658 1250 247453408 247453417
    0xe070914010c020a1205010f020a020c0d0c080d0519170105010507020a03020a0b030910090f170c0f010e010e0a0c260601030b0403091d0a0e10020f040317040317 71
    0x181401d807080e0900b60081082080303217030041041c0310894000340c010407000744203104141c81b410b88211308142803420000d498820002045123303100c076040d100240301c0d135103401c080100710000c11603518100041018010f41c000c681250107180000c255400e03600c2c081e09800d61602c0e000300b28071850b6030030a00155a250844802a6008205810048010b883d040c12180c05480200075480d01c0f4075205918616010012591403031075030400c152440000c8207446100703141540b0181480d4964000d46015a0364043c4400001d142e2107440103880d04000107511800d40301a54000031300041e00d440d00400d60700c550196006201102251040044d400c8035800c00744291024240d8081004a004000d0315101080c1c0050743c01e80c44c0304050004141e0005404030082c52103000020105d04805a529010500201161806a2241008000600c0512241c054070404250454540c0c5e081d011400f01c90308603000c115825482e0044044060280360291400c0700ea0040807aa03c0f1a44070011301650f810 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 247455908 1250 247454658 247454699
    0x9010210020f0f07060f061d0402040203060607120305091c1b0606170304050405010512060402010809210306030f032a0709060915060e030c01030221010314070e0709 73
    0x900410602411110080c408203004180c01b15904014031024411240e440e4440348584d031015200619181c00e800a90b0750107034040340c00503140d65a11005c1120791058040041514030a0603c1522540d0564081402501000700301c520b000a0400c00c404602144104480400c40b05a424119840d0540500707500c80e124940204045903140c2c00030f400c035030031081031100941010a05011a0030a4815140140f101300c50507072005480d200117549452000c0c101034104410000040c90700c801c1040280404504005a0341444210990815a0f81c00c292111407207401941d025455100c40001900d100e111102c09000d980c02d111003003a2245860780c610200c26003d90940092440304611400b4000c007081c40004c500703d0f02c00501c140b00c01405030400c40034401c0300701c501c3d2255140042d41169144080c280140d68400c4040030503801c10001c8001d04448444400202c104010002d007801e0240b0356100b103441007911908885000712088440708009100c1100400440e000600000701580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 247457158 1250 247455908 247455937
    0x902030a0203030708031609060c1b0f0801020406031404050712060f02030703240e070e0301140103050a02100201051e180706020f0c03010504020d11030708100f0b060901021002 78
    0x115507400300341580c1002034244c3d50070034044104806500c00d01105030343d049551500c0040141032070009001c3d00400300000d421843d03c8403841000c510891080b00240078442c59900500790354040c814083d501071b004510010307042c42408449081401c516074015944900500202410403040380707006d0394540d5003601c400361184040300d041030083c0b00550151601d83d07008260112113000e200e021600c403d51140303041c040c0002c20000e070104401081d40000107403400820403070304100020301600c4500075040041c1c03150070001080020000341e9004080c03090394920900400e10304160300b283c0c2d00f01c400184034581c0f05506103401c0508a03006034803440340b502d001100800c50710074524081d0203410071800740e401107041240719031040100c0c456a1714200c1c02445249070590201c3d070b0880b0720038070043c44480d01540308030981e07a0030301c9a200548060301c211000e032224034050b94040c0003444d44c03400c101803500c1401480c0e81003c408440300c0c81d2041e0021b01e950b00204020704001c0d8019044c900031503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 247458408 1250 247457158 247457173
    0x90b0a0b030c281d0d0515060d02030709150b0f04030f020109120c0501080a0e030f0d0623040501060314160e0604060804050c03060403090e090109060e0319050a0210090203 76
    0x600c3e1188094580d41020b1340ca204100300c0540c11480342c503e0904600303118071605001c1c44002000025180d0b003001001e2000384590301c4140104601c8507568074025407502408001007980c0036642e200c0314140c1034040200404603a40e4480016a10680b0300310164400100406c1c00441d5000243c00d84040c410704d0030300303a60f99031400d90850740d0841801c21a03000007010000c01040d0f0380b1405945e000759588004110011030030861540d00d202e40201052030010108810450050300d43c03218000300420542c800b40381030380c004080020b1a101071000d1042c0d140500100e4032034800d00c20154864440c02d640c51503600e480c400501041c0400300140200310001170038108503140c80300984001c0000781c85400310303401d09103009402c004089035414044c0d0700040c00c010220340d00284020890303180700d200304569140e0f106114050402c01c03501400d000d05040c68807904000c0040200800d40c40b04001001240c1e00c00412150352040440500069001e03184c9d420400005601180c2824402070891700003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 247459658 1250 247458408 247458457
    0x60e060708070609060f0209010e01120f021204030914150c0f0714010e0405040b0613061211131e020a1e09170303010602030a0813170301090b0a0b030c 67
    0x190b6000700400c407500ca8a80c000c200801034103002d90b074904440b51005509103521640000c2032001102c10141c10484140b040c110303080d05a50042401c082541010b6669040c0e00038a064040410381d411800126100e2001a4030440b00e40054031a610040122a95100c01e0941030a9130700007088080250003400d15510610800f04400c00c001d1018501414101c80c041002402c3c03d0344481e8900d0095080c5410400040c0510b501560f0000c021210480030300c1c4200b02e54001410a504026040101c01200e807041c0619010414408031044032840404808600400c0c00d48400136454841d00280c0c2e00040c65000242c3c0143c40b6095031440c080105488559402e80f04035440913034178000c12200c0780b0034046264010f05010082540200940c0b4652420b10000d640c0d201c0c2134402010062100c01045864000c1c2c074a84442c0c64004e071345a90010703101c3c4c6030740509500c02e225141580345010b00759141410030614a4046541148030b017401d43e034400c00b844000350f00201648040d103d411200034030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 247460908 1250 247459658 247459673
    0x30a0503150a151103030c07030c08071e02091e0a0209010302360915010c0c03050a05071403070321180807082103070c081b061014030601060e0607 65
    0x910f1681c441c48900550548058079800310380b82c0076222504200100b0041e10b48040865400582c10f24000300c6826a6040000b014020b0190040c142c0000414244000620b281c100030a02c0c000c0307810080c1512240016401c040340a0074065442c6400800103003030700b1382036010f8146505c0604015161121030003622030310414003405110351444191301100140c100005034803005d0000d88050260741840ca071081c0b260110103206904200c0c11039125800c1040710f441c0e0341c0045a014048403c0c092151800c161110310901a20004c202c1150504d1200e29001a0400840c0e4120303406400f4141c01d009660b020390b41102030070b1705101060206c4d0000303d04400c441070080c00400083c2c000d107800d044444d42000d1100d01c2d0481110444500c4551039140a000c0302c0c0c009900341816524141549094845400340800040c4442507174031280e9180c14000c07650a01c11030204540c4c05899403560008a000e13001018031a406900c0840140702c054003503101c505032800c1c0105010f00304811079880743c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 247462158 1250 247460908 247460929
    0x11070b15210102041a0705121e0705012901050a030e01020c0a030c050c01030b06120604060e090106060207080a0b0117010e031918081f0f05040b10060203070302030a050315 76
    0x160705a41c00107041101480c100b0b50000014071040c42c03140b4003049500c8440da01c40b6060300709414003000041c00051106102014106e00f01d401d1030050300c400e65070404a00074017491100e071410100030584107041c001c1c0b8903a00040040c0584499080100344d00089004001354481d030a034943d0700b0817480c1c040060070041260154803981d1841d00341800b900d4001c0c00c00c108860b08605145c2010202130b801c0c3d541c03009031480901c0725256503016a071840300040182001c2e90100e0804004a0144142c108043d040b500680c0c1c9640c0071500c05994071242030b69143c034008006000345030100010b02c0080700c1c900f40181b24012000000c606501d500c14400d0071503210089842800551503c0710030724a400c100342c88450005048002801c900e0700400c20313180c4900c1d5010310302042010105a10040c06030f0b000103030301200800c1c01c0121b031602c0e03d001355681c0390551708022400000c25000641ca4400001c45105903410f82c00303507051821504c010b5031590009410507007407441ca00110115501c07404c0310107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 247463408 1250 247462158 247462219
    0x30f0901020c182508040204090201180e01090b0102030c1203060111250621020c0a0f0609020f0303030c0412020f03010c03050a0e03040f1e05030f010c020111070b15 73
    0x800305041800782d40c8038106900e80141003034038207892904504d541221503e90700540686003c01c0320b202c00c0c401240d1460714285d4090a52f0b00302d00010555890121030141a24600c0c0010080c0056080069a0f28042c0d10300b0300403c1d41c4003e0400110300a05009580c1060f4181480c035030324024600d1072030400c0c1e8080c04601a425410a2003e4100051190140203000c9420700b401c014501601004a01800101203604160000b0710700c00080c80c100003031a511500324051003031491080c074141c0d014005060041c1d02c52a11400c2e011002d20740402243c2c000c10840c0c60280c034051804091604500f01840b050340c3c0701403442d0b10b00145490070300401ca8484d0940c0e60000303881c90488a00c904407280c5080300162940b05000a11106041c014118192410301d54085a10440400ca102d070040150300150303050b002d0f00c0241c015862054000190018094000707010300d00000048103032500580c4805005070790400042606485035245440c0100b4000e8258100c00c8004641080d03451840081b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 247464658 1250 247463408 247463449
    0x90603070c0309090c0e0d0533060901061707050706110909010605040605040603021303140d080a05060a0303080a0b09090a050606150405090c070c06030204050112050603030f0901020c 81
    0x20350701003503400b4006002828003000104280030103020000d00f03850a1b100c29a00541c490f000c47d10610204119003c0001c44240004030151500580d0303210110712407032840041207250002c01c1c12403034009a0b990603182640e83d925034405200011200c03804000d801c030014880c0c00c00c01c2201044060044561550098852590703c14905090110104050303107c3c0c030400c00c0c10f0000303202d4181e10204417002c5442618001d43c0386c02c8500c088070341001480e48010084030b11481803c40580f00841d030452184a2030b120703442265142004030041d12011140190700404046060001a01031200150014018400050000c4c010804220504030641f0417030341c1ca0748404004010810300304000c40e0700c00c0050362105000e01d02900910402c1c052801020311646030380000400d40c0311814181d9a00d1500b1504c101101640d981c4090300941c040d0007101d0001790210150104010079020b01802604058000c614020b410004a002500001d6405045001382d00840000c0c2c0c0c1d80e0342d504045505150700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 247465908 1250 247464658 247464677
    0xb030103120f080c07050c100f090602010614060c100905280c050d0203030d02040308040504061d060112021b030405041416050703030603080a0c060c140301031709060307 75
    0x140041c07540c0c40100000308001d01030581150403070b4400380715038010301500703590781d100c0500c0e10f0003900f03049501c404560029408800003448503800511030380040307825102c0c103c0e07107a11204100d0030380d64940180208032a5041c0040801d0600c00010006009541e00740c1c0c100c0d400008010050b9040c4c1402942e040d40132004d807040140c510a8440500c40b0498904409604259101e9a107a500f5218140c450000c0f1078040b070554a0a104a41c5103524040b41150703210707101d25180300c2d250001d02490f4012403600d84003042c0c80c0d002e00841395408040b03494001e056941e11004503082c0901e03581a01d50950240055464050620700c5643c481602601441d110b90070242030204650301c500c085038000c070b076080911005d0302ccc6031508143c8540da43d142c00342e41c0b22107034101600941410382c0000e0001c1000035141c640ca9900c00907190f00d00303114071028000e0710110a01158545004606a0803460080004000041040400030b5203418400d200b00e003070805000c00503015030070850b041c00c00302d1013000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 247467158 1250 247465908 247465913
    0x230a0f0305010902041206020c01020702030d0306141816021f050f0609060a03060207031403040501050402030705030601141201140702030414040c050f030718120c15020307021c0c0b030103 83
    0xc440c050080103404504103880c00382141c40d007200859007e0b1001f6070000d01c07442e000e07400390125042c01d500a130484410104031a401001041039100da00c07249030000c3d100445031714290010a00ba07004116482010b0748404403440410320360500001c05611a14142c90806075406036032404010f0041c0001504d4984940d81c4090324000803c1075204404190401c4403680d2504010303016240c02280058442882e8907041c2d5403c0d1320302d83d19004440c408801c00040080541126104a20a4095880c9182c3c1d070b00502d030740d401c028055552005070031051041207050a03228000c0f1185540004905140b43c060801103207030050311000c0c010303000044c1c103004440d1060354a241c40c44040d20204040200844024100c0c0140034000e0303c030303680c0000401c03400c0b441400911002c1525401d1410103035501c0c180d103000103200140803240000036500000e00d91018031903559085400da000303107207408151b03800c201010000c1091000081160440c2c0d40201e80002042005490b414404656950450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 247468408 1250 247467158 247467161
    0xe07050a030f02040605072004050c0306130b13270b091e03030f13060f0606170103020a060c05070906060305150301050603070513090f0b060103150312230a0f03 71
    0x100c1c18082e0540c0104410003100d0350040071100c0140d0007805100700d118070102122080780341d08080c40d80c02404d02d000c5c0000581c551005501928013210f0036540030010781040e6040e40d025480d0207a129604004017003034071006800140c1030441201b8030010000200c80c00303030346000a5000546560020300e042115a0400300003031580c498650540c0c0030000300503a1060303036910008110301c0c0340b94144000700d200b038a0003607404031110ba40042c05000c080c1c3e90280401c0242040d12900303002420203440038208941c0603e0f10b1341600c0c1c000d001286000c4c14401c06542100c50000304403194401c0c51800501d1322042d201d0440980030994004c0ba690a025081000700040d0040e03075440703039241c1003d010403560001440c00490300181c1d900d08000d4440420380d001043c3c002000f03030440382c80c04400b200300042c05e04001e100d843c090324100b025032824084103c3e85840c07400014020a0b12000141c00e4a00030031502003082d03d26810421420380421100710795810890384100401e000d00c1c608503029415 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 247469658 1250 247468408 247468421
    0xd060512210310031b120308070e010509030a020d020303090d1a07050c0606010e03011d03120a0510060309060b1c0204050f0c0706020c1c051b151f0e07050a03 70
    0x480721421400c200f411896082c150f0700c001440020111881a100c40030707404044000c0540c10010314402c141c03420081c00c000001c1703410380c002814001000803c0c0d8054000e844a8a6019006000b2440607600344000b5003500038042e80c0c58030080c8004041c1e0b80c0ca001c5195020f911807188452540703482d0000760408400504907a05008090000c1800d07140e0005907150300c44824030b004d403003607030312440420700509106119403546c1c1458030103200c08406c000010255582e04886860a40d0307592441c0400329101640c19980c140000b400410003584260003841b59103006043c0050f07500d00c1c010014209860b800d5074507081c0800c10b11520190700e0181300349039011401c100030182618007800c6408882c803c520004010503804991400b01e0b500421400440d25807400352480e20006408010300540c01504004010001144420442030004100803422442d1191030100b1a1101c1e00c0000d20b2200c0e406510798000103a403000140a402c41a01c01d00444254643c6684c0c3d002c4c001004007a40c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 247470908 1250 247469658 247469713
    0xc1f0306060215040201030c2304080c1f08040c0b04120203010f050609130302010608070905091908040b0d0e01090b0603071707060f050d1104210b0c0d060512 70
    0xc01d20300380f44081030480a4560056091074000748002d1005c0302079070f451301600100d0620101ca811442c0281d00c840000b402590044021120b03c6613840081201003a5034030204845070403607000c104942d50084130b0391900b2910441e03585156075140c025110b819002a4403010070014001202c0741541001c0c81401500040b411061002d40b50400200d0302c2032901501d0303810018072019000c1c003131610039400100070300900426901400d03601c1c4082c002070001641c000320540910040c0c0f10b0010080b1207c1c40f60954409002800c241c9412140700c0f464202940d00f800ca40d0700c8200380f2104900a110340301c6034038402c3c140d05610741049402c0c54030f0800c0a401001456071488000703c1c0d02c3e000040c81504561481c500a00b0700c0701c64143c115500d00034070a910002030f040006001e09000c0041c0508140d50404d0103414800003103011184245402c41806040f0300d40307100101e8003596441c0f004001c074a00280020030703090303511030110b42903c0d804910320403141c1100c1d14000340d08000140c01100e45c1d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 247472158 1250 247470908 247470913
    0x1200309040612020a0b0901020109080723030403112101050a050421020613050307020901080a17090108061201240f06090303020d030b012319050313020405090c1f03060602 76
    0x18801d5001c101001740c14001d0240c6090049124003184e8402d4001c050740642c007900a0b0340303a0a9901d4205129807008003084280392081c911318203044000415a822a50030100d0001103006103801d2207056510b07980c0d18284402c0307400c4502e00d100024019540a00700745500060b00e80380034107081400c59040f2101a42d59541180e681854503400190150880c9802c50403c000d00ca00c1d240485c070b50f00c0b42c41402504420000000141c0c0c039408145051840d000e0801c0d00c0c9040b2141e0009031580c4600c0c02c802c3d000c44c1204001c107009090500415819001101c0001011480418008100d48080d149012810b1a4003000d1000c242c89094200c000e2210342400d003c52811964069111100101d03804c0070190b81d9062024142e100d007080c007802484104190f06128a0008a10140d60103400c06840004503003080e000030324030440449114080310103002883c0c3d0700035030800000e00300c00340c9000b00c28810094003c075265150340c0240d021000c0e43c0915000c10364260303800b40071355200340e01100954 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 247473408 1250 247472158 247472189
    0x801140607060b062503030506030d08072f01021c0605011430060306061e190b03100602100b0607080904020706090606081227012003090406 62
    0x1a00d0300c8003590701580d441003000c19101c0c40c140224005005081451100c0d10410120841e40140c2e00d20381038510340aa58284280e0303650a0506507510b070742480c80c400061240c80000c0313000c2e105600800b800d41d0316042030b9004420000800300482e000c0703062074200b030b580041c1c2d0302100054505441441e240b001410701080b0318240c0007a01c9001010200d0041d40b00c0000c407034008812501ca4490b210054498000f1941a03000c0d03c60a03105041320340501a1103690085801da24102070580c4414025050621403e0514400c0c052049120203c80019060300d01d8089030b40c6124401541c800d500003030200d08050701d0404024986660b41c021064150f1429000d80d0742d82d187d003000c4820340c6e500304020b20390316182c03480460000c0c0328005016016501d011190f800f00110ba4000320121001780044903100241c038020484a4401c1c050380c0b001c844c103000f86080403255402000e031601c183c1410030710b07100100a400c6031090010b0750344010ba86c0d0400900381c403143c41c041c8940301c00b60030a0903910206 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 247474658 1250 247473408 247473449
    0x140109080622050102030a06031106120106030b03010b042307050a091401050403050615041b02100c02010605090109091209050303090f04020d0608030304121701030f150606020c010801 81
    0x115580640640e0201d880d0340401d888104000c0780804510f0f5112000319501d20304442c42100401050108480e07113803440c4540c0090380303401416a00212110903040210b6441c2120940c024032241058076010b54881c0c0e0801015660340c0b0815001d040c1d4040c184902d5500ca1f5110310aa0b40010001d40a11109010151070b040d408038200d000c0d0340c0030b040948140c003040c000503100c0e400742d50303c0102503100342d200300700300041c2a581d4540c40400c165800c2c402e5039408030410110200c028138400c0141d20900343c20500a0340c07a00700c2050ac4100b4000002e0040d2218049000301800740c20944030140c550f40340004108401d603000c0d8105110b440c1c081009030030700700003a03100d00c214011070b03220320b86422000020341d881e90704490382801041010803110342c0c5c034444207450b6041100e0603a6920036045645522030b0082d04002c08003100d86440d0142c0e40e00f1a6940700ea07016002c50299a0222200000320000f080f03446900701034502c640003800d81000c00000106020416003151031031b01d610b620f0094a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 247475908 1250 247474658 247474663
    0xf1005011a03070903060204090c020f0304060c030e04060b0c030c0f0c01121a04020c21040e011502070324050601090302031e01090203071d0a0b03100207030e030105010f14010908 79
    0x1000340c0701c0012a660340c452000c111a008119040038020300d10004000450317004652000d4000c00c1140c0039500711072002d249064590255100d604045403c1d2103052001a04c00c0944031a1240c0007440080c615458000342081030b0404040f0150b00e40c0002025880385904024034114982200c00605240003a94002400605060300300351506441e41005010b10041c4e03680c00321490800f420464651035404006030b40c89082160351841c0c0c1005080d1480410742c4d0310201d03800e4507a49842d4854603480c01c007401c1d103200380d0f0750707038590860103103020100004d42000c00b03440c1072040c0458481c0001e0a48003a60085650140103035041c045801810001610003007441503464000a54070180c601c501c1038018090102c07403a00a606008901d004650380f221070801202d140310307050035851b00b5910201c09008882d5140c80566041d44034280890311621a500100f104511910305090b84944c185c002c2800c7d50b1081c5c01c4581800f41511040c842d20014629804000a003442c0c1820610b1400e010283c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 247477158 1250 247475908 247475939
    0x6010f05150a0f0311091503071101150312052104020405010608190203280207030e090108100b04110c0c030d0302070b04020913050610050901060e130b040e07080f100501 75
    0x814940c48060030517801c8085006d40d60801c202400000289010050305126944100c0d008c3c00400c0500b0b01c0505e0204051040007480703035100d00003070000390841c0c480c8100b010604401d001080000c10848120f19801000303600c540c150001411240c0c2010b00c1048103451050700b141c41001821070800c900b006450035070110000c0440c800503a60b07110302d1140328454282c0d18010010804407000003000d406c180e4000c0200d140a80e0b10030003552400f03020030031001c0081c49046015400a2000c01d81045180d008942d20840100009580c100014000301590048501c800c00c0c0d802c41c045038801410140103455a0741c1c000e160071484c2ca00c003030f51402c030040d0001c6c00180c0586000c04c00a040403005416822180d90842c04480042c50300c505001c011300c0c1c081c003810740952906c100020b40c3e90f000d01301030071101c02e000b01601c8815410000c03500041038502031075544285c44800c5c04d40280b00034000e0070003600f030190290540a4070540b8140ca0045a082c42a40d80d600d024010010703010030b000d010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 247478408 1250 247477158 247477187
    0x2030a0c0203120406050c010e0604050303043201020a030f110f070c080a05100e030f1902280203070b030402060301210b0a1a0a032301060806010f05150a 68
    0x55034801114008030f403914550010500d5141d00004020980c3c80e0000d000e8145861048000d020310086a031545460f00c0080d1b50003401a0300034004540040e4241e802c00413580c096001c0e60802c040d50208100344080c50040c0e50801d41d40c0007420031030442d45402144001c0e1b505c81380910440820b404041c0346d600c22045402400e90010440303031b04104200d003c4078000c007107040486580c2034280c100181c0b902102d03050052010319180801d01e090101100b641d10014400c1d03c9582006841c0c0035080102403924020400c6000d0f540000b206007001301c0c09200342400501210b0811206441407620b4400160800d46940c0810700401c8010b0b555801103d06440c0c4440c0072200032010311980b40304002c5c0040004184c50388540400c040b8100d1ba9010070380d2402051034084051451001380401ca00d00340c0006059502200078a0180641c20900141d0145004000243d1590f64614050a062003038010f6840071030240300420051900c400000240800c800402d403501c5030080c00640040ca4078480c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 247479658 1250 247478408 247478417
    0x9060903090d08040504051f0e070c0201080403020109020d052a0a2c150f0f0a03110f0a092012060d060e0610081b01020a0f0206072f0f0102030a 64
    0x40802c01c0500000e44c0c0082c00054024421418a9a100e1000000e0b6814401258a51010016240700301998050190b04140c813000071030032240c1c0044928480080042e8103641d21581c038900145c4400500c41b8070740f8060006443e0164903034045d0182c0982c45101801800070144405030b10340c1d40d4038003d0b0211000c0c41c40c00c040c41c20b0b40103010451018461150200d25000d442084116110401c0006a108017220b02c405102c2c040020070521000120015070401c0f81d8035401c0c00040d0034030b080da4030300c003030001e128a009076000e50020358415059000280c1280e1518054940b03442c06100195507290011515818030009452416500800400d080c1c450301c0212402000c1c0941c550200754404440000e84005280100000200300000d11034070343d0305c0c81041240c0300004c501d04400d18040030140c0c040e007040041c0b078980308040780d80c40d14140e91240c0c0410508000549a83c079035406009121600c4c0c0318950b1035503604100040150201c0e00600c0d41e8034116820303a03804070803190400441d090 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 247480908 1250 247479658 247479679
    0x30e030c180403090806010b09010306050a030b04170c0d050720060a0815040906020319020f040b0c0f0105090f100c05040608090c0a0810050a02040608040227070c0b0906090309 78
    0x18100c54107001981720703900300d0040b41c00124000811000501030001c0c05c2c2c80520905545206200040b001c501c80540300100010100d4001003034142c417400d4940c01e480320b4906040c2c1c1c0c0403031641032111440c891004108006500c000704030902241d0846003041100c85441c034992400450840e2003240d6000c020443d80b203000406400e8407080d6114100409442004000b04914080000b54002d580142c800c0c0d000b85002840c00206000b242da01e254100444c40c1003520f428903480d52608036800400041c012404003541c001d80900c80c2d80c0c4074551803802050190110300c07010781000001007081a005041201c03840c800d030b4010b01110202d4a2a1a01c80495566460b000303080c100f00040f01035103c0c40e0810b001409032000903408080c000350100c10841501c658007001c08900c142d100b500d0204008400080c094a000038002d00f80306070b031800142460403107a441c18042c03070040b903141001c40c1382d8030f40c481c0500c80145521503120720410010102401e201124955074050f813542c1c14440c510321b09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 247482014 1106 247480908 247480913
    0x706021c09080904020c0106090e010501030c09020f0909070c050d11010c020c0904020d080c01060b1216091e0308030109060501020f0d0807080a0b1309030e030c1804 73
    0x1844186030050f03240520003e034000414a0410307542e6814000780901070340c0102210440f804000041701d6041d440d04d0014244c280c1c0020328424414042c1c213298003140c07000c1742e12611040321000e845a442140403110f0000080f002046800340140d080c055580140b00c180041c40b03c01c0090081079190b035001c0707946180c0c55101944c0131001d540480c1c09810b1800d440250503004e0700c0e01070301d03200813000100d0964409500004404500003440840f10544000d4140c00c8000c110136942d0b0072604160040c80e11986009802000401c810f03941d6404009820180045500c140940e443c0d40e50b40d0301001c010030a5205060140c090a00700c0010b203600800d8044188009498a589d141c5581900b125030200051850004643c0c86200340c0540c1d440d4286c0320300310b801303061011500c2d02007450002c0544110b498024021740c480e403200340d056903503045001c0e6421881e00422000740c2c0c650 = true := by decide +kernel

theorem cover : BRFrame.Cov 247302158 247482014 := by
  have h0 := BRFrame.cov_init 247302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 247302158 ≤ n) (h2 : n < 247482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
