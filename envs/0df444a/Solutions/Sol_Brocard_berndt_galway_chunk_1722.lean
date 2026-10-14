-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1722
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:25:58.642833+00:00
-- url     : https://prove2.me/submissions/d149bcbd-8b52-483d-9c9c-29a79871344f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 309532374 ≤ n < 309712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 309533624 1250 309532374 309532393
    0x2160f030209070c14070512060f0c0f0705070906150306140f03030d02041d09010501060509131808030a1104120b040f0611030604061509061d0306130506100602 71
    0x11050100a1010301082113203001c0d4400500b85490505030800c000f8014004542404140025045140d1171400281d010904200f1400b00148501d5404029a02102d4039400400a2480030740980c50b0001c01c01e0261000104501440350b02ca0000c50340c00c010045148809154250201c9d4070a00682c0310030318840640c03049500308200400401d031b0300901202d00d400c40720341054080341c0040d0003540769000036401d107070100c3c6070600300240c109055000800180d454444050311501c5603d4407140078031201c442c1030441c1186a8803003540d0407030703045a0180700c959500c0c0c1403c00d68001c46400710280d251482c00752640d080a07003900c080ea500c0c0075114100c4005925840385d5100c00a00c2111a6a4104000310002d0f02ca4000c15070f020303500707416054070f030300786070b8104030648645411001c400341a880391040c080e40e001c4c800101b221501c1c1801c066400d9104100c036a4800b02007903040e0948180001e01c03c1d0200d10014080209000e0010b03603005440d94683d84d900390400d4424000140e00c000010b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 309534874 1250 309533624 309533629
    0x40f0c14031e0c060310090b150406031a130b04060b04030203070b0f13030503030106080a2c01201806030c0703030506030c210c040c020d0c050c06071202160f0302 72
    0x1c0d1500314015003103c0b400d542a800185869204a40b00002e4680c002010443c1081034010b0210f103150489200550310046210314410f400380303114450406490740071013400c41e94a6901c12107041c4020b0300701290603070b41045a0300545070400f0802c0c0200d14101000414404040c2a642600c0d402005440c86a203401c0215045400120030ba13a40742d0750400c41c1403032021030b04241c2c138000c610600140da101d602d03001d000303041d0080c010096071302c03c1c0c10306000c1e0343c1d400004950240288643c442e00e00000c101520040d0040030800e4500c2043e150402805008111038005028007031181c000350450072107100144400c1d4001502d043d070328102c00307200c0880042e0003170704403a60282001d03049811a03400f40002914142d11480d09509068890300d69005004c414040c604505009036010f1100c0c2c400c208000f5540c40e251103c400420040604550802c80280b00302844440020f0149441d080e107800d0a4100c401c034104154007501c11502c0c816502034110003004103c650100e0005c1400d89541c09 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 309536124 1250 309534874 309534913
    0xd020d0203040b1b010207031e0306270e01021303230d140f040b1213031d01052809060314040201030c05090927010b100c0f0b040f0c1403 61
    0x80c0904d40d901350700e40c02c80e48509201500415000f596000010000349241d0b5854502e0704541e001014104507081c011803020000c5c3c49402d0152074081c0000700ac20264903002003501584c6e0350f49a5000003503080b20000344800c0102030ba4012001d4a8401030b5200c0c280f0020010f0000d0340c49140c0021280d40c801c240250343e08000d196031210b40302d26208103040902c94540c015003102880c50004505c4106400e01a22595030140c4211036101072480c2d00c0d18050700f032001804007108949030700c41c10660721740d1082c4185ca142c0d0515003a070700220700d12441404081030780441c400000a100c55000a1a103200307000700c00706200002e50040d240d844640044015041c1c0403a403000f4000b0400c5901115110091218499075410100b480d101e10505100048800c060784042010f038105140701199035170340d0104608403042802d0004100001c0c0c82c00c0150308410700005041c2c4200c602c01c21007804410001e00300703d58803800e4098100394907072101c0144040a4030015030968031200301c042c115001240e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 309537374 1250 309536124 309536137
    0x1090509070308070302030406091202030a0b0a0e010e010e0c010f0e010e0d0b07080118231f0810151d07031b0c0501050a06051f120e01020307020d020d0203040b 71
    0x309035051a6207986481505522100b4220f00580c40040c0400407140e008490b6409013881104046503481e040c0c0000340e841d8040d860241480020f200881c03c2403281d54021849403038030400074005105010340480c000e040940030040a405100c101d0340c010340c42102c00050701c5009494480101141c0d90044928041c2c1c3d28205800c2041c070311000b4041401d0200f058456160703075542403142d6040101d40c01d01c14240c402040070040c1071290183d811a0300b8242d1002940c52400e0b914440d50310504003a03042d0120124100018200c070002040940c0003040c1070b1480c03000402c0504c00c020304450405a0004688101e4503459410247c40d034103c80711001311a00107003145000b04400307850242c644005444482840302040c00e18010790708008003130080b283e01c0781090300d04204d21845c040100e11080303209040f80120044161030441b0817801040714080d96074040c3d504000030000100d01d14002e41c400d0329410050301c9100c02c1c40a14600c0081d000114540d030382e015500741031921300c0d820360540140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 309538624 1250 309537374 309537391
    0xc03070f030b09270f1b03071a070b0108071823130b010b0a0c1e0623060a060f12110a020114011502030a270f14090f010905 55
    0x8514000a07030740d50000f110f01034100c107000c40c3c5401070203524800c0d08004100c0301c03d4940c3c00c03000500e1071200010460022519111030840941c42d9600002800e041103074120321001074200941400b40d07003e05000d8aa014411900401300c2e980314415566658028801c03082c04110240c1c00142d8000241c10881c0c0401c03042c1c9004410074802801d140341c4041c01c5507440c0424444030079200500414410940c01031269004984c42d00d82c15000040420405200284c090381d01490542c1100d41140ca4031040190001400c0102c07110050340175031441c8a1060002c41401e01d000410b1442c603040c41700e0400c440d07040d201c4554508465600340d90409800400c001c070141d40300720700c2e01e00ca0f035510f00401c020761103a4000a0480000098002c6110040e044181c43c0108240740c0110380b90004103e40408a076070814032041c1c800503074010901c89042c4040c10440e00501b100045e40d001d401c20001c01c0d5000500200c0489116000b41b08011100b201c1c201c40c8603042800401280006601442d0445540d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 309539874 1250 309538624 309538631
    0x1406030c0702121b1801030c060804050f01060f140102010c2c031203060a0e041e080d1508060705130312050c031206010806120a030e0a05100203070b010e0c03070f03 73
    0x400203a03410110208a41c3c1840075075039404240da07190030185c180d200080440c01603401d5040d512846500105800f460087c000d821001c6024807000f081400702e0504c40e04004d00c440358541c100500c030715401c3d10032502e800b034484041d840c1a40c010700803000c20302e50f03965564030101e401071800d000c0240c061400c0280040c0340c14002d00317951020721a8000d22800301c0c15269582c2404070601103107056a0788000301c0b66507800c1c00d00000844a68524140607890441e070b1510181a003450368107446201030355402d013490450700c86044200003100004841c10b02c0b0548119a448010a0f43c040c412031903030140c1910130803418000508040e01e05801400360746052804e0803442c0c0545840c544c80081100d83c0d140f07120741000040c0d0381c4103540c9680040c05039079070070107000804507081d03941454980090030b00a0b180c030408225280d00c03e07000e0041030028034050000c065004c001e5101d138806001070324102c14400021440c68142c1e04c0d064001d0f100c03002980d285540b030110071241400c0d82542c1078200b545 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 309541124 1250 309539874 309539899
    0x30e0c010e190b070212010606050a030207150606120c231606050123240c0f06070c17070f03080702030d0609020316080c1b070302090108010c091406030c0702 70
    0x3548002540903000b107a030384135507032401401040624072561241c010300742e040500c18005e4a61180c10364005101034140561108804c0c90007010000d03030380300e50000340c1d0b250250014295601400f480408400c145040021016944084034030800548002c00601e22a104010366500c400f00109041c0103120121030000c201541ca14040e41ea080e40252504082010302c6404650705442c05042060101c03010190b890036015100040c0310000b00000720654081840b2480d60002d0004548c0407020106481044ca80745101074000845000d0580740d000003083d0405810300941c044602e001d41119414108030007070355040b50b8a52006028004500050103807000004c541e00580c000340200700b1015851b4689070040804aa80070b0103240c0c01c0040007400d0180c185425012500c000d064850341d41c5400907412085407800025600081d003006aa5000107101c0406502000404400795180300c24166241c000244480380580040c0c1c3c4824100003182c184003c500c010800b0f00d102400c049100203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 309542374 1250 309541124 309541159
    0x3050706050a0c05060a0c020708070f0b0304020d0c0620010b0901030b04150507030b0f03060712151e2d060818031204020103150f0509090c0a080706080601030e0c010e 74
    0xd407986c41c403442e01c0e0044441c02a80501c84a402b40c1182070003030500310319202c5080c030b41c20102d201d100201800080880c0954554404105075a038000102c002440e50341c01c80205500c003100f01c521640000040450789408041c011850b0100b002020100140d003941c40f403404140001e0800c41e10307940c111504000d00385190050f00d00c034565644000407004020404e10200703103115400745200742c02001c20094507a410071a429110f1020460003c0c0080200f01850003090082e0041d50440310314401c1602120445c050034001d0302ca01c484141c041c90406501d111407140c40320070407102d58000704000e2040504c1900d94036030040d072950900d8501c1d400061141e0455208040100100420a04000555030140100c106030b2200549503039203689013110300550028a405141d115000c0000440c1c04d1410402803551b21150050002e0102c0381d44850240d41c80e4001d200342c4001c207820400145466000e0301c25102042c0c0032202801c13249043c0340c0115082c1e1400100c0d20360150394611840c4500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 309543624 1250 309542374 309542383
    0x10b0d1811090c1216030609021201090e0f06160207030f120e030303090d053a050603010516030e07080709062102010509090403030e010203040b060103051003050706050a0c05 77
    0x318000c00c94034540702049014030404070380050103064521410002071012400941016500818020314038080005808084001d801c4c60b074820a0340c030303001042c0c0b0380c1242985c088560484403800e1040140c0e4510802031078070380f041c580d41c10b81f4036003010300084e02042805030048500100761050342c148984a0b070311000e0241003110103982e070f205854084ca44480d0800602c1609000840056040d443c1100710140d881898400712001c2210101d6003c0451014411040c201444c03a06080c00100601c6241401d5005038160269440e05160210300d070384c1010f00c2114003560740c13020078051558000c542600501111429504980300705400024140400d10001010b0940c21002160891401078000411580b2140c5038a202215480040040c1c1e0880220382441d00292014030703803a510f40c00c0a90007001040030700e1480d0350002003000100303d002440c00c1c0c8904000d0324204669200e8805280c0c03080c0c10b500001b00158011401407007250302500260240070341034940aa0041741655495041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 309544874 1250 309543624 309543671
    0x90f24060d0f0b120316030504170307051203040c0504050c0d1a0f0a050d0308070c0f121d0904020618030a140c060a05090409020409060c02100f020c06010b0d 70
    0x906564002c40e4208000d1030140c801982012500010110506500c0716100d200c1c00c0071900c04580b80d0f10046007058007034005c1e20001c00c07070540b00d51342e02d105040c04952a5800071000300c0303890141f440c00303180d080070746400d03a40541d400040c146201400e00742400002c0201403c0781100c4e000034410004200340718000c0c000046c14182e000b0b0b20090b11b140a215481d21800c4030f032446440c3c0e50005000a440d901d480400583c0c052415202c44e880e0340348290b404980c070600160880d48840342d54003d025403038103060002c811550f40d5075040309644d400707100e83e014280203a03503000803071002260151a103100030740005000074801610084035203002174540240010101e40550703420f500c400740400240007404844406076440c510741001d50b6001000d500ca510003092050307135118040819500e49900c4811559407003e0200309c544070307803040030303540c1ca20301c9007524100343c1018041c2d010050140241c074407000b5920b0081c58564200302003a6101d410113491260300981c0d602d103460300c54cd20036906c10794 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 309546124 1250 309544874 309544897
    0xb0a0302030a031106060a05090a0b04061806150504050120010209360c071205120a05100b0c070513110a0504140303070209070c06090c080c01030b090f2406 69
    0x12260101d04c03514100038000304040c0c415401640d003003140d92541c2c142c8591000742c00000161245190b00002d0080600ea00310900e0300d03c1a20f6481d82001495000009071000442c0800b11868041c1003240d8911503400341d00d0015a60502890050414008142c3ea0007029000541001003050104043e004800448a060424003e507030701c20785070341500b070341c1080d00c40d2a5410017440e0080341c1e40c200b07115511004100100c61000941180e119a050390038150151071441000c0c203104a01c1d07009804103656901840d044000000b0b0400b01000c102c1c2c0003404420064440d0b249040c080002c0c9409546007140a60707295050700782c407800c0b21070041ca1502c1087c0c40e8240c88034103180d001d20010f2021072503035000380e004001450160381c0d9081c110303602031ba0514050b1911041132410341e01403c2842002011540380c034401007510f440c00300d1301c000900400e85c0d080080f0188081004205042520301d250070020100200c2c11207041c1c099858260130106280401e138502210120381c00e0341c08500783d070340c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 309547374 1250 309546124 309546137
    0x60e0f1006080105040f080c0c0303070f020118080615120703080403151a04090602090307080c0f041407080c0408060c120a050402090115030e0f030a020601081204090b0a0302030a03 80
    0xc2440304030311841c0e000e044900001c20251515a80d0704600e40303030f507a01c0034003814030106504602800401500703c40c03007070140c2925242c0700c061400040d0012241d008901080319104201c1011070141c2c0c0390000c448000b4010300e5603880e00508100d080502800094000321000040100d080c000c0102c0e0004605c620819556075286080c10f000c2608162310090403503003050840b1242a04200301d510340c1c10000c85002841c0040c0e1b00c0d004c1c0c028401e144400e500750040150025400300040fa65040700001078499501c4041101c0800c403c80d1800044c0207541207082e0f0210b01100d1141100319031010001c07030981e103041d8803000910701d41202141c0316010311000054050104040e11811900702220007010300060525034000388020005000c1d0703100c000a1082d1181c80c4a119801c402034410700c10301a1101e24501061031034032035018a40b1000035114620002969a10009810308036520000019050905040854018120300201300b41d01100d03003200480503030703014800c29500318807d80705c03107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 309548624 1250 309547374 309547393
    0xa120f020a0f05100e120d02030a0612060501090b0105070f0b04050a0516060216061b0611040305010209100f020a111503071d0a1401030908130803030f06090613020304060e0f 77
    0x20261703401c40503600c03071a4108142690300c0030080d0040c0c40002d14000310241e16541c541c00d2290041605501c41d419640c207403c044424001e041c1d0103103040c0c8000e418140480c485030001910f0910456600501504189907090f011440c0025965002407050301130758040091134640c10300d094501440001a105102010084a9010841c122614442c040780385000c919003540503048807006038100d540c00343c4a11010080080550020380d2084941c4440c5031103039181e0400b64001c1d0070407809280900600b0002101c41d900500362102c403c441035000381031280b4075070350796004442c0500c0d2103508030b944440d9602190407190040c40c0716032840e9035842992541300f420034107195101c0d184a03000e0b0951420500c045c010383d40d404260321000b0b080100b07400c851403920156501c100d1039080c11105510002003404d0001100071401070000304140f1072241c807580208522030350161142c940c850700014081c0060806a0003450740b00b8003c41c400990302148031003250400010702800341d015005211031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 309549874 1250 309548624 309548653
    0x6020c07080c0306040206030109051504020a020c01120209060702120c03100b240a0f1b05010605090f0c0702091306060e0105100905030a0303020f0d060f030b0105030a120f020a0f05 80
    0x1602c00850110002c2c0b05078203054020844510041c00740441c015154400600702c0c21716030000c100210000b41007103503100d000c60070080d121100d213041302d40000c1c40d000c85074010850500a480a564001380321a03e0a2071543c02c1065051898401003000e00641100211039601031010120420f5410b00c041061710100080009140040e01803400c2d0510304450b25007031065480c180ca400404a04244a2421400c1d00543d0502000a11f030190340d170000340314804112064000600300c88040e41c4007031441d00c03134410180f2440400c4460b400165030500c14080035161002684e9040020341101c1c0d140c1c1c840035118402514803e030044035083c501c3c000104080d007048041d104050503585003002ca12428040001c0d02d400320610090300700340d0081401c4094620000c00c44090390842e6504028050342c59108540751203444c8001d8580034008400000c0501300460a1505103500892018408100203425102004d08100160441c0325259280000a19485407030400d1030082c1c1c0140401968000f1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 309551124 1250 309549874 309549883
    0x20a0225140d0515151905041d030702010507020a0e181c0206040809060c030301080f0709050c120901020f070f0b100303171e0a1a01030b060405150706020c0708 71
    0x610790054201d07100210102d40040364244607102045a64101a11400c214403a00312007904215400132003441c6000352030345500f07081411241305031400e01004002070800400c4003c0307070a5071140341d001001803030010362164008040722440104078100180d1100c109d0b44606808460841d000d000e2034400b0b03c1c4445041103901c03c42c03010740104441503d11401c009480d40c0010700001c01da10800701f5003541d1952007009507428403952504803900d170b680d140546c1d5651440310512102074000c090010407901c425000d210310500e80410302c0c43c07502092011000d07520301c008005a003195400e1041041d14946080200751842c02498030241600c03480c10070755000d01e0040e20154403d24613900800010740c00503018401c5045400c1000d03091307078500307a10640c120034400700d408480f4552000c011041e03000758854000c0c41d00001a030100703000303040c00650880b111414055880141030000300300b00c2c0741c516011500c4150002c0d03842d00f010079580e144010ba070016119039455070000d840510040701c0400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 309552374 1250 309551124 309551159
    0x10903021509221a060405031b03010902030114150306071d0409060204060203040519080c0d03090914071e0e06070c090908041502070e181c030c09050d0203070504020a0225 76
    0x880c89480d00b4540000643d40d800e0740101852700003980c0c00041d480d0740e801c0d405a100d040d00580244140c4104007002c4944582c2115083c08119201c00004a03d040001c0d10ba80f0078612603c924400d041a000740d01910320b00c483c10940d000e41ca800c2d551002a0080c001307080141802d0f0000c688841c2014204005082581090300c2206004603040206c8540000d809010820030b50b0180c00412007400c00f191011600e800c500101820020915184c02904410034810704139030faa0076207266049144e10903a181500100000546038192600e66031800c03900504d09103108035400e07086190384e0545401610305030340c0240c54080300454100320303111041e003d01906000c10310203420b4450504442040a8101610031000c40e0003400350424121410404847c0b42e10680b03454903280313005002e000780580480c1c0d6001002071704c80d02c000503d41c14508200c40c10950b0090150103850304000c10b0000a40006004004501c1880400c800d81400111204104401018030a03509400c1c113a25803540c50380758 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 309553624 1250 309552374 309552379
    0xa030c0c08030402100c050d090603050717010315090b0c0904180c0902090d02090a3606020f1b01090501060e2202150a050403060b010903021509221a 66
    0x10040c038006980c51048030340c0198116181d140c40f040c2401e003140d00d5103002100901c5071142c254101c884a4200c24408102e40c4641d81c01c0c015581d1b514400c5600a0010b6844105600403100510003c1d0480c0c038030800d681d400c1c060008803a80c0303e840c2e01c881500e06480401c66148000340913070060819001c1c1c010034260002020303441007941d030f4a20340300501901c01e0743d961030350104a5030030301d945002d0581413a5800502d410014188020316400800d0814020314414040b8003512180e00300c43c4084107504030702c0b0207000d0050307151515140d02070b61003400b9180c200b8004002613181a11103202085081076948000210180707240380481c211401c40c2c008a000610140420a0000802d046c00440d00e5030426501e100c40b01c10310200354020360310401889090408183c400e070f05603020001d4000c5078010502070041040700d60064509024501010350454100789513040550700d141c00404003014064803031031003801e050010384101f0004a8442140f9030700c420001c00c0a50304400115403d0108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 309554874 1250 309553624 309553637
    0x19020403290403080c130e09010b0a170c0904020609180a050705030f01030305090f0405011202030705040e1222060309060c020d0519050d050103050319031118060d110a030c 76
    0x243c8020f00341a500070812181d9940c00603103e1031241d40c08142800030b045018007404030707090100350705004c1c100c4411010f005090b80300700003423070949202589040b070300d881c4003603c0031740c0c003203002e014110394003e0059030003050030021407445845404100d0110b803000c42c0c0701040b50405519800641c0c10262240080040c20f2042c4005010890800c5044950506000740d03030704242c0300441c44981194440c20760043c6001c1c000a41140c451070f03d4180c540c0300700e0594041c2c1c0c5c0c4510400c811500410744103403085e48100007082e00c0c080090002c1c80c5032401c5075446041034860b0314507403031821615007100b0000b80e00c0c2c68a110800045010381080c4e68420f0001c1c000391400d0030401407080c043c40800301112104e202d41c0704203060146e004c541c0040a00c0605104540e103a0402a0340d0358800701d0b0325070810085c0040303110068460305c1808811500d0011042c6801d51000d0820b2080303150442042d84004204200d002c038148500c12040b181c040c0c40b020644907006540041c086031009040c17041441f04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 309556124 1250 309554874 309554881
    0x200607020c0f12010f050a140f0103140a06020706020a031b080402090c04080a0c1e06080604110c0a0b15010f0819021e120705211902040329 62
    0x2004561609100002e80e010464240c2980c005405580c40120b104401c1d40782c0704900300b403004960071480c842e18100c4428014925051407001076014103c0308440003051680040c00095450101c100711540302404a070003504498035188101e07030001204442d0194006400b518542e014041d00201840020620b0307104c1007602c034007a1003e140288000d02c19141d40c400601500050380c2034401601600080350340e410984e1414640000240c0034140040c2000c2c0c01805464800103c82810740e81035a0711980c107a2150010300006c4c000405070307007e1005042c08054000e072001c0141c6d4a034540180301081003410324540506080000721451410007080d080e400d1020b07034125403425088141c120306000140c5240c022403009010700c3c10400d00b552032500003e804240341e0f10181c0030081080707100c1c0040ea1101350054495105420003038982e1209071080d00d444a6500401c2540000c0ba16524802d24507144580c604076809900200c8c0c5030204a00602140a13206054030844055003c40a40302e00b0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 309557374 1250 309556124 309556127
    0x70f030f09261303050606090901060510030e010f05130c0509090d1112070b0103060b010203031003030c06090b090708060604020310150509031605120a03080a1a0a0303200607 77
    0x242d0100407400c0888060054406480c410011520080841040403050030f40b00c2c82c0980c0c5400e41942e00d50300c5003102001090010760706115500441d00300500c04100d446600c0c00030360142441400d050f072a55a244400481140da0380540ca00c14182103680c04d03021402450501070120003030f080140280c003048100184400d00052034043c603070190503c86e001e10300b025211442d18040d10506003480b94086020740801868200d194141d134855102801014a21001240c0d00d01044411400c5e500000b24100f004c01e018014014245000d0324001c2001060340c2c664001280058a0400c00755120711070412828006101e82a00014216402c3d490750410b0903142d9403004c10b03401000c52000d030048404085c6030140c8101c541e403035000f5090b210301c00e0340406810040d2829200301070017490000d41381d03008640c0224444400c02e07490340700c210158440600041c001c1015480d00c400c0c0301d0324610140001d54031216441c0081d84079540da109142508507808445031000303032020149502440501000a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 309558624 1250 309557374 309557393
    0xa1d0108060f040e0a03020a0c09050601020c0103022214030705040b1f02070801091506080327120102180102280224160c080f070e0a14070f030f09 65
    0x1850450300d41c8079030000315000030700500504943c05654416559030301708060700441d02c80070b858080c01c00b44040c542e5491a00c01500c4044440a0050f0402d200f50701c8558081e03800781504000122000420006002d25950f91440c281c01075003550410300e103000301c5864100080c07000f50606130742c1032040498080204081079008072558009102a40700a81c5651082040c04010550140240003801e5203081c05403030390b40380c1c2d86801c001c1814058041107002e4000111010201000aa58140180c1d40705c850345d0f9040b0f4540803940014941280700c1b807100240040d184441000d003101c1090440800068504130080100a064540b1403919041c090003c4401200e41307501a92080e86500604105a40d05409c1d030b101480140008518625030754003090500c960948918030030310703080b9100d90815030380703d0881ca80f60616a020403030030b2025466080030242c0103240d05a0200d41401c111070700c0d800405013150500005041002521030042d0301d40140d074a004003003842044042c00740d40b641c1010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 309559874 1250 309558624 309558631
    0x12081b0601032609100e060714010c0309080909040309080f1615090b03040203030702040219081f061d04060b0a09150f03150f0602030405120f0a020d0611030106050a1d0108 76
    0x11808581702c04092409155a0b01004030300420b0030f5514a00fa150100082c6c5030500d84034005d41c0f070711109064090107403046210698204a12034103102c0613000b000710031b0600810482c100710b520440028410001c00c040b2805004503406880303078001040c510510250b05078001c160810f50700301c42910490b001040c4105582c6652501d40d03580d9103c0c00031a165101c2e524000350002e2000035142c817001c105030b416182d200e1080d5a10505611110241ca200001c01c0c40d50b13801c414100d203420000c0500070086d4084520011411840141c000400a01120a294000f0642140028404840e2580f0180031030161242014410001c081041d00403c6001d0190340c3c142410341c0c8010f81c03020704808890220080c107101414100c22503d4000003512900316100f030501900d012828200d0214000c14414282c001d0400140807000d034a400b000780f80d0011100070394680781c0d03e50b5100f21000709400154040e00554641d25a1403000d07a05c000d00d8581d1180c15284000b40c5ea002c2100303aaa80540b603140c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 309561124 1250 309559874 309559879
    0x42f1e091603021e0d0e0a2411030a0504120f020d050f071704080d030b0f01030c0c1a04030e01050c120901020102250605060a0b0412081b0601032609 66
    0x101d510707046100350000d11814a40c000b40032000300c406600070741c51000416210344a04010b01c5034090041c100340e070f90f4070350120080c250480450789040161581003a80c4111404140200c1c3e0009011502e494070b070b205031a06030315030f525030f420041440804800c1d810789522a1810743c02001d01e20800940345c140314880c100400034000b80460440300e60300143c8460300d8000c85103903241404154120072075802485481864043c001007004861701901ca091600d1340080c2040e0a10303488600118000c1c000708020a003030003040c04500e400304001c10181e12105440d052125214109800d001c1c00f00b9030030342c26507070400c034003004113003200780021a20714002e91428140c1500c0f5240c401c0141d0290141201c0b9011900d454180220200d80a02140700c0c41c034002d4504022580720f01052200020b854010041e02c04420041004607804880d985528640180d580c1820400c00800d102d400480ca010034004030b50101d00180103110106500110a40912a50b14006043d00920f000e480c00740071101803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 309562374 1250 309561124 309561151
    0x31e030e1905120a0b180c090c120408070308150d110609060a021501060c0c140d02040e011b0e010f0804050f030a0206070e180f042f1e09 61
    0x9555110700004400600402003021562000029100d940e4500d01541503072502c0120340850b10030300c009015441c07203414031800390103076084240034403c0f182000307840800f640c3c10400070156007503040c00001d4004d522401d07056903070310748609004011001c090602c40046c41c00d01c0707800c149035441c40c0d40d807120b59911040c103c42021074000011041c0c0541c0600c0c9401000000d07090f641141e0215501090000c0903a08055a03620b403001222800c001c84001040303250519014005040e545441c05e002d44c00051910204101543c04a810b9581211143c1701d0ba82d101c86918800c01c80741e100c440200c141c44d2425010707070b8482000007030030043d20850410900c400c01c408541030010601045031040941030803a5550074070608000c1d0b451008859020000d420000a0122440d140842070114070403032100d2050340d2610852b04504e28000b40086891000810040c01c0601e05610303182d18407810494903094290f1500f051110365a03078090000d1082c0318402e1071044035611100c2a54004422030f00f602e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 309563624 1250 309562374 309562399
    0xb04030b0603070b0c0a0308090a050604140a080706020301060806010806100309050f010212041a100902220605040512030708180111120304030f03020a1e0c06090c031e030e 76
    0x107400c02925070041004040c00103451200b01c000051310801b054440d0f9100026540c408074016155255481c004060b6008003000c5004280714007809140601c101c010788007030921607603c103401b50b4011142194000e03008401048041d4002d5152a400202030030010341501d04078000601c400080c0c20580d00740b580d0769030030300c2c24420100501c0104c1402c81008640c1c40307010144191004034100d8080381c5040b824142c00c601200c01600d51409159003100c121180350826502402a401003481101c2141c65440c220641c94411000500240043e44410342ccd04c5081c102400a500241c11114540358400c1000000059407541210b818841303401c2c0398500b064000d070040f03c42d0350f10900d40c0c08241c071950100c4420f50300200011343c0243d209407901501000e84d0f1100f54168000d810364100401c2c0101c140001040c0f103002c85e05407940041c501030040f25041e42c1d0b40c00458000d46801d0340c02951000040c400c11a001075054602c0c07000c0d591583d113102c40c1d560020203c0c55481e4106002d01d5504a10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 309564874 1250 309563624 309563629
    0x20a02040c050708030108030c0705100806011b0b0708090609010c020a061508100b10030b01020607180b0a0201091106030903180402120f100509100b0c100905030c07060302040b04030b06 82
    0x50383c0240f540140b0056a07541d46150070341e600d4201600c0d0a00b503000700c00000520707180880c8503044003049612101240d607110727001902d6035404411101c03044031aa21280001038018507215214004a40316000f5a082401180745041801816000d841c1e140c11501100b590b000108a805280d11510200d0048504201c050350400b1035071104010b480380b50041c400d00b1aaa41111031034500640b8070b024846110603048003602c060400c80d1740035810800101d0403035842402d102d201c40d19446506002d4560b145030a6840350b11240803200141d5580504000b0030100181c0c00500e5007003196100d00710704141d41032035164450011344081d10018103c0301400d60310790f0340544034100344108007004180750004c0751140302803044812068007421160081128502035106a004126400708600c95508258000c121a44000c070f10902ca8070880b030201440e90340b140101600940b18402843c1c4500c048806586031145a40010080c50b00500044c0150075200c41034a0480b50030203103080e00f50320749401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 309566124 1250 309564874 309564877
    0xf02070b0903071d09060a0519180b010603090506060316050111210a1803030e0d050c030a08090a06030b15070305070f0305270d110121050403030b030a03020a02040c05 74
    0x3010050304d42003003014404950301d21544601141000d07a403d558030098050122041110186208902030901c03400305d604a43c00300c10030210806070210105e10f5034030b0342d20910100b43d001000003901d6845450401130240201a00b220082d4000c0082c182c003030340780c0c25401405008050406c0007103100405115420810000c04808050400c005005940762502d886c0e488100c0302408241001c2610110000540c03900301129010f55030440f1040e203d00400503200241c600a8886108503c241d0140d40e50600103d45094441c400711aa1036603208240a100c803419403004050501d0700300555070760307203e0b0441042d41307001c1000b07136655502c1107250641d0b0600580901800307100030002e46008040d005001080c1c503001450181c6040034018811104e00860015200c2d0004010300b907a00010f401500c4030204d00c0414102001000180c405402c0002800305050a407140c482c428401456018843d40c40700c00400e030041c00a80c1200e07100030b0b644100544000303014583d00c84074030340d0f060722580 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 309567374 1250 309566124 309566129
    0xb0403051303080d0605180c180a0f06030c1713020604030b0703050403030b0402041211060405180f06010804020306070c03110717010e21030709090207050307030801060f02070b090307 81
    0x3107652400742c0ca030700b0060aa508861030382d02c1c41314903059020986181c81041c51187c8840d0b42c21050803035461404c4052650401c1040904031004462a50035076603440c4840f4000d4201000c680040724944103001302a1102107800d83c2c18010161980c1c90b1a407501000c0d150312030040c2c038810344480c0d071510104416200c1c0344d00c0503207960040424024400e03071540001c1d0260b07000c1e90301800041030900402c02244510703c160305c240142c1c40314240000d0701c10601d210560f4002003070a070030590b4038408982d00b607a80d080c014440d00454803c00100c0c1d05501c005581104081c41c200c10940b0380b07540030a96070701c4084d01c00c0080c021b0b001c3c48001007510503000c0c1c1c5004400081524150355031190b02c0301c00c070000d26a07022502d5003080344112825a0014928112a580f8500036465107196005010340364000f0b46482c3c10031000207800715403070300180001c1010500c110300840c2e5500701401c0007480120107801c55010800428020342d9580e60004030b000c00c0d0303015240320039030b05d04030500024500205507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 309568624 1250 309567374 309567397
    0xf060204061707031518020d0510181406060d0b0a080d0206150102031b0c06180f040b13020a02240403090b030402010c0f050118050d090902070209040b040305 70
    0x501080700e039441400c0e61250068030aa076880c0e41c840d40f2041e001d46a40981c0910b2180820504120030a43c0344107410380c0c50b0241c03c00516160f005802e4006881c1300716400765403000103403070800c40d09a400c0c1280030000002c90b02000b40c0c00601c1d800c0300f41d4044c05406944242c0d404100c4010340c141070b034030170459001300a0a180c40140d8074091603880d62866258900503000b07640000300340001c044c140101401f4140e0145260920b601c40714071440442d101c0540c042c0c86101c254020540f00e00c8001c000074090b04a24900108010742004045c2d2510398010b4025814a485030f4100c1d01c91500c40c090b00000708001589540c00300301e0407464501c9056562580240004401941c0e10030f04c4c24250041380241c1c0c501c000c042e01c644282c00188020b440007400103c440c00f8540102d403800c0b50318001c19116000109540300308140c0c2400e40c2c07040304030a940d00d8110540c24110540c000c1440001065005800c2d81040b00707540020384880001413015140301040000201014030a408a440c0e20070b00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 309569874 1250 309568624 309568627
    0x3090201030237030203040f0f081902010207060c020c030c040b13021204060c0f02331f121703150306090a050c0d0803041b051008100b030f040803040f0602 69
    0x41c1c15102c501c05a100040e01c0308204081503c02e028824000c0345c3c401d40d000452040024815603c0c00092001c140c410b607410401844544e086c10320540c1b54141032400c1da800980c03206030a041500403500c580040805643c0414808446510080340d41d00c00140100e9000401c103d084000c6180c014248068100f500d10015041070510307152401903001e6809181e04002240a034081501d07410481c04c82c00b00541d00c16511011003146500302c1924000807a08010726540d6140d0190a8207042a151404c01c0400c014048042c0076400e040d06c0010320400e00f6590a60041d91120007008090041c440700c8080700100141c0004542c4524040400c00a0122070461030030040994a6451200088541c1c4c05140c000600700e140ca6120040420382088026245031129510140d0310080410300400e410341d00e02d40042c01d581c840854855401041c0c865116600d01032800d812045499040403140c0700c0c0a0041c03000c10585010000d9105500c080c40540da6112800e1900039860750303002c000d00c000d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 309571124 1250 309569874 309569917
    0xf030709090b010f0506040320030a020d081c060f1202040e03040608010f06051e03101a0a08010906061e021504080a020c030a110d021f1709030f0703030902010302 72
    0x302c240099048880d0b110741d4400541e1124208071803480340c0d220250035494070045980c542c1c0300c94a90b51174003000080885411492560100b08041203810054842c007001041020000c0c2c07250514940c807840c0c1d01020404541442907070000d90845010301d084034996614a0421500c5960101d203038100c8070b508481c0c43d00d0740c07042d00900c044805d015003191030000c0d0000240881c015070555803030000d42c40003800d00482608102100e6040203042c01246010f46900045c0e9007250f0010102038060140d20650350611071502400240040c2c0c800c49400f032603d2402c1002d43e074851040381c103001400310400d0304121143c80480c9007010540322039a8445009040c00b0402940d24010b000300404c0d5000d803018a012a0b04140c0c441107981e501420441c14949062030034686401c0454081c1d200410b0001005460b070344020700341020000b500049640ca0b1024980c038a04190001d40c8151308100031490700c46450481c8540f8007410700003c081c50f4850340000116800303601550f4400002144110740000e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 309572374 1250 309571124 309571133
    0xe010204090605010f14090108060d02090405031b060c040e07090906060323190f0905120a090f06120506041d0601091d0303060609010c0c0602060910090b060f03070909 74
    0x2100748030f410f0224102c40c503041d01c0039000c0c012a6640c055504085410b224003100113440702140140030b268813a8100c100352006903a490700040c002e600603001144c8420705901e0444040c010190004c809a000320100300170120903104440c165088104207441a45440c0030070344060141d60014010f560400c1804200c43e030741a48803d000511622a203105101c10380c00e43d109140c800d540030b082e2605903105561035406680c000240440b91084001a19001c035186caa060100040b000381885074001200c000d015403000124000c1d0240d410442c442515046002c2c0c0380c120b40105019080e07454200054041d6125030000422190360403802700041c1c44803c00540300c0009004400f2503900e040201c82c20025500342e068006484400258690303100c2c042080042c0d0440000641005a0040704800162120842e480140b8150300144218101502d0743c80c1003030580560514001e161032000313004904610191900108195600313000702c01e031400030900f442c1c41038111040c142d041401800800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 309573624 1250 309572374 309572381
    0x307030609210c0308150609010e011206090218060309030d05130210030e12090604140f0a08100f1404060e0a06021b06010906030c030206031819020301050a2a030e01020409 76
    0x3c1e20a6a6003189942d81800711070189505001d0160014401e0002c1402075010311604503944005060913420718000e82003000940749c054100000e415004200c03664204a00d41703011156503403c031203643c2546420040d0740d40d00d00409089411858690300418002001582000312464001d41a40c2c1400b105007c0940580100c5500407810b106d1a01c840b02581c1036402a141410340c01089180b4083c1b80c6080542e01103008400650320454140f0309403866619003078500000c0c807006018004026000d000e00003224401e0191908560070201c040c003480c08901d54403548554822400600c81d246c00740c5651030800c0902d8014080e510020714620a111500200114103952100b103510580e00e888049080d201c15100091100d04614003c1c0010f19020000d1070340101000c080c84680c00c2c0c51000d09150503107003603419a0300401c03412004103505082c0031701903009051440170300000940c550089042c2e00c5c110200094207541d2150303104050702c6600b01e40d9904180000030b5454549510050004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 309574874 1250 309573624 309573647
    0x815040f291509090705010c05100906060501080a18020918010e0f07060203090d061d031201030309090905070e0717040b09060f1005060d020c0f0714030c030703060921 74
    0x80210b40c00404445180c0300c8440d521640050010300202e0740f401c001514001062501199a0300400ca03441201c00e12900ca400001400b88070701003a1645484005090390310040c0003200c03031a0130300723a0b41c1010851040380d5110756a810b0700c220300c0c25034410981103440e00040c1069050781d400c083c680d940104d40080d11a040099440c01d0302c0d002c03035454000b0790b80ca00c00c240c070051700101c4481190001c240349500c0100802c2030340030401074109034040401e01350340c414414100302400090042c01410380c07002c0c1c628090308604c04104000c1225403541540c0c0c05891207951350881003800080c02d81c43c0702d0424602c0034041b07545804080e0515143c0a0801141142c103030f510780c4900c0740081c0a0948120350603026a0303102003e4070a007402c000074448541d0240403c9041e0540810030051210000c0100040d41c1c40072002a110a9040070007440000c030180c4c2180e031181e0300083ca40e11440d80c000c2503480450b0740c4801d00040c1050145010340604006100c0c800391442961000010180c21505090340c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 309576124 1250 309574874 309574891
    0x306090303090c0506270406030803010f06020114010803161707080702100e060d0506150f0901110c220b030307140d09061d180112020a0815040f29 65
    0x1441525503060007170a00901c90800a40d4064901c10030800e1005165152012000b41c0301207001516600d6003401503000780d108411042d1018401c100203036082c450413031410240302224030254500303810303190b0f240a0301c03410a444c045a0b542000070822000444200d40541d80345098441b04c44e400c0c004416040300c00305034000c0b843d43c0494014a031081c076550315a003800034081c40c00c0510500e4200d0003440006c1c415600040d20a00000d0001c8000000d4030940c0b20300c0002d25610840d460004182042a10400740030384d0100d00300d1046a40d4140540080c0c0000e40d8050301c1290340c103164074000d0884000119018040014454140b200b40385840c2001c0c0c21180c121040300b5120141110900d0729840340e580081d41d40c0351019000c04080d007200281c1d8400806a9605640c50030950004480c01e0344401035114090340c2840031410070f501800002c040d180050180201c03814a43d0962010003007005000702450b06030002041204605841e8844040e450300c86081003003035414034151070503545203c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 309577374 1250 309576124 309576143
    0x40c151e0c03080609070813060e0313092f090a090c02030405091003110904020d120914190509091509010b09090309031c02072312060f160504030609030309 69
    0x307034030b030a042a04034000d841c47d43d07640e84a80d550000c090110086108221140b1b61151905001c1203000c101803c43c0b42020b54000035100d1408030010110b4110740450300003125620703156904922141c0c08004640c1c0b08180310307130307840c074410000034404d80b035031f13000003a0581c68031981c016540c4e03001010f40306580341170f2898441c6450380d030242e0710b95610030310004000c1e61100b1011402c0f0f042060031070f60824405040c100d0026815660405031580a254413000140304403030401c0305c272080b201d03e401514070544400100185012101048004078094240140108004100180420081d10449041514055029080c0100118083c00201c0c080b0b80c42031484c04042000040d000c4200c0d0f07484c0500900900d000d0544805001c03441c11070324071004c29800307500c10001e60441038840610348000b80b07440700851070040384100217041a0340c01240b04164000c0c4100061a070800b00c5d26900400400c40442804c0301441d07084035203110b02d8000411090401e500344041581540240c2c2440344510301c2003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 309578624 1250 309577374 309577381
    0x207030f0206040807120c0b0a050405070603020c0a020904050304050d21032a0908010603030309050f010605092e061e0203180906150316030507020105040c151e0c0308 74
    0x2241e03100070580c0c000d8400c00041254a0004030028010381b080c45040c100f6030200941c035101c24070506800c0f9281162603413074100700020090180924030151546080843c1032841100003d580c0f032003c0c6600900440f2510040380c20f100082050f03400410b0001d21281c0c4412140c600000c0c19544540b400041c4c4811035000000b60b40203004100e100c0f030010070740d19907072502d011120f0f400c04e508440580901121203400b1400d00030a006904c06103004e41c801050210192402610b4074910500c0b068899141c50307024405d80d40e4821601d82c1001800c807105598074403040c18401065035500c101c0b071421180f044001100c5421808441c0081c15000c40160103075003150017640c880c4114804800000c2c48810030300b00300d180c00400c460b048000504100c81c240800045076045900c261210786507032000c0104085940d0f458006c903540808584028081c50402d030781e03418907aa41900030f40241138414a05401007510980240d02c1140e40320b800521040c0380b10354003508000d40f03880305400041101001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 309579874 1250 309578624 309578627
    0x1e0f05090616080712260a02130302100c021c0807030f0216030c06021005010b04150306030501021210090605010e06030c0d05010b09040e070503060c0f07050703030806040b0306060f040b03070f03060207030f 91
    0x3054011071003400600664958510341f000b50700c18640c2e02140c009003c0d0100150302c52403c40048050380c0d07103824196401d6401000f40d141c80d00c0c200034440481c00b0102070000b50b04041520240c0358507007000700c040744640e1003c0c1d041c0024034500b449009031040000080c020410311820440300d40d0b400f03880481c10505040415641d00b4040c500d01c24400300000c10000c0c0c61840c92114058540ca40015442c3c2c40340e4415083e42d00002c0c01038400c02e5150103005a2401e07041880c0000c00d0488001c018103441c000020b4121044102501e01c5124003000203650f545050049407450988603908004030b41c0c440c034000c13009400c124105030103103240c01141002c2070380010f036410940d00000c000740f41d59035a0240e00c09050740040c090030010343c030612100000581c1040040c0166200303480d80035a5140c648180000c440b0100d9903544254040828081c603500c5014a2424907141a500802c58030303c0d18010034075140d0141d00a20300d41c007551b080041440704690245c0501e6109503540031810440704070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 309581124 1250 309579874 309579917
    0xa08070c1401020609211308010c1107030f020103110f07060608062a03040507030519061401060e09180f0f010b03010e0d08150904031e0f05090616080712 68
    0x7503401036a4486c550003c0341c00349142c1142c1001100c0c40c601c0e4582040e1200c0984000d80381e0b4003045d450381d1507142050000c0d41041e4000400e180000c010031400389151114071140700300305000ba040c590341d10700b1425036000d62030480702044a0704000c181d8400d060714001000341818800c8145501030140460881b81402d840381e11340408540c0e00401c1d1042c45a0108001da0020348100c07814400e040c00000021000d110b01c41a03480c0d00784034290f080302581091400d854810307121500c50b80081005122a54000803031030b40100081e5484040e5070740f0030016200c6030f54404100440303445040810103404d540001d2403480e441d401002030110352554028107082e1550b540600c1035a400000e0740b080100d105041d91039012882e00d5441c40340c1180ba401003007030440c0a41d400c0e40085c9100320340c0088203050184099202015181c5a4806419850002c0460080424180c07080000040080c0d03d120921602e041843d00545881d81e5446276103403010103990502c040c41c1c04140112160141c0d2580c0e8034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 309582374 1250 309581124 309581131
    0x15080d0206010e06130518190b0109060b0d0902010c050609010221060603040b0c040510050301030318080303011806092406051c051305060a1505061603030e0a08070c14010206 77
    0x101740d07010702e454201001025010092003080503c0010034000c0c0300040821038003038402070108254a44107600d0921014120050308040555814468200021034000081ba030281039003000004100c0d110380300481e02e403001c0d8500075149100e610207220581c101036000300ba0345595124038a6100ca5001041d03a414181140c0e03180d48001d00f4000903001c07500221100f0360100d4130050207850241c0350740005040307006a503000c2d8009030001c001441055002031001081c001144c40312002071b89006015603481c07105025400c0c07036030144500704a08441c10b82080001d49040c400030310146045003001034842e000380c5046058014840380000768980141c044070a202902c01c040a0004032801c240c1014040c041d00544c1c0d500300041c4145c0104905101290080d2860b44001c9603001d0414075140418142e80c01052003030004000045405050450000c402d6616040101c0c000307001c003c405042070b0030700b00b01401b40100007403150100030083c044001582c02000c541f4401c1101341e401240c1c0ca91045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 309583624 1250 309582374 309582379
    0x2d091e0303011a0415020d0e0111060610021e010f0606050310030809151b010c0e010c0f1a0106031509020a2709021201030c0e16050d15080d0206010e06 67
    0x700010321500410001080c503402e40c060090b85080c1d40e41420190180316045c64400681003030500d01e1000d41c0c460f244032a2142d0074a0004808000201031940301c101c06440c3c580720303281d07449030300081600034007007644441d084081c180510250203000c10301805105804c00e10b010718066011030b10b14098030580340251840304500c2c0036282513940c0d02a20340d22456040c0d6001d01c0c5402541c2881c020b40e00202100c0e113480090140c201800101c09094982580c5407900740284094244090707640006a013822941142c80c000c00781c90346091034061002140440c459001c8114000314076184c15802c00a807892959020b900304590368196038040f401130b5400707140010480c50b251964100343d00c8191894900012002006554900c080001c0342d1101c00c0010031980114010001d01000241c2c802c024030420002411518100040c10148440040000240f0030040b500305045c0c807040e805121034001c4045013003d81c980b510409581c5400090350203005118510002c101100068861800b40001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 309584874 1250 309583624 309583627
    0x8010b0a0503120a030915020a0f0905090c120a06120c031719050a0e06030703060e10060e010807031b08160f20281403030f04020103052d091e03 64
    0x20410110301421071b0410a458000c0d4a040c800740f004503600c010114441c1c0da4841c00e4075820300b0b100242911400d0340c41948544003036010089003250500407a1290304410700069000d070303103481c106002020381c0c2d0818140000320b1000042040070031800719040d603005444140c42014170b81e000400038840c061010070100f05048015403890f0081002d0a081456402c04104001001300403079141d404c11201c0070000f1742c59140c00c0009000c0100c0391600000341c15070a081031130820501400010020f03038100d0400003c480000d00d02846a8000703031201030b250080303600781580319030300034403550080c1c0e00c1d40d514458240c0c0c1102401c1c0078071250507030070a00d9140c00c2041a110300c600c901c203601940112840d8054034440c90f48204030258401541100006054100c1000d42002c0380c410110411440d660390040050000d0490300700d03c0c49900075070901e00842c642d0b0f2000211b8823012481d1070320380c8170700c8450540f0a60702e04001c6401c91281c10140110b6401108132000551611f498010080e5541c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 309586124 1250 309584874 309584887
    0x6120714060a1e020c131404030c021503150a08060907180b1908010507090b1608093a080d020a0908030d0c02010605042306010e0a08010b0a050312 65
    0x1400c030003400802c5a0782c200000180c4104050310340014441c540600160042450382481e4a0701300c40001c5107a04846003008076600e07113004030b81000005880502403021030585c030001c5684004020600c42c00460301e01e0340301d0a09202d21021008a41003061080004600114030a80005403503442091a01c0040516618121018500c5c04490581c6045281c03034841c5070085480300900d000c00c1d141e0240610742030b18a49900b003400c4036030141445041040c00041000800500f0302661040b2482c0c1600c4007201001c1c2c90048028498001c4158025001c0c1d088101083c81500a001d034103050303191303460500e10103401c3c038850302900070f40d004100305400e2001c0700340005c80c0d40c054295901507043c201c08842e15505014650b800122007500d41c541c07616101303404c140d030a0154100030507041c2c0e4184000070020b00d2003c00c803100340c24861401c02903880002c81682c810ba6804a00b840043c00351034065440e504214007038280301549c14010b02102c0c1d030029003400c00180d981d88100110301c0c554188007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 309587374 1250 309586124 309586129
    0xd11070510051012050610150903060b0105210412090503120322050a0c050f0a1403010f0501090b0102070e04030f0c032d0201180c090b0112050c0306120714 69
    0x1102803e0540b480150860200d0041421082800c0180c0504004c201525002c0100c10140706182c01088000303140035542020503030482103c6003969480300c0e0105030b41519800488036030054116144903803c41c0b407074002c00c50013110700880c00b660060b5031003000020804026951044d641c0303d81038259210f50347c044001c2907010007a64018840c01c10400901164544001050200120607107030340e003203240c5c000c2c20420301c1041030f0000c010a4905660300c11340d07040050f6500103d44661201c2030800005001a0750b07080d0f1140320382e550390301c604019550711850300400900d190a5058054800c2d41000b191000c004000c2901c280d506503a490848014000111604040004118140446400b0780b9009101a0f801c944058040c83c00001d000c24100100030300707559184030f82088081d5006a100e020440c040110425501c0c01007000c10301c1441100120303640d030030410311660280c0c0b80c0414000c404a40d13800950280404484100c0b40740d094030440c0b40c40301e815124007080307515245100c030043d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 309588624 1250 309587374 309587381
    0xb1207061b0204021b0f0607030b0102150702032a0f0703110f0a0b03131e020109170c060d0507030b06040b07061805010c0e01120e10021b0a080d11070510 68
    0x301d102a1000d82480c0381018590b0b290031790b41c1c807407160340d0b04413552120a00c60200720b0203901c90198030f005d100d5003041c10300103034541c41f5140521010885038800100300038020030466800082c0417408500c0348890694401c404180314070100100d010741e0703c0d110404400003d506d4143c85d0000f0651368000442020805000700e201180c0350400034441c2c00145003111140514030903005035000000c4090315280080308504d035401c4540041081429040141c0d03030010b030036402d6500e000089003a25160641041c6400c2c00d00f04500d0741300d13a00196080c180c0155400c205d026490740d490900c440a4246c1c00c22030f00740294003d100000704180800400f08929070419140d21128141c107030400e00068403002d082d5000441030801080001d4000145d40d40d0003201d4241d2080b80f070004021042c100d91040d901c806074243d40214150b0040f5038410808000c40000311901000300803681855540e25003048260820f412100b085c901d0469410b01c030303003543c8045440483d48800a404eaa00140442c030009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 309589874 1250 309588624 309588677
    0x10815040605060f1e030c090937060b03060d0303180c0e040b07020d0c2907110c010e0a090507090503120408010f4206030b120706 58
    0x290700d0300301c0003400d51520380042c071295101e040d031030342d0381d181034680710007420990b40310060304503000c00070044030800710004d807410b0b136030300700c801c082c05440e50884040b0b10700c40e4904552846a0101080340c1e242100400760b00c842d880c0c154241b0015584144965a90004803911504200c0e00302031000040e00c43c2d4015042d0392240030440298580644a908119002d270b00f040c881c0000b03560a00003804209409641c7c0010903200402e10480c0b09040240036840d5980010078844010310b040c2e00c0d280e0198881022910800000c50b0507150600009040c060341c134101500b580501c01c07007260503510401640071049006400ca100030740c40e00403410020030f80240641c0412800c2c610108003680c09000c1380d03003180890144203441b141000001c508440d110348244410307e2800050b102c54031321240c00180c56459440e41074030000f1116001e10506c035000003200e40210b0002c00003060554141e40545107002054070a202606072032501c4039035a455038000c48c00403641042011601c00b151101d600a07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 309591124 1250 309589874 309589879
    0x6100f08071205010b040302090f2208040504090b0417040b03191b021b0f15091c030801151107180f090507060323070806120f0604120509010815 64
    0x102e0311a1540002c080341e07400e800564041c03c00107010015858405543d54001842691416217800c0100c1d4048451610003440744600c01d900881509200311007060702c0c000d00d000741c000d1001050f1858540790300602101c04441d40e440401d0302d0b10302c402e07202098400340d030780b2030825500d16121130303241321910140031844d60f070940c3c4c0b184c0347d42e04c202c21464445520150702d600186025003402d2a1098803824000340319000d02c00c2e4400c0561940d40e01d0481c16040e048141c4490b5039004040040392150181181144a0b00c104098601c1051313808401c0904803019801000380700c6403d0041240da001180d00d000301e45034000c0e01c09024200300398450006100742000005292140c04650505840080c601501d10f5081044100030f42c0d905400340b204056041109003080c0510750002e440f0052000d4903100412a55400080290712503100009990300c121040791315030083e20710501d540300f40131902241c14001c4210600380e414010313015203034210740586030a107040e640c00400c001c011055065080e03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 309592374 1250 309591124 309591137
    0x111504080a030e2e0e01020c01050f0307020309120601080c1c200d03120c05090a03110f060316020d09050d03080a020d02040f08070b0a0e040f15090e0606100f0807 72
    0xc03074a1004a182105004c43c0742c035481c1113004c0300c000908250038103804203055400c8070341c0399200703a07078000e0450314103085a580a54403919000400c91a50041144030358100344e58072040c0c41010000910300381294a42412100a4007483e4103204807410825000b580320b0842d04025000039900c5141980c480b0f00d0b1000c030002c030b0807554000070a0880000b00c2500824450008020384849070f001c0c44d00f8001d40760604614004c4908007003a000304013480003420000801081620590b5000c400e07010307117400101810340700d040441001c00028006848400075200782c8034108100d41c0210720420072030320000d2190300307000500d0b02c003980d52a02c020701c9020182d90801083c0150a0103201400250400301e4031050003d0401032900d103041c06e40d80250528100031b119130b82a01d50f0040c00342841007410744010440c0b0362880802c0d000750811001045c2c00350314401003c90307800b5042d445411040c40020450f403458441d50306000c1d520700d90740006070024049031801d403105c90083d5801c5802c0961450400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 309593624 1250 309592374 309592399
    0x91c0f02030607110606090402033a0905100309050607031805031201030201020708060103050c0d08071401020a03060e06060306270705030f01150c020f011209111504080a030e 77
    0xd04140c003c0b01c1d404045580c80c411004690002c10055038060b4080d11b01c4040f0b0306103138002983c2c0e0403c40500e043c0c281c0042203521a02640d2a55260801c0398100b40c2c040f0b242c85a5401414a00700c900445000b44107030203420354018464003503144100d400c000030700700030744501008402603c150075600c85200c03040249140002c000700003d100301500c000e010600c65056100085c1081074030382c0803007410340c403030401480820301c0442e000c50291001c5070051442d038400c0c909005180141203024124001c81c1c1446211a00103400802c00804c1c150386c100f1007552201040c1103500006e42d60260010b109000040705810240b041c07500030307511103c06056004000381030100d050b90864050300060008014000040b004900072409094640e4102200b090201c80042401d80103041c0070b80b04005c03a4602120076409a00b0101c49040010414044110f82c0d0400c50400a44020750b40c0c043c20400c1501c0f0080c0d182002980c0682d02d4000c00380000b048546c03400c070f43c1e11101e480000c0d031200008101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 309594874 1250 309593624 309593629
    0x3110d1a09120403060906061a16020a09050907062606092701060501120c0806010806060d0e0601150e130203060f120c0f01030c0903060504061814060903091c0f02 72
    0x40c0c0300840c480c40303012562144030b07d0700074181c80c8160b01000032410310030020818521540203445460806200c810318404003800003859413446c0b540080c44807840c1030b05215a00d44049001c3d402d4684a86408403204007181c210641c640184408102c0b01e2320000101e030162421200a40e08031610700820200030545000d1300c20501c40641d0301625a0303640d44000c020a58003c2c14040702115103803410400f00300c4c1001e01522541d001025107040004980000c1c00076504e001c1070741c040c00000601081081410a08117a50340d4081c0242d000e0048581c8d80060614450001c105603000042c2800c07101c4c09248106034040e406c00f07012207030f0080d8400a031001c2ca442d044c1800300c613001f41d00d000700607282003030061200301c001810b030540c1058113001d81d404180b030f000f00e544003c0740d5100d400014159950b0806200034400c01007003504019011903d42c052111441441b0320180074082554000c2d190b0b15840d542d0f9101d540d24440e041441140b000801e03031900800401c8450003200d0080030710035117600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 309596124 1250 309594874 309594877
    0x30322150203071e0c090b0d050304060f020c040c090b030714030406050604050f0f0c070f050105040f02030d0503070c11030102090301090305030a1802031c11060c0403110d1a0912 79
    0xc4500603400800d4010074030144240144a00e091207510200c0380c0402c0d00c2e441a002664054180c22035224050305400b5240c0102c0022419044410ba0b51074a440e10740003801c0800c5001c80034010b20850348070038410f14052013013445600d0581c0300c66110358a0a422800b107601300034400b5041c40914100381541401140041d0310540c0308050018580c44c101007040100c1c1c1000e000110a504000f04024000745050b400c00d4010b4140c3c030102d80c84561030711b08000f9900c0300480041595091005000401c640142510800c0c1e108a0503500c1c41248410215041c0c00203c0340301e00000c080c440b0f481c000c00c042a0a91038061000390004d1700e0000c0315804242980e5a0306c1c0120700064001042014440c0140b2a400c130307a0308010213000042208ac1c0020707a441c07030071022800404104074502d00b82c081c021580c0040000c80c4800355815480c203480c0019507900548400d40b11032215a000c15000d1500201d142e0f0f15640c070a40c03e400104111101c482c59080040a40d0001e120381421800e90350744440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 309597374 1250 309596124 309596159
    0x30703091712160320220311150c07030f0807051605010207080d050d020c011407050901030c0305010e07080903090301090c051302040515090604030210020a110906030322 75
    0x2030042c6a18101802070120903103028030700d10100340c03800812261880e000b424607449400549501c139118550840b240545001c404c0f0a40c1049012000000401410000101c10a542240d40240d20701c040d03000780c0114452846114100c1c2c200c69030070710006071443c50001d44140280320701c50502180c0d0313990743d2408045d14140700c00422180b0b0104199a030402040c005002c001001d0458403031405400390a50058a403180015500400c10320350000d02548403142c46020070b0403803002402c0451000c0c003640d01440f01d02d40000d040c03c85001c0c80310701900481d4100d51031036400c00c409a82d001c00466081c4005081402d660000b0043c00c0e8140d80c0900507680c2c0300307001f08080f2010300d20745810000f43c8410091450181c0740103103c100324540c0c9030005000c0225071801d0300e5907a130401000003421403080e0342009510400e1002202e00c130315070020b030b4920302c24801e800743d21074004258100608100100e0f04d05901d6801008030000c44402e03c800c1912101900ca40c1c4200c05032541508001c524100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 309598624 1250 309597374 309597397
    0xc09250e0a1d0109110f0313290a060f0303033305190e0106050d02040f03060504111806121203070503091e03040e042301021c0b060307030917 63
    0x2212158031046030101d032a0052100705002c03c60800e0b140d100001724002c406500c2c40808000c4005913180c1e030084807025000c1d9000200700c0801d0013045014000322409900000d04142881c0050f540c0c032594811401074644c600c241e103444901d140e500710007500449041381e40e50301680e00c1d1140d6180405016804003480804001e0301142810144042040404680e13403807004000010014001c03500d0146040d10118580b25988050400b0044080c1c4190361105400c900200000002c1c009142d1100d030080c1c0c03080c038517503004112103000c10402200701610420761060348408a004d81c0703800da00300440b8065040684501c40181034030307800240c0044a00b0400310b10700004006c0b03251000d00440e28200201c02c80c44451607522031401e6aa4050f0b0700130b0302c2c0ca009404c0301040501100241940341c084503c401502d07500700d09441c00d4040d400014079000c004d0300c041c5c03449640c0c81d203d010341780d001c1c4000307007030681503540314030048000e400c40384000c1d112100c103480d2580b07410101000808501690303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 309599874 1250 309598624 309598649
    0xf060903070f080c0307050904030f170f1b070506010b030603011d030c1e060c070305041e09050105010509010e040c0302090d030c17090619020715020f0c09250e0a 72
    0x608926034107090244010174803e0300140d00a004e00d40c2d40c035040301c0c0c026415103428010540f8a05059580d00702240002000c8a0220100a100c90401c1080c9204295040c1e81840382e0541741c40d05903040c0185840184160020001804004041405503920040c01000411400c003690001ca42c3d60740c03038100c11819600b0016a2074004202040b240c41c030140031003203050000700c03c0314100c0c0e05d1742c201400c1d2074007084001a485040c1445841601c0103008a8442019403010031544154154030b0741c031400c803206050100001d1650300a034191031440e08183c481c9003039401c000d010403005001105500d014598240b03d0000c1d580c079040c410f10300762842501c1d003240f801840e00f030034041c061a20920034581785040040f0001901c40805840040100e2000203143d900d103500103074103101c2240c029440030400c4513081c81c10540d000410444c40120b8605442484a503881402144502140c40787e1000e50259481c0071030f05107040c42d00e06034a41c20315140b01882121400640854040d91161048035030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 309601124 1250 309599874 309599879
    0x12032a051b0321040b0114030115151d220906090b0f060a06050909060a03080a050414061e0a1202130303300e07080f0d140a08060f060903070f 63
    0x81940704910700c400303e01c0d50141626156440c88002c2105006654040d0142c485508494409404c0700140b2001d070b5510032585a19103420701c50003a21005c410b8001945103190b102000ca2001004a490501502030700c0c200c10300c40e4802c0d1840380e441c030403403c045a0380c001140101d41d40d480b03008210ba218403100b005c0740c02d1030030108010100103004944982c007484420001c881d041021102c403990250341a0301655100400a803d4001517030024040702c000107801c45815078410010401c2c0c1e040c0341c1e9039a107800119030a1207003030301500354400259442d1640d070282d0090420003401800b00540b4140307080b12547e40300302060380c0160406490710030301c801c010b05c201904940000b40b401408500c10218000140012441d00040503903102c8465680c1c03500303103440c2011f004040140c140b190841c0e1070f04004d00a92a0740b03140110428002031021002500744541d1070044485140050b66046401d464103010400a0b00c203060450340e00c6001000220401d4900f03001c0b201c000d040c820034004801e071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 309602374 1250 309601124 309601147
    0xc05060901090807080717070509040204051807030803061314010506031f080307030f0203120a0c050c150106020d0f0207180b1003060608060105040305060a0b0d0812010312032a051b03 81
    0x1f07030343c3e114000c41ca40000c10140710545400303001950098040300c0100e0b6035141c0d0b02c240c08004201084040d03207030181c84008000c0c031070480300847c0140c02c04d89030003942d446410418000c4421107008030980084a40c0101300b5450640055504001c128162000b844081c0070010042105944001140e42002c9024001d05400c1105007002c14410f002951400800301741800c0c1c00e9000803c0220445e95600d40443e6841c447c800342c9030002000c0044910070006568684c16281e024800d14006119480600c04002e1060004411810700c0390010209542000030500c0803c03540840b89120a617514007110311a5a00d40700001600f803a6200040d810342030100003030103180c006044e107060010410041000601c0083e5041d03115045c03e20003d070042c1c003140090f6882905050183c640c400c04105a11544042004641260300c40d0b05845e00c0c000c240c4c01c090701030b50022400b41c04040f4130204030110355030702c803542d695a8601c245419071905a070040844816820090031a0a6070300106006a882 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 309603624 1250 309602374 309602399
    0x60f0708010e0609040210050c190c050102010b06030f0601020c130e01050105061c0e070302040501241403130507080609010f24031b0b1801080703090c050609010908070807 76
    0x40c8649440d802851803e2000724000c4180908000c1c0107540766503442c00086e20501c00d80c4d101c1c54400060340c400e010060843e400901c040c030415078807060b80d50f40005840d80148103203c040c08020304943d0079a0380ba0019541d05070002072410b41507002d8500c0b034412a6036280c801c2c940c80d440d07088000a01c0d65550314400e08445058001030f0003000c1c10018103004400c442e0160a000d01325200104403002017056203802c00206da03000a401505000c004900c800c540e03045a4404181c250003110912a600d400303d401c004080d484030399282040000c540c1b1b002080d25180c400030301a0040743c001a84e0b441702d0600e80f2a003210400c0550759940600d041c1d41d621401900050101803a00a10341900100700149500d464403009001c1c00c0c80e03814242080584100340001040420712a075202e664007103215100156440501c0d002500c10702c001101d46019100340382415400402000500d42050288500340c0e02205503241440034107040007071900c1e01041844090700896010302665841c20410780d400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 309604874 1250 309603624 309603629
    0x3140102073008190c0504050a0308070b0a060303050304080307020a0f05060117060124120207050d120213050f040f09200a08060601050706020d09050606120316080a020708060f070801 81
    0x10481c8103c1407010640703652a107000a04c000001c0001c40c130080d294162514070441d80001c4c2c102c1440300c4004140284200a085c072940901c11184007517030781048a5003114003e020003804101c0910100300445d18810107180d022101d401203030f00d03000f2103845401c00c04000c40811117055200a00600c0b4100d450071204080c3c080f0b00000b0062541000c101060640000241d480314078510168000001d1190003061046041848110341d1602141011070700d031900d4401440100303c40c0c3d0420540354a15101300c2d11401500411070040d903040204025480c0ca1004c5520784c071070b89403513406124180e5032081c440d040d8440d4041d0403003034188020500c034445400c0c0d16140300b081c0c0c068003046843c401043d11540103009107001076486d0070500d8124000e002c0e00f54001c802c98030300010a0100400064030f1805103004464109900300b071070051541c1c9108003256140c141d0028041c020004002c170307001e000c481485e4010307522450744440c0c083e460502d046621626844140003031107185c64200c00003501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 309606124 1250 309604874 309604877
    0x2b140307051905161502010506060403110f010311040b03041707020a030303150f0b0c1c0f260c0706050a0c080402131b0c020f030106050307031401020730 68
    0x1400c40a071a0700d515818050b80c000714500c6404075030b00c10050180040d640000720314424480d0301c0d40740c04907a0344c44817501302840d000d50b00e80800300e0007505c1c0200c240c03001c17130341d01c14661440f03180c0c00e20031f06c901c46400110f010305150311200c040c46038084650240000d407610780e155588a00d09420120407040004085e40e00e43c8900700070203005a12445805030076250907040200d01742d6079440d080f18000b03e02c0e6000d6500703240c42803808900040d1b0b600040503200200000c545c0109a41601640c044107504815008110000106442d00d405125006003d10303000c0d620300c00281c804ea5a0b0a102c00d42103405000082000521104001d1103110780c1e80c10a404400c1000800c081540103007441d1130141000c0e1082806040c2007440a107550409024410f41309000ca44451003044042c00c0381099840c02c1b0310440454100d4003090405104510850703100400804015155803074003104202081824503155400700040b1010460440724240540c0d200000110f5446079485c0945044c80c10a15440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 309607374 1250 309606124 309606127
    0x1801020601140f09070207081f150509070f021c0807020d03021c0914010f201207030e0312010609050f0906010c0308060103060e090607201b2b1403 65
    0x6403900d034550080b690740415140c12030079455100f07060381f502501d0b5210400070710440101086200320101244500400100c09000c108800d44000b2074a122701e006242e006410b910004d40741e54410074142c01c80240a00656046140941c140c28003025140300e0040800d60704002c1c400c050398100903d01d50b491041c41d046003000030b507081260300e00c3c0c1c0c041110414140c40d02250010b00c040c042c141b1000300d100c00001c004034040005800c0c09003010b04141405141c88000c60707480c20340302d0421141c111480780102c4026a50300441036000f000c00c0b20304102c01d84018808046a1840090520b000e400f02d030710383e0010140342034104103072120b010040c03034003d03062401445145d90f0041c8031100314907031504140b030003950340c0f00041f00140aa5031004c0c01031059042408841200800d442d405000a5550441c54450540844c0c2c200c0e40c10503040c0c1d40c10b9100000f101180d40c85105c0d0703142c80060040c000e5000400090011600e203802c010302c0c02c3d000000586400411200320a000c00c00f01f1814043e5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 309608624 1250 309607374 309607409
    0xc0102030f042907050c10021902040c0903050601060201051b04060516062c010c020c010914010c2307090b0105090d06060801050705030a060e010e06060a141801020601 74
    0x25066004a2050036046407584100d0380c00f080c00c03a201030740f402d100c400030310782c481c4480c0c02c000c2c0c2e03100c0200017410f0191a0315508854524408112001900d40c03001a10b150440c02e6420b01c0010545500c0c0c15080100307198000c0009401840b266000302102c1e07001041d00d00301000014603503003100910300381d2540704020400010f508034003601c0340c501d480c00c0d01c040e103490710b41032030006030803190940440c031454504600d042c90100840f41400d4080b000c0200040e4880c54400d80c1c1c0c07819444c4c40c050108055203402c00443c03c84101a9031040c406242c001d00070794907507407020301d80102d05242489601000315485a140c104010780d40040050314401e02c0300351036242c00a02144148180305014080c00500075007400307880d4015900815140008100a1519120080c150f030415264110b06506112002940117405004203040c0c0c1c42410a0b0521501ca140411420341e05c8062035806208002c015212480b04200c0900b9000b455048001c0002014500090806905030801810214140c010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 309609874 1250 309608624 309608647
    0x1e061005010c020a15020c041d060c040b070b0c0c0715020d0f0905010f1404090c081e0106050a2304080709020c060105041515211b030b240c0c010203 66
    0x702e8400c1d03400c0861780f054036041207041c480310540d5035800a0800100d030721461081d5625801000c0301038144d52075900c1e491880207144c07241e481100149001030213850040380c1c0032803a00c1e4211107810006454034112040c65414110150302c902c1034003a120000c003400b103030144240607102c007942c84e00100c000d01c0403001405c2d1019a02941d8100104442c450a10720302070b0810601c0104440e1401d900d455031921070030701a1020060b80800184508042981c5041403102000020143c842c0d4440030303030074084c3c11a00b40d004015488100f0005c0700c6403c0740003143e100301c2c0b8030390400d50a07020b546500b009015450865980d110200042c41000340c2c551000000c540380d030545000325000701d404c21006220b05103c0590ba088644559400c600700f80d415600288800545003840c00d445101c6503690a07503038112400003034280fa4490405a6081100e440395101c05101000102040180d00000c45c15400c1c04804010103107070048000751449048100302b014500c85103092008501c3c26011112 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 309611124 1250 309609874 309609889
    0xf090509150c04030203060c0408070515030a091e062c0a0f05030417010204140616020f04061503093302031e040f020a0f0b0f0c1e061005010c02 64
    0x101c04219291000c040307251118070a085400440e0010100e884174141904010f010794094410581544640c0e0400241c82c10301d80185803401030418020f50965580304550170280940c2d641c00c8900e0a011241000110b84056034404201c0c0240300009030305603080e40200c3c034044110781d00d0b09040d280100c848003800d00014506909503101110300c4098074070b460b0440c9140500d8000c4030525002c40c14409030715034154050b00460b01511400c1c01c2c6c0300100000d1152502c81c03c03031072500a10b103d41c1003101506000050a01c003201c06400060141c1e074840003000c03a5945c0c4400000069200c41c4100c051100380898080400d614100d05401d1021529902131001c0080040d82902500400014103180082d8000700c040b12482840241a00d02031a040c8280201140100e00c075443c002e01c04210b60070030f07ca84030159480c100240b0725143c0500c910030130341d07005448074280303c1c8107003088104d4800560f1205000010000010003460034000381a4250313a2041d0030250400c980c8000c20340c01340e66a1403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 309612374 1250 309611124 309611143
    0x50606040306022206110c010528020a05010e030406090806060a060f03180b06041a060a0c140d030506090a021908180f030d0e12090402160c030c0f090509 68
    0x2c07005070364140e003452250101c00607551040c00702e52158400034030305c0d400480e0050b607020741d48103648860f00a2801582c01d80120b02281e680c49103600003002c0b81560310341c0c09454403109801145c6140c200d07a07a0780c81c00e440210340b0201d050342000c10208016a04044a503001d04810005007181d40350040105040304202d20591040150302c0c1c41400d03955000c0d600c04ca02ca4120b49551000001040c1401c80c840c0c0c1040d60b200b030003030341740c08a040100851007d01d0040c544000b03051a24144001c0c0701155046d00c005001e0f5a0084e010b16075000b180020868102921980d13200400d2902e4918101710040200408080140e030041207011411568511412400403044c103010300645c07282020038140c4a0000e24040d80c503c111501d44c035080030004050302011441c2c0c0c3c002d0060b017902c880e44a40b2603c1804810061031014800302d540c92400750040d00c101c0000c00c200f0f03444180c040d07c81c20002c034103d5009a84500f406101408a000b03520459405006507460502c081e0428000c1e841d510480b40d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 309613624 1250 309612374 309612383
    0x1020f031611150c071a0c0604121812110307080706031d0303040f0b01060c150207050111190810230301110706050603190320070306060b0c010f0506060403 69
    0x9589800103980c0300240d1401d040303110109543c4074184c4c03c4032242d0304c49050254152142c02441a040c9071580c0c0301c1110400c58000700601030a03200c1d951070b88001c074280c1c3c007000305205651840036440d080402c440030017000b07600a40d02a00300079090142800c1043c041e8140260448001440040000603800c070465041d8a800584002020320850008140c03c182c1d09031400004180002c0c0b0a21802c0151042d0040040201c0c80c1da07110700035034a0f00000440104820034003144091000c51783e078003401d003050042d400171174040c0350314018548583c407584080c4090600c2e00c40c04013171175030b04c40d017129802491035018280c06403e0840b20002c5c0d5502d68000c2400e2920f1168001c407070348003904020b050804804586403110340d1031a004000d000101c40180c00780c820303208882d80340c136a002c12030b0b0007441e01034446000c00d41c1070390080002081e0404459402b80300c0d4190000008041344603003030080c0483ca035a0354641d2852103101e402d444a640304080320509103401d00c0380b136940c3c2408079803c40303501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 309614874 1250 309613624 309613643
    0x601210305040f09020304060e030301060f140c010c020304090501081209040c09081002120a060e1f1a0d0f1b0f12050901090209070c0f02040b03030706090c0501020f0316 75
    0x19490115450301c180d400c100c10350400d01800140703500700c58000d10302443c89000d041c44001001100d00340c6d6070109100341e40000301055511761f4243c3c0101000b4061040304503200d40703441c10b2040c015007950400718003440103901c0050304100707451461049034050110700014041440030054008907500403141000d00c00d6503900240d0120a028002a5005000100035580c00080112382c000c001e4001d00019181c04040c54002110141d407441010b05a4108481480c480d440b0407440c200d14103104048001d501845800c0403c501c0300c01e00c0305e00020048000c0c41592441c10f030384690180d4401c0e40030002e00c581012000c50149200c1c0914209169151410b054002101102120218002685440803500c1d1205010b0403500641201035128005d544d8003059850b90241110043d00442001c0e14128516408100600d843e40103e0380e034600040403a0300b04001600d4580480711032240071900180d032010100101d580601c1103d0000d82d410b00910306140090f00b01d2003440002c503000078200d003134 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 309616124 1250 309614874 309614939
    0x60901121b080f100635010602071409011a0f1209030a030b010201140a020a0327050c0d110f0409050f070905070e0307090c09080a03050301210f11130c0c0c05030601 73
    0xca120003040295141b5140b0801945d541501035140d900a00036280c05003119041040c4030b01301107810302d04035260f018400c2d07400f200f080034441007a084081c8908000400700404000720050300c06a80c011451100559502d80f140000078040700e440803581419a414603540c024580340403200607501c4000c0e00c60241e036810503c0c1c400c078014002000010a100d0300702d000907852490490000200070301c6041250ba0b15150007003000b4403070b0301c00300b0001c010000e2094140e590741400c2044104d501409480454841c4040c4d841c642084192440001c40b84d0000e9020440f0004500605411004038103004c0e600030083c40200c1d8841d2201c1c010b951126807200c2c00b1a02c51b5200d05600f2006207003090a0b10803400181c58024000d50082c4035198901d6035200c0a0003008038150301600c00581e02007616044030400e07640b405460b107604071145a001d070f0400d40f014095002070042044600003075450400c0794003503140501541e045c582065000390b110034014840120407140c5010071090b00c4220356a441e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 309617374 1250 309616124 309616187
    0x405040b07031e1109040e01020906040303030903020102120112060f02191d061209060108070b0703080403031401080c010809030322172b0b060901121b080f1006 71
    0x140b15911081d0101d00c4c0c1041c070003000398510003902060f0800c0701c003445034920f0041c91900780d004002100741e004104120800000c0e020b41d200c4500e040c424000035040c01c00e0108040d01b0118268810400b03c0e031203070210b0042160a00c141110006156400c43c2829240907000104840740041070090242440091110060511807203100c07000040c5016070783c0d5140c0d40308081d0b41c681500e088490307200768400820328030300c007042030b1040d102d00c418a60308101c046c1e20119080400a4000c1e002d00d951040c8069100d00801c8181e4003920385880140000f6403407a000601c60000103003e1440c941081c424801060080341005540f4040882038190901c10750070640d00284409100f00104a000a505400c90303420005810303006014040c4180795281c04116503094441c0c0b4600694850410081c076582c0d5805244904071901c0400700000e28800c4d0210112032070041068504040360080d020880040003000030194080800004440040d10744000a009613032a02c1c0b462030400c0c0120314205450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 309618624 1250 309617374 309617411
    0xc0203010f110a11010b131a040501171002070b0a020705331602060a05090a0c030605041e0b0402040b01050708130e060102010c081807080d030b0109050405040b0703 73
    0x100703140420070421105520540c0c6582c00801000f010403208020303100d40140601c200024084043c0040442800e81c1e0014001041103040d204a1203200507443c81d403540766403103041c4c042d00180c08804103500c50700750000d16040c620140b100e0201c1c0100b11503000542c942d28841d4018500c96000340c0c5840192400500305080304c5011450501034000c244919030151203e030750402d0b01901d0350461603c51850034514660107546c14005644030314089010401e040d0320407039214030400d0554080d440c60341c2d10481006001d520913958191241e0510042c800d1042424000c1e14004001241003182030f0340d001086500108040c2c803590b42c4617032038140c9900400c101ea81250344060b14503035402c0240300120030100305004504091500300001107082d401482a240355021301d4642d5582aa2039880c1c80000e51084044010240141301000814201c10001103212201607103004c691100e43c00d00041c84240c141d404144190f08003011720000c03030244d80890343c2107100c600d4003140000c0910703c070b80c161 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 309619874 1250 309618624 309618641
    0x1a190636090515150901142e020307050c040605100509150c0604060f0c0207090b0303041221090509060904020d020604180f0204050306070c0312052e150c020301 71
    0x80c010058072000d49844201c401c0e104c1c61003c01000724610344982400b4030003100b4001c6241e203282421540d40356103030210500b0300381d20710900700c03903490042201d41760801000e40d0440303000740c4e1011422200304402070015030b490381ca0aa90401009240c2400a8039a40403910032030103228000a100035540c4410200916203180c00710399655174616000403035a43c8604840603940305180a1003c000b11a9600881c2d40c0c10071583e00074100c01d800e05e1101030041424260b0740e6490700c010000003494400a002c4112030f28058025000482c40d03080038000480d10745c0d10000b0400041b0a810300c4160341c1c604c511500a5001d031030a80d80b81d80c5510101d0452085100f02961041000c03c000480102c8101d03192901244000300307010750b054000d0304005900950180c160306400110001e07240600c122501c95000c1d00a10f4913080d14000c2c08100402c40b03c0035200c07a02e042e0b15401281500303038440b400c60104801d04401c090300032460a039280703405c3d0300d010600c1303420046080414010743d502500128032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 309621124 1250 309619874 309619883
    0x6082b140a0c020108090705090135010204030b090606031506031f0614090f01052403010f030b01080319080a02041701060311100207050d1a19063609 66
    0x50301e40105201602d102c0c04400300300c3c00078600000260725000042070301412504041c101b00b80070b90030110480d451140c0403621207508142c3c440e2454281c03864802d1070055842400c00141d6450a50410b8001100000d001d039006602400030702c07205480000303076452030304441d0100c80680d4440000090814040070b1005008119038107644007280c2c0e05a10503400c446c81c03051100c0c1c0da40400c40c1031250543d02100d1425003855064010032803800c151480d024223203c1c05074428844400004036030303a50f070001e800512101840d0f00d414800c2229040403640034142450040d0b0401070500d8040c1da1168000d540e9804015030307080400c060340d80075016a07021300080c0240b1941d0704070005000d4000d0083c0d11041d070700112087c0404440c1d003000901045c447c1682d50180c2400d5003000140664050846821520110410b05c0c0084c4078180e030500c0c40c010b400740300d018036101d10304d030f40844150346444d04070003070055042c00c1040d1503094020700400341c03042800b51104440c060200c60001030115190141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 309622374 1250 309621124 309621127
    0x308040f14030c100516091e0b03010306090209011406190509041d1002090105041509030803130b060406050102190f08030903041e060e01030b0d0c120606082b14 71
    0x1592418081385a54000c000b207001000b040ea41c001c1000e0800c5100180310000c00e100e000c0038040c005e00c0d240c0810b461440c0702c0441c0011307513a81c036102480303078801da05c00c2c1e8140f6a80c0000200310b103003d001403801413001c0c03801141441b0384030000540b00d2094140080f000c9140540e0f140010f4002d0742911900132008004202d26442d03440540d24043d600c0802800e140500c0c03c2800801140341709030b032041c8178180e4920b810b0500303190008550142c10703038181003407110113000003000610700e1000f18803840d001c0140c1d80c032881d0145040440c2600141c0202e204509000c400d1005c2e90780043c421032103046044a4002600050800c50781e2071086090181c022000042003021144000005000300d0f1f000007114440345040544201c2c0307a030494024280010030404162500758805c1e0482480c0c0c1c40020119060034289a40324545214990b0005490400308884101800740c107100e1b00d00100321142c054820030103c07110002041212120500e11035042501880d40d5521411000301d0050403840280d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 309623624 1250 309622374 309622387
    0x50307171306020315010201050f251803121206081018060603030905120307050601090209220b0109090e060f07120507051c1404140c190317070308040f1403 69
    0x22506148030717903010f03001d5030a10003c2803101e20881c1890784242812440d1580403171001da032940da410822070103141005049c5040e0a80b420304640e10350011440360203040d40c00c44080101030480901c000c003080700940b81c00f070104101c0c1e5000c281440d802141c00d600050b40305803420b807860707080c1d07070301502a048518100020003016000f60b481c00503100d0131211901c18103000c9031b606a480c030900f00000c000307402c82c0700104000700b429006020701c0040240326120b28150203e07510081c22120100e906036a40701c0403050029600100d00202402c2d80550903c652030a10303628941d5220702800380b1501e40841d0380003800951180300f40c2400e80e09484414052400c180c48000c045401040d43c412a00c92030300d21614524000c0d109a0b400d40c181007217905050703512900c44055000303401612290900510310020819038880354a03420200104800c07a0703e03d0305500300310249016100d1184805c09003081404042904000c90541c813036400707562103403504920b18103110300302c00c00720b0700318000c0c440410702 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 309624874 1250 309623624 309623641
    0xb01030f06080f0c0d080d0507050d0f0f050106050408061506220905062d15120108010c0c03080a0510030204020403030807021b01170a0209030a03020703120503071713060203 77
    0x166000c0080300c0b002c650104d44140200440d4404244004020240402c0b5080c00728803a50001c82e809038183c01c3c0756003000d141d0403401040e58030190101d14119134481c10701e00200c00074428140900074a14003c0c1c1024104800c0680c3d54502404540c0309221510fa00042540d40004039074582c040214009815041c1c1c0c481403801c251103000b480c030560300344000600c043c10700c10140355415403100300e4003140096541030701500c1030f16609022303005210289045600300c54100100014541c1c1c6510403c65858841510b084a1410740d01e0000c100d4800e5101010036405500c49030417181c0d4050010f8079403646558142c0181c01544025005070011900005060300441d240b403141c80300341c003a1201c00440101000d0346010820103e404600c0306400c51803464804424181d0000000100600e0007c070b900010b40b6020034040110016800b104090040000980554001c2e404c5400d00905509241c0005821408406400424005480700180445604076006001160041011562401c00c00034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 309626124 1250 309624874 309624883
    0xe03030f120405010c030207020a050f01020c0901080c0a0902040f0b0d0b0306011d0610050d020f070203060108030a020f07083406090510090308030c070f050f030d050603010203190b01030f0608 85
    0x4041c0c1c0c0f90752a00c0d00302024140640220f0346083c2e4014034003040c050a20082202942e00d01c2c10382030452080481482d141d44600d4612406800040d0041003e80c1c08201081441e03034007a000307944090300610007005810459982c4100384d45580c0c01d00d9884100e80e40180e0300030140410301a61500ca200c0c00040c500041494070501c0310043c1d0680b00881c0d039a40c09010a15100104000002d070b020800b10480c00341603070141c00190110ba01c030741e20f00035141e0006454010281c02481481c1c100003004446a50100101c01c1040c40303200c0a02440340c900040280c85d001140440040301041503200004400f42c0054240ca0754640b444107101c0321b07214480240302c1429400780074050b804841c2c2c0f9a1f121809030115000300ca0380300840c107256a41d008006041c1e50000c030400c549074038140307030030600081050010342901c0760040700458071042100d002a099030405091240264410002d124114a103a483c203400040300c10404034500307400d140120010560341000a407814030f030842c0811030800206 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 309627374 1250 309626124 309626131
    0xc140403030f030c050c070504110705030c073b100810090615030816021f1718030304020111160303030b1e06070b0c041802070201080106020d0f0e03030f12 69
    0x3e408002107145100150b41e1032140c1d0100c4079066004030003c00051610340c00110702861114045402c00039586d44041c9150000340303c11440f0342003102e00784200a45908680b6102824008110b034011035903001519120400e65008007802e078440004d220941c49a000030000d00540c030032281010000c0c0c08010041c0400c2e002101e0040c1030640161781d9600100d03540c400d0f02c1d00720308003d2412014903000d0045081c030b404100d07000447c1416044081032031304800e1805240549405009070511420640258001012034280e008031000e0f0040b4000004262680700c1e40c20b0a1030f41015004440b414641460016400c19040d5030982c040101030303154010340c5a0060517039210080c041c00000c40b1010b040c5100300b241c1c000c0c17003d012450102e4040b84a42d6005402001d0451506481c0c103e0b0508944680e0082040507800140c84000c41d64071403002030040005101421411180010042a07444010302b030301c2c01c000260046116541d801e0044403140c0f01c0a05505540d4078400604081511046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 309628624 1250 309627374 309627377
    0x903020c0607050c100201050c0f18030d080a05010503010627140907080f032b02071704031b08030a0e15030103051c050a02030706020a03140a1a04021305040c140403030f 75
    0x841d4122051b4014001c85008054116503d410100201c20b1840190400c8944e05649500c02511840740c0e1414882901c41003c165152403443c0f03005c400060960302c060f844140a03038542801041190031000e2203400700c01c600030400c1401a080395104010b0f1849403100d00d0000c6100013802104100060200120350104094500b000300c0d2000d01038690065201e110b560b100105074408a540aa559035034000c01032040040c107007821511002d0600d510369851080c650720000c1c050041c04100d0422220001129603803c01050400f05240d480f4022014140c0500088640c03510703e503a038054080f04102c1c00240307815104e40c2d4074108590b8880352107950b103000c685c810071000b010b10310940445241c100140c00940c68034519036035060007503002e81e0141742055941c011070403284003020031079401b40390790140124500d0540e80b505c000e2000b0421005118030310421440c41f81031803241c3e01c070045030002c0307800107401c102a902c140e0f0600000700040011590008002c001c254001008241e40d601c03a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 309629874 1250 309628624 309628639
    0xc0c060e03160e0103021c0b0a05040c1707031106070506040501020d0e160323101401050109030f1709030d050a0e060c1f0f0c05190c080307030903020c0607050c 71
    0x10b80100c5034941a8000c00540040e031070014005400c003482610340b000b044855400346080c0c5902c8086603494181c1b41a240725803128107103c14000d1801d00200604205038840c02c0968034000c8507941d4401a1100034039440781c45c44684440e5030b8050075108a80e40010540d11a4a49843c001c1c0c000e5010340c55440781b1a1401551401d60040007a402c0e80151030401100207035030550305c0d1001240c50200003000c495180d881010a444d0080c080c0d14089600c404011030029a8058228a4104141c0203141000740003102040416100d0101040c61a08844040c400003200b1071448914400c1a100e81e40610881d001450f52130f50210061880c0a01c0f655110550800b0004000943c8220030000c6829842080105070f142010001340b200d510300d03610b00045038940c0c540c1303c5054800110308800420303000302d2010759081240070b9615047c007551034281540c548030740d6110031902020300240300b0183e0701c0107040f0230507000b0404e10b16980c0d801002e540d100c0394903142c0f40d42c2d01d040896050340610348 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 309631124 1250 309629874 309629893
    0x18182012011502030c1506010909021206040e03040f0e270a030309150c05091206240d0b0c070605161e0915020102040603140c07030c1136091015090608030405031b0f100c0c060e03 79
    0xa1608600600d002e15324007404040c103d40e00d0440203403070030000503211200641400191040c6500c40c21100d114281c48140d2100810420810760042501e2811015040a000c0162980030550295081000c00c0ea00d00c1c003c41003c00403c3e0060512200180320404040500050002d5030010340740946c4907079010304c103607a5000c0402180c0541f000c2d00c04007050410214120840308203030031a00700b02c0c2030f1408500070355a034800c1581c00300850070b802c40940d600007014000c040c2d160207410101c0c0c4180d903010700282404454440341c1c2c89054005410001d03035510b4002000345802044021580041c410082a0b080b1410b0409140d00070001c011012111032a80946a910300c0d1410b01c00c0343d002d009010305507007840861015007040c1c048989070309000c0700046101c031003030f00c030b541c01a01c000030055480e141084285490f004844e55650103c1c207402000364030310b903180c0e140716410f0321054031450003510f401031040ea100c1c0030046009001000e543c0f40402c560354880c50f22241c0035802c5040f15200764 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 309632374 1250 309631124 309631171
    0x51003020a0b091806040b090114130e0705010f02030c120a080f0f0a050604020702040216030e15030718182012011502030c1506010909021206040e03040f0e 69
    0x802c150140e60040141c602c410f916030700d0b101c51355602c1003001d84046814420940000c00705c5a09030410554150707242e11003641070804000394815079040c00c1d81005084040415159103000a00c034540c10804201d0311005058428000d541200050404131405074807459000422508840c8090001840000009070b0980020300482d0258803202c6040000f0340b90000382c5070207010010002600940c080140d0801a00c8501c024544045908900d02400b580f034a0020f00340c107000090280714044902c441c10411407400c0850b82c005030b182c00d14231140c032241d41c2c8007020201594000695030f0100311f43c4030010140c1e600300c40106c1c00d40300f21550030001903100e09a04c2c4d0146080b0090840b40c0040180004201040401030041480c01140d04201042c080145000010201461000082c4040c0521541c2000b880e401030200c02c803055040c1070008202008804004000780e1003107444080c036040c003003000e1085802500503000c0c51035040d5124400c0c0d840e000b01c00c1e6680f48000072404945141030f03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 309633624 1250 309632374 309632377
    0x804020118290c160f08061e0a110d0207060b09010b070206070f0206360d020904140303010b120a0c020c060d0209060d0c0e042f040801051003020a0b 66
    0xc80701000751400384100e240b02000695112106061032034020008804082801c0022060f8074038000f4030b914103035081842e0b64403181859840201194007020900066483c8503150409021040070001283e40d514142c02c1d0180c500c2e60340c2c854081d00001030003604072b4501d400404a007400b9075014803071200c001c41400080d01c0244118803040c3c00a1205100528000004115150281e0191605500309800046540d40800b115a040495400302c0510100300107603000020010811f203004c403180600045138012041f20320080c070502c0103d0000d002c204c209008512494a8101225101d607102d074400072490340020400c2000e040450006060000d01e80075901c84500160b001d1318584100600b841415000001c0328128141c00340311409507525020080c2100701090980810354a100c201d02a210303000117081c00e800f0ba410010601d0182501c05080a66103291b4001c84c000040407140f045001c1c0100e0300141815400d01c2c048c80a04500700620800303580c021561071074482e82e0b07600d090f2003e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 309634874 1250 309633624 309633629
    0xa0c0303080a0b18010b07080c0d11150103020114090103140f07030e03090307030b130f0c0303090b070f020120030d090c0602030403120f05090409030f180e010506070602040f060804020118 83
    0xc01e4600014400c050b168806061004e100302d4449040c0880901c940c1e0512142d01482b1000813814204020b000c41c041200603c40640c4080403040c550550700020101c05a000a42030704000c0010f0181d0964800ea000020365059071000e08500e0610303503070003140c0c0502564814000780c201006e0190b001000310807244000d40050042c0315180c59a5140b90001c4402445118000040c02d52040810402244082004e100e0701881c00c5150640c900a000d00d0140c2c2c0000850075410b10554000440402c030701030800380c0900780385000d040000e23148003080c40c481ea03000c5514003022030110003400e029003004038802e12440e0f041408c15101c9070120394078000e6110203800701081040203500c00f8060025103901c4681c0c3d1400c645003400000104095403043d2100718002040b10380211910740d07004480c404014202148801000d140a000804204041c003449109c0e00c0d001404000b00001581101c008201d00030582541a41d940b43c043c000c404101e07010b03404984051f20079071207010096160700c03d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 309636124 1250 309634874 309634909
    0x30a1416080c0409110607050a0605011a1606061d011401110a031d040c1809020405031506041d1c080f0103120903080c0304081b030d110a0c0303080a0b 67
    0x1010b40303006040101500f861075040e24150380400d03070351a90307498032030007048414054002414089403d01e001011110142d0161811540e81c1602c040b01400300c00880741504802048081989201d00f4540c000b0704095016025168644100001c0c104621006904990700101210010708452005590218038847d0040386600a00d880c900024000c0044480c0a81030304140102c80300744101080490b5040400f00c000700d180031106401070f007650409070707018000031201941401d18220109a83c3c0d022603403001403440d18440001d8a03502e0b244e1060500120b0080b00303034529007000300c1c115200e01551070654003a200d121804001c10780140000390060740494124441030303107552240b03040303d003420b01032800b01b1280c082e000010550441c040c18500040102940e5128070b04100c040ca0240c07081c0c2c0d000e038071403000950001682c1c1c0129140707100c6080340c10041c8441e2154410a8103219061000516031400200088281540198000d00c509100315040003a050403008100050011040890 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 309637374 1250 309636124 309636133
    0x9060f05010e131a0a02090910030308190e030417160b070b151905131a01140f0a0314010806090c1003060f030516060504060507061a030a141608 64
    0x8519009192400f56400e00440c6140750481c401c410000004405944aa07402038000c20510000d19000725010780005601400200d014955a0046c1400383c0080102541d03404404001e0f241c0c5529820490500c015902966500c0e512890080c10b8400c118800c6d800c11300c500020071183c0d135081c1170050306483e006042142440003a564011031000d0007000e10341c1c004400c4c035007801b450301c80c1da92104001d0300441d6103c0680d8101814013079003e04202200315420b04005100c4c2019202030420000840c0030310f0f1030801e07450803062003076480c8a0400c6943c0410f400103544180c41c0d626510400703840ca074003c0c000c081ca076680c00c0c0300b5903140000d58800b113594110111142c4540340c0241ca214603100e183c100850340d280d441c0403205010b00d0076402030b501a000305040158100103542c861b80500b40c541011820701c0d041400081c454040c0360740090070990794985940c1c2d00f003012908010720500090855481e4003035482c084145d00c241d00b00d01d440510520140010440c018110001520780000090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 309638624 1250 309637374 309637381
    0x3050f22020f18090f010b1c0807050304090b01022e15080709020309060606041a0706021201060f1e0e0108041104060806090c0103110403080c070503010f09060f05010e 74
    0xc0c1822509408200d03448072141090b044107807038400c030440b41c1691034035a900c004d1038000d00040c02d19221081101059260921002c010341d10700041103258108403a0740c01c0d02c21154501030b03002d445032000161251102050004401e00305800c65440e495081c0e007601c1c4000c42c074004c115950485482010517107151543c50201c0d101003035001402c81c40440f080801516501c800c0c01d428818590461803490341c0000410903010000c01c20682c00100c180c4d402498075280c02c1e030b010306805020046032041140040d00d0310500c82a50103a450302044400075494a50b5a100f01401e4841650451000300c3c40072261a45191040792017424404915240c6003000b1400340011a84000028001c5420061040e8010640c0e00c0c4c3c6d108010107025110300815940c140703202003514002001074501d0400d403c00c00c12160245c070305001d03034048903400a14180c90740180b1801c28202012a008250150310780b24a51710391940c283c0160314151301a140030486150020b070581c0a44009018091441d03040c00040f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 309639874 1250 309638624 309638671
    0x40633050604050a090f110f0403061a062a0607170604060b0306060f04080307080702090a0605030a080c01091202060a15140f010203190302070b07030b0d0b1509010b070303050f 78
    0x24200304c6d05443c02c005503206440c00d0039417280e00000c0080410440101c0c0510412800b8801c0000c02e6860200c500e88201d600400103041c0e2203a0b60b00c01c41c03d00310310f4043c2c1d0095500c806400020003025010786d8001d00e00218018461040d0084000d01514044081045420240700d4030007a5041c079034804c0d145030b48140500c4000d40c4942602c2c900d00c5070400000415480c1800a05000c0d071061044640e11034185c0104a03a074030001c1c1000c160503240c060204550b6038002020b940301603018042c10b4850303000081c12030051100e03040250401c1d51010400010a502142a510605042d0400c008298607200d4407102e89802c0c0c000c0001c809455510120185450744810082c1e40f01481120300e04a6446408156100d09201c0c050209401050000400000c2000a80d101c1c0700c902e41001020400000641c0101c400b03080902000007017000304021482c0080380d41405000589a4410381d65541e000c0c2c041c6900024064000914180104015079507ca0104e406001010b40200070340752003020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 309641124 1250 309639874 309639881
    0x3080d24090c090305070b030a0c020f0304030308040f06020a0207090e0c0f0906041d01050709060c050d0e030c04140a0606030902150c01060f06020c04140c04030b040633050604050a09 81
    0x1150051194482d0300200041742000980c015050103250a91282851032559094a0005000030b0654014540c4c540040700002f00b40c030700310380c1c040c9845030042c2c860707082c1540000d0074007001400f00340c0001411f22f003058001826404845440b101000402e8102d5009612005000c840a80c03214a9880c0d2809924094090780c0d04808020000208241040c25000c03002c0e440e0900500c0694454040042550300680f91000614440c20140c00140480d50f8031071b190721142d0142d406112407418082004c0d1400c120038400d07000c003d4810040b410812a5500c0101000c807100d0861a00740b0801240541c401d0146140d0950b000d003900c40e000040c0c41e14100c060304200c41207841c41d980c4103000942130a008a90758002e01840e000740c034045000509000544151241c1070408914200610003c1d000d000211021260414403140c1251202e1801da00039001070b51313844150100521140c84100c007801c2c00c00380e082e40d2003c0c1c80c2e00360701d589500307018060143c0e215031707030380440d02c2041002011442d07007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 309642374 1250 309641124 309641141
    0x2c0105030a0f0204080703170f0d05040c0f140913050d051c05131401110d0b0303090303030103082104020d02040e010e060106050d141504090f060603080d2409 70
    0x800101e0700030808402201244c00030b502001250748240030800c00d2041c80110507644401111000f032501c2c032111041c46140c807825030b40c1e031611130756680042c09104481518801130001070080130002c0344d0703c666884003e0f803018000740c070511700d4031f01149004035500d082214050f0f00401074918092940342c03c1da116084001b446610300d000315440c2081c001d46203e074522aa2003080241103041c85d6040000865200000c0c05201d03a1406203040d409840090980c0d110304140c01000c120440c04d003010a085015450026825200200002c000c000c4c1c1d50018050320800070300c45a03d110501c0c0e03465101c0c100c003a200650865903c030401005800e0940103c0e220b0800c601c00414000c0303120900503c2d1980c02d0b4000307030001d40040764040d403403241c5018038894050f0a50900d003942c200b00094007103400d00e9807403040c1b2413651440300404226102e81c0d03150701d143e0028001c1220030b40d00d05143c0040d074002e150104202c0d2601750084522102408444e44140201841e40c1c0700c3e904101c1808000c2c40b040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 309643624 1250 309642374 309642391
    0x4020603070c080c010504030e010804030206060f120f2b1205040c05030307140c040c120c031103010b0703080a02040e0a0902030c04020c150c0307020a330902012c010503 75
    0x10410402140c040b40083c001309a4600c00007178545000d0400070400120501c2030fa04000c1000c00307000c0801d41c001203842d0030410480c0e10f07800b1034004100041e0a4010031910001c9800b03081004501035802140c0514518503c1104030600c4a04480855100c100c1d04e40a0b070208074001000d500310a0782c0d90001307034464443d403580c00d001a20356001078030390780084400316551303070010041c40ea000c0c40511040da083c02d42560180226180248090200c0307000340780e13100d01d40b48e81341c2104580034807a81140360012a100445a500e58448a441c103081c1c0c0140420741c04918510040740b00d91103a80b00300d9086801103ca030900b103880b6007111030050800a1400d80c2e061103a001d002c0c229136100e100030158904940c00400070004114a0313201c1054006000022840050040060442c3c000c0b910a060592140362055a4000c0c1c00c810401c030485402a480341c0000e0309403640f5041401e40c012040345000341c940c040d100c03104081250b180307140c0c070101440036440c0f48003411391540950061078008022 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 309644874 1250 309643624 309643637
    0xc0f0a050f1c050915161b0b0906210403230a30051f081912020a0b071d0301151a0d09080301030c0e04111c05010609020a20060402060307 61
    0x142201768030640100c4a40036010100c940c20100b0001c0401c801c1c010041c5460381f060f5014913040011900d80a1115224003640001402d1001d80313859072100e40c103504140f00080b20f60b0800b07040040c840c81036280a420300342c0c0c1c60312224401140303160554841011540c1d540c014001e041c10862045001d174241c8400c3b00141403003030341c14010030307010320b52040104882c94070500070103c0031200c8040250303110807065040900384031146141004240d9240340c02c4424419221680703002240307040b41c0c080006d1b00001d0064184a50903501a1050145c90106410001c041c040c4404041c220764100003c400b00048c465010820840060001d1403542071048110381460320881c102010f0303a02d100001c42e9085000401841080720600f28036002d4200f86142812629090ba611100d041072404007501c14002901c000c1c214429460f00e0400e4580d1180c0207200140d40c9442001c081d4001024501c08030342080c440006a803c0f21280311a0307050000001d00c03040e02c0f41d07000d01c80340d81d0018010108000a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 309646124 1250 309644874 309644899
    0x3080a14190207060f1a040902100810170d0305060f0907030c050c1b030f0d1409060403150603050f0c1f051b0d0f08060310050a020c0f0a050f1c0509 66
    0x1980f00341d015000031117002041c696110b08020101210454485100741c2c9841c1c600340150300e5034440d0481e4500300f418074200c240c9500340c0503260340c0100d502000f00041c0f8a890b080680d1408aa0f000002015850a00464403180c08000c0c12a805803001030b0080342e03100000c6c035054400c1e0020848001c590038501e2500700c41140003030a248101550100301c003040c90300c2c1080d9041c20030002c0c04281c1c4900241400c0e42d814500100700e90f9a220240c2ca481802180345403d940d41d550454000355484500c242055000301c5414000d04040d00c02502c05000b080003800c145200481e4034091b202c8020060fa000706103508905140c29080c0e4000010014284814054217240d0100f4950174400e500040c2590398407088000c0008815a6140341040710304402d00007185c0f000200d80c0342c3c1c025014008501c660350300404078003e02408040c030b58203110b44502c5107100b4001046900c1103038000e030191414503601e900d5944e551030b5807000c000101c0c80440d0001504a1040f009000d032440300510b4159000e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 309647374 1250 309646124 309646133
    0x4020415030b0603060a06050a03080a0201180b0a050a0e0a0221031c0f0902060f0703020c0a1e080606030d0f050409021207080601020f1f0605030102040f0303080a14190207 76
    0x40a5003003141d0842c020810f00100d89020000309901c03422581c4180b0140d4140008100c2c40906407000074144100400d03c60b040600030341000800c0001d2940c141e0311402c040c10302030029402900c581010b03515020204540d051140900c1c820060000c00501e0840416401e12a40120f030115429451111501c01c01e0a80c4003030004080d06200e50b4842c3c0620030094400800f11410800d442181d00d00e000d2030301005031185c6080e1490201140e070390a44895060800341c0c101240110b4041d0b020704003035008102203081c1e101042030f4103240d0341144411910781c07180e141d40d024141c0303000340d265100440791040f151007601503180c58105494040c1c00c0541d101c5055050360440f4180e00e01d4071582c80f040145080c2d006107817541c07100091005000f0310803e00f06060300c0759921240c0c40f100a211114080314001ca0750000c000400018000719a1103542d003400c0d101c0c003051408100d00283d503020119000170454060348114901da90b061081a40300c5882c5441e410380440a01c0100d16000e01c103002c00306 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 309648624 1250 309647374 309647411
    0x22050a02040e06040c1e03030807020c1203040914040c030b07050403060f140f1006050309010209130c02070506040b0306040b01121518140c090d020d0c141005070605040204 76
    0x82d8802d800038002030800c3d01d4442c0c007480c103c0c0c105d10800103480860008030141c1102d10b0b8201c0ea0141003444507602c5125040381042904680603030030030700c0400c5400d607500000005100b101c03103488040210021440401150000030744000d040502080b00910100d40c400c21525003101c46810503a160a90b281c2d105004e817003428103921805a5142042103020b0001c0300d205a0140030340c0d40348207807450810043c5142c2e9009018031001c129000c400120410b2003581140c074516401480c05060040708280340029051002548005011703d086c0040c49080131001c0c1c4083d02e460f04412030850b56004107100080140e0400d480c100b1034070510545952015204851fa10380100c011400000d003003108400301c00703003000c5601801500d02030725290702899400f500c0d90072032002c0043c240d4420f000000181c00d405001d030040c2d404910520040d0420803021005804c0320710345403100715076100d14030805c00d40000745205100400c408002e20000200c455101d50380c02440100009500109032601034940d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 309649874 1250 309648624 309648641
    0x50909010e04061a0d12020c1203130506030c220b2706030c0409091103253c0315020d0f06240201060812030402100822050a0204 57
    0x40201d88091205005060045110f0038284140001505003480040b07107125900b0070001d04488514201c1d1059036100380b08182840d4002041d40b8108008008c100d40c5a6010349030000d130b0003a547d18000b8880c24120142ca2060002c01c08080c00c00d2540b280c1c03030841c516446442d0003000c04145003c50041c42039006030003640380007090b4941c1a40000100d10820050703135442446070b13a042c010041201c0c5483d0442d0183c40c1c11800110315205586440d442080c038006106515010304141000e88100e5100d0b480e0340514400071101901d60751710a004071a00210b00100541c01300c2001580d80c1f02407425030541590b015000310102940d417902d4a40c01c40a0544003441e45a40005561501d072000d8046c84c91444950072040002d40d2400410400d150240500d0100100301c0301c40d44500e440c002c0d8800b900611030481175419280d0048034010044e84222412841880034048d01a201403056176420703c034480d2480c0c40c2101c00c0071904030701881082003000319541d02c52000c515005840e6070207048038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 309651124 1250 309649874 309649889
    0x306050406140f010c0222060e0406020310060c080a0e0d141011131a0d020c010c110303040c050105130506040806010f170a03050904020714070303030f020a020303150105090901 78
    0x1031442404003045040f81c8104851810414a4000c00313015075200301d2610308040fa40102410742c503200c190b03404050611640809d8100d4050350401040c40b030181c00452103030010b0300d1031b081c10a0700c46c00207403802c490482000d08001c50511400754840d000e442d42660b00f880007824034910303080640d02c03001000c0c1e40d003070010002d41003000c0c03e100000450281059500d10407a0290800685030f510401e0b2307400c903110b4040075800308000d8881c401c0f1488100d0b5181081c4840543da00c0292401b128003074000d400708000001d2200c203941d20950300110035203000d00d41c00013400640a20f0400112003036049101304c04800811054006a25075450000300010640c0c0d46c0a00920b40c0b50241c0c0b160452004d0f842284002c0c020381c54180280c8003c0350032103146516003000c40c0c48005003808500240038000d070080a48070641400340d231030100002c111045a102c0d54091102590010071001a0f000380382e01c92016a006002050585c0e403010b504400d000d00614146051080c0c1d000003813024102a801002c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 309652374 1250 309651124 309651149
    0x5150a081008061e060a06021b1503040b0702060c0702090708060a08030a021005060303040b03010317041505030405010c1805120a06020f0403060b1f11120414030c03061b0a0306050406 81
    0x1060402029005c2d44014201c80340300e0b40620b0b001002c0c0d10f60828140c030b104941c0441d4070314030300b07075403035880c117161060002112a480346028030784070703d02c00802d88040003d4451240090740a00c103d40440d0b081541c06882101507480e200c1060b1100c140c041c00040d4065001407001c14110010030150010b011140e00410320041101111800c0303400142c000c0703000703070020072080c0582039043c01101d044030750100c0c00200411440600007114011500100c00ea140c2c110546580260301c00051801240504020096050500070941d0f121500e092440e401048440301000689029041030076442c250000340d132062195603543d0030890340000e10300100c101d0041824401e002d0903104140c0300c0d50040d00c024251181c5288141180d00380480702400308458024005180031013441092100e841101c3c18640b250784541c6841002010003890345d020744100340b41d40020f4a000140349004540e440d42c82e58480b41c40360801803280d40018218021b05440703080c0010b442d203d0784030700c0d00104410005070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 309653624 1250 309652374 309652411
    0x1110702090447010e0106051308010c030f0f06260a1505070f0c08090d031106070306090b0a0e0103030f0917060f090f12090f040504080d0605150a08100806 69
    0x8007480950840c034420b02000900180207a0010403070039410340302d65051041d22801c809450301961b59007032b080b4903900e5003400c4c1d0100010380c25400c42e03041903011840901603043c5507948001110683d01c00c81007041101031800000380a00304000c440703100002c3c2a12400241074480d4010005182490031146540b8010026030316032040d0341001050361441c15060b80300d01760310b0340072943c060120f285215840103c030050816006014441a100c4218151459031a021001500130030740f5201c0c0d1400141410442c09183c0b074080007120a0b51000381245080d64291380b000c8804800c0c40c1c0844041c0400d14801203065240340c40c44c006410880c1004040a28000250011070701c00544036000d107a124010b4045000d00101d0380204070442c80044644070f40f0b0010004624100e02055150030a01d05803d010920441c4030040040d04030780d020a0101c59075030340610054181c8040e40c584000f8092001c82610f620032068a038100c0300074031101003a65241c2ca049410404141c401c8040020a540c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 309654874 1250 309653624 309653723
    0x1a0c0723250302030607080c0d05060607050a03030b040b1005030112031718150f060d020a0902040603020316080915060a0b030f070e1002030405011101020d05070c030908011107020904 81
    0x18158400b1b45480e00c24207500700741c44030300d40c64000d6180d52300e02c070703a12640080c4941d1035200580b501d19401c4812036030848410300b00600100000188a40503e003006050010f9003000769421040603070b00c0c0c8c2e99500e940e1030710302012150070070402c04508212200c1404044e400f0f101d0380c914010041c0e0108060003001b114407442c40e18646030007c0720080400c004009038030024101d041d500401c15034444255108074800284140307101e400207100301c0d10110300070482540c0365014502c2824420315440c91a1003204040d100c40700300f100e02c1030580d441004002d0813115003407400c1390414130142481403e161285807452164000325910030500001c1001c11824691201e9024070540040da6550700c0b15041c407100a4580c400d600840d414000011058161040250b044481030a94100704020f0b0307040644008100b0030000001358005960a0000308040070184a0307920070381546004289008502c2d82403045000d070043c41956850054001000d5880bc1c640c03400d041c8000304981880d000c2021442c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 309656124 1250 309654874 309654883
    0xc100906021504080a08190509010608070b04080d0f11010603060b130501050108060d020d06140103030909020a0203040521070b040815010b030609130804031a0c072325030203 77
    0x480651120341d440030b000204080300120317560320010f4a003030801a5140c0001220484640165141c450301d040200030004c0030650010b01550048001d5031031096030b43e403c000c1d00b40524020142e15400010380103844901a03828071b444a8100c2c1400082c100400019a007124410340c17080d03e03034070b8130381d01c0800031880c06030686d0a40c8141e0010401444d41004002050903400030813482c090b45855420409560714400e03902640740d40200244003d6401a800c00340201c0300b84001c4020800009010807982c02d64000d03562005417030760007182840d207800f081050741400015035240c00900708850b003000c100c05008140c05400c0401429660343e150000ca140b50a581555880f048110324005028040020301202d8014104880b8400d082c1c88265460322542d082100003040c0d480006400803c04c035108110080c154083c2070708408c9991428890407152081c00c0c2e0051103604601500c00801880d0b03880c06c6400300000044408281e8030441090700405c143e0903c107900b9110b41030800441c0b80c02c11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 309657374 1250 309656124 309656143
    0x3090521091c1a07111603060e06010614070f120206041704120f0503040b0a0c06050601080603031b0106051003020702030708010c050f07050a0b040605040c0e0601120e0c10090602 79
    0x11401c4a200b0032521200d54404001c0d1442240b20300107008141003074070880000540b4480318098650380100400c0d2500130030b915100031280d21342041007102c940d29021507031074100c03415030300c84500c0c4981d80a0440f5966000c210101d561991200c008808101c1900c0f80102c1c0c440250010402800c00b814258601c00780b42070b84c4c20001c00100070a12516000030300c8014150f42c410034103541780c0014a4241c0c19809203800240c0c40d100049005486503a01580800e09503010700e0080100c1d840320001101c4120003160683d8055204000103407aa4444112040c004104440005400c5450354000741108402042040000c0c3d000b180720800d503d414040c0100800e010790081210100c40721000e0058024040c481c00340c1400420500144081800a00f008940c452480141d45c41c1a1911030010241650281c40b1584c6002c404100d4100070141c07140078100507100e45200f82440a18900584010400002d960080e09a80c25164403a05200544c84125413a40b01016042c020020300e001e4824 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 309658624 1250 309657374 309657409
    0x605071a040f020a080f100f11070b15031501060507030306210c090c0f05070302120706020c010e0a02030613021c0b04030f1b02060d092a0602150105010309052109 72
    0x3603044012620000610009000d0075101c023054803440320302c0a1b001014080f1004520400c00224101041044855103204a01c48592241d00b94100c44c11f050744d0307900c81c0709003943c82c10b94440188100b44c040c001405031144285400304403a5103c000451202408490900311a202000001d04000900981e04094400e20b4000c0000c000f40c1000104103001c0e41462806000e0001090000d05109001284908042005866542045182c0b120003580310140160340c6528066600411106c045945880390390001d00400064840e008144100c01c4003c400300c0e8003d50050024014103030100300502014000c44200340301c1e140030704000d00b208050280c81410013188444a02c0c50620032a0140385894058501ca0349445050342d08c10000c00b03003030340c0103040038051402408581d0500c4500c60030001c21500302c19111a034405c01681e40310076524070120362904400041c0f00b107512a034400114039000c3e030102e4003aa80300707480320364481e41308540034a550000007840061900b4070780071028000c00c11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 309659874 1250 309658624 309658633
    0xa0b1f14070f080912150403030b040b010f0521040506040b060a15050a050c0a0c08120a080a0203130210030b1516060c0908011a090703050906010605071a040f020a08 73
    0x159848120002c030b5000000c22207240800d8505036621481400e408900c0c450b4121740304c0100034100e00052100c200e40880c0000d0030a503521499003410b000d40c8501d001c060b11a2107080955a00c00c0d102c0341c0048a002e0700c2d104110406100d015035031035019004a00543c0038000c00d0825040c03030a0405c0000342514090030003982c04206140f03206450902da070410345442e42d00ca802c401c0c011103151003038400b01c51540c41140c0c1c0035824040c551440c00220344039081100c04654480c03401c000180035900850010607070b50310005407001d1482c1c00440d0710001032101c0e5102c0401c2980001c4032100c103210803100103076440e400b04100e400d1910a002c008074440c0071450030813958102781a084060010018a12525004120003180c0101155000351000700c0c000d1001d00740701c6c121b1040d04031000c02c42074410340309503020981d618064460b642c025080380b07010b40100c3e828030f441035903141c0c003600701182d80460100d108080810300100d90341c0500d100340c200c09681d0f841401044905940b6400c040ba8a400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 309661124 1250 309659874 309659887
    0x6080f03030708040501020412080901030c02010e030703050f1e040e070306140f0406050901120b220b090c15030103050c0118050f01020a020604090c14040602060f0a0b1f14 76
    0x1800000d4070307071002c014a005505540d55251450190250340d000035044103200205c00e042221440203030900e06021b82c1d0400001c031148008074280c0d00b40c402c940c1400d0300108188401b0070b01c600000c2c503a20600780c4041345070003596480798203c0d680390040401d400c40302003800e1212030801c01420341c1104071440c00740031007420245c0c0c0c51034030303400510280d100340d0308411542400d03200c80d08501c00401004100f41c246c4d680d149905482000c10400c201c643c428440000b0f0a001d0b004106d102e0b40c118107101c00c200c403520641d5050202040a0203a002c40d00c1000c0c10030a031a5180340c40d80c1009440d01180b42e40f0b039403461901501d004008144030303060115503520080c40c0c582518590b402c60b4422185095a8045000181c1c1001c1c01c00001940080001401058400c1c0941041e40d130142d5943e10180c4403042c10f02d40d82e1690156010710001030300103a0118248069050703200e0740240c2c0c00e040005416001070000740d40c07240191154020400c0c103208061056800c2121a9507080c041c056261a201c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 309662374 1250 309661124 309661153
    0x903071502010e3d23090706030908030106050c03040b0304060920010806041a0d1103070501050f030a0b040623030d2a14100e1908030604050406021606020d0608 71
    0x420013044424001109540039401c1801a0414949120f200c06891038030241c95008003000041203c0b851018402c0100001d400b81c403a11604440301d40101000d4116401c143d000c5400d644207018411452006200110319080359800071030103188181c40000d102e003090325002c0e078030901011300c4c085803840401c0c10300c11300c1e6001079000b54004070858000421007032650340e036101c1c50740e5100702c81c2d0094190500310b01041149185540b564a08501300d503012607441c001101c091041054003010848140007107940e41d40c44d0f8024000ba07200040000c514580c035140482031500c1c01000d0300108540e45d2864130490708062140700c4a000382450121f030034008000e2136810b405100100300c41520350103406030090015043d071201521400c1400d079561141681c00c090042c140c220858400c601600c0004203004525840045180340d00546103400e5a0780c100811000f400c2c000c0003503442c030b5000c024a1224038003990003003899130f105940040cbc991901010a500f15003880d0090a9907a105880d5180c40700b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 309663624 1250 309662374 309662443
    0x303030711010e030703030b03100c0507030c022b0c0f0f0b13050d05070611060f040b04170316090503010c14160501090c08190c06050903071502010e 66
    0x100c03203041c04448001118445401004603c8000e000f5002c00b09044081541c5034000040b0b050b03045048070602d81c3d142130b01b0400ca5210a902c0d0f0041041000800c0001e4004c50081000078001018101c04560069032040090303d135246000e1000c0c000b000613010001000c90000281c880204201031250804031024040512070040f503600c054041b0710703083d070740d044442004058080901100c60500f4149440b41c1d9030650740c002c810108070307203100418211400090f070500c6082c9000c03c0d00a07039107a0351036025a60102600c10350ba00301381548460a00200d0000560140a200030b0884075210702000c0200340510682103241300f64103000c1c580c501c1a42c046030401d405607050310340c036664914140c12003200841c040b030000d00550824541030184250f203001e580031181d88005a031882c0c030043e80344883c464070745100104482011003044c04071500c6900500801c85018040700c04040d100c840e5840d10700300529031000140e4440310100c507051414000c5550441300084400c1d00c1c103c0407140aa0030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 309664874 1250 309663624 309663631
    0xa061d01113c0406120506090c0309100c120c08090303041101020a0c030b042d120507020405010e04031407030815060702090717011202031f06030512070c0e06030303 73
    0x158611101c0115421542520040450301540710a40b01030480b60300c8401c076402601c1064007281ca0b010b0240198800c03806428401c581c010010100ca95030041c00348401c0d040682000d04a00c0b4600d041d044441c010b100d040e4000b00140c440c6100314418030340c00e07006c5d81c400100401c1003007944010320410b01000001d59402950040e0780c43d0081d0380d440c00403460081e180740c001e4001c1c40710100020030300140301e002074003460150100490380c007407500c000601c641c41d88041c08802644110500042045a00407074000070003881e140c1d18000d003a80015080d04c0d402e8204400c0d1082d0710040c0420182c12200340d10038408014115410810302d51000707020003034010140203c01c17200162100342c035980c0c1822500c203554010144d070310600346a0002040c9448841568135241c80e00300011414882840319120400d90040051441d070b0310560140074840c0c0c42c004000d8240f605c0d048048005a000e100389201c0c2c10052440c4da031142541d092800c41c28090b644200c0390100c112042c49069140070041700c1d0b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 309666124 1250 309664874 309664897
    0x3040b03040609020d020a09060305010f06030305160602040513020d0c0c020603040611070605010303020c0906040e07091a04020c030d150609060e032e0f02040e130c03050a061d0111 80
    0x203c1d1041c1e80081030318005514002584a28645030104042403d1307807003001074900170301c020008003031001071140c1207074414003014010070414000c4083c0d4280240c2000c0c103542c8650405418a5030f01c0c8041000710011002c0c840ea455000f040741031400f00b40744145108446075160007001070b00190041092440301510262070162190340074a89d1254000480e450107500407400c00072980e4a0400a4640817006c09507403040b03109501003801442c05005400c0c201003140090701006141041400c000c002046060300340342400c0400d1040c0d40d5445c8054208903400b07c0182d681d501005c0c500e8012110519030b480008100c009080c400507034000c6849040c2d0b0b0300ea04000000864040000740782002c00351256454911403080302c203800c011585001036503540301800303000d000d689402000c1a401107001c1c0d140200ca040c2c00080080e8aa48040300d1041d020f24441c46012780c0301c1e12458103101c0380c540242d46031502d031b1030051400f0b00300070981010050020001c0005a0303c1c0c0f2403c8006d031050210b1000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 309667374 1250 309666124 309666131
    0x20901051309050615090f0903190e061201260c010c0809031b130509030d0b011110060f0509160509010203090a03050610080610030f060b040c0309120203040b030406 73
    0x800400381d9070009000780c2e044002c461941c5046102410309200307000c0610300035016500031420b42e020b1102007a0290005402440c04c0c110303080304200704046115500d1082125035030725940d894642000070141c0c1b944048801460b0741c100000d10303030407240701804601c80407000350080030050b90100d001c890104003460144445203d03410030054038010154120b505004041c284403c2046c41001e41c906031005840c0c2d14058801c03160500308488045036104420b401c10080c0d410280d030641d10004800c2c2c4141010207003039480030a040d14154110820a040c0b44d5243d4090068580916050000700b00440e9003001038940300703814003641d00b0315988030800c2c0076000c511151946e0007031099800c038103006081110038503aa42050341c0c0e01d21066138151a5001072950109101300b01117440352080c3c0e40d500c50302e083c80d85199110140d5042c090b07010b444207641c0e0041c66030f699845005800c980e08865801140c4403400c0d00b80b60108000d17903404402954000c000c2040404036420550307510940000000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 309668624 1250 309667374 309667399
    0x90912030f270a020f0103091e0c0b12010e04170703080a061a09090a0204080a0b0a0f09030f0503060112062303030a0212091207080a03020f010c170a060512030c120702090105 77
    0x42c1d000c3e01108c0b80051020708024200c03040c880303952075092030711030040c00c01c440d005940760348000c5c09200d04088481c00c1e003050001400341c8021814100e402c00d01c550000c075480c1c504035019041d03075040722008600080c451014405120390a000c1c3c0701c00307860440c80d081009e6019014003072842c8a001c0c00e25024070a103200241a54031558156402000c3d800152000c8000611b0200c826500c00c84040000d2840d000c200322011005100b02184d040c1d03da00e64642c1c070001488142c030795402c01401c19042244142e48603100b007010780a00002408801c0d281044215144100c0300080006003500b4000d5005008182d0743c01c3e4005054084a100c07001d090303980d4034042e00840c08461100d14181d0880c8079420000480100000e441501a4040e9003130300d521030003041d452402d80d015004803600103692041e8254444481c42c10003030b003000500ca40050030940c2da4011508118880190708040d030800b144030590b040c41030118403425004100d00501d403160700c0d40003595854060103428007a400c0b44510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 309669874 1250 309668624 309668627
    0x10050c0309061e220c1503050f1302010507050f0a0c050f01030903020c0607110a030c030b0a0605030a02010806010201151511070b0703050f040b0d0501050a060507020906090912030f270a020f01 85
    0x130402580001411003d280c80e0500344154032000b00b441000a071608000070401d00000140390b002d81020b18048426030801e800456181d04244416030b00707401380c000b00b26500b000030040003041d64032508c0d409a143c1c3ca02010045c004000ca60550f051500300701c607a0b40001d42c0400d00c2c1981c100100d070580d0b16030000707007440c12070294103c00203a008a2200300c04020f01441c0d408031000c6922480d4100080d950b01e80958040e18414882c1e82e40552110740d210006600914600da03120006100010701a040802e41e03130384140c00c5502409581c408070401c0e10610344d04c01034449641701c19400802ca0b081c0351030b240302c0041c030074844003804010003c40c928000d807096008070380040401c5081c03662030703101185108004180c20702c6510300c9000c00320030000300e07140150140c401603a0014005001c554552050100100006000010600410b10000360303a906000266000d500e107050304411903e0414451100ba000840303400c80e8000071a42c200d840c950700040c0d14a485641a200c501480c2c148000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 309671124 1250 309669874 309669931
    0x14011703181504090e07080105060117070c060906090309080d02070509220b0f07030b040b0f0409050c040606050712020a021003090c0b040602010c020d0e2110050c0309061e 76
    0x401300e40f03091031038128070000001100e1064034110390007002a03481d0f80c40107403403a5000c1c42c41b00c0c801c86a0b8500089446018007030710b0500c03500502000c01d001905503241c9084451251048001c1810220240445078040240c4c60b10303d042800101240b60401000581d0300c0402808406445045d6040c042c107072440c00c0040d500346a124540300343c0307030900c084401c1c8010340880b00480080e2a1103410401440d19005c2c0240e03660f805001c004c2e03981350074020f1201500014806448030721a0030b0842600b519103104100060405550320303903c0b04c00750b14042404140400c40b131021940b00004040150b5039451450714461682d00f40080c103034100f032502d076010a19a50000070400d1011070b0008146070103400481c6201003a60035601d000111000580c2d0a0501c030310643e400613640020f15448012404c0c400e10304172400c00880c0c0001826010741e00c26107a040b9420314600201000340030301d01104101084e0444104130440b01886081e241d0107818180080101040ca206541c0611a03c042c0b001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 309672374 1250 309671124 309671129
    0x90613020c070806160905062802011e090302120a11162904120f020303070c1701060518040f1703070e060c0a060207080d14011703181504 61
    0x180199100c0c003258240545920040c415202280100c1c400200688510003070f015880306951a1060405d0800b000e21100b40c21a0034406c50f841410100c41510b15200c10086120360207650003c91740744148480d9243c0c400e402c1d40d450a4041c10034a4001c0000e4011540c0070042200007660ba80f500b82c00f040c201d44010420103144941e00074402e2030207054003041154019102401a1f0b0303201c482c0300c40b81e030740324540781003240032208c102c113001c03d0010040c80c4000c02c1c1683e001d003005c829050456000282554070002e000c40d180705070504204104050960780212180c1c442008101e400c1c500743c0032803540d0310135410401003240310328002020030880425107400b85812030b4080c800084d4010055600d03034026113100c40800d03105404a40b40b850010f0031208000d000b40c001d0003e00c850741c0d4604000c0d400451088038129418011000c45404c42d209182507000e5400c0074238440d51506240c400c41c0a840e040104058004120740103103080a51a01d1045c00703030a4500340754103405041d03000c41e41d0143d0b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 309673624 1250 309672374 309672409
    0x315180b090604171602090c07050102130f060203030108031218010906090b0a060503070927030c020901120b0f06010201110d02071a01180c0504050a06110115080c0906 74
    0x3035003841062100001d5a501ca1845010420381403030380c1480d040b45a0155616540001240c0c00c003400041c180704011541103d465025076060030741540d6420f0981c1c0018813048000181c02000304840d00344903160000070311090001d50701d594180510300b9140c1c468900c8010072104039101082001101b9000d5440458103c002002644003610740b000203401c004400340c401d1b08101c0003164904282c3d00c91a801c4620003001040b58610b0201c568020f0300d08e0741840c0400e044224110f21020300946070b0181a18401c0e81d82c1003850340c8600c1000545001a044035108a100c210f424000400001d46190020702c1c0011058640c0d44e4800100d0242c007120114110300d020100c0c0c110304114054002d80040341c071a4400e1011401200c0030750a042034248a03100300000603481c2814100314951100080c0003880ca001c600e8a034852001c40c00c04005036025100140d450548814014002e100f10301c8800d5552a00320071083c0340845030b903503c04001120920690342c4201051107a682c1c01001c1000d034800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 309674874 1250 309673624 309673643
    0xb1c151a060313030305060303030c0a0c050a1707030206010e240406050301150503060c091008071b03110f0d090510050d050103060b090702011112041b0308030a15031518 75
    0x1c5000d49100c903c034814118040fa0812012a00b24a0040301f0f481c45608402049414400c9485040f40d41d40a100c10a481c140540a910f4000c54024001c84000c403081e510141d17501c039170900d0300916143c2c059101c07840c3d01c2100020b1240103245c428a4108100700741109144901314080042c0092000342c1c0a0b5500d0361801420448002a550407a421180301700c007aa4036541d07500c12011803e210b00c03842540e00c40859044492402c0c02907030350b90303045007032881c2c000040e54480c52140380981d090b40302503000c43c0307151611350000d04040020383c4d1500340b034802a080070aa25400a8003482c2a0700480d032094405011000740548110252a00725108500900080d65203081100041c09064242c5001c0d007005000a00c0041c014002c80207400d901c503d40d5803a0079000400844020b0000c0c0c000c940700c11100c6070303481d043c000f40315a02e0059801161001d03641d091445103041160000c45440c400484521402c00c0820410340300105848190880030605440e9000100302906050000034130441c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 309676124 1250 309674874 309674881
    0x90302010e01050d0507031a06120f1905190507020d0c14010f050c0c010e06130b0601170411031b061903060b0a020a021c08090409050f100b1c151a0603 67
    0x381504001d030b03500740d0150031f00280142c423030500200e0320418591f0760301202440003040301003181820a03680700443c4258800d4521480e5403450940d002591440e1107441562074550840c8214810710381c11103118001404442c81d5507801920100304841d028054500350000c0000c041d0081d0081144011118805c01070b5281109040c0100c0e004148440345170743c40c02010380181d4a002400500a6001c10307460b02d180c03903071565800b85035070000303040314100880d446008031410300c5040161300607842001c2c16504240d90310b041c03504d840900040c102581081c525a003815841719401c5912008809030312200d0304507003880c15030180125074046480c008000484494460740403e8403100103100312a590401e04c25100d01701044616400007a1031000c040003803820354900366000b85141ca102c0c40c15988000380d9405110308103504485400c103525101e0315011020f141c11420310300c4440000000101852081d150060702d103c020f0008040d240d95000d0b040214039062080801042006128a55034034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 309677374 1250 309676124 309676127
    0xe04021e0c010c020c0904060902010e0a0306140a0506181308160b07050403080a081e01081b0315071404050a0306021804060303080c0915070305040e100501090302010e01050d0507 79
    0x41c080c2040c10754552a081400c2e00c1c2e98404078018001100c01480d184841d1182e4850500510003000120f041c800100754a10203901c60040860095010302c2001484580078071310706d0200d617401043e151200340703090100301c01a078031032003e491180b40c0395010158a0741c50061000040e201140301600c0104003048501d440a0780481d181a0f080c49482c0c0030440e80c55907041503900780207500001f02000401d000001000344101030b2107520040b1031905445d07014094980841420007078000200360b07001040303040d0341c007030140e807030015a40e1041e07000305114003031074002560015015101404000345408460003217003c11050340d003e0311000300000800c0740e03139142150096000b40c20381e400010900381e035110345240034480c2c8011641c05846480050392161500c0159500484ae42940700f28000026001001100050000c191182d295203a6580c181840c00380400c00080c0401d64214a40e14140280d0340d000f1840300480340e0a0074100481e01044006803200d0049003040303208940750800300108075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 309678624 1250 309677374 309677377
    0x7060e06060a0e0405030304030f0e130c020c09060d0b040f12090e130b040b070912110102011d101d0f010506090105040c05121810061d04020f010e04021e 68
    0x100740c11981c541100e0740d42c0c0301c0d41004840407600901540c10910010700424000c000c0054425031510344900248040301c0000d14440c220b03c2104115a40c5604280010790101b1540c24000340442c0c0d100c42a20388200086e03104043c2c50b0004000c60042c501003000c00c0f100088040309140d00000c600c9034402007480c010702c0e03003400d1f00c1803003810103140d80850b400c408400803403c603082d04000f4540555a07551100c006000c1b02034603130710401c04035000000d00151100203a07440306104807810308010382d108000a095647c00380590341e00341c20f214400030300701400141644041c20729210200700c140e1041242c4955012804104500f8040c0c2500341f030940070117605c001c0c8280317011170f00700e0705c00e17603c44061004848002d03501401060042000f1000039141855803588442c3e280108540501500c940c181802242c0d0250700c415621524140316803492003490031002540f04080020a1405030001003840d0042070125040c4450044c0b440c180d92031320740403644100b03003045600c075200440442c8441c0c036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 309679874 1250 309678624 309678631
    0xb0609210a3002030703030b0f060d0203042a06030e011d06060405010e0907050f0a0801140a0609020f030a09060e1605030c0604030b18070f06090302040b01090602060a0b0607060e06 80
    0x81902d000d8201074048141d180710b815071105980114288812603900354010b1550007074aa41c80b8213007240030700c1696283e10040ca41c60044500141e12810107280c0341050801050f4440003039890880c410700402e00d8851940100c42c1c0c98500455001c00541c5013900618140035005407690800c3c0c444400a000021407502030503040d54200b00a0f03070b070760310010410303101591880040d812901e810071003803901031444562400024210340200781e98241450840d0390400802c00025800c50800c40700840a1156400500340d5000030f62910643c0c1122581c2c030310005001c51307985030307940701c091007400f259074088202c0b0010a01155034040c0c41000c407028151051003424480e104101c0d50052034207000c0c0c161001c0b2076100200315066100c0e10240325510320100d00c040404c3c8245000010002d0281300008020106525072070540c0707003180103201c1950040a80039060001800007081400d5000407071590285030550000381c034907000702c00284a8400e80b18041e040904081c6107130a11140460020700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 309681124 1250 309679874 309679913
    0x2103040f0e060405010f180b03030705010507020f030705060117010b0a0602070f0518070f27031703070e060306060408122104200a090915050702010b0609210a 70
    0x92a07640704100001e40318240181088407942c0c240407c00011841d0582858207001800416110000e101182c84c603040205c0035130b016074452045c4a08181c0500c410849482d44501071032500c0c10340c1d1682d0782d650034107108000b402c11400404a0b800c49080d48080c11400b070040080303c21030383d582d900a6564107240102c0074882d40c280c200098524000101c48400241c00d4614a683da554038020354101d00002200004e0288480740b1002e12018030a402c1a084440702d005030000d03007141809080c0342802c0c18110442c40042040c0100f0681103801040d60a1003112041c2e501c1d542ca40128940780500c2d405515207110f002c015a0114074100017070051400200e4044050903081c1c07440c1d00007080700303031409802121844040c840c034581d05104d0030301d00d800141c0a040c0365030350703410b044040780c0c3e05200644207204803000c0003132005c039940516a00400c3c0362000780603a6002200081d443c0c45041004c2d80f00e07410031000c20958450f015804219042c262003034070b007101d40505008006e02035002c4d4044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 309682374 1250 309681124 309681149
    0xa0506060301020a0c02040c170103080a03050a02090306130302030d02040e01140102010606090e06041806050703050f01050f06070c08030a0203070c051f0302180603130309150e2103040f 82
    0x40309424140700b0360300c0d07070340255541514200143d003c3c00000d0880404550801c1240e0500641030303800c084140c3d00851241500c5586c0c0d8132174080c002d0840d0000f401d0100100d0040100c5030090303400184554000ca0081011304448400c0c0c50144d1951140d0909540850b0020030001840245a269941241c0700d400c50b4041109a10004908a910744c0c0524404210048003c3c80440c03c590300310340c0d000002800c0014018610784c884c1c0e400d80c804c000c088525035103410030004e4203030340344c01042d030800030045808026505040029450030018200c2e40c1c01303054041211014007540207400c034021b080784800c1da640c40c3c4111a00a403a9072000324142d031401003500001826090101141d502d80851907145480c0304500380c41200a07500514401c0e0a14400b007283e0106682e036036006500a0b105111940f07003c003000d14000d043c0844640c070819003103030b40382103600000f50403030314501010004440c00300e2620b4609030359481d0168000000e00340d51102284c04954030200c0002030094914002c01030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 309683624 1250 309682374 309682381
    0x2030904110a050f031306090f02130e0706051e0c0601080706050304030207171c020d260403050c07090c050702011205070c060c0c020301050a09170a050f0a1407050a0506 75
    0x1c0710b4482d01540b000050790030045080d046400002031038009080d200a640010705548800c1c1c299014408195691020025032204500d40704131481c0405110f04000d0110092140ca516100c0b151071246005103d400078a08024105041d004400c01110303030351454942007001c08040d62007409005003211072050060200d03801e03026405030391180360b0546c003c1000380c0c00c1160380110b41c144082c8402c00d900c5990340d50ba00e1038604a00d00084054103900030401050206401003a45c07040c4e0702000320385d44510005400700c16084000355031040c1c244c01c2195a80100c241003070300e442c9056103c40c116502e094003032000039a1200c020b02d8418002d80e03925107154005114803048460a4840c0008981d03c0e184403c0050a02c1c0c100c80c0100c0180e0402c0310341c049264001c24203582c0b00300c501d00111a0303658451402c002e109140080c0652180032000c1c00c200403403a01401d00d10a00c054400031300d0001c1030035020700c2e1061031040c006429501c86683c032072000c0c1c9410340da25242e01c48111118020300002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 309684874 1250 309683624 309683651
    0x11011d0106081504110103180203030307080a0501060f120b0f0a1502010507171501180602030c19230106050d0b15011d04051e0103030512060d080f0306130c02030904 73
    0x403405a03403c20f5030b10b01780c5c8200b8001034008000009402960000c10504031000d03a406101442c1700788640e80b180319080c50140c00e101c00712201604443e00703000c914030041d00b4003a444800d0203210004000b00040a8212400184c0c1685502c410300350b2040b0b243c0c1c2e02083c8041400d84401030550b954000707001c0781d01c4001342540d0810084d00068955440c4000282801c0c0b2120640040083d044c180b899454650030000c0340d1814594100001587c4005109192002c04008060800d00c0c175694142c00b01006070b0300c50080781c0707031008a0040300d480305400c00c81002b42903022030004c1c14010003800c190082c514103420300d02812180320311000002812a1141d50264690b441210f0f401400089956804000c00008183c05000d00c00000300c0000708008509480c045240030b075000741c860075243c0300c11064241c00c2c5440140700074029042580075200041025066030403140d9089600c540b039a8418020604c0002e44500d244a000c2c2841d429440c00e40c5c000c8020845002c0644061060131182c445 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 309686124 1250 309684874 309684913
    0x120315040921080606032202041508061608131b030609020f0907050a11070906120c06030b010507200d062c03030f041e03030c09080d090611011d010608 67
    0xd8407600868100000350250346602c1c1c1c82e90307001c0c1f095140b116003410503401150482e003104000080403100d11605103c502020000617038003c501440304d103141003174544014405d0102600798050480080400c1c0108032002924a04021b032a540d00500e086d684c4c1050b00140800c9982a0f0042e1242e02e0300310b11a09010400512640440e101d040c134000e031100e0b0441e40420752198010b2a40500342010503020414041c4600812110740a0301c44000c2a003000060300c0c2d9543d21403814980392080074035040c1d80203425201c0349500402140e4103006014900210414041c2d0341681c8011103200a10800c40240e00580321025a1021039580c0701070800c03803c58000385a5107880f440c0e88140006580c000c07260a44e47c1e0700a10a07452810002ea10307400307280c90341c1c803c0c54088002c40e071500c003402e85066102050300028131080700101940902c80c1000b6000000341e028140401c00607183c05150070308250044c541c80418552000080300d000071140d4001d240700e001e400b0703c6000d07030100b02d17200c0900c404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 309687374 1250 309686124 309686131
    0xb01050702090f130605040c031e030e1309150c09080c0a1802130e06040b0103050402010c17130602150f060616020a0909030c05010605010f0212031504092108 70
    0xc10401254590f010443c1010000400409103280c1940380c0038001031440c05500d0013103202e000c01020b01c0d030652a001083c104c0c44100b181080c44040c000c51702181e842103440101c81400c0e0b524001500343c411100d070150924400c090f1070100d0b940c095100501c0700b03910190107454543c0c3c400300708540395807403180c07100c88030644a54802c3c110207007030000c0c0103840c0b9114101019004018030b000000161400c03036680d10b602001c588640101000304034180307801030441c401801d280070080e43c505540080c10304101070002500c81800d0425040501010f401110b804c1800042019840f80d81ca950096407660400c0012a180200601113031046c035030359042500a80c0000d15503405c003103000140e00d4800c039103000e003a84d1010b0103020004616000748200000c1c103010751345030520f0010a0424a094401a901081c108140c0b4900c1c41c0066a021034100310320003a51030b40304d170381ea16a07405522020481c1c1c5000c1d0741c42840c00e040c0c1420030007010584454052160041c600f1140700301c0042e91005000c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 309688624 1250 309687374 309687379
    0x1805040608030a030209030102070c06080f22030c02010e04060f03140c21010f231005100c0201140a051b060103030905010503092401081e030711180f0a0b01050702 72
    0x50242440e8031303002e5005840954001f4000609062203502c2e002d0280006078800300205084c03000317001e074181061105540c001c140e03401c40004003500c040441d00204c8540809400c00c82d14600b09011a03104080c41c0600765070043c000d00555403035914100d45440f16100c1100e00141c40c1800c1d080c0c000002c20960942800240303000c0b520340b00203000c1c2e508040f85400707081c0c0c43c2d560f44c1d002e000300c410b051194101c00007003411894076403502c3c1e10804c42d600c00054100c0081c1d0182e003508002c1c6076150340182d005480103160101c0344e00003038401624010801146a283c2070f03004a00d44d40303074a40c00009803100561210402000c07500302c0d8071580d01c4901c00e00001d00000c003494014481c5c0d5002e04002c1d908844c3c070f0300803680380c0c034890041507940c1c92508080003141c00d2b070300004115050302008042c020303e500380d1802c01240492500c065591140c0707a0010002100c8503980c01c942d41d260241040040a51603081c6e0851602840742e4000b9242210303503000052a02c503001205502c10001c0d5998503602 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 309689874 1250 309688624 309688627
    0xe010b01031a300706021b06070b071101060e09030304020f0a2115020c100b0307060e0d03030b06030910060f050907030e010e030d0b0a0501110601030f0203030904020307180504060803 81
    0x1243e000da1810349a0640e480c000100d12441d5844078004100b00b800030045a8094800030744600c00003410280e8242c51700c0d1203014140180740100d088005450707042100c44c14610701c000310616106014190b564807010303080c0c1200c0200008264080001c2d4801d500c200d0700490141d48500410018003124000c40039440d00e190400e0071300b0880201c01d924070602401403907004480d004801da003030b80c0c001c50002840b03404c829040c0300c3c4081d00703010783d90921030110050074040e814003a005240c0d840e0b01850340d2040c0450400381091600030384c4034103400c02e00502081e82d60701c3c000d44410350790500707a000c06881c00e142c010b0000b13004204603001f40588400908440b03440d10380f040d04402134144100c14001e25581c416507480081000c0000b00000452844040b2303000780b243c41005950074903644418144080750003000503080700850744505480d806030891801960700d0000ca0f1a40c0289580c05800030700c00418041081d4005810f60701c804c80d000b0508400588880910090310b50611035032005500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 309691124 1250 309689874 309689899
    0x90b030708340311030f07050f190b12010311010201020703080705130b0c01090b060d020303040302060a0e132a091a19050a08010602011401030f02130e010b01031a 72
    0x101c41e10340703801e4603049401c015001440e400602d03212506500403103104005580800c280d040c2846400c0c114403c402c06460744a1070032001c1243c1c81d00191503d4401c0c042d04000c040d81e10100d40c00703007001e0503c00801030340301e0440d2100008541000e0200ba14036404955600f505907105008540020b603160f0b403107240700e40301d0b00c00942e05030304081ca0301d940607006460f001c00d001c2c040401409100c1c840398000324450a003420600b44e0041e01414540c01200c000c0c6800f40540c40005c21a802ca9070b051b101c440c1c0e590b8244004681504010203810f9100e86030307103000d203091031058000480300c03c0704040c14501266034585210400400300350070130109460400c00c1091040c80d8800b80709003002c2030300003450800d501d100e465550354026120004280c1c017140d0002c031294006896030240c000360000300401041289106021a0148801000910359998403011511854417107841d40d40c000d14203004a0b0716841e4050701a0000035001400280342c04070036080b43ea518410b0724615000a01440c0c0c40c030a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 309692374 1250 309691124 309691153
    0x109050c061602031f0606080105032518060905061905090901020f0d0e060c040b0d0507030f091101030c21020d14090604110607030e0f0114040b04090b030708 70
    0x4210302c1405549140c40e40304240075032000d000700220200c944d03049803003019001820404880054004030100407003100180815100040c0c020f20090690381804040310b000301000340ba0000c4c5410440c0c64801130b5007450401d8015421039015940301c10300600c51a17031564280701c800341004211200a0064035410800790409401c85500102c03010009894448280c40035a500d601009844113081e54903054151410030a01400d504002d41d000090320705403900718911002d0181040b01c1000b5543e40010444a074042c2d4000c3d04105080740c5c05001a05660500440003152035054901081c14070a517002d070280301c1c0c19900a801da455407c2040704101000340c000035040010400401e03551500618a0043d480d95a14402c0d06038070018441450b003845c0c07007007404030502c0500340110828030075030000980222524040b0841520226040813107000100c0d90700c441c410705189400ca0000b400314070307070940306c1c010416a0b21150701031004443c4642455581d046601c070700f51060304404050300509 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 309693624 1250 309692374 309692377
    0x1f0501140f0f010908030a051b0307080706022101080a050c010305010b041a070f05030703030c050304030507120c1506060e030313030201050d0207170c0d080f061c061103010f080109050c06 83
    0x10b001031401c03e412070b4840386810b1941d404180310401080000c114110184884004100b4445024020310304101250340d40101c0341c010603800030041900821030004040c01304415400da2010002481b01d1542c0d20301a40c0d07260144c0d1081696540222001c00d5010b50080c01410304844005c1d411501d00342c42c10b074000d050001c42d04840d000e0300104010b527201203030400c500c02662500480245503112854038018007200c2d2600201400c3c00014402c200c04a6042819101d1031508812001340c845d14042d0308540c4d0031041071009010455040c800000309805501c81c0060760069140c1e0104071074080708141da64015020301101e600c24490061005520640c050400480150005402d107046c0c0c0d0780340c814403000c0f031b82145017250f00800c0304144400c040101081014a9081c1103406040003070510700b0144c2c004240302c1c000d4078500702c6a40380320402e9a10202c4540c110100f0032001c0300110300c40400d940300380709185482d40b005101040c0e900b018441d847e100c65000006045851041040c044d45 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 309694874 1250 309693624 309693649
    0x20c0907140d061a090102070816090911040905030306040b0603131115041202012a06020906120f040203160f1404090605130b0c0a02120903010b031f0501140f 70
    0x30b82d100c043c0000c8031600124944061415080c10a44404925000910700314955100c903e06074840c002103220032958441d41002d80d4907410000c11090300703a0800700700312410041c1c4980c005140015100a100c0084060f501642088130180200281c4c0020018036010503650030782d151481980303000001d6840d503206440780b00f01a0980e0303401080e12201000f650030507400b480e4400d001c481307581c00715039205c444121007100a2400903424110110750540d0810940fa00404417940094000714030b41d601c1c0d0aa0b80d400b08a041c1070800d0b4039002030841303015a000e440803030091041d9543c0c45005800c1041c0202a20800d0b6103000400b450312840b043c90005050a4a401c11340d500c121102083c000d00a240c480c205080744404c0f540c4141c42c05103c1084000c2039510011020f020b51071a0741d501164541d1150b22071005aa01d51107100006801800c4850310305a061080c0c06842203002c0000d0760708003503e054030710100305903a0307a080c0201080c41e00c1c24455900c0b01816682d034282c4e243c11000c403800b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 309696124 1250 309694874 309694897
    0x8100b040b060309060703181505280608060f090d08100b0703020c01094106070c0e061009050d15020307020304090b0f09040f080f0a030b01020c090714 67
    0x907030701c1c48070000c919264415a40040c480d00190300f003214a030340601480300d5554024896007130400e41c0b602d402c1025170b811062030041c00d445002040c0645601c3c1c00c4c401410040241c0854a1320500400c1070040003039125000241c011600040c014540d1641802e11500442c0080d021003089075408032100000140f42c032180950000022482ca1144270242c10114440d40042081c1140d060001d040701031681e1040300780c0415024400c070094201035120380584041005594030801010140e4126095030140340d070000008250a4140200010440c0488080e400f03941c078507480c0d102c2802000924821a41c000c80c401e050104910f003085c2004034040ea014100180b0608030501c20001680c1c42030380d012005030f00200742844a1007062280040c6240121035554000d030b4040701241520100030405442d008178410408180305803403085900d841c00380c2220715991401254050024280038013043e0040c452112940010704210079054010519525850000e089001842c9182d90082c1c0f090381 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 309697374 1250 309696124 309696131
    0x7030b0a05100504171906020a1106010b190c14030307140c060c070311060f090f070e160c0605010807030c08010c0210050603030d09290714092205011401030608100b04 74
    0xc03242c01b0190284050910408000d03940d00c4866000901006007200712106e5504850010003040340c2c200c048902c0c50301c1c15800348914803a502c006070364412a5440c0034001c4503c041c98207030071041c00710007144120000d4880901c540c00081c40c62006000346050590703140c0c0000c02054511b000305025121282c8a490302d200d00d802c00061603400c2100c2580c1c81074000c0d1b801010702850540a0040140c00300d6810010700c08c46140401d02112220060708180c144081d01c9401c450f20761013610f8807600035810100909c0903582d1110320075070300c128503c000d503562a1030090204a0842c10b01441300060b40540c01040e85007000c0310610024040900107a516100030011a181c98039a0b0041004460182540d0003564a42c1030300483e0410403940d204440c600500100b010294011440254030070100c00d405480c0c8588001042d50180100c1c2c00c07480490281c0250400c1c0303181e640015060b1100c0d142c5603131102003020019004e4601c40d0103042c1c02034002ca0043c04c1e24003015400103d0707581d0000c0c0f011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 309698624 1250 309697374 309697393
    0xf031a060706050106030f0c05030402040c110d02030315061602041a03010905060a0e07030c0608040515010b0910090b040e060a0e010b03071b1101050a0e030607030b0a0510050417 79
    0x500c5a032141c4001c448050311103004218460701440340522294403044203201ca0351001c0001402440020002841a5502c040070310300d0341d10234948010450140c02c02c5948000304a0750107541d03900112500000c00b04200611210350511000f80c0d281f80580d08694120101554200000360180458201e4164052a14040780765002d026010901e030103030010f001142400003100041d2088031031140460b07170004c0300410018442c1d070f01d00e1049031000d2070651400e0319189402801d043c5c0003500d88650102030000407a801c4d0324103008008186040b0307041440c0e03805580e001c0c0c503480014401c440c04d412040c4002c001c09a00e094520343e1000700103002905a40e00d402260a08a10230307001070f6400351011040045668200740a50f06404048040c0100c110103680c80003540a644460b65040040200d1180400b90141c80410308a08000303090310390328500035000074024541e04210700d01c60b0001010005180c200082c841c00c0c40700341a99194540303070403e540c144007070000540030440c034825000c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 309699874 1250 309698624 309698629
    0xc020a0201210e0d09030501051806060108040f38010b0301050d0203010b030a0807030801142416031206060305091b01110a0303050f010905130221060f1608070f031a 73
    0x1c9421900694460004003415801e140f421074500822506100c60700f030700f46c044924400101c1d2f5a01070b800f46400d414a035164906222200300110b0018a042d00c5c04512040e40e404905498840d02c00d40c0003001158a1850001c5400d16801c1c170841140d181d003040148503034100202c41003600d5001800100d4003410360130200389403041d13030401a0303618034011405904141c1c1c004415030040191403d804c9409031b42070001204041c13184a08614602d100e4204e404200201c3d007624007184040384659030322240781c200a0803003102c8095100c441c0d0b01d0200302107002030183c443d41e4024a20080101110701c000810050303c00041c244240c188407071b80300702c0e003020101048214442c91180d81e0100710b40c00c00c8005071680031010b0b00b00340000b5041604008200c040d014620283d260102c0f42d030020144580000342407403c0c20104c15034070380900e04c00c005e20482c0c92688036005140e550010440c042d007000048400703031010350300706000030528461010020301c690030160b0041d8480000c1d004031601d0900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 309701124 1250 309699874 309699883
    0xa0f121b06020d060f0806010608150607060c030c05070b13020a0810151505070b041e0f02130504231501081e010c05220509040c090c020a0201210e 65
    0x1c60302140c000030804a8456140182c8009203c281402c0240c0b9003442406a19181c05008202c2000780b40400140000e07403c0c020718aaa050182503c3c0d0381d030716603051070805440041d440001280c104200c6040e114450412540e01f40d0b00030242e51002c1e12002c4100340b0702e140001003a68084814000030950309400c0c00307031100d15000190000f4500c030401c401810622800d074413001044000300c00300e162280e005000c542e440c40c2d00100000f495503ea00c1c00c2c400b0340e45900c454500c05207001443d07504000b0300240107520580200d030354550074071080350302206a5008690007402215528280c84496010540d03034054182034009070351001d14542c2443c580c0352026800080f5503401201204405040c03042c0e03140c1d444001100074402c8004000740070300f052040980042e0540302c0149002c180d010b84c035060b28082d100c0208410000c0c00c250038004c86902d1103008403805249021443c0a10f1400040c05101031a03041e116030055032086c054008058001c0d84a040015844012507089240e0500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 309702374 1250 309701124 309701177
    0xb0f0711041404031e171b03070203070201030e030304080a0804080403050a231606050a0c0203011d101404080304020d1a100501092303121908090a0f12 67
    0x8402c0b6854502410020190140400c0580e080c20181c03800c08410f691103d02c241080840e0480c00f89241ca82d0503028001c891a1204800204000b0081c80304459000c4001c4c01028001d0b82d05110748041c240107da22440152801000b05004100714480d01e0700404005902c18004c0742100e0a0a599880f440c2c10f00c000d41c00c2c1142e00104020100d40d00f00001c400801c1d03145249001843c07511014104051740c601140140c40600801141e9034441d0340c4100304443c01250f01500910061099851303070901e050000c2c035116018020403030103403030314041c2d442131035426040003451300c43e644c59645502c1ea0360362014000380d82103504401a14081103c1903c451942c0d0007910b04140d86150290f28900005020f41090b81046a000010010340c400400c04001c03112590701040031311201040040e10f400c1a41c0d94010981c20f0224484622000417051150714085a448031440d0795101603c803a200c2643d0400100b41e407820078010303000b00d04a00d075801019281420041c018082084800c000b400c10304 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 309703624 1250 309702374 309702401
    0x2208010213060f0e0a03231905010b1206010905190513020109080a15021312030e13020313150225050706080601122018010801050603010b0f071104 65
    0x70041004425030040d030401d050101407608851140030800001d18049040c4030150001c14000c0000706403140040d110b1500c001d04504030f60a81c00700c00c6201640f4440303054281e0381540f0f0f00180e44d000b401d110901c0000e0702c0ea50340240a543e803c003036803a1b009000242400c03105500c100100c140c018000d1041c180100c00b0107c0c2111580178910004001c074441390440c1c00d4640104038450002903c207924100040144000940c0703d5100104000c0c64085582c490503000d01011000e406041d0003d4400201c03a01c00d4411400081c0161031910a0b8407055a078260b41000d010200808603100d9201480d040c3c111280151405112800a6032a020220300d2001462132b030010354030411004001c040020041ea0070b10021500d02140060514020040180d51403a01d4004034bc1003800c3c0c40045e800c0f1240050403681d142c043c006440300443d5100c2d0140ca012031140f030000316044c500041508d040300c4c03c4d06003451501703010401c03402e801d0b00500000c42381d07103030108402c0140e59283d00500391100c015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 309704874 1250 309703624 309703657
    0xe070c12080f0a060b07080d02070605010605040e0a110d020a090302040218031e030a0c060e030a0305040506060306040c1a0909090c011b020105090d1b030507060f110322080102 78
    0x29080c00805480040c1907240620301d804d01c10812190a5401d8889503a0403850198403000c010b1000b001901c114400140300d54a40b00c00800d580382c0100240c8207560444034240c51650310140c080d01110750341c000b4008090030501c503d8100f95130a40091282c1d554520b08400055a2035003c141640c00650506402c011500803c442d6428108944035403d6030b0a881d15038016034403600d180e240d109840f9200d007000034004602003409410f400c09907203018024202d80d90b41005410080c01004260307012983c50017940c01103200e92800080160150b03401c111824826468035083c220b2030351180d000302088a9052010b082203685240c403071441142d0031000f400140c544a00014142e01c0da910000307507020b98004400703000d0b0342d016003581e020300c070305485418912015003050303551014040460540303c21421004004c02c40c0c0803c004040f50300e50b46480005c5030b843d03442540c2419281100400030b40c030610102505202010b140c1e059000c0803907030064201c0d100c400860036a4070085084011088 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 309706124 1250 309704874 309704881
    0xa05090711011a031603080a260a020a0305160207060f030b0d060902010e1c060f090204020c1e03040b030c0f0c07032004090b0402040902040f2a030c02070e070c1208 73
    0x130103110828000e40c6841051114900395500c1030917a014022443c03080190790b410200101403c0c0001240305e55076990341c030038145082d907071650196118a00710300002c0e00305004103402050303c01360142001900e8001d841c1e150305040c0c04441c000780c55070302402055241c0f0ba1003645a1203003c1b40c661101d000301404611800340780009800c0b45150841d442c02201060341211024071075003a15a2629030240c80410170040b1141e404014040600300030398441d01c0003d030342508480c00079644003846040341c00d2000700420007403c10f4407801180300780e43c81100304200013003618000b44020001a44501c921074100f481c04000946006460f400846140005024204a54010000c6c000245600303c60a0150900d1943d0300c5a810341c010b80000d00031500e03109170304110341c0c0304c0d0440d01c110309420104010001c013040102c0701c50481d00407040044118514903c00c41440b80c0038540201604d0340090081a281007440102d0660081030f00c010080c404403082c00207500e044070181d04540342d5588840130705 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 309707374 1250 309706124 309706129
    0x1012030809070b040e04170f03190614011b140d0f0801080a0f0209040501200d0b03031204140c09040c05030c0a05011d0414040506010e0903090a05090711011a 70
    0x1902e90000102400709001c1045030420f5400c0c030030b5100750b02c91040c104c0c440d61609804028003400140e4000800007000f04982c102003503001d0740c00514214020b006060340d40f01c401004103105036409000130104005030704560002c0e0641002103208501c14107215000d59400360406450070501e10000e441401d81c0f5802d15030000100340500803910150110010a560b20148140100c80090181c4490030001303051007005e50200d2400754803041d41c4205c0e00310034400e210060703000c8480ca101892800d04008168100002504c14051554410f9203103912240c507510042c0602510255051040c2500c840701174458002c911300861140700324446e0340b410201054240f450310000d00340180114070040195030b0f44849140a500c0071703501449846034030b01d801700f03024000c0c0380c011141c0400184184801c101d0000b4116040310440300c485281900c0d8035000d16103901c11168241c0d401950701005005518100d44002d400544504140e114025802c2c001d500f5039914889040384400d031488010f2850 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 309708624 1250 309707374 309707383
    0x42c010207120f02100c05120408090a09050c04030f080c10020d06050603101806050d05060106081305030a0f0e090f0417070803130c05030604050a030e0f181012030809 74
    0xc030443c2401d0011400000c1c0007035581e80100720004805d0344502c07842a1003801070085400c000f0b80751155a10902e050b050150407a4440000b00c0d00900840324000342c011502d106031030146038000801441d10f45140c482e011510b5240605441d01d460801201400b00340400039422024141034016840c0c1c00d45286480c122000341d48010301a00c0200f003009403030340d0707512a2003041d207442c2054104042242c00700ca10050280b0f41100c1d420109400d0a80240500024170034120741c01c80e136500340b003540e0340854510110041800240264030a01c00c1d444030600070307851091b8203515482d203200b404100c8030004000c0d500c01d4401e50b0000320340c3e0742840b00340407113a00600d0030031240c0d44d051880c12800d0740d0f800c0301900c40141a40c034400707000c00500080080703c00c0c2e440010f04000702120854145410050380b160b150620440200354480b03012644e50410109401c00003600030301101c0e001e171004c03040c1c0f411014004d108200e05c2c8000440070900c0c80e2981f004001490095403022000d01c1c00c0c0300c206262 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 309709874 1250 309708624 309708653
    0xd0f031e0b060f12091b100807300c020c01090e0417040e0709080606030c1c02060c1e0c0607060b0d08040807090f0219050a0203041d0403020c0a0b0405042c010207 72
    0x10040320303400206c42601c8003030024442c214140b030809440d6031089000c407880907659005142010729000c03002c1c004240da5440c20802d0301c484c2d2003004010070507003050b65500c109030049030102c0c042c0001040050841580319620502446812010310407906419000381d02c0303500b102c2d480d400c07480140800c0e02e0740000110060a07a402c01000681131050000b940c400c02d00c0900e910840c0b03028a16a004054404646401c6501a1800e500c500607840f10b40d4441d00a5203494904403045600550390010000302d480b18800054400b5261201c2911010054200c1080c1c01d0b800c02c008500260001e00c44000400050001d100604429401c00c55401e050710803004401c0702050040c40144602c0c06031840140041c042403e10070341e1000c180c0d40c240e0950045a0040c10207090305140615109003007100c10788034611903404d9401c00c0250b4000c1000030206801400c040400a01c0180410b0070154000040d03e203500c15504441c2e04c89001502c00d000c80d02c114146a42d401003030407002c014041303858030740 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 309711124 1250 309709874 309709903
    0x5012408042d050a1a070c171602220b0402030103020915180702011a0d050d030c170c070204180b1f0503010e0d0f031e0b060f1209 58
    0x141c281610398059035000e120000740510b0724420320301009074625900007400c560103011380316400442e0405041040140018448407000325001540d418818030001a03480d0380801c0d1881c100c9905041c0300900e0300a5811003002d0150509001c015a0751003070803075200310b02c414400b00300911554031070080d203940d400240d00403401800180b00507550511034560080c03504240490245103280012040e8852503407040e05c00e1210000d002c250b03a03040d08403282400e444140015520421010302c0b003501030705603000c0d081f0b8000c582102090741c42504a00d210300640e280851008200f60444580d015003950b08410a410029072201141414000d90503c14ad400c11600118405c5458461032007600a00301e480114490560034810544140d448014000203002042040c04c1440401d5036405051740b540c0104040c0000525503034880e002d031006c29441d40c1042c0d07054a02d0700e510500a85001510258007110521650241c07e41740005848104180c40c04e0135140d017010031106003880007254040c1c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 309712230 1106 309711124 309711137
    0x402070206030a0603200607020103051f090b030d020a05100209010c0c180b121504170a1e14040b09031e101407270801050124 56
    0x3099074402c0204841800c0048002e0f4411040342001b01e910040070805000154840c0e00015007044000d0514508481480072940703a448841d04035005c11940c4401e650b0542c6020400449890028000b403c14089280c4880d5122900155030030036154001815030b0b0203901c95041e03a108107030040c43c075640c1641c03110406010035000761700740e1a01c5401c010010743c4600d4401c00840106076124001c0862802c0402905400b400041c400e460b0078000410a000c10002c403002425102500da441410b034841e1806032031080200130803880e04008481c0c4032013036008096003c0390180c03a4110941d81d291720082d00040c1c548002d8200b6041070650140e1150350100d4001401119500b01e002e0901c00d54040c100c2100c501c940480706200040c03c3c8440070380002c40200c00c1c1440721000740c0114801180c03030b03d01c00b80c00c0d20000e0307110380401c4450180d09900200c085000d0201c407007052030f024 = true := by decide +kernel

theorem cover : BRFrame.Cov 309532374 309712230 := by
  have h0 := BRFrame.cov_init 309532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 309532374 ≤ n) (h2 : n < 309712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
