-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2477
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:49:47.518391+00:00
-- url     : https://prove2.me/submissions/ad1ce73f-72a7-4bea-9ca5-04fb4ac88564

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 445323741 ≤ n < 445503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 445324991 1250 445323741 445323757
    0x8070f020612040201120b06070609020604030803010b03070e0f060904051e011d1e070c08071505160305010f0902090a0504020a0f020f060c0712020c10030f0e0312010504020705070b 80
    0x24500104019583c010840841401c0400000d0207144021f030006041403040ca0002403095a54191000135921118155009554050211540e0b561504003141c15504100c0304030f800074414a40001e05820000c03105182002e020b070000342041081c8041201916000303004c86038440381c0680340090356024100850080c200f88000c1ca601c0c80030520b05268440d0300400101c5610412043c940800c0c01c000c1103075034000002c1c82c3c900b218020901d04020148101c0300c1c00f0b4506507001002003907111442d03021602588010303c006d003c120030301d10190103a500074441c48802424403032040044440301c1d0000c2080d1000102080e40301511040058207e0304404040000191840300d9800d0f443c2d010000864030441510061160385400c01880b1030510070180c004008107194599000024005c000070ba054510052100d5100400048d000780188495290b55803060306080c1c001c0c0c0c1044e4084216050309012a00300506030703003840c0034040030f54085142128180300d48580040c00309441c20240c5456 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 445326241 1250 445324991 445325017
    0x12051602100f0906080405060a09023c0d050c1903020901030f02090c121f2c070908061b04030b0a021e12151203040b0d061703040308070f0206 63
    0x40c00070107000400c3c100362500700c20280a029001d01010500008a4983c070469144000c5048a414400b16080030020302d000386000c140c2c3c91040403603d081d01d02d400001c4406122184030380c00d104042111030010391001402d42d4000342104116403c05040408400d600d00885500356540d070f40c00720300b00000c26441038400320140910a02180382c80050140c01c0300301202c400d810324221884420307003200058a0800d00420398005c0d0349000c1c580341c4411004000250000f4002c0c1c0c4030048000303451100c640307102040310b507800000e0707074646c012080281903800c00001851581daa068404000c594445034088210b0424003000000507155035500e0320840c68000d01684600004418441c1f0421800d001c0b1a2708000340a00130480e210712054651041e5641e004040303040d10140801d40d4a400031707490b840d60303000001d000710300419035400800500512440070000c07103581d60200401d541222500c0e0115800030802000840d80b40d00107495070b1380c003c0c880b90780000c00b5a1b00150884c0c1c00140030340301c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 445327491 1250 445326241 445326257
    0x1050405060a08060a0903030603060204031a0a0c0c0b04020d140d0f030902010806061e0406030e1e0d050309100510090e06040b0c0a050c01050708010807121205160210 74
    0x164101406980d030082000d0b50119800350610b0059900c480d030050420b0355043e611101c4806041c07007600f1034002160000c004650b00d40c2c0b01e007088400703007010440c10b821410307400e00030039250b21076403142d00710004181e0303145810101c2d03984c1c4400300188081d10999100d030480c05092b01040f21b004110160680f80c00007082805031909002e401c1000b180061424103141008142c0035036017140f00260301c4002211410b98440d00410540020a18041d409a040801242c00700b8290341590001c400f00b01000700f1502200039448035a9401c00d0002c102c58226000340c290b20712001d00401c080d42c1c12401c0d10040c1c5000c142c0001048045800454480340716104108040100b5a85842034a001c0401c55000c1c28903494282c6400d051060b01408aa01d8828005240980e6502c9107080c0c07008640c0001c0240281e04000c0300003800c1d00c90a00900340507004100000035100d05500a643c0e0340c5501c10000003405111003401d9605230001e41c6059107840707070640350708010703075841c0c03600c07842050641c94001c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 445328741 1250 445327491 445327499
    0x40f0906020301062d140a02010f050106030209041401030f120504090905161509051201020903060f010512030415030504060e15150a030c0b0d1104080102182b020111031201 76
    0x501c0c518140c3d82414601901c0d01170032407843d80151150390703500540c06407558407622040100d00424264894102c3c291502d400815403640c141c009285c28641180d0500140c1480c3c04403003801d01c02032100a04003100311029100203655521074281c0b40c0c86908100c0c0c200b9030745a00b81019207030702c15030880f507540100481c1e07500c4150b030014400c0681038101c00b0b240c5401203410042c1c814062030140300d1061040d5091520414025011185a1800513059a009050510076490850000e00510340f0982003801000d40032800041a94116100c8911900404100e0315080d0020a03029005403001a1110b1941680d07aa08200740343d40101c3d243c04c800c40d545098940307141c8141c8425001813041c1000d64042020039003466501051b906414000e0b07569084101c0c0d010014141896030040c0e00300041000500d0140650250141852030310245071030031040410040c0d040001080d21200d40032054002c2c070341c04590700c4a1030303003030b481030404440c01c0414072a440c0c42c5801103580e40380400e842c0f0380144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 445329991 1250 445328741 445328777
    0x30109050a0603260409060e10080102030f0112051009030507032007271803090b090d11040914070f0e010602060c030a0603080412061802030309040f090602030106 72
    0x264407804980741004030780d0642e55900001c140440c0718401d110200f00c0c0c00100c107601030046078010000e051080001c9552030310f03c4201d0900c101c0f1090207172407810741d000030851818000c0341e1207503007000d1414442c0d03801c0c6000c11000109003002035540e032080152a01c4855140d2141a64050081d01d031551601c10a2400a144514444801c0c0d181004002000003980c2c2c0042e52205840c0400c0d48881d4828a480140410407040c2142c100464100440c2c40300341c604030040040014065a40d0703495a43c0c55440d403001c40e00c2007007040ba03044514514000c0111700504414042490010000304202c0030305d85410201080308814404e480c0c01441c0c0401c4480c1c01100303c0c000601c000b2160030f05540c900309020f521218018101d40114034000002005003540b54402000340d58072610003512140c0b00c540d1030001c81140c4100b126145c0ca032440340c030120400e50b0b1a40300b1640e0700174019490070b031440307042c031020300150b85589044940320038400002a08900203540680440da454000c6412840b000e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 445331241 1250 445329991 445330001
    0xc080c0a020a05070b07110a0e01050d03030e0a081b0622030c02040c030204150e1806181014060c0a02061e030406020a0e09220213020d0e010e070807030b0406021e030109 75
    0x10b08c0b4004034001080740c9110300d00114112070040300c560040014074141039000e000320011110140c0112024034040001580203080350700c480141303802200034401c0085644503c02c4c1e400031442c820030191a14001681ccd414540310398030078030b0100030b481c090380d010405803450240c80b10082074002c075090004c0035480d46408407914951403e0050060041c0c003050038007030065a0740c081d035500000040c00d0b030786134594641d011401c40403005080c2d2a200e84061070b0041940980307420800941c05106c81442c040c0e00356030300354001c10301034200b11186a0801c0b84950180f41c05608014046c201c180d0742081c1ca0000d0b62003276008900141e56480030a4000f400001c58840c514403444840c4140030007001050080880310240a9104003c0105800042c242040c881ca80c403802d0750001038440c4607a101500444404a02d0303c000b070244000c1c00d0036445d1a0507840c007600d04161f109190070070100740029140c40e0814000c100052501c82c0700d0b0003102d1513400004902004810000c01005039a1040c410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 445332491 1250 445331241 445331273
    0x2708010b04111206120303070e0a0e04081909090e1b01020102120c0a09051f02160515130b0c03030712050105060a0c0501111603120c080c0a020a05070b07 68
    0x2c0090200042c01c4010301e015142c1810480c2c840003000807415100c00400c050490132120440383c492500c2400101010700380c0402034028041000c0004840035181c12642c01264442201810444a0944140100b000c202000204030181400081d00c45007446020100202c0c1e402401c1d4880c0d40003445054141c000c000241160310403c00014000100c0c3d55a83e084154001c02d16624100124126540c00481d0841070b403159121600110f80d1419518070000560603070251280d1042c82810380d1144230709442450b801c0f41c45003650b200b03e107101500802c92000d40d40c20f42c000080c0c03100740070002034100250b2407540c0d9100206011030180c2045078540c0343c00d50f001d028030807981080041031260040040400c140010240440100300e800e405c140165040992051385420704900c0490244111034008e402146420303039260080310007030050325005c60040e186c4403200d48032114903001c1ca900c440503600c21401041d80000000388103001c100002c120000807591540d0300360401e41c03510034124034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 445333741 1250 445332491 445332499
    0x1308030a09030206071b0b04081605130b041d0109051e070905040f02040f0c0e0f030607081e090d120e07030209060604080106090e0c09071409012708010b 68
    0x8080c0050744103100034156641036800c00d4a40080e4130344035101c0f20701c0c1c0c0040c16070002440400304044a4100c0900300f1150754008440b00f9101500c22004104558040c241e004842520320b882d401c0c8040e001a802548041d00010302c0c40c0b919650100c07550100148000ca50b51180406420b20200700300c0303103148041002465600600d021495565a1200c2c17140594640c1c880000400f445002e4a409610503005003040c03102c00c2c402000c003c01016030ba1582008101542002d4100d130405824012613400081c00824042c0c031080410785900400504142d41422440d20313a01142c4200e0340c0b42d90050030010020540a80e0391031020301119035885500c11407901c2d051144000040c0000c040040f41d405603000d07425600e0340b002041e81441590840b2441c0d40c01c01d40c001503a09200d90045503641403110958000051000c20800c80090550707a40f07001660403105088601e0b5094001d02d6141c41c14104034a00b02000902036028221080e2022000a804401040610028007d11900342d200319 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 445334991 1250 445333741 445333747
    0xd0501050108010e0105040c090b03071e031e05040507080d05030103061808071407090603140d0302030c1c1d010c0206090d0504140303041d0a1104140105131a130803 73
    0x104c1c0185003580144619807043d074880300f503105610300070f01d417401c0904860308040741d49103080c01011300345020318403040d980141c600c40040c218921030701c40c0409420340e41c1034001050140b1101e0300080d14000e80151824051084009102e86003000b0000e0111001d4482d41c0e141d61540c200f0008a69001c84024280340103034219000140a000868105561001050101c6010f00300b03101e00e0f114054011a11740c52900001105102160b00c2071240c410104040740d641c410342da4004c034141d020a0703c2425000b80140003003c003000102c02d020015a801c0304002460428200c420b8009403890703c03c00c91707141d5517652603500d9070b54107105013a4446450b60041404190f040001443c2d80310740c0c421100c0d2088130f800b080380150750a0084800800040041d0004040303204500440c0081c2070b56801300217031400e64400d80c0c220b400c9090790100d64001c12000300e845029070055070701e40c1c4200000790b0101604135000c60180d10310750710b00f07548170b088401c3c158803039a0210801c5001d49080e0081103070340e4014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 445336241 1250 445334991 445334999
    0x23040f021308100516050c0c090a0917090105040501122a08090f03090f0d0609050f1c080a0b011e020304060f0c11010f09030602030108030307090608090c061c0905030d050105010801 80
    0x7603002c001845d030702c1d0310b07042e50795001110425003412102c207503880c0d001080405001d0300c40525004400418022520720824a0300140e0a14881c480d46102c2c0e030204009010030021036000b606401d0b511101c10501203440281e5013000444080d00c030070380c00c850b52006401040c502e80d0024040750f105401d100102184020b40c0c1d442513485c060039100b90300c03840c003024075284582c0381c1c007908810b4554080003d20450015251940d10784446140204061050412240032444d05103400c0d88980c030300341c842c1403c0ea1038140c000b50207810803050403414005108018000d5480e030945908011246502440d151401c19400070810201e4110316410007803000b01003c003149407240c04080d107400c00d00340030f164000e10030800d481044280d44080d06440c8040000105018040021407051145603034464540b40c8900043d81c441d10180d44d0400b041d84510600100c50403c0f10091505080c2c80202e1405059605550703800d5580742c00c030460b030a401c003144800f8940715a00901e80944000d0800d10819810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 445337491 1250 445336241 445336261
    0x1a06030606130509010b0915091f03060b010309020d0308041704050906040207140a03030504051908160302030d0c3906050c040f030807050d030623040f0213081005 72
    0x10310802d00485542d100041480358000754001e0f0031084001e00201594036020515110f6887e81c0300703000c0d00442680c00003840c07514038201032170840701f00503000c00030440c02c41d220b400c01040c1c0b889284d81031640e12100b040259548a0f1046071451182d5118407982ca41407504007846441490b0401c0455070502042c0025903c42c00e0440e80300342c040d5401078840c003903070504806140e000c816045c1c40780900c111000c20b050b855000140301e00d001d0001c5503880203c400001040c110600f8001c0d05c803110500c07032284400062f90303880f8152070081c411030381080c0489500d1011248112020408a0fa8294400404030390a0410501001000740e0348080c181078010a950b2455014074010001e80d07941d80040d2102007144165005094000d180c2190141c0303c0c0381c460119808050192418403408400c03e500920902402c001d440c2c056510001460101c0803452516842e80c4556070701c16101d00500c0f5600043d0301c080d150b10208605242c0216280c414070600708080b030f14102081604103c2000b6982007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 445338741 1250 445337491 445337509
    0xf030906080112082a060114060901050a030c11010203070504060e06071e0f06050f0106170907211407051201020c19020627042d050c0c0102071a06030606 68
    0x20300b080180c2d9031800c3e0343c03203145c02c0c5860702c00101e0702c00c0720f1081e040b032000f031400106070341a1200b181030b000c00102d034042001400d0145800450000e1010400d651485200f5000750301050042c0c00c4c1460900742e960724140c01c1e0380080390003000061020a00700032140d03101514904c81242556014601511074030b0348160741e80d010318444580705100034588104150b07103001403049500f00404105c181040208050300b00c8080c0305030b00004503008440c003020040105690b00515402005001c200d1a0440d008054030b0341041c41400a00d540c0040c0021a943c01d6003003103520003a101a090a50510003040910308202864a02ea81e2040c0441c4040039400503000c0541c4070300502101001d0000d100141c12403040d0202c42c48154801600c0020745841d0745140e440d1001e04a42c00e00614003411440f000c940c4418a0380c01114855520ba251000d406610440c0c20102d2044502d10300031441c2d02d024260707406140d08641d0068801d607000d43c0b10007841c44039500400d04801414050400c8400500481 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 445339991 1250 445338741 445338743
    0x100221040e04030806030a080a0504140f0d0210020111120412080f0c03101d0a0f15182027031c030b0a0b0c2e09060b0a030f030906080112 61
    0x24480c045000ca40c5c04001f40080f0b564007032903a66481c080c0000080030b41d0401d100318915035003040051001841d0116012640b01000380070001503105a400700800d0007032181114080d55601c4090a214039107000041030500c0c00038540c4031003801d280ca0504101e18040208404021800b424061031070301c0d00c40c4068001150707034907040d12522660410090306e0b0700d940c0007500030520200340d09034001102d90302e240f00e8a0070560400c4020404030444040e51690000e400c44c441c0c001c4400c0c084251840c20005c0d40c1d074803810000072002d4145441c0d44c0c060044d010104c8980101242c6540d400300d006481c55120503401020071004009103002c00e40e00c004078101900c00306440d1a403094014400d44c03141c3e5100d0300003000c40c021590b80c0d180038040343d44182c0a28106004020356110200a50b020003403009150500d0318401c549141e005000400300e1080131500d150302c41e03030348100b65929181c1d074201850050410340100e130f90038503001d0b14200742a4050000d001c3c05c4001000150b0150b601030080c0c0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 445341241 1250 445339991 445339997
    0x60809031207021207030816020304050109050118080a0b1b04030b281a03010b03010501050d031209060f0b011b0308010501050a0203120108030912030f070818100221040e0403 77
    0x55210b9110503403c04a001c682c1040a0701d001c50310409040d0300071800d9010720b1480c1100440b5400080d01281c9078800d50061340d0203d00c0d2007404102d154400d41010090081c0040003c0c5030641340c0020a04003040d150381078418a05c10301c20700c13009401c04410780890b1200c90b51440c1c90300e86959100c541c040030040214a442c002c00d582c107081402040c1410071900805841000340d1201c2c49060403503020300300b1141d4000e40c80c0036500609800c05108060613900002d00d0b68010300704650782214411000c200001607641c54685000000d000b5006003221003131904000b00d142104100014020b0762140745801c40c00c0f02c0d0820000109401140183c19074030207183c00303070b90380030072030300c160f2951044003c0c103034680104500000f004000480075000d1148101d0f142440c01004090f5582e8a01561a00c080098010082a000205c1450003010021000302e001320056644034005030184600071078500250300302c60f4035584d652500039100591a80400382c454103150a10b175002641d020300820090038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 445342491 1250 445341241 445341277
    0x1407050c13241d0903160201140d0f05130f03180f0e010618080c0f010c050a06090203060c27041509020a0e01082a1b07050a06080903 59
    0x1008406401400891800004402641c8610700d01c420003000d451150003560302d81407602002c08043c0c10380090040390300e5801941040c2c10400f848148845106040b414003800b000d02e01292540900500800d80e81d5580015001000680a206907100100a0750301d40e0241d0324070324001003904241c1c024481e0145885840c0350034003051102c41120316006600703070f9010310000003812070120501034140c5281e41d4804000740041c40002d90401da180c0150325031074104c0210150903080a003102d0700e102c0303030524101a020146440e0141800b41c014401c1e10350035264141c0c0e600303508040000541104c4c92110592600b1b011b2904186090f0030014810741c0201c501c03c031035031150349039001704026440710a00c1c3d480e100d81d118000c00003540055041000b080c01c284000100e98041c59016200e603106403005901c1c110303120200705c5042c4400caa0790b0320103d028010001d00c108000624003a903e001c1000b44285401c000401000300801e1b401001040110420030002010110a85600c3c5101d0342800745 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 445343741 1250 445342491 445342519
    0xf050f030f15150705010c091a1606020f130519060e1201020a0503151828020d06090501090b1c0c0b070305071a06010518060c071202011407050c 64
    0xa1460785180d81580c806400f48402c450792003010001e02070a849030008000c40d0b00114002c2c4d0f6014024860705100700601c1c1580c1030004002401802c0134419030814942421055580360103e800c44294805900b001040c0d00216000c13000843c03016140c2140d0340030411074040c0c05031901c1c0743c5a01810081028164503085e25881e46030001c101004444000c3d52102c101ca80003c0003030304112005a030320100f041d008e101c01e0600340780c14020200156010aa995210785038a4a01d0740c1c1c0c03582200d59641d0300c404c10814400640b0150078200762040d4041491450040d0070419180183c0117081144d1500c9455561a42e810f0850403a50501c12a0000e03a04041c1c100405c50032001d038018014214001001810168010002c01c0b545100380141220b101c0f1403100d03801709030021200076011600401c004245009101900c5a0a110082c02d080c40c0c5004c2503041e504045c010741c440680e414290860400315a0000c0083c01020f1050542e01e08040c0191a0160b49200101c811070048032005402e030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 445344991 1250 445343741 445343761
    0x50a090e04030c020114070209070f0e041109030f0106182403060204090c111e010902120609070509070504090f0b190302040e0d051e04030209160f050f030f 69
    0x400202800e40e200112803501d42400b82030789056000480c002080300040d003040300b407101c0c250303448190060101903447d40d5041003656820348000f805800d2002070908034102d0303902ca000341c450b0f400c06003030120b0315081c0b843c046c1481c049451701940b0569040c48010702900303807402d0003a00114520b0070007080b040b10740040020034800c191360002c40485642c00c040203200e40354005008841500000300320b2030300b0f100030490b001d4003080c5442d20b5680003075500800110b400c00003c59030f800400b00000d03910050382e0025911501030160b402e116001a0200300742e202c4240035403001828281d48005a40c501510000c109200340d000e5803038059034070300203404042c1481c1e002c0a4481800323030500c1c0081660b44aa08807900007440700700d20a0741020310450001c5070204a80c22900c207217449690400b12003158400c6529407a541481c0380b01018000000540c0d900114503002d01c6803604d47c007a0742c0300d121400506806007800007100b400350420007244140d000504907640803a0880c001e400c03d8840340011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 445346241 1250 445344991 445345007
    0xa021e0f0c0d08040215070302031c020405040207050f0d03140a05092112011a040902091f0c1101020303040308071229040f050c0307110109051009030e120607050a 72
    0x4254521444080b00d04107034000228902690084a0390584c8004001d038100051084040c0100107030018000c41c2c5a5401d80e14004802c840550300160034651200040b074100d80040800b46e501d030348407006a4404460038001d00c086030741c113031038144144188441110700145000e002c00711030b030f03a03268006485443d05020855040c0c40d00b80700d44d82d5100e544c02d858549500708582e0001c80300c608100005003d0760143c0800340c0d500c445903020f0b04051600340700c4d100075008001196000701018459802d10164800840c1c4a110f25460b200312082040c00c10081001c162002e07141550f00c20010710000c00d4219003daa03102041c1e1406032000318100810340058008410400c1804a58008050403080380080c100c15034003003500d040081c030449a41050a55209540ba000070100800101c1c12040c03103503190000003a021000420003030001c1d540c03a403400c003010010b030000da070399086480304040d40300d80c048000325403c80e104028810405192900d800029040d0360601000052909080d4090380740 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 445347491 1250 445346241 445346257
    0x1080d050318011802010215060a0501030b1c03081602070b0d020306010318030917010b150705160902070605070309030f18030c0f0501110d0c02010c11060315090a021e0f 75
    0x900c132400962070440002c20200c1c030102e0141c0500800c03000e51414103480c551150b0002024811031525240040d40104021424160400808100110409180d2261610492080e43c0d80c040510300003440b11104030486100b60b045402544007049000c20810070f43d444680090b90060792510f942006a008007611021100c0010010035980c0606400c900c00404a3f9800c0411200d42c01140d2421400c80301c1c4c0e48031403039110102424a081c810f5042020b4400c0034401c1084503042d0741300c101008058081a4800d54101340c0001d080000c001d41401a550002101d00301841448d0707003660007816440054400c801000181403c0142c101080018030001b5900408105031090700c40c80c07110308160070360251601181c444208018190700020300641d1042c120756a0454031071895004544491050b4003c0e40c0407910100c9034103241d681c04000b940500420301d440c20007803107031406004c54400000d1014130740c24410b00282c1030400c110034100c10000c00f900103550b40c44d0b21040d00d020700e034055654 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 445348741 1250 445347491 445347493
    0x2010e0406170c0f04061d0718080f0705090c030f070519030f060506090310020903011b030b03060622020c030f0403030f09081204050d03020705060d060609050901080d050318 77
    0x100d042003111000c2210841d403d415900e001c95690741406000513a041032203101e405010080c040e0095460185040d42c1107250780c50040200b07a40c40003442c80031422500b1030040342d0400001c0e0441280200805c2000740710a8580103081c0c5070001c500100350100a0040f03a590020b40006040305202e0411901c15801515101c02000b80c9101c004000780588804410348078901080400c5610b0020280c3e010118010000c0204603291004c590182d00481c81d031039090340d21480102440c41d070502036844055129a000207500c0003c01c10145855400b41c101030181ea00c0c5030400d680484003103100302c01424000030150340c0b04403010303113186540304058824030740060100c1d001c020140d1140712541c0c800340955981c0708060300d4500d856200c100114820002d07850800c4200214200b0301c00030a401800380c01035a845640d03802c0483c0d807a40c00180c0c1041540d0390780000f4842990002c002e0006000140c85c04030b441e6041103940343e0b840c0051a00082880404000580000d8000c070318030102c1c1d01018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 445349991 1250 445348741 445348769
    0x41101140d0e0105090309280e0103030503090d1e030207080d0603050c0306010617040201080619090b0a06020109110411250b09010b030c21060f010303030617060402010e0406 77
    0x403038201c0080c5190394400c1195402d2101146481e00d00100741e0301d40582c000c00103d005400c0000c03030642c0c0900304c602d085402c86c1440000404031070400b03506000310b01030386480e5540e107003143c041030401d0000c140803418800c08181000e00a0204560120049128100141d0b102180c2c20300380500c0c010007019401d81c1782410710100803c5004a020741c0201010740c1100d03a10b0340c03164406d4030509070b10760031104c085181c0d5000601642c8a100d80d50f40002d000340065040000d0b840c0d1000806070b0641146402644401e5082c00f142031504c1c030000204000d1000708502d00c0a42e07207605500b070540c0f070758034440c5849001c0364880030b002400316406215940c56200c40804600504008151101d0040c2c0700b100d442e00024032000c0040c003403520b08640050140102c1c006000c1000107004164000d0518116420300c103a00fa07100401c03130240111921104404903600d5072500400342c40c481c1d003200a100049402e241c1400b0340014049401c1942420005800c3c0c4c03251000c90001c0c86180d00c41c0503661070311 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 445351241 1250 445349991 445350007
    0x4021c02040308070b010509131709030d020106170c0123040f0e07030b0f09071110020a08090c0a030804060e131a150a0c060203150901080f010f0b0904110114 70
    0x121000708031880c800c20317240b80c0e66a0380d4010440284001c13507111440f448036900d02e000140780321040b214401e0002070242e00704030144000c40d21300044096500b0150b90344800a1003030811840260800682c1c07000104600e50380e0307400003040d107110211105800c20035143c10720031041c95030042d1005404000c044800b001d5036030102c403905840940341c40340801d16084100310b09041c400101c0c0c14450020f0f203080718a4494445c1110041410201d01c1b00ea40a40516407100514a0006081c0b405443d66034040a0400c45030450410355202c100d18030461801c2d20800020300840e043c0c1e401c441e19070501d41c0301ca00c0d9000209042e894280350720080c4516001c02c101c698020640c000c00780e000159066242c00d5a007404102903840340a80b0140415603842c011070000d60550025a03204061108139842c4204c01c0c00898003544017a000082150020810440003950920503010006100c100c2030000c182d0030004140c091034098400342c4184103080c948141d42c1d001c0c1c1d40302102400400307030300f5075183c40b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 445352491 1250 445351241 445351253
    0xd17040303030e070b070206090112150314030a0f0f020f07060801140121020a0c1703071103031003290108030d0606022419020a05072a030204021c020403 68
    0x26010860200c0d00d40300544202502c0003561034150b494592007185010016000c0107200d40210202074100110290710318400300060150b200760742c4000c8060007032503086180010b50f503911000d4608852b8814440105087d922040f4482815194203296000d40803042040f420100c0305032203d400c0d0f01c2100c20020b100c40d03000b5112412110a00c1c113850f07003c0010300044503815400b0b1450400c00e00007400c6520404c520303600400c182d070b05601f05141c0c0c04d0711550320380d100500020207071442144c0c00b00c1000a8503400101d0540c06c64008d030b0140d843d43c940071070941c00d03c42d214080506014441c021b60300001c02c0611140b50300e42c00249030340c10349603500c000c401d90766805111000101c0d0f0030410300241440c00020741c4941044125900f00301196403500100384200002c1c11904000c44612015407a040c85100170009003440c0c0d9103e5648400034200710785010742d28a03c542020b01303401006c61041d00034145a01c11381c1d6045074090b030b8400a05d50401b00000000c4d04185441c1e200003400810011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 445353741 1250 445352491 445352497
    0x603020f0316050706410f0907050307080d1404031707080702030105040f142407030b060c070e0105090609063303010f0602030c060403030f0207060c1706040b010f0e0d17 75
    0x241d10007031b8582c90399440288682440078006140360549220001c070b2115100b1804841c0d102e216071040b5100c1c1ca07070b2035001038070300000c40e8081d11a03508002c41c41c40091f80e208ca41c5510160445a51900d4149160b541080c0c04403003000c0500003400100b600d07001c00004104680c0708903001002030029060074103140d50001180c1004841c861505000361100c8040410b40c800c440c184100c40d19030441c0d002c40e018a074040300038801000c05036148980c41059440802401040c1004002401010709000c40d4280d4008182c211611603601d075020400a40d99050149a0041007510141c3d01080b1010295050000da51554103604645034013400b01424020080c504840002e22031100982e50742c0c00c00d07030720f0348144208242c054101d0b0000401082c02a00550401ca90100d00146000c2140c0c490004030f800c01100003000950380d820a2402100704214280c00c2101103c0400c250740a400020b03003007031414581072081c84038400002074a0303981c0c42d240303050b81a080201e0a803003468140c802101d0354 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 445354991 1250 445353741 445353791
    0x5070804170625030b0a1a03150604030c0b07030e030f0c01020c040902090414280201200309270f0f0906010506030c07051e0c0a0603020f0316050706 66
    0x1100d2100000c11a88803c1e54002c6185120703000446501a0603204602518003104002e42184070580001040e0000c5816a0138420007a9005a10b80c03c1043e00b50b00443c4401c80345501c9003a09020034404070700411a48001c0310700c5075046954035812440c05a666011040049a1500501c0c02d450210705000c2080f15102000f6401d6403811074407a010001243c4110401940040310700b400500081c1441000c0d024030100101280c4145510b0010080c00b00340d0b01203c0054000158584011544c1003d0b520614030700322803400250740c01c1c649845603240200990544102c403401c1240104004c40720240c08014983d100780802072819000d1004004800e03030704170906406400c001021b4140c08907900e81a104018501460f40e20340c040a403c035500322a4041e00c650040000076032984c1e442407104110603410001502c2500030f02800c0040c00070340ca41c400300a1500400c035910100c410802202c2d8441c400006840710f0000c03015048440f07000d100002003089290001a01000b08910301c1c8040007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 445356241 1250 445354991 445354993
    0x1b0c04060f08070e090343021302070525080f0a03090f0e13060b030a030e04230a09110310020d0615120b0111070f08010b01020d090e04030507080417 66
    0x20703568140388040e40c0c800c5074402c9171354005214102a42091802a60100e044205107101c00c074404a41d02c10125074140c03003044c0e01c02001d0702c5901141401d003c0300c8861003aa20003103041c10850f80702c81d51181308020f2030403440d030f04410b502545034083c030080c0fa024061001c01c44845003011910b4564403c01c40030250040340819100069120b510144103054130b9180b41b1888082c1c48043c184e40040b81c210b1001c6640341c1c0c44040e19101a10f04000e10b48005002c0e941702d41c04050b071807042c8130484018001e004185032101c20b8130301c017000254002c990006a45000084d4810403030620b1402000000041940350240b02810380b014019600034041d4618840410401d281d940c2816080700d88090034480007150340c4107415402c561a42d88501c3c04110706041840f00545190f840034180307980c50300807021030820003005002920091180685850007800103104a111014000c4c20300402449603610078600000040c08240c07140003074801040d0b000c440c89884a40346c21003490b00c030280004a86031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 445357491 1250 445356241 445356253
    0x307170606130b030d080604140a0c030c020304050109030b061f081902070b0609100b03010b1b010e070e0702010b040c05040603050601090b0315010207050909060105011b03051b0c04060f08 83
    0x8800c10320b103d100d60303050000340109684100e002d010b4400d200c00410342a441075071841603c00d001110200d00e4464514002c1c00213490400c2000502218140703217400c800c540c000d200500050b40c02104810036603401030b52900c199a14000014004420782c9228041c50414441001000b508400d81c24003441c040c1c107445c0340303c5031700300000d504900801d000a080c030a1002c0c04076003d800d00105090300503000300c903181c20f81030f21080400325650081c2d2008152090008041450400001c0c100071300d50b03000302c002e11900c4408030210740c2c0c88445000e84000c2000c490003003080c01d4000d512000351804047d00a012101c0f50100181064101d13200c0c00c00402c0c00c20000440c20740c81041c5100981e0010b40309c107815030b1208884401011007040d10203055211380032000c140307a0345e011400d0748142d10100040c981c0e5030620000412240140c070000044603406403803940040e401c00d0030b641002c0102c403030079008101580202c0b46040b1001d44126005403400d40c000c5844a810801002a190f240c021940 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 445358741 1250 445357491 445357519
    0xc010c030b09070c1e050a140709060f0506090f190602060a050a021201090209010c0c0902070203011d0a060b180901052e05040e07030c080f06130803150307170606 72
    0x10382c030384e0089002002d02c80344581c13914403410000d0360507000500a401b00c0e40b81003801e80c0c807850082c42c601c40230f83c3c40c0d50103e05c0811269103240103100180000410b5220454648004995035001e0030b21342511801c1d00f18000c20701c903100c41e0f000303c558541d8078002922442c0d466102940316401507450540340d80c14440020799018090084460700d203100c00b04000168a003c40c00c10094005000c2e1504010115903010003141000704484080d004001d001641c50216104050031280b050600303003500c660486c1c21640e02e14010801009d07c0781c1140c404190940d0800004004e4000ca80a02964030050000e00000600561040d8400c0002d03241a144203450501e50f1568000c0c1440c0e00b01204d401d004050200c0c2c101504a0b100001862084441264613075880d00919801c03604004440d03404201b00001319002000010f07041070030f02e04440014402a20f446040348402030034250b00f088070740d08844103910100712582c003d0102d0014400700c0100001c2a03903da000030b640c0584641702c450070390700d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 445359991 1250 445358741 445358747
    0x4020f1306140c0604140709020d150f081e0109081801020d09050d0201111207120806060f0f0a11030307020f010e03030603150a0b06123412020c010c030b0907 70
    0x500b00c02080c0700204111766440d40d490340651020052910035001d0b4a03070000340f8003494005443c006010b0f0101281d01400c01211b2030000b481da038042c90070b03400c10a400704060311003c5598a004132810407125100c0843c1c021890142804010081c46201c0000300b5031032030103400f16083c8000d0703001d13400d50b440a0b52000f400c8540005500a850380040100c654500540c010701c00703000c071700d054034003030724410340c4501c042d0005030700045030a0b0b03a0500036000043c44958080850303070b4003540071511241080207901403102540078003117070801c14040000f0000c481600801c0c0d06c2d9040c0003d20704403035507850104170003911030101540742c40942d801c00b045508494404001d032440ba2501030020300e0003003140c10710001d110303401510003070f2440d6862161100c10b4407101d00074085d2a074110303500030300c40c1004000000c80361150b0550280841d030400407200d01c12240300f82100c0e400030500d4002c4000236a0300c0660000c1c0704155010b070b045e6183c0720100c512184c06420101d0400000c0716180400e9403030f0380040d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 445361241 1250 445359991 445359997
    0x16030806030a150c03090f03021c0906020d03020f070b10090e03040b07020d03181d010503010b1e040b0612010f0e0c03130c03050d090503010c030917030604020f130614 74
    0x140640c0910203d02c620000d55803007551071402a18002c1200e00c500c0d2a43c65465881244c140d00580101f03640603007101d0040e01c0c030000c20209142220100b0301d000c20007501e440d220f03e0320404040d00010711604000500003aa0070440c0c105040742028140440c22a55400c01c034401e41150904003c50343d460b020000c07040c0c03001c5510a8200d00d141210307503030070030038041140300c1c0440600202d50340b000c24440503092040b001e880c9104451007160942000c40e0160001640031620a80c140780d20491140c48202c40260b20408690b80a10404030103400103001e4800449600c2d009200803554038612142c8044141c100c6150b0f0b4240c0c40e0003910b6440b20802801c0481c0c2d5403000901c1003022500c01e00038040070094a074002e0154040940d180e5450f039082401d0720180c0c000152402c40e0a00052030b0a124074025800981000c00020129680e0020a102c10300411400e1440c00b00018500303440c1d0350111101c40d001d61604656485a00b8a400d1078110b0a014010000701c0d80406441248140021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 445362491 1250 445361241 445361243
    0x1306061b0f2303190e0604050f121912020714030d140f0a0e090f060901030f0606031a090705030d02121617030411040b0612040f12020a020102120403080a18080316030806030a 77
    0xd0840d03849d04850034030561407c0310030a55094032900f850400040385440106881b1740c8514011000c890840c00003d04c0c21030150001c9420305c180d505c2e000401e0b5400101103c440701182841c0328062070301e0030301d2041c1d8026411b0400030740d00002085224030380d2040071210040801c41d40304200352101640d9509040044450315040394a2100500114408001010b038030740c40b6402c0490410388079a1291284003561f121018100300100902007141c505002d01d002034901a03008001c1e4002021000390703a00d404080081080600003414035604002090380070325076800c16180d5903c90304207824800d01e58004c8406542c207040c0e608100300149400d00400301a00c10042030f003410304440d1040302c0b00d03420025108a0b00584c0042030384000540c10b500054032002260007500c8060030500029080006007a0081c02d0124100424070000304500242c3c0d44450003440d098003103440a00c07000700028600d4111074500e1101060054410242c11410711165102c0c0c2e65100490b120300060640d140d20040d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 445363741 1250 445362491 445362499
    0x406020303040f051006181d03030703180215280504090e0a060e06011401030203090604062d0b04060503150403080a02091306061b0f2303190e060405 66
    0x400314021038100781440f03401501800a42e845281581c120b10100e4410754003040349004950458111222184110711600803c0340490302032001c40d500198413444000d2808003895520105c1030880007245c5038001c021580540300d00c26000558000d44c2458005c1c543d24540c1d180032074a80d01001c04d1281c0c1e0700c0e0021100d038503040d0402d41001400d00251403030400000d883e10038290140c01042c120f0242044d41c1203000040d004c43d505190401c1c4100aa5010140c11706004209020100c003000958a41c8590001c0b030004000259a02560450300200c00101252281030301c1a03803404126441662900c20841d410400d03070b6503a50605403100c40984451905104420001e808a40109806580074003400401454504000002900f1011f80000c0d00b400e1956000f0502407607422400b140031101c0c0b001c0105154011954030404445c201940090aa81c4502c26031408010001e000220a0104600781d0303888014041c0500451a91850140f000914a040b10f88450070170f07804440030b984001e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 445364991 1250 445363741 445363747
    0x300102310312050f0313020901090908070602090f030303090c0306010f030b040303151d09060112080304080721080f010e07020c0603060d020603040c03030e0f0922020301050c0d060b04060203 84
    0x1456506496003032440440510100f08450610f0404484c01144581c0000c410841c201e441307401403110741d0005800074a0b0040c80c00b00c5050110f5000d4050b01c2e10b2560085016a4a411400124507180c04c1c50700e00d5501b44c800071040c03010100000c01d0102940341c0540441c0d00a81e40d4a40c1118098443c0c4405400740030340d0008580803e2107a004641e1210101085c40802c0303941c0c441c40d40b0441e84419106480c1714481040c010702600601c400d60040855003103400c9025081c1c2c41c0e880040c40041c1005050000020701036080100c503050f040d81c1c100c07070b013484a015664014009003202004503074480115501c030002080002d8505031032b5019221a83c018450034208800340302450f8805042d86034041101d6100f40c0060751b40f40c00031881a88910020b1507260700e989009080110700740c15151042e0540358000c8034135141c01d40d03078581c007180402c0202c0300d4684e8280281d00b919800c0748065019401d0108110b4400e1698000340000545000c04021031070352024540c005004038090000142c00170 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 445366241 1250 445364991 445364993
    0x503061003110306071416020a1205060c03041212060b040e09010c0f0905010f12050403021f02070803070e13060306020a0e0402070b01050603060604080d030920010e3001023103 78
    0xc40068031580003121f0fa0b000c0f010300f0070b80000e50045041d41c0101ea54400700d00000c030402030140510703504041d14501142c1181071a5440302040343d14041c0801c200802044002802081c41d04440010030940407229540c0d40c80b509619050003048031920710035030030b04c6014400a032254484010460496480b2154075082030011201207814072046070820560101c10b58040b2100d00c80d007405075209800824100c0103424240440501d0917840350300d80c9205000030b0012510000c122580b00c8210301e0091071031209040090106903090100e403025515100d800710401c040c643c01801244519118004204181130803c0240e1007050b6004200142c0361300100320351308154018603013003400202aa0304240d2100700640c54104001c0c0c0f0f00c4002501c8460107001c5c004c403d012007500c0005c1c4186d080801c501680041c0c2500a06c0c071420b401407101c3d003407040403501036040400ea0f50015442083d212840408210f000c1d410000e000005e06a11600d52021b40c0c0d40144040c0200807681240c2c1003440c51 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 445367491 1250 445366241 445366277
    0x6090105043201030c0f060203030c0306061b06070e06040f05150f0a030c0f300605060f03060f0405100603090807140d080a270507050306100311030607 67
    0x45040c440e94a2000551001429444081c0350350700e02c040c07484035034982d0724509010b1a02441948103510707180408005001a550100c00c42e548240715400700c5540b501c840700030420f248a0800aa4900d0011042149142d800410307103034060702250f0740c1c070743d40d440c0c1c0e6104002142c8101d00c80c5144500d618041044a828464408940b00500400503428800d8000701c2c214103a21810030321000a0f920507414000d1a045400d20003d00d0491400c4030040c140e04c1d03541d601901650050010300c40c41580600e01441b070a0300504060100030305081d031a0f20070400c07607074001d400c152490b5200d0346000c0e00104d05801c1a1084611401103610941c0c011407820300260000c040740401901c0c206810030640c000710b07840b403840d0300828043c5030062140701c080703900042091602808040b4607500b806a0103404070401d85d600c45440e61a09000010740319a442c14034a8880b01d603026903014081c810421030001c50241007a81202e00540c09003400d050407404164507858101c0380030011801142141160380c40c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 445368741 1250 445367491 445367501
    0x20d0e180603010b061c0c17060103050910060f051f02030319090c03030c06050a092402130609060f0306050913060902030f0d021b03100c050d0f060306060e0609010504 74
    0x150140002880003046130114600ea8403401c03c4100000040000d80b800001e1842017100d00030292070060b000000481c1c08007141031002c3c05170340c10551911701041e954941801104054000488108001c81e1394a01c60142d52125100302403207541c02400d4a080714140300355010f540d01c64ae034091460b544e621408080400296a04969a2940c0701c0090000481c1c10919101541c042d07101d802d03280359640f81c01c02c251303800103011950f01c60034200100300040860850340c00e050301c0015041615509000820f00034020540342400e50b844001c800952241c01000000c1a03901d56900e0080d03e000f221805e03000d0b15168850306401c08041d1000030b18101850f4103d10580348900c3c40440c094085400003031805212200716140ea0700f00c1c42103080d20320380400a100e5001180c0c1b501c0b00301c685881e40007a88910207038210000c03207034961844203d89031062086951006007400d0420112805403000c074020010b9000c215001464164040341800000303200300d100f40e8004000001503130804060202405e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 445369991 1250 445368741 445368751
    0x703032c1e060708072109020f0d0b07030c110114060a06021b060a0e120d09080a0b0103111f0c17160609150c0e090a0e1203072d020d0e18 61
    0x2140307070300750921958480c112009505400002043c986240c1c010080030214958127076100380b801410960000d0720300443c1c65032011050800040880c020f0070300340c0d009400320795211295441c14100703804d80340804400034010002902e54035843da86840c411b82c5d459421403940a40c0c01006003842c5407510b000e00042c480b942552400d003151540410210b04180e5030180105640d80000d0748042203607501c20300709002885841c00070400310300d8a403030b001c3c1c5400f810f00014250415400c060000381d2a010500d041c0b0510b0300c21078043d00ea400f602c00802d4410041c200b00c583c07802d29030b200607148144509942d01751700d28000c10100b0075070541d215401007040040448001e03080c0c00c104c5d01d402d032883c0b10300e051a1415481e03440c01c0750204010040c03a800018400070600c0e01d812420300c080c0d00001440214584020381440c1d80b41c4542505440003032131142c100c0303410340780075015050302c0f107d0f500c50168515181e02202e010070000e0b00d043e1802c070204880741d50444a00ba0184004c100c01c400c03000d400c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 445371241 1250 445369991 445369997
    0xc13090b1503152508060f060f160f0206190e030a020f0904031106010902091f0804080705030903060a0e0f150a0f0204050d03050406092106020703032c1e06070807 72
    0x40481d0350ba204c842007204d40c45001c0f0740c02c2010000c56051004a51410a84c200c45040c90580c0c0954004070074001c0452440040500118000c1045004aa020810303600100700c00e0300e90350b010340e0f050030385030080c10200005041c0006411150900040b1107501035402000c42c68414000e106004240500420075800c00c030b2941505030100c4001c0c400302d400f800c10220050b9807203050405010110030340138030800400e01c000b4007108000b603105036250b40283d0f0284000d5a00d098030b0905520b1b5005010350280e140c041e00e018400500d565034030040010345408241ca802901240c2c5031910354620341181004989071400084410210758015035806407030b41d00050070542c80d94081940c1c42c42012084010039000a01808150f0b00a0300580c010900d001e600070340d401c04c900300c0d190417010b0054010803168000c10003108140c003a4100030348900d45000b50303070480c040d1100072000352640b82e0603e0116000f00410303581c0c2c08024108003e40c0300254001403400d81c903045002c6980c280d00401900c20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 445372491 1250 445371241 445371271
    0xe091504051f0b12070f0608040f08030a0203011403010b0307050411041e06080928060f05041a15010e06090a030c03060204090f020301060e120c13090b150315 70
    0x441402c9900c000d02d0074000c50710004100e00104240540000b807512034000c1e82c1e01c516420014401c2021542c0291445da28104040340c403a440d000000c1c003802070006002ca440401041520905607002e9412190744440803802103100c0c4041c07608a845103d25030b41c15070404c4030b00b03000500703103500001005507004560b80d01e060382c1d400421310401c4410780918404900c00b00f080229550007000203811142140281c0340740c11001c0e802c0150f44045a120440a2412600c1c0106104d440c0d84140440c0c442c4000600883c074040c030f0801a072081020701600f5950300c0c200410480d44400c403a0a40380a0185c544010910700314040005a400c11140a680700418880220008171080728800041d031158102580302c03400e00d0541d100b520352401c080c0e510180b040c001006440e50001818901c0442925541c42d118907100d0300c4c41c1000702d2a500076811240d40100c0081102071a0711881c2c14a00421040480b42c0b40c040030003c8150100c506d899240c0c0c0b0201c004d0701c225242c460810303001034a00c1d100c455 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 445373741 1250 445372491 445372513
    0xb010908070b120a05060d0f02150a210e12030a150303050a170c07020405090f07060f0816171812040e090a080d0e03070510150e09150405 61
    0x100c0d041e00740e0000c2c021207801042a49039140003001490700680300510600540c40c000d000f26041d5840c80c00007811300d40002418905640b1081c08509282d0300241410f17075034560300c1002a242d44216204c07800e56007001551444800c03443c1c400c1c0480c84400101404400d0980b088042c550b0700060004076074186c2d1642442003034030080308460000e600c41c1d00c2d01a1950340d951030107040b50305140345011102d44100d04204171039041100b104d40140c0d041780e000407c2d84846072540d02c2c180181c000c46d222845042d1011070807e801451018440c0d9080c0c6da056000d80d1400b180010100741c50b159200880d288a04641039141071150003079011401010000e200d1070b000806078580783c1050f8445441c0200080d0600c16950600711140d40131410314010518290306a0386d19619109000c40140b1141c4e644004040900081c004c0302e00094000c001c07285032102e410000001480e14000b5508641540304002512000701e940711171107245000040e180b01e140000050001e82e130000d108543d5401a00d0340d0348 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 445374991 1250 445373741 445373743
    0x210f04050717072301170609010335041e080d031e020307081005032b0201140405070e090f0316030e06030901050703060602150103120504050312090a060c02060306040b010908 77
    0x4100c60f135003200c8483e61442d88000b4003440001d494188800701100c04014003516200180d5044903840120900e07000c842d810302007140800100095071021008500040e11490400a001501c03000d07541c24413008007000701041540100d1040c41d4503600810b046e15120b0f4040e0740084224890391540184100800032220b04990084030428007150014080c003001c0f41c00c3c00c1851001c0c0c178080d002090410105684d03450807c0141c0101c62120006030710145149100b03400030340290503017012508641c1864038145c0c0e103480301402030103440360380e07180000ca01070000940f01c0c1449034058091480d09010306103c1c1c14031003440130245c050083c1e0000c0c1c07400e0342e1140801188030309480c03400000c4508202c007004040d81c020f903102c0780455120300446040c3d5900600c550b81101d90000c0e5107408038044d86805e81d0240900d900040c0e250103100d0301700c1d1800300c8032001032003858412074600c031900340c5175042500c020880340c2d40690041414400542075080992094045942c141043d58281c0e607500141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 445376241 1250 445374991 445375019
    0x1120203010e0d09091d0a0611161505060d030507320a06150b0405040e0f0604030c030f080c030c0d0b130207050115050d0201051c02210f0405071707 66
    0x5040010b000c013030100310324034040c4a250040090206800400c100310041e05644554516014120a07514541232900d02c0c0024201c803503245040d0050b20103074403981012910001130040d00c0500c5414000040c4140c07400803000800c503545521414181078581c0c95001d88071158520083c06034510170020380c1281009040d2600c51036402004104010452414106644050340007038080c20503048140b00300741206050700c0c183e50301510001a917081d20440d0b05e1410300b41c008800389601900b02440189940121036144050007034484810f0944000f4088841140854000201440c10b0000c61010078850340200000c078401003010841d00255000941c1080030744681c6031030385074001000b40803c83d081c0150755410a00040d514040d43c80c20010940d000c0242100a0401400107122100d41c28120b25025130b03032507403000854951120700c401c20003c1c0b200080302c3c1d480c1d031910302c0015824642143c01c11710650b40075014000251510880c0f441c3ca812a903a24a0b20303000310400429200c04070a80303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 445377491 1250 445376241 445376263
    0x63105040b011508240a1806030210080105010f08090c3003070f0807030c2915030703120203220905102102150703020d141201120203010e 61
    0x70200340d49030110403100424840b5522007845003400421010f041c2c9101c3e03102ca218100740c20b00080a42e4107002a100140ba500082188100740d044688007010682c0301109480c425104c4005099914a040d03804034001d02c1914009106000740304202480741500617084240041280c000c0b080e00b200262040d4030803074040d071000e0300e41c5240141e000c000c5803124024284c40c1000c3c602c1d0550b03540740c16440c403404403000b8240c4500020071100b050702c01c0d0350501440d0b80014100d800130903640c20351106215160307044070f84004c09074040b039011b10543c0320380e0000d080018018000c80d451036440300d200036284018641907000600541c01c4002051130907051100c40d88050b10621b0f81411a601d00b1103401030304055284800500510803152656812144003080f581341d60320000c100d100144070002907041203901c1d900003040304803c0640025954800c80c00c6a107419044104d003004401c000e000300310910420038011001003004000c00c0400c561413500140003c0b0346011aa13454a14250070100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 445378741 1250 445377491 445377503
    0xf030d080609070c3504090905060f0c03130201140a050306040c02030f040911071703160518010e040209040204151202130504020a0e0307060c03140306310504 70
    0x410810700e440d01080007540702c002401c14840046181e16089200c03456202c075100200c107481600e01c05045644600080030002c0d040859070356485130603a1010301100a401ca4583c4103560210b65000a00800d00f8424108a0012401c42c0c0d62030b120180031062460040c2c0c14811184060b900c2050b261000341065002915940d0396130611006010071901d4a0380d4038000c642003030000003d1040107904503011600510000701c0e0002c100210307592207108802c002440351006000d00b49a48070342c88055032003182206070911600e100c1203420749440c070601d00c40d088940c80c2c00784c1e2070038158010440810129801f5000604249100d00420201e0380250003103192800e0580340b501c90294003404400e915080c0c200194100505005600d9000c0071701d00071548502e4000c640396080c14810483d4000c3c5d0b1100030211102030355a150041c000740204d03030040e8001207602c0d15100f00100740c1801c0324060180a0000002d8006081c200d5030100556003865a04a0800180031a0680c039401014001da000308 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 445379991 1250 445378741 445378757
    0x303060d11010e030631030503160e030d08090c330d09060b030f030c33042a08030717130605030609061918020f0c060603011503150207020f030d 64
    0x1040300d48402c100c40c00c40b401e0001061b10010000b54040d050300d401c10740003500c001b04000760200035a00302e03c001c0403041e050f00c5070281050215921100f0140101c0c85401a00e100c4061a0b0500c0a0034020104602d010075000d80f000c2d0000b080d1041c9001044d400b40e19040c00d000d5410300d1a81030b030307038504c501381c903603c1e01c841d84112107146c14008002c40d950341900840c544500610075030303101c031101612400074480c403240f020f0b050701810300311b01000c00d4181085102c40c5011726103444090355129007911020718607010020026109003559050300c001800550a0020359954821103510f00b50040f46002c40c140205410f4507170684921015000d40d132291a00c03854420148410b001d00100b09038070400a882c0c0000d810361241c1d0604098407660071810040300008003620000c1d2158021507002d8540c00a9001560000800c500340600e508a000b40700b000c21036801ca0a210049020240041f0007142080340000302c50f0b401000050310140a2100205840000030300f044010403488010070742c44 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 445381241 1250 445379991 445380031
    0x20705060d110417062d071202031905070207032307030f0501060510031b031109100206010521030a050310030b010e0a11031b0d0b0d1a07020303060d11010e0306 71
    0x17807000551104504440540c440400c014446001140c0c80b203074100517440c01c001c605400d10031a061016401c024105645c6ca00380b240182c25824500c03454048403619000105006a10116070724003102e400c02440e00e481c207440245050500c5c6c0748020010540700e003000001c00502a45c0c110900c1d903026500000e9841c0c50320050210640c01c005180301018034025410850382c01c00d0307860422840070ba2030005035000c04040b0485a5100366002d01d54000501340f905205254001980e81c1a28820754034160928000540d507000d10318404203102c1e05070024441d02940c0c41c070803c09103905c003004c240107080307156480d142c440d500340d02038000300303908a6400100b2240e05100d005122010a607101d5a5185180c4800f01480a01030044001c80043d0002a92001885150844a4600001030510a03031014519040b4200c02d0300c240100034902c803c0d00083e07280350012094034414a0040c00402406514ad0f490300b80515100c10503505004020a0305049500c041106130300c01d001d0f0f100c42101d40d0b245 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 445382491 1250 445381241 445381243
    0x15071e02180f15010903110a09110a03200a0c11060403080309011808180103150f05010f050a2f07080c010207050303090d030c150f15050102010c020705060d110417 72
    0x1000704580e50203c0c4403c10100e07940da21104210803a038100012484402035140003c0906100ba03000e014407900745041154800403080080600080c01c1d18200140030450314202001e01d948030000f40c050341c0a001192005000780400c12200d84100c0d40c6522001c6900001040342d042504252044800442044104ca509104240f140b806a10141c0652400d9135903020740d0744102e17680604240006010000142d0283c2c0003000d202c0d290800440b40301d80c40f18080b544408561041d07034002042c03d14070701c0c5218000c20032120040003641d580d822171401158034400e03040088141084407100e480c402c0070030b640148540800307818604041d1003403220f50800240341c030724160005440383d002081032007119520040c4828159906040460308182941481e0310244c402d005044500d509010724442800c50b01c0d4480b800e6144103111690240d5100d00c01282202c0e0103184013000369110034401d1280d8500314010341070744c010640000c0f85445594441c0e2000c0d400c180c0c4203c803601000b4403c0b400c0420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 445383741 1250 445382491 445382521
    0x30d110a0e0d120e01030b04020c0309010e1503040f1415060307090e07170304033804030507020f0f0d0803100801020909011512051f0515071e0218 65
    0x7400321103040d81200d040e152021820100c6070001d06004500449012990190704101c4000e100104115200c000b0012540d03203d034010300c000e03400507800203082c00352444c1400c40100782011149585080daa108d0b40c40d0303a1401300c0080280d0307500d400d15541f04240d140402000001440c2c000610302e081c02d10328241480c1507281d8228072200f9040c040d0000505c80001100821120340c2070b25030a2801022401d181580f080c3d40000e80a41045401c040782110280036104000500315003505d20701d240f8101004180e003080e9401000500c0401120b0050714101340107050f816001440d030f0317a1a889480001c0c1054840c20400c482540003c401c1203a1402c2501d1414001c0043c2e038001d514100001d400100d0101050048c0300449803040401c2d103080d4400c2e9580f0700c40074409001000681054440400c0310382001720000000d6100150101c0c26003801b0310504080c1920716030b8141000c107140e031101491010340d00496070251a0300800c202598855254080954a0400419007410b240718180e04140d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 445384991 1250 445383741 445383767
    0x70b070206090a0303180b0709060e0105090a270f0b03010b04050906060603090115060c110117130f0203191a060d061109040501170c0915040905030d110a 68
    0x5001407007000981540442d686103102d5042c0b50000d540d0400c8421175030344012100b000b0b414a4841c1c810410341c103801030100403ea9241713407584c079116246100112801c1c41040a110b400030f0807030408020340c0c018410184c407180c032041413007070601c043e5607440d800f00d61941180124441d100d003501e00351420300307100b124000c0000351424041880c006004a0380c40c50041c103054043d01380040000c03a5072001390310036041000040302d052065a59010004d003400340c40343d0184c40701150103440b69400e6001b40d40349014103590103040000ca96807004081e21480c107610b015501509007203021001694144420301013008280c02c2200001024101004100320000801d11807804c7d150911506a40e10130083c003889030f00000200b02815501881d501c1030082410468001713041000124007190200148004259014100c0e884248210300300b0600e41000d480b0f00e0401d400c060200780e01824103412040d5a68043d0b81181c0c540300e0300e44600c4003102d0004c030041f940220085500e100165024030000724817 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 445386241 1250 445384991 445384993
    0x10f0c1b020a0b090d0f0318060507030e040509031605032505190c260f0c010e06070602310f0803031807050a03050714030d170c0915070b0702 63
    0x840e60365404620614164010101e11002c04280030f19155544518001460b40c031000d005801c030520314000d041d16000b014910038446040303c011074054450070580358400e8250751035981d042c0b20b42040c0b20041401030032405280c04200b102846e0300003507502281000b40302d0700c01160358100c0c80d02c0c440004980d02080d102c22a44820821001c40d9000800c420b0007400981e07140d1103180e1914041c82d001e22240d00490800f11080030079104507801d01002d1035407000c001c09485400c01c903c0001c58682e03120101c140c0c08071741207000d240745c64180b0501030800c15210340710041c034041ca80300c9003c1305041d1841e07038210308140101c10011110020b24881e0014141c4002c82445070342002140c507205d00005000b0085030403d5124250041d20411000c0001d04028043c99400c0c1d840703040060311030b000c80c001c3c0c03548010394000680d424100003528801241155882b9100802c0524480380042f1014001e00f07900102801808841d07034425030180805190010810b80c5c80c00c043c40d1401c0000402000f5200f9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 445387491 1250 445386241 445386287
    0xd060e01051e030d1d1503040302060c092407050f03131d0c0d0912050c160f03080f04091a040c1713050709050f0106020613020a030320010f0c 63
    0x3c0d00d0004101e90703010003e042518681e01e2200d40b1201400c48a010380d644110041040c5051b4032101000318041c40c0280c0c2a600e0544c2c44601800192041076902038200300f0040d02c50a17040c03020b9411402c131001c000c00491134005143c440790b14020011046401681000079a1680e00d84040b0900008055101028125030340d007040791000d400c0c3c01030a4900040c000503200c83e28140c01e5104240c515402042030120440215009100b40c10044010000d88107180309805030b50600c0c501d0000b07e41b5003506101c15a42980d84041c4030303420503007a44d09091001d11010030090111f0160420950200b081c4405828810b02084151441088140c00780f00c030b83c41c41281b400c24014404e0b0b0303008031034180840080c2124a0501c0c0b0300001075212132010b600c2d050901144480d8020070604a49150303085902a48400303030191250303403402c3d500a5000c000f07400c04100180c010b1065407207520300c82c11070103003249044880e1425100c90a410420055447c100c2c02e403442d03006400002c800b6241c0d030009034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 445388741 1250 445387491 445387549
    0x114090708011d2701150504050c091915020307060c110d0e0f041505030606031b040b010905102106081513080409060e0105060c0d03110d060e0105 65
    0x500c011003062038820840c4050000b02c01c0220840d9454400d913002118440d2503205201d0381d4020405005c0e40313180046035403000101c0303141034054940185142d04001e4030380903034042081a44642214000c190403402040003400c12003c1e0301c0081620313900d401940d070300c6066140000031a0a42805c403800c7c459000018800707c50700003540740c80524141030030f01000110000140040c002e240016510a090101c02c81c00e00075801b4809d01101d07170560480307645840d600100b50b1180780f4880d039030301012146541c000c150b04c0c1580207600105018100891090b845070081450b0720944a010404900500440702c074132420500003c1d0082c0000c4810420f4a00b480f41e0a40c480b122035904081c0180b0341d201180022804400f071090460340b20401d00c0d5155030f10080500500014403440c00307001784d4036000140b542040d40498540c403441c04c0282c03901c00c0352650294000c0100101903210312a003030003030070043d140387d00c0b03948040c1c0729608040f01150300d400308000680c500c01242400c2810b1421004e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 445389991 1250 445388741 445388759
    0x10f06030b1503100e011d010b2412070201021314060a1101020d0603031808030702010504120f050d02010207142b050c030d05190504020303030109021e03011409070801 74
    0x16041a01440b2500300700d144040080e26040d825901a1012441e0401152180b0015840309170840d12240c5500d410410070360403a4201c8400d4034101d03070040060300e140481007103605002c0940709480da52184c18048543c15404e0311440448010016079400a1100c04070391503200d02c080105400c4205003020750804002c40c840d4041c4220380c00a2101c0070205020580d400c1d01a100b4410048604000c0b507a640d0400408640c10f10302040481c405400000c1603103031000c0101d074002a0183c42d19841c01c2d10307185906c02000b03408002914001440c54411001600a000000380034000b54005071f1242c00c40d080c8190740b50350380607a0f80d81c0382d8444165800c81100c803088600d039484c641200d01c0070402001c0000e071352a11170341d02815101d000002e230040000070035511080c014800d03104030300070740c52409420000310b410a84019525910510040009000e290002d090f2239002d000d640410001d456207519050f0030a0b0008a20451111070360541400e0803181590700800a2614a0840d45480d21403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 445391241 1250 445389991 445390013
    0x8040f0b2d04030e0607050703050a0305031006080108030405060a031b0e3606270a050105030c011e090b040909050114071b021f02070501020606030a150207020d021c0203010f0603 79
    0x40c5c0503100c041791031018010148403400041d0382141c15540706000615005080745e008a40042d807072400e024001c1849407040c10241d0507608128021441d01d4102001c00c2840d8104444220401d601d5002d4410f00c040382014900301c1c0c28071610b901c1d0328103100f00100007502070041c200c0035564003041f11001c120024006004032104d4484032641c050f8a519000c20803032400c0554034014050342e8500c40f511034221281141c031942611a040150380d80700e108250f01d8100c502441030024420000305044050b2541407107501509906003070b014199145443c200681150340306c0c0898658800c00071041c000c00380181c68000e140784c50489402e01e0401e00c00361049004400280141000640900c110f403111410740b43c1c40300c0c1c505c003c42144115400300a40ea03003540e0040714010f000e000089482c42c18001514401c3c0399124202c10031100304200031200075040034009a0340060112000b03c05a01d6407a40f112290900e801c10003c2c4142c00d0040c0b50a480c1d502038070000e075074604541040491084130034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 445392491 1250 445391241 445391267
    0x15030606030406021605030c010510060f1202090a140f010507020109090e07170d1d210304151205070528020a0b131109090d08040f0b2d0403 62
    0x54036460352140c2c10400001e01a180c09030301c0445a4462510078000000068080650701c04024003040e40c604030081035520f014421500422180240182182d028041450400300315100060a00d460f040014622440d00c2c0e024402c50030041d521400035041180e08554610400c3c2007141c1740115540c0024600c0802d0301c20328a020f41d4843d111004c88000340502c10091180702014011502c80680151b19403020301d10301d10109001c4190441c220000a9504801c551300030710f0081d41d1030360b008000780c0100a040020b44140020400407450761030719201412281601c1e618401d07000610729200c41295000b9101000303001062084030075a0406a8000c0c00151484003070307020855002409918100011400030228070844082180d034083c09100c2d19100b5001d2460340360400d5075901840100c1c402650304444503000301101e1800d0900420013960803900c01d8141580d44200e54444480b207403070035241c00d000c85800d8210f5a003c00150402c1d01d00c816505c101006071401d00d5500034180740c050044e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 445393741 1250 445392491 445392499
    0x20a020a0f05042f0c19060e1603030509040b0d0503070f0c14060f160204050c0d11090906040e0f01050f070909020c1c14070f03181a091314090c150306 67
    0x601e4042d041050000301b40b442140350ba0300380b0a0a5501c0c0c658090004000e40300c080b8403c5000b4540400720031103001d012613400da2a07051502034240180409454281c010b550800c203c0c40448000907070420040c400940121111009401149808078080b8500e90281c0c1a8010807480b160683d5030b0300003250b0b10800c840044950b0b6282c01092032030700d078a075140e020303500ca45000d007084129120390008000004031880708110f001600050005d85014603401250081e061b180004d043d03042a620047c0c18031608400c4032000c454688041e429141c0403250700d80584035840074840000d4104940c0c2020700391034541941040ba8840b4130030f590ba1603000300c13407007901c00b00d141340075145024a0b0b9142982c101c040d2402c0e034584190804089241000104400040b44c02d4404030011409400d03250036502403080218200c034808000d400c16410107011580d100c80d4500b10800c0d40e003014458107141d8805940000b00501d0034020030b500340b03c0d641509600407140c1220b003140a41d500da04807940020111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 445394991 1250 445393741 445393747
    0x204051e13060b120c010e04090b0f0601020106081207030e12030a08060f0303040603240e0a020c100203040302010e060105031609020318070f170312040201030903020a020a0f05042f 80
    0x8100302018000080e04582c004c0b001c000b40c0c482c98080401e903002285030031380b20601105241e2092008580304000041e081700d1514004c02c40781c0003070040e0305070040310510020545607203402d101420001480c0700c600210100148220401da005241d03e848100119100c0c4154946c0600544c5ca9104250100e02002464800201d155075008030840d481140a0100d949440d101c0390041d000b40400a044460800c40c0011900900040040d400c16100d50440680c80c0d03403501c0b01d06001a40120ba52030348a4003440d1902c21103140c403440518407072400380d4008637420f900c05c1c004c0b505118060300600c0c00380c2c0042441c4c0155640c0481c41c4003c40b00c4130300c40143d99648000c5410b0480011412050705070040100025607182508400002d484160307103002c400c0500d00715a04d982c0d100b149111030000407880300260166001e43c4c85144080d0013030041d01c150350507035400038100384000d4010390b10080202c1002e0090b4106441104070020b816003690803400c007084060071800d180c68011684505c800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 445396241 1250 445394991 445394993
    0x7092901030908040f09110a050f030705070f120e09092802060f120c1611010e090901050a110301080601140109080105150f01051e0309120301030f0204051e13 70
    0xb54440c014803504103c1d00b544440d203d85c08214a4007007841a080803e060501d00344900c1006c804480500403a03854040c07403d0711040e014407254000034101c0c07040c00028040c99002c2101514091501840341d0208400040f0300d01020300155800c07041207011308485000c00c00d52820019402002c24000c0010315222000142c1150005502580c000e40164000ca2a046041c404002404014410a403060501c0d81c5800e20045c045c003c0315103000c0403031304814102c400300c0c10301c3c4045c41d00b0b4101894080701c0c46140d040030503040801503c0d5007049a41d1407003041a0a404c0f4131940542007414040d01e4619450620010380d40e80060080002c85ca090209645890b030107054844014082c0d440280500d11740719440e0450010004a01400b0b8441c45201c0056907200714110b4506d8400030002d0a94000c417192041c105810042c01c50401e48185040700c1d660360041000b4500840c4110041d20209200d80306010a440e00603105201c04440224031002003d00c415040d980261091030110181080f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 445397491 1250 445396241 445396247
    0xd08041407091107120f050a03020d06030204020c0705040f09020607060c1704030f0905040501150804050f03040801091104090b0c0f070b070206090d02060603030f130906120507092901 81
    0x100740c0c000b0703610702d161010011480c80b444001c0c0071124041e0f0f900c140c1c2d800145034142c450219030440100098010006e50840e01d0190b030181c44d8245030700c1c83c002000d644982c0458103c1c0c2c0075121500165110a004200628040c0038140024650403000c0c4404071843d4003044050040d500d0092609072102845154036105503c00108880154403a200c181010b04000d040d45020003080e03000180c01204c081032a06280c0200c074101c5140d1080d003d140324500c0400c4a0094014004031000c1c0100741056181c080204003800103880204000940c180700741c500320a038003018620701e41c041c034104403031a4045540c0341021603100842e0507065550700c42c84014020144070741c900003043d00050b070702407241d029400502103224048080894200c44584602641e980100715a4030b9815842088414004c294010140c0343c40300e03c0805540c103071901d07445030909a80705500407000313401113082e80405101c01082903100600d00c0802c00c000800c05032050450b4800c40459419402d103c0c0d070800179550748 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 445398741 1250 445397491 445397503
    0xb0c011e0e0c271e1f150e030d0e0102060a090804120c08010501121101022107061407030905071707090504020303120a020c160f0e04080c0d030c0807020d080414 71
    0xb8099000f00c1034504107012106110011003820700c07001490b400628400c2c010642d441c000340b560304201e040d4915181c24500c0d64442d012055081222210000140340c03005c100300300c80040d158a400ea11120300000085c6804c200403e610300b0309041c1307446071011890030340c02c460580301c004020490400c018203158180c0e900c190b104003050340ca010700015100414008015074544500c0b40040a4000300004a1b6603910a5071030350280c3c0b80c189660440600180000d12615120321030101d000c4c035200142c082c80280450389540406d0302d034282d040c01c02605000550103000780003a008550300b4140c565942c0d948550041126159503030740810295603007002643c81d0100b4650910855290007280c4102075080380210380090322036858100c20141104034032600703444031000c4612480d45450000c040c040800350003a10021401c00410f0f5408509100301d441c07040054078049070510340220014554a0001d00b0311045403c400108910281d2144a294000ea000601c2080c145820392289007000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 445399991 1250 445398741 445398799
    0x8120403080406050c0a240f0e07090b040b19060f0918050a0b06031006030e010c0c06050406091a06090a050903070204110415180806040201080a090501060b0c011e0e0c 74
    0x1401e40b4138600c94a18006114481c01c41e12100e040c8a0100d9403602c0c8c1007039030b65170010101103800666082c0550541588800f008002c001d1000c1442d40b042e4002c90038050040a4040d0b40e44100c09007400500e801c003680790740d440c8248c0307003a00c070b000e203000c6010801428070306015080300e4a800204050351502c4d0001d17034500200600c2d05a503401d25440e0365a42c84035520a88001c2401c14044040211042c403c007001c00e16691902800400305965900062800810441d80b17260745200800c0070400709034070441c0d8a90250100c00c89400d2103c208108103a004004c64a150f083c03104101061001000359a02c05038181c8010a480034a43c402000c40e0145070060041800c0c00c1803040c4090390701000020100039411510500c07651100c050f25110602202e01a000c1040c00011804400c003590004400c540100300025030261101719001c641e50202c0000c03585691103a40714070001c10b40007215000c0015074001000071400b04141c3c0707a110086009558802c660107254450105040084011b0013 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 445401241 1250 445399991 445400003
    0x51212130c0315020a120c02070e0c1e0a030e010603020a030206070c15020102130503010e070b0d09061109190305060a2307091a040609030b040f060e030408120403080406050c0a 78
    0x1034003c04003100007500024030800000d103072607440032004600751160308511a01540a80615805c002c6180422140070300030340b5514104000c1d04440c0701d04d103141002440d000030390050323072054403400080039a4031208180c40c0c10b074502502080141d80d0800e0b01e1040380e0303042d10196100d001c0b07811700000d10a910380c030280c2e03140500303c04020026810760040c80d0306d49540001d45100b544420034107089440d808003c0c03000f5445400180011400c050213050094214480402e01d070800307564030015546040400b90002c08082003991146c0340019580c809400440c4440c40c03030900c1c54071100e507900700140c803204900d0707900d603000c4644030350381d92101c0c00104a104440026040280c0000c118503524499111011030000485501000e80021142100c1540c3e4a81d50f400b81142c4aa200846011f0300440b1400c1803c502500041d0702d40c01042045942c180140d030705c0c1c41c076010000f800c1154841c51440340200c100414000100400241c406907141460301e03039110900c14002900e4418130340c030040d0407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 445402491 1250 445401241 445401263
    0x328020910060909021c020c1603080a0e0907020601060e04021b06072726011a120109080f03041a040b1609060c1202031c050103051212130c03 63
    0x80c03600e0050380e0021201035940301c0b0035403540ca00e0307002c4c12400741c1e40d0200301405180d14211041440c1c0c1c5c0191211114807401d0351040d01c0707078490980c40902c850340112500038002c9003080394140c10410400b800042a140040b00d49050003000f510b58105002d131009010301c4080da801c45880d43c1d41620b0b0015461245030704a0048000c0701560361804848441c000703021030380e60040c5a0325a0710188200000c11000c050060706081c6114091164403402d0b1404650310800c4401c048400d000e07203102c1441140b8607020b1540e500003400410a0603811002d4207a05015490b800182c03070b40101c0d10348140c80c100391030320382c2c40d1454240b1509029905034004842140d0900090100c1103024078051103d0340403407034582e12a9542a5814046480f494022034070640e480d502141c1a4070000e00c2100d02d1340305882c5800c618581120403c0d10f200700f202c4019650b10010f004004040107044140103640d0019418403001a41c1c5480f2010300030200c0d1900c40e89030207250200000048401d01030b550206141c55 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 445403741 1250 445402491 445402501
    0x12090801060906090507020f1203060316230108130b04020a0305030a050a02010c03050103020108010603021b0d050405010e0303120613020408031c0c11070611070305070605030118050603280209 85
    0x901030314002c4c000701929040c04503010b103000013400810002c1b42c002500c00740c0d000015110307264000070003254240c0500c80c903508003651628000c0015002251180300c0c0364a8000201c00141039540e80c850601c023004041c461180040340340b4040c119404070200607141d48510200c1c0861030f003944020440c0c4404034403002c100f5081005800d0965040e1700800c151600f200b01201500c03400e100c064089844c0380c0041c891070307100340c000305400d2400c0c4c0000b1009445840c0d1117452b2211100e04c95000034400700301031006d5030348800d01d070308401300860082d4107101c03038004c002500e004d02824062141c0500d080c2000b4a0f600c68041c1c50040509800790b944403107080008040a107064003910342c40340d1509242d00b940600440350f41e10101201d400401c44542054400e41310040d880d8001c032601d1242e218000001403040000102421084c7c4c1d4141e160352600035043e051862041000d4240c500340410030900341c41c000ba0710403028203510450103043c505100010710940c03190b0000794215600300e04000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 445404991 1250 445403741 445403759
    0x121d03030403022b0903030c1e0803060102070801050f0604090f0c0603141e060415030822050d03020c0907030207140a0209130f1b0b040e0609061c1209080106 70
    0x180c03001d0a40d18100c1c484ca598164030031500c00b400b2580458a05141030002c2481a4064410311f803140550580000c021103501281d2051403004998510001040007490350381848810010560b0303030300a0040e4284a8500b012861000b042c1901884d51000c201d000e0ec010070003049505500400408280e80d20740500030301a00c0b0038044c42c0c01517030a213000301c0c1c06043d2403031002c9400303032814040c1c0c4035039140c1b0740420025010307042c1855461440424080b0104055200400e42c40348609403c240c00442d21300400d00e2001c4507442148581d402406180110f50007103a00281180b0840701d02442d55210700e020b4009021f0300300042e040406580c012000741c04001780521515000700e50106440d27444c401c03450040565018000d040e8014080d001000480508608041100c048401c8183c580c0300c0240c0c0c3c00d04e4025070b1140b40404c201c8000c1c0321840c1407401259801c041c0a50700c86c4400c41d8880300084420701c21480042209840304403050005208070049400717040b0f0b0344000d121a6030b4482e004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 445406241 1250 445404991 445405003
    0x18061508040c050108070804020904150c020109050106080c09040b040320100506041e0510050d150615080106110c04060f05030601090627020f030a1a0a0303121d0303040302 76
    0x102c950801852011419601824255202d1100c2c1c0d503440e049592164280300301032002502c101c0c0c0c80c00c20b8500e81101440f2900036684640792a900005480d10b0a0034494290b40090307001030b2158000b8102c1041c42e449010070781d644143c0004400c0115261352404a442c0720181030340300622440d1182245018101082c00c07645014541000c2c425515400c0400044030b00b400140710294089010001c0c2020f06504140d41c054001070300907486a80d0380000c1000044140070840c2c5860038114104c0254a60f889508043c0400c608820300c541c0030f0503000340030540107020741c1060042c40d4000b5150300d1001c0200046055014005001003a5030301510071401680f40925880380c00303490700104401c030041c8202011202400001c04107220400c040c510301d131041c5690181070756000c1240056640d0820011402142c41e108001600c4a00b60310841034207042d1496144901ca4540c1c4c20008290701150484c49107200c50340001e247c909107114801c494400035118210740c0004002c100c2816008558 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 445407491 1250 445406241 445406243
    0x312010303270501050405010e01030f090b060a060504031a2205030a09210b0c041703030a064109010308030105040c09080a0803060109120606031e0506011806150804 73
    0x52403444400d4880c860090402d4081d450024000740f104002540c4100313021140420107050000d105a40c1030140815107040e17140699840902c0c1d424020f035030510100301c0c03001300124a0600e0400e4110b59070702d0002c1c4607074840c4c0800f41151102050075070100a94950648401c1041540f8141652800c0c40d00c81e0405001700d008138400403000a40540f41c0128800382e501d160400714540299640d07480c1940001510b0082c64030018030010039000603400040720025603000c02103840c0c0c03a0060155042e11050f03007116118841d03d204442c2400b08000844a1a81c030180382c443d400f4104600208500c2c500c0f00d0103552100c540000003003405000380043d81a6a419901030085500d0b100c0300765400c2c06503220b1104070b0b5010008110208995401031038101c03005240c40305116035038003007024040f981c03040207030b403926510b2000b00200030760700c0c3c2a40c407691540d0310074a0140c183c0b0b48983d03880e01d8052144008104280c51105080c1a00740d0042029200c15002c1c10700015074511b00508135901250 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 445408741 1250 445407491 445407527
    0x30a140d0b220c020c0a0b0703020f0f010204051c030c0b0403050d0908090306060114180307090921140a110a06060e010611010623030109120201090b06120c120312010303 75
    0x2000080d0f034404100240c01c4007018101c1e0844501c6c0c000002030541c4002826800c5015040e10030541e00c40510108030340700c070a00005616103050030700b0016030b100825200062603100c0b0340904c000942000e010031032a60401804039160307445080580d42482030441c4102114a071202100401a4001c00b404d101d0405800301c030b025980390001903900138002c60b1034040d00070060207011000003184621000c1c071500642507800c0550394810b1b050070746844410881c0c082ca120f558003014100002c681010780350061900c04041600e400005140e40300300082c030b80800c500c004aa5030210340402100103041c0d0300007020015990f131448108801c030801c0c02902c00140c2070082c0ba007124001400f81c3c00958041e20010034168020320140010400150ba003ea015500d0308140300102c0c8072041c0c0c05958140f20f0f0004907a00e0150b00d00700e00c0c1d044006000310700c00d95132800c20811180c000165142c0315117054614000102540d058280755000d8400050460311000c1c002004256000c1135101075031107040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 445409991 1250 445408741 445408751
    0x803031f0905010e160c080d1e0b0a060e0a120605040302152403150106030c020d090812131205150a02072402070602030a0209010f02030a140d0b22 65
    0x340c0301e6090b01c5083c41006410030025011480280d0072402c4a2965000c0d0304004607000c2e61503650020541080d00011421030f031320706072845414400c0581010040401d4800c016100d0328400082e02407000f40540350400400c83e60140c42ca032242107094000d070141c0740c19503c2452440c42c0803400383c0b0b400c80e070880060151440e0328641052200c0c0301801482c1049003c44070040c000b260442c0c5014208200d949445048c400040c5c41703015240e0036010303090555002c28400d8103400c009c0c0c9004d10700700c00903007000002601000b40041c081010349581d0404500349544403a588034039903001200f03401c003c43c1914503081941c10068002a418034401c1d40303d0003c19142d0301d1300854812809001000f414220080c0d801450001000442d9214010700040060415403036849040880c0c00444000c44903a6000481c42040e607000490100c1010742132000390303d4090745001c018485103071140000b000300e501207150034080c03010340c0040e105a80040c1c1429402042580c064900b21900410380311044d1900e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 445411241 1250 445409991 445409999
    0x609010e15010e0609062b0507050d0b0115020705060d0b1903021c1e060b0a0f30061b030b040e030f0d060e01061e051608070c0803031f 60
    0x105034002e04071220150849900d07503502045c0300c0003000040001c3e6000049182145505404074000c09002181c0c03031b01c0c180c1c00682490302c0c1d4a080d81603000144100c200d50003810001d82c009102c541950600345c2940039566018500313900e001281d4000741c0d0f1000340031130041405000d541c03061003801c600f00d941005481c0c0c44040000b20f94014007000c0d410070b80c11003404c0350501c940005281d09030300ca11502080100103492106071140d08840442e241616403035460071600d084c01941000e80303400036908100318945416014000f02081454040e030320700c5001018100c0b01320700642034540c1c005600380b0203007501c080d0820003581508042c00200345880805a400d04241c4a403252000220000754a849c0319842285c806130001d082c0c201002d0307124103022480c100400c114070300920701a02c0d440c1441e1500d0404503840800c042d6a00c0c20014203100b1a6010765482d07140e4041d0356084240a80c1d62141418810381200541d08a00c0c0305101c0002070240c07070310116210000c0034031415914003210b626 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 445412491 1250 445411241 445411273
    0x6040501030f060b030c1917031602150d0903030204230f0415080a21020307030801050904030519020f12030402130b0607061e0b010219060e0f0609010e 67
    0x1e000c05010104030b4005100012425030140030206001000c48004180920003e200501c1004120040040c3e01900b0400440c07001c50301e22410380301c0f4000d54180b01c403105405086242c01400640300301c100e088020800805401111814803100c1014400d600c503e08014002c3d6102d445690720118504541120405a40010560701440108003510f8444010100406401c150080c407003c11811800002c0b17082c01044003000c454400d650700d240d0b81d00000d040202c00c0754000083e0b01550000c0020000003036001c2c10031815900e084411103183c0d16142001c40e0321380203e44000c41c03520b22869000d981c1540005180e80c408000408850f007660003011055801d000644000790004010a443c00080ca5581c20800328540064062410544544c46450a440c54801d009108110b51480608440c03030500400c0e100038000e0000700080c181120310034450b0048402c001c3d0000395554103404211b5801d1100b640310f1800300013111294213000c4085402880c404a01c7c015a100300b164102c80841 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 445413741 1250 445412491 445412501
    0x90106050910120209041a0906061602040f0209091003420b0d0303021e031510050d0e150901060b07080a020a1a040b010503060903070305090f03030a080f0604 70
    0x1030152030400c051a02d001c0a68401084880048885400340840040303610303284650310f0091005113034102d403a03500c4002c0c402c3c0140003408850044001b00402e944460707082c0728a14000b41d0685000036400d01c0d0442e118000e000340031080c3da204076501c092100455100310000180c9004400070442401d1300046c14410a050654900e00b4100c5141c04a0195110700420554408008000325500500e280000d6012420140032008640d0101d0341029100391917094030280c0c1c290403101485c47c2061015086029152084107208901002080040d28414002d54240041d02c0e202409445200500140c0742d01c4481e102010340340c402030014001050500400d0100c400025180c1d10717050b050745a282d00da51000362141d0075842501e0303801000402c152100045c0c24503621300c000180c1041d14095000d0301069020620030b5016505000300e0f00404000c6840e244e80c90309056996001c5400821000040f08000c2c6c0d5041c000410001c0110b500032004900c5604801061900c03a502c210411040714 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 445414991 1250 445413741 445413757
    0x23030702090105030d230c07080304141804020409060609050a0605041a01091a040f061214040203071716080a0c120305070b1f03050d031505060909040f0512040509010605 75
    0x1655480a03026007921403400081580d21b903442d05140005000b07840d880e20285074005c00e0703542d00004040294821400403e07030040411500701c0300c0c1113902c018005400030054806886550b881041d0320405c401030740908001c0101c9141400305103480c0700c200c00201454881c0c03900650a0190640c00c0074006510643c0310001612803100e01c40c103100c5502203036000c956169100303e2040001281d035418544040000305869510502d00f084600000e44c04c0d40d04040008080c140c0000c24000180d402150200a42e1401030180188000e0f440c20a0719010500100e21444480054045100c072400b240c1c0400840c000c010309180c45560318494035800e602c1500180000301d007440f140000803460005103810a000d641c01c01c10388402c0d10301610b9441c4056108a540e070740020b95001c2940c0e007500481c00e640d141040104809440d22000c20100d104004415100f07040345000142002a0007520148035030300401224100342e1b0b90344489141b54050302403548182050f600000d1600c2c40f4400b01c500c60303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 445416241 1250 445414991 445414997
    0x2006010815100e06010c05250509070e091009020d051b0a0207030221190b0c13090903140409020304150606050702010f111615030509030406050723030702090105030d 73
    0x640d26000c512803040802404e0f090421080c1d072159030110b04104007080c6074844422804d20090186120410898031603072046020742c5202d010000450b812030720380c0d00c5100c0103a50090341661094061248411117030001c403491b03807005c92881d62603440e5920442c82864400304900340340d0208090b00c0d5035030054500c0c0000590044e00184018100140540c2c0920341c0712080c2c015110010850340d04180482010b1511218114030f202d040c0188003071002d8100c00b5200035103242c03540c01715121103a00580d0040d0320310301e43c0b1925014105031180c1e915521017410b914100703440e26202d036403040195000342c5059903280d2503c91302218007581882000c0403503890717490300361801041e135005440e07060014a546050100000041c921210240240f91408851a40380310030320b400c00c80e05441046000d00e0b0718040525103810808001400030441c2d0681e42c440c24841e80318500352170920310382581e1049103c603441c01005034000703004000001d48426442126a1030943c0e803610240f503600c8407034030124800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 445417491 1250 445416241 445416271
    0x51005040603080c01110436020f0a020c0f0f0609190f03110603010e01050d151e0e0f0d12060515040509060102010908040909230a140712122006010815 67
    0x144040c107040c00d003070142c0c86003080c07400001c0710a030420498028ad03030700c0c0003c880c001030b2150f01c160f418007580f400d246003100c01c901007000c05000708140d01007000321180140c80010301380c81a9501c0c88001c200c40c181e000160703086a030b1160300380b0308031000f184002c458242c0040075001c103516188081d40e05880c181e0003017000d01d031718000c2000024850700c03009803511a02c510503064240b442d80602e040b81290800c04010048807050000226048a072205505070000d4680c0d141d00070700803603000d00c000110316004c0180c12000900e5402000706034000c030390068000d06102c0810200c078025008440e0110792402c01603540c90016802c2c0e030b4981a000700a00da0401c01400488a0750784088580c1c4e01441d0101c00221254081001c44c00c10406c21050079130090b00304c00c042100e010074035003201c2d5816000d450060f24004804000302c8403c5801032103490541d203502110341c420001c2c088220b4018040c07400b441500b21b44151120702c20700a0a9043c0034600c0f14900c000b10904a032800348a4440c800e400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 445418741 1250 445417491 445417529
    0x2307080604111c1a1206010608070203120108160e07080105120c090c0c06060607050c100c12030c0206070f2705090c0a02061e0a051005040603080c011104 68
    0x402042e01036008420614144560095101084200c00b0043d0a0000020700c52032009800707007100a80710001c901c1884c01604203032400d0400301300d03581181c1503818114402e445030031099065001d45106000800c8407280002504000040d10a5003c3c030000700c5030352070980320030b0902e04424040300c80001040c2144010032483c1024161032164080074425500030300e004c00c0006201040649208012106c0411000c0800300c0070300800c0d4001030100c6015142c480e16075106500c40703144080d10340c403882103511426440341c001c44904403140d41c00781400060190f0100003034024002c4100d054014440d42d00012038050142101701d41fa41c407243c0751041040703d0500b81c000a030603240d210005180c041003001507182c80ea103540f00d010300c0801000545503803c2c2c11000b0f280000080440d80d60f10103005114042d810000c09561300002600c401181540c0c0300011140ca6503c181d02c001d030003514050340003050144075005411000b441c03078001d010309041011020800e000d617000e403080308229210450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 445419991 1250 445418741 445418749
    0x21005030105010f230a0206310f0203150a0203040308150a0b031009060329010f030b06040e032706030601050f0a031107140105061e0409021f020123070806 69
    0x500402c051503080400c0100822050190019003131600586d1241e23052109905a00c400c507003145650080c1800b0000c02c0702c1540030710a000308030140108004a4209040d034409008084a002c2c1030001e017885810130003ca00c000b58030864041d00081c4126010541007200c440400b122a040285454459810b210258050b54005440c3c1114184150b40000d820907580c02a5001940039507500030403000384c04848025001200c4101c106020317000e00511001d800d030483d0601792070b04000240003598030074000c10001c2ca012119400c003488040f40380c5045401400c42100c0e200d101c1250404078483c140284121400161241030104900f449000900341504001d0710040e44c0d035240101d41461a4501504164040202903403500e41d00c10188241440900070b0b01c1e0402001d441c2e00304032141c090412422854039214091141e61502042e100795640d02d031a600042400c060000700b04080503101074001d01000e00302c0140600e0106403100501c0d4001c03500c910994198489800c030b565090204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 445421241 1250 445419991 445420007
    0x31106071409060706060305030703021510061103070209040b100602010b10260c0a03050603061003060b0112150905070c0809040b1f18052d06070b0c07021005030105010f 75
    0x80f070f0011801d20100700462030a006420046000344041c698540da0750130000d0500c0c141e010b80704a0008100107002000240c2004202112010301e030449035103c0340080f290462007001c5020754000030400a21050145145080e8020200c1510b11a00d4030396481d420307400c0c0c0d955014540c1d80a44521a42c0042a004101100140703074408002c2d002003607110781080c1001800e17514103403c01340105402c403141d40c01d84200d50300400c00300e00900f00d03031034544d401007100d000c14040100101d403a0303160005281d010750040c8840b19600c58083c48080382c2006c8507c0078107468840c2c0301d00e031400e00002c41c885600494000501c0c0d600144094a422881d00601c800b9180c0c1c0c1a480781c000d410103900c411070b00d084c030306070b00c40d1a5640e130741c3d0010030024500841c12502c19500007520990582c01004800901000c02c0d80207912921695045002c00030002a0355001d803040c00b52280030711700204011015600f0007000340c60b100300e0301d600a440c55000c00f11040c1c042402014013051181100001050143c001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 445422491 1250 445421241 445421257
    0x60f03030c0609140d020a03180e0a0e030f0a0c020306011e090c051b01021306020c030a060f09060608210910030209030f1b010809060709152a0311060714 68
    0x500400242c02c0c01c501490300814140500050b0800c0c3c141004155024504c0100c0302d0007604180c00303290902c4ad80b51f50102c000343c81e4001080d500c2080032204401401611030104150305480d460b201c10031800350890150020892003400f400c00017050602c0003803440302d480051001c03980180c81c00c00d02048000d012415229040c0319060104917080ca4644c00c122030083c501100140e00ca02c8940e1001a00c003c0380c0d0440000d40d0080a51840b0325100000d04132451134004901041541d039041710340000340200600075101c1c9040c1100410a00000152010302030310b070b1580f045004418050070a8a801054aaa0741c0602401e40302e0300714501c03a030007030b00c4403140017429140c00c000c50402c22442c117446c03041009911411107070540c00303075030b0841040b90b4000f020501034617152500a000520f00d410324041e05082d505148004946588295408083c1001e8042040310440044460001284e00c102086001034440c008103d48840040f400d18095181d90312010940380302ea01200b036071a040440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 445423741 1250 445422491 445422503
    0x52706010b0313030219031d03060609130f0f0f051e07060e0f041a0a0b032a040b040303080f0106020c090402090c0903010f0b04180b040809041e0c03060f03030c0609 73
    0x11072104e161b2000041034041c034070948800c140101130600802203034003030906061003500144d00708802038462500840e845201030020403044159071400c8003c0804401c00944014405800300b81000080c1b01070f03c803410b020702e08582c010383d041c1926075405e0030030288040068100403004c011460080380003107403007003006101d845407181000c0450f044a010b0101030011108000000009040c85000180600744040820b032031490013a0066030b21300901d0302941c0c03a0790059104450300101c3c010982d409800100c1c9415071710b90f070301d00700100301c0c0c0300542d203c41c075016024000080990000600007100040075104a00755600d030340170080312190040030082c0b012810800e5000955007885084080e0b00070b404000382400c650001d00084030002c01c0405002400c056204001c200c0200d900b5510550112040c1e69441e413580114000c2c0800707075204816410074100c3c00c00c0d00962074008000301c0c0e1041c0e508015940da80c900d03004129050f0301c03015011440c02d0591501103030150304010b00843c0a94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 445424991 1250 445423741 445423753
    0x912030c161e031511180109060521042306040c2418050604170c010306050904080d090206070f020f150405061809010602060a05090111180a030204052706010b03130302 74
    0x1c1c0f8104041d43c09006e400000710070201e801c06242da0403440b65005006180381403410180c0e00711040003100d0380b40510005500c40300b0005400c1015509540c41c042c2c200304c0b60ba800c0e030541c4541c1d5a680d801c3c160303012200404038000104000d90074000c0b03c8001903da0f00c405543d111a000d09841109880c1d002c3c00b0004082d07400420b00d0344031503005000038402040d0410384140b0360309076142003084200600c1d04040c2426420020341d581c68400540064014034041d43d55903001240740700805410f080250070900201e4560180700c60350070240b101c54003d43c0d00f844803031142010800c441c1544082c0303c1d04241e0601050110381000ca0152513074100200b42804c524070740100154818000f6406800180e004d0000c124500b061402195088848080203000c8900c0036840440c85025080b00043c154034503401c5c02c1c225688441d022001981c015008001c00d00305403049044800c2031100c251389072901c0c00d10442e1131582c0000c12038126400031403e0b81c11900c64858500c041032104805404610030f070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 445426241 1250 445424991 445425011
    0x120501201b0f0f0d030506030303040f1b0504050c04050405070c020a09110906030a0203061002010908120a0906050f160c120804030908070603061a09010903080912030c161e0315 78
    0x20019080786480f01c4000b0b003000720f00a60700809582001b48114080c0e0000d00038040000c03900c1126480165000182d40b1160201100017003540b24143d00003680203040405103c42215841c00030820b840c0d05035000e11190f6500c000c1a03c2c11052078030b00030f42000300103608000748a010703484081461540721509103000046000900241c1003039074804136450703000003841082d15003c00121401c24540c0001d1150340d4081e202d2100a010390014070307001c1d544500c00035142d42d110390b12a8440307a903c02010002400c01002e40d64090b88200e030a1282c880904030041040c80c01207611001181c0d001e8810032280c04890030450728500050801c4040c40b0342143d0100740504140485030140115550002c0c0852900ca5414100104414580000d40e010003202c1c8540e64441140300c1a0b80d0004001c2d03a5401c41c800100d1748140340403101003990b000203d40f402082c400402c0c4001800c0d807100345202044d4031802c854000c000b0310a021940388100c02e00400000e990101110f0040d04000c3e40084c411101d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 445427491 1250 445426241 445426243
    0x28121b09050f180f01050f01140f1305040e07091a0a1a37110c1908010c120e0102091c0812010b0c01060f06020d0c05030f04120501201b0f 61
    0x4151040d2130700d0400e0300018089070030051034400140d4401d19281080240040c100c1001e48107402c1c05010120300010b070945241c0d08080001b0091002070b200b00008044490215219640340c0143c503821420100007400c280c8240400c0f101042004200440040ca0b103a0b010f002c02841d11861450401d00f030080c82000e03008001c0b854442c02c603180702c6500101401c0345e50716034101c0c41144c480c1404848000e10f1a50040000c003c8041c2c0c000382d81c00c58507400442e00608000849502c45e900300ced828003814440301c5500503d20180d03010b40d0202803061000d40603c190a07030068801c050b40210309100544443c103922010514594080d9180910703080300b080400d88142c1e001d0304407100060340007540000c030040900c15940101103040c0030300c8030300d420700000a40310390b03100303943c0000c200c8a0b2040d030003404418000c4a000f10300c0486070b260b40e283d48101c1b440c800c910440090380c195282c0f19800943c0e004248580341601016000146030861035503c0301051950711003020490300c1010040746507440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 445428741 1250 445427491 445427539
    0xd15050a0308031815010e040c0f080102270d08130e010e010302010f0305010f0b0a1205071e0302040501050a140c010e010f0f06140628121b09050f 65
    0x1c0607000d40b594034a440303c1c80c00e000725000441e142c031541c03244000c02d104e20a20701865054406000342824903440c0c60508103101243c6401c02c9a182910440008900005500070803c528025031005041c0d22034103050780382c10086500191300101e003022a4000240440001d04406110b029251103041d15042810b013a410240c001a1407512924014025903800201100b03540e04c3c1031405000320340c1018001120260284107a1124240c082020700619000f5212039542c1c40b81000100400d141403800200346480c0328400b504040c1444200b1120b4600c28001c58090340c0d410f071541494800083c0c2c040b2008140c0e9401403101034024803500004203828001c6049030520b40c0c5c0040742d501e4035105100121180b5065003140e292a0841c00c1165410810b05038040c4d01c2c007162156103c7e117030a0243c92010184100c800d0b0a82e11030a900d002e03907074002c00140019003d448081025540702c113051650302c0b1905202c00086000200200321038074004545914110000d0310040004a100900e151484 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 445429991 1250 445428741 445428743
    0x705131e0b0304020a060e030a0503120f130b0705090117040f0201030b040c09050402070f0f0b0f0a110306280902210c0d0507020a151406060f0d15050a03 68
    0x340540020168000c59005420180030640a010b10350b083c25800540740c1989407103688103000c603e000c1442c160f581404050305098015083d295101c0b24101c0650300e80400300c524114010f151030124615030708084041004660000019507607481300301044d111500a2820281040540c1d0902403c0c100305c1611030b40079501c0303103c56034645c416600c0050180d4440b510241e000394580240c030002c841c3d01800b540b084640503180140e8840c81402c1080000c24442d401400f101d40c0018028100401460460311030481c1c0d03040c4900d0f039101c1c242c21406490081c8020f2400c5101800400d20030b2510304112200c1070500d04d0081141d1030000d6049024404c20b901a802190b8041103500b480d0850403072039501784a0382c5201c01840d16020b000a0064000c0000c0710004a40e200b0004001600070080082015000000403a50090100100b07001d0100408240040072012010030311a080c198184c40d06100c10002041c1095007101d00c0c1c100500c56000511030602003d800011035895a10300c80c00a1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 445431241 1250 445429991 445430009
    0xa0302060c21090a050405040609050f060708060a24020a060c02010f0e030406080f1302180a0b010809100c12050a0902010912020607020f011211041724070513 70
    0xe440d002c0004181d580c960610a18200d0401000c03000342c1e01d070746295050390307411140002e55442c5c03810101e00038600080c00074120300c03e6841e603901500000580364402c1c0155600c00e805a0303945001c1c080040f80a215290814003007085100c8642d1070000d240c01c16020601c12541e0099690301c2c4c0d001583c142d109814007607595201480c102c1703003090042c07100c42c00181006618051038410003d148940050180b1070385050840496070281c0307080c0407010f05075002088020113580112405820103802d84140140e04c3c5000c50020390303540690f55551141c04503101810744401440c0003540a0900ca0485104021410030071212280c090320855000d205411000900140c0a20015001c104980c100304d010071400b04140700140daa800807a204180d060b00c446200402c0c1074010b03a040b91419070466112410400351070924400304014000711480c600200e01e07048a1808a9034584100303100c42e00d100b0300c001c0e01111000c8051403011740c004403145002d519022185a40c5020329003550845040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 445432491 1250 445431241 445431253
    0x60c0c1406090108060112240e0c03160210060803090103050108060702060c13120506091216110a1805060f0123160c0f0e07050c0c040f0f0e011d0105060307030f020a0302060c 77
    0x5095000e0094000b6180c810301c00d000906102b6030801c91400002d011545108001010f1002c10f0310174042c58100c41c1030b40400384a0305d078442c1d4820ba200d401407a1507a0009107804000070300003c0c0001d4140c020100340d009081640c0314200c8800190317108202c403d080400c103850004012440e0070781c44002a0040d4050310490805101c5103050240142c0104038954050080ca4081d81072441850780c6079030b0004e403030354440c0380d1400031410141c801d0780000702603407440090303104149407504410700c254800c070b50003c8220204001500e4200700c000b8140303004c6454070b00048900d801800100fa4039902801201020045903486a0315441e40d500040c6078000e501c074080100800d9406150307046051400c0990401003d0500c403a591740c40070f2a19441603407660f5059241032007980c4a002c842c003030003401b400030040e000c914a018000083e2403c1100440496001403c1010302c50f1700d010300c1d03005000d440068910b03240c030041c80d65110b600f81d80c0f04c0c0307110f040000140c1d9400028030128001d80d0107440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 445433741 1250 445432491 445432541
    0x3181a0d050610090b03040218070305071103040b04060e0409052b030501321507021503040309170328030b010903150f020c07060c0c1406090108060112 67
    0x7900c102070090340c000d800000d000b0715079541116405080d955891a101c0e120750300d0b40000f603051812551130808042441003401903d03a071603008684070b10340b1500d6048202c0d038840405940d030b11543c800d0648800302840305100b818441c840a298840d4001c01c045000926500d0360340c20104c5101240c44850300405044100050402110208600c0d6050812541d0302d40b00d1451040c40e01a220443d1140540800e0311040381c9035142c140c11660b0140c002540398030400b20102e565403000c0410b078071031203180b4020356014120508072407040e41e041d40c5a5000d070b03182c1600c031aa00c42d404000d01045000030300106e00e0052103c2108401641070582e8401010f00ca2138014084555401040d410402d4500043c80800c0d5a881d83c030120085c0f070031001805034404c064030b10080c018003180c60607a005500f000185d66030711041c000e000c2c500545c41200c401759140c1101601c1820b5100380d581001050001c0b9507550b000b030110540c00303401810a01004454003c014080b01c940e070054040c2c410111202507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 445434991 1250 445433741 445433767
    0x4050c0d080f070302101802091b09060a021014090f0c101103070512040f090b0907051b0a061a092206061e030308070f0207052403070503010503101803181a 69
    0xe03402002c004ad140d40c003240c414004001d94032132201c84600803040050003003100d40c400c1006501280d170310b001c108a040c0041030b03000040e00047d1070305800c501ca00d404101c020040402c00c00041d1720001c00007001c00c03030851010b6602003441801201e850000744002d0001c034009100044015810a1301d00d0b613151b0600708a40f5200a032500500d40701407401030508a00d441b50401c00d5000034060424503203400d0009200c04e985014485202100d020300f01111003000300c56041503042042105450441048160030300118082c00c9610015942110bd0038100f052a003c44441d10701c0d00410000c14582d480f040d10390f5201420500d141c0540c204d80b4010001c1c140e2080c0703042d4115641c2d2078090341d11001040000d503108414010f20348142c80b0300d40170701c0aa104030340300c917900e10703032003003210b41c1c0341c0c5003822014040d40c009105540c02409013185252881c0700c61b2040c40070741a52484440c0149049032421102010701092110b1583c201442c0410b021001c00d0301d00829000790640b4695881b03460301c603d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 445436241 1250 445434991 445435009
    0x1e0303020d090b031504060b04030503070203061b07121202040303120e01060f051e090408130b09152a0109060b0a14010c030c020409030804050c0d080f070302101802 73
    0x4105940e070003805000c090400310782d0000ca0192101003e0f030646170000700102a030b6030005031041030005000041080120280c80c44034002c1703080c0c4003140e88814040301800341045045071400c800300821800150307284003040f4000d0403442c1203401182e61aa8000c100c2c1d0240c0c100340c01207a01c0340740101c09451745001d808604200e0500900c03c851400c00403a940c103d0314011244200c01402c003000031168441011070761204004c040b80700a0405017003804060b4090501035190740201040415910450000c54141010140c0700303070080d039050700b03d0501c290070003000c45c28441c0b01c04980f42403401c05d11460f0b8083d4100031000186120051500c041213800301d26185010301c080c41070030010a9050001074801c8542800c0803214010503180403554036400100080d1710030310b080c80410034180d01c180380308d00c16072251080b15014240641044154229603800a05c00f8008000358060100c04a020b4014140300740115604400c02082c0c207003d40d140f00d030310b4161002e11940c00c5001d43c5040000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 445437491 1250 445436241 445436263
    0x2030d0315050402090609060403260301080606010c050f06010605041d100501030b03030d060905010e0f100501030c020c030f010b030c011707390308090705030604020f0103061e030302 81
    0x104001e5207a034400d002100800c140314082c403990380464a104151909001c864081400900c03050f038654681c070380705840120341520054034107000038002c00c403c40a082101c1c16980c400b4020503081e6101d0004441104840808591a0080408900950347c00704201c6002c0c0c000d80e210203490b50b050241c50f280d680e410700c05032100c0a0001d03091000f030142c020009003d455080c03a0115a40744200003091441c468090755034a5107207041e00000d00780c200f0340e0056068a200b43c1e42c05182d62241d20480c1000101990302d020098035850040203103601903805206500841d00644060b20040c2c0300003402c04010007544034181c1d440c1e038000c041d14502400344401501c0709003002145c115140c2c00f421280100104201c05000842007c0001e010848244100e00741142440840c00c1c2605108950000540c6c2c00407004a144000800d0034600701142e0701065030400350013410b440d41c1c0ca808000140780320010b10390605581d1080425003600250b002c50007441030b21140c055041c60351500a103071a1841d41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 445438741 1250 445437491 445437497
    0x506010f08040204020d0e060118050106050909150a080f03040801110408030a0e060d020a0f0906210f020c03031305101e0504141b01110102120c180a0e0402030d 71
    0x295014041d003002026030020b030161030058803403010038110360040c060840074036010303c545d60000070401261403480080b820b50f5841400389998417442946c0368010300d4400d07944028484000b83d101e0f041c5075101c007505040103008013a000d6680089504001030209035080a800014080c445807009015200d1071ba0341c4d0100003840c1600d8481c64030f4a9006181c1d441d41000f441c04662100b6075102001d4030301d14071080d9070455a4521091000d007005a000c3c4600d4042540100e0002d000b40c02255808902c5402c0110f040b00d0120001c550002442c0070980e080340d440e824042255402001c0014511070310111001c0a100d007102d003401c33841c0c0314000e14030801403810100c0349000038402e032034501808250880e0225040d1100d241c0803951442c41d2200305068425400d0f6401c8020000c01500c401040c20f0302c8079048089660800760a030f103d00061164a01c00d01030100d490140202e0080090181c04968111311160140000304039007401d070700200f491000e034802d00c401d5140031b10508601c0e20b1a81 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 445439991 1250 445438741 445438757
    0xd0f110c0a021201060305031303050f060103030906030207170c15130507030f080c060c0423030312060d120309060b0607031d01031d030703090b04060e1c0f15050601 73
    0x808040d50341c111600000380034000c3c03000d005039800d509400c007902840d4004240e1313884402c4882108003031585440151454495450300c13400414011507840d040c1c03138056851000c03540c20110700340c0207940180700440c1c06120114103c102929031401520354122200044d09241c20f481d410054440d002601080150b1a600c440c100000d200080b01c8084903400340310120500000d05000415029202c4220241e0040004025420000000070030584680031040c03282020301c00304d1041c811403108001c1d80c15900c00c001540281e2000700503541d00480c02001d40518405d41c1c0e50f4062001c80081004000c603031103054440030484540a00c03029075000b90340c41820040c2035100288040c1c080c2d01100c40c000b4100a444d4101c5c0d101380c001d070340c0c0c050004885800c0701d041c40e580240e41c0c0c0d101038000d8000840c00e01700401c0040c9184111001c84100390341d08070200e08121b0412410658520a0f0360b60b00c0b01184540000030b6002a0242c100c80c0078414105c1180403028030f05007900c40040904e4104a416 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 445441241 1250 445439991 445440007
    0x180115140c011a03120405041a030a0620040602100b1c0b06150c06070c110d030c0c092306030319030c09080607120e03071e051005131410020d0f11 65
    0x2171016282126805c0b01c3c0460030740140f90f58480d003180c080251582600510951806012a40d00b00300b0060072002900c0d8031211728034413101100d01030750045c400140c0012960419644641d000215501c00c014001c0401b0f807541002c014800501c68400c440d041130740010000c0c145030140418026414400c4081e01d0038035032010700d44c0c40d074500621100034445618480020700c610340c0c0d42c0012420010b0050703500d80300e8604019000c003601d85022106881d025202094803427590140304803101c00810100e11081451a41c0003601100600d4143c040c0700501c81240c0c6c8952404034958050402d481c0003c0460035114003c3c0440c506801600b00d2f42c1c000e04c1802080399010204400d5802c451500281c10090252001d04502c61342a004e0100082161090701d1034074000c95140003103210720110f07100550982c0c0f12605440b03040718008403800391a02c0400c0070030450140003071b141200341c00b680c100540160043c4102d800c40007803425020355402200356038445034880c0c01c1c1d603011240ba0f102d0030207180c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 445442491 1250 445441241 445441273
    0x207050409020a06111e0a050c03011103131104110a110a02090c090d150e0624010c0303020c060f06040609111b0312040f11180115140c011a03 63
    0x601c00c940030030005170039200c0d454030188071001201007000c2c004540c410700300c411540e031080390701802c2c0c2d60b50003010381100061034148140c1080c00c0000800d03d003941d903045440c9103030b42956602a100c5050b1082007002070703078440c800c1101e50050701c80101d480341c07021072000f040b01c45540d10004803030344940911005030b921001d082d40e010314800040d66681032048085144090910030050284c101c980a181001500c2c0e04140c8070411507404076030195841d2112180591603c4860000440e00d1603281c442652182804104850182c05d000d03281101074a445c40c54020112001d9031142213050612499151074041c0b00d004011181e028030400000c1003c3c06a60f12581c0c0800b4030b002030190705910328100620607541900110a11080e082c903040c0ad000046e01113156088440407071603901202903142020881019001c01c043c0f82581e82c1c2031460070b960400e482035104080c4140030400310714051800d40205174280104002241480c00c0a41d200d610701d0f20744100c0c03446904420009048a20703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 445443741 1250 445442491 445442509
    0x100905070216091a06120901050601180501030b0d050307030e120708061305011805060a0612120f0306080a2114161712090d080106020a080702190f06020705040902 72
    0x2c58030000340c001c20580e950070303440080001c011742003d07020131100c99031100c000ca40761261000038006d02131961340740011119000420194504051110020b01003540f01f0b46c03190494180140c1586011341e81900d0307491454000803000c4000640b0000203d50700d040c41c1014068400d81040117040c15130928107143c1d140c3e200203000d482c0c3d91364102c2e0740e60240042500044030b40b0244107000b00078901242050f6895100448141885a09004000800385030701d1011807515a0485c110740c8528000840031101c1c0c45200d84036204058a40001007294138003800715031031440c4603440c0c04c1d000c40c409010310040d00140100b8041030140401c00c01c040011170f00121180d80700c240f41003106400301c900e00413140c0140b480d110b031110035000c2441ca45c80034092894500a858040c00c54400224241c0122000c520034000c0800680002d1291000a1080006440e140384018000c4420705428806a050700d102603024500f0003008440801c2030301e4040c04403002802040e5424042c1ca03480345c010a08030300c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 445444991 1250 445443741 445443749
    0x306020d0f2403110609060406080109050c0715050a0e030d060e0f2a0d0f0903020114061507060207080d1401090510030f030201020c0d0203190201180b06010203070605100905070216 80
    0x1115104c100e010f07551031100b00e03140118018112034507140c41d06002041c41209002d842d0b1600d1a0101141d5005080d4058030076603644602c0e5075140c44d0707c0c0b07034251010380303800b078600038010383c070303050825801032040c8003410707154110032400180e0302c1c6080a00741c19080040e04402c12084800240000075001141d41d0056410628110301c00c0a45070f603d100d43e40c425078041141c503504d402e0500a0000c1c00c0e400030405c4c1c0e07000e0360090240045494204500880664501b03a1144041c1043c40b4149a0400500714150142d400142403011030b480d038140550150440c100842e655100424407a44031115160152130700e50300c10480740c600362a0740040c03d180d40c00040c007804c45074408a410140700b501210039806403402030b28103148800e080650f994008441c2c0d110859442c4400808040c07051050034191511042c0c103203181510350716906000c41c0301900031030442c002009140089a200e0160b54002c2c00b1082042c541c00c3e00c0c2075000030489502908202c1150880c5c15409050382d040314010007a6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 445446241 1250 445444991 445445003
    0x6061806130c1404030b0105010f02010203070909050a0204050d05071e0803090d0f0f120908030a0e0f03010204081509010510050f09060f0d0602071a06060409150306020d0f2403 78
    0x407600740c8250f0f90180b04000620b5030540010340402007000780b9002e04d040b500d0a0f2140c90100d85029401d900742d0004035003520005011800c02c1100c400141c00040e0010f48080300103107081d40311004035003003c0c101d10003070368264040c040400481c80c654080c800c03c1e80c84504d0341310423030b402c003000c0d5500c0f8403c824003144103030840100c20043c004d50102c00440a60300c01c2030501c45562078036002140e054070b0403d50001c06c40c4080d0000d010a00481200d164818580e5040f05a081d603c00300555031707038580e030010340642d0309020105421030304101c034900500b01103e95611a1809611881c00d5407002031a581700301040440802c03458851408512140d001101d1780c4140c1d6903a600460781c4d2450040240d03038000c45000e0380206215555006116641c014042c0f01400d0710f00b4424604104d00c1519000c3e00294100f10401002d6015406401424000078000205130790741d455120580e00640001611142d0b0b81c1e01c103002e260b68502c600321500045004c01c84503c1d00e8203803141c8181c020741c4806041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 445447491 1250 445446241 445446251
    0x1060f05010212030f36010b0103060f05120a0803090601150c02060a080a0906020a0f1206060206040807030201061a1206040524150703090503120f030103320606180613 74
    0x125a5920920043e205042400e6441c40101d400035844d440d84050403181044d440c08d10218043d510a0090030b064400b002100e942142c80c010a2189190280850003407502548043e00c00040c0100c00650003850140000d040c9541005910742d16204816a21000d0182c2c0350b95810058940d0001c1d1204221a8246808140c3c3d480e12128007410744100000c01175480081d16031041d9400544400944c40c45554a1600c41444030380442124038a00610003da40010000b0300003481420050079100e10074400844c009540f10070f92401002c0d0100d18a1355220045010450400140903840d8020000c0b5000d200d03078100b040164484402501c3c07000044090604080c4543d2124549a4035403401c0000c0240d0300c1c02c042c00c00500e25086806201e1007801084495040d515401d0207a4080c02c01c0d104403181742d81d1a40e80d80340540031030081c6c5c554049901c251000d5038001d921031402c841c0b1038914041c1441d441d210080103000240500014a8660b18509010036901c0d960304140030702000c0000014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 445448741 1250 445447491 445447501
    0x210201021303080d14010e040b0c0c07080705091501080403030b010309020607060207050c03060103032114040b16022b031805010608120f09010c15090501060f05010212030f 76
    0x20180c410209060408014072030300100304000c800041c80342c040d5000d02048910308103048079681c0e110a10410a1144e001d20200e00130030850344400b6005016140b481345088a402c04aa06240c4107501610154002c4102001142480400c00b80d000300b80950000e0100c003041c2c00a0310b610f001820141c04c059171001000c409034029440b840d91a40c00500b2103895a00c9813400b01c02960002400f11054001d43c004000b030380c00c0006526045e81c0c1c1c5902d581c0824001803880c40c2030290b000b42043d02641d100e803104040d0400714441740b402180aa1800c074405c1c900300c204449050b50340315451085501c42d122229000c42c4014058403001180c0301c4640416048042c11000b07080402c80c103100000c500c0611404002056000701e00702d030760711425500742c1c0800040e905894060000c0103105043c04004256031584036201140100c0d1180c0a0b00845136003084000c4200e402240003141d0581d0b56000510481c6103a00c1c40000503c0c00348018000166441c0e21031402e40006000c040301c0307254a0020038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 445449991 1250 445448741 445448743
    0x40b0714043803010b0706020409050901020306030705120d03020309013207050a080f040303060b0d023103080d020712051c1401050135061003092102 66
    0x28460184501545031240d89504040b004440010b650745500e5503402d20340b8003a11082900c2c41c0e40c800380521418150380ca4600c03c84a07a5100f80c0c811078000742e0070000031842c0c401d5485554001c01d41140010b03200d2504000707040c5881030b1030300801d118042e08221180401c0000a01c1d600320100f500d4056129119040c40d0740c090306410340d14034a081c1e10421002110032903030401d01000c4207041c400b00c0b1305845806040c0c07140d2140c44e0460000889010004250440070307154180c115200785000105c8541d6032180f01016041420a420320a0700001d40c081c0780c4640c440b0311981044800030801504545624040c0725803c80d00c4001e0540c00701180340314180a00e94140d428964010049040d5401072210041c8580d120520b244414044004c89030000c01a5100d80340e0141991004004242d0a001c0107442c0070a90720380f0343e018038102d68990380f41c801d41001d048a0b03110099610502c542060301c01c00041e00510070820b42018902440840441e20000d81030320403601f681200d08610540c1a812 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 445451241 1250 445449991 445450007
    0x2f090301092a0b0a0f1412011820090405130c03030302120a18020405130602220611030307031a10170c0702060405040b010e0a030c18050f040b07 64
    0x240001c1c1e11801c20040100030640201c81060942c5030b0b2008907034450b0311441d00b0b40138001460001840c40314070160300c203010341442d02c2d0f640e882013a428101403500b22030140d400d009070404940d0007684054207074803003464056405122802402000011216130000c81035019102480348225140c0c0c0101d90440b001115070701d010743d04119401c111300e440e0b0030702030041c4d48403100c2c9011100025000491320307a90352080da800c205000d01a041c0c4144260200409000090099000b010402c406000011140d20003044d9070440000c500241203026088904020b21940c0240b00744203840510803070080c4044212070340300c0054240014030440352096500030083d21121a40c0111101f0f503110b00c15038005c4c2c0c081d0585901c0341ca94414990f100700440c03070030340034071100250003810611003030280d03162540000d04054018589040200c009400240012045500688044481d52414022042010541004802068414022400c02000c203003500480104003070300d490f0b41c104c040761405100c0d5100b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 445452491 1250 445451241 445451243
    0x304030f32031801030b0d320a060b03061003080a1e020a0203071e0e06041112011d0c090904020f06030108150603060115140d020711042f09030109 65
    0x480c01c01c620459010b0350302c3c0d0041c000c1000a8010400c4040d1079032082c02503a5403150040c08651002d0019928102101c2c00d00b418041c5030640c2480040b100541d00c1800d0307025041d21402050100001d00341641114850313400a4005c0d00f00a04101703000850f88440340441c0c3c2c1c81245603a4803568540c0840318003050300004500b1a101e603041d0040660300041d0105224000c0b07007500c44142c0d035450320303111a2891200386046007c8125080000442d01880c80390f1202d00600040344141030983c40001e6544410b03070310400e603600100140312400108814001c1c04070022a40c520300c0c02c003000c8840300c074010040e0184c030400090000034119115060030306105180609031544039611109050307254031044454144031050340000071290f1400080c85412144040c50000b14010011801c5030245059a007001d0003010400c40c0c51940750b0148001c04095002e088680001070b0320385c04000c02e48409842c181d40701030b0040c00350800341e180c0030310050700c0401d4060019901d100381c0c0c3c0824007400351180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 445453741 1250 445452491 445452563
    0x3010b03130c03020306190c090e0601050a232104080909220c290405010c0503070c060f121a130905010203010e062815090b03070c0c05030304030f 65
    0x200388081d007c5c0180f035841c04030001c00320601408a008400701d400c0705851160a0088484c203010590f03650040c4000c1c071448103945000081405121100d000740070010a911100e800c001a04011055811413007207103000c084901d007041800d141d00c03103000c58001d80710310501c0780300ca05d00480c1c10081d2010300029910748a0068900c80952820b241c0d291070b0303040c80340f202e000551081289905001c48170604042d000344c44040d0400703061800440c2d412199000440b640e03c0100009404039911301c415031b00030209a600d6100341201118020010120724100a8545090803c00c00d203030500100007150a0300c0988800f10029401c0340610050494201c003d04a544004004510b40e80d91011861044030181c810205003d446a00340002c0c031600c8090840910144605009262550618942900c424503040d06400d80302c09145286a00584015020400410a90782001220045080206411800f41d41081c1c50350700c9503a6044444030f0010b107240740281034024a003000100361603048101d14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 445454991 1250 445453741 445453753
    0x11061b011a030709060b030c07080f07150b060418051909060b030c0a0308030a0b0d0b011d0c04081f02160507060905040c0c081804050c071703010b03130c030203 71
    0x40c021003070380d90460101c0d00034007420703101040c50503180c02464211003c05c408146107550703a010755519a04a00d00c211070000c410000c4440c40c200103000740039000d024080d405000c070710701d000703c100310b8010f1450b103400b8000902040081d00c0b049001c05e010000d04a10111b51380e5500204900c0d5658907588001b05079180802100c00e018041c0c1c00100b00102c15421110041d00d060f0401c983c804003444000c00305101080061070f079601c2504400152100904404110b480540c0c038640406005d80000314410003902e00082072004501c80250000c002200e882c6c03800782403030b06803500c0712800f445904186509000745e0320420b00d6a81190460180e06030074484424182c54140e0312103540d07125502c0024400480402c03285464031038440030881541360a040f070140c69544910a40041302e00785a80284400c1c2020380b501c540c002c15109a00c0b0816071581c4030311700c0c1b4140111240704150269002800d1005201c42c1000508480d00a081c0019460203051580340c50203804c4a40d0300f0080d0103003d10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 445456241 1250 445454991 445455011
    0xa0e0108010603050c040924091707021305041110020708030a031d030f0d0914150108010e1501030b10030501060e010303030606021c0509030c04020c0309031911061b01 74
    0x641c042c0c400e40e0300c1001900e00e03006080e410002036640041015000080020040890741160300b04c0300202d0203a131002003480740980d00d804084d05565a220039041e00c001451004624210f18032542d020103201d803c0109040584a0140190072554154082e9000c0b00c20304100c180200915001043c2080840f036643c40c031004001c0c0542403400c2040418031108200d9261b1000101c00e860741c0d8001c1c10b5109007028a1918a20080c268190040e1840c0082500028014800784025048100e803c90f82c140d095140641c43d5003110100f2101101c190000c00301a95402d400b1501c01303044a8200300204502c0c0c44107150b41c0d0880085500c0200203601e4160b0002c0c1c41c0c8154840c09049a000361400c119072560350005980380e00413000800351400d00d8038005145680200054009040090b00b1105151103a5000c50201e9100c1400c0842503030001c9606403042c03404202c40d2094055042c1d40c04580d004580c2d9400700d034000d03071319a11311480d80030603420b2004030f2a002c481440100000244502061 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 445457491 1250 445456241 445456243
    0x9070309053a140a11160f06030204030b010e06040b030303090c0f0105040308120c1b030301030c1403030307030f09020d08070b01060221070204020408061915140f0a0e0108 76
    0xc00061420365100341c824480b085a684020801005881d40303c0300b1404801d1a00c0b2a02a400b102980d0140701002d280b4440800d010000006425180140c4491060901c00c14200c65511580b050b0b042500410081c00068001c009a0b81140c5c840e82e0f613408a61211740c001409000110249074240c8404000c1108500001400f03108105d8251403c2c40ca10403500c00442e40c0d8410b0b400041c02846c13080000848615029041c5580103101e52071480c10039400c02c940000451a0101540c000e51000c0010301c140004112100002d0480704c0c101c0d81103030480000300c0e80341c1c04010201c0c1e0601d13554400e25400b2800d5500650112070b4005c02583c1c1581c150701e41070010350801501612150650400410b5003400001c041c0c0d034aa503000107840c050b0002c3c0f9624001940070100c1240c105409010006060504000b034500452407030090007040403500b0640c100300c07031504145032044d007044a003c015081020343d18603100c1d2410398240100703d0481006caa10b0448540c844240c9400e207100003c2c4440c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 445458741 1250 445457491 445457533
    0xc060f0c12220b1816030b090f0601090b030708070f1e0b1606050603061012050313060e010f02061302010804060b0a0303020d030c021b06031b0c0106060807031a0907030905 76
    0x204c01d50541104040c40d54440d5580e100401581820950780c4080c0045200200ba851340035018408032100790a4140c110b50410714280c1c804090507458580768101840c080c0806005059a030004040c140c1c648080f1380240703d200d220313000b08513042054280700030744684400d03005454070910b09a41c5884810718009000c4a01c00181c0d00241b0b4000866098a800f04030140a606440109800f550400f0b8409108031581d040441d941d1004005180c0c0e0000100340b4003009082d2506c9180d071503541c00b40050421250810054215000101001340030207804090548607a0280391251041d5a9490003000038421440c03181e42c40100c002c0c4c0041015400690007512041076074040c0051902c004060b41c3c0c9654016a10400d244030039260302090900304003555000100070b81201c2409011f84454410b0361003100103c5d550307510344005101d1540c00c006983e800c020320745000c00420b40c1821038800d9501d46254580d12a0440c070011943e860f2083e040740c608030780c10000751440000741482d011a40c031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 445459991 1250 445458741 445458751
    0x2a04030501110301050f0103051902090102150915070c05150709050913060b03030702090a090303060e181501050d0f2904050601060311160204090b0c0c060f0c12220b 73
    0x6e002401000d180354800e0082d140100e0003a0700c1c0c0019190f40c400700402075080b14030348904610030b01c8850081c0052b1101c140d030142049101038031203810200e03440380481400074100c500344075203401c504002400020ba924180c038500100903291380c84205084418072003a501c03da41c0710304001d061201c030a00040915904c5480380104001c621004c0040c10740340c2c0107100c000703584100200009090820711ba0420216103129140c00110a41c4554245414a9096a8030b0301c020007112500d420040f802c10001200000c50183c0860541c5400300281900d032103c90014440e010040c4030504004a04c05008091442c032501802030745900071035030480810490703060314035204020001407281d01902c0340310007085540c030115150130601582003034112001d59080341c0107507a81c5c6c03005020596071b101c1785005402026400382d42e2280f03904054a4402c0142081c0351008040342031001010f0500c0032224100181000b540c6581d640a005400c41a09104c0c507070000180c4a040404001c007030881c1d14415 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 445461241 1250 445459991 445459999
    0x160c0605130f20040c0207140a0f0b040e070801030c030f020310050a0c200303010b0c1c03090b09011103011203090801152108030c030a090611030a0b092a0403050111030105 76
    0xda202d00f010030050b5030b8084003403005604090b209018002d10071600946560003c2c0120040b250b68443c44d0b4200b80b030961040010400100782030014000151113141c11009500e00300c94154196140c00112090303e00c0001c0600703c2c408800703001c5407000d0010000c1107419450401c55450b0405802d00a00f8950520b8000541c1411800304110b1b002030340c0d2031003622404001c42c2903a00b48240c050240d032003079000b19101e10818044a94071070b1095890350442006550110328020907103003400c40000302801c508007030b90401074100008409401901d045500c0683c8001d10b41c64241000e854290060f0410a820b509200103030300a0201d090100085032041801718541d4403041c1907030980c0f0b10060f00020901e04082000c9103401e800e40010b96040340780c0e818005010441a03541c0c904540002d10410303610712000c810003404040303912a0303900f18034013a9441c407018540503155030030b060049094540c0d060303210b0018200003410102601c1c003556100c402004003c111212040081c1c20034400c0c50703c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 445462491 1250 445461241 445461293
    0xa0c020c121e03040801022d0901140912010612140d0905040213080a0f02030610060e3003041401050901021f15031505160c0605130f 59
    0x1401c1803680018202200c0019258222006581c802034059a0703010b807006200910020640300740038401002802c00c1c0a000c0b0107010b4283d00302c4105c010b144103011007020010b21100c2e4460760800d2501c48488055800c40c2c0c1e0340c1d0038580009900f038840d03102c000c11642ca0068003240c03c4102c2200a0812400b4942c1016101e50300003e02d03541d8100480140002031f9152070410141c01c1c02c6c0c0103022080d0240c1d0350302c000552691112450501087c01c10303140b00d0185088e241c2507050600c800d6410000303d1661304141424500e01800c040102c0b080280038582c2a08002d00d4580f0f22102a904c40d900e1000c601c0c02c100359003003002e0707480d0014099046482544882004a9801003040b54460a4180c001e080c2c001100301411000010200c5031074021074594280da112040f00c514640c000d54807402451440f80c3c030a00c0c5100464000901c10030114810b64030081c0055081162806520340c000004501582c6003e160340100703ca4600082281e18240b05074810002d01587c0d041c80400301c8080044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 445463741 1250 445462491 445462513
    0x60c14030901020d0e030106030b0c030a0b0102030a140702060c1203090c091009150503060702030c01050105040b0604050d050111070827010801090b0105040f030507050a14090604020a0c02090a0c02 87
    0x149074441c0d4800e5a001da40b20f4204a62514014a5060845400140000741c1c0540c0da403030b40045d503401140d540e00070200020800a500c500362103042c462501c05e1005504004500d440640401001c010911446c00045241c804650b14001241c2d59140d08005540c01511510302914040c0c01c20b4500346a94001c01109123000e007019900c152007044200040d11f030345464440648002c200000c00359891040c071070070105581c0c90800080d40180c145038021070740c0b000c003c070085084407410b800c40d030b01c580d061210409882d59100142c9055035003c80c0c810301d01421030301e002801440800514410071502080030014004400c01401040c2c41000341e00c0605941202100071045c0a4809030740800c003c10014480c101165001494001c0103051039440c1c1a280c010400760358060364400c6545500c039620907c228201174003000004e0a0403000c0d0815241980001050101c0040c4030030b0050b50301007010720009124060841406801808243d10740c1003602e4981c015049007a83c1401510510301559 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 445464991 1250 445463741 445463743
    0x20f1308030705060f0916060905180f061207030b011e050414070305060a08100c200c09040f02040203090c0405090d1707260105040f0204080c091f060c14 68
    0x68003030b07a0700c540988626a100d01140b01d00740700103800001d640c402c80e925030036000c0001c207803130028010f1601c509800c00e24200c1004483c1000c40307c00c900e241244000e11400780700d10905103400160480c0c501c22030082c0e1020302c600d054804c0d40054001c222400c00000d0140c000b2034814000e0320030001c0c51445075126403e0200fa9002d10610141408401c0000394899210f5889075422490003003000824594850740b903481e00c064046401d4449a494065030314554200440300e52604602e43c00c0c00c240d9101d0380344a81c40340c0c0c031680e1703050203010034a0000b420090344154148213940d0048c0210744908120690b1640d0340103165000c1d01407498140445c04402c0002542240300340c80340d80c0e9120b030301c001d2000d192040d01f002d008001400495001070115031000d200c02450049400208a640c0d0326000400058172070102e50b160520740f040000740700c01c04003c50060342160081d200d029140c3c83d8034a1020204030002e8040f050a40070007030120303e0a510101441300c1c40e00800d8140590042103e0076 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 445466241 1250 445464991 445464997
    0x405040201120b04020918090d0f0507030c06020f042405090a031e06090f060b15030a150302040c0c030e0913031d03060a09050d030e2509020f130803 66
    0x80d000c0b07080e050b1200a80d01e0720f500100c41c0d44001400c054141517075074010030190104030812074003032000e40c010000704520802074400e04c01002d18101d6482e07141303003030003030014441c00e50068100403840d05c8081c240300e000c3e01214403583e0044010740c0e44c3c0b581c03141e510718030320401c032880241890103501c0050854807900c00d882000100030701c0d4445a500c3c50b90b07102040d81100c2901d0041d41c84444030803000c03808611402400d680941400c00701c01c46180ba00200303e4040d05091031094094110b1500b42c01a0031041e62b5110700d04400010358010509810850908070f5440254041d04000c4c80440c01640803040c2420544291160b6260040013401c11022a6040f1002d5898000c4216100c3c00701744540840454440c1e90700b1800c1da40c04a032408241440f400310b50350003c0b1515520781c0d008010b410000d038444160503160030491100405019500e0b01c0301600c4400c01d40c0d42d012807018990b5411001c6000a04980904540c0d40112a002042c5034100501c0742600c00b0b2440400a9024004022 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 445467491 1250 445466241 445466243
    0x901030308011d090717120f130602010204081c17090d0905010c050d050f1308031206010819050603030405280501181a0c03030a0f0f0e150903070b24040504 69
    0x350244508000c100e06e80343e031701002d40c1d1845100c1d045200c101003060000030207950510100040c2d4a14240c3e40a0700c0c1d00c001a4041000c6a104200802400c603011419403c0074140100e02c0b08080074400040b207040441c41003240080840380c1c14052000c0d40020010b40340c0c40d541e140da002c8690386d5801500e000c9488000030742aa08003604040166216100405e00b0845c00c1044c1b0b401d00345908000d5050440c640c10a1009038000100032590103607102c95264810001d00c0e11900320f241002d5240c04422003200c8607009039440380045411683c0c107000b514081d04014150780080c0b8682c04208111a44042100003e841004000704155100701c600c118060030301c022021801d8640f01240205418141064912000c1030140b07481480043c0005d6009146d00b51010070a50301a044000c1124542c1b102420782610b800c140320100d060103d50f0403076071083c10641481c180e9400010300d00b03510465100514111030502001100f490000808020710b2071210002d800901c6001403101719401520 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 445468741 1250 445467491 445467493
    0x40209090c03060f0c1204050703020102010f0605180603071e0f06022406060405060c010203100f1a03040204020f041d07020303100e0a0608030a0c02040e0105070813030c020901030308011d09 84
    0x1000504c030b5440d200440d80c22000ea020111301d030152100c605215854162422112900300350310030400e41da4240103c0410b410410805c0002900d000c000034410364078840d541400214110015140e0340c0d06200541c01401ca80c0107079180c0e01514491606942c450340550b610504403060045440d0341300050403482d85280020306002c2c50405014110314250040c0200d500200c00c0001041e242c56a402400800c00034070005600ea041900310100c83c0c01c3c1540100215280304c8001300910584e030745403440c95041c2410142d50700d449174004240603109505052000f117800060000f0412216644540c09a03c036101218940d29294000c1340c0344d01c002d03103842c205a40f07284414060940460306907500702407802e00002e0340c1a41c0303485423401d541100b401c80c3d001c1140081924103608040c0504040461104020051403038203500250401d00068446200b45100040348810180608030404100c0e8001301180c4456a40f0315004180440034051140d10754540000320070315003071745094580074040c80d038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 445469991 1250 445468741 445468753
    0x9130e0d0813080703030e1e10020702030309060301262a0609041a0a080a0c03030503060612010308030105010e09040b1b130b07051c050d1a1008040209090c03 70
    0x40401c03201007030041d2034507000b41450075044000801860082946901c20303113010610501400440703007081b89000ca41c03400e03e440540c0c1c0040b11040841c0c0880c4604154034016166040b5002091560141c20f00680c0c1100c000070002c9000c5141846800042d01c80390600490b01d51071210ba07948a5060318540303403081c0340d0079524800800c0d1420710a0841e91010f0109814034008800180030b846005c2001c10341200500040e840504114001c14060b04084004202d10240c0c2e5803020540b0340c161102408105000c008a0700590300e11049460001081200402c956141d0801c3c006a61082c4a1140460300c0340031030922500b01080c580c0d105580065561440755501004040c01c40c01021074222013410030480007100c102483c000c0c01c080c1820828107901e52040346003441c80e01c6200070501c0000c4510b55108150140c1c4582240c4000d8056800480c800d41c246050841c00e0100f41420750303000c55100c2883c540c1d903901c600041d101d0390003142e4028540c1c541400d03464440d40f080ca01d15400d81c001da = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 445471241 1250 445469991 445470013
    0x302100e09041b0b1e091216051005070b012d06050a02160506090d03110322050612011802120f150603010609031704050904080408010e0610050f010905030d0509130e 73
    0x49000390a00344c1007e0030500c840c404407494a406c040e001d05040c070380c550080e0018042401c20f1030000081000e00e040c42071500a403900c841103081130520900c20801403c0300c060450160f5a940300d2601c541400b8010070b107549400029280380c00291070040148244084581c10a8040d68100c0450b107014080918055011050140c1c102c0e6080f0f003038040c0000342d1642c02c5403410410003003090401d14101511941100340c192010100250300c030364441c910600061406616900340641140c2c040c6c08100160f03030354504e880019000e40b44500124030703c402c04002c03941c00118000c030b100b042906200c1c4095075501007001003902003800340380001105d441d010f01c00100114052011800e0300c1e1380c01d13801e20741c0e100c00042e50a00100e8044800c1400843c04200480c0c007402201c2c01540c00710302514461a000640c101d540d400c0d4442c59224005204000e41316901a400d103101406000d0140d412803503007402c01400c0d90344808501805450703103a03e0101080c25a2040c0811115100081e05084040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 445472491 1250 445471241 445471297
    0x111030417070f2f181f0e10150306060801150c06020a021c020c01020a020609041514030d050c0d0315080d0807080708100302100e09041b0b 62
    0x80b41c1c8044420319001020500815003d1044400c1e101e054510303899810b14540c3c4a5403075640e0303640280d0090b00c44111000d2205d45102c022644400c110708042c42405614060b00c105c5078041d48107641c104c00c840144074840580441010030303500124041000c1c109001c1040b0100e6245100c0c1d4000075000200500c0003200358451606c074010245803215400751640c442c0412070b4061a40310f00940d01800803807800b9848000c0414481c2004e001030a040203e420000c1d46910300108001e00c910400280740b00c1a66869026000700000504440e4101d42c4803260051440d200e08001c0e40700348036801120308036510a108441059040c00003818080282c418290701500307800c5041c08500100e00008102a6810801d80800c200d05a8440300f140c01d01c01c030042c100d031030081e00081c20440d03000100a071f400050040c401c1129030540d00010f04144401d8101c40c01c1c200c134642c05501c82c40c480d0601090041020041c0e4a001c035140300710f03e0369503441030350401501c55200c448110185500d0b40a85000c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 445473741 1250 445472491 445472497
    0x7120c2012030d0b010201060b120a021b060702010b0f03010218040506060f0f2805121915091a090a090501201e0a05091c020307170111030417 63
    0x26016140714840d0000c66031680c02c41c0c1020072072030001c43d550400d8420b150f81c240101701c001d01a816190746408800007050524010051003a0384003a000920441500702d0130340040c80190054050700c1c3d41382001d001c001c1c040c00250418500c20f0502d0300c40c203440f40c03130306200303d415420b903112404174407201a1003440080e200080c407160b400070080c031080481e42451401040007032041101e2541c1d502201e68060900c80350140b65104048492000300c03455074201040751281040e00c0c030b036002c4580c0c440103502c8a5250310781481840b5410002c00940c0600100851015644514401c0c020f5a40141d02100c0300550300c11801e900c034000c0404900c2290702544030f0800310380194004500c91500411558070b1500015031227046000005429070980c0844d441c4d642c01d109150070032403038200c001500400134042c0c0d0780002d104070300c0800101e45140c0004408403a01d0b0b805015600030075503030070f2590195400aa5100030550808512240d4406420b048078030440d40040c0c3ca0740d4051009050310004d070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 445474991 1250 445473741 445473803
    0x11070317121b07240507020303070f03060506030619090606020d0e0303120f190c0804150b0105031f170a0b090708030301030303020703030b090c0406090e0f040618080a030207120c 79
    0x220076135055003002681402444e1081e07016400659807030501c100014040e07003260046d5000c05262181c280000d1351240101c030340081d030413a04007042c0b80c122103d9035020005da1703000c04412842c0070703000540c10303801142d03010002d282a1564031000141c182490344a10078461011540d49400700060b030206603480c1c005400501e104680c1c080240b1902c0000c00300d9200e10b50000c00301e00b21344100010840c0300700491140c103454071010300a546d000b00c0003900d80d01000d440c1078001400503000b00400c03840725440f031005207003207230030890910110314042d0b4031214900710580c1c040c8401400a07503410f0000540e58200c81ca1040210f103980e1030740e02c1c02c80c025003282504904058585181304001d64902881074002d00805100558503807804102500c0c081c51076211854002e0701c00104040c0320803d14580740c1c481d8128502254104105106c0140c403412990008e000100104180002c1da6142e03026100071482205011120b18074050183e8100110140082500315044204010000c003200244504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 445476241 1250 445474991 445475033
    0x1e0201050123090703110f130e06040e0606060c0f0a060f05060907120b0607060507020c101809020a020102041a121e040f03020f0304170c06130611070317121b07 71
    0x21000c035501f5420f140c0d01401d14141e00c0a161b4809202d032100409003940c0210085a0820801e041c40301880d031070b0600241036910800c404142d800c80c07000300b88100102c10750321006840e04120549018802400c04842801400e4985400900d9604004410b1801041e0700d403500d0604850b550303142c1000d0001c0c007070b4441c0c02c10001d00105001136201e005950203490036401510704504028140300c13500c1b408942203410001150041c9040146030202c1d40305079494502c000d41e8451240c2416406441035602c44032941c0c1c003a1a11413428840c48000d00040382c1206081c00307540d00e4000c14032031400d405035464a1524010300100d000280204020f01a1a12a006070385580b0480013100d411504141d04c02000b40e07060301c2d0514403856050050340f0011008844a0b0704003403201144071580341050181c001800201f48048600c0381d8104400401513a11003024440101d07100c0c4207840a81217206022445518400071850003840345400d5031004202c05000c42c141044c03510307130a540c1c8003188180522 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 445477491 1250 445476241 445476247
    0x50d090c0510021b040614091e0c041401020706050313050a080316031805150c16030507031e0e042d060e1305070b0a1e020105012309070311 62
    0x220b600c0b0000d03414401042038000e80048031201005030300d00740100c01014401e0346015018003102000003406c2d040c18009984005d0580c0d07074501c100824041074000c40702901540010043c1c0c07414460010320a84004460160785d48900d10f005a81d210f1a41c0030b4113001c0351041c4002004001161482d020403400780c0300b29804801c403030703c0780030590303206680840b80c403a01c60300945410790301030054107200380c10281d0591000e5041c1d25056180d010400101c62110440004180402c0e04c41d000e840030341c0e100002d100484101803902500b40d9100a10803008500900200701c41c81130448400250b00301e80b07440f81d21401032440d0070000101584540c0c020106085031030200c4684201e03105600b80d0800e2003000030356030305010148402030001048000703400c82c1458030343c00280010484c2821503881e4511583c5032880c00c207040e9600c400c0120b07503140c800000b4980740c01840d415005141242c0459070440705020034144804040401c40c2e10700c070b4100c04107201003000540309030301c0905444211085181 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 445478741 1250 445477491 445477499
    0x52a07080427060308090117010f060e012606040e0c03101e020d09020a0503070312050d0b06030403080f0a0e0c0d0f08120403120513030c05070b0d060e130201050d090c 74
    0x200b03d80c01a00280c45140340811032020f1542c00041e028520150340800400ca50316110456454100e00e0040204010124030039800990182c0e21582444a494625444002c2405410ba00302502140d040b4441c07030800c4c0d02e02010000204542c3c90181000d4094030103500070b41140c00141c00c10402090291103000300000b420b0a4601c007a00e0401311000011401898034010410755440c80c0d00040d00c0394200601c104005030300d07100707540e0a2440600f40f03e9150b19007040c206000382035010071560813440002c00c100400d940a46024440e2541e114000c07100e45800c41c08c041251502400030107654801000508580f070301c20302c101e041c1d500c58501d910712144076584e1250260010180d04a1040c07892040c4010503421115240b4552000d580c10442440c2c20b0001503810b5015040c060240300a02414a0501800344050006000c3c021000c6580314866403052009100398031a88a19410b0040440c0c0d40300609440c44000f40d030140c0da5a4204600032030306000a00c60080101c1d080454400005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 445479991 1250 445478741 445478819
    0xf03030f0f0306190b07140a14010b041d0705191a04030b07080714031005060f0d111204240c0f0807030908040b0a05070501052a070804 60
    0x854080003000307010b42c407810100188100380d001405650302c21408158180505080c00007541c40268120f188420015954540139003010000800034080003040d02e44410040300540120f403172018252410041e001200c0030000e0030a42c1584c440480d030300721040400c080c0ca40003103601c40c0c0c11000c0308031400d2603603034281d01c88940003100c07600324281201050400902400c182295403006980c02c00c03021a1404000c000d0030483c0034603030082e9502020001c19192003070311074024003502d030203010540d4540d10118001101c0c1c21031140c81d2041e50529440100d075010350f000795260301141c41e56843c21921a9580c0d1051131309005c054416011a144040c070b142c9140c2d01a0102400030360b01e80310f02c01e1141040040a40c50010f10441c1411b0402e80710b640081d01c0113048030100d8000103200d603110011040110b03014469200c0c041c0c80c1d0741c00d09090003d02c100000a400000d50f1149070703400051003074036840c0e60714000c0d070304041d0040300e0500040120b0804101d00351132410007420102e2903002d03051044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 445481241 1250 445479991 445479997
    0x30c09090d020706020c0603191b1206080f0a03030506030a05060109020d1b02150702070308070c0501080f0f06010810090f0f0f06050d020f0a0506030a0b0102011506020604020f03030f 81
    0x2003140d84044100c80410303806000080182c91280301030200c210182002c58210320026100342155200f1080d00c00840302d8135031112003040c580100341c031112881400c1c0108450380344080a10301c5031078880b0004000c41d000a060501c0c55a10024095841d03d945080e0000c1c5002846c0c1ca805009288250340014030500c505800390441c03000050703e500c055030b464001c42c0c600802032043c3c445400610100340383c002410b06a103800105480565a81d0640308038288002c60344010203d201c045189004c00c00705d100804240da000fa81c4050180d13980c01e00d030303c00105083d2040c20700c1d004001c0124406501c82e290079680580070062424400c0d55488a56080b0351500c14000d1400e035840594072050300c03040c001c0e0b580e40b010001040c8412400d29000480544000300001d102c1c10b01140544000c1c0c507003a402000602d0020138131a181e01d80300102c00c001e404428900e9006529001c102800706074140c0d40c40c0e059941c151700074000b40c2d0f00e41e030a000b1000a41e9a41720350511040c06002e80f205045801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 445482491 1250 445481241 445481251
    0x708070803041401151206050705160809041422061e0213060f021002091201061e0e040c09020a0c060617120a0f20150426030c09030c09 60
    0x10b101804010203903e1382121029140c880701e804100004200c0340c0151803001c10303403e8104100080303e0b190081d06a80074400d01c00003c800d00d402317011030001d01240001400f108441a41e051099202c90b801e10446040c4c00c407110b10f0002c01c50500581840c10501003e9500c40c401c07000080c05420400c8101403076100b0880307801d01240c0028802418510883d00a8010425802d181071760f007210542c0691103c049900c05c078541c60740841c000d20250b4488240c091340000c8a002081129241c4c0c94500c1e468913181c00d61041500d42400016440b90700b508410702c0350350821a0300c0329041c105090b100185d400010b42508207c488010030010070402d10074800141582c284c3d41e00040c050440c13203414004880300d5844448014015210719a400820b031b41500c06041c03030701c0d406105840b9286480102584003042161003a03190109030340c62509880360042d402100341d481c40345000650103d01401e20340a03a01085024404240000000300c0540484035001301601c078001e10b428003141c80d158003290 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 445483741 1250 445482491 445482503
    0x3071b050405152d0d1a011203020622020405060f0a150f1b06091a0a2c0c0f040f020c060f060105041a0306130c020d1121070807080304 60
    0x1c5000030f51605103501403c9103010300001c1444070000804003514100c082005004001e880301000c100402e0364900f40380200e1a144110fa9035840741c9014003420401c4100710003511a640200c0e11501a480d4100030802ca4610008241c4000e5030034000501409405141c1100c010158080c5640c1c40d5054640035045c1c40d031039860720420840340100014064410401800003081c0108000160b46045800064000d6004600780986181950011651004c071060b180a02e8003400301e0a400742d0000304690080c170340c1240245480308480120704e540b08104825551000ca40101e09041c00c14810b11403820090000901080110440090768440c5200130055040f10041001d0b5080364000140c202c0001c2c64100c0c03c280c18105031840101180200c10303a8000080f0000d0700f01d903542c03134030742c102c4080006050088042a0b00081c0d620b4072075080c0344c800300389030310050303003040c5000501c440c3e681c001007650000e48000220360094a600081045e1a5858200555030114070840300460049100d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 445484991 1250 445483741 445483771
    0x90f090210030b010c0f030509030d030c080c040b070b070e030a030203031902040302030a0803040609060c0201090c0911160807020607050a0c080a08070b10030c0f0305011d03071b050405 82
    0x11042144064241220314140b5142c07000030b02250341d0100801d0140ca910051030540001c0345d04040e01c00b8001c0c1105940d05102d440d40710320400750b05400c079031600343d0319440d8501251500111110366004c2c0380180003811409215810100d848408079540195050400d210400c0038200802c0c2014842141030780980d200205104846410844030080100c0000085080c541150300290315402c00e1000606110000700200b018000c40340d008111080d80301c0e0081004400e100e1700a4041d000c8800251043d5104600004081c802c41c00782c813030b00044040400740307400c6c0c20f8020f59103d00900001901c912900340301c9880140c0b90036000b03210580c00b81e80100410100b910389622001c441d030b0040403a075044580740750002100384040c0c5014960000e00c0c84980c3c0e80317104140d4800c0c03000b980003412946d803402c000a541c2d200c2d0000f00301580c1c0240000c0c440b407545030440f44d0b2516910408030b8000d91080060a01094105100821003404040d29441080c1e031140000e0690b00c066400c030309601481d07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 445486241 1250 445484991 445484993
    0x7080d050f0912070f0e0105040c0e0d0305041211130506090703090f0b0405070e070e0108010b03061c0b0a0b03011a0f0d0b010b031801090b010b18090103111206010806040303090804090f09 83
    0x1b000150041c002201c092080032800c110040807406104200350151140c007400790205030003103055030043e110511001c81c0003201e0f41060450304103641d003114065940f68101102d00076241c00b450348191000340400340c99442c0c6150403030060000903c1510b07004d0115200c40c0c0040d80c559221405540030350010100301c2e0a0a4400d01c087c10041d1482c03041c0403404d5084010f60360081c02c640d044a40030800302d503d85d42c46101140c1500d211010a00900b103102c0144401c003d46040c24502480700d848080040710103000526088540c881d100c3c0c5803180c02140740140510300381881304144007000c2c100d04c441014030354030340b55515401e8010500e400c502108204d0508140002803007592040c0c2c00910942c00c00c3e8550000505040c001c03042c40c040001400c03c200b40001929101004024025208540e92030038200102070b440c40840388202410011000c0c92070340051210306840f00d1a01803d03060300e982e9001d8009156044049900c804c09101c005100080c40c82401d09030f218651000c00c0f005c42c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 445487491 1250 445486241 445486259
    0x50c03010303170108070902030a060504090c14120703060e0a021c1a0f0f04020109080d05070204152111150909071b0311030409060f0807080d050f0912070f 69
    0x16140d480b80f0140c454001081034a0000405400316186c4000040c4d681d00c03580d041402034109608090303003190a0109050801818401000480f2680010503070401c01c0d0404010700b0303074240e42084c3c0155022010500c0800d001364005203100440c0b0f822280c8030902680450044503442c0e51600100103512002c00511500c003000318042c00f07005c4981c1c2c1092800340c8004001010181280b014103a6810000c2c085900480302c050203080b1440854001c040c2649006003240e0005404901407410311108105812035007100342c0503600030f06842c4082c1c0b5006d45641c0e1605664242c2501c1040c1141210385680d240c905086c42c040307240440141d5034411443c1031210016024000404001c4001c04440c0707042c08104e5408841541450038862613491351164a203107010315040300e44d03000e191860028840b66454403403801c6441c000300740d031075641e0343d09683d41d100c00344c1040003008190100041c44010040b00c000308a202d0005101460041c1d020a245161240681102080760080f4900b4132044032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 445488741 1250 445487491 445487507
    0x30506011a0304021003150339030816170a080103120806100c02031c0e030d080c0901110a0f050309040617100e0304080d030c030b180c0a050d050c03010303 69
    0x3200341c25407482c42c109540402c910050980d1204105951000c0d18561104003020200040d40c0109040700c0c035010076650007401d000c2c03408190005000c0d0785441186000001d40c030f00100c9030090955828819000204800c0e0424814112113241140403100d0207118484050001002d1030781d07500c0581d6045141c52440749125883c0002032041c3c840802880f55540707030301d1207c04600381c40c2c01c0d0505003051000c01d16004d4551541c000c50341100e601c3c2407180ea4403402d01810401d0032421602038640344001550040030603103105400c580e003082a0b00c0e41b03500501c924901ca0703039150b08440c081070003501d81c1501d8021007903080392a6000050250202e151a01912014140305844035080d0f9038004591aa922f03040c408022110703440300341461048005005580013400910151a125102a000200140050111075001c249802034405042c100a0400e0107c225030501c02113040c0c1340c0d885124a150003248080c001c101c020000c4c0203c01d106030051350b000d090700d4855143c6950540c81e0150602e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 445489991 1250 445488741 445488779
    0x50709050c122e0305010c0f0c03090b090604033e0f040902030a0b0106020d02070f260c0402040b13140315100b190f0503010b0a080903120103050601 66
    0x504140050228829444040d40d001a030394080f02071000144400c49681c007a40c81c460b40620841d400001051040641002c1119602640c4a456a54074600d003a50700b8416010f0140024400c48018440d1181c000000c0c44040c00040415062694a44d20040084000c40b04402040600d0124014000b4242c041d1035103800a0700e5074048400944001c13070a1800311003c078621542c0ca0f4209001503440038400319042076001504016250303110203000c1c1d55010305c070b02d2250052040200003e80300c0d0103d1100800d4030080310408240040460080c003002d4241c40f107100060007110f454500c40c1e0303510b00c01007004003850b4000381e0701c41654141d4004ca20341d4903840152441d0100401c4407666501003003c004042da4801d04075911b4458400140004200742c02c0240c00d000c0010b81e003048400d5200e0f40c1021941c0036550021400c6c5682000c17143c6020a12420b510700105003d8807442c24000c0c42c486620006502c122420b10700c48400c4001e009400387d00c29100780e04400014404511142c0f00b00c4592 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 445491241 1250 445489991 445490011
    0x30b030c040c170a0b041d060f011208130807060f1803020102060f0a1b081f0f0b0a05091009031511030a05180109060e1e0a1b090905070905 62
    0x3070000800e000c2c1501805460306240c0b42da00f10700055000b403480e400030a40701c0340034000700a0401901a00d480154081c500740c240c43c801c00e00001e4920b560440f240e4180c94001c0100e103101e00c1d00d507454004a40000b0541019103c120101082c10201000301a00034480c2e0382e03810b1801c1640d07a402a24551001c15214030203007038040d0500140c1d0b0009402500161a05411445603907a11b0081005000c0f9400071101c0081d40703410b6400ca554030500d050300904100c45010741070207156040340065100c521801d180310308120010004158014098845042e0f6030030110701d005941800203403a58152180315020400f00c150a0013800303035603404440d07043d45120040081c40d05240f81d46410b80070007000740398410788400010702201940d44a0311104c400c00c0d40240101680340ca0184081d08071210718500303a01c910302d5a91918100c0f04c518080c0c00c801c1c4800b500c0001c0180c0c9402003003180d0710b050946900b0b800303d00003840c481c0c00c0c03080307100c1d1500840c083c2a03400d0411214806890700a4402404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 445492491 1250 445491241 445491251
    0x60e0a05010506270f0c0c03040b04030201031b140903070306140a050c1201120212100501080c030c01050712090b0a112116022407060c020303070f0309020303070b0106030b030c04 79
    0x901100e1300e5568114030141c1c1103240c5c0c1d544035401c1300c2c503602c030311280d5030205d0101003800944a960b200142095a100340c80c280400404919500454105005d80c600014400301d40140c114107880001d16611001500b81c2d2191030f12911a034050750302070040c14410b106c02900f00172400d1428400c06400c40b0421401c3c5140c1104a0700340d03c0800c2c418002c00411803082d00e9410115503d00e40001c00306003d034415910b8020003246100000d0109100d40800340c0181500e81906190101344074120020585505060070070f9038903002c1c464100e100409080c000c0900300819010017040203070a00a28640d20810558081c01d4580d00700f40703080b520840c03a20700c0e6507440041031110005498182c1441c00300310402002c20f00010f00c60030504045003020304541d0280701c1c0c031316000000030003083d4007071141401581601101241d1381c1c4030032103400c2c0c000b580312018079601c10300c2500140003440c0024100c0303091002035222042401000c2c0e02c10750120b95a8103c02d02c1e1404c0500c12500351070002c80c1d08001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 445493741 1250 445492491 445492549
    0x190314010207170f0706050c030631020322080a0210060506030613110a02070503150f190204092a0f020601061b0c0617010b070804030f060e0a05010506 67
    0x950b07240b400582400140807504c00d036603c0340c4505442180740c0010091205041c00fa000c1d00350303580180e848900407800100b400d500480101c00400c02192602d20818060b00741c610350314002e40001d0255080340701c05c208034001d52010500c0407960300b0300030410240d075210005c0010b4502054440048252130405004220607070351041070fa680202d094a02c0788050351904001802003100c1d01b025050349074007146846800354009442410340e9802d030211401103282154525051400711048841854204002100900750309000307403400e03d01c6400542007a0304d580c4c200c07040c1c03502c1500c5055181c44603100043c000d4105180000e202885041c156107401d01e00800a4452005025110074403030000106003c18080c044d0b00050150040b004003581510b44900030180c4d84124400080100e00d0390010555507614003c803051107501200c0c2e81e24143c51607460740e454544510b02983c4031a80d0702840e005058007072012620040c4a08000601c4d0710700032041003603495004a0020741032590000d800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 445494991 1250 445493741 445493753
    0x901090f05100c05030c0607110d020c0a1e230f0f0d060e0c09041203062103080c0706021308070b091c02030c1503060103050c0a020a020f01050405190314010207 71
    0xb0301519107918007000c010802c0d0600510b107115005c8000f085100d00f500b001075803a804516005030200000a40b1030380ca411b110201c1e51446002c02c00b5070b0040103440304007d4a80c1d0000d403800070100714003151484a07030b260076109400410b8030f40008000d9114103d0030315803410886a6640071000c40b02d00c0c10440c002008940a81c01a0f035006014a5580c1a041180502086005203070000244080380c149454a803181003a00c04032581c4011a06112002c01c06e88600c0311003005458298501410010003510211100c19019007012088642005190081201c40c0000d00d444130300d046c031a06006181021440c078160b01540020141c800a012848840d560030340c4000c00c4090614011440c0305603800024105140222520b40c00600b86121031000c000550256100e180709032030400c2180d980f02c22908041c4a00f05078140107800c038094241c0180382c401c0d080500000706140540c182030300c0e10045000c01012520005200c052200c0c01c004100c00f5240c0302c02d40c04426002942491000d60310303a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 445496241 1250 445494991 445495009
    0x3120306010216091e091e0213020a0302070c120b07050f0f041707150512100b070b0a0510030b0406020c0106051003090b0612060414030d05070906020d0206010f0504020c010e0109080901090f05 85
    0x4087d00250703100310a42503581d01c00001d0840c1034880d808651300d23140c104d4007070000d6200c241d0854660300c101c180021403100c404202c154064000d900d6080a580320340301140c842e4030207454141d165005000403145d60680350007400252169200703e1801d02c102080561a0410039440702c9560840c5400e440b0b005503028080d05c5817489810048038040c0c550034422210b00040e44c0003040b488030081100e800303001ca0904414020400d805040003a500d6043d01c0d410050414003000e0b120101c444041000036138158010051000c3d20b03000000c030b064480d0700246070242e440c110b1310002626a2208018010303a510f266400200480303000481641110400e5190b503002003004c1c141c819010360401555405208132411703035880400801c400e203403040c40170b403030403a01d8041d0800501c034040c92110820300020b89941a9440035a9a0122030718003020000a0341c0070903074056103952500030307003210503200b4000c604c1d42c64880c0030140d0b00c490020000401d24030f00c65021031000850b0702410845a1030b01f0306c2d9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 445497491 1250 445496241 445496273
    0x609090111041203020c0d030302091203070b0613090c0e240a0302190b0d140a0507020a060b060f07150b150a050a030b03060a1e02070203120306010216091e09 70
    0xf600640043c58101641405910922241c00111000301c620400d80d041d030082c043d100c800c65810100a081c3d2a00725603d004e4031100501009600c80840c81503c0c24110001140b42d400b00302280b41c2d82c140d6030b80b51002a042c0d00410620b045078050248c0701d0103207220290f4040c91420f18118016802000580e503103854840a4090503041400010291221080c1c074060b0603040a2203990705a082a041c000300700b24041000702400c6600072805003031082c003c0d036019620a41c001c4c030104813652075030002400c005546560003002042107549200441c0c020300041030051918030060248005400d099400d4040c015100309810b2811076044000310040e40d004515a18040380c5400c8011000d800415025440e41d60600c0781c80201b113040c2a8981100d85110100c4010104503101404498160301078400020f506410004000224500f41c0016561050052040b00d29041c040d5103d030075520382d80e801c5880203a0716102c001c08540b00074a5a0b4000c1c2e1482e543c10004201c5540f42c0b00040006480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 445498741 1250 445497491 445497509
    0x40308030a0608070f050103140f04110402041d06030123010b0f0904060b070201031119031e0c0215090607090b0304030c05010f09020405011203080705030a02041a03060909011104 79
    0x3044094050b0b0380440b0203040030b441211451901d030458000158090b1007000e0010307003441034142000b1404141c0794081d0020072011005c40e11160f8862686011007024550010b50a000000e808c80c10b0707154100d0b000c944000d40d81018245201403600b500d418400701c0c0010800440745c041400d00d2100c103e411141940c11240c1c9610044140120910580c075880b5485401e1050100340002640c0c014500240300740c804001140400e42c280100b401200b280007601817007580d41188040c001d8001c00500c411811306a60074030223003e01d0000f00c40c900100c1c54016800300f545402004054003485400141c0e0310700400403403801e00c100500285181c00703892440760700400440c0416018201c00c5201ca94020000d02000060602a90081440780d00aa03c220309101c00051580600101c80403040d0300340d9500420340c0d56156050f038590784098000403200d5030030440012900700b0000c44c082c03194242e040140c2d5a0600100304120404050f00702da081c0e914250750807901a205100f12422290522 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 445499991 1250 445498741 445498747
    0xf0303090307080a020a0b04060509100902030727181a0402031c0e0a062a15181b03061a09060111011d01061d01030507050f0d05010e0f06011406040308 67
    0x12000b00e0400340015001447c40301c0940502c000c0003440e410445c8140c00071012540901c02d2020807401361400c2503406034040d001000180311a4030340da09a0f070303a22500e2041c10b000e024190310b588800c60f050a40c0460b00490030746041c100300200c1c0305103c1150040c0c0c604000303040c10943c00190b11417441100d0b10f58407041e45088880390754060140300e1100c41000304100c0e5017994a001c050082c031024001060031030f606502d200280c45148060001c5550042d0440890990980303c001c02022191171641c10050948448000078085d040a903024450850300307110b00e6859032502c03c05035190941030451003050343d0100e201f40d854584140e50300140034a44880c2150000d00c0c05401400e400e480301800914607801843e803104150800401c8418070865028a00020350014075000000e00000705160060a020041031a216014001c0800024103203502070595985250131560750301841c43c0182c0142d40c000301d02c00410b020302c500400011041e14084213540002a070380c1c2c4107901004100034408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 445501241 1250 445499991 445500007
    0xf0304061d0a0801020a0206101a0d1802030a0c05010e0a12060f1503200a08060a020d021b010b1e030d0c0501020c01050c0403060f11030721021b0f030309030708 71
    0x788010100030450703c002150b0303c00030039100941f901d5049400352907100d40c905000a1210f816071441c4581c280d502c040c50700341140001a1030103003201e1010420054140c9a8100142c2c2c1c0c1070182c1c00600740b04140b1440c4080c034000000d0041225982c01c148150340d044010081058810401c0d00e00e158171520002e040d28140915100504038040c07824040383c2120700200c01c0240d071054404000f108109803d44441c41102040f40380d4010740100e8005030004c41c08200501a1034000d8660401100e001505051102d184040103840000c034803080c682d1140100722030360401c00c29840740030000240760303503c034419400440c0d902c1c08041c45581c100280c00094900b401820350559040026550090119040c0f5025002094001d800305941b01443c2980c0c002c45003c0fa4410382840411001c4100d085968451040c0d880c0900310070710508000303211101030004889840100264020b4501742440301128107034040c0b4001010f130a20695038030400902000310000803d0701c28a0b0791065259a07200b0003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 445502491 1250 445501241 445501249
    0x6080405151807050603090d140f1c0506031c1202040f060c021002030a020606101806121d030706020c1f0c08060d0b07050c032a0f0304061d 62
    0x20088110078140040000c1c000e041e9982c100d9911000d014108440c016078854041100382d1005403002c4005501c100c4105201038003450044d485424144001400d100c0000301c2c01c3d6403940704580d20012401e00c3c04685200014900c070f50394015070181c00520b0800b06e000100704e0109044001401070181e00c69414603180300300e0b011a40034004103004014080d5503070308058440b030b482c14004c07881001030030800054144008251400c0044541c0104000d0320b0f40410700c8031060a49a500040000c4103201c40c50301c03007040d81a400102516034540210400d02c80c0b140d0221000d404d41198403c051011820a0350300000035a102030f034108400680d2600050125485c240410007001505000340c807451244030000e0380302c0c601c4c1e0400e40d102c0c8102c82c1c0c0c5080400c60365001500d0020130440d100e031301103022144110060b040c4185903400f02d0307140091401e0480380c0d201c24101000c3c8081d00b00c03d86078000410070f004171482c2400500045007040d080c00009031003146110008982c084a102c240c41342503072 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 445503597 1106 445502491 445502503
    0x9050708130c0e25021b10050409050a02070c0906050a1a030f0a0f11091f080a0c03060b03040b0a0b0609030a08071112061b1306080405 60
    0x4240744120f002e00d00c0260800d4051580403040540150012005801000041e00180040912140c40305020300c2e000194a000e81051410303044416084030642d402e13180320550200305e03030362a40700210085c091003c0141504400303400015141074079612403001d6031829100c0506d456210401c801300100b07807100c84250803504100040c40c0306281d80c28aa0080d049010110b64054203000a1094a41d0101442d2010600080540c0c171407901da01096881d00514003481007003c1e4214010f4007002e801803421000d00d40f500410041d070f82c881d92080300a4070352113240684a06040c21700c40c00c000001ca40c40c9612a250003010005442d010b000d442c0c40301d800a006108075240f6541e82d4620350441c0d402160300d4840d900c8030b104940c0e1888d000101160b014001080390b454454004000c0c200c92410308441208104000d07401488031904042c01d81c0d0807418020419202d07440d1040c5460 = true := by decide +kernel

theorem cover : BRFrame.Cov 445323741 445503597 := by
  have h0 := BRFrame.cov_init 445323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 445323741 ≤ n) (h2 : n < 445503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
