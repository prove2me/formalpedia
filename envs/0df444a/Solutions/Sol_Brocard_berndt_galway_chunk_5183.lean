-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5183
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:01:26.289482+00:00
-- url     : https://prove2.me/submissions/72469fd2-86cc-4fc0-999a-943cf7ad4141

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 932014388 ≤ n < 932194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 932015638 1250 932014388 932014397
    0x11070215120610052b061409040f140f21120712020d0609150501020a0c09180203060f0609090c150a0314070201020a08060f011706060c100912050901 66
    0x1c2e103070303402c1c810485400442c0a050000c2881240004a0f2580700c09040511000a410b241581d070030004050701c207a43c010b0b00a50003031100180c5284c40e0f80300c115900681000400e00b070b9266501f0f0200c0c00f8944101801c5550141540380000e6450001781360161050309001c070340340c0011041e0442100d0080c8040e0f411500006004620342a00c80e0506d803100705a01c031300044c03410051828400c1201c141c2c1d0700083e00b0701e032100301403400e2840080d100d2000304401e0000c0c00303440754950307245443c503a001e00130784404030b0395020450356045035040f40b145a81c0e0b025041b03408030308100e60a00c1324036004a480d03038485c441000c0003a04105001c101441e00a002070b10f415524050900c8000b16900018469001c040c1d0324444002080014070b44180620820340005a461101c460001c00b40800100140d00030b00140c0c00c20b00b807a0344c0c0311040074201185514100201d4a8000019190344201709500885104840142c88006030550203240120b00c2940301c1d03840d9010311002a151070140080c00b50109 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 932016888 1250 932015638 932015641
    0x4050c030402010c05160806090c010203040b0a050a09121a10290d05010f03121803032001021c060807050d08161e230309061c1107021512 61
    0x41d4041c80c1010011341c802d10560f41a18842e140c4801180004c0d4030080182e8414011300100030003e0104078810942880507500e89810900101c6052080507904000c02c00300007201c001591051707001703101410b4080c4801e0802c002500300180c54070314420362a5280042e0601050700340e10b0030b02a05c4c08440e0359030000c440030030007408040a00009484280603c041c10409160314040ca445080e01904154442c5240c45041d170500320000c0240300a660b083c0710080d59400700240f9540260306c100d030740c5854024600380b101e9481c62140c40d144091030b5459070002c50120850700750721881045038030b814201003241c107503908802503503003d5034480c81c1c2d0800780c16032001010500c01c0d0010545082c405900c0140d1031901d94980c6c031000103030780c4a80e03088550601014200700302e01050f032013140c606410301607091031410840c80d10781c841e4401b0b580c4101c80015001c051000b60201c1d00010011615080000300d501e01d0a61440d03622691049100f01181d00c603c4050141800603a0443c44040103807a890b0f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 932018138 1250 932016888 932016893
    0x9100b0301271b050901201e06070e0d081e180d15020714071404050619051e12070306050c0307090902030c090d0c0503010c02190611091507020f04050c0304 69
    0x7913174010805213042008800b11600c07102400510407620700d4000e03004013032012201060032420005650b03001c0380d58101c6000d0200c036540c0103a11010401c01183c4410410040d032500c1811442156040702802d900898141b00c8019003002030b00030603a0b5080000c0c2c13071610100410044004c081401004941c210300000e55010140d800341c5503181c0b007a00c41c04c040c40e401280103842e111072940258803030005074800b400d0764100350081e01c3c5c0080058580d0074100d9107803c100c42082580f809524002d8502d0001c0c401010038114a6451020740506460b03110100300384082e4540c8001e00051b01d034a0f09050208075000a40f030116445080b0039560076074140e08255103c0f000c0c0d8009485c2c1000c0341b5090145e00201d94034410858242132188030502c490300d00c0c2400781401c1d41c0c14060800f0035500084c5032400b03c80b84060740004400e911103070000e650450606656a503015040d2200d81181d202c48444a0141c00d2500418085008136044205c0c08070034000c200c1617540c1194280403403002070000c03800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 932019388 1250 932018138 932018147
    0x140607180f0e150604140a1502190507090626060c07120c060f1e0204080a06090203010e030310061b020a0e060d08210f1509100b0301271b 61
    0x420100b400742070b6140d20220700c0040d04c15001508108600d1214a07403206251030607100010043c00000104039000c003000c0000780d1a14111069050840d6000380484100401808808068030004604215070303901c855a021503c1007091900c1e107601c100100702d020440000884030310482c0c121000e2440c20003d652030483c98110701020105024901c001803000840e54099948190040c0c500010700e810b241e484400b214104041c000034984c030402c0144500140071840c1c0902e030707810542c01b1520440070702c0401c2c01020100144a9103000200c01d02221717101e00041c0c10200c901076a604a03114041d824000c4800c400210003e522135002030f0104841007800320300325032046000303101681d4204262500c1e0410b90110b0844d0036001820030340c03001c0524042c3e06043e0484030300034100055140010480140d001038a1905201d442d0348400a10080e544c0c254010141000e0b0030000c2d200e5a440c40d4080f51480d0307903004101000110241c0c03648040c518400d50500c6840021200c543c1d448446040e01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 932020638 1250 932019388 932019391
    0x40b04090519051c120f0902030706051c050f060907020c01080f09031911160302061608160803040210050306010f080604060305010e060601081f030803070c140607180f0e 75
    0x8480b4090f035501135684810b00c4c8400009811a501c50803065210541072104860703012610f91207641c030700b1100d000561000500c0500784d9201781825503550a8102c0148003804295421050f9036041600700910140007801041c019a41619140c05035203c8040581e02c0c2c0c0c400703c5406002641e10400100c451500d0505560810b40c0308050ba807408140d840001d110204811043c0c01240784000300e81d0014104201003c0000e12503007481e00800e0942c0c0c0061003d20800c0c2062000d1440c2003090014410300004569028182203c8035040101d5403920030702c5508100c80691044040821125156006078103c82c840c090580d102c80c0311607658603082c4d0703103484088c184030f4220303a581d0310100000e2000d03c1000100c1001c10014101071030034000040600303a0081c00804424525900304007007505050710721080d40d9000c00000d4a942c0c0f1301070200c07003290310100041c001e218128048a018140420204d0040303030300743d490000c091a58080ca1000c5a001e125601e100400d411007040112010408103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 932021888 1250 932020638 932020643
    0x303020304230705030d020106060210020c0309090a0b040506040903020a0224070c0e07030b100305041a0c03040c0b030618130209160e0307050d0305090f0618040b04090519 76
    0xe980701240c2c24920b40d24046542c2d102c2d071103075011036414421841d041004c0e4005840d00c2c8024030426090040c000d403030760000358242c6040c5401043d0304000403001d00581d410a4005080c60900b4602005100050020248100e019078905008140c880c1041c1c0508891950160014401d025507035003030003486001908103001c004504a0000c145080813402070009034002d0b020481c540b03050074025000c5c0301000c0e0218041c145070481480c0300c0c1e1585100e201c07600c0d40b94280060a40e8032405e0100c21440021620382d84211510100010f1805007405180102d020b8450320600c40d865426940c0988410f03120168041020604025030165414410360300192034400c01f5101ca4107a80422112101070f207071410741e071065480004c03401d6400010fa01c1c001720110000c222075031521000c907651145003907019080210010b4820360a840e800142c01c18403101904aa43c1e030000710f00389030070b40c1c00c0c643c003030510071401c048900a96141502650901d036420a000e000300c408220841c41004581601c00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 932023138 1250 932021888 932021903
    0xe0f0720031c0609052a0d0f0c120b01051605120304080714030f030a0b0f18100603020405060906092814010f0f0f0c050f15010803160303020304 64
    0x484601009001802101001c114211001040310110710306540075904040d141c149080b082000c8058540f81c0c0082940361011406d00800c0130003003080d0f0900c9005003403040e050034458100d000000d587e1040700ca844117a62084000c84d03080c20104c085d56041c3e81003d00181080c8413044100350881d00300e03100700d442041110070006c90312018030020780041780c060310080c001048605c2400f1621042044e5241e028020b1131603c0c3e0419660007850201525001013590f40b40142e071070b42d172195012030144850091203505800c2c081684600000021140009000c1070384c08009400d138000e0090300c0540c4d40040c0a98140328040e0181300880e00705c602d81c103a214100034070919400f89004408c41c4d505400c071448201c1c01c1e080a40c4d00c0c0e208904803031081d04004c541150701019540c0000350343c004164a14011900380c1458804543c110820240605a801081c50881c64000300003924040031251110400c000e13a41c034801c850b201d00440382c40107000c2845016043c0003c1c8245d0007107030f00078421100d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 932024388 1250 932023138 932023187
    0x7090b0f0d060314010c08010b0f03271c0e0d080d1d0a060c050a080a0c021c02151302090a05060109030c08031e0c0a0b09070b0a050d060e0f07 63
    0x340200b9510310b54025a5901000208801803140c01c1c01019000c03201ca080007000d651404508226a204a00350b10445020200226401c004421810310040800c00402200254601c503640d4036001100c1441514204d40381100c0c1c015802581c412441c2d4800800072141404142c4407286d603136003c51071182d030ba26642c094129010042c221410040c0314004001d005040241c40c014003210003460340b03c818071070b0501036480075650081070703654000c800c034001003001144410260315114045c90407040c210300d02010441c01945c0050341c1003805210504180083d1034511002c803a403224024042e41201d01c00c40021400502038000c40e40006040c5403980702a03950780c440c9600000b0784d0304500d03080c1e000000c0d440c9090b00c000030040c8031b180c1c100e89240d03c5c000e905140e80c0d5a40901e4207000703100700d040d80e00048507052f0512107800148541249165144540000240180c0c0b00459a118291810001044215101e0483c82c45442201160f0748951103c240075907981070120700501c0c00f0038035200f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 932025638 1250 932024388 932024407
    0x20c0f150c010504080a03150b0723031815210702070f06170f091906291305040818040b100203030709080f120a0c0f0c0906090507090b0f 61
    0x1c9164400c034011740b50242c4440b44610010140e911882410861040c0700c0c4051103220900d200f140c5d0a9035100340380705082622544414503180d81006244050300011846540c800b08003e040f00700500704442a18a4000307908108210340500003104080c25420095607140030315419109421020a0040301d44413a40e42c0680c244c401d4a41d005030340024040450745003079180c900105c981202000c00115031504e030248549645400c214142040e1202c081e500c102802103c0d80400039000380301d60015a416044244041c0480544626a0203000901c840d090201e105200d030354000c90744810040c1c5021604a21000c910540c8001203a00c030b41c8d13070714406680d070b50340074030368680c2d507a00303070040c4d9180d140c1220041c009800b5584101891b4001c2c91090030302032400f08815504032880c808c02a02c400810000300d413110141c01c0c1c024860010710740d0383c40a102d2440a05401c1301d07103030395080c40010740300c4640c4c1040d254242c51400210740116810702641c0d4051001d0a6184a000c01c22801d080081c0e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 932026888 1250 932025638 932025641
    0x220506070909060b0a0e1e130203040c171c0e0603090607030e030f03010b0723071e031a040305130e16090b0403140705040221010501020c0f150c01 65
    0x56540d031000c5050300004200c80440c5002d11401001d10740840c1d03013403045820026040108070900c0503c1141c02c00c42400702031504c442036414040001e07240300f440c0c03454104000700a50041d60150b4103041d031081c5c00140080c1c0e0342180010050800040d086404a8400c0b4603c41e10255008100380310510300f03680c002da02d84074095441007260ac4001d02070317401c00c400003400300d5000801640700d5030020403001030703820450000c50341160a01c40c182d80d07a81c0c50720304000148407920740002c8251000005d84040403900001d01c1c40a8a1103443e06600c41c6800850900d550129031100500200b00801050180800c181b0020781c058040e041003494030608240c6184500c016411401d4060015401d014420b43c43d000c16070094406810305040385814041c10400301c1c0100d21000304802803000c80d140c00302500380408002494040e0046d5100d031145c4450005450140ca81070300e000c0b001400001c0e0715840050340d0010000041d0a49068110b10414407021202445c030b070b480b244004000001c800e101c02d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 932028138 1250 932026888 932026891
    0x61e031b081b0901090b0f0c0a0803010f0f140409030e190810050403091802160c090b0411030117030c0706050a080f06090601030b010c060c0324080303220506 70
    0x116541c4020918141154420b210318510900320303854030a100402159030041c014900351103600c0300306030722117400d054848071a02c150304e00700200f8051014100d0400c0b200d0800740d0b050b42d02c04000c864000d615117401c096869042e110701500704440b4424801e4500703155201000a030700a1808080541c03101010404405d2207401c584440c9400b00740c10000707220213122012141c55400390034080d508007a10000d1442c0e90314000c9007400f181c4821582307905420b81d41100e01420501d54040c02403000760800e0210710180b485000d03016810b1007182841841c00b4170070203c501c1440c02c600b50469090800d0700360100d200d41502d1076131384800c01100f054005c0c104404c0700200400e56503e60399044500c03008007101c40107440f21040180200502240340c0d40c1d46100f03a8002020b01c0c0c00254044c641004a0f00300070580809008107140c0034141c0c0000c0d40c103400c1000d0b100c0700003c0003180c1c0e0000c1c00640c480c107201d52040c00101d030420700108824031801080030440c813019042d41c1091500a0300c43d1418540c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 932029388 1250 932028138 932028191
    0xb03011d060a0606111c110f21070b010303030f06170102071232041d06043e040815040c0e0903090909070b0705011410061e03 56
    0x22081c20048100c82038000e103806890315103000c40040b006401c031640e88802600300c81c54084101d01c141d0002c54850202080609812411104440c41244915071241440840032006080da910380045000c0d555080b0380919070302070741d629007a070b00c3d6860440041896104e1401c0031a02c075240020f0f00e01c196005031004422410005aa43c0c140d468020700d03040c0455184000e001c80b03c88170490000c05200300c0042c050408001e101035000f4140304a0452245800c201b00300c1c04240040040c21014041440c07080c0e50580b4100281100329000d161841c0380c4651070720f54030001000c0d1200b1068030000c9000350410703082155060a440340c00d250b0800b10303509090824004400100418405000c4102c00100200550001c00f82010f9022035224410031400178014240440450450401004160700800035205c800b5110162464243d000c2c0c00380202c00d090696800000c680f010b449030070160111140c81e1212002c5583e0008615405890004c010f0181036076112030840261034800e880354070aa = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 932030638 1250 932029388 932029393
    0xa08030a0c080603030708090d0c17070801020421020409020406031a010504090305041202010e0301240b0a08070c0303020c030708030402192106091e0b0108010903020d030b03011d 79
    0xe8000840d2044604000d42003040012980074000151408422903400c150004282999082c001e4007140e640c0c10070880c01420924212400a9244640c40b1500907518004040d202c882da5030703174034850a0380100d0103620316003075038a20b00310701a82c08210b8189229102900c00710b080c03070185c0c000400b03e4246500a03074090001a000410440311000100c0c00b51400f00c1c1d041218a5440e1401041c03800f0758004d0040c2800e800300100b00b5a80512040c15880c10001e000f84030b409803400c424180010039684811000303141d00800700d8280408403d40344041040d969150700c036600e22000b250f2549410805500313040e404c01961259910610007004e106e4046d000d15952801c0c00d10620150b0340f04a14519001055424103000d88c8080501c502d4030000402c2008141c4011410244002e101c0ca040041c0018602c04194050310700054445c14080d000d0006001d8507a070741c43e6428240c50130040e0040041e0814040921994000d07445408404801b5000141d003000d024400c5d899280381c1080643d081e07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 932031888 1250 932030638 932030641
    0x220b0a0e0c09121b06070201110a1118060f0d0f12051b0f100b12100e010c080f131505130203060a020715020307021203131a0103080307110304080a0803 67
    0xf0700f400c51860092080ca00000c1005200a0400990310303803a600c8150310600300001c00c8400c0d0383c07017001208214000202036960107101803510742c070220b0203200950b0189204400141e410400c0d80403d6200d48006009880310301c40781400c209080e009c1901c11030b098141d402c4002c1c08101074080c3c071840405151511aaa1400000b40352810003095007182c2035540200c0400086450126a04c01020080c10021800c2c00d4010f002800410010b0199401c0b80300f013103250b900c05482504070320b1000208600130404645030706801c13640b02604940d100702c0c10b841803002c11020810201c014107428019940c248800314029480d400b664400c0d5208107801c00201c0303911003540f6050200c26000150008218500001561040c07000441002800d214035400300000e6000c5001740050070700420108200341d62482c007a4281407018031000030558140a50440c80a600c01084000324103880d0000c031071604564450404132003d40b0100300c10b0000d80000d110000d21883e04000a02010744a0f68000762039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 932033138 1250 932031888 932031907
    0x5041b08071406280e03010c1805102a0204050f040501060803040f18020702091e07091a0c0a0c06020f15040c0e07140714010b220b0a0e0c 61
    0x40305820609a4410303c0200481c2c0007256004001040f000b40c420b801011840c040d50041d6699105282c2c00b540550800310080c611310780c450415002c0c645100002c1001e0b075180d100f4040d62a600c2d44a00380410f07400220000705600313000400100780c0c58101500a4007016502141c140c80d000c0d1416101c01810906000030404203000d00000f400c0083d00440c1818501100b1740082099807085110712012551002c8550300d5a4044800e8140c0203800c00d540e034104140c1e0302848143e103c4612607024181404201500e00c98003000c0105e42200348140d1400b00c0103005034841d5440b00800580c0361190b10071000000c0e89003240311380182120307000360100c01039512600303050203251044140507844203000c01001a09948080d81600c5008940101507034455500b6180d201c0140c0344079281d030002060240801c0502811230040c031b80c2d07150090020442c9142806042c04000e600000c1c480300d820038015000c02c2e00e612101c18094018000d800e450303070301c1d40918480f09060325580a82000007548484 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 932034388 1250 932033138 932033159
    0x30605010512010507020d0c1a0108030405190501020c0405180609100f112a07090c0f02012d090b180d17160c0210090905060a0e060405041b0807 64
    0x1c020408001c1c8803d16005d00006d44980804050742c092091400c2c80c1001d01c403030105400c8015207000f03e88410755842e42151940ca8201e4442c1a00ca0103003006c607107042418040f80007003100e070181c0007051440e019004010103000018503c01040b0341c00c03041d200c0a00c4040110f28000c10f902d0001d0010b00e000805100c09464211104400940c10078003044ca801c02254100c0d04038021f10340c2403404503900c0398506008401c4901980700d0301d2059040204410300a5404200101c40548468080c60b0740e407207040c0e0aa030700403100d0f0b20406036500d2032150892000c0910305803800503032400080301d45903a035803420411020348141c401c01c1640300140303c84920030440c004074213550303081c408152807114509040d5100024000d82880f04249480e01c200d43c024441144401d07030081c2000c0700604410340003090106070788078940c41d560401e0f0100d54a42800f50030181131351150001e502d0300740d560708103100140c10090701c204d400c1c04510426550006c0c500304e0703036400b420a0802a00034645418200360 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 932035638 1250 932034388 932034409
    0x503030a0c12020405010e12010219111b011b03051309060f05061c0905162c011a0310051f020f010203190b0a0f090204060207080f0303072001060306050105 69
    0x880144104014400b1b0382c0c0044480030503800490741040b01144107401c0a01a00903040e00d00c0008072b1440d24065455005122040031064120454815603503035208e034200410031000d0703a40440d80c5001949035000e0610303d0011880d001c2d0030f01501e0000d00300001102d808080e40b207500050b42e200750900a50340014035060091130304590107801d1016648020352000640c030254a801652151848100b100078040c0c011407403000e45204804564810a00c0b030f1706c3c0e0701340d500072446254542500780c007101c0070140b050584118440800c0c5003802c1c07420001e15603002070f24128204001c188001110340d0707185119041d55103504284050810040300280c513114034800003042690040c030401940782580c1c8050300d441c0d060b10780d010074110050004618184600d40107610315040b8888040f8102449400510442d50700ea402c5030b2078642c0d20b0b0b1440d9110b103807611010b20150020001309100610580c00c04040150038080002c003c0e40120615084034141d5100b12102900e641c01040141b43c004c4054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 932036888 1250 932035638 932035667
    0xb0c071404050705030c031003080d02090907140406120608030c03130b2b021c0e0c0607023a1b06050903060106081506070c15111005070c0503030a0c 66
    0x510950403c01d070042c00c0c0b4040200500c201581c040300043c22811400e00010003141c1080b42c4075540d03402c00180301e019512508056014007520b04c0071440c00f520900b0401104003c12540c2c500302030500408588001104c15a00c9049884540220360800207000401a09445e04021a566028642c2c21a40c040c410703840f1643c186000e1003840412040c4015081c00b5161055210885503c003d501c4002400307039043c42006040880070882106045a10a01642000c0011981c5068204040080512403000000d420000e071140314615181103c92180d1000d40400e1f205d0101004c0200340382c42461414000d903940120101c00c0c003403001c1c15102c0744000d00014a4160314203800b0380d001ca9960079040c4100020405600b000030302010b10419190701d0101c005282d10742c2d074800ca040c89600c0400724000c0040300880c160420680c68003074851515400c0c410400f030502c001301948003400829005100c1c80a21801510074000501c00380002c501c104030011000848180c03900009110707120f2520b82 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 932038138 1250 932036888 932036891
    0x619060314030a1427060706051819080708070c05030610140a030834060f051302090f04020312040b0a08011502070506030c1b06150f0a050603100b0c071404 69
    0x5ca0070301a031001d400c4070b009160703000c00000d41c002036008958207104170000941010324240a010065140082d40300c4c10b10108411a1001901070458042440e903800380209a1a4204006000181030754040c24050f405a4085070810395210042820318800315011780342e07441221414002080d2600444150260a403810041c150540d51340014034450403a4440202001007003001ca84944200c8441d43c0c445003410011442c0340601e081006001038603501100307181001c000400c1216000300e01c080040c0c00801e1a407081d203c2c2c1c8050242d680340600142d0b0540103003010540710a40c042d00400003410024802ca072f6500d00250010034030700040c8c0240311440c00c802c80001c2ca080d07000071035409071841102c40303643d01e03215402008414880d0000c0c51031800c40415020038003010200c0c000b4444c100d50004821050650420000059110380c19941e100001060512013030520401650784008c401490741100342d111039142c101e9400c180d0b00d07003a02e0b51189206100801c00003010b0039484005440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 932039388 1250 932038138 932038147
    0x31812030210141023150a0905040b0a170f06190510050108010b180310020306010210050c07140f0109200306220812010603020a08180619060314030a14 67
    0x50303103482071103244105040b00e10b04640e50300240343c068505814a4100614404d82580f246c0080708941e04009100f801090f0300c80702c005840d040500503810861001414021007070305000f8100c800045d00c030782100d030902c510241e0300001c583c10006030b0b004440c850480d102c45546010001d0641d100102114100e4030000004c10459800400003419128010f10660701c4031407803c0c2e510010703035200e040c203a4140726844a60841c0055540107501809080e070a40e0000394403107807500f06031401a42c140700c461104004e0b020114000315905542000b0800640d81c901c06022409402c0d200c944800b034421070440c2d9039450303124003598000e4207840c0041c5c000e004da501e08070004074140e01c0079201d51448200d51301000820400c0304011981244d05000c0e51000558480780020025001850240c0c00308803c440405c1440201301d00c2c405c803e0131220020300c140c1e590f10407458040f846501029241984884000c4000785007070048440c00441c1074010b54946503499030007040d241d11403044c154506000c11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 932040638 1250 932039388 932039401
    0x120a0e0d140c0f070f080c0d240b060c060f162003120705040f0f03050d0c0201050921120c12070f0b0c090f0402030601050703181203021014 62
    0x544201c01940401506902c4001030610380b4102801c1c1200e242e5103015070003020807402c451075008401d503009241201e4000c07144d10280701c07402075801005400e4a2404080150b040280714200ca40e00b000c944c4046481060340c0007051441d00469900c10503500211704010f130041c0030020035944015000d2003180e10780714908000d00081c103927911a290304200440c0b1441d024000f001103c003407020205000324107182031400100f9607005400303880c0ca040300d180d400141c3e1240b00d42c45241070300e07040000b6202d40c16035900700351001d01c0040422814061309001c1d0b401640e80b038041010b00400e0070101e040e114035282980505092001c1c01c403011700302043c02200c42d103140000c1c000300303000400d0500311b60f2882d0a041c10100b1a400240041013484140c08201c20540383c41d000c1c01c0990b078242c900300c00d000516820031090780401c8821a0001c3c03000d0084a000c01d01c941036000c0304681c07a0b00250303d00c40d2500103908004414030426000350b4415100000204100d205446001613000054011b03818041d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 932041888 1250 932040638 932040647
    0x81c030c0c060504020414040302061b190e12010f0605010e0406080c09090118061413050c150705060106050a0924121409060610020f03070f17120a0e0d 67
    0x101d0300a0701055071000041c04644540d404940401402004201145041c1c40d00950702e000844500580d9924004403030841481c8400f969051540d0189048500810030b40454000180380d103104c0e40581e411040030031403c001c1c030400c1d0321044001404181c090038900003401c4100d080a105018505d00041009130f0300010075a0300c91080205c4040740300e5201d00344450701520f24842d00000003048031403400100b010b42d50000d221050028601d0080e40c0d5100c03071603204442e80c0c06025006030051840e0038501c0c94081000041c2c00840d10140342003404d181c5a0170300c0d0030070903003200c1c3c0031520002e0703420b0440b5040140080206903c0c11003000d544020400903103603e1649a6504c24040b0024024031800ca00d90041c03003144d030051200400c03500e081d1021030b5482000351030283c015501120364008440c03001c90054401042c1d140210319200150340d50141900c113505003641c80941c0070310b20b415003000200040000d850301015031080da0a181c504002101c00100c4441c40e55072004691100c2c09801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 932043138 1250 932041888 932041907
    0x30302030c0f030c070306092904020f1008041202030f04090b0418050a0201050702040b040504050a0303110c1b0607120c0c09180f060b040f050f0a060303021222081c030c 75
    0x1152010400301214945001e41c07135039401105421100700d5003027240c0700d003600e048140700f6802111191031101c12442403018440399030b94881e0000d41d10074001000300d00f107030202200e0700c100c80c8112440c0c5643d41004002e03d400641000001d5901d07201c1240f01440c040c050a1050b500b2440751350483c8001d1b5442d2560703030180003c0203041c440701084000c19560380764405440800003410500141c645441c1c000c0d21050a92011808289001c40c10500102000b068442c103807500d07401040011101c0241da0f2004041002c42a4000801c00c69440024000103002c01480c5503501c410110f400b0b60700c0e008a94480300c2e041943c00d98641481c4c4007080341140719020103035800909001d480d2000b81050300142a0400890781c00a0030400d10400c002c0d501c2e800355100780585080c0d1805030312001c0318070054a64510010300141c2c011b0754408420a0a50014595989046100c039800c1d51250000315a50082e41e00810701a0070261200d64003505405404003580094070b02004030740510790b07020b40b81918 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 932044388 1250 932043138 932043143
    0x90609010f151419031410050d05030d020c0615100806040504030306080102161a010b0304140f0114250918020c011103010f080c030a02091f030302030c0f030c0703 72
    0xa2410350840c18024041164400542c503d0280d441102901444528520407000c000091410b960191400d45130000c082c021f108052800410320b02d048100f140b5051119020790303250108000b0b14075583e110384000c082912104019041c9850400c01440c2030019003039042e03000720034001e00031003840d900980351075004504a0b4001020b80355418101d00500072a04400a0b540c40000e8604800810b04031042d03c2074400d2201744a5042d944d007128011500c01e21821101c14401d001140c000b0341c400e80c02e62007802c3c420085031080d0920700d2001d825a078001d046020150101000e01c00b01011000c46440a41c00751000f00c4080c2c0c1c61848003c180e094144641014507200c48110704204a0300e8048415003000303c8002c1c0407c200010074011190300038410341600c41c80c207003c00200c91102103603620f500c14008003e00a140301980034400b12030f0000b0415032503800d803040303401c680306014814000514001e5005507100c00842c0301e01484c050b0202040001c0750f005000c480441000055840b00b641d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 932045638 1250 932044388 932044409
    0x7051302160f0503070b1519030b0105040908070c03080307030e0a2d050f0106050f0909190c080d1d0a080c060c03040e01060e041104060813170a0806090609010f 71
    0x10b585040142c1140603005000f40101200018094811425001c60440c4241100d000e40440805075607549100c0c0c0c0c40c88000d164100c0ca1004011506e0184d2054440e540107200207850250140d5503c45c114000e80c0045071410008024001c90a506216201014006500404040c690b9484118054200080a0000711414801001c3d02000030b8030090781d180c1d211003244c15030245101c0703480c06000345d801094060f06448030b0040301807401100c00d5005a9089001d0034500c12030b200d031440d02516442095658158103403001403607480030000c1a9141040d030b0f40e468600b007410f00d00810110011100f9503ca007a0b6540180800078010481e0a140e0710f003164260307076940308015107500398081c0358800440c50803080e000080103078021920b6014544200c50401c4440c0840ca01e00c500c5004034024040040c00e0100000c49112944800c2c20740e0600a000300c202000d00d122002000c0d0b0b01c003180100001e02158140045401c12803155030300a102154040c0383c640c14550707050048452032040c0700500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 932046888 1250 932045638 932045663
    0x10060b181906020109052e110f07030309030806060f180f15070b10210c051c0c0b040815043e0406030804120813080705130216 56
    0x703035254411001c408400d441100c5605988010103402031154041c141c07081c4c010014041c0d520020808102e284440d41c03c40c00c4005142c0304010360003080040c90034000303c00104140e041d10384010025140280c0b10342e07801302c2c0784c105034038000781610700203041d503030160b00103019258a44540d00141d0b05c240c003002e00d2102c654100317400040d0504201c00a130981000e40c0403481c840309400385004210080c010902c3e1940c0780c8401100d008844150320402030341412030505806c81d185142c11480c201801402c00c0c03081161544c0014061703140007200f4018010a0801c4d8508001c8410f02410052040b0350503242858a41000701d52600064a0082107060304071b80050104952645132a022052440244003c2580014248000800303c100f054403611840c1541c04580341500508099a83c400e2159040c64900846050321303405000c0c0031035500c2c80c1481070509079040351880200404c10940200310b02454801030060905c9ca0940704142c0900400442410207100a0300b0340b0529842015007040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 932048138 1250 932046888 932046937
    0xa180b06190b0a0c0b0c030603060f070c0507080714030102030c04061b060c02030a170411090a02040b03040804140102060124110313060e030a022202071b060210060b 73
    0x401c40c140e0440c00303980c840860141c600a50168900701c40912656444c4016107540b021050380d1302049890507415405680003804078824040c0e450707040380c0203052150319a03032255511403d02d009a00f02504c5c0c1d80c407800c000c000c1902c00c0c6031501003071503040d0002c41c6142401262100e4902c118060441401005e05548102c11940320240368200c1d0042003c1090b07900c00c6000079140e0b030000c82c18030001040418040d0b0810f800040c0180039990080810210f032403103106000e13600000502e081e214036400e1100040000c540d600444c070981c8a9448a40d4131401c28050980c10290501c0c0c2c10b045610070342c0107000b444100e080070304c0551598a5041700c19038074000c0032201d42d07140e1400d84286000c00314840407001030386099182941c6194030340c0a140101c9600307055503081c08410282d8442c58440f0100103840812016414003000544058500162030311241c500031401006040080c0701a00c0421034594148019000403000030400c4c00b002c0e107401c11100050240003100742003e5840c040c1081c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 932049388 1250 932048138 932048179
    0xf0e0f060303071424070c0210200609010c2c220920010c030302160b0708070207050108040305120603160f0503012712020a020a09050a180b06 63
    0x282513a2056041481080c1d45265a4503201d141d2080384610404030402d90305c1041e00f1302918810340295881030341d6035480381c0030408030555036500003080c000c02c44165a030000b210005800ca0082c20300c014009414620280c0b0b0031510100200d20401480710000b48000300070300c0c0d0303c0d10164004150100c4880c1d040e0001116189440d02c060340e02a0212180320b00d0040a0300400d038214010280b460140d00300000c0c001e614500340c21009d002071008043d120019009138060300c05c0030117209a40c1c42a01c0e4560740d83c0a8100252810004181c030341c810840e01c0781e410041d0780c024101c05c2c40e020000c0e04140d900a0550300807640b0035601c01d503030000051015181004040d00c14103210300031610f03c5036106841845c04081e401094000e50038124240110028a003d4a00329600c21b120407004540300c0d128500051910200030085005450480d005681d451450f03d010b881592000540c0c2c2c00e02c3c6440d03104507a51030949064480d0b00710859408100030950b03860344000156200005d04545081030030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 932050638 1250 932049388 932049397
    0x10c12030221090c090f0a0f0209090702010e0607030e060109022b0e07090221040201050c10050a0e0a02010f08070e06040b09010f0810090f110a0c0c0f0e0f060303 72
    0x4040c8030941e41c2a01c0781e441c0700c85000d01850808013580d80c03e034002001e1210100b411910032104040070404a100d02e603041e40090504003020380d005040c20fa130301e0002a03025006036030f1280140c0d111402400404428020240c0201d03040c00d04010007140445581c0e1184014400c5251003a40880c0201240e410b1070303442d580d501110600b61901440da011507a0041c0551000b002061169100100b014103030b6208440c2d12045405021403101111981c034810704000a201700c0c10800184490050500300300940d1881c00a4610702190078541510500d04507a401c1000c040b1960104080b01c002d030360484c00c1d00c0401c0308585002452555511400d42e040081c08441a411480000d00000c0001d29030740a4840c03030500340c4c2e50307100410b5644401c4415250640d2031540c800c090381d5041181c0d8170b0a6000d0609068100b40c0450080c55150340d20400c3d404c40808440492091048c0c80c0400400d03150b841d02800e001d00d0021105030800300c0038060204001c0c03444500c40b031104003107042941e003001601c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 932051888 1250 932050638 932050657
    0x61b020f0405270c030a230d120c03291203070b090708030a0909020706060f15080a1e09050703060921030b1507020a2105060a020702010c120302 64
    0x62040d4100010800f000f0383c0b4650a103d8007a01d20300d26209103e2020400e9145440c00034001d201c44035a5403208134050541c2d08946400c00c0e18012803000004060025200310075041e11600c00320641001e480c006d890300c12038900109498620129001c0f0201c6500600c41c41101c0010075140b0382c44004561100100c0000c4156032101103480c1d8200050b414043d481860601d0903259519902c1b204582d4a0207003014060125034040002d00038070016501410303243d0700491300030410580e21460a403116406410096846802c142e5620a00d034110700c683d504101960310400206070351160000d954441a00c0d030700324180c4c94520304c90510404000c501e01454110f0010000700365603103043c0c03126940c10041400060541d4035180251030292040614881c4d014100203510140411102542d501070803003240d10110186002c10215003800108800300040c21182258042a0034181d15200c0d00601d050700e624010018100140d85c4800340800c004c1c4c4c005608082d5640c0028254064054802c91 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 932053138 1250 932051888 932051891
    0xe220e0f060c0705010f0b090612010b1c02030d020a1518140303040209090d090b1c06030602090a0b07020303090103230a1a09040c0e0a0608030c07140a061b020f04 72
    0x2c2c45507180c0c401006001c0140b14500030800c6141c3ca0300340b40140c07100071988641c040c880200140484c14640b8031038505c1140c1e44000074020340004001802c00408a402c0207841540806610440c1000c103c0c3e402003c05074001000315000784c0e80c03170148031050388140c80003807511528147c1c0040700c00311050102650050b03d49421000154506a581d003040b06e0136442044d040780426141800846c0710045020381e5176800504d0340c1003050242c0300f43c4c482e5001110400141c008018013401e80e20030135001d0741c862074016948812500411038000f1054109070407c0c0030411202005960010464174480000e0070042409a402604900319a46600e42d580c8101900b40c1040050115507000e400b004582c40d80d03040d0115002c1e070034040450b4003214028003019220005000c0c500b211140b85600c1030740c08c800414030584880a1600b0354000b0f034119981c039030100d101484003020403054202c089400392000701b0021300d803101c020300c03040c000312010020402e801c0301070055490b509007a00140601910 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 932054388 1250 932053138 932053141
    0x31201030204021b010f02070b07050a020c01032c0d0906090506190207030b04061b1e031104050303040e0f0903271f0f020105090705030a020f27070e220e0f06 70
    0x3c0001c0d47c030018040342c9d100c0b00e5074005184a0700231001d5600205449d801404440300d2840103500512400d02c8012404d0700d011050001f0103030021070449803a944502070102c848107a240500400f01c03c1d08600140880d01400f849107031aa4800d0350700101e01d4643d6950300080040003030703081c101c5581015140c440346408103c14802a5046030650031441c0f110a00804001c842c101d601d4001d10709024075000f24407202034907031403103600702c0e1112010700071040e45000c0e03980001030b00d95802607014240b00503a86040000d0450b0141003180d0181c41c2d0f03001b851600c0358002130426030702c0c0160020006500101c80000c0350341c0364040d81c400310301003080c96011040ba000c6006071180140341c400100541c02c020018403108408a0003208a80014000740041c040c02c2e0700f00604164803145052b08485840451421515121140204e130505c3d225158180d040002c0010009280d04414500070345201c0410011580071004942320f0040c0e40100140c2c49202c4151207045ca010003079043c2c40c0780b03c3d610 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 932055638 1250 932054388 932054411
    0x11b060e010c18050406140907120e0c0118050109170a0507030305030f0a0b030606040b0103021201060801060f03050108120f12010311040608011a060f04170604020a0602031201030204021b01 84
    0xa42420f110b0b10007000c00714110760b00d204010542c0e040c3e00a2010303eaa1a28803076280c0c0c00c000030441d803c20814140050394034000d2142c0812600984110a0680d0000050104550300101113000084c00c62000100560811001030b08603203241c82044140d400000382c511240f1014400f604185611405480c0c41595904000380103800540780030b6641502c40000c80c070384010b0ba210741e0b000f0400c041c0c0604003954403081080001d250725942c2c181403540030060f8903a045980001c02d806003c0c40d85404d125541082c2004200d1890195071800740f61501d8014003006a001500081c0c0c1a45140d00664840701201e401d940b034028030131600c0301e0781c41000c0040100038101ca03042c05c2c2580155010030604d6580d44e415030984450304c1812483c5882200f40d9031a5040c614000e04054600c0c0b4080b619240d07980381103c8034214082410640d03904000144401c46c94207501210082000f40700860909110340d11401c28800107100081c413590740002d000340c00705000046001d40b0581710008019841008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 932056888 1250 932055638 932055647
    0xf0f01021c0206150d0317090c1c050c0d0b010e1305160504050718050418020a03030c030201051303020613051e060a061a0703110a060f1506030b011b060e010c 70
    0x29600f4108524080304903a045003000b0300d02003d0780d44c2650b07e0a240030700381c0030010005080580303060324502038900c2410135511020041840e0040c80450081c000d40c440c14028100034030303000e43e1445104c0b400415000b144004600c241501c0003408500b9143d15120035180c41d60b0700901c070042050181c5d024401910804280300800c50f0001c2d00c1c180840c2c1d0702c000c0100c81d5014144040d0541c80c0c040041440141020382c411000069402013190041800da0005502e4200e00c0d4800c40008503c908680304043d428050a81c00c02104804010718104c0340d41c0103501c40c00000c02d4040381c0240c1054180038444100b040d1052a50501e40e01c20718010342506e0240c4814080740d400503a10309000000801030380c0104400400b92900c000c040c100107040d6000c07242030741d000300d05002038403070514200c0c0403c540707120301d00241c0c04040c000100301903105000c0001c2841d56009409052404c2040159660031110030b030b07103c50000780405205c94881c50808000e00c95130481c11981d61a2448185449800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 932058138 1250 932056888 932056891
    0xc1c05100803090102210c0715020705090f040b07020a02092d010308031b2218050601052a0604052a0f1002010b090a020316030b0f0f01021c0206 64
    0xc186080035001e440348459580c1e44103c260990040c5d1003c4120300c0c0c2030401044030b4841d0f12130b138402c441c5406900c020b901c2c03801400e1381000080c0d02c9421104404240c041001a0091405440f041041d20b4600c03100c1c03021140060000c1d180007038000008680a20a02c044502c40390f004081c40c06508100030310a1121800301c0500e142080b120803084880c880340308556040301d50000009146981d60f03040f00040b8901c00c0c01034070b441141444004401625221080c8280f80840101da01c1645800030034040510340240f024000c03807400301405411399201301210800e00c10540241c120b80d040c508942e03d40361641038820700c28010b82c0b00b4002000b030302260705a1072548034448010552450300306040c1d603003a5061016400302225444a000381032510050409200500002a001c4498000b04250407801c0f11a1074890f030340081084044150164204a00c041a141c100300300e00003040418001044002d0503480381c0d0b00e06030320038841d0b80300b0860102e4205d0410b20f45007a02441d0380019564440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 932059388 1250 932058138 932058151
    0xc020d0b2e050307230f010c060608010b0a0605190e010e040609050612071d06131802011101020412110a0b070b09190b0609040c050604140901060311070b0c1c05 71
    0x501030f002500c04e903c440c0e00d171440740203050070095142c6000204802490300d28441414401c2041403c404280706110741c0300244148000410002c10403000c00001001c241c2044080c0300c2e00b07004601c07604101880701d040749081b600703010324245024001a41c195200c1250103910504120020682c0001500614061001500e0845500302d08860054540c01240030b8111210030307001003407030702c1240001007582280002c0c066403074150400c10013005541c0180c8140310400700f50100c507821560310540d0420303031844107002103041c503003050aa074401c0da40f0300c46c020344070324443c114100c4a6a21011041c00802a040c1a5982c0385ca40d03151030012a170301200c0448260103032101c000b0310f0080640301000c10550140c40d0303c02a0342c0c1c1104104981002a000359040d00e0040e0000c20b09031941c80042018240628040d560044501308025044405030003407410141400a80b00d1906040c0040c2d030401e0f40e100f50851500e0f0395510303103031000e40640140c0d80c0521941d004c0143e28071140b6448280a41d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 932060638 1250 932059388 932059393
    0xa0905090a050405031c1805011d0615010e181905060609010f200d1116080d050a020a02090a02030103021207050609060904110f0a09060c020d0b2e0503 67
    0x19034141da03080c1151070448000e80150001c200704400b203580311090054501c144800080d007215500e11207040482d4100d0101e407141e41d5407080009070035500c0010321b4507184009c0104018034000c249144060105113609042c000740e41c0f403c6400382e480d2404c9424840c0d031041965064031308000d0468501c1c210400100256281c0b20101ea5942450002c80d4113980040c0c6603074884801c4130004680030f0004124140b0b0b40c020b003604c0604404030031b00038840c00c6042641c8074491a0111440c1c50300b4110005107a003500b9050300c00070000c600020607040c09107402400c29544a0803000c0c01681000b00041c2c009612502141c108140354449130b0246040c0c070300a0343d440641212506003140e45136024020380f80c0c005000d10402c0c6280c5001c070020101d103200500081400c0c510400b560300306c3d4104d030702d0b050b0000001240c072110003603000b0464002094a45024045440300e5000b00b82400780013840908140400000100383c421800d0390000705901e14204018219601242c8110800240c0503184c40390 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 932061888 1250 932060638 932060641
    0x50a050105070e01140f0708070303021c06060f0e090402270112150c0210050c07050105090303070e1c170423152106030c03030c07080c0111151504020a090509 70
    0x4210b21040e9042e1281b52403466261401c0394566070451717001244210200741e001c1100500c0c00c000841504505110504041504d0341441009445480819000b00420005894035140c1c3c0d0b64006542d9009030b010b544160101581150f02d18150030240140a030b2000150000600d075460700c1180c400071802450b40510074104e2040c80015039105e14202c0005030300000c3da1003541c48280c0d01460700490100c0501e4900b41107581c419007501c008850191a5802c040304100c03200d90041400c40c90700c00100c0f81c0b04180100403030210150000280051300f00d8000e8035404104964400441d4080c080500f1a040c50040401d01051201910400c09002c0c4c20150254616148000c0949200c000303560071181c907080e451000c81c42500d2000302001e900d03100d030701200502500c0c01d10082506002100c007600d052818a12220716069501001c0da04102071031001501448000c90b000001c01003521800d91917441d81c2161411500340c466195a0082c4006140074030680c02000b9541281c40030348282a40c3e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 932063138 1250 932061888 932061917
    0x90a1b181203020606010e0109080d09290a110709051807090b150c0102090d0c080105090303060d020d020d080c0a0c14010c0b0408121311030a020a0909050a050105070e01 75
    0x80400368000d0144c1d0000001c1101503018409500b02d030241858003003512a07480d040285842050701c0c403540400c003d03a800f880101241d03503510181d40000300c80400714071111340b0128401e02c107030b82c3e1590400054603902d56843c4002d20028005040f020428006414201e422040c1c00e207002d202c08903079100340e000005800b40140500400e00100500c0040405003440e103080580c2c1c001400c50b190742d50f0030000c540c007983d030300822061458001d54170b4401c0c1c10700380b00070f032402c40301e010744008402c0c0d00c1031007045038a0740c1c0e00d201c1000c1d199051340c2c045124116440030800b4110135040080940c2c1d004180000084000a560501913025181c0b5a030016540e00c4000e441c0d00d0007061881c0010040e8031050040780307410350060f40140c4503c00091828020081940b5050700c03d07101c0c2d56002101d8141ca4090041e001d8003401003031b01c200d0141030303000313900c0d40080d441062611584000c1740c0c40320034000038000144060602d01d90044000c1c03010b45080710004100703504204040c1d021602141c0714160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 932064388 1250 932063138 932063159
    0x31b060a0515010e1f030b01170610030e013327021b06070201060501030f150513060515070b0c03010e010303140d09030e0103180c05090a1b18 63
    0x10b4030301c141041c0710740701c00a00446201283c01d074455003051280a1450400041103104c1000c00b565503000100502c440c00010705440030302e20710550b1903100006100d0b6039902c43d000d007298102ca90070b00103a4040b40409031409041c501d0380365410054048a041c4c402c4600132411040030300c015a40460148e01d519554408021842d03e0100c800c41d41c106c2c0d0340c0440c1d4168002c007008010400581072100d415600185008021038503040180d4503800d08005550b018058a000100e0401003441b1800040002ca0034001681c45520321032101d070103580014110503130010700503001c090060700078030103400c1c450b03031042e4401401120700c5540f07040010510130b4030f03006484c16038150317014521079a442e50b14129034010160b40a840a02d8082240894110785c921540741524800c0d08d4055110203540000340480e2002044403410400c180c03600c0000400c4030fa006010b494045551b0882d645420001a004007840030743c0f910815030f501c00e0303551000d030070040400d8108a49910078070010380310841a02d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 932065638 1250 932064388 932064391
    0x7261b130605033f040e0a15080c1003050f0604090204021c060317072a0b040602100f0b101b02061b1b0607021023040501020c180c130305031b060a05 66
    0x5a009405d0009000ca0f8210000c500d03000740d0403441c049007004000080182031000c81d40f024481758044c003101e05082c145001d08004281d4036007000c0000d4035000c03101c00c050010041150703101c2d41d82c40c000c4a007107680d642c1c113584100d401da2901d05025100a60410001c00943c0016171f181b10b640c1100540e041c01c2c00b0111008550700000b14100103003c0183c4507400d80b11a01d42c4940300f50001c40109a07200b40c2c6e40074200074615603000303080205401d40303180210342032490384a00780e504000d000c003050340b07601340001404401d42ca0400f42c00b14082200c0070a200c00703a00020b41c004000035507031170b10052164054401d220341205a910501c1e0f4850581c500c40c0f6038802807500034405000c900301514000441400e241e02074240f00141071402a00101640c801250200c5912004030b0180700650741001040d0700a0b4050319940d20400e622180401070660091051340d00c1d042c0040d41c82e414807020300121005540c00170459031200440c039210541081ea1001070000340c0316030303400200448101e00805 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 932066888 1250 932065638 932065753
    0x1008330702032223120a030e060c030d020c01060302010f0e0a0e15040903080129030109020901120608062212050c0a0507261b13060503 60
    0x118500409001d102400c140f07107031480c1a020740140000034850101040c501d0180024089000e4440c0408080200039054104100341030780c403040641c0c0c0029041075543c503010384d040b540c103922a140900441d141d07114120322620f91a002040e9802c0e0050150004001e8070f08c04d0303c41d940c0c90b040d08481210400303070f00340c40741e60311140145040000e80d0582101175000f0503a00d02c4085c040c0d54010108055409900f4110700044a20300100141c000904442040560b07400105001a03030188a81d801c82c001802071880b17075a070000e0508041e0317005103031842c920322000000b8000036607600302da2500c0b88000c494641c8030315441001d0800b0b581c0b840e0450f045169000d4032811922680720300c120fa458021203030208041c8503502d683d81c04280d041005030010090821380461245105121040c00460142e41e074210303501903040d4030038490500c0501d2203200005da0390300840401c0a00075074080c01180d8172440d0140100401108806c4106d80d2589013842035501c99055044010070b00480c606031840407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 932068138 1250 932066888 932066893
    0x200d02031b090c0a020a03050f040506030709080f0a020f1c2f01050a1b03091d060f0105070f12021e030a0e0a0f0e1305120409050901050f0c031008330702 68
    0xb5000a00a401904082030744044540c1000d40701d42c00303319207a100f502c1d8000401c480580811030001c0402403040e0384940303000038051009203036000c54030011a00d07117024441c00e200e4108141c480002032494501316088145c100c03041c4000c00d2070403250007e00ea001c2d201440031004600da554080e108884001c400b40d9a8060032200252200d07555115480044003082040000000d10100c0f1460710a140c1c0800d803030803545800c102c000c201452010841d0207060220074888500480d42041103100140c1e040f040c2050342d43c144980807402c0c0303403400c40d1207013410482c140e16038802c81000010b000120344a8513811030304001c01c0c00700501c0200910550403540f03040b003401e015101c54400030540198070610200d1119000742d40300350070400005400c569085000c04c3c02c03c8614280c5c02100d400c01c040c0c02c0204800d0400700440014103100500d10b641016002004c55070184a4840b544014403500c800c0e0b42002d5000582040e8500000c5200c1d07040e2030802c1e40302c580a520101170305001c3d1403030340c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 932069388 1250 932068138 932068153
    0xa110a03080a2a020115050301050708130303091b0905060904050d050a020a08041202130509060a0c0e0a0f0602070f0e13020a030f0602090913200d02031b090c0a02 72
    0x1c858001d085660480c040c11045014101c160200c0c3da0302c0c40001c0b201c640c0000c00c00a05c0c103401002141e804c1d51116201380e04010900c030115811803141c40d00041c140340006d8041c01c6074103003500a404190300040000034001d2842ca01441e009200100340d480e084c0c0c0c10720407074a60b142000034140b001ea40207230082d0441182008110301400003800488864016200e404c00d042d2114012500590b0000c0700c1200e00c100d4000441c98854102242c0c8002480100428101550550340e900c800401003150170b13607550405544075000350312a804500c0010701741c061a5854466035501c10500b031181c50054071400c44040380c00a1040030100544003180540c540594580c011125908490a416038001c000d005020001c03072155045154018080c503400340e51104600c0a005040c11b009041048080c2000342030000525000d00d6010880310050b444101d2051180000308009144000250701d0b00c900849401060394400340d1303000e4810116681455981c03400400c0710a840340804820050f0025107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 932070638 1250 932069388 932069401
    0x40e0121053c010204080606061c0b0f130903030c0f0503061c0f1a06010e1e01050c010c0c02030c061912060905070e13060f03031b060606050a110a0308 67
    0x55120403800301c41100c002030700c01005001e00180c00300381202c2c0030340c0d400040c184010b510801c2038940046042d54114501140030300007400341000c1121800140ba20342c6181400b5686000744400d40f0b10004281003048a1100c9500c401482881c0382100840d0400d503013400c0f00c5001e000000a54601c580f9042d10310307554502042040707034001600c0108102c1d000038840114050300407070070483e8440c003541e0405401150651b0340880e00140254100311001000e00003641340c00c0d902b500240c2d41907290101c444003410040c1c170240a0075166905641c0317801480101a584111000c1d11580280c040d0b070041d45450040c06202d201b420078811600b500386800e1010140f04405000fa1000c0b4164001441030301c5100142c02d0b41c905503140c2d00007403c02c050010840c9010741b100c6214800d10f0600300041032030b0a1100355808014800034050294242c00300380490480284020440d500c01010030482c1d865440107042a0420155100000d007550076a0383c1038403000a051800c2c6415854076511550b412 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 932071888 1250 932070638 932070673
    0xf23070206011409090f0105240f0607230d030902012309010804080d1505031915021305030d08011d070e090c09030a11120712030c020a0308040e012105 67
    0x14101d0035046c441c160340204059400e20840c0d0142c1c442c00608880320440d60b080300c85000d10841c2140c4904034000c0700020542d00c2100300d0314a0340d442403000021001440c03000005000c00412540300f405820341c0c80781226415030000051900c02d884841c650820383c40198035130b03101500402505542000210801d41c041c10441d179029209200451a010884030240b098400641c45210548403900c2c06111928080c420241d42d02c61042045140c0b001d140c8448164059184a85118590000c0c900079042c50002121002d008040d080700d0030a00c0305080101000024401c64201443c1e510041d030701d0554242801c2d02403403007a52480c603407451107030070482e14140181440e000c50004000740c0544d03842c18061420303006c0c0903041814007415070009110702040e1038a41c513581a0004842881080c48006898051640514105d050a202403010507181c08450f04040d207061000706000031030318003001c079281c1a10304801907102a009288080205241c0b204d10081240e0041c10100f000403416 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 932073138 1250 932071888 932071891
    0x801200c0718090c0605090906090c0904060e2a0915070f030c03030507091211010c052b0509030a02010e0a090c39030809010f23070206011409 63
    0x1000203a410301550b900d10100d518441c18405401c0b01c0d15070b07000e041806002200c890007000b8601b085450482180001125824018000d0b03101f1456140866a5010340109507210601d014008000e156100c40c501c0c0740d1000126803d01da01c40011100e22072620f903241c10000da4031000c00342c103801c0280480800841c1c049003a444e02e1074032814401e400c0880c4506802d05038444c000c1c1c50315108401103040040540d00003c2c450750500c0003600042100840b8040307920ba80036049030380c0804034469400125040f415805000c1e050744107041c02001221441c04d10400c0e0008a0070348026420604d5205a800d03010f85401a17030f154000a00e1000594025480512401402060604804e444401d0b10086a140c8159038000a1043d014085080f000e90701059008421ba6907406042950504075085105809002000c000351140401c0544009410100d60319500140078070542c1450342e02500e20f085140000540b151410010640150011a445040e03800150701c0c1c104d540140d20034852107420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 932074388 1250 932073138 932073157
    0x5030a0b150a0f080c0408030403030503150a0f0e1608060909071a0a12181707051e16050a2108040306150e22050c03060c13080120 58
    0x1480341582008081c0e80008001c001c0c095211200803407821072008041000051544007180003c000500c011040042910b044a60520f00280c1e240d558901141c5500c0e0f50b40d507202e800514010b0042200b0009032415410740300007100310b01c0329035079805101d002140e80e020200d0200d014040402c116081154540364046103400c103c9002a03030b0342000e035400302c03c004008d4034101d0300400c6005910758080014400e000c600035040c48185000010705034005c2100300d009040c1c00003403100c00c0b160510041603070051030f04841178413243c520001c2e03d8001101d2400c42e2108600a80703c00b500007a5071030740060281c41c13028000f00140783c203002c2411905c2240070681c1030100c0e0149850000241144010000382d40b280c0b9004c83c0c510940d80c154581d45201c1c4c2c102c88043c41d0f001080181c040008000000000703c0d4008050b0006c1640c2840790410600d80075480c3c2602600040020514407900140070503144e1802c0845803c2d6110052030032580510201d4400080d90907811025100a1000c0d100140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 932075638 1250 932074388 932074399
    0x603040b0423070801150b0301060509010c0618060c020d020616051b070f060c0b04150902300f07090c0e0a060e0f100806040e0f03070302010213140105030a0b 70
    0xc54a000e4020202c2401c42100a40d021480a001c80c4400303020391450300440800075000700d420019145010f000501951040107004209044941e2003465498a038903004802000500c0000c6454629042c540340e043d5072550802c400880882d100140c0b9000314031599000d000e881d254003050260010064203480d08209003440310280c071200345c21400d1501b03602940201142d03854200101c40c00c41080c0c2c00744046c05811841d4101041e090440035034003a50143d4100504040c80c18480014200c10314040e41100300c02090050040c55068442a03042c210440c0c5020503041c41d051a43e210030100c080d00140e0890403042050101e07940003c03120602e01d00f04000e01300034a0011407100750319a40414005840312a428610742454688003c0504c0181d52001101c03c051002504480b00940400d000f01d42d9030307111801810301031003074549986e61082074036034070030b56401c0c024080d40154801494800c02940c001071004001503803e5607044041c1c454604550710f0348000300c01410394250454011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 932076888 1250 932075638 932075663
    0xd0b0103110a030509060907030b070c031202071a1807030209061315030c0609270b0a0f0503060a0507080c13030b13060e071a0f040509010b270603040b04 68
    0x180c07408005441800b81542c1c0000b101d2518500041c50710601034924811600b00c504203102142c90100803d60106440c28844842212442c3c22940c4ca015500010a40c82c8040f0700c660410021182ca00b620182800e00700d0343c16290703e86040280703104100c51801544c4201410401801d1445c3d00503489180204108008552407a0003001c0d1005000395440e50070681d0390a00411a1f05012a8098280c42c42c05000721418141a00d00d03904451181c0950805004031449a5400e9908003011a100c06003809580d0390b40d40300101200d28050065038400d0081c00000303100c5c80741c0f51049030f2089065070b66039007007130302c03902070500d015800008a040c445610b50070110100f9001801207018500700b5002c910b5018007801c02900b10744100d07030f29500c182c2100c20708000144144400ca00c0c0c8295201015a44100c1d40b0508002880b0382d60000c0e80180034080001040c8030008043805000d0142403108180c2281c2006402c1c001c0d0309440c0c0c0640c800000c1c00401d0120354024155039000f40300d4090029078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 932078138 1250 932076888 932076911
    0x6021f02090d080403140714010c1506060f0e0915150403060501060f0f03200d06121b21170f030405010911240d24080705010804080d0b0103 62
    0x70380003251003c0d101e26000240400c10400c0c2c060408441d010100c000c0d103da1410070761002c0e604100002440d042015125641c42800080d082c80c51484001400801889640b110064842d0f000502c003040800e4485400849a090840308035204000c500c1c28800903040c020100115180a21207003d64040c0501000c00090164442d15002e007840303403145c4c441c014a12000810601540010750101810640301c0c02c4446440f400e840040c249104940703840f02c000045900092255500c0440c120100c2c0d20520280000f440c403040c1009003810300d4046182c0c8801d508240c11510003115100c0500c2c400d0100049000c0d1a42d58400808650301c0030b141240c0340c0c0704443c494000b51010b81d030f16551698260204000300850800045007a50182c4514400803030f070060246101c00c0c01403401800240e562003c00007a80075003404400e410b62102c0e58005654640b440c480380d801080607034400c01d00007041070343c0101090791041b41d018002610700544404c0080c050a4203900303040c181a02c1ea07004944 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 932079388 1250 932078138 932078149
    0x316050a0803011d0a0c020c04050c0d110c010c0509030d0509040207080319050106112a0a080607020f0613110f09130203060a0c020d0c0305190302031f06021f0209 72
    0xd245140c0c081c104e2086a4010004030080a402c60318101d103072085202d12907070081240480341c4800c44000801d680c544800175640c1c883c1d0141061240c3c58620f21101a0128030003400304528848000c0007001103010087e40d261243c110402c2d40340d8003100250709aa0711960050090800203400507050a01300d558142668009907281c00090303c4500b181c002e4000c0b40c3c420b00340101450315150900345c0f80311300301c2d0351180c103514004008014480500300803000e65041d4070b002c20748041c0810504540e6810119280e0340142e641c8001401060b8100100f4400016500c3c000c0170103181c07030380030300c030b003d5031040301c54031b00440310b6070308074169424541099440a007003078401d0340e0314480b81e5020100e40c4105401d180000780001e411500c0c100860002d01c4d40029100d1801c0c41d035041510303180b00300d401c0039130340c82c0038003550201089500440303032414540c99005540240c2c00200078429580a2a501d034529101034001c040042c0d00c54800312050501545c0264910310365010014039000d60740010a8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 932080638 1250 932079388 932079391
    0xa11070806060d1a3d0b2203060519050601020c1e030714010314010f12030504030501051f050306071202030a41250e031b01120903020316050a0803 65
    0x403044400700d4510420040c0d2400780c0d0468402d9244107070146040c02e40c00b02105c5c3c1440c0508100c4210103e40a001000100000300100c1a40301c20003040036a40e02d448005401d04444000a08034180c0b400c0083c541180030785806058140c01528ae4901d411050040e501c2c0040c80c0c01c0340e0a4039291041581d510244101005009030380c460043d208212000901598085614112903a800c0c81c010001c442008130004290340d40c0f12442c16000200c0d060440d01341c004ca030009003241d481d040c240191599005070046002d290071030041562a82e071800c0507220b0000b100c0b00c00100b586a0032220005281d68015548548421000600b0f840c1d00c00e840351400004501000200700c11411148648854032005c410290782a03c5000d010300d01084102003409050201003c04a4021400c540c440e0040da070040c0580c0d4050100e0318102494000740040c1408040c02f00c0c0820025468880400018003e02a0094040d00114940162100c1c450011480780600352401c0c05050480d400050600c001035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 932081888 1250 932080638 932080651
    0x6020415080a0501141309031106010e09100b1003090501060b070302010905010b060c0304030f0201022a0f0105090f092203050a030f020414100c0503030106050a11070806060d1a 78
    0x407016242250805040f00c0060308103c4001d140c03802c200b0b00598072030b401d0008000e800c4c40045801c074a107240036110480e04d01e03948045401030000100e2000410b80381a8031540c258401c58581030901d1146100300c41840c030b031094100015080308110540290060b1034283d20400002448075914403040b44035420280003140140d450311807041c1071281c00d010b5030034845000c0b50550720382a403400c1050b07130381e214600c070040114890b44d2403081560300900c100010b005e180f401c00c03407245105501140d00390103000201840b83c1700e8202c890041c2d500c00c03c291030182d03901818801c2034800700d0080000d590002008140462030113052008140345d0140c24605441c370030b849043d10b42619941c05000ea4140d81c01c01c80002d0b105001c00c01002c40d094140910070b0341c0c00d440b90300040f5440340c02144c5128240310702038810b100c000000698250301070002c0c625160159034801004401d000c00a890315420b105000c4d0715808400440c0d52403420109a8440511403844450301400100c40e09019800461fa003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 932083138 1250 932081888 932081897
    0x306040e0c0310020a090f0f050120030d0e01150b030129070c03171e09040f0e072d091d060901091401020307020d03050603031e04170307030e060706020415 69
    0x82d000b0240c0046506d00909042c49031009410705007898885407120b00d2207428100f1030a80d01c012484064808402c2035003840c0f05c20b40c3ea8407140c5098185c0600611002c4040703541c03034400c10b0344035009035201040a41d001ca41400d49540d2a10900c1d01d040c40c4400000003900f0112060011350b100400300a00e0796511420b0f4456042c0d1550404074554020f80304034661440c000c00c0366007110014000d02502d44010b00400e42d0315040000301103801010740c41c8505014520b485d00690400000080d240111014030992100b2440880342c4020381c0903079828100310422449005000040103500324031004035400c070300c00c0100a1005482ca250900680780f44005035582c81000c0c051000021041440301000d10081d49542032100c80250b49004040c0d0341400c1503a110003280f01070f94244121003420b46c600d0058210041440310741e1032150320a200b201c800d000842d643c444080004001d03500810340685410625215040a1000d950302c42d00b0201d4003541d08000102e869540400828400031440d41c2c1d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 932084388 1250 932083138 932083147
    0x5040312230f0c060a061e1202040c0903080c1b010309110402030405010b0604090501080d050c0307030f110d0e0f10090909062007150203060a05010507060e0f0a05010f09080306040e0c031002 84
    0x10041c003851104120980590a2540078010500249223102010b0f50545000900ca000c044003280d04921580004040e060005514001030000084443c221801d005005014003072410041d07048581031403008241141d018145002032070164041c540c051301800001c944aa01400000d4207039109410074010141e4400c01030190303050800564a525485040031460000208000c580d00e00600c00003d003013240c1551541b90741171140c00850070304d0111000700e40c1181300e6030700c014211040501c0e01600440101403200f0b510f1030254910080d42c5500d86800800701d0410340c0702005062210410b41d07400e07488180550070564050f80710101c2040540c0b4076501e60515243c10044144041c0c0e104800a005009004043d03850304a46011140c0900305140d40ba8801c1c0f90039006414224180d083c40d001e0344003408072a034000305502038080e200381d000700280b01c002e022100032550984000f03401c00400b81b0000701d060815620a80254400c0c20071203520342100c5000070700e030181d00d624a409250700410b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 932085638 1250 932084388 932084399
    0xc090504051f1d01050f06090d0606080d050a140a08180c0d030e01030b040b0f010f26040b0a05090c06161205091c02130b06041505040312230f0c060a06 67
    0x510702e0140004031200081d006c44080080c080e401021000c46c41100b40308494003c12174075a0011005107880e0003a145074000043c00605103405c42c1c603003035000c503608240300c1c030100ea2074001301c030711712a108d4540701c24507107521043c8102140400081240791103034808004255468034a41d0221510954410030b001040310001001d54021900e6140170b00c0c10304004603035643c3c803e007403462801402e207003407001300708482070444402020000c81c0342d41c02c0d01e100410407a42a0004a1440389020303030a1855a500d0700d040e0070080720802c9070801d0854000f2200382d400c0c0e03c1d1980c000e080c000180b170045902e14015840c0c00d90302d00d02480d0300002240001030018010b0038042d203c0d4402410140646400c8840c41e00401d401d44c0103640e0441e04c0e5030313450b4192411135550303000b40d6015050f01c0c262400340c0581040042c010340e00602065400010711450209010311900006c980c1c4820201001044541d29401c20b690b0303049010410241035041c400140f0003003080080e9840340d400394401182039881c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 932086888 1250 932085638 932085689
    0x9160b0318030a0c03030b0105090a140a05030a030804030c170d0f0509010c05070f081204060b15071a04030908011806060b040501080114030717060a0f0c090504051f 73
    0x25207415403904284000010300d40c1118500100d9501420040703030314041c0d00e004032901c3c468500001c0e0b01400a650219210071018090345000800742d030a14006512202090340e1400c007a000107001880480c00607002900c00c00c00100064440c21409003d101080c0c19680139401c100c00306403280e9950b12020305c00700002d0044540012015008000050080ca0010414490600003401c80800c1c82849000c00c5a440100d9941c0d41850b40302d40168282071071320801a200400c005446070b000110481d0f080083c7e101120307160741d4800c00c8003014044a280403000301c1c400030016070501005080c00a441e040a02aa00700e00509e40c40011049a40b85850300484000c0d421401b956038040c1300c1440181d03004801c2d141954422070100200700315483c0001d19103c06038015948203100c0c08828010144000303550b40c010f1040d15003c0c0400e46495503036000f146c400c111040001022058100904c7c06c250748819008010b2a8519400404440a0700c03180103141d4042c00114032840030102c6405c400d07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 932088138 1250 932086888 932086921
    0x2220612030815190e0c041205060430081801020d0b0a091109240f030621070b070614071e0206060d11040f1509060602010b030d0809160b03 62
    0x3c0381c1340140703401c0d01c88038006160f440e400f512040c4410400824000301018060341c0040c030600120614005892815030344460003610f042780e5109500541254a2000c1c2c54200c2c41d07629007042d0492a030460400403250200c014002c90000704408050301420042800100441c2035002c501003400354800003804002801da0380485251407901101c901c680700705a0031900c400804070303407491003008a01c8610a030851700783c1662010420000d05555035118160207140700382c104951003600c444030700c0e050705180d031300e00024a41c09810085090000c005808050040a8003c2c14002044203050190280300e50090b100c002c00300301d25000014061080000e00707000c0301c2051010b450107040007004261540d440321001004a440341c1780c1c00840341c49039400110107410b61181440446101c007000250700411b4020001038600305140410141e00501941d940000060020030840001c000d00303d9240a000c2c052902c07c0c01988814003182e404650241d0140c011922187d60320f06201b041c0301c030107204 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 932089388 1250 932088138 932088181
    0x81309061a07050c0d21030501050f01050c0a2306090c040533010c0b070c0c080109080702090a1e0e0d03180b1f080102091003020304022206120308 65
    0x1c20001d002c00104003162503813843c24281c03201142c842c0c00746040c1540c070001d0980e5000042602000d05c00807035050300018101e410a4490364154204880112098800d4000418480d401010708a0004403c5000000c001c0301c10b000a0b191280e41e444402d041840960300421107601401c201c03071003032409100305a04202c0303900a08490805010140c41d00d00446400c031014080c01208496469020780b1603001000d5004a9080c901d151160300505200401c05050350031680c038240c0410284414490b02e00000e42091000c0c1c24210141e003040000c08000740034099041e1644944c080c0285000c01d00322817005184c8000c42d88070704945420f0301c4c2542e8241a00105420106a680800c5c1c1780c0418805441e0810030800460f5181284100503600d40511103610012400c0c00040c681010350290260100031101c40e4108100514110140e00007554040e40c0705000b0058890040c00b41003400e12892600f46010030002d644030035460103807070384000c190007080e005010047c0011206000440004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 932090638 1250 932089388 932089439
    0x103050114091513062705011a070312021207080106021b09060a0905160318020904080705070e10032303040611100f02090907022e060b0c01021c05061003020708130906 74
    0x40c50507448821038001c0d275941c1e1003103280c00182c1c0000e041c401c030b42c3c600301024001815503480c48120a40d00300618200c50f4040000c1803440041340040c404a4112120007002e5070000307103801d502080100c0c2c1a8041d0410342c1c403144140000071940741c2030052620400f0150659800d400e6094005004c1c6c4600c2c06542c108985501c1e08000140d45a0303100e50741007a000700090345c640d8628a132061a0403419000101b605641d103040211090340075070802c00307a0f84110321816900e5440002c0301428048608410030541040c07005000f06071003440040340c3d2602e41c40440b00d1400c00080710004940c620000c4491858000038180040c0c1001c0d028660048101e100501c80f1f03408008042a40c43c24001015028461414a284450b141c2d500010050040b013100540d440700c40ba0f141600079880042c4200034103a40c040030101d501c62500c03401d0f10514010707102e00380b0540c05400440c000d41c0075800840300d1040510650354400304c51f441d4007001d0000340c03000040300c9040801043c2114010407190f4140b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 932091888 1250 932090638 932090641
    0xc0809061f0303140702151b07080604030e1f08160f02300c0c101403191b0e01030e0115150207081009020103050114091513062705 58
    0x4915045166046940600e0212004e42004804042c00d12440001075030002c0310840344801d00c0d070f1f036000404100e054101805100c1c60500e000544842845c41000d107260480d500050100f4003e64048200441c01000608004031060f2903044841c21400d00e28000f402000030000b808201d5050201e41040a080164540c2c600b940c0095803000c0790601c1e0305244040454518651001c0740e10f9404407140c181e440381e1604d02e900010340d51a1443c049451103120401c420300f0303016006681601143d200856128595a2a40e0023074130800c43c1d4405410106590b20785006503413141410650402e00d4555813400d01d4002071340010180c468503200c6505991500640381815000030070031200700d80c1441e018036980280740b10164282101035005003e54007460030302182e0a200b6034055690a8401d81301041280d807201901003d82c00c4204100b45c0061032a000315000340fa1030003144009001c010034104001414403000020b81f1a1a4009100081420503480d8072418104412a0308518a00b04201c1c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 932093138 1250 932091888 932091931
    0xa11040f051005030c030a0e0c060c100614030a030c02030c150a02060115020d0e030114010609031704140108090c060f070b06030604030e19030f0b090c011d01030b0d0203010c080906 80
    0x8911018142c01f04e00317640c0d100e851141000901c2441d80a0000510503034403008410982c0303403a221140144400c841c5412804500c240c3d900c0d105452a0300068010424440e16a4055912000e50301d401d03a803510946844031042e80c0c3e02d012614506204001245e1a412280f0001c1e16214068000c100d170704034011001c1034210707400240c0303181681c610b10344121444412030101e401019000c0004500807a05c81c0003003007c3c0e4120340b24104403842071000305148250303a1000d00c2035004600418001c1c00d07142800c000e1a60dc42c00e0406d8100300060156840f00e14082c0014001d6845030000500d100f0022600c1030034000e103203110b00d0348001c05a02903d007a04d007da0b002400070f01c1d2442c0140c03150b041902542030403842800e480c000f80d540700d051038800e42c526040151450b0300c100c0e81070420f0700c10a002072100754411441e0040408803507202c04c80400007003005402801040020705d820164200e500009a40d09008a0300c07808072640b98078141d41040c4810900309035001b80fa40310602d01c0910241c90 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 932094388 1250 932093138 932093161
    0xe0105010b180f01020c061b07080f0f01020301030c050103020d0209121f140f0702190516060507030c080927070f0206280b03010f2705060402090a11040f05100503 72
    0x1080004481240c2d03200800500d01001d004400a0340d00c0070700c6003240202cac0395840000d100c5240d141900841d60030000046140e400d03072009000062070b400810344200132650003600603009588458002500b06040880813840d40354903c800c103200c42c5e0143c100c0c2e900f9030050945108549407100c005102407840c40d00002000e6002a20201d048400000002e24241c402e1218a10080c114012003034110403900301166129140941c0784400c4004d9600040c00b240502e04a65515505440d01028135002e602c41d018a9000304040c9500301d1202c5401d46214014003c4200c11001c0030302c0128220b0518140052000703e1503403540066520171402d1020a49030704683c0344488100d03180d0303211558081c1004102821054047c03540560801044c0302480c4503c2d048500c0da0034032844032400116280e40c40c10580c0a0b00e0b18080e1254000d1400f00c2c003d410020041c0b50301040c00c800100c2c056204003580e44080e8040d901c00d00d40d031800c000040c4514a04199035040522951070300e2810340c01c1080b800c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 932095638 1250 932094388 932094403
    0xb040602030702062503021510061b1b0b13050607031e03060312110606220504061413110603070909090201090f1503060b0c0304050d03030e0105010b180f0102 70
    0x78410300001c1060891580170101100c019102e541c024040d01d505450060355880b00307540e40d5125130804900044441401000a0086a146680e04110040703043c1f41e259442d02c0500741500c0a4800c0c0201c01f4100d02d07124070200081005c4000030340e03154421071803000b4454040c0c00c000c0c400d41c000c00020780407a60204510a0980c00003084024035001c100c0141e006000540c002801403c8030503071510710a81248001c8003407414042a180c0c0ca507560f1042010340442c0c002e040d28220008015008801415808560f00c1481018001803952072804020980c500c112620100000c110340360f00c01700502d550040c01c080d50151022800c40c1095031018002000f68040c012003565241e4054066a100b00c4200d402814101e0200c1c10f0540c0b02da8402c1c1f0702e44002c00c2d03860003007418503a000402d00c01103c100c80e4800140e10165050030300303000400c03410081201050302050780350141c00000500c28440c150081032492a600e070744410740107a0a107881203180246110380d084110740352041e44c0124501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 932096888 1250 932095638 932095643
    0xc050109080c0c01030e0c0a0e0c070c060e03060a0605010503130305090d1b0e04031403091504061a010819020906190e041a030604240609090c080d0e13020715050a060b0406020307 79
    0x2280781e6180e00f45141d05018bc5040a056404920000600d20b40c011401d07440ea20025400c0d504c20303036554400b80f001e0b41c0700c0c1d109441c00140108000b840b0807070610005001036100e403404924052080d400035120300421007041c2c848503040501c180032500b00d02c6203480240b400e10620990361034540c0700540b0076010100d40300c0b66a000007000071240b4a0501010000c030300c0046040b222410a400d08000030401c2d0f04503448003080300e003688030096008504040c416041c0300308040c0000c001aa15002035080410710742e4000c40140042c542d45208074045061500c480e694128424038070904110170385403a80c401c084000031048003440141c4010034846d5015411945002c41000b0804c901c5d40e040071741c00d94182c05d8920b00500460404d5a940000300340c903000b62887c600c9240c89130503041c0c5680c504818400450010020000c00c0d08117600f611000b00e102d0b05005050803e95140e05104802544541c5c44981d035600c1003100c000a14810310303001d8041c02103480e092078180b500203942c1e4458410007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 932098138 1250 932096888 932096909
    0x80f0607141602090a0b0f010311090d020a0302100503040c06080705220f0e0f070f0f0e060403080c010f05010f05030d1419080a0b090f04030c050109080c0c01030e0c0a 74
    0x44001c2c51440886408002c2c1c0c0c00381083c0241d2030802c0ca0034000380044948507200b1160201b1700d441c0d540c07080c0a5403003102c050b60380c40c51600b42100108480d1400c0d0200490304a00c0307400c00040560b80348003c2c0440c05525032121542e920b09403070880f03e581c40540101c014000d00c3c0c402d00c80a981c0c894181e4010314100c40082e02040030b580b481342546155035000d01e05094080901240b5880c22800543c01a6107200c0b42030513988900034107995800b4070300c0035200040c00300822011442d204034095402c0d413402802b02481c16440781c40b0303c041ca52100004100aa440700c900720342c40c2d51507101d00ca0045ca5184072414880e8103000000351210a000703050f400b0801007120034481c09501000303d400d0140145610b07040500e01500240c402c5a0441e134412a03149800c030200c406040c11503002e0b00c103000300d04d1182d4a0740c0d55039500791150814110f040c1c0301590303550502c0c400500d0200081c5881c0300302100802d0b1540000380010f007540e140340044040b40d00101403900d401d4941c10041c81c01d03115203400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 932099388 1250 932098138 932098147
    0x2405100e01180f0602030a0806240a121b11070501080714040b0703080906130206040608090a1a01140d44070209061c0210030608010e0601080f060714 66
    0x50600305411542c01089900000c8000011300c680c00000501c0501040d0726103640b160b46050400070b448a51050070140803a903102c0f02c0e00c4a440d50300081c45240d00b00e00b0b01c0d01c5000041c14180c000c4445410b0b001181100c40000849665000a40800a06c0c8400f000f031440c14280300c002000740b02d019111809000b441070103070301c02c0b44015003030341c018080b10402ca40d2203a0550034014020a07040d640c0b0301c4140906030215020608d002b003044c9041d500070340740e03515051900008440264004040560394050300c0d000000081c428031900d8000400c841060b070031135040601060910f60f240600c0c2e44102510302541c0006501e03141d081038540c00d180c400c2802007103404207445110640410800c0f120800031300d4034008400360030151181c5402528581c8095031003000b448030707003103101450820b62101c801d00c080052821020502044910740382c04149960317660842c41c20342d00140c68594058000200501403284100a000c43c10704c8007500419660801c154050f00ca030300d9900d2001d144900029 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 932100638 1250 932099388 932099417
    0x5120901051e130807230a050304140a05040e070e0106181a130303020607030f111905130e150a0f0b070503041d16091d0414012405100e01 61
    0xf000c82559004803c9941d103102034540b080682d070a03030a449801603400300030f203052640c0c005010310005034001c0007141740c241840f00c100401f4038542401c0d54004140d84001c19640c4990188145e9198520020000e032400c001140608c0241600113408100c1e900302c240c0106030300c4010100440b0224407603815a001613025201280c422610700c002011405c07a4000200355000072440d1141c0350707917507007005403001400c1c1907419600c0d06910f4118041060242c294500200c10083d035521105007000d0345890340101c400700c00164035600c50302480081008000640d032903c0c2e003885606208071518540c1506140c0d200c903103248503028881402d14003164640400c0000c000300c60141c0100010000041a0080403030140981100c002d034907020461050042c01d80909050380507200a1101024914446403000e0440c1100801c10790340c0000390101900c00350000c1c8203014030310440808030700e80c2e0405c0343d4501c140d40001d0752202d0701030303143e40d28000700166219a00421001c004d10700b4443c90030404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 932101888 1250 932100638 932100661
    0x603051c0311341406070206040f11041d0d09050402040821070f0f050c0a0b2b0501060207050a0e07020a0b04050114010f05100302030c07030c02030f0d05120901051e 73
    0x69985019a9024020840c144071100c0098904e800f01c11088840039901e80108a0b2078031000d81d0700030501c0020015013000901c46505120b02a80045d00015040c0d400303c205003003001a030940d02c2c040f5042403c854418560002c2810090802600c0039445c05e4604180c543e9541903815a140e84680c01c2003540710100b450900700c64480b40c103c102c800310b044182c10820038034924024100d6441c030a42150580b10b080c20010f40003200c140c2d400003400c1c10070400340c3c94000f1007030105901882c0501072140c0c2240d0118030459018151680c01403040e00d0405061088c1c0d0390f119040084181c0c452004c110865500007008400c40b50310081d540001d0711103181c0039002d00102e16203132040000d80d00001c03680c407500c94502c90880e80103e40d01084241000b409400701c0c030083d28800c1410004000000100b03000e0034140420700c0c400390855188036445401c05050440e1180c800d00080c800040c84031350710188500d5103410500c0e100082003141812100400d4641c1c042880c0e5030364200d00c4002503060810b8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 932103138 1250 932101888 932101957
    0x321090312070813150e090925050109060903080403082b05041506051e06190804170c0604060b130c05070203070f120f11040603051c0311 61
    0x1c8002a00d50100d032500c60142d80100124083c00400c40000080401c9030380c07003190070149580c8502c0c5800d2207000034000c05c102d00a00360011071081403184040d01a025040920400d13800d401610114107200004021001581c40401089100d070000d0010811031003c40c0c1c100c030703805261075603540b04581000d515089040f181c000c4c502c0c6c50780da100c1c103060401d8104a10552003001c4595048416490762000c480480c010a40c01c140116007c01c0156a040900c0343d20590082c04503081c403c00f0150886107005210021000500395400e21003000400d00318048200d1000400c0f074208084803861070340d6084020005004951200341025154440095800c03864819050900c88682521300161083d07000d84030032400380c4030741c060008142c0401034000341500e0a59035840070031200d41d2507200d0b0401800380d054079813030002403150803103554901c5540c00940c4900041e1185403000301c01e00e040d0500031000e0704189400c040510141c40e100904a4610480c40340c0070035456401d180600040510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 932104388 1250 932103138 932103163
    0x31e070209011203021b0d0c060519210506040b0907090810050103110d11090c04031b0b030106050a0504050d0b0105180f0a1e23010f06021005061915020c03210903 72
    0x9041e01c049809c503403200081400650b404c00b0804500c0c10203030101c807155807001100051001480d144c4500c81a29008283c001600a00c0420005031400000d9001001a106c6402180e840401006150414032203554018003400b020046507240d922103214118250b01c9851052011440355010401d4030041c1c129410405006030f0540c1c03074000c2000105030f100c1c2c00190f42440701c2c1181c01162441e1100c2c61425140d44014407405c0da40303010016169070300040001000c0c480c00340f001181a403a9100c6640d0100c0c040d032290304842d49040b061200d114800b0710485003124020080046ca1041180d4943c0c101d4003540c40081c07009409581420b08440d0107103500e08e094107210044001020394030180f1541d205200300d00314140d0340c42c281d0030008000c0744154009600200c48480e41890643e0103181d210340003504100c1c10006800b000404498550050003904076040f0341c01c846280e0406c40000700c9041540200520b2020408004c450070001e40400740484000400d00c140f6101440b28820040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 932105638 1250 932104388 932104403
    0x20904150c02010510091503020108040c090c02010c141305120a050f06040303060e040b041502070f0b0403030e070b030606131e0305160b030f0405031e070209011203021b0d 76
    0x4910300020301811054850b41034640b00b00c0e402003006c5404d0711400c20300c040f81107122074005207150700564000d440200b041d076081034000d000203155010713400f4001d0001c000c1d500001e8854074444024201d00414440d45000781414007802c1c455208040301041662811a14601000e1a0080d00e5103084501b01008100740200c9807650b0fa41040003030170718011403190701c080c00bd10f62200c080c0640320754121070103041e040740480410041740d4804038810310f001030b0340c00240c940010b903140c0a030f82c0b10110100711580c51405040106141e41441004c100d404164050710310f05180c800100150302000c0c0449116000018540000641c9411a94000c00c00b4107440e0110192115100c410f10764030380f005841a00030b500b4000a001c1800c05e0380e4080d1106851580e09644641200019101d0000c10848542c842080341191083d2080d11496540050701d00080e0f482c0424818080c0018041e40454400d06550019100003600424090741d2100a50010a452030060300029200c0003040d0014000c01c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 932106888 1250 932105638 932105651
    0x3010f020a09030b070816030b0303131202090c041a090a080a0f03020d032702010905041d12071e06060315020d0507020f0304090209010201201308010c080402090415 73
    0x560402c4182c0c08a0b8062000003099680c2d45005540070b01084606848412401c0303420703d50240668040350038018051f048a051a11101302202d44107015041303203840c0e2168002d400218501410515804144002c01030305040c07415907841190040140d0f004090750003c129a01d05854145031a03008084d084119000012075081002c0200d007100000d40040c01030801d41c4199500a000b405403000c15070322108070301804071040b902c0f44800018100d0400c002a030700014196a00c1c042c0500034000c1061500c00080b00d080d2180c40c0c0301c00c045000008a40a101c00c1010415500c0c0f00d42e034000d45591070303021122161134400020700c41c0d9007004000903e81851a0b54001481e400b0b024035402510040149844009045e6136400181d4a110540c2d80100001e000078040307600135000e03030f0006000103d240740841c588182c2045540341c00014199004c240000b02025914a20004111020080000402002e00103100c050300601c00790061001c8404181044180c81c01c240000b40c5034481004030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 932108138 1250 932106888 932106907
    0x10302090306100608090601060801050d03020a1502250b01142407020f09060d1212022106010918090218160305071107140402040f0603050a11070f060b03010f02 71
    0x43d090501903500018010300c0090908080040d0544c10f82c1c0445c0c88002c660303880e000410107040501c81d4110118080d101e1004005080d01071406030383d00c00a20701603111360201c0340f24440010822143d203461003008201401003842501d000303043d43c0d140006074001c6400c40000c25003220020b0400c071340c01e06110302c10150034450300c001b502d4118030072200c0314005081d1008005155806540103680718814008000001d05c650050041409040c00d080e01c041c201c100301d006c1240c10010b0110041c0805800c030b40e15180035660700d180d001109003802c0d60740d28280604003104c082e40ba03403540104e6076280303d80001e5644e8440682c00c07040b81402c0b803007046d00e030000e02c05004e0751405030700101190514000c10718442c0146411183c0302d0305040108415440d201c6a62100486e064541d90015803c01c03021410349a10100c40e0060504d80e00c2c0403443e42801711155003110480100c500110506001e07120002c0e4264000741081d07904407501192040302c40001074010701ca401442c01640e480020b551a8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 932109388 1250 932108138 932108161
    0x31f06020109021e090a090302101518200c031e340818180907060e1e01030f02030a09021215060d050708070f080c220b010302090306 59
    0x840c4280c0d001c8000041344590600b05182c20610141c1c80b031342400000e18030301e10650014074031078003d1044072008a107280e03601d01120750342901da003d2400042424010341c00d4038603080c0c0d83e2010010701003210419520000910032000201d00313140910001d0702040c114410025900d1603007070190441820100300c002c411139030f0301101640849001034180d00b2100007404948101410111040141d0703062156107201c8954401071101d01c40c4ca14441041b105512403035a9000c041c2120869404d043c24001c80303162400805a10000400c1030704524501d00ba22520401d06110158210403203901c0030714001a805000300540603c3c01c03038030100820a48800c075400040b00c441c0250b039840c406c842c0e64845940c079000d800703000d081c90154800100321182481001c2c03840940c007404c2983c110b1038a0391485414503040d64881d207480e440e40f480500a444050045880d8000201c0b080080c500d040f01120300b0902e50600e48d01c0d44c02d56100d070300e01201d900035011100c001c01d00400351941841c0c030541005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 932110638 1250 932109388 932109401
    0x2808030c0408060c07060f090201051b19060b09090609150406020c010f020a12090f08030c040b12060907180e220620040f030602071e03020705030d0f050f031f060201 73
    0x2031b0034034288880790103911214410216190b070103a46007441c1c2601c0c0a1032100c45054480007001610510700f01100d06801642d2480241d441400003050241d0820100008440007418a075641c0d00706509004240f43c00046000c8030300b40e18031400081c2d9407a810090002d0042040e076444c29424220710060010159000f0034440200703490350700044522060220484010400092292408400c00c0f4080391003400550b0740100c204200b00e01e041d440e861810703c00e820200d00201c01d003410380148181d0f8036240c0b0545601240741e16007580c0241080424000d4a00107110f40d5500c25121008185041d815024100d0b80b15240b102400c40700d803051400b503005014a0410a00e20b0702c03620603042d05400034000302c2c1e00704c6603400184000c02d415612140001d501c0042c0c00ca690320100184444041607024990203694065000343c00c01c1450034040c103060656001c440001c104848200400d0a504141074075503040d107a21855840350b0b10310501d4000c100040d82508048440000700140e9158150040d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 932111888 1250 932110638 932110643
    0x120c11060907080d050a02030f0705010608031c0f0509031611180f010e0c0715140c03090c010e0303040e060f12030d0e03041d0406091b03052808030c0408060c07 71
    0x210b02d0130700c0104044500c0d004000548006070801c1021004406606c0f01a114070750160000103240d560b40e9440383e18540c00700c40004114441041c1110350021039224a064601e0301010901c45880c10311925500c0303125104200301d610711652044e8080c49018407690325100b6019180007074421440c41c40c6010800100c442000b5014504000306107041700151050140003840071190514100795200e0012a030440402043c0941c1d44400e0060709022000b568050200d188400356641440280607060240008005040c40441d580146664400000b1642115812240c07140680c40d40c50000b0b68900d1310540b0b90382d2042346083d45805180010000b000122104d442c10130844805484458403409207120f0501c0d0a0002e0b0403a140d801c1e500440c00e80c1c020302c41c2030001080407060b6240c25840500840005200151410a0003040020401b0040a502100c0c0039499a1304203101d0700a9503c04560040400f00044042420340090600b030714090f0900300140c62043c40c115510716400e410243e010f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 932113138 1250 932111888 932111893
    0x90609020603190f140402060307051c06051c0804150c020306072c0d060e0a022115100b160503030f04170a2a081c1506120c1106090708 60
    0x2d101a580b00d0311a00e505ca0002c190454055500e0740c0030032a158100070412000d00c02c08200c8100700c010001e070620741c2030a08600008030141003009105005211450803000d44122014a00c0403990440c01d0f102100e85280030480b0440d2501d0040310024404000203405101c3c86060180403034100d1144c5140d95200c5030040300c60403440c5103810172204074101c1c094000107422000c8020888680000340d4071481031080710100f0242d5408070320001005a083c1c07084102c00c004004c443d01c1b0600440c001d4088030000707000b80b401e01d0045160210380c00c3c490590184400501c00c5120703c40018005d8040c0e81210a03241c03a031030301d9280c08198007000c443c1160f810502030000c0030801000016a0314411035503982d07040c000400000c00d8401615154618540e000c0381507203100040c41b940c018101c101003e401701c018403450382444402e0343c020311a48211551218800e00c412548406003041d40420a480420305443c402000e031070301004112203071a18083c040400001b45000560401140c194108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 932114388 1250 932113138 932113151
    0x9050c03060705091306051f020f0102040612150b030907030302012d0903121e05010504020a05030a0b01090b0a2f070b0912061314030901050a0309060902060319 71
    0x8041d2114421601680030801c140321048a500304010384020019078070800144042e200d1001074107011051a50a01e0220341031a071840580d414000c0c018010510300003582000d060550241c80f103040404c0241007542c0d00c0310103060782401c2582c540014000e1800c0740d5541d00b040341c0c4064440e006804160055800c2481031014003001640720cc0303032034100ca03908c41030100b007008030076000d0301d10034200383d040000300e80b00707407410700d48522a000021700510200410003403900c0c004010360310b05900c002d104034414002d4400094002c002c507070707001c0e00170040000d04000c0d1500603120001250080000d241004c00c42609070b540140400e600425020411080300c003825a081c0d5008140200740c00c600c9d04078003420040742140f42c000d8030041c00018039680045884050329850100d04492a21302003800500b5075007032044810a1850b919a1200074629142400e130010302180304040c000010541d0765031140782840000c1d889240040d5004150035a40d090150110400d0916065030361005840c01c03c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 932115638 1250 932114388 932114413
    0x1060509011a0c07091104080105063106091401030b1f18021b06010e010b0a1b02121c1403040209040b0702280b01080d020a12110307060905 62
    0x14064101d92440e2090004180d40c40c0c030825080c0c0105683c00101d00c41c0190104c0c80c10210f0203051203940c02980c000b501c540c64004401d0035102e014000038010b801400c10031180070000161150480c90000380c0050317680011585e40000c201030b500800c038842c9041500403200c558020024126401540405018cc0b140a0300084403400ca04286214134507559007040f21610b91440300b902d00b0580340d0300606014400c81d5650311204241100c00e96a0402c2006010012500361514050058500d00b0703824094141d40c0904181d12080c490f20519988440c1c030021503035115400803107200b180c0d0503a40c0c1403c0c0c482075040703030120900181c004114900702c807000c4c0c102620281ca10540d00107140b03800d01d0b111a04c4003c03070008094034400850151440003203121004003c44843c2d107035103074141074107440c1505219403c01c00607001004280c004400a03003240d640059a044080d030090f00c200c50f2800c0a400945d1600300492006805020105600301400f0035a17009074503081c0628140d600200362344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 932116888 1250 932115638 932115649
    0x1020301032325051f0201061a3a15150207030f02040b030601060e03010f06081b0a090e060108100b031203150904050607032f1806030414010605 64
    0x2c600702c9807580c0450920032048110300e003003242005081940f0f0309060303124400300e56010019011130003003150820048044035030900c2407074010200d2550121000c0310440710030000c0c8c82001189080c160010282230410b85507142c0c00200020345e480b2503030b0078040f82240b0300c0140c03a800c48405010303028070400042d18906661400c0f5078180ca9406890b40c1821555060002024900142c0c1c11583c0e501407400350340c034100841c5019110640351414400c001204040c29220411380d41c1d2046030074010104207091000564642c4001c03400c418490501c000c2010400e240d400d640038401035414080d4080d0201d00201d16a41a40c17403040c19500b5450381c1c101c45409650450100ca44c055112100f142164100d00001e160480e0503240400c110009110001d40381080c150b60640d041d420820501602a4061140d1800041640000c043e5001c00201b050301001409001c40101c440000d810b4180000d081d02001200b01c0090281c1c1c0c4a06041c03c001d9182c00c000c4000780d07400d620b4800082540d1604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 932118138 1250 932116888 932116943
    0x15060b0903030703200313081b0a05120a0203010c11101a010c081c0515120c0411070b10050312040f061101090c061d010c1502130807080102030103 65
    0x103070045141c5225613404a440c0c8040700e160883c411502c40e81c0300d6481c0d0b070a000030031507070f01043c8031000024140b40049052045503444d0700d401100030302c0c0c00301c040d480d0400d846048039030444400d001080350580d01410002c209000070342c99440e05a6040c407013508a8611200c2500000c00c035144200f0300d14035001142d02809403001c00c0e000400742c1203040c0d8401c0c5000b0f07066500c5601010b003408800140b40c5141001074404131a40c0e900eaa0401140ea880076802c4001590211500c0d404450039168050719030300e00e41c1c0d016019a40382e0302c00c8414150140c0407903c000d6802a54a20140392079644c2c40c00305803050040500c01d00a0360004845d9580d024186d9050b074100c4603440414074034041056960707440c1c1f115004199501d0b0243c61001c00c40e40c40c00000201113545441c138031282e00034207a281070400c1c682c000e814001042c508102140301b981881034104964030005a441500f031500c01c075521004c1d03020340300340c0c400c0c0d130000700d0100b0064001d1030403248991a00c104075401e1610300c0100010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 932119388 1250 932118138 932118157
    0x90f050d140702130c050d11190f08061e150a03050601080115081305030d1d070e01090e1c1d100203190908010905030714060c18010509040915060b 65
    0x1401440c08048104e582c0040582c141c20301300189002c00703418041c0203481d4010f003203000d0b2142c04200400803400c59040c07a0041d50403890a5506000854030203814120b010342140c1c0503440c500c204100342c9000407082d00c048031317000f04401c40000500c64103403c580d200c1103a082c0042e081401044030b650181ca14181070711600c4900c17000b51240da0a044900b410020310b014001e03440c20f411100400d906200800380c901c8070400c0030422107001c01c0300c607000d0002d01d13180d180c00c0c0e4050301080000701c040d0604e090640c1e0882d40080740030411400ca031741c82c10120300104408860300c012610300007508a40043c50407501d40401601000c00708081149171500c80300d10602580040124420340000e0483e008028002400d00e914802e444d860900c0c2141c000303807021a401da00006082062142004c23a0b82891084d10780100120301d4060f10700c3c0901d0280c205045403000c8540d141a5a036030103101030320700151015000300148040ba080a0403446c250301200c000e90351030400c0205804c111a0100d882c04c84 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 932120638 1250 932119388 932119399
    0x12060f051c0812040305090409030206040219210510020c0618030414040c030e0f070602060f060f101421060d0302030a050a020109080406030606020706020601050f09060103090f050d140702 83
    0xf290001941406900610441c20032000f00860522591103100e00c040c0c183c041c2c0d00030421460310384184105c2001011041c007410710116802c12166100448030440403031407664400c00304c049461702d586840400c2d03024580203030010864442c03146000820a105400302501c038090b0707070502d03406a900d9208a0180000842d40784040306c0b500e041c40d8010782c002640c0b07860002601030b42640780c2e5041c40c141040c102c0450b00610802c0007560340c100403468003c0034a01550005040141c0056105680c01038028010710403001540d81d07031070013003d02c4070840d541425890703a580450317001140582840c2480d01c0007005100013041607800c11001c04054141e0580080d491300c0507a07003054400e40c01c0107421402715900c0799081000144154050401440701d0b4a000c103159041c000080d0810a40d174100508541c00340b8010401941c3c0d0300200d5110f100291050800c9441d4080120058141c41078068504000c0103110010804001622814108030b60798000420b54a418015294410601d0181d400f6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 932121888 1250 932120638 932120647
    0x100f03051908120117010b0103021207080c21010f0b0901020a1401090602180405061002070e042307030201080c0a23070b0403020714062812060f051c08 67
    0x1101510300300001c0c81d00422489040c50000c02552080340e10980061803500420700c0052510034090003a1994554242815414004100c41c07024040100402c60030030810008041103d2002c010101da64403040c1e10302c0d8241c0c01c0750099042510300c2b001e110303036502c40d407000d14001001c9a0102c1583c000c0a0168040c204940c120348810ba403100410040b48415541c0b04650030010b0414030042100f41d9001d500104401c1d0302d5402c010480390010840e134024101401e00d500340303e0380032400341c05031148604000103c1c1c6841c1460581183e03840c00748404d049803c0c1c3c1c5030b0a00729001400000b1207200f642e84420b11340c0d4408640c0054020341c00340c50003041182e43c070240880440b442d80060301d40e600c0c162a050043d19103415080c60001d44003a40075070041c0c401813002820700e50005002c2c1c070301070303480600d0400300b100319800301f02c804018402084265003130849a0781c802d640150303161500c81001d000068481e103042e800d8100b01d05c0f61038400c018640c10560306801005654040e503401ca09500d041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 932123138 1250 932121888 932121913
    0x6010f1115060f1314060f031002070c0906170f032d0d1107050606030105130609050c060409020406110d1e030204030803100e0906090c040c0224100f0305 68
    0x481e14050445580240c4241c80303014540c4503101d0794000c6450714000405c1c90040c1100e0380c105500c01610072405811009200400394070000764406203d0050400141c1c2c038a400e0a00c506140380302d420683e100d9013004000a101030a105555a5418100d406d803030352840080491540ca2080c00d9207010219080e00300c0c80b088101d10369500c03121581c90400c01d407500c0c0a8840b1401114902c481c96100140003160a10500c182000184d502800c203500800035800c000e400c2d80054850b03200b000b0080c0f41c4401c080b40030048103100703104482c0c4010b0141034030b6540f2034105101079005405100d0004040c030b0700d603404903000007644045420b0b0039240c08004100210a100003111484104418585c007000004001011031000f54030840d900c0101d00c41c8a810701c2815001c1c0d5401910052a580c0b000050065601d40881d80d40000c1804440014a4420b2024140c4c00e0242900040400500045011940390300c0c1c220420b10690100160000c2d4540315106c4503065241070102600030b5200816007082c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 932124388 1250 932123138 932123173
    0x60f0e0124060c080d24090e07030b06121c030b09040210050c120406020a0311150c0c12030906010302010e01171f080109060e011d190609050703030806010f11 70
    0x203009015031300d0b00d40381050b4042d00c8010398024551444101107011701d0359028a201400c4a03018100c03094080c020b001c40301150f80d503950714a00014100b0400900803c01581d02d00c200c0d905224a070f0001e4500211000500b074800864010884e804a41001c02041d50f070715260a8040c82164003c002a41d851800e03601220203801c1180c20203940c0c4100040019240342d54000b5100401c0316070300811650400f40340042401154041d05c500a074054003400324034085460b54070750702c00d81c144200390f2180e00c5048900c0c501403043d81b10800e00c00d4000103002c181c110200b60b85050742e000781c9031107164200d0900111007150381100b0740b01000c00b440000c1a0300900110707a0190000b01003407804bc8680d00c030b845003821a110000101d42d515178a100030034412900b801001101e0802c0c5100301ea081b804480c405d0307190440900024040003e04100d40208040c3e544038106081c3c00000b00c074030385e40e2285005805d4180a440b482d0116400c1014000c00b107100d65840400d82044074050f0201070500c1e1002e40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 932125638 1250 932124388 932124407
    0x20f040e150913020117060d03030f0b061c0e0d020a0f02400b030304211b0303020f03130e06030c030d03061e12020904030c060f0e012406 61
    0x115540e0a03402001c03a50303591140c000d0145961010b50300152269200241a850174040e0b0494410400400c1102c0e03980c03003112000e0306540504000c600300300307040280c10041c4cc26583c09540b2040c0469545c0322285031140c000643c80c88034100f0008240c1c505035581d0307034101c034400d4540141d02100c00c10340090417509000c104581b02a040800d0742c0c80c184d0940b0348030060000761a41031000c1c102a8840c0c0742c502d101056880f09004010080282c2903008240c0ba03100b207000d0340403000a0014102074000f60505880340054208140480c20000c055103c1d0055540d44010b0f00144074030300d004c001032840401240c13004d0510403482d055049c03500400d42c5a90000500c2203030f050203507400000380ba07281400541c021080ca5500020110308017140c0c60030160048403030a070022505482401a204104111004280c040f69284016961460b03315002420600018107030b0381041c641c010700d2080c81d00079801050300c090080c01444591010120b01000316403c1d00c03100c098410040110600400d13005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 932126888 1250 932125638 932125651
    0xd0b09060f1e09010e070f0e0325050303040b090108091506040b280609060203031603020f070503070516060816030c0e03030705060103021903030801060e013501050301020f040e 78
    0x74542c1c106041c0015641c1500b41e2106104c0d045200030489559880380c0c00181144940c1040011030345170f600480c3d524014805100700745064020760054410180c88035100412005044075503c945421100006800803e183e80c0800c10342c001080c2e22030000700d03003449480d01044480101d55501d20400c0050b0500d070610980140e00e01070b0840600352140400d0310403288950181d50241d141c0b91008114402d240d200c0000c5400510138407588450000c82c26030448002c0c80c01503100e12030421044500e2090b12402440c501c00001c0b500b0070414081a043c0f55a4960f40700b903842c940d0741d1030043d561400211650ba031706100d000381c00103101c1c1c003981c0460424403403894201c08420314100072901d10f034000c1405451643c080c900402c2180741c41210400d1540c0d00d01d441460701490350b50050300616060003000144a1042075810300d03a4890020102500020199550007030381000002c0c0102c1c1da41c20390380c1d04003003204002254a050500860342e12040c09076007949010b14042628440d6440a0043d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 932128138 1250 932126888 932126929
    0x30204060e2809050a0b0612030913021b0a030306030605010e09030a18181d12160510050411040605010918180602040605041d010608060f13020a02030d0b09060f 71
    0x200c0200d0313410004100000d01c906c0c245189410a002040840c501010721031805500c10847c1044c0d42d100d01000355240c10309000c001d070b1590380c040652100d1a02c60040c2c0000b42c40350400110602d581900041c0c1140d006400401031a41c0740d43c5842c207100d10441d00320b852980200101c10340907106603517460000500c3c1055249043d190810741d0b00074640e03041c43c2d46296440f0380d4190f42200d02409041c008455900003014215000100c2c503000340a580340703c013441402d50500c00103202040c0320114040c50400010801031910b4682411200359100d101c0d801286000004101940541800001d0302c0000c80d460b46261880402c1101901c9910b04d0070b04844840c080410010340d171800504040c0019849040c2c58034201207903c01070148070b01c3c00130ba00c0e189100040261030b800c29280e580100d002e80e45400404041808281c429840785a00e504d05031000540104050f8040003030000f1090f03994090081c2c001600400c02c072020305950155000102580015561411480210708215403040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 932129388 1250 932128138 932128151
    0x5031306060512010213090621030c0812070e0a0f170f07060e030d03060b040b0903150a0e1e060a02220f0e09010c2007170304030204060e28 62
    0x1003002d1803c401d038145900da4022030300320301c08401880410b010340440c0d075040110a00e81141c40d0000c2e10340d1400124001100d40b12081454452030255079000d8014110560385c0c0c0a10700a200320010458807000000e22a40d601560b900d0541c480c01c04440c42070b8103010300542005800e400054640c170000941e48140300c0b00d2517a80b801403211500911307036511009081c204120506040042d1101c81200f014038040d1309021101140b8140c03025242c40510081c0c0311450400482c0c94100d054150107210070000003040351310889500007c00300070980090b82c05840ca40c1d1902020441c5400e4424403c0e00402c0010762210700740e5015041066410302d00780384084d0442240c10020300c19400c81d14441d5003610050008080b0384818540091030803000b042400c642503001403084040110032090021480544902c0c0c2c0380812503030307000e00309840d001005420003400980c0d982d8020710049001e03c0c00c2c0f0500044407650303d104248134a0300c2d010300c1002c200a20710042003013031245501000c82942c510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 932130638 1250 932129388 932129399
    0x803010f082116051f050f16030b060d1407030606030902011e21020c0111070b0406051f090f18050d11010912050307020c0901180905030906070503071101030605010503130606 77
    0x30a417120305000c0c22050400c43c00e01e1218081d1900204103800441142050001c090f407901c003c00c0821816140019040c1040000502a03101340c0c0380c00c2000ca8105403120316141802072a09014a07241d0301c0030810156140401e40039100c05590180c040b5182a032452210306118030391403e02da0482c41d101c43c03e10625480901c42c0748000300d243c4005640400c003807000c00404d214404441c00c160101d46d04010300b66640400080b8001d00c0102002d407114040381c821181242d80c2200ea242003184a8020354a4813035000091041c7d0510801180c245007000000c10180841d0110850f001005424100c00501d000c1d01c4400b03405c541c0003000d40d038070200000407070720800d6808403411007035584560ba4141031a0013454401c144000c00e208180c07180040105039068080005d83d10440b00703000c50f900c9005d081050940c0140d00c122600044000b070b015082240c040001e0142d035200368041003085d0210001141210054080d81d808a00100040b8005404202010025030322484000c10904c1d200c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 932131888 1250 932130638 932130643
    0xc050412140a031706030604120e0f060c0109060b0f09060918011a090a270c08010509060f09010204030209060f0f040911100e030a03050f0403050601030803010f08211605 75
    0x40400d0f07000502010300b91100050b00f103ca83e0b0800012001056a42003940f1070300ca4a1800b600080d0078000e201103584440c0e00c480c0e003000b02480004000e60b4881c989100d12030f0291185000854040e45000700b0b203c820b2502e5a101124414081c00030708003659500240200b01c08045c1070010251804844014001e009020b006070684490f400005a1103481c424407191a00103480f1141c0d5a04150340d101d03552448a61021048411504119440b000c0b030805403100c09254008998650904041003503150000580354042c0914100401040e43c03005a042c4c00c0f0f01031780c04020362040c062400b18000303180c070802e00031034100024402c181d0f0380d98000010301140c00c844411034400308013040701c200510b0824540e0040c1c3c41c00341801d024000d20040000c0e11403d500000409100000ca015aa8080c9003410389000d154040c04075209941c507810320b03100f160803d100c0c00208200d109d00219903004041001c21036681d03220459080c031890800c240321030ba00019003020390160440d44610214008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 932133138 1250 932131888 932131903
    0xb1912020708070b0f04320f1e0307050a0201080601050417060f090a0b0402300a020f300f030d05100608040807030503100b030420040c05041214 64
    0x541500743c2e80c000601d00468000001041451184038440030440450682c460190041d2561004441c607418035064801c0c0c44d08520b0304164080c480c44911080d4030a0000c0c0528140307284d0003240c5482c0402c0701d50942d60b482013a00060494009056841c015402284115044001410141d0405071039000c4012100068013114500d940312105204800804a800c13641001840019042031a150780311000c00d1b0b100904000d004124440400580503220900d280e41c1c9465104945494440030301401e6654411079001ea208124104e9030078078518100000036019241c144503c80c1183c40c22207101000e03000c810100040d8051300140c880c288034280010402c1d41d01c80440050242031021046a0604803a08900300780b081d0b4100b4440030504510540702003c1c3c0c545861075a039510004440300d14141c0b0382c030400b002d2001109000400001291640f4481c001c0050004032402d01410002940c2c8143c15820201d54100424031503012100000081a07028180001245509103801481c0052 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 932134388 1250 932133138 932133143
    0x19060209010e01080c09090c090306010e1e1509100801020408011e0c090b18041a030d02011104090c1e09080f0f0c1c1b090c090b19120207 61
    0x9001480500c1580c0210304000c4108080c60000011301d8401c80e0310382507119a50040f031040e10340c0400607802d03502e070504450044401505072803403540e4072100700900070f006545400e002042042e100e40c141070507400b11071040952013500e4810880c90828854910800b40407004507074486100401c501000740020002030180000010341032010741c601142c0b008110001488003810b003040765400607800140c14064030190310704140d8400e030360744204a10a0f121560183c2250921102d0200c15100e4220003850000c01e41c00c0d61a50325650780b04034201da4070350190b080f07a55824082402860060707800120307002c6990400c40b6060314044420411003121850392300c0003410380304092241d6141404030080c030007000001015048948505180c5450403c040d40f1302070103181e4000304408188943c92076980d500010400c00e070203103203188003000303c4250068956445c1895016460f2512401c070b08001c46090310a0a81003004440011b5484490034101004000056a203440c103803549200614410b407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 932135638 1250 932134388 932134391
    0x50c040504031d06160803060a09050f070311121602011d030a0207080a030e0609060d0207030806010201050108070303020703023102070506060405060d141e071e030203070306020c1906 81
    0x70103a0f035810490480304150301c0c0c0589024401303c00c41da4900c4512001156100c0c00c03c0d6144d41c0c5200201c0d100020580c44a040311307040106010491640341c90f22030007228155000d0000002c1040c078424503204501e80d4120f8402a000058184213100d10b107032409603814400407404a940d80c1c5407801c1800300b00f2200b00b80d80c000041441080390100103450041c00e0030005010303814402d844c003411180c0201e01c0c1501030003001580d400e0b182c0e507240880d0004515103000315221105c609008101441c00c442c0c03d0b01562a20002140d07100300019410b04480d8160300400041e42142d090140c1c2c001e40c00007821103d4000444014101020801d1078813842c05028016100c41050411070702c1e05401070200340c026841c0c0418007203c6e840c0c246101401d160005d50800001c450220701300d00c2c00c008020b42c40c0081041a0448041e1400410401d0490701e00400450014252900008107007034513200c020340c15405840c0400000300c2c1d81d0081c0000407a01c030255000024903421466285042420071070303619 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 932136888 1250 932135638 932135657
    0x20c1905030601050a03080a0c061d06070908120a0e0d020a0b0307030c08010e070e1f0c0203150c0a1d060304030c03080a0506150903030708070c170622050c04050403 73
    0x1d05042051900504045822200d51851904d428406100303400d402420000300d60b04000500980745c006051031403c1c031131042c03032810b40c42e51101d4440c24160b5030103000488018000903a02000203041c4d070340400308000603103071525a1a081c0d0300d2503c0d007051075820035100c80000c40580e132562401c030000c10074440340d15030b40e240c80c0d2030003011510000d190505014001d4010300000c000e042c6c00701e0f07214100d03042000e01c1c50a007d00080c0d007110708200160002c4c4440645911030f030f030721889888a4070320a508030741111260050803461100110b580f00c400c8802400850a10fa00c40c8445990745440c0c940c15800c0210341d040451044c0d48112030540c0424103502c250010164480d0220703920000110081040742003001c00a080c040030489103180b00d000200d01c984d000d540920403100c0e92588895a80d540d01420310b0031440d5100301c1d1281c08a05099400e42c02107050340401e0360380c030528000c08444007070a482d80d07501c001081800360035101c2d44503002d8120180d440c3c40c85034901450280d1907a0a82 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 932138138 1250 932136888 932136899
    0x415050114070f02090a15150e03011a042409051e10030b07021f0608070806040b01120f0209090a050706050a020a2d030f090608090d080403020c19 65
    0x30304000361411180c04010050300010880e1a00141c00d2071341e0441d07041805844040d080800340001c00c02c0207070000f800300000a0000c122960150121036951204107102d409842014201c401c41034020100c020b6600b0840410320b0180c1c000c004001f0f008440704401040e408034107a0001c80c4d5000340c80c683c0d0396030091000910703280d0040304840b4507a94640740e062812041110204806e440010500c000c804040b070b24481c001d000e40c003400d444a071001c0181d011400000c402401c1540f01e080007034003c580c004103000e0004101c261185070008001d60280c0d00c4d00304500c0c0c00300c26510041d106115844248401a40d80c0d1708420700425884c4010302446d50241001c031304100e55540020180a800c0000c61501030f0042044011f10390000054144049a40c00103403500701805001406003280180c18010590450340b0300600c051155241c1c601e01ea11782c5400d13030b1a40c000341c2d0b0f1041030b54400c0c0c442c40902d80c4600c030718070f40c0075200f407050f1a02c0f600400d01003080e1098204030710404c00b202d90000d102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 932139388 1250 932138138 932138147
    0x15020a1104020901020d0c03030e0d090e09070503071a1306030b03011506020c0f0d020a0f06080105100c0b04050c0a0f03021c08041a0c100608010c02160b0d0b04150501 74
    0x61900e4111402c40c509690140080d60b10840d0080050502c0325161542c0c003458000e034016401d06940e4030684030300d01c030902002400001c150040000d00a05100482c02540d400903185041c0d6101030001c001a60600b52082240c2929420000c944981040518006890303035440740c000b4500d5440c040b5112600c0420103003981c694181504402d0005a010412a0350001c3d544584007003d840f0040303003400000200d0a041d011100280d0441c42c0c3c1240092110807005d45541260720a9a8041040e62514104a51200c0a4036400002003042e00114081425010312680003407098080301d01c0700401c0e5003c02e410307500c01e51241000c0160301000b0415408e1107006140702c0e05180040c01c0c103550785691130322194004d0b40248070414101502d84241104100111441704104604403099020001178400c0901654040e49070b540d4200710b0a1801c0600000d450041c5404894991103841d0a191920500d5000700c4111980651240c40c107610700d4a551084c2d050150000f4007943e840d03801c0000142 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 932140638 1250 932139388 932139413
    0x10b03010e0309061c0911090f01030807030f17100f05030a02060403140a080d0c030e3708070c08011d0303011413051005030d2102030403030615020a 66
    0x24000d0341072141503203103000040304035403440100300d40c120303101c1083c0d0303c0354010140080c98021240d40341034024000d12048a45904021600300e50203a603613690a6481c01401e0b5013032100800d401c00500c04480020f014901a01c018405880c010b41503070380100a1031a051016100400f410b00140300c02d01440e80441d849a0280c4400e40040c00d800423690301140362807140b840003600251000e110104074010600c00240d0350742e000000151100701810040e00281040f444090200e45040d07841022030320045011054601410100d40c0d09070390700c1c840e12403100d0b13120312100d4404544040440005006c2009050014050307902000c001341418186801c50310a1503118680c0e040a0185143da00000030449040d0f03071000344052003100e84140402c504000000d00e00064034100b0301003249112800302c460b000c8803000c4040b41c07d0084000002d89a054407580c801501009100040481405c20f17002940c10501c61f29001488596400900e11900385080c003800050308400d88800500410b442c403074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 932141888 1250 932140638 932140661
    0x303110304050a17030405090c09132307030e12120a270501090b190501140a031403070204020708040e01080309060403020904030309080a051e031326040603050901 72
    0x203518060400c0d00050074072200d0310584010481c20b120b5920b408205105990003061302800410250824400268280c2c2040e508140201710a4140741400c0b030311402903c0030380348051880c0c0410204050108580400144024181a00c0710500c40c0005400c2142c10f42c000c0d10250402e441e00c0311344000303440500c000b80004005504012440c941980c03880706600819610b0f40344221a0303509850701501508003040040c140300401010020084d43c1c00c40003048481142c00204242d82c0c031544541e803244100501640c0140040206000103010380544095284060302140d040000b564000780981c0c3c004002110100008036040080c818440151809002c941025508010400d0082102ca000c1c03403001a1141009102003014140254001c1040c2d5801c01c1009a940c8840d240142c030a92108547d80d040801d000403010305d000c00c4a05031ba0285a002c1070403c00400181c032030348a44800f0382c0344805466603584014512000c0740c0c1c018002041b464074041103910b80008641c2c00c4030b0015521 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 932143138 1250 932141888 932141893
    0x120a0e07060e12070e0c0304140d110f0d0e060904110a091a071208181204060216291c0603141b190306062615070e01170f01030311 58
    0x500117401203030042039200400729191522a61039080c010100362094001220744d0254a035040c0115034400c1c1e440401410100441c0d01d407503c0403803000d54030104018174000040340c121010710305140c800020001e030b090040c00404d408030003e6001e03515034012114800421040001040ba1686108010f0411350004410505205148d215000039445002034101001603180000c1d00c028240380c03060708103122001c02c460002c4900d511801040c0c0c040d010b42d2025104550f498003940f0340d801140416195040110f000c61142c1c80449840c40b0f5040b4844244c0100600240350140074414a603100707401e2600c404140c0310300d14104074180b0141c02007190220340010110151a22182440700f000c1042034a000c01032070041000312217041d1b000c0d080180342500385803001440e40080c00a03d46078010300c1901c03c3c1c0031038030311101550f521609070b0b02080424031100061407135400381c0c001d01804101814220400b013840c08003102d40c15000ca43c0b0003050035a900051003415804402038450040f843c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 932144388 1250 932143138 932143153
    0xf010609060815011407050a140c060d020309190c09110901020c09061311120c0405010906030906060b0408010f0c0306080a3804050d090308120a0e07060e12 69
    0x40244400340003000b0010303a80f00c4140151180c1d22550b07114600045c0d80c10a03a855066038036003940c880d5207001f002c0d68128802c002c01d10440c0408500e481d100e0100070411840c100900d402d17000031b0b4000502d43d00b0a0302a01840001a4401c401c505642900c0307040311010340780c202600202101d2240011b09002c0d44140f2030140b16980024041c09489800c0b03508a01e15965580040c0010740704960012855042c280004c2c04610054080d1000050f41b01e07100010303551384c1810b004903000314400d060004044440410000b80a5400441c0c498014070000c10711a03101c048001d0f066200e5031001c42036a56401c800745600c125441070800d03105140c0350920480c0d1400d44515030310203200300060895076040d96582081c5100b180700c2d92121010740e0360000c14443c5180d02d03030780d9100300301c070309641c00d0260000240001c3c0c030907034105050f07139803100b0020700344074080001101c0ca4600034a030980c00303a034402d80082d8201041061070020900340d034a10722080c40300c40a1041410f900d00107041c1d168420303803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 932145638 1250 932144388 932144399
    0x60705040608010905041112030a0206061903170403020607210e0306180109150615231b100b0f0d0210030e1014060916080402060a02240f010609 64
    0x2a4890459941c09400b107921b840d00c1c01c00740708020907911596030009140509140b801d401101030181414540c080d00c10f81c0d61844140595184081544a550301c078584080c00010340024040c0044203c4c011700303604264480d40844e160368030005040c4c80070404020565903407181e0340b00c0c041c4440c41030b103000520102d00c0d2003c84da5485000e800246040022060303102020b0b030035808291013603001090000e01001e00c00440000303180e0750203490f04010411034480416030103020341c40c9205a012035410307401c2c1c48642d40f00d0201d0b082695500c0602c5200086a860920b0402c901c0007501084ca000007140b00d518820406503144020030903010b1142c50080c0b00140c1e50ba5190043c806405003004500090510b40c964208460080c40d028140d240403002c030802c54074926014407404041e95401016281c3c9203200303030b6400d030341642400006d40d020001801410280050f0450105e240100c990100d1080e240714142000300c070f840c4800042a07410070030101e104540b010700402c3d6030f0030f00e4035440b070802 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 932146888 1250 932145638 932145647
    0x1005010e03070509070c06060b0703020c1002210919090b040b0d02040f0e03070606030201080a0219140c030a080a0606050301030b0a020c1504050606040b0415051e040603050a050607050406 83
    0x1d11038103106030313a10000035990602400d6840b090f2503001c02c003042410746980302001d050b0411041640180301c0c2a1413a541070620400d5079500202c1900104452410080e007500908000390701f002d4145014401211991204c3c3c040400c0915022001140305040184d0303402200c820302c1495114038142107403580643c952200b64400c040d010b90340415600380c40f20200000d42400d880721070480c800003c541e1300b40a80f691107201070328800d985450450b141e040c00402030b030056241942c110000c240005107401c0c040c8102c894003046103940035040448544050341150028248080815030b100204000c04020b449000301070400e505000d804c550460b280d00080324070082c9500d036401d41c000b034100c030302c1c9808103c0500813410204580d0150300e054500140c496400390340d80c500440c10448012410302e8580500700580000001030b1500500d44007c00081040007505403c0b100101042035600c0c1d1140d000b40400b450244005010280007843c0040c030b419402028030041020601c41449160b901 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 932148138 1250 932146888 932146903
    0xe060c0f0c012d140411091f0909030207150e1e0307033002060a181e020a091104090b011e080109140402030613050a0f0302061005010e03 61
    0x10280380986400741d140546004142d090f0b03a011104803404910310040182194032045501020700900284611000540f000d06060750001c3c003c608034400440e05091810314540c4c0500c01480100c0100480b108100603440990000011681c07205041400d0540400c620304c01000b030352048540f8400e0345070000700031010112590f44200200c50210a401402102000041400600303481005035a49013480e000d00070b0401002225400300c00303044440300d1500c002004003e003600500001e80d203842ca104000c20220710010303160041c41005101081e40701a06541c0d40c2001ea407400301282031401041031601069001c030760340b82e040820000d40415403009440031120786101c080740300c0c03200c3c00050318400c11804110006040d415159903407154002e558038101c8108003002c102c103900c400640c0c13419000489020b5019880300022441548024801c114194023400585186643d030f554bc030002c16403818000e40050b4000014440181042031800d801032100742404400707000d018021070b40b5100e8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 932149388 1250 932148138 932148157
    0x21e1804080a081306020a020304090b011b060b0105070b010803030601030e0304080a08070c030b0f0402010e0a03020a031506180209010f0804030e04050702010b0d0507031502070b011415120603010e060c 89
    0x1040c0020038500c0d1004c20031122000d81c005029501d960a0301c1d40250750340c0041c400c164945040040d41021540a400192118001020b00582400e035580b0344038043c112041c100b5040100070000f60010a06008d0000d0203400f4803805141d03241031410004054841d040e0903200030740c0041108014050002501c80d01c050f82c01a4010b845110506000350740d00f456078000b41080ca590820002e65007000b107480b600c078910036200c5d21445086081848031407107140c040250482c0c8400340c24400b040982107541d04100800740040b813895101e020918415160011a0101c0754020403003010640c1c210320325090840380f6207004c2030285403d4800401c1103043d140500d00595580c000b04401501c01e410003a4010806480e6001c40c508900d07102e0381c2c80340e25100c1552040280700c01d120140e00030b4004c4400440d00842141010307400c007008400e90700300c81e80285900541b98410f460481c03285101414540c82d9200e14102c007072419005040c02e4415035a581610740c0c000c5002c20110b40d4149059800c20300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 932150638 1250 932149388 932149397
    0x4050705091e15090432070504020702120d02030a230301061b21080114010206012105100e060601020703120c020102190803040507060903110108070c021e1804080a 72
    0x2200daa00303807185544800500f54211100c030b0200300a0050f40a52a801c40c400d007103070000c84894880100c860307104103100c40308503078204a030204200d180613005400540d00043c2203003060140400c0062600803884c1d0300b040548c00111b4241c3c05180c101c60790400c0b800c0c0340080b201110380003803413621007444140115800d01c01150b0858060701221001c8181c0541d0000c240b00d07a4070440c2c00c1c402c075080b104211140000d00000e00100740d0f03001075130405643c880107030020b0806900b0000075104086002c9800310140a5542c041c2e8086a010898641101030074031000500240d007840742c1e4103000340142f0702410340d40602000c20010740340d0103007182000703c035180c00e8190f0346d05840101c0c02c00c0311003010800c940b8086131480041c04100c100440c010b6100740100c1e84480d540c0c0303d0640301d4842910001e0070300041020035408950050808680c480e12030326003a04807070003960001d20307010180161500405c482c01140000b60600a13140384900b0f62200800c1c001c0d29007559a40384d01d02c41c0c185800c0410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 932151888 1250 932150638 932150641
    0x50406050a20010203180c03072c150a1409010b130803120a0b09070e01122702010e01031e0e0705030f010b010e10021c051c020304050705091e 63
    0x90b1044445000d400c4008000b40c415480d0501c08a020b0740051302e00108403240210300c1c142844c00090341c0c4242402c0a0b01801d200c0b0f150010f203101e91280944442100e01c1c070031103c1207a4003040c5102d80d00c1040c007185195000c503440310601c0203480e056000030307810303806800303000c00690b0754070300b00c181142d2103106a1a51400700340c1d03a460000c03280c2d9000b00a00e10002c00c1d540e96120042803c2449190f01007000c015941900007002480b02c1c050300e20740d0101d08141c803541e1155205a0600d1a040650803003c0b940d5030304045820b400640700515180d5400c14490448115170703003c030311a9540f072000d2a01f40301c1d2403250200408100c007007008407015259604c0340018815014802040200703801419140703480c043c0c10005010740b58489000780020b1422901c800185021003050504078040c0d80144024500c1300e44001b400c0038104610b03018048148040c0c05100d2041ea1202d29444040e4005a12801c0038607050f89030240c650002c903c1000304508004070003a40341070a490511706800c540d2540d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 932153138 1250 932151888 932151907
    0xb0610080f0603011b2016060c0f0c03080304032c01110c041107050d0813060221090709050a0615081306020414180702071a09043905040605 62
    0x14035500b02000700c0302d400c3d0745c640d40d0740c240c12140511410240e00304001051007000e0f400c548824201c0c1400e049036140417414818140310301207884d101485060616080100c1c1d440d070443d0030b89554011a1040e4000080104040c0d0204000060071020070081c020101054540d80360324140e10015410051a11200341090340e0801c11000c0d00ba00140040111400403141404141d00281080d50345109400e01c1111040c480d10b0702a1040110001020000080f550b40c0d8000e58007003150316045041e0005120600d803c00c603442ca014020640051440e140703442510030a481000b00380c088070a19041c01000908038000f40720601e44101e180403130003a6a10200d0100500d040503000e0039261003c83c1c04945500c00c0c403102024550102d585010102014103400702aa90440d040c000580240c2c0c070411540581f030400c2004128001e5000342002445004141200e60728101404a03080d000c141d1107040c10203030148080c0704006031100c0142b10000e0b0002c2c0c01c0340319034441d0701c0811100042d56000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 932154388 1250 932153138 932153141
    0x140904020d020c010615050708030411040f050c03061201090b0408030c0c06150a0524031e0f0a0c2c060d0f0e0601061d0402070212190b0610080f060301 67
    0x22506000801151246070701036129009100c5d42c02000080060040f081d40800e000307034161404141c0c0300000300e156030749581d074503040b100b0f0105042d42c116403601c414401880f128007070700d80b0503403100c0e2000e80c403403509408009078107101840c1c1c10001e914080c0b112010402407014141d0103508141015501c0e1110203154840380b0490200500ca4010300d000d00100760002104d0070070490045903018085501c40e0f081081c076503182c19482c2354107501003441080410303d200180d40d0000c14442c11141580b6107003444814504219400489803039003008000140c5124450144006001d00d03100d414111625642d0740343c5042410049010f0445c5d40900c1300c980e4564080350b0301050000c4007132003082114201c48014007801c4582110f24040c0400116501d40716030342081d682e0301c04c4040602c3c103854140030311009500210b400e0b80c206070380c661a807500840070403040c060007500c41c541092150b0f0318144400218000703020144500c160141702a0020f1303204a015030880710b100b4010325140c42d12000a070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 932155638 1250 932154388 932154397
    0x3090d0c0503190611040503032704090303141602061f03120f09060206090c09101e1701090b0123030610140607021503040804050405040b0a0b1014090402 68
    0x2503043c410312034807180c02600d03504003d40292180b0810b00180a00c885481d5850089001c6c482e01540144144010802101990050000846400c9803c400d0000109041d0381a060040e00481d403200c841011701410140c0507030344035134100c03440210b00c66802002911084094181e10302c1001c40d41502e08641c1c0248600c00c02541d01040c0f011041c6940030b000b500d90b50004c040764005c9001c1e804000392550020503824480c19440c00985010b560b070500b00554a01e0203004c0d10240700130103d010403620740507048028800c500c4800c18040d28030b030848203c9004403041004115905005810002440990701e460644441071024108100b420702030184042c010710b00c6d25030621995080c0088903410700d08003400d0b86d01c00c5013402003001c80541400071a1040400003900703d440c241c1c00b120540d41e010301a40d000340c411030000707262950f00c00004090350300607030b025154201d6240900c01c080342540314114a00c20143e43d1ba519503011042e01030505074400c948811f540b00c2c00a0354544681c0c45a040b038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 932156888 1250 932155638 932155649
    0x12031b1103100504120801050906060705030c0105340804110f130516091211030a0c0602060f152b0803010f0806060a0f2105060a05040c0f030503090d0c 67
    0x260b0500751550401d6010305000c3e207058603156410350703034140c40c2481102128161000981188480e403924018004194800c810a032031500061029510300442802405d0180b01d00700301032607055262160f0139101107091400e004045900d2040f8005a0790030203400c541c05600400e0080c20002d01c607011650502c4512243d0754404030902e14641c40c14040d910190003607402155586040c5e6003e081541d004019000c1c0b103884080d42200a0f000881094170b4140300840070301541c0340642c16075540c0c0d106030030f5900444003581009003001143e4256011056009092008010f00109038402064050000d40e01c031030035100d168105d505080d00005d22502c120b40e40b003078010340c0e03075a500c4098524041407402070710034502072070021550074600b1750002d006907280e001041da5000e103403040d25580408007000c9510160403800381100032490910896208091a940100e00ea10f0140b810040150b0160030170f030b400d00f40810b0b007400402c5000080d54010701003501c035941050941e04082154051a5011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 932158138 1250 932156888 932156893
    0x190c0e061303230c0f0f030709050f0604020702100c081b0a110409021f0e090403110625030f02042408061c0308071403011e12031b1103 60
    0x100700001140e40081c01100c1c0182e484010043e1007a0140f4044443d1140b00c801d00d511040190340285000c803107007016500700802c603221a0124070040b130308000301503010407070507540c600400910b008000401c1e940b116044500f1880c00041c0d0f40000e00c1790210410940030000c03d03c040c0c50070440d240d4220340c0c01034441c030040146842c00000b415541c03510b4850486400800000141003070400d400b078014030300e0b0300400c5110300c610081015800d0011010a5008101344843c00708070f161203105841d400340d070082d80c03810300d0045005009454010080c14071019001020b2104644000003d038560080307101d403070081b8a101c00b80f40c609010780510381202c2c41c40c1441141e500a046c04041d007544843e41c0361b0701c0b407030240c3d600c140030800d03800e050f082440c120700440081c2c2000607100c1e1001ca40d1203000e40c1081e0040700400c800016194000f60405020760540900480032800c03154005001096964058085d010031a50000e00219101d4411385c05100714480040802170000200e405c0900040c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 932159388 1250 932158138 932158147
    0x18090b0a1502120d021809010605040b0307050f03131a010612020a020307050708071a04051503060111010c0f090801061a0304080412150b06070b012d080706020105010608190c0e06 79
    0xb03108000d50140c00749a01c42d4a03084c500002501706050004d048030218ac8540e4102480c00e01540120390000384071104020040105203200c41740b20700030b540100c0c507101a2442083c400d150000201801d20988000484440e004016182d03002c0d64020000c0791401026807103446c10202a440c502450070000d0550207541804502201c000801c030013202e07159000003d003c00e101240045920a501800b40c210090581d1902200c07042c00040d50046818502006031444490340c0d1421180140a100300054016500c0c140c03060384484000007506140300208040303482e040c582c202104200c09601c65440e40400000c040c03242c10000c1d50010141140c900c08224001d2924052584113620101c2c00c107440d1a400c207910341094800d903504664403d80ba12040d90030000d0a030b051540d0300311100800207000c0201c013045401f6017903400013804620014400c580c14240064255203058100384108564541002101c180411325480c03a140c244600144010700302000f2103020369100f01c0190003000014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 932160638 1250 932159388 932159407
    0x302072004060b3007020a030305070e0910092405240a05030604050a23190c11151015052104030e01021b040b0f0a0618090b0a150212 59
    0x702031002d015403418101504010306854113100c40e01954454016404250b212001034041d034401e58220b42581055040d0103c000700140000c20f0480310306c000c02d99107010400804540b8000c42c0c548096071400d030124070610801c0c4540941440c402c46100f100c403c005424040d03100300b01c2e035203001c1101c402c0c541d45140401d0f0140c629801030f81e09c07030b0140e03103003070700092103050780e4820303480d0080000c109100c0300c80184066051158002c1e05c01c02d00c802c212611010110074520a1020845058450350071020014041500344000e110798403035509082c9003080740c020030303e0680f103027038030301a0140c2214200e03003030001c4800307005070003010585407030b0620814403500000061500c11403180c2d441009081c0010012600c401401c0c406141d20f48402c020343c421850907802c4081101c4014007503403000c041075000150404140d601c9131010842c00800807000c035060410403000740284003000d03c46228a800440c2e00c035140b501c42e4410f005003a09041c1c480600c00d01c050901c83e16150030042d12403d015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 932161888 1250 932160638 932160667
    0x203040515010f061d030106051c031b080f0c0c0406170d090f14031005100f1202030318041407020304091508061f030807060f0501060302072004060b 66
    0x9110340407084481e000000355014200454010743d0199540c500d0001d040d920805085080009070a40c10b540303d050110780d58035a540d640704501403a41d240700c0e0311401da080c05000b0401112814000624170003100700881d40030404c5603125807a50400550714141c0b41b40740c5091403050502154418100130340000c02c1d00040391406110520712054828120a094060341e9070225071044110038100e801040101da080282c9080340a4000f0b000d4440e160b05905410040b900111849100100040424009248001c88000241c0b80b00003480c01c4203038154001a9490058140700d400581030321004d0001c0d0740b96500400410b8201e40141c0c000c504040001948a030060b0003000e804900e40007c5d03040c4c07503185001d06c0088485610181129444000b2901002c0280c110061042e0003500700c008001030f03442c0c2c0140140ca00500002a06164a016890685406070300c641d040500611003680420429a15a41c1c0b8445000710340c01d03850300c06c07404600641b029a00860480c040031034005032101f480c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 932163138 1250 932161888 932161903
    0xd08130c0e190207030927020c011b090f030605060103060302060304150f0c082e0e071b2f03010e06041e170a031103010303020f010629031902030405 66
    0x40601d8540161800c2c1c04040c22801044400707400180403a400b08406a007610003040d0360b013965145582d100501c4800741060781c1c410410714406070340d1403004c400b2122044003201c01c1d400342d0349003e0800f1460304081d110400058040a001b255803000826400e078001d41c0142d000b0766001d007802c8d86038980350808001101401d040c942c042c0d803c10200e4108002c152240344445c41c00ea41303c3d0041500c500d030486150308280d04031483c4465080c40c21440050489054038020010361b0540311407031806507401400d56468034184d040d4900d02c02d02940020b00256815842049000030344210300d400e1020440c1c0000050450070303090752900d44001032000010030b01303511a502503186107407442503e441c503e14a000303030800506010704055118010340150350007400c65a11515020030882c0070796030b181d0321961081e801200940e000c0c69105c00030242c280a420020500d0740300b000348033100d81740000c00c140e0200c00b101049036800000120b845484007074803150070401d501c045440703280a241080c0c2c0c810700d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 932164388 1250 932163138 932163151
    0x60c160f03080f0609090714060c190c0b07080a1206050405090c0f030d020616021015080610050a05010e01050d090c08070e360604080a0318050d08130c0e 68
    0x18000c0c000350036810101e003080c0c01b50f2514030050502500c1c00183c074001228001c0354940c00b9004214070845001c0801c100c41c94040703001440b0790f0070070480c030b070030300c2511056402070020100c01e00c01a03000c50700740c000382c64101026040071140b401c107148150b401040c29400c1907510038540f0051110b482d03400108041e030400d00b0b58849858001c08010550b848800e10360420050344590002a505001e545070072001c0407181c0115100e0650000c016402e42e80c0702d4040c202c804200361810069400704002c0310390403a402c4403142da02d0074100804108420780034081c490500010004001d0b082c0d2241e82180e4268416443c100420292403424844508803481203480610034a100441c480c062100d82c0381c050000310b0003000a1100309617912500e080c0d030041c401c0b00700020000061111200b0b10031103100e2449881050f40c0c40804013009001c071840718072903c9000101e0b40c5243c001900c000390074910301e21541071001071903591645103641104a6840242201e00c68900040d080d415804014080e52 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 932165638 1250 932164388 932164411
    0x90a05071107050a09150801020315100305070806150706020d0903030c021204120206070204140a0516020a06200c030a091208070f03230d05090708060c160f0308 71
    0x1440940c10680d540068043c1690000b00c04400b00042e0800340c0c481c441801d41e1001107260742d5a40c0d980c260898100b120300f502c0340c15103a03c4894081c6407509180d59441d040b070908000390b00b0a10700042c50500002c15440c00b90300d80e42290310060483c001035038140395005805650341e14400030108080e10760508118040703418031010784801400441c03508100003280c08072a042c68986498004503944005082c1c0c2c01c940100002c1c0c02685480c020b0086907061010304440c5170070202e80c54003c460300180180c540980d1030b6040c641060b03002c01d94282040c0c00c0040415040a04100d5030f144240c25900f6903092a400540b0750080040480a001d41708035030303150042d07e2555021802c0e0300560b00c810082c8448001c002e44000264043e2141114600a00c0c181c0f12050f00804609a5141c0c50314440e004d1010203c1e250a4180c900d0155542c00320000001d085441c0c0341500c1c8598425001d00030306214240842e0010202143c00f02500d41c098000c1e0610003040c5641c1409001040191694910700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 932166888 1250 932165638 932165657
    0x30a0309140102060f0f0a0f0207080307090504110f091804032105060f010507063c020c0c1318080c06070206090d05070219081501120201090e0c0702090a0507 70
    0x3903002080e101d2080c1c0348030001e501c0b46d50701c501c0032100b01c44008240c09652681c4600245030344017948041e01019207e9000981d0f00d04180e4030240000d002a07000c184100d007001c20180c003e002007420b5900c110302883d08135450325042c40005900c07200024416510f03a131040100010f042e441009c0400c800c40100f42c60f80c403030040c40c04d418180d4100300d6259800441d01c078020005944980014103a050048000148202c261001d006a12440c100600021000100c42c602071280b00c601c0308100c25001582140340c142002d4020340c45241042000d0311580b1103260b03180c1e209040ba008181d544290b4448420b8110742483c040150386c1280c00400f8182c401c410009600be4000501c89005500800040819690710035040320242d02030402241c01406000b031071aa03200c1000f2000000c0c0c85050301a00c0d500c180c00c0361411a03480b0503441030303450100c45425040540d80020803403054132005100454550b41e2408000344500c50140003d401c0640d1208000541c0340c2c65108502500d40d60ba80e500345d5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 932168138 1250 932166888 932166929
    0x60a0c170a0207140d0b0a1e020304050a031809020a17060904020109090519020f0c0c06030f04060f1b030c020601120b0114040905031209060604020304150b0f030a0309 74
    0x19009034070750100540e1000100b841541000c00c01322000b12001000c0840c00d0890341e0701e5840d0460300350f401074042c940720104803110f20045107901011002070403045042d86082e45800303a031419440c5018007801090340703410010701e1080704c02c1000381c40b18a00035940c0d0500030b0b10041c5135414881c02c80d9000035000001c07881c0c51400b090744074003e54050b91401102c0d4240002e2100401015200340d00c200600d40401060807518006001c10701c00103a40d113602d800c0c4041c0302d282402c817207030031480c441d002c20020003041c0030b12020780c9508181c101900040c0b00d040c1c0d00b0500700811070300c060000b445164452400340140d05400000054031a03500351011a640d4850031000303a408818010320140c2e140006001d0444104002891000000c001041c9000640c94227411070307002c0c010001c031468104040000641042000c0c5400032415602140303940f5241d1900080c1910009000036036540740e01c0c0003442c41da2006040c1c15201d00c002c054446107800c5140c00b03010700f01c9604c68a05d0100c6401000d014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 932169388 1250 932168138 932168183
    0x90f03130b2a031e0408150a020d090c050312091c0314040308091e010f080a091403190912080c010f020f0706050f0601020a02010f020a0609060f2405010c060b060a0c 73
    0xc40311644c00401c2c8240c42c2d443ca1f01e007260001000c5640950307091001c01585451801401d100780d00540c88402d015050405050a00c82c211144281c025020007080d0916150030b8a801c408250300380c0c0840045030146401c84140317442400d599040a0045004820302039428024507092102302c4840d420041d45514a1406440100d5110301150800d50181c6215000d500c001d544504810000121150166140343c001c50344030600785800c0c0c1c00411000540a180000d540c181c0b28036041c440b492030f203810244148030002c45401019100e001c04c0a5204880135007011199955030320041d5100c042080c00440a600008001c1d240d1605210124810065488030240115010b0303002d40300c0b1041b00d8006450000c20014910118400c1108000104080f440740540706803041c00d01085a04d0700003a0342003034035a58004544503100300e1460741100030f12015518101c0c0d42c00c2c00e04922601c00d5081c402c00800c5480c00a581004000070769014a5602c04d5041240901c500e046074072300000e0300140741 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 932170638 1250 932169388 932169397
    0x9061502011e1802040603050a03021006030c05040e0c090108100b060f0d02090a120b10080c01020d0f021006030b0f18031813090b090f03130b2a031e 66
    0x52461080070450410101180c0120b41c140303a0f030b000301c07419055032a40810b049600660003038801d604608240070800d98103008100c5404041903091007071a0464984e8032045143d8070540d8420380d9503400940e80000c060108010440004010403400e6a403070301e02e00d03158443c04086071307511450407465102900c0c04106560319100790365209030804c07404c00b02c0f40e40250b01000000754003d840d0240002d02c2d95066021104040c8203800c00640c0b82410301d1100c029820f50303003201190307403c500296101640d00050a00f01c0500a00c1c2c86a040d0290007000c0e070502c6c8140d08249442804c000380402808110090036000346802841e00240d5a502188603100c0c000480d110804e6800401855080c0041a610084408002400c5405400700c004081085450040007100c4508403d4104040302e01d05000010595040b58080c0d441c0080e0b4000001c0c803241c2c2401000402000440d05242d1808a035000c2039075410700c4500f0303160700c0e070400c2c00700740d0303690440f403101941e1041c012a900400000d40741602c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 932171888 1250 932170638 932170661
    0x20a02040e150103020f03010b130e070b041203181d04050c100504090b0301060914100603020c210408010623010c11060d150603060801050a09030c02010818070906150201 75
    0x1801c2c503400d65003003022602c0761950079036040d034803001e090741c40da46c034841c0400506d00c05860024602186900040c10032249500c0a00010000e0004010801505020b020026818070780010a035150300350726510384031290880b4503016000d5548075a003030440f0514600450041c001c46200607070f0380d4108102e01c605040620002542030004002c1028590051894010f00600200e8410784a119400c1241c00000c00c05084030301c10000e100d011034500d500710f009072a20340340a51a14020001141e40c50190110100561082c1c0c804c5618910140c8259400380c80c0303a8000307001c099070380c028220031000807e84a406148002005a1041d03002d4070311030a601e80d000d10092240c40003e0100029908501c100203c800d848408040c1070495003166480a03203d6900c0005406080040440c21078100030400c400c02c51605810301d0200707400c810481140d643c2442c00c8503c9a0b580c448403000c8072500440c441c04c51040d403001003039964258101d101a684030f44d0942e416251080380c12401c1e6400031011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 932173138 1250 932171888 932171923
    0x3100e01060201151e03030f0212210a05040816060902030303070804050706090e0106110c030115080106141804050a0b0f01140306040b2403031201030b0f01060e220c020a02040e 78
    0x6c10000340610341c00d184c40c80786401615040044948510415480300300c00301c882c06c01060341c03c1070f40c000d14500c0320341240c10680704005500d05503035841c400344244403201c43c0c0c01506400715820400ca9030404c045090f0701806030b0352241070140c4050325680b07058400f01c59a00600c1e001080c5d1a12481c0f129040310040301c141c014030b901e0020140c44080700c07401000034074040d500b212030540d1424014407000d400c0ea0108507590f6880c4c00000b070300719091504a0385c01c44181d0000c80c0c2045d901c5c0c0140320741c00e0200c80b2103003403240c8603403900918040742441c1c0142890207103420040e11224004000f41210003441c0c3c80b90b01401001c5c00c05407201c00441d401050031400c080891103401d00b5007890046030741c007100b042401c400008002855508482d849092010401f4018001c01020000198018032554070703081103075051a070050b10f01c1d42d440c42d80c5030080401c0c000c2e01c021480b1680e20200c1e03040500c0c604004020b0306810003500c51680707440a0380a9424140c001500a400140e42400110000305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 932174388 1250 932173138 932173199
    0xd0510150b071101030c031b020709050603030c0c1912050601080d0c051b13020c0c030d09050901140612010b0703021b0d03080c0c01150807060f05070803100e0106020115 75
    0x40d17004100d2000300008240d940d00407004d10462070304c44450701c52000d400404070540b4040f1414213503640108014040d400a00c1100006c840010391100002d40072100002c2c6083c41d45805606070143c1c1d40540011804211408184000401e0300c1d81614000e0066404100c2a000300f500c1009401c1e4004040c1c3d03220203020b0007001c0304100ca0040910009066008500240703e00c9400c0c1d0300722041c05107841d08444042c81907494200940c400c401d4850900c200041d1038080004c4c10140c05204903c111407844030179000740d0740da92040300d00c201150081c0340c0c0e072961110300185880d0450f00f801c03800752184c01c14140c0419030345039020410390b400030903440e00e80301c4996080355840300141c0f0f00b4200060500604204131f400780214044003012410000f041880c010100d80780c105140d00540600c07101e40001c82071103603c802100d40380b0307400401d4580d17242c441000d00340c0c00d07401c3d9070700252040501034000320305541e06411280f048000020b1004409807200c151640d0042c07030403d10300d0644d2002a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 932175638 1250 932174388 932174423
    0x180c0903031d1503090f0c090115110a080d0e010c0801210807050d080f0c25030c0c0905071101020313021005190903030816090308090d0510150b07 65
    0x2040c0c80c2c15800103000204078240540d000100b030341040c1d40d14225900400954200c14004100940c09100c0440384104203525010400b4200c100892034601004280385007418008801c1000c4e1140302d500415140d9100c0c1702d803031000000c00100d9103a07001075003400c9d0001c0d4854031030070540307042e90200e0012041d00424440300e040d202c01c01440c200d0b4214410310200000c44c4050000d80326410311a03d80192516020442c4056500000c0c5070b0190200240f222058080e800c01841d5260150311f142c0c01a03082c4103003010307201952520001483c2c40420364001ca2501201c0d04142c0c000c0e89107884244803240d800c003400e8241e0108541845c43e04034042e03161000340c50a594445c400e991282000d03440c1104541e00401442c0d00201080007141181a0400405a001e812264020b41c2c000c410414103c0c2c1d418001c1604016200152000c6004560b00120ba0303a100120394000ea846070450300421980d07040d44d03016242d001805001c070140420300290a08410b4100d5400c1648503150004070410740 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 932176888 1250 932175638 932175677
    0xc06032a02071805070801081212060d08180f0f010206160915031a011d21030c0a05010c09030302100e0a0209010e0a05060f100507060f020301180c090303 68
    0xe2291a0852149410000301000d00c181c0d681c0308402820000f00700c500e40154050004441a40600300550001e176084401c40d8031002a6281c0d00e064162080744c07911040001241404410000fa003500c8002811404078000c4c821081c504010a42c0d41c4440350440104020108208084850168000c00006420994110280b6078489203d0408444d01394a41403e0a8001008402d0700082551602c00d4401c0464070311525800d00000d10f00302c8030b2031b0175040c0e14405001a525486000e04648188540400d00d0b2003080c1c68500c10010880b81c4500c1100c410b02d9035046c400740c06480035440c001c8107043e090300c20000c030b0003070360b4144c3c00600180c6201c0b00c120000700131442c5203081501924031107000590ba60200d0900030040504801407034281055008200da10161036288610364011f404504d50300c0e17540d0141500c1519042c09910346400d0704080380070b09884405541c48510020011504200030b10704150304144c580c04c100401d100c40c0030f0954902040d40800380101d400d10340301000b0791041c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 932178138 1250 932176888 932176961
    0x30901090902090d050a0302030307080a020f0426030c01060509010b0a02070501050a090509010b0306010810030209015105090a092724090812070c0507080106030c0603 74
    0x44c151240070b4000e03468060400c81112000c0300107070000000d000130303a54000c40094005003451400c51511030020300340d4617640f145209410141c01100c0300103d14104254290002800010a4a40d05d00001e41604e0091035075005081c402c224407000450180420801e460001c1c615070003c1003400e051030019120780c0c0100001e0410400381080120315501c4480c0024028000c441171281c80e400c02c100090017000005003000c1f040406000c00300b0143e036030144c450b41160041a1418080480c16018600c8103039a0090403000008201c58481c0031400c0030032428404041140b0406801c100d0f0508172410720407140440d62080c8400800d004408869001c00e810006451110940c1066145024502141420b099034901d0301220700106140c018020000080300c0d04000704021000b0343c0d2510310500901180d030560282e45000a000540130320291a00140c00a08455001d540c03821032501800d143d00044541d04001c00002881034000d020380507a60001c40c6d000065002440880c1031542c50 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 932179388 1250 932178138 932178157
    0x50d0f1d03090604270e070906140307140406030609050d030c0203070507030809131b0207050324060409020d0b0907090c0527040606030207061107080f071a090a05010608030901090902 81
    0x15101d03c0d07541004041c031070b80c4500c00358034001e060321f5498405038108441f8190712488a600803488400840e80e40403c41505071014145002e074545180c4003c507004000f02c0d08020b000340c1c0383c030942d1002d00400007040c0f410741c0080e54040c0030681d0b01280881c1c6a00543c007006213281d002e0f40051000400c40409030910f61400741180d00c0404540500c0c4003912200d0741b0029401d45840740c03080000f58148000405054160000d0440f00359030301a0109400720401110380c0c1034186404121259a40e802c24120780c2e070020700340c11901c016801e052444e6001518a83d01c0c500c20450002450411400f8615000d04562103003801d00010700521000b1304014040d03034903540c0d40d0860061003a40d135071141c0350181ca0306a400513199041480c080f42222210301040c1e1480701c080c04101d0000e40c20a04a9525103494a0344544070501450080c92402004a4640008100c4d808000c801c050015207800310380c1c0903000038032440b541c4400b125101c1c0700d06d402c2d45001440500e018400004160000d010860 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 932180638 1250 932179388 932179439
    0x304050313060e19060203121b0c0721031b03030f0507021e0f210c03031312080c0d1a1c0c0f05060d0b01050d0f1d03090604 55
    0xa906040c0320000c80140e400600c0443c62850014540d41404101100145105503a031480c1c9400c0c014081d540340207000d2003850075000600000d81c04071400011390b84000b4021f0040d62180c08904080d034844005010310001c440400480310142c0710807a003800009a01611a020441c80e02c5000c400849055202541415102d200d101507040d40d034441c0b6440349100e41d000c0c1c1541c0c0501300d44003150b4403608910303d5069002003580d001c4050081081c0080e400c0b4440c5100071070b5a001085010b9000725841601c0f13602000c000c00501d200101d058a0140b132050071a4400a117103007500317541003c0140d4181c4075441c028406000c2ca050194001d08103a940309508200c034581c0c1500090220150703100081c8040b020000310070800400d88203010103002454081025103061201088890188803a0788400030745905003a000d40c0d00520480381a00070000c02842030b9612515404080c00c000007031051159a100c20f00c00d0700840c0402952518a0300400c07480c986440c01401c2e81509811810321074805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 932181888 1250 932180638 932180647
    0x20409060e0f2508120c0a0c09020d0609140601030f020702210705030a030c0219050d0317060102010221042f04273c0c120c0b03040503 60
    0x24001003201151030b42c2c0c19401451502614000b440b160b0301000440d0310020a008018400400086240610711918105103034541c604160080d03e41104898017400e0350401039004940c0c5c604507001098281e81120092150f141d0720196841112040d00b075805d80c401ba1500412603640c800d400249210035840c2015042c40320540001d00071416407101089900c40c0582e6554814030144079040003020102c002d05006000303520080d080001000000b4072840c04140035125940035031070716401805003c0c0c043c0c04c000d40d40380b4020b08041106480041a00382100000b19a98414021074103102140c0340c0b00b240100c0c4014032842d0140307000d4000c0b21200711141c00c032903c44481c14580522903100c2c00c001521205124140012103e9005400e0030042190129084100e5600810104c15500c24070600403205071000c1203010801c3c3e031064524101d420122441c02e8100c3caa400b1003d94020100c04404903500c0250f4240c2e03101a00b00100a500701c0c1404000480240d000f0b0341d0b00c0344c080e8050304e141 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 932183138 1250 932181888 932181911
    0x70807141813060b0d0506090c0f0706090c0b030a0e07060f0c020a030f0807110105041d091c020106030b0a0513031202090a1205060a050415110c2407031802040906 72
    0x680c2d0054204c0d092101c80880ca01006170380501842d50000e20560304c00c405410300a4440015100b802d41c0700e600584000758030f004015003588000f941b02e8210415001c8162600c6000d42954006c0d86c0030500b640c10030101c040c4454000c605030080360700d0ad0b03c4150b892005010141d40803001a00c0690740078640c1000040850004c0c0060481c0c6407040c4001c580c1d800704c1e46030100304480c055403503a0410606200c02c1c40160340c20058461002e42806188030503590b068900352504000c82180e03290340403081c285602141c0c05402403c01d882c4550b54031113040c0d0f580000601104c004039107070000c030003080b42d9940c00300340034408440c0c110318603001c05843c100c003180100b40c0064290f846aa0103100d02403544080c014144505034000301082c005002a04140d15940501e040684445d0281595400f80c04800c00700d407002c56480c4034283c0c09480d040260a5400c00e6000c4000b184000c2c0740303d030342d000940c100340310b481500000c6401d0155020b410420360240401081c0a01c4100d0308541e03500300701e008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 932184388 1250 932183138 932183141
    0x4030b01080601080708010903020304121e110a170c01180b041401080f1b131a0d050106110a0b1810050105150405090c0a0309021008070807141813 65
    0x3804050000b449103514101d515861710901d40d000d90700d5640f5260138800000d50102c00c48086411281c1c00d0840d500240c1001102e405030390800b0900300112803480c40800800d5242c0c010030381000c07946805d00035036401d517504200324007440c4040c2c150020101c01d443c0350f01400e50302415020111040f4803080c1c03140b81c07454480d44150000c80351f01c42c900610003805c3da445248a640044c0300803000c03402e400c00d4243c10f81c400d036182d648582c081002003044400c0c06122910340e00180204046000320038156401540c465201d2502510b85604040012034824003440d0100c0d803004c1c00c40c2c01032203005a47c0c1c0b030f95070101a0207042040088444c0840d09040d4504111a0503005018a4002080d503d48000c01c103940710700000e1011301c0304c0103201c00c0005980d817240c0c039980200003240642d030b1290b10010840050296050095004620354003640c6880d07440245588075007040c2e20358014903180c40c0d44c2540c00e15003003503120b880c50a0402505030417500c0f10204000c19070300a40800407a00c0307100010b60 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 932185638 1250 932184388 932184391
    0xa2117150a030f05010606092403110f04030b0609040b04110f060316080901060f090e0a06110304060b0102280309030b070f080c090901030f080f0409020901030b01032c0304030b 78
    0x124220f003d02c3c12081800b000384244001400513003492009140360045000d04403840031010008203084c0b00031012868007a0f0400307980300c03510440e09a0789000e213505103080341d003043c00165070803c00310001500c2420000c0c620360088c0d070400546103142d51569100e180007901480e86642080c41d0134080c0301c05881c1c580155008115042d071540050341740307050040c00400020300414550303052060030401380c000f1542c6d10054900c510408500d50f05030860903807509107038142c014032403403030004420070303564024010f10701491141c001840200c03000001281d940d01c410354204501d840103025090140610703920035950a100b428074294030351f600d464240c80350310112110f0010400114095401a80c07007910f04d50700c00d86c0d00c640182003941c0c1344040b9941d01c4050000501c203100024023041404281c0e0161109503c0c0c60740507a549549440c0550043c1d04025616400700b420080700b80c1840d030007800f4415001140002c41070000d2042581d005010038001c00c1950140020030020001c50701070450503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 932186888 1250 932185638 932185643
    0xc050306010206070c0b070c03032004030201140901080c07020d0203011d25060f140f0409060e1509060112020417061e0a020a03020c0f0a2117150a03 66
    0x2a100e1805600180c20400300070314160802174500c50383c9000a4806103c0c90300030005240100b40390b58545001c2c3c00800d00341c4038101107076004500982401c500c545c01801980d00c00e903201080000300000c03003103050040310915030214074030000040f074074802c1202070039440303000428100102901e0b030003003421a0401c002d84120300070100c0d501c40512108000350303100045242c54103140080c20170310f00c0c0784102c25030017040c1c100001c0310503440c0c1c0144181d02e028601603810748202e59940041c0b05045c86030f4003d01c61911044d0501000040c010502c000e114455894002240031041c082e4040040041d00284600d040c842d400d00ca01d038100c10303140702410150980e108000d0081410040301c1d860302c24000c0030398850070054544055030109025030550005400d04025850f20a404010b601a000b0564001501d106a1072080d2140c03000182100c2500e028950140140782c014030705c4049030003034a00240100f00c110700000440c01040c80c9031540070100350f0084101c8410200080d9040041c0d9006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 932188138 1250 932186888 932186897
    0x6090b04140601060905030330090a030806090603030703210603080327030d0507140a02031b010606050403020112090212030309060601030203072708061812131214010c 74
    0x8403030600041141d90302504131400c0030312031607140c040000d65901c12038a40e80e003805500344143d4000c419000490000e510303102006446d07071a200d54450703910003400c0b006400080c4a84085243d40c14a084064052403018001d1803400344561819610020481030440d03403003114a40d84041c0d0059485124040c40c0f01d03183d225900d00301019a0304141070020428940c108150041c01d60f026000401c5502c00f0414000c04a01070f507607038809480c2c50340440c94001c802400050f150a2095011004203004003c0142d0224448540700003103081742c40c18080e082c0032450400c4103001640c050550146820030481c00403442d08890b6010644044100d584a10366031304c040144400c4007000d0010942c80302c000e20b002c5045203000f0300300803e0000007000c0080100204500000701c0141d980d410720143c000042280c1403414803140318440c4100d2410141054001c061105a002c0030074800c603208500341c9104d454442d418040c1e82603117980c60804c1160038003407040101080c0142070084c0b0b0f810904c113486 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 932189388 1250 932188138 932188163
    0xf050a09360b1609120501060504110c010e0f0d0e06130f03200d03270305060915010e0703050601110f0102090112090f030509061b0a0201030c020f0d0c06090b04 71
    0x80c210314110003c2e00358032111010b01601d0120310b41c4611032008440411035441007803061801c00c0740c0149000d401864100b4207207a07000319810001001040c2400e13103040200300100103060b13030079103551203000c1e9100642c01804101c1c20b210301c40c0c02082450713100108107500c0d202c0000202031140181d41d01070103154074000700400c21b10210390202c0481030790480c0841c03507284001000030180c41c041c5600600348101d0f04034001c02d2160301905180940c0100c0000f07000151a800c145969401c00c0f13400080c58458103000303149200c1070b15100d9048600200001c032440d00e48440c00d07000303880010200c504020045442c410802d004120150701074801400043e80c500c00c040005103c0b0700c0c00115466400d040612003000a000e00112048050301850055160071700d00300000c07050b11400c00898100002c0c040d80c5c0b120044045070300324280740300341c904000c1c10303400c50410390f281d070181c2d60041901d400c81884040054043c0200c601d925108200000303114040e5521410b00b4a0280c3d007e0300d50800590 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 932190638 1250 932189388 932189393
    0x13110403060c1710060c111806040608010e0a111504030b0a06052b023d090509160521100605041802090a031e03090f050a0936 56
    0x800400c80207031040103001a16052032404e20f40c60f151320801c07040181d011290020300910740c81c40f81441c900184a8243c81c41c070003400007035001d01610283e01c118549080000c240301d0501c100101641c005c0040d040303a0100e5114095001400700840390001d060340160304d05504584020310241d442140f0601240c180305042c5012682030341c0010340a140864018204001c0040340f07030f10310f6060720320001e070207552a101080740c06030500600050400b0800c9010031801641c011a0078001159459860441004000310b5012105108094200b6580b4010402404141e6010b1b6039192480c2880c0340781a0703003aa03003400c048005200b00c440e43c900300c0040c011040c00c2080e0080040029203010340c14141000710030007201c54640e407128050350780068098001d40313440080710001c64110000500300540311000c3e031040858510101e002407001031011603050455611141a1031015000340c020303509140600b4020303d00703507055241a001407011202801d070003040c05540d400c03000700900365808151 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 932191888 1250 932190638 932190647
    0x7060509100b09010303081807170304081b0f13090f0b04021816050903070905040b0f010f03080403030f030e0a11150c06040f0c09090320010e0c13110403060c 70
    0x4600b040c8604000d03001000426401071145401a0403190301e41034026941c0c003034500d450103542c818a4481d62140b420303484c5a101002500c2152001c606580c02c580e40f000441001c900c04848003503100107a0040060942400c502e140240452100001150700340d0740c0321820a400905c0007110b9417032416080004506240c00c40f40f220f8040e4103c2400c4501340342060900350341d035031400c000c204500072038040300590b002c1000e00010246d12104201c942443c0c00c3c104640141140c4111005180000000e007045030503a80c4070131250041480c50030f0900f0746c0e50880310300403031402d070741c0815848112007900b00d0005d110003101e40b8403484295402c00c4600d03003440040304c2d06456644181c1010300108000000100b0810381c4542d11203800601c00c000b078034001c032b0301d02083d400210415107406071403010150001030128056030921850382180c0f113419841c41c00d0b10b860071b10020807070300030114004d038604101c40500b403102c100c041d02140b0080813420034a4660005c1e801500d015444100c100340a40c1c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 932193138 1250 932191888 932191901
    0x2901030c0626091f0b01020d0e1903120e01020a05122809030201030f1503080c01060e0a0e011505031b130903020312090601261204060512071817030706050910 70
    0x21308051088890040010b9242c88840c16081c0500c20404840d010954942508034861121002d040c0b11007031b10703800d0400e00701c800c442c401c07004920351a450f070100c0e40c0001000b070110341d4484001e1200c444141704501041c2c01904041c9007420703505d0a4142d0490f4484a40e0044030030aa549042c203601d140001015658112000c180c0c0c1441c0a0300245485020200300c000c2d40d030407201d0f007507844d4110300304a4010030095104008604400080c03200340146500b040307281c40c5201009000d4648484070b0042550401e1207002e50561203014003040e041c03850040300b5507007900107125103604c01c40360388000240c0d07140720710840042e0000103410045200c000d400f15000490074005200300d41c10018288480c40d0304200600c400c049184142e4104074042020881c1c45400c2150340341ca941d91a00302428a03000a480140d0040040300010401449002c007050810300d07140c1141107840c0380000b592101c00d840351101c03019020410402d4040380c1c45004240c059002e040c000e2145103c180301d2401110342 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 932194244 1106 932193138 932193193
    0x1029240301060c2f0d0c0801060f09060b0306090c0c010209031c030f1a040209010e0411071202030712030b03010b09042901030c062609 60
    0x184680203601442c0b003018a580f1004c01c550101d82903611000342e0700d000104481680c62185000001d034802a030007200c401c4100c070745800c0140e0075250282c0042c800c0091103541005404040d1181c1c400030440034000d1410350030440700003410894082e001c01107a04001c1284010000c00f9030449240440040480d68249110301c04001d4440c41030b0004c0f0301103032400f09440340000090190040c100000104400c456285008000080d0412130f5414100001c2382894100c41e1034a12402d94150380310707042c241c4c4540c2c55242100640422024a5086401c148202030008803c41e11904000c0e070741d0704012032408440d4012900408000003000c3c1e004100c036080c0428011910703a001d101c0720022011059071142d003540d9016204083c480100b40e0140c00904000103841418119150705039521200700030850700c010810164002d48248610f504007041c801610304101c08003058400 = true := by decide +kernel

theorem cover : BRFrame.Cov 932014388 932194244 := by
  have h0 := BRFrame.cov_init 932014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 932014388 ≤ n) (h2 : n < 932194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
