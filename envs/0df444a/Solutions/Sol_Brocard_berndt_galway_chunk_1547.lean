-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1547
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:31:02.827214+00:00
-- url     : https://prove2.me/submissions/f24b53a9-5004-4bae-aca3-0a6f238adc88

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 278057553 ≤ n < 278237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 278058803 1250 278057553 278057599
    0x1d010f092c090102121b0301050607061b0c0506010f0b0d02090103061d0a05070f0c02011d031006080f070f0303050c0c04090b0f0f070c1103100e0303010e0108010b 72
    0x11a000c4621401018582115680c1c4440c0120001c6002585801d1004d000c207210003000380202400d000103610504d0b05134100800e4904451007114070b65111110340c03d0002c0038006517002d00a00c0142c41e003104c460740d03800400c20030080c0d0094080340e24a0b80c9600402d00d40600ca03024295000a003800090245011500140003040b010300d00441c070165284455158101800b4082003620b00c25820840c9518135417107102c0d40038901e803a1041003520500005044800040c01c041e04102d101501050b00110032080e00300c0f5280064125110724980201e29001014075004901960284220f2011018000218141a206a80301100c1032501c1c50344c096540760310030120039401e40211400b21029a03101c4c840e2821660045203484018a08186203007203084009181e60100b030303806405e10201c15488143c01c07500035880300245d01019100c02c00a4682044e00380300d420483c2c02c041405000b80000300185048074513800e003071162a40ca42c0c00003800e9508401380550003002240e01c2d10000c1c10301401d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 278060053 1250 278058803 278058839
    0x2040f05090901020f1912091106180a090b0102061b03010b13050402031005041b0e120c04090f02090702031c18020a0905070e0a0f0302040902060c0d1d010f09 70
    0xb00041c13400010301000113054004140e545c8450300b241c03001340e00300c41d0890201c01951014142c104a90040755441500d80604000c2042c020302c00819075090320b04041107101c9007520001d240b903040694500c150005820800310340e50050284401040e692034140d00525810340303c03d03c0450640c0c0c02c00180c0c441c503400c0b10600d00d824210b0f50000080756155840114000d1403000600c4860710305040c140401d072015031901554030b90b50b4122040d4407a038481104c3d503005404a580070005082c0308501c40c60007400c108020b034007a00d0294244104072820a681d4140c91003652481256a942c1000b130f81c83e802800230a68401c020322151150240080c0c1c020220b40c00b10015803c00d11006401003441810701c2e4012415603907450080c0002c1036042606034000e807008994140e4501c0c2008440c0c000d10312030b440000d0040e031310707084c00300219601e46007076440040d0b0910846020704282000201120b00083d0812013050615441c400ca65104942c0901001801c2d2a111502c40c5441d01c40300c50040401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 278061303 1250 278060053 278060071
    0x313090506011710030c150807030c09051c050601051804110111060708010303080a062306070b0901020405040c050a020616050c0a06060f061b080a0c02090408190302040f0509 77
    0x30000c444280f0303440242c20300682038444154012401e52402c2c0e9508080d03034221483d03501d1032600820b905d5502c845c0c0a9030003082c1f40707804105600040705c159103ca5003504895400710b5490541c1c07801000c2503901007101401801180c131180d9940041c4644c506040c18804500310400c40007401080410509072807010303043c941162030482100940d0300381002901c0260004464100401c1850741c03045196404c84506981003090302d14007502c000c02e4132a51a110110000c032006041e5041e5140c0c4190303030f0240c0d00045820007601d42149524001d500500032180301d240303013802500d20244030720140c90007000c0a40081029440396118842c0c40000b4038104002c0100c100401d030040c403001d00c10301d1511442000082080742c108100300c3c0e604060f98200000300280d41d414002022070000752401c00c19009080303103a84841c1350000310380d103008680020f50041c0c0050140000c006a000003400000703011401d00000c00043c06040b0f041c2d10443c07258600030b0344400000d110525058402e25008050782e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 278062553 1250 278061303 278061317
    0x5040c0b0301060207140a1a1b06060105040915080a03050d06060206041a15060a180e1614041d091b0907030b0609040903030914011514010e041406010908031309050601 74
    0x40e02340c200c030000700c6200c001c0c5484004070b01e80c180c0c040751116140c00480d00401921240c9040070009010340a188104204180c41e62a82c4041d14039218030070011700b05641c181c40d074070811410050300b164403401b225546107240000000d8482d01c00704200d4044e40d07001020f860300c00c401e20607115800314003034000000b44130106540d03403140d51650700508140100c0d84407091611081e4603040300c001e0907540840d49100c1d030b02040001e1100c8400d032183d4189668240201d8040baa440c14507024021608101803019021000280342d2210102003481809400b08864110032500805c10718403412100f440d400c45450300214400c0d42c0650414031588101030308040c00e014a101c002401d0f00c049103402c0d00070070f554600c2c000c1840000d44080121154060007448005030184201d4103042261088070000721400c020000c040e8441c00a010555800030024020341000d10034000003400e055900701d0111300382490004680300040180c580620103030000114840c502000c1350701070070009110a04005007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 278063803 1250 278062553 278062559
    0x105010506031b1c0b04060909050c0d050f0f06180a0f1e02040204180506060c0304030b060f09090106060306080a1a0403053a060806041401110d05040c0b0301060207140a 75
    0x400380510580c4012480041610745042c07040c40100ca00c0d80d002300c100f00d414449044003186d8009004030003c4429503240d0380940c960300b40741d8104060305039510000d002d4552401401c400010380d150080c0c0106109141840800c02c0b21592103006035401004945550110320200d00d0750b5038601d45801820302c0019101d00c69900050490b032050b0803a103980100b44140d0308018400c2d11500360b100b10183e642c4d0303160085000c0c6032030352805180b03c020300d100c00b2200062002e07240c001c10003140503c0582031070f0040c146406144d0291500c2d014200000b4500440000c440d00f0014034414900e40180c001302080d400d0411807602040010025010300c80108280c2c404001d440122400d6281e4101d00403e41d000544091804440c0d0000350b442950304007002403001e910301180460300264000841c800d6503d9914100303014044050341000390100105410382c8011054200300d114a1003100458100c0389c440040a85600080c002e180c0185c1c0a403c0903c20200415036000c0520001404540e80980e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 278065053 1250 278063803 278063827
    0x1020c0109050a0605010b040e0117010f050403030e060f06061806090a0b0418110a0e010c050607021e0a030509120703021917071802210f0906090105010506031b 71
    0x7100307001120340b80d000d0450a024040d4622819003d4815280401d00c0c00c0c0c54400e00030511101801841c480280000c4038015100096100100e00881124140f0240c6020300700078008180b418500e070b01ca409601c3c0003c2c200101c0d40c40c9030b40f10704002005a414000c043c1e00c900042d04c8001c41a03034100e4004c10001e11503946d04c0c0011001071401200e1640c0e183d0409000031800d0385108001910035081010140740300c40c1500560b01c805c4980d2600a071305584060040b2180c40d5440406440d9016120500c0322440d0301168a03410f100e207150f03110002c90310003078903075540b40d20000015002541c10b00995685241400048040d08089822181d68a40704e4002404005045c95803e80034420040b0821600c2c2440c0740d0000c0c038105140103855018070b0070313203c0c00c040311072040328142007a07000501410702c20400b10300c5051050009003010f21803034820100000200260740311a210310a2100042509005020343d9050303403400382c480d504603140c0f110040d080f014103540300b400e101c000b4480e60714076070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 278066303 1250 278065053 278065061
    0x15030a0e070807080715080402100c2402030106030c0c08030403030c0507080d050601090b181315090b09060603070c030503180d02010f180302071202060909010b0a0306231201020c01 80
    0x10101360007a08100b407a1907101c0c80c419009440ba00e040c00141d030100400360342c0c0c01664601800d0b180c02c0510b034241c0c5c103241008017820850110844507a60f009418032910007507000c0e6040c1d800f561030070440c0d0184180d007a0b880c00503400005122010410001e80040c2c0f0a4102c4000040c05040990900b10a40c3c3e0315038036504100550701c4460360344c80420080f903900c000f0700c800900c000121985021000c01c00c1c000703081450402d550007016207810048100304642d015180400c0002c1e410901691160000b4000c0c1c004c2d0a40d05100b8081703440803501e58a00303241100d000f41115102c4011442c100d5134203a865400050840741c17002140f15140086500034042e4007000742880d4000a54103a55550319801ca4a81084101c2c40d482610410381c00203030001040c1c0143d40f80d0180280000c02d1a1000500500c02e800415802c1407a070000000c0100c07128016081440550b1801e122007512050580c4040380030607802094581d20346611302c61414021400d15104001c0c00c000341c80d00803c1c49245081d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 278067553 1250 278066303 278066309
    0x90b04230307080c06100617150a080601080d2f100609050702060106021222050d0302030d0e0c0603040b151002030702011d030606011b0c030c050f15030a0e070807 72
    0x5000207001802d040c0181701107a80410b0450750a1101401c0010003000c0c0c401028546000554034408980d030880d040081c078512000c020003c004407921011343c26102d21081c0300b8400e41d48640c82011038420b000f01c49801c102400d154103203e1a0344070604081d40003540e14043e1b042c0740030319035502c180100c0e540a000094143e40b02c0201c1c0904021100915140059102c0c800b1500a01d0160000b0b040140454520865800805c2000200840309603502411030340443e50207014044440f04140c0c002c03010b446828500c5030304010542180740c180341c82d1502c0399032082e0700080410020b80080c0f42400f13059006541450301034003421b001d4020650040c0ca0310b000c031b405a4000f0891008541e40f00500e610180d464502044103d05201d0100f5500d00c1e010f0320071418032407500080c0c00c100f5404400d000103680c001c28540341a6aa80c10414000f882c10f0041c035018800200343c0301d01c81e003403c0d404242c8219200046c185103030340307031900d810052200b14080d08250055610000390100104045006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 278068803 1250 278067553 278067563
    0xa0f05062b170f040602060a1a010c0c080601240504030528020301050108100e010603210c050706031508060f0114030c0a080f1e100f0609020c0c0a09090b04230307 72
    0x2139035061035000392071b00600410108040e81030081800f00700902403900b003801d850a08011480200a1a0194164001c1e8100045a1040030000610620810020017400810720f110551203c0f503c1c0081302c0600c15804040c0056010401d100d068031800800c410300302400401e0961031140c940d0000b402c0d1102a8485822a44407184950700c0f6a660301c036541e40801024000c2180c185540d486a60f842da98030041c41d4030500c401074100b6840e000d507652009503544030b0166010581c40d050050000c000403884c945d0705c298440c80224500400186450051101c0504514968a080015008001d03007080540c1c06004118101e50a61218400362010740060006402d0a0000c1a0301c14070704500b180750b07120b05d00d05420464900540200b0a240084802d0f500840c81c0300b00b18490001a1015900c1842524800610400c042c05c010855040c0c0d110300301c030011201d50307603070151000347e400302d4402078400304003840490700051180d042420380410922032032480559105d01541150880702007a64 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 278070053 1250 278068803 278068807
    0xb030a0f060b010306050904080a170109062916030216060c14010510031b0e04050d0807031a0105070c030516031b3005060a0f05062b170f 61
    0x41081c01e000700b0444a0003860104400c80c680000074107220000740c8043c010003000155200b94030710448000303100c0f40051943c540d00f540e4405108009140c0340c802d140d0b46114501c900005803141c40003110802500c0c410640c24084080c6450ba01c11911003812004d5100360391807000b244800003001401405280c89141540851381001e523030b07a1300101180d442c3ca900d804c04003d280c911b048000c0c8181d9801100c05601d201c403414216403000103d800081a003100c03a003c2104000e0006514803052420741d071503481640783d03094160b090304c284140c030001c004550b00d0b0703c15155115002034807034180504042c0303008a03620f456460810182c035070490003034602c1c00414001c0c04411308001e0100100240b0100344a403611520707410306461004003201101d42d803200c4152641044005401882e00203040d2001802d114801000821207003d4010406003480000741081c034005107808014a03454a201d0202a110788820070320343d10040c021907502c03441826102d810030b1298090499900001140e507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 278071303 1250 278070053 278070083
    0x7050901170609071505030c130b04140307150c21080402031b010203030a020904090b1801140103050d08040311010e0d1101090215030c09041a040605030604050715030b030a 76
    0x5402d00500030301629440d0f00940c030030000710500845055070a02c1500d086500c0703071071303842e6200b1552003051030340c1c516003403100700125111210000810481c0c40215505900700c16020505840750140d1140c21403080607a07450450060180c460402a0742c403502003071070007d0140030394146140c40e00507060002aa00030801046041c20082c040b121120702c05204102c01c05100000e40e2440010820080c5580100d400c1c0c0f1310742c455030000c1c0c001c540c0c0215840c81c40d1404258200c05080b051514034501d41c00d0030b0a041003000c498413070f01e05803a0407001521200c12400015180b440300580111300700030300716070390610380c000a01c54148942d0710040903003010801c0d00c50080c041f407400c0c0e400c130380e030350345811076000050b41d0b6103074204941070405507085d480341e40302100101a405684401c2d5005800d080180d5695001c5c1e550030f02809108440c10005140c55405040d521001142c0091150384202418802001810490404070003503140124035920724001282c240455090201e506008030710742d02c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 278072553 1250 278071303 278071349
    0x6090c0108090307080307030c0329091620030c060414071d13030e0301020a05030108010e0a030f0c051c030c031415010e030304050a1d0c0f07031107050901 69
    0x10b0300810a03500460402c40d060b02e03036120510015003034600307140e681c410a4240a0003600000e02d5500002a40307400c642e00003040c1c01c0c0b0164800105c1d803003040c802c800901103442031071200e5020222999403003000d40700f841030070510007209036900c1401c2c8400d00c003600c080e042c1042018400d520881c0c26164000d070740b81c032440c503082da02d8100c00c82000c1e01724402c6503500e046407592a4000611085400d4282c01c0f418161244005a84225010f500010b0600c0c9900e81001c01113040f03481070802040341d0003070b208131140ca805a42800800080c6114000d401043c49030300001ca045000700c01b0b84060207080c0825050801910f444070300429143c904c400070b101d4252080c0c80111025921030516494240c002d25102140b145149051212a9007246015101002514041c0c40d0180407005031545944042001c91040e204840306851240300044001840d24152941d104011840505140b03440d81d003aa0710074000415800c107481101310014565442c42e080c00e0080c10358034400700100c6c81040354 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 278073803 1250 278072553 278072567
    0x1b080706020f010209100c0312050108070311040e0607080c2503031d0709090305091201060f08012c030d050708091506061b030c0304030302010b1008130b150306090c01 74
    0x40742c0001d0f44180035403032044e200c0140941c0408014507107407803001d0061a081d5528010b01c030308040035a01d444000319583c5000264039040d83d01464803840d103140c414042005603001e11030041c4080e086030300403ca0681c060855507802940c454019810482024002600884089402d01640310a000d1003800c1c103805201d8031150320301d584440100070001c00d40c069581c110354412038101d0703aa203c034044203140c40b44094a074510300c0100140d00381050885400c3c041c04940c040c01d807100c949480c1c0000c60b207005100c3c0c01c100032040030300c1c0703081103070b14402000d02d0104a4030b220115020030010603e00340402c1c41030074410a01da031117035015810a01c00d4589405401c8650308512422181404003968550003a699144401501484030a0250510a0640c000c059108102e840049004010540c040d048042040d8040d22032003801e40d56800e0803908050181c440d00c225810b06041e403004100c191520307540c05036009d0500c5184113030a0001c0303403030290100c51080c61a00002c003044050742c3d00c001c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 278075053 1250 278073803 278073823
    0x1203030501090b0f090c09040204120b100f080a03030c2a050c12030f0a020a17270105070f031428030902093111040606030c1b1b08070602 61
    0xc1d00c2c034240c4c0c103100041020101d000d00000e545641c08108030039580d0fa1501260042e1144001e18201703290a850441c83c500301c1038510010354130241d200403a40a101503100e8044401180c020900c4d04080e80f015001030203540c03c441c00b0031140701009000b4440c690882c4040c072201584022401000341070050810700140c0380355100d40f0300f2424100d09000008180c0c1c05264804503120358450284c402685000c13459400240707022403441c4074000304031222020b80b0006a03842c01c0d140c0c03185407110494100030044075406003c1002071003075a0120360a1683c85070f04034468146654084100c1000041c1d50300710325007540c240d0100360740790b01c5404046245182c1020441c201070280b501594002241c69000a04040d0481c0000000306105109441469041c1085084952505107141007071903401601984035402141040400242c031482886850050302055444410000c0138103016198000c0c04902036034040301d040710b042c000c1ca1040e18240000c000354001445441e16100e00603041c081810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 278076303 1250 278075053 278075059
    0x1051e0d1a03340e0406050604050c03010b03040c0b13170a080702100e060703030903021c09060e0609060d0b09280b060d090309050312311203030501090b 68
    0x401d003000c540e180002c218050f80300d52400b2002400030007849580308001c142d034420888044001c0080c1c5400500d40803402540103072002d01040d03031100d040c030007a24001d6485050302e038801c0004028211701d510245070020701c105220408540e8a003e1070880e038201502c910000e039212001003001c1c1484003d041c8084106c20040c16003610f0b02e80b0741c0c8803280103e0401900801031034005040301d40c0310711440030700300c0d1004100b10303281c40850500800034640180c003100944900c1c03c405203103842c000d11200c6040e0315990ae4108241c204441110b001125820092700000244184202955060080c06e51480c0c0304170001125404141006031f1120701030588807000d000d10f901007401d0340c1050340c2c001d00612a204041004141d000108005220751280b0020703440c40c0c02d09071410036500198a4044a80031800c491542599101441d10b92261401d813021a41101c8407210310303100321550460150448903030000e40306607030364103013502d82008080490002e6075880060000009910900c40000400c1d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 278077553 1250 278076303 278076341
    0x30203191812020a030803010e0a0f0207020f060a110f0d02010501060c201c0b0f0105010f05040302041104182a1725050c0d08090d0c0201051e0d 64
    0x500c5100d20964160040401c0502c07000701c060309541303c4a0100c0010340c2d1010f0700716520b42c1e6a4000354180031040e141400b107181002a00c42c5803802c82d009441601c0e070010310300381c07503101c2c000e00b0818146d01102c1201c060000d10186480001c1c001e0113200700c0c640c0c400000d80440f0005000007400c5541c141c220303400380a0100b0742d074404240c980101c041428600010343c0121200840003444501d00e04c8110601e111814010b0410010442d050038041c0340800f64412040e40c03501d00640341010781c110100001407043c8010005442c168204031080d030303035400b051442d1680341c2003482c07590305403500032500554039070051001e80c0180c88110301c5c1012840d404400c040703064000003491407940c0c81010034070300904c2e800710f484c11060304036820700701202050b111624280400c0150082d00006181c2045000355070240555a029440251240c41d207140900240e2010100036100007001250036130400506021646070141440c199443c0c610000036182d498185000c030a5043d00c0c9a11a00003000c055 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 278078803 1250 278077553 278077577
    0x1905090c061c0e061003030804030e090414060a0506130906020409020708040e090a0b04110102070f090b0a05090f130305070c0e010e060d080a0516060603031808070302060f0c010f0903020319 84
    0x30545c80001a680c0c903190925041d00c507814110360407540d00394981e034401c00700000c1c403081080660070761051a222106803107070f69403050341590440e002140c159400c00043c400f003200ca030b0100d50180c02070350721690005050030348a84c10303001241c02450040ba44000f0000302448101d011001403640400c89a00400445069982d00240b031800a48028403026160003410210381c000e10480c0c001d4912a444551207035503801c40d803400741c00514901402000d13030050126050802a20301c0d4070411481505607030903203d080241d4a031084044054003041401c1c41424001841000068000c017400740c0d040d02d5550504409107030824014090390720034003034042001c001403034401c01da400140650400d41d8a81d102c01c1c900501c140034403a002003101d45800d1000c000c0582002c14900001414111034808035150307000c0b19034400d024000030f54041c40902c40108800f40e940d0080c00c150090344008038405d1803041d094015100e2041003100036030404540d5800b002080a44c0b10f0481506e0f240011035103031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 278080053 1250 278078803 278078821
    0x5071b0611032a0702061801020a021003060f14030a110d0803010807030317040c06180906030b090118051b01140a080901050c090906060a0c0803090d090e1905090c061c0e06 76
    0x1085160105207840c0b47c0e41400f00030f81c000d01001161075005481a50000314000c002070040099000e41c811018100c0b07000300d8a403151703c4c1e603191a041d010340103000d407034940d4442ca2803030310704c00e0019580005070550000005030704c88040c500038a400b00c0102a01419868090006840c038081500102d082c4003c000109564010b004115a01801d10039800c4500d01541c0e00c005801c1d41141d40198101803002080107140600d01d0700c641144002001444034501100e0148140000041d110b64441c01288890a140c0c415400031002c050400c8528003425000d5004d803a003205164401040303100c01001580300c03081c00b034030707900c41030203141e10345409410710010700802005010b0070b000c0c00d804600200c085008507040307400d541d00050b11585034509610895a102c003001142000111010390002c5d6108560300c20794001c00b51011103181c0342e8006003014004210062001c0901d21130715031503050b01d0b141c881c0101003100c0e850b010425048116100f03402a036140400d4100c8035481402006603500f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 278081303 1250 278080053 278080057
    0xf1813020901050910020c0d0f170c10051f08010203040203070b030121050102070804080a110411120a0b04051501081e010314010b0a1508070305071b0611032a070206 73
    0x1184c200c55004900c24100d000b03e20b03185c84c030030945400010085150b01030010010300d10b1030642c0726074298640c460715034465007a180203060090160354002c0c498a42400b070366400159022450041124120041c5111045c2d48600e543c0000d855075030010070311096082c00e00241c0050441c0411180c80c652502c440c4401112481c404240185081305c40e0008001c0f00b901202da8180e00044401d840e0303515200003540382c40742a14101d4802400c40c084260b00c0c00d09002d8502100c14038038038942000104c0c4506094402c008100308882030703490b00c1000c02a680c230700c1894020520003420b00c4160103200005800f050380a004008903001404082a80c0c0740c114003038038150b039800f0380043c550710b146036192409810520790380d550103041c1c10390114000ca8244040c1503e40031a50303680180c0e46074810194215001540c0d268005100381035600c4a0010a17521028003510440300001c0700d1b803444049400a030415242d5403801b503a03500204044c0041006002d00401005c0070491600000740d00107841d038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 278082553 1250 278081303 278081317
    0x140d1107060e01050a060b0d0b01091d180f03091c050a0605060f0a030209130c031a0601081e0c03100f0f1d1003020f130207060506040c1409090c0f181302090105 71
    0x325200c01c140317103c03a407007030a00100918111014cd0200c8c41703400815224a10103c64008060042c51440040c028001a0202594803401c0c069468000300c0824050711012840302a41001034000b00000010410481c100d072043c024580000e40d4240f41c02041082e4074903a81e440c0c407c01900c40d0520159491a2030b164014185542e03803414618640707840e162000c0283d1000e001800031100074115028100f03006031252000341ea40314415074030302d604070644480c03411105681c010017000141d203a146990045411010010503240390640e01d02060012070102e4000500452140c1c0042000451409480102d62010700c1341c175a140c505843c04c40314400306440064401d05080742103c80948035040012031802402c0c0781590364820314140759000d0030054603014007a624100071400e50b603200720f5542c2100495940c1c1d180c80c122650041081c1c541d80602010b00700c090070060302c0d1811174102c0081c0715179580e0003030100b00d98051404001e00740b15890170001a403401002440707902d80e4450229021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 278083803 1250 278082553 278082577
    0xa0f0513180603080d0c0f0e090f060a0302060c0303040507060503130b04060e0106090b0a050105041d060f0603090d0e03010e0d080c040905073c0f030e03040915050a06140d1107060e01050a060b 85
    0x14554a8a00188101201d63720181d00402c000503070252110b030200003103120780d0044013101c0038a5034416080740c0501c4110750801d100d04102035000000340d20710b074506130820b008100110300c0c1120800c0081c00c55480c0e03401065a82e40d1101d61541a00300502c0e5500106000d09009003003e26002e0080540c04020b00c480c080c0c110f2100000c0c1d00c5a45560440f0300e00140a4426a01c070b29004c504242e8811523902c661011682400c0007040600c0c2c14016801600f88400280c140184400c80c240d800050192075610120014000403444005502c00c05205404598580103ca40e5000b08820b2400c10003200031900740c0060450110300c0070258081105c401c09190401d241940c0f11401c078003c101071100d00800d8080050002811031554001405000c05582c45c0d1002d65500c404105222180d8400c810200301048041014141600c000d0500c036092a800850b5500c000c000c11203640e40402c030b0880300070742e84042c00c0182e030000344185a48052203101c00c0141d10708003d2040700601500b520000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 278085053 1250 278083803 278083831
    0x10f0f1d16020703050d0305090f0c0f010c060e0a080910080f010b0f0c060c0408070b03060307092403080d2904020c01061a0a0f0513180603080d0c0f0e09 68
    0x1041e032081042c0001140c0000c2510140101841c00401030709040e00c00c042c5900c501d081ca1900400080713811480a44010014900602414015910310358041c1083c1c60140e952809180811018071410700050b22480e03151395038007400002c000c01014110b541c0340407c50041c08101342090102825810340c0d52550041d070300c64141d40d07024a80781c442d040301146c42d4004c1c41d042c03203d0400170601800c03d071b840c03000507118113688a00003442540802c54810390305500c010010810a6120761103114a04a80320401c1d56003040240804410001648201c6070000000745100b5404640e2040c154158a07051003842d900c07007001215071180b104071001d04e01c910350001d9102024074096101100401c1b191001c5220000003180d940880e8102c031605601154207007944184d2a44560700b2102015070310b55070b500505042a618500804004074028041c650710711000c404514900d010744410340a941002c40d110301d030108010010082170075114180641c004031402c0b20b070b0b02d45002540c05040c1244100d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 278086303 1250 278085053 278085091
    0x10051204110609121f15090c050702030d080f010e04031215381903020f040506031503070506090d06050a1104030c03051506010509060903070e010f0f1d 67
    0x5106842002c00203540641c1c0c0314410741208801040655260108001c440104014000000c00b580c452510600d0b0803071103024180440040c1742d124500203606449c1a50414007954046441d2a00e6480c0c618085207155003007000c61203070313400d0580c05003003181c00c445064113142da005084083c0c031420040c865031301d6600050a08040b0000740c00102036803900a101c00320341420042d4403110345a8190b0701741002588020041004d00110350042c0f07818064172015820b401000c60094010300f40d80c4c40348501c100030004490f92184050743c0500089590041141184d17810589021242d030301c054080c60301441800c0141e0b0b03400784d459034003036007101002c1000d41c0d0310400e5100800d80750030008075042c0f000c50088203110503440c88106480c820300858001e0700d034481804681c10781c200c51040c00901c0c00c0110090a090841c003909c400d110280c112101c250b140d241d10420308000f41c20003442191456401c204282900d44200300030818080500b03280010b44000e13207003481c0014440c001001c03c0f81108 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 278087553 1250 278086303 278086309
    0xb1303030e0706032016030807090b12061c02061e070c0305030a0f090509070c03020c102102160204020306011b0b0703050106210b01020120091005120411 68
    0x75540150350441500c1001d500d40314040c1c010f0000b60810b0103042852240341103821901d00488501c404801020b080401040d601121041d6005001c2801c02c002800c00080c600704c000040c001d4841d05c400901e042d0b1601c0003d00100d403400502103080130142601807000350300d0314012960300600d409400a0b0301c91000b441c02c0e0a61041c2a0010560310b55404000705004020000c1c2040c135482e583c0e0040503242c604012a0643d17618040e25610041410215550602403440c1d01145446801560803030b903c0040011418003102c09000007090010040c1180403c1c11400e484e0411000342c421800c0180ca800b8401c00f906440400074000e65001001c40c4050703000d1080c6883e5419014200c0c0240c03425860083e1285105540c4440843d060100104019000d000940200424034604d9840140070f42d013050040c00f8034012480c10b555036030f8080c00714680004100001400084120b96454000c0e0b8240024056184550802c200c018440104640d01c001c1354180c200d9040002800e41401382d03800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 278088803 1250 278087553 278087561
    0x303050403081e0f060307050a08300f0711030d02100c050423010e03100b090606032e1d01140409080a050304060f1404030305060102190201030e0c0406030510180b130303 75
    0x230769020780d80c40b07800a40c1000004000d800101c80741c9150030300c50000c0240e010140412050fa494299040c021800e040c54070754060403150740550a07117420703201420086814400c144d200000140c00c0219500011042e500442e15981c800d4905986000c2c034140c655140301030070800740311003500d890100c00c405a01c07440e1a280c980c0c0008054070050002000d840c030081007501d04140c0600a448002019850900203a0784540d00e048003044240c5030b159080000f4900b8a41740300e06c0d40203503a102040ca41a980214000b04261041e10f15095040162241d031303100184802c584075070300300071220001807028002daa0481d0340c1410700303076141c3c5c441740b800001a1403c142a04c0002d85002d850a400440d4500c0b007a00450107603c1c00c000320380700ca200498440700404450760420102c520700100551290340840300e01800c00b0260b82c07210314103e0000f0160351442e8011b60b03195010100d04820040c040c4182802c80d0014805040c0c004010f030348405482000801003c011804c00988200303040c02508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 278090053 1250 278088803 278088809
    0x150709260d050307030b0105090a1202030a08040909050c030109030903020d0c05030d09090b03061b25050f0609030a020604031407020a0e09161d1306090303050403081e0f060307 78
    0x8266a60070040c1c11000340301c1c3d081101c8a60000303061560350140c80d40a44101e45920102034400492541404203d0b402d14900f00c80403a05171141030240c0c0d01281814001e00007900103a100426106100c1c20141c2c03401c0107241c491071103645441a85000a07401051090440341c0c19100700c50302c04010304214101d002c81c0e03440960507004880401c01c003260301904020035030740785000420441e8803480903d951142c007154003150110301c0b0000710302c0346900c0fa00a0310714030b40b2500300a444018540108031052140c0e08c2c003118994002940d03100070f01010300c01c0070350111400300250f091501d42c0760001d5031120043e002030240840c074031041d6003102c085000c0710b0703c5a80240422031125a80c41851042c6101110003800034054850725440b00800d102c60780c4102c881c000c421000b0303804000e071030b800320902c0a00056070f000d071054450400242ea50140b03548450103514001034034a018200500300c500014070440c84c400c2003010480b9000100040c3d030741c02004000c003007902981c46401191070141190 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 278091303 1250 278090053 278090129
    0x10e010909050f04150507020c040e030d02120a0507050705030d050a09050607080709290d1e02071a06010c170c07030506150102030703050304060b0109180509150709 73
    0x10400183e50b90318500d0502451003800d034250300455108241080318829174140006030400310003103030185050380180408680001c192440c06034922480c1089034030280e49c20350b21004c04c0c003c100d210842032160a074003007414207105180c480e0f40c0d50b4191b102e114401042c5021540d410100c0c0c3d4250f40d5522000c001c1d0b51040480e2540d0500300b40250080c2411522040019220040031803420074010001d26404404020020784040003111902103800c40d192407140c0d2581c0d448120a005103c0300302c2c072680c101c1144016a2a109800d20100b072070780c03169820050806507000d22015036881035106c1d003030703d41000003c1c04038500c0c1001243d640c031610502c1100e510660401000340107010440b18041e002160100030710203102c8005a803a4003c100e800350100e001031001901082154014109007a07051606c0006a510b0304072074090107050140c0503c1c0c441e81c507000c102100c00100722443d01b14138042c69800b080e241c4508028404042402104110305e0800010742e00c0c1090745001d624202400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 278092553 1250 278091303 278091311
    0xf030e0a14011506140d1a03160306050a0203040206030c0c070b0307030e19020306160e0301020d0c02060a050402150d09140c010912033005010305100b060405030c010e010909 77
    0x4400c80a0180404115101a250709094001803160213094440903a0300c4a42140307003006c088250b031100400d0015244462803070f08204200c0955014051005040c50002c0707285411403c505028048400c010304001c3c1c190320420a01c0007599450301901da110003980e00d0540da0f442042030081c106041e540c030064a4083c040f0900520f50313056003119902c400e056044406101d00150000b0804030003040207509134100310041015014900844400b0b050281031444030784000601180c00c991003150300303076581551810340300c1c0d400d81e06000494010540460500c120708280e0005003403141484210340100b000041d800c4814000743e0000da400d1030b086a50845010001203c154845038840300140c00200010404268030780d10700152141c4513010703078441c1c070809016403481d100c50003460b46501d009190b6141c0d150320b2002038007945000c0c40c41100903101c614401405101a40c1849070380510900060005102d2070b200000c912a5101c03003407a29065002c2000c0060b40c01c007003240c210381c02c540c0c14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 278093803 1250 278092553 278092583
    0xd0f2f09181009110d180b01062325022404090b060c07050108150a1401020f06130605060111100e0601091a040507050c0a0f021e0f0d0606150804110d02010f030e0a 72
    0xd00090345954261600015140e40030169402b52142c3c1a0007900c00c44201d500c1440d1710071042c1b00c603013094805020200610101008901100c801c2070150428440004007803040ca1240d009000701031200303503881420b150130410101d0702c0da80c0d1405010304104005000901e030441618005480540c05007406400c0340c3c54005102d48500c400c28002c0c05072240321040294040c0005009100321207c142d081030000c03a41d0f88841c06000081c09840c100b00107040c810f4030710700083c4102d15618441500020324540088412401e091050340031305c040c01d280004007100041e9044002070b44030760465001906940d03219080d5090700a00b103128a8a11502030070604000007403400e004064001c58090b0401d04038107107540c00c040c01c00c0042580050070340410b040303207040c04001c20030608c5c0301e00d0340420150f0315205045185541182440005001c20041c03009022a0f0144a540b00c0030580b850140b000c081d0f00081d2070290380c001130104140d6030351000b4070916418010101c4031907006001d160010320f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 278095053 1250 278093803 278093807
    0x3031f170307060506030604200a090203240603010b0711150f0c01060902040f03030c0203100507090501090506070507050d0503040302040c050d0f2f09181009110d180b0106 76
    0xb148000301c401e2440c08010400a107400548030f0722886d4070400002180c0c112a2100c1d40300361140741a190070046032070b0080b651f9282400603600c602c80c80301e0381c64043e07007a0842034602841d0700307007680d400b442081005000781889141140c030f8007174102e60809107000411020071500f92402000c0c61050b14003140d14602c49030700c10024080c2c520b40e80024840b40d46c440820703004a118511a00c1c520955200e82040020b0050300202922130000b42501ca840b401c520901c0150342003103d00400003140504d09219640c0c0003545480580800d540bd107003000750980d00d29540c0c100130300605101d00103000401e410080d0030801c0b5400f6642c041c0c0180800c054442c0080d12079005400301d83c4003203041050200300418588a00707542140070781c50707520224000020050b180444400c10700c1408004100322511900c500f00c040280184604600c8102e01e000100c801c50a41c058200343c518074240300c40001c03044080000d48112460100e0700207440c2c40e000c60104400040031340000d1040c0c030020000100c02d070f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 278096303 1250 278095053 278095057
    0x3090219030f0b090c01091715040c08070602061302040504080418050f16080402040b040b120c01170717071e0c0c050607151a0a03050f1005060303031f1703 69
    0x1480f462010f0f02c42e0300c8214100e40c43d003548400c1d241c00590003080130407039842460b84a07840300e14039806845141d030340315203c4089040e048905486140300802c08020340002000fa45004040c20b1001d0540382c200780d000c030900c0c0240c1d000007a100d40c0d12100818140900d80044900400900c2200000c2d800726860a1015103000c560b00750104103410300081c0000019074120401c0c140b00d640d00e0072280e889a0820005115030188190419a941c4501c010b0351100071401c8440c4174490018140b0403603001c001412000780400f049040b040c12418002003a8004504ea24070721750650220f942651490021030320302c4414006960020780511326001055002024410034030701400000400da610303242031000921a210005140c5090f40445203410340345640724803250002030b0746440c40ca590707030000988040800d40060320281c01102c6020000c60781008000201c10340d10600340028500800003e85901000304855200301761110b070721030248000c2c42d1010180c18072003000d00c8803245090b1955569 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 278097553 1250 278096303 278096333
    0x601030c06050c031e0405030106060905030601060915050702040b180f0108071401120e0706050a080105030c0d060905010b04110703021e0307031103040504090f11040504030f0309021903 82
    0x358058900400c07582d205034111640d210080b0015441c021143c10307110b02419003003034a00700c0400c2c103103c00300e215542030007414010b002c681e440c00304a50400081600303200c4181d00130001c3c4003240b041088086840081441c0034038040c208140c96a170940003103000b03406840125540100780158480d101c05420700418010341c0c03031000301010781c0c1e00d4030000b0b9541d08160154090001d04140c809049603c1340001783c01c2da01000d08049105024082c645292144540041d00840c6010400b00e1a00d540066020f005060450080c130503820303080c0c0400c030b65980308680945801d44618002d0107002c0250804501d02001400c10841421028a0705d5556040500f0440c011300a4011040c01160360710b80d107164244070803000e5071520890744c0e020f803105a41d1138090701c02804107000000f40c41e60b4502c04ea0403070500801022110740c0a40ca410401c0521000c1440c0c031852500b81403001081c0d11240314400c0705040d0900203150511800001c603800854000210020050480401001050b80e220461 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 278098803 1250 278097553 278097563
    0x30a0c020d050301120c120b07080a091104020706090507030803070e0303030417070c1e0f0e040c061211031801050105010912060908040806040c050123041203020f030705060103 78
    0x124818008a07200c1c0c40554072100081c10520040c040480d02003030304000f40b4803454500d00440c3d541e91400020307580c10f520640b480400181040503550b0440700c101e9101d502d0301c02c10002180e1590b41c0ca41200c0c0344200302c50007075901041d200100407482d030101074000e030440d007143c123065034914011000350700841d0300b14000b4500810519003410f0000a81e0301440d03000112801c1a01c2010604403603070814007055400030000000054078011034140000e030001c240c40303000301d19418001e06501c0d40031603902c01114001d2160400020403075444280007581c540d882c1607030f20b0410400c0ac801c083c000390184240d9000e0f0000c188015090740d80b00c0f17078044007084802407043e42e98800040d103221025104035080032805d401500f00145480d4410740a01c0d210310f40031800d040d1901c03040362824108503001c0b03030030750740001d0b06004a40c2c000c031400403100400d41443c94084171401ca10300d202e004510485942080d6034030404c0806000b88017298a408400045a4550709035062913035858100f0300c41030391 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 278100053 1250 278098803 278098811
    0xb010317091e010f030e0a023c0109050a0b1e0d020d24080703121206030b0402150903031e0403052b031a010503041103030d091b03021c1115030a 64
    0x5002c6000b80101e250201d0b2807005000207421540900401e8000c414100680100300703140c48101c8040c9c1a0b00166100c150400064540089000941140c00d5500100d220300c3e1103010400001d40d5610480d86009110700c601302100c190158090f01901582c100303001480e001160316044000e00d0741c414030100e078018500c00b41020740c030651040380c8902d8bc001d92440340c00c088014804a102d40380001000c404a28044038004201c100380b400f01d0703001e07030000c031000c0c2c9035a0140019803510000e42140740052900b014035110b15200001e6983c420f241e885000c07924a240c00b00d40c050200783c00e441c02503421a0641c0c150303000420344009000859500d0010248405407250324151087c411801012074845a83c00d102c1000070040da04c60b0001402103402645840006080303803000d10181040909880c404515150240b030001c3e9101e82d0107a1107050300351003005c01c1025a5a0511030066009500e5001280520b0b904011840d440e80030003054025004403030044103510500c000f140b040b0a0703003000308 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 278101303 1250 278100053 278100077
    0x20d02060a02040602031e090d060b0f0f01020616020f010501090203060a0f050a050f040f0e010c0e0108040c03060e0f0a050a061a010c1509060e070e0f01030b010317091e01 76
    0x7004070700990040200603071003030101289000c2504000c4072801620200d031420071810b0400551030500c0f00d10304440043d04c2d4802e0f86114100300070034200803e4115200245136035001e00007542e440c0c1c01401c1ca900078458201d00014140280030002c203440c500b400034842580c5a00e0448003952041c0e510750701520005100141088000311030f10305803100140342408071460720b01007000050350801c030b0320750041e07680070255031a00e1070344034008005d03100c4800803458030320030600603103802d100560490500942404000c002105041c0c032900381c99002e1800101ea08024240c94030304000050209520310420003504203110b8001031407190503119100c1848040910002003864001d0342c0d00d454046840b1035603040c0000c084c5607503054214842900000c00749043d8032560f05035580040aa4410b800c002000e101d010310721861140d00013080313200c0103d03d51641e640d8003102c60781480082c0c01455210804a81c410048080340c0c9450002400c0c01c00c40d900690481071550510340c6800d0100b10510141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 278102553 1250 278101303 278101321
    0x506070e0105120c280c03030e01020f0306040507020c0a030507050a0f150c060b06070c03020f010c031209030e0a0603020a020615030c040f022b05070509090103020f010e10020d0206 80
    0x45200700c9107105481d450740c0f01c400021240f9041890000c1d0020f031185c080c2450003440c00d505060381001e0b42da58210b13a040d6030901908452140e0740b091403d90040011501c00c981400c1269003141080e100000d4a6881e504203c0c146403240c01c9036070384141072030800000e0140000740b56064540484890b25096034400030008030340010b01c114000700301099541d1400724018101041c07101e00038003012a200c00c170140010a075074040380d402c84002003808001d105600b4400120710702c462003800c1007400214076031000740a4100740517042c80a503427122400c200f0184110310169070224094116114140c0350003001d4040e401580d0700c42c0040c0300d040b0016040708008400050180405400342c1101c0f0382003018440603046a440c0c908415408202c074100d84220340e0170041c2d40000c005515405045460291401d0b070354007426180400105100d66180c075510799541ca41100d9040314081070784242d00300140c80601741c6d10703990b0b94018440a4a00e01c2c0b107402103074030500d00100364207440b010347d989100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 278103803 1250 278102553 278102557
    0x607020d0501060f08240f0709030c080708010f14040b0c070803040609060b0103090312020c011d070305370201020c030a032a1a060d060204080c100806180a0b0603040506070e0105 79
    0xc0306c0c041034440780101d0144014009215003001c51403804404882c0c07070741c652400e40f10140d0b101c1c607096400b006d4100880a400c0c030030401c1e080041402030080d010300c42c08461a446000d403001c1c0801200b8000f18055940e69030440e0107942d17000d00300c107840c0c0c40c05040510003170081c008107440050410004202540c440e00c0344521b001d5058890100b005010300b03025009410001c5900034940da41c000380080711081c3c071005150100f0640003452010309520300b450410b0f0442c054600302611070001d58040340c9080801c04815801c5122402680e442400102c0c0f5282003030b80301303680501820017500b0070b0660041c10115041038091000300a1100629440b04240c01040042c0c499020241d042e41d41d4008501390310303000311005080750b241c0c0c0c00741d0b120802240e0081c1d11070162980181c0040c601400e11881038420001e503400c0648240c036014002c583c040801c841c680a036294000c0009800441039801000c502c0d401510300c0b40c41c0d1600d07103481542d0718030680d040d8020445517841c42d0003542c41002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 278105053 1250 278103803 278103853
    0xd0e0303060906060c0d03050a18111906080103030c0206040e0406051012050a0b060f150703020c01030606300f06050a0b1c09170705030a0305060f0a03020607020d0501060f08 77
    0x101560141e1b200c0480080c031024080b82c06103921062880604840d680f11821410b00590345070071541d041c0810002580801a501210240290000c00c40c154000c5540d41c110303034050400080c00e206070310015120380b04540180a00c0b8010318140800d011640d88564480e00000954000b8a030311000030380c1e1440c070800402002540310320904400942c141c8001a080500074201d103219001203000501030000c0201c00703005c2c1d10703004103420b4207044c0e04000303101c6814400e08041086c1c60a140000303003034915074946d0310305079505a1018401c0307149240110841c904201400c2008100005c00030000d0030551203102d10501d0401000b1a100301c00008440c10380c01d000300c07043c0504c1c000840080290080391015245207804640c100440004400149042c0784200003541d52003420b4035003e0226000070340b89034040c1c00d100008a015403904126001030f41d0b012100c0c00c1e218035a40c400030b5480c0040420040465017400320000b07100078200504016200b44100303840300481041c080b21004c0450314 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 278106303 1250 278105053 278105077
    0x20f0601080a0f051905030319090201080109021305040203071206090b18040c0b07111207080d050c0f0102130608130b19020c07080601080d21110d0e030306090606 72
    0x4016000a01032014410b071151041061310b0303c2c90b2171005410f0300b05903100c0c800e44154000004201c0401051032a6000b41c001000c3c0400101c20070342c00080044205000e200200c03a400104165104403681d03101d001003000520956032440c207035600506d0740100c2c1c844e013021036091a5010a60f080c20b4001e480c9207002c00341200062170020311403070141d690040d00c291031059500401007140c0b000c08000700041c900401d02c3c140f1154454092100201d40044d42c5082600a107406105000003c070701c10b4209a40c5103055174a40e540703d02010309044c80701484078559880000d404400c200c01c064078000700c5005071181174850b41c40d540d18501c1c2051185004080c0c0008000080c00042c1c1042122850000f500d001406d014003550040d24000305a00003c11582c45a0010081c4910400c10715125407068604680c408440d00f941c4140414401401010140c61300f000f411006201d1042d1808104903150510400c010310030441d0300e99105881c100c0c0680c800310b0000348141468030444054661030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 278107553 1250 278106303 278106313
    0x706090e0c03061909090605040c0503010e0c280305010606030b03121e040b0c0f0c03191e120306080c01030c050904090c080d080f070306030b2206060e07020f060108 73
    0x8001085030454a000100700c10642c450b41c085560245c034814420071a120ba44001b8603801c003404c01e000c3c0f491150b441507200c0da0418801c0072803054007181d405010102520400c040b290b2107007290324800441b40340e480700c500c1440c1000040c0a070540044045903001d880400642030902d05040e00d8540c50031040280c2c1030108145110008541e401c0c54203001c1050001d41081d4032440d0f505aa603020b0b07214040c1c144e00c1628003008a0740140511442c20100714018060441e00302e80c114841510150080c0a640380c80100507c009800500c0c1c42c1e0751603000b090b4140ca843d0680000e0010492802182114450040301c05031550103845112182c0c1d1980d02caa41c180039401c4100006410f11150403241881c5040001070303910400c010400d243c03940e0340c40307000c542c0c80e107042c0030341308032000174403c00800d03080580c1080824800000d039600244143c16590580f683c3c4c5080d1004101c08c000010041803402c58009148221041a41c0c00b0b0f0b03080d40c3c00d4952820f80c09100c559240380038041d82c1129001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 278108803 1250 278107553 278107561
    0x12101b0801050604180b0402070303090203060f01180209060f0c03070b090c09040624060905011b0c0b0a02010e0a0c03231c020708030a030603020108090a0302060703020d021b0706090e0c03 83
    0x902c0341140c0304c03034845c040411246240c40204060717070050002140803e403520350b40e40440c9418081c05900c00040c032078054281d803500d4071b0040d94405650450034040d6000503856071644900c011070300c3d5541034503d002e940b404072100d40c80e1b407a401000107541c1d000403d000b0070095800450f450703e21140050250006840316201d20004280c00100b00c59401c61074008421407896031001c041c014030003a114160307240d1030080007409601c000d081c035202607030010008500040c148840c4030142d402d001c00381603c1d903034540c1c0164018100011950382e035104840e0b8407010000c070721104c07a007501d10070350305d00154a080c071010036a403120304d40c00b0030001d81200d00000c40751103100c400302491010520469400e0f03a5035200182c115800180c00e2000a5142d22092081d560000720b055003240d42d0100508114003d502c000307481d500b000e045001055000104429182c1564042c0d429035881602e13040e4007002d12541c900c0d90340b040c0d03209510124150850000350762520745110f920488580901a28507a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 278110053 1250 278108803 278108819
    0x2d12070b06091f0303051e0301080304170703060212180c0307150504090f0b0102010e28030c0b07080604051003020f09090f16030309090911010e12101b0801050604 72
    0x50018100c445240480d00f0321403c03403601107025001503010fa100c0c10780c0c0e54060140700301c028603070030f90780c0100c0e9004000401c120a0000210740c100c50a40f580461020744100905040500a03480600858000310b50424420340782c0003e103000c2e11300c03190403000020405402a488500015006515400000007040180340c071300d1104581000c9854131914050310307014000200c68268051400a680d208072010703155809224031410814000300030034070000e00032501a441c07010030b41c10101e030340c2c4000e44040c01c240c011501c1c003440c00c1d480014010149001c51000b485410103d41051145082001054003200220408016260060181ca8180c0180c40500c00d80703400113800c1c58121f228040d403c0350044c03010b02000e803185841c4040c52240a00d941401002d00c80543c011084091403c148100094595001202141001e084c04000301d9801d03800250012101010f0702001d00604810903450085a0b00400c001018500680000000720303008031000d000034010940c10500800040c00303589 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 278111303 1250 278110053 278110069
    0x1a0901180f0b06121e06101209060e0d091a04050409021219031e05030f06040603060c09032307050114040807060c0b090d0509122d12070b06 62
    0x516034040104001c044071000c039105612250111000300400001c0c88845400b10802c902c1758040304e02c3d800c0c5582011400110315280314018134042c80440201121024880c1e00300c1c8045580189080100455014180741c40f10700940b050320020704410004a0b4281c5d05018801c00d00466410527400d0900f010280802410300381002d0b07900401042d600c0c50060801c0103048110400d507043d01e1515461840c015121108051082c001450255440040340c0c0d400000e034ad0f403240745600350781841d0b102e03540440d0003018150000f500c440d06015440705a150000000c82c222071180c00425181c2980107181070503020041c02400a50704050f0301001b596104800480c40340041803603882c81c142d0b4440040d494000341d68844008982c0988040301802207420b01640c0c00106840036201c6000100c1c40104148102d041340e5104a0422201a103c030f03c04105404480c5442c49441040e4042d0600304402d980d02d800c0544080e200382c4000346e400d4412003007517136541c0b60700050360b0300d03170b510b841042040306 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 278112553 1250 278111303 278111321
    0x61d06040c061d060f13060302070203060402090c092e0203040308030f18100914010209030604031803080d050114010c0506072d20070b070215040e01091a090118 71
    0x103100040c2d41a9540d940304020190240200c83c05c0c1c3d6030301840c15800744009500d5100c2814188180304074405038602050035507001b41d04940b0f407940c3d0341e2440c2e0030200b2802803a2416401644803801801c00d1060004101c0300140c00c00200c026424900e40c00300c2c1c0d0380c0702d540001000da4101344045448804140c00d2682c01091800306040d001c04981c1920346400d01400c11000c0b1540c50f200510103009801c5c142c916040b10802c020342c03074440c8040200b0394614001c1d02c01010001010a00303900701103c03440060107107510104030380d601c3c10302120450151000b8024051040e60302004440075602074140da44040341d010b0060081980c560300d041d076240c80d07540410b0941a500071032807407249010001c8640060701c5600c840d560303684100100125020b0f1000040015408150305015010b54441034580701981100c58202440c0d60310904072050045900a54003420700c180003217108a82c81d0030030654054801070038500c064880c002c2040201f402c1c4038580c0c0d250003010300a8043d11540e0014848 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 278113803 1250 278112553 278112587
    0x50a0302011d06091005040f0902160f03031b020105090d03020337090813080d09091512080c100b061c1424090610110a02030604061d06040c06 63
    0x10300c031084c03020130040d070803c8501400048000505000b20100c24140b5006131131104801c50400c034824258230f070343c8007040001408a079500c180000801d0701c44d4101c084281e082d00c0d502c007601140319002902a02d400c0d40c806119010341104110740910034800c0d40e2046c00314020319901500c20400c690707600d40c2ca8a1107041d004000c031284c1c08494105020325050284a400b1181d5100c07502032000942c40541e800504207904007210040d40690300c9000041a40c0e1480b10000b04c17494030300c2c8100e180031119881904482032a0400310305026210016100750601d46062300c2403204000c4110b0101c40400b84181d501080c18403104450810b035801401c130107000b07910006440c50324412803101244040303a0920b0000c8040e031010350715114074198106000c0081e10310600b54200480000d034800a20702e0840200001c043d0701000c00b00b02005080310075a00542565a10300306030802c403016001902c94107080280701d07040500381c0c001c0040c00510441d049030402c06500d05103034088030864440300390488 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 278115053 1250 278113803 278113807
    0x4030b060d210215060f10090504060f08160509150112050108010b130b0108040f140f07060e0109080d030504021c1a06010f0c084b18150403060f09020307050a0302011d06 75
    0x1070b2a11079204002c050800c1a843c41c133141d1a00440394941a181544000b0204c49a5400c22a5031910400c1c11740014040a08ad580030130a400101d40e851441c001c070144c02070604000003020501940061081c4000741c4000104908088443d000d407a802d210040c0000d40010011307000caa40c1150200e1154405c1480441c40c901c00c0f00980e01e0b001c041c0744501c0640c4c000000410800390032846a0700411000e0912500080c5800c038901d842e000360741443d006068607000000d0440d0358040703008100181500d8240700d40011800c02c9161901c0000c5003610b0402c1103004940650300070001c000400407150740343c0084600982d00c505c0b2a0b000500b1141030140c01c03a9802c80c40c0d0304d5203540c0104170203c03100022181c088280c8203880881c2e444c0c21000080c1d41c100002c0c080244080140c03600520241d03800880030b420050000f2081c403817540094005447e000340740380c2c619155045642034a00031400c03504000e444100f00a40103205100c003d020510642d1056044400e403041c0d00b00700b80c00200028 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 278116303 1250 278115053 278115059
    0x6100c080c01062121021c0207060e09040b0a0b0102102301060e030a030e060702090a020c0106051c030e03010b03061e0a050c04030b060d210215060f1009 68
    0x944160400100c00c0402d944942041c000c41c40388440c804d41e850602d100c1d0805107030168417044900014001840f19515140042c1c3c51141e00820010510300204420622010618100252690214068000010031640102100d03113030900c0c500d401180c1144d0f03080401e4a9115400000b802902203540c158014071900612400c11445442c56200707001141c140c5281110f0000301021030160000814098003038020441502d000030701000c480c0c0e02d07083c43c10074242e0b4040000d11a00550380029400140c20040000114803500501840f401a400a00c1160b840d0030411207484a00718160840745041850000428400e8211003c08440034000189228203c004a400c0a6003110101c900251131004480c0c07000d20340c26242c1d071211030098104000c1c02c042240d071415201d180320103054030401501098169813226003103103069502c45031b054404014041100b02c419605145213025005045040b549008012000c034842d40c0010003c2044d84442e00070080c0e10003d00400c0c0040141d040701c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 278117553 1250 278116303 278116313
    0xf0f0b09011707090302210a0312090501060902090319030f0c08090909030a0206070c02061b191b0b03010308030408071a0a020306150903070b0c0f01060b09210606100c 74
    0x2c207015494070f036285507110303080d80144005a194035a80594481680220402c2040702240b0984482d03814170f890341c011074a403000007024140326913010300705518015002a40e001c080c1d00030580410b0982c00d9810311300c00b80f030384192260b00c4500080c0205454020703901005118560743d8070031511880c180d03414101d04502140c4e0b40c40741150450f21a50000032105421901008aa54003410901d481515809680c0c08280704d8011a800c00c880341c0132007000c140c402d1009100b0b000c0620035078000c00e91a40d0441c103202081c0985401413401030104071602203050074924044038142c07a04181d02a2442d00c2c0c40e5188642ca0788004000d550041d007041c4940c888103d20500f00303000302440301000da12400c2400410240081035468071000c0d03142000300a4040e10081842011108c2c130102480d103445543c1d03001400c0502451418010754a02000445d4042c200405042850404c1e5408903d040c541c403205203400605070040c942507400080026030304e18010158041442c420301d000d0020028507510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 278118803 1250 278117553 278117597
    0x121909060218010e10090b0304020a0e090604060c09052b08071406060405150f011107060201051807060c0b0702030702130903030b0102010506010c0f08090603010f0801060f0f0b0901 80
    0x11207501c0b403054401c0509580e009810003400c12044070042e80300014400050301503050f074070610301c52035000703c001000e654810441301c0082100c000140c001c0d103030a460003030f1038201c05c840850f0044c3c80c211112542038414101502035440c0948001031020800c0002006402ea003a1480f803030300381407186040007c443e64090301c400c074032410218200ca05460241800c0c044018810303130040d03107800204421002c101001360b441e410305a421120001c19840101c56120303010041007400e01c80c8400006035070794154031a500c00e1540d9117022010113100040642c841d40c0d103102e01c80000f101c480840c00030840c040742007a0042c070b0500480340703000c806501040107584108100c05825580d080a0300c14150140034038407026100740f00030002e80c42c0bc140064030007001d9100c080c0c40c1124a4070105d007046814003c50b00450230060644c2d80301d60b0f460290304070495150240075010750034a08002580021070359584240c0e01c5d80351590344c0c09030604104c29041c0c9c05c03240302d460401001e5504004e0b14044104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 278120053 1250 278118803 278118817
    0x2c0102040312090815160e03010f020c0a02040b0d05060c18090c04080d0c2402070807052a0a0605030606070c080c0102010b150d020a050705060f100b1219090602 71
    0x880000f868a0168035604004c510034002108001d031008020402d00701a02c5107808107141d00f440c4403003800600100e801000303400c01010301140300040c280b403480d40018414803824400c507401c1c0b00704034540c0140070260240400c020182d1388040d0104580301441009003900c150844890569018244006480c0c441c05070740e0340320380c018005803d102c05401804405155041420040c415001c1640c1e00465420150314010403407a603403225516a604a4048801298001340c9558a5445904100f612040900048500d10040d5200c0c065410080300081200210060a00c10040c2c81e180051328694001007000d50f0080c03007048208000b1f41d2841c441c0c006044240000c0044189a200280c04c580700681c0b9107118144456000c03d005070384c0c0b8100e0f090140b250b800503032900c261800130742c2e0b58050924006e00900400040001850010641e0343c4104454004140202d41d102080d142d1841580002c050342e001000001c0c41d1491009280c86000c0e220100c000703241011500d80f04100c2c1c010b02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 278121303 1250 278120053 278120057
    0x21e18040b060a14090105012016050316060210022a01051902070c0302121207060c080a0507052b0603050f010e071d0c3a2c0102040312 60
    0x250900460b428401d60306005030002481c80004030100c5000515545e20510440c4d042140c4080084241c04125200810b160300c400b00b103420b40e4040d4099507900c13122500079a030007803241070300400c84140c103240242c1c22500b01da00a0041070464100d484044c0d8040300c046c0c1000300d5980500b401d0704411030b070040b01c032040f1400002428180680e05141043c03c2c01c4032005894018000c2c0c00c0454154220708048a904442d00030004602e90366a030700b0f00e96262260b40c40032030049804414008681c00c120a0780d2115038403041d282d03444e115000222501039404e0f0001403400c0c01040d01001e01004000090030200480c0b440b00300b00001204240c0f40540c1003140c1d141c0201201c10000c1c0c809004403107014156802800700035042c1103242c91000a001c00340e1407109600408282030400382c00c1124000700d0b1100350414500700020460024804000c00c0d0003030301c0f803012041c181d2544a0321030001880d082030258006c0c0414082c000141002c1030900c0e0125550030440040010b00d4041704142c110255 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 278122553 1250 278121303 278121323
    0x90e0106030b18010609050601090b2203030c06050115090e0405120a02100b060a0f05030a1e1e05160e120a06090203070b0406020c04090302031303110f0409021e1804 73
    0x40c2d03600f1420b407a0154005160142404103010030faa80100800e0141c94100800c2ca469000905648550348081c1d04031043c070b990b04803400710a00d588056550040d42c01150180082c0e41d1701c1582050080c64000c007000001c05400f41400111105a082c0d90403d0242003282c05580081c01891500e81c000170210707015034483c800c9040d40034024000d00c2200c5c070f021282181806070300c1d003001d058561004180c404100c4004002034080406512100310340445482d061402d400543e42131009021131100b00c041e211251785c0d0511041c0050040500c15507407800c4001283e8098407041c4c03116113050224641c40561900030000204040108000450107400c1c046800300d0280181801d00031030b0f80242c1000481040240806900002c01c26203130780d820f0300c00250344805030a089056001e2110401c000c5d0103171590000078806e000b5a45d4045000c1294450700c0c6008240401040310400b0030020f4000c07210410f03c1c121101c1010414400c4807014188500d100f407800c003840e04110f4100c8080300e02c1414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 278123803 1250 278122553 278122591
    0xa0501140a05090a090c0b03010f06090b030912030a09022d0306094306020c0406050a031509050a080315060304050604022101020a05040504150f090e0106030b 70
    0x6044110520400a5580000090a190100d83c91510041074121095290842c807010004200d050a00801611815540321350b100d0300c80c0d41c0c1903d5944500c4002842000003c41c1410707070081202d01440814008000204091808090f02d03007008040041d003d0ba1150344001589031030403480241605019008441c6580c0c5403104620700e803504007540254858020480d0700c1c5800159201e581c00fa54241e51188a00e00c4c01030485065040c20b18031700e0451b40458078401c0803541c43c4450a4400039020b1320031444940007440102ea00c2ea10405920015040007080070840003068004c03010300300310001c54400080e032074081c685a42c405088642500010810100028011035144a030b0800c80300540303142400e41b1202c0c0c0e03660014102034030130848410760f0880b401800c00014043e041d0741000b90344404911720090420341040c0318290056007022900303040c4071811003520055039120064040341d1b5062030240c0c40100f07072000030707025190350310003000c4041f030161040390317101e10081c5c5004040403007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 278125053 1250 278123803 278123819
    0xd0609060c022d01060312020a02010f140a05090a09020a02030a0806190605031305060a140615040e0406020f0301030602030a15030519030306030c0b0a020d021f090201170a0501 78
    0xa403035041e10119002003205242d4040c9000800d00c01a003502c3d10b0911001002c0c200500608084c3d1000742500c103100d6803640447d0300420346566180c000d80728854210303264034050315000e40d60074804942c2c2d182080182c038014050400f0b8401c803400540358042d0a030b1140003903001c90344141d410001590010501c10714241e0310040c103680c0150103482101c01d0f081c00c1d200507524210a23010703a000744000131001480c6c40046c0d0b410510001e4004040f5802400d1007030190009000c04908002052544030015485081451303034500c0207030081d08180c1c50280341201c3c000c0c00d528040c00c12a801c5800b084109412405503018502071801008010b039282040502c0000302c0300010782c620724182c404842007000c40c3d00850041510304680207681e460b0146840d00301c0080c0f5584d0002055020184c0001c070342241010040c141600b0703e83c00300c9451166aa0b41039030360303102110054041610407414010303a00ea5503000a04280c3c4103040035190102c03019262003080900300d070040121550790004205c442 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 278126303 1250 278125053 278125061
    0x19051c1e02030415020f070308030c070c0f080c19060807020f0a030e0f01030c090b0901120e060103030806031c050a110f010e2512020a12050d08010e0112030f0e0d060906 75
    0x1131840c0c0014206c0584590a01c4e8035080280320180c10443d0200c0080e28001c0f090085500742503001c030786c50725031544841c0444085006400b0f451072034441d69a600400c0d04090707880102d000c05c010b070321490f03003484c00300103d800c014002c01e07501c11402100c0c009c9000d82c10800c211000240701e500c540080311034078401c1c000c01c20302e0704009a04043c00d1461900c004c580040d55141510101d0001d80c0d07075941a000180c1c0c1c402c3c040c1103060381a9141a00309401d40c0c402003089810789200c1c0d1742d051426102e04042550720134010207a6214110a6459546c081d8001c07001030041c10342509050055054000c01075042c40406e40c00d40841da51620742200b4400c4007407001c10060a001104003041100c218000701903443c00f070146401d01c86140f540e00056656500e0000018844000d1820820b1460700d00300f9210300410300a030010030703042c0c2d0000c204000b0f0070303886906071340880f40c1484450146031021075140d07482c100c0303403404e00c0300c0070124034081e03165840702d08401402187c02268212051600ca0111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 278127553 1250 278126303 278126339
    0x2040b100809390109080307060b030705150a051c0501081507050408150903090415031703070507120c051606090801020313121e08040519051c1e020304 67
    0x6190303c4041003c840c008401d180c0d542041001906244988039401038030520b0682d040040b59220124100c4100b001581005144130016416581102e50394400d01c6410903440c01e151504203070034001808042e110340060300c1034038403a008558510310040201400c407282078002c2202a0004880c1d03000036445056000c4d0400307528034000d840c00703143c0308081d61202c0d000386150030009000004540703890b00420039100c007008010300c02c02400001d80125403c800f640d2000725484a904213108030681c2c3c800e805c2d20710499141d12980d1414516554196034100344c5039040701840040d140c00c03804030320100005454000e10301c018030200c5007440c8024003411041c0d41300782d20300e0703004000b080071030000c0e50780401c45a40e010305c950788480914a8151020409005010b4548007004100441d40da4401e2096000d01c1c00380044da012010311200b03144800d0210200a0b110350302c0411042c00d070398594003850f44011031502c1d161000c010505400d40f00c1c2c00c0c2226480700168804076080c82001d80301404a404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 278128803 1250 278127553 278127583
    0x80901020d1e0c050703020a15140702030a06090609150f0e1b1002100509030a1b02010f051303020a0803121008060606030a06051f02010c09030809060702040b100809 73
    0x14140880ca103080c09020404002c504002c405114038007008001c0201d03102640c2c0c001c1c100c00710140c80c0c2003030303003081c1d0082d071014000240703400c0090307508080c05800c035050b00790090081e001c2114261038801c05002d0380ba00c100c48655458500320003250b00b00c604c04010b000604804a10707038503e42004810b44240003103000c455000203030001309880100c3c080b150f044d0000d131350000111200d02c40582c1040c441ea404010b071a410901045407508002c002016441c800340c0b21100806055116011001c0b4110030090201744c10703d8154400d0740c011800703420040c0081c13007010a0541c4a40c0490b104d01380551010b421230388041042c080c1050000e002a911032845084001514602001c10f80c0e40c070000342a60303009140000c0072031170042164010070082c150192121502403101703424004c06c0100001d06c400154642600710f19801c3c0700d007282d0800c4a800003551800c10f0b40344130030000d842d03002c058126402540c40301d503040e10361240c203080d014925290300d4038032140c038148080382d0170012143d00c0a55 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 278130053 1250 278128803 278128817
    0x70b0f060117010e040f0b01090606020607110303130219120204060801020a1409010912080304050f010c09030201030b04020d15150905010807080406090209090a110d0206091e0d080901020d 83
    0x120382c0000c2520604550940c19681810303101d6041c80c195210700441c020344549130b80c40c00131400700545d4000d0340440c0c9480d801c0301d400b070380d40c5013040f42e443c1090001e003541c513001000868076449612140d041d02e2750004242075110300050b0111143c0c1425584144100e10703440c4200419440c1501c1484010030040c0000d6185c9048140700600c6120308420000b4a6040800d1080b1316034400c0300210054666842c000304c3d10b00d624100b40b102508100c0d400c9410b480707980070105c0d0405040c01030624505c82519100002070a50f03005402901402c106284c00070340c24410403014002030b0250384100100c801d80082d15600b008072000f000e031b2012001409008010608110b1a613002e00c480354041c8043c5032007031003902e0b10302e0045e024001c03540020358040e00000601c5549800401c408600368498141585446158011710102d0854108083c0d0302c4075040c4010301aa04080c0b05016646510282a1040b5000040040c1600c0414203040d9088030020640101c1035030100041584483c442c18418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 278131303 1250 278130053 278130077
    0x8070812070f030f0903020603151c24021309060f060801140d081926010515070309090e01020a090603090b19020403061e0501050a03030503011a090303070b0f0601 72
    0x18070b00c60002080102001982800c164100d07108803a040302440d40103091079581c0c102554201d000940f0442400d100300007010204e80700c41040e10344003242c15481040f0003080c41008410034003200c60380124211183c0c0030402c08004038440c4107203401420b41e1040010328030b820140d241c11600d02c0c540002040c0190140140f061135040c0541415403041140d954942035654600f2080700c0c00781c0c2201c5c4d19400d40e110f14a0768125000f002907a819020b144110380c004030b000c20a00441c880c28400c0e183c10044c1080300e1140900800300400400f4002e04018901a0f40c401c10141110500d41c40044203941c0442d440b614954042c8083c0300420561909100c40040780d116600e030340c3cec1d02402d401d0700841c00c011080030311305403a0140e9009641255007000680d0311010170180f982c555541d408201e81c030304000800c061030503115910580b134040d600c3c1415a801e050b44110241010440d0014100c0e060000f02e40708d40d4100300074900c091040a580440d400c0c94415801c02d594041c25403414042007040d81 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 278132553 1250 278131303 278131313
    0x216030b060f060c0a030903060b0a03110d031e050a1706012c150403020301050106030e0a06050a1407020a030801140f090604150305060405060109020f031612060807081207 76
    0x6400400440b142c0c0408095180000da55104901840c1c299001d140341c240e050680000d08042200e0089805000744001001080429000c9000013858640d0a9062034150b040c40c01000b40064030078103020301401184120040c500104d1102c0400048000480c0600c996003d01c20701c485044545444500e8182840040c28060031030001d11101c0410708800d01842c0d007500c8580041c68405810115035240c101480c950b560f20501040e07020f5828280002070700c0c1d1092146403640035003400a004003001c0d591303a4034007070701026016084107511042c4000e12034083c820a44c1c054a0550000c00c141c8074035160103444800142e1003028000302600240c1407a881d81a404140d414003103d890485954417000a801084a920840c07019400c000d0080100000014014080c500641c11181c950307a0f19410ac00582c42032050310040b8910902c00300d21030401c41c0d81d1504c403180f40741c103044807002341d520788080c21a581a402120b1031751018108000091301401280c10003070780c240020385000d441e6220 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 278133803 1250 278132553 278132573
    0x141c02010605240c1221131103070b0a02030405010314060604031b08030301090c0e031612140a110a080a0305040306020a020c03011103150148060906050c0304020a03020405060112050f0106021603 86
    0x1028150751504a204023042e81c041c03000b140070f0f054070400c072925208140e500a44c0c03504140280744c0820318094418a484611200d03035413207441700501081c030301805c59480414015880e642803d803218021004a0f5a02c0d051010314080c088001001034000703400600240828540d404240c025002044412001050385000704e040c1c800e9500a02d500d49210b01e4900c82108200b40f0383c1c0740354003510180c1c0040001801e041c0c07080361011101c00502c2604c40c44800d03140c0720203080040108004200c1000061455005030107107600354016241c11031000f01c0031a00b5540c1e1402030000b0340400204014158000417a50340c2044000e03c0c11801c5072808960b040c00400b03c08250680481808404000700d0010324070300d00c1ca0f00d004030003060315406185488809480ba0300c008440c0346041c640003410614294059030300c201c1d00280302031400ba2943c5c092000400001d45003d0401c00300a600050104150140501400c03408611848a44c90f0480003400d112500d4080e05029440038070801c04540d006074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 278135053 1250 278133803 278133841
    0x409020312090d02040e15072a0204060e070c020301290f0d140105070905041e090c1703130b03131202030403141c02010605240c1221 59
    0x503580c1c441d0004009400030528540007513000d03003401640c9071707020808103e00e000403041e0042c001c1c0c1d80d11880c40c107131082010000c21b82100302000301c0011940404108145692b4000340001a4241d202e00301c20900c000308480a03004145071001040840c01d0074401d101142d82280c9070031004148001030b5501604128035806d01c200746504004500340c1d0307a004003928440e4081e11a806100010450501030042200c14002194144000158600b49809081d00a8201001c0b51050040342c0d0000401410322500c1518940800e5402050001140c4c002200d20440ca200541c1c560400810318007035102103402c55120076600b1f005000040d1951601d102d84150f21514002248183d90b40407851070003198000750070302c004e805a10382c4c402d50100305041d622580c0c050403a01610f0030441039007652042d115560b007024031602904401c0c0039030140301550070080c406c0f0f2407500d8440030800f0b1030000304000c0702c102144000f96243c51801c2d045030092080b140c024400301c0030b16026102c0090614014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 278136303 1250 278135053 278135083
    0x50901120911030d0c14010902010504051e060a050c010b0d0f080307170c03060102060702060106021f020403020d03051c1527060f0807080f10021b03120a0b04090203 73
    0x156000800110b00958650b20102504442c001c1e07800000041800002103000c0e50317184005074020013030350b00c10700850381c03001d4040c1c440c01e2a0525200900040c1c1818000044010f0f4411144800c02e9803150000c111a20082d500e180c0c0b250007122b803603401c403111100300b80e10421040458900080c3c28000304002c0341d4200718050f80341c0e59411001c0c0e442400041203501191f0160b41045031540542000d5070180b04207a080ba44660b4504409903138540080c01108056440b503c801100001d84402c1c4c9034131103501102c05410a40c0e203a01042000c00720010480110f14003040c0c0100703482814800d4551812911801c1c040c40380340d40d80204002c5802e018100011011450000c0c82c0c800391103000c1d4918694200820940b5a2580b54400c1c40c021030003281ca05001d1140c0000c1c1a040004140411900020103094550854a121402903104289600130401103206000ea50780c4180083c10751008000c02901036407406110321030440780d541983c02c0c401c030b18005111025850000751690844190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 278137553 1250 278136303 278136311
    0xf17031e070c08160e07020105041a1e0901241401081b07050106090606030b1f0c0b040501050601080c07080a080403050408030d0603120c0f15020d02180a050105090112 74
    0x504011612803110741000003d03210b202035030318050030a031507284200c41581c0a0115240c03500d110403030030f940d01964064800310040342c0071182e0400e03200900d9081729040720030351903018600e5150107141004841000e11a5510401545e9841c1d15a20f42c3d05812441309904548a05000c060501c003200c8030625410803d031440001c61a05d610f1102c50440300380c0b00d0019441da00c5900c0d00398081c1039203004040140c1e0501c040062240e00034000c2408a84004010000c00680503140641d2902090300180070480340c2465540032072550501540914000e800120741c1e450010005400c041d40501841c000800400440b00460351190a540d980c0a40b071034845015219401c0440c0c1c0c0c1d000343d8105640d54000050308903c2096654010000c5a1080c005590070119910b0140c0d0746007405803024000f42e010f04071182c005544a02e810200030ba03503031302c01070170480340c0b014140898111000d000080030404030100c40c030340b401c400050000c0c0803d1a0952401c03500d040000c16001103600b50320041915 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 278138803 1250 278137553 278137567
    0x305030a0f0204080c03070e061e1809061f0608011e030501020c0307060b0618090a09060f060512070305120d0603020301320402101b0b010f17031e 65
    0x1a811000016003000c0040d034032281c8031a0510745407600a04006e109102e104400265035034091200ca03c9060014860344009800d40c80b154207403004500081da2140101c900b10060f010414501030240e0101d1000f08001c0c907000c1030001070036456144c0d0950310300360008100980c0d5400311003035040d2920003480701401d1080440300200d180440d0001400b550000c1030090703007490004040d104160255805004100c4141d041c812103218500200102e05050f541d25142414170007413550304107041c040c0002b001c60494039032108680e050054040c000f6200d110401c076a14103460214110304580010301161341c69565184c3d07a900c0c21241a00301c076400880d200d20246407991081c00150b0b00a03000303101100a020070000740760000f02003004140c8040c040d1072086100e0840b80c2d441150301421070008660000d006940303d5000e400c81882c40800304030006c001a001040a60091544084188800d03043c010000c941440d030002c80c0d070007a40140048024014a440c1009566108054a980c1e4180c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 278140053 1250 278138803 278138821
    0xc0e131212140103030f090609080d03051b0d0f0e15060103051b0c0102030603060709030b010506090a0305100603060c020307020a030213110a0c03020c0604030203030706271415090a030503 83
    0x10b524140245210a42c0001007456007003801b080320060603907600c03855140c031000195641011805040601d030701802000380c99a02940c0400d8010300c1c90030300702080043c05080380400b6481014000019a1640071600050320140680340312115542c02500f031540b2117030516a524200100214101500c910224030a002030300d205400c16800c11000700d83c0c1d94081032229002c1e45c17003542c410303002e4030526000400d414802d01d02c20090b80c1e8402c0c000000740c1d00c0c01c0d0400000750003400002e644a4803400000000600c100305269840c008160f000c941c05d455418040d040781e03920032056080d900100041e40041e40d41c2c030451402e503a8100c40c861068909100c0e210000c2629040a010b41e43c400201d90619582101d59041c0180c440e81c00c407001a40b100b403d0000354021440000d4040d03200340040400140c55420a4924001c1d8900407a120b0144c00300385c400d482800311027070301c00352203403030000c0401c020a1111800401d1484200313615810890317615942c4500881c00030b001c220005c404110b01c1d00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 278141303 1250 278140053 278140061
    0x507050405130605120a0210030e160e07080a0b060901120b090f040b060d0b151f09180501270209030d11010c0311030105011209050106030c0e131212 66
    0x1041c09840c062081150300d1801c802054a400784d2882015664111904a0000546184266406013821141ca41841c10682c06030191003080040c500403805840c840181500c4050004c2250884140795410a0400540b000d00c0141118400034200f4141e40c100d503c4100448209507000c0c40d28803440c0d40c0c0d1001c050300501650341c05580c40030441c3c041c4807004040100749030280340201407008254840b00104a4031401d04140140000d1104000ad00b48140d02181d42042c08000380c1301244042140f1010384490050343c02c881d010940e010028880855103040f03501100b008284100555418041200f40c64206408182405c50f41041e5044680d4202e0701034920814005e4200c0741d403400c0701000a441380788c2d00040c0284662030110007034185c0b4440d000e15401c1d8813031f40c07038910b1650b404d010044a80719400f04240041586170f203180c00000c2c10904c6914025401000c0e03030030550b130078155002c0c0b8400b805003011100291100b50300000c16070460642d19085810309004031002030b02a4500003030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 278142553 1250 278141303 278141309
    0xc03021818010605060a230c030a1b02011e18180c0c05030f0913151703070b0c0901023c070608010b1c020307030b040f060303120e070b0301080307020906041a0405070504 75
    0x40f08000c2382000619100201030405020152905c000c1a000720000b203008100c0350801070300080f54400700b40e80d525007a000040c001581842c0040b295441c02c0302c10a5080a264064803910241101d10920b40728030f4483c402d0710070083c4c500296070641640320180da0b40100103084a55150000b294003030f99132800b10f0740c114843c8030081400810700c40001d2091200c020b10078942c5547c26410703e06e000c000c0210448200300d034442b4190324540c840b20312a0079586c00200015040d80324160010000b0048100100a10101e0380b208040010580c102d000f901c112501c0180d805901c180c00510980c0c3c2c01c800e6841c155452580926120040c0400b158002100c00c01003421261000090100c001d40c103402c0001c695405403010700440320f0345140031040302d44600c80a40000c0c0d5001103440423010701e8102e241c0c880840d00c22120740c103890f460f00c00c885910a80c8942082c0c0d00014503841141403032001c00d64800000c0301c0400c0b0741035061003104511350307034803401501c9030350b0714000140058081c0080d00c010f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 278143803 1250 278142553 278142617
    0x2150f101a03010608060409020d030e0303090d0501050933040f0807030503062806080a0b1f020609071a0a0909050112061503080906070c03021818010605060a 70
    0x5103000c15075200c007030355000380203440004240c0c10002d030981c00c15010f0082c4440e07026000c0e44e01b400380b1341c07802c40340a072580c08081d0781400104213020641e610300e80c001408030b01030800015141007800e140e5281026400b4503032092155840412415202514556400c6e1004102d0388515640c03843e151000044d0584001c10881c404102c8500340b6910001851242360b0036504001e0070788407030305405681e85044180c10f40c1e2410719103092082e58030034603800e40c00c411103910200e08400c0450015043c0016070010300900800e26010303040403a410030000e038000315800c0181004134180110515218a107000800c0390340700000715020325911a101e10700042030600c0007000b203543c40b000a0180c650b0711050585902d400c00131800c400e03455072a040390440782e014449074a440841c00501c20680c0200e01c1c144d0720484224000805612852808080c4198134540d100052a200221106284155070802d245a02d0428213100e103440e0807040300d943d000070b070400b010613a10540c603030400c0350030061014803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 278145053 1250 278143803 278143829
    0x9030d021305100905030c04090c0e0109091e020d023105011706010f0501030e0a150b101704031103090d120f17010e040609050f0a020a0602150f10 65
    0x400707158003828803000d84504032144090764007600e100700c46006450040c1a4560040344440129150039444946043c0c8a4200246020350710070300034403190400d907c80d8020540b110121001c00020340c140a1800098000b10f500843c1c0540100700d0f806801c00000b4000c224801c05480e050083c5641c440e04560040d45031100c51290f045110040c0101384203c100003524280101d040404c082160741c142c1e0759600c80c0700703d12840d003030044002c4d100200f445d55030f074011b8110041c08900c89140070100f01c20b200740e0110700214503805000c070100101420300c082002088690880e01900d00e00950880c5e0141340010041800e07880b114110711a003c50f0316031010b02d466802c82000110200110301070b44903101d81c1882040c603c81541c020303a10780c605907001480100184244e10007048015085800307614002014003165403620301e40314905080350b00641c048901e40782145800807a040203000302e4406464152180100e032700b0304440203800e40f01e07083c43d43c50000e4140712000a1002c02411507548500f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 278146303 1250 278145053 278145067
    0x7080d020a0207030c08010e03030a0506040213030305040519270204080114100902121f030b011d0a021603110c0604120510150b0d110c030a02150903030f09030d02 72
    0xe55986190f11040b2400c6050302e40c00100c006e018840e10300c022483c80c0c0a94559a07480110a0080c1802060b80b075000d54213006540d043d0300142070b1a40590311a4640603600c504020420580c88186c145d40c10410f40c00c1d0b042402204401009a13800d85081100b4007000d00700d08003554044e011f5038125200d01e600e00060103c080584030003150060300261100c0d41c1d0326440e146594203903c038040d4010781480c010300102e8010700b80b03c003480d0030302205003001c10344042e00d075603401000d9982a4021011120420f240e4081da4075120005600011044001c500d0700b404241c5950800c032180801600384031040f0202400301034207110640c580c1e880180b85650b11915001c0404120744901c0040d03943e44100c0300c242e46c4d4010a441600c4000b046585404485450a01000c042d036000d9800315800d1500d0781070b12014251a100640008003e00003e161241407100f4000d1800c04580750700c4009401c00070a11148034404403c0701d07002203074009422007a07511030b810145907100701c120305404148001103407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 278147553 1250 278146303 278146307
    0x70c0302132307020601050607170301060806130504030f110304050d0f03020610080606131b0201020a020c03030f07060b0307180c0306050909060115020a02120d02010c051e07080d020a 81
    0x140c102a81d1044100140114661811000c0702c11910080580c4c00800140724524001020300f02051144243c002c1920700c3c072070040c0ba6500281d02c03a1001c21250030a0007554506580d00340c0c55004002010800c030b2030983c4000701450403034400d8209109621031440340c110700900449014103000b91450a0000d01483c14440501402506500500903107001c11004c0c2c400e550317540115020301c1e00808107602c0c1c043c204132040301d1140c80011926a00c2064006503600c100c0e81152804c0c0c642c00058541200940c041d0030b08010540e000d202c2d800c10071418185070882010b0310482d5070043c1c00041c44810720700c042898240c16410131292462031248070f140084140d000500d8480980d42c1c18001c19540310b003480425501600c03800709a030002d400502268280210042200c011881107030312406854001c20072107008003030602042d4100e600e00c464015024011248040c5862070510315146114840d8049041000900700190708006400702c18040780c03a094503110242000c00b19034882940d000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 278148803 1250 278147553 278147561
    0x10b07060b0603010b0d0f090605090609120909041b08030403060f0c03060e0a09021f0c0c08030406020319091d06090903092808010606020f01270602070c030213 71
    0x100e6032a81401c2010699052800c2900d04075620320703166904040c11282514090b107804a03040078481c1d0341d40301c0540810b2080c001c980c0151a4540500410f08150100908001e401c61200c50080401c2203000d0070307911244800d03503116400010180c11682c16150302c215040c10355022091511000c5000310520500394455890350070580303130400c00c0310b102e04401e505a8101340706400012580701d000410714070041d0080c2016030301c014030101851f06281001c49040b6030340340e114800178107403200089c03c0200d00200c070405040440000c50429182100081d034071300c035034607400250100030502144024080c40004c1d020344011180380564070721100702c0ca450440d0486030b50703100300e05100100d002b00c440030084950414001c0c0280c0c84d09003061408100690964008183d810101c0d00d000075660020301c2040054201d550240c80740800a00d882425030700c285100d103010041e032000e0322120542c1400070100d401c0c1e02000140c0c8540e03050400b0000f203036507a440603401c41c0075019102811a01580 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 278150053 1250 278148803 278148817
    0x51006141308010e03181c0305160b01230a050a150203040b03041410051014030c03060406290105040905060f0a14040f05060a0302010503280902010f02012a05070209010b 75
    0xd170506c400d40075030041040604101110b034502a40701480d010200c4c0c41180284100c1002c00c280c80c0e026456907035075a481c1a4240d01590300100006001c20009005c440c031301441c00c4003103841c0001c40341071000207a01000c0c0c48c031565600501034800b030f8240701e000f80300303460040c240c407401d0300d03102c1c036203410000b24039880b040407a20b050040200c140601070b21072103502d020300590f8944034902800d1021403042c901d10254000d0345441003207102c48407076504008140c8100c4c810b100c046050b54001e0454422b6038042d01c0154031079a440c406650301079a110041d071302240d000c02e00204058a1303110205005860025032789410001190002c102c4818140c400101480c043c1d80820504030160803500445509903112070740308103400030401c0036601c07990185800000503c04118409001011080028864611040131039140d001c04010743d030300110780c0044010755000030700407048014815200c40408560120400c0e84440e000540a0310070000e545403542c2c0a801000c044d40c55448524050300004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 278151303 1250 278150053 278150077
    0x2030f0d0905101107150c020a1202210a02010507031103390a0b090106050607060f0c0f020c092806080105220807170406050904051006141308010e03 66
    0x9101e1030480e8802c2c8824907100c40351201820a00341445e241a800d06d401c0e000300d00070000390b0040440903a48008111008009442110500340d1a5106000001c450b0500d06d1148800b480740178844904041005100710340c2c246400341d9982d4061405480101b00e0700f2180e40030b0300c4089000c01d10b0709080481820000b014a4a0800b007d60486500d02e50f1030007060005101e400040d440c0d4001030356001d609410503460f200108000d91140040f07801c036000142c0a40d40c41c0d85a441c3e03000001c400344500c903410307071162600b0500d803541d0300e1000e0f503145664100071b802000e452000880900650031394031030346500c0e000003114900c480000d440140003a0700803c1c4141d441c25020610318900c54024046101c05408000300014180d1250007880e013101e481555003414080d810424081e88100a00c0541582e4980c580c9070f51040090004030f83c00281a000301000602c814010142c10441d54103800421000c640d46d1208039041c103124010701903004015641c00e02e0700c010004400400508440d441c41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 278152553 1250 278151303 278151319
    0x3022502180f090606090c0d020304061803091a0a090509070c050303091006151e0309081c0b0109051c05120a020607020d03091505061809070612060b03010b0702030f0d0905 76
    0x1400410481e41011f483c1c1900e0150104184030345100160042c5174402e0086200017440079440e141441c04111801c01180043c142c42414002411300c6464101c411580c03064080c06c11041000142c4510203601034240702c1c1c0c01c880000b030740142c412814401d0f219404010380351030b8103140380c42d2507540d208250458001404e003580400d030700002e04840341440b1440c1d55001862420303824601c481c0120034002504044d199118900400c030040020f01c00301200490b1024044900d00d001c030304980d40000c0c000e0400841840401c11a900c019507051809024404c1401780f551381d140c81460600d80414148101030007165800f01c55802003401c41c8181c0c100c0c0c0944010102100003102113640041009048091081100c50b03580499440543e0100021b0701030020030004018240c0d81000031640401564002c810500066501c66071040340c41c02005800d210b0b4074108401c41c451780c001405201459070001c90b01100750355007086610041052803007075070340b020510310000b004485903024043c054620 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 278153803 1250 278152553 278152561
    0x20d0b03060c0f090d140604060f0e0a020114040e040f0209160203030106080615071416050105090904080f0d05010801050601171803131e0603022502180f0906 70
    0x2011404078800c010390b51802d4a40f90b00c0d0403070401541c0220b206903410100c55032240c00000e049801c01c481442e264402442540340600d07280701580d111102d015081405c0c0400420043c8001a60310790342682400c0c00a102c0200c0518000203028503805413280007140302c01d010070320003982c1c220341c0304c03034025251148545d84011038803485031011090300c0c00581c000c1004010943c0b00b140725680101300104501403901c18212a1012500302e03950507100c48520383e10946004004110700744401034035031051300340036207040000b801d14001e0040031802298103000190410000d0000c4899242c00094440d8450100e0740c18070000380002d004000b110f610304000700f03d196018000c440308404140d0500c0585035075603455026441044200780e01a44414090010158981440d40000e810b07440c4421640500c950781030240714806038002c0051503c10007543e41c5c140c00e2824207100c4014405450300344040300340b02081c0c2014044038108100ca510030140702c051980303000c04602800b400000c607000f50311 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 278155053 1250 278153803 278153809
    0x516150b03070b07060203040507050405040501020a170903070605060d1a092a0d0201030b031e100e030a08040c0b070c1d060a090c2313080c010906031d010f020d0b 72
    0x3145000301d03c00e1039018005600080c10b15002154414490ba080e0350314a507a91000c0744c00e50f074058904817110794020502c4020035601c000701d1b1b07c0020030203a2790401410006400b5840c2d00c1200c2c1d0140200741c45000090381912030b5050a88943d50008003e283e01c4504011803030341800170b03602c8100301d005d400c43c0901907055807030800c1d040c03a540e000705076101842c9100300080880c00740702c201d0505449101c200000c0c5d40c240308460454990541c0e40c02c608000c2118942407240d101c800c5c40c0044d14200c404401c2c02d03400070641d1540c4086060112003a203940c10701000412042e07020040608002800c2c0003004850340000003140c1400490040b40c0710080700e4011080341c103c40407a0825000303142000a05265001910805600e082c500344e0a41884c42c1180ca071900c0115074400c2d4440041c0d100d5143e020555003000030000f590140c06240c000c0b400003880f045080c0320305001c154542901c50380582020070440112800c20008015150142000c400690032049003da89945440e1200c0840c4c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 278156303 1250 278155053 278155063
    0x8030a0909061d090109020405010e10080118060504080403050d030c0e1807030c0302041e06081006020d0507150203090a0606080a050c060f040518430516150b03 71
    0x14010003030143c101e030034807494299502801400c0c0480c035900c44400c0700140c0c83d68410203010302400200c04a0f5840e0901400301d044c0d105501604181c0c0c0340c55015040551004402c404c9031742d1010001c280c6444504210b92603010340e400c050001c4c029484071400d100d4160b403140707446d0000794807040c6d403030b10350403040081f5074a0507412224040b001c84001488203201e50f00c4040903a140382170060410307484004008041c5503842420703149005003c010f10440c2d8001502942c4180c0c500c0015071500c0c2030500c000e40f0344c1c0ba14624901803280101d108010000c07070303070303401c20402e02c9200c4d04640342d1421105d1642e485d03454500540380c4a18007800401c072035070041802c000c1150008002c0c150604803105026070b0360310889000c0c007050000e00006c1025501d00d110414044000d0f402132110f81814810183da029024448100803150308503082d00100080c0c100141c003080c585c12108644a603050151564854000c2c1102d04104101c0c1c50340805c810300c40f01c080c0c030011a243c1003202d001142c050640e50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 278157553 1250 278156303 278156309
    0x6010201061203051b120d060e0c0c0a0308061f1707080c04061107030204091b0f0312050309070f0617010918021c1a0402030c01090501120b120708030a090906 70
    0x1134810800211032001404031112240c50071400c0302c600b00c6030154000c2d80354024010211106445400400c8070003ca40d42403034000200350882c510301903091504035603c10840d040102031003080381c002602e90351048401540c1c0e039000f14114211002d4007200a10500007040c3c0000d50005840100f40414420320415201c0e1031900c1d10b443c0341c141011030990300388503c000c0c1d01d500c6216244020006032160700412407094070400740c0f40b029441c2031000d814002c031389d0b400c0170325602011030b001c01c04101416417100e018103103070801d44e40d292a40f60520341416099007004c5c142e2503020f02d0010301c0f2035000c1c0018040c1002c1d1102c00c0f203942d0b202d52250301542d002d106560003503480212103001500c2e100a410140710352510300341c3d00a4505680d002c4802607148011078590601004100541c2411300600d0107031242441d104800c07034280000600003626110302901000d594003210146900d40003840d0610040d07020480e10030329520b0341d4a6a076030303214400741d00c00194201800585d142a600500085e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 278158803 1250 278157553 278157557
    0xa0c020c2b0501090c050a1710050703090b0403020f102a051207120c02010c02060c0c10110d2d050a0b0405071d0303070201080a05280506010201061203 67
    0x2a000005100445081400070800001980c28042000181e802d00c00d0b404201c1c411030003400307060301c0c24081101003031860f4005680000320b0500209010710100300d0100c3d420641c6800038240d110404200d004080158000302114150b0040c0411f054001030490035210341c0500300c07440400400c0942c1c0c10b0b12071102c252001d4604806e04100d44c2c1f810310240c00c50103040e0b4500107041003622060010703688002d130368500105026402c400e10f165924007070301480c3c0c065030001340b20490070f03c02d00960764003005103032a40392880401c84c0351152609100c42e110a2241c52400e105900c80014003c4103030307201c01503003000b1500e8030001c900944804010b8600d0388000785200c040b089170f2489140082c08000b0100e143c07095a509c03403280304c0d507114422140181402ea4074990403805244401c020300416180b01440f81e03000740174800050303900896181d03001120100115003500c0d500b8884a07000c40003911409004881400e01070b07442c00c25406244a54001d030300034480281d8a090003408500d1107000a00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 278160053 1250 278158803 278158819
    0xc030a120507033b151605041512060807081f2a051207120e0102030c0406120605040227090c1801090302131409010b030a17070602040b030a0c020c 65
    0x503840d00d901e03103030b1103000c0c000c1030541c4a800041d0711180d09201c109400c10241640c503c2c01c0c4085031b50a042c0b03100720310016042a41c82c2600f8580203400b0b00c01030000b0781c070406c03984031680c0004804e542c02010040c1b0b00b110449015685901e0429100d0a00700046440350b1001180851504403502030721105060000c2c240401c000060f07266118081c40c110b01d40c0c00d1042c00c00074100902842d002e01407007900c040c1d0310388060300c1c50840303030310140c9500601581c956030060040c4609000c4000c02c5900f203a0560904c1c01342880c480d00724402809040c1e1001d503000b807010807003142c01111414030302100070000282c11406010748040010183e400d683c2c0000c20b0030140720340e54150300c180410442e400700504025980990302d0380050501c0c40d0451662014540310107400601980c0c001207a50082c032040001d0100000c0100420760b15040d05078090300000300c6061002400d40e100007140c04007500082c00b55039454480342d51090503442501c00510702d03032801d0f444096851012403640015200201050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 278161303 1250 278160053 278160101
    0x1002030702070e1e0103170f030106080402013c091a090102070602011b0305040f0609060f15030b0f1e0112030e011d060c0708061e0609070c1203020c030a12050703 72
    0x1c0d008820440020048001001803c2c08c403403a000140d4024030441d51100c14620301071000400380714061404000c0041000d4200c50008001030b000c007074060200c01315000300300403c1c108840c002800d901c26064030801d003880c4900c80d0b40308002040ca0076400e8080310201c59070b0700307401c9088481507411120180c04619151854501c02c2c0c00180c0c01600490030015054040d854441c22210051001ca4001c3d5a07124413500768442c41c00b40110262940c03200152441ca0f41c2c89406401e0030080c40f480c03081c407a44e000035038036540300341100c076560426180030900c542e100c6000c1411480c8a62064012902000501c25907620402203620300c0030440c2541040c4011150031b0200c583c000c03180340b011a024452012850303010401482d84910071501c10b000007811a00b90002780d290b0041c2c5014002c481d11010405840d400511114074207620500c54102d105032502d045009003d200f0700c00b01c05003c001030240129911541108007074484440400c000d0302c0f401025811200d1381c800a4010b11503003c006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 278162553 1250 278161303 278161313
    0x60310090c030b030d2a08030103060f0e0a030f0206010e090a170405060703031d060f04030c0309151d19060309020a0302040908071401020a0e121002030702070e1e0103 74
    0x1c0724800302410302050710210354001900f040e28002072600094010200c5050074414002c580c80d0707804400302c400c0c0903003400b17407982c0c1414403050001070f01440e00c845e500c01200003580e200c08041095442944c684989a1400504400160380c1940062080d40f00115102c0000601d081c001c441c00c5008202c0150181c2e540c0700300c0d141d00e071121070752454188000207003038031003c0041400d01e109540000304200012523001c48814402019a00f0740d03c000108800068503820303841d081909400c042110881d40d240480309540303d40c0000ca54454099084400715030070034036800300c0e03800c13403185001c080030304500340030701d103040c64140b80c0b52200c00400030000710f0701a07030040480600141010b010a5140c0d0042000d480c3c1042c002c64031316400040c0380041c406050981c0820181410096180180310100100405180cc6045110300780903c00c071110308078200310003403101e642d0b03003800e45d12440e2119029456040605c0b80c2580c8066400c009201480010144000c100035040c8040e1107900316203403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 278163803 1250 278162553 278162561
    0x20c0307051008191d1b0303070206030a0204050a030b07021e03041518060e03061609141c03020105090f030c030f130f030818010503040510180204050f011406031009 73
    0x8209040810303010048000b01c85c02148214007007444071100c540044800246840400d025503001582c26240310750396aa00803003129442e0350100e03202510f94452103804030017403003158450780d80541c41c064008200303c070303c0d51541d129004580a0343c80b000041c00f4000c18003645040800160303041080240000550300c0d51001e82c48005140002c0d64078401c024503030042906401000200300000f0002074149020090a81c2c030069040192500141d0390b81c0281040d1603e02611b041c0811000c00200d2548410b040524115142d0702c0300700d149a16814080d0003040306440b007200b6405040c0ca50b20400c4000402c444010103102c0003940b0b0009601203544868228824400680104410000d03454039146c40040103140202d034890366941000d5152801205104211814403809001b080089071022903c4c0c4803c000c540c0000c42c02c0c04000403840c2403401c00600c002c0d403252400d403e11000c407070b0030b006140c1a648480c1080031441803e40c2001000d0004039141c078000709800405110100c11604 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 278165053 1250 278163803 278163811
    0x41206050f1302134215030f020c1b0405060f090a0203060d0c0902211e150411070b0703110a0c1703070314150139050a03020c0307051008 61
    0x80004004d204034202c00200c0321801c460302030b140440001103030411040c9817000941422140b80d50303403541c988a025444842280421401c0c59580c0d03070001c0c1d480340d154044880610294050700c9441d820440400e4664403074881a900440c03038140000e50600382100310010307450001780464075a0b507031020b04601a42c0f0043c0560b0308140180308201c00115124202030241c2032210000d40c640c2c1c0752030394005201105040ca605103803a040c1c28010b2004060317982c2c0f114485c41d004004060b40d02c00e2004078000011010980d000780c13810410b02c2c24030380f511025040c164450071003001580c44074502101558061030402c0000c48040100080c0b0b58095408409141d00c541d034070030a100d0000450108a8000710f40d1400465151a4400107a0070554003581d80b150061500c441c100c0490000201501ca1031461407507001d00001c101c0540a118202e0b80d001040d1201400c0d07001d00040c64141d032200100c2400320050711a0800c052503d141c085205001e0b078002801e16584a401a18125202e0708050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 278166303 1250 278165053 278165089
    0x5040215030f07080604110f0c0705030f250f0e07031b09030302060619170a0f03050406091a03070323041412030f13030504080102041206050f1302 65
    0x24015203200c09040000d50b1081d00c40da0415861494840005803d0002c001c01142c407441c90300c002241035141c1a403c0c2c0302076005802843d0f4660b41c2d071045403440c012480d0001a4140705610684039141c4e80041d00c0d8100c01031014080421025407450402c1c12441401801d501414102d8144010000b0003c4140c0c802018030303000c2a403030503203040d084504440070078000004400070380c1441030540401c8116041442640c15044129002c40e9104201d031407406006503500d14a04d880d0600c100800c514083c1640000e04c50b40650041d24020b00954030520413480810051640040c84001c43c3c602062900b0910031014950340e203540d0210700406200c0302c4c9038011142c0e0010003480c0101d00300d002d81305034400d81c40900703042c88100f01c0301c0c038201045a103510414020402c100710101a510f219400410044219030900d900303140c2902c0078092030b040124250300c080303400980082d402c035070095818080da070104010303103c2c00303018412907608036401600440400203080060500c0002040c1c446242d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 278167553 1250 278166303 278166319
    0x1203042c060103020f0d05010e1006110c01110a08040b0d0b0a0b0403031803080c010e0f0a0302070e04050708101a0a0503031602040b060708040311060406080c0c2d010f0c0c0204050402 81
    0x341801b88103c410a0f00301040c809011001c1250605c402100e0703501910203410588011210b10100c1951040750300a07460410070809902860100100b010440b196400440d0300d80b12034550528840b15002082526013190038420600e170b0341d0500c1d1110b1010340f0200840d45140a06688054518000c80c0814152044025400101081c10400034054025200c1d00101d2a080032020403894000441c100b0003054104080880c0000c4d0000340c4038044400340c0711201241d6641b414004d04010007036200d8051400340c600c0c44200403040d80c0c082c1241650b01140282802480c000703010080800b0b0007500e81651040014501c40c08060407a000342070300c000d1011032a021124003240003500414421212903401240902c00c02000141c540c0140c2004c1e1220703030400d8682000140403920180c2a504001030016084103210000d120300a040d1004102924800080500c840b030003242240000e80301d0751038449802102d000c54080c1d10048821035503500040b070015000c110080501074022684103000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 278168803 1250 278167553 278167567
    0xb0f070509040614040b040b0a05040f0b0607030c1205040e0106053108010b06030f070c03120204030c05130c120c09081c1d1516021203042c060103020f 67
    0xb881c05000042e00c1012084201c41c0c0c400d0050005660400e81171601c118144848a000c41c0ca925070107a04464003220049200540155814000c01c4090011a0001380c0021000c0a040e0011020301d0000d100701400710400b10000c03401c0314580218059890200070140041003194856030240039085a00320381c2a00c6d280c00494008101103103040b0324074181002039000c01400400384604407540c103007690780d02d00c0c52400741c5410807050701c010440014402005130074000e140c45001c00b00e0035425820811556185c0b00d092401c80c4140901c1914464003180c110009400014007512204441680f20b01c01e054042358051406040891048020000ca508000a084008000e009000c001d800ba4001221040b084000d114020b0105040c1e03150140b07540060717243d01c680e2202e006803420548096101c4808107101c452041407544040c1d800300281c200081c490b20080010720494a20140780c003440898003941c0c030030444540140b000c042c552500041d1081d4040e400510340078080703c080c03500d4040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 278170053 1250 278168803 278168809
    0x8120301060845101e050405031314040608010905100b1203030c12060307030305190e0409030f11011512020111070b040906060504080307150b03071409060d0b0f070509 74
    0x81d1449400c100d03e040d0320319024440000d01202c16001c440301018014181241c94203810320b40208043d01010350b40b0000a414414140140c469031584004107040c2566200080147d030043c25118034030581c9080700005040d541481103004055210028066606030781a1140003070005c41c50164010540d28001140c620b030a0005620a46001d4011601c43d407000c842510106001401c07240640d018440500110b0b81140540ba0109500318080c1800441218120340c80716403555000d070024100703c40e181c02c240e0006403101000a09a8030010121010340d1001d090307a41c1e0803442c0048000306172083c081d12074400e80d5803100e1401070500424000c5084007c5142454503803098a86c00720201d014085890680141e034010602c1e440c09a05113400c0440058507031140040040c078079004800d41a0080500f034000c1150100e000341587c2400345c0e11400d68488032031a08410344030b003070540006511868000da40007200e030f070032841d00001c90703542c1080e00204c090003528000500c8400d018000c6259 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 278171303 1250 278170053 278170141
    0x2040f020705030d05010602030702061e1c0c02160f030b0c0f070c03110d03050d0b0409051c0908010507020c060a0c060c2601060e040207140115081203010608 70
    0x7502c240300841d070f516100007140c0c0407550180c00403011504100000b00c00b41c2c3c1c0d1002a1610500d40326400f102d84a4451007443d2280301b480d102c000c2070b000300e44074558080115809040005415002c3e07900208603002854540d1010f4004c901c940341801e10b0600119075910300c3d041c2d1107103400340f181e890006003230007a200d0707904002d00c200c0b40707002101ca06100f0490700700030700c4000c036405864400d4008501d03940541280034002d050343c0721503035034807010340c05030344581000368825004820380f070340444098194031003005000480000b25000d080c00164180d0140f003031074883e024642c042d0640d407080d4030030421160301901d028010440055811008a0007921034030300d11041e1511b07094204e00380b00f02e49060b0050080d8820038402d105070010086160400c0300e100c555241201c00503580c41c818544030b03402400030900103400358030700480e00b240d800031120700c0010760b0700c1c410885514400b2140b00b80c00e184000d026400004250501060b954112041e83d440f8102c40b1281c0c003620840545051501e007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 278172553 1250 278171303 278171317
    0xf050909101706090303011a0d0501030305040503010608120405090c19030209091303020a02090a09050303010f0503070503060118020d0209030f0606100c05060f042d0b06060a0e0d02040f02 83
    0x8140803008100c0980740b0382d681c07a1008880d50180880d450721240e034580301d0205210340c1740884220710b188408882c45a0454445402c0d17041d003001256141e04004002e901701e8041c2034001d610300715010403140d000040d9061011200d8890b00c0ca0203040400f07000b0492405843c020715128144105010b4005901101180203010341e00161511803c0f010000d950001418001d4404040095000803c1d4040303401c010813038050340e407091280c5501344123a00420181c10003030b000340004000410804906919001103070000c40c00c0b01c6101da200e2041580f18a02840b03148403905c030121512806141d03640290107d06000d000050a101401c0c0c013081c01c02c1c90404420385550400e0080020783c0c9012038000f0002c81841c54600e50490080d40e40c19071310000600010141c2d10068006002c101034030101e0811040300104a20480400141204c0c955082c0300003102d400c4468000500d2a00348041a214082d007036641c1c0d0802014a2428003604089009050342c0113521481900b1400c1780e140020824 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 278173803 1250 278172553 278172571
    0x10903050a0b0a060506040e13150606110c04060b03070c05120f0306010801090e0c040207060603020414040c06080c160302010f1814030f220e25080105100f050909 72
    0x30302e15103c8003407000c41d440b82d081184a0304040c0424013241c1c2e0b8a0403400e5002030220b5280100030b000f8105928142e91080310400c0250514402003140c507031042060900c100307105c0880703012038072034020001940c0c45800303450900081030001035562403241401e0200b2074010030070341d880a980c100c10085541e014251b0300442000000c1070104a50f4002c9000d4010010880c08000003100c47c0d1049843d00d00d02460030f4880d58010440f08c040c00103d610140003190b00420801601d4000ca060340c0c0c01d0350080b501a104400c81e10000914140200d44651199070750303a84480c038114100020100c1000004026021503503034038100168400c2c503200e207092040c60140203003041003a42c50072501d407a15110740b500440e00248010350000f07140d5425100c1046402642c1c9001070841c280c184051061039000d07115004648083c45100547c5100c07103c02080090500c0f0f104142c41d51054038003107030a00c50a80c204445544000f0310912402000c80a5040703443c003135141c40c19103c00608154026500640 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 278175053 1250 278173803 278173823
    0x301050f07020c2b06050603060a0e03030105010c0c090e0105090f030a0f12150b040f0501031503030e1c0f060c0c031e05040f030804060314010b0304080a0c1a071805130b010903050a 80
    0xe04c1c84c3c1000324961000c401d44050064040040bd02926400180304a50612150101d0201080282e0100c070019045e002c03001c100792104500c015029040c2926817071224040e201140a01c010301104880045010780c403000c182c01e0030480304a07000b6002c0201c0410007550b510a80c0d00c284585845c0c04000d00011107410345850801d41c80310303070005280e8041410715103000c0e41070454414006426044a0b00b508152160044081c0810801d804050488000c009030291400800000d07140703540000d4001c007000c005001c3d0018003511301007138428025010034021041c007145c541c0c045d002054001c0a43ca806802c3c1070780e4819910300700909410840c1c0c6190045000d000d07a55051050340038001c0c403200803180361b51406138540524030000d40003404d00000010080485405004410301c05940032500c0e09044c929910b60062240c01564410001400d0101c1e407034007d218000040142e8600820411a000074900e4100042030000c01c1c69042c080b4004000000c04d40612400341d0395401214040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 278176303 1250 278175053 278175061
    0x2030a030f080604060609120203010212040615050402090d020405070e0a0b0c01050a0615050c03120a0203040c0e0108120d1112040308010e1b0c0c15090301050f07020c2b0605 77
    0x5442d416004212501441ca4600100035040c1e210502d601107800c040441c103030011302030002c607001e446101030018100c40d00c5400d2204101081e1310034034005100ca15019800c41d224003c20041c2d228651303400c0d03489552888403801600c1c0991245030017240c2400d1010520703143e400070420030b9200c2c0e4428801681c000c01c42c00c242c0f030000e000711548200c2da9a020410341d42050001c1c211002c01c10800402c1107800704004001d14801c00c21a0307081c0c007142c1c44510403131a141c10118080d510403141100c0010182c40300051000c5480030070b42c141e4820401038001840100c0d12003505402c41d544040d0300c1c0e911005803580c1511080010002c0031500380d8280400e1405080103050400103902001911440d02c0c10000b400c0f1095004841c0100702c9a8a10360701c7c0828015181380641c40021039503c8004101e0b603401007007107140100400c0d40107400901140d61450340140814400b00d40002c050b0b007041c58174031464540514084110701c6030241d102c1c904110713031015060040b5000c0d01180c0c5141d98400344 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 278177553 1250 278176303 278176307
    0xa03110a08100207020112090b01120303020c1617060402010203030a110706020a020c03190203060f070203090411040626060d03020f0607050d050606130e07030f0908090109060c080304030c02060702030a030f 91
    0x72884445420b401401003456a89d29072101e40d00500c22aa800ca950300e00f003104140c400e404440d114071882c81120303e441004841c130740600540b80300d600708903412000420703500d140105090b8401e540580246040d552044410409000101c1400360510030401c40782d0700081c86031018051558940c0e0050106680070303410302d1301c0c24282a544200d905140044c0d5401a5000101c05521607c00c10089600743c0300c418050b80f440c06042c2c0ca0039403187c14100c1204542c1c0b2000094401c9882030368075000c4140000c80092540c02801c01885800b00401c1c001072000d05090300c0d070490091191040b269042c04060342c0300d04040055441400298000403500e50740036150003043d410036800c99815290020f90604410300c680b09100718000202c0c0c1200241c441c50207540000b00d030540c440c3e81400300306050328000c0083d83c844684203010070210705000c1003a9101d98401c074009980031402da80b854640c0c0e01c0507500340703040c03510807030340030000300f01110040c1c90a220600020b0710a0311125044c1d0520100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 278178803 1250 278177553 278177567
    0x30709020703111522050d0e2404090b220e07060504050306040b0709150503040506070305010b070b090c210d0f020705010e0d1a010f090b0a03110a081002070201 71
    0xfa8042e48910300303c2c01100e080480d900d07089100200f880c680d104a444440300341040e000009040c1d07001c1d16521014941d0000300240c1880000ca8244401c2092940c800c0b8080e0b0070040c140c2c01312181031000b80014402d590102c2c0904200074110301000e40c900b80103041c400409918000080d85550200641e00c1c1d003004600090200c5081c10303400c01c1e041102280c0d417041c004201801a059210104501501130000318010f07080a1058000304642041c002e40315501c155003c480512484c0000f4a800b48030f0300c2101c2c16101c3c4400d44610340170681e203980610204c041c000700903901a65510a4056481460b810010840d1400c3c40c95030f0790319501000d00b000c580c581801d082c000c1c0c418407402201e901103802c0e07040e240b003401c00e0f05c7e28590343c801203142031911000060044100440c41c2c10011480130030740e4102c03441104140c0c10251a0380010091340d0340c6000080d004031808034280300182c904c4450003100c20000d800032000d1035540a0142c642846010400e41d61680000c4000540d684589 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 278180053 1250 278178803 278178827
    0x7021f02040f120221030a260601120b120c011107150c140d0309030806010c23070509040602130f080d110c13020301090c110a030807020313030b06270105040203060f030709020703 79
    0x8c03100007000c0c0080e0400302030014041410441d480340c2410500303015901070740e16148050140b4400c518584012a0381d004a2504640461854517070039482c0c042c00500c440903540c488514041404901c2c0c41a50b00104041d01102c0040d0001d00c5c0904002042118240c00c10103690003040c104d02505002e8840701c0050400b60421030f600c1c10f1840850500d004002800c001d15007244140450007900500f4800d80d9084070760b00103d0a010b00c024410550064064100c501b00050350b8a50b49803002e0110b01017034800c00c00740f50045021290440d000703c141c00040190841600c000340303034150002e10700b0494180d0700d00e111a4044014462901c0c41e21441e24914034a081040c28424a010300030382c1d0700c812100040400003401e0000b07540d14402c0c0300791445018900340c8a078400b501d034900420883d0044503114000c1c13a903000244280703a070310144c2034040d0041090311085a403c18081c030029600c01801282c10400ea2000c0000c151000c000c2840206807080005880301030510b0020010b20a02d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 278181303 1250 278180053 278180087
    0xd030c05030708271002030412050403031d0a03080c01090c05010c02010207120f020a0b070611030705030a05040203070f03110a0602120301140a05060307021f02040f120221030a 78
    0x4010014050703040074040d9003004c001c40c0c0c19900500c5500318003004005040083e041c60040c2895010525140e0300698061442064403007400b00c01020100d0782d6000c0c0d0700c400b500040e4441d01c010040c0030013400c5900c2940b400307401c01c9210340d100c1e16421610b50000e4408003c582d940c0b904002442000042c0201400091078406044070075500002c1d0794034090702982c40001c40000390007003008100c00c80968201c0d8054445e4041c203585005126403604050000c2d00c109003803004070050b018401c400c481c41180d00d501c0d00d03411625200d102d00c0060000500c22038240c0715122000c600c0985d11440c0c000254450514130009100d01da0502c1104ca250758407010556120440040d514864241900c9c1543e0f0041c00b85d001252050300082e01508640d0f00054004a0020a000b18150302040300d2101c255421009102c036014140410102d121f584520400f514a52070f041c4010010041c0401c0114001010800c6800700c0001c48000c8026413040d07107041e03500004019104540004480c1d180380c0c105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 278182553 1250 278181303 278181307
    0x110304080a030e240a06080d0903110406030320070e1816030f0b1504020714010510180b031c081906061202030718030302010506040605060f0a050702210d030c05 71
    0x1e459032059202114404006800c907560000300840c0e031700e80c4840b0040c4458000c4030886101800d0103082140c040c013064411401c400c1c07080c8490b040500500c411254107648820b0050070301003030405e501d1000c8601022a00031054000fa00e00c070b108408500030020740400800e003151032144030340b81c03500c101d070500d80301d044a05040011511402c81c10442c0350300207441e02070603070314140c1143c05100618202644280b0100d020b1007448060400b0021894440380208201d44454101091782c0c0c2030751085c030b080307007080440054442e00c503a0821400f060014049801010b095045107441003140d03a11070000807081c40c10842c1d651803000710706444114081d420001107007403500080a0010414071081c00e82e80003c04074810a01c03444c013296100401a20a115494407481c3c024040d001c05d41c2c16030b04c554100440440c2504d01103040750016024889034914002060f94255101e41010300d0980e0300125116081c552000800c00c0401134140748005044420f880f800c01030210340704015020100601 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 278183803 1250 278182553 278182573
    0xa030e120d0605011704260a0c03090e160509151c0b0114180a030209070e0f0102030c07090f093c050a0f080c07080708010c020604020a1701110304080a030e 69
    0x1680513aa030869003212031603032000e00000d00e200d81f0181d48004d42030b40c520000b64041e41682c3c0901f41810841c443d076201c15410703030703100300d038a030301007401d44a01e040103049070045c0505501850040400007130140c203c0f00c03d8001c041d410729031600030002d0b407050075404c1d00543ca003030881c40c4142c5400d00002d00300815046a002d40c05411070082514a009640e000d4443ca1320507039031041e03400000d5600800c1c0802074075044078001e10f14103180070ba01b409200c0c0709440703505940c00401507520b4424034100034120341c0e1034140b400c40030701103c6107000c200b20394600742e038008100c0408020214804603001c540340c408a4981903180444441d035400301107805c1e01d0491000070780200b200030101385c2154422071068518201080e16210706e0703054694512960100040c15500440c945080302c600e0b9000700000912208107a0b1940c408a078020751041c0743d1001840410703100b042015960143c800005551071005c400c2c804241d1003614181da4000001c107102e00010380c140070ba004000070017009003134544c003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 278185053 1250 278183803 278183837
    0x308120106180e130807051005090d1403060a0f23060f0403020f040f020c01060302190b0405010c0602160807060b041b0e0d300305010810020a030e120d060501 70
    0x6800d003d90180302958401240b140c5224141c084811501300342e21a585480a20340742e070b96540702144c9001c2032400c01c0005062034102095400030303442c240d00c4002c0400a408101005903000070111680203003603041c00f0070700000c1509988087c0c2482c0381807800c1d8180003003020311000f0307030281800d114440070000010300c080340b0070039501240d40c19110b051030030b4602800940981003211003a10342510105403560f446005400080c12240282d404c0494000810000300104815000c0c041136581c0400c030400080d4802c4084000d01401584018103000c0b100307021a04410061a00780c441c0c2102103402403d0020354454800c805d44100c80800c100c20720010701c801003417584420300e02403105210b10039840b9100ca1006900e500d40c800c0340124014041c00b40c00402030149004061048155482620064024446d003070607102100010603034010b0309014400a98040c17021902010341342d01c001e0300903c200704030680c140064842c0a07901e036030305414000d045820541c401410081c102000d01c0881c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 278186303 1250 278185053 278185097
    0x616020d0e01121a0a0909020a12030207092a0c030801230301090b0406050c070f0807241d0307020f120114091f0515010305100f0308120106 62
    0x103410341420310300240d0110050701c005050401c0400c0351401c0481205601c0103035615040213507412a443e0071100e072201d8842d801c0b500100002504203000503002d0203500041031103110302c94070038411591484d444209001c180c5600c40c03013203c2c1c2c81417070b0b043c2911180900d40219604402500c0e01940e0043e80b074030010031081c41807040c102c0420719034040440f40040d4840c009540400a0000c0c001d0380c4c2c841c40c00815500c401c9800342c84103460301000c00d00b503001050440c0c1c00503410803d080c204022035202c05038144d01600e000c0724507860181c1311100d400c040105110710f0400713440c4000f81da611601c400b42c002010b05103440303a5a820801c40f403030040c0d6035000840501e804c103031206c841900c0c0c0445228010701310001c81c0f0607000c001800f00314480070000b4207050318010f84802281d40256a01000c000d848083c0c8100d00000003814007103c0700e501c01e0344801c0e44280015403540c401907071121034240d40c240f2500103a429041c009407480402031001031282c0101100d10307056140c40129070807070b41c2407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 278187553 1250 278186303 278186323
    0x201050a0e0a09021308060609040f03080a02090409032007081506030a05030c1b0a06120c03090b011205060f090606010c030c021324140607060e030318061602 70
    0x1201d070055003410303182c86030400480501072a00e0119611032003c10344000039400c43c400c003001344c030441d0300042150400b455010301136607101e10804030045a5580135101c203500248404100f6501b441241200d555074011139810b41c0c00b90b01c440003007070049a51001c00e01040003c040701030740300d00420484200700259250840c940c1d5661041e182d100da40000c0d040000500c405040380c4070100324550940400714049d03141085041d81000803498020600c015196584030f10008155881c0700808a80c081e40c0014040c4100c902e000100c110a40c0d4582c0b101c0c07942a000b00544130304d41004107082120800100350444040c0d940200c0c0c5280500c59640d40d039500606041c104000307000914101070152001c100d006900402c01200c8020902e003030030042c034441d04062410020f018050001000d1203250000380d074203c03080c0f95074229844080c0031042e40214412a43d243c5e4030850b80c6c211600510240d4025880c01d80034983c400301d4800494070341140503012241c0c1440c82c0904c1201903400040000315 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 278188803 1250 278187553 278187557
    0x1f0e07110d0203180607330b151804060603061a04050306060d0f0501112502010c0b130804030b1e070203040e100509070215010906030b0a0203060409170a17040201050a 74
    0x21441d1001c02203000c5016146d4002c0c5400300c1000d0311200b035054040601082d9481036190f040e060144400350040e248203602c4150490201ca04000c00f11042d00018641903503902003c21041d00e840021500300c43c1c20368081c00000b60f550310300b4085a08485d450f8440c150803003000c02d00f01810800000d8031042c002d04264031449018100004006222085400c81c0f50040000c1241003000403a400399940448076607050102d1210f85070349481c1803403170390100702034041c0d44241d9003c0030740d500c20303c04080207001110b030340005460080c001480c0d0320040000e14800d01024183d4200720604070a040ba00241380d00105004404200c0050742c0041607030101d07070b00c6000b00031082e160200c0301410130401d900069000790b050b40401003440d40000c0c10f440350054141c07182005aa9410381c0070110b880c1800028032021082c0d0110b000d880e2a5009181c000130001c100085292803a03661814103968000e5071200210040f40d540c40c45500210400ca80110207411950286855030009050388118204601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 278190053 1250 278188803 278188837
    0xf050103060518041110080105011704050c0f130c0302040513050403140a05042301020f060c0d022113060b0f09060607063c1a01081f0e07110d0203 65
    0x404e005d00300d03910200c0d5290240c4094880504000001e2400d01c0c240519408074104051043c1c074000c059001e24400c83e0450007600c540082001008050011189500d90000c454103031980c1e80da18074820185120515100181e54902c2c000a100846000c1840b070340e0914600010080440d82007803a410b581c180750a5001d54500941c8000e80e01805035030803c09440c198180c80e51a001089491440640400d80858980c0398000c03007815a01c1c1c6084031a02c0700400c0901001c6003041480d0050003c0d050319015180a800c81410321070303018002104c960b0095072248070810140000c1e403240017403444050b00d0b10262040250040740400c003003d0a682d000d000d000036580c06101c1c4c41d0784201081141c2251000c54061000c2e00710410140e80945034039450b401c1c0310304011880d003500ca91380440680c0d06003190300d00c084800640e81030070000c0000480305100c40361000f46051700000e0030042c051761014050070b410308507801410f01419840f0310240781d0011221041c466000010345503100f60303080101d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 278191303 1250 278190053 278190061
    0x30702011202130e0609061e1003060801020c010504030f0807050a0c0203031c0507020c0a0509010314030408030304061e05071d03070b070b01060f05130608130515010f050103060518 80
    0x44000c3c46036603c921214800002d0108807424040d4695000320400c41d10318055442d42d004000d0882c03400d81b2400c0903160401806141c5040080c0c45068640003410006034103941d880195003660f0089001840700c1e550b070001c020805412011510056082d0f00c2e2801c40e61030300c41800341c404c0c03003141c5881c405c0c40b000c40111000c642e0100200e0300c581e101c81c055800400c040e00013410203840203454450150282801304440c034100303103940d4000c5032401032207500711f81d280d44c03034000741000d41f59843c0b00c942c0000c002c0450000c400b0070095025510034940007404150148025925400c002c40061045003000107008040e54440100003504000102e4003080e99111000203103802150752000d078240703e000c104a8203001c0665501412182036454214a1540c0c20b08100c40c9441100401d0a02d6030881400340302c0c880c41071040030b500280300c03103400041d0b142c80c0e11307014609070782d494440101094000042c0080c086040121008180a00b4107006241c09c2a00043d44491842400f42212103808005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 278192553 1250 278191303 278191337
    0x6020a032f030a031406150313050102070c03082802030315030309041a1f20150112060b0111070b030408040b0c0604201c170f0d0b0406060203070201 66
    0x7030369000440e5402c40750307030b2041d001c2c3c080c1c050462120030710405400f84c0005034460030500d0b20f20743d116980305202899070b61480a00d1410b04c800720f0007501c06650a0254070700084c03480342134001850240f03e032143c0b2420b10700990300b80c0885c41c0080701c1842e10010008035001b500001525003010040d84409403050349000403d2841c02010052580a410004807110440f8034500441c82a1800c2e164003500702041d049540c00d0040c40c1018100007554401c0400300c102c50092004940c4580360140c808007031000248000491303003a080b089010a113241450108420f0b4842c3d503800b11400e080080608500a01d542d49400711803040d0704240c0c1e0004001010000c1030001c07a000f9040821007182c56826040c1041d43d01d0038220340c01c403000781d0040c5084012010306450781080c468000c245a8115001d0310b84210301e02c01421044910104403110603c56540d00c1010308074807450052520b49480d5420f000d00140c808e0142c1840c00f4514196052021039404011213420540a007401e1600810310001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 278193803 1250 278192553 278192627
    0x206090301150902040303030605040204050612040c05090705030601030e07060806060d1407051b19020d03031d0321040818010c0609050307030806040212011701140a0b010906020a03 80
    0x29500403100212011580400f56400382050720b02035a0704100703041d1070b0000d001c128421400b42661080c01401500102e03001c450056521507ca41c03500005c095a0f240401d261220070b8401c0f00c0415000f20400581d0750703051055803d00e100300710091010b9441c1900285c9116070180a20b030003241c002561504400d642c0c3c04c4004c0f00b0118060080c6103140940000740190001c00c5482c03117507001084080c2228000040313044a0105c4c2118400c06119290f08210001c03e800d0011014513448541c240c4803540c1c07000f02c0c400a00000006182d0301c040480d00c641d0300c1c0340e020341c542030308c2180320044c400890248000d40b0819121040e074080c90402007030058814200f000b50080446090003502c104101010000d4911280300b03481310f003c00d0703e403035007000160f0045180c42c07c144260345004100c03501041c000c0c0c0004020010000808589503218690300840481d6440d04031612050565000c1d40d10030040c5d401417502e440034025584259400410070088041e4407c0d810512402c600021b00c540b41d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 278195053 1250 278193803 278193821
    0xf091a0a0902030a121418101101180c05030a03120e0f060108030705070b0c0c04090c0515070c050f09070305100e041b0602011503081b1e06070e010801030206090301 73
    0x116132515441e4a440c0c8440803262004000058203c80801401c03004101500c50111804801082e909210b0041c40f00c811030a40c40e902c100403407584001c021003802e100e50001c00c201035a01d50b0440d065070800c1c011024240d44001e01030751000480b0742c00700e5840004210350700a104800724a41802d004900e00d0102948c2900c03289002e1702c00001444400080201a02485101074904081c0d403009175040e03d001e982400c0f100c54120703506110403498154016820300d407040140042164440c0081105420240b204410b02c520006445040c0084603e21000402040b42c200081100a0000c1000c0340e40280919080c0b50b15000401cdd08986e0085d0800b02a20b0b4644c0d1510203441c00d4200070450503120600b031102080c050a000c41c0d40c910600584940d4484c0b04c50000034686169250b542c150701042c2d890001501d1903242c411140d03424001c50040c24602030001c50104554070700e50313040c500040c0c01e42c014442401f40035040f99030010b4030581182c4d012a10103448256030008613026000c051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 278196303 1250 278195053 278195059
    0xd0605091507110613080415021501090207031206050a0e0c1c02091801050a2306040801060806221202010b04060e090c0402071106090105070804080a060f091a0a0902 73
    0x2104012100b82e01120030f1890650f040200c44543d00e4803c249039140c401243d001e441450200014030401c002a083d0086c0e032002441220509030030080c210001100a821202c1c82d260005084821f0607841015108a60010034040003030519100009140307164600c6004003a1708880e0010f00c0e030484a0050724034648110000700b14804207000500025070010726031512404410301d02e50400c502561410381658000360101c1030042c2080b4007424017002580188095010b00607040718551a000c0250006102500000c91041c2c01d100c500e504000c0c00078200c80108149040301c118501b90740c4000c455840c0c00c03405031085141c0b840812805402a480441e4101d030070b1140c0041c140b0201c8604500c5802d0140070f032a8601404000c000607845603078000b0700140400e4052a0f05850040001e051040381410300038584159a0740b040000d8020394801152500034003800410300145000703c8445d02c0d8008020440b4924035901d148a2200c0600382c1160b0719144c0e4001000071106e644025000c0da001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 278197553 1250 278196303 278196343
    0x207080a390e01080a02010c11040b0d08070311030703050702040b0a17070806011d01050f2202090a0f0308030f040c0f092003070c03112812020c0d060509 68
    0x14850401144210b00c11101240845400000c1e520307404640b400714154142d43d0456031404944508101d881101c81c410fa0142e511540c010040c0c0d580c04403107030094030440403107488800a007030151150403901240001904100016000641c0c090102e96005604a030002031102c80302c00810011300c1030f500003075010048805134500c20080002c08800b1030b510348003120f02c035030b0729030140180c8540b1100340b107040061a1001072290340b0f40810202620030380078001110900e0940782110804000d024032500f400e40c0091060680d0400007a00d0001d0070001c00311f40c0c0414916920705005100080c00c0800d00031045001c10100303d41c1500c2500200304540e98034030280e48403a100001000b4a11003442000d10f0600c5a00c4070b00721850590f0301c01c1724540c848900d90b60464609459243c0503039002660b41c015504030303c080520009640008a00c40104010aa0064900a400002521464415036001d22005185036503404070107031155501450118181e10307081d010b1841d0003d0109000c0c484000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 278198803 1250 278197553 278197643
    0x30608031c200d15060905060d0f14180309060a030f09050f010c0305130c170a060c1e080108030306040905100f151409010324051008010c0207080a 65
    0x140c40b000d0210680086001c01002154102c80040070555124020200b1a114003c02041c40d00c1005000503500951000c1902482501000c0840381074840000c6120041c0040c44540403251450300e0951004c2001146001100b04c00280240a118052410181c54031403081202c01e098002c038041a60100c01c94080b405a104110b000e440f4001da0400001d107400c0c001124107564405641800790407080c03012196040041d43d88c3e01c9842030602d0881842441240720000300c081c404c12010145c0380d602c2502d500840c0d820515800d00f880d18031001c001c0d0343d02c010f120b000380100803650000d0b82100e001030601d9103446c0c9a400c00d0f40c1803a412681e145084940c2c0381403d400d421402d219a2144080b043c080c1c4c560020130422152102d455801040400c01800020380c1b58848000310351070b070a4103500052038030140200740d800031034400040d03c64807003041024a209024176022454180050000303682000903a555980c00344201501040c0c8007080c20f498106e075804c0340360300c241104c41000c01c102c41c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 278200053 1250 278198803 278198861
    0x12041b0902041a030c04030201032004030b06010e0301140105040b0d0b09010506010f020a03020c04090314030405010609111602060a030e030d020c0d0309021806040b130b10030608031c 81
    0x42c4203116800300c1c3c3c160030220141d030000c00c80f0b102e203400b0f040c4070b0f003005e080d034004400074116110131480320810840c00003841071070741014100079481100c1c2d0940f549080e4000401714503441d040c543c02681130440e28200d4903890a0618152503058400180041603080064103200d0315043c0070704640300351304c144520040b0642040d84501000e03250105203008944040380c1c0c604c440c040203401600312410740000c07460300341c00610030580a0320708000511004001800b850b401684d0844250703660b2801049036480d58095445405410116181040003103144031586400510000b8070a250024100348081e0082d0712607500003517604e0882e41c4030b521000b01c58000758800c4000700c10610408104c51481442401140d04c0142d01401495011f0320340d8002010304d440103064140d009459049000c15511001c802e16108504050045000e16a905c2131009205402030081c0c1003505252042c000d440c400411114640d4000008030307408140e8154090080092078111320344800b00510600140b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 278201303 1250 278200053 278200057
    0x30216150b010509010503041509020a090903020d1805060904021210080f0703080f03060f03060702010903141812031303030e0306091c050c01020c0106090603140303040812041b0902 80
    0x20000203000c02014104100640e0a40103501c0ca40340014810000a00001c0f04051282c100020620004c5541c05c025400100c2c42c85064000b1440c499540c1108418150304000306200e44a00c0d0500c200482c141140c003204041440c0a41d900540c000105c402c42038490350304407070f40f4000001003c4074a08100c1a50000c0021520450780036204508040038084004228402205d40c03020200c2d20b030000303c507803480d01a04020f01c00c551041803102c230903080f928240b000e42e1190260b98000075141207280f8000e0803c100c00d107a402e40c00b1b04180144c411a24402110981e400422500070310b1240c1d116043e00d10750700c00d000000720b0ba01c030312a00000c02c1540065a005070020b0441c10741e0300742d540b1401e20079138035486c04c0c0340d070410b50700701100104149000e4130050400c024140000740c90140044034150968251b0f030b0003a0086607640008000748011504809940d2010303101035031660400341c40d03180321130260038001502036180c2c1000c2000c011600d8415500e03400b080c96492840c40c0d641c04090025 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 278202553 1250 278201303 278201333
    0x3080c03030412110c09040f02030f16060e0307060813080a0f080601030c140306030106030515010f0e01080c01030b06071a09071a070f140a0807020f0d1e03030216 72
    0x1942c0d4000009240a000c4e0300c0e1080300e40b210704000e0905400741c004201e0035400140064800440c0100190050b80301440b0401002007503d0080101c0901e414092103108000e51000c4100072505141ca4880d0780e02141e1001114100d1900d080300f6240c804120010b0550100000e040d810b002807030129281d007004c04022001441d40301c0e4404d990b2404015810f0f5001004110002050100c10711416409440030356000003010303000042e00c0703840387d03206c0d854203501005525084080c0b40042240080004206000d000c1d40050792a095140c0050360b9641e001d1000300d14181600d42d06a680700362628810b8a400c1600040c828074503034a140701440e5003200a8410b50403d009402d030103d8001c12050755200d00d20f40b064015858101540c40320800c0c040704007400c0b2001000c41c0d901103c908010800d145803640a111802d0340d60111f4410401e0350600e5070232860181241620100200d07490103141220004c40481c0241020420b1600301e0081c03003130103244103154003854910000c0c40072011259442c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 278203803 1250 278202553 278202563
    0x90303030b150901110313060905030d3b090c07020a150c0b220320070b04060302090a03020307270209030a1b03211d01020712050703080c030304 64
    0x81e140184148600303122120002c10309140100015900755100d1910025000c203c502a42e0900d14455000e004450096200c1c0000034a102e0040c4500d14041c401da07080d09a040c01e2000100d410341c02d020402c096030b0b52402151429842202100f0807101c0281c1c02c0300c000003005c0c08103602e0b040c0244442c0b9004a42c05a0080c10746120200d00400f05000550740d001e101d40381e910603810190384101c00302c2001401c40698062040d103ca041c0000403442840e0944291240c0c0c0402006180d4100e2652101c02e6a04550384040010030012250780122000e80b200c4d8a009030741c036441000402c0e804c441551000b90036204106001403081800c1c100e40b200c180c1010071405200021603110420b90141c022400e43c19001111072800142040301b02e40d001000c21041100a07071b079251104030f10120766400a450613404002c03d0b05860340d004c10007840c058010720b8649444031032880001c1d0303205c0081c01690030606960002c00140030040016a005640c070040042e51018110265501c9400c00e40701101c2c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 278205053 1250 278203803 278203811
    0x21f0e090a0e1905071a0c16030308150109060c0206070b010e0601020f06060907081003060515090105010206090d03200705030406030605030a11040f09060203041a0c092409060a09030303 82
    0x10345100000f5880c4207260400010080242070515071140480b00d001d602d82801010031001c2c42c40c00c0107200d540c100f030091481d549182c2e4514213000e030000f40010a000320000d00c62080c84656a00204030f08159005807074030405480c81ea05c00b0400d0b03489200f0300505680d008400010340000d1344181248038010aa0940c2d0151f08440045650385000340d500642c00440000007412480c400c02d000b944c010701e032101c5565055500e0321290100c900c00e0351002c00b04152004020711504002004600610080c4003c00c2c907440e2402c50b9544403d40c0b200050300301601c900c2039002903201040c03040441441c0005030740d40c844036480c0c00d542d80e03400391003801d0110342801c8000500e460041080784440b604400f041340c00c1a5000c2c10040100038128180040710398444034040841c91030b00c003a5101d94410042d0742111001203070715880f412001019400d01e5401008211000e49071380748402414074010031044030307884803040075260f80c2c041c0054494000101044400050798048007600440713010f510100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 278206303 1250 278205053 278205073
    0x6020913090c0602120f1606061a07020108010e060f0d020a0f0b03010503010e010225050a1a040b060a0506160c0b0c03030103060f0c140d0b04020f0c1504021f0e090a0e 74
    0x21803030080d1600317502c006c1420310080f110b28040608030501c451043c4c0e40040c1d425101d01010001d400c0707006840e040b1440c081125011540c210343d13424050210b110101c0d006151500000303082e049000a0f460103250061411011074440c01c010f44082d10581446a0320b680e211141e00810790000d2040620a41c2401d414800010042c4201c985c02c61040c0b0b00006a00024140c440c50529890f02c215a540310b0ac5401d40003042d038403486a501269803400503003543c10302d42009903120b40d0203019103216415a010400503646d401c01100c03400000c18504030b00240160519286000d520780c041e50b000c1d2400604192200c0e004401541038911600040107994032881c1303c042141c49100074080421040a58110b80000d0351000d8092985d20381e0000c07461284c004040b0b02a80c00c04a50310403500302c04544207064a4090095110700b01a80c071010389545001c0c0c000404040202e05106c80707107149140c1030210355105600c400b0400a010302400900c5c14160110001440036850f071030380318043c6034100c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 278207553 1250 278206303 278206333
    0x10e0606040b0d08030903041d010501030c092909090702060916120b270d020c010314041112030705070303090e07080403031a0411040f0b1606020913090c0602 70
    0x402c1203030020309444058500ba40d03c440c040c0c2d04c040c000034040d2005010014964040d00074403540ca1407550708442d4154501070001d0300340d41d070030150b02060104c2181d0511504e070301402c106090310300003d103d0300107400d4141d0209080c4200201503411100d01c0c820085510380005080340a02c60100c102c070354502c0c3d0916895001c8039140036a078150b00740e03002c1c2c0601140c10080902c0d008910300c041040c0c0400100b455841c90a4501d8403070820b9000f0515010440741c041c000e000240b042820180506000da0f0400550140000d10040c007802c03185000000a849581c85800504640c904882c0d440d211030a0441d9a0415484200c0c006803802d440841c000240140603805440c05803107445a5403030701d541c241c010b0184050300c1c03c00c50282d00080000c40e07480b401740c032072034000d1034680544e41d5003090030603400f00c0111f80200c0003038001040350b1085c0104d055051259260000b0005032941141000110200c504c081d9082c103040c20035859005000700504858121b40b03854085075540f92080d080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 278208803 1250 278207553 278207561
    0xf030b091b090a180f03231e0f0a030608060106030b0105120a0e030a1806020a0503120603030f1206010306080d0509011805031203100518060f010c020a08010e060604 73
    0x90303111804504200e900481c20071000d0700342c01c2090f40602042850704c0c90709441e9620030303411099417182d140364100014981c1007005240400248140c0f03489840065111990760300c00c0d000f03648503544c292441442c40c00310810a07038040028403503840d5a5981c0014005000c0c2c10140902c1c0400e014041c000a0303014000d2003000340300041030716240d0a00d60220710a200300c0c18010301051000e51a00d00106901c20144000d001040150312014100119810f1000c0c2401864102c4c2041d0f5000620040110704000240c0300300f8980340340314912680c0d074800840c0c294066407400c00b1103000085482a0100050041e6600c500000ea030b013048540d9440840c141d66100b01010017011440811103d501d5500c0703506012400b1001501e00c0c0010f50380d0302d022030302c2c0c403481e0342d400d420324640031091140c40c0c1705040041004090468026052034464400607256100c050010792040d003d0ba840005503034010400f181c12150020805078a85a5407083c55019204600c1e003e450f038001c0100050880c41d10b480307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 278210053 1250 278208803 278208823
    0x902030f0a0c1b0f020a0312020102121503060414011401061205060a0605030a02090105190206071d0a091d010608030903100e0a0807080f07060b0a060206190b06040308040f030b09 79
    0xf00c0c2540509a103440110030b941142c10398100d1441c0070041701003004c11114450f40c140c4d40d8001070761955010400031041c04090207030016014140e03c695400e0b42e0003e03149800c10f4000a8140900307a1310245940107180c80c0c003468410500380000040c0c100d42002c55010044610b44040c4103a5a461007000b005e00f00d1402554007040062011992004056001d8400880181404c918210055a40003a4901842a0b000040c5e0002082200855010601d8011122040e480043c00c210705170002d00158400d0080c200126078400c80e03000e40d1281018008001c02d0208020401162070b2204240c44c0d0b801011540d010344a003020300c622941c414456001e54071800c401030860344e0300d29525420740c1d03400b006081c1c805520a00c030346600b00c66400003c0c5101c1d40724003000944402e0540c18020821065031100c401e6400c2002006403001009482c4182002260400101d04001000040d072a00403501301526040b00420701192109038039071200203a07406541101065900c0d81c1c941a036543d0110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 278211303 1250 278210053 278210087
    0x110403060606050307020a110d0501060902090f030a03050a030f0912021c020f0304051917060108011d031b1c0801050f03010618050613050c090f0a080d0e04060902030f0a0c 76
    0x1070b50354404581c8ca11042c0008000007810400700341c00e00c2e15458259038041e0482012242d000a00d14450301d0710070b1809e2485e03101030300034040c00801501e000d04280184191803003419281d01d10040040707196400b030080d141d44040780a40c00c0c0103061009684015402201800304a083d850701202e038000244851501600c000543c1307001c0c100f4051103191800201007025008103041e020903030485000c5070703911000c006001804190300d005002030941d1030a6007840d1440e624038480d48942003001c400c07294190401440a0b62400d94403a94510300074600d0b100048081c58404051078a980c0490594100c540031504860310701c0f00c0c1c804060813140707980305074011200203038540784001c00960409035101400034140705030303410345008082c02c0e580200d41101512f0400110140d542c600140d5141c07012105541910880342401c03c200d650303c1141241205004111254051139903c0b9004007010304103c8000703548900b004403114090000581d07141081034240341403d4241c2d445220007450a105c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 278212553 1250 278211303 278211313
    0xb0a0603050c04052403010b13060302030106050706090c0e07020c0114030609070807020f0706051903060e010b3106081305071202030a02040501140a050a0311060307050d11040306060605030702 85
    0x88010041c180f0301d0032000e540e1710408065a001d0038007140000c1e500034004070704215501e50120125000409454200005140c07040c4018044254407009550800c0d92000340080c45c60100d08044020807207130b9019040106c0060f0800c45416808614950180403e0300c0f4044000030200d140c4015000403075529401c281d1a034005800c1902c210b40c1e042d04219180183d03880c3e00c00c8030080d103080021a030030442c041035001441f985600a40d4980c3c2138403800e203140c2000640d050020400c1c0020061150700485134002c078040c0041401403880b08109007201044c14100300b00094400305112003842280d001c01c00443c0028070074000c002d0340140c0503070b000e8050064a418440904802860908240d07094800c259081c001a1954450305019103042c154180d10b0320040c404000d0803d00c0c64004034020a0f126004000140740480e86240142c01140c4050301d0350f903035440031a407902800904070b9205061400450850000f40014006d0740c0c01440107210003501c0312010754081c401966008010380c04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 278213803 1250 278212553 278212559
    0xe0a061b0f03110307061b0302090d060c14030405062a030403180b0d1e0212040204180807060504031e1b03141305040f11030a0b04090212010b0a0603050c04 69
    0x50695240315282c400e061184094080160451a54111140c00c03110030350740310340d0303800c00c1e40b94028080307070448030781c6815441d001040d008030701c01c00c0220364010700e6943c50340115811180030f1041c100c1d054407078250284e03e918040c101580c1e03418060b240744088540f03941d40d900310300c01c14403201400111a4020302d481c40e1141d03a403ca403807070114488081224010300c1c0c045902c9004000411058204400c0400c0f090780030b82203c200d00000403156440a84108120750051038225200b070f0340240c041b140003c0b80b1101d080c14484442c3c6061000300600000140b04c401c00c426a80040d015034000c0c2d440c07200c1c0c035a6a13600418038401a0101d10081113082849483c06c0d2013040320103049920030716199614074072483d0540b01d950404500d100504c10352180500c2103086ca4460729000c8402c0700018029200100704a800501c80904101d0721961101180c4441d0748840d0042c4080e01c0e8003034143d0141d000141030700e500070034902202620800059000203061486030007410b010740d600300489860245 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 278215053 1250 278213803 278213813
    0x207031706010c260409021b01050f10060e06090a0602071e05130e0f1617060705040b0304030c0f080d0b09010b1b070f0308070212010606020304090f0207050d0e0a061b 74
    0x20074410a1101000c10003000c20f801d0407e0002c0c2400c81d480c41105510103906070500b9003992802420a8034503031540c410800c0480148508008031041e0341407071000074401c2804150b051088080303113900850501c600041099000501004481100384007003286840200451400e6496202d6283d00c070451480b1070114a525030f010701e2403015818210740d6404c0c25020f100e0308002c1d545c0000d417600c224074841040744600c41440c07400003800340d80103070401c1c6ca00180c002d40140160300070b00e990070390081300003807c2600842c108502c0780d410501e00c900e104190320740308120354000c0008110342420201c5061503800c105200506850b000b912490405103040a40c0100901d82240c8240f207201c0d070180005c000c00d150f170703c074006140225007103656500107006000841c40c54402ca86426851300c00100146d90703012083e6020f46010780720201d01c9421075804a006802010300c0506030b0b0043d0304c820351507150419411400b0b05030580703e500b40d01d03680c1c076825520021304407491218580380c0450304001030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 278216303 1250 278215053 278215103
    0x609080304150809010f050a06060906020303090604121214011419060f0306030212030a0305180c010c03051c1a0a050603040602090303041203180918020909070503010207031706010c 80
    0x101c1c01800040e42c0210310446d101510300c203a0340940019a40d000522800350700a07101f0b00a4003160004610b9414031038401c03035030f0341c40060000d081c846e002041030f01700c5403082c41401030b440d001078014800d0140c0d00108400e2001c0a200e00744040301c07601240005410200030340c030000030000c00c0f504002c41c6454400c1d41d8001240740719008241c2e80780c0d008401603841d0006821070403060700003562909086d902c080c1c02c9036000361100d40e0710200f1000001c0001000640102d030340d2004e183c074004000042c5010703200390040e40300c42c6030055444443d01070403e207254071030640440c00c0c2e001c10128030203030018004000c3d000d004243e0800e000f0000103000c01c100750014002030310302404807860300d9a141103c0c0d503052203040088000624141d030b00d015041a0071651800341210100030800310624031883c401c0d054551000a01a6075504d00040345520700f0b03c0040b005010280007595101e14910300182441c41c9040100c161200c945c01242c9103504c569042031080f135100c01c81d20055403501041981d40c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 278217553 1250 278216303 278216311
    0x18190803181f080f010e13150f05070e0a090c0f030504020f040908040f0b0901090501120e06090a020406140102030319020d111b0d1209060902031606090803041508 72
    0x4a609561400310403900741c41c2000540c1d070942d4885090341000780c0e200140a0061b40018030480e5020305001045140926030345515074031180c0b0100f811200069140505003503650500c9052800b000c0203040c603000040182e14200807143d08080541719841d950844034880380700c0000449144040181c0350103039114a0f04140000d2254685000c80c0300040c0580742072150444501c10b01040c1004218003004034103000e0403d0694442c01c0c242680002005a042407060604101e05550090324184042c1c3c0b1003c000328207101628614901140a13907518104410103e01940c5081800100740b041804104421070050340558516104c500070b00350020b901005590003540c1c00c000c010b6142040340328854154250500c015201d900507140289807186804ca0b1190325044043d07030001142e07100304c0707c1d91200a003110000700301e2644c2c10000010000c84000940503ca45003440c400304142a40030301c01c984140c0d40c0c800f00e40751074000158990140d8415800b11480b070081c180c0c0010b00880c0d45548c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 278218803 1250 278217553 278217559
    0x516050306011b0206030703020a020d050703351017150c0c0f03030a050114060a0804150905070803130501020f03120403110d0f03111303060911061819080318 70
    0x400c3c2c10399000102c255000381c03020700202e07600103255401c40b5014000140d9118441c20620308050b100d4801070600114040c0c0c41e8660304803d5101280c8410700c080340144182c800349051068504070308102d200001038000e41400d9648241e040c0d00e405400107260b034040103041c0300c9801b283c5a0a480c0000c64002c0410b4841900540711210b030b0845080014512038841004041855450310703424602c0e111001e01418080c0310b081041c20fa203607400410698200d42e2126040d01e0446081100b00010311741c45900800c1401029400102c21400102800001e44a88100e5009540e142d0040e1f23940d078030742850f00c60250424015a0b103122043c0004903400740c06401c0687c3c58000058400b4184541d02c2d00b02030104404d00d545a801c141d2612540c1c484a4008602515200c03d45811040c159400d220041450762508080380c1004000d00040c1c140c5079010b442c80391181c401000c144201400001880c0c065076040702c4007054007103015242c00840783c0502c099032400310349401c240507041c1c0c64108690 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 278220053 1250 278218803 278218847
    0xc0903020316032f090403080609070f02030a0f1407060b131404060905010f05130303150501050904180b0f01030605061e12070302060f0c060a0209210a0b0f0109051605030601 77
    0x80c0036125610f017103104070310958400b0030b00d19000b020401002c0c0090601400c0000358541005c82980000031569050070f82e0030306410742d074000181101d8030510486400da451070301180c1c3da01046419009203006860032078802c0d205660400c4006c0485a0b581c2c80b101006036801c0104020440e95030041403404d00900001c19014110f145074800e4500c240d41094280c500c003000b480605501d40302d003203074083d026580c690344035140000080c414010000d50b1342c031075540d5000102840321500b042d03031910755115044070700c90301d00104c04c0d00d0140000d00c41642c00300e080100040c850720f840740a0b07000035030841c0c8800101d0b001c4103061064a14078804907800c00d00c00c40201001590340e40000d44a45134020308096a118010b00c8104c0c100500901021281401808100f00e150f440d02c102104280803c2c2101c0c483c0014030100c640307030229050000c0e090510400a0107140d840c51001300741a601440000e0009403503843c0582c42a0f0f501d0701e54840000c4042c030114883c1d601c2480c801010f0f03800000140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 278221303 1250 278220053 278220143
    0x303090102121e0301030c0311030a020901051504090c0c03020d1806030b03030702040f020306240f0705070e01091b020604030c0803090a0503180a060503010b03041b090c090302031603 81
    0x186681e0300031b0b001614804410743e010410441040e80c40d2220b084258090703c0d08601c2d0380d020660720f000c1801018805e819291000d1090b00700700301502c009003207d0b0428864242030300c034081c1c04003d41c00e40030340050150784121240c5a015007202401c0007016000410701d5864000100c0c0245001d4080540c140810007031000560307030728040c0c201c100c03500e610700588d02d045c01c4080000c04c441e88405064076400700400c00400c2c1c000b4000342c07075440c002c01022640e150001e103401c1e418800c507a001144006242c100200700b0518560044d0340c060808280240c1c1c14441c40f1059a407180304503801030000b501050210300141d4079101940c2c00960b00f0044a80c04ca1003640c0b03031723811030300051580500340c66810131180442c074207000300e41c0040026003008cd00d5941081c0781401130b840001c10192212194403840d4807500c3da603095120050039203c904000d001c0302c41a0003003c049061100360310070702c6103040c8500c045481080640441368441500c06800f4812201c46240110f41034900135581c84c90740e281 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 278222553 1250 278221303 278221357
    0x714090d050106061e090302040207050f1501230d0f26030604050c030402090c16020604080105090f06070905011b020a0b0a03060614070609051e0c01030506030309010212 75
    0x9901010301c20400419070f90300b410b40040070810100b00d0103811680480114070901c0e0400c6103981a00e40549001d07a59481d9410210300c0d00451310780b8035101d8400e10910b980d2600c92510000d069441140d90820f600c405014000c20b03040d4065206a808a5059040400200350713030a00600c3c68466071304401440000202c840f0000b071440f81022101e4400401c2100a10382403050651180340700c1f01950840c101070f00030901d50a07000307100312440080020342d20800e11060850000340b9034028507150340c4540320090940601001ea6944a10344030b101055400d5103400b0652a219003c82c0c0d8030110b24500d040700449420f0403034144110801300c5e020342500580c4a10680c41c0280021280309540c0e80380030103004040b1421076025100700000d01d10a0740d0440f402c1c1085030001a00420040360b002481d007000c60030070074811000b06084481510f0842c900300e010441c6a5501c40988040025589017018503807688a981c40c0c007030060300000c800030002180358004d8028100d589040203102c613007940301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 278223803 1250 278222553 278222569
    0xf1516050f0a02040605061305090c040503011b030b151603120906060302240405060c0c0424080c0a090513060c020a110d1a06010509030304150e01080906071409 71
    0x20741034560072105003441541401e01a0f0001004283d8002d85031000910000300c1c0c00089010b41c0c0c1c4030702d0381d24011501d180b002d001503c0151500400030024011200312040c0b02e404034800b8440070034100303411006d0324030785a60014000c04002000d0761505484241d2110b0164030090110180700a0107034919103100310f0320424561034031452001482605500401c00b002d45071000000c0c80c0843e030a822580c007084502030b41c0c01c4a0060300c03003548610b94940301d20b007048800d46a50383c0061403c00d2000c050b6155174462000f07003040c100c0e905a015120107480b0340301c958200711250050702c0c2c09010020480e4a901040d840451000404103170b01c2c9a41d280c0b8242c42e0b400c0e4526005034060341107202840708134850b103200b130071085032000300890140d031380c0c201d60411006002194901e00d40000768264090012514072030401000c0d80d9480b41c07202c4488844140d800080ea00041914103500301c0303035028400c6180102c0c0090001d2006580c0c0140c03c44040d6000f40111440080500c4101100c1d103551070703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 278225053 1250 278223803 278223823
    0x308060411160f0302010e030f18040902190312030b1f030603140d021603030e01081009090c0e010506030402010c0605040c2402010e010b0a140d0804060203180f151605 74
    0x7008003c90556410024203554550424034255041003010340040c0608400f107a03000600604c607020160794100005008110702d10010390032940c164410690381c0d504039031507230580307103c2d452008402c16081006c41c2150a581c003d643c101e40611040a24060440c1e9194481d0b09a0f00d00420310742d85968404007444000b030300d1026194403007122000f0b401d0b01840000c054002d81e1040407040303441d540303000f008200105031990500804001150074100c84200140203012403500502801c840c45c90314000100c450b00c50040c03160344200c004a007900d00340080301e000f240c05030f5078503050700d4058540c0402404007900407140c01da107904002800c4442039002c210b203008851034250480302d1141001c0c0c05c0d01c400030990841c0b03034909015010b80340e80b202880c40590b90803c144821a00803c0040380100c2c5010a004d0f100900216000414541c008014500b68800b00c0e40602040400803c0c44124400114560b81c400d10000151a03a281008003a00340001c90120b8800794000b90344405060581c142e07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 278226303 1250 278225053 278225063
    0x30c100c0501060504110d02030901060b030108160506090619030608010c03050603010b0f0102100e03130b0a09060e0306160c0c03060c0e0306040c2601020c01020306040612030806041116 82
    0x109540041c49820300c2102c000b00030548081c003202400080c40c0c59203101d0010700031551507020010580034102540408060510440c10503901d584440469644030502c500c04450000245400300c0c1504000c1c096924112002d810f0904203d5950008103801900ba10b4071401c0554541000400c801e00340031f00784003d1484e0b00e001030035091010916080d034005080a602400300785662200076640060381400300e01c6025000259407848030b01c07081c103500c10890070f891044042c0784042a4910160b000348031050ac2d039141c49500c16603038202642c620840610144c1d054004c24005014102e5400403083c0200091402c0307003030624640d0320b8a20b50002c540080d14070613a28491140c3d055040b200c032400b0340100b00d0040074146040e03910158002030034026a14241d0b142c0c5110704d15044a8550500002c2d4204002d54848003401c1c02c69000703400407a1810710417030134510001000800d04d1100030080b034240d543c0f156599107200c10700010707000401d20207800302410450341503421158030702c80a03024854 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 278227553 1250 278226303 278226317
    0x160f260a05060a09020a140d08031521210405090a140906040b0702120d0e0a02030303280b1c0201050c01151d010e01061b14100c02120403030806030c10 67
    0x14010b1255001c2240c01c960648114400c2407011f5503585040e640e4030580c00803003a903581c0c2d074006204010308141c03104243c008000569111603541c411501040040301202100d14003020040815600840c001c2840c0c000c020803c000c1c821810411540790380f21150310008900140380182e038803034000080307440d50700301c0c1c000c042803100700300e4260a4075400c140c440c80100400740745184002c040d4403681c16901849591600b410b00b1503441404110f040e90780080c1600e407285008100e070302d00c0340d08003141100c8445555010403101c0d0400e203d240540e08000d8203140908003420a00b02102c80d11500583c1804810700c82080410802d0240c0d0842c0b80c1220103101441d40f6040c041402040c2c1c02c12880708141403000144508144030400b14110b40305442c0c180e03503030100da0064500d0100108401340c904884820800c2801600107030200411802100402c080c07080140101c0c5c445083e86800000f8034030410041001c244500c010542180c00282a6142460f040c030009114005044402000ca00c507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 278228803 1250 278227553 278227571
    0x30412050c040c02120409050907050312070302010e06100e0621070e0c070b040215070c03030f08091b01030c030e0a030e0a1403030a050a02030c0f160f260a05060a 72
    0x40c020a00d0f68542070009004100038440c1c041e52a0046000c0c84001d01e80da20005140b0340400c00809000708030180035900f07401c1a0010364049507011840c240d02660811803800c4040b000059028450541c0500e0507c0c0542400040204d2003009403081c1d91044503d4001464844103410244154101c90010080d0521388602c800a40c80c0003416400700d400c00b440500301040240c0d0000f68400d0341211075070407003c6400d5001ca528000c888000d000010380701404010180c1048088601f491070340c0361840303642d540003682962101b01c004907140c502014a00041c1ca940660090a0b04255078200414083e1034400e0542c5001e40c40c1000307600041c0c050024121f5030401030740180241903210314291450707000c82c0110795288100c10012080203000a00307001054424816100c50040f080140c0f0704589404180f10360b01c1e002407007009407240c2403c00019509031000c01d01802c8440d00f200b1560400400070201540620b105480880d42c0141170b05080054400d0081911480c0220000114141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 278230053 1250 278228803 278228809
    0xc0c07050d0503090d0302190602130504020a0225030203061f212607060c2c100306080706110c0d0506061509100c0203210318030412050c 61
    0x6155000d5030181e604601010081800030040310341951041d600b20350401420f10f41246002554060b4808613540c081e2130100f00a4203800410342022295040e0001d50707102e004000403845004203100c0980c1c000f0307a020443e50070714007409181941121042c18600c0c6ea03500800c1c20040c0448049040700d030703030401040d040700007055018040c10a50098030107103c41a07074504000303001d456015114102c0880203081c030440c41600c0c00603450740310143c81c0d180c900d61318000000d000008079400c086104028050110024100031111840c0c407200f415141c030010209010801441004800815480e8600401c030050108640b03401011a41d0741c800703e18007503884003810101007a078894491507240c140e980c049000081c10b285c1000e02102c1d60b80c03500030300c0240d42c001841405040c64021000d411000354083e0048050f0428900031380680d0040103002010540580c281d05020502490500104400c201d4012000c00b40b403480004407032510780c0f249680701e50101000012951a4000c4460380c007541 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 278231303 1250 278230053 278230063
    0x1b020601150503010602120309010906180c0506090604030213110c07080f01110306060d320108030f071401020c1914060105090105040903031b08010f2c090a0b0c0c 72
    0x1010500e00b4034155414140c0003511089002c9289039207007804000f00314907110030b511076142294030a400b04240d0040c4c0d0900151002402015074025410460014003828950111002040020078a600e4507003545e08000c100d15a0303c021040165440701c400841845600050080c0001c100003082018074049074540743c807059103010074981e41026003220b0104c0310407064030f4000404860f150f0719074039844203400c000c1c901042c044a04540c40340100d810140540112099448000d4504803540c0c0c9642c0c4590341c80c4659a5841000541000030700c000c9280d00f400400003c422500140c45c040f410050f00c0d1420141c4008005004203a03c1c54004005850041e01d400e89600c0c40500f10303540c5048005030950905204950203251903030071040400d40301e50700a85941c124180180b55118200e68000d01e406401d00a841d0707600c10380c800c00b240c2404100300d400410f80c0d420440c03a94039540f08800110146001c0e000c408548a0303d0b2520001500d40b4038841d00c61000e041116407102a0802d07524500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 278232553 1250 278231303 278231339
    0x2070209091507030902030a021504051c12080c13061e020105040b07111002030c0405010e18010303140c150426030f1f060521010620011b020601 64
    0xb81e100040d000d0b1000c0c110901141d00800038100040c3e065040c0c00881c2c00c003182c03d0002980880c00d0b262640610f04180003400941d4810b0b41c6500346446805402200b84117a800d0140c0308440060b0176403012071080310302c1c0b64000e03c0c2d195907500746038103065040f0100e02203800c1800401c004400c592000303901000820745850b01c510080c40b80e82010789500184000103840d050400c01684001e0b400d0341c03010441140880c03248001150f0b64900048003c140742c0003130041900150100c08250000d03e410601c0c400000ca13182084682a4a0740c5e4007a82d00a0034004458039500080c4179141e46030200f840b00c1502d0b84031a000c105481d01d030503d0481040c0c030039141540d100c400051300c064628440002070fa6400380303181211a9207520340f40c0d00e8040350310740e10a801401780c1004401080a583c440080d0010f44242e0b4040c0355099061504070380b880c0000d000d410005441004c1c2c0044142c2484c10104076207034240000103140d170012100380701c2025031400580159010790f00400c03145c0783c401200c2c652 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 278233803 1250 278232553 278232571
    0x30315040204120b0a0b130902031006030503040e150603010b28120f02040f060f030c020d080a0b0112060626040203030a0503040c0e010905040302011a130e0102090a0902070209 78
    0xd0a0b042c03075148a03000000035405000c2d80200000243c1c10103050303004905100c0e00400c002c03003035400076001c2005856054001c80c020f015083c1c900e405a4bc10703000d404140e82d0b004015608080c20300c82055a0340038018009c000c42036102c1040f62554488000031800f820002c0300d1b0507034a00142000d04025540407010b00c0c18208030380501740350542d10a031040c4440394050000b10b1850800d07443c0d0800303805160029030800640303500000340a60030140c2c048401c642da4034103001005050034143d031603441040310302e00030031026070004d044840306034481c1c80b1010050505a90342595000c103403084855681010002c18456580e800142d00303a503c4840c160310400031952030b28985503011a4a0b07001e59020700d0306005000c8042020010075040001c054401401c80c03c147e507035580e40c180003500050b00e00340c01552030102c00300a0b2401c100d40200509501402402c810101701c0580f000408641038951030b0342d5800e20196401e0b036602c41c0ca85006003681c200140e11423729004016691002401c0b81003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 278235053 1250 278233803 278233807
    0x2f0d050a060521030d1107080a08010e09010c08010b09120f010507110c060d090c030807030c1202010b01090e07120e0a05120315131413060c02150a0e010b030f0303150402 75
    0xd0a0000101711280e44a0026002c0b852a280c69010702c454043c0e03100040080a010510003402030f401180f0b17034100c07203400c0c02081103034071034403022403ca80201402500003030300e510041c8141c100000081150710405004151604c2e0113640b91824807450000142d01c6035120002d0080d0b4581c02a12a0019101100039080503440318002509503c1031901c0c070120140c41c1c1c01100c051101200d0b6000c000c0d50054110b6030303141c001d850b0042039226005001c0741c03c20a0391301170402c2d00c0d205201c0c00d140484180c40b041e6030a4108609032004030002000c81d000c00c0080180f07078072422400d020b0250012241c2c002880d0a80941c0340090a0050907001c00501e010244208180c2c0612244c01c07030b01010f8141c40302e0581100d92803000003d800800300c0500301c540440140f01040d1030784406400d0040c000d18040040e40e1410b40100d072103403150f20f21808041094404141d058602d540b041c01c0c1091a000000383c0070031106c0200b0f00f042e00c03814403820203401c08030401c4220404a40481315030311084a00714 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 278236303 1250 278235053 278235109
    0x20601080d2001090206031608010f0b03130203010f0c17160909020a092c09060c0a030b0301090c0b250f06020306010c060608030a020c042f0d050a0605 67
    0x4140c4190255084a11400b00069800c0c800e8290b0100410381c0c1c01502840e900d180c01540350541c84190040600026400000040e2301c0503500403d0003a108580c0545103503071240c41c80e55055001c0444203903419540c0d00001150700700e40340314440410800d81c40e030380c042d00140311a030b203480382c0d00415031250b4801d0400000302140d402244c0c6c44c01c0e503908090050700d445880c00101e80c10915504030740070510113801a4100c00c04020f020f03a0f1303444400c0700700d180305583c0e0420217031b01d5190a0701c40d4070301490b0070f22011100c64040d8000746050b08025000088000c402d464036851104150b0001c0c40014001407400078200309018149081e40c0e03804100805208580d4035603000721030315180941500d90200209825078843c560071559540c0200e02803110b143c440c000d81e0303102d41c0007144800142c82120301414440c2090702800807000000c01092001201d0310321800500c0601c5020502e0301c500420441441700310380d1050074001c03030744418000b6030141404188452074800c600038064420003030090b4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 278237410 1107 278236303 278236307
    0x406150f020a05120d0b040e0607110f01020d05040302070603050412081e090f0f07050a03080306060705150403080c070b1906120602090130050601051b0c01020601080d 74
    0x400c0540b00c000100001c440742035503000b11a41200c9c000031b40d020701038500264038000b1401600d9040b2a0b0003607a9089034014260145000d54410910041c1641044660041e041c1424100280c4c00c00c0d032502817002d41980100c008204840380010b2801156015800600d00c444100700054145004200d40703070340c3c142404095901c40d80801c42035201e0009402804c0742c201518041c105400d5803200d0260782e0000f04489d40000d01000700e000020010041806801c0d00400883e0039401d0601e80184601005030460303803611402d01020340402c20381d001c0710b030700080b0440341c40c1c40c042050910b56014007101e504c01c0c0d950700c10b0190041d042c00429001400d100c10245d9a2000c0c040c042c0c03604180b8801c1c0800c40b4981000c00d504100762068940d80f1058000c0c905050090400d107030720302e0008012103543c4440080d6040210303140c083d56010003040c0d004d40050707400b500381c4c0c00c1308001c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 278057553 278237410 := by
  have h0 := BRFrame.cov_init 278057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 278057553 ≤ n) (h2 : n < 278237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
