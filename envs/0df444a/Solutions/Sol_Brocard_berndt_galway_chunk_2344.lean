-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2344
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:25:28.153413+00:00
-- url     : https://prove2.me/submissions/1a52dc9a-468b-4ffb-82b3-33a1050d2697

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 421402877 ≤ n < 421582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 421404127 1250 421402877 421402889
    0x6060406081c090e01080f1204030b0c03040602090306010306020a0905090f0105010c15020a0c060e0d0801090c0c020411030906071e1b1a0f01170303040206160807110306010905190504030306 84
    0x807030395a41d101011f5540e080d200d20240c450144030300c41080041540b00761011286c10003036070600f50f40c400c4004955540003c0c0102c500e56400d001c2950240c9041100354060340c4514001684d404003240c01500c00c00c007a40c0441d104002060800c087d074101c00d8541d40c11110282400801040d1230b1802c01458121207144641c4035201007910382040c0e60040c1c9010b440ea0090340b0802007a080c85100b29115002013241501085880004024030746099000c180070507140c0c9400f942e6408a64001019211407000182007903001200f0f1002184040c02269003001960a100c0c210b404503610004814032401040401d0020f01d51044800007561501100c61940c41f103040098014149c04490f494042902e11469440c091400402e0811008400300b41a0150301d004504550791a0700704041507010ba10040a0400c07811200c02c00a440c000281c5100f500c0707075200510240c00030040c9803401c0c40583c0070301451800c203401d02c5200541075602c1c0312200f0001e130000c03078bc1d952142070a07006858290301035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 421405377 1250 421404127 421404149
    0x20c09010f140d08070516090c080c07020d11030d09030b01060302070506040b1b0d05090c0a1208030c040b03100602010e010b100c17030702160902070804150c02040504060b0306060406081c09 84
    0x10070001040a140c080580c0c0d164523040084400240d4100e0b008131003181d0031088514100544c0000d40b0301145003510013440390a10141014003100840d0510b50001040408503401880a2003044600f00c4890302400451600310b043c0b6646450702035860074060300140c03105d014071005c12252100c0142010390000c40d12203281e03440000350801c0300200310496000d8054010f03031120785004d2a2844510003118503a508020310101e5940b940c9109a202500c0072550b0312003040001000c0d04d8000c0510310510703841c0441c400541c9000310103030a4802c0070416401c640d14003440c141481e56000100329642c50f241c40c290404c042c3c1032501680d0344280901303000401402004000e54264005810321450045001d105881681e40b407002e0207902450400502055060209005d403e8030240e0b042003585807444c000740003064030f80105084030700944080e5480358030750704003071081e0a042101c603410480540c2d082010301d1400c10b4507a1a40c1000e8562030741c84410785c0703580300340d1481108000064003c1d2401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 421406627 1250 421405377 421405393
    0x708030115020f0109020102101515020c13020702130908070f140d05030108150601021204080c0907180b03060402120f040c050915101e020c09010f140d080705 70
    0x580d8540c0c003590a0501c0140700e5000c0000c2c4030303c030600400c00a190b06030010440780c00c1d091280d0001c0c200b0408002000000080c001451129036003c1003541c3d40d00350050b1811271440014812085071003400c2b00d400d1801049160016101c0c0000154562a000c0b400200c40810b450504001d214044010703140f6000c8120040512001c40a0502e4a91304281214071506000402340c0f00c0f80403d2055100e580c11420345051000b404102160b444081413069038120903840d001d401454001c1d0700a801c1c0c60f800b000c014800e030308140010301e0700301000c0d0800840c1c400e445400600d010009024a0101d1800840070a44640351a01691560440660112100e103469020714095000c111070a4426184040380020710b03040c500c505038050716450302d000321003110490900c01a002c403c10580101b01814400001200701042c2c05503154916030b02400995521508009031840188c00c201e10388130505200301700e80c42501080300000c8805613200c050210b094205244c1e00d00803000050314034050703805 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 421407877 1250 421406627 421406639
    0xc2812020f030418140f0a151d060f09250503060d11010212070f050709050c040905190e0c01030c02070617060d06060305030307020f15130203210403020109050301140c0f07080301 79
    0x700c040c7c403480702c002c403c2100840301c07a861b50008203207104009161107a8000d4608000c0c1c003650b0958000c2d00a00350030b0071660710401040002900300c0d024007035a45040c4080160078104814058644058904903045007860700000b20484440c103030060980c6040140c0c0c4c1c82c264002c2c0300840072003540d180c4072515068181001c500203400007004958030702401d0400f060101003440381601510861043ca8282420540c0450045c50094510703c20040c00c4411702900011034059400da6000c07020103045ca401c00400090151900541c2d90707415500719203001d0091640c42111291202d0341c00085480c01d84503038011865807404c10001618190415001209011000008500448003a400c81da205241c0c6035100361a4405407840740c2000840d4004100d1006181c4440c40710a8001000d480100003c3c4001ea4502c02c0d14012400051030f0101c1c1c00c00941d0380206081000b04429002840b000c00c11032002143c814004021009070b8a02040000400061106460000354024251545e9584401c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 421409127 1250 421407877 421407901
    0x90c051002210a1e1e03092906012d0c080f0301150915080405010b0907031d03030c04050105031305010507020a06050603030910050c2812020f03041814 67
    0xc508000c130b00002803481d0383d640c506220301140c1410365110802d109842100c801d14161410030001095103654900d00441c8030000c01c060240c3d410500f82660b4185440141c5144500900160510100c6e0840b00404429507848143d10b20f062048844150703c125819140c8254105028006440104402d42c0712480d00780150b06a5140c10841e900900600f101198041490701a1822003001c00c1c600090003802186410b0b00b00b0700c80c0d000800c0ca2010403001c1005210f04580c071500183d100c40a40d550010207840c40140e04c07140c600558030754075007101c0954252050380304440c1040350000001c0c94030321150940c000310a03400301c000c0c005800c03c10002940c0fa02c881006035031540c03800c40800c036203182c008100c406900d03001d01400401d003411001550541c0265601c0702c0f140c014400840743c01c0c01d005030f8040e02030020914481c2407000a040a1403881c004554070004e651100c014140507030000015502141c540682c0d01e008038071200e103500081c05075804411b05c0c80c40c0702d200f4002c04000407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 421410377 1250 421409127 421409137
    0x130209031501150908030726070602070c0501110f07030b100f031103010518060a05040809030703051e030921070f150f030b01090b181c0302010609090c05100221 71
    0x4c0d51500c401603211044d5548921a01000415020510508034103490350745039640440c0c0341c00705416042510396146c42040c1c2e400000b00f00d604002e9404207100304d40e04012041032480c1c0020080c0304180d007411350280d8403513003030001600400916002070b0303088010142c10f60141070000d903038500603079891405403114541403a5052007075090000050909090707040c1d88a08580100043c15a6124001030394014540580b082da601c42e000c11101e101d54030100550801548600000d100802c05003441c0d6405c2084844070501d25081004595081c0d078800300102d02020010b041c0024455608208902d0700388103a0058150f203d89036400140500e8400317901c10501d1040d102e141d100441000f0450031500303125005801300d0000c0c40213204c08040c0f6030251180345031400510403c009108000740f08001a0780c1d2282e01440460006d6081550a009000042a16040038052000c03541e070b512078100304d03034041c06015000d0300014084951003007002d0001d4183e00060741140003c80c060042c06a408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 421411627 1250 421410377 421410419
    0x30f0c0d02010e0309010f1b08131a04050604272c0f070909140f01051b04060f12020904060e100b0c06010311030703060c0e1203030402130209031501 66
    0x1074440b080f40190300200880ba0b004005955034076101074400d0007502c0b44a201501031044135400b040d8000011001030090280c040e488081603500c03841c000b00c05024441d030401ca01c102850a2008120303a803258400d070360540e41c41c22184d40c001d0007012400e0030701d9030410644c0b0000d141010b450b850310507400080c80c00c200d100007514107144041034070041e0340d0352060360084426a12054040250516550192045500c10941414181c0c40e840704a40307408400050660107075510024040143c40c2a4081d507007040710300c50342030f0415240420181c0308800c8032440b0b90510a0316848042c0303c0c002503045410004000713104001c210f03200e4136a012a0030085400110b81030025070301080481120083d00d101410400c011309e200d80c2540c2e142c0d500328034100c0c2c11a07014440c0d00004800580b581c0941c642c020300342c2d40c8940800402d00208111184a030b0802101034000304280009030716224105603c40c9400500543c1e504c08840100b8030789004880f48841c45c0382e800001140a4032000081c2001c0700c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 421412877 1250 421411627 421411631
    0x70204230a0213140f1002030906031801051605030c0307052203060c0203120105060f071203020304060605094308090c0109081c0207090f1508060c0403060905030f0c0d0201 76
    0x1c2c9a207520b0004107040130030706038099200f1481001301d28041c1034900c1110b40b60701c19a13040000c0e500103c0c040e60002d032403c4c48410802522400d811702c00b40324041d800202c20508101400300080d010341940710207003a0903410040080052041c40c040c02c1100c03001000d04010440c1c030b070720032104010072440901003142c80504120218490034800800e0380e143c4050f130010030306164a00410030109500210010820300001d002c280007040040c02c500d00c1d10201924050380d00c1c80c19145c61412645980c003c184108ca400b418000346911407606c01c284c0d228006d9280040c004207040c03048224541220406c0d11108444405800662022005000d60300d5070b0100c45007070010000659040e803036401520090313444445a405208001d40c10340d820f44404d4015115029198410a000d0766480400c0c14245c03616003246003a5007a0040385040240507000140c0300318107108540d0101e5108921010b8955900c0c0c000d91010b0050a001322001f650201e504155030305590100e0075120b240c03c040000240d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 421414127 1250 421412877 421412879
    0x60601210507092102180c090616060e06041101020106031203021c06060f0e0405070e100504050a0611100e0c061809072703020102030313031e020303101703070204230a0213 76
    0xda503001b8407070044031700c0325445007004166028840c20390002e12041d0410981402e4038404680c1602c40c126813506000003508444c900341c10034070240321000c10201e04581c5401410000b0401070f080c4440e090000f441c015075207804c46c031202e0a5260440041c024000d00d0b01c440060703015000411101c52000d070b51540081800c0b944100012148100c0d19038001c1644004040010300e000040b0b4012141c4a0070311500b460385540201c2e01013445034014030085101e0900032070075074008108590f60030740784450030b0003600c045110b00d540350b41e00e18480501854010643d1103489100228a010b42c40001c3c00180c01d52401707150080ca0b80c1400c56407500351881c10002282c2c007550742003502090b2901a002145151074104114400c01c3d100001541004803551180b440c25041c1849071103400d14a40c0195240c0c10b05210705c4002e00340690201c21fa82e81102c0c42c500d088070006c401c1c0c0307041e150100c0717000400c03504403d004402c40343d5181401d072410b4413003410001d1107042da0b8080c01c1584000710b0b40d41c29031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 421415377 1250 421414127 421414159
    0x1030b0405101d01060618090903140408060a0e0309030a021c0510050114030703120c060f090b0603060603070f090c14030408120a02030112060b030304090c05030603060601210507092102 82
    0x5003250010f03107442061f5a990510034074007030707410805503684a03182a41b484c00030001c1c620002d401a070800e0300f41c0d81010b0140a500d807124003980c04105a440c0243d40740209040c0025500c0d80c111070001d0241e180c01242c28400d180c0030301400c3d59650480140c80300054068246001000b09003e24031020884c281380c40b015040c0003445009881e44103010302c610500d0b2220030385d0f0742e21070810211040c03038850080a062003c207000788405036200c3e0f40c00c0c0410b414100c0400d0b04008004000b42d0103540180703402c020016101c020481240c5269100080000c0001c204444d2000d158140440040d0000184410403c4030b0009003080030800d460880c1a40700c0760100010b80c8000c2c490f0b80303003050a04100c4c1000c50b04c0ca81c0f004403810b070700801700c0c0e1800c0d6444006405881c1f00c045000d000c22004801c0140e0340c1414400703258402c4003407901c00f8a01c03464501d010180300b1810442c00354a95a81c0000d0161401542c18030003500c4440a032074490010004a03100c0407012001c101e0090050854244074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 421416627 1250 421415377 421415387
    0x801080a020f01481a061f0f0e100e01050d06030209070203030a0c0201110a030e07052205060d0f2303120702010b01020d0e0d0203030912071a0f0301030b0405101d010606 75
    0x119404190880058000c3c40f03000c401107405080507900c4500220034800050521b20440c0c2165800e07112240240e04c0c40c40c0c0513200d01c3c0c602d02c09500030b86403135140607403980d4442c0450bd040c4000342003e540381c0c03280c2100c900003421550402504500da40060155090b00007010318400d4105000038800c0f1000c01e0012802c0e200300c1d142d2254a15424050b001c0401c1c004e81150402000880440308681c0d5500b0000f032440c0d4414002403042d03100b0303040e4081c00c08a01e01070fa0360b000350299500c0888551654600f5402c40305140c018040301d002e840341c074040c900c40e80d4208540100041c2101d4a502d0700c40041503100000717407950b601540c40e00c0000c891039400800d1810010680c1e480d0711012a00c2e040a004290940c0d07002240d05000c1008030044681d100c10000041900c0c4030002c2004900300003030344c80162103040308a40e9004050081ca580807150704112410b617640301407040f08a89031498504d01c2c0c0b43c8034603500a06107080000310701c800c4042450614424001a009100c410b580e000f040d59 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 421417877 1250 421416627 421416767
    0xc09070c0c1203120501060806010f0201020f0a08040206070b090102090109060e03070303050f120a0c180e04110f03060f060406120302101a03030706020a0f0801080a020f01 76
    0x6030841c1d11400c0080340000c82041144070300a040669503845045414030481d5002d03000140843d0042080c0081560720107581140b46ca110f000841c030303007056182280018000d8980740410400c031600090215214801544c54655010b00251640d04007203002c14040e401c01c18969000030009240051a58440c081c05142444013902421030a07085480880fa5540094481403444ad0204603240b40113649404451050303004500008914003107000050408401508018001144107800d101c42d15424180c5500268080e0b0400742c0d40017100085084e480279440495454010001004000c0c10300e800c48074440c15040303504009103619501c1e070a29080d924180900180e00658409040b18200d50002c21740080d00359114011000ca000004e1455001983c00c0b109103030040342881800342c00881e481d032440c2c03841c00e00d8889581401c1c002584c800d0100c0003c0c0c483d800c8035a01440b00c0c0d00400900e129650120700303402e0014407000d0202003544010304080c001300c0d00010240d0b03040b1035107000d0718 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 421419127 1250 421417877 421417883
    0x10201061a04053d030216050319080f221509171603111504080c060604020313032f0a0b130b070c0312050703050124050f070f140c09070c 61
    0x4e240b04c0846100c3c0440b5a10312201400d141e400c201c0c045040441c050320a0b2410b00c94801591f4501c018100c100c0c845105524280c01d10403a4014040c5d03604002c04503d0f071020450011a1070102200b401c0e03a4030b008203100161400816040e1703128141d0054100100b90707802200e83c91111040c0e24ae0603c0140b180781e034403040e008041c181c09800a441110340c001d010800d8011a415140007641c0c0071216003094800320b400c900e001030341466299043c0001350707000307078111011030452800400360751100d103004500504004460038a440400a54258800100003000c00b50703a10100f051140b50756482c0130a13066401d203041400045180c004285040501ca900c6024600c0588031800103503441400d81008a0602c01580f01c1071903207022601c41c0710300c81d0802d55001700b803951400000b000c404200a45100328101205000c6400c11380041c2220b00b141600343d1070980ea6040e0341480251100d1902c0f0042110380c04450080705240d0000302da08800f80100c4160805031562032040e284554041c40c02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 421420377 1250 421419127 421419199
    0xe0607020606220e030c0d08073e0f0c060405150c100908030f06120a0803090a02040207051606090e070509010c050312010305071a03060f010201061a0405 68
    0x1000b508201071100c40d1440716180c2c08603414030184012055034001c500380380855202040c3c1e2054000100014545026075090502c0306007802d03030000b04003980003484001ca83c1e54001e543d0804091000c1030300030061101c81003840420030041490340710403030341d00600c000d8400c0329107084a03840e01c44201d40882c5c41c0104800b0700242e2180d01089240c200b049082c0c0c1301c2c054000f504486080c070f07010346020303076120b02c0001d582c0349461050900da10401424560194011031000c3c464a1000210708400035041a110fa8680d56454805807400e5800c940c000c0d001800418060204040010b5141c1e04500b018603100401d44c80c0c03c01250a8a6548919020380c4111380206016a005e54002c1078400018035200e1910030840e112245183c2c482c24404600100d030070010000d05c60300388614406841000b81c20445e408005c06190810701003d00f40600ca01103511022099030b000f50301100080c0f4050513000160801d0011130036803038000d03200c1c0c0d9010308400320204c4c3d1003c602c0070b0201c6650002e5202 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 421421627 1250 421420377 421420381
    0x21303060c09030c06091e0e06210a0c140405060d061802060313060e030906390d0e0a050a0308070c05120c180103020d03050f120a060602010e06070206 67
    0x1018054010a81c07490144010381e000400440c801c40400c50203001c241e00e40861b5140f4021003104c1c00d021680656840401c60700b0240300b0300d01e40b50300b580e4001e41d04850f40e01c66000c002c0b400580d54410843d10000900c1440c1040c0200032001c8020701c110343d04410509203560f2894188402e80701c04890b401e500010b014030710b0703000820550107402c2c11160011095081c10b0035601150080d0310507035401101c512500400c404201442c01100d0386038200d840514140a4150086078040c0114820000340010103441d4680c0c141403d4901007098040d8a4290710340c0150305501500c82c0d1703486007118005415440449060704041a00317204a071400742c080030400e842e50303d07040c8164103c2c8804450074014a10300185950300c41401ca00d4050f4080c01401040000a041002ea1600b44005c040040002c40040003d40d440420085404c2d406041c0245e84004003000d4079401c0c410513039142c0ca24500401400300108040d4090310a550003500204001d84801800da641c807007046400c84016804100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 421422877 1250 421421627 421421633
    0xc0e0901060e0d0303020418021902011416020c13060e09071203121d010501050112090507050d03051204030804170712120f090809010e0a061209030c020d0b0403080109021303 77
    0x109003c201c90080c0780060400f42c5490b40050503c46110001c540c0365004a0200702e4140344801ca6842940540000c0040c56416138840300c0b152001840200704189040b031515055009210b48424040c0c020070356900e103c03422208a0040c9414010300b44461040d000244031904d0000780e010555035910000ca0300450381e580c089406d1004030401c5942d0700c0d00c0d10021408601004c0030009000070680000c2243d41c189000108245650281c1450305824400c03100c01140c8007103020317403d4400985000c40c1c170384040d0070192032510440b42d5500f182c0000c5420041819404a10180194401ca00d07800242c0b0f00e240c0e036440c0c0780c0220b81c00a0030850041c070124807424001d0f0400c0799600d500b0740000c01c5111118030140129680c0d24000c0d074801c000016181010740cac1c400c444c01f44d8240200c4840312484e003071040090500c1d030706611036642c3e140e0300d14010003031500400780190301b1580102a071196690301c2c034182c0f43e4548141c508a0100c1c41031400826549214029103000100c10060944e2241c9152 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 421424127 1250 421422877 421422889
    0xf070b01150c02041802030d090e09010c0e10031103011d07082511010204030303020c0106060311041e170a020405060603060d020d0804080f0d09090209060414040b0a090c0e0901060e 80
    0x203240e8000314201420202c01030f11f040c491110494080c0d00c072a465940391030b1281d208544020b0440c5040c0e45002c445414480e004000d00c0d44000e4251000f010210742c200c01030f030003031040754281e2041e03d00c040000581410703100100e45100d941c003500440580c80f02542030f40c0005060b45d030301c80304071a20170174085107480105200f45840803a280034183c0a00d284d0f031540c04c90740150004d800007a0002203040d84454240103000090886141c200034203200100310100c140a02d0142c001c2d40c11801844842058a40c0e5400c1c020701008000040c185031140382480d0703140382c940300890049080c600090150303d05a401d507881090040c2a0124402459003001001d0440b40c2044560328000d00c00420314400811685240540c144000d20312800c814a025101c04e0075036114a071040d0040209042c26202c94043d41c1c11600348400000c002e0403a000001c003d40341e02004c59411200500c8005240d500342e400000e508161a202e0780b0000000e2414030401000074025240410211035118099040c61 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 421425377 1250 421424127 421424141
    0x40209040b04020a09030c0f0e0f0a02070206040b0304110405011503020c0a0507080c010809030705030901050f0d1406011d06341a181b0103060305030f070b01150c0204 74
    0xd100080008400300060100e07000b0580ca180002c01e040c10500c10400201041405450b40482454515141c9841c580300004010940c100440450021501c80c1c0c00315010f0341e121581c02440e0303d84881d00c071814000207800c22503059070a03000b0061400083c0c00d0602c9040d059400310500070200040c01e0340190065848030115000d90703c600d4100002050041c040311025060380c00103420310042142c00144105c001408001d000d030820029040040d1001048440c040b0080c20050b40302c4d00150200a603d01560300198915400c04182d62444e0100f5081c06118001c240c86026040d000d0702c013010100301d04405055002a01004120300603400c00b0b481070302140302882440c21020a40f042510094440308084950385001d10301a00343c15030000019030711400c08202e2006a0317200c82c10070b0755101c000d401c800c011040090301441459203e41c006070060354103c0c1c11244d656840d0300080055a0103030303a090301e90184a00012928800200fa480c90802039aa10420000150380821008003c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 421426627 1250 421425377 421425379
    0x12030506010c0602130b040803030406060b1201091109060a020105090709140417040f03030c02210a030c1415061c03050f0903030d090b040b01050906220e01091415070e040209 77
    0xf52170000203035100f00300010000341901c61b000e15140c1c1850701d056802c0c0c440f00d80002c00040c409002d030f19001c0c42559002411920a0710000c41c1c00030501504810300d11488803655009800001e4085401c0c0d01500202e01541c140030866074040d503a41d01b000111016101075401042d0303082c020a022481030b0102d8410382c009c00c00c0c2a442d0940c0c51020350400d00781d90b842100401d402c41c50000641c6061110096440d2401e80062007240c0c0780301e6040e49604004100800b400302004443c030a005540c60a100507405a50407600c0c1d28180301343c080b4802c1c074201c80d410701c0b030f02c80344901444580d1480d40c184459075050700d81d94100071280d004505c90390041c10500b501880280100369200c00ba0f03028a1282c00e004a03461445070420b41000544450140c00842c020320418040c4651501d07480050302c2484c040000e060749019000500c81c000d0400544030000940c00d001c0d000f030902c40321143e071698002c14071044483c29042c581c508a6000e104036042c0c0041134100c44076072901c2c02d00340c00800501c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 421427877 1250 421426627 421426657
    0x22140304051012180b0103120c0b071815020304050d0f050d030506040f0b150d061208030711010c050415020a050d1e0903021e0a0803040e0412030506010c0602 70
    0x500da03004100c101100403400e100048069003140300f40c0005220300e201c0c00c104642d0000200700c2d40e84a21818450612005006903802e540305440684038514a241e070507400940d8110b5401c014200400d49031808807103070142010b000001480403d100c603030b03501c01032689e002385007040d00d04800c10102c0303030304000c041e95080042d020700c000044003405003090007120b5440025490609505000459114140001102e8609059100d00b550786060340425a0716901c0c0941d03480c0c035102448405044a40e124a4142e1103401e020020031500c040035522402c072640d910144464a064418283d541c4001d03444042a0100001d020200c0f030f101903100182114011200300a1003580d9051130410071003441c2001800240d4032100381c50110309007405e084000c0c030f08440c050f4219000202d000103058180c2c90003100d060415856600d8803500c1000030f000034070640341c075640e4441404508013030440302140c039002510708410240d030080c130566001d01010303075655203900c07907984e60403000754026000844052 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 421429127 1250 421427877 421427879
    0x10030b1b040f0e01150206040204020f07050f0105390325020706020f01140c03041a0103080a08100806070c05120c0a141f05100b030703050f22140304 66
    0x1120400104010114482200002443d0200200000b401a000321000407a0b0004c00c0810035400180d0701e400640440e80140c0d41c0080f0100e040303440c420b0200090240c001d002c20740d01030f00c0065000600c641d2420300d91002d00a4003030184c0c0b5054141d0111000c0c410805c9a07454905064040a9035011080b0081001c070760301c1045001e48990780d5003d1402c01680021030a1041960600ca40c0c550240d0610080c04404644102d5080440b4010189594000003000060922803840351000c4499068000104296128203003107071964803280d21100400c0710b07a0089a81c04e600c407250041140c2903c000703400c407600c4001c0d044a80024509068846109080300910f40d400c0d0b9400610300b290511000f00354110552505217075410804d2500e0480f6004041c003000a41f0603004150400003544c10000746965500020b5680300c12260000e10400f5008020001c110313070554050b6000311400b6991804a59500d00300c40704240d4030384480c6180741e1500641c2c000240854802c0010708200c034050f03031300305 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 421430377 1250 421429127 421429171
    0x41503020703200c01170c09150702040606081b03040807152717040e13031e0c110a1505070c0815010e07020a0c0e0a0209090a060f05040510030b 64
    0x100a01050100e0b682c00015296440e07607040403e40c80c4041200e038138074000e49049a0b4145040c008c41c3e014902030f07818001d80007115041d550454400c41d6005004128054680c60000c2c43c10004454405404a14110f0794a4900c0c514090724030460307000422130300e44071941da200343c460701b0b0315541c1c116107948503a40303284e211820080300c032604004404543d4405041d402c0c800c85044c5107400c00c00003a40204028010102da0f0a00fa41d440020303000862040c0001c1d14040358800000d404400e01e20380b1140002008640c4410311602d8140103003800d501d108115070400c0222800f6100342c1e11110340308c02c2c40140b5540124060701e28203020320000d20b8102d6032004a0380c200a6a0300c650000c1180400052205680007411079411502c1c603c0249007420b41d90f230701e07141c40d85070b40c0c050500c07960000000902803034804c0c0c0440c2c101060141c10700000c1d081ca03d4140020305182c1c014440503558008000c100303401c161241c10720588002c1202003041d03140d030310703075101101c400b4000c01a0320003080410403d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 421431627 1250 421430377 421430417
    0x70315020d090b06130e15040c170a17030f18070806011d010609030308041b0909060b0a091401050d020a05031b031b09070305100518040606050402041503020703 71
    0x2c60302500c810255842c2007000c0003103901c806111380c01902d01e0404010350341c40e07000a4621000d050030300c10711030585036030500e10780701040e0b988100703072020503170f120490801c03004500204601d1054414510b9000358480c007200300d010480d01540c1c9001d840002a880d11801402181052004400e80c0c2d03080c1e0b2140d220504100e0243c00c81382c1a5a10090054041c0704581c442c24014030030f518000782c1050031035400502050002d0805418203011904505131a9802d0844070020035510500b003000f64580e15284024059a058552042d01000380000c0c013404d1a0060301c010341282e80c680341150b800d00c801c00454000ea1501640c00c03080000000c10103132000c1140c040e07052808020020030741d484c042058940408600052a03e034407910f1960704d0398554005c40c2d90044c107581000b00f020740d81c0c4501d800c103a00550b40716650226260085c21501e1449244080c0a2802180140500d5444e001840141e2003148181d5100b00c44820310460001e02c240e0103066054800d15014003a04010030f40041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 421432877 1250 421431627 421431641
    0x90513020301140307050a060e06120f06100914120a0f0b0108010f1b11010905030a03020705060604051509150406140112151403070909080a021e070315020d 69
    0x14940c0d001005205141107220340760100300c8101e00030000705040001040b80e140c054030501c1d092080700d60482401e81e54000030344400041d0224507251300d140031348030150030a1098551501404a1174900d0725028031608620090711000f403a40d02e0340040910038000c0100c044400703844035006100c41413001841c0e05001c0c01b20700d40140303205521541402489400c6400b030513540e09859180c84a030100d940d032922100200300d846424441174600c80425500c4c054a4074002c000c4c841d0000040c18441141c040d405014094020b004035a03941c0c0d00d8000744130132581c0070355240303035179000420070a1440d10b0188034a9501c0201410313680305424040c80810155540354000d902c440d000414802481d585c00680c050030b03841c3c3c00e2003d001c54000319104560143c8a400303417413540d100c0d007082007409860401103c3e0007040d0b9800f0810000510b03080200072904a00e85410050040000004003100407040440b81428040d01410f00217181d540c900c0184030860201802981c1c09001d022209082845418 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 421434127 1250 421432877 421432909
    0x90204120c0803040e071b0c09020a0e300304080123070804030804060e070b0d0c02070623090d12030605040c03181202010e03032503050c0a0c030905 66
    0x905404507031510251200c0181c1040029520600c03040215148400d81a50012600e00741490040b015807200100d11864502c007030124145800b0019240e04964014080344229a80300143e4205035000c01030901041c180814421034240c01741d01e84030790905041c140c0745030f42100f20380c0b4042d560b82c00c01c1e0a458841c1440800c5908140a11850460708400e00c1e5118916103001c181c1e80c81c181c0c0e00079109500281001c2c05869035041c45c1c600802d020040c08010b01260032085450b05201103101c3c01904a01d41540010301400030005002406004001038640320301e942a640c010300481c81c00f4007a0003000f80568011000018000826104805410744121581e0046145400d1500b40002c0d42c6030380146100701850450400049280c840c640020340f03078010401c000f118403411080f4007402000740521118000081130080307500c4d6041c4030740511001c005940700d641410840a8040740d100700c3e948520b60700108012041103124880585d20648281040032038142c0f290040380035004614160 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 421435377 1250 421434127 421434149
    0xb15070302071401120b0102010f022701020a080d0207170c031305190603180c0e100e1006180b040b0c1603021c03050d0f0b040c030e06061504090204 66
    0x440034503a040c000d9001030180380f8000d010203141a40000c2030194240c0060544035a41c4d070780c07000c81c0d03031003900b000840020742803040d0749039050f031101c0283c00100155580c091495503518104154000708540e0205a0807120250908140442640280d40800800c4034204e84030b80410440c80460806446e68142d07040c000c1d40c4038040c000340d410035407650fa00014403c0c0e46551a1074a02c1400d16080070035581d061a02041c901503110b4021510006503030020184020080e01240c0743e9624040700c0e10a403c109010751065a441040c0c2c10180e1042c0c0f85126081c42c004030520034a030080311050283c1840754441e5800c2580d600d40003203160456000402800c80000300301c051a0000c01039403010141300101d2080c007610750b074001000425140825400c0b9950000780000b03050003441542e50807a8200c0741441a0702e142c441c0b141c000e00c1204d00f1540b04501e0041c5030b40b85c492003031043d204001d07555802009103450704020400718141100c0140000340e41000045180203850001d00b005152030440c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 421436627 1250 421435377 421435387
    0xb040b10050c070803040e0609070c0221010b0603040303091e11060711042406020319080714400902030c070f060e06010e090304060815091003030e04020a08010b030a0b15 75
    0x411189d0f01c80a0b04d620100908580344201603500c2d540d5210304441d4510703024a1001c500110203000d03001008685622140100800c018943c050704a0710b09103204c2d03410030980700d51561450700d0100201e100030f0840d00000911206600708180141215801800038680c00822080002d050740c81104108204c1114070305680709030102d08502c4005402c40f4006181040c01e00052003195038290b030410070070400074130003243c1d0150244a03000c00d04400890b2555036001840407404000701c00078903020b0909141611001c21000c880d000c840d51101d030700d4045601503c1c082ca10000380d0005002492048010030030040040c411711090340000c0c1c40362001058900e41c00c4441c50808105901c0581e120100400300311410101000b210191001800e106c0300e00d8981040e02da032018654103615401a15140606c81800141b6581d08100d910a60354101e07841400f40902050f0b0140d04507071004aa80c420042c000c50302d40002444e8030206810740024414540400aa00c0c0401103074800410840050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 421437877 1250 421436627 421436629
    0x3030f050421030c0203091e1f08240f010201320a0b0a09202a0c060a080402060f070f03080c18061b06010b0d0b040b10050c070803040e06 61
    0xb652076071410190404005011404d44007035228410740c41114800c1502c1c0c0c140c60341c107952a8800c441c90340c10140078851081c0c07000c10010742c40c1658510fa031022502c500e0000d1070740c1070f1813100c4241004880704c100f420751030201d080c008100c618001c010b06554032601e2810074000c00d0000c121080d80d4031034a40145075100020341039803a102030216142c107820705103150b00c40c0d150110010103ca0004400090b5001301c00b100c0c441410300320161a0004400244204d01c3c5840c0043c0d0a07900300512079000100f4030860285641d0300c0e5202d010b00d8002c60107100c2042d145001d03200e5070b03602900142c429464803003e89032441083d4042501110408803450391281419400035140d075000c58031815840c600145036201c2c1000b22031510016120b09000911120001d02c02c42e000d8030707861000c03000c0f607441c0e584484040d0260340080444006883c900006011145003500505910000207062920000041720007100c250b0712644030381c1c2c1640310b45000060700c110104001c0c80205075520301c00d9000c0c1410341c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 421439127 1250 421437877 421437923
    0xc030204330e0a0b0f132a0e0d050706050f07050114010303021603051b01200615060315010327030504050a0b09010f0e010c02040e1c181203030f0504 66
    0x684120102807030030792503200b1078480314259600400200d400d44e450300e440102460180401ca10445c40110742d148044540da89020b601e034203450320540fa208515a041c400380025003444841c05009039001d42c40c10000180371380028801c11001c0e19005103000401e454050035904148500d1110b00741c00303001001450360520030049807480c0c6102d524811881d54460541d24006d0000c500303600340705444239090340da008031104080c14610148041005500340c4465460b44001c9928245d00b000b004c2c01c407000b46c036110040702c0c800c508401c130030341c0c1507a02103004400a0500300c40800380030b0a5040e40056603606000c1c0c4060841c0300340c0c0e5a5950f24208024891104070a50264440c0356040c440460741da030300450300f08080d14441c504031568420300c1004076800500104003a4110746400c1d0b111280ea403011411307822842907101c0c0c3c040c0d820f00c0a40110b56080403640c06000368111001c0a06c80164800403c181e03042c040d1070042040b4604000040c00c42e00d0583d001c4542a502c0c2c0c1c041e0002c0449a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 421440377 1250 421439127 421439131
    0x406020111030702030f03060a03151509020a0c0b06030c0303120a20070201080402011404030803041103030c060c07170c030a0207090c0e01030e070b0f180a030c030204330e 76
    0x80080c2c11414403490103545d034007402d414139025101c080002011500d03504114801541c00080702c80080300c8070a8903200828407070301c03038290702c5107080c1d808107401c2010f000f01c6444642d15a02c1021800654443c1c4100a10261070f01e64503001d480c0039140540e4003080035200c401820348268640d401c003480860700310341155030400c0918204000307451151194909448403185c0a091009055032a440101c0d501130062645248088002c100400be022050010310303c12845008143e0803800c034a0109680e90140b003440082640c011030000c1e1043c040d0710081d066903072049a601801d01400d00c84d500380b9030020000d065031a403011030391002c43c5504000b030300020026074104200401701c001004100403072840200e0b040c50f403640f1019200b400c080008500901c503095100c0d894810035400145aa4018401c0c95001c005c40c00e416582842c001d901101200e5001408901d034031f2855003803001800351407218070046074400c1c0d405001c14082800c0c1140c103004048004106074200980c003440740c200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 421441627 1250 421440377 421440401
    0xa0603050d02032502011d0a05040c030603020a09020304021c0501140711060609010b091507020303120711030c030a032c0f0106091404141c030f05090c0f010f030b0604080304060201 80
    0x1142c1c075080540d800840080c0d030107220700140700d21020a070f00485c14003121940081d03042407a040b6460f82c80c8cd4103a100e00f0550b40f0071944a0366071541c3e4044101680815100070b5441150040c0d44200d21401100321a204d520550000c160740a44050780310000b84103c90726004a8407040340186401c20a109166002d40105e8405d034207075062030011241ca01503040c01500640c4000390000398001c021043d40e005580c01400c0f02e942e80d1003030940c1e122144041d5105008110030000681014102000392440000b07580000c5050001d100c07003c5010b8042025030f185d40040401072102c0c8256119150140321201c4401003156210040b08035084030782507841408110701e0036400442402000e120590040d03007190f06040c54261281c69a801c203285407002d0000000c10104400d40b00d0b8064003c005036a2442c82c08120342d0307075021810350b02c03480e8511040f41c0c00308009030442003a600402c82c08040c4609442c1c000307201030421010406075400b641010072031b90b002290802005909003d075804c0c2a030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 421442877 1250 421441627 421441687
    0x80304090c0c0c0e070c020310060e07020d0503040609170a020a03081003030206010308090102150f01150f0527061803011803050f070503090d140609010209180a0603050d0203 77
    0x4680c3c03a02049800540501340c442121380d001300d8402031040300ea024200350002c0941e410b800b5481104001041d05118004070940f80ba40020aa24004101070008010b20389400d80b130741d96280c4d14034000b8150910100c901c10301c0f601c0000c240c0c0c10044050b091010040e0000d14001081d814003401c8000001d02d14140a80c0f05901800040e07404140b842c1100e5104043d01d48941d0709000503410180c04113013201305004420204403005035101e501a04071603220103109015002180c04031500c0c5103114407140460000c1085c0c144540480c0103100e0b0055000d11030071405003c1c103000801552003042d1104040410602c40728023441c080c410903400c1720b114258500b0803a0b503a0380180c003038010030460025a1401140201c14030000703104440c2019001401c03610300e00454600740d140102100d04a05035445410700041c2c401c0014402ca6a000800502c4c9a01c0404038500d60702c0b114a0040041c0c1020b0b032110f0002001036070030401c004004015802841d11501e5440300754035058904080010545 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 421444127 1250 421442877 421442897
    0x603281a090309040b040e2e14220516031406040201020c01120b0301060b1c0b01051611030111071b06080a0203061206010b030709140f28080304090c 66
    0x8200e405500069074082559117103000007a0003404501408062801182c13540f4042d05035100c0003041e1a10110711000c0300701c24040e80b04003282e140c104958050801400841c0c4001c20420306420580d040103600142d400b0b0075980d6609001811403500525402032000f401081001881a469800d03001c00500e80c1c0d251070340000350b0b03a00031551942d0500007000c4030b8a40c910310540007440403003009002404803a58a1041000036801030f0301013005072039002a6070241241ea4010014030302816510141041006169010036501d0848100e419940d52841e5550546017070140d46401da40704811140c4440746420000143c0c242c02d02c005400009919051000c10780029465400080ea6680183c69070b03581d10104554496441c0d80f42c0c01403081c0320000602841903c01148513070515a0f071030f032106542d00350020180d510440e0140c2d201003584400c52040c280000008025907000d040d08a00348180590180e4000351600324080603000050240481d40d002c0c002c4103d12003003484e12070260 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 421445377 1250 421444127 421444141
    0xb0417030f0a2d050901031803020c0907031509150f03080a050d060503150a06050f03060c0c01060e09030a030b1806040e12131508040b040b0603281a 66
    0x2c0c400c200e40c00c802e0199050385024440004481007a0641d12146600041c2000b0140507084c0d0300030700e024034006428100300c81040200f420352403004542c560002c0020002c900b040045030340004225100301640e519101040502c5000744000500c44102c0006405101102190b1400f8160704400e100841d60041000040d810904645100381545000d41c1c450b0103000308103000c0d1030550302c480e44c58170805006004810f4a035002c14010440303941c082102c50b1341d420074030284441410495626030090400501c5d008640340007440c0e080b410030f0002911584480c5500b0301908181d6201c062a0710214040d107000d81c02d84101480007800320303509002404200360110b280d0400030310701401151200d82e0501070007400c02520140c51502c0002a4441501300e5828600b410144102c00e100722010400c50449806174031010302450304100c8940a66071a81c960901c00c42000e0700040d058464408100280c1d001441a81d250241c00751085240820904060406142a44501c201061241d06000b09 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 421446627 1250 421445377 421445407
    0xf0a031a030a1a090a02040905030a0305010905010807051e030105090307052802010c06110f130902090603070807021207080a1d0109050d020a030605010b1c0b06071e020a0b041703 79
    0x140030f480908400da0b41e94032180d42004418040250454107000c400c1c3c0130401c01001078500c81c01155000c101a80e070310070045e0241c030001c1c8190481a04107080170700c80c50030304070f941c5007502c6020f82c82072205005030f1000c42e0031950700321020f000a4001040010400c00280615007002c00303c1c44c81c103c1110b48000d00c00240d00c07080c8900a051041424a5004001031900641c0815140c15405d90b207c1da00e1007009143e50b4040580401c06220b02180440d90102520945a5444015100d103056545030300c410b880400c0060180d105521500028030031804800000f00640c2d80305414031078880191081c00f5204c08000d0210180c018000c4a8909069a20003245411113004071000c0250042c00d00108208180c02e0700041c002500303040002ca0040d40b050000c11040b03062070341140c0700000b9130041904462480181c2c99206070200141008200c50700e0260760110805d00c0900c0410040f03a001500030161940102420384020804005925204215202580005d8007542c98464a030f43c1d5095 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 421447877 1250 421446627 421446653
    0x903210e09011508090f19050a060507030203100608011202010311040305070603090c1d270a0507050108060d1e03030e01090f050f07050a150201021b01060e010605210403050f0a031a030a 82
    0x40e6000307241f50000d09204c4200f007019050303a0054001c00a50030461001406540102c071440b054480c0f64000085442c8580b004038101d50751810f6408480300a81c2c0110302074500e0003221164004140300c048085030307041c48407070001c000907180040c15121900d407034000d10a90b9448070401c1e01c0c10000102406401d4010140d02000c460041f040580300ca5244241c00c8501c140031004612500044030100140098110140c4200740c882204079515107040081c600c039250001852030701103125600c56078404200701240d41d1310a0070045030040d0ba590030282142c00d150015a51403a9010311502802020310102e03480d070304c0d62809095001e080030049078602446103c1c0c0c01107030034640c4070758010a100303605552980842003d5140b00c24610010140a032aa600800c400b01952000008005c1d014804940665a07051800700e8542d10f00042d0072542c482c009c0c000d0701400020055040c0c5c01e06e2420082c49070180f580c40000305144413211482e600f0a10307a581500a51003001604081070325111040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 421449127 1250 421447877 421447903
    0x6030411011206030b01050405090705060a050a0c0210170609060d080d060e13061401151107030209010b0c060a090b06090403050903031201050f010903210e09011508090f 75
    0x149000c0000c100480315055051128404949041d10220400110003181c40c100c0d44110307014032554132500f804503281c8281e40726450340300c0401c00610484034001c10142181c81070504200060410940101c0c28070b00010105000182d500d4100d0503201843c0c0002c15007004080d50080e6103440c00310301196403061405405007807000041080c055440040d0441c0c801303486210300321403240c00d00c0e01d80300340c0c4408401d00032205107041903c401c0000d18070705040307412101108003115281c50078100994414222404070001409442170101c00f43c3c0380c02c00301c3ca00034041054110364804407030008a0520002401d0b43d0760b980d0416140c1004142501c2d101d6810240c00c8864054a440f94a07060306d85c5c2c4500c1d002503170107000124601ca030749111521a41d040b41c9060b20980c075140d5078103004498071061400001d0a10120300326003c0240728004c0882d48108650030410800701d0241c00182c0c0c1b1040981c0401c0c141000c000045503000d03400345540390800840801089401c1116000d80d40701d82116680c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 421450377 1250 421449127 421449143
    0x30204230129040e04020108011e050d230304080114010f0323190201030b1f030209030102090a0b07050d180509070c06021809060321090a050306090a15020306060304 73
    0x9028180589006608601c2c0021115640742d03078441c4080d00d100012501640420320a80000683e298154a08048042c064001c8400705051070f0400130300540440081c1c41040041ca0300c07a20000c0d01304102c00b510b010b158011512a86004001403d40d4080703140a2900c2c034104004000d0340008400910540f07034440040d40c2c201c0c1c503080d101d090000403407070ac200140c4640c50390040d0a0074030102400005000307036024403001c5143c1d0107124820702c0340e980140020a005c2010f1140e14403030350281c40e40d00380060000d0300d011424000103c0c0d00755190004024864000703007800401070100280b40c10286a800c016101492100d1212051201d521850b8090401f4800251560748200034061070140e0180007151175410a03501c4224141b802c009244c0649105808241245000a480018540c4188007190302c170307400c0c8000820340c0e003040c00c0c507a80003405072a003c152a0790038071207144a0781d1002c0040c1030408460901c5406d40c43c89d8002074804510400c240925034813441e088943c010b402c8001c0d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 421451627 1250 421450377 421450409
    0x207060507060b041e050405011b0c02010825120609091205030714030405030d0b01030b06161b03031805010c03090b0304030c021009090b0415030311120301060503010302042301 78
    0x803401402d030b4074860103e5034000417030081840f00d0a0780b20034010ba000f400200100104001161921508240d0010105130205040c50056200c0c0304540d60201402d512040411740c15081e88030740307062043c0ca4101091801d0300c0c50604020f141715001c024a0184820b01c4403107a641c0340d0100c040c4114815404001d80080054182400b4024841d20301c20f00110a540d00d2815040041d100c1e00b11100401c2c1680c2001c12145880d03119000300000440c004000350300c0c02000c6000202240c0b1045021514068146c0c40c00d5990114000f442e4001c40c040d80b907000e07094000340c0c1030404501c141e4111605105110070260042903020369a81c0a580c0030102455480d242c500301983d41001e450700c004d5018256400c2d1400c1181e2000c035031011150f5205c000d20852071414108070540d8401e240c04103101e0030415041010038030802040500005600640d034841160301c004484c568003d80190300412000801001142041c0c40780001400c0100841440b4014510f1a4104403006100c1d0003603600102d20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 421452877 1250 421451627 421451629
    0x100e281e0507050d03113703020c1003051006020f1c231c060b03060f1302030703060311010503070215150402070b1e070804150216210207060507060b 66
    0x118040107840b00404802131405685801840e40c0300003150f40d515400b9100d040c101c1020204d100c00c2c20001001c00f90030701003e4206244090a00180c1d00780c0c1148a0b004c031070390103a00d443c1da41c02c180907036a690114152a02900c0070b40ca9164a9100c0c004660284400744e80c941c0b00400e41941c041e074800751140c004140e40c0c0040b14140040031603868210013101040c4000f0601b039004029820416668510410400c00c0c00000c0325894441c2080b403420820000307542c4e150060743c0340c0c0315810042040da41007480020f60022030304100c072070402090741e582003401400041c165400d07101e00e0900e4550720350318000744001e440d0712810000f040041c10b450080b406078548113840107011000500119240d07615810310116800c01562280e00c0b00103a880038503050700304c030111180325090b0360311003503159110707503032041308a840c0f6080f01600140c1c2403241e100303200c0c461080c0070542c50266040814a9540400a9540c1e12060200c003080d588030329006c208850701b01080c1c5000c00d400400005651250034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 421454127 1250 421452877 421452883
    0x309100b01270e090a020d060c0512130c14010e010c140f0c0a0b04060507030c020f210606030c15030405011b020f120906030402090603100e281e05 65
    0x3819142464000d261510300000079010b00700c11190014452403440d200c0d2840c0d580c491505a81c007941212820209070003281d01500003540606840c9000743c540050100106a80c1d44296440d0401403102048202400701160701100034042d0300c062610558281310001c1d21031104940110f050044100750f9505004a120001d0f00000c0494240c880005403403608030b8550490890581c0701c2c04881d000490421400e80c00e403002d44045403981407400703a41e510705032107054251104070391003400c2050307044d81516800a51240358480e40c03040003586401c0a451410410014060350081d0300035420050030390b5881107074134003c06c072902c2c80c03640d2502d07139003000c6025004800c150100000d1500c0008030300c41d4001085142503610006451030400c1201c0114020304c80e60f00f010341d1042d42440072402500e0816451608458010100d509400068103c40c01340c500c0ca21804586070421030741043c041c4621612087c681c8042c1500d00c40c00c0d8a150340d0000c4601042c180e20420701000c0d10800100300e010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 421455377 1250 421454127 421454147
    0x405010b0301110909100e0117010204081204060e0d0c1403030c030a02070501020f0609060c0306030f0d12110906030a0203041a2d07020c0103111c050115050309100b01 74
    0x60003d10401034050049070540d44a442c056014041100006162181e520b6580090702c0c8214028025a440c0000d00c07091402944582821554200400a508407003000411106240900d0303050f00c9915007040540901a40750700b03d070245030f5401d19500002d10b451208015112030f921801780c0c0b4051070001c00d00c0d500502402d50000e1200141428845030001140c3c42150801d0342181c8540034100d20303940d02c40105850101c40b82c0e114201107280000080080c40c1c1c441005801c40b030401c4c1c0760b448640e14002c019913524021481075080014141541d00500402c0c10203070700725501d00780034800801c0c524440103116400b140d5011002c10100100d424202c0310301c0072500c1c00700d061424241a020100c80b40900c60591012608000031013010404c104144034450580103810745260010054010b01a4000e20280d040300411400e100fa4003009141215811400b0001499604241e54858095164840701d4144103040c000c20020450000e9001812030b860f02001c100390600300c1c0160b8046507030f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 421456627 1250 421455377 421455379
    0x1140f040e1015020a0b040f020618030c0a080604080901031b020709050709081506040f0e1b0102060f150a050a0602060901062c04051608031e0418050405010b 70
    0x9000100d00c1000840700d4020000b6001000c44507680d4801841e034040e50288100240e001003202401007400804515409401900a10724103002035000071000d40c0078039600d00c2d040180c07261000b00e074101000294200c42003669030715009130030b04a0050ba01d6400400c01001d242e400a20000b003644240c00203101104500d00c415802c41c00c05501a4541404c1c1c002c3c61459441c0200154006100301860011100d402d000351103502c003000300c4065610401001240c02c0340e103d45000796025018803440c1e944030200406441d6040109030f401c40c51400b09525681150705c598184010704030782480094021294440302510301e42c014001c14020707142d80e40301d5680502556400030b1881e4000c6545441640c10800030444551120740c260740d0241e078038124214480083c59144400d610028007a40c0250255040350892040110744070001c4e8201d4101c0310154001140705c001c03400c2e040c042c00b0340303e01e010360b5181e04150a100e424121440c1d00010114050f45a002050900c00c0a5101c0f05070b00d60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 421457877 1250 421456627 421456657
    0xc070807030c03030f1e120e1b09090d0e0d05100507030603110316090e03040317070b0109060b070f080706050705030114040b0f012307032c030c0114 66
    0xd07032428208428001840709501040109003070712082071091500e18401000e03000c0b40d40480e41e5111003111300004502500c854507030380d243d05440c010030800c0b00f0700c2c00c1c2c0c00c03007400102d170f00e200c41090002c018006000c40d41c40358030009813540e0325500300107021000030060b288403e010b6440d040ca240b90401010810303c0b11840c203405c3c4500c1035490380121099900489801c06440c0e03200c01410382d5044010500141d2046100007030110842e1070304010ba2200482c01144e083c261a92245034550740c141c0308080e44440b0004a0030104142e6001c07460040c1042141001031a103003003502203d07446413440007440320107400400f904000347c40050710001600501e0821983c900400c0250040d40700307000d02581040190103d2100f441e041c0504020064090315030384801c414200151559103100701055540f01c0101051000b504143e806401c80301c0c000d0340c0700105002801d0351a1460482000010700c99124110b406225840c00140211581c50a2900030506003402d4403401d214001c5e0302090312056 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 421459127 1250 421457877 421457879
    0x6190b07110405180c06090a09110a0806090115050d020d020a080403020f01060305101a090708150409020607120504120501021b1f09020109051809010c0813080c070807 74
    0x58510181c0295840036542085591180110a40c03e80c3d0489651040355000d10350701d10311424800c0140001c904007400e60390320103441d80340602c10794031681005000c44501189008140c2e0384941d0b5207402010a4400451550428610300000025070107020144840003880d18056030040c6d048038a10078040c90110740b1040c62030341c002d003c403d0682d8183c0c0148074807541000b17084410301c10702d000c0343d912600400e052443c10054601820440030303100004060400344010b545c890101c074520480300c0d5039420700070740382170025101001c0016030b40c180150319006081700141c03200f8044819854004e8440203000300c8001c41100e0500c07a07500035103144c40614042d2000c000054001d00020398084421100d030f81e8a1181407070340d496482d000401d0f5000d104029003005142a0f0000c9199801803508850300c80d02c8401140c2e08503a04031844049030061810088520801e00c47c0c88102c0305203143c820201d0030310703001000460440c140e029000c920006424641c1180401080c4010314142d008c3d100c00c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 421460377 1250 421459127 421459133
    0xb09040521250510111e0c011127100e04090501060833040305070c0317041707030b0c160c1509150203043005010609061d06190b07 58
    0x40080c0d008480b00e1107070600070808884030b4041e0007104500b0802c02820805d6606101c0c484801031101b20354205010020311900e00300070b000b090524480295071558070000700c3c01d1001804000006401e07040c14484604d00942e0318808031050000075490241c0c000800741c0002070080c0b00d80c031001009036107009000034001d4008141d00d9120302c40c0c0711454040c0b0145507a10000b48500004204802e0081000a40002c0c020000b400900d0b00030100e0b40c0c1c5d619242d580d00303040100001141e008180010400b00070085014041182c3c115100c4044c0248918507500d800c408540944403000c0b4441c00f20f0710050190702035500241d5940c018141440e0700b6501c880044080e05030090a200080c1a20408610281d0701000d1100d1910958000d500d01b07490100c0c10100b03241540c0282c41c0d4600205418204c624a40340105401401000001a102e10f824032150803a43c2e1544860303054000c50b10304078445950303138100e0365000348291407810380880d87c01144010b2540300d81048906136008140c403014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 421461627 1250 421460377 421460437
    0x303161b090e0c0306040210050c07080601090b1e01021e010b13090201090f080d030507050f0d0c1b08030f070c02060a03090b06090103050607031109040c0305040203010b09040521 79
    0x1542e1038010f0701e0f02c1001c00000e254552800b150040e4000c000a490285407074401e60003485016103103001e0b9041c5903202e0055074184ac0013a84501c800a4488a2031410741c40c240302150704041003c100d075401c40c0200c40c0041e40b58114008500c0e404240e0a25807500002e0a41141c282c80f54005c1c2100d6006484100c500010140d1035021790005481c0500440c40000c21010301003550074402c006e203541e0310592406c402406c0001c06850070884140040c12101c44a04094440e214210700c0202e10b45000302002404031200320102220040c0c4010b00c0350105280300101c0360001c0e0400d0143c04250303281c21b13060345c07a1149a24002d4010340c0c00940311101c00c0d80f41c1d02c41c6031001d108044c020740c281c65440c1004420242800b000e021600600c1c017081180c0d000381d2007d01100c20b50400107060005160001301102c20b503141c858007107502d420400c8114a4284140100008200d4048032103083c5615600e56904000c0c0303d0a9003203441014252610076900c0079617103d5164061500c0842c05600f400e200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 421462877 1250 421461627 421461641
    0x20703120504140d18090507140c0102070204090822061202090a0f0b04090513030e121c0309050705031b010807030204030213020a02010c0c08192016060504050303161b09 75
    0xb4040044110101d1b540c0ca40380a454021351f00ca80d01d2540b1410300d211081700c2c81d0b201c45440c0d4500d650802244005842c8d83c054444001d003e4070503152140e0700385600c801c0d403d0405000c40e400080928050010f560803440380b101352201480f0060300d0700703d42400300c1c600030070681164120584080000a4a00b418030040c010b441190406110503122a41159221145c03280002c0108090500c001c10700c1c00c201021a07580e188a80845035401c140140c860700300e404035030b003540009444524040902c201044403000400c000d50041c01d5a00d6680c285c0e4101136000380103581001040b030081000c1c80c2c46034050b2409180c0041172000c00400324001c440096011001000165082920f034240b03050103280312501940c0c03c030500f1490141c004111080382c42007a02000c00b80f00c18501c0100071440000601c07120846450000c085a9034001004018881c0941c426820850100414070481d2404030039911401c0c2d489180b18910201e920b00040c00307108801c1322108018000000107018000c0d504000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 421464127 1250 421462877 421462907
    0x908012a0503040c03080903030d0e0d111207080f040b0301060f0e010c020a050f1309060207060b09070203070305031305030c06011e0503060621060103030c0b0703020703120504140d 80
    0x108546000305094945010441e4003030441030b4181c41c20030208100d0402001c00340c0c1c00a0a81e46401c02801d03000e0203e03480300407014a16888040324101c9140c116802d0000440b113000200507200c034007504282107105113107008041c11408110000a91500703800d4802070900c800da1151250b0311060001c240066600000001507c01006040154016520500401d801504003031101d0f05080034440c40620390304c01c803a0030055018078603100030020302c10460080c1c030411015a0796035403800c00c3c0702540d440056162003132014000707010b1030640000455507070640c1741c01d20b16201d55810651200c0c4d00c800160240c02c9000000e80706007140da0100c0c60f40d0503181c9500c69542100c10402c406144002540a22905540300c6004594a0310305a41d2080040c0d84070310701407900d000301015050411400707a10460104049242c00e1080007a83d840d20b5500624a16045040074040d07100103000b101404290b100ca61b61301c05c08038080c80f0704c4040510314007080400f118074400383d00f40010b008920602c002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 421465377 1250 421464127 421464191
    0x3060c0a1404080607180f060c0b07020102091e011b0602070b09060603070b250b010609050603040c030b060f0a06180f15080a0b0a06050703021504051c090801 70
    0x4200c001d035440701502d041d90040d1006044680c2c41140c1600c6c4000da141c50861071100c00480015040001c0d060071003e00701a55480040d04000d140c040b401c201c0252228041d0b900502c4811040e4440c104241c0900c00101300700b00d0341a02c1000181c0c0c08040395003402745508200d010740801e0142d642c00034201d0301d00c80c0100c07804543d40d0303480e503a4031034400381c4d10254190416141081082100300147c0341d0007802c4542d6070b8180c00c02c00a07500440c806407004075500c4440000402440750000ca80000034803054078558990308e004d559512402005000081034080030801254944e204c40011104203140602a00c200301d480c0c14010f404903551000e42100517001c00e2010070f08142400b04041150458034008130040c0007040203449900c0001c2007505076641d0347c000103106650b040d070344a0041c20a515895a02d003050304000b802c107200c0c100183c840002c00400e01c40050320000c2c5500a81000b401010440c01c800441100c0c440410741c440340e503d40c00c001d609a400070000d8409000e80c2803001d58 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 421466627 1250 421465377 421465397
    0x2209050f0901051b07080f04121401020703051603030b04111308030f030f130c0306050a0f0e3c0d09050a082a030a0302060709050f0a0504020706020903060c0a 70
    0x9a600340da5040700c0b55001110701e0304859280110b040c2c09085c44900c20402c2e01e0030841900080b0000d604181d0101180c0082e2000603c14810f4601307030070407600755900007503250503110389015201d0700c24041407005003240301c0005002c0c1840307940b2001c0c0c1400002c20610500c42c4046030505141c1007190b54200c9200746003c00100b030540002114980c8a51500d000c0c150340d14410011040d00004040002280301e40c200500040c000c124014051031141d80006200c0c02d0078244039080b03a07481062001390f546408006d041041d00000d20386d0301808e404c030300300c3d0301c00d40b4906005082200c448950703c4030030f545011049210700c010900f120600c07440d0780c4402c0c80035a21000c000c51a95035100c4d007416508454112213a40c10001605100f800481400d1002401c1c500b02085c900b101b07d46094005070060014000c226502c580800000e040c2118141c80d20782c00741c00000d82d00507242c424a40f103030b9030008404081100310380582d04801002802e9503481d161442c1c0f800801d61007030503800b00181024603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 421467877 1250 421466627 421466641
    0x14010201060e0402040c200d08130807060905010605040e01020912010b01051b0718051006030e0d0302030417071515120206090102070312030b0a0b0406080c2209050f 73
    0x80390100702e880311107518980b916241c090100a10450b081007003009a0341c44080841d0700d503054104204551b110090044070b41c00e503801080305002800c149440c5480c3d071a45008500ba180036148421b40010f40010003074224900303240142055446a0741040c1408004030100e04194040c0c080c1d0582500e0603074076120b15250060807111102c1c1481c2c0810780605c0100080c00e0284205550040b40d1000c94078070549586122000300025410a50050744074002c001060014141c51002000e0908040c04050300c48058030307480d0b503100d0044408060303001c00041c05210300005000c52004549902d0ba0343d40c440c40c00c04100c0e07070410700e007000000307420015803000312240b80c680b480441d2407100c010141d00c00143e00b004459402850082d04612070140003001007000000c00281154281d140060b8845122051044601456000c0d20b51800c091100b08a02034000c1945c0b0b03031040403180d0542c2d4401008041c100000c500b6056681464080b6030041004500c5034005030040e0041d9082c4805580c0b030764 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 421469127 1250 421467877 421467881
    0x2060906040812040f08030408070311060f07120915060509070e0d0204050a020903011506021e03180114070302010212010e0714030702030c0105040c090624050904020910080114010201 81
    0x10700c0080101d0b00400a00c0b900043d01071074690064441c0b800c1102d22841d948451300a90800c0c4c6003a00c00740c03400164101019048001c0300000302845024201d146800c2a0b25038010f04018403007810701c841d682244609500545c042001c81d44d01c0052582c413000014140001044940121406135104802251000d40600d910800c0ca820051442205820640c00d2101510340540050354441c6c013444164084e95083c00754040c2c00503000c03009040503141c402c0007483e26010541074480801907800c0c01ba10400c01104440285d221b0120840c04682e55200486a07a0601c0e21145140c80001c50a041099819001481111402441440c039640c031150270728040c0b0019940017002c1407040608400c0401c3d240c4c003550303100e109401039a0270b000c6c00c0d982403801d503403044408031820200740c0c00a0006c00b8007403040c64080c0c550b035101205540512400c1280d03550140d10050244240031074141c80079520b5030100c0342480006010500007810552002e000b000c030a0140c001007601d601c0c4c0c04d0005500c14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 421470377 1250 421469127 421469131
    0x2070816030f0201090b0d09020405010b07080904050709080304030501050a151401080c040b0f07020316081b0d14160602060c070314070b010b2d040905100e070f02060906 75
    0xc000000d01034a155a4542c0581c00301000b02e05111061100103035003200e0001034424072000040205082c42c5920401c000c03220140c00080300400c05101801c040303801e035002d5031012401a140000c071511480801e94040c2d08a9012601e54400000d000c020054103420440c01003c82d04014000040005c001e4450744145000c2d4180400054800010f2903101c4c54981d84c0040044541c2d528068568900202a5001c01d160300d0740544002903140440c1401c100341400d00b140c020b81d08a20a04007400b15446415a5207a4140400c02c601e079141c0c0d9940d0b0f00040d200041e88841c3d89000d422440b4000d686513400350b44110b01c0c808101030000380c40c40c00440d61510500102c040c1d40d00d00340ea039541c2628804d8451805880320f207818815900001c0c820310b8254040c0c200300c80420303214460030001c1807480008203409103030403205a0b0584c142e07508000988003581d030440c00c00714241e62043c41100000f0f40350340c00b0601907450b0200348114150440c1c41074030b008006600351901c6030307549403900c0d07038440d02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 421471627 1250 421470377 421470403
    0x40308070602031306020d09020a05090f13050f0a03030e0d0903080406050d110a050915040e0402040e0a1208061011070b070507030501140f01051f050a0c05060a020406020708 77
    0x1044050005070321503000355481802501003850682140d210f100498005510b082941a41c40540e90300390700e41002d92500500044618409a26002010861811006d408030004030381501c180000c1050a0003485270320941442211810003850600a0280074040075480c41c601881d2140720320349201d032003408262504001920314007854420102e445600108140a0b5a80d403800303141040c41e004001085940038981da565219140302c0d0402001c00c114520034010745800300810806c0c0c001da503916981c400d0b011907000036a481510603560600c0082a0010801c58203000a03442c00b0f5040000c0c0f07030042c0030540340e42c5921111741d80c080e81c00007401051307881c003680030030b00800038280c0c50381c000c0040a20900c20b98030403070340e079540703503420359800c44040c04840312103d040007018030a459405004000445055516000070785c0d1607040d015042e00c1200c10000b0000f09820803500801546001d1580101143c07264646a07036040000d40103400f0f184c005000d0503c0020361400009002c00c40480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 421472877 1250 421471627 421471643
    0x30c080c15060603101e0e090114070c0c051509040e0d030506030f1e0a1401060501030c08070e01080405010b031e06061906030f0f020403140114010f0905090118030906090b0403 78
    0x41000140c2040c140200391b85820302c03118800104038584031002c004d00840005001040809201014114a4000903c0702c404c2140c0b4507181d00102d00505d08900c00c442065030f075a0741043c016240d0500700c0c891240702c6a00725081200f0072020a000248022010082e650108140d450320300425480c0c0300380d00b5441405503c00c1d110ba02300500981441c00380410030313100f141c41d911804c0d80d60591001c60003074544c003d40d558460410003540c00d406424451742040c9049500e501d0260009004030701d203600390038100296040007d0070810258060900450300604417041d800484c0c510050703210040314012928000c000105146040604002c0708088401e06514840b60500c40120001c04030302041000381c40e01c908085903080c00703a1009001641c010100c089010780030303822071801d440800407a5104004844010030101a001007043c0640d504a0000308058076400ba180d80035101e90003007032101518a14401c010550042e41400c01c840c00781d207800340150760b01e50078031034580954803020f01380c46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 421474127 1250 421472877 421472879
    0x601140f01050f0c0708150109060303170621280b060d0326180606010801090e071d060901080109050307020f1c050102130506030907050d030c080c1506060310 70
    0x5801840a000f801441803c0e180c1001004a0105d1604e0250b50104500741c002e24a515118005075240342e02402e2010b10500c40946143da0050420078120b49008100302c0c040c1c0440c410340d55480d8282c00b01840b10400c02072904c0300c1c00e079090302c648400045912290f0310b00003901200100d84106440c140d0846076481c800d680319400d00007500420361084040150401c0701c981c1c0c400801140c5130740c2c6134045500400d10324140310707201c9120360149034940940d8840410040380e40e90281d0700e9415203040c00c002040c0007000d10040fa1610f1519000b444051003016034008204144800440c17047d2411503002c03c1c0c50340d032078070080d080300c40d400c0c80a0181e400810175200541401c182c031080e0b8403800307800717031440c100101d41d40320381d1001e003140444490750000348035180321900b018180c001e8081224a1482c1d400d041038074540d070382c2061081d20300411807102400245400313a40b00082454114051079540c80303080c2d0155407a144100a070001d0241c905021030203500b0b004003500d105030346e050506100c107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 421475377 1250 421474127 421474129
    0x3060109080c0f0402031b0304030f120203240409080c0d1407030207090902060d0f0c0f02010b0d1401150b04030501060b0a0503180f03070501050f09060417090324090601140f 77
    0xc2c0d80000c03c0180c04407c1d1001d03200345e074001c036001544518040c0e0784540031071040c1c0030021f00700c41056281c080d03054014004e000070540c100c900607840c031000700458460944817601103005401c051101808404001c50400400c26010440120301c524640d078043c01760019800c0815240158000500103030710007541031008002035480242814002081a0b003032903048000c075001e68581c0c0500c0750708a0f803280361074010582c203c28a6618150103000a01c20300b020308001c20901144410017078040210540000d003095801c2d070185032100313020b14209441546440b89103d560707000f44421203c0b50319000c00040d4048105094480640c4182d840300c0c5980c480b42d44182c20303050907402d0305805015840700c0c0d44020350b0400041c0140e40c41140040742c40c2c9030050101903a4140205010704035003020301000001881c8040742e4081c580750b00045602d640100000c60b140c45109000e130b100c0100c031070000b104144d64000c1e0322481001e00c00c081b1101c136030320b9401c0c035201010b241c035100740c001090540305406 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 421476627 1250 421475377 421475381
    0xc08010e030a0507020d0c18201e0d0c080921160309090204120b0f07050f0a11191101031b120915020a0206130203100c020c030604050303060109080c0f04 68
    0x2c25000401d1140d106c1c0705c81d250003024500e240d01880d540700a580d584000c0304031394000c04004001030940b000a41007810003850183c49031202130400302c42003848440c60342c131030001030720161303009080c0400085859103c081c02c00c1c8811380e0311f210340b4840d00195001c100301c1040844400710503441c0780f509003da402400311034188aa9011402d011000030046410801403010308000d0181507481c0c038019005083c801140d00d4050643e0b00a41116001c2105840e0010105e075448040e1250345940d408102c0000c0715840d41d241c9041d200d90060040303400c0003d07146c4840900407809651601d0b40142480010b5040316010388a0240c1a00e007410340c504040c0c0108a038540c11070b24580c02082d120034940d0786a0240010712803c400f5241c1c045104450a50f041042070750158030810100f8000c00140c000a41d00e803468000b1146141c5ca0304464035100b8400c2c01001200310002d0300711070060801e40b86c055105d4000703c80303040c000b5001300d000081d404800241101c81e0000a406c9901160601c014480 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 421477877 1250 421476627 421476637
    0x40c03030c061d0c041a030601051504080105040809120615130f06080d080705031506030a09080307090303110724030b0303040303021b06030402130c030b0315040c08010e030a05 78
    0x1a4035699020f14440001c1c3d040c21041000044901400400e00403008104c00c5541703e80343d040c0c0101c1d924442451a07280003030100e054410886031942d1400c111850310080e48180e0300038203000d50a190522007040440c5010303090505040320000c24041d102d0300f205235281e1040310050200004091500010f0418040c1c4011707414050801007403203d801c0e0028001d45440d5030020030145e01910b02d01007602e900030351603034000d201d80c80c04e00d18509180d800c0c806040000c00c6030a114042c00030105c7d4000003690b100070f94840c0d0000405403a40340c5840045c000711582d20081d004584a0380c5100e403400310114903103007562403118080001d0410a044220103c071a201c092040c117a54200c80103035590100041e0009600c00d90052644803140f4455103890300c0300f0039006001d00d00034010300005030b0300c070040e4a1006012406c00121255152000c80c041c20f8140180c64042c040c66042d0121000d100850318402c0d4010090344100d550b50f036548900300e94440800d0501900144100c0c03015610483c0141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 421479127 1250 421477877 421477883
    0x3050f250908151006020c0a03080903010b04060605180a150309060e1501030c0f0b0d020c0c0901080703030201110a050403141006090209030607110c10120203040503030915040c03030c 81
    0xc1500c54845a105141404682110f0200745a180401400c1e691100044001c1c09091003d030900c1800b00740401c1450b85503000c0242180400300c3c00440c152000d5003c0028100c005009006d043d944100207401a802100901003804906a08018606090080d0700c02ca5580222054001c0b4203c64220018515144101c070f120340c0320080c010084104004080440030070b14881d0704594918542110a880e16501c024180301825008002200e6184150b5640102c0e14001580da0041901d803035040480030141103902c010280004640d0640003c0e200045d01d20940007040300640101c4850140c2c02401e00c5140003034410841803001078100401e003041001c5d0182142e0b441c4054044040c00e40d035403900060940e960100d0024100c2c070b01040800c2e000341003810110800d00084185546886c0070018541c003500250164007405841031a1108a003008a00110f4807418145400c41d00ca500944269107188580c03401d01c6000300ca0486124026503001420041036480d568096401403110308080d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 421480377 1250 421479127 421479137
    0xc0608010617192d1401060305040b16050d0606110708030720060d0c030b1005070c03081c060b1e04150c080c06090616030c0203030a020306031c030c03050f25 70
    0x19104d00b0156484840035400408000c202c20080800854039204142d202d241018140002d000100b2110202690091001c50303405541c1410110152120300c6034880980e011441e0800000740380360300a00052038a020380060b0343d03100e40d8072103078581d40740140440500781d07449015240c514101a240c6685024001a01c01406c0c090007a49203c11200c1200405011948030225400c0340c0c40e01a8640440c80902d050040c188070050702c0c4d02202c941c203400014142c040c000fa88014020b6104d9080802c1018500103110036900c403915035945401ca4a00b02d00d80600e40a19803c903c4410010359003a5400c1c00c04603804d840d130000c000c4074041c1c2d03280000e80d4078100410140950281c1800454800e265000040c2140c0c00d11034126030007109040d40345010036181c21101d28125901004927600308100c14009a00ca8481c0c10010341400e03a00701002100d490f58000c6105050b82540043e2000f0446450030051030f50b60b80e420715444002256202c440c40e50a1a1203241c014401d10700581d070074128506 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 421481627 1250 421480377 421480421
    0x203031807080a0605150103050c030a05060301060810060f0501030507020325021e030d0e06093d031b170403090515071b0e01170a0c060801061719 65
    0x10007801c10b0600d80003030b41c5164417441048401e010381121021042d0302031a08100c00e01d8190420440743c04081c0150070810b4030b07840810050f5500350000350141108200351000f2200d02c40a11008080520940308420b5190400148560207841054880e211310340145141a00f043c5440581d01d02107a1044202080c240c44507000da2240717240000a40034643d8400009420130b420540b4040d00c0500040030001104142d407900d440d0305081d203840100954002d00a0103031418074030f118060841c2980c12450280c07008a4003030500300c40d15103140c10b468400b04141c0700305030901c2d40312200d511240408a14041c40346024103490b000e09550144c003a00e424075140f51610009401907403613000b500308048000c15480107100b10303552907400041141050020140c60250b40b003541400500c100d441208584024680d21305081c44964030385680000903d4800752514400f45c50181d0a009003800111014500101038051034040ca0040003080306108c25241d8680f039003409411401c01c120070140010035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 421482877 1250 421481627 421481639
    0xe1015090b042d0311151204060212070801030f030f0507020d0305030901150e010b0a140d1d161a1308010f0510030f080708121905070f0203031807 65
    0x40d001904074582034101002440703008440d03003220300f00010302e0006011002c10000e03640a00700007a180c000d8504a902c0c0203501e5100c100d500881a409916003c610104804c100495006205d01da2854481c03103c59225a5000c0f0703085a02408010032603141c03802c001c001f1034040d51039141840120315100d454840c4550104a5904c1030000440200350007005010200724203000300c031541c140c969080d403101d41c0740540c03a1500890610074802ca0010000310780700d0b5a44102d005113041c0c48540400e030703500c1e8204440e0400a02c0f0b081c480c84440e00307010745a12140c190110b01142114880d104031010b9904180b41c09181c034441250b00c0701840001c2000b6044000000720403802495030600020304080403500301d0b0144c0d48001c0102910070800781082c80082c058402511111341c0000285440701c4240ca4050f0b000d12885484086194aa4080040000040300041010154070380c051000e03459982080e117114403286403070300c050303041803000501c88114080d100240c44802011030b00c02d60380d100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 421484127 1250 421482877 421482899
    0x150f0a1d1002061803160b090304030c0e0a0b01030b0f0f061903051602120403030810090e0c030c01081302092505040920030a050405011103130c0e101509 68
    0x50741540940c0245081024228454843c1035800303c0003005186003185080140d0906201038600a00090000e004180542410030540b006076500c070301607c00f500d44995807040c0300c44003100c0703540c01141812040c0c1300a51284c042e030064070001030b0a100150b00410100a0075104000315280c10650a100c8050b102003060302d0300020340010b8400180a00f0401c12020360300300d004c02054199030004100101c20200c00c001c40381140c3c0c16240543c51502c0e2800e00000c081810b41c0303e0903401e800c20a8000040f0300c0442c503100356200890032181a44581c03001034942602c112441c15040b08915822030150802060450340540920200c400409001c80078141041e542c0045070001540464240f00485030383c0b0952404824a00007440001210013125000348402090241d2542c1c9410108040040075048122003a4075861304540701d20f840e01d41d29600901002c41a540140b00390400100f00260380301d070501940074000300030800781c10458082a86003115044104015002000254040342c82c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 421485377 1250 421484127 421484149
    0x20705072606060f0a122a05011103040303050f0c0709110c0c1503070309050a050102040303230316111608031c110307050304030c120f080117062409040809150f0a1d 73
    0x100c2089403401c8c01c0c04001002903085c8003d400d00c0717074002c200c1400071907000802c2c0e600a400505540d527a508c4a608901c2c00c12400394041c10f00103003802d40c5140c00c58115400382035100c1240e070460300d808154900300190155002078030381d00391380c2c00c0020820741c41c42074002c41c240c035008500320340d0b07210943d946060072644039500540000f01205c45031118511200c0a8404806102c1019403c509100b0170b15a65442da000c452400d000c0d1005800505120600040c024502d071958100b008680e20f800a60326580300e024001d1401a1803109411141840d10400ba40c0c1c00907644018110340e60000c0035150390740b010b0701c1607040c0441c009a040004003a0307450407199918175a95840e0550030410058201c10741078020b0410b504000f070900481c2c60300010415030103207009000c0b0340d0000e4210740001c0818880740c0741760382007030000081100340035205009160600c01911024440c1d00300654800b910702402803042ca18003020800c402c40103205807012603814078060381000c06858a140011104008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 421486627 1250 421485377 421485443
    0x60e010e04030e10080a0b0a08060703050708010f0605070206181302091f23131e08010902010903060f0b0a090905010c03060b0904020705072606060f0a12 68
    0x1500c801c000c20103a004900280c02d01068800d1001c00b08244d9000d00824030003044480003135038a030304d00358107981e40c004403000804514007038074a40c0c1400c41d0010090007080f110000881c0d485000050a0003030344005400315030180ea075250900c4040c0c2d007080036650150000d005e40800a98405c5441c0d5951000d20480f1140c1c0000180d0382c14001c01407026900d860b121400440340440c96051295402c5a000c801900810390b182005000b10f00b0500468011902d903e10004240c100104080300a102c050348070078038042441150310b80d160300c0c5a080c1e03a445031000b800180520800c01c00919a0f401403803a003a01381c100842e16034156004030352032504a501c000640c07a107951098090100a201d0611072840038a018881541040b0f0070052901c951031040d80655070004a031002d102c0e06200d2080a0a822600000c1d081844000f101d1707180c680e81400840c0d40642d0001c14000d182210108802110103402c42a02c2450812110310f0b508220400b540d0a403a518000b00e25a05030385640054085 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 421487877 1250 421486627 421486649
    0x6090b03191d0c0d0206040605161b14091501110307080f1c14060f1f080106021015090902060c0a1b0504061a090111070305071409130312060e01 64
    0x281000c010383c03030680b00074200d901501c4414000000750703d5242c2110190742060400c1a6604044a01d584401440309005810004481d850724162682c4000c000c0482d200c5015400100c00ca03001044086182903c1ca031007104243c000c210349550180d1500e01c0d0000d112000c0d80d003084c07019208d0340c030140d0007000c419405000000d01c41c40c0e41e44034000884107a01c041c14081103d0988000815030f5440040c14040c0b1070f51050850b80029030340d030040c0b8040b0080000c0142402c05e0240409442c0003020f00075034025016000703100b40c00e02014494541c3c2000c1941c0c1c409000c0b880c001c00c02c4020a0540f009981000c0100611500103008000c602c40442c4111030040d00c00e21b05004031550744805405c8075100e2400c1c41e4003003114140804145a420304030200b0716a0790f440100040c0c84c105003c501c2d80300a80541d10002091107008941c00c02160300003d007451510700c1100400c43c4c0010201c82445000e150b02d002030000c28810000c0c0520311a07030940c0010440d0725111101002c08090380451103402c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 421489127 1250 421487877 421487921
    0x30114300a060516030e0f0a03030506040f090b0402040b01050c07210519050f0a020306010504050c0702090c091c030503040b0901020d06090e160605120406061d04050d020706090b0319 81
    0x55418800d100002c1001b00103840f201c40c444409a40311040c1080207000c06465001090540c0c0c1c856205074640b003000b0b88104802030152a01549460041741c0c00d030700c200d24041150460354042d00807600f250032680e01a200c040d0a1204e0040343e4030022528012500d01119210000f400401410304162a0b1150440c0118590b00e0010b161150b5004404c01541190050000613280040c00700d0648100f243c01040c140d0b607096000c4410701501c10040e40c41100c0809100621403180e0080034170304000d890101e080e0101aa8003140e444110b280107001500820010300030401c2410401d8005051708005032601c030044c40c00d4400d80381e05401107007149542c3c1482c440258020002c03614405c540b004900020b5280140203802030041001c2c0c0c100b0000000700250801c01c075a440071000e480303500c00421109030014503400201e201214102d90701c0c031503110880501400003072030714200d030302a0362401c0240b03003443c4610009400140212240c4c4110382e20b18402d540142c001d03d00702600f021840f03540d01c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 421490377 1250 421489127 421489171
    0x1e0302010b0a29090418241e020306010903060c090501090e060109031502090607060501082b05090d2306010b030105060406050a12060b030114300a0605 67
    0x5103040d94003207003200c0301e111a00c2d6001001c43e00340c14000841460455110035600d4042009001c5861014806080d818400c00410040107400910201c030303040b107011030310b103090042c00460300460040c80c07441001c60f9076406032018030b800031580141c0c10f142c0090448e07a26502d190079154900240000f1442d4400700303009650740001200c1c0201640c21450398182401d10000e0a6502c4070301024160a003402181c01240740c0341e4040703951704807000d000346a4603103050420300c004010a01500d14580544c5580708881a04011609070b01e9a0b421600b12001410800690b0325622031040c241c0c109040c020300601007070b904030f15020503001211014402e48090f5101c0c50400320705810000c910a400e100500003901c0d03080c107540a407005424802c0d91545000b100391803544d40708080382c0c41c0d03a00f00b1402050b00d102c0d0030007550403076240f01c500a0228100d8000c2054046c2ca00101002c55584c58441042b40005020394503521a071020658680301002c0d1940810343e001129040c000c00d049100e41000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 421491627 1250 421490377 421490389
    0x702011a0102030301050a0509060d050316030e040b0102070e09070e1609050a03080706090c1211101b060c03020408160807060f081b0904021c0c080c040b071e0302010b 74
    0x528000d01c099031856040c0000680703410501e008e82801988500700154507601c8540c00c030040d07907401c4000c8980790500c0380b629810322003c580084001440c500c0c945080e80c102070050007038410f0140c02406145040003001c404000d0018040b481512412000103032040103182c801d402503014503440c00d0f186c0070442000e0400030161f80003900521441c1c5040003c614214192000c40c2d9115401040300300113800d1030982c0240e240c010704813420340381141d0310030084030640103c003185003501c0080c0174050781c82c010358905294020106040d01601841c4000400c0c2d82c1c000f19110710507040050526407109030051501d2540b14614100c9101d5840074441d40c08100b08030002003105103020040c0c5208202c00522001028014240f003072035458940440800c004241e42c100c80700030b88110b458141000c51141180c4001c4d000e6170540c0c1ca070100340c2005a10444140703120700d190f40c524625007880c1880d512903603440904241c8205a000091000406014459150180c080d900101d4215100d03410485 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 421492877 1250 421491627 421491671
    0x180501150206010608090304030b010608040b070302090d062003190b0a0302060a050c01060b0f21010312261302090f06010e0f0609030a12180321030e06070201 70
    0x4030032030241154424603a03000500e00e0548007289060303c032640f1000e0b0700c0f40c074501a0b50001880070004000200d00305500c0040c0c5071041d801021440e00e5615283c406030220302c600080c40307401c1038480c4e12420104180d07401210101c4984001d0540452841520b100c0d2034100b5245844c0d12941c0e4806020760000900032680d03503a00840705e058840d4078550000e2000d110744040c142c2404404162204240000c2d84203200900c0c900404e6565000407c0086010b41e0140f0983d060141181c5070206000b0580e1542906a0342d0000c0700e034448081c0000103a5650300c0010741100c2d8007491401c9901400b280349d420714001d00e1500004c60700030203507104001800e80020803883e40c0106a004100311aa0f110241305481c18040d10b040040c08888400f14030203120340040c03642c00d403044003050340800441c078418503880344141c0e98040249802241c00107c1135003d1201805001c0d12682e00c4142050080d841d01c030002d60b5040c00201800c40c41111400e00e402141c2250150350b4410020400111031a2811 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 421494127 1250 421492877 421492889
    0x603050f01110403110f0307080c0a08070e04081e0d090201120903140c0705180402031507050a1206080a060c080c0c060112020607021906020c060403030813080d06180501 75
    0x102c14a501048a9040e6001d1880050300d20815005609030303544400007120000c00d0090181d41541c3d8580380103598540300f104600f8066180c00340c0c00103a0f0310b400f107142000e48850b0001071a064540ba194010550440892200c64804600e643e0740254080700050071800c105040100e08107200d030001400c50607500c05c10080f85030410948400003a230213220f070440c1c0b0980c10005a160250040e0300c40c036104590300a190090303200c50359007408242001c4607920440c4220111080550121981550f4000584410700400c005001040d22035001c2c0203882e1900c914010001011582c0710440c900d4958a5801581c030b4035520203c2002840d84440803660024034040e24600e0a00c260f400342e0340e680f030148078124072024550059021956a40100c40c1019001000c0344110f40500c103d24a02d00442c1c826000507101b18000d55001e420941c1c150741c1100c4e0141c0380d07155a6902c1d00d05503003940c401c0c80c4049420729400c014019100c52240329240240c185000307803041c01108011000220340060f0003030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 421495377 1250 421494127 421494131
    0x150607022422050109062f0712030e10110a080a1e05031b040503030d090f0602130617161110150504050604060503121b03030a0e010b04270c0801050a0603050f01 71
    0xd03d402c2920000c0c80d02c00503c7d842001103004001c8040c1001c0c59034008006500c18500800140356204c0031843e10f004080712404103400300c0f003000381ca040105807650303981600710103050000b1582c044042c10b60100035042c0b9000300a18080050480407a81003044041000801402540308001f401200e04100048296152608080000340e032801031718100403086403607458210401c07400c000401d0f83c96601c078030155211150303080a0704e4021254040d4000154001c070340203c920308110042400b6180900c5c83c5500d034262035100307d9003007150069100f428410741d02d003c0010b0400748101c2480007080c1500c4803001c0d090004100a95002805980c815030070030100307102c5943c0c04911018004a1079520341c0e83d641039200680d00c4089610301da43c85500000c400c109010050350030000b80c1960420081003c2c8080728204800ca03414296041160b40708141081c1d070304510246044031081c0100c00220045031399070055405e4660072910342c28115201c400800800004000e0b45030300d24014002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 421496627 1250 421495377 421495397
    0x51b0d2c0a0911091003090b07081902031e0709090b0909071419030503040e01060309051018050a051c09080309010c0606090203070815060702242205010906 69
    0x1d08003207094000c03000e4556581c890000c400303c070441120184140600407601c0318020480141c010f15010f4130070b0b66620716a40025035641d21510003e80320703003a03090007105c0d8501031003815002504000c1548140342c0c0040071080307002262041843c843d500c1030751240c0f006401c1907000c0d0140d0300280000c42c002c52051050003400d110124000d070030b03211808182e0207424420400512245003840044070540c40c0c0910100a01c4070200040040d9440c07540c400c02983d9a4000803821100d140748081c010390070041c0a8107156a03950801e00d6844106000b86140c01080d0b02d0b01030501b0307121101207803103901007170640c105609803046c64554181c03e03042085049140441d02e83d140e20910751240e0400c20881004810402941d000358041d0030a60811074036443e1884000d021040d066030108103119580021280d43d1402404441005c3c1c0d01601821740000001c114500c0904810941070703c010062010441740380c00c1f07a003243c003001c041d0302c102002d0340c0c940300000d002c0c611076400400030841c1c0d0b004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 421497877 1250 421496627 421496629
    0x50a060918020d120912060219050f1206031006080a02040507020d0c11010c0b1501021e030d0203060f0423090105070f080402120102030903070201270303051b0d2c 72
    0x400740030f42e50704a60007038860b0084c14003c4510a0650f084548802005094401030101d40c1d4050311340ca0024242c030240001060009454900400d400444211420400c0d010400c5800015a4028034080c0032100a280c0e13000440041d158260080165644003d900343d080d49000e0007016004245400500462740060400030003194240380c01404003d012010200701340d00c1000c50b00507460b00003409240e942800088441c14400002e00c1c90f00520030410f446660a10405121060f100010000c528042580ca49000a0b40006110591295984100c4551a03c1d02e00420106803035415900d4524803210070192000400030348010b5140c0c0c0b405041001140e000888464000d0003414002880d9543d0f10001385940c100c21032944595001105100c41448000094158941700342c881c90911994400308981007014800c64400b40800c501040000c03a004000520350340303105003402c1e048001c10300b044600c1c0c5158010180c0003c2c1128401c2401803101448000506131411041d115440b40c1030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 421499127 1250 421497877 421497889
    0x2030721050f010e09210c1501051e030106080a060203101d040602031f06030614010212160f06380108040222050103111008070c030e0604050301050a06091802 70
    0x1005000d0b2002c0b1401c08030307502c41c0041281c850508a030b8281c4c96180b603404808000542c004000100040c80b130708a4034030048d02040d052038141e8201400e4640130107507480d1040c001c5400021031a030507559600e80401c0000061001302c80c520700410025950342484140c035048180f6651007580c040b4400e005a103070710340181c0d402c10740180d003001c40541c0380d4560b90003d40c0f500d030008802d04102482404000340c0c041d090f4010400311a41d200b00740403807003600b600690303c5070010009903004c01070401001200c0034102d01400001d5001e410581007030b02c0300380e0b01c403000c035007481c1d030420740c3d03561904030600110b0001255644105103000034014291901d00020b4110800988021300c071b001655280668040d451400403506220003805009959590410000380011300c00d2207030081e420070416440d018040d0074980c0c040c07920382d030f580c205803000c6c1d40341103070b011034002d2103194010020040001c2c10760f006d008190048500305400201a89005464804c40e00e0342d180d410301600c0780000001c091b950744 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 421500377 1250 421499127 421499129
    0x3061302060901031812030e01020a2a05240a0c020309010324030b190b030703260a1808160b0f04091811090c0904090507080102030721050f01 63
    0x162041c6445007201401a000b510001701440301a0079241e16003006d20aa5091006004110b40c80402902540c5007000f801d0b441880c041c10081036124050b0802c2c410a2190f101c0072a00900f0148052401d0b0742d252401c0c000d401c006200000c041083d80301c07082403045000c0d604210350301804c10002e4801c500103034903800344169642c107040d80c8812030980300c640f0740802e030013182c0207851000c4001c2d10392a1150340720360180c5500e0107206005400e4604e088051003000c58511000f402000d54614640d03400b42692103680300b111046641e02220501074900038040c1c0041241501d03503000b00c00784c001d42a0280d0f1220741c006001e070342c4000713404000b000c2c07400904000c0d20381c480340341c5949150000010358140701d40e0307000c41600d502d03290022500c00a1302401140b821b1040109152a100700d07030401560a000b070714511241c0d40104100d0419180c076a0180f040588602c068071b4426079aa45107508a0f04111000d20204104100c1c420060070051084d107680c00c00c13514100414202054502d80708541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 421501627 1250 421500377 421500379
    0x403090f0303080c13050a060f170103020f0d080c0d080609130b0606070c03020a090c1215170c1f1101180303090f240f0b0f04050709081608070503061302 68
    0x907084410a0760b45c41c1140240c80090607980d40242d0301c400044c04132501e0f0000d68000b03850058401d540c54510500c050480303400824503400c0d82d0340c6c081000900e10006208880ca490b04001102445170140b01c030052140301c5e6120044a45001424070107103840003407582d00c1c403102e0402d0f1040068140c07520250030001c1502e8580c0c85091901d445e520181458101950240039030320001503800454002800c981c2c070683e2442c0b201e135030440514042c0c0d00c0408050750311048030740c1c00b80145e01c00c411022550401707007c2154150002040410f4240c2171075420307890f0429030b11075120890390b0045001d0000525140003003002c55142c142c2460000322800008003010307116092101032050703180010512513000041c810030741c010140d1040000698011060161b030030300360a40b0071041d8510070761a0145000d401d100140203000108001040010010018009001401b0404400400c10304880190242071201e0041c2011046458003410f0b0f449148203910510810112084181c10300ea001c81d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 421502877 1250 421501627 421501651
    0x2060f1b0c070b0c011107150906140403080619060212090d170a0e0f240d09030806030106050405040203190312180204110a1706030705060c060403090f030308 70
    0x201032160800588511004162144100318010078010040c50040c103109900e03c00800000301e40000348a03a900512102400400c61014000748400c2590445040e092081c0d2000507003a0007603030798a03078854003070303605800086414080050509081440b03409005103c2c2c0c00184407481c02c80000c1d42e42890600c14884400b001c1a0718039141c07a6001d0480d40f00354070000c074803000c0000144000040d049141030760002518a090b5a009091207242d80d01d85400182c4940800e0b1080407021011945004e80c582007010104076031402c1410520890030703403510a5443e04c425048c80e00030035007510a542c02551055140c1000c1c080141d90004983c440003e00d40d803500b9520405040603070301401d44242000005081415078100514404095220783c1d1088600b04100b1402400322042030090410000c0402e002f03000c1c05c45000350700800c03158030901c000c0c04c0f0b4440580b9030002c182e40f038010501b21003043c0d000d64184420150401000000b03412000482c40c8100e141d600e00524031030024100b00d500603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 421504127 1250 421502877 421502911
    0xd051e0705010b030601080a05070b040609090b1201020d09110301020405090103170d1506021c020c0415050a12200603060609030c0d0c0f05041503060b24070201090602060f 76
    0x110083d0443c110b0740e003004055850941c2c0da81400c640b52a88007100307c5490240e0100495030329030403002d0b034065032100e54446070210700b030801c0d0700c00900e01d54511552103144140c1940880d0f200340014008074110324804244440b0078a0518655503882c460184030b0b900622051001d074490049042c1165081b13245003424006900c0e407141c041c8203a011085c415030a00001d111144500882082180e4090f4201c03003440f1240303004503079011020b000501c0140c001d0045c10440349051340018a003220320800c6070300c0740741e80c40001461029499111100c10041d44905806001120040c40d054802c04425100004004000a001c0c1c1c80001c000ba0f10816003c100d114440e00d01300422201200080c18020303000c0803030b0a00140c00c05c2c0e188038070940850911000f080c54200390141c5078500c03d1003500340074028295620480600903001015070810400c07090000c910900403c4680e500310840c24a5564045d03a00004010b80700350b8100e04190362048060100b15540810f000341d100310740c05680c004003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 421505377 1250 421504127 421504133
    0xf071101140d02090906040203060d020f0a0801020c0d03060e01030c060818010507081503010603151a0a0605041d0c120a0b120c091509043008090d051e07 68
    0x8540c40792141506000c046000c1010b0480303503004200d610011210558650784400421017644000c07600a034000350b40115510050030b0482c2c50440780500146542074282d112070700c4908907001035168110325803200386c500a003203030103125076405481d890349490450340c15600c428072a4041c602c21401045100c000240a414549040a4212800100038809818641402810031100342c82c41030401c1d02c02103112485280510840b0112584942c0180145803200240f40060183c000d400540a0740481e03401c14030703591101058003401c0e498460b15110340c185182145200c191171001c150681448082c0800688600c05a43c8000303810b911691040d41c9440494001e06540e19000e0b4000ba00c4005002500c6000320380c0d405002c5064400c1406507807484680e4141110b00300050f504254500c000c58080352071000000e90f181ca02d8000e900405800198415040fa0054030113070001d143c10052000c41d56060000070a560900d00c0c4c090b007080610b10b01c0c001c02102184c8000c92000c00000c4003810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 421506627 1250 421505377 421505387
    0x605130e060303040b030f070e0f030d0e0f0a0602071805011802070507272f1b070b0d0e011a0402091914030706020d090e0408070209090f070801020f071101 69
    0x2c0c01042c07007000d8403403c001f06803502c020002d50340000031a81d101040361503820900490700322000028010010681c1111054950169000c203054202e00410305049040d200e151010006100d558010309946180011700036220b51458584411030b800e043c01040200b07204030f80c070102ca006114006035501990b00d00300c0c0c5420425401807000103240c04081e00c4011000010300303621071068109004505540b50550074040468a200c1c3d2041006401e9125402c1102c0182003181075008403d406d14442044262400c89158841040042c00003280300c0981ca05015030240d1008003c003d0100c1c0d11700504500c0c05041c00e030700c01805158003085400140da1540e0000071481541120f10910540300d4007180b119800c40f40e401d5010740316074040005d000c0d01c00604040170b00300c2c650700e11091074105441c0b24412007001d001540c0c5070b00107101c80409690307600243c90142106030002c02044c06032440740b03401c0019581c40052035074418042ea010306510b800072145055030100480c80513405003001610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 421507877 1250 421506627 421506629
    0x518101511010507080601020c2403190216060e0c0a060503071b080405120d080609070908030c010c080105100206010306050c071a06010201050f1e041721010605130e06030304 77
    0x2141d03600f00001d0003000ca40008030340d4080c14017a429540116500414004428403c03054005500c8503c03007014070210741c040195030084c1c00346902181b414801c55908060380c020210b00e1462038440800700c0100803082c41810000c0c00000f001d00356a60300c910010380215010b200d06011b200e00000042c81c007070711030b511080c1030b280c021080384000300c01c50512074207035041400784500880480300446800320300007032403480e44412903480c00811340e03881083c8008024043c0105003440414040417602c408140040c1c04000168400000c80f0700315440d00908201040e1b1240b4040c101001480c100c066000c01d456065036080344010034162a0101c4144280c07240ba0030240450080d0382d0241481460114514060b050981c000d0265480d001042c04070000b0643c1c8054080040d02500d480204512001d00da005006454840d051201c6a8865003143d0080411000310030062002c40401180c4a40c803c1c0540303c1850000e00703042c4106001c11103801107000b031b00c1c48254180300045840c1d0301007049070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 421509127 1250 421507877 421507907
    0x19080c04090c090c09030b09060108030d0b01030b0603041b05010503010b07020415080f03030709060203090607060c17090106030b01090504080a1b0f080c062a09010309050307050705181015 83
    0x204040702854000e20b175921341c0c042268060001c0c0d0105a10360000594903040e6248800a10700e4100d5201c1840003c106031141d41e4141a121a51540c40356201d402443c843c9014480c1da1500c119400600050244190001d9050010a00061103ca000c100640382a1641901c00040c443d4805521181006003503200c88441c0c85598210071070faa00210195006104030380741d140609854034402e98990250b00c0199800c41414011007021400540025842101c070782072040f04007114008940011104503950350301c983d11404200100a0b421822031300400d0306040c04c003d80c3c2400d5503050121300c10403c02c00100b0421030b210819402401070318801882c0d126000d1994010946442c440c150001c2800040c03501070400002c1c9004169654440f004000e020340600c40041d0300600010782e0480c002e010f04260340c5100442c0081d404000500965014900514030340c1d16210820002d610803402d400c040a000b5420b1107181108101030340180c40441c04c0c840d404030706813403044a280c0102c003089 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 421510377 1250 421509127 421509131
    0x31e0904090327030308190216050106181107020906120313050a12020102060103170f04030c05090c040b090108040f02031b150703050d1d060c0919080c04090c09 71
    0x400030560015604511405020903280103030b83d03924108408955a440082e01080c002000120584600140018940c0c5600c00c01410300509082c12507008807400d00455072a0340d626010b20004400c00c2070200408090308080c81680041b80042c2040d0180f0603000340a940c082011030056659401c6410710300c00c010003143d440e0b51484005c60f20100461050f24007640340b40c400841d030459a000542c3c24542c040c1c0050585901c1c50f91200180410b141c564090500e06210b5001c0f80b0008000401c011070044030054002c03401c000401c4003003000030303108030704150701008100300103159401a0703138070440c003400c0855642c0e84505126400b507000d00c04c025803600908080030101c18807000b4030007004005440c0000890b054404120343c0b441400c01c082d020403400e0104070441c3d00301e40c002403e181000018010300041c000304651400d002982c0442c000e120214031900b02d82045d010390302c0d10300040b41d0f01d5181c2e40d10304290941c541d2846c01d81240202d8540c40307080c2c140f29031008144000d081810301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 421511627 1250 421510377 421510391
    0x1050d0c05041e0e13031b0c050a0306021b030c190507050405090307210c11060c060705030f1e0609100302060a020d020c04021801081f09050115030608031e0904 71
    0x41442d48081809444c3c0000d148078082140c0401ca0000b2159040d81074a0f94155901c1205c2e81074030030842c29408594620814101080c0b984491070f44d000254861003000d82c8404d010000c00d000940c2d4030001c03690907403081c41101e4a02d00002000228203078040714a000e2000d00f4140181031110700d07080103410a0a040900250701e000000030400d9501580d005d000a016070418201c0e8400410303501c4000918900d44d26002c507003860f15034003840d04010051450000c04020305070905808851b000040756001c41040500301c01040019449407501c609046041d41004610100403406032015008070000d400080d807041c4429803542c042c5400801094581d480007030000d5841c5c80703080b4a50018051a01032020504080c02520f0505c2943c2403100004408440115013155008040c2082a0740912008010216414511000d4021442c002c00c0c2036041c0b07100d50b01c0ca2001c0c104403400b010300e460020402c0050100950b00c403e4402920721445100381d441010700750103848103003a8007500d0128 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 421512877 1250 421511627 421511669
    0xe150f07120e01230c03120c040303020f030f07030f0309050f0615151801200d080f0708010501230c030d061212050f0415020a0b0903040501050d0c0504 67
    0x1034141031680190359076509001d44400110343e113900700c454050002c0c030b51070080002048400083e0450f0303540102107a05160398542c035020041c0301030300c030300f807a11000003003e1061640c10f202141c0c070a05030800540c50300311005005000c0748901e0601408022002d400c8940d240d1081c1c1220b006240c110003100c0101d1495501103843d404180e528143c0b080144120354140e00b0070006080800744400015410103a00048080109140c0b00b07946040110360b1241e614100240c0d04208030751890748005140c0c8060058019221040213005607850704a0700b4200304030303140d001c404507054a900f86451440e0720104016031309074002807800300c1d00200001c101d4040140001024003110000b02000b0f0011564480001e6842844108080e18149010800700382c0b00c0c0c040e9000f013007016120f64529203031950350b00800321075103009081400142c00020004040c4200f41109541010015028520741850100003802c07520030800c805448948802c03a041902d0f00900585008192099803004010f12041c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 421514127 1250 421512877 421512893
    0x2010f1e0801090e0109080d0203040c03020d0b010e1b033c150d05075402090a120203031207021c0302041211040f060909020a150e150f07 61
    0x1000d03c2e09800e14002e560041644140520741040d40c000b00340918080004219502940c070040041c2c0c0d211f01000300010060300c8403404030a20f40e000b00207400255040915540081401515002c1406841d852a04400d111340c001c0b00d4002c42d1400100d481f07803401590081d131010360601d28107221080003852800300c040c1a071310b03d0f05c9150440701440410408130200150300110311400f030800c0d484540280550303049180203034428103c120408108500f221840346002c020ba001c2c0e441c88046a07246680c0040d4404120150603245180039418400c20300042008544140319191400c2c0140d20321074250340b41172040312024a4428000c00c030328070740740384040d58810541e86100c00c1c24082100c800c042c0c500c60f2090b00d0a484e0429024800c1d5940c50300c401300e6a0114901055001d5908c00c41410808040d1164000524400780b000c1020707145401005400341c20f41d44140c031400f400c0203400b184a0390044650341e80d41800ca610704015041260424580c2c02400d82205003003600007640014040c2035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 421515377 1250 421514127 421514129
    0x20040b09091011040f170721020108060d021c030315030f02030d02030a0909020309030c01060801150b03060a0b03070c1a0a060b0901080a1a0a091409030301030f02010f1e0801 77
    0x10b00303400d000040840030010030b0b034800c134429002d00d01a6407009009500b9109880404945411b0840750280e4981440502c240050340c0c01d6001050600c10307400840d40c0110645038808011901000e40103a65004600400ba40d8025098140c030103000380c504241c040d5000500002d00c1420031a001601e03484c0c24050011491016442441500750081420784008111105103556585220f6a646402c2010010b0341003c0c05101c0940000c0c049040442c2d824890980203200d218000b08160548090b0b9080301c0302990400001c958040007027003907503100e81e144041154508610340b9501c3d034481004032220302005c003004003840c860341040c08000c88103400300e6000e1030740d650703040100c0b664400380300e040d602c00c105000b03010034198000106c6152450740440d0b2594204404c03610000c41d1100022848492600001281a5070b0352141030030206035415550f016042400071440c55045460b81c60b01c3e6203611030001d0410484034890b04406100c0e85900c6c0e595071529141415442c01c000004c0e00320602 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 421516627 1250 421515377 421515403
    0x181b0309010209010e03031606150b0a08150d170d060f080604031806020c19090e071401021207060b0a0522140c0a080a110c03071b0320040b0909 64
    0x48000c0700c017585804402c41d5881c23013031242401000c15240c0e441e10081d25880b80111660207100c1000190054141d000741200d0010703a40d018214a00001c0005000d501c03c040940a40d00420f0300c400041c040b9084d54055190070703404142c56a01c0041514042c2501e504844507094440f10000380d00d00b00061458000ea00c20b0704c440400702c48881400742814028819400140e2204c80240b206090404244c1e95510b281131b10200c0c01600d46855000381c8442c00c601c0002d690080004001400e8903001214548009102a2210300f02001c40780c40e190080b0135004c3d003030a5032941038541030368034210288000d14001d0b11120b144a00c0c00720843c9000c1e01021078540881c04c3c42c03400d006903004c00400911034010108054205030b03130440103c40b10b0b00028261200300d980d501c0011414982007000c3c4c1000d0904000540e9241c40c585006401030744180391409a241941c0c17800d00014501b41c0040c1984910351f40c41c0e100082c0b0b06000030b030251039141c0c041d682000341071060041194002c21080d0322829 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 421517877 1250 421516627 421516637
    0x405041509061a03060603151e0f061206060c010906231005100e0d0b0108030a0f0f020a03030e0a151506050313020f1f020102030a0c0c02181b030901020901 69
    0x742c1e076503a450030450340b03d444a1082d0300801c0000c02da46032880c080c581001c6082c401c001c2600381c10010402c410001410380440c00b1411418094900e09184044811241591010b041c142000b5502c02002d01c0a445984514404986011155025484008483d802403c180503181012504c2004924203404510400302164009603002021281a908030385000e040070258414000040b524070f88010300c0030b40d01142c0840240d000c40c01d000380381406058004082d550310152448081c00a2100a40c10002e20080312814102d03140c022031090422901070a01207002030110003d1424511141401056184204081c0043c0314641d440444403905550a07694a1034848074207681c0c0340003c6401d184006031540c010001070601d5008034103000c0300540300c80000e11481461074501352a4508410043c0c0d8044100041240640110811a210740c10880c100507040e40200d0b0085420307062400d15044510041007140f840320012010001c0d01c4e07a10b050701d81c00c100c0e0020707002c2e40c0409040741c0052 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 421519127 1250 421517877 421517879
    0x609031b2206090b0d020a0b030709030501061701050601020706090b030a0e0d030b0a0618031407080d0c0b07030b0607030f05041206020c0105060f0108042d060c032d0b0402040504150906 82
    0x20811105e202c4100c0d40040c0700031041d40c501402d001705980010300400412210310030000003c0ca09008840c0135011407009800b130709851041084c01c440004207a2030441d40803d070f04020f0030b034124a860054406905204d960703a039445c0429000340250040301c0900e031080400143e51158140d1121100001c02c4800c4c8a01c01d41d078072800c0703400d4060800b0b0740d8170034061400104000780d03030386081c0f440d0070f1409000e0f1906660b440c03c0d5541000c000084d0003001c03540280e85802040041100c242c1c0c0060342e1700b020043d0265410200d1400e0250500080c1405004062101401d002c0c00a40700188085d2940d0300817041546040c00280d0087d0307035070203859801d20020030168580701d070051030300301c506964031481641e4580300e5800003203080390480c030b564810081d00000c17004d500040381203042c021000480c01ea0403c510040880c0d416291400d288107000b001155021b02d07214014001d00200130002c01d001c0c402000040003445180d00c069481880d14083d0048240344d6000c00301100d002c9d40e410000c007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 421520377 1250 421519127 421519129
    0x90319030c200c09100302120d09050904080f0310052206080705030c10050f122a0d0e070506030f100e15040f090624050609031b2206090b 61
    0x1070034030b0050300b005a4228040030261401d1400c4515400801106002201070303494000c5960140705025804107600080722061015030043d5090004110a60f68103030710789041c1d100c0c50200d0148011254101d03400101041152201a00382d81c040c7c04c00034950281c846100540056040c021701c440500d003407c1000000d440d640c045201402c540000c0c016020030b1b40c1c0c00d400c022801000b85d0001c01400014050351900618a90207428020105200d90850f410090400c2c400804480301024200010b154243d69215914040d034110894405010500e030702035015060800348680c200e00c0d0040400720800541b50b0b0500f07080e501400038058109112074070b84810005030a021100d0302090b500d0190100325504140e4000079481c048840c0c00101488590384500c1501c048060301700341401c043c42140e001d04c001201e95401030104580d001e14103d810804a500d6404802c03148259107070511442c481c1e40c4604442039420302501c0514a00700921116020040000d4020721403400c0c80d0070b02030038807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 421521627 1250 421520377 421520417
    0xf06061b0c060503092802040b04090f060513021503180d141c05040309060905270606070b070c030f080624040510020309150702060d0203090319030c 66
    0x1015001411a00304034245030050b10542c1c0045c2440b660362050055184210038130045100203502d08000320f480d2220307580100301c280d6014500d2148128038000480c07000945081e000d88034554031500210b0186c0d120600e5108107200c00c100a50000c1440b5090519140c00d4401540304018108844e401481290301c4940e9813000c0480074008124403030f1038030001a007810050001080c5e521800600412002c3e5003605460003a1170480104140090030300c401600304a00e00090041907800914043c1040300da1056800701c2d548542550305550b002c50001c0d10b4103021101e4158001d004401c1307604008200500842c124402680060b4805c14a0080c41c1d00c610700f0180a100020158a4a1102e8143d240e6810101612407501c0202c104800516074545820344001212075402841e11001e1075402d00024081103c00641c224500b01707c07406c010307070f511701c113841d18089007200058803903a6001c40249103128007042c0c18640706584103d916060303459000780518a8207035884400c410441e01074400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 421522877 1250 421521627 421521677
    0x15050609040b091c02030c06070203190c0f020402071a0604020307050f2208010c091212050c030f1204021305060f010c11040c020f071202130b040b040f0606 69
    0x5400603100e008100480e040303506a54028800c80c003610360540c22514041010700c1d1515982e00941c0002c1807002d074411060010940c000e046002461910100000c60500007040d04804400c0c004401601400c1c4440407410541060303003d441190717980d03504c2c201030070100c041c0740422120b0b606020004020307080c030b4000d0380d005031000d807621030070942c580d440d00105401240041030120f14240c240c0401002e15580c0320003c104a000000b41d0032000e020081c0145400d0f0401891070440c0c999000024040b0800745442740210300d081926060048040d81c11842440f40c4501429804619856403100781624140210320031600d654a0201102e18207058507000c03285aa488034800c000a0f50950107252407848481c496134285510b000000c0001e41110000004800180e02c0090380d0303200f044041100030050310700140881d41c00702c0c0550000b424180c0908c0481c0290780ca0b0214008161102c1c0c01503104508010002c3c00b88155000c85000244028490100001c00007002c110031fa40c0d012550b10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 421524127 1250 421522877 421522879
    0x70b0a062903130f050703140f010e03040b0c19061a0405131203060305031315050c120d0204090921030b130506180f010303080a060b0d0b0402130f03150506 69
    0x50070740d40d44401c5981c814002d07183c140c81c040044003240d400500e09124440107184110790003004003003c622071616290a0006d2550346d07030b1404101541c0c406001082d90100d521036200c040d80c84000c00405410003c0d03407441d809910705078a5900c000c201e51030700241c240400807007604810141110400c401d849050300c2d03100d441e0040c0c2c170a01c0042044205404980c0035682008140717075603655a074a141d50f01440f40d1818250031002e05020402c0d8021600c4e10020030340c1750081c04c0072a0081003603140c0200038004100000d001442449583c50b903010303a070041c108008108820222410104051041e492840100000c0e1482200c0454001c1c407071421201005450030410440180c031030b074020070b8003909065105517401c2201c0c240344044208184600b5110704e884910794034628001c1d0014202074482a0954101002402901010b005030740709400e05480200725010700d20085402031203280300c8401640d05090300407078510201c0c1d4481c400c4a101d05290380071f0b40c0304842180102c500030f645032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 421525377 1250 421524127 421524209
    0xe03060103030c02100f0c0f02040b0303070b0405060105150307030b030c210d0203270d0605040507060f02010b0f091b0a031e0e250f090501031203060501081605070b0a06 75
    0x11f40003282040810f8517032103202500002d101400c14000031300d0340c2c200c004216044002141080304103c401d02c2001d004010550750241003c01a40031150030340002801d050406179508000d06499401700714101060fa40a408801d820b07a240d0030003802881801c048c41024070400d590040320520004c203d80b01c03084403401042001c118052505549900307181e4041c0e011102d581140d01207074880c0b05a50050384100001e05040c0d203404401f8001600b91061003096901d010402901c1d620f40600e000ba58007003c07030b103986050b07541c1e01030000c9e80c41041502c000c03001d0010a5041c11150940d0040d040c8c44010007101d480419910440c4050b14442e216540c00c45d001008005031070113948003920201c441d0350080c9480551681c0a0b81356000e4681e00c200c2c1019103130001041403180045542050342014a01801406d0800001034124200600408443c400c005030014483d4421402e8401d01a031011801e0000c1c03c152040c3c0b0054105401482c2c4c60314200c3c4046505081d88062100d4040e12203050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 421526627 1250 421525377 421525397
    0x6040515091b040506030c12070201020901120c0c0f060e1603050a06020c070915030b01050111070e070c080d06260d08070507020414150d081602010e03060103030c02100f 75
    0x11950310345111841401180b8002d000210740fa0395114043d40c800c20b40e0845058680c180c900d600307101110b02806007001e591040041c07510690340528095031440c108200441c6040003641c00711842110040041d0011508401040c20010160071a0700208403100840b04407201041807800c4038070b1a880018034660007501c2420004409030046c021441088040c0c0705a5561241600d0036500082d40036800300f090351300140100414160740c0e5015003820320b003a800c4012400901c07646c0e603010303002e1146032110100016a074540b041c0040048a03a001d110944c6811940800c0405000140141120340b03090f0442221519842c4e02483c20500000d002070031502070f20513064421510140a090420400700024405a00c071030003141c0c004040d031440000395141c50300d0131a602c507130389004c054441da00c44400342000c502040b00f524204148101c01c03c009110703070720041e40d13a00c4a007030425400d8011800000240b5802406007000c10b402650384801c03031301d41d0440031210305080c0383c210382c085096010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 421527877 1250 421526627 421526641
    0xd061d07150c20091003060c09033903051011070b0f1330020c01020735030712030b01080106181a0408070504050721020f040e0604051509 61
    0x44402c00c45000d01203283e124420301c001ca400910111a50b84410900203000c00c200038162254152102c1d0314900f18400f142035540300c01021034462011200c2c42c0403c0c0e802c1701c0548900b80006c0070715a1021245c1c0100c2c0c0c0c0d07443c0a64407070100d140d070314400d20b203060389080060040c02c04503543c043d400102a09150380e000c00e68078001c54083c008407140d00d102c000090000311a01c60b1401100c05440c22104003200c924110700c9a071000c1c20041045410002c55031080da60001030300025900d030543c04140080798030009524452030302c100030403544a415001140351401000420145000c0e4070a440c407a181c2c0281a42502c4c0500100e42c00030303141600402035035108030340400c3c00306401070011080640c3c1e01d0142c203111540e030080c5014210001000c201d0702e2070401003000203050170341d01884140b502c1c01e0050300026101052080450034030720001141c2d40b05604859802c243c21148503141c42d223600f0500705030a0103c070220300852500d0007250761700e15801060034446d03000410041c1507a40e030304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 421529127 1250 421527877 421527893
    0xf120807171207050c0105060d0203062208210a05041509050a150608070e040804060806010908070e04021c0506190209120a0b100f03020f0d061d07150c 67
    0x22003036000d0000c14060422003202c0c511010f401880182d49480e03c0340c40b0803017400e084810203050148259100595940140c5010075101e0384050001c072910b10211500b03101d8040100c200300c004059a00021f1600100442c0e40c484103400d0804101a0380c1640c0c80040100880d60166005410b4000005030816001e00380d80080c26001e11030400e035070f011245039480c80400882e54030640d0701039440b0682400241010880b00d4001c0044059841c0982040c2d1540540d521980c019a820404410b00040c507990041c1c098500900d546030440784c001e07940340b18400000e40151400c82c86401c00310980030008034a800c052000f0750b009405001c254903144a55540c940549004205060b0280b01998082d078514060300582507048001e06a2050b1518040c404a400181002414000304200f402402641003224043e240c0c190345201076a02108001105400420801008542040000c100c1c11003c106001042601401110354070780e00c86a40c1c012443c0880a2280014045a22640810b03085 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 421530377 1250 421529127 421529153
    0x1906090305071a0402091506040302120c030607030509011112190f14010312030203090d050706020f1b0708071a09040902090103290c0405010f090b03010603060f120807 74
    0x641001c925101c210740e034142c071212442ca00811115444000c100550a107103006661200c1c000380a007131341512400000b42103000e0f0f8000a402001d456007a007070000c0040029815940005084641c030703181461004001d041c085070403198a50034980301070001040c000030340c1c100070140c0f580c0c417802d03580d510311040c0d030151080515000b0507152907a410048090b48100c2c5100301d050032072080d031036045041141482c40816900010940f0420403c030410f140420800d4100e029890510764550b010300b0444042d008007003085e1100c200005a039040c01c440d034030150454031004002d40d09aa0750307030544075488020910891507240029401c445014000000030110441c00a200295401c2d441e00801c40b40d03d003d0b0801c680003c41e41e0450003004219411f4039455620a0326880b82c00d14050420140078007580c46014184034141d1003404a0303c0c011048107004e0a0301040390b0380c4070340e99070360300034007030312041c484e00780c80380035441c00402c0717201140212281d0310790402c1605107040c802d556410800005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 421531627 1250 421530377 421530383
    0xd02060d0c021e0129030d050a0e031614190501180902030a0501230f0f0315090d170c030412140703030b15031501050d1103010b040303020f190609 65
    0x40012500305058410510300400c1400f40000440c0018207600c001592018452010100c0c2c010085e019150b80000320707500042d44520304903803503903a0590700340c9035454541c14060303150140300e016044502080070030300c08940300161903804002e015010b01410180a1080c8020b89402540034061075020700440c0316841c84003440c1a90355595009200d0480c2c1007555001030351600c07000104008001480108405801c0d91491a1888140b0002610036110304150b02d016041220b24080310307035414040c11180000512221001d4508418101e44500e920100140070400c4c0448440e50820426043380c4070300d070711003000c51035910b558483c1ca508248040d009000c114112495924a1a001d4042c2c06081d100b500c01040516002c0304100d0130b070300041000c4025400500801c000c07a412900b0305800c0001c28280b81c2e41c2e66038810216005407002d800b060194101c0080002201d0000d0001441240c0c0a607080c0c1780c20489030f201d80da407251444054501403d4014142001050055002080343c80c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 421532877 1250 421531627 421531633
    0xb1312030b06070209040c0608010503070b04030b040804080d120c050c152d09101107020906061918060809030307050a05040e0702030d051005060409020d0204030803240d02060d0c02 80
    0x910380c0011703000c04007264211281a0248005c0280e1504400031328003400b802ca01900d045170411841800c90700442c0700282c0f4144405c0040b80500003a2400c603006412668182c03540c5601070040944040700e003030010b48549181a2460080c10310980a8501c00c1009402501384900201d0046100c548003503c11080c0c0202051301c1030f843c00c08860b843d022403020f060000704500e071005810b420500503c180c6003100c0c0c2410316110b055008041103c0d4400d90468910400362101c4c1d0100380c5c20f01401a29808025200021520181e08540300c3c410050389840703018240c9448810440d40c490054805040c0c56106102040525000c3d8002c0d0814569918260b801c040e50f030f21000e01550803d80d07040000d0303040010300410300c03001c1e0f000e910350080c88181300c5c0c003166180c00c001c1043d0344518429240c40342c2d030204913030030031046c3e5804840066801c004410303201d0030804540d0500d6680748160542070210410122218240011880c0005400902e160300b4000c1c4c99403001c0c0030300300700103080741140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 421534127 1250 421532877 421532887
    0x100b07060e01061212080f0a050a09020604120b0112030503061e1917070e06010e0619200105010509180f0a0c060207060806061e040e0a090b1312030b06 67
    0x4024801c10005000021100713415480604169040b01c08404180040003215020006074035034031000950400b0940c00000380f50350b1103081c40320050100846c003d500040001d000030306400d02100c0d810f20705015415042035a42c0e1683c1c502000c441e50303c80140803c0d01880050710b1890895940c03840d032800140c2050241141e580081c0010a099139070080c0030000c040709000d061094002c040030790075410002c0070403500340040c41d4160342e0000c0c201410880645084500ca45030401074400c2d61186004101c1002c000e240f000e00410603089820384071b1031000880440d2084140160f90407940050000c0c81d084d201c1ea43c0d134500c540f131481b40c3c11400c0d104680e03401c060b00c40104040301d15a80640e0803e51158103258000707090024507408802040150800c2c8105131b5034103011541184200e003504214000c0302d040c0300340c4900441d408920403030b003a40101300782e809107500801c034258424485200e042e0748442868200d08031550000d08440d641c00c20480021b402517000180040000301024144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 421535377 1250 421534127 421534151
    0xb1518040807030e01020d0903110a170318150304020411070b040b06040b0109080309090a06080f0705011202043f061b1b060506010528021005100b0706 67
    0x11201035608440039074002030342605041c1d01c01100c6442030004d00c0036140317290091078010300c802c400d404082d00f103041c02e00c401419503861004460050580c09154070201c2d000c4840d40b5121b4200d080214071503511501000c0041c6480da5030320b441d900c2900a55411621503400744001880c48908001400170f003005150081400840303c10701c2580709000583c20751030704d0700501055440e00321401c0e0610580038401e1140040204c1501c141e604141d80c42080380d990010ba000242c41d80c0c0d8031002441c05080015045854085018004d98030b00f03880f20b00caa00f01d000c40c04800c07803081d485030400c00110240108a00c5005150b48111000340000b20784507094400c0702e200e00a0801c0c40d044501e01d03a6440520601c442016129500c0c000e1410b1070030350491442035041840031071842c02030030680e030b070000501568010304c1540c50718544043c0000c0540181c0442c501c004007503038007101c051310a0000e42c00340400c15004851140000303141d800540d80c905104c40da01600800811a021501e51800d0101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 421536627 1250 421535377 421535419
    0xe151506030f04020a09110d02071a0708010906150f051315030e06090304080d0c05010e030d05040521091302040b0d05040308071e080403020307050604200d0b15 71
    0x8441d0394202c1c0500d0705142c810040f0280355a801070801310b00f002d0860103a070f0400030580d06a030011050259917040c4c41c3c50075100110759001c4c0c4400000d010801d10450513400140d05041c1d5100d4a01001140e444403120202c0b81c4044c0c581900144400d0502e4030301c2032180000d032202c1d070b241c0c02d1221203040d2103036a25501446c072060b146002036560041d2a000784001c200c00c50700141824059884c01d070401c40050b0f01c0e009a4101041840110300066040220940c8084440c030036900c203503a00c80c856007403204040c1406440654072442522118245c2c2c1410044042e103054407108501d103400369010a12040031041040803542070b609100000354240c0040050400a5050900041d0307031600d0b107000790010901030000c1c4100900c04000001540710040f51207481070f010709051141d907545207400c034030318031400c8002400f034014502403004000794060025620000003a251003110109130901c28444070503400a814056080d01042000c3d841400d81c0001d45000b9180340c41d4a1044103030302013 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 421537877 1250 421536627 421536631
    0x30a0b03150f041e15020306040c0309080a0c080705010e06060a05010f1e050408100209010908120306061810081008030f040e0a09080c0d031515030b03010b040903020a1202010e15150603 82
    0xb046a0b0004100701c42854107101d2b0724020081d1f400d08029418880e00d4410f028000d0100e41014086500c07041c00c02e001d00c81c0e040d02d1175140c3c442c0c001d0155000d800741d09a00e4003020703182c0500403050b9501c049059800742102518031441d03503841803044101000300d55403030b1060b010028140041048080b680500c2880710506055080c08050707038411100000410841040d4402c00031504040414050710044004907508420102c41e0a9101c2101e0500a0f00d1079541e81c19096002203000060a501904022003500c00d50703900b118075610035900d1544030b480340300d00c4031413103000c200c03c10061260181841c2002d0700f00005140004900e4a699103208080d1b10000046415078489400301002c150315020390340ea000c0601c1a00c007401445d0058400300c1c56000c800a80174582c0781d8203500c41544007580801c228850091090040b10260f0401035240c1c40428001d0b501ea81040c81c45504483c014040c2e1403c5400e00340041c01e214044840000e03c150740034001d40407a04a4100001e030586e0780c41c004d54 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 421539127 1250 421537877 421537913
    0x905180603060a050601021f110301470310151d0d120e220b15070804030b090c1e0102100908031302040f02030a0b03150f041e 56
    0x21445040c1902014a0240024a1500d08504240800099036404902010540d952816495482400700d400101401500d0181480701c2030101c000100e050082207a000003c60b00001c1d40e90540102481e90b010305964101c1d01c1c40f200d2010f20900300e01032410010f6900c034840c40900621591600c00a00d028500312825800050070300007190f00c00c602c101401c0031644021a40264a040d460f5104034000c102110384809000c00407090004d00d858405c01100081c0110340e401d01003c0031b400c40c0d400241540d4034424011180c41490302d00600408048800d01c0f600316000506080c074641c0d80d90000100200000018007802c00388029a8448058104c2414007109441c40040ea200000920b00280b8504118646042a03e05004900024100ca402c2108502000c1003204c181c0040f40150118500b00040300f0720020400c580c1190380c3c0c0c40000244030490a1300d101c030100700c840030003420080c0c2ea40c1003500e659001150000305d036601c040c10107101d2022050400c28250b00d5001154080503011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 421540377 1250 421539127 421539169
    0xf020318060702071206020309011b110d02011505100c050d120b01020a0210050a021e07030b130c1203030b0303030906070207050a1d0405010b030706020c0438010905 73
    0xe00080035051100c20761155180c0300070b1048524255040040701104000a00559030001c00303d092001e02703401500c0e0184202141002001c3d07807079002088036200450b49001c50290800403240d591040c0200c91541e42d906100d515080e050004110764400f00800a100303001550b00901c1c0001c0003404404405c1c0b03085c0d110080150000b003500010f81b00e000d92424115006144031000503500c103290104562541e2a046489468607c02649030401d03820004110380003643c2241da58020000312107003500d08c14103c1242c6030300d81c0150040c80ca641040002d01808100e401406802c10081808038514043d00e000b040340c18030780000c03c2c190380c01a6140f003904d4211108001c2d840380c0400540000b05016a006180385213881140090421428240c0c5485000040490309001094110014019004042c0c0c1e42e8260f8030440a0b550321012040035004d2403d0a030550302e821186441c10800c0c2d045074440148152040f21b10541c2425014902810b200e000c80d00031503191200c0101c06105a035007000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 421541627 1250 421540377 421540411
    0xf010e07260a0507031b12051b0123031f061e0c08030f070215131e06060f24120c12060b0714160513450506010506070203010f0203 58
    0x161b44104150000e00320041102210b0000503000603440f0b580c2e00801002080441c07034080100d508094082c40791314400e0603100b5035642010082e0055010747c41100410b400c8c0c81080284182c00602481802d000ca0050503103100c1d20500c1003944800340700c0614241140c412190782d03a41c40c2d5001a82d0200300404031030104140303103070100099070713421a00c29004d210301d1402039001c2c0001141950010801c1d0302c01c0924691080715002d105078003503400300301841a40d484051661700718001c0e109019010003a600c50704100f00c07004004250a01d0242d41d4483d0020704840c0d882d0281c200014500308124503510454581c2d00a0311500d0082c12200c030600b55078100034144051415004034254441c8d400a4802c0114200160700034400c80b1803e9458080314850b80040780001c04125000a5512000070700043d445c0c4002002c4200800c0110b8142e803051a21309a80c00141560280040050b0300850061240d49041805000424401800401d50000003070701d04003660002d41f54840c00c6a85044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 421542877 1250 421541627 421541663
    0xc0a0311010c1d0f0a180b100906090603050c0702100503061504080a03111e010b0108010e1501110c0a0f05091303080408090604080105090f010e07260a050703 70
    0x4290140103503250500503611056030210f0a00c21440289100b154507900d5802c440d103803d48410001c205500c2e4103008215a9851280030f8414105400e20416009001c0c09000b030158041505890031951128011418000180c00401001d01005100042880fa60006a03200c0d1241d8100049036954a078a03420504180301c01c48100401f4114070100c180014407082e03000041c59003810750540340a00440740f074000191b00300b100c90b085850300006101e0100c008020b054100c0110b44100382d036181c02c540c1ea00c0e8111103c0e044141c1700c41c17400c0c80e1341c0c6a42d4442980304604042e00304200400799031003080c201000402400056100c0321510046d4482040310b4a0250034041d400016401188030f410300039680103001e084010401000d00c40f011420f103800c4e840722002d807000350000e0344c006c0002d4280035030007e0350f4000c002104140c560030050440c0b1440070216404003120002241559000700503141d080b942d14198680e85403e00c508900e00700442c004020100085005221032703010302c04898 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 421544127 1250 421542877 421542881
    0x3090a03020120070206031e0112051e0d030b010e0a060e090705161502040b03010e180304081203040203100c050a0f05030f06060714010f0c03140105090106140c0a031101 75
    0x985403055a031a484000010f8182c40740c1295142581100d1081d526581c050503902203140882c2c00c810200c00c00d800108031b02c49001000b003c214010003c41d0b103010200f561180309015080c000d515103410890741810454003a40140c0f241c404141051030310b190049000c54009036940d44404c2c00039400b41001a00c40c1420b0f1806d0703400a0052401c24030f0155440d8420050703000b5480000c02a020f19003080b022802d030382c3e040e50050300c03664181a6036969502140082d09100313880c4940d1a40d42140310003066040002218125540400901500602001c0d048c280340c2000b002603801d80a05118074006658510030200c01007001d03100c0c940c95108030200140080381100c0e946060100800611490b0302c0c865a01e079a001c00c2c1207440a07035a2071640b614a20206054025840c0b641c28008441ca045449401100c4040ba881d82c08000e05180704440c0c0078094000c0c401d46800910b03542c0140b005510500041c60591800742d400762502604400b114a405072a180036800510024240c001554081c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 421545377 1250 421544127 421544141
    0x4050601020a06050702011d06010308030414070f060507051b0307051c0203010903090810020403081c0209100e0f030106030807020103050903120f0709080303161d09010e0f10030f1e0803090a030201 87
    0x304014108ad40c10b641c0c42a01c13a1102803c05040160082c042c80d01141c000c0203240301400307090b020556102c3e984e0102030b0158100503801c4819005000038848203400702d1341640031242004005018a0345014240000200300b545e5030038042044000d9440580c03424050800154030980e11903046d2441c04443c0c0741040d00840c10300b62650700400c01040880c0c40d500989500180e000c03074455800b20240c08050007446600310958200b2080303181500000e401c80f050080c4000240c031b80070081d00590b001c040c200e91150200500101c81440701c0713409544a9440300d5800014501180c0c41c080b48914182a1010b0031a03d25042031003403010445002da004482100802180008601714240280d1104805402c1d1003d94100902c1c081020404440d8240180300c00c20045c4c00301016503101d0b13040c0c88840804070b5400c200c2c12480d001003424440303984040c00460740c00010381d9070041035a03900c5410f506800f01c1016112009030310000d0218001200031402080260000c0551000c0c925019080d01d01d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 421546627 1250 421545377 421545431
    0x30903060c0313022b0303141806040f1412031b0703081504110a030b03010c02030702101202120108060612070605040e04050111031905060a06090504050601020a0605070201 76
    0x10920501602021000d840c043c16541150208000c2c03003400380d01001a103030b004401d042201c0f681780708411325400d0390000480740b00300002155a0303690914410460450702d0600c2699501410004011503210402c91004070310400d403054121905500040c5000814200034462290000c144200c1003004121a50000c0c413180070603003001b402c6c0c0c60281903004014030b2000d4000380200c940c1c886075500d07440241071305000c9644c552113031031404005000f810b413100c0190080d0300e0b21405080050001045d87c180641c010b26102a020022a00315187c10343c07024400220341c0c013071115008410119280030b028103d00d0005000a1928800304800044d400032441700302e4210013818400594044115000e84d41c840b00300102c1d980f102d180c401e0050111423628440c80310b0210600a08000c009070300c51000c007455900b0f001d5611030102f081003043d000c0c032804022800d13450013082103040581019901000500580300d5080301c0d0344446055071070031259140103035034070311450402d0740c4034400ca4420040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 421547877 1250 421546627 421546651
    0x10050c010501050a120308060d0b16121a01050f070203031c05100806010b0c07230a0602060702100f0f0f061e050d02093d060e21010209040e03090306 66
    0x3180002c17850072521443c0c000740c10089000700040d140d885211610803e581d21035001c00303440c9000100319490402441d21800000e80c0c0c0440d244420b24580100c110201002c024103a003080c000c0015075155001c0c0100d0741c3c0340c21090100402580c1d0a201401480880462584069124040c40411100000d000d5090901e24176401e120294000903e1810350354038001c05a6034610b0501c49500d0461258081c0c001c00c9282d80307030700000346240310407801d011400380c1c1e640c00000c0c1c44440c03c3c1e8403400e04484082c0140c1c414100b10b211000705070810001005200400036112078a0108201a6040c8202000c0c1c0991aa50b0802c9000e640581411001a0130003144154034103000000380c52002000e0040d10501c1c0d07950208030000700740b00051507081c4e1800c030280005412100c0441c1d00300031424a51044d4000c141c000101a4001c2d040804641001030884022007038000c20404400010564808a59401c0c400300203180c503a0710420003400c003090021502c03a0280c008041c6400c00081268541c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 421549127 1250 421547877 421547879
    0x80118021e0904020405040501090204090c0813030e0d080324040b03070302060f040f060e010306380408030c0a02030105070207030305030a05070210050a0209040b010f141810050c010501050a 84
    0x816100c94642000d0a103030001c030798885407840010040c1c05950056a400792403c0000a15601103074010012074030700c06030520071000700d80d1007540c01e0101250240d0020780c0e086000e00000f44982c20480b0301c1d03400282000c19601c44c03505d0b011581c3e0000c841c090301d0340044020800c120301e80101c000319a0501281c0c10b200310000000442e1310345410703110003406000302142c104040c90601c025200542450141150a5a9619801402d84021020a900bc2450003034041074a4005a64268071560400003038110b854003805c0c1401c0410745442c400c5078001090001181a410070300081080c0c200560041441031003a00402d421104042e0108056603c015402c00000781c100d407e0300d900850002000420795188031040c2d0030801002c021100081c13811080010528484e03016200700401610b00300881d469110040d11284c40840001c40803410010a03010a804400014112100380000340c4210030903e002003031151041914400104d20081481c142d13070712003446076030b0050074115076064140d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 421550377 1250 421549127 421549147
    0x601090e1b03040515040c0906050301110702100e0415080622080703091a120702012903012a021605060406142a0c010804110d020a08010c08011802 65
    0x4020070501050399104003000060030300005024003c41003e02220756089458070303280001e1000e4041c0a1081b40611700b030300103c0c150805100c1d1070600381d001256545080042c0d02000095581150b007881084050415607480d61500d00501c0540d80009410f80030707041c10100c04070b0030311710020814613502c0a4804420007110801c9a0aa01035410032030041d944d402c079041c121145030f103a41101181a8254035800100310030140200901c4502c01c1840300c560722402001c03170a9071000300040c000002502030150480a940700001103a030030090002400e921500c0e015140c0a9400528001914030040da203980c081d018481306007010010900c550802e402c00c030005055002c0c0c0d000d10400c20808940382e03c9c00d8416a0221911071a0030640d106400d504400a62800c2c002142c0c50f0800e4020f01001d5401540202b00c0300c0d0043d5072004490b0203180c4c0900c140003c44040c0101aa8010030704003001a40d294284600102802c05a40724541981400d00d40c0a0318182051034618145c41080102e43c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 421551627 1250 421550377 421550401
    0x60918050712020d05010c0903060b121e01020d050901052e0603090c0509092b08040602070201030207120f02150408030a0b0105041d0907060305060a0e07031104030303050601090e 79
    0x650b511200544040000c0b800444c40134400340200400541c6048468201e4941000ca0f0000300c0303104a1341481f02d4100c1c4006e111549210100c440c22690203110305040d000c941c4001c21403003200d10301c001810006140c140b0401d40d4030941d404503072a5550410301c500402203c4145886a10728014010761810120391002507440600c245c01c20142d41d20041c0d001c0144a4030404010a80102241c5960520300d6006444507482080245250300c000141d8215a2aa91900d04140c0c2d040c1c0390a01541c0d1140c039a807010b9409028101d041540c00c000380c00005104114020b0f400c04aa07981503d24500080040e01d4181d0001d89500130003001001c010016000c50b0481381d004540c100045281c1000600580b00c2d805107800c10f8030322200440e90482c0b00700e00e8104161040c1c40e03003c100c5141d1a076803c0140d040b00d001b529110b80002d0402000e001d00d48110000542200071480c00045c850b9802c0205003554001d90401c600007922102407020a40e032002d0460041e1502d003448a6403170404bc0400344c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 421552877 1250 421551627 421551629
    0x90902060417010213030503030628030807051207030503010e0a09110f0102011d1b10050909130c03200117060d080c030301030c21080a0e0607050106090609180507 72
    0x144202162081080d08801c1d01628641c01d40080da845c0c00f0380e260320f001d94880d0402c40761540101d000f902110f022134642c03ca220540607107607111842c4030b070841c2c9a0025a500148094909110b0500c5490880811400030109140a070b9110317078807941050580003121402510306403910b81480c040a0224110051a81c000d11049038054201c100100c0140d000d0003d101031440c1360314402c01c07081a880b00c0865000b6102101d40328000d4226104c1041115404540c111580015014003410107117080c88540c068003d483c8000340301a80e0040d5862020080003034208840000d1100704107010b101515400074452603090070191011444050100c1e6080c6000748070b9032040320318074800303024026140e04481c0610000340540f5601c0d070310303420000c2801480b0b21440443d40d01c2d00e140465800b03403d03643d500056600c0b01800b881c0890f011003c80b040a03985814a92141b01004480000f13902481004001c0404890114480e450100f5400c1210b244107410310707a01e0b5040b40c00000040020680070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 421554127 1250 421552877 421552889
    0x60302070204150603050603010b12060a051801050702030904051e040602091201020d091226060109080a030e0f0f060304080c120c06010e100806070305180d03150909020604 76
    0x1600d030309140c000100584104440700d50300d070322003e8010914960682145126100c150001e219003d00e01040c002c40003400c0c2c4441c400f5811800100c2d40c02400d41d0001600304000c141c0c48410404202d064a08540040c0d801ca00582e1000505502a0609015099000b4855a4201d1206014600780d150800c0002d0009086690001c0c0324401552501c441c90711000c1610000c41d01c580c080c078180c2c801840e00d01c4003614080032591b0b413000340a1082117a20300c0c4500003c015003800181500035011a000074108d1410b0140742000494400c030300700300300b0500c180a41d403031480e0200e100c424007003803412201005006074002e100e100982d4403294110394005a100d0148c42d0307204240500c1c54101003107242c40c1200b5940c001342004c46d0440010f03042b0306036000365940503141e03140c8030741c5241120b83d18410f01c0c80769040b420001e081c0b24000d80c00a90b211040802c0c1c1305800c8074403001e041c240095000041c0100c1d94450440d0344a003807100c81072005e490440c904103c0104c3d40d03000070303025005500c106 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 421555377 1250 421554127 421554131
    0x40303170c07230109150e06060d120e1f031109010e0904081605060106020105070804020d12180f1a12010e130b0f0103030e030c0108011203021203010b0408120705070603 75
    0x1c00c080f203010300d4104260300090307000300310019003480c20311002401c440488400c2d5050294120903450302048a60054600030059580b2400c1940d034820583c0092071004244880030440300065110f12100402001203455880c04c8840b003150040c0c00c85440d0031140e800040309200e0021543d030840398590381c920045a00101a45e210705c3c8c2014140b140010150201c0348210605003001030014034181a02c2583c1c00900555660f9002225102000c4802070f610404460500340070403641044a0a041e9487c6040003c200007007003d02100140d0303030700ca1450601500b10403c00b604070303074042d0340c50507460981070303490401c80d4000f41c485504103015001e800c201c598041040680c2c80242c600d02c1d55440007a241c410b20b006990401e02400074442034002c0b4010300f62601a618000c5140c0743c203070205031288105a4207006078003541d04e1407032400301c2c10344c45900e454005104550001d12b000300030f9188a155290308020481d1b062071040b0741545200ea03418001d00c1c00180b0080f54413400e0798094540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 421556627 1250 421555377 421555403
    0x2070f05011202040f1512110405060703030906050c041e032a030f0510050a0203040b0408090f1309140f0c10140304060f110c03030a0203040c0812040303170c07 71
    0x10b100c00070321943e40075100c000c014000000e100328161214080c051400e403100c400074200341c801e403002e8564040c40003040110821080c013003403410401500b000da020b403074001048241661001c5c2160fa00742c516900702040030404009107007515802c04d07183d580c2100c5142c41107145943c0e5040b0b0a4010b06040da0203412107541610040d07126201100075508980d510500304c3e02c0c3d003855611540050075092816052400090b001d240c00e00880b806180c3c0454040681d685640f00c40400b0740281c2085640803209503900340c5a40c7d4ae40c0e403498040612194009440922032409404124490f4120301071908198485400102d000c81c290107022010380703140c04c8031011548101c502802243c1d204014840101c1448280022503010416052044004105040d141c1d15440c80a0143d04000031140e401003001410031515a00030f1500300b84194000d1400320340324002d450a004a11402c0010240c0106041044c9540701c0003d54030a41c040102c4002802ccc842000a203a201c1d400001d048442c424603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 421557877 1250 421556627 421556657
    0x105070314090118090203090105010b03010605120718090b030d1e0807020309040f0f05060307050a0302040902121c0e0d030f05130801050703020c100b01050901110a0602030f0a0c02070f0501 84
    0xb030034001002c0c4c0303403c01070003a81c40c0d09800009400554015040b90300e04400440c0d00d8040504881c181c1d09151100350a260b081c0c03e4101c40b0002c001c2c041410070103422280a480342e40744180f41c010340401c4502040ca04642c105052404060005090400c44c903421110020b410000b14844075074064541081142d403018030582c1765100341125583c01914010071401c0004c4c0c0b07980203850504503442e041c0115120081010b5a5021900480b40d10512498082005180980c440c88101c2d2026190681d4420500c8109042c41e030020072180c09002100c0d074158a00382c0c4165694080241122040618003194038018030010301130000c41d0074000c001a030f54845042c141801001010644001e020915100900070083e40140c080e13140a88207031020b42400303c1aa029284e84180c06940b02c1c0d0400c00a070004540d15400c80100c0a094000d500c0c030000070a42a0006503c2600b9110301d086550a064010000700c602c060620421500704005c14404200300b502d00008503402441c0405000103000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 421559127 1250 421557877 421557887
    0x10f060b2205030d05040503150103030f05091c24140103062c0f07050109140d0c1a1c15060e01020f01091103010608030a12020a1106040c030c0501050703140901 71
    0x2c0c02440d41885210110301e01c4661060007002a12400d4040c0c40e00c40c0941c48260100c0503084c0401408602a104000341462080000d450101d80040c0899000000078401801d9143ca0743d00c25030702120444070f10f07110001242c0c007410911a48000804c07030030100d80d01004810f00180401030050740c40d4525080100464542211541581301d1101c030030702480d81650b40d8494403006001e6075402030381000036156015207420710441d03007090714071a01c00b04c41400b00245111a0b0004554240d407089000c43e064840030a2580310701c0102d00d10303581d21100384042241c04444200c02007142810540c0600c0a0841e605010045800c107040262048000000607410017004131100c85107036181925110a2100601c2c3c40700b1f080605800812a070707a115110151280b15600c0c2d03078800f095400107a0b407071001d0294014494001e140c40c048041c105100401828440195420755070400703141001d04c20701c103100d00c81700020a000d0924501d06449650b0140c0b0040324400010640e1304080742042199000b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 421560377 1250 421559127 421559129
    0x20090f0d0b0a050106020105070e03030d0b0102071503020909130f030c03050c0f15070309021813120201050901110405010e060918010602060f0609011d0403030b091008010f060b22 79
    0x3000544541e460828a07081c000c09091003050010340c02d04002c5200300d40506421074001c03002a01943c5890f50300c0400b940030303040100600d4118802c01500040300d42c8039182401e41c100d000d40d405a507540740d980411811031005041006182190540c203400540c241c3e0304941c0043d898107120b001840303030b41005d440c03034025194043d440f401480a00441f141c00418009036580095242042980f00c1e480120100c541020f002504243c08600320070401101052169004650302d503041d0702050256078500420344032403c00e40141c0c4d11003040c003031900000e000e0780d140750741c2918203d81484d1070240001d02180680f15414060b0400244d00100d549501540321081c0200c40c6042006503501c11009545080446010218034082c0c00810024504500c440e412038240039403080c00030300f51048010440b02c000d0011024160380d00081501901c420303070068440c14a00c00301d460450b180002d08d40c00e5031001c0343c040f603000307103409024844460b0b8403082d1008800004603160b0554040d44002a00c1815 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 421561627 1250 421560377 421560383
    0x15030b0312041404050117031605031303060506030c011d0f01051905070b090304030f020f041404050d182907050a080d0c020a050a02040203092103010920090f0d 71
    0x380400d0250f0300d036200c603540103000d8034200001da0341c0c0c2906010000382504403d085400402030342c1400968403210103007040c003a0342501d00e401180d104a166600c1b603680111a010784440410205140034000340c0f20802c801c0c00d081c13040c1880f030178000c000705141c140114810841480900c13083e901c10340550700b51904a09034400c030170f600c040c0c004d49542c01c1040c046419612950004545100c007006640c00c43c2d0740320100c150466665804c000301103500100040e001980c40880120040d1401c40a900460280002d010110216080108001407070307405181c95416001c810131004819417540410a01006c6090b869030805412034a05407041c610b000e069885554021014012214014284040c0d415005c03c49062425401c2e81c4412004001030202c1c1c00c81101e01e00942043e4005651020f03181040d25103c1100300c10082d5819428071300d2043c640780100c01800404414071600c0403824204540c0c4603006500d043c2541107120b81c81c84d0034018180c90160303452540f50400c4010b80564 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 421562877 1250 421561627 421561663
    0x90e09060109111b1c300f15090f060501080c0702030109150506100e030316140f010509070512030d0915020a050a030c0315030f0212030a0c0506010f15030b03 70
    0x11032060641e528000708041c8410305d80125140e400490045909005403000d4103400d039070342d44402c031038500303903240c540701c004c200e80e4640c80c001303a869005101d1005d00422500300300f0106400c1c03900c0c1104803010f22043c50195450004e00b8031042e0380000d103190344039882d501881c0d0f9902491011038003505c03e01c1402800d14400312a8a1150b00c80c41c2c208138454007054035410f80710401c00c001161096845002260903800c200065042c0024465100b500039000301c1082c0003c4c3c00600c0e60510300304c41078100301120b95541d0b0038420b8501f000d101447c010401201d0300f4880f92404c1140365124420b03040d0407580c00d41d80d540c3c14400c00c00120016032510410403011515400c1220700a07060f684049810400280b07800c2d44004054020b10900740d85d128140e80b012019815590341d08040c11440600313980c040400d02510301c0d145000c0008010781c020940d254140a003542c0750880c078000301a04460b1f141942c1000038019010070729019100140c1c07a00e80882c4501541c008a42064110000340c10412 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 421564127 1250 421562877 421562917
    0xc1203070c06170603070f14030c06040801061806030309151106160f08070f0e04020c060c040f0e0402010e010509010309050a05071701020f040308070302070e0a0c090e0906010911 79
    0x25402228a41240d00001c03c2078000781d541504140e181c0409005414401111840520444070720000340c0210f420060202e86030164402c001034074680040c1d0000e00b82e0b83d107412003031125402d01c42551281c00b00400c070a011031410341c1c0c1c000e000c8900c103000e002442d0b078800d220715504501c60440318800d91040c1c401c0c0c4040c3e05112031015200d0791104c11913070114201c01c2e080411507100302c00c15442044190b48041c80c10350700e01021540102c04124140c0c0c840e400f440800e000e40401c0c42402c0c000d03000d1540c6207641e01d181070b07070070002440c140d8003250a000c829020440540d8021041c00700c502000d180055a4409000058000b05400040075060f44a0241000200000002c06800795115001e6204207401e104030000d082c8d00c039852a02d0480c92043c0810400101120040c001c0b451107801921049500ea0880751107614003181d903680b6013500d4041e900000c5402c900b58101805d1507896901d09460044603640c0e44401c10302c281c505582c0e840c3c00c7c0e0f46a0121700c005a8107600030038a03480c1491 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 421565377 1250 421564127 421564139
    0x30705101b0f0f020103110910260a0c11060f010501050f040e1602060a0902030705040903030e060703060501035c042d03030e010e150a0315080c1203070c 68
    0x200300408003c0f40403d242c070700c81c1c2403104920001c6e10a08d6100801d80c441c112001281140c1515000c6094210384103021501c40c120140c40380400d10982100f00d0000301e102080390000d008400703140660040307810482c1840440c404810406041d42c41c01c0c2807141d0754071080d03140701d0400c0c0f00c0d030380c80030303000d046400144148080d180f00d422030750f00440c2c2d00300e907441d46480c944c140880b160350381c00039416401980100802e09081e0400182207001c1d040000f903c0c00c20070159030030514201e4800d0300107590b83d0b100740718560b018810008419541ca20034604102d40d80e0040c041100804400300000c083c0328070018000c1c81c800200e00ca58100b016500380351155076034000296400a00480005110b062101040b13850f400307036066411040488040e0b519841e58038282c41c3d080c80d0018480c1002400036801005407901007500340080035031a1823650715240820014100c620324803018444410b041000c20030f03041d0020704c1181c403800444d4a200c030444500c80007803a502c548140144080e444100009070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 421566627 1250 421565377 421565393
    0x21100f0807351b031b0904020d0b010e04060e01051603021c02040f170a03020d0c050f0610090c030504050705060d0b04050906090d0201021c0506030f16080c030705101b0f 75
    0x200081c0000f004602503404054031505103075003000c04c031012050495018505010302c40d4005001038800c45c440c150075111210442801d0300400d076005e5240c2c040c04108920b91007014041c00354040208480c3c284042141c29411580903003400701500860812129501c00302c018040403000d007011541d5540c0c50f44680204c004600c10300020103c1d041750700400390400305072013103040c0e45903002d480d402241c060140c4268030541800d40d20341c8125810146a00c000700b0119018203c500021000d0a207040c4040b81a11407a80340b1004240c105400c1c007000400014131603096460445d0b0031611002801e105070014880700322460313409814842800201840800c1d443c0c0120030310300c02d6a00641c5410426401c0c3d21602d07441c0d4045259503154074030061305a5100176041000203007502c83c80f00c01003004600d03042080c0190903114111304001c000d441410410800c840703800b40c000c0c012440c60200001c5204a0001c903403c140100d001d8040f020301450800c1001c01e652000b600c038a601054140105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 421567877 1250 421566627 421566643
    0xf0d0206060f090408070308090312010e040209060d03170c0d020f12060316030b10080303090714122812030203010807050103110d0c030221100f080735 67
    0xc080d00c502c0030103045509010710620320a80e0800800c5142141d1642c0031522903000800c0c0b81d110340010720101902c0401d80400900030a48000e500000342440d00401000d800301900507403141c4807070b40014001030303007016140d0750307031160034007040305541c0e9407800d0308502e204820740260f41c0b9100041c000d65402401002e00341003004904500d8481e03407088145035031815500343c040d00c03500ca06042040040c8041490991056458042161090362036210524582003582e45100c1740e00103100c244201500080c1c00400484200c41ea038042400c1c000e803035034690404001412000c00c103031340c401031100114a00e5800f21548120a07098038003a02d03800a000303400c20701403c801c50191520005856100340901100c003e280c90701103180241c0718015400401181400000340368003402990815a9480000101b10b070040300092103a1600110b2080040342c0c41c0c000e40720504011005112215002504009640012002420140962504252505c1241c1151088809460507105010350102d8158 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 421569127 1250 421567877 421567879
    0xf070219030908060c0405130e15070c060b030d0c06050402040b0604120b0106030935190e041503021207050901060f08090d0e0d02040902060c0c09090a0c030b06030f0d020606 77
    0x422a456000b680041449a441900d901a454234040b4644003030a41c001c00701c41c0748910464100002c0d40c0301c003d0a03440100c40d070b01e011520095070b860610bd40c500a0b4921070000f240500a15021420301038a100380d040d0303001d04a0f540e108006011901d642c1d00401412100500440c1c903070750340e0000c0f601c8103281c0d01402c480e00180310000090503030180c01181380c03056000203480b600e000b80c01018841c1a106103000c41821000ca1007031100040000e0042520000781089141d0080002d1005882d000c9224a09806039280c00501c110b03407030741c1089000540e0f904860f08460441507a451929000780c0340c000b55807046240e80001840c5810100300c1e66000f0442d22525019516040c0203030729042d103031508202007210100008007070324003080d018180c20b10040000036000798540200b0b1046c1c11040d181803030355114111041052800a800c2c0758428941002004000c60715981e440503a1101d110040049400c2400704429a42c18805003103c506600101c6d00340f0005160000c1d510001900c4103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 421570377 1250 421569127 421569133
    0x303040605070f0e2116140a30020105190306030309060203070201211d0304060320070f060b120a0b0a060f150306172103010e0f070219030908 63
    0x40c0c044a010b140040140c03600100740b4020483c91540021040d080400c110007140200b01e800b52102d60200c040d5030142c5801c050341e821003070700c2002307000450380c00d5000141d4204030783d044500d03085d04594142000f5600b41c921111009410320050310103000f80a20a1400c070768143d46e81c00c140307134941d11a4007128080e58821015035030303600050341c0303910881c1c2001e030026001d8650109030224164038070030000d55880c400070749403214484900800e40c1040d002c80441d04001070801510340c3c14050a010070b51400d02c40d8040050803005844184a00070004100269000701c046c103005071030b0f0202c400524040c04611800442c000940c0d01c4401e07010702161110407020210748070319213a1085009480190388600244e50400d51040781010070b5800c1c100c201501e52102244034040d00d60814102c0c04080010080c0961024460040341c80c1f411107980101030900040001100854021307400c00012000d502c030340c2e15880400c03420000c50212a0381403100c1c2c3c9040c0810103138402d94003001c940c003034019 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 421571627 1250 421570377 421570397
    0xa060905010b040203010e1501090b070f0c0f0f030311150c0702011106060105040501030e0717031c0207030804060510080d020f060f0129071a06100e031f0e030304060507 75
    0x40001320f010a02441d250700c01000000f034644a001c0e03155242d0000c05040c03a40d001d070380c1c82c84019802d9000346130448085541c40d80d42410052012280c40182240800c081c442d0350503c45070908100451002a0400024040811045405002d22503078441c0d14501340005141041424805511070f00b422400201e0080c1805644100842c800b4000d9405a54482c5042d150500450190400c080c0e50020750060100000700510f00030103a0f04983c1000340555150a82c80c41440703542071010200040c41401000700300c00007035112241c41c0d03000d0b0f07104070005007940350041845083d00035508100d03c6845161150303d2000c4d000140552602c3c181011034260303940d4001d450322082000c0c811625001c20410840c00e000e0001c03c946419200301c2801c0c0c13800c00c10592100d070032485041003250b003600c22510912900e400d184d01034401d5019103041500503e2403c0300801d43e1141080e001e8140443c01c3d0403000d000d0b0119802400d031251520703040317030f1f00c82c142414010010001950064003040312002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 421572877 1250 421571627 421571629
    0x2060c180a0906060f0c0209011404020c01090507031403030105060d0c03020c070611070902090907050f0f0d090c06020f15071803080d0506091b180d03110d020f0709020c0a02030a060905010b 84
    0x15001c02c07031540c0608010956440cac10014a40c0c08064842c3e00d601540174002000020300910454a42e940618000c0248070f19604003011305005071225400e0316042040184039944901c1c00312242c0125100c3c0004450284030000c4000b8000d2108201d05030144080000e501035010074030880c0b02c103114040d100e80b039070380f250700c10204e01c103660a80e60000061400621190302901c0540000200c014100740b60094111039000250302819041541d1a035420b81041445001e55121000c1c0c041c40c0003d20704e60018886981d5990301c620001110b40a5410000d0b107050302c00c0c412103030404560070101050302c0d1249045c02490b00050702c0c0480b46403502c40061050700c2d00070100c1c0d0090381070341e0f88491003100f91a04407103168424402e40110041d00d00b02d50030742e911084009003c0c24069074441c4411092080498106110710b202d1100b15480f004095a6044000c100702e821150a40d07401643c4256100816050540580c40a985802a5040302062002c907400c0040968814002042003a081e04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 421574127 1250 421572877 421572887
    0x804021c0f061a131505060f030109050106050304030c0b041b030305030a0e0c13090201051b0105041103010b1008130618033902030c091314060702060c180a0906060f 73
    0x2401c0c15600c42100000c82c010014142e0100650364042817003250800e8039000420342c1d0341d00488a281075124004010400350150388251400341c01149822031960416440003841110b8100d8081c00c86290f9101250402c210790714840c01c1c10320f41180307007601e840d528200580107800454401c5241800c06089122407e000701d280104440c0c02400c103079030002100081c0d401422140000ca06005081292040310721100510702e003914044000030901d45011b00e0040c02048541c40d80d14042e03070428149001d0fa81d034038100038102680030701e00001e45030780e0900c4070341d900e050340d940c040c103154544801c0784148400c100641c9001c60081d2070b90712695a0050010400e0390b071403820a80ea1245401521080386040c1c541050294002403c9428903120580047c2000c0c2c4207036a07100880301c2e054420350070800107000d00d030701900300e0b20060302080c64042d4000e5114480100f20500f424000252000e540c40d050113102c4181c04007518401c00513858a030329400800440c010107010586102406501510038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 421575377 1250 421574127 421574171
    0x1815180c0e091006091e270204030809010e150f160618020a0f080712031205160311030903120606220e011710020c030d02030c07020901080d02030a0804021c0f06 71
    0x4400030000300da103800c5101c41d080392041f010b9944a0100b0b81400e040850328000780004d18000d91107141d5450301400094601805c00d2040ca001300171400e0320100c100349400540c3c212090140c803040da14500e901900c15020000980201594030305403804c00c5104082040018082c4203030b800703019141d1074202252155041d4480e21450b940702c14428088100103503d98910380f0300c00e0400c5207a01290025410a40b68201e460f0144140d0986ca00d1303050070b905004030540d18004000191441c01c0804520341c8904c0740e035089a1441001070003144039500da241c11100c8505001500011417928220a88094141c80c0306683c2c041c0280720002c207040b204c543c248103007246000001e2090130244140000a5000185040c20310f000c22310480012202c207000661161140e4010306540c4c07201441003044115040c0c02113a83c0f40d02c08580078000035000411a0071805041c2040340c419503403480004d10f005034a03c090131039120b050204400304440003203600d000ca44500014020081c4180e44951070140b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 421576627 1250 421575377 421575419
    0x30c11060103024b0109030506061021050103050c090f04020f190602070f0914040b04050a0f030315090b061c060f1815180c0e09100609 60
    0x300e00d00401c014601145403d88020060303030b00441402c48410303002c0b03200042d50001d15440c0c6075400880b040c0c0303400b2448424040c0090034403a03049425500c81e1a0380d404000c0a250040350b403042055a11030180141c011488405000d07026800040c005880c060042072008407240d00c030304030f4981a5071170018056445029003440c14007540e5502d03020450741175100d818264101900007000001e003203980041c00041c0c4041c4d0024084103291001c0c105144600390700c4003294518103c400e000360f00b0301c0d44103d50803039000700701d207061520359007440350402c511513100601d04110420383d1820186c064011508141c00b505203040d40ca03a6800441040d1440d00c074401d544640104000c040454241c80300244102800714001541074464203aa000c100e03050708040500c000d1341d4403000780c083c224001c4000350318144d035481243e949080b01082403614188601c1620688440c5290441440303008502e0a01c1e000400100d0b0302d0410043c07002c20a0118010400003584020000c00c000c00c1c002001d0f110003003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 421577877 1250 421576627 421576633
    0x200a17060d021e120321010f0b090603100504050a050703050907060e130e01060b0903061e13060b131508010203040203331914060d02120a0602040b030106030c11 71
    0x70758403121072030f824607003920b03183e0010440e90030200c0f5101c03c201030824550032910310113030a41e18004508086005a025107546a01150180f121b00618400d541c2d581109490803626900c84507032103170366007500c1c2d081290000e2609080260801d440c0d00428011549510200700b103854000d80a41c680240340180e0740400c0220440c480c2e00c1c1460b40c01c0d00301e04d06090720700041d8200c0c1762021900f0740b1259400340c2640788012462a1140c078082c049070b074001000c0690399030701e15050030b0802044400142031000f65007105c004103090103110340001c8601c60300181090070030180c0340100e00c020000341c5410700c2480c10001c0040745018052086034002c2d80c004004190083c045004950000351072040000c00700e0710051003c0309c401d8007401450049808210b030b442014511000c001c00c0701c0301503510001058049051207603030789034003103640c4485070141d0701500c501400401d00352501c440800c000302400c0c400900050620070b00b201070341c10399400c0d5505120308643c41070219220750003040e400341d040d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 421579127 1250 421577877 421577899
    0x1e021b01050912030c1b0604030309120602121003030201060b04050906040209120f030d05060409031e020c0307030809040b0a0e130c091d011508030d200a17060d02 72
    0x1600600c00390090710b5006205003140e28608118900b1900b100c001031007113a0102c845800d0388004a20800c1c2c4c011000d40d040d0342404d10b141c9008050a101e0702c02c85000c0c4812015100600002d60101c0d40d600e46184500c04860030025590480814503100a90065107004804965aa5900215012500c0c02040c06034141c584404201c000e610240005601c0883d0140f0046092018440b02c000c000b54540070350340394034042e5040001e80d8002003000303218900d040101000650080c120445600181e501200c416000c902c2c103078030b40b200088400d50301d489459000010001000700525100400b642d090080017280340a002c145032450203011503116050002582c20108081d8500405001d4841c94030311681c0c4080e0f0404642460032500001c045c14104d100f0520000d000d00b640e03e0743c0c4002c059000a140154650716030240c41401d240481d10b51588203114048a5071503130400d0b403041c01081da10000e101001d000c40c0703c40748081d240300560314000780c00307490510303007200306250041d024894070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 421580377 1250 421579127 421579129
    0x1d1c0212120c1b0d080109060501140d0b04050c0a030f060e06120a020402070606080d090302150a11062514040b030a2c0c03061e1003121e021b 63
    0x1e408010090a081032040c0a41d007007002c10944004502001c4801505510b08921002065000140c225080d428109a820001d40c0d0384504e007410030014007807070140c8480b10301100c64013500b40020102d0f4814103203000e103c1c01c038024a00510040d1102c2c4c43c1007003401e46050640c003e40f5224407079039000210481c0043c0c154200080c0c18081800360005845c44511107a0000307080782c00c030b00c0d0140c9100b9903a8a0070320800a003040b088064660034103103200c201e840c650000d04c01c0304000003544000d02000c02c40000050188604032070409250080e1221407801c0c2540640f9803644a9850044908810103c0000350190040d00d20303241c8110002407030a0b0074142d4071240b90340302911140107155103001c1380301051a19240700b003024015400e1040030010b8440b45525083ca10108036102c3e030045000d001012801e0300c00d4581180844003841000d94400c1100da0107003400d64000391500c0368041d1602d00e04c541c011000014403c034402100300903596440f00b280d50300000d01c0206480101c00780d8070046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 421581627 1250 421580377 421580407
    0x140c03060d0b0114010e1f050c0a0b1f15080a0c0905060d060609320f0904150c0c0206070b270109060b010804051507031d1c0212 57
    0x200060140400400c0302075030761402003810b0300340c0c04240b030b0034418841c08030b5a41c2d11101003044803100b201c2040d42d00224000090707001d00094042c10a20500103400c4081c00d900340025001e0b81d8000100041910f8144a440600c104800305c20020944151021681c07400d035100c0754804c0f80d60b96441d500c8595583d1103040c002c1c20032f05004824001d509000080035030b01c020081442042045010036200d203404e90150048009400c256410000b5484001c5603520890610729603014084000942041e0400452250300414011541159801d410031007480b007450268000c420504400f0000366009102c21500501c881d10300a502541c108403280200703001103440368000110421010b420145113060711001000c00b4500071280e5142ca0b008814401d25101e5102080d600382000c038400d29050381c925403540d452a0076140c40c203c0d41c5d004165490310940c00f0030741c00592800200301510203000c1c816039581442d400d415484407504c01d00d8070b00c0b1b80701040000d904442c00241c981003409000e14056 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 421582733 1106 421581627 421581631
    0x601060c0807110d03081518040b04030e06130e01090204030c1e0b390c10050d0c0314090a0803040609020f0a0b041701140c03 56
    0x414250800d980890240d84400c400740d40319071a103014050038041d80c2d54150032002000100c010140c00102d01b50140d40c060a840c0500e80030801005814100303e142d000c210346101001c1400942c400007240d4001d442400d04140d011b0201011602540054481c1c1009505000d004c00084030440006405800124002d600e00350a540b50410700d00e64511800610100d00b0744000c08592101803920086d001c41c2411958510318045014180040c400032040907805184022200b54402c080c00304111035200054804002c02a0030406040920309001003880760030007078440105041d1007100003002041d140041c0d103440090604142050080c403145841d800282000089082c201c03c1d06ea0095025902003821001840070603d011490300d4196088001c000001c14440600b102600070341e018000700814594220700070307a00f030f02e09201403041d100c0c0b002c1e804903066455041c0250303 = true := by decide +kernel

theorem cover : BRFrame.Cov 421402877 421582733 := by
  have h0 := BRFrame.cov_init 421402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 421402877 ≤ n) (h2 : n < 421582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
