-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1566
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:36:18.841557+00:00
-- url     : https://prove2.me/submissions/a8ba2aed-1a28-472f-89ce-f9a27ce335c6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 281474820 ≤ n < 281654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 281476070 1250 281474820 281474827
    0x9060d0c122015091002031b03030f0c28020307150507030b0a0302031009031202030c041409040b160c060e060601020111070f02060f04080303090114160903080c070803 74
    0x8086401d280300404082200b1940b00d001076a03450300c0140c3d0580041104460303032406a2880612052071640c0c90802c0940c84240100048082c2e8044a04034000a41000b1920303440c2c1500140700142c0040c03c0b400800c0000c0000781c2d0f21529500034000082d00106041d020910307204412031030740c4a12003002d8903541c0c0c440341c038910581c003a81115000d940165002c0c440b910851003007241d03620701440000e40c143d04c170100c2c0344100d0741e0a0300110b25540c00303070520340b54810484218900741e900803a003200400704c0019050202c00c8252107099100c007400d407855480d80c54603a80b94445050042e01c4c00205520031040010b003030384901d42d0080c3d0300380d00110501038200440101c0b965041c0a031007450141d400c2c4441158100c44103402e03a0580c1c0d0300401c10544442041d000d20105500c00302c24008055400c010202c0c0c078910800055008018610001a0740c00c0c41d40e46901c4c0d914001f50041c2d070640800c0080070143d0b5401000701c1c6c01d5a401c15203e0340d590b000154524640340170399108030140d01010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 281477320 1250 281476070 281476073
    0x103030926151f08030d0f06050a08030307080a0207020d02040506060f16020a09091a070306050402030f1b04050f0f03010209030106030b07030f0212070c06060b0d021309050609060d0c12 82
    0xa4014a00074070380c0045548400307101d02c001c40c0030410310307010b0481340b81e04c2405060a4030110b50000c115824041000042c01601c0700042210303010b55400210580d8000401c2c03111541e4802000c42e07000c024041f0844c10502154001040c5500300c6e000a0b2041c1e450780b020410503030b258012641039a8280d081603560b80140f4503800610b2039103941c02e0744070b24140c0c2c10000d0191054000c41904c60f910282c004180d03070501e24072104010340071b402c1e5401c040e55040040ba0391f440d144015801a594441c0c001803601d003400c1c8021484402080c84c0d821901d082c4020401615244001c801c0035400702c6a16021104800100f402401081e140b04e6043d07080560000500040e185054069034440d5018001c40c0700d13a401070401d81c415120240e03501d5034100f0010b60040c2c032800c409040988103000c0400d6507a5100c45400c040d800996240704d03040e0707000540500251149550800400c2000d205000034a881c1e400501042402015180501e09000c02c000401c8441c12041d4040c0410070701210200c0a50b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 281478570 1250 281477320 281477353
    0x3030b190f0905010503030a0215040f02060307031a03010b0109090209010e03060403050910111902240301060929031932040c050103150b071214030103030926 70
    0xa0b8407501118918280c0013007031300c0c2004011107800ca011034000704100d010009501c1a201742c0180300b0341d505c1d60808940001a03403000000d5000390004c0e41c000c0f6083d2a464000141d01820f1903016209a24154001440c0d9800450040881d0121100180c071039140350011ba42c4040c07043d9403075905000e0308003000200350b00b00020f85107403001665441c041c070030103e005941151500894500c030f68403401211480c600f8030790082401d1807019056807107821501000c0c414201481010000703404c1c1c003100602130720f640501700d00d00810005e0241c602148010218126a001c8010b0100ca84c0c1000030004840e500a81314010742503082d107401f000050342c5c109000c0270034841501181c100040c2010400c0740d00716210070480c016900950301d881c4140ca0000194002d0000b01c00c1c0001d800400600001c0002c20a806004136a001d4500c141e21858041c0008140d0760190251321041c801c180010710100f548841d0200644e420403c090220340810300030040b0610751503224401e180b00d04980c00002101c3c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 281479820 1250 281478570 281478599
    0xa11041119090b0c0a1707151b022b020a0512040311220c022406090a05010f06050d0204030c0b120c0301060e010813020306070801060e150703030b19 66
    0x30716079101028251280300826840c0304070f55960003154082014000803e402200e03070810302c5000c1c00350610b00b00f119030b01c0b00140d00070300054050b840d50351240b01c8034801c8203441c020801d000500c0601034047c88402c020395050389080c01c05038020040d0644107010f90080040c604820b030800221048103200c03207801d808607880390104a450b0040d01008501c0750910800f20070f001102c0180d5480140406480c1d10000d041000c1650304500c100803000c0f400340f0104414040c10f0401148001c0070b440d040052108800b400b8013200301852a21004102c40e1420f07401000560701203103806550788194220020280c091500080d00e5031003030502c001107690010300180310158000b0011030a07540c9040c07240000c0c0c08240b00750000329007a00508203007903210703100207079000800422038502c100700390300400d16048040304c030304020441040052080907007207000310280c03c1c3e04032145100310340481c1e0414100d0003114801414141c541444480c1942c07038454042d0080c0c00000c1404c403079550f03042c02c421b2421 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 281481070 1250 281479820 281479867
    0x21302040803031b0f0301061d0405010b0c0609060106020d050d060e13050c1002060109020d140103060504030206100f052b03050415050f030c030405150a0b0111030307020a110411 79
    0xc240c4100c900390903043c401a17410981030151042c0c20b581c603002058958062100351418603a01c140800c00e426070751b501c241030103044c16018058503541c683c2d06070b034600380d0080c0102400d80d0090b0300400c4040e0b40020805040384007031030003c2d1281140340491000d404142c01600201c01c0d1103040007903c807280600e60320000d0144084405154105040c0850704110a42d41801600468014400030006400030081c01010321000905100c60801e0341224180030f8204031842c40d180c0081c0401d050341000a40d81140c1c0c03542003000240d1604030f0000f0308511503c112070140000d001c13811031010005c40d1900c03425202000c0911110903518001300b180d44036020300c0724002c3c007005000c1c4010780308005803010483d10201803442c0d03843e01c003c1c00b0069003008100b110140706150301d010b100707590f031a04c0c10701811000901154203d041000503180201d00f01c03540050f0360060080120a42d40003401444898004132400012104034011030064050a940c10441c60300000346409540880c000340501e94 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 281482320 1250 281481070 281481091
    0x10f0b010e0402130501030e0f01020c0102090a0f0612050a0219021509150c0c0109120503090c04090f06051b0f040f0e0709090b0102031303080901090b090105070f02130204080303 79
    0x806030030003080102d02500000400030201c0c10005d00c11940241c2c041c00700032400c80c045441c01400754001509980c000049240c150350040703441002801d1200d102409132843c0900f03c4011410000001c014070a0780b40e0601c00c150b11800414031888041c1d044bd040c2170005200004140010301000c3c1d50b17658000c089900700d217441000200d84103c0032450240b8003c011564211646400d142c14510b90001485c40f02c6556072002c4080020315810007409072613030b0f640c48050300c030311740782144504001040034401c0c066810103009100069031244003004032a8040800078094446040d00c1018a92000d03280e1080c00000541c150000f080c41c010b402100d04942d00c05881540704c0c0c1404100b41001e985482c04a503040200780700303500b92a0422202c801045c8112810003180040c01516680903034015901e00c04001282d041559101218070080d280701c9140a00d003011010008100744038510000c1c103d0409410b00a0441d55481408a071404c10030400755201d94550006a40760742c0180c4444080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 281483570 1250 281482320 281482337
    0x1151101050603120c01060b030124022e06030204020313020f1816110105151311190e0301020304050601150215070e0111150a0c08010e01050d03020f010f0b01 70
    0x20014010075104801c003030050300d08640c0e10a110003940e000740300c03090072554031000c011814460010207503000b42103461410f04c1200c100003100c641501c001104500f1500280f0603212a40341c2c40007001c1d40b941709080d5015001c640084001e000b0407180c0c2000754000c1c000014440584906400a420345000300c1e41070712040b04400410144181402c0c0406a4451078400104001000213100034203180354109505c1621010302041e086400885082a4019a440c07078030340700d4100144002c4501580f007d040254202c119602044c90043c40d100150083c0e80107106071585208481110360441d000e17009540740e0401349001911345109016841c810506c00c00030014440c40010514450340120740e07428001d450300582210191602c656140c1407001035602c1c880c0d81203040207801044511030407161054105000c0c0c441c10785d883c81180300c0c00c0007601001840005010b0902c030703044440031070f07100c000c2e403a0525040c0d04200110002000651810101030a01c42c20750300b1503c2c0300700c0c00b41d036400c1e030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 281484820 1250 281483570 281483597
    0x30b090901052d01030212160f030c060f081f050406030f0b0f04110402070c030213050103030210020a1d04060b0c0f0606040903080703051801020a2d0210230115 71
    0xf0069084034040380b410030050b00410150602d2908001180c83d0101604d121101c4442001e494090543c00000c2c01400541d080061000c000c00d1800640410f2500a0441d502c1d04402410000058a03449040940e0040c0442840b0446840c00043c070002c0d0050003110350301d003420042d21080d40401d544647d0340800080a027000c00104501c5551f0110b4110480752030101444000e401641e41150014680400400540d5032400030740c800940742200030034558150b1a000342400c0310010001d080c280144035101032142c2090900f048160183d40700000007801c031002601501099104000b50480040c114280240124601c1d03242202c84040721110307101d030700a1208580c0c0b0700d04080e00043c8414013040c1c1d07140c801d0308082d4020050225411301800c80356140d508980c0198400d0707001c180380d500d0807801c0e0200e50780c481c001860341d20b400d07402640c065500a034807034101e0150050100d0341c840c11240010701d8500301504030407096006003099a190340b040c00014502e10f1050000c04c01e580203822 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 281486070 1250 281484820 281484871
    0xf0f02071e03091205120c100b01110a06200a2003090d0f02010c0b0703060509010e0403020304290403080a0e0406053a231c0c03030b09090105 63
    0x1d081d650598680680c07602d000c0d18683c0701c10160f40100d4213030255003040c01032000c610020704004582900074045400c1c5980c0b8000c215030300c600350b40d410b002c0c07856080c01680c000801c0c601012a000040828040d501403840200304690304065040c0c490042050070f816035200c40d500e80e15109c2984040c40603004015010b40d42d020702c0c112294044040242400000c2022002c08010340c8103040503654011155290001c581c4120749400000e650b80784204005e20f0440003042c01041038411110a41c00c203030314001c2d143c1c402c5001e082240c022180e10f60480d1414208003101840002500c9500e440d2645071a0019038003136031148000a40348050900e944c0f130103210311030480d10001c0c4951410014007100448000100880703144050840d052814000c1c2a07400d109200c600c1070f0740907903070119403c2036201c00c90707100f1600f03500a80c0003045d0614070303044c54103942c404000c0d207042a111007041da04d000c5000d0300602489540040c4548140004c000054000a00805095407c096400d4950301c040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 281487320 1250 281486070 281486123
    0x40509010f030c0f080d030c05090904240203010e15031207050313050102010216120e0d0b06180403050405090408090303070302150105010f080c1602090108060412080f1602010f0f0207 81
    0x200340c150411040c006d20340e4085c0c2d00003111681a400c001e41410355890014031200c5048505032a0000d80329400c3c94600e11044154841010a000031801e550501c0d42c06030b41110000c00d0546500c454043d198650b503000c100c0100d03008079945199030361b0044c0f490455185d801200c01164080400d0202054560042c000d0340c1c0700780764408810703084103242c5c3c542c8055240102c540a0910100d9031880036140c84030800f2055a0b801100c100c80141880020312000040007181313402050110010b01000036030050886007168021034a5000540b90350801252902c141100b41f941440005009810503802040d6054029881e030000d020582e60750006481240d500c00c1d4900000c0c00d60070000c0c0b04859114080c2c048070f2103500e40c0041402d0254041242c241080c1c10440795a80880c04000811180d10324451104a0301e2403c81d40d0b9080050012000e501c001d090210000d100545030440c1d43e100754403c3c000340711440c00500103e452032034014001e51140c8000d6030300394031b440416242403a808828 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 281488570 1250 281487320 281487329
    0x9040f021903020906010c21030209031209011202031012051b01020d0507061505030706320706180c0603060311180c1e03040320070b0a0f05040509010f030c0f 70
    0x34089907171740e010011156200d84800840300710a0305244018018102861040d118009840040c0c3e41d070600f10800d4540007010007000e224103401c000f5400180da00c00300b0072650407203a20000da140c0d1a10000c40e544038a080c0c003c081040c0c08428540180000010142c2024800880041a002d059001281c80f03c403d50603913008614100300c0500042c10543c04000040c1e45000035500d6180c0700c3c00041d04013400d65004a00080100490340140a20103040c003101e1a000c00c401c0b0311411660401c281c0314010070101400d003681e02da508018010700b400004201c2503001c1c25400490f40c8424000d002480180030544280c180c1c24406803031410134400d403020150400010080e266100005c80203e584401504402587c6880407a050701074540043e502451103030b11a04042da01d014600e4a503c04c50180c00e14075640251001c106c002c0ea85011103645c1715a514182a2002e9840e800356042c0c8660b90005070080b0140d000003502009001515007520b218074140d01c412590b884030440c082d00103006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 281489820 1250 281488570 281488579
    0x60302150903070b040e0906010603150e2e090b010804081206130e0706030e16090f180b150108041703070c06050a0b040f02040602100b0f09040f02190302 68
    0x301006a4203103601424076103800404403411984c0b10310b40c40070143c0299019019007002c1a0510990000a200795805070085245c00c0004542128420184400c54881d6074601440d000115140104103042c3d1102100b02c2064010104100420b05002042034441c114180d0b2030111a40440d40c4101d20150203550006031850404200d4148100300c050054150340d40035008580d404c65005160084a810300c2074900138100e1140741060147c1981c29600c0b003840c1c40e400144000c03020b00e440021080540b200c04000141806440304003034000c04610083d50944c102040780072081089014103207218400f4400a030203030160003030040d00c207110b003540c008145400c408a000c1c030001500700138583c08146031811201d241260b1f100c0c40d040f07074010f0f184800600c4c0c5503c1e6909407820140111a90f01c40480021484c0616012000351540c505503c11740b06291a4071084410359201d21001e10b071020000c0c460420b60a0619003540b6031480b041e000c0340903980c0705c190041503150b1a030ba44030071250080d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 281491070 1250 281489820 281489839
    0x1b012a0c0302010f0c2004091208011508010501120c0504080f2107020a0b0304050c0d0506070806030708030904050a02040f060807120c080610111b181501050c12030c07020f04060302 80
    0x1540e401c3e06c1d1490031405401694624101e000300c0d240020300111146540c0700c24200e54100f0a03040c012040078813280741400b5000c40100100e0742c0c01031500c0900c002d003640c0050440146942206c561007554008041ca124408010001190108076a11680e0241c58189491445842d10342c40600845401a611101d250f4007000350345040d100540d0301c40d21400a49416900c0480040d4103110503240540d8940c2c400c804001005401000440e00007604400401307940745050403190b5030384a40007000303004945a03408100406e000c0c1d0103030307000b61040310310354409175440d010010000f0008980580c0003c5915003000d44035200c80c441c14403082c000347c0e5042010741c2c52005020f401c465110051040080b20001d40c500c006040c030498001c503100305640c41d01100ca9108004a110603001c0a260b88818842070180114608900c10b410584c01c0c213005403101740130740429040c84c0f10840001c0e84244008204030600b248140140662031080364819841040c45051004503201404000c0d008440d01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 281492320 1250 281491070 281491103
    0x51f020f1912020c040501030803040506070e090117030f0408010e060a090c030201030c05070609120f0215060d0804030c0608040218130213090606140406081b012a0c0302010f0c 78
    0x15020011258082c0c011030b13a01c0003481c3d0224007158402d900542c3c5841010041c40100101440701907005101d9251580012078554000707900070006104011018051071a8000245e509000341da01400514a601e1307100c5640d14540c601802000b02c0d0b10086004440004e41d044000d40716050909420a003006905411940154001e000b1401c2003000c1c09002c0c494600051580d002d040c10132840f90131400c840c00006600a4080d51a148004040d0740154400607502402000d15544c84031040302d441c03100440d2402c1c029424402d40e040030f011102071800108006800904982c0618800e484088030b07589002441013401a06171010300c184c01c01d406440380546401b40f1004042190400c00003074514442e0b58610854050340d020b0f84000400019400c640d2829200b610f00404030344d009040440c0003102031716000da07c4060244d05000d811861801e03c00c00828a400b21404036055095900550342401501920300d0301c4100e0005030480609a8424410910703031040720b5010b0300e040142c6001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 281493570 1250 281492320 281492333
    0x60e01020d0c06050604060519050f0a0503120a171f09141603060b070c050405060910032d0f0c0b040b04060c020d0515010e070c0201080f0a06051f020f19 68
    0x1501486c1c2c02a11110007042139a14095034803041826000380f05034052503e0705010520101d00e44007032040c6034818040180c0e8402044403040c201c89030380c0d0540c0e181d0740c4403c00d07200281000c09042c0c07003103840c01c1000400baa00054202c9003c0c00000d001666981da150b41605442e0151012030b02854040040751076080b8081d0b42c0381d03000d0424100402e02c103484000d21111a000b59000740c80020380355000b000141003500c5001d80109055410070800e10740b050072000d40e00624440181001211141c030380d44000c0c29507480e038446480c4450410002c03040d04000d40b240000303034820b541004c0d61100006080400c10b003101d0445120b51441c80c06e040ca006026035040030501000d076000708031070010b080058414490304040d50114150305840303505240c1d034522625030060404040c0701300e44a0003005070fa00f002c102c3d544180d05c60074002c981c0d61601c007036401500f0f1503070003150004c048403051541d030600010701c400f40c3c849070740c21586090a003c0c101903070384100b82544034000c040ca400c081d0102d01e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 281494820 1250 281493570 281493581
    0x10207081207110609010b09090a0206030c0708040f060809010b0907021b0a08010608070614040b030408030406090b070203030a0c03200f0f0f1309140a020d0f090507060e01020d0c06 80
    0x1500d0420044503183e2400260a0a808543c1c640e01a551109601240d1415121081e00301c03201800030030804460394003050842c4001360080da44840080341c0d541c10000310000f280c020f0604061020301c410303555140603280d450146c4028a0325400c003c3d0784401070404c1c00a5911a00041e07009050006490f20880010004da092490b0001070a800200d41c11900340106c4004000380001054818940300004024020424090352803078000c00c4100425051403050b030340c226401010103a600d8507980b60100041c009a18000d1500b600c0200f0041c42c560003101039841060811818003440c420b11208404803403500c1c00c59180c42c1e54080000e446811008050540350700d000c1d10070341c5800309007522612181c20000c040c2903512000605420700b819820f2440c0010b0004e42d000f8408140b0101c80c40415160090a0511107640030450440008150b000f0007901e80394600c0401c0181c902d42080f984a00740e501032103020400025940615503c00100d001c050b401035624a004075075555100c402900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 281496070 1250 281494820 281494831
    0xb070e030c09040c030c0510050406030c0e1903031d03071a0c0a0b0402180c03130305040911040f06020f03031f150302030414030301120201080603150c030f01080102070812 76
    0x4500740021040d40c0300e4000b141e0203640a107074907807012491840e01d40c041d1551604028056010001c2081030540c001003518152241414089262180c0701c104562000203582c25660140140c1004000104100c0031030094902903030302c0703422607120300b0303031002d6030001440a4036015440030744100040d0703c014040821790001c00044a150170a4400c8091522001036000c1d1181441d02c01480111701d04039490b5410f01e00302e00c640000614210150110b0b90000421110509450a03c4501018410f000300e030060042d0110801c501104100504c2c501c1d00075000340c00301c5158415022640f41e000003110112424404000d6103103596208880b0003400021a8524940c0110300d40419550a0f5006410707006903940d80058030303441c00341011820041034440280e00d507082000103000c26800071681c00000c0d90207003420b0200703854100c0031900c0e1111410748401c0700340c101020710000500705401075029400300c000c0ba40f51662512942401c0b4480c1b80700040c05007404018101101908008a96106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 281497320 1250 281496070 281496073
    0xf05160b0906010602060a091119170309040b040e0303040305070f0218071701080304050103091106030c0c1623010302070f05030c0d05130311060403140c0906010302070b070e03 78
    0x800503512218040d105480304035080c1c00400051081c2036040050301d40c0900400c81c1408840d03840c1e02c03100c00000741010020f0041b8840c0e030183c090540d280b01c0081c02410600e04000c0d09014100303c09481780c01600c00340388124100181c58540c1e01d441c0c0a8512081400c00140d89551155641034415501c0f03040110b44003106070102a025980c2d440020341c012903c842c0c0010545030542009102500a0220805000ca07600040c0a1203000100b44c90640300207013400a100c08040c1401c210003802003480310750140c4000100704200c01124040d084e04d002c00000c07580f1200d400045200c6c50701c105d000c1d120340380d40c94460003010405410030f40f46140406050041c507010194031107090249140c4001d407582e03400080c00421030b0004000e08110b10a0503c2d100f4101070216400c2c03140d440107480060320a00c103000341c01d4030550728201220001c40e071040c00280f203100107100164072070034424800340c440c89041c0005102c80d4000d000310748220341d10440d07104155442207070540b074440e08009041e405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 281498570 1250 281497320 281497357
    0x6030309031b13090c051c0c0902040306240504110d050907030210110d030c090305030307031b0c0519030215010608070315051807121a10030209180601170114041b0f05 74
    0x200743c0b100c0c0c941c0c8c00760040d040d0141e0b03101c2c00c508140094030501100050080c200300d01400c801442c5503030304010303220308580200d42103100801840c3c0a000c3c24990752071307491404003400048000010944201c91090728111030b40903030903c007070307880010100214809402c0b054840090601ca581702da00e601c446410310550b49600c84e1078051550700200c2d00180400d81da42190040d03c19400c0d46083e0200e040c0c5007000810f02d0715034800341c80b1100d1440d04031141e2216214501014020310115648400d4520303a5011580e40b240010701800040d6011008203141000351b80109520920000c151200580250740b40200c281125040c0700340101044108502c49221882c80400c074001d85a400c028401102e0b4046100c1c420450080321480910301458810031070900c460f02c0d0701040b003000f0103181c1d208984030383d92000140c4264601d81042c0c0c2d0503940e00d0f80003149441c903400300c8001c050b01c00d03102000080c4180c400d080000074602540f40c0031481d0902d278015800d100303500901c103142403407543c1d2a6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 281499820 1250 281498570 281498573
    0x506030a15021b100e2e0b090c0a03050106020109110112060905010f0501020105010e01050d080c030d0f05071b0b0c0d060902070c21080703050306030309031b13090c051c 75
    0x1480d403d5030148220f0382c10241c0340d01d0329000107006220403d18030802030002401031031042540c0b070111404d098403c03e0191001c840740649540200229030707014162070039070710702034040d60790607844180c1c0100840c0c40d04002188452051144056840e405280786450080710300056500c1700000408041e60b40d180c0102240c1c500e0389000c1c0310300034400c5182220005080600285c00e580303050700140c41c1e421105004021580d40e100d2400ca11941101c88107903507215054172a8218030814007805105c600b011b0040581c0305031540007134401e0714640d50700180c0200994081c00405c840c504040c1c00401e0040c0400d105000010080c5091060048c00140180d52210079009a80107500159124412260f040000c0098040d01c0c54800d00751394815a242c48003595500c181e8045c800001e400c220307011000480c9d03628100120b481c9610024215081c0180000c17102522a494201040c0509c080400c1c000203800c45005403440342c1e50110b03600700694244030030720260a201c24803110403032055440010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 281501070 1250 281499820 281499847
    0x2104080414121b010f11060c070804080a0b01050a09020703020a060f1d0d030b1f1d1206070e061201122102010212011a07062a030b040b040506030a1502 67
    0x105041c3c21440c8105065802600140292034824417200c20300054a004030355201000c50071076071010f0080c10b06900c170111428440281d00440d04040814400d03044c5400074003007200c00d064100c80c0211412009507468a030721005a00580d04d0060262b0f0041000c00300092981c1c004851200c144140050000415032100d424441c03500b140c001c0b250030040c19410314983c140108003c604082e5851200d0124141c0c203040600341465031501041b10001000703100451092042d094000c0040150444210b80300307440f5201c50301542d000d00482d046459201640c100317041603400c2030540c2508040c00ea881c0502e048032050002c10204d81c1040300341466105400814203601918400d60300042c0c81d1540b15404100128040e0080c91500f404d403491a00807c0201d803c8660482d405580400c2c0f1412250042c44666460705011000708000c485030040c55600d48d0013070780d441d03108640500840d030120b02407008480060711400c1e01504003050150101d0f08111022058000c410b41c0146800788241e070b602c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 281502320 1250 281501070 281501083
    0x60b0f090139060b18070804050c0405150a0f140906120604050a030906080126010b040f1a06031e07020c1801150908190302070806010b210408041412 66
    0x14005080320072000c100f44401849041414401512550f240466904244819a5000b001e0204004902c3c0c0041c04000041c8803c180b40c90001e04144203070304100f008164001e034405071480c0205198000024907500c0034404804503015a80b650b507034802003405114846c10000c11440e00801d8103246c2c00301980301003000c644510301840280030009001d190081100000f9400f0700104040100103010710b070050f161165160020841217044003020741c1441e4050090b45d080c2c03a50152034058004078921560300003500c0d483d00c0207415000700310003204101c024001500c1c403c5161034105591840e0045681503541c1100482c0100c6510014500005090140800204803038200e000c00400c22003241d020102548c29480c03e1010100303081500440c0d8038078204409403c0316070a080c600c400d050080c480f501c040e2014a040d6091580c50340051000c0fa444070200c0c51803a03001031410080071078042c0d040c81c01033b5400401e041c581031600062624103001031800c035910039055102c1255020041120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 281503570 1250 281502320 281502407
    0xa0917040605070b090309101116090e010b030a081e041e0303030b1233090102040f0b180420030403030606120902090c070c03080c0f01060b0f0901 65
    0xb4a80d0b12011860584c00300040500440100c0d402071040a100d6503449413a0740030700b0348501d0803002030803501284900d40604020508000c00351417001040c41c003802d42141a0801c5c27014000d016102c8150181540c0f440b00d18005410000180801c1a00301d4244400c91a50510303070150340d0415813904101d46444032918440d1f11484111441001019010b001d808202c00c012a40070901c0100c1d80401a01c0e00e558040c41c0300100500070b000c515000d10707c690200b07914080120301c951807900010b060300030762060281d40f104c805c0d2124006105880002292441034810302e07461580c1607201e003407101810b1500a20030141c682541404420301c0001c001d10320450080c0e8001c9580c614140c0007514020a81d80f0810440f400e011140d00907032075514449401c4004407862503901c101504041c8070840c0ca07a000105031850005240c00070078800510404407184010081102d01d03036480c032030001442000c0383c44c07c5039101800f0b40c42c070b00d44c02280201c1c0c00490002c3c50881a40c2e40340050350341103800180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 281504820 1250 281503570 281503577
    0x103021009050a2d060518012703052b05030c0d11130b041202060906090306040b1015090b13080303070207030308010f080304031e0210090524030a09170406 69
    0x1001c41c00c129110a81e804041c03071400c03511061800c05c0c2c4010007511655112403903480c218000702c11564411515680c007041400104403620390201020a6610040d20054980344a45440001301000c02c503041103010022204440c012114480d060780e040c0c20040c2842d000400511651116402500490405a0310300c040603a071007046680405170000203400512420300c05100c01d0084118200c159000b464044403400d44071003c01c0001001b5118019200e41c05004410a02c0108024100414010344140e80f8080040d13803280286903100c100210110b0001b014103070100010740342030000b4040c8080507080100c88a0700d0382c800318516401a1061001a4803101c02081415402035210b03000d400f207024000451850511041e0340c078000c1d40030181070601e030f101c8107007110103847c4100e5070b110303901074000c0d510301044d100e0140880c0401e01c00c0500812200c103843c40c11290f810a40403c040d41c880c406411611005103260080c0800007040722850407241000308406200009400104800d94 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 281506070 1250 281504820 281504849
    0xb0a03020a1e020d0311160c0305120307080f04110d14010c0e0f0609010c05010501030c03030806030c100e15040902090a120c030f08120f060307060c02090103021009050a 75
    0x6100600a061507000b01000c0d02403034040604030b41c0e020800340891191031078040744059004a80c00014401e11426100700e8010b00d5004003001300d01d0314440102d80c0a001030750751800703031600607485500c0110354082c0003174080c4001a0307084d07180b1a03120b60420300942e0b140d201a42e9540210340b641c2c0302e111007a03403a0100700380d0184c02150240903040c1c8140a501d0042039803115038010030a064100c16240b4030401003c2801d1103564458000300d40040d8020000b800b00f9603607414007038400c13441400305900051b0910b0016400f41400a40c0144600c030250511070301c030401080465405c61901d5130950320190500044801f00625005000071380a801c6005a50785410400c202800b0000d60041c0304001c0c102c90ae000c0072030289500b54045980003c2c00103409841445e221160b03104ac0c001034904105c0d050144030b5450710050f000d5200e61816421034600c00d407142c170141c80ca9490104005d500ca10700710014401803c00c90601124011035043c2030f41d83c43d88510004030074135087e030420990300d00d000c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 281507320 1250 281506070 281506087
    0x7030b0925090e0c090f060409060608070302210a110c0705090115140906040312031a0301020301080a030c0203160b0a02011109010c140f010c050c0f070608130c0b0a0302 75
    0xa2070204503440040c00c2400700585032820010222100030718806403954041a00d00450301e4071103c030b6151041c000d00e80c0b9a00c0b615101d101e002840f0a004400c0015070140005413154002d200719038181c140c1d0492031000c80043c5182c4000c201d00184865038450701c0d9100c822002c2c032400d01401044e106900a0b00c0c0710b0381018280310880d0416405900c1c0d84004245c6000420f0308501d104403510101e407402c50f0341d0100500416020300c1507602c000d004100327615900d071449a16a000c44c2000b0828134920b85486403003030405091f80001e01032622190440d482401c0068021603541e0a02d80c8090243c070034140f041c280d807010038ac0003076101c001502d000103010000e6a50a210702e20821314040c0ba42410508942c000130811480b224008000c3c85901c0048031211404000c041164242e0000900c198915000e00030400c2d00442900d100320302c159412044c03041030104985007030750341c0c0d03980b03a20a560310301c401502141e041c04810b48140c0303000c0c500442d040381d0b91002051400b149403809039a54024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 281508570 1250 281507320 281507371
    0x20109080415110a0803180f0a030807030b0316050d03030e0703050309030d08090705210609030c0f0a02090403081b0408010504021305060d021504080304090903090f0e0103060507030b09 82
    0xf0412068607030f40022103001d00080c28101501d412901803602c0240348010350301090f1419010716000340151050306003440405a000c0c070510321070001950288403e94041040c10358a89076290140107604980e0005e01c600d007003103000042e0b40350203444c4c08205108401703401428421250415590f1340c00020b810f00e100d05041040c0602c040b02c500e001003003440e08039166621042140182482030410408100e044589602c41c01080e944c001c007615aa8101070110503a65030099014030002d0007080b104560100c3c0c04070b00800425009070031640d4550b1540e034126880c1c04000e10143c030510944600380d009122140150014041d14030000803503080c580104851140c000d0403011982d17080408120042e2109140d154000740c2c107482400f04110303e413002c880c0c60b010319086006030b40703c0418006040008c50308041000d41c02900c40228035034031000031400f902d00a000e00500b138510071004100040c1a43d001c1030344440c2d10700c0e00085003c6002c0001c1d40e01c1000351400c0c1e012045466156480f03844 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 281509820 1250 281508570 281508587
    0xc06030b06070b01090203270f0609010606140a0527010e0a0510030b03030409090308060901380f040303180602011a0d061b26040213020a020109080415 67
    0x4456460800802d036960000d2a0014080c140d4000c0e00400072441d001c1d404c140050682214240d080034501c2604c0800e07641e401e0341c41c3c224109110b03e001207203140806200d21000c1c0c400d00d50701c3c6d44524900c080410799540c0031001ca0020090104070012407600d40d40c0509203008030084020f8412810500010000101e2142c11881407030301c01000c00003580e80e6600002c2191a50601149654000c00000d003140aa40d0044081a040c481c0420400d64052070b15440303a0003c4850320500c1c0d81310002104071002c0b0007100c21008445a600c012043da808001e20706025444c0007440c03520280d2200c02d07085810950046020a6500c6200304c40c2d00d49144229000e094984000c00080f54580404490300e85000d00b010b003e252501203a00c103000080d081010b803455a01c0c030007000b0b1b0307504803030050450328141030384a1001d40b464424031902d0300003c09140542c2e0020010301c0002c160b088980006d5000c2c07440300003035641c1c0b1811440000e43c0384024000400340da24140600d440824006009020f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 281511070 1250 281509820 281509841
    0xd0203071a13150c200402031e0c16170706020a090315050f130f0f1a150a09020315091906060306120b0402010219080a030b1f050306030a0f0c0603 65
    0x29507072900001984d0145000200d036411030550101e0800c400342110080d4100080c0941060000080019081043d00c261010103088403c00d519541c400d031410565002d03203801c1c1040d01407100341c800c000c00c40325200c0441c2020300d54141440d14169036501003c0744d200840d480d000c40c890400410a1207a142c00681c8280304d103e405000c00d2404001c0d0020401b0700400b25000c143d20b92414501748929114a20310071640b20b04e1803868105141044070119184800107140300c101d070700000c5c000b8000441c0c440000c94000e4840300060f03080c011401d0280d04000d01c52140f82400d4562002e503655005003580c0100301c08004039034145500d03082001aa0500d4000d0310605081c000100092000d4000100016410600700e4401e0b4a0341e20040b420031403899025414003004103061030602c134100d1300400589481e91410040c01401d5014864508903141440300c4901d0b0b640d01c9041d06078001c00044d540008010250b544104069071000301c7c40346050700a40340300c44600c00a00c0440e0b00361141c45e4885 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 281512320 1250 281511070 281511089
    0xe0606100302031018020706020c03090909030708041202041811030105010603020f0d11160c0f0608040b310b1e060d120504030c0b0901030515030a020d0203071a13 72
    0x514042003490800c5205100e1a894a10171100ca01c1c0c01d0402ca9058030316141c1d0001c402e6503108080071840395a90429004144101a4580403a44444000040311510f660111141d4202171030301000c5c5202e9030744101d0a80e002616180310119020a07212030a0f10940f0424840c16001c0c0e022051508582c4160001014503204000c508040040345060390010b2040c403c0208003803c0307231102c6078081e0052401400f000740610041400704910500c0b401c0643d040140700030080e03503071080111441c2e14252000392520078040c000c240d04040c00b900d40080307100000b0660408112444111104c861000b400380c61030900d1b08180005942400740c2075000f4091564412058105a4001440c18414440081154001e0404880c009001c1c0050383d0043d600140a14038030b6990f800c0307101c000d500021243e40042e00d040c0006c0c85c40c0f46035000070340400e1030280c000c0a40070819400d00805003144181647e251140035800150000c880204680301c9054031141c0751551140b0b40c01c555070414070382255080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 281513570 1250 281512320 281512327
    0x30f0e0613051c060507051b01090807061a1e030616021c0e030d0f020d03110d0b060403080f0c060106020c0303030a050a0e011104050a05011d06070203100e0606100302 74
    0xc0307190000c4540940b8012034962845401c001c01c50003624080c8071000705514200310030400c40f143c00c84040c000c1c40e1615070007d2800c1d201e1070340300340c03c90744d020100411f10340d420300c03c50300071404692011041c1100440d2554107045c110f00040c807a081450410351951241110f040014103051000540140c5588101580301010840103500c403444100090300c1600a000400200361044940609000b0050280c44400c007940300003d003517132038600d2003001622418100303240252180c89940c184410758201d90382031800c1d145041c0007400c00850195402082480084089655070700202a095084e1086a6540d00030035659402c20b40161300540640d001176500003a5034030040304490303000401480000f12913907803a05020050548415582e801c0d86070103480444004400000c0065800841d2a01d0100340c0d2040110f90306c107240007018207626801304054449040240141400c9880201515408034500081c20211607814035032000c01d50160050000038102a200030105c2949842c0c20752a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 281514820 1250 281513570 281513587
    0x50406050604050a0510260a0c020f060105041d1504060b01020f0a031218030c150c0912030207030f050a060c0305040206090f03070b2a0109031211090607030f0e06 72
    0x200300d841c4205c0e030050015541c41c2d140d40344101d02c000141c2d00060031120b2074148031281c1d1403242400b250031614079481d001100c0e084600010f030a00c8000303130070002820305a003410113000180641554040101800c010b4a003100342050050080340400038030701200303902d01401d1a4040d00c00d180581410740d000610300c00500d4601003a082405501418100b099090450b035107030090500c006034503450001524180b0030076510100b0054841c2c014606c03650001c0c02c03c5440000c450003881ca85d00840c1444c14100030b041044501602c4550081c0103480e0002d43d2521115061b80584d40300326107030b400c110748000030410785100b03400e4401040d2074104500d1a02c0c1c4d0102d001c7c0d208a04215106203480040b003a010b82d0100801c030080e00d003a1444a4588040703904003810094049003e071754038148070b030b884802484144101d818054160381c8128908443d501240005c0840204d1180d1103030f010400882591648001000100e1017a41e504281c843c540c54003d260340d001118091080804010903603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 281516070 1250 281514820 281514829
    0x108030403030302070f020d0615050103050702070524030106051c0b090123100f0201052a0d0605030102040e0405160509060103020f070209070f0912171606090c05040605060405 78
    0x80c262035260900603a0384840c1d0428104c2500070880080d40031040811003820000c0c15004078610304041021102410703240c0e00190146c41085504000603807000c2d004000e140750a07809400010007941c08060f000d00002c47c0303110340703034400d8111002140c000100f01c07000c81060000703024035004030003040142e0040c4d5000076024102c1031140708041109128003801c40b07500003210207081c000040c400501d03202c0495019105403c28006100594a03001c00100c80e83d80003800710f281c0c01d1404101c0045180901000d1007280c22041c00c400701140c0d00c00011030701d2f880900c010b002804080c0c0240000385007510300103203408800d041e80142d0018110302000311345c03142c1c01d2180d0000c000342400b50302c0c1d910b81c1080304254011000080c0d40036114a041c0001c4541068400d026581c1942d0f441500a8940d80d98240c0149802001000d803d07908030f000d8240c96480c4040c0500d800d00700021903030750701552a0501904c0741030780103032032900c24a8005c008914246c818680100000ea50b075504091401e80001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 281517320 1250 281516070 281516077
    0xc0301180b060c01090c0f0b03060d06020c0f0a031d040b010903030806041e0c0f080408160c080a060c020c030106050102030d0209060405090a020c431805100509010803 74
    0x540c0d0280c540420006550b40d000a560b404141c140082000c14000e0a01c4400c5028600c94120300030803880f0085440491001280c0c41200043d044055042c000d65a000c000e510216500503035002d503d181c03112000080c001500081d01030759640030b5080c80b0090204040380501c00151055203400e54924042e42c0040d00d00007101c0d09420f02c1142a03442102003401fa01212800464000d8075202040d4842076039440550317419443c1c0c0c0c5503480f41c2c0101c6000ea404540c1994064a034000c1846450841044200d910120078440c54038032038290750310140d061400e201401c2c00c40c0e0080c1c40306806071104e40d04010032515040124002c0c4585072070170300040cad140d00c20041d20403400c030340004116080391138071812a4002c14001e8079046117803400c603061200940099251083c14001c0c8010303070142e0000300c401181d0150380388840c0040301060221909403003850703050450294090010008002d07503200903400500e16141c1000c5082c0c5031070803840400300c1803600042d100d28000320040c02141800401e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 281518570 1250 281517320 281517359
    0xe09040308040516030c09060510050409020711040c030207060c0504060f030b030a0f0c0905010b030c031315180209010b040803030f0a1e0b120136020d11090c0301 72
    0x81c0001d6200c07400e05508014440010b0840540310320740000400040b841410219000354604011071502d0354100301d010086078407a400000c805000602008482d9801004068403400b5044e000e400c4000204060703d207002079200100394040f8070a000c0c00380c00e00540e50301c1c000f01c2c80e20a141905180016018aa80404075010990780d01d001302d82d1078a041111003c401e0300302c40010002015458403d0101e140381c06849001c900301000002c94001840a0324014000d0f0f0340700904554980c079140c44000c41164040e00d000103902c010800700d014a10400c0201041441528181092401400100302c8103a06c824481081000104a852008000d43e07400044604054600761503001c0d07000f01510034204001c80313080c00056041d1410400e94005060360600b1f556981c24401c40c0900d42d42203580030352444000c4504440d103980425203089001c42e201550f0800301700030340b10302d2700851201038180204540d8605d881c4070090782d40c41d10b101c5003a445103440a0040c03a540c10f0000405101c044000d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 281519820 1250 281518570 281518577
    0x201120c0c0804080105041506030309030b0703090b0a0b281401020a060f0518011808030709170105090610120f14010c08040c120c05120c03031c0b010e090403 70
    0xc00e00d4460466100529041002607460319180c0340124004e001c1503070100c900c2c0160700b000514915080c002d0000701e1703405880760980b40c2c0c07031901c84420f09240207000b0020144d8070403c5a00003905070182a01a031010f120000d00010030b00e040c0170303c981071402c0c49094444682503015042030a01000c000b41c0d010310056958880031080141d2a00e070f05403800400e0740d0b0400444111200701640102d10402d000b88080d0f0f404841a0442400c03100000302c04030004404190100c04150f070217000f19080940f03403503c2c41c0c180341e80303801500701840c520b00240c000d070b5122001d108044504010341c5401001c050030b003038003040c6840e1900e43ca51400d240000d0503404c1150208092048001a11100009031b000a03c1004000500107041200480e400c40e00d01a001303801181d050360380c40c3c544050aa01c070500a1195013410104070081340c012141102ea40718609446075151418070162a0b004030b40391800005041608600d002c1c3c880e59807445042122f0040d040d00c0316a40e404255410541505 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 281521070 1250 281519820 281519831
    0xc06050916052e17070503090d030b010905030a03030605040c0513090b03120705060402010801080106060e04090807060606020307031b080a050304050c040509030a02060a06080606280308071e020112 87
    0x12102e18084803030350080802140c00c080f02c6082c441c0c01402590b01080310000b00e014a50f142c02041e1500d020555410b100d036070001a5141245029a00c40b402c0c10005040000c407032650390f00000e203090f980d50002c03000a92511010040360502d400784510205081c180b85007002021020030702c10f21264815180a00c0d12a0108075407a2024441c8102010900b160180d80f1000ea04100b0369650090320b0480c00580b0700742c00014010018400d1030203a80d01552003481d0080800200b0000e030150344d800740c40c0c12208000d0350300003c0113842100d00a06254005c0d5444096504010340b04c107040c80200481038101190740400503112204075103400d403450030120b1326916079080c0540703810311500d031654009151000b4403002850010241025800315800c80c0c1c1142e444440303c10903151188601e112a501c241c010404c0c42c0380010000100784040301c40020303059010900762450005541c0142e5281e04002812802d00c03480604014408105c0f04082901c3c00c0e480d40002d01c500c80001c44070b8011036580 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 281522320 1250 281521070 281521099
    0x1912050d02040b030f1503010b01020d0e1201092103020418020a1206170f03120411030a150b011b02030703031b0c090c0807020f030708030c040e04030c0605091605 72
    0x1d505031405448081c035241e480f803401c6022840058015500c070407101c4030b04641c250680c601405104c06140042e4085c0c05440b000c40c0082d51806503403011107a01c10400d444600c4284000d124a4401c24060000c0c0c0da01c401a5552820b04c80d0040300b003002c00c15004202c14000d0313142d0349250b410020b220040040e0f88010341c0f40b0031604540d440401055560500b000041c0069480c010220500700300f40941e101814080b241595a01c00c040c4c500c04880c035110005004500c00507621011110040c00380e540c4014296642003078a85c02c90407000b480c030b031794000c40b5006580c0407600c564914120385541c07040213001c1c3c000070b94825280c40000d08000d0205c02c00001c4400c40d425030402d46c4c2c2d02400c100f0f461034640c60311002601103603001100180e001400600d2080c0300090b01480d95004070055403078002c0603141c02215900c0241000440740c1d0421001600c4500f141e01e15110310300a503224105180d1070714090b426500098080212507000c0c03e02c020f1000b00e070103410412107008031078415030390200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 281523570 1250 281522320 281522347
    0x10605030c0f0405060c010c0e1c020f0103021c0e0d0306080c0409080f0c100b060406050a0c0201020106170f0d0212090105130504021c0b01080f04020f041103010602030a02191205 79
    0x4139000b41c0d401002c046080e03004843d05400821015005440e082c1c13601600780700740306034410009422004211406114005410318145482c280700041c540903141900d010b40c94455040c1c0f020820708601e9030740f9080d02010f04140101086e400380391806100f21031400003900d0355202000e1405108640d924400c0c410490a0022110110f0100070915100c00031885281c0e15039081540d9a8596030814001249522b0f01c0c600b100c003500c00a032180390403c00038540440300008040000c9055640e034220205070360400120900c064000c42004290380c01c0791008580c1082e0360f600e0a2029913000a00c201035070300e8454241c0301c00407000e18019888000381d4922005002080d8042c0c2c0d0480e2000500c107208100158031001a07001d2180305100f81c0520300011924207400b195136500000010000c9001441c10002120408000902c04505517032b4101e803034800da074030aa12003805a03000240d2404280d4062081c180700c02c100303940711245444d0a8843c14501c58010482c01c080260000d02c02c15a0581c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 281524820 1250 281523570 281523577
    0x501050a0c06050619062f0d12060e010902031501020a03090b0d021207021c0206010e071b020306090309030c030a12140d061409011e150c020316060305090303010605030c0f 76
    0x40c904142e56043d5940c2d103002c1c000e02d8064987d04100340f88100c4511440200c7e114500702134030075a0040080600410301191084000111507190580b1458001191556040e001e80a0854280016540e090001241c40c1c1010a1311020741076401100100d1f021903048560201124412104c0c16030703d55404010800901c03c2282105000c0000b409101e0700701d500040d04044491604629034a0070849601617070b03201000d1140b542100800030000f81224801d000d440c0d5003581d9028035a0f040f14080d40005d0901c081241d001d2413a0b0b0000c07981c00e0480c5000c2050032403000041c2d014000400303040c0c83da01444c000301d50400c0f040c41103100b8841e141d02d080b40b0840c1c90428403240100041520351200452038505036108922a0340310380c001091071107a80c41c06800c10303800d222300850143d00c2c00c8080303032200e600f180d210070070f1010414448000d61000c1c03100b806020303100b408803010241460000f402700c40000d490b42c00941d00c24001448829004011250400381c644070090301c80a159003c0d107440d20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 281526070 1250 281524820 281524849
    0xc0906170114040e0f0c010e0603090606042003041b120b13020a1208040e070306230303210109050a06060203220b070302061905091024031406010501050a0c060506 72
    0x810044010740006011403119001b0500f60703a500d032240d80602c1000941d000c00c1c0c9210b107240e00400082401c900d01030780501c21141400d0042914542114407100d05a0030482e426201842c540c1c40100700b815444c0c503400e000e841d8031062100c9500740341d151800e034043d0017052403105c151103891b80000d640d5417800200013030560882c90303218099a46000d8181c0c6e0000d100b40b182444580c40441c603c01d001340a020142c0f40e90b0402002c0c10301103135140d2205d900c0c03401002a0180800c2042c603410000391140480107030007191000055500d4406500222000282202c28482c9000014400558040100c440c2c3c1c2c000d5400c50140c41007100f81004003d00030340d119130341c440c00002c1c0c018205500401e80512460000021a5440320160746003825188103c85820b65508104000040d251540e803019210248200229000d40c0c0c40422041640c1d0072900143c0340c0180b10b0315481520042008613074054402031a01d5400c10070020402303442150301e03903c0240070a03107490004c0c805031110070380d641044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 281527320 1250 281526070 281526073
    0x90f12091923010801060c080702130501080d0912051f1401091a0d02031e030c100603021f0816030b09042603060a030b1003150c0906170114040e 64
    0x5503912403282c410244540c4440d05558850240e030348540c0039200f014125041e548a506c1801050340e28841141d105000c02c0341c1c890b4106007008100c516a100d514040c18046004000c5002c2445c005040344a40740d002118441c0c09690340f00004101007620000d580b0304210f8040b800c1802100c50000c0e1507a100440281c0404500018150503250803041c440030325040c002c4040050441840441801d80c034010307406a000c14401c08400d404140f408696110020070f0300c0c14601c00d04003c42c00d0609000080301d41984886050096150185c40e0300c13450341080c085c3c64481c00350088003404e1190020300c6024a07506c200b004070070a90007034102d10702d0301c1cac8000c0c44e08800d40341914240780300c0c5040020b490302100440003081c0610346007600b141d016540c010100a54103140d56200c0f40c007050004c007082c0718210310840c0000011100c00600c00c2041c2001070108410b80646030050220005a12801c2005001c10b21100d4038030390600441d05540306100d4401036030808801040c090003810750b000d0207a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 281528570 1250 281527320 281527369
    0x1f030c0501081e0c0a0917070b03070201020c150702010507021906090c181410050f090a14070203180a180902040b12010f0e0303072c0a06020114090f1209 68
    0x110503004c802006038501c1520341c1e100c11a240c01001c402c0b4030703640741c07000c2c0c0c6540089000d00c520900403003c5c40c0d01c1310081c400945400c8100071103c3c02c1c40e018000101b4a205008244000c0e145c080c0151540303e04548010803204502400c00f8201c41070801c80601899030320240341d805e001e11186003101500c0600301c2c1c508407400178070340d62009007007080c2c4640c1c560020601180c60005601e00c520100e51004204020641d80182001540c01010b001164500d42c0e500001c07003c9080c0308000d078828003050b005540c440000b4804100d4030750308014000d00c50f0f4450300701488001c4010751190032554450b43c001440000ba0720108005004495501e0303402030070f084ca00186a04150003c261410640300705100c1103100381d00440c0d8900041c7c8101004c11010031252401d1202040c03000203000035030340301c0c10300b44407240003044030750303219422a0b00142d440320076881850104da40182e80000400c4000e00e10000b46204850321500716010303041d0002800603070304420b99210074203804a8042002c12045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 281529820 1250 281528570 281528581
    0xc030203060d0f0f240e01151e0302040606120e06070906030c0306050301051503190819022802090f0c0a0e010203090a09050f010b09090a0f090b0a051f030c0501081e 73
    0x1107039241c1e0170f084011a07083c6498100d22a8060003025003644008038014101030420380394010207424402e9452070706401186c00400341c0c0da940101c1000300030f2500da40c014602c1c4910720409590f4000501000c0d64040b4091210090f4014502000c5807164500024071401010f01100503081d0703948807030f80c19803d0005010013000100c010034801c503011030840359998a009540c0b5204c0900600c0904238007000c0c072814400c10340041c0080004181403040d210b0890030302402c03007031501c0c2c0c042c0c00c0c51780242410410801c41c28070f4180b20382c100c000710f0643c000380c0c034008184043c40c2c0b00740c18010042054181213804207034020410b8803124040107082d00459526461003200600c0e0482c2c20420b65403021000045010042040f0b410300800502614415070341c1d03908510180020780c0a61000c01e560b030040390082000d0300403c50040010300c0003c1450f04151034a80350b805820075100100c034461000401c00102d41c40410001c0f81c00a0a0003162980d890002d6102207071142100c0503215000400c006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 281531070 1250 281529820 281529863
    0x80c1302030406090f2306010e150a03050a080304060b121b0d08031321050f1c140709050f01020304030b06010c020a08030c010c0f02030702360a0c030203060d0f0f 72
    0x48803421085031108046c0d055540307040d0f840303800384100c0900b42c4900c0089804420a000483e213841000303002e02c1c100f15581e41d40d2502e0a4030704501a0fa28540100601007000014020400702150449120560000740c00405450b280d054122000351214401200c005407140d941c20503600c1d0308802455124a000b409008801c0c1c140c45086419603100000c0c1265140c031810283c028103015504d02d803c01400a40c5600294845254050b1003050b8015504032402c440c05546d0018006404a0100b420001e401510f00340c0103030080ca114101c0f070f808201c010390380001a2800c6036001600c00500d1b0302c8650041c5d5103141004e20282d04107240b10b6001c42e854100000800308291941e000300500041030200f11100c2c0a488654001030f081003005801500d421600f40c20030b4100301c41c441c00c02e10140349040d06c2c00b1400740e04402c1481440010000040c119106d41210021241400e5165141100c0000c40c0c0c001c4000c8020020b0010380c00402c28808000d083c211042c0c0c0c0903a00030fa10b45074140303e11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 281532320 1250 281531070 281531093
    0x20a08120309150f040308070e040203041b09050c070f0204020702091e060d0c0e190c030b090c0403020f101809062d090c0203090315010f080c1302030406090f 70
    0x10000d43c800d68258988100003584414400d0a0004083c5000c3c0c8495078200d0b070380d400c050328200030450b0720082000507555600c0114051881010b40c0e1400b1460040b144140003101d5020b42d02607440c1c6010003400b040ca81040b154055804030420348200580c5c4001402405031a4001c4e41008851003000b9032102003007510400e5802c08100c000b11030390b030785003001148486600300504034030844008101c1c6401c010800e43d001100802000340502d40821200b00300c4260021420001e1b441d610140c4e20342c00d0002009802141d070300c466a20f0302d8250380126520460030490030b0300880380726110940c1c1301d2140394107034440881620155441d60384d41140c0c038080d200b00c0c0100890100c180000d00341450400d0407461042c060005403507401e51a09555000030075107980160150700040181c1c11050303405000c0341e10300c0d54408030b40803401d50600400d079a6050742c0d0f4000b2300450b8060b040445c1260382d1014007401c0110409400750344c075566843c00d10081c0030f008100404096400c91448104401414030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 281533570 1250 281532320 281532331
    0xa090c03020306030f0703110108040303140a020315040608120f1303060b0406090b010806150c1f1d0a06020a0e0418031202040f0b07030306080303010803071704080613020a081203 79
    0x8599008050112141d11b030002da11004000303a03200c0c15001c41e254001c2102c20361190080c04c0004030fa400000c04882070800486076420740550010800040e46040030301c0303404000058408001060800a000d0b03964518651400b40b410404641c94985442640450742480030441540c200b0710368034982003000d414052101d510a606081020440e803a1074800c042011805968522654581d82c060000d485d902424108000c05d0422504400c1e09040040e82e4000b1290800345400c0e455114060080724600302c00088a52031010587c0c480348030000f401d100184d04604010303070361350884070280d60442001d42c1068101c0d08044800e61031918a03141803203070a002c0c2c0c0300c2c0b41612800329400b50407482a030042c66041705105600303001005046d8041d243c410320a00340018191b417215145469a0030981c0300c1040355100042c0c0104020710101d070000700b5080100f8503401d01d0304184103180c54800082c001e03172845103417002450655948040c2c0780000c0c501601a194441920100c0c07108a03802141c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 281534820 1250 281533570 281533573
    0x3c0f0703060608281104060902071a070f08041101020a120807030b010509060409020c0a022d0102120906030a0f020a091d070f080403030608010612051b130b0a090c0302030603 77
    0x611041d00c05540d1410902024001050100c00c41c4c070f0382d40c02c0f0070b40ca03003240704507001540ca0401061150385c0c0d00c01820981c0c080c02903050746911460500028000c000c0c101e0003001000038641e450f071600a407040d900282e100c0090030940000000403441c114410a001c1c0c00b440c201008a548250403a060034000e41c00b03590144130040044006540318405c1d0324400e500000c00700420030075040c180c2e02809074801b607841514401500da40000e00140c40c034040240307110b100c18240303502910343c12400340d480d03184c02e0000d0700300c941010102e1002c2d03002d10b03200700307010b00c0c400030004030b03480030301d27404010201c803000b00842d2a1000b4a2004044100500902d80c0350150050a1080c1c8014854800c0c45100b6680e21041c075040c403074a088592000251040f014180c881101080c4590300f0b0082c6000360070110415a41c004842c149286007840c4038210b500c41d42c1008406041c0b645031150305001c03101d059040810028001c1001c01c0c02c2290a90105c1d00c510720344038000c0f40a60349600198044d860480 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 281536070 1250 281534820 281534833
    0x82e060f1205060109050d020607060e0d110a02060307030c02030c0109050d091e06230a0804060b040506031203070c0c1202101b02150f030a0e3c0f0703060608 70
    0x208540890b88181e610502060960004016900d0030024401b14248040c04403030030b001241d56140d054403900d11126a054003c00510803074154442c6659610010a00080002000f55004105544400b07002c0c2c40805407a101a4541d2500800444082103c554001c010200302d03030504c00d4507020394130251000500c41c0100003929000c502214000e20255031480840c141c50500c05841109200703604048000c858040000e41071441d1003c2d080b00e80d06a25404100c0c03401c0d01c1c2c043e0442d0741c140503081c403541c038250a200b810780303001072078640c3d04402e480c2d910b0f41c0b625599410340d40d0082c1c1c107200400d000308400b00822444c0300003203048602031007500c9106815111160070b40308036400160100101030001460000362602004041d6400f426100003403402c3c680c80d0a0341183c0c0c4c008c60b40340e00f03510380302c1c0380b0340d5031203003080248844480c2c1d0f200300d070984c0b155201d02c481c0d0300301c10380c41840307014031000030b494403110301c06000103000c46241c0e10403110229500d10340040604003d102d0000140281c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 281537320 1250 281536070 281536097
    0x3100e040c031e08030a050603210a03050f01150f0e0d0f0b090624190602060402120303010b120a020c01060e0109050a110d09030c060f090b06030d082e060f 69
    0x64003034101c2958400c00083c1141c2d118441c0c0801800001c05007a030500c02c0d00036103c040030ac95119072002641e442401307a0344400f0460b000d0155040030f4031802e6074000d118010400050490f64810103d4040d242407906442e201108584402003d0440e40d8006103c1c031540c0c04018000340080001446811403200c95643c03403802c2c0d501c4144c100d803030400d00c030b13081c101c0c50401a08421013044071080052400f81d150500d1000e281e060a02a0499400350f80200c050009516102c0344241540c01030074000c625560404104000d24003a039015052000c405102040c0c0c8401c4036010784240b05850402000700f00e6840800d991700080a100340d80c3c4082ca804c0c007103103598405000341c10b007000e02d401c3e1203450800d1120000e0010245080243c0030040c035005a0070014003280101100806c00d6040419902d006060940d0401c001506d101d10952252490b0a0300a030405d01080d800460a8841c0d4442034403011016065252800b442c075503581020710205030550000040a220385a80d0354114507030120 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 281538570 1250 281537320 281537363
    0xf05061f150909021b190f170724050610140d0b03030a020a0201180608070c03110111192109050a080a0c0c141f020f120c190b060603100e040c03 64
    0x414003134100307e042200d4602090a562100783c90804003000030745004055102c1030b03180c4c60100402c5060403c0c944110320740050501603541c000c2c804944a1801c0325000f50094000200d41643c01c045c40004554003200100c41e41c004200d4490140a9a43d02c00e11064029251141030300c0132408035125107142d039404400c8402c41402e4503042e803159002501d54203025202090102d908408001c05000012980305080c002c0c240b190b04d2902d01140c4820036052622001c01c496074008013000b40020120400a5503540010071060313905600042d00c0e04941041402c1401d0a4005410048009816444a07a10003040c070070302d83c041c1c144000e52684580f0040309015000c4070450748184081e030001d452110315401d501d82021140100c840010310b005020f82000ba0a0b075000d0b0b0503180118111401c0003082c00042d0003016503071107c0300407040755a24010540c001500d22402900007100050102c8a5030001101a14024490044a241c240740549043e0b62a0104440081c121421400003141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 281539820 1250 281538570 281538613
    0x1005030c07030e040906020c0106060e0312041208040509070804020a0f050306040b1f0605091f080c181e0f06160323070f05061f150909021b 62
    0x34910055107011529101218000046140154041d950b080c1000014001e44000c00c0c005c58400300114007249000c6c0050324920f050b1074120f000b90001c5282c40000103510381100c059800c09150741c030613540c03d410810118081c94008a421403000c00a02880c40e40101c0d941c1d03ca0f41c403c80c0e404a03e10f071112030182c414081d44c070810f0741540c03104001c1000141c40e800955800b4900e5405060024207800781941542c0180d400b0001040707002451300032a0408116100043c10044030700441801c1150004096010040c11407908110224111911507811600c400c040036006248401301c00498480c038401c2080003003664400d5280326071080d41403c004058a140d02081c01c140c0440c03243d0382d182540c44000b42c0d880b49144683c1e06002558400d030038006030580c940204414001d002845c900546040390203007000104010a8200d1407001d003180c000722040e02d40014207481c2500207088103654421403074202134001c50001c03d6151071140e0f80d0350307000b004130920401c54440100020700c1c0c1281c1c50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 281541070 1250 281539820 281539831
    0x81b09040602070311010507111b010c08130e0109380118030b090f0f070305060a1a0d210903020f10020312070f0e0f030d0305060f04110702100503 65
    0x190100000d030200d08240d0182445034040e0803c40b0b402e00d15000c0403401c4070000c0761003c012400b0b00c59012807a4904000b034500141c642d000c0000100d030200006044110401801004508002020108200050040c000924030808581d41558407843d040c405486040696200540c100d2040d94400203810066003c8400c4121844003128080004464000d03080e802c0c20302c511012400000015101c4190321701c1810013074050700460807400d000c0c50421860a201d00619840f042c402d0000c16000701d103464011601c1d420000d440f5020f080d404500400d01c007042540a049502074105021195030300d45203d0009415200c1c0302e0000440546000d112404040d42200b4141d08025181c100102806035802171401104d080c00ca102404043e6120200d5030080083c2103858658100f030340242e4203164400046800300801c0120401295491191404c03020405803a0760225150351034050780141c421401400500500070000907115450b07010100481c0074181c0c46e602e80c1c7c1407070f2240c0d064038041c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 281542320 1250 281541070 281541079
    0x614070309090f060503060a020d060e09060c0304020d120c02090c13090906020c07030813050a0605090915030f030c0d020c0102120d020f041e05010212071e06060f081b 74
    0x85082800c03620040a0038000340c103461340e4030f9401145030382e81000031600c12480c3c030b0f40140e0b650b900170001c001610803075809500510414424445031880204409500052824070941c8036a500e00000e1064109884041c0484840150705d0300407a50100d81000400d00940f8452030301e0701c6541c082e00e4140310301c070400d42051000c050180701d110f0003070f007140440038001d80b0094109408201c180381480c0700c541c8102c0b0f800c0b40c0060014071882c0c008201c1c0d0001c1000b164800c1c0403514000020b8413038440c0428081c403424580300005c041c1621440461240c01005d41240d48071418891a0362341e03a40600d5071305065108200c01030080c50300c0020042d00308103042e400740001c1c00c809103518032240c10018130844d0441d0203000ca03580c00000030001c1e100800000004032640c3c016881500070032284d50b00003c0c119001b20303910040594a60341120701c42c2d6070219071030403540800554002c0483c05136800034036850034050001034401c802510001642c64103c01d42c1d04050807a06842105400d020089420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 281543570 1250 281542320 281542337
    0x8090a02130e060f0a0c02010b06030c0d0608033403053004030903060e150c07060e100608070e0106090303030b040207120807030c1418030a0501060f06140703 70
    0x6040007200d00c0e0300c4002240000c038100c2d001200e05410007038100e8294850300321140800c04110340900035100c04903500d0000308211030110000c40c0340c03407200400c0e040e0341210010301d802940060303601c008010076681c07003601d88580c111a00241e0b020300c21912003c00c3c000380c0070001035088121801044d4640e16440c3c0c1e47c074005196420f14841440603000b40c0203c1104000204450668500207100f68800d5070380800d0f690951074418102e4000d03072002946988050320568400d40d200d4091500100b09241c2280c0703c10a40c90035001401c050180360040b40108491826003c540c2d42140c1c0070307244404150380515448a054420f040742c248208000145451010404a8042e0f03201c00c41100b00500050300e0070084c0c1d212542e042625242c1c03200003501c12410840c80b0303a4944150390701d8001780d1078a10365100d150002c1c04158021255056480702060103004c200355800c112481d02079074054024040681e49454681e94940030b44110804a84628801d20140c24102e04441c100d96154032032951 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 281544820 1250 281543570 281543573
    0x40303022a0a121101090c1532040506040b04090c0c1101050d090b07020d18230102150a1406040203040203060a05180307051f3e031501030c08090a 65
    0x34407209030844411300c440318071100c3d1a054280250b465882c000e500a250452402071180b640040e016110020400640200c0300000000304520b89517128040d10403640c210307083c08078880351146901031039020100040005085d500d58000d88102d603040d04041141d410311241c1990f00c400a844010300340c0d01c4030750030b070000c3d0760050020380f119025219001804c0c1480341d0f1042c030040710984402002d6400240b296100560008025449030107403041f0080541c03500c10080780751a0240100034104e41e15030000303a0141d10800c03610860059800c13141080d4106000071400822866101020b0421258001a0301d820703d8001c890045034050010401640c560030300300001d240c09003102c02e591641900c0050b401c07074200f000d041000d004d400034241c0c0036a4284400c080c000070030201030586040c010512401403008038000120081e005808490b84000b0030f0380e03800003604a09000700d0a6000c014001d1310068070012481c00d03442a2400c0119488000d016100e40c803081795451980d0b48001ea0120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 281546070 1250 281544820 281544833
    0x6060901062a0f05010b040c0210050405030f1603080106021b0d03021e010204090b180c1303050a030503040201020c0901030503030a0902180411180705030105040209060909040303022a0a 82
    0x40c29000c01d0480380380341a842c2e000920302ea0b048000999a110200641c0e4080c084288200c958403442164200602003050401075200c0340014840810b6a0390350002505200e0103004541c00c0326140c00c511559180140002c0e180e0760524881600051610400441c10340c0c0000354200c803803905000fa00d54010b00803802c0140c0c031070190300200c04500440c0000c903640c44800d00c1d850059540d02002503110345c14164013a00325142c445060380303da2500c3d0b0b0038400c91b020203940190480c0403c43c0c0d1558600809140104411256100800b0351181c00d40b8042410390000c05140100d2003682500d540102400401c25400020700000c0c015030030410105070158419800301802d2071000e0090074403904a00d210b80300c0300c601194103603030360340040da0500c0892504040008039a01140420071807400e0100c0c0041050105004081c01580c0c001900201565514191400c3d410000c1500f8968507061500401942028071450b4010041c1d0b0309040440d803421889480c1e503078001c002420b542140d038541a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 281547320 1250 281546070 281546087
    0xc080d0201020c190623190902060f03090a1a070905040213060f0e0406080105040c061b02091009020c011e09020d020415080d11120306180615040801050103020a05030606090106 78
    0x41725241d55850a002c6801d02c41015194080000c0c0d035111440c2c80c00c6c04c1c60f40581a503194495952170328096000005a0b20313131064500c00300400c891662280e0398000c61038a4144062006084030a4141c4480d400100400d900c0d071280280d582d40742901561a0b0600c001c0e8042c0b03035440b81d1503180e4420240242d510403d43d03075502140c145400d030300c01100b40c0049011640303d0780040c80f03e40d45800800050251a100301c000a24444ca4a403482c44a01041d19640000c0301c10001d11a04010000c07945c042e9188131311230085c042042c0115a03820346121180c2c0201120b04106911841d040301c40c0f0b920000c1da00c54070429a8000d03202c901804d00c6a400c00c00103200c44440d82150300e10b8580040f5406000300810314416045888440354680b8a80000d40ba102d102c502c1c0b002d03134090030001c100c203036155110310b003403803074400c580c110156142c1030f00142800c1e800810aa48090010400180b01c2030150443c5049034000d0354400303001c9494100b41074851208489040e04007102c1e800401c8a1482002c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 281548570 1250 281547320 281547323
    0x3120b0108071d06070602130f0e0c09030102070b0c0a08012103121b08040b010506040b0a030b0f12010c08010e160f1e05221413020c07030c080d0201020c19 69
    0x20103843c140c040001130059000204181c452030350200f005217a00c2444025500602103082824013803a10b401ca62103e8103e0042509028000215660095407425015180200c1d03110094005034a071081d64000c4a400840801000440304030002510b01060b880b00da1950801585104c0c88660b10b0300c0507901c940c015405400c1c1d10340d03900100c9500324000401d1880700120795a4080c4142024186110a00b00c10380246206070001c00080006104500480c0c40c9075050781800300d2250303000320001d0312039080311840d2078000366401948201c441c019408015091400e440d51400c50b600da40f0307a01c42051040f60806604180c02600c902c140d80940d82480c5484050314041201c031404a2003101c07010401031100c4003142001c644000c00c03207a09a0980d4484a551900c0ca035402d01e800850150701c80854031080c06407000700c80d0706030003e6240d0111407268010a040b29480c80d9207140120483c2c4e00740c4109900d82c0511440200500d00c18006c682c000c81c805070081203851141e600305215208040310 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 281549820 1250 281548570 281548607
    0x906011e051308060112050d05030c0d05040201120609050106031109030709050c040801020d06050405010b090a09022a06090f03040303080610050d0c020c0310140f0c1b0a03120b010807 81
    0xf40c00401008514003900c41110380c00d07000d603e2072034607a191240c803141840910009004000900c0490320540300030004003240400d503515580010307030b0b038114800403120890b41803140100d4915035980210303040340e44030780c0c0c00c20403513401d54048a024040c0e8485554107800a010820100c549500580c1c1c0000d10307010300c1d6140a030380c0c84086089a0044e03614035802500c0740c004001c0380c6814070420b8018480601100e141c10b4040d00051441c201300c3c000d42c41800d0340031440d040054400a01d007001140d410284819221014040d11340e220022540400c042c03003420380d1340108900c08800d44040301e0b40740c0c503803003660b845c0c03541000b820b000610314a00c10450280708944a40c9040d01951444101640103052040c805405140c14400700071140c5070a58103281c00110401700c0700c001c03554842c0d41007144000c0d545420004034403520940304c40c1d4031000103841280040d42404510104500d101e80c8600c115007035841003070015503801215107408503004100207280f050081d411240203030600d0b00b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 281551070 1250 281549820 281549857
    0x6020a03050d020f04120311070e07022a040606020f010606210f0f0203240102030a050406051b061603050609041e11150901110c0a05010c15050a0b0906011e05 70
    0xb40906c0100004036016000604a070940b540c0d010410700a0b1809081c0c0c980f01c01d40c45140c01600030395900000b0321202d10408c0c480124100713141e911591446950740042007030006640c0c4d42d0000b50740c1c0745c400030721102c9540f0b0080d001800b00d025040032800e50305003e045242e0802c1c2026514014052012440340e425261500c1c0c2401a80600c025440341c0340040080301c03070410003c5880d81c0f9810f0462440d0565104010703000c04aa0004241c40442e0114500141d840401e0720710b000a8542680d00c2e1001889010140310101c45d4500740d0500319403056a08000695641e0104203860318103130380140c0300e07101410010003400789000701000c00501540e902a075a5901d4004105130002d440d410032070b480b90109025005603800b0901346140310461004100349204440012102c144901c1900d05205c100c041113410803802458101d01c02507078050820892409000e80783c054591221554450b00014001034055070140034050f5802510144103040c0007071890b8150b5459015128003c0c4030701240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 281552320 1250 281551070 281551079
    0x31b10120501032001020c090a20030403020102040602120f04030201050d09050604050123060918160f050f061303031209020603090102130f031e110603091606020a03050d020f04 78
    0x180520750003184070309100102d400004031243c002103030304060181150011007140c80039980d60040c2d260400e0505030006002d948140022080340c40b4a043c1c0003400c0300200400050580640c0a00308031880f07074007074604d101d80340d40981245d482448100f0f081075100380020301c01b651244020b05020000c4640000d03c0c1c0b0b6550f1501e501e0160100c0d8125101c1e9165000b40c0314103500031020803081d0210030398989050a12100065030603500626003110500e49240034940b0719410003825003d2a4000e0555007019180c034103405a05081d40034450084802145442c51400c040c5c085440d590040f4210101b4541160b8084400115018043c049a40c980f115600517030b44410003540200740d2000010382d01c4551400c0212485e0095000104044100d042000418125504c080900c1c4c034104903150182c07600d00d0402440c1501e1007174540c0015003c030800c0078004000800c05601e041c00508085095680d41049a80c2c407924000100001c000780921041814503070060140c00c41c804e000d8a0400b5101c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 281553570 1250 281552320 281552357
    0x30203010219090f0503060f0408160606050a0b19110705060d091a07050708090a091d01110c0a151404080d061d06060306010e19060806031b10 63
    0x4000c255420110b0001c4a282c0d400c0000d450041031244000101a03103400700294a941c8001c10f241e0541c0d16680c006000c004001d0111200340400c110005490b4040d0306004004104500526020790300741c01d400715000005900f40d5107900c1d004d450111903240321840449199164200501140c0308003030000c0303200d83c3c0e00c8024001b003035100303440020445160708000803441da403500c0640c4c580448070140014503a00404840c1d8850f000f0b07540980d212241004590107814550084100c81c1c50301581c104901100b80300d013151080804000c0c050a00329041903003551080501d800d9155102451250000d126080035034030b0840001800100300070880e03641f011041c0101c034210b03440600050801104201d41c400c64014046080680c00e1130301c2e000d05011000000904201d200307007408400540241c1c804c103215004480081c01c83c040700d0302080d03070314041071886000325400318000c0b1700010b0180c20001007102c11820303041c80203140e20510005108011801034484001c003c240c4038580c5c0c07210710 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 281554820 1250 281553570 281553577
    0xc0302031b03011803051213020a090c020f0c031c02071508090d080c0702012a1b08162c091005070302131809060e0606010315230105040302030102 65
    0x4108500e64004160307202010b08403443d00c080265180900e410180220768003005643d160015988091240d84580304d040076001a40038001350300c810b07400004611050301c0c1d0400c12500b4840d800f1600e20080c4440101d40300c4280d419074a40552010390409010b803600e035040c1d42c2c010142d00595100b692a003000b0b0042030444000b1001080811081c0328a40f041044a662141860710f0b040e80703641810408058240301d0301001070304000c2d090038804030600d42590410314241041030409503043d564a461008148881603650f0395504803003000850301d0000c00d40740110843c10307251301d00310340c2021965144411450a1070407070310b40c800f441c01a909003490800e030051443c18000d0080c500b40e02c498505584004142004260051088c10b0400c00c41c500c074201910340340301c016242045070704d8600300200640007028212038100600ea20050b5008116107008a0003a64240a411240880c10001502c02d108402541c4511349290880c91014003100800d518149445881c4c0b030f549400181c01e980 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 281556070 1250 281554820 281554843
    0x30201143405130f0e0601020304031205030411030619111c0f1d0304051f0e1201020c030d0203060f0102010902030316060b130228020c0405100e010b0d18110d0c030203 74
    0x210080303051103000e84241780c082c0e00440c2440214030b807905541d03a1050545094081030180500440802e080151402c03290015110241c11240c0500d42000c0304400c0940c00044410054a040c2c1845550b41e59841203998003c418001c2d86982060f5000c2600207040359051012800c0d81c1c3d8419010000c80000e4205002100360000d545a0f410302040120340c840ba040042c54115902d40c00c4040181c10046a02c00c10104581e15450b17429207080721406481149000c1007207001c00944d44424003150303800b0714001ca0041d25450715207040381005a007207038000e1a0107580365100b80201c419403210700c10b80241c07142c070420002c02c99102032800f0800c00d08107202408121600410551030701c0009154455040e044000003181200640c0006903c0f89518a42035018640340c60000e1210070360080744100401c82518030008540c0d481d6000c581c50303048128500b0805040040c0240d000414030400c02040fa04007020a0b2103506600820103840c060030003c4880d100c0b466800005a502413040f0740402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 281557320 1250 281556070 281556089
    0xf0406050627040203100b07031710080c090708010b0d0b100c030f031103011208040506030106091e030c0e0601030b030109050601080f0a050d0e1c03020114340513 72
    0x49040b62041d075880e00d0542d001c01e0142d03205000300000300c0d5407180f400c1c0c1101c50910341706685988605080341d08200d0410a80b0790006040b003807008a4404803c02400c4501c41c405884030340c04c000040100e10002942c40b0800213035517000601440708a50010881002080c2000a0701c45401012540301c1401090202c003060100300010240364000303103450480c1200e80703010800c08141c10344c03032405400180075050240103010280e800304184002150702400000f0451500c0b0740e510040101150b845004220701400c0c0c0744803130072981907040050405d680c0d01601c8803411505101e030001c07110000a285a0400d5101c80c5030090301e840c20305c6081085402000a841e0715818462540c0c0307482ea040c008541141d2040c142103001c6103000c50012024840c07480c0c84103803a0703110310015440c0443c6a00148a030000042400d00f055015444414840140b046601c0f0302d60b98242d2502610649128041541c0807041c82000020070828001c00e449290b818a1070408240c000308055203403030f641100303068 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 281558570 1250 281557320 281557357
    0x14010f02250509150d1506090504050322141e0405180c10120504060e1501032f01180f0308070b010504020306060d09021f120c0e0307050f04060506 65
    0x1414056110355114007030f0280c141c131102c80000410081002440083e144000550804070a40e86940001c801403110b000b040c0602d0403d42006600d030381c800c00402c554004000108407401c8620500c6a04413504030340c030b6203002807403a401c3c410f410490301d10180814210001c40003a5070350307a20440b0701620420003100aa684a003c00d9841c240401240504c0b4490650841c0546a80114440b0329005400c1c004a42c0c3d858a282c140090000602e60f003c01e805102c00a50700c03030304848041c074100c038003ca5500d000d00380e800781584c41c0809107003c50b1b1820084024004010750260901e904c60b000d045007100c4506a5442c120f0410248075041200c049000042d22000d0001501481d80542341c02c8a0071407031340c00c00b04009000d91295400d45010507440b1080074042d9501d190002212010281e0b42200206039a08002c148005410300d00008500d410010b41c5100e100361354200e1120300c00f42c0204025402c210030030415a406000b00c992183d100c420129050703c07081d0190a8568900c0d044604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 281559820 1250 281558570 281558579
    0x203010906110a091a0d0e0c030a2406060503010e04030215010f0303180509060d05030d0f050103050607020d120b0a030807030c032604030f180e060a09050114010f0225 74
    0x341001c0e44040801c0103031507000e0b0301700003206007192000e90b13014100003803544817010124200700d03a8540c410780c58094808a04144610041020a91828040042e80c0141d43c4a0000708803211030048800180007031005000405502804540150107401114603031600d40058414200b0241c018800d03400c4041820000c0640240c1402c0c20040c54540340e90f0b1140c101008189034500c01400c07688500c2c010b200b08400e003e4107204403035801c4500803040c02024180c40740317600507104c20f10040380c1611502000546140c404155190031310440d545600c0500800c0d1034080c090480c40011507030108506400100003104080100800c904c40e4a603240701444508010748480e42c1000e011030320142194030758411b00044c5c03108550142d8141804c24100c51816011900c80506c481c02d180541c8556a010425414012040b40308240071983e0f07002d581c0c2c903040008299102031141810621069000201a41c040d074a404410a4680304036504a40600d60104200900000140485010107000d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 281561070 1250 281559820 281559827
    0xd17040911180f061c06030c0b070b040809010e0303040f030c06020303100303080c040e040506060a1406030a0c0c0b0106080601080604060b2b0f060e100f0b070203010906110a 77
    0x440c41d000035210600301440401c0510b41480c5801d0b50a01c0f8580300c1c414224590707120810fa501104403c6500c0c0800c440500d200c00080c0341030701003914030381c1070b13020000362410564003100c00090b030241030403000340c50312303990a030164000c1500385040c490103a843c1041e58804101410007440c039116980311283c80c5040554281c406074110008641042040011100b511541c0e030040780d91600e051403a568039558840468003c4c3d8028141e1304a05600740000e000d40040d030240a50411204003c0d19a51201c0401d0299140510700e81c10034400e00015030000342c02d0740a0340074020242131020440543d0380d601080e0103002d800050105080c007051025659212a94a0741b01030180c0c3e007007241e07c0c100401c0d00104d00502d42d020305800d40124820000d40e00300c44905190480044051004072035162010700904920700407150380d011311000080b248240d14940e503048941405011222030b0500001d003007564040c0d24180c0e055900e80c0680340014000d8441c5a540d20020f1201a4a5450380c40c0001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 281562320 1250 281561070 281561081
    0xf050f100912090806070f090506040305030a0212040f0b090d081902150705030406052e03110604030b0f0901020919080d0305010e0703020c07080304030b041419030507020d170409 79
    0x2c03400c1080c180f205000c4030900044250b000869414001161a00c0345400c0b50f00326400d800454005401060000c2040b00010161000584d0398094400300c40d108039449089005600c00c48003010040d560802c1041d0301d071402803101c01009040410000403903114150194800484050320f550f84044408000d075044c0544444002070f4180c0c0b00c05070418100c002e04501001e000903058030750750300118400250000110050440c45455181002060041c0d030821402c144401d07580c6c55a800c0e1440050f2400b5070444041d2603000c40d118009899440422500186c02032401d10f05640c201b151442c40e580d58003003912215584481108402c0c10030907035509010741a5514000d25080c40014409046c000300c03c0c41d40000c02d40340060b142c1450b841c2d003924106841d4482511400001000710900000c020140d00c16030045031280c80f1108602551550380b010099000050050050700c640080d104000800d01280002c011664484c040e45410724541d152280202034240c0000b0108101309080c0a81d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 281563570 1250 281562320 281562353
    0x106081605070b0610110706020d09090209130908040b0c01050103030f0c030e121608030301051908030403170d021c0c09061e110628060308070f050f1009 68
    0x20340c1000c1140e91222507404000d0f0015105000c1c00709a05c40c054441c41c03918800b25298012120320070740d1140c000e9144c24202c0c2c56200010543e01d004203181140b0300071100e5044000c0c0034010410000c01d4802c2c000d0003410011170b20780e8030030000014102c444c032015210700300b504400050786514500d40136211488207050081801a0940440c010070340041d1180100c0c07200759642540c0c10340801e000c500b469525003a581c1802c80c070b4080840c1c10403000002c1d60507554143c074104030b40329100380c0c5241414040d01c41c0303805513442003005100040c5040c21020040703503a82d540300d09010518a01c102a600440c414804640203429003441c032003a0750044800149041c10041d1b4640d0428078000d02c0990020460003e51005040b644d8010b8840c14420040b80340b050286c81003400c01544e41e14072512107900001e51032a030300700d0a000f84101d61089200322507008100c6444c2201c595500f892904c140301d0709648074043e0030b99a040c0070800f03103c0742c950f00e07269080000c0c071141c003850640c8042407009103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 281564820 1250 281563570 281563577
    0xa0f05010e0601050334030207060c0504030f15020706021902100b031207050c0a15080604020a050406030911090108152202090c04120c05090f1513110301060816 71
    0x78840340741d0f045805c49402c80c50740403480564000d8551200300000d8580f4491101e8031075140402c24803a41540a8000103218a005200303445202c0c1084900740140d0001820003483d80b0f070044001000c3c5d20400400c180c0c510030240c20840203445150481e04045052840300c4e4500300c80900c0341d6810303c55242e84561000f0700f00949507521010a5861071861101c078601e1744002140020300400300080c44011342c0090804150741c1c2c039030b000030b6040c2c0a19203060740429182da01140d090b143c6030003607454141c3c02c2c0da00c0302d08143c98404120007421a00e07c2c10b0f0303869000e1140b605038948a5a041502902e540b00c0100180702c507100000085202c020000b8010750890400101d8554150034901d5280381c04907071740f070541c0d2242c0c1c1442665114640c81086110000034446d402c000800034042c003110b000712448003860396948903a42d980c0314100d0711a96246403045400e00300e49403001c080b071945440080001a040a40c140310b4005610a070400400f05245074100090404c401d114180704811500e13 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 281566070 1250 281564820 281564849
    0x30415180e01150f210b041d0307051e0a030c08070b01030c061805030c0906011404030b0601120207260f04090e07080a080f160206070f03031d1906140a0f0501 70
    0x245d10340410414812072140c0691030b840c0000c401d690380c0d00180383c2c0d0308003558445844007a00034280c3c5e032617000c0e05003207840c0d00411024841001d0540031030300528000c48083c060311041a90121a0b5418011045442031010703c00300c8049072500c1c2006000c1c6119201951205091010160080403031030580307603880703004140a002d1502c1c04640100c2e10750090301c070702681e916480010f803100401200d11101c1c0c1200824000305000c00b505450380203070002e0302c5030392000489054807800da00c21114081c3c40c910010800401d8424940d4044182d0f072002090241030000814100009520960040742d26075291005e40000100501045006055007801485a00c10030340d550381542c0036604510034003481c0494148084075075007010030f080c10750041c029683d909007881e207440c0900000e5000d8000034a0300401c0d800c107011402c000001d0071401c0000f490300140701c81c200c0c200d03240d40101c1291800d496400803000025046203440c05404600e00200703500300c0c0c8801c0361089a4050344000f0503915140d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 281567320 1250 281566070 281566097
    0x120506031204030b090106050315010e1e07080411040609090506010803041a0306060d0618050906100308031e01060f0f020c090c07020d021005120108030415180e01150f 74
    0x1c01290222540b04010ba50b943e40c80484a500500840e80708076050b0040240d4000c40810144030385050f00e652503440c5542c3e45448200f600c50302500b210f0700d0750501e404004210058064154a580a07110b0501c516490526070b002c1410b5400b141d001c41449901c40c0c401c0d804200d414044d040c050b00300b0a00441c14980341004c2c2980300b05404481400380080000428005e40340c9004458030414601410f2014990f5404183c0c00d0984928111500615041c081205d802000c2192405a40c65881144881d4207544a800305035201419000d118511176094054640038040380350b0081c540c2e919080050001c410f1701421600c0035150000c219000107462280903600c05074100e411113107030b0603504d4030355140388045405420b0020019501c8401c0c2c040a180e215800001803980308000317003c210590b60b0318640255640103c2c0a080144904004a10011407040846061402101c00b2402119036589152181820284c01118408000d03d13265400541c00510070b120b044490b01e0105642c4000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 281568570 1250 281567320 281567353
    0x201303230c15040914010501030f06060918020702130504050f0105060109060f05070510051602010e060103030c1703070e0405060f0a090e010b0307120201090b03040819030e0a0312050603 82
    0x1260005104058403080342c0d12521010090301c2c003070b084105040210302d1181c090303150050405d01c9207900081c00c00c158103040e0710545c001c0c0d004a400319283c13041c0e4141000c00c40030b81802c001c80c0350140c00707a09000d0040981c0c0c0303107003d00703090002c1c61170005440d082c182042414081d0804044c0c910b030b81450140003169921903d28004c403413451404174500b012120007268544100b00340a04188504108103900448a0f4030090003103001d065000307142c82002400307a0980e44600320554064008a00401c0800c0c014007240c0d03e0544208000d2130401090341140c542e83e0400d80340c90700050140d80020103c0d007018131516401c0202100c18000205000000800320360960003160740341c03074071040010301d0b4180941200c40d481c80018241c8a02c1601c881c0401d81000b00c0410580c00114a03e2000402401c10000c40b4051034208400c149000760f07840e010304021000300d1220081503620030031005182d6080c06040300d110300c00e5440100c03039540e013a800c206441c0043c0400f8401d402501304a10000f11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 281569820 1250 281568570 281568583
    0x9030b060103180516080f0706120b04090f080414040209030a0215160311061f0b070302070e3303030913060509011811180420130323 59
    0x1007460081420007500f00e2404246418042c014294801c1000480707520030307078050102c15a00382c0c00031541c0c0d00d5a40c0d80d074160340342440d10405000c12858881100c4200c00d9801c650304d8624080d10204010110355152103004661050648105801003000e100402400350103800607401180e0a41c104021080007944130880090020721a211003445180c0070304400056800d104030380061100d00a0035404d0180c030141400c41d0a401c0e500920000071003410403025001c80c805080580d20030814113044080030150300102c800d0f810f40c81020000203645000d80031181c0b0410800103081d40c440151035020740c40304484a450020000c0003006170070192400000d60b5400320301280c0c07504003840b00030480e9004041e95088980c001070380700000f048103c0070301d482030303103194140c9001c1080d030010352007440042c06140d00d01c00fa02a0b405940e0301051403e504601d904016a08046110151151803803100760701c50b6000c04064801030b0760800510207030042e450f0481004c11100800d05940300101034a406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 281571070 1250 281569820 281569831
    0x70311090103050a0f0c050a08060a0f030201050f041a1803062a07060203130213050f0103032007091d03180d05030d0e0318100212031b070f02040b0109030b 69
    0x180e88400007142c248071a0000c14605c11204c10070071015600c0c0390001e0581d8031049030781000c28449808101c1600b013624000f8100c0c0c8520341603150b03460440d40119a103900007810300410010a11003c07821480000029030507001e44038200d5900c01d240100005400413500096100b0f0b0410020040c0c00c0c480b400d0040c603d40091540744225520056000510740203442c8090320842c404402c012070400b16034031a41d103042c021940ca180b0b440180d22214295442121207100c0198903600410004e03000e14560f07041a103165121400d0034004421052400c0300e19845000125124a000c028603040c2c0c0c052108640c034514061440e010800c40030318603a0310f41603001c9020704c003101043d606214090050710b001b10006c0b00300f0320041c01030125090b52a00204850b00c02c010440341100c01500d021201d08040f0380107500075140b0b0000e0f1051604113600002e2044a000c0714007600d03800803942c0400100036043c071960301034070303202528010700c001c4036021034881d41030021001090021400d90301d0020742c000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 281572320 1250 281571070 281571077
    0xa05030a0b0c0307030e0718050f0c1e0c0a0506011707080c0607020d08160b07050301080c090406110c0604060c020a0203120703140309010b010e06130603091703010611060703110901 80
    0x280c8030a4005c9009080070401e419183c0907051001c5913204000303040d01080220200e09100d96112079040c80a0410b0556003410500001c106c9584008039804a8140d0365222201c1c0740d0a0420b40c0000e01e0421035011001c448030f420407070062058450039030300c007503929015030024620a03041c00502981e4207092141688204408a103107011580ca031440000410b600c0000e0a03195499010b40b10a00c0c2200c00741143d415203540c0c00900418802e01c2664100c543c1ca80c004c2218851600601825844c040c1080d660140c403500e00c0781c80081700e180202058020b11004041031700d400d05114084405c0040304c207045410200382d840150382c00103410b10b252742010110550750b52031303440c041c5c40f59501041e180030050404401c1001c0c0030705c194481d1401d03050130388454488407010000c028403445183e22100d001441c40b042446494402d5200003900c03071241c0500d0b01d10426078151004240c000741d1007200020703100c295650034000b0503ca01900050542424890515003404903105070007602c0005042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 281573570 1250 281572320 281572327
    0x519110307030e370c1514091e030a06230a0504050a080a0e15091309020a12020102010b090c04171c0f0c020a090506032112060607050f0a020a05030a0b0c 68
    0x4c0300384605192075065404081910340c650b4481c02c3c026007200c0701d0141c2c1d000c1000c0d4213140d4102d01420b01143d03004240240b0f005c55044526020844501c4040080c1d80c00d4840c5d20181800a07082c0d104040c0313a00381c80b10101e04112004242442c4e0b80e40700a1038281480c4c141010700000400000e080410707243e01c0322a040c0c84040d00d0104445090401000c981e002240140c611001080e500040040030740950703190400002c80002e0000703444801e640250849090302041185060402038a89100c0c0705200110f10480010b00081007458107548101d201200003508001c050000c7d107108080b1a04800907150f2201d51121009007038102c28031120500c99010419107444d072254503060301040c3d00071310744071070240c844022800400d0200c402134000e201382c401404000d402091030080b00301d2808011440c0504d031044240070740b80042c20554104106001500002e50b050180241d03a0340c0000040084408500401c581c0c0101540002e02a402107640795021502d036100103540801800c0c80389a8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 281574820 1250 281573570 281573653
    0x320150714130e0a27020f010e03060f0915070e010305060f0916020c010e0a03020d02030c060f030907091e1515080901200406030519110307030e 64
    0x1188103144042e80121000c50000c40c2c2c2c0090700300e40701d01861840b0300800c4068151031103400480449854250141ca10703e040500500e4041800f05032900e0616089000e544407001083c5400010b9602d500200607442c1080030b000c00070004840c00c80d0201c8101e0700c0340d0601502c094000384005140504154803000081c4440c0c5485040e035601444c041e104940901d4400d048914000c21400c4074801401107601c2c5202035849100c003107104000080c07019200600d50385c00c10540e41e500040490300f50240300741070b00d4240d0703a01c805044030f4100c1e000c0450340c83c80c0c204041424034400350402d500380751802242c0c0e20f06000310481030030b010304205030025521070304e850340d0410b40ca400d41c0301044000000c40002d0b0500d40c480015030186902000a004042d81c2e840c03061842c01c980c2a051030f000e4401d000030071005210f9000a60402c4480098004000d076448154042d01d00100d00c8040c1a4800000c1c0001960f0512411400c4140301d07000d014150703207041c5180030440004800b2414051071281511 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 281576070 1250 281574820 281574857
    0x10908392b0803010b190908030d0e0c040509030a12090b0a0e100509030d0506090c0304080a1809090506071110091401140103120c12050a030b0a0303201507 69
    0xd1915401982c515140c0d0b0352082551000d0b80000d41c04034000a0041c012190300303014003120340640d04040003460031701d654241044020508068440014401c00f181c600141e00d541c410180140903500c06565100721890b8040c0c0074620301c00c0320b410002e20b05234443c408114010401500320704030b00004265401500e10451800e01e40e0402c07804000d1a06040c4203c854002004049107a0306002c01c0c001a90b81c5004c201e00100304481d0b00c40608402c00c00940003a01c41402000c04034202e05200000b005c0642015004020503000a180240d5030800c260600c2000c226650744a100fa03d40712601c50341c10b404864841d058004d5600304a6100d1100c0c0040102034100300d13203c2000c26008101204242c01c0745007000e0428407041c2c80101e910030361140610300c1802c028260a821402100c0178420711001100d5903130000b02c0000c101569440d00c242180c2d01c00143c08001d5000c0d60362600380e50300b1102c2c03810704100c1101000c4281d82c440882d07403464814540e0b03010780c010450706044840e030a01c8101034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 281577320 1250 281576070 281576149
    0x5060a020309090f090c0109050d0b100b030103240b0d0201030e1005040f02011106040b1302010c0501090b01050907031806020d0e03070c080d03020403020f0f01090839 74
    0x840d4002c0d6540c3c108011800c1e020010361044035070718215840050f150005540112603030084c260812002001c48001c02d0105020300d0300a500400040c403210394030b0110184a80003030300101c4400101c3c60b941040d41c3c4005070181031426150f4420010445540000351400c100303448000c0c181612034140c1600400d0500045032640e81d4080180107074500351506074409415158100c0c08608800301e0043c4800340050028411030384007440c034010b5107842881d0080e012222000b02d0400000c40e12410014000703000340c0a101d0b01c02d6500d1500c0b541403400708022218000d0001080502c4c0400104000d001274542c82211a084000184e6400c0c84035041006403401c003944013103611002805004200c4074041c81011900200b058442d80103141c941141a0700c590322010394400c1496000c01c50502d401455500e002905040c03500540c0d649003113039803d04042c514004100300f0001526041030b0437120343c204106100104008080c0415000580e4480c2c1c01c1c0704000a4144000d07000300c800106d035480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 281578570 1250 281577320 281577337
    0x3060513110d090609060e01050105090f090a1208090f1204230d03090f0509010b0a0518040c17011205060708070201150e011701151e0306060308030106081e0105060a0203 75
    0x34000c65243c0e0600340c001c0e1a140100302d403620300d40960b0282c0c0e0881882843c0c161503008148800c161201640c07125010380103004448540110305a0000240350a24060f185a005031210040341c50a11452410650340c1c00d80900d1035000419131108100c210b00888003a6005480613640410118144d01004080b4a040c281c100286003004001c1c980c00442d18821611400115041175031a03000b4858801028820803413244805d0000201d031a002d400984001504864241c540d0300102001178107484454078803c0104200c9281110b805040183e002e024240359000400d202c1843e94034182d903103800810803803c101c54a400b243d410391003901310b9031650010308000045144c403842004141c00c0c0a10034480001000383c6582d0301e001040c000c10f0314202056801441e042c3c5060a0490361041c17004c0c1500c2c2100902e100403000030704034070074540614003a1344119100c2d81440c0c009041400e01811440c202402440c00b80718410070a244541541c03416900f498031601e104206910f58000c6558 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 281579820 1250 281578570 281578597
    0x90d050106331407020f0d02090c04060306063e07061e0314040206090a0b1305100801080613211d0103060305060414070302030a0506090c010306051311 67
    0xa09040000401c00b00e42044440203480c180904201c16504210b014002c1c0740340603010312081001d89094403100315210000382403e5010b088580c000340f03400d18112001007613030308081014485280c1c944101405031156041081c0445052070010480003241d040343c004401031651140d0549844100c0c0100851100c0c049440070313501c545026000704a204005840e641c03810400f580014402c0c0903c8920102980100745c0b680ca4036001e100c9590b010354001600104501ca0004040020100170480d41403e407443d000d001e41024200445180f1000c01482086058801801034003030101e011500965600d1100c0c408250615110000c0844d003102580307405a000e9102208541100003c10840c100d0050b00107107134082e2005404a600501024100f43d022400250020700d295412001007413030081180c6000d079030317940000d1410941160445064006100382304440004100100b908003003400e0611585040c10045104007205182400d401038843c0203a030b04040340e4000f100d0354440081c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 281581070 1250 281579820 281579849
    0x3091203030c17360d021c030207020303030a0b0d06020415020f030a02030d05061504031209050409110f0109030228150e1e100908150103020105090d050106 69
    0x200a801441d141c4044000f248525280300ca01d0341c0c122001c54492401445000744007512480c14201c1000c0f410441180000412540c0880310010410380fa8848010342c0100248040c8604d01740c04018142120010b242c014001000142d40200a03250710201c1e101c000506003035114009502540c40ca24040d25061001501160800541280d1070038000d07a6000c403407140440440d09a0f80b4400c816240c00160010310174812504aa030308240e0b04000020205600c0c191001071240c0a644554000c42d1880c1c180002d107400190080c020750028402110200845c0815440301f80481c0158652544103c204910155641c3c0c000c084600c042c540141c480d646500391030b2a503c449003458094500c0c1c10090400c0005e400c070400702407a00d0319940341d44182d56210000d00b4803003102c406042e0345004000d8800d6040c8180c03905100154002c505541d001011460042914200041550300e4200c1c190204010b00150740c011040b01e40d8803000fa5048030b00140b00b8100740d801403409400c100d45a010b0034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 281582320 1250 281581070 281581073
    0x50c0901210908070b0702060c0313030c0c27180b0a091b050414090d0c1511030106030b0f01020c0f060d14070305070801270b0d150515010c0807030912 67
    0x80f020340380313040c460401c40c0c1a40c0c03070380d41042e40e42d00c07012140c050729400104001481f180c8030500419040348241030140d0140d20590311088840d0143d00454810b4000d0740c4030303010b521380d615001020010340500c01c005000700450440504903038282c0207000514190301040d90120140e001c1a2030740d8000302a0f00a030b07241401d030100703070307101d02c1c0304080c440d6040201c100c08003100074070801e0080c0210401040d454104080c1500e440800c000140d841c1c0c0c06041c40e011350108a401048810b0680c0c1401c10794035810007a01134200c503074000301980591030407040c0b0001c03a40c0009000b0214681150704410750101907001400c0ca06c90381d1108010941098103d041a61201040c0b5000e0344140d1010302040d030b00d03040304441d0b048091040d1100b04445180301500c140448400c81d6925400741c8000c00d01c0d40100e4040303869142844022a40071454841000103a0220b2080d5031300700c0c0456216901103440980020510320811a001c0e01e420000200b590815004412023802418091a0002d14004a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 281583570 1250 281582320 281582333
    0x13080d1e0c091503020c031b12030703090506130b0f06060c03040609090b030d0f050a0903061d060106030507200106031a041a070f030b1503190f050c09012109 70
    0x540c0305140c550740706815441c41041c001d00990f203000040398019030400760f220710700c1800010781e051a40009d008203c441070b0900b070520000c510920a0f92070100c0c03e91300320310300301d480c00000415003026040403580540006a5040040d41c2051021a0340079035074441c0c2001600c41e2185805800851000260000b032898000040c20100c03920288100f0900313508005141d02c44500031808030001d0141505040114015000f80441303500c5c601c0d000d0360740c684079550b40040b10000d0015007015828a414072101540c01c12a00c1d0141040c0e1805103d0383c03d2000010301100c0206034141c842031841041076964034030035440701c0e0003560090301051040b01c0c4070100c0050403400340c4041c0c4000a021203d043d0401e038443c0d0f8503000d070300d496a41c6a0f9654540c00200c0003400c0104c511170b03216140340945442e140380c0ca809180100450490082400f0710759032640216036880f65a00219801c00d420440d1444015003a0740c80740300203082107003510704203011403050300c01c41c03141c1415094603200700401030105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 281584820 1250 281583570 281583587
    0x2031f06060e1503040b0a0b0d0b09060a06060827060a020429030622050c03061009030b0a021b010c0c020a23120a02060304050a060513080d1e0c 64
    0x1e0342e4036041c2c001e900e5201449504008021899a210b100f080800c0003d200d03480e40300ea00c580401ca001810100c04d5000a1089001205c103032154403141e402e01104010501101c2c0d00401405030800040e460040060700c1c4400040c00b240c05c1e0703000040c400780c841080081c01c10306200350b007094031141e2030003082c00002074020f401803894110305803083d06015100d00b041041651400000c8500b0b6039202410491045103440070f2440300103010501041c607642c6802914010b2140301c0c2c7d07180c3c0760316140040c4032034001c1080300c040c10040d1401040000c106e5894501c3e811001c010000740c0c2e2180170860000c2d144002000004041d03107415407001c60383c0c0c0e000c4452002d4038400c41d8820384495560603550030680311490003003071902d840f008400143c40d03c403600c1640e220301d80069604c13249031500000c6668200703c03820f403030503003103545803130104122481030a6000d91070010300c0981d03041c02d803100342d40c60060503100742c0d03190390b10710b80f090101803101010303101d42a2007102030004000d1004010401d08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 281586070 1250 281584820 281584829
    0x60103030f020304081504021309030e0103050a1a0409020a031202070806070809100b0114040e0108120307020a03120923061006020307060b191d010e04020f01030902031f06 76
    0xe0000440141070303440802101c085510280041100c5012a080c2000020300500200d81c421058036142078449451300803421a28080e8440e081d000c0e00b24400541513860040c00588454907102c125020b01e58040004a50101c00303407000280d03011544003042500001e500043c001d983c1300c0c220285615070029448080da440d40301950050b0700c91a800707541789802943e000c0031725006240200051510384d07008591000052601c003600142c00ca20f4046140e0041e04002081d0b410322005009900e001c01051004c02035407d4a075140d4646000b00a48030403e40000038108864078010203151212500041c620035003101000c0c0c109120405034200074802808240058013030b1400144040e214104280100c0d4460313000f6501c2e00c0039941d40d06005142c65000503038080d000844461401c1d414840b02006040d0680490342000741c200702090032500b0581c03000c07803090980810400182c48070209544004002c1c00c0201d501c250900c000b034200220f0424064411849074500c1042c05040e400070411035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 281587320 1250 281586070 281586077
    0xc06040b04050c06070f02010e03100e010c02070f05180a1506030509010c11061b1201030c050a0803041409132f010813080f130b070303061707060f03020f040806010303 74
    0x1c0c0f04180041c40c000c0f010003629603a5a016104c0155000c0d2180d00d00a10004003910034001103044000100c580310119240390369501c071502002d00360104410b10141a101400500031864440010007100c106841500342100940c0464240310700b40d0040c08020b84501e2070300d04069111640100100310880e01c0c0714043d0b08180400c80301d0781c010783d0690300822032000603281e155215003001c00c0c1810705c103424582e40b100c2000489010050800b000c0d005e07601c10700c400b1000b1403401040044001c81500704181035001008100101264484410700611044d9403207001390760342108194a03555400006403c102805010104614180002042850150084141d500070440c01181c80301c10480309000c40360030042d042800300e5080400381100390704101d0a0307803034108030307007219004450b103580b0080c0c404401040900070140c240c0110390140042c1c1c2c80d900c007040c044a60180e03895903603208040500c0307103604074880e14620030340445140304614080c0c1d86c2e540341e071030840c00d546400910083c2e000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 281588570 1250 281587320 281587333
    0x191d030304050a0201080c0310030204050919050d1116140f0d150c020106181a030a030305010602150402030316060b04090804050901090207081e160302031207030b0102070e0c0c06040b0405 83
    0x7ca88090050300e01640075949841b40440c210b900f40401403078050070142c0184155656000906c5e0350b83c400024035882103019040c511020403020b01003840c0600c080c030554011814040000c41e0003038054046928102441d5001c0701484046855180001c0810390013400100c45d940078007644038102c64038007242d00402c02c4043c040710b808908032041070040034099a0504080c840e608035070f8000720111201030000c0e28030031200a000a18004800328100d01294640e001000b00c3d60701031010300310388110014040614078060340060380341d10522403200c1240c2c241103c15030520a0b9a400801161000340c01003001400034107040060350814802c0d248201258030011420f8070b254001d0750704540c1d10000d59070804000c01c85886001181401030644004180b0a8810031400c0e890b251080d18003a4003d55514003035007800b0a01c15100620701c8050500749007402d46e281c1d0b030001c5d032081201c40041d00070141d500c82c0f40c000712003449040d6420089100344002c2c8824000c05000030b0703004a100703030101d0b0503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 281589820 1250 281588570 281588581
    0x1104020408030702010311040e0f190504020a03060504060f020a020312011224020c1c0215060a09110c03182706040e0f06010303080601120203191d030304050a020108 73
    0x6034891401207400300e800034030050b00154020340212002c4002901c4880c107145d1031b00c0c13418114403812101d0303800d240845024401301c030100c1015640807118140c003d00192506401003000303e0301502c0018103250b83c80c0c0004060100e903601c0f203c0c80d0300300520103540e01c15040320003d60300e401c4000d0503101003080900004484506c8040029181e502080c0034030551564620300030820f500f003030b181e0880780c0c0820400b105091709000c0c6405400401e0540e8580030400c4000929104006800303a0380603a54005211495076001350800490311410b00100c0c0c002034a0201e2030583c007179600310f1b084a120100354030039008000110b01490300000e44280c1d0740d001c402503100c00381800d65441e5004810340080451064181a08041181d0043e40d084650344c58000103030a02d802001da0041d00051442ea00713001d921360344819818801880404250709509000014010b6090f040c40708401c59036460501c81c24074041e6914480c039070482d000603a91a446d250820700e841c0e038031800040703000449100025031f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 281591070 1250 281589820 281589829
    0x101109010f090510142104060b092e0f03080c0f0610030305031003140f0c0d03020606100903020612070f21050411060403030c060f201614010911 64
    0x400700c8400401e68078480802c4c00c4181c420040c02d0b12030002a100800c8802d40c020102c0000c8048600700c500c0700241071900713081490884503c541864400d05402c42881014182a0bc001d02c0342c0301380a005031801840000b241c1016501d03039000e58055492500004140004171015204542d030035019544030041c201c07060351303d5800403601d085940c03d00035020300100b031141000c0c1d80c4c41034040710302c1c110340c41e269107450361820400003158890303600562071011424424400a0f03032050058907540d0900c0303601c1c2e80280d101c5100501d030b0350044201a0201000c0c03480b594405008640161409540c4da1421001d480607980440f030301804a0f0b06c59a8441106106201a80c01c144814400844041407107820802a00300548152aa40015040302c455550f829006000031480b9807034541d62100386151020a07a04804035041d42149030206201d110803160120085000c0e4040e01140c0d11203040ca408032403c40f8954000d003c1c2040a10320400c050015031198450700d0040001c145050300310070400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 281592320 1250 281591070 281591087
    0x8120106030603150903021608100606081306090204021909031b0b0d02030603010f0204060e01090b12070f021906050609091c050c01060e070302040501090b07020306010b0309101109010f 82
    0xc046850781a2111001381040d4806008640b192054507602e5010310318012007205170b5000f502e0242c203e840721444c550038a110303030402400c40d030524088502d02000d41620342c644a900141680f40c40f850034130308655a40e4100c400e15040003c00c0454401c5684004108046902049400e240c000c07c061050303040450f80f0408941c0302c80401842c2655a00c103240107500094100da4040d901c84e030000f44494040d001400241c081aaa5803400c010300d600010030030845e65125405000c0204900c0802c124503401095000510703003455120503808410480c6000c1422650003100c0301119110f604002842d0402030090340c048a8003030b81901c03070350a4141c90307108064124500003501c035811030110307004e41c01400004139100c00002d00e030741d071fa4640301a03040000c481000009034005000d101d6036130440c41280107000700d47d90b45ca0070108294003095480c04180544409140d0100000b13000c903d0800c0814100242c1c00380501005802e0a00380c0c5581e0410751a090102d80c088503901c41d01d030312035101e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 281593570 1250 281592320 281592323
    0x5010507200a020f060c010e0a08031006030e0703141501180e030a020714010c02130f05090a0506040321020c0c1509010c0b04020604080d020a020a0e0705071b1208120106030603 78
    0x84204d14601001c01c26070342c3c00a0a5100203540b20300c07c0b000700c03140c10701c0f8042c4e88a0269110741e03507d01e448081e002c40c201c05600404103041c43d258204440c108001240c0b825280d104a03000440c101509105160a420040640c050161080003084a01c0d00c80207e083c098a0440c09120760100c1210640d2a401082d8071a00182e100400801404036001c6a038028598181400d1040154940208100382e683c03103900e4211030707290707041854190b6a80c41440d41c00300c105070141c00c4003129595299114000940003504001d600600144422403e540484410300f800300c0031503480e04224030700d580302e100300c26010f272103500c84041d19a0320f85ca08000300c8081d168160368480c02c20b20180d95070381d00c00c440544240d80240c42480302285902c020006112050060f80040a10190301e104000290340c03290003040d0125010818088490b41003800d8a004a901104a00d003001240c00301c00100030042d4400d800c220140c070054414014524020141c100c07514211003426a2109019401e0364031500c070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 281594820 1250 281593570 281593579
    0x2010f110a0e0f130906020301030210110d080601030216050c040507030506030a0b130f1a070507030f0c0212030f131502060c0304060b100918140117010905010507200a02 75
    0x59540b8022507400803c07040101301c8010b0718078510980b4100e0701c40e004100c032100da0000c0140194a0301044d00d43d6117180710314080407415142c01310945c84206164640b81480004004181300c0d83c06031301902c808031103880f00481c551805040050340d034010048028042c500c2d11300030a54507882030154601c40c400c05001410241c0795a0386030301b00264000e0108c448100c41026201c0020048881d225040e4001d10008036007068401302c3d10800840a0030030024440200903c100003038100b07103004200901e42c103206181d10401d00114858440703035802c00400703001c00030b00d4401010b103c45c007a0015a00c0301e0b800d081e81c980c0300d041600700d5822000340940581c0c4560700240080c1c656000540d403241c420000822007000c1140440c503120315254401010810620301031041c1c4424446201d204150510b0901c1400c0030340c6440c4500007011301800c500f25032038905241d40d081003500440f54055004008004507d06594010602c50306c0c245261004040c560b455581d603980012800940c540040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 281596070 1250 281594820 281594837
    0xa0f1119120f0f0c0615030b01030b0112021c08120103050313050604051f050c030703020d0e04020909071101060b0c010902150c0303130f050d030c0e041406062802010f110a 76
    0x100203884c0200042400c42d001e5403201c030142c0c22045800380d920003c41c804c80d0007a00759415468142004041608040710790030808102d0070144e6191080e140c40600d4240020810078000d0903d0190f500c18007412a240382c5902000004118000004009118961004c120b4140c0c0b540c0401c201c0303214a00c070f0254051103000741b55007242d00f100c140740c1000080d07082c05481c00444420703250854200705401e82c05a00318400114481e60004052408c03400111021032401c5000c0300000c80050b0041c0c103220030011400c0b0385001455096210170040c11030340d03840903241da4036468091701808090360100e0113803000c441800105034941c4141d90052100c023010b03500710764410800c01c42000c04d0803410f4550003c1e562014000c00e40600032030103114410794000c501600d5140015000ca900404094010b503d8415403448407035100007421781010701120080c0c0c0e100c0c86e80315080078a901d11a007004400d007501e00409034454055100404d182c0358008184101d64094900c0c15581c002c15840001103014034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 281597320 1250 281596070 281596097
    0x70b01150201020c1608150c1806090a030c050f040203091902010306090609150519140607020312040f06021f0e0a1707170c030a0f1119120f 62
    0x621040c0403500152000504120520715003d10309614507048408410b2220403d0140c00814020310420903c9207240080c0d50030048446c9080c0d11807081e40c411562814059000d040d581c3c1401c403454104010300300302d64151070b814070224049003441064031421190000b115141002d00030399100e0300c1c00d603001d000c0041c0151549418490381302400c90400d40c0d241e40115541ea5548030f444090001130400040321031b440c0740301e0203000b070541d00054882c01c05101c0240d00708018000034030544028007040c0031f40903420000f041e003501800c0002981030007401350030754907412400090700440b0b80074403402c2e107510307a25942640c840396030701c500c044a1032812070300b509075400a8016603440500502100d154440980301c1c45004142c403054078a0f000800941481071100380410301d030035500f0280e0101d26001511040e00c0d641d00c140302840e0700b0301005103070034000345d40154a00b4a1106040b82980c4020149a041000e880074200c0111008540d803a006407a0038880c0800744518881c9031544c0c0340b07900c00c0d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 281598570 1250 281597320 281597339
    0x2906100e12031218010e0705061804110d020a0f110703110d0c08010b03010b060f040509060a170d09170706120608010207080903010b0105030c250212071a070b01 71
    0x4040500c2982c442044000050f250b410f0b4a00e1044c1254010b160302034002550075400e50b01c40151509865205640c1800f4654454044400104c10800754640ca0190b1502103400b030901e0090780201c43e41e000c00c01d0310400000750010807107804103a580e140ca2440698068a000b101c040380030b07555a0144c8000d000240140c0b00820b4070b030000400b80c8402c04a00d135110010541c0c01e0b00544180d075114100b00c8020b0509000e070b1844048210361083c10034040403d01102030003584509440352090324081141071b200c0100f0040981245007046000245100040c0d9517009015200c10005030305200004840b40d00141e43d48064034028082d20f030341440d01008503400980000c040281c0c541e128000112031809100030f022041c401c0344001e4a5400090070507003120108100c41d410701c0405c10401c03040c8141c07802118140c000303950240100560b00c130341c201c0e11500342d50310003508461608890041840000303001c404550040c0d51503070043c0e0307070a800b1010070302460000500301000c01005000c500c3d00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 281599820 1250 281598570 281598589
    0xe21070303090605030930031021030e0904020609030a0803040201080a020403031b0303021605061e062101021314030f0705010f08040f0c17070503120a0e010c2906100e 74
    0x340d0b1100c9514941c100600c00b071030382d8405c6d274815041d0103030301c40204400c620901200708152600f0616458032556600c002e0b181400034180a4803c8420100040842d510101950251900581161019407552a001c0d04a41c02510141d01182d0749500041e081142402203800b07070380e4140e960650200481124184020703844404505142c2c0a02844000004500e10071001078060002001e060400c400841c580241294010822201d410104000b50700c4003903c02c20b5480c0040d01000000d040c4680311740c02400781c01600c040c0c2d0010000005004024207034400d603251411000d0f1a46d285807001c3d0702d43d13280d465104071400714a10032880800140652141e0b94040d0003a80041000c4015a036045000415608680280b8119001d00c000c02c00040050101a06040c0d0051201348032202208115004840380ca04c1008494282d106280c1d100e081c10500c540d83c484000c070f074500e540750590000c1c030f141110803030b45e1100c0d0a00001e865241207180801c01181c540c0b9003030010421401400790425 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 281601070 1250 281599820 281599873
    0x206071e1401020a0e03031e07050102041d1e04020f0d0809060d05040b012102040c020c0901230103060e0109110403050625020312070e210703030906050309 69
    0x6004541a02084101c071519212140840c001a5070300b40d280400340ca0f00c00c0c07442a0070700031790041c4a0b0595440b002001c3c201c610303400035005034844100381780050191282c0c6d007107544403680d041c0c041c07046003501041803405041213084064403c113021980640000003168083e600c080f4080e044602c0703082c0307960120b1010b4015034a41d85800806804101c03940c4c0000c200022082c0e40303004000038421754119480c0949140d03000300040304141d1001e8900d4040300c030030203480750342d8540c1c801034214000c100c80710440f00083d01200c500e41e518004030050842c40c00c2162099006686442450742c840d205100c1070303400010300001e03240d080415650040500c0b1540f41b0741000c04006c0400481d404000440c8500d10240c512006207a0f190000c4d100e0782c004461070029980107201181044040a00c4254003085c1e034a00001c00c100c0c03901c006500b806840c00c50840359071549080001c2404080780f06816640282c951a000d103942e220201d4140c07200701c1c2c082c80190880400d080d01080858100000c11b03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 281602320 1250 281601070 281601113
    0x15050f031f1130060604030f02060d1413050f01021c02162a0e0f130c0f0602100507050a02100902010c080d0b03010c08070e010c02120d0f08090703020607 68
    0x4483c11028112190303203d0740c1107030848400d02d4052103101881c2d06666100200b070711120705140c65039403142c500b00c4141350020322801c400b19280300c41400303960001c2501240d441c0307402134608160007000c0c8484641031054a0324018030115100022050086925003021811038000308414a0aa8070003034000c1102d4541003450105000302140b000c00e00c184242078010306449105071101800703040b03088681c0c0198051031402007001040c603081d401060744070b414a623544040c0b040d145030504894980741c0101641600172403002c0b0b6101e600140d201583c000c080000c12031511104070988441c043d00150400580c8480108204105035401402001d8418140000180030950300c224658020004248100381d40700000071040c90309010b030091250a83c10719507158240b0603402040050300210050600040b1007803541191074411000c100344101105940f000c0c601d4000080140b400400c2550000c1c18a201161003040045091001c407a401401c052030001c82d5596031403d40b0800c43c0ca408030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 281603570 1250 281602320 281602327
    0x601080c090a09061e06090606140c0c1c0204051f0b0703030608010c0507110411161e0308100b0c15061c03050301180207020d03051b0115050f031f11 66
    0x1611a014182201001585040d22072945c0e040d440c1c02c4450a034400304203503041010411450350001610040c029031411429582d503203e0340c110340b500704500f56950b00b144905401e16080c900407030302107000c40e20895040c41203844180c01d905000c980322001c0c1d201c5041d13649042001e003c00d00024217065210741170104005030f8034140744e421905c0344a01c103008140002001c008210500b03401241d640d000b00d13010403d8440021010383c203402121440160090304041080910081200102d00841c000d0440281d002c0a440c2c02020b404054a01a040078825003003c030b0104400c0041d1408222014001d10302a0002c6451026040029144030f800c2607104000060004da421464880c40303000342c60742c07a665450500c400b0381d0a0b040042407400c252040c40010010307552000840107841d05442d18075150b46903071480303250b02c0c4405004c501316586417400086080a540c60020125402154846005151282410b1300e511001384810383d44106110112020710f069440b074a80c500419007003505 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 281604820 1250 281603570 281603573
    0x1e090f0a0501050a200a0c0213090305070309060f0e040b0604080102040b04081203010602060601081b0316020601080a1a04020406050d111003050f06042d05090c01050c07120213020304081b0601080c090a09 90
    0x1191052b007010740010f0400181c0d45e060640040c4014002e00d49071509410845444900510305e94040351002d208540710070344020a40c0e9504151009031035100021980d1b00e030396070345a12603988548581119401810925519a00c16005580c100c1e501c0d50007802c8240ea502c801107034260340081405003805912102180c02c18946405584501590012400d1072514184040d00c0d21005902c81c80072607001c10840000039000b000b007114403414001c03242d481a1114030009002d4400364001c160480300c440045002e0084220980c0081c003002d80e503007104001d01c03c07000c90603a04201d17540e15500d000d50021420504295100040300101406060711502c114162007404000d0001c402415540724018032852044c1030002180101090074418a04000440516250425885242c41c1f020a89492406544425050f03c03548124080219a41d140629020782140c2109902034549808842101560303080000c0030b5041e10444401003c01c02110020083c1c1e280c401440301501c40d840d10041d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 281606070 1250 281604820 281604859
    0x30613090c0f08010b01091a04031b0e0c0a120b0901030b06030a1707110a03021810090924060e01090b010215040c1d1e090f0a0501050a200a0c02 64
    0x20b000e44014030001c25540251000100703403003100c1c3c2002100d8103020a04192400d440d40807103003140d1703000000344400701d5144c0505507490040d9100c00c80010b015800c001040e081c240041040407800c1e12050326038242d02040d1012030b050f07010550b4020021200500109003449112030380048010120ba52002d141c2c0e554032201460043c4d41d2804503004107403a810400b660080c00c0100c201a41c250703503202c1c61900000c0001a54500c0706e909580c1034004103031001404405030b0090f000c0781074180003030609403800018001402130f103510298145114180c1401003401404c040321809020780c5816401d10714410000d00d03601c5002810341c0305200300d401400d9100403c3ea0310071805030f405000d0251a00c0c203100c88456100e20b80082c609a1402080014514a090000c038000c203450541035030341e41d5455961415070789014840c200e120300355114040000c1500154420f107c0351a080c4400003640707036440700d0715040c01441402510305100c0300b01002e1081c54410410307400204554200e90301980030307e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 281607320 1250 281606070 281606099
    0x4170307050a081c1112040c0312020a0b0a0c020a06180218040203060702032502010c0602070b160309030e0603070315060314071d01080615040b04031106030613090c 73
    0x11120050003048106402e840034040312507500343d04d90140182c2c281201240c513035126064111640c240000d003c01d0911a481402c1405560310a103249039480c0c0e0540d0207544c44a442c0011201d42d110360000503600c1490380510201e0746d00b1a0000e1041500da50703190005842280850482d9603115425800940d4401d92407450100700c2044400581c1450700500d4149680101110b081d0362041000c080400300612400382612400f54a00214032400e100490b1164101c01000c1c0007580042034507400c1c0407861542c01d001c1c0025038144205580f40c0002a0300380c130700c50800540801e004505d410100d080860055900200c21701d00007400840701031068004110035000640003d03036404110340d84070610204150002480c0c1045200c44110784800451072103a0708155041055030b030082042500c840041d40c03c10415040c4403902d440e207404003d03804d60003034401540c00402c04403107051182498011240500c6c006004002070402015500b009403036050000c4400600b00040082d0a9000c1d2104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 281608570 1250 281607320 281607323
    0x903010c090f0e0106080408030a060b1804060f0602031e191e050405090a0f0b0406080c0a0504020705030307140903070323010e06060d0204020c070806010f0b0c0304170307050a 78
    0x1c1040c80ca00303100d00000b601070b054100303458001000005100c06504502c50590195200034190390f2599a102c5081c0a4221648000c0c580a40410b196078018100d80080c40c2c40c00060349d041207499511003980350104100e00c40c40d005a0800c00c00880d4654440f900340e80f0780e0004619451030540c104900d00b820444201100c3c2c009184a00c004905030911444407465000b02d182850070035042400041846030040d1084024541e10302c69115004810b4100303511004004008018499490b600541c4510002d180540304060b1084082100d1501d031080e9107a40340c11000a5046540300345068501928600001441c10820702c034550181d942000103d000d14414a441c0b0010403e058040d045540f402c10500000d074145400401209800260700354001400c803000010500c1c1800860002d2150b466010307040d00400c1008602801d00088180c1207400d540740040344140e95900e48025070140e81c0145142c0d8004000c00c10103101041080201c00202c801a64585540f42c0d41d003510f8070340c01a40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 281609820 1250 281608570 281608577
    0x60916111006030b010b0304030504050d060906061403010605040e15090a06060b0901030e030a020a0305090a031a010e06030304080a12050c030309070501020709060503100906140a0203090c0d0807170903010c 91
    0x14284100142030300c130300d0f0042020003c26411410241e8000e8114081c1e800755900984911001e0800c1c00500d1304900e0a05400910402c41645c40d54410003031041820301c282c0c003940c2801d800180909040c824610800701141c05004042e000450b00c2100480180c0b00004a10070700009030086400d80c455840184a200340741c641e1205004005010b40b60821140c4a00341c0040c0280707900340b600844e40042481d41841c045035246404000645103007180d41014200c1c1c00040714007c1c80c00055032106058451680e04100181d030340104240d624032444c0100140c1c6d0f00200144800180462201c0b4440149420607030b04000c0c1c000c520b1440e6400854082d1042d03400481c0401065070103208100103040d0602c0c091000034181404039130b40300707500442109443d0f514081d01c014001240e01500500f556107145900a04014502402079042135031031480a008010000005240c0340364407002c440c1e4031200050811540d51103141c1c2c0b6407007500c0b840c20728120400c6154240d590070702c42d0710040095030301c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 281611070 1250 281609820 281609831
    0x60c07030305010509010501021c03061a030108160b070b190216020a0b03091f0b030d1d0301090210081819051c020316060b030303010b030103050c01080609161110 72
    0x30010140d86041c1d0115000305450401406581d80c04604510384400d420034559003004030b440c0032801030003070381c2c059600400b4140800710340b40100307801181200c4401049070b056410960541116200502c00d0207021035080041388006440d0303080b1581e0195078682e485002c4e00070b010703144003130740d0080c000e0243d402c1d41c07400040c2c00c51070050b0201029050b0054800d06610745508095a20143d01d03040c6a4010401c2d0781000880060b070300210003c3e540501500d010200e2044040c01500d42c40808225002c103018240c0c03020b00f0140701d0a01d40356001400c00c1d1014031044000d6904507406020350034103107600d440d01b818a880402041c1901d07010742c0071088007910b6504181d0304142994008141a0440300040c1103070075400007d581d40010814503041503c500b43c5400001419110100c1e07401d400044000240381c003039600038504036809542611507418549004407078a48040740c06070741c0b101945000c208806071180c030003824250b050030403500209000703018600d085c0042d40c60340c501507280c2d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 281612320 1250 281611070 281611073
    0x509091036020a21062a03200a11010504210201020918060604031e11090f010e09030d060803030718060e1905060d0c0305010503031608070c0305060c07 67
    0x290100c00c808501d0110402101e5081e40c00219030414502c940282081e01c6403610f0005000100394a20150348500d00300000c456005070b20644891030203ea42142e181c0140c58200c0500a00407001e6601c2c5030080a005036514032100313800c54104100b02000c00036030b0220310a00c41d01c00d2141502603030098820b00c504075442440e0000c40e03110276038504216401441420708586640910300011001c1031a003510b1b41e40c8483c081040d601440c0d201400044082c80a444920301c295542d00c0180d00540c3d880b83c1e14011202800000d072020f540707410394500c25030300403c42c03101480f0002e90403190101c00c0e01d280c0751594050388141c0b00c1541018207071750000414821035a13004044201403501c80314504200c2840e1071005461203440c40c07210341c081c607100e03405201030041810520014103001000d468842c508001703c40700811400c182003000c285058008101850000281c4103650703400c10900010800c145d42d55045500880011506001060008030000301d0074041684503c1c0c90318035254846129 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 281613570 1250 281612320 281612381
    0x5071a3705060105120103020d03180e09070f0e0a0902060408070603020306040f0e06010b0304030207030b27010203060f06090a1d0a05070e0f0105210901150806090705090910 77
    0x1910b07660501c40e0400100c842e62640d00403080c1142d07012175181c0b01058050400381d407e0822803250050707000315a54085501422112180d00521540084502032500c520500c2140c48143c02a100b900c54402c00080a00400d40c0244110520240280b41880e643d0036880d890325a01d60010401f0039008800c204441c200ad201c1d000d1210301c00c5000340510450020081e4a0340818001e00c1d100c10700010028045c14001c02c0f028000319800403a241c0d81c1d01c1c001d0602007001a04aa003a1145070a81e400281030140500a40f40200d1004010052034500001008002e0b0b111700443c0b0f400c01c5044400090b41d00107031010755030700040c0340d10024081c40c0000310782d000c642c40140300034180000c1c5460385040352a1f003401e41810300028201541e4428416501117a8079160312061700903284c5810410400b000190020801a10b442420142d1a5110019942c40b8103048980d040203078014801040036190110142d0780216400c0300740c43e85114040c80030b4098404500c04910044845608403038610407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 281614820 1250 281613570 281613581
    0xc1710050901081029100509060a091d0103020a14030f0d02010506010f0201110405010516020a08100b091303030510081c0e030105071715030102070b09010b0105071a37 74
    0xc3c0305c0e21000d070031700100580e100d240c4030348003458020700c084600035046174000c0d01110740020004146545484800500030040c4100d0301486150f00c06486140710350281c440002810b80364010302c15012103080850a0440c1c82007544165072600c03540c1c101d000f90311030a0100714a034507800e6001003841d00d03203c40003414954030300c441201168940001c20300318484102c244c5007a0307036091030419940c11120301d04a501604040001e5804030343c2d02400108041d001428902c070a003005010b0161840000421031600401c481540c10440440300c0b40001a01ca07609c400e80c0b001c1402da48954081e05c03038107880d240c610442518410164884600044941c10002481c10082c04030004d210b42e28065400818150000540200c1802440040f4540c90907112078051042800340003151600d0080c10160252681175600b401c0e2075103014601b8401d948240202c8241503080132080b00b00a0111132034064100000340f05000480d405a6184d101025508d541020000c10340d440c12100d20842401408445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 281616070 1250 281614820 281614841
    0x2060105090403050d0902040b04020c0c090109060605030c07060e120919050105090f01140a051206040903020a0f1a010303030c0908010203060f062d04090f0c17100509010810 77
    0x4507100401c00003c0c0d0003070449100d040c441001003020f4100c5c1c4013240103000040b250340d40c014004120382e80c5008002880110500d02160550ba0076680c0b9025082164024000c801c0018030410018400310b04e041c6c02494003901c543c00c00100d5010031601d4908110f044541c820500f000000c980300c051424004c482e00301d502e890b4205030420315100003c7d0281c0b0039100494029100e2002d0714181c0c0e8025500f0390003c040036004c5540e00d41c81c1f050000c040b07500280500c140244d00341e001c24443d0030b0a00c074040a40b6031680080c01c96040c17549a4940030f03441e200702202d0020081c0520381c0c154110628aa0085220343c40100d50014400b401402d041e000c1c0d0014a5560310520400c1542c0c3e80b1075086861980f03041e15020b94445585007209100c1e103425100151013400b41075002019080743c80144100d030b588103410090340c600b0f40498070643d0318a0200318001804807a00a5914841c80403203508600700d82140d404090355031010501020099000000c43d400066030108070f41542c1c000c07050b080c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 281617320 1250 281616070 281616079
    0x306110a140306180403030f060b0a090807050a033e011101050f06040f0b03030408031903020304030509060f120a0f1d0303071803060207060207060b12100c0201092102060105 77
    0x503d400c40214010900c40c8500f06000600704000c0750605000341e200c000b090096034000c0c0155512745241001e00da104a414100003100300c0c000150a0102041c00c9040c0d410080000903100d01d035464050941d000c061101c10b031500f201d41940c524605148040d03420351031030b2041c50500d0501d8400585a4400841c00d207103c3d9040c042000f2140b40104ce525501280840300052900130001d80c0c20018000300542d16018400042c0110741020700101601c201e00802d0000000510380c1e4070202d00b80d0100740c0f00100803d90510648038685441005047e90201c0c40ea903281c240f1005803110034150400741c0c0c004441c0c0744d541c0d5100e501100c19000c2d074680010055507108007560b0000d2501e035039100c0241084104258141034111038070f01c6550740802160890025910b6101c00e041103002903220308000c075822031400c46280f540d4149141001d12900d41040901201c0c503101c5c00c500060450030b004803045540c1c0304c003045d0010b00d2403601e00600c00e90040c2c00c0c01e004caa48880192416106800c482d00c40e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 281618570 1250 281617320 281617327
    0x40b0a09150e030d18061515050a170717060d050a0f02210601150306081509070b0705070f0b12041b261e120f040306110a14 55
    0x81020110301036507400d0906000030780c0c210440c1040b4154010020241c40e8070f07080c0002ca05041d48a1089400341500440c0704000044910302c070080108070520601081605020f14001e105004902230084402213040011109010911001c0b064000321a150003094841c07120100d4090503940c0b02c0da2045003900d070090714035580c2d158260b8038915070400500d00c5a41d04031880440d140c12003442144500d04201d204965000001d140d16000709004400d010308840900b140054400d005250490b10500302801c0a00c11307000b090950490000d107954128420ba23440003800040c00001071a000d805a4054006241032900300e1140540503808059150000c0c850020b501001511351608507500040304903818000e01103144034084940d04c0b5032903c0341c0f078440904250700032507000400030000d0030a0f2001c1511929500e02080d940c2900c0c03c500e5806100c2c406807a100d0b61009004100c5d404803040d0030075650740e4409094601c901d200144400780440ca0300c40700c2d60801031030203a01d07603844103032804e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 281619820 1250 281618570 281618573
    0x3070c0c080f0c040506040e03040308120702011406090702160f09051005210703081305010809121821030712090302030c09130204050106030507020705011103041214060f040b0a09 79
    0x55801d10701030f400b841991784038041107107640d50368811062110204152522560749003492034180e0002200c1c441880c0100340010041d0344184600c291501402d81491940d480c0e4806024003280014041c50039032040e4580d1158000c601c2481c83c000f480004204029141003010070400e80e00090401c1c0d848004280c400d020f9903495105a44040e001da03004803060007550300d0100e282462130f5002401c001000615547c001c030b015848101965001e0300c5801403502c402c00003941e141103041d0022000c500c144050000c1c0303c017028482c0a5400300801d582421049030400d0018041c90900100540d40002703221410803045150600c1d4990140c20498641c51854002c60b440f030200b151342034409c0300c3e40b8001034296403101003d2501039401404c03c0115607100e540180007490309039200009807292001c00101c540c40340c65044a07130002003000d58185880c160401c2204820300d003003180c550046d0f62188495a004001440c0b00300307a403600884c501e0505042c030150781000548260f0b801402d10f0790303510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 281621070 1250 281619820 281619823
    0xf30030f030103062d0f0e1c050a0e06120108010b010503100b070201030f0f0501050108010801090305041208041802041509240e1003020c01050709031208061503070c0c080f 76
    0x741181d4000c500480c1d0340f06440710b80e031005801c1603d4004404020170841c50039620982c0a808410300c000c208002c401c821a11440e580c2015100843ca0b03030440780c5601307000c0ba1040006d8002d02500b400c01048900c038060000b9090780200d0108909405084010003004c174007401003412075a03080c20541e1950900c0c010140c04003100c0d0052001d014400140d100869100ba0b01803280b10341d446a0401c01c0810305406000030380001e1250720700140640001050140707041c8210182c10380c0c161945841e00b031408280006181c202c40e401c0c1d0380d90006110004120380d102c2d115500380c1c0a494030040c2d94900300818400310048903400340080000034041800302105e502007c0c1b2003e12003543c20104058010000c49800652607902504103c083ea0f400141c10f425130050698461280300034085540c1e44001210101d51a200243c904c40044142c000700500414002d6000400580b003041801400d0705900c840768420307100c200c00542080c502c101404007500140018009540160107404219105030b03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 281622320 1250 281621070 281621077
    0x201c0c030c02120c19150b0a120b0c160506010312050412032102130602060114060a080711030a111005091018050d0905150c0712020f30030f 62
    0x1a4800e0b80001081101d900c0e0402c8010885c0f2816052580b60b43c01c18a800080303882400c0780d190502c0e080400400407440c041c0b1300d050541d420010110038000307080d1030b0034600348009004070b9441a001c001007041d101e400d50b44820040d000742c00400f4154914540f0003844c3e02d604c1946401c201c000e2000b44810150720085c1c110260301490041940855038030040390052020180e0084144005161100c40d40e0b4500d607407040b9006502681c045a0740c0710400002c2c01882409154030920800c4281070107401242794540200d0a40b42c0240c022280122007450365100c03e05d1107000c543d0884407003a640c5010440f8040040c2e6054013400503052540b8503658071007640f08211000c588581e03800500e03045001c0601d030001d1704081101c1207031102d03841c05041c0d24054003a440c0a041000b030402c02da609207604844000c010310307005009940c68000c5001061014a500302e038003000900c0c4030406941e03803003a900032a940700d810000b88504241102c4640c09089600e0341c11130b030018840852041c01078001e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 281623570 1250 281622320 281622343
    0x518041d06070305090307110319030f1b050a0201050c031b03070b07021c080612060c04210b1303030603080d0609050702010905060103020d1b060c1101110a06201c0c030c02 76
    0x142003108c504100180c1806071208100c121203003420940d009043c2d000d501510f00d0903558440101c045458107800f105c03420709502c040e00070b07071180000a00552013400141381c01807001056034149000340e1254800d611041c03e880040380c2c001b0507075006000c458143c4a4104246000404e007500030403903081c03040b4034108080428401d13150002029911020010f10000c184881519800e00c0e15001d21000380d0054007411112500c8080990701d00014a000505641c0c0c11208403101c941d91160880399032200108110100340e20354000100144220020b06103001500001050721820004e0a008a4500400c4501103a042c01240400b04c0c41c003103045815a0307019601141c074064942400c541e80002108003031002c04002d9000a20b841d4800220900907110300c8409041d9100d520044881040100840c159500314100f01c0c00082e0b6154000965500e200c2c1004202500c00c041540d25908640720684620b528601d00c14070904c0d01e44512072051400d41402c0148040d01c0380b00039514190b9562 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 281624820 1250 281623570 281623583
    0xb1309030905060c01050a0506031609150f030809100302180f0f090f04030f020d0e04020702030a02100c020a080d08040f0f0c060f1205070e010518041d06070305090307 74
    0x6105050500c80c1c1141806000094801070b030300c0301c0e005001d41c000d02080740d20800391480c007404540b441c075010911001070207003191022460b90400c00700500030081d0803492400d1140300b40001424121b141c045100440c02200b0741a21948200148244004009884800c1502c100100d100345640895140c0c5022030649184105c2c250010100700d00f40d0401e0000c0b548140a5400c006101008284039449180b1981d00c819081801032000d0366150342050a09002c140e041648144a0400f640600206030008044034035080240c0c01040c0b150b51828a00d400181940e8484425820a60714840080c0300c040c1c0244030894401400400050001e0002400ca06510342030710148241c50120071a6250004015942184c0c1d941c2c024043c05289403079600441d0300000170841c511003078403400c0d2242025484104610f06001c0044442e540551007c00181c965040d244805480342c2c880d01c2c4100d04444c2d4507841b02044008080d140241c000d01140416082100300302c6200404819500c07203036407020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 281626070 1250 281624820 281624831
    0x10807090209010e0a03050a12050c0d111c0906020d17070305060111060f0105100806090411010c061e060b190c06060306050f15040b210312070201020406030f0b13 72
    0x40b210f1035502210f40d54044401000482407080218803210058410100440450740c0c00d2270503515801402124521394001c080c18110041c003507101e4659010030342c0107813091541d0f0001c47c010b040c08004070010001d0301c0054140300c8240c0422500411a080d810082c0346640340390845024100010091410162100081103840c2d008001248003000d0fa5030580d141860714944140c6030400c24410644610000c3c0303911400d2038010b0181b103009010103042c1202c00d0361940c1b1a400d02800002c0170b14100302500141e08003280441c42000f103c0d50a41d88980c140814403440c1d54240c505070340080a100300e0800000d170002052410341740710b0070748a08000904d55454140302000b4121980040c0c901801c0070200010740700f01e030807014031a04000e01445448007000d000d00044503281d00c4081d8105406002c00040d60840d880380780051508c1da800c4904d003100c0c5110b00e0402200c1503d0788030150303401003400c2c001641c040c0148a00d000007501c1c20044d0b140d540b40020b0082413034100d158407031a07541c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 281627320 1250 281626070 281626087
    0xa0503120d0c0c02030f030c060609010305060403030e12040f080706021c111509061806100302010525031809050610050a0c02040c09091a030a02060c0115030803070f080108070902 79
    0x14210f2038000c1d90001c05403032030310850711086030700c90344038840041d83c1d402080000b5800349011984141602d400200402143c1d40c2c55800f43c00806020782e10005500c1400f818225428a1000400213440c100e4403500081d450003050903d041000c0e0446015904161030309403d9000c00780502c005034400c0d10f00b000728240c5001006e810200c2c28007420841d41070910030014031140000d0414000da40e24040a121100b1881d409a01c6000540d0410720964544108001541c810005081d00020b10b41c1070101c881c00c5181e40300b1070002542021000300d0340c5d06100c29140b195070705901c00104902d110a10151070f000300090007051800c0c0340802481408581e40d00e24600c00c0c6018403803030354050810040008502006003c0214500c91400c03414105240032000031b08010000d00c02e588003a00409404440c6d40c02c00c415a0011200302c001c0e9035135070064511454114280748029030081044a540e811301d00340003040f8940c0705814100f0f00c20302100401024800144950454001d900c00603202c0444 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 281628570 1250 281627320 281627327
    0x61a1e0313030f09150905120106060203030703150e0109050402031b0a18020c070e09010e3c07060327050a0213022206091a03010909111009050a0503120d0c 69
    0x703030417072118000f0070303420045c03d03c0d041440481074440c119590307040443d29040039405d8414900450005070014804540c0e0381d03009404c80b01c0d1180080503181c059607121031031003417034403401da01c501074441d100c0051105600f01400f03054041c4e40c802a500d08014003c1c07001c510110703514420082030b044400c40404804003598180c0d2340752413041d003c0c0c640345a075a000540390300c0c5040c8c030746220f107510340086103003c00d20004195248926080c501d03c1000f011840303070300750014029180700c4034040031440400902d4060109001500d490344000400980207180c40b010503409440b800c1006034500000000305100082c0202503e904494400e104601c4c1e07003c80c6d0203409254000030152035506c03400480ca80007011038409441a6030b4580c140d070ba90703d55004030102d600340c440202a460030401400103005d150408a0010b0091100d03c0440f815000442c070129808807100c0b000a144010138007140c40c3c61708012009200031402440c0e815034810001b00b6034032440c01c03202d074120750302d0005502c2e1a02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 281629820 1250 281628570 281628587
    0xf040206070303180f050c0105040f050609040207141617031b03090d03050409050705030f070309020a05061602090901110d0e07030b0f010e010e04080d0b04061a1e0313030f 76
    0x1880d8620b9104c4002c40c540130400c0ca00d0040110f03540d0241413030299081d4030804c251021189004c10350001645400c040c80100e07480b4502054202d90200300c0760380815142c01092048046035401007000c100164071596000e07040303070821014500345601d0024442400800d580c0035100344034031488181045c05005145200d994607054100e1720380c40c401020306421402030411104428410302c62a0707107420040322140f00807100030302e85030100c10208000a1095000c160f444e4806000500c04549820001d10717160095440e5003091180c1142003011410901881600802200001c1c811050380c0100c0d44560301a03000008000c070f54502d440000d2101c10403003a0700840d00809c00c2015402e1007145140400780902809116411034000060a40c1c0740b04c40541c41290081c880078208008800580042c2c86902c441c10ba11540341c4002013803218080500ba4464082121000d0ba1001c504401c03000702c0c2c204e620310190a500600c1040804111141040f014503403514000040d04107030030041c0c4503e00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 281631070 1250 281629820 281629841
    0x1b090a0b030d020109030e040c081b07150c120501060905150706020304080c0601140a05151306260628030807030c0611071709010e0402120106030c05030f040206070303 74
    0x4282c008400d101d81d0198010707a4001c0c002c1e512115450034242c20b0000b40c48055000c00006818070000480190341c20807610006010044103501d8100f00f5155085030302404c404e1614595642e501d1449419040b4280c1186150306180a01c020341c90f00301e003d405000c02c1d21a5070b0007003050140c1e4801900584040b42c00702c82d48010119160f090608080c07069810145051038580709402c00440c440001640621012800610303044110f0305141c140702070003c2d03144c0074411240c1c0504c810b25140500815403c0a003540303a0b2400e1078040c4c0c04074000b4100c2c03588030f481100a81c1010a0014030b8a81210b110441264441101201c1100e071000c4880f0300e61030341c000742c040c820210321203003010b91001c212501744c3d01441090101c205000c0b002025440303134210041051400030207a8500d1000f00000e002500f6050424031b1f00c217900c0c0707408030b406d9034802042009801c4441c401400520381600c181030b44040546070031400c5103000403818000050290000e48140710110311003007054401c0c0c000c5045071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 281632320 1250 281631070 281631073
    0x10305070504080a1b170309010509040f050717160503011401090308040905091209010512040c08030f12130305040e0a110408060604050f070c0605090c0306180c031b090a0b03 77
    0xc4ca12801c24069810481e10255500101c1c07a80005413185441005811a40e14101a528205441c001503c40382d0010410580068a0b003030b200c44021240d01c9018072031200c0751640580140700ba0000b0500d44401440762400316403110004142e158050240c9040d18403a00202d400328600d02d00594008134503500c020511200090080344650b0319422490041c2c1e84907046450140c02660b515240307008220126000510511000f170f4181d100348265a04079002c0c81c0181401515148e034941954020701849901e0788000a01c458030001220010f5400012007100034050180c55400500600c80d6208100300c2680c881c020401900349513000c043e0381d2926400075542c2c0d60340ca11007681c44100494038140b04600d4400020198551212481d1083c0b10990b10380303080321559616a402080040d2101005109000c000c4095032400c00903d030194040041c00442d1a0000507003520b4500c0384085240a82c001e41d16400c1c4c4041c65101003010004104c8a00d002696601503c000806410460a506 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 281633570 1250 281632320 281632333
    0x3060a060609170f011d0d0e0906280b090108090c0108011203030b03061501030c020d090b0a02070801110306030714060d0f020c0106030b0613050402030c010507170d14010608040b0601030507050408 87
    0xc002000c48446c180e24946d410744042c02c1200005075501e6400c0c0c2c1041d80c2107240b110000b0b075a4074024a6000710a21700d03040d20328144240420f03158560200d80c20140d1701160004611003550303004400035510090400017000f441601d94002400d281061040100b020b48a6003c3d00c1094000c0e0402080c14801800702d0f001307807030a4044100d402d04404440c9010a250051081c4954404903000091034496203031480c00e9450400c0790b08490744080040c004502031034001144500003070054102d0389509403c1241c0f40d0415070100b604103c440d50101e401da40040f1071740c2140751514000d40d12440221040095004c5104d803100c006071103542010300c4075510300b000110030041804041801244140d50414000c0542d800b40b40490f0810740f0069410b500103000318806600c20300c02494200e200c1c0c600c0402025002e520074403580c12010f00da50a060b01c0311000c4600385075010840c9d0050019250540d81c908040c0c40d05411500d000d013005041544440010340c80d240104125001840f4900c101c2d2070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 281634820 1250 281633570 281633591
    0xc050d1a01030f0203150f01052115060301121b03020d0303090b0c2104020d020904050102040e070507030509090615040603150801060e0a050601030b130b03060a060609170f01 77
    0x261040c6800940840d1404074a040d50045602c00e0301d00c16800e03a0750040b5000c2c10081013203005d6803000452410800c0c01c02c1020401c05001c2d000000c10116000b004c80315081c04601044111100712400b40034042c00d00c010400d014050094a040540060210807181200c000307841400c40c07250006500328070054400c904042d4107a01068515004807800e9100e078403030340b00000c043e115032170200e010400c0d511420f0b1000303500c0120081d0030a200070007154606465502251035900211010b540c9654081001c0007421304003c81142d00103154607080d454601e0300c2c0d4014009014081e00700b07018841410010b296900e030305000d001442c42c482c0760203444a42c1c4140081c043e2800030058041134540d9040085c1115050140d141038076190f141d03401c41a80c0300301d007550003080010a00d5041503201d81c0c40c2e80f160740701c0043d2200b07a800390080c0403a000860000b81481c2c010064952109246480c80411115030310a03d40c10a542140f610081c5412181c014146442c2800307014000f80d52070300d0342441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 281636070 1250 281634820 281634851
    0x602041a0307031a0109030b09010f0905150c07020a0b0c0718060306060e0705030711030906070b0105091b0405100302070c0f030203060f15010f302703030c050d 71
    0x144500040e5800707000241000d1020f413100c24000400e980440c40d204000e000060800c00b4040c3c1c0244e5080000404400d8488214142c1d0b080303400a880c650044044680103442440546510500320501e8900d4042071382e021030003030740f800d200754141e0400200f0030394494042803041c100104850344070f500401c0c0c80b44040d000102480e00c8101c6200d0714000300011040d030360703c200318800c03078060312158290358455805032141842e110480d0041e010820402c0c07456511480a132004600a562140007503041200f44161540d000d8026000d0386c0255480450602a00084400b81c0b2803c1c1c0f40b4035113409030114242c001c2c0c000c5280c0140903562001010034040a0914400c088a000724111680d03500d03680d003400a510008ea917100800c442c200404041540100340c0045180d800c1d10300740300c00350010f400340030f547c003401d15812200c0c4c08a0250800485402c0c01015440038001d0801030303485d1070701040c90040d600b5060b0000c0070f00d074072540e0040312540164140c8100d048055410700c1030310014404c21 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 281637320 1250 281636070 281636077
    0x1140d02010c02041a030c01030506100503040f05030d0203070305090a050a033b0a050d0503042601050735240303030c0a02010c0c02010804030c1511090a080102071e0602041a 77
    0x211b010b486058a000b61940c03190003030602841c0082d0801c0081501c0d44e900301e40c0355100510903100c1034400180440040d40410040003200151000162203040c5540003c050305c0005d401c000d171a51104c0000da0110300042403a800d800d40c10304281d247c1e8500665080e40b49002c6440c07a40300c0c10700c030051206007a0950b0b000b11030b02401c03c0f540c810015464100b0001c0d07034450740d500a022940300b40420f03c20078900b90a8981100303480c00125045400400041c0c0c02d4400031141c103400109403144464040c580d4000d05074400f540380e0b0f0428052001601201034080c001400c49165048480c1e080c00140f41d60249074000410290690f0b64a00d014462848103601c1691110010b41c600b1603042919441105510708141e41691041455180c5403001c86005414070015a6030210801100301460154410740c040718400303045843d01c1d08405410030001e01800c0d40701800603401040300230009401d01141210030a6003031104000c411181c10b004009005507080400b040001d170740200c11071402100034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 281638570 1250 281637320 281637371
    0x1030b1017091c050714072414031305010515060a05090a030c060206040c061e052214031002040e06060c1203040f060b0f06250b0c030601110601140d02010c0204 71
    0x3461a0746c0503100071180d85d0b21680c0300b010804050b100700c80003200c0586000e040d03801024500000340860388180080540d03c02d9842d59140c03010344c0c0c5108100402809101e61102405403102510301080b0040b0b51584154060320040000008441c00340c1d0703443c0c0d5903180281d5000211a0300903500c50b100a951010190b034181c4e08400b100030001001807156102c1c000d80c107031245e00c16040070240d4105a400350051012199092100d040c0c03006c0782d50700c10f03103654020410030802c01d42519002090500340508000d0b40b143e0703a801000140542c00070801c80a401c0503050724410350392000101c1031814420595a00e80b50040c001081c8030505c0211000a0110b07402403004200851081c3c04000c00c1503400000140c1183c020300c080440c40e040c1e00710b4484540c420102c2e0f88003c4a1541e29000d03a0f5030110f4140c604800044244055940c0c0460800102a01c6030300030801c81d41452194801c15004040d82d41c0310b00314010035542164490503410b003045901500501c07158034504a100382d41c190355001d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 281639820 1250 281638570 281638583
    0xb01030c031403040501020a020f04020717040f08030705190317040501050601080108030937080106080d02160e0a09080307030507030b0d02090a02090f0901120201030b1017091c0507 80
    0x10b19045068040216800c49a05800411f2442c05990070302c49040d94122005c1d92203642448550701051075074900d40c42030a420344003665114201685c100c1c014031280c006804990050003000c000074000200e5640c80151303101c811902c4442e61900f00c5016103003015420403010004203000400c4015004240070700000d8031070011982e00d648805035280521800a540110070030ba080d0084082010710882d441107910b203c0340520300342d01001e01c502c0c1044d80007a0041c0c1d981d050401a070b00040c0b04240842e46148064031616440c4080703011a1042c5009044c1c41c40103040204162090b50342c883d0750141d60208089880b441d21a0300075000340411104c02d00401d05000000c01645080c9c89001400c680c02000c01d00b641c0c07034411660b0000e4002e0300c9034a4000245101c101110b907685510203009044044403010390b107109200042c03e580300000005e01030030b401d0105015564100d021444200c40750241c240840e03880724200740c5007800c40340c01e070844150141d00500603242c0c4a402461120301426 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 281641070 1250 281639820 281639843
    0x1230403090e0c0a0f0207090213090513080301090e1e0c0a06051905160203060103050d090803030c120a0b0a080304080f0d0e0d05010f0c0e030d0f08061201090b01030c03 75
    0x848024080000c540e0806185001c0041305002401600010f4044c10300d0b204489840b500c6084540803070340094201c0348002c030100c0c0304120316441c80c0681c560110f42e01c4207404001c4080d43d140011804107015840d6801e4992201101004081040c9442145407002412040342c01302026911a56040c4189000e4140f109020600c18021401c86444e6070300d02c9856030701c080e0710718021920b035045420100d8a050315020072101595003000b40e03a0180d4040c801a03c80700d00d202c00c01402607907041c0d2041420350024010017403a2280030042c0d80810030160321210746981c828140c00c00800c0c146240d2a0720440c107400105019800102500903038000c0c40c110750a44e010900310036036500c001c511010002d5050500f202050030034007420640584038100100e02100d0302c170600c0c406c1e20660340c45000001c005060b42e014610f02002501c00000580c141203481d030144040041520350020401d9000e02404000d081c00f1000960240461344c1d0072051000e0156100d20b40495441040d00c016113102c130415 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 281642320 1250 281641070 281641079
    0x130903032a1103090402070539010302030408070c0806090f0102040f03031803050d0804020a050904030e01050318061e06100c060510051207080607021f020c0123040309 74
    0x6030082540d40504440101035010381d00401c0342d00340740c0c442c401c1c00c00b80001d110b80806910703580080e100c1c65100b00080c0408100500d0007410440d6054250a0701e100315144980908418801c030400c9c40e1b1003845e01603075940d194180a1a41c0c42048402000000303074610004030884003040d824051314414041e58612119010018280d00481c0500700300188042d00400c0028080c000c0c045110f18000c0181c40e01c240d591300e449080001001c15440403500c50800c010441ca045038441c005410101c882014900b01a2001030840400508a5045c1b00d000004141e2001d240384110105c1d01c20a8115592440d200001c6a862810709400201012040f000300d4480d01e880950440009081e40d00e02c807c840650325460007401000c2d00f5481d622600c410081400e490fa004215044852400201049031401020a1034000020a40303030441d04454a150000400a4103035820840024400f58036299080303c010300502800186441d4201c0f1440046101c50b00d110715544120b002e40c840588182d40c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 281643570 1250 281642320 281642351
    0x81b15040506090d0203010b06031003020f09010803162d0b060f030d0c1a070e090106230f0405060a20120f1803070603090c17120a0e13090303 63
    0xd602500b0380c07001d018003a415031070502d0080d82012900050001c03c005191501248451340161120904a001d0010031700560610042d0200707820b9054548040541c5001c00e056100d004070000d0303c0c09072080c50440303001d00048085050078180981152251003107020b205004502d41407408039880070100c80060b007203203400240c07181c070114050041c000718005890101c48000c41c4450444840240f0071f00710300c801040b2010184510401d484035280c5500c03440400101010590020007003000e0741e4452040e40d002c000203a807952046403401c03503d50031b0027403c0403000c1c0126004903400020110310f044609600c100c05003000ca52002c032100381d03880c008081c41d0300e450400b4241e0204a80c00c024035420364500c0c0300100302003d944001c0c003804804000010b424080164442030010303844104640a2000640e5003400500080008611800443c0c01c02525450a6400311446050104154090300c0c00707940075120700d46005180112a4610001c0302005002c4044140c0029251000e451040c406 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 281644820 1250 281643570 281643577
    0x307080301062706050315041b050708041509210f0f150e0303220b0f0414010e1608190b060616302106081b15 49
    0x42160680385182c0c00d0030700580301c05100d400c0d2035404203245070b0011032800384680c5160141c411a030b14141e89007014400251011505101a8800ca1804184070b40d0141c034a580700d218207125040403901c0300310390304080701c01d401075030301c64800c140b041c2c185020101d5002c1701600940300301600140c4070030300d141d544008038407282400416480c10f03451008046403002c00c081c07041d0384c41200d11000c1c0c06c21b0402d41100b9205011003003082c951000c000d22a440700d080c6504622030388242209001500d07280c0b10014220000341008141d22701400109084c403400c12141c03000500014000d104080c604025681d0307403440345000030003800c101400442e0360500821030b120007600da2500c6203c00c03545a120940c02e200058805ea500c410108600c40b29840004d0024900c103003d40807071030045060281004007110ba04c4880c0341c8034411010203100068018000300061b41e0100d80e64150b00d025031101d03c1c0200707101c0c0c101160600c15402c4c680070141c445903034481c1072001507810400c0e4203084202d8031160b01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 281646070 1250 281644820 281644823
    0x31d0109051c0210020304140307062f04030b070e10050301050102062401030b06131205010501080102040302130507021f021b0d090603090804050d140d050a0c0b04050a080406021e0307 81
    0x20041c0c4035401d98904c4070340255802038042e09414291003d80c9041520315030002c20100e80890b00d03215200031901c07014070443c40001c041c1840c404113158072245041948501e0000402c50390780b1001040c1c84030700c5000e8480400c4d02c040c3c0f06c42c0c0b0070f4004840c0034046810134400c9038010711036540000c10f030800609003404007014041000c440030030408015000750120001c0036030030500c140041e60f01131985180703000040004020784240150039050042c20354074140c005101d96801003100700016110320305105409280340d240010b4076218441c1c1281013002c0b642c1c07100005801e00030030104002d42c50303000b041d00c10003514400700c400181c000c0340c03600d401080074000c022640d0301c402002064001c3d08144445807040340901c1c5007a46a400040f803540b84150f09685440d90451030760342034881044541d800d030700603091143c104000640c009105000340c40d03009088409403c042802c00074100502c06404c0d41c40401244c403192500002951030b01c0f2010300c802400e0313040340d6010f04142c0c04401c555446 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 281647320 1250 281646070 281646073
    0x5044208190b222007060f0204080309190504020d050f0f060312280f11030301030803040f03020a0b040308150a1d1801020d0b18100312031d0109051c02 67
    0x14184056000380c03110100d030b00c006255813507404082c52805071410076044031554014260304c45a040c03e1000455800042890206104010500c2481000070130b0300c0307081c00210703041c480f45581c5251111051800741e00190308103002060038041034442c2c0e00322900c1154190f03100b0640d6640d200111080c0f040560f41c0319056040781144800b4048110014000081ca40c24044087e01000d1005107003494001140b00004800e1544030455561241c2c00900b0341042d80c00550031541191a40c0c00280720140c0000c0c54007000f01440d00c01c160090088541003604812010340516090034080c05c0b604044501c5d0b5040740201c1c1030f00c0905c0c90088441ca09617001443da255920b0704400004414440240419540e400421390211006a00740000d015a004090021807450180400d000c260340800d5103965500e40d0f04010001c9070007840380f01e07104490b08a00c1d10381003e031011005400901d107048041e03146c40c0425000045810b8150854070713509219008a0390704045980c01801b0440740880402d005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 281648570 1250 281647320 281647339
    0x11010207030e1c0b09030301090501240513090213050307170c040b0117040302030d0b01030203040210030507050d140910090807030c150204090f05060105044208190b 73
    0x280e0a00042e180500f00d010a444182c810369a1a90010780c00e04403110f22041c0d200000600c0400454060280180aa10589002c81320800d200710710044a014850b000c10102050b040b441915a8003030f17400600d032400007196a0342800030014140c11040c01014005d02c601000058004000c2d0b01c07032000c05900700054204402c03104200f1020b0540a50003d0411170300100b0040c6600f450303070085000394882c7d0019a80c1e024004241010b581d0301d0501a030500d84140304000c09a101c0d46404080c0020364540040d090f5a40001134442b40290f40e190340285140040900c180d407015202c49000301080c070215000b0380e01c1c0181c240165400d1107001820b61100340320303010009006050740d0030880e200302030104102d01e000c1034000c03c903003150384054105034450a0704081c842491040076005482843d080e460b00b801c01c0c0410031501e0a41e0269080c0b03020b05403000e01d00707044010342c604040740b010088040150351140c0041c0b410b1019112041001c04080c40c04120040354860100081d4025224128 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 281649820 1250 281648570 281648597
    0x50f030a0803061809060412030b01050406110f030f070201110604030c02060c010b030318041b0f11190b06090109020301050a0e060f102307200a17010204061101020703 74
    0x121600050b180340d0f0014040010f030140d44007110701451045c3c500340010043d0f8500350031711703880140342d0103409800d061a0030011582c0d41d0b840402c07101130318101c3c10201c1381300c40409151480d100c15401020380717902001c1501d04100d0b030000010701040d07000742d94402508064040c1503440350030070354008010070f1808161600504088001d011020910307000095200040c80100c0c0c25079001c5a401000903220200ca004c151909202e4444100300e0056074503561205600041c0c1040524503410080c08a201c1ca00790200d00c00301300301d4494280a0b0003201c114800ba2500b035641100669090748103085100000c1690038581c800d8030704a49004085002e039a00e08040b80311850b001510280d000110126645500d44401005020703001c0241e8503203811040c3d100c0c124040785040c008c3c09103106810012403021465000f00552440c00341c0031340e010305c01110400558096601d03804100c0c49031007a45810302071079041d8040e02c112051610f03809102d5011400b06800c0348180303e00200031803021400f40e070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 281651070 1250 281649820 281649833
    0x7021c02070e16050d3207140309071a0703020105060108090a0b0703020f0304150c03090f1403070b0f070311040608190204090f0203091e06010e130803130309050f030a 74
    0x26803c42c8141003e80c602440d00c1c5210059800340860980d010848600d0000807464188050b03020196a4805911741c1c1032a1400030040c8121030721290300d40e480440132802e929414040b0b00018441c1c2c400520185185541d544001d400c2111b00354055482c2ca1300064255000c1c442c8644596581c10181036a58215a58062004009400002019401c0c001c807603440003002c0095020307074010f244081648509000201c00d07100c29524610405007090300300303000a0072003114807403401e90000440340652104541940740d4040c204000d402c0c00465414000401c994080c1e80f409541d560760140075004807030300d1a0b0050311440c03140000050075100001d0028401c1003005c1c1c04460b2098016152640e105400c4c030076901c1a040c02045c7c00d60000070710100c42d10404c01c90200c0007040e504000d00304526091a500e8090501c02e4203a03041c4030700e0014581d0040f69030b66806a90b440400d15403681824031001c80318441103a41180800d00200340070a141c580002c04100b2000001d005203e1101700740c0c3c594 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 281652320 1250 281651070 281651101
    0x522120215011211060f0f07081204080d0b0303041a2b1a090108030a1214130213060f090e030c0703080a080109050f0402011b050607021c02070e 64
    0x104114014400716104a09110712814020000254419090f40d03240c204542c82c059050304292091100300a0101c0d4444204292407200581048082d114501800c0051061003050003446190390036004210401c00f62201801c240c1e0003940c41006540e40c44002e0556a220368003440b17011202c60648040c1d08074107103009165031181d540d9150402c0c08040b08400300d45c000070030316459050321241454404051841081c5502008603091012549070002e00c07600e0b881000a80010012500c58400b070746071071500512501c44403140b4403685403410799110120080c90f440d0880c41080303050043c1038800c405015020036549281d008005603481c25a1030001031448842c000780c140810b2281c150320020501280c0010750040c2000b0f070f50703002c10200003001c110b016084404003c0c680b0043c048405550300721980d00590a007440c1a030725044d000220792422003600000d2a0b8442c18082140444d0f02244440001b00901d59a04815903d043c1c203980351070b0035001c0c0003c81e91142c2d00107580c428441885 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 281653570 1250 281652320 281652353
    0x603060308030609070201090c030c060e041107060203070c140114090a02010e100e0a17120a020d140405030a05070303030b06040303021f0e030409061d04020d15060b0a020c040522 79
    0x1038140c189e99454181f22107951007980c01251210381000a5a0030442c0b808101004980800010050191000c420301501102034007041e80840018074403406424159132481e0400f021524100504c0c06240c06403203c2c5140355241c040301c0b4082207185030001410b007004c5070305865825100c903036031090080c4443d03190840410000f1200e0010340303d0b01d40c080034070302401d507800031492140341070032105203407404c0d1000d801e40b801c900f006007620311640802c5002d008420303441c2c000440c411860301c0308090301590f000780c3d602d8000d2681c1d60040050010b140b5003141d00c00e07241440030b440c91008200d800d000c1e0b4440500981c000c8080c5480c00300c10056404c15108964400207400505040b0051841d04150410f00185039030b01410f0040032481c8c8070b9044501c580c50a00103441c43d1550104185200c0400300800405045065030754180e41e80d00408090200349000c41d84070600e8000003075680384000640c44c01039180c0b00114401090b04040c0030030419040c1d0320211401da860b5100080001410b01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 281654676 1106 281653570 281653573
    0x7030e0414090a1704032a050405010510140706050907030b240607050c12161a0327060712150e0a09061803030204030b0106030603080306090702 64
    0x741d0f002083d9104240c40d034030b042c5200c090045030080303410050142c0410503103040d407068144000c44803081010b00c1143c0c00d941d540140002c0703075001e00480340c026040040151030700f03001c4ea56000100d80c80710380c40352401d403068684604440040e242c8910b141c109a40070402c0c03040c101c500e0b40d0010144d8151045440040c0da001c80d41442d0401141d000d000081560018044244100c0c0850403000c0c00a40f02c17540e00600280e190540c4070b8400c441d0901407a030120782c4800d0404001030200b0300541007032660f101c9180c1c59150864000300711550340051030010b0310304501440500d00500882d00c1c0d0b10704201e803892680007a03522484040c2010b51004a040241042a481c16500b000f10041d002650a48a08000c0701510188011020000764400208105540750b80200110790007440c4c10340040c0d8a48608405495091101030140501030010902603e00030a031a40c11603490700 = true := by decide +kernel

theorem cover : BRFrame.Cov 281474820 281654676 := by
  have h0 := BRFrame.cov_init 281474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 281474820 ≤ n) (h2 : n < 281654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
